Require Import List.
Require Import Compare_dec.

Require Import SimpSyntax.

Require Import Le Lt.
Require Import Plus Minus.

(*
X0 : Type
X1 : forall (x0:X0),Type
X2 : forall (x0:X0) (x1:X1 x0),Type
X3 : forall (x0:X0) (x1:X1 x0) (x2:X2 x0 x1),Type
X4 : forall (x0:X0) (x1:X1 x0) (x2:X2 x0 x1) (x3:X3 x0 x1 x2),Type
...
*)

(* Definition of chained types as raw terms *)

Definition chArgs m := seq O m.

Fixpoint chFam n m : simpFam := match n with
	O => nil |
	S n => (n,chArgs m) :: chFam n (S m)
end.

(* Not actually part of the definition, but related to chSig *)
Fixpoint chCtxD n := match n with
	O => nil |
	S n => chFam n O :: chCtxD n
end.

Fixpoint chSig n l := match n with
	O => l |
	S n => chSig n (chFam n O :: l)
end.

Lemma chFam_length n : forall m,length (chFam n m) = n.
	induction n;intro.

	reflexivity.

	simpl.
	rewrite IHn.
	reflexivity.
Qed.

Lemma chFam_nth s : forall n m,(s <= n)->(nth s (chFam (S n) m) (O,nil) = (n - s,chArgs (s + m))).
	induction s;intros ? ?.

	destruct n;intro;reflexivity.

	destruct n;intro.
		destruct le_Sn_O with (1 := H).
	change (nth s (chFam (S n) (S m)) (O,nil) = (n - s,chArgs (S (s + m)))).
	rewrite plus_n_Sm.
	apply IHs.
	apply le_S_n with (1 := H).
Qed.

Lemma chCtxD_length n : length (chCtxD n) = n.
	induction n.

	reflexivity.

	simpl.
	rewrite IHn.
	reflexivity.
Qed.

Lemma chCtxD_skipn s : forall n,skipn s (chCtxD n) = chCtxD (n - s).
	induction s;intro;(destruct n;[reflexivity |]).

	reflexivity.

	simpl.
	apply IHs.
Qed.

Lemma chCtxD_nth s : forall n,(s <= n)->(nth s (chCtxD (S n)) nil = chFam (n - s) O).
	induction s;intro.

	destruct n;intro;reflexivity.

	destruct n;intro.
		destruct le_Sn_O with (1 := H).
	change (nth s (chCtxD (S n)) nil = chFam (n - s) O).
	apply IHs.
	apply le_S_n with (1 := H).
Qed.

Lemma chSig_unzip n : forall l,chSig (S n) l = unzip n (chCtxD n) (chFam n O :: l).
	induction n;intro.

	reflexivity.

	apply IHn.
Qed.

(* Proof that chained types are well-typed *)

Lemma chArgsFree l : laBumpG 1 l (chArgs l) = chArgs l.
	assert (forall s,(s <= l)->(laBumpG 1 l (seq (l - s) s) = seq (l - s) s));
	[|
		pose proof (H _ (le_n _));
		rewrite <- minus_n_n in H0;
		exact H0
	].
	intro.
	induction s;intro.

	reflexivity.

	simpl.
	rewrite (proj1 (nat_compare_lt _ _));
	[|
		unfold lt;
		rewrite minus_Sn_m with (1 := H);
		simpl;
		apply le_minus
	].
	rewrite minus_Sn_m with (1 := H).
	simpl.
	rewrite IHs with (1 := lt_le_weak _ _ H).
	reflexivity.
Qed.

Lemma chFamFree n m : forall l,fBumpG 1 l (fBumpD m (chFam n l)) = fBumpD m (chFam n l).
	induction n;intro.

	reflexivity.

	simpl.
	rewrite chArgsFree.
	rewrite IHn.
	reflexivity.
Qed.

Lemma chArgsOK n m : (m < n)->SimpParamOK (unzip m (chFam n O) nil) (fBumpD (n - m) (chFam m O)) (chArgs m) nil.
	intro.
	pose (T s := fApply (fBumpD (n - m) (chFam m O)) (seq (m - s) s)).
	assert (Tlen : forall s,length (T s) = m - s).
		intro.
		unfold T.
		rewrite fApply_length.
		rewrite fBumpD_length.
		rewrite chFam_length.
		rewrite seq_length.
		reflexivity.
	assert (forall s,(s <= m)->SimpParamOK (unzip m (chFam n O) nil) (fBumpD (n - m) (chFam m O)) (seq (m - s) s) (T s));
	[|
		pose proof (H0 _ (le_n _));
		pose proof (Tlen m);
		rewrite <- minus_n_n in H1,H2;
		destruct (T m);[exact H1 | destruct O_S with (1 := eq_sym H2)]
	].
	intro.
	induction s;intro;unfold T;simpl.

	apply spOKNil.
	apply chFamFree.

	rewrite minus_Sn_m with (1 := H0).
	simpl.
	assert (Hmn := lt_le_weak _ _ H).
	assert (Hsm := lt_le_weak _ _ H0).
	apply spOKCons.
		unfold lt.
		rewrite minus_Sn_m with (1 := H0).
		rewrite unzip_length;[| rewrite chFam_length;exact Hmn].
		simpl.
		rewrite <- plus_n_O.
		apply le_minus.
	fold (T s).
	rewrite minus_Sn_m with (1 := H0).
	simpl.
	assert (O < length (T s)).
		rewrite Tlen.
		apply plus_lt_reg_l with s.
		rewrite <- plus_n_O.
		rewrite <- le_plus_minus with (1 := Hsm).
		exact H0.
	replace (pBumpG (m - s) O (nth (m - S s) (unzip m (chFam n O) nil) (O,nil))) with (hd (O,nil) (T s)).
		destruct (T s);[destruct lt_n_O with (1 := H1) | exact (IHs Hsm)].
	unfold T.
	clear T Tlen IHs H1.
	rewrite unzip_nthLo;
	[|
		unfold lt;
		rewrite minus_Sn_m with (1 := H0);
		simpl;
		apply le_minus
	|
		rewrite chFam_length;
		exact Hmn
	].
	rewrite minus_Sn_m with (1 := H0).
	simpl.
	replace (m - (m - s)) with s;
	[|
		apply plus_reg_l with (m - s);
		rewrite <- le_plus_minus with (1 := le_minus _ _);
		rewrite <- plus_comm;
		rewrite <- le_plus_minus with (1 := Hsm);
		reflexivity
	].
	clear Hmn.
	destruct n.
		destruct lt_n_O with (1 := H).
	rewrite chFam_nth with (1 := le_trans _ _ _ Hsm (le_S_n _ _ H)).
	rewrite <- plus_n_O.
	clear Hsm.
	destruct m.
		destruct le_Sn_O with (1 := H0).
	assert (Hmn := lt_le_weak _ _ (lt_S_n _ _ H)).
	assert (Hsm := le_S_n _ _ H0).
	clear H.
	simpl (S n - S m).
	rewrite fApply_hd;rewrite seq_length;
	[| rewrite fBumpD_length;rewrite chFam_length;exact H0].
	rewrite fBumpD_nth;[| rewrite chFam_length;exact H0].
	rewrite chFam_nth with (1 := Hsm).
	rewrite <- plus_n_O.
	replace (n - m + (m - s)) with (n - s);
	[|
		apply plus_reg_l with s;
		rewrite <- le_plus_minus with (1 := le_trans _ _ _ Hsm Hmn);
		rewrite <- plus_comm;
		rewrite <- plus_assoc;
		rewrite <- (plus_comm s);
		rewrite <- le_plus_minus with (1 := Hsm);
		rewrite <- plus_comm;
		apply le_plus_minus with (1 := Hmn)
	].
	unfold pMSubstG.
	rewrite seq_length.
	unfold pBumpG.
	refine (match _ in _ = b return (_,_) = (_,b) with eq_refl => eq_refl _ end).
	clear n H0 Hmn Hsm.
	unfold laBumpG.
	apply map_ext_In.
	intros.
	pose proof (seq_In _ _ _ H).
	clear H.
	destruct H0 as (_,?).
	simpl in H.
	rewrite seq_nth with (1 := H).
	rewrite (proj1 (nat_compare_lt _ _) H).
	destruct (nat_compare_spec a O);try reflexivity.
	destruct lt_n_O with (1 := H0).
Qed.

Lemma chFamOK n : SimpFamOK (chCtxD n) nil (chFam n O).
	assert (forall s,(s <= n)->SimpFamOK (chCtxD n) (unzip (n - s) (chFam n O) nil) (chFam s (n - s)));
	[|
		pose proof (H _ (le_n _));
		rewrite <- minus_n_n in H0;
		exact H0
	].
	intro.
	induction s;intro.

	apply sfOKNil.

	destruct n.
		destruct le_Sn_O with (1 := H).
	assert (Hsn := le_S_n _ _ H).
	simpl minus.
	simpl (chFam (S s)).
	lazy beta.
	set (s' := n - s).
	assert (Hs'n : s' <= n).
		apply le_minus.
	assert (Hs : s = n - s').
		apply plus_reg_l with s'.
		rewrite <- le_plus_minus with (1 := Hs'n).
		unfold s'.
		rewrite <- plus_comm.
		rewrite <- le_plus_minus with (1 := Hsn).
		reflexivity.
	apply sfOKCons.
		rewrite chCtxD_length.
		exact H.

		rewrite chCtxD_nth with (1 := Hsn).
		fold s'.
		rewrite Hs.
		rewrite minus_Sn_m with (1 := Hs'n).
		apply chArgsOK.
		apply le_n_S with (1 := Hs'n).

		set (s'' := s) at 2.
		rewrite Hs.
		subst s''.
		set (s'' := s') at 2.
		rewrite (plus_n_O s'').
		subst s''.
		rewrite <- chFam_nth with (1 := Hs'n).
		rewrite unzip_consNth;[| rewrite chFam_length;apply le_n_S with (1 := Hs'n)].
		unfold s'.
		rewrite minus_Sn_m with (1 := Hsn).
		apply IHs.
		apply le_S with (1 := Hsn).
Qed.

Lemma chSigOK n : SimpFamsOK nil (chSig (S n) nil).
	rewrite chSig_unzip.
	set (n' := n) at 1.
	rewrite <- (chCtxD_length n').
	subst n'.
	apply sfsOKUnzip.
		apply chFamOK.
	rewrite chCtxD_length.
	intros.
	destruct n.
		destruct lt_n_O with (1 := H).
	rewrite chCtxD_skipn.
	rewrite chCtxD_nth with (1 := le_S_n _ _ H).
	apply chFamOK.
Qed.

(* <Under construction> *)

Lemma sfsUnzip' D F P : SimpFamOK D nil F->(forall Fs,SimpFamsOK nil Fs->P)->P.
	intros.
	assert (forall s,(s <= length D)->SimpFamsOK (skipn s D) (unzip s D (F :: nil)));
	[|
		pose proof (H1 _ (le_n _));
		rewrite skipnSkipAll in H2;
		exact H2
	].
	intro.
	induction s;intro.

	apply sfsOKOne with (1 := H).

	rewrite <- unzip_consNth with (d := nil) (1 := H1).
	apply sfsOKCons with (1 := H0 _ H1).
	rewrite skipn_consNth with (1 := H1).
	apply IHs.
	apply lt_le_weak with (1 := H1).
Qed.

Lemma chSig' n P : (forall Fs,SimpFamsOK nil Fs->P)->P.
	rewrite chSig_unzip.
	set (n' := n) at 1.
	rewrite <- (chCtxD_length n').
	subst n'.
	apply sfsOKUnzip.
		apply chFamOK.
	rewrite chCtxD_length.
	intros.
	destruct n.
		destruct lt_n_O with (1 := H).
	rewrite chCtxD_skipn.
	rewrite chCtxD_nth with (1 := le_S_n _ _ H).
	apply chFamOK.
Qed.

Inductive Ctx : Type->Type :=
	nilCtx : Ctx unit |
	consCtx G (T:G->Type) : Ctx G->Ctx (sigT T).

(*
Inductive Ctx' G : Type :=
	nilCtx' : ((unit:Type) = G)->Ctx' G |
	consCtx' G' (T:G'->Type) : Ctx' G'->(sigT T = G)->Ctx' G.

Definition prime G : Ctx G->Ctx' G.
	intro.
	induction X.

	apply nilCtx'.
	reflexivity.

	apply (consCtx' _ _ T IHX).
	reflexivity.
Defined.
Implicit Arguments prime [G].

Definition unprime G : Ctx' G->Ctx G.
	intro.
	induction X.

	rewrite <- e.
	apply nilCtx.

	rewrite <- e.
	exact (consCtx _ _ IHX).
Defined.
Implicit Arguments unprime [G].

Lemma prime_unprime G (X:Ctx' G) : prime (unprime X) = X.
	induction X.

	rewrite <- e.
	reflexivity.

	rewrite <- e.
	simpl.
	rewrite IHX.
	reflexivity.
Qed.

Lemma unprime_prime G (X:Ctx G) : unprime (prime X) = X.
	induction X.

	reflexivity.

	simpl.
	rewrite IHX.
	reflexivity.
Qed.

(* What we _really_ want *)
Inductive ctx : Type :=
	cnil |
	ccons (G:ctx) (T:ictx G->Type).
with
Fixpoint ictx (G:ctx) : Type := match G with
	cnil => unit |
	ccons G T => sigT T
end.
*)

Inductive Chain : nat->Type->Type :=
