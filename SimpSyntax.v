Require Import List.
Require Import Compare_dec.

Require Import Utils.

Require Import Le Lt.
Require Import Plus Minus.

(* Syntax of Simple type system *)

Definition simpFam := list (nat * list nat).

Definition varBump n l i := match nat_compare i l with
	Lt => i |
	_ => n + i
end.

Definition varSubst l b i := match nat_compare i l with
	Lt => i |
	Eq => l + b |
	Gt => pred i
end.

Definition laBump n l := map (varBump n l).
Definition laSubst la l b := map (varSubst l b) la.

Definition pBumpG n l (p:nat * _) := let (f,la) := p in (f,laBump n l la).
Definition pSubstG (p:nat * _) l b := let (f,la) := p in (f,laSubst la l b).

Definition pMSubstG (p:nat * _) v := let (f,la) := p in (f,map (fun a=>match nat_compare a (length v) with
	Lt => nth a v O |
	_ => a - length v
end) la).

Fixpoint fBumpG n l (F:simpFam) : simpFam := match F with
	nil => nil |
	p :: F => pBumpG n l p :: fBumpG n (S l) F
end.

Fixpoint fSubstG (F:simpFam) l b : simpFam := match F with
	nil => nil |
	p :: F => pSubstG p l b :: fSubstG F (S l) b
end.

Definition fBumpD n (F:simpFam) : simpFam := map (fun p:_ * _=>let (f,la) := p in (n + f,la)) F.

Fixpoint fApply (F:simpFam) la := match la with
	nil => F |
	a :: la => fSubstG (tl (fApply F la)) O a
end.

Lemma varBumpLo n l i : (i < l)->(varBump n l i = i).
	intro.
	unfold varBump.
	rewrite (proj1 (nat_compare_lt _ _) H).
	reflexivity.
Qed.

Lemma varBumpHi n l i : ~(i < l)->(varBump n l i = n + i).
	intro.
	unfold varBump.
	destruct (nat_compare_spec i l);try reflexivity.
	exact (match H H0 with end).
Qed.

Lemma varSubstLt l b i : (i < l)->(varSubst l b i = i).
	intro.
	unfold varSubst.
	rewrite (proj1 (nat_compare_lt _ _) H).
	reflexivity.
Qed.

Lemma varSubstEq l b i : (i = l)->varSubst l b i = l + b.
	intro.
	unfold varSubst.
	rewrite (proj2 (nat_compare_eq_iff _ _) H).
	reflexivity.
Qed.

Lemma varSubstGt l b i : (i > l)->(varSubst l b i = pred i).
	intro.
	unfold varSubst.
	rewrite (proj1 (nat_compare_gt _ _) H).
	reflexivity.
Qed.

Lemma varBump_Bump n1 n2 l1 l2 i : (l1 <= l2)->
(varBump n2 (n1 + l2) (varBump n1 l1 i) = varBump n1 l1 (varBump n2 l2 i)).
	intro.
	destruct (lt_dec i l1).

	assert (i < l2).
		exact (le_trans _ _ _ l H).
	rewrite varBumpLo with (1 := l).
	rewrite varBumpLo with (1 := H0).
	rewrite varBumpLo with (1 := l).
	apply varBumpLo.
	apply le_trans with (1 := H0).
	apply le_plus_r.

	rewrite varBumpHi with (1 := n).
	destruct (lt_dec i l2).
		rewrite varBumpLo with (1 := l).
		rewrite varBumpHi with (1 := n).
		apply varBumpLo.
		apply plus_lt_compat_l with (1 := l).

		rewrite varBumpHi with (1 := n0).
		rewrite varBumpHi;[| intro;apply n0;apply plus_lt_reg_l with (1 := H0)].
		rewrite varBumpHi;
		[|
			intro;
			apply n;
			apply le_trans with (2 := H0);
			apply le_n_S;
			apply le_plus_r
		].
		rewrite plus_assoc.
		rewrite <- (plus_comm n1).
		rewrite <- plus_assoc.
		reflexivity.
Qed.

Lemma varBumpDiv a b n l i : (n <= b)->(varBump a (l + n) (varBump b l i) = varBump (a + b) l i).
	intro.
	destruct (lt_dec i l).

	rewrite varBumpLo with (1 := l0).
	rewrite varBumpLo with (1 := l0).
	apply varBumpLo.
	apply le_trans with (1 := l0).
	apply le_plus_l.

	rewrite varBumpHi with (1 := n0).
	rewrite varBumpHi with (1 := n0).
	rewrite <- plus_assoc.
	apply varBumpHi.
	intro.
	apply n0.
	apply plus_lt_reg_l with n.
	rewrite <- (plus_comm l).
	apply le_trans with (2 := H0).
	apply le_n_S.
	apply plus_le_compat_r with (1 := H).
Qed.

Lemma varBump_Subst n x l b i :
varBump n (x + l) (varSubst l b i) = varSubst l (varBump n x b) (varBump n (S x + l) i).
	destruct (lt_dec i (S x + l)).

	rewrite varBumpLo with (1 := l0).
	destruct (lt_eq_lt_dec i l);[destruct s |].
		rewrite varSubstLt with (1 := l1).
		rewrite varSubstLt with (1 := l1).
		apply varBumpLo.
		apply le_trans with (1 := l1).
		apply le_plus_r.

		rewrite varSubstEq with (1 := e).
		rewrite varSubstEq with (1 := e).
		assert (forall k,varBump l O k = l + k).
			intro.
			apply varBumpHi.
			apply lt_n_O.
		rewrite <- H.
		rewrite <- plus_comm.
		rewrite varBump_Bump with (1 := le_O_n _).
		apply H.

		rewrite varSubstGt with (1 := l1).
		rewrite varSubstGt with (1 := l1).
		apply varBumpLo.
		destruct i.
			destruct lt_n_O with (1 := l1).
		simpl in l0 |- *.
		apply lt_S_n with (1 := l0).

	rewrite varBumpHi with (1 := n0).
	assert (l < i).
		apply not_lt.
		intro.
		apply n0.
		apply le_trans with (1 := H).
		simpl.
		rewrite plus_n_Sm.
		apply le_plus_r.
	rewrite varSubstGt with (1 := H).
	rewrite varSubstGt;[| apply le_trans with (1 := H);apply le_plus_r].
	destruct i.
		destruct lt_n_O with (1 := H).
	rewrite <- plus_n_Sm.
	simpl.
	apply varBumpHi.
	intro.
	apply n0.
	simpl.
	apply lt_n_S with (1 := H0).
Qed.

Lemma varSubst_Bump n l1 l2 b i : (l1 <= l2)->
(varSubst (n + l2) b (varBump n l1 i) = varBump n l1 (varSubst l2 b i)).
	intro.
	destruct (lt_eq_lt_dec i l2);[destruct s |].

	rewrite varSubstLt with (1 := l).
	destruct (lt_dec i l1).
		rewrite varBumpLo with (1 := l0).
		apply varSubstLt.
		apply le_trans with (1 := l).
		apply le_plus_r.

		rewrite varBumpHi with (1 := n0).
		apply varSubstLt.
		apply plus_lt_compat_l with (1 := l).

	rewrite varSubstEq with (1 := e).
	rewrite e.
	clear i e.
	rewrite varBumpHi with (1 := le_not_lt _ _ H).
	rewrite varBumpHi;[| apply le_not_lt;apply le_trans with (1 := H);apply le_plus_l].
	rewrite varSubstEq with (1 := eq_refl _).
	rewrite <- plus_assoc.
	reflexivity.

	rewrite varSubstGt with (1 := l).
	rewrite varBumpHi;[| apply le_not_lt;apply le_trans with (2 := l);apply le_S with (1 := H)].
	rewrite varSubstGt with (1 := plus_lt_compat_l _ _ _ l).
	destruct i.
		destruct lt_n_O with (1 := l).
	rewrite <- plus_n_Sm.
	simpl.
	rewrite varBumpHi.
		reflexivity.
	apply le_not_lt.
	exact (le_trans _ _ _ H (le_S_n _ _ l)).
Qed.

Lemma varSubstDiv n l1 l2 b i : (l1 <= l2 <= l1 + n)->(varSubst l2 b (varBump (S n) l1 i) = varBump n l1 i).
	intro.
	destruct H.
	destruct (lt_dec i l1).

	rewrite varBumpLo with (1 := l).
	rewrite varBumpLo with (1 := l).
	apply varSubstLt.
	apply le_trans with (1 := l) (2 := H).

	rewrite varBumpHi with (1 := n0).
	rewrite varBumpHi with (1 := n0).
	apply varSubstGt.
	simpl.
	apply le_n_S.
	apply le_trans with (1 := H0).
	rewrite <- plus_comm.
	apply plus_le_compat_l.
	apply not_lt with (1 := n0).
Qed.

Lemma varSubst_Subst x l b1 b2 i : varSubst (x + l) b1 (varSubst l b2 i) =
varSubst l (varSubst x b1 b2) (varSubst (S x + l) b1 i).
	destruct (lt_eq_lt_dec i (S x + l));[destruct s |].

	rewrite varSubstLt with (1 := l0).
	destruct (lt_eq_lt_dec i l);[destruct s |].
		rewrite varSubstLt with (1 := l1).
		rewrite varSubstLt with (1 := l1).
		apply varSubstLt.
		apply le_trans with (1 := l1).
		apply le_plus_r.

		rewrite varSubstEq with (1 := e).
		rewrite varSubstEq with (1 := e).
		assert (forall k,varBump l O k = l + k).
			intro.
			apply varBumpHi.
			apply lt_n_O.
		rewrite <- H.
		rewrite <- plus_comm.
		rewrite varSubst_Bump with (1 := le_O_n _).
		apply H.

		rewrite varSubstGt with (1 := l1).
		rewrite varSubstGt with (1 := l1).
		apply varSubstLt.
		destruct i.
			destruct lt_n_O with (1 := l1).
		simpl in l0 |- *.
		apply lt_S_n with (1 := l0).

	rewrite varSubstEq with (1 := e).
	subst i.
	rewrite varSubstGt with (l := l);[| simpl;apply le_n_S;apply le_plus_r].
	rewrite varSubstGt with (l := l);[| simpl;apply le_n_S;rewrite <- plus_comm;rewrite plus_assoc;apply le_plus_r].
	simpl.
	apply varSubstEq with (1 := eq_refl _).

	rewrite varSubstGt with (1 := l0).
	rewrite varSubstGt with (l := l);[| apply le_trans with (2 := l0);apply le_n_S;apply le_plus_r].
	destruct i.
		destruct lt_n_O with (1 := l0).
	simpl in l0 |- *.
	pose proof (lt_S_n _ _ l0).
	clear l0.
	rewrite varSubstGt with (1 := H).
	rewrite varSubstGt with (l := l);[| apply le_trans with (2 := H);apply le_n_S;apply le_plus_r].
	reflexivity.
Qed.

Lemma laBump_O l la : laBump O l la = la.
	unfold laBump.
	rewrite map_ext with (g := fun a=>a).
		rewrite map_id.
		reflexivity.
	intro.
	unfold varBump.
	destruct (nat_compare a l);reflexivity.
Qed.

Lemma laBump_Bump n1 n2 l1 l2 la : (l1 <= l2)->
(laBump n2 (n1 + l2) (laBump n1 l1 la) = laBump n1 l1 (laBump n2 l2 la)).
	intro.
	unfold laBump.
	rewrite map_map.
	rewrite map_map.
	apply map_ext.
	clear la.
	intro i.
	apply varBump_Bump with (1 := H).
Qed.

Lemma laBumpDiv a b n l la : (n <= b)->(laBump a (l + n) (laBump b l la) = laBump (a + b) l la).
	intro.
	unfold laBump.
	rewrite map_map.
	apply map_ext.
	clear la.
	intro i.
	apply varBumpDiv with (1 := H).
Qed.

Lemma laBump_Subst n x la l b :
laBump n (x + l) (laSubst la l b) = laSubst (laBump n (S x + l) la) l (varBump n x b).
	unfold laBump.
	unfold laSubst.
	rewrite map_map.
	rewrite map_map.
	apply map_ext.
	clear la.
	intro i.
	apply varBump_Subst.
Qed.

Lemma laFreeBump n l la : (laBump 1 l la = la)->(laBump n l la = la).
	intro.
	induction n.

	apply laBump_O.

	change (S n) with (1 + n).
	rewrite <- laBumpDiv with (1 := le_O_n _).
	rewrite <- plus_n_O.
	rewrite IHn.
	exact H.
Qed.

Lemma laSubst_Bump n la l1 l2 b : (l1 <= l2)->
(laSubst (laBump n l1 la) (n + l2) b = laBump n l1 (laSubst la l2 b)).
	intro.
	unfold laBump.
	unfold laSubst.
	rewrite map_map.
	rewrite map_map.
	apply map_ext.
	clear la.
	intro i.
	apply varSubst_Bump with (1 := H).
Qed.

Lemma laSubstDiv n la l1 l2 b : (l1 <= l2 <= l1 + n)->(laSubst (laBump (S n) l1 la) l2 b = laBump n l1 la).
	intro.
	unfold laBump.
	unfold laSubst.
	rewrite map_map.
	apply map_ext.
	clear la.
	intro i.
	apply varSubstDiv with (1 := H).
Qed.

Lemma laSubst_Subst x la l b1 b2 : laSubst (laSubst la l b2) (x + l) b1 =
laSubst (laSubst la (S x + l) b1) l (varSubst x b1 b2).
	unfold laSubst.
	rewrite map_map.
	rewrite map_map.
	apply map_ext.
	clear la.
	intro i.
	apply varSubst_Subst.
Qed.

Lemma fBumpG_O F : forall l,fBumpG O l F = F.
	induction F;intro.

	reflexivity.

	destruct a as (f,la).
	simpl.
	rewrite laBump_O.
	rewrite IHF.
	reflexivity.
Qed.

Lemma fSubstG_length F a : forall l,length (fSubstG F l a) = length F.
	induction F as [| p];intro.

	reflexivity.

	simpl.
	rewrite IHF.
	reflexivity.
Qed.

Lemma fSubstG_nth n a : forall F l,(n < length F)->(nth n (fSubstG F l a) (O,nil) = pSubstG (nth n F (O,nil)) (n + l) a).
	induction n;intros ? ?;(destruct F;intro;[destruct lt_n_O with (1 := H) |]);simpl.

	reflexivity.

	rewrite plus_n_Sm.
	apply IHn.
	apply lt_S_n with (1 := H).
Qed.

Lemma pMSubstG_nil p : pMSubstG p nil = p.
	destruct p as (f,la).
	simpl.
	rewrite map_ext with (g := fun a=>a).
		rewrite map_id.
		reflexivity.
	clear f.
	intro.
	rewrite <- minus_n_O.
	destruct (nat_compare_spec a O);try reflexivity.
	destruct lt_n_O with (1 := H).
Qed.

Lemma pMSubstG_snoc p v b : pMSubstG p (v ++ b :: nil) = pMSubstG (pSubstG p (length v) b) v.
	destruct p as (f,la).
	simpl.
	rewrite app_length.
	simpl.
	rewrite <- plus_n_Sm.
	rewrite <- plus_n_O.
	refine (match _ in _ = m return (_,_) = (_,m) with eq_refl => eq_refl _ end).
	clear f.
	unfold laSubst.
	rewrite map_map.
	apply map_ext.
	intro.
	unfold varSubst.
	destruct (nat_compare_spec a (length v)).

	rewrite H.
	rewrite (proj1 (nat_compare_lt _ _) (le_n _)).
	rewrite app_nth2 with (1 := le_n _).
	rewrite <- minus_n_n.
	simpl.
	rewrite minus_plus.
	destruct (nat_compare_spec (length v + b) (length v));try reflexivity.
	destruct (lt_n_O b).
	apply plus_lt_reg_l with (length v).
	rewrite <- plus_n_O.
	exact H0.

	rewrite (proj1 (nat_compare_lt _ _) (lt_S _ _ H)).
	rewrite app_nth1 with (1 := H).
	rewrite (proj1 (nat_compare_lt _ _) H).
	reflexivity.

	destruct a.
		destruct lt_n_O with (1 := H).
	simpl.
	destruct (nat_compare_spec a (length v));try reflexivity.
	destruct (lt_irrefl a).
	apply le_trans with (1 := H0).
	apply le_S_n with (1 := H).
Qed.

Lemma fBumpD_O F : fBumpD O F = F.
	unfold fBumpD.
	simpl.
	rewrite map_ext with (g := fun p=>p).
		rewrite map_id.
		reflexivity.
	intro.
	destruct a as (f,la).
	reflexivity.
Qed.

Lemma fBumpD_length n F : length (fBumpD n F) = length F.
	apply map_length.
Qed.

Lemma fBumpD_nth n m F d : (n < length F)->(nth n (fBumpD m F) d = let (f,la) := nth n F d in (m + f,la)).
	intro.
	unfold fBumpD.
	set (pB (p:_ * list nat) := let (f,la) := p in (m + f,la)).
	fold (pB (nth n F d)).
	rewrite nth_indep with (d' := pB d).
		apply map_nth.
	rewrite map_length.
	exact H.
Qed.

Lemma fApply_nil la : fApply nil la = nil.
	induction la;simpl.

	reflexivity.

	rewrite IHla.
	reflexivity.
Qed.

Lemma fApply_cons p F la a : fApply (p :: F) (la ++ a :: nil) = fApply (fSubstG F O a) la.
	induction la;simpl.

	reflexivity.

	rewrite IHla.
	reflexivity.
Qed.

Lemma fApply_length F la : length (fApply F la) = length F - length la.
	induction la;simpl.

	apply minus_n_O.

	rewrite fSubstG_length.
	rewrite length_tl.
	rewrite IHla.
	apply minus_n_Sm.
Qed.

Lemma fApply_hd la : forall F,(length la < length F)->(hd (O,nil) (fApply F la) = pMSubstG (nth (length la) F (O,nil)) la).
	induction la as [| a] using rev_ind;intro;(destruct F;[intro;destruct lt_n_O with (1 := H) |]).

	simpl.
	intro.
	rewrite pMSubstG_nil.
	reflexivity.

	rewrite app_length.
	simpl plus.
	rewrite <- plus_n_Sm.
	rewrite <- plus_n_O.
	simpl.
	intro.
	pose proof (lt_S_n _ _ H).
	rewrite fApply_cons.
	rewrite IHla;[| rewrite fSubstG_length;exact H0].
	rewrite fSubstG_nth with (1 := H0).
	rewrite <- plus_n_O.
	rewrite pMSubstG_snoc.
	reflexivity.
Qed.

(* Simple typing rules (But I don't mean simply-typed as in simply-typed lambda calculus.) *)

Inductive SimpParamOK G F : list nat->simpFam->Set :=
	spOKNil : SimpParamOK G F nil F |
	spOKCons a la (B:simpFam) : (a < length G)->
		SimpParamOK G F la (pBumpG (S a) O (nth a G (O,nil)) :: B)->
		SimpParamOK G F (a :: la) (fSubstG B O a).

Inductive SimpFamOK (D:list simpFam) G : simpFam->Set :=
	sfOKNil : SimpFamOK D G nil |
	sfOKCons f la T : (f < length D)->
		SimpParamOK G (fBumpD (S f) (nth f D nil)) la nil->
		SimpFamOK D ((f,la) :: G) T->
		SimpFamOK D G ((f,la) :: T).

Inductive SimpFamsOK D : list simpFam->Set :=
	sfsOKOne F : SimpFamOK D nil F->SimpFamsOK D (F :: nil) |
	sfsOKCons F Fs : SimpFamOK D nil F->SimpFamsOK (F :: D) Fs->SimpFamsOK D (F :: Fs).

Inductive SimpFCtxOK : list simpFam->Set :=
	sfcOKNil : SimpFCtxOK nil |
	sfcOKCons D F : SimpFCtxOK D->SimpFamOK D nil F->SimpFCtxOK (F :: D).

Inductive SimpPCtxOK (D:list simpFam) : list (nat * list nat)->Set :=
	spcOKNil : SimpPCtxOK D nil |
	spcOKCons G f la : (f < length D)->
		SimpPCtxOK D G->
		SimpParamOK G (fBumpD (S f) (nth f D nil)) la nil->
		SimpPCtxOK D ((f,la) :: G).

Lemma fctxProjOK f : forall D,SimpFCtxOK D->(f < length D)->SimpFamOK (skipn (S f) D) nil (nth f D nil).
	induction f;intros ? ?;(destruct H;intro;[destruct lt_n_O with (1 := H) |]).

	simpl.
	exact s.

	simpl in H0.
	exact (IHf _ H (lt_S_n _ _ H0)).
Qed.

Lemma pctxProjOK D a P : forall G,SimpPCtxOK D G->(a < length G)->(forall f la,
	((f,la) = nth a G (O,nil))->
	SimpParamOK (skipn (S a) G) (fBumpD (S f) (nth f D nil)) la nil->
P)->P.
	induction a;intros ? ?;(destruct H;intro;[destruct lt_n_O with (1 := H) |]).

	simpl.
	intro rtn.
	exact (rtn _ _ (eq_refl _) s).

	simpl in H0.
	exact (IHa _ H (lt_S_n _ _ H0)).
Qed.

Lemma spOKFree G F la T : SimpParamOK G F la T->(laBump 1 (length G) la = la).
	intro.
	induction H.

	reflexivity.

	simpl.
	rewrite varBumpLo with (1 := l).
	rewrite IHSimpParamOK.
	reflexivity.
Qed.

Lemma sfOKFree D G T : SimpFamOK D G T->(fBumpG 1 (length G) T = T).
	intro.
	induction H.

	reflexivity.

	simpl in IHSimpFamOK |- *.
	rewrite spOKFree with (1 := s).
	rewrite IHSimpFamOK.
	reflexivity.
Qed.

Lemma sfsOKUnzip D F : SimpFamOK D nil F->
	(forall s,(s < length D)->SimpFamOK (skipn (S s) D) nil (nth s D nil))->
SimpFamsOK nil (unzip (length D) D (F :: nil)).
	intros.
	assert (forall s,(s <= length D)->SimpFamsOK (skipn s D) (unzip s D (F :: nil)));
	[|
		pose proof (H1 _ (le_n _));
		rewrite skipnSkipAll in H2;
		exact H2
	].
	intro.
	induction s;intro.

	simpl.
	apply sfsOKOne with (1 := H).

	rewrite <- unzip_consNth with (d := nil) (1 := H1).
	apply sfsOKCons with (1 := H0 _ H1).
	rewrite skipn_consNth with (1 := H1).
	apply IHs.
	apply lt_le_weak with (1 := H1).
Qed.
