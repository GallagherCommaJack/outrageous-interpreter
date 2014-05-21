Require Import List.
Require Import Compare_dec.

Require Import Le Lt.
Require Import Plus Minus.

(* Some handy stuff missing from the standard library *)

(* Like rev_append, but moves at most s elements *)
Fixpoint unzip T s (l l':list T) := match s with
	O => l' |
	S s => match l with
		nil => l' |
		a :: l => unzip T s l (a :: l')
	end
end.
Implicit Arguments unzip [T].

Lemma minus_n_Sm n : forall m,pred (n - m) = n - S m.
	induction n;intro.

	reflexivity.

	destruct m.
		apply minus_n_O.

		apply IHn.
Qed.

Lemma length_tl T (l:list T) : length (tl l) = pred (length l).
	destruct l;reflexivity.
Qed.

Lemma map_ext_In A B (f g:A->B) l : (forall a,In a l->(f a = g a))->(map f l = map g l).
	induction l;intro.

	reflexivity.

	simpl in H |- *.
	rewrite <- (H _ (or_introl _ (eq_refl _))).
	rewrite <- IHl.
		reflexivity.
	intros.
	exact (H _ (or_intror _ H0)).
Qed.

Lemma skipnSkipAll T (l:list T) : skipn (length l) l = nil.
	induction l.

	reflexivity.

	exact IHl.
Qed.

Lemma skipn_consNth T n (d:T) : forall l,(n < length l)->(nth n l d :: skipn (S n) l = skipn n l).
	induction n;intro;(destruct l;intro;[destruct lt_n_O with (1 := H) |]).

	reflexivity.

	apply IHn.
	apply lt_S_n with (1 := H).
Qed.

Lemma seq_In n l : forall s,In n (seq s l)->(s <= n < s + l).
	induction l;intros;simpl in H.

	destruct H.

	rewrite <- plus_n_Sm.
	destruct H.
		rewrite <- H.
		apply conj with (1 := le_n _).
		apply (le_plus_l (S s)).

		destruct (IHl _ H).
		apply conj with (1 := lt_le_weak _ _ H0).
		exact H1.
Qed.

Lemma unzip_length T n : forall l l':list T,(n <= length l)->(length (unzip n l l') = n + length l').
	induction n;intros ? ?.

	intro.
	reflexivity.

	destruct l;intro.
		destruct le_Sn_O with (1 := H).
	simpl in H |- *.
	rewrite plus_n_Sm.
	apply IHn.
	apply le_S_n with (1 := H).
Qed.

Lemma unzip_consNth T n (d:T) : forall l l',(n < length l)->(nth n l d :: unzip n l l' = unzip (S n) l l').
	induction n;intros ? ?;(destruct l;intro;[destruct lt_n_O with (1 := H) |]).

	reflexivity.

	apply IHn.
	apply lt_S_n with (1 := H).
Qed.

Lemma unzip_nthHi T n l l' (d:T) : forall m,(n <= m)->(n <= length l)->(nth m (unzip n l l') d = nth (m - n) l' d).
	induction n;intro.

	intros.
	rewrite <- minus_n_O.
	reflexivity.

	destruct m;intro.
		destruct le_Sn_O with (1 := H).
	intro.
	rewrite <- unzip_consNth with (d := d) (1 := H0).
	simpl.
	apply IHn with (1 := le_S_n _ _ H) (2 := lt_le_weak _ _ H0).
Qed.

Lemma unzip_nthLo T n m (d:T) : (m < n)->forall l l',(n <= length l)->(nth m (unzip n l l') d = nth (n - S m) l d).
	intro.
	induction H as [| n];intros ? ?;(destruct l;intro Hl;simpl in Hl;[destruct le_Sn_O with (1 := Hl) |]).

	simpl unzip.
	simpl minus.
	rewrite <- minus_n_n.
	change (nth O (t :: l) d) with (nth O (t :: l') d).
	rewrite (minus_n_n m).
	apply unzip_nthHi with (1 := le_n _) (2 := le_S_n _ _ Hl).

	rewrite <- minus_Sn_m with (1 := H).
	simpl.
	apply IHle with (1 := le_S_n _ _ Hl).
Qed.

(* Syntax of Simple type system *)

Definition simpFam := list (nat * list nat).

Definition laBumpG n l := map (fun a=>match nat_compare a l with
	Lt => a |
	_ => n + a
end).

Definition laSubstG la l b := map (fun a=>match nat_compare a l with
	Lt => a |
	Eq => l + b |
	Gt => pred a
end) la.

Definition pBumpG n l (p:nat * _) := let (f,la) := p in (f,laBumpG n l la).
Definition pSubstG (p:nat * _) l b := let (f,la) := p in (f,laSubstG la l b).

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

Lemma laBumpG_O l la : laBumpG O l la = la.
	unfold laBumpG.
	rewrite map_ext with (g := fun a=>a).
		rewrite map_id.
		reflexivity.
	intro.
	destruct (nat_compare a l);reflexivity.
Qed.

Lemma fBumpG_O F : forall l,fBumpG O l F = F.
	induction F;intro.

	reflexivity.

	destruct a as (f,la).
	simpl.
	rewrite laBumpG_O.
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
	induction n;intros ? ?;(destruct F;intro;[destruct lt_n_O with (1 := H) |]).

	reflexivity.

	simpl.
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
	unfold laSubstG.
	rewrite map_map.
	apply map_ext.
	intro.
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
	induction la.

	reflexivity.

	simpl.
	rewrite IHla.
	reflexivity.
Qed.

Lemma fApply_cons p F la a : fApply (p :: F) (la ++ a :: nil) = fApply (fSubstG F O a) la.
	induction la.

	reflexivity.

	simpl.
	rewrite IHla.
	reflexivity.
Qed.

Lemma fApply_length F la : length (fApply F la) = length F - length la.
	induction la.

	apply minus_n_O.

	simpl.
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
	spOKNil : (fBumpG 1 O F = F)->SimpParamOK G F nil F |
	spOKCons a la (B:simpFam) : (a < length G)->SimpParamOK G F la (pBumpG (S a) O (nth a G (O,nil)) :: B)->SimpParamOK G F (a :: la) (fSubstG B O a).

Inductive SimpFamOK (D:list simpFam) G : simpFam->Set :=
	sfOKNil : SimpFamOK D G nil |
	sfOKCons f la T : (f < length D)->SimpParamOK G (fBumpD (S f) (nth f D nil)) la nil->SimpFamOK D ((f,la) :: G) T->SimpFamOK D G ((f,la) :: T).

Inductive SimpFamsOK D : list simpFam->Set :=
	sfsOKOne F : SimpFamOK D nil F->SimpFamsOK D (F :: nil) |
	sfsOKCons F Fs : SimpFamOK D nil F->SimpFamsOK (F :: D) Fs->SimpFamsOK D (F :: Fs).

Lemma sfsOKUnzip D F : SimpFamOK D nil F->(forall s,(s < length D)->SimpFamOK (skipn (S s) D) nil (nth s D nil))->SimpFamsOK nil (unzip (length D) D (F :: nil)).
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
