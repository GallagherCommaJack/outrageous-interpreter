Require Import List.

Require Import SimpSyntax.
Require Import TreeSyntax.

Require Import Le Lt.
Require Import Plus Minus.
Require Import Compare_dec.

Require Import Utils.
Require Import Substitutions.

Import VarBump.
Import TreeTermBump.
Import TreeVarSubst.
Import TreeVarOKBump.
Import TreeVarOKSubst.

Fixpoint laTree l f la := match la with
	nil => var (l + f) |
	a :: la => apl (laTree l f la) (var a)
end.

Definition spTree l (p:_ * _) := let (f,la) := p in El (laTree l f la).

Fixpoint sfTree l (F:simpFam) := match F with
	nil => Uv |
	p :: F => Pi (spTree l p) (sfTree (S l) F)
end.

Definition sfcTree := map (sfTree O).

Fixpoint spcTree G := match G with
	nil => nil |
	p :: G => spTree (length G) p :: spcTree G
end.

Lemma laTreeChLvl l f la : laTree l f la = laTree O (l + f) la.
	induction la;simpl.

	reflexivity.

	rewrite <- IHla.
	reflexivity.
Qed.

Lemma spcTree_length G : length (spcTree G) = length G.
	induction G;simpl.

	reflexivity.

	rewrite IHG.
	reflexivity.
Qed.

Lemma spcTree_nth a : forall G,(a < length G)->
(nth a (spcTree G) Uv = spTree (length G - S a) (nth a G (O,nil))).
	induction a;intro;(destruct G;intro;[destruct lt_n_O with (1 := H) |]);simpl.

	rewrite <- minus_n_O.
	reflexivity.

	exact (IHa _ (lt_S_n _ _ H)).
Qed.

Lemma laTree_BumpG n l1 l2 f la : (l1 <= l2)->(laTree (l2 + n) f (laBump n l1 la) = ttBump n l1 (laTree l2 f la)).
	intro.
	induction la;simpl.

	rewrite varBumpHi;[| apply le_not_lt;apply le_plus_trans with (1 := H)].
	rewrite plus_assoc.
	rewrite <- (plus_comm n).
	reflexivity.

	rewrite IHla.
	reflexivity.
Qed.

Lemma spTree_BumpG n l1 l2 p : (l1 <= l2)->(spTree (l2 + n) (pBumpG n l1 p) = tpBump n l1 (spTree l2 p)).
	intro.
	destruct p as (f,la).
	simpl.
	rewrite laTree_BumpG with (1 := H).
	reflexivity.
Qed.

Lemma sfTree_BumpG n F : forall l1 l2,(l1 <= l2)->(sfTree (l2 + n) (fBumpG n l1 F) = tpBump n l1 (sfTree l2 F)).
	induction F;intros;simpl.

	reflexivity.

	rewrite spTree_BumpG with (1 := H).
	change (S (l2 + n)) with (S l2 + n).
	rewrite (IHF _ _ (le_n_S _ _ H)).
	reflexivity.
Qed.

Lemma sfTree_BumpDG a b F : forall l,(fBumpG 1 l F = F)->
(sfTree (l + a) (fBumpD b F) = tpBump (a + b) l (sfTree l F)).
	induction F as [| p].

	simpl.
	intros.
	reflexivity.

	intro.
	destruct p as (f,la).
	simpl.
	intro.
	rewrite <- laTree_BumpG with (1 := le_n _).
	rewrite (laTreeChLvl _ f).
	rewrite plus_assoc.
	rewrite <- plus_assoc.
	rewrite <- laTreeChLvl.
	pose proof (ap (fun F=>snd (hd (f,la) F)) H).
	pose proof (ap (@tl _) H).
	simpl in H0,H1.
	clear H.
	rewrite laFreeBump with (1 := H0).
	rewrite <- (IHF _ H1).
	reflexivity.
Qed.

Lemma var_simpVarSubst l b i : var (SimpSubst.varSubst l b i) = varSubst l (var b) i.
	unfold SimpSubst.varSubst.
	unfold varSubst.
	destruct (nat_compare i l);[simpl;rewrite varBumpHi with (1 := lt_n_O _) | |];reflexivity.
Qed.

Lemma laTree_SubstG f la l1 l2 b : (l1 <= l2)->(laTree l2 f (laSubst la l1 b) = ttSubst l1 (var b) (laTree (S l2) f la)).
	intro.
	induction la;simpl.

	rewrite varSubstGt;[| apply le_n_S;apply le_plus_trans with (1 := H)].
	exact (eq_refl (var (l2 + f))).

	rewrite <- IHla.
	rewrite var_simpVarSubst.
	reflexivity.
Qed.

Lemma spTree_SubstG p l1 l2 b : (l1 <= l2)->(spTree l2 (pSubstG p l1 b) = tpSubst l1 (var b) (spTree (S l2) p)).
	intro.
	destruct p as (f,la).
	simpl.
	rewrite <- laTree_SubstG with (1 := H).
	reflexivity.
Qed.

Lemma sfTree_SubstG F b : forall l1 l2,(l1 <= l2)->(sfTree l2 (fSubstG F l1 b) = tpSubst l1 (var b) (sfTree (S l2) F)).
	induction F;intros;simpl.

	reflexivity.

	rewrite <- spTree_SubstG with (1 := H).
	rewrite <- (IHF _ _ (le_n_S _ _ H)).
	reflexivity.
Qed.

Lemma spOKTree D G F f la T : SimpParamOK G F la T->let G' := spcTree G ++ sfcTree D in
VarOK G' (length G + f) (sfTree (length G) F)->TreeTermOK G' (laTree (length G) f la) (sfTree (length G) T).
	simpl.
	intros Hla Hf.
	induction Hla;simpl.

	apply ttOKVar with (1 := Hf).

	rewrite sfTree_SubstG with (1 := le_O_n _).
	apply ttOKApl with (1 := IHHla).
	apply ttOKVar.
	rewrite le_plus_minus with (1 := l).
	rewrite <- plus_comm.
	rewrite spTree_BumpG with (1 := le_O_n _).
	rewrite <- spcTree_nth with (1 := l).
	assert (a < length (spcTree G)).
		rewrite spcTree_length.
		exact l.
	rewrite <- app_nth1 with (l' := sfcTree D) (1 := H).
	apply mkVarOK.
	rewrite app_length.
	apply le_plus_trans with (1 := H).
Qed.

Lemma sfOKTree D G T : SimpFCtxOK D->SimpFamOK D G T->let G' := spcTree G ++ sfcTree D in
CtxOK G'->TreeTypeOK G' (sfTree (length G) T).
	intros HD ?.
	simpl.
	induction H;intro.

	simpl.
	apply tpOKUv.

	simpl in IHSimpFamOK |- *.
	assert (TreeTypeOK (spcTree G ++ sfcTree D) (El (laTree (length G) f la))).
		apply tpOKEl.
		apply spOKTree with (1 := s).
		change (length G) with (O + length G) at 2.
		rewrite sfTree_BumpDG with (1 := sfOKFree _ _ _ (fctxProjOK _ _ HD l)).
		simpl.
		rewrite <- plus_n_Sm.
		rewrite <- map_nth.
		fold sfcTree.
		simpl.
		set (f' := f) at 3.
		replace f' with (length G + f - length (spcTree G));subst f';[| rewrite spcTree_length;apply minus_plus].
		rewrite <- app_nth2 with (l := spcTree G);[| rewrite spcTree_length;apply le_plus_l].
		apply mkVarOK.
		rewrite app_length.
		rewrite spcTree_length.
		apply plus_lt_compat_l.
		unfold sfcTree.
		rewrite map_length.
		exact l.
	refine (let H := IHSimpFamOK _ in _).
		apply ctxOKCons with (1 := X) (2 := H0).
	apply tpOKPi with (1 := H0) (2 := H1).
Qed.
