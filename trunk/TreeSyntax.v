Require Import List.
Require Import Substitutions.
Require Import DepTyping.

Require Import Le.

(* Tree syntax, to do typing in one context *)
Inductive treeTerm : Set :=
	var (i:nat) |
	apl (f a:treeTerm).

Inductive treeType : Set :=
	Uv |
	El (t:treeTerm) |
	Pi (A B:treeType).

Import VarBump.

Fixpoint ttBump n l t := match t with
	var i => var (varBump n l i) |
	apl f a => apl (ttBump n l f) (ttBump n l a)
end.

Fixpoint tpBump n l T := match T with
	Uv => Uv |
	El t => El (ttBump n l t) |
	Pi A B => Pi (tpBump n l A) (tpBump n (S l) B)
end.

Lemma ttBump_O l t : ttBump O l t = t.
	induction t;simpl.

	rewrite varBump_O.
	reflexivity.

	rewrite IHt1.
	rewrite IHt2.
	reflexivity.
Qed.

Lemma ttBump_Bump n1 n2 l1 l2 t : (l1 <= l2)->
(ttBump n2 (n1 + l2) (ttBump n1 l1 t) = ttBump n1 l1 (ttBump n2 l2 t)).
	intro.
	induction t;simpl.

	rewrite varBump_Bump with (1 := H).
	reflexivity.

	rewrite IHt1.
	rewrite IHt2.
	reflexivity.
Qed.

Lemma ttBumpDiv a b n l t : (n <= b)->(ttBump a (l + n) (ttBump b l t) = ttBump (a + b) l t).
	intro.
	induction t;simpl.

	rewrite varBumpDiv with (1 := H).
	reflexivity.

	rewrite IHt1.
	rewrite IHt2.
	reflexivity.
Qed.

Lemma tpBump_O T : forall l,tpBump O l T = T.
	induction T;intro;simpl.

	reflexivity.

	rewrite ttBump_O.
	reflexivity.

	rewrite IHT1.
	rewrite IHT2.
	reflexivity.
Qed.

Lemma tpBump_Bump n1 n2 T : forall l1 l2,(l1 <= l2)->
(tpBump n2 (n1 + l2) (tpBump n1 l1 T) = tpBump n1 l1 (tpBump n2 l2 T)).
	induction T;intros;simpl.

	reflexivity.

	rewrite ttBump_Bump with (1 := H).
	reflexivity.

	rewrite plus_n_Sm.
	rewrite IHT1 with (1 := H).
	rewrite IHT2 with (1 := le_n_S _ _ H).
	reflexivity.
Qed.

Lemma tpBumpDiv a b n T : (n <= b)->forall l,tpBump a (l + n) (tpBump b l T) = tpBump (a + b) l T.
	intro.
	induction T;intro;simpl.

	reflexivity.

	rewrite ttBumpDiv with (1 := H).
	reflexivity.

	change (S (l + n)) with (S l + n).
	rewrite IHT1.
	rewrite IHT2.
	reflexivity.
Qed.

Module Import TreeTermBump <: TERMBUMP.

Definition term := treeTerm.

Definition tmVar := var.
Definition tmBump := ttBump.

Lemma tmBump_Var n l i : tmBump n l (tmVar i) = tmVar (varBump n l i).
	reflexivity.
Qed.

Definition tmBump_Bump := ttBump_Bump.
Definition tmBumpDiv := ttBumpDiv.

End TreeTermBump.

Module Import TreeVarSubst := VarSubst TreeTermBump.

Fixpoint ttSubst l (b t:treeTerm) : treeTerm := match t with
	var i => varSubst l b i |
	apl f a => apl (ttSubst l b f) (ttSubst l b a)
end.

Fixpoint tpSubst l b T := match T with
	Uv => Uv |
	El t => El (ttSubst l b t) |
	Pi A B => Pi (tpSubst l b A) (tpSubst (S l) b B)
end.

Lemma ttBump_Subst n x l b t :
ttBump n (x + l) (ttSubst l b t) = ttSubst l (ttBump n x b) (ttBump n (S x + l) t).
	induction t;simpl.

	apply varBump_Subst.

	change (S (x + l)) with (S x + l).
	rewrite <- IHt1.
	rewrite <- IHt2.
	reflexivity.
Qed.

Lemma ttSubst_Bump n l1 l2 b t : (l1 <= l2)->
(ttSubst (n + l2) b (ttBump n l1 t) = ttBump n l1 (ttSubst l2 b t)).
	intro.
	induction t;simpl.

	apply varSubst_Bump with (1 := H).

	rewrite IHt1.
	rewrite IHt2.
	reflexivity.
Qed.

Lemma ttSubstDiv n l1 l2 b t : (l1 <= l2 <= l1 + n)->(ttSubst l2 b (ttBump (S n) l1 t) = ttBump n l1 t).
	intro.
	induction t;simpl.

	apply varSubstDiv with (1 := H).

	rewrite IHt1.
	rewrite IHt2.
	reflexivity.
Qed.

Lemma tpBump_Subst n x b T : forall l,
tpBump n (x + l) (tpSubst l b T) = tpSubst l (ttBump n x b) (tpBump n (S x + l) T).
	induction T;intro;simpl.

	reflexivity.

	rewrite <- ttBump_Subst.
	reflexivity.

	rewrite <- IHT1.
	rewrite plus_n_Sm.
	rewrite <- IHT2.
	reflexivity.
Qed.

Lemma tpSubst_Bump n b T : forall l1 l2,(l1 <= l2)->
(tpSubst (n + l2) b (tpBump n l1 T) = tpBump n l1 (tpSubst l2 b T)).
	induction T;intros;simpl.

	reflexivity.

	rewrite ttSubst_Bump with (1 := H).
	reflexivity.

	rewrite plus_n_Sm.
	rewrite IHT1 with (1 := H).
	rewrite IHT2 with (1 := le_n_S _ _ H).
	reflexivity.
Qed.

Lemma tpSubstDiv n b T : forall l1 l2,(l1 <= l2 <= l1 + n)->(tpSubst l2 b (tpBump (S n) l1 T) = tpBump n l1 T).
	induction T;intros;simpl.

	reflexivity.

	rewrite ttSubstDiv with (1 := H).
	reflexivity.

	rewrite IHT1 with (1 := H).
	rewrite IHT2;[| destruct H;simpl;exact (conj (le_n_S _ _ H) (le_n_S _ _ H0))].
	reflexivity.
Qed.

Module Import TreeTermSubst <: TERMSUBST.

Module TermBump := TreeTermBump.
Module VarSubst := TreeVarSubst.

Definition tmSubst := ttSubst.

Lemma tmSubst_Var l b i : tmSubst l b (tmVar i) = varSubst l b i.
	reflexivity.
Qed.

Definition tmSubst_Bump := ttSubst_Bump.
Definition tmSubstDiv := ttSubstDiv.

End TreeTermSubst.

Module Import TreeVarSubstSubst := VarSubstSubst TreeTermSubst.

Lemma ttSubst_Subst x l b1 b2 t : ttSubst (x + l) b1 (ttSubst l b2 t) =
ttSubst l (ttSubst x b1 b2) (ttSubst (S x + l) b1 t).
	induction t;simpl.

	apply varSubst_Subst.

	change (S (x + l)) with (S x + l).
	rewrite <- IHt1.
	rewrite <- IHt2.
	reflexivity.
Qed.

Lemma tpSubst_Subst x b1 b2 T : forall l,tpSubst (x + l) b1 (tpSubst l b2 T) =
tpSubst l (ttSubst x b1 b2) (tpSubst (S x + l) b1 T).
	induction T;intro;simpl.

	reflexivity.

	rewrite <- ttSubst_Subst.
	reflexivity.

	rewrite <- IHT1.
	rewrite plus_n_Sm.
	rewrite <- IHT2.
	reflexivity.
Qed.

Module Import TreeTypes <: TYPES.

Module TermBump := TreeTermBump.

Definition type := treeType.

Definition tyDf := Uv.
Definition tyBump := tpBump.
Definition tySubst := tpSubst.

Definition tyBump_Bump := tpBump_Bump.
Definition tyBumpDiv := tpBumpDiv.
Definition tySubst_Bump := tpSubst_Bump.
Definition tySubstDiv := tpSubstDiv.

End TreeTypes.

Module Import TreeVarOKBump := VarOKBump TreeTypes.

Inductive TreeTermOK (G:list treeType) : treeTerm->treeType->Set :=
	ttOKVar i (T:treeType) : VarOK G i T->TreeTermOK G (var i) T |
	ttOKApl A B f a : TreeTermOK G f (Pi A B)->TreeTermOK G a A->
		TreeTermOK G (apl f a) (tpSubst O a B).

Inductive TreeTypeOK G : treeType->Set :=
	tpOKUv : TreeTypeOK G Uv |
	tpOKEl t : TreeTermOK G t Uv->TreeTypeOK G (El t) |
	tpOKPi A B : TreeTypeOK G A->TreeTypeOK (A :: G) B->TreeTypeOK G (Pi A B).

Lemma ttOKBump GL X GR t T : TreeTermOK (GR ++ GL) t T->
TreeTermOK (ctxBump (length X) GR ++ X ++ GL) (ttBump (length X) (length GR) t) (tpBump (length X) (length GR) T).
	remember (GR ++ GL) as G.
	intro.
	revert GR HeqG.
	induction H;intros;simpl.

	apply ttOKVar.
	apply varOKBump.
	unfold type.
	rewrite <- HeqG.
	exact v.

	assert (IH1 := IHTreeTermOK1 _ HeqG).
	assert (IH2 := IHTreeTermOK2 _ HeqG).
	clear IHTreeTermOK1 IHTreeTermOK2.
	simpl in IH1.
	set (gr := length GR) at 3.
	rewrite (plus_n_O gr).
	subst gr.
	rewrite tpBump_Subst.
	rewrite <- plus_n_O.
	apply ttOKApl with (1 := IH1) (2 := IH2).
Qed.

Lemma tpOKBump GL X GR T : TreeTypeOK (GR ++ GL) T->
TreeTypeOK (ctxBump (length X) GR ++ X ++ GL) (tpBump (length X) (length GR) T).
	remember (GR ++ GL) as G.
	intro.
	revert GR HeqG.
	induction H;intros;simpl.

	apply tpOKUv.

	apply tpOKEl.
	change Uv with (tpBump (length X) (length GR) Uv).
	apply ttOKBump.
	rewrite <- HeqG.
	exact t0.

	apply tpOKPi.
		exact (IHTreeTypeOK1 _ HeqG).

		apply (IHTreeTypeOK2 (A :: GR)).
		simpl.
		rewrite <- HeqG.
		reflexivity.
Qed.

Module Import TreeTypingBump <: TYPINGBUMP.

Module Types := TreeTypes.
Module VarSubst := TreeVarSubst.
Module VarOKBump := TreeVarOKBump.

Definition TermOK := TreeTermOK.
Definition TypeOK := TreeTypeOK.

Definition tmOKVar := ttOKVar.
Definition tmOKBump := ttOKBump.

End TreeTypingBump.

Module Import TreeVarOKSubst := VarOKSubst TreeTypingBump.

Lemma ttOKSubst GL b B GR t T : TreeTermOK GL b B->TreeTermOK (GR ++ B :: GL) t T->
TreeTermOK (ctxSubst b GR ++ GL) (ttSubst (length GR) b t) (tpSubst (length GR) b T).
	intro.
	remember (GR ++ B :: GL) as G.
	intro.
	revert GR HeqG.
	induction H0;intros;simpl.

	apply varOKSubst with (1 := H).
	unfold type.
	rewrite <- HeqG.
	exact v.

	assert (IH1 := IHTreeTermOK1 _ HeqG).
	assert (IH2 := IHTreeTermOK2 _ HeqG).
	clear IHTreeTermOK1 IHTreeTermOK2.
	simpl in IH1.
	set (gr := length GR) at 3.
	rewrite (plus_n_O gr).
	subst gr.
	rewrite tpSubst_Subst.
	rewrite <- plus_n_O.
	apply ttOKApl with (1 := IH1) (2 := IH2).
Qed.

Lemma tpOKSubst GL b B GR T : TreeTermOK GL b B->TreeTypeOK (GR ++ B :: GL) T->
TreeTypeOK (ctxSubst b GR ++ GL) (tpSubst (length GR) b T).
	intro.
	remember (GR ++ B :: GL) as G.
	intro.
	revert GR HeqG.
	induction H0;intros;simpl.

	apply tpOKUv.

	apply tpOKEl.
	change Uv with (tpSubst (length GR) b Uv).
	apply ttOKSubst with (1 := H).
	rewrite <- HeqG.
	exact t0.

	apply tpOKPi.
		exact (IHTreeTypeOK1 _ HeqG).

		apply (IHTreeTypeOK2 (A :: GR)).
		simpl.
		rewrite <- HeqG.
		reflexivity.
Qed.
