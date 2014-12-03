Require Import List.

Require Import Utils.
Require Import Substitutions.

Require Import Le Lt.
Require Import Plus Minus.
Require Import Compare_dec.

Module Type TYPES.

Declare Module Import TermBump : TERMBUMP.

Parameter type : Type.

Parameter tyDf : type.
Parameter tyBump : forall (n l:nat) (T:type),type.
Parameter tySubst : forall (l:nat) (b:term) (T:type),type.

Axiom tyBump_Bump : forall n1 n2 T l1 l2,(l1 <= l2)->
(tyBump n2 (n1 + l2) (tyBump n1 l1 T) = tyBump n1 l1 (tyBump n2 l2 T)).

Axiom tyBumpDiv : forall a b n T,(n <= b)->forall l,tyBump a (l + n) (tyBump b l T) = tyBump (a + b) l T.

Axiom tySubst_Bump : forall n b T l1 l2,(l1 <= l2)->
(tySubst (n + l2) b (tyBump n l1 T) = tyBump n l1 (tySubst l2 b T)).

Axiom tySubstDiv : forall n b T l1 l2,(l1 <= l2 <= l1 + n)->(tySubst l2 b (tyBump (S n) l1 T) = tyBump n l1 T).

End TYPES.

Module VarOKBump (Import Types : TYPES).

Import VarBump.
Import TermBump.

Fixpoint ctxBump n G := match G with
	nil => nil |
	T :: G => tyBump n (length G) T :: ctxBump n G
end.

Fixpoint ctxSubst b G := match G with
	nil => nil |
	T :: G => tySubst (length G) b T :: ctxSubst b G
end.

Lemma ctxBump_length n G : length (ctxBump n G) = length G.
	induction G;simpl.

	reflexivity.

	rewrite IHG.
	reflexivity.
Qed.

Lemma ctxBump_nth i n : forall G,(i < length G)->(nth i (ctxBump n G) tyDf = tyBump n (length G - S i) (nth i G tyDf)).
	induction i;intro;(destruct G as [| T];intro;[destruct lt_n_O with (1 := H) |]);simpl.

	rewrite <- minus_n_O.
	reflexivity.

	apply IHi.
	apply lt_S_n with (1 := H).
Qed.

Lemma ctxSubst_length b G : length (ctxSubst b G) = length G.
	induction G;simpl.

	reflexivity.

	rewrite IHG.
	reflexivity.
Qed.

Lemma ctxSubst_nth i b : forall G,(i < length G)->(nth i (ctxSubst b G) tyDf = tySubst (length G - S i) b (nth i G tyDf)).
	induction i;intro;(destruct G as [| T];intro;[destruct lt_n_O with (1 := H) |]);simpl.

	rewrite <- minus_n_O.
	reflexivity.

	apply IHi.
	apply lt_S_n with (1 := H).
Qed.

Inductive VarOK G i : type->Set := mkVarOK : (i < length G)->VarOK G i (tyBump (S i) O (nth i G tyDf)).

Lemma varOKBump GL X GR i T : VarOK (GR ++ GL) i T->
VarOK (ctxBump (length X) GR ++ X ++ GL) (varBump (length X) (length GR) i) (tyBump (length X) (length GR) T).
	intro.
	destruct H.
	destruct (le_lt_dec (length GR) i).

	rewrite varBumpHi with (1 := le_not_lt _ _ l0).
	assert (let i' := length X + i in
	tyBump (length X) (length GR) (tyBump (S i) O (nth i (GR ++ GL) tyDf)) =
	tyBump (S i') O (nth i' (ctxBump (length X) GR ++ X ++ GL) tyDf)).
		simpl.
		rewrite app_nth2 with (1 := l0).
		rewrite app_nth2;rewrite ctxBump_length;[| apply le_trans with (1 := l0);apply le_plus_r].
		rewrite <- le_plus_minus_assoc with (1 := l0).
		rewrite app_nth2 with (1 := le_plus_l _ _).
		rewrite minus_plus.
		change (length GR) at 1 with (O + length GR).
		rewrite tyBumpDiv with (1 := le_S _ _ l0).
		rewrite plus_n_Sm.
		reflexivity.
	simpl in H.
	rewrite H.
	apply mkVarOK.
	rewrite app_length.
	rewrite ctxBump_length.
	rewrite app_length.
	rewrite plus_assoc.
	rewrite <- (plus_comm (length X)).
	rewrite <- plus_assoc.
	apply plus_lt_compat_l.
	rewrite <- app_length.
	exact l.

	rewrite varBumpLo with (1 := l0).
	assert (tyBump (length X) (length GR) (tyBump (S i) O (nth i (GR ++ GL) tyDf)) =
	tyBump (S i) O (nth i (ctxBump (length X) GR ++ X ++ GL) tyDf)).
		rewrite app_nth1 with (1 := l0).
		rewrite app_nth1;[| rewrite ctxBump_length;exact l0].
		rewrite ctxBump_nth with (1 := l0).
		rewrite <- tyBump_Bump with (1 := le_O_n _).
		rewrite <- le_plus_minus with (1 := l0).
		reflexivity.
	rewrite H.
	apply mkVarOK.
	rewrite app_length.
	rewrite ctxBump_length.
	apply le_plus_trans with (1 := l0).
Qed.

End VarOKBump.

Module Type TYPINGBUMP.

Declare Module Import Types : TYPES.
Import TermBump.

Module VarSubst := VarSubst TermBump.
Module Import VarOKBump := VarOKBump Types.

Parameter TermOK : forall (G:list type) (t:term) (T:type),Type.
Parameter TypeOK : forall (G:list type) (T:type),Type.

Axiom tmOKVar : forall G i T,VarOK G i T->TermOK G (tmVar i) T.

Axiom tmOKBump : forall GL X GR t T,TermOK (GR ++ GL) t T->
TermOK (ctxBump (length X) GR ++ X ++ GL) (tmBump (length X) (length GR) t) (tyBump (length X) (length GR) T).

End TYPINGBUMP.

Module VarOKSubst (Import TypingBump : TYPINGBUMP).

Import Types VarSubst VarOKBump.
Import TermBump.

Inductive CtxOK : list type->Type :=
	ctxOKNil : CtxOK nil |
	ctxOKCons G T : CtxOK G->TypeOK G T->CtxOK (T :: G).

Lemma ctxProjOK i : forall G,CtxOK G->(i < length G)->TypeOK (skipn (S i) G) (nth i G tyDf).
	induction i;intros;(destruct X;[destruct lt_n_O with (1 := H) |]).

	exact t.

	exact (IHi _ X (le_S_n _ _ H)).
Qed.

Lemma varOKSubst GL b B GR i T : TermOK GL b B->VarOK (GR ++ B :: GL) i T->
TermOK (ctxSubst b GR ++ GL) (varSubst (length GR) b i) (tySubst (length GR) b T).
	intros Hb Hi.
	destruct Hi.
	destruct (lt_eq_lt_dec i (length GR));[clear l;destruct s |].

	rewrite varSubstLt with (1 := l).
	assert (tySubst (length GR) b (tyBump (S i) O (nth i (GR ++ B :: GL) tyDf)) =
	tyBump (S i) O (nth i (ctxSubst b GR ++ GL) tyDf)).
		rewrite app_nth1 with (1 := l).
		rewrite app_nth1;[| rewrite ctxSubst_length;exact l].
		rewrite ctxSubst_nth with (1 := l).
		rewrite <- tySubst_Bump with (1 := le_O_n _).
		rewrite <- le_plus_minus with (1 := l).
		reflexivity.
	rewrite H.
	apply tmOKVar.
	apply mkVarOK.
	rewrite app_length.
	rewrite ctxSubst_length.
	apply le_plus_trans with (1 := l).

	rewrite varSubstEq with (1 := e).
	subst i.
	rewrite app_nth2 with (1 := le_n _).
	rewrite minus_diag.
	simpl.
	rewrite tySubstDiv with (1 := conj (le_O_n _) (le_n (length GR))).
	change (ctxSubst b GR ++ GL) with (ctxBump (length GR) nil ++ ctxSubst b GR ++ GL).
	rewrite <- (ctxSubst_length b GR).
	apply tmOKBump with (1 := Hb).

	rewrite varSubstGt with (1 := l0).
	revert l.
	destruct i.
		destruct lt_n_O with (1 := l0).
	rewrite app_length.
	simpl.
	rewrite <- plus_n_Sm.
	intro.
	rewrite app_nth2 with (1 := lt_le_weak _ _ l0).
	assert (Hlo := le_S_n _ _ l0).
	assert (Hhi := lt_S_n _ _ l).
	clear l0 l.
	rewrite <- minus_Sn_m with (1 := Hlo).
	simpl.
	rewrite tySubstDiv with (1 := conj (le_O_n _) (le_S _ _ Hlo)).
	assert (nth (i - length GR) GL tyDf =
	nth i (ctxSubst b GR ++ GL) tyDf).
		rewrite app_nth2;rewrite ctxSubst_length;[| exact Hlo].
		reflexivity.
	rewrite H.
	apply tmOKVar.
	apply mkVarOK.
	rewrite app_length.
	rewrite ctxSubst_length.
	exact Hhi.
Qed.

End VarOKSubst.
