Require Import Compare_dec.

Require Import Le Lt.
Require Import Plus.

Module VarBump.

Definition varBump n l i := match nat_compare i l with
	Lt => i |
	_ => n + i
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

Lemma varBump_O l i : varBump O l i = i.
	unfold varBump.
	destruct (nat_compare i l);reflexivity.
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

End VarBump.

Module Type TERMBUMP.

Import VarBump.

Parameter term : Type.

Parameter tmVar : forall i:nat,term.
Parameter tmBump : forall (n l:nat) (t:term),term.

Axiom tmBump_Var : forall n l i,tmBump n l (tmVar i) = tmVar (varBump n l i).

Axiom tmBump_Bump : forall n1 n2 l1 l2 t,(l1 <= l2)->
(tmBump n2 (n1 + l2) (tmBump n1 l1 t) = tmBump n1 l1 (tmBump n2 l2 t)).

Axiom tmBumpDiv : forall a b n l t,(n <= b)->(tmBump a (l + n) (tmBump b l t) = tmBump (a + b) l t).

End TERMBUMP.

Module VarSubst (Import TermBump : TERMBUMP).

Import VarBump.

Definition varSubst l b i := match nat_compare i l with
	Lt => tmVar i |
	Eq => tmBump l O b |
	Gt => tmVar (pred i)
end.

Lemma varSubstLt l b i : (i < l)->(varSubst l b i = tmVar i).
	intro.
	unfold varSubst.
	rewrite (proj1 (nat_compare_lt _ _) H).
	reflexivity.
Qed.

Lemma varSubstEq l b i : (i = l)->(varSubst l b i = tmBump l O b).
	intro.
	unfold varSubst.
	rewrite (proj2 (nat_compare_eq_iff _ _) H).
	reflexivity.
Qed.

Lemma varSubstGt l b i : (i > l)->(varSubst l b i = tmVar (pred i)).
	intro.
	unfold varSubst.
	rewrite (proj1 (nat_compare_gt _ _) H).
	reflexivity.
Qed.

Lemma varBump_Subst n x l b i :
tmBump n (x + l) (varSubst l b i) = varSubst l (tmBump n x b) (varBump n (S x + l) i).
	destruct (lt_dec i (S x + l)).

	rewrite varBumpLo with (1 := l0).
	destruct (lt_eq_lt_dec i l);[destruct s |].
		rewrite varSubstLt with (1 := l1).
		rewrite varSubstLt with (1 := l1).
		rewrite tmBump_Var.
		rewrite varBumpLo;[reflexivity |].
		apply le_trans with (1 := l1).
		apply le_plus_r.

		rewrite varSubstEq with (1 := e).
		rewrite varSubstEq with (1 := e).
		rewrite <- plus_comm.
		apply tmBump_Bump.
		apply le_O_n.

		rewrite varSubstGt with (1 := l1).
		rewrite varSubstGt with (1 := l1).
		rewrite tmBump_Var.
		apply (f_equal tmVar).
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
	rewrite tmBump_Var.
	rewrite varSubstGt;[| apply le_trans with (1 := H);apply le_plus_r].
	apply (f_equal tmVar).
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
(varSubst (n + l2) b (varBump n l1 i) = tmBump n l1 (varSubst l2 b i)).
	intro.
	destruct (lt_eq_lt_dec i l2);[destruct s |].

	rewrite varSubstLt with (1 := l).
	rewrite tmBump_Var.
	destruct (lt_dec i l1).
		rewrite varBumpLo with (1 := l0).
		apply varSubstLt.
		apply le_trans with (1 := l).
		apply le_plus_r.

		rewrite varBumpHi with (1 := n0).
		apply varSubstLt.
		apply plus_lt_compat_l with (1 := l).

	subst i.
	rewrite varBumpHi with (1 := le_not_lt _ _ H).
	rewrite varSubstEq with (1 := eq_refl _).
	rewrite varSubstEq with (1 := eq_refl _).
	rewrite <- tmBumpDiv with (1 := H).
	simpl.
	reflexivity.

	rewrite varBumpHi;[| apply le_not_lt;apply le_trans with (2 := l);apply le_S with (1 := H)].
	rewrite varSubstGt with (1 := plus_lt_compat_l _ _ _ l).
	rewrite varSubstGt with (1 := l).
	rewrite tmBump_Var.
	apply (f_equal tmVar).
	destruct i.
		destruct lt_n_O with (1 := l).
	rewrite <- plus_n_Sm.
	simpl.
	rewrite varBumpHi;[reflexivity |].
	apply le_not_lt.
	apply le_trans with (1 := H) (2 := le_S_n _ _ l).
Qed.

Lemma varSubstDiv n l1 l2 b i : (l1 <= l2 <= l1 + n)->(varSubst l2 b (varBump (S n) l1 i) = tmVar (varBump n l1 i)).
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

End VarSubst.

Module Type TERMSUBST.

Declare Module Import TermBump : TERMBUMP.

Module Import VarSubst := VarSubst TermBump.

Parameter tmSubst : forall (l:nat) (b t:term),term.

Axiom tmSubst_Var : forall l b i,tmSubst l b (tmVar i) = varSubst l b i.

Axiom tmSubst_Bump : forall n l1 l2 b t,(l1 <= l2)->
(tmSubst (n + l2) b (tmBump n l1 t) = tmBump n l1 (tmSubst l2 b t)).

Axiom tmSubstDiv : forall n l1 l2 b t,(l1 <= l2 <= l1 + n)->(tmSubst l2 b (tmBump (S n) l1 t) = tmBump n l1 t).

End TERMSUBST.

Module VarSubstSubst (Import TermSubst : TERMSUBST).

Import TermBump VarSubst.

Lemma varSubst_Subst x l b1 b2 i : tmSubst (x + l) b1 (varSubst l b2 i) =
tmSubst l (tmSubst x b1 b2) (varSubst (S x + l) b1 i).
	destruct (lt_eq_lt_dec i (S x + l));[destruct s |].

	rewrite varSubstLt with (1 := l0).
	rewrite tmSubst_Var.
	destruct (lt_eq_lt_dec i l);[destruct s |].
		rewrite varSubstLt with (1 := l1).
		rewrite varSubstLt with (1 := l1).
		rewrite tmSubst_Var.
		apply varSubstLt.
		apply le_trans with (1 := l1).
		apply le_plus_r.

		rewrite varSubstEq with (1 := e).
		rewrite varSubstEq with (1 := e).
		rewrite <- plus_comm.
		apply tmSubst_Bump with (1 := le_O_n _).

		rewrite varSubstGt with (1 := l1).
		rewrite varSubstGt with (1 := l1).
		rewrite tmSubst_Var.
		apply varSubstLt.
		destruct i.
			destruct lt_n_O with (1 := l1).
		simpl in l0 |- *.
		apply lt_S_n with (1 := l0).

	subst i.
	rewrite varSubstGt with (l := l);[| simpl;apply le_n_S;apply le_plus_r].
	rewrite tmSubst_Var.
	rewrite varSubstEq with (1 := eq_refl _).
	rewrite varSubstEq with (1 := eq_refl _).
	simpl.
	rewrite tmSubstDiv;[reflexivity |].
	simpl.
	apply conj with (1 := le_O_n _).
	apply le_plus_r.

	rewrite varSubstGt with (l := l);[| apply le_trans with (2 := l0);apply le_n_S;apply le_plus_r].
	rewrite varSubstGt with (1 := l0).
	rewrite tmSubst_Var.
	rewrite tmSubst_Var.
	destruct i.
		destruct lt_n_O with (1 := l0).
	simpl in l0 |- *.
	pose proof (lt_S_n _ _ l0).
	clear l0.
	rewrite varSubstGt with (1 := H).
	rewrite varSubstGt with (l := l);[| apply le_trans with (2 := H);apply le_n_S;apply le_plus_r].
	reflexivity.
Qed.

End VarSubstSubst.
