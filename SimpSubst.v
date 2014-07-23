Require Import Compare_dec.
Require Import Utils.

Require Import Le Lt.
Require Import Plus.

Definition varBump n l i := match nat_compare i l with
	Lt => i |
	_ => n + i
end.

Definition varSubst l b i := match nat_compare i l with
	Lt => i |
	Eq => l + b |
	Gt => pred i
end.

Lemma lt_ltdHi n l i : ~(i < l)->ltd l (S n + i).
	intro.
	apply lt_ltd.
	simpl.
	apply le_n_S.
	rewrite <- plus_comm.
	apply le_plus_trans.
	exact (not_lt _ _ H).
Qed.
Implicit Arguments lt_ltdHi [l i].

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
