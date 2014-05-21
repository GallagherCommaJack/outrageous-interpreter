(*
ST0 has X0, a type
ST1 has X0, a type
	and X1, a function from pairs of X0 to type
ST2 has X0, X1,
	and X2, a function from three X0's, and one X1 for each pair of X0's, to type
ST3 has X0, X1, X2,
	and X3, a function from four X0's, one X1 for each pair of X0's, and one X2 for each triple of X1's, to type
...

Parameter X0 : Type.
Parameter X1 : forall (x0 x1:X0),Type.
Parameter X2 : forall (x0 x1 x2:X0)
	(x01:X1 x0 x1) (x02:X1 x0 x2) (x12:X1 x1 x2)
	,Type.
Parameter X3 : forall (x0 x1 x2 x3:X0)
	(x01:X1 x0 x1) (x02:X1 x0 x2) (x03:X1 x0 x3) (x12:X1 x1 x2) (x13:X1 x1 x3) (x23:X1 x2 x3)
	(x012:X2 _ _ _ x01 x02 x12) (x013:X2 _ _ _ x01 x03 x13) (x023:X2 _ _ _ x02 x03 x23) (x123:X2 _ _ _ x12 x13 x23)
	,Type.
...

STn := {X0;X1;...;Xn}
*)

Require Import List.

Require Import Le Lt.
Require Import Plus Minus.
Require Import Compare_dec.

(* Parts of simplex l with n points *)
Fixpoint takeN (l:list nat) n := match n with
	O => nil :: nil |
	S n' => match l with
		nil => nil |
		h :: l' => map (fun r=>h :: r) (takeN l' n') ++ takeN l' n
	end
end.

(* Parts of simplex l with at most n points, in reverse order. No empty simplexes. *)
Fixpoint parts l n := match n with
	O => nil |
	S n' => rev_append (takeN l n) (parts l n')
end.

(* Binders for n-dimensional parts of simplex w *)
Definition simps w n := map (fun l=>(l,parts l n)) (takeN w (S n)).

(* Binders for parts of simplex w with dimension less than n, in reverse order *)
Fixpoint binders w n := match n with
	O => nil |
	S n' => rev_append (simps w n') (binders w n')
end.

Inductive SubSimp : list nat->list nat->Prop :=
	ssNils : SubSimp nil nil |
	ssDrop s l p : SubSimp s l->SubSimp s (p :: l) |
	ssKeep s l p : SubSimp s l->SubSimp (p :: s) (p :: l).

Lemma ssNil l : SubSimp nil l.
	induction l.

	exact ssNils.

	apply ssDrop with (1 := IHl).
Qed.

Lemma ssNilInv s : SubSimp s nil->(s = nil).
	intro.
	inversion_clear H.
	reflexivity.
Qed.

Inductive SSConsInv h l : list nat->Prop :=
	ssConsInvDrop s : SubSimp s l->SSConsInv h l s |
	ssConsInvKeep s : SubSimp s l->SSConsInv h l (h :: s).
Lemma ssConsInv s h l : SubSimp s (h :: l)->SSConsInv h l s.
	intro.
	inversion_clear H.

	apply ssConsInvDrop with (1 := H0).

	apply ssConsInvKeep with (1 := H0).
Qed.

Lemma ssRefl l : SubSimp l l.
	induction l.

	exact ssNils.

	apply ssKeep with (1 := IHl).
Qed.

Lemma ssTrans a b c : SubSimp a b->SubSimp b c->SubSimp a c.
	intros.
	revert a H.
	induction H0;intros.

	exact H.

	apply ssDrop.
	exact (IHSubSimp _ H).

	case ssConsInv with (1 := H);clear a H;intros a ?.
		apply ssDrop.
		exact (IHSubSimp _ H).

		apply ssKeep.
		exact (IHSubSimp _ H).
Qed.

Lemma takeNInd (P:list nat->nat->Prop)
	(takeO:forall l,P l O)
	(takeNil:forall n,P nil (S n))
	(takeNext:forall h l n,(forall n,P l n)->P (h :: l) (S n))
l : forall n,P l n.
	induction l;intro;(destruct n;[apply takeO |]).

	apply takeNil.

	apply takeNext.
	exact IHl.
Qed.

Lemma takeNInInd (P:list nat->nat->list nat->Prop)
	(takeO:forall l,P l O nil)
	(takeKeep:forall h l n s,In s (takeN l n)->P l n s->P (h :: l) (S n) (h :: s))
	(takeDrop:forall h l n s,In s (takeN l (S n))->P l (S n) s->P (h :: l) (S n) s)
l n : forall s,In s (takeN l n)->P l n s.
	induction l n as [| | h l n] using takeNInd;intro.

	assert (justNil : In s (nil :: nil)->(P l O s)).
		intro.
		destruct H.

		rewrite <- H.
		apply takeO.

		destruct H.
	destruct l;exact justNil.

	intro.
	destruct H.

	simpl.
	intro.
	destruct in_app_or with (1 := H0).
		destruct (proj1 (in_map_iff _ _ _) H1) as (r,(?,?)).
		rewrite <- H2.
		apply takeKeep with (1 := H3).
		exact (H _ _ H3).

		apply takeDrop with (1 := H1).
		exact (H _ _ H1).
Qed.

Lemma takeNInLength l n s : In s (takeN l n)->(length s = n).
	intro.
	inversion H using takeNInInd;clear l n s H;intros.

	reflexivity.

	rewrite <- H0.
	reflexivity.

	exact H0.
Qed.

Lemma takeNInSub l n s : In s (takeN l n)->SubSimp s l.
	intro.
	inversion H using takeNInInd;clear l n s H;intros.

	apply ssNil.

	apply ssKeep with (1 := H0).

	apply ssDrop with (1 := H0).
Qed.

Lemma takeNInI l n : forall s,(length s = n)->SubSimp s l->In s (takeN l n).
	induction l n as [| | h l n] using takeNInd;intros.

	clear H0.
	destruct s;[| destruct O_S with (1 := eq_sym H)].
	destruct l;left;reflexivity.

	simpl.
	revert H.
	rewrite ssNilInv with (1 := H0).
	apply O_S.

	revert H0.
	case ssConsInv with (1 := H1);clear s H1;simpl;intros;apply in_or_app.
		right.
		exact (H _ _ H1 H0).

		left.
		apply in_map.
		exact (H _ _ (eq_add_S _ _ H1) H0).
Qed.

Lemma takeNTrans s i l n m : In s (takeN i n)->In i (takeN l m)->In s (takeN l n).
	intros.
	apply takeNInI.

	apply takeNInLength with (1 := H).

	apply ssTrans with i.
		apply takeNInSub with (1 := H).

		apply takeNInSub with (1 := H0).
Qed.

Lemma partsCumulI s l n m : In s (takeN l (S n))->(S n <= m)->In s (parts l m).
	intros.
	induction H0;simpl;rewrite rev_append_rev;apply in_or_app.

	left.
	apply in_rev with (1 := H).

	right.
	exact IHle.
Qed.

Lemma partsCumulE l n s : In s (parts l n)->exists m,m <= n /\ In s (takeN l m).
	induction n;simpl.

	intro.
	destruct H.

	rewrite rev_append_rev.
	intro.
	destruct in_app_or with (1 := H).
		exists (S n).
		apply conj with (1 := le_n _).
		apply in_rev with (1 := H0).

		destruct (IHn H0) as (m,(?,?)).
		exists m.
		exact (conj (le_S _ _ H1) H2).
Qed.

Lemma simpsInE w n l a : In (l,a) (simps w n)->(In l (takeN w (S n)) /\ parts l n = a).
	intro.
	destruct (proj1 (in_map_iff _ _ _) H) as (?,(?,?)).
	assert (x = l /\ parts x n = a).
		change (fst (x,parts x n) = fst (l,a) /\ snd (x,parts x n) = snd (l,a)).
		rewrite <- H0.
		split;reflexivity.
	clear H H0.
	destruct H2.
	rewrite <- H.
	exact (conj H1 H0).
Qed.

Lemma simpsInDim w n b : In b (simps w n)->(length (fst b) = S n).
	destruct b as (l,a).
	intro.
	simpl.
	destruct simpsInE with (1 := H) as (?,_).
	apply takeNInLength with (1 := H0).
Qed.

Lemma simpsStrict w n l a s : In (l,a) (simps w n)->In s a->(length s < length l).
	intros.
	destruct simpsInE with (1 := H).
	subst a.
	destruct partsCumulE with (1 := H0) as (m,(?,?)).
	rewrite takeNInLength with (1 := H1).
	rewrite takeNInLength with (1 := H3).
	apply le_n_S with (1 := H2).
Qed.

Lemma bindersInDim w n b : In b (binders w n)->(length (fst b) <= n).
	induction n.

	intro.
	destruct H.

	simpl.
	rewrite rev_append_rev.
	intro.
	destruct in_app_or with (1 := H).
		rewrite simpsInDim with (1 := proj2 (in_rev _ _) H0).
		apply le_n.

		apply le_S.
		exact (IHn H0).
Qed.

Definition getBinder g a := nth a g (@nil nat,@nil (list nat)).
Definition getArg g a b := nth b (snd (getBinder g a)) nil.

Lemma bindersLengthContraV w n : forall a b,let g := binders w n in
	(a < length g)->(b < length g)->
	(length (fst (getBinder g a)) < length (fst (getBinder g b)))->
(b < a).
	induction n;intros ? ?.

	intros ? ?.
	destruct lt_n_O with (1 := H).

	simpl binders.
	rewrite rev_append_rev.
	intros ? ? ?.
	pose (lg := rev (simps w n)).
	assert (shA : (length lg <= a)->(a - length lg < length (binders w n))).
		intro.
		apply plus_lt_reg_l with (length lg).
		rewrite <- le_plus_minus with (1 := H1).
		rewrite <- app_length.
		exact H.
	assert (shB : (length lg <= b)->(b - length lg < length (binders w n))).
		intro.
		apply plus_lt_reg_l with (length lg).
		rewrite <- le_plus_minus with (1 := H1).
		rewrite <- app_length.
		exact H0.
	unfold g.
	unfold getBinder.
	(destruct (le_lt_dec (length lg) a);
	[rewrite app_nth2 with (1 := l);fold (getBinder (binders w n) (a - length lg)) |
	rewrite app_nth1 with (1 := l);fold (getBinder lg a)]);
	(destruct (le_lt_dec (length lg) b);
	[rewrite app_nth2 with (1 := l0);fold (getBinder (binders w n) (b - length lg)) |
	rewrite app_nth1 with (1 := l0);fold (getBinder lg b)]).
		intro.
		rewrite le_plus_minus with (1 := l0).
		rewrite le_plus_minus with (1 := l).
		apply plus_lt_compat_l.
		apply IHn with (1 := shA l) (2 := shB l0) (3 := H1).

		intros _.
		apply le_trans with (1 := l0) (2 := l).

		intro.
		destruct lt_irrefl with (S n).
		apply le_S.
		assert (In (getBinder lg a) (simps w n)).
			apply in_rev.
			apply nth_In with (1 := l).
		rewrite simpsInDim with (1 := H2) in H1.
		apply le_trans with (1 := H1).
		apply bindersInDim with w.
		apply nth_In.
		exact (shB l0).

		intro.
		destruct lt_irrefl with (S n).
		assert (In (getBinder lg a) (simps w n)).
			apply in_rev.
			apply nth_In with (1 := l).
		assert (In (getBinder lg b) (simps w n)).
			apply in_rev.
			apply nth_In with (1 := l0).
		rewrite <- simpsInDim with (1 := H2) at 1.
		rewrite <- simpsInDim with (1 := H3).
		exact H1.
Qed.

Lemma argIndexes w n a b : let g := binders w n in
	(a < length g)->(b < length (snd (getBinder g a)))->
exists i,getArg g a b = fst (getBinder g (i + a)).
	intros.
Qed.
