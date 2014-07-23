Require Import List.
Require Import Compare_dec.

Require Import Le Lt.
Require Import Plus Minus.

Definition ap A B (f:A->B) (a1 a2:A) (p:a1 = a2) := match p in _ = a2 return f a1 = f a2 with eq_refl => eq_refl _ end.
Implicit Arguments ap [A B a1 a2].

Definition tr A (B:A->Type) (a1 a2:A) (p:a1 = a2) := match p in _ = a2 return B a1->B a2 with eq_refl => fun b=>b end.
Implicit Arguments tr [A a1 a2].

Definition cast (T1 T2:Type) (p:T1 = T2) := match p in _ = T2 return T1->T2 with eq_refl => fun x=>x end.
Implicit Arguments cast [T1 T2].

Definition Sinj n m : forall e:S n = S m,n = m := @ap _ _ pred _ _.
Implicit Arguments Sinj [n m].

Definition IsTrue b := match b with
	true => True |
	false => False
end.

Definition true_false : true <> false := fun e=>tr IsTrue e I.

Definition IsO n := match n with O => True | _ => False end.
Definition IsS n := match n with O => False | _ => True end.

Definition OUnfold n := match n return IsO n->(n = O) with
	O => fun _=>eq_refl _ |
	_ => fun z=>match z with end
end.
Implicit Arguments OUnfold [n].

Definition SUnfold n := match n return IsS n->(n = S (pred n)) with
	O => fun nz=>match nz with end |
	_ => fun _=>eq_refl _
end.
Implicit Arguments SUnfold [n].

Definition IsLt c := match c with Lt => True | _ => False end.
Definition IsEq c := match c with Eq => True | _ => False end.
Definition IsGt c := match c with Gt => True | _ => False end.

Definition ltd a b := IsLt (nat_compare a b).
Definition eqd a b := IsEq (nat_compare a b).
Definition gtd a b := IsGt (nat_compare a b).

Definition ltd_n_O n : ~ltd n O.
	destruct n;exact (fun x=>x).
Defined.
Implicit Arguments ltd_n_O [n].

Lemma lt_ltd l i : (i < l)->ltd i l.
	intro.
	unfold ltd.
	rewrite (proj1 (nat_compare_lt _ _) H).
	exact I.
Qed.
Implicit Arguments lt_ltd [l i].

Fixpoint gtd_ltd a b : gtd a b = ltd b a := match a,b with
	O,O => eq_refl False |
	O,S _ => eq_refl False |
	S _,O => eq_refl True |
	S a,S b => gtd_ltd a b
end.

Fixpoint eqd_eq a b : eqd a b->(a = b) := match a,b with
	O,O => fun x:True=>eq_refl O |
	O,S _ => fun x:False=>match x with end |
	S _,O => fun x:False=>match x with end |
	S a,S b => fun p:eqd a b=>ap S (eqd_eq a b p)
end.
Implicit Arguments eqd_eq [a b].

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

Lemma le_plus_minus_assoc a b c : (c <= b)->(a + (b - c) = a + b - c).
	intro.
	apply plus_reg_l with c.
	rewrite <- le_plus_minus;[| apply le_trans with (1 := H);apply le_plus_r].
	rewrite plus_assoc.
	rewrite <- (plus_comm a).
	rewrite <- plus_assoc.
	rewrite <- le_plus_minus with (1 := H).
	reflexivity.
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
