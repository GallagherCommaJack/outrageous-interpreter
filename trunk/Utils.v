Require Import Compare_dec.

Definition ap A B (f:A->B) (a1 a2:A) (p:a1 = a2) := match p in _ = a2 return f a1 = f a2 with eq_refl => eq_refl _ end.
Implicit Arguments ap [A B a1 a2].

Definition tr A (B:A->Type) (a1 a2:A) (p:a1 = a2) := match p in _ = a2 return B a1->B a2 with eq_refl => fun b=>b end.
Implicit Arguments tr [A a1 a2].

Definition trid (T1 T2:Type) (p:T1 = T2) := match p in _ = T2 return T1->T2 with eq_refl => fun x=>x end.
Implicit Arguments trid [T1 T2].

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
