Require Import EqStuff.
Require Import Contexts.

Definition sigEqFix A (B:A->Type) a b p : (existT B a b = p)->(existT _ a b = existT _ (projT1 p) (projT2 p)).
	destruct p as (a',b').
	intro.
	exact H.
Defined.
Implicit Arguments sigEqFix [A B a b p].

Fixpoint natEq n m := match n,m with
	O,O => unit |
	S n,S m => natEq n m |
	_,_ => False
end.

Definition natEqEC n m : (n = m)->natEq n m.
	intro.
	apply (tr _ H).
	clear m H.
	revert n.
	exact (fix natEqRefl n : natEq n n := match n with
		O => tt |
		S n => natEqRefl n
	end).
Defined.
Implicit Arguments natEqEC [n m].

Definition natEqDC : forall n m,natEq n m->(n = m).
	refine (fix natEqDC n m : natEq n m->(n = m) := match n,m with
		O,O => fun _=>eq_refl _ |
		S n0,S m0 => fun c=>_ |
		_,_ => fun x=>match x with end
	end).
	simpl in c.
	apply (tr (fun _=>_) (natEqDC _ _ c)).
	reflexivity.
Defined.
Implicit Arguments natEqDC [n m].

Lemma natEqECDC n : forall m (e:natEq n m),natEqEC (natEqDC e) = e.
	induction n;intro;destruct m;intro;simpl in e.

	simpl.
	destruct e.
	reflexivity.

	destruct e.

	destruct e.

	set (e' := e) at 2.
	replace e' with (natEqEC (natEqDC e));[| apply IHn].
	clear e'.
	simpl.
	rewrite <- (natEqDC e).
	reflexivity.
Qed.

Lemma natEqDCEC n m (e:n = m) : natEqDC (natEqEC e) = e.
	rewrite <- e.
	clear m e.
	induction n.

	reflexivity.

	change (tr (fun m=>S n = S m) (natEqDC (natEqEC (eq_refl n))) (eq_refl (S n)) = eq_refl (S n)).
	rewrite IHn.
	reflexivity.
Qed.

Definition eqZipO D G C GL GR : ZipCtx D G C O GL GR->(existT (fun G=>forall d,G d->Type) G C = existT _ GL GR).
	intro.
	apply (zipCtxOInv X (fun _ _ _ _=>_)).
	reflexivity.
Defined.
Implicit Arguments eqZipO [D G C GL GR].

Definition zipOEq D G C GL GR : (existT _ G C = existT _ GL GR)->ZipCtx D G C O GL GR.
	intro.
	apply (tr (fun p:sigT (fun G=>forall d,G d->Type)=>match p with existT GL GR => ZipCtx D G C O GL GR end) H).
	apply zipCtxO.
Defined.
Implicit Arguments zipOEq [D G C GL GR].

Lemma ezInv D (G:D->Type) C GL GR (e:existT _ G C = existT _ GL GR) : eqZipO (zipOEq e) = e.
	refine (match e as e return eqZipO (zipOEq (sigEqFix e)) = sigEqFix e with eq_refl => _ end).
	reflexivity.
Qed.

Lemma zeInv D G C GL GR (z:ZipCtx D G C O GL GR) : zipOEq (eqZipO z) = z.
	pose (P n := ZipCtx D G C n GL GR).
	assert (forall e:O = O,zipOEq (eqZipO (tr P e z)) = tr P e z);[| exact (H (eq_refl _))].
	revert P.
	apply (zipCtxOInv z (fun n GL GR z=>let P n := ZipCtx D G C n GL GR in
		forall e:n = O,zipOEq (eqZipO (tr P e z)) = tr P e z)).
	clear GL GR z.
	intros.
	rewrite <- (natEqDCEC _ _ e).
	reflexivity.
Qed.

Remark eqZipO_zipO D G C : eqZipO (zipCtxO D G C) = eq_refl _.
	reflexivity.
Qed.

Lemma foo D G C : (forall z:ZipCtx D G C O G C,z = zipCtxO D G C)->
forall e:existT (fun G=>forall d,G d->Type) G C = existT _ G C,e = eq_refl _.
	intros.
	rewrite <- ezInv with (e := e).
	rewrite (H (zipOEq e)).
	reflexivity.
Qed.
