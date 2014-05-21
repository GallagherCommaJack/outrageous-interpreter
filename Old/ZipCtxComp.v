Require Import Contexts.

(* Cleaning up zipCtxComp for reduction *)

(* A semantic judgement. That is, a context and a conclusion type. *)
Inductive Judg D : Type := judg (G:D->Type) (C:forall d,G d->Type).
Implicit Arguments judg [D].

Definition judgG D (J:Judg D) := match J with judg G _ => G end.
Implicit Arguments judgG [D].
Definition judgC D (J:Judg D) : forall d,judgG J d->Type := match J with judg _ C => C end.
Implicit Arguments judgC [D].

(*
Fixpoint zipCtx D G C n GL GL' GR (f:forall d,GL' d->GL d) : ZipCtx D G C n GL GR->Judg D := match n with
	O => fun _=>judg GL' (fun d g=>GR d (f d g)) |
	S n => fun z=>zipCtxSInv z (fun _ _ _=>_) (fun T _ z=>zipCtx _ _ _ _ _ _ _
		(fun d (g:sigT (fun g=>T d (f d g)))=>existT _ (f d (projT1 g)) (projT2 g)) z)
end.
*)

Definition zipCtx D G C n GL GL' GR (f:forall d,GL' d->GL d) : ZipCtx D G C n GL GR->Judg D.
	intro z.
	apply (zipCtxComp _ z GL' f).
	intros.
	exact (judg G' (fun d g=>C d (f' d g))).
Defined.
Implicit Arguments zipCtx [D G C n GL GR].

Lemma zipCtxOK D G C G' C' n GL GR (z:ZipCtx D G C n GL GR) : forall GL' f,(zipCtx GL' f z = judg G' C')->
ZipCtx D G' C' n GL' (fun d g=>GR d (f d g)).
	induction z using zipCtxInd;intros.

	change ((fun J=>ZipCtx D (judgG J) (judgC J) O GL' (fun d g=>C d (f d g))) (judg G' C')).
	rewrite <- H.
	apply zipCtxO.

	pose proof (X _ _ _ _ _ H).
	apply zipCtxS with (1 := X0).
Qed.

(*
Lemma zipCtxOKC D G C G' C' n GL GR (z:ZipCtx D G C n GL GR) : forall GL' f,
	ZipCtx D G' C' n GL' (fun d g=>GR d (f d g))->
(zipCtx GL' f z = judg G' C').
	induction z using zipCtxInd;intros;simpl.

	apply zipCtxOInv with (1 := X).
	reflexivity.

	remember (fun d g=>forall x,GR d (existT _ (f d g) x)) as GR'.
	revert HeqGR'.
	apply zipCtxSInv with (1 := X).
	clear GR' X.
	intros T' GR' ? ?.
	apply H.
Qed.
*)
