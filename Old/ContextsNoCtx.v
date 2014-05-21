Require Import EqStuff.

(* Semantic type-level contexts, as left nested sigmas *)

(* Strongly typed de Bruijn indexes:
 * Allow you to project from an environment, n steps from the near end.
 *)
Inductive AtTCtx : forall D,nat->(D->Type)->Type :=
	topTCtx D (T:D->Type) : AtTCtx (sigT T) O (fun d=>T (projT1 d)) |
	popTCtx D n T T' : AtTCtx D n T->AtTCtx (sigT T') (S n) (fun d=>T (projT1 d)).
Implicit Arguments topTCtx [D].
Implicit Arguments popTCtx [D n T].

(* Project from an environment *)
Fixpoint tctxProj D n T (f:AtTCtx D n T) : forall d,T d := match f with
	topTCtx _ _ => @projT2 _ _ |
	popTCtx _ _ _ _ f => fun d=>tctxProj _ _ _ f (projT1 d)
end.
Implicit Arguments tctxProj [D n T].

(* Semantic contexts (in a type-level context) *)

Inductive AtCtx D : forall G:D->Type,nat->(forall d,G d->Type)->Type :=
	topCtx G (T:forall d,G d->Type) : AtCtx D (fun d=>sigT (T d)) O (fun d g=>T d (projT1 g)) |
	popCtx G n T T' : AtCtx D G n T->AtCtx D (fun d=>sigT (T' d)) (S n) (fun d g=>T d (projT1 g)).
Implicit Arguments AtCtx [D].
Implicit Arguments topCtx [D G].
Implicit Arguments popCtx [D G n T].

Fixpoint ctxProj D (G:D->Type) n T (a:AtCtx G n T) d : forall g,T d g := match a with
	topCtx _ _ => @projT2 _ _ |
	popCtx _ _ _ _ a => fun g=>ctxProj _ _ _ _ a _ (projT1 g)
end.
Implicit Arguments ctxProj [D G n T].

(* Weaken for a new type-level context entry *)
Fixpoint ctxBumpD D G n T (F:D->Type) (a:AtCtx G n T) :
AtCtx (fun d:sigT F=>G (projT1 d)) n (fun d=>T (projT1 d)) := match a with
	topCtx _ _ => topCtx _ |
	popCtx _ _ _ _ a => popCtx _ (ctxBumpD _ _ _ _ _ a)
end.
Implicit Arguments ctxBumpD [D G n T].

Lemma ctxProj_BumpD D (G:D->Type) n T (a:AtCtx G n T) F : ctxProj (ctxBumpD F a) = (fun d=>ctxProj a (projT1 d)).
	induction a.

	reflexivity.

	simpl.
	rewrite IHa.
	reflexivity.
Qed.

(* Context zipping stuff, which helps with structural operations. *)

(* Relational zipper for judgements
 * G/C are the original context/conclusion.
 * GL is the left part remaining zipped.
 * The nat is how many context entries have been unzipped.
 * The last index is a right nested pi--a "right context"--where stuff has been unzipped.
 * Ignoring the nat index, this can be thought of as a preorder on judgements.
 *)
Inductive ZipCtx D G C : nat->forall GL:D->Type,(forall d,GL d->Type)->Type :=
	zipCtxO : ZipCtx D G C O G C |
	zipCtxS n GL T GR :
		ZipCtx D G C n (fun d=>sigT (T d)) GR->
		ZipCtx D G C (S n) GL (fun d g=>forall x,GR d (existT _ g x)).
Implicit Arguments zipCtxS [D G C n GL T GR].

Definition zipCtxOInv D G C GL GR (z:ZipCtx D G C O GL GR) (P:forall n GL GR,ZipCtx D G C n GL GR->Type)
	(zcO:P O G C (zipCtxO D G C))
: P _ _ _ z := match z in ZipCtx _ _ _ zro _ _ return (O = zro)->P _ _ _ z with
	zipCtxO => fun _=>zcO |
	zipCtxS _ _ _ _ _ => fun e=>match O_S _ e with end
end (eq_refl _).
Implicit Arguments zipCtxOInv [D G C GL GR].

Definition zipCtxSInv D G C n GL GR (z:ZipCtx D G C (S n) GL GR) : forall (P:forall n GR,ZipCtx D G C n GL GR->Type)
	(zcS:forall T GR (z:ZipCtx D G C n (fun d=>sigT (T d)) GR),
		P _ (fun d g=>forall x,GR d (existT _ g x)) (zipCtxS z))
,P _ _ z.
	simpl.
	refine (match z as z in ZipCtx _ _ _ Sn _ _ return (Sn = S n)->forall P,_->P _ _ z with
		zipCtxO => fun e=>match O_S _ e with end |
		zipCtxS _ _ _ _ z0 => fun e _ zcS=>_
	end (eq_refl _)).
	exact (match eq_sym (Sinj e) return _ with eq_refl => zcS _ _ end z0).
Defined.
Implicit Arguments zipCtxSInv [D G C n GL GR].

Definition zipCtxInd D G C (P:forall n GL GR,ZipCtx D G C n GL GR->Type)
	(zcO:P _ _ _ (zipCtxO D G C))
	(zcS:forall n,(forall GL GR (z:ZipCtx D G C n GL GR),P n GL GR z)->
		forall GL (T:forall d,GL d->Type) GR (z:ZipCtx D G C n (fun d=>sigT (T d)) GR),P _ _ _ (zipCtxS z))
: forall n GL GR (z:ZipCtx D G C n GL GR),P _ _ _ z.
	refine (fix zipCtxInd n := match n with
		O => fun _ _ z=>_ |
		S _ => fun GL GR z=>_
	end).

	exact (zipCtxOInv z _ zcO).

	exact (zipCtxSInv z (fun n GR z=>P n GL GR z) (zcS _ (zipCtxInd _) _)).
Defined.
Implicit Arguments zipCtxInd [D G C n GL GR].

Definition zipCtxSL D G T C n GL GR (z:ZipCtx D G (fun d g=>forall x,C d (existT _ g x)) n GL GR) :
ZipCtx D (fun d=>sigT (T d)) C (S n) GL GR.
	induction z as [| ? ? ? T'] using zipCtxInd.

	apply zipCtxS.
	apply zipCtxO.

	apply zipCtxS.
	apply X with (1 := z).
Defined.
Implicit Arguments zipCtxSL [D G T C n GL GR].

Lemma zipCtxSLInv D G C (P:forall G,(forall d,G d->Type)->Type) n : forall GL GR (z:ZipCtx D G C (S n) GL GR)
	(zcSL:forall G T C (z:ZipCtx D G (fun d g=>forall x,C d (existT _ g x)) n GL GR),
		P (fun d=>sigT (T d)) C),
P G C.
	induction n;intros ? ? ?;
	apply (zipCtxSInv z (fun _ _ _=>_));clear GR z;intros.

	assert (P (fun d=>sigT (T d)) GR->P G C).
		apply (zipCtxOInv z (fun _ GL GR _=>P GL GR->_)).
		exact (fun p=>p).
	apply X.
	clear X.
	apply zcSL.
	apply zipCtxO.

	apply IHn with (1 := z).
	clear G C IHn z.
	intros ? T' ? ?.
	apply zcSL.
	exact (zipCtxS z).
Qed.

Lemma zipCtxTrans D L1 R1 n L2 R2 L3 R3 : ZipCtx D L1 R1 n L2 R2->forall m,ZipCtx D L2 R2 m L3 R3->
ZipCtx D L1 R1 (n + m) L3 R3.
	intro.
	induction X;intros.

	exact X.

	simpl.
	rewrite plus_n_Sm.
	apply IHX.
	apply zipCtxSL with (1 := X0).
Qed.

(* Left/right context relations stating that a left/right context can be/has been unzipped n times *)

Inductive IsLCtx D : nat->(D->Type)->Type :=
	lCtxO G : IsLCtx D O G |
	lCtxS n G (T:forall d,G d->Type) : IsLCtx D n G->IsLCtx D (S n) (fun d=>sigT (T d)).

Inductive IsRCtx D (GL:D->Type) : nat->(forall d,GL d->Type)->Type :=
	rCtxO C : IsRCtx D GL O C |
	rCtxS n T GR : IsRCtx D (fun d=>sigT (T d)) n GR->IsRCtx D GL (S n) (fun d g=>forall x,GR d (existT _ g x)).

Lemma lCtxSInv D n G P : IsLCtx D (S n) G->(forall G (T:forall d,G d->Type),IsLCtx D n G->P (fun d=>sigT (T d)))->P G.
	intros.
	inversion_clear X.
	apply X0 with (1 := X1).
Qed.

Lemma rCtxSInv D GL n GR P : IsRCtx D GL (S n) GR->
	(forall T GR,IsRCtx D (fun d=>sigT (T d)) n GR->
	P (fun d g=>forall x,GR d (existT _ g x)))->
P GR.
	intros.
	inversion_clear X.
	apply X0 with (1 := X1).
Qed.

Lemma lCtxZipper D n GL GR : forall G C,ZipCtx D G C n GL GR->IsLCtx D n G.
	induction n;intros.

	apply lCtxO.

	apply zipCtxSLInv with (P := fun _ _=>_) (1 := X).
	clear G C X.
	intros.
	apply lCtxS.
	apply IHn with (1 := z).
Qed.

Lemma rCtxZipper D G C n GL GR : ZipCtx D G C n GL GR->IsRCtx D GL n GR.
	intro.
	induction X.

	apply rCtxO.

	apply rCtxS with (1 := IHX).
Qed.

Lemma unzipLCtx D n C : forall G,IsLCtx D n G->forall F,(forall GL GR,ZipCtx D G F n GL GR->C)->C.
	induction n.

	intros.
	apply (X0 G F).
	apply zipCtxO.

	intros ? ?.
	apply lCtxSInv with (1 := X).
	clear G X.
	intros.
	apply (IHn _ X (fun d g=>forall x,F d (existT _ g x))).
	intros.
	apply (X0 GL GR).
	exact (zipCtxSL X1).
Qed.

Lemma zipRCtx D n GL GR C : IsRCtx D GL n GR->(forall G F,ZipCtx D G F n GL GR->C)->C.
	intro.
	induction X as [? F |];intro.

	apply (X GL F).
	apply zipCtxO.

	apply IHX.
	intros.
	apply (X0 G F).
	exact (zipCtxS X1).
Qed.

(* Map with precompose *)

Inductive ZipCtxComp D G C n GL GR : Type := mkZipCtxComp G' (f':forall d,G' d->G d)
	(z':ZipCtx D G' (fun d g=>C d (f' d g)) n GL GR).
Implicit Arguments mkZipCtxComp [D G C n GL GR].

Definition zc_G' D G C n GL GR (zc:ZipCtxComp D G C n GL GR) := match zc with mkZipCtxComp G' _ _ => G' end.
Implicit Arguments zc_G' [D G C n GL GR].

Definition zc_f' D G C n GL GR (zc:ZipCtxComp D G C n GL GR) : forall d,zc_G' zc d->G d := match zc with mkZipCtxComp _ f' _ => f' end.
Implicit Arguments zc_f' [D G C n GL GR].

Definition zipCtxComp D G C n GL GR (z:ZipCtx D G C n GL GR) : forall GL' f,
ZipCtxComp D G C n GL' (fun d g=>GR d (f d g)).
	induction z using zipCtxInd;intros.

	apply (mkZipCtxComp GL' f).
	apply zipCtxO.

	exact (match X _ _ z _ (fun d (g:sigT (fun g=>T d (f d g)))=>existT _ (f d (projT1 g)) (projT2 g)) with
		mkZipCtxComp G' f' z' => mkZipCtxComp G' f' (zipCtxS z') end).
Defined.
Implicit Arguments zipCtxComp [D G C n GL GR].

Definition zipCtxSComp D G C n GL (T:forall d,GL d->Type) GR GL' f
	(zc:ZipCtxComp D G C n
		(fun d=>sigT (fun g=>T d (f d g)))
		(fun d g=>GR d (existT _ (f d (projT1 g)) (projT2 g))))
: ZipCtxComp D G C (S n) GL' (fun d g=>forall x:T d (f d g),GR d (existT _ (f d g) x)) := match zc with
	mkZipCtxComp G' f' z' => mkZipCtxComp G' f' (zipCtxS z')
end.
Implicit Arguments zipCtxSComp [D G C n GL T GR GL' f].

Definition zipCtxSComp' D G C n GL (T:forall d,GL d->Type) GR (z:ZipCtx D G C n (fun d=>sigT (T d)) GR) GL' f :
ZipCtxComp D G C (S n) GL' (fun d g=>forall x:T d (f d g),GR d (existT _ (f d g) x)).
	pose (T' d g := T d (f d g)).
	pose (f' d (g:sigT (T' d)) := existT _ (f d (projT1 g)) (projT2 g)).
	exact (zipCtxSComp (zipCtxComp z (fun d=>sigT (T' d)) f')).
Defined.
Implicit Arguments zipCtxSComp' [D G C n GL T GR].

Lemma zipCtxCompSEq D G C n GL (T:forall d,GL d->Type) GR (z:ZipCtx D G C n (fun d=>sigT (T d)) GR) GL' f :
zipCtxComp (zipCtxS z) GL' f = zipCtxSComp' z GL' f.
	reflexivity.
Qed.

Definition zipCtxSLComp D G T C n GL GR GL' (f:forall d,GL' d->GL d)
	(zc:ZipCtxComp D G (fun d g=>forall x:T d g,C d (existT _ g x)) n GL' (fun d g=>GR d (f d g)))
: ZipCtxComp D (fun d=>sigT (T d)) C (S n) GL' (fun d g=>GR d (f d g)).
	refine (match zc with mkZipCtxComp G' f' z' => _ end).
	pose (T' d g := T d (f' d g)).
	pose (f'' d (g:sigT (T' d)) := existT _ (f' d (projT1 g)) (projT2 g)).
	pose (C' d g := C d (f'' d g)).
	change (ZipCtx D G' (fun d g=>forall x:T' d g,C' d (existT _ g x)) n GL' (fun d g=>GR d (f d g))) in z'.
	exact (mkZipCtxComp (fun d=>sigT (T' d)) f'' (zipCtxSL z')).
Defined.
Implicit Arguments zipCtxSLComp [D G T C n GL GL' f].

Definition zipCtxSLComp' D G T C n GL GR (z:ZipCtx D G (fun d g=>forall x:T d g,C d (existT _ g x)) n GL GR)
GL' (f:forall d,GL' d->GL d) := zipCtxSLComp _ (zipCtxComp z GL' f).
Implicit Arguments zipCtxSLComp' [D G T C n GL GR].

Lemma zipCtxSLCompRewr D G T C n GL GR GL' (f:forall d,GL' d->GL d)
	(zc:ZipCtxComp D G (fun d g=>forall x:T d g,C d (existT _ g x)) n GL' (fun d g=>GR d (f d g)))
	(P:forall G',(forall d,G' d->sigT (T d))->Type)
: P (zc_G' (zipCtxSLComp GR zc)) (zc_f' (zipCtxSLComp GR zc))->
P (fun d=>sigT (fun g=>T d (zc_f' zc d g))) (fun d g=>existT _ (zc_f' zc d (projT1 g)) (projT2 g)).
	destruct zc.
	exact (fun p=>p).
Qed.
Implicit Arguments zipCtxSLCompRewr [D G T C n GL GR GL' f].

Lemma zipCtxSSLCompEq D G T C n GL T' GR GL' (f:forall d,GL' d->GL d)
	(zc:ZipCtxComp D G (fun d g=>forall x:T d g,C d (existT _ g x)) n
		(fun d=>sigT (fun g=>T' d (f d g)))
		(fun d g=>GR d (existT _ (f d (projT1 g)) (projT2 g))))
: zipCtxSComp (zipCtxSLComp GR zc) = zipCtxSLComp (fun d g=>forall x,GR d (existT _ g x)) (zipCtxSComp zc).
	simpl in zc.
	destruct zc.
	reflexivity.
Qed.

Lemma zipCtxCompSLEq D G T C n GL GR (z:ZipCtx D G (fun d g=>forall x:T d g,C d (existT _ g x)) n GL GR) :
forall GL' f,zipCtxComp (zipCtxSL z) GL' f = zipCtxSLComp' z GL' f.
	induction z as [| ? ? ? T'] using zipCtxInd;intros.

	reflexivity.

	simpl zipCtxSL.
	rewrite zipCtxCompSEq.
	unfold zipCtxSComp'.
	rewrite H.
	unfold zipCtxSLComp'.
	rewrite zipCtxCompSEq.
	rewrite zipCtxSSLCompEq.
	reflexivity.
Qed.

(* Context extension *)

Inductive ExtCtx D GL : nat->(D->Type)->Type :=
	extCtxO : ExtCtx D GL O GL |
	extCtxS n G : ExtCtx D GL n G->forall T:forall d,G d->Type,ExtCtx D GL (S n) (fun d=>sigT (T d)).
Implicit Arguments extCtxS [D GL n G].

Definition extCtxOInv D GL G (xg:ExtCtx D GL O G) (P:forall n G,ExtCtx D GL n G->Type)
	(xgO:P O GL (extCtxO D GL))
: P _ _ xg := match xg in ExtCtx _ _ zro _ return (O = zro)->P _ _ xg with
	extCtxO => fun _=>xgO |
	extCtxS _ _ _ _ => fun e=>match O_S _ e with end
end (eq_refl _).
Implicit Arguments extCtxOInv [D GL G].

Definition extCtxSInv D GL n G (xg:ExtCtx D GL (S n) G) : forall (P:forall n G,ExtCtx D GL n G->Type)
	(xgS:forall G (xg:ExtCtx D GL n G) T,P _ _ (extCtxS xg T))
,P _ _ xg.
	refine (match xg as xg in ExtCtx _ _ Sn _ return (Sn = S n)->forall P,_->P _ _ xg with
		extCtxO => fun e=>match O_S _ e with end |
		extCtxS _ _ xg0 _ => fun e _ xgS=>_
	end (eq_refl _)).
	exact (match eq_sym (Sinj e) return _ with eq_refl => xgS _ end xg0 _).
Defined.
Implicit Arguments extCtxSInv [D GL n G].

Definition extCtxInd D GL (P:forall n G,ExtCtx D GL n G->Type)
	(xgO:P _ _ (extCtxO D GL))
	(xgS:forall n,(forall G (xg:ExtCtx D GL n G),P _ _ xg)->
		forall G (xg:ExtCtx D GL n G) T,P _ _ (extCtxS xg T))
: forall n G (xg:ExtCtx D GL n G),P _ _ xg.
	refine (fix extCtxInd n := match n with
		O => fun _ xg=>_ |
		S _ => fun G xg=>_
	end).

	exact (extCtxOInv xg _ xgO).

	exact (extCtxSInv xg _ (xgS _ (extCtxInd _))).
Defined.
Implicit Arguments extCtxInd [D GL n G].

Inductive ExtCtxComp D GL n G : Type := mkExtCtxComp G' (f':forall d,G' d->G d) (xg':ExtCtx D GL n G').
Implicit Arguments mkExtCtxComp [D GL n G].

Definition xc_G' D GL n G (xc:ExtCtxComp D GL n G) := match xc with mkExtCtxComp G' _ _ => G' end.
Implicit Arguments xc_G' [D GL n G].

Definition xc_f' D GL n G (xc:ExtCtxComp D GL n G) : forall d,xc_G' xc d->G d := match xc with mkExtCtxComp _ f' _ => f' end.
Implicit Arguments xc_f' [D GL n G].

Definition extCtxComp D GL n G (xg:ExtCtx D GL n G) GL' (f:forall d,GL' d->GL d) : ExtCtxComp D GL' n G.
	revert n G xg.
	refine (fix extCtxComp n G xg := match xg in ExtCtx _ _ n G return ExtCtxComp D GL' n G with
		extCtxO => _ |
		extCtxS _ _ xg0 _ => _
	end).

	apply (mkExtCtxComp GL' f).
	apply extCtxO.

	exact (match extCtxComp _ _ xg0 with mkExtCtxComp G' f' xg' => mkExtCtxComp _
		(fun d (g:sigT (fun g=>T d (f' d g)))=>existT _ (f' d (projT1 g)) (projT2 g)) (extCtxS xg' _)
	end).
Defined.
Implicit Arguments extCtxComp [D GL n G].

Definition extCtxSComp D GL n G (xc:ExtCtxComp D GL n G) T :
ExtCtxComp D GL (S n) (fun d=>sigT (T d)) := match xc with mkExtCtxComp _ f xg =>
	mkExtCtxComp _ (fun d (g:sigT (fun g=>T d (f d g)))=>existT _ (f d (projT1 g)) (projT2 g)) (extCtxS xg _)
end.
Implicit Arguments extCtxSComp [D GL n G].

Definition extCtxSComp' D GL n G (xg:ExtCtx D GL n G) GL' f T : ExtCtxComp D GL' (S n) (fun d=>sigT (T d))
:= extCtxSComp (extCtxComp xg GL' f) T.
Implicit Arguments extCtxSComp' [D GL n G].

Lemma extCtxCompSEq D GL n G (xg:ExtCtx D GL n G) T GL' f : extCtxComp (extCtxS xg T) GL' f = extCtxSComp' xg GL' f T.
	reflexivity.
Qed.
Implicit Arguments extCtxCompSEq [D GL n G T GL' f].

Lemma extCtxSCompRewr D GL n G (xc:ExtCtxComp D GL n G) T (P:forall G',(forall d,G' d->sigT (T d))->Type)
: P (xc_G' (extCtxSComp xc T)) (xc_f' (extCtxSComp xc T))->
P _ (fun d (g:sigT (fun g=>T d (xc_f' xc d g)))=>existT _ (xc_f' xc d (projT1 g)) (projT2 g)).
	destruct xc.
	exact (fun p=>p).
Qed.
Implicit Arguments extCtxSCompRewr [D GL n G].
