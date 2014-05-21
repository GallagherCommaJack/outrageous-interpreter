Require Import EqStuff.
Require Import Le Lt.

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

Inductive CtxS D : (D->Type)->Type :=
	empCtxS : CtxS D (fun d=>unit) |
	extCtxS G : CtxS D G->forall T:forall d,G d->Type,CtxS D (fun d=>sigT (T d)).
Implicit Arguments CtxS [D].
Implicit Arguments extCtxS [D G].

Inductive Ctx D : Type := ctx (G:D->Type) (s:CtxS G).
Implicit Arguments ctx [D G].

Definition ctxTp D (G:Ctx D) := match G with ctx G _ => G end.
Implicit Arguments ctxTp [D].
Coercion ctxTp : Ctx >-> Funclass.

Definition ctxSc D (G:Ctx D) : CtxS G := match G with ctx _ s => s end.
Implicit Arguments ctxSc [D].

Definition empCtx D := ctx (empCtxS D).
Definition extCtx D (G:Ctx D) (T:forall d,G d->Type) := ctx (extCtxS (ctxSc G) T).
Implicit Arguments extCtx [D].

Definition CtxNEmp D (G:Ctx D) := match G with
	ctx _ empCtxS => False |
	ctx _ (extCtxS _ _ _) => True
end.
Implicit Arguments CtxNEmp [D].

Definition ctxInit D G := match G with
	ctx _ empCtxS => empCtx D |
	ctx _ (extCtxS _ s _) => ctx s
end.
Implicit Arguments ctxInit [D].

Definition ctxTop D (G:Ctx D) : forall d,ctxInit G d->Type.
	destruct G.
	destruct s;simpl.

	exact (fun d g=>unit).

	exact T.
Defined.
Implicit Arguments ctxTop [D].

Definition extCtxUnfold D (G:Ctx D) : forall ne:CtxNEmp G,G = extCtx (ctxInit G) (ctxTop G).
	destruct G.
	destruct s;simpl;intro.

	exact (match ne with end).

	reflexivity.
Defined.
Implicit Arguments extCtxUnfold [D G].

Definition extCtxInj D (G1 G2:Ctx D) : forall T1 T2 (e:extCtx G1 T1 = extCtx G2 T2),
existT (fun G:Ctx D=>forall d,G d->Type) G1 T1 = existT _ G2 T2.
	destruct G1 as (G1,s1).
	destruct G2 as (G2,s2).
	simpl.
	intros.
	exact (tr (fun Gx=>_ = existT _ _ (ctxTop Gx)) e (eq_refl _)).
Defined.
Implicit Arguments extCtxInj [D G1 G2 T1 T2].

Inductive AtCtx D : forall G:Ctx D,nat->(forall d,G d->Type)->Type :=
	topCtx G T : AtCtx D (extCtx G T) O (fun d g=>T d (projT1 g)) |
	popCtx G n T : AtCtx D G n T->forall T',AtCtx D (extCtx G T') (S n) (fun d g=>T d (projT1 g)).
Implicit Arguments AtCtx [D].
Implicit Arguments topCtx [D].
Implicit Arguments popCtx [D G n T].

Definition topCtxInv_ext D (G:Ctx D) T' T (a:AtCtx (extCtx G T') O T) (P:forall G T' n T,AtCtx (extCtx G T') n T->Type)
	(top:P _ _ _ _ (topCtx G T'))
: P _ _ _ _ a.
	pose (P' Gx n T (a:AtCtx Gx n T) := forall ne:CtxNEmp Gx,
		P _ _ _ _ (projT2 (tr (fun G=>sigT (AtCtx G n)) (extCtxUnfold ne) (existT _ _ a)))).
	assert (Peq := match G as G return forall T' T a,P G T' O T a = P (ctx (ctxSc G)) _ _ _ a
		with ctx _ _ => fun _ _ _=>eq_refl _ end T').
	apply (tr (fun C=>C) (eq_sym (Peq _ _))).
	generalize I.
	change (P' _ _ _ a).
	refine (match a as a in AtCtx Gx zro T return (O = zro)->(extCtx G T' = Gx)->P' _ _ _ a with
		topCtx _ _ => fun Hn HG=>_ |
		popCtx _ _ _ _ _ => fun e=>match O_S _ e with end
	end (eq_refl _) (eq_refl _)).
	apply (tr (fun GT'=>P' _ _ _ (topCtx (projT1 GT') (projT2 GT'))) (extCtxInj HG)).
	simpl.
	intro.
	simpl.
	exact (tr (fun C=>C) (Peq _ _) top).
Defined.
Implicit Arguments topCtxInv_ext [D G T' T].

Definition topCtxInv_extEq D (G:Ctx D) T P := match G
return forall T top,topCtxInv_ext (topCtx G T) P top = top
	with ctx _ _ => fun _ _=>eq_refl _ end T.
Implicit Arguments topCtxInv_extEq [D G T].

Definition popCtxInv_ext D (G:Ctx D) T' n T (a:AtCtx (extCtx G T') (S n) T) (P:forall G T' n T,AtCtx (extCtx G T') n T->Type)
	(pop:forall T (a:AtCtx G n T),P _ _ _ _ (popCtx a T'))
: P _ _ _ _ a.
	pose (P' Gx n T (a:AtCtx Gx n T) := forall ne:CtxNEmp Gx,
		P _ _ _ _ (projT2 (tr (fun G=>sigT (AtCtx G n)) (extCtxUnfold ne) (existT _ _ a)))).
	assert (Peq := match G as G return forall T' T a,P G T' (S n) T a = P (ctx (ctxSc G)) _ _ _ a
		with ctx _ _ => fun _ _ _=>eq_refl _ end T').
	apply (tr (fun C=>C) (eq_sym (Peq _ _))).
	generalize I.
	change (P' _ _ _ a).
	refine (match a as a in AtCtx Gx Sn T return (Sn = S n)->(extCtx G T' = Gx)->P' _ _ _ a with
		topCtx _ _ => fun e=>match O_S _ e with end |
		popCtx _ _ T0 a0 _ => fun Hn HG=>_
	end (eq_refl _) (eq_refl _)).
	revert T0 a0.
	apply (tr (fun _=>_) (eq_sym (Sinj Hn))).
	apply (tr (fun GT'=>forall T (a:AtCtx _ _ T),P' _ _ _ (popCtx a (projT2 GT'))) (extCtxInj HG)).
	simpl.
	intros ? ? ?.
	simpl.
	exact (tr (fun C=>C) (Peq _ _) (pop _ _)).
Defined.
Implicit Arguments popCtxInv_ext [D G T' n T].

Definition popCtxInv_extEq D (G:Ctx D) T' n T a P := match G
return forall T' T (a:AtCtx G n T) pop,popCtxInv_ext (popCtx a T') P pop = pop T a
	with ctx _ _ => fun _ _ _ _=>eq_refl _ end T' T a.
Implicit Arguments popCtxInv_extEq [D G T' n T].

Fixpoint ctxProj D (G:Ctx D) n T (a:AtCtx G n T) d : forall g,T d g := match a with
	topCtx _ _ => @projT2 _ _ |
	popCtx _ _ _ a _ => fun g=>ctxProj _ _ _ _ a _ (projT1 g)
end.
Implicit Arguments ctxProj [D G n T].

Definition atCtxEta D (G:Ctx D) n T (a:AtCtx G n T) : AtCtx G n (fun d g=>T d g) := match a with
	topCtx _ _ => topCtx _ _ |
	popCtx _ _ _ a _ => popCtx a _
end.
Implicit Arguments atCtxEta [D G n T].

Lemma ctxProj_Eta D (G:Ctx D) n T (a:AtCtx G n T) : ctxProj (atCtxEta a) = fun d g=>ctxProj a d g.
	destruct a;reflexivity.
Qed.

(* Weaken for a new type-level context entry *)

Fixpoint ctxSBumpD D (F G:D->Type) (s:CtxS G) : CtxS (fun d:sigT F=>G (projT1 d)) := match s with
	empCtxS => empCtxS _ |
	extCtxS _ s _ => extCtxS (ctxSBumpD _ _ _ s) _
end.
Implicit Arguments ctxSBumpD [D G].

Definition ctxBumpD D (F:D->Type) (G:Ctx D) := ctx (ctxSBumpD F (ctxSc G)).
Implicit Arguments ctxBumpD [D].

Fixpoint atBumpD D (F:D->Type) G n T (a:AtCtx G n T) :
AtCtx (ctxBumpD F G) n (fun d=>T (projT1 d)) := match a with
	topCtx G _ => topCtx (ctxBumpD F G) _ |
	popCtx _ _ _ a _ => popCtx (atBumpD _ _ _ _ _ a) _
end.
Implicit Arguments atBumpD [D G n T].

Lemma ctxProj_BumpD D F (G:Ctx D) n T (a:AtCtx G n T) : ctxProj (atBumpD F a) = fun d=>ctxProj a (projT1 d).
	induction a.

	reflexivity.

	simpl.
	rewrite IHa.
	reflexivity.
Qed.

(* Iterated context extension *)

Inductive ExtCtx D GL : nat->Ctx D->Type :=
	extOCtx : ExtCtx D GL O GL |
	extSCtx n G : ExtCtx D GL n G->forall T:forall d,G d->Type,ExtCtx D GL (S n) (extCtx G T).
Implicit Arguments ExtCtx [D].
Implicit Arguments extOCtx [D].
Implicit Arguments extSCtx [D GL n G].

Definition extOCtxInv D (GL G:Ctx D) (xg:ExtCtx GL O G) (P:forall n G,ExtCtx GL n G->Type)
	(xgO:P O GL (extOCtx GL))
: P _ _ xg := match xg in ExtCtx _ zro _ return (O = zro)->P _ _ xg with
	extOCtx => fun _=>xgO |
	extSCtx _ _ _ _ => fun e=>match O_S _ e with end
end (eq_refl _).
Implicit Arguments extOCtxInv [D GL G].

Definition extSCtxInv D (GL:Ctx D) n G (xg:ExtCtx GL (S n) G) (P:forall n G,ExtCtx GL n G->Type)
	(xgS:forall G (xg:ExtCtx GL n G) T,P _ _ (extSCtx xg T))
: P _ _ xg.
	refine (match xg as xg in ExtCtx _ Sn _ return (Sn = S n)->P _ _ xg with
		extOCtx => fun e=>match O_S _ e with end |
		extSCtx _ _ xg0 _ => fun e=>_
	end (eq_refl _)).
	exact (match eq_sym (Sinj e) return _ with eq_refl => xgS _ end xg0 _).
Defined.
Implicit Arguments extSCtxInv [D GL n G].

(* Induction on the number of added entries *)
Definition extCtxNInd D (GL:Ctx D) (P:forall n G,ExtCtx GL n G->Type)
	(xgO:P _ _ (extOCtx GL))
	(xgS:forall n,(forall G (xg:ExtCtx GL n G),P _ _ xg)->
		forall G (xg:ExtCtx GL n G) T,P _ _ (extSCtx xg T))
: forall n G (xg:ExtCtx GL n G),P _ _ xg.
	refine (fix extCtxNInd n G := match n with
		O => fun xg=>_ |
		S _ => fun xg=>_
	end).

	exact (extOCtxInv xg _ xgO).

	exact (extSCtxInv xg _ (xgS _ (extCtxNInd _))).
Defined.
Implicit Arguments extCtxNInd [D GL n G].

Definition extSCtxInv_ext D (GL:Ctx D) n G T (xg:ExtCtx GL (S n) (extCtx G T)) (P:forall n G T,ExtCtx GL n (extCtx G T)->Type)
	(xgS:forall xg:ExtCtx GL n G,P _ _ _ (extSCtx xg T))
: P _ _ _ xg.
	pose (P' n Gx (xg:ExtCtx GL n Gx) := forall ne:CtxNEmp Gx,
		P _ _ _ (tr (ExtCtx GL n) (extCtxUnfold ne) xg)).
	assert (Peq := match G as G return forall T xg,P (S n) G T xg = P _ (ctx (ctxSc G)) _ xg
		with ctx _ _ => fun _ _=>eq_refl _ end T).
	apply (tr (fun C=>C) (eq_sym (Peq _))).
	generalize I.
	change (P' _ _ xg).
	refine (match xg as xg in ExtCtx _ Sn Gx return (Sn = S n)->(extCtx G T = Gx)->P' _ _ xg with
		extOCtx => fun e=>match O_S _ e with end |
		extSCtx _ _ xg0 _ => fun Hn HG=>_
	end (eq_refl _) (eq_refl _)).
	revert xg0.
	apply (tr (fun _=>_) (eq_sym (Sinj Hn))).
	apply (tr (fun GT=>forall xg,P' _ _ (extSCtx xg (projT2 GT))) (extCtxInj HG)).
	simpl.
	intros ? ?.
	simpl.
	exact (tr (fun C=>C) (Peq _) (xgS _)).
Defined.
Implicit Arguments extSCtxInv_ext [D GL n G T].

Definition extSCtxInv_extEq D (GL:Ctx D) n G T xg P := match G
return forall T (xg:ExtCtx GL n G) xgS,extSCtxInv_ext (extSCtx xg T) P xgS = xgS xg
	with ctx _ _ => fun _ _ _=>eq_refl _ end T xg.
Implicit Arguments extSCtxInv_extEq [D GL n G T].

Lemma extAtCtxInd D (GL:Ctx D) P (C:forall n G P',ExtCtx (extCtx GL P) n G->AtCtx G n P'->Type)
	(xgO:C _ _ _ (extOCtx _) (topCtx GL P))
	(xgS:forall n G P' xg (a:AtCtx G n P') T,C _ _ _ xg a->C _ _ _ (extSCtx xg T) (popCtx a T))
n G (xg:ExtCtx (extCtx GL P) n G) : forall P' (a:AtCtx G n P'),C _ _ _ xg a.
	induction xg;intros.

	clear xgS.
	assert (z : IsO O).
		exact I.
	revert z C xgO.
	apply (topCtxInv_ext a (fun GL P n _ a=>forall (z:IsO n)
		(C:forall n G P',ExtCtx (extCtx GL P) n G->AtCtx G n P'->Type) xgO,
		C _ _ _ (extOCtx _) (tr (fun n=>AtCtx _ n _) (OUnfold z) a))).
	simpl.
	intros _ ? ?.
	exact xgO.

	assert (nz : IsS (S n)).
		exact I.
	revert nz xg IHxg.
	apply (popCtxInv_ext a (fun _ _ n _ a=>forall (nz:IsS n) xg (IHxg:forall P' a,C _ _ _ xg a),
		C _ _ _ (extSCtx xg _) (tr (fun n=>AtCtx _ n _) (SUnfold nz) a))).
	clear P' a.
	simpl.
	intros P' ? _ ? ?.
	apply xgS.
	apply IHxg.
Qed.

Inductive ExtCtxComp D GL' n G : Type := mkExtCtxComp (G':Ctx D) (xg':ExtCtx GL' n G') (f':forall d,G' d->G d).
Implicit Arguments ExtCtxComp [D].
Implicit Arguments mkExtCtxComp [D GL' n G G'].

Definition xc_G' D (GL':Ctx D) n G (xc:ExtCtxComp GL' n G) := match xc with mkExtCtxComp G' _ _ => G' end.
Implicit Arguments xc_G' [D GL' n G].

Definition xc_xg' D (GL':Ctx D) n G (xc:ExtCtxComp GL' n G) : ExtCtx GL' n (xc_G' xc) := match xc with mkExtCtxComp _ xg' _ => xg' end.
Implicit Arguments xc_xg' [D GL' n G].

Definition xc_f' D (GL':Ctx D) n G (xc:ExtCtxComp GL' n G) : forall d,xc_G' xc d->G d := match xc with mkExtCtxComp _ _ f' => f' end.
Implicit Arguments xc_f' [D GL' n G].

Definition extCtxComp D GL n G (xg:ExtCtx GL n G) (GL':Ctx D) (f:forall d,GL' d->GL d) : ExtCtxComp GL' n G.
	revert n G xg.
	refine (fix extCtxComp n G xg := match xg in ExtCtx _ n G return ExtCtxComp GL' n G with
		extOCtx => _ |
		extSCtx _ _ xg0 T => _
	end).

	exact (mkExtCtxComp (extOCtx _) f).

	pose (xc := extCtxComp _ _ xg0).
	exact (mkExtCtxComp (extSCtx (xc_xg' xc) _)
		(fun d (g:sigT (fun g=>T d (_ d g)))=>existT _ (xc_f' xc d (projT1 g)) (projT2 g))).
Defined.
Implicit Arguments extCtxComp [D GL n G].

Definition xgBumpG D (GL:Ctx D) P l G (xg:ExtCtx GL l G) := extCtxComp xg (extCtx GL P) (fun d=>@projT1 _ _).
Implicit Arguments xgBumpG [D GL l G].

Definition ctxBumpG D (GL:Ctx D) P l G (xg:ExtCtx GL l G) := xc_G' (xgBumpG P xg).
Implicit Arguments ctxBumpG [D GL l G].

Definition elBumpG D (GL:Ctx D) P l G (xg:ExtCtx GL l G) T (F:forall d (g:G d),T d g) d (g:ctxBumpG P xg d) :=
	F d (xc_f' (xgBumpG P xg) d g).
Implicit Arguments elBumpG [D GL l G T].

Definition atBumpGLo D (GL:Ctx D) P l G n T (xg:ExtCtx GL l G) (a:AtCtx G n T) (Ho:n < l) : AtCtx (ctxBumpG P xg) n (elBumpG P xg T).
	revert l Ho xg.
	induction a;intro;(destruct l;intro;[exact (match lt_n_O _ Ho with end) |]);intro.

	apply (extSCtxInv_ext xg).
	clear xg.
	intro.
	unfold ctxBumpG.
	simpl.
	apply topCtx.

	revert T a IHa.
	apply (extSCtxInv_ext xg).
	clear xg.
	intros.
	change (AtCtx (extCtx (ctxBumpG P xg) (elBumpG P xg T')) (S n) (fun d g=>elBumpG P xg T d (projT1 g))).
	apply popCtx.
	exact (IHa _ (lt_S_n _ _ Ho) xg).
Defined.
Implicit Arguments atBumpGLo [D GL l G n T].

Definition atBumpGHi D (GL:Ctx D) P l G n T (xg:ExtCtx GL l G) (a:AtCtx G n T) (Ho:l <= n) : AtCtx (ctxBumpG P xg) (S n) (elBumpG P xg T).
	revert n Ho T a.
	induction xg as [| l ? ? ? T'].

	intros.
	unfold ctxBumpG.
	simpl.
	apply (popCtx a).

	intro.
	destruct n.
		intro.
		exact (match le_Sn_O _ Ho with end).
	intros.
	revert xg IHxg.
	apply (popCtxInv_ext a (fun _ _ _ _ _=>_)).
	clear T a.
	intros.
	change (AtCtx (extCtx (ctxBumpG P xg) (elBumpG P xg T')) (S (S n)) (fun d g=>elBumpG P xg T d (projT1 g))).
	apply popCtx.
	exact (IHxg _ (le_S_n _ _ Ho) _ a).
Defined.
Implicit Arguments atBumpGHi [D GL l G n T].

Lemma ctxProj_BumpGLo D (GL:Ctx D) P l G n T (xg:ExtCtx GL l G) (a:AtCtx G n T) (Ho:n < l) :
ctxProj (atBumpGLo P xg a Ho) = elBumpG P xg (ctxProj a).
	revert l Ho xg.
	induction a;intro;(destruct l;intro;[exact (match lt_n_O _ Ho with end) |]);intro.

	revert Ho.
	apply (extSCtxInv_ext xg).
	clear xg.
	intros.
	simpl.
	rewrite extSCtxInv_extEq.
	reflexivity.

	revert T a IHa Ho.
	apply (extSCtxInv_ext xg).
	clear xg.
	intros.
	simpl.
	rewrite extSCtxInv_extEq.
	change (ctxProj (popCtx (atBumpGLo P xg a (lt_S_n _ _ Ho)) (elBumpG P xg T')) =
		elBumpG P (extSCtx xg T') (ctxProj (popCtx a T'))).
	simpl.
	rewrite IHa.
	reflexivity.
Qed.

Lemma ctxProj_BumpGHi D (GL:Ctx D) P l G n T (xg:ExtCtx GL l G) (a:AtCtx G n T) (Ho:l <= n) :
ctxProj (atBumpGHi P xg a Ho) = elBumpG P xg (ctxProj a).
	revert n Ho T a.
	induction xg as [| l ? ? ? T'].

	intros.
	reflexivity.

	intro.
	destruct n.
		intro.
		exact (match le_Sn_O _ Ho with end).
	intros.
	revert xg IHxg Ho.
	apply (popCtxInv_ext a).
	clear T a.
	intros.
	simpl.
	rewrite popCtxInv_extEq.
	change (ctxProj (popCtx (atBumpGHi P xg a (le_S_n _ _ Ho)) (elBumpG P xg T')) =
		elBumpG P (extSCtx xg T') (ctxProj (popCtx a T'))).
	simpl.
	rewrite IHxg.
	reflexivity.
Qed.

Definition xgSubst D (GL:Ctx D) P l G (xg:ExtCtx (extCtx GL P) l G) (p:forall d g,P d g) :=
	extCtxComp xg GL (fun d g=>existT _ g (p d g)).
Implicit Arguments xgSubst [D GL P l G].

Definition ctxSubst D (GL:Ctx D) P l G (xg:ExtCtx (extCtx GL P) l G) p := xc_G' (xgSubst xg p).
Implicit Arguments ctxSubst [D GL P l G].

Definition elSubst D (GL:Ctx D) P l G (xg:ExtCtx (extCtx GL P) l G) T (F:forall d (g:G d),T d g) p
	d (g:ctxSubst xg p d) := F d (xc_f' (xgSubst xg p) d g).
Implicit Arguments elSubst [D GL P l G T].

Definition atSubstLt D (GL:Ctx D) P l G n T (xg:ExtCtx (extCtx GL P) l G) (a:AtCtx G n T) (Ho:n < l) p :
AtCtx (ctxSubst xg p) n (elSubst xg T p).
	revert l Ho xg.
	induction a;intro;(destruct l;intro;[exact (match lt_n_O _ Ho with end) |]);intro.

	apply (extSCtxInv_ext xg).
	clear xg.
	intro.
	unfold ctxSubst.
	simpl.
	apply topCtx.

	revert T a IHa.
	apply (extSCtxInv_ext xg).
	clear xg.
	intros.
	change (AtCtx (extCtx (ctxSubst xg p) (elSubst xg T' p)) (S n) (fun d g=>elSubst xg T p d (projT1 g))).
	apply popCtx.
	exact (IHa _ (lt_S_n _ _ Ho) xg).
Defined.
Implicit Arguments atSubstLt [D GL P l G n T].

Definition atSubstGt D (GL:Ctx D) P l G n T (xg:ExtCtx (extCtx GL P) l G) (a:AtCtx G (S n) T) (Ho:l <= n) p :
AtCtx (ctxSubst xg p) n (elSubst xg T p).
	revert n Ho T a.
	induction xg as [| l ? ? ? T'].

	intros.
	revert p.
	apply (popCtxInv_ext a (fun _ _ _ _ _=>_)).
	clear T a.
	intros.
	exact (atCtxEta a).

	intro.
	destruct n.
		intro.
		exact (match le_Sn_O _ Ho with end).
	intros.
	revert xg IHxg.
	apply (popCtxInv_ext a (fun _ _ _ _ _=>_)).
	clear T a.
	intros.
	change (AtCtx (extCtx (ctxSubst xg p) (elSubst xg T' p)) (S n) (fun d g=>elSubst xg T p d (projT1 g))).
	apply popCtx.
	exact (IHxg _ (le_S_n _ _ Ho) _ a).
Defined.
Implicit Arguments atSubstGt [D GL P l G n T].

Definition elMBumpG D (GL:Ctx D) P n G P' (xg:ExtCtx (extCtx GL P) n G) (a:AtCtx G n P')
(p:forall d g,P d g) : forall d g,P' d g.
	revert P' a.
	induction xg;intros ? ?.

	apply (topCtxInv_ext a (fun _ _ _ _ _=>_)).
	intros.
	apply p.

	apply (popCtxInv_ext a (fun _ _ _ _ _=>_)).
	clear P' a.
	intros P' ? ? ?.
	exact (IHxg _ a _ _).
Defined.
Implicit Arguments elMBumpG [D GL P n G P'].

Lemma ctxProj_SubstLt D (GL:Ctx D) P l G n T (xg:ExtCtx (extCtx GL P) l G) (a:AtCtx G n T) (Ho:n < l) p :
ctxProj (atSubstLt xg a Ho p) = elSubst xg (ctxProj a) p.
	revert l Ho xg.
	induction a;intro;(destruct l;intro;[exact (match lt_n_O _ Ho with end) |]);intro.

	revert Ho.
	apply (extSCtxInv_ext xg).
	clear xg.
	intros.
	simpl.
	rewrite extSCtxInv_extEq.
	reflexivity.

	revert T a IHa Ho.
	apply (extSCtxInv_ext xg).
	clear xg.
	intros.
	simpl.
	rewrite extSCtxInv_extEq.
	change (ctxProj (popCtx (atSubstLt xg a (lt_S_n _ _ Ho) p) (elSubst xg T' p)) =
		elSubst (extSCtx xg T') (ctxProj (popCtx a T')) p).
	simpl.
	rewrite IHa.
	reflexivity.
Qed.

Lemma ctxProj_SubstGt D (GL:Ctx D) P l G n T (xg:ExtCtx (extCtx GL P) l G) (a:AtCtx G (S n) T) (Ho:l <= n) p :
ctxProj (atSubstGt xg a Ho p) = elSubst xg (ctxProj a) p.
	revert n Ho T a.
	induction xg as [| l ? ? ? T'].

	intros.
	assert (nz : IsS (S n)).
		exact I.
	revert nz Ho p.
	apply (popCtxInv_ext a (fun GL P Sn T a=>forall (nz:IsS Sn) Ho p,
		ctxProj (atSubstGt (extOCtx _) (tr (fun n=>AtCtx (extCtx GL P) n T) (SUnfold nz) a) Ho p) =
		elSubst (extOCtx _) (ctxProj a) p)).
	simpl pred.
	simpl tr.
	clear T a.
	intros ? ? _ ? ?.
	simpl.
	rewrite popCtxInv_extEq.
	apply eq_trans with (1 := ctxProj_Eta _ _ _ _ a).
	reflexivity.

	intro.
	destruct n.
		intro.
		exact (match le_Sn_O _ Ho with end).
	intros.
	assert (nz : IsS (S (S n))).
		exact I.
	revert nz Ho p xg IHxg.
	apply (popCtxInv_ext a (fun G T' SSn T a=>forall (nz:IsS SSn) Ho p xg IHxg,
		ctxProj (atSubstGt (extSCtx xg T') (tr (fun n=>AtCtx (extCtx G T') n T) (SUnfold nz) a) Ho p) =
		elSubst (extSCtx xg T') (ctxProj a) p)).
	simpl pred.
	simpl tr.
	clear T a.
	intros ? ? _.
	intros.
	simpl.
	rewrite popCtxInv_extEq.
	change (ctxProj (popCtx (atSubstGt xg a (le_S_n _ _ Ho) p) (elSubst xg T' p)) =
		elSubst (extSCtx xg T') (ctxProj (popCtx a T')) p).
	simpl.
	rewrite IHxg.
	reflexivity.
Qed.

Lemma ctxProj_SubstEq D (GL:Ctx D) P n G P' (xg:ExtCtx (extCtx GL P) n G) (a:AtCtx G n P') p :
elSubst xg (elMBumpG xg a p) p = elSubst xg (ctxProj a) p.
	apply extAtCtxInd with (xg := xg) (a := a);clear n G P' xg a;intros;simpl.

	rewrite topCtxInv_extEq.
	reflexivity.

	rewrite popCtxInv_extEq.
	change ((fun d (g:ctxSubst (extSCtx xg T) p d)=>elSubst xg (elMBumpG xg a p) p d (projT1 g)) =
		(fun d g=>elSubst xg (ctxProj a) p d (projT1 g))).
	rewrite H.
	reflexivity.
Qed.

(* Stuff for substituting one variable for another. Probably should've called it atMBumpG. *)

Inductive AtCtxExt D (G:Ctx D) n' : Type := mkAtCtxExt T (a:AtCtx G n' T).
Implicit Arguments AtCtxExt [D].
Implicit Arguments mkAtCtxExt [D G n' T].

Definition ax_T D (G:Ctx D) n' (ax:AtCtxExt G n') := match ax with mkAtCtxExt T _ => T end.
Implicit Arguments ax_T [D G n'].

Definition ax_a D (G:Ctx D) n' (ax:AtCtxExt G n') : AtCtx G n' (ax_T ax) := match ax with mkAtCtxExt _ a => a end.
Implicit Arguments ax_a [D G n'].

Fixpoint atCtxExt D (GL:Ctx D) l G n T (xg:ExtCtx GL l G) (a:AtCtx GL n T) : AtCtxExt G (l + n) := match xg with
	extOCtx => mkAtCtxExt a |
	extSCtx _ _ xg T' => mkAtCtxExt (popCtx (ax_a (atCtxExt _ _ _ _ _ _ xg a)) T')
end.
Implicit Arguments atCtxExt [D GL l G n T].

Definition atCtxExtTEq D (GL:Ctx D) a b P G (b':AtCtx GL b P) (xg:ExtCtx (extCtx GL P) a G) :
forall P' (a':AtCtx G a P'),ax_T (atCtxExt xg (popCtx b' P)) = P'.
	induction xg as [| a];intros ? ?;simpl.

	apply (topCtxInv_ext a' (fun _ _ _ _ _=>_)).
	reflexivity.

	revert xg IHxg.
	apply (popCtxInv_ext a' (fun _ _ _ _ _=>_)).
	clear P' a'.
	intros P' a' ? ?.
	apply (tr (fun _=>_) (IHxg _ a')).
	reflexivity.
Defined.
Implicit Arguments atCtxExtTEq [D GL a b P G P'].

Lemma ctxProj_Ext D (GL:Ctx D) a b P G P' (b':AtCtx GL b P) (xg:ExtCtx (extCtx GL P) a G) (a':AtCtx G a P') :
ctxProj (tr (AtCtx G _) (atCtxExtTEq b' xg a') (ax_a (atCtxExt xg (popCtx b' P)))) = elMBumpG xg a' (ctxProj b').
	apply extAtCtxInd with (xg := xg) (a := a');clear a G P' xg a';[| intros a ? ? ? a' ? ?];simpl.

	rewrite topCtxInv_extEq.
	rewrite topCtxInv_extEq.
	reflexivity.

	rewrite popCtxInv_extEq.
	rewrite popCtxInv_extEq.
	rewrite <- H.
	rewrite <- (atCtxExtTEq b' xg a').
	reflexivity.
Qed.
