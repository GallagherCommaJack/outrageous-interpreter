Require Import Utils.

Module Type CTXTYP.

Parameter Tp : Type->Type.

Parameter tpTp : forall G,Tp G->G->Type.
Implicit Arguments tpTp [G].
Coercion tpTp : Tp >-> Funclass.

Parameter tpMap : forall G G' (f:G'->G),Tp G->Tp G'.
Implicit Arguments tpMap [G G'].

Parameter tpMapEq : forall G G' (f:G'->G) (T:Tp G),(fun g=>T (f g)) = tpMap f T.
Implicit Arguments tpMapEq [G G'].

End CTXTYP.

Module Context (Import Typ : CTXTYP).

(* Semantic contexts *)

Inductive CtxS : Type->Type :=
	empCtxS : CtxS unit |
	extCtxS G : CtxS G->forall T:Tp G,CtxS (sigT T).
Implicit Arguments extCtxS [G].

Inductive Ctx : Type := ctx G (s:CtxS G).
Implicit Arguments ctx [G].

Definition ctxTp G := match G with ctx G _ => G end.
Coercion ctxTp : Ctx >-> Sortclass.

Definition ctxSc (G:Ctx) : CtxS G := match G with ctx _ s => s end.

Definition empCtx := ctx empCtxS.
Definition extCtx G T := ctx (extCtxS (ctxSc G) T).

Definition IsExtCtx G := match G with
	ctx _ empCtxS => False |
	ctx _ (extCtxS _ _ _) => True
end.

Definition ctxInit G := match G with
	ctx _ empCtxS => empCtx |
	ctx _ (extCtxS _ s _) => ctx s
end.

Definition ctxTop G : forall ne:IsExtCtx G,Tp (ctxInit G).
	destruct G.
	destruct s;simpl;intro.

	destruct ne.

	exact T.
Defined.
Implicit Arguments ctxTop [G].

Fixpoint ctxLenS G (s:CtxS G) := match s with
	empCtxS => O |
	extCtxS _ s _ => S (ctxLenS _ s)
end.
Implicit Arguments ctxLenS [G].

Definition ctxLen G := ctxLenS (ctxSc G).

Definition extCtxUnfold G : forall ne:IsExtCtx G,G = extCtx (ctxInit G) (ctxTop ne).
	destruct G.
	destruct s;simpl;intro.

	destruct ne.

	reflexivity.
Defined.
Implicit Arguments extCtxUnfold [G].

Definition extCtxInj G1 G2 : forall T1 T2 (e:extCtx G1 T1 = extCtx G2 T2),
existT Tp G1 T1 = existT Tp G2 T2.
	destruct G1 as (G1,s1).
	destruct G2 as (G2,s2).
	simpl.
	intros.
	generalize I.
	apply (tr (fun Gx=>forall ne:IsExtCtx Gx,_ = existT _ _ (ctxTop ne)) e).
	simpl.
	intro.
	reflexivity.
Defined.
Implicit Arguments extCtxInj [G1 G2 T1 T2].

(* Strongly typed de Bruijn indexes *)

(*
Inductive AtCtx : forall G:Ctx,nat->Tp G->Type :=
	topCtx G T : AtCtx (extCtx G T) O (tpMap (@projT1 _ _) T) |
	popCtx G n T : AtCtx G n T->forall T',AtCtx (extCtx G T') (S n) (tpMap (@projT1 _ _) T).
*)

Inductive PopCtx G (T':G->Type) P : Tp (sigT T')->Type :=
	mkPopCtx T : P T->PopCtx G T' P (tpMap (@projT1 _ _) T).
Implicit Arguments PopCtx [G].
Implicit Arguments mkPopCtx [G].

Fixpoint AtCtxS G (s:CtxS G) n := match s in CtxS G return forall T:Tp G,Type with
	empCtxS => fun T=>Empty_set |
	extCtxS _ s T' => match n with
		O => eq (tpMap (@projT1 _ _) T') |
		S n => PopCtx T' (AtCtxS _ s n)
	end
end.
Implicit Arguments AtCtxS [G].

Definition AtCtx G := AtCtxS (ctxSc G).

Definition topCtx G T : AtCtx (extCtx G T) O (tpMap (@projT1 _ _) T) := eq_refl _.

Definition popCtx G n T (a:AtCtx G n T) T' : AtCtx (extCtx G T') (S n) (tpMap (@projT1 _ _) T) :=
	mkPopCtx _ _ _ a.
Implicit Arguments popCtx [G n T].

Definition atCtxIndS (P:forall G n T,AtCtx G n T->Type)
	(top:forall G T,P _ _ _ (topCtx G T))
	(pop:forall G n T (a:AtCtx G n T) (IHa:P _ _ _ a) T',P _ _ _ (popCtx a T'))
: forall G (s:CtxS G) n T (a:AtCtx (ctx s) n T),P _ _ _ a.
	refine (fix atCtxIndS G s n := match s in CtxS G return forall T (a:AtCtx (ctx s) n T),P _ _ _ a with
		empCtxS => _ |
		extCtxS _ s _ => _
	end);clear G s;simpl;intro.

	intro.
	destruct a.

	destruct n;unfold AtCtx;simpl;intro;destruct a.
		exact (top (ctx s0) _).

		exact (pop _ _ _ _ (atCtxIndS _ _ _ _ _) _).
Defined.

Definition AtCtx_rect (P:forall G n T,AtCtx G n T->Type)
	(top:forall G T,P _ _ _ (topCtx G T))
	(pop:forall G n T (a:AtCtx G n T) (IHa:P _ _ _ a) T',P _ _ _ (popCtx a T'))
G := match G return forall n T (a:AtCtx G n T),P _ _ _ a with ctx _ s => atCtxIndS P top pop _ s end.
Implicit Arguments AtCtx_rect [G n T].

Inductive ExAtCtx G n : Type := exAtCtx T (a:AtCtx G n T).
Implicit Arguments exAtCtx [G n T].

Definition xa_T G n (xa:ExAtCtx G n) := match xa with exAtCtx T _ => T end.
Implicit Arguments xa_T [G n].

Definition xa_a G n (xa:ExAtCtx G n) : AtCtx G n (xa_T xa) := match xa with exAtCtx _ a => a end.
Implicit Arguments xa_a [G n].

Definition atCtxUniq G n T1 (a1:AtCtx G n T1) : forall T2 (a2:AtCtx G n T2),
exAtCtx a1 = exAtCtx a2.
	induction a1 as [| ? ? T1] using AtCtx_rect;intros.

	destruct a2.
	reflexivity.

	change (PopCtx T' (AtCtx G n) T2) in a2.
	destruct a2 as (T2,a2).
	exact (tr (fun xa=>_ = exAtCtx (popCtx (xa_a xa) T')) (IHa1 _ a2) (eq_refl _)).
Defined.
Implicit Arguments atCtxUniq [G n T1 T2].

Definition ctxProj G n T (a:AtCtx G n T) : forall g,T g.
	induction a using AtCtx_rect.

	apply (tr (fun X=>forall g,X g) (tpMapEq (@projT1 _ T) T)).
	exact (@projT2 _ _).

	apply (tr (fun X=>forall g,X g) (tpMapEq (@projT1 _ T') T)).
	exact (fun g=>IHa (projT1 g)).
Defined.
Implicit Arguments ctxProj [G n T].

(*
Remark ctxProj_top G T : ctxProj (topCtx G T) = @projT2 _ _.
	reflexivity.
Qed.

Definition ctxProj_pop G n := match G
return forall T (a:AtCtx G n T) T',(fun g=>ctxProj a (projT1 g)) = ctxProj (popCtx a T')
	with ctx _ _ => fun _ _ _=>eq_refl _ end.
Implicit Arguments ctxProj_pop [G n T].

Definition atCtxEta G n : forall T (a:AtCtx G n T),AtCtx G n (fun g=>T g).
	destruct G.
	unfold AtCtx.
	simpl.
	intro.
	destruct s as [| ? ? T'].

	simpl.
	exact (fun x=>x).

	destruct n;simpl;intro;destruct a.
		reflexivity.

		exact (mkPopCtx _ _ _ a).
Defined.
Implicit Arguments atCtxEta [G n T].

Definition ctxProj_Eta G n : forall T (a:AtCtx G n T),(fun g=>ctxProj a g) = ctxProj (atCtxEta a).
	destruct G.
	unfold AtCtx.
	simpl ctxSc.
	simpl ctxTp.
	intro.
	destruct s as [| ? ? T'].

	simpl AtCtxS.
	intro.
	destruct a.

	destruct n;simpl AtCtxS;intro;destruct a;reflexivity.
Defined.
Implicit Arguments ctxProj_Eta [G n T].
*)

(* Iterated context extension *)

Inductive ExtCtx GL : nat->Ctx->Type :=
	extOCtx : ExtCtx GL O GL |
	extSCtx n G : ExtCtx GL n G->forall T:G->Type,ExtCtx GL (S n) (extCtx G T).
Implicit Arguments extSCtx [GL n G].

Definition extSCtxInv GL n G T (xg:ExtCtx GL (S n) (extCtx G T)) (P:forall n G T,ExtCtx GL n (extCtx G T)->Type)
	(xgS:forall xg:ExtCtx GL n G,P _ _ _ (extSCtx xg T))
: P _ _ _ xg.
	pose (P' n Gx (xg:ExtCtx GL n Gx) := forall ne:IsExtCtx Gx,
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
Implicit Arguments extSCtxInv [GL n G T].

Definition extSCtxInvEq GL n G P := match G
return forall T (xg:ExtCtx GL n G) xgS,xgS xg = extSCtxInv (extSCtx xg T) P xgS
	with ctx _ _ => fun _ _ _=>eq_refl _ end.
Implicit Arguments extSCtxInvEq [GL n G T].

(*
Inductive ExtSCtx P : Ctx->Type := mkExtSCtx G : P G->forall T,ExtSCtx P (extCtx G T).
Implicit Arguments mkExtSCtx [P G].

Fixpoint ExtCtx GL n : Ctx->Type := match n with
	O => eq GL |
	S n => ExtSCtx (ExtCtx GL n)
end.

Definition extOCtx GL : ExtCtx GL O GL := eq_refl _.
Definition extSCtx GL n G (xg:ExtCtx GL n G) T : ExtCtx GL (S n) (extCtx G T) := mkExtSCtx xg _.
Implicit Arguments extSCtx [GL n G].

Definition ExtCtx_rect GL (P:forall n G,ExtCtx GL n G->Type)
	(xgO:P _ _ (extOCtx GL))
	(xgS:forall n G (xg:ExtCtx GL n G) (IHxg:P _ _ xg) T,P _ _ (extSCtx xg T))
: forall n G (xg:ExtCtx GL n G),P _ _ xg.
	refine (fix ExtCtx_rect n G := match n return forall xg:ExtCtx GL n G,P _ _ xg with
		O => _ |
		S _ => _
	end);simpl;intro;destruct xg.

	exact xgO.

	exact (xgS _ _ _ (ExtCtx_rect _ _ _) _).
Defined.
Implicit Arguments ExtCtx_rect [GL n G].

Definition extSCtxInv P G T (xg:ExtSCtx P (extCtx G T)) (C:forall G T,ExtSCtx P (extCtx G T)->Type)
	(xgS:forall xg:P G,C _ _ (mkExtSCtx xg T))
: C _ _ xg.
	pose (C' Gx xg := forall ne:IsExtCtx Gx,C _ _ (tr (ExtSCtx P) (extCtxUnfold ne) xg)).
	assert (HC : forall G T xg,C G T xg = C (ctx (ctxSc G)) T xg).
		exact (fun G=>match G with ctx _ _ => fun _ _=>eq_refl _ end).
	apply (tr (fun X=>X) (eq_sym (HC _ _ _))).
	generalize I.
	change (C' _ xg).
	refine (match xg as xg in ExtSCtx _ Gx return (extCtx G T = Gx)->C' Gx xg with
		mkExtSCtx _ xg _ => _ end (eq_refl _)).
	clear xg.
	intro.
	revert xg0.
	apply (tr (fun s=>forall xg:P (projT1 s),C' _ (mkExtSCtx xg (projT2 s))) (extCtxInj H)).
	clear G0 T0 H.
	simpl.
	intros ? ?.
	simpl.
	exact (tr (fun X=>X) (HC _ _ _) (xgS xg)).
Defined.
Implicit Arguments extSCtxInv [P G T].

Definition extSCtxInvEq P G C := match G
return forall T (xg:P G) xgS,xgS xg = extSCtxInv (mkExtSCtx xg T) C xgS
	with ctx _ _ => fun _ _ _=>eq_refl _ end.
Implicit Arguments extSCtxInvEq [P G T].
*)

(*
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
*)

Fixpoint unExt GL n G (xg:ExtCtx GL n G) : G->GL := match xg with
	extOCtx => fun g=>g |
	extSCtx _ _ xg _ => fun g=>unExt _ _ _ xg (projT1 g)
end.
Implicit Arguments unExt [GL n G].

Definition extAtCtxInd GL P (C:forall n G P',ExtCtx (extCtx GL P) n G->AtCtx G n P'->Type)
	(xgO:C _ _ _ (extOCtx _) (topCtx GL P))
	(xgS:forall n G P' xg (a:AtCtx G n P') T,C _ _ _ xg a->C _ _ _ (extSCtx xg T) (popCtx a T))
n G (xg:ExtCtx (extCtx GL P) n G) : forall P' (a:AtCtx G n P'),C _ _ _ xg a.
	induction xg;unfold AtCtx;simpl;intros;destruct a.

	exact xgO.

	exact (xgS _ _ _ _ _ _ (IHxg _ _)).
Defined.
Implicit Arguments extAtCtxInd [GL P n G P'].

Inductive ExtCtxComp GL' n G : Type := mkExtCtxComp G' (xg':ExtCtx GL' n G') (f':G'->G).
Implicit Arguments mkExtCtxComp [GL' n G G'].

Definition xc_G' GL' n G (xc:ExtCtxComp GL' n G) := match xc with mkExtCtxComp G' _ _ => G' end.
Implicit Arguments xc_G' [GL' n G].

Definition xc_xg' GL' n G (xc:ExtCtxComp GL' n G) : ExtCtx GL' n (xc_G' xc) := match xc with mkExtCtxComp _ xg' _ => xg' end.
Implicit Arguments xc_xg' [GL' n G].

Definition xc_f' GL' n G (xc:ExtCtxComp GL' n G) : xc_G' xc->G := match xc with mkExtCtxComp _ _ f' => f' end.
Implicit Arguments xc_f' [GL' n G].

Definition extCtxComp GL n G (xg:ExtCtx GL n G) (GL':Ctx) (f:GL'->GL) : ExtCtxComp GL' n G.
	induction xg.

	exact (mkExtCtxComp (extOCtx _) f).

	exact (mkExtCtxComp (extSCtx (xc_xg' IHxg) _)
		(fun (g:sigT (fun g=>T (_ g)))=>existT _ (xc_f' IHxg (projT1 g)) (projT2 g))).
Defined.
Implicit Arguments extCtxComp [GL n G].

Definition xcBump GL P l G (xg:ExtCtx GL l G) := extCtxComp xg (extCtx GL P) (@projT1 _ _).
Implicit Arguments xcBump [GL l G].

Definition ctxBump GL P l G (xg:ExtCtx GL l G) := xc_G' (xcBump P xg).
Implicit Arguments ctxBump [GL l G].

Definition xgBump GL P l G (xg:ExtCtx GL l G) : ExtCtx _ l (ctxBump P xg) := xc_xg' (xcBump P xg).
Implicit Arguments xgBump [GL l G].

Definition elBump GL P l G (xg:ExtCtx GL l G) T (t:forall g,T g) (g:ctxBump P xg) :=
	t (xc_f' (xcBump P xg) g).
Implicit Arguments elBump [GL l G T].

Definition atBumpLo GL P l G n T (xg:ExtCtx GL l G) (a:AtCtx G n T) (Ho:ltd n l) : AtCtx (ctxBump P xg) n (elBump P xg T).
	revert l Ho xg.
	induction a using AtCtx_rect;intro;(destruct l;intro;[exact (match Ho with end) |]);simpl;intro.

	apply (extSCtxInv xg).
	clear xg.
	intro.
	reflexivity.

	revert T a IHa.
	apply (extSCtxInv xg).
	clear xg.
	intros.
	change (AtCtx (extCtx (ctxBump P xg) (elBump P xg T')) (S n) (fun g=>elBump P xg T (projT1 g))).
	apply popCtx.
	exact (IHa _ Ho xg).
Defined.
Implicit Arguments atBumpLo [GL l G n T].

Definition atBumpHi GL P l G n T (xg:ExtCtx GL l G) (a:AtCtx G n T) (Ho:ltd l (S n)) : AtCtx (ctxBump P xg) (S n) (elBump P xg T).
	revert n Ho T a.
	induction xg as [| l ? ? ? T'].

	intros.
	unfold ctxBump.
	simpl.
	apply (popCtx a).

	intro.
	destruct n.
		intro.
		exact (match ltd_n_O Ho with end).
	intros.
	change (PopCtx T' (AtCtx G n) T) in a.
	destruct a.
	change (AtCtx (extCtx (ctxBump P xg) (elBump P xg T')) (S (S n)) (fun g=>elBump P xg T (projT1 g))).
	apply popCtx.
	exact (IHxg _ Ho _ a).
Defined.
Implicit Arguments atBumpHi [GL l G n T].

Definition ctxProj_BumpLo GL P l G n T (xg:ExtCtx GL l G) (a:AtCtx G n T) (Ho:ltd n l) :
elBump P xg (ctxProj a) = ctxProj (atBumpLo P xg a Ho).
	revert l Ho xg.
	induction a using AtCtx_rect;intro;(destruct l;intro;[exact (match Ho with end) |]);intro.

	revert Ho.
	apply (extSCtxInv xg).
	clear xg.
	revert T.
	destruct G.
	simpl.
	intros.
	reflexivity.

	revert T a IHa Ho.
	apply (extSCtxInv xg).
	clear xg.
	revert T'.
	destruct G.
	simpl ctxTp.
	intros.
	change (elBump P (extSCtx xg T') (ctxProj (popCtx a T')) =
		ctxProj (popCtx (atBumpLo P xg a Ho) (elBump P xg T'))).
	apply (tr (fun X=>_ = X) (ctxProj_pop (atBumpLo P xg a Ho) (elBump P xg T'))).
	apply (tr (fun X=>_ = fun g=>X (projT1 g)) (IHa _ Ho xg)).
	reflexivity.
Defined.
Implicit Arguments ctxProj_BumpLo [GL l G n T].

Definition ctxProj_BumpHi GL P l G n T (xg:ExtCtx GL l G) (a:AtCtx G n T) (Ho:ltd l (S n)) :
elBump P xg (ctxProj a) = ctxProj (atBumpHi P xg a Ho).
	revert n Ho T a.
	induction xg as [| l ? ? ? T'].

	intros ? ?.
	revert P.
	destruct GL as (GL,?).
	simpl ctxTp.
	intros.
	reflexivity.

	intro.
	destruct n.
		intro.
		exact (match ltd_n_O Ho with end).
	intros.
	change (PopCtx T' (AtCtx G n) T) in a.
	destruct a.
	change (elBump P (extSCtx xg T') (ctxProj (popCtx a T')) =
		ctxProj (popCtx (atBumpHi P xg a Ho) (elBump P xg T'))).
	apply (tr (fun X=>elBump P (extSCtx xg T') X = _) (ctxProj_pop a T')).
	apply (tr (fun X=>_ = X) (ctxProj_pop (atBumpHi P xg a Ho) (elBump P xg T'))).
	apply (tr (fun X=>_ = fun g=>X (projT1 g)) (IHxg _ Ho _ a)).
	reflexivity.
Defined.
Implicit Arguments ctxProj_BumpHi [GL l G n T].

Definition xcSubst GL P l G (xg:ExtCtx (extCtx GL P) l G) (p:forall g,P g) :=
	extCtxComp xg GL (fun g=>existT _ g (p g)).
Implicit Arguments xcSubst [GL P l G].

Definition ctxSubst GL P l G (xg:ExtCtx (extCtx GL P) l G) p := xc_G' (xcSubst xg p).
Implicit Arguments ctxSubst [GL P l G].

Definition xgSubst GL P l G (xg:ExtCtx (extCtx GL P) l G) p : ExtCtx GL l (ctxSubst xg p) :=
	xc_xg' (xcSubst xg p).
Implicit Arguments xgSubst [GL P l G].

Definition elSubst GL P l G (xg:ExtCtx (extCtx GL P) l G) T (t:forall g,T g) p
	(g:ctxSubst xg p) := t (xc_f' (xcSubst xg p) g).
Implicit Arguments elSubst [GL P l G T].

Definition atSubstLt GL P l G n T (xg:ExtCtx (extCtx GL P) l G) (a:AtCtx G n T) (Ho:ltd n l) p :
AtCtx (ctxSubst xg p) n (elSubst xg T p).
	revert l Ho xg.
	induction a using AtCtx_rect;intro;(destruct l;intro;[exact (match Ho with end) |]);intro.

	apply (extSCtxInv xg).
	clear xg.
	intro.
	unfold ctxSubst.
	simpl.
	apply topCtx.

	revert T a IHa.
	apply (extSCtxInv xg).
	clear xg.
	intros.
	change (AtCtx (extCtx (ctxSubst xg p) (elSubst xg T' p)) (S n) (fun g=>elSubst xg T p (projT1 g))).
	apply popCtx.
	exact (IHa _ Ho xg).
Defined.
Implicit Arguments atSubstLt [GL P l G n T].

Definition atSubstGt GL P l G n T (xg:ExtCtx (extCtx GL P) l G) (a:AtCtx G (S n) T) (Ho:ltd l (S n)) p :
AtCtx (ctxSubst xg p) n (elSubst xg T p).
	revert n Ho T a.
	induction xg as [| l ? ? ? T'].

	intros.
	change (PopCtx P (AtCtx GL n) T) in a.
	destruct a.
	exact (atCtxEta a).

	intro.
	destruct n.
		intro.
		exact (match ltd_n_O Ho with end).
	intros.
	change (PopCtx T' (AtCtx G (S n)) T) in a.
	destruct a.
	change (AtCtx (extCtx (ctxSubst xg p) (elSubst xg T' p)) (S n) (fun g=>elSubst xg T p (projT1 g))).
	apply popCtx.
	exact (IHxg _ Ho _ a).
Defined.
Implicit Arguments atSubstGt [GL P l G n T].

Definition elMBump GL P n G P' (xg:ExtCtx (extCtx GL P) n G) (a:AtCtx G n P') (p:forall g,P g) : forall g,P' g.
	revert P' a.
	induction xg;intros ? ?.

	destruct a.
	exact (fun g=>p (projT1 g)).

	change (PopCtx T (AtCtx G n) P') in a.
	destruct a as (P',?).
	exact (fun g=>IHxg _ a (projT1 g)).
Defined.
Implicit Arguments elMBump [GL P n G P'].

Definition ctxProj_SubstLt GL P l G n T (xg:ExtCtx (extCtx GL P) l G) (a:AtCtx G n T) (Ho:ltd n l) p :
elSubst xg (ctxProj a) p = ctxProj (atSubstLt xg a Ho p).
	revert l Ho xg.
	induction a using AtCtx_rect;intro;(destruct l;intro;[exact (match Ho with end) |]);intro.

	revert Ho.
	apply (extSCtxInv xg).
	clear xg.
	revert T.
	destruct G.
	simpl.
	intros.
	reflexivity.

	revert T a IHa Ho.
	apply (extSCtxInv xg).
	clear xg.
	revert T'.
	destruct G.
	simpl ctxTp.
	intros.
	change (elSubst (extSCtx xg T') (ctxProj (popCtx a T')) p =
		ctxProj (popCtx (atSubstLt xg a Ho p) (elSubst xg T' p))).
	apply (tr (fun X=>_ = X) (ctxProj_pop (atSubstLt xg a Ho p) (elSubst xg T' p))).
	apply (tr (fun X=>_ = fun g=>X (projT1 g)) (IHa _ Ho xg)).
	reflexivity.
Defined.
Implicit Arguments ctxProj_SubstLt [GL P l G n T].

Definition ctxProj_SubstGt GL P l G n T (xg:ExtCtx (extCtx GL P) l G) (a:AtCtx G (S n) T) (Ho:ltd l (S n)) p :
elSubst xg (ctxProj a) p = ctxProj (atSubstGt xg a Ho p).
	revert n Ho T a.
	induction xg as [| l ? ? ? T'].

	intros.
	change (PopCtx P (AtCtx GL n) T) in a.
	destruct a.
	change (elSubst (extOCtx (extCtx GL P)) (ctxProj (popCtx a P)) p = ctxProj (atCtxEta a)).
	apply (tr (fun X=>elSubst (extOCtx _) X p = _) (ctxProj_pop a P)).
	apply (tr (fun X=>_ = X) (ctxProj_Eta a)).
	reflexivity.

	intro.
	destruct n.
		intro.
		exact (match ltd_n_O Ho with end).
	intros.
	change (PopCtx T' (AtCtx G (S n)) T) in a.
	destruct a.
	change (elSubst (extSCtx xg T') (ctxProj (popCtx a T')) p =
		ctxProj (popCtx (atSubstGt xg a Ho p) (elSubst xg T' p))).
	apply (tr (fun X=>elSubst (extSCtx xg T') X p = _) (ctxProj_pop a T')).
	apply (tr (fun X=>_ = X) (ctxProj_pop (atSubstGt xg a Ho p) (elSubst xg T' p))).
	apply (tr (fun X=>_ = fun g=>X (projT1 g)) (IHxg _ Ho _ a)).
	reflexivity.
Defined.
Implicit Arguments ctxProj_SubstGt [GL P l G n T].

Definition ctxProj_SubstEq GL P n G P' (xg:ExtCtx (extCtx GL P) n G) (a:AtCtx G n P') p :
elSubst xg (ctxProj a) p = elSubst xg (elMBump xg a p) p.
	apply extAtCtxInd with (xg := xg) (a := a);clear n G P' xg a.

	reflexivity.

	intros ? ?.
	destruct G.
	simpl ctxTp.
	intros.
	change ((fun g:ctxSubst (extSCtx xg T) p=>elSubst xg (ctxProj a) p (projT1 g)) =
		(fun g=>elSubst xg (elMBump xg a p) p (projT1 g))).
	apply (tr (fun X=>_ = fun g:ctxSubst (extSCtx xg T) p=>X (projT1 g)) H).
	reflexivity.
Defined.
Implicit Arguments ctxProj_SubstEq [GL P n G P'].

(* Stuff for substituting one variable for another *)

Fixpoint atMBump GL l G n T (xg:ExtCtx GL l G) (a:AtCtx GL n T) : ExAtCtx G (l + n) := match xg with
	extOCtx => exAtCtx a |
	extSCtx _ _ xg T' => exAtCtx (popCtx (xa_a (atMBump _ _ _ _ _ xg a)) T')
end.
Implicit Arguments atMBump [GL l G n T].

Definition atMBumpTEq GL a b P G (b':AtCtx GL b P) (xg:ExtCtx (extCtx GL P) a G) :
forall P' (a':AtCtx G a P'),xa_T (atMBump xg (popCtx b' P)) = P'.
	induction xg as [| a];intros ? ?;simpl.

	destruct a'.
	reflexivity.

	change (PopCtx T (AtCtx G a) P') in a'.
	destruct a' as (P',a').
	apply (tr (fun _=>_) (IHxg _ a')).
	reflexivity.
Defined.
Implicit Arguments atMBumpTEq [GL a b P G P'].

Definition ctxProj_MBump GL a b P G P' (b':AtCtx GL b P) (xg:ExtCtx (extCtx GL P) a G) (a':AtCtx G a P') :
ctxProj (tr (AtCtx G _) (atMBumpTEq b' xg a') (xa_a (atMBump xg (popCtx b' P)))) = elMBump xg a' (ctxProj b').
	apply extAtCtxInd with (xg := xg) (a := a');clear a G P' xg a'.

	revert P b'.
	destruct GL as (GL,?).
	intros.
	reflexivity.

	intros a ?.
	destruct G.
	simpl ctxTp.
	intros ? ? a' ? ?.
	simpl elMBump.
	apply (tr (fun t=>_ = fun g=>t (projT1 g)) H).
	simpl atMBumpTEq.
	refine (match atMBumpTEq b' xg a' as teq
		return ctxProj (tr (AtCtx (extCtx (ctx s) _) _) (tr _ teq _) _) =
			fun g=>ctxProj (tr _ teq _) (projT1 g)
		with eq_refl => _ end).
	clear P' a' H.
	simpl tr.
	reflexivity.
Defined.
Implicit Arguments ctxProj_MBump [GL a b P G P'].

End Context.
