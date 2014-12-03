Require Import Utils.

Set Implicit Arguments.

Module Type CTXTYP.

Parameter Typ : Type.

Parameter TypTp : Typ->Type.
Coercion TypTp : Typ >-> Sortclass.

End CTXTYP.

Module Contex (Import CtxTyp : CTXTYP).

(* Semantic contexts *)

Inductive CtxS : Type->Type :=
	empCtxS : CtxS unit |
	extCtxS G (s:CtxS G) (T:G->Typ) : CtxS (sigT T).

Inductive Ctx : Type := ctx G (s:CtxS G).

Definition CtxTp G := match G with ctx G _ => G end.
Coercion CtxTp : Ctx >-> Sortclass.

Definition ctxSc (G:Ctx) : CtxS G := match G with ctx _ s => s end.

Definition EmpCtx := ctx empCtxS.
Definition ExtCtx G T := ctx (extCtxS (ctxSc G) T).

Definition IsExtCtx G := match G with
	ctx _ empCtxS => False |
	ctx _ (extCtxS _ _ _) => True
end.

Definition CtxInit G := match G with
	ctx _ empCtxS => EmpCtx |
	ctx _ (extCtxS _ s _) => ctx s
end.

Definition CtxTop G : forall ne:IsExtCtx G,CtxInit G->Typ.
	destruct G.
	destruct s;simpl;intro.

	destruct ne.

	exact T.
Defined.
Arguments CtxTop [G] ne g.

Fixpoint ctxLenS G (s:CtxS G) := match s with
	empCtxS => O |
	extCtxS _ s _ => S (ctxLenS s)
end.

Definition ctxLen G := ctxLenS (ctxSc G).

Definition extCtxUnfold G : forall ne:IsExtCtx G,G = ExtCtx (CtxInit G) (CtxTop ne).
	destruct G.
	destruct s;simpl;intro.

	destruct ne.

	reflexivity.
Defined.
Arguments extCtxUnfold [G] ne.

Definition extCtxInj G1 G2 : forall T1 T2 (e:ExtCtx G1 T1 = ExtCtx G2 T2),
existT (fun G:Ctx=>G->Typ) G1 T1 = existT _ G2 T2.
	destruct G1 as (G1,s1).
	destruct G2 as (G2,s2).
	simpl.
	intros.
	generalize I.
	apply (tr (fun Gx=>forall ne:IsExtCtx Gx,_ = existT (fun G:Ctx=>G->Typ) _ (CtxTop ne)) e).
	simpl.
	intro.
	reflexivity.
Defined.

(* Strongly typed de Bruijn indexes *)

(*
Inductive AtCtx : forall G:Ctx,nat->(G->Typ)->Type :=
	topCtx G T : AtCtx (ExtCtx G T) O (fun g=>T (projT1 g)) |
	popCtx G i T : AtCtx G i T->forall T',AtCtx (ExtCtx G T') (S i) (fun g=>T (projT1 g)).
*)

Inductive PopCtx G (T':G->Typ) P : (sigT T'->Typ)->Type :=
	mkPopCtx T : P T->PopCtx T' P (fun g=>T (projT1 g)).

Fixpoint AtCtxS G (s:CtxS G) i : (G->Typ)->Type := match s with
	empCtxS => fun T=>Empty_set |
	extCtxS _ s T' => match i with
		O => eq (fun g=>T' (projT1 g)) |
		S i => PopCtx T' (AtCtxS s i)
	end
end.

Definition AtCtx G := AtCtxS (ctxSc G).

Definition topCtx G T : AtCtx (ExtCtx G T) O (fun g=>T (projT1 g)) := eq_refl.

Definition popCtx G i T (a:AtCtx G i T) T' : AtCtx (ExtCtx G T') (S i) (fun g=>T (projT1 g)) := mkPopCtx _ _ _ a.
Arguments popCtx [G i T] a T'.

Definition atCtxIndS (P:forall G i T,AtCtx G i T->Type)
	(top:forall G T,P _ _ _ (topCtx G T))
	(pop:forall G i T (a:AtCtx G i T) (IHa:P _ _ _ a) T',P _ _ _ (popCtx a T'))
: forall G (s:CtxS G) i T (a:AtCtx (ctx s) i T),P _ _ _ a.
	refine (fix atCtxIndS G s i := match s in CtxS G return forall T (a:AtCtx (ctx s) i T),P _ _ _ a with
		empCtxS => _ |
		extCtxS _ s0 _ => _
	end);clear G s;simpl;intro.

	intro.
	destruct a.

	destruct i;unfold AtCtx;simpl;intro;destruct a.
		exact (top (ctx s0) _).

		exact (pop _ _ _ _ (atCtxIndS _ _ _ _ _) _).
Defined.

Definition AtCtx_rect (P:forall G i T,AtCtx G i T->Type)
	(top:forall G T,P _ _ _ (topCtx G T))
	(pop:forall G i T (a:AtCtx G i T) (IHa:P _ _ _ a) T',P _ _ _ (popCtx a T'))
G : forall i T (a:AtCtx G i T),P _ _ _ a := match G with ctx _ s => atCtxIndS P top pop s end.

Inductive ExAtCtx G i : Type := exAtCtx T (a:AtCtx G i T).
Arguments exAtCtx [G i T] a.

Definition xa_T G i (xa:ExAtCtx G i) := match xa with exAtCtx T _ => T end.
Definition xa_a G i (xa:ExAtCtx G i) : AtCtx G i (xa_T xa) := match xa with exAtCtx _ a => a end.

Definition atCtxUniq G i T1 (a1:AtCtx G i T1) : forall T2 (a2:AtCtx G i T2),
exAtCtx a1 = exAtCtx a2.
	induction a1 as [| ? ? T1] using AtCtx_rect;intros.

	destruct a2.
	reflexivity.

	change (PopCtx T' (AtCtx G i) T2) in a2.
	destruct a2 as (T2,a2).
	exact (tr (fun xa=>exAtCtx (popCtx a1 T') = exAtCtx (popCtx (xa_a xa) T')) (IHa1 _ a2) eq_refl).
Defined.
Arguments atCtxUniq [G i T1] a1 [T2] a2.

Definition envProj G i T (a:AtCtx G i T) : forall g,T g.
	induction a using AtCtx_rect.

	exact (@projT2 _ _).

	exact (fun g=>IHa (projT1 g)).
Defined.
Arguments envProj [G i T] a g.

Remark envProj_top G T : envProj (topCtx G T) = @projT2 _ _.
	reflexivity.
Qed.

Lemma envProj_pop G i : forall T (a:AtCtx G i T) T',(fun g=>envProj a (projT1 g)) = envProj (popCtx a T').
	destruct G.
	simpl CtxTp.
	intros.
	reflexivity.
Qed.
Arguments envProj_pop [G i T] a T'.

(* Telescopes (Iterated context extension) *)

Inductive TeleS GL : nat->Ctx->Type :=
	empTeleS : TeleS GL O GL |
	extTeleS n G (xg:TeleS GL n G) T : TeleS GL (S n) (ExtCtx G T).

Definition extTeleSInv GL n G T (xg:TeleS GL (S n) (ExtCtx G T)) (P:forall n G T,TeleS GL n (ExtCtx G T)->Type)
	(ext:forall xg:TeleS GL n G,P _ _ _ (extTeleS xg T))
: P _ _ _ xg.
	pose (P' n Gx (xg:TeleS GL n Gx) := forall ne:IsExtCtx Gx,
		P _ _ _ (tr (TeleS GL n) (extCtxUnfold ne) xg)).
	assert (Peq := match G return forall T xg,P (S n) G T xg = P _ (ctx (ctxSc G)) _ xg
		with ctx _ _ => fun _ _=>eq_refl end T).
	apply (tr (fun C=>C) (eq_sym (Peq _))).
	generalize I.
	refine (match xg in TeleS _ Sn Gx return (Sn = S n)->(ExtCtx G T = Gx)->P' _ _ xg with
		empTeleS => fun e=>match O_S _ e with end |
		extTeleS _ _ xg0 _ => fun Hn HG=>_
	end eq_refl eq_refl).
	revert xg0.
	apply (tr (fun _=>_) (eq_sym (Sinj Hn))).
	apply (tr (fun GT=>forall xg,P' _ _ (extTeleS xg (projT2 GT))) (extCtxInj HG)).
	simpl.
	intros ? ?.
	simpl.
	exact (tr (fun C=>C) (Peq _) (ext _)).
Defined.

Lemma extTeleSInvEq GL n G P : forall T (xg:TeleS GL n G) ext,ext xg = extTeleSInv (extTeleS xg T) P ext.
	destruct G.
	simpl CtxTp.
	intros.
	exact (eq_refl (ext xg)).
Qed.

Fixpoint unExt GL n G (xg:TeleS GL n G) : G->GL := match xg with
	empTeleS => fun g=>g |
	extTeleS _ _ xg _ => fun g=>unExt xg (projT1 g)
end.

Fixpoint atUnExt GL n G i T (xg:TeleS GL n G) (a:AtCtx GL i T) : AtCtx G (n + i) (fun g=>T (unExt xg g)) := match xg with
	empTeleS => a |
	extTeleS _ _ xg T' => popCtx (atUnExt i T xg a) T'
end.
Arguments atUnExt [GL n G i T] xg a.

Lemma envProj_UnExt GL n G i T (xg:TeleS GL n G) (a:AtCtx GL i T) : (fun g=>envProj a (unExt xg g)) = envProj (atUnExt xg a).
	induction xg as [| ? ? ? ? T'].

	exact (eq_refl (envProj a)).

	simpl atUnExt.
	apply (tr (fun x=>_ = x) (envProj_pop (atUnExt xg a) T')).
	apply (tr (fun x=>_ = fun g=>x (projT1 g)) IHxg).
	reflexivity.
Qed.
Arguments envProj_UnExt [GL n G i T] xg a.

(* Telescope Computation *)

Inductive TeleComp GL' n G : Type := mkTeleComp G' (xg':TeleS GL' n G') (f':G'->G).

Definition xc_G' GL' n G (xc:TeleComp GL' n G) := match xc with mkTeleComp G' _ _ => G' end.
Definition xc_xg' GL' n G (xc:TeleComp GL' n G) : TeleS GL' n (xc_G' xc) := match xc with mkTeleComp _ xg' _ => xg' end.
Definition xc_f' GL' n G (xc:TeleComp GL' n G) : xc_G' xc->G := match xc with mkTeleComp _ _ f' => f' end.

Definition teleComp GL n G (xg:TeleS GL n G) (GL':Ctx) (f:GL'->GL) : TeleComp GL' n G.
	induction xg.

	exact (mkTeleComp (empTeleS _) f).

	refine (mkTeleComp (extTeleS (xc_xg' IHxg) _)
		(fun (g:sigT (fun g=>T (xc_f' IHxg g)))=>existT _ (xc_f' IHxg (projT1 g)) _)).
	exact (projT2 g).
Defined.

(* Bump *)

Definition xcBump GL n GL' (X:TeleS GL n GL') l G (xg:TeleS GL l G) := teleComp xg GL' (unExt X).

Definition CtxBump GL n GL' (X:TeleS GL n GL') l G (xg:TeleS GL l G) := xc_G' (xcBump X xg).

Definition elBump GL n GL' (X:TeleS GL n GL') l G (xg:TeleS GL l G) T (t:forall g,T g) (g:CtxBump X xg) :=
	t (xc_f' (xcBump X xg) g).
Arguments elBump [GL n GL'] X [l G] xg [T] t g.

Definition atBumpLo GL n GL' l G i T (X:TeleS GL n GL') (xg:TeleS GL l G) (a:AtCtx G i T) (Ho:ltd i l) : AtCtx (CtxBump X xg) i (elBump X xg T).
	revert l Ho xg.
	induction a using AtCtx_rect;intro;(destruct l;intro;[exact (match Ho with end) |]);simpl;intro.

	apply (extTeleSInv xg).
	clear xg.
	intro.
	change (AtCtx (ExtCtx (CtxBump X xg) (elBump X xg T)) O (fun g=>elBump X xg T (projT1 g))).
	apply topCtx.

	revert T a IHa.
	apply (extTeleSInv xg).
	clear xg.
	intros.
	change (AtCtx (ExtCtx (CtxBump X xg) (elBump X xg T')) (S i) (fun g=>elBump X xg T (projT1 g))).
	apply popCtx.
	exact (IHa _ Ho xg).
Defined.
Arguments atBumpLo [GL n GL' l G i T] X xg a Ho.

Lemma envProj_BumpLo GL n GL' l G i T (X:TeleS GL n GL') (xg:TeleS GL l G) (a:AtCtx G i T) (Ho:ltd i l) :
elBump X xg (envProj a) = envProj (atBumpLo X xg a Ho).
	revert l Ho xg.
	induction a using AtCtx_rect;intro;(destruct l;intro;[exact (match Ho with end) |]);intro.

	revert Ho.
	apply (extTeleSInv xg).
	clear xg.
	revert T.
	destruct G.
	simpl.
	intros.
	reflexivity.

	revert T a IHa Ho.
	apply (extTeleSInv xg).
	clear xg.
	revert T'.
	destruct G.
	simpl CtxTp.
	intros.
	change (elBump X (extTeleS xg T') (envProj (popCtx a T')) =
		envProj (popCtx (atBumpLo X xg a Ho) (elBump X xg T'))).
	apply (tr (fun x=>_ = x) (envProj_pop (atBumpLo X xg a Ho) (elBump X xg T'))).
	apply (tr (fun x=>_ = fun g=>x (projT1 g)) (IHa _ Ho xg)).
	reflexivity.
Qed.
Arguments envProj_BumpLo [GL n GL' l G i T] X xg a Ho.

Definition atBumpHi GL n GL' l G i T (X:TeleS GL n GL') (xg:TeleS GL l G) (a:AtCtx G i T) (Ho:ltd l (S i)) : AtCtx (CtxBump X xg) (n + i) (elBump X xg T).
	revert i Ho T a.
	induction xg as [| l ? ? ? T'].

	intros.
	exact (atUnExt X a).

	intro.
	destruct i.
		intro.
		exact (match ltd_n_O Ho with end).
	intros.
	apply (tr (fun v=>AtCtx _ v _) (plus_n_Sm n i)).
	change (PopCtx T' (AtCtx G i) T) in a.
	destruct a.
	change (AtCtx (ExtCtx (CtxBump X xg) (elBump X xg T')) (S (n + i)) (fun g=>elBump X xg T (projT1 g))).
	apply popCtx.
	exact (IHxg _ Ho _ a).
Defined.
Arguments atBumpHi [GL n GL' l G i T] X xg a Ho.

Lemma envProj_BumpHi GL n GL' l G i T (X:TeleS GL n GL') (xg:TeleS GL l G) (a:AtCtx G i T) (Ho:ltd l (S i)) :
elBump X xg (envProj a) = envProj (atBumpHi X xg a Ho).
	revert i Ho T a.
	induction xg as [| l ? ? ? T'].

	intros.
	simpl.
	apply (tr (fun x=>_ = x) (envProj_UnExt X a)).
	reflexivity.

	intro.
	destruct i.
		intro.
		exact (match ltd_n_O Ho with end).
	intros.
	change (PopCtx T' (AtCtx G i) T) in a.
	destruct a.
	simpl atBumpHi.
	destruct (plus_n_Sm n i).
	simpl tr.
	apply (tr (fun x=>elBump X (extTeleS xg T') x = _) (envProj_pop a T')).
	apply (tr (fun x=>_ = x) (envProj_pop (atBumpHi X xg a Ho) (elBump X xg T'))).
	apply (tr (fun x=>_ = fun g=>x (projT1 g)) (IHxg _ Ho _ a)).
	reflexivity.
Qed.
Arguments envProj_BumpHi [GL n GL' l G i T] X xg a Ho.

(* Subst *)

Definition xcSubst GL B l G (xg:TeleS (ExtCtx GL B) l G) (b:forall g,B g) := teleComp xg GL (fun g=>existT B g (b g)).

Definition CtxSubst GL B l G (xg:TeleS (ExtCtx GL B) l G) b := xc_G' (xcSubst xg b).

Definition elSubst GL B l G (xg:TeleS (ExtCtx GL B) l G) b T (t:forall g,T g) (g:CtxSubst xg b) :=
	t (xc_f' (xcSubst xg b) g).
Arguments elSubst [GL B l G] xg b [T] t g.

Definition atSubstLt GL B l G i T (xg:TeleS (ExtCtx GL B) l G) b (a:AtCtx G i T) (Ho:ltd i l) :
AtCtx (CtxSubst xg b) i (elSubst xg b T).
	revert l Ho xg.
	induction a using AtCtx_rect;intro;(destruct l;intro;[exact (match Ho with end) |]);intro.

	apply (extTeleSInv xg).
	clear xg.
	intro.
	apply (topCtx (CtxSubst xg b) (elSubst xg b T)).

	revert T a IHa.
	apply (extTeleSInv xg).
	clear xg.
	intros.
	exact (popCtx (IHa _ Ho xg) (elSubst xg b T')).
Defined.
Arguments atSubstLt [GL B l G i T] xg b a Ho.

Lemma envProj_SubstLt GL B l G i T (xg:TeleS (ExtCtx GL B) l G) b (a:AtCtx G i T) (Ho:ltd i l) :
elSubst xg b (envProj a) = envProj (atSubstLt xg b a Ho).
	revert l Ho xg.
	induction a using AtCtx_rect;intro;(destruct l;intro;[exact (match Ho with end) |]);intro.

	revert Ho.
	apply (extTeleSInv xg).
	clear xg.
	revert T.
	destruct G.
	simpl CtxTp.
	intros.
	reflexivity.

	revert T a IHa Ho.
	apply (extTeleSInv xg).
	clear xg.
	revert T'.
	destruct G.
	simpl CtxTp.
	intros.
	change (elSubst (extTeleS xg T') b (envProj (popCtx a T')) =
		envProj (popCtx (atSubstLt xg b a Ho) (elSubst xg b T'))).
	apply (tr (fun x=>_ = x) (envProj_pop (atSubstLt xg b a Ho) (elSubst xg b T'))).
	apply (tr (fun x=>_ = fun g=>x (projT1 g)) (IHa _ Ho xg)).
	reflexivity.
Qed.
Arguments envProj_SubstLt [GL B l G i T] xg b a Ho.

Definition atSubstGt GL B l G i T (xg:TeleS (ExtCtx GL B) l G) b (a:AtCtx G (S i) T) (Ho:ltd l (S i)) :
AtCtx (CtxSubst xg b) i (elSubst xg b T).
	revert i Ho T a.
	induction xg as [| l ? ? ? T'].

	intros.
	change (PopCtx B (AtCtx GL i) T) in a.
	destruct a.
	exact a.

	intro.
	destruct i.
		intro.
		exact (match ltd_n_O Ho with end).
	intros.
	change (PopCtx T' (AtCtx G (S i)) T) in a.
	destruct a.
	exact (popCtx (IHxg _ Ho _ a) (elSubst xg b T')).
Defined.
Arguments atSubstGt [GL B l G i T] xg b a Ho.

Lemma envProj_SubstGt GL B l G i T (xg:TeleS (ExtCtx GL B) l G) b (a:AtCtx G (S i) T) (Ho:ltd l (S i)) :
elSubst xg b (envProj a) = envProj (atSubstGt xg b a Ho).
	revert i Ho T a.
	induction xg as [| l ? ? ? T'].

	intros.
	change (PopCtx B (AtCtx GL i) T) in a.
	destruct a.
	change (elSubst (empTeleS (ExtCtx GL B)) b (envProj (popCtx a B)) = envProj a).
	apply (tr (fun x=>elSubst (empTeleS _) b x = _) (envProj_pop a B)).
	reflexivity.

	intro.
	destruct i.
		intro.
		exact (match ltd_n_O Ho with end).
	intros.
	change (PopCtx T' (AtCtx G (S i)) T) in a.
	destruct a.
	change (elSubst (extTeleS xg T') b (envProj (popCtx a T')) =
		envProj (popCtx (atSubstGt xg b a Ho) (elSubst xg b T'))).
	apply (tr (fun x=>elSubst (extTeleS xg T') b x = _) (envProj_pop a T')).
	apply (tr (fun x=>_ = x) (envProj_pop (atSubstGt xg b a Ho) (elSubst xg b T'))).
	apply (tr (fun x=>_ = fun g=>x (projT1 g)) (IHxg _ Ho _ a)).
	reflexivity.
Qed.
Arguments envProj_SubstGt [GL B l G i T] xg b a Ho.

Lemma xcSubstEqUnExt GL B l G (xg:TeleS (ExtCtx GL B) l G) b : forall B' (a:AtCtx G l B'),
	let X : TeleS GL l (CtxSubst xg b) := xc_xg' (xcSubst xg b) in
existT (fun T:_->Typ=>forall g,T g) (fun g=>B (unExt X g)) (fun g=>b (unExt X g)) =
existT _ (elSubst xg b B') (elSubst xg b (envProj a)).
	induction xg as [| l];intros;unfold AtCtx in a;simpl in a.

	destruct a.
	unfold elSubst.
	unfold CtxSubst.
	simpl.
	reflexivity.

	set (Tt (T:_->Typ) := forall g,T g).
	change (CtxSubst (extTeleS xg T) b) with (ExtCtx (CtxSubst xg b) (elSubst xg b T)) in Tt.
	destruct a as (B').
	change (AtCtx G l B') in a.
	simpl unExt.
	clear X.
	set (X := xc_xg' (xcSubst xg b)).
	apply (tr (fun x:forall g,B' (projT1 g)=>_ = existT Tt _ (elSubst (extTeleS xg T) b x)) (envProj_pop a T)).
	apply (tr (fun s:{T:_->Typ & forall g,T g}=>_ = existT Tt (fun g=>projT1 s (projT1 g)) (fun g=>projT2 s (projT1 g))) (IHxg _ a)).
	simpl.
	fold X.
	reflexivity.
Qed.
Arguments xcSubstEqUnExt [GL B l G] xg b [B'] a.

End Contex.
