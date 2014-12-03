Require Import List.
Require Import Compare_dec.

Require Import Utils.
Require Import Substitutions.
Require Import DepTyping.
Require Import Context.

Require Import Lt.

Set Implicit Arguments.

Module VarItrpBump (Import CtxTyp : CTXTYP).

Module Import Contex := Contex CtxTyp.

Import VarBump.

Definition atBump GL n GL' l G i T (X:TeleS GL n GL') (xg:TeleS GL l G) (a:AtCtx G i T) :
AtCtx (CtxBump X xg) (varBump n l i) (elBump X xg T).
	destruct (lt_dec i l) as [Ho | Ho].

	apply (tr (fun v=>AtCtx _ v _) (eq_sym (varBumpLo _ _ _ Ho))).
	exact (atBumpLo X xg a (lt_ltd Ho)).

	apply (tr (fun v=>AtCtx _ v _) (eq_sym (varBumpHi _ _ _ Ho))).
	exact (atBumpHi X xg a (not_lt_ltd Ho)).
Defined.
Arguments atBump [GL n GL' l G i T] X xg a.

Lemma envProj_Bump GL n GL' l G i T (X:TeleS GL n GL') (xg:TeleS GL l G) (a:AtCtx G i T) :
elBump X xg (envProj a) = envProj (atBump X xg a).
	unfold atBump.
	destruct (lt_dec i l) as [Ho | Ho].

	destruct (eq_sym (varBumpLo n l i Ho)).
	simpl.
	apply envProj_BumpLo.

	destruct (eq_sym (varBumpHi n l i Ho)).
	simpl.
	apply envProj_BumpHi.
Qed.
Arguments envProj_Bump [GL n GL' l G i T] X xg a.

Inductive VarItrp (G:Ctx) i : forall T:G->Typ,(forall g,T g)->Type :=
	varItrp T (i':AtCtx G i T) : VarItrp G i T (envProj i').
Arguments varItrp [G i T] i'.

Lemma varItrpUniq G i T1 T2 t1 t2 (X1:VarItrp G i T1 t1) (X2:VarItrp G i T2 t2) :
existT (fun T:G->Typ=>forall g,T g) T1 t1 = existT _ T2 t2.
	destruct X1 as (T1,i1).
	destruct X2 as (T2,i2).
	apply (tr (fun x=>_ = existT _ (xa_T x) (envProj (xa_a x))) (atCtxUniq i1 i2)).
	simpl.
	reflexivity.
Qed.

Lemma varItrpBump GL n GL' l G i T t' (X:TeleS GL n GL') (xg:TeleS GL l G) (Xi:VarItrp G i T t') :
VarItrp (CtxBump X xg) (varBump n l i) (elBump X xg T) (elBump X xg t').
	destruct Xi.
	apply (tr _ (eq_sym (envProj_Bump X xg i'))).
	apply varItrp.
Qed.

End VarItrpBump.

Module Type TERMITRPBUMP.

Declare Module Import CtxTyp : CTXTYP.

Module Import VarItrpBump := VarItrpBump CtxTyp.
Import Contex.

Declare Module Import TermBump : TERMBUMP.

Module VarSubst := VarSubst TermBump.

Parameter TermItrp : forall (G:Ctx) (t:term) (T:G->Typ) (t':forall g,T g),Type.

Axiom tmItrpVar : forall G i T t',VarItrp G i T t'->TermItrp G (tmVar i) T t'.

Axiom tmItrpBump : forall GL n GL' l G t T t' (X:TeleS GL n GL') (xg:TeleS GL l G),TermItrp G t T t'->
TermItrp (CtxBump X xg) (tmBump n l t) (elBump X xg T) (elBump X xg t').

End TERMITRPBUMP.

Module VarItrpSubst (Import TermItrpBump : TERMITRPBUMP).

Import CtxTyp VarItrpBump TermBump VarSubst.
Import Contex.

Lemma varItrpSubst GL B l G b b' i T t' (xg:TeleS (ExtCtx GL B) l G) (Xb:TermItrp GL b B b') (Xi:VarItrp G i T t') :
TermItrp (CtxSubst xg b') (varSubst l b i) (elSubst xg b' T) (elSubst xg b' t').
	destruct (lt_eq_lt_dec i l) as [s | Ho];[destruct s as [Ho | Ho] |];pattern (varSubst l b i).

	apply (tr _ (eq_sym (varSubstLt _ _ _ Ho))).
	apply tmItrpVar.
	destruct Xi.
	apply (tr _ (eq_sym (envProj_SubstLt xg b' i' (lt_ltd Ho)))).
	apply varItrp.

	apply (tr _ (eq_sym (varSubstEq _ _ _ Ho))).
	assert (Xl := tr (fun i=>VarItrp G i T t') Ho Xi).
	simpl in Xl.
	clear i Xi Ho.
	destruct Xl as (?,l').
	apply (tr (fun s=>TermItrp _ _ (projT1 s) (projT2 s)) (xcSubstEqUnExt xg b' l')).
	simpl.
	set (X := xc_xg' (xcSubst xg b')).
	change (TeleS GL l (CtxSubst xg b')) in (type of X).
	exact (tmItrpBump X (empTeleS GL) Xb).

	apply (tr _ (eq_sym (varSubstGt _ _ _ Ho))).
	apply tmItrpVar.
	revert Xi.
	destruct i.
		destruct (lt_n_O _ Ho).
	simpl.
	intro.
	destruct Xi.
	apply (tr _ (eq_sym (envProj_SubstGt xg b' i' (lt_ltd Ho)))).
	apply varItrp.
Qed.

End VarItrpSubst.

Module Type TYPESITRP.

Declare Module Import Types : TYPES.

Module VarOKBump := VarOKBump Types.

Declare Module Import TermItrpBump : TERMITRPBUMP with Module TermBump := TermBump.
Import CtxTyp VarItrpBump.Contex.

Parameter TypeItrp : forall (G:Ctx) (T:type) (T':G->Typ),Type.

Axiom tyItrpUniq : forall G T T1 T2,TypeItrp G T T1->TypeItrp G T T2->(T1 = T2).

Axiom tyItrpBump : forall GL n GL' l G T T' (X:TeleS GL n GL') (xg:TeleS GL l G) (XT:TypeItrp G T T'),
TypeItrp (CtxBump X xg) (tyBump n l T) (elBump X xg T').

Axiom tyItrpSubst : forall GL B l G b b' T T' (xg:TeleS (ExtCtx GL B) l G) (Xb:TermItrp GL b B b') (XT:TypeItrp G T T'),
TypeItrp (CtxSubst xg b') (tySubst l b T) (elSubst xg b' T').

End TYPESITRP.

Module ContexItrp (Import TypesItrp : TYPESITRP).

Import VarBump.

Import Types VarOKBump TermItrpBump.
Import CtxTyp VarItrpBump.
Import Contex.

(*
Inductive CtxItrp : list type->Ctx->Type :=
	ctxItrpNil : CtxItrp nil EmpCtx |
	ctxItrpCons T G G' T' : CtxItrp G G'->TypeItrp G' T T'->
		CtxItrp (T :: G) (ExtCtx G' T').
*)

Inductive CtxItrpCons T R : Ctx->Type :=
	ctxItrpCons G' T' : R G'->TypeItrp G' T T'->CtxItrpCons T R (ExtCtx G' T').
Arguments ctxItrpCons [T R G' T'] XG XT.

Fixpoint CtxItrp G : Ctx->Type := match G with
	nil => eq EmpCtx |
	T :: G => CtxItrpCons T (CtxItrp G)
end.

Lemma ctxItrpUniq G : forall G1 G2 (X1:CtxItrp G G1) (X2:CtxItrp G G2),G1 = G2.
	induction G as [| T];simpl;intros.

	destruct X1.
	destruct X2.
	reflexivity.

	destruct X1 as (G1,T1,XG1,XT1).
	destruct X2 as (G2,T2,XG2,XT2).
	revert T2 XT2.
	pattern G2.
	apply (tr _ (IHG _ _ XG1 XG2)).
	clear G2 XG2.
	intros.
	pattern T2.
	apply (tr _ (tyItrpUniq XT1 XT2)).
	reflexivity.
Qed.
Arguments ctxItrpUniq [G G1 G2] X1 X2.

Lemma ctxItrpProjNoBump i C : forall G G',(ltd i (length G))->CtxItrp G G'->
	(forall GL T (xg:TeleS GL (S i) G'),AtCtx G' i (fun g=>T (unExt xg g))->TypeItrp GL (nth i G tyDf) T->C)->
C.
	induction i;intros ? ?;(destruct G as [| T];intro;[destruct H |]);simpl;intro XG;
	destruct XG as (?,?,XG,XT);intro rtn.

	exact (rtn _ _ (extTeleS (empTeleS G') T') (topCtx G' T') XT).

	apply (IHi _ _ H XG).
	intros ? P xg i' XP.
	exact (rtn _ _ (extTeleS xg T') (popCtx i' T') XP).
Qed.
Arguments ctxItrpProjNoBump [i C G G'] _ XG _.

Lemma ctxItrpProj G G' (XG:CtxItrp G G') i C : (ltd i (length G))->
	(forall T,AtCtx G' i T->TypeItrp G' (tyBump (S i) O (nth i G tyDf)) T->C)->
C.
	intros ? rtn.
	apply (ctxItrpProjNoBump H XG).
	intros ? ? xg i' XT.
	exact (rtn _ i' (tyItrpBump xg (empTeleS _) XT)).
Qed.
Arguments ctxItrpProj [G G'] XG [i C] _ _.

Lemma varItrpTotal G G' i T (XG:CtxItrp G G') C : VarOK G i T->
	(forall T' (i':AtCtx G' i T'),TypeItrp G' T T'->VarItrp G' i T' (envProj i')->C)->
C.
	intro.
	destruct H.
	intro rtn.
	apply (ctxItrpProj XG (lt_ltd l)).
	intros ? i' ?.
	exact (rtn _ _ X (varItrp i')).
Qed.

End ContexItrp.
