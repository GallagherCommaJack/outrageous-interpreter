Require Import List.

Require Import Utils.
Require Import Substitutions.
Require Import TreeSyntax.
Require Import Context.
Require Import DepItrp.

Import VarBump.
Import TreeTermBump.
Import TreeTypes.
Import TreeVarOKBump.

Set Implicit Arguments.

(* Structured semantic types = type codes = universe construction *)

Module Import TypCode <: CTXTYP.

Inductive TypS : Type->Type :=
	typUvS : TypS Type |
	typElS T : TypS T |
	typPiS A (B:A->Type) : TypS A->(forall a,TypS (B a))->TypS (forall a,B a).
Arguments typPiS [A B] As Bs.

Example X2s : TypS (forall (X0:Type) (X1:forall (x0:X0),Type),forall (x0:X0) (x1:X1 x0),Type).
	exact (typPiS typUvS (fun X0=>
		typPiS (typPiS (typElS X0) (fun x0=>typUvS)) (fun X1=>
		typPiS (typElS X0) (fun x0=>
		typPiS (typElS (X1 x0)) (fun x1=>
		typUvS))))).
Qed.

Inductive TypR : Type := typ T (s:TypS T).

Definition Typ := TypR.

Definition TypTp (T:Typ) := match T with typ T _ => T end.
Coercion TypTp : Typ >-> Sortclass.

Definition typSc (T:Typ) : TypS T := match T with typ _ s => s end.

Definition TypUv : Typ := typ typUvS.
Definition TypEl T : Typ := typ (typElS T).
Definition TypPi (A:Typ) (B:A->Typ) : Typ := typ (typPiS (typSc A) (fun a=>typSc (B a))).

Definition IsTypUv (T:Typ) := match T with
	typ _ typUvS => True |
	_ => False
end.

Definition typUvUnfold T : IsTypUv T->(T = TypUv).
	destruct T.
	destruct s;simpl;intro;try solve [destruct H].
	reflexivity.
Defined.
Arguments typUvUnfold [T] H.

Definition IsTypPi (T:Typ) := match T with
	typ _ (typPiS _ _ _ _) => True |
	_ => False
end.

Definition TypDom (T:Typ) := match T with
	typ _ (typPiS _ _ A _) => typ A |
	_ => T
end.

Definition TypCdm T : TypDom T->Typ.
	destruct T.
	exact (match s return TypDom (typ s)->Typ with
		typPiS _ _ _ B => fun a=>typ (B a) |
		_ => fun _=>TypUv
	end).
Defined.

Definition typPiUnfold T : IsTypPi T->(T = TypPi (TypDom T) (TypCdm T)).
	destruct T.
	destruct s;simpl;intro;try solve [destruct H].
	reflexivity.
Defined.
Arguments typPiUnfold [T] H.

End TypCode.

Module Import CodeVarItrpBump := VarItrpBump TypCode.
Import Contex.

(* Interpretation relations *)

(*
Inductive TreeTermItrp (G:Ctx) : treeTerm->forall T:G->Typ,(forall g,T g)->Type :=
	ttItrpVar i T (i':AtCtx G i T) : TreeTermItrp G (var i) T (envProj i') |
	ttItrpApl f a A B f' a' : TreeTermItrp G f (fun g=>TypPi (A g) (B g)) f'->TreeTermItrp G a A a'->
		TreeTermItrp G (apl f a) (fun g=>B g (a' g)) (fun g=>f' g (a' g)).

Inductive TreeTypeItrp (G:Ctx) : treeType->(G->Typ)->Type :=
	tpItrpUv : TreeTypeItrp G Uv (fun g=>TypUv) |
	tpItrpEl t t' : TreeTermItrp G t (fun g=>TypUv) t'->TreeTypeItrp G (El t) (fun g=>TypEl (t' g)) |
	tpItrpPi A B A' B' : TreeTypeItrp G A A'->TreeTypeItrp (ExtCtx G A') B B'->
		TreeTypeItrp G (Pi A B) (fun g=>TypPi (A' g) (fun a=>B' (existT A' g a))).
*)

Inductive TTItrpApl (G:Ctx) (Rf Ra:forall T:G->Typ,(forall g,T g)->Type) : forall T:G->Typ,(forall g,T g)->Type :=
	ttItrpApl A B (Bs:forall g a,TypS (B g a)) f' a' : Rf (fun g=>TypPi (A g) (fun a=>typ (Bs g a))) f'->Ra A a'->
		TTItrpApl G Rf Ra (fun g=>typ (Bs g (a' g))) (fun g=>f' g (a' g)).
Arguments ttItrpApl [G Rf Ra A B] Bs [f' a'] Xf Xa.

Fixpoint TreeTermItrp G t := match t with
	var i => VarItrp G i |
	apl f a => TTItrpApl G (TreeTermItrp G f) (TreeTermItrp G a)
end.

Inductive TPItrpEl (G:Ctx) t : (G->Typ)->Type :=
	tpItrpEl t' : TreeTermItrp G t (fun g=>TypUv) t'->TPItrpEl G t (fun g=>TypEl (t' g)).
Arguments tpItrpEl [G t t'] Xt.

Inductive TPItrpPi (G:Ctx) (RA RB:forall G:Ctx,(G->Typ)->Type) : (G->Typ)->Type :=
	tpItrpPi A' B' (B's:forall g,TypS (B' g)) : RA G A'->RB (ExtCtx G A') (fun g=>typ (B's g))->
		TPItrpPi G RA RB (fun g=>TypPi (A' g) (fun a=>typ (B's (existT A' g a)))).
Arguments tpItrpPi [G RA RB A' B'] B's XA XB.

Fixpoint TreeTypeItrp (G:Ctx) T : (G->Typ)->Type := match T with
	Uv => eq (fun g=>TypUv) |
	El t => TPItrpEl G t |
	Pi A B => TPItrpPi G (fun G=>TreeTypeItrp G A) (fun G=>TreeTypeItrp G B)
end.

Definition sigTEqE A (P:A->Type) (s1 s2:sigT P) : (s1 = s2)->
{p:projT1 s1 = projT1 s2 & tr P p (projT2 s1) = projT2 s2}.
	intro.
	pattern s2.
	apply (tr _ H).
	exists eq_refl.
	simpl.
	reflexivity.
Defined.

(* Oops *)
Axiom UIP : forall T (x:T) (p:x = x),eq_refl x = p.

Definition projT2Eq A (P:A->Type) a (p1 p2:P a) : (existT P a p1 = existT P a p2)->(p1 = p2).
	intro.
	destruct (sigTEqE H).
	simpl in x,e.
	exact (tr (fun x=>tr P x p1 = p2) (eq_sym (UIP x)) e).
Defined.

Lemma ttItrpUniq G t : forall T1 T2 t1 t2 (X1:TreeTermItrp G t T1 t1) (X2:TreeTermItrp G t T2 t2),
existT (fun T:G->Typ=>forall g,T g) T1 t1 = existT _ T2 t2.
	set (Tt (T:G->Typ) := forall g,T g).
	induction t as [| f ? a ?];simpl;intros.

	exact (varItrpUniq X1 X2).

	destruct X1 as (A1,B1,Bs1,f1,a1,Xf1,Xa1).
	destruct X2 as (A2,B2,Bs2,f2,a2,Xf2,Xa2).
	simpl in f1,f2.
	revert B2 Bs2 f2 Xf2.
	apply (tr (fun x:sigT Tt=>forall B2 (Bs2:forall g a,TypS (B2 g a)) f2
		(Xf2:TreeTermItrp G f (fun g=>TypPi (projT1 x g) (fun a=>typ (Bs2 g a))) f2),
		_ = existT Tt (fun g=>typ (Bs2 g (projT2 x g))) (fun g=>f2 g (projT2 x g)))
	(IHt2 _ _ _ _ Xa1 Xa2)).
	simpl.
	clear IHt2 A2 a2 Xa2.
	intros.
	pose proof (IHt1 _ _ _ _ Xf1 Xf2).
	clear IHt1 Xf1 Xf2.
	pose (ABf1 := existT Tt (fun g=>TypPi (A1 g) (fun a=>typ (Bs1 g a))) f1).
	pose (ABf2 := existT Tt (fun g=>TypPi (A1 g) (fun a=>typ (Bs2 g a))) f2).
	change (ABf1 = ABf2) in H.
	pose (A (s:sigT Tt) g := TypTp (TypDom (projT1 s g))).
	pose (BR (s:sigT Tt) g := TypCdm (projT1 s g)).
	change (forall s g,A s g->Typ) in (type of BR).
	pose (fT (A:G->Type) (BR:forall g,A g->Typ) := forall g a,BR g a).
	assert (existT (fun A=>sigT (fT A)) (A ABf1) (existT (fT _) (BR ABf1) (projT2 ABf1)) =
	existT _ (A ABf2) (existT _ (BR ABf2) (projT2 ABf2))).
		generalize (fun g:G=>I).
		apply (tr (fun s=>forall H:forall g,IsTypPi (projT1 s g),_ =
			existT (fun A=>sigT (fT A)) (A s) (existT (fT _) (BR s) (fun g=>tr _ (typPiUnfold (H g)) (projT2 s g))))
		H).
		simpl.
		intros _.
		change (fun g=>f1 g) with f1.
		reflexivity.
	clear H.
	subst ABf1 ABf2 A BR.
	simpl in H0.
	pose proof (projT2Eq H0).
	clear H0.
	apply (tr (fun x:sigT (fT A1)=>_ = existT Tt (fun g=>projT1 x g (a1 g)) (fun g=>projT2 x g (a1 g))) H).
	simpl.
	reflexivity.
Qed.
Arguments ttItrpUniq [G t T1 T2 t1 t2] X1 X2.

Lemma tpItrpUniq T : forall G T1 T2 (X1:TreeTypeItrp G T T1) (X2:TreeTypeItrp G T T2),T1 = T2.
	induction T as [| | A ? B ?];simpl;intros.

	destruct X1.
	destruct X2.
	reflexivity.

	destruct X1 as (t1,X1).
	destruct X2 as (t2,X2).
	generalize (fun g:G=>I).
	apply (tr (fun s:{T:G->Typ & forall g,T g}=>forall H:forall g,IsTypUv (projT1 s g),
		_ = fun g=>TypEl (tr _ (typUvUnfold (H g)) (projT2 s g))) (ttItrpUniq X1 X2)).
	simpl.
	intros _.
	reflexivity.

	destruct X1 as (A1,B1,Bs1,XA1,XB1).
	destruct X2 as (A2,B2,Bs2,XA2,XB2).
	revert B2 Bs2 XB2.
	pattern A2.
	apply (tr _ (IHT1 _ _ _ XA1 XA2)).
	clear A2 XA2.
	intros.
	apply (tr (fun Bf=>_ = fun g=>TypPi (A1 g) (fun a=>Bf (existT A1 g a))) (IHT2 _ _ _ XB1 XB2)).
	reflexivity.
Qed.
Arguments tpItrpUniq [T G T1 T2] X1 X2.

Lemma ttItrpBump GL n GL' l G t (X:TeleS GL n GL') (xg:TeleS GL l G) : forall T t' (Xt:TreeTermItrp G t T t'),
TreeTermItrp (CtxBump X xg) (ttBump n l t) (elBump X xg T) (elBump X xg t').
	induction t as [| f ? a ?];simpl;intros.

	exact (varItrpBump X xg Xt).

	destruct Xt as (?,?,?,?,?,Xf,Xa).
	exact (ttItrpApl (elBump X xg Bs) (IHt1 _ _ Xf) (IHt2 _ _ Xa)).
Qed.
Arguments ttItrpBump [GL n GL' l G t] X xg [T t'] Xt.

Lemma tpItrpBump GL n GL' T (X:TeleS GL n GL') : forall l G T' (xg:TeleS GL l G) (XT:TreeTypeItrp G T T'),
TreeTypeItrp (CtxBump X xg) (tpBump n l T) (elBump X xg T').
	induction T as [| | A ? B ?];simpl;intros.

	destruct XT.
	reflexivity.

	destruct XT as (?,Xt).
	exact (tpItrpEl (ttItrpBump X xg Xt)).

	destruct XT as (?,?,?,XA,XB).
	apply tpItrpPi with (A' := elBump X xg A') (B' := elBump X (extTeleS xg A') B') (B's := elBump X (extTeleS xg A') B's).
		exact (IHT1 _ _ _ xg XA).

		exact (IHT2 _ _ _ (extTeleS xg A') XB).
Qed.
Arguments tpItrpBump [GL n GL' T] X [l G T'] xg XT.

Module Import TreeTermItrpBump <: TERMITRPBUMP.

Module CtxTyp := TypCode.
Module VarItrpBump := CodeVarItrpBump.
Module TermBump := TreeTermBump.
Module VarSubst := TreeVarSubst.

Definition TermItrp := TreeTermItrp.
Definition tmItrpVar G i T t' (Xi:VarItrp G i T t') := Xi.
Definition tmItrpBump GL n GL' l G t T t' (X:TeleS GL n GL') (xg:TeleS GL l G) : TermItrp G t T t'->_ := ttItrpBump X xg (t' := t').

End TreeTermItrpBump.

Module Import TreeVarItrpSubst := VarItrpSubst TreeTermItrpBump.

Lemma ttItrpSubst GL B l G b b' t (xg:TeleS (ExtCtx GL B) l G) (Xb:TreeTermItrp GL b B b') : forall T t' (Xt:TreeTermItrp G t T t'),
TreeTermItrp (CtxSubst xg b') (ttSubst l b t) (elSubst xg b' T) (elSubst xg b' t').
	induction t as [| f ? a ?];simpl;intros.

	exact (varItrpSubst xg Xb Xt).

	destruct Xt as (?,?,?,?,?,Xf,Xa).
	exact (ttItrpApl (elSubst xg b' Bs) (IHt1 _ _ Xf) (IHt2 _ _ Xa)).
Qed.
Arguments ttItrpSubst [GL B l G b b' t] xg Xb [T t'] Xt.

Lemma tpItrpSubst GL B l G b b' T (xg:TeleS (ExtCtx GL B) l G) (Xb:TreeTermItrp GL b B b') : forall T' (XT:TreeTypeItrp G T T'),
TreeTypeItrp (CtxSubst xg b') (tpSubst l b T) (elSubst xg b' T').
	revert l G xg.
	induction T as [| | A ? B0 ?];simpl;intros.

	destruct XT.
	reflexivity.

	destruct XT as (?,Xt).
	exact (tpItrpEl (ttItrpSubst xg Xb Xt)).

	destruct XT as (?,?,?,XA,XB).
	apply tpItrpPi with (A' := elSubst xg b' A') (B' := elSubst (extTeleS xg A') b' B') (B's := elSubst (extTeleS xg A') b' B's).
		exact (IHT1 _ _ xg _ XA).

		exact (IHT2 _ _ (extTeleS xg A') _ XB).
Qed.
Arguments tpItrpSubst [GL B l G b b' T] xg Xb [T'] XT.

Module Import TreeTypesItrp <: TYPESITRP.

Module Types := TreeTypes.
Module VarOKBump := TreeVarOKBump.
Module TermItrpBump := TreeTermItrpBump.

Definition TypeItrp := TreeTypeItrp.

Definition tyItrpUniq G T T1 T2 : TypeItrp G T T1->TypeItrp G T T2->_ := tpItrpUniq (T2 := T2).
Definition tyItrpBump GL n GL' l G T T' (X:TeleS GL n GL') : forall xg:TeleS GL l G,TypeItrp G T T'->_ := tpItrpBump X (T' := T').
Definition tyItrpSubst GL B l G b b' T T' (xg:TeleS _ l G) (Xb:TermItrp GL b B b') : TypeItrp G T T'->_ := tpItrpSubst xg Xb (T' := T').

End TreeTypesItrp.

Module Import TreeContexItrp := ContexItrp TreeTypesItrp.

Inductive ExTreeTermItrp G t T : Type :=
	exTreeTermItrp T' t' : TreeTermItrp G t T' t'->TreeTypeItrp G T T'->ExTreeTermItrp G t T.
Arguments exTreeTermItrp [G t T] T' t' Xt XT.

Lemma ttItrpTotal (G:list treeType) (G':Ctx) t T (XG:CtxItrp G G') : TreeTermOK G t T->ExTreeTermItrp G' t T.
	intro.
	induction H.

	apply (varItrpTotal XG v).
	intros ? ? XT Xi.
	apply (exTreeTermItrp T' (envProj i')) with (1 := Xi) (2 := XT).

	clear H H0.
	destruct IHTreeTermOK1 as (T,f',Xf).
	simpl in t.
	destruct t as (A1,?,?,XA1,XB).
	simpl in f'.
	destruct IHTreeTermOK2 as (A2,a',Xa,XA2).
	revert a' Xa.
	pattern A2.
	apply (tr _ (tpItrpUniq XA1 XA2)).
	clear A2 XA2.
	intros.
	apply (exTreeTermItrp (fun g=>typ (B's (existT A1 g (a' g)))) (fun g=>f' g (a' g))).
		simpl.
		exact (ttItrpApl _ Xf Xa).

		exact (tpItrpSubst (empTeleS _) Xa XB).
Qed.
Arguments ttItrpTotal [G G' t T] XG _.

Lemma tpItrpTotal' G T C : TreeTypeOK G T->forall (G':Ctx) (XG:CtxItrp G G'),
	(forall T' (T's:forall g,TypS (T' g)),TreeTypeItrp G' T (fun g=>typ (T's g))->C)->
C.
	intro.
	induction H;intros ? ? rtn.

	apply (rtn _ (fun g=>typUvS)).
	reflexivity.

	destruct (ttItrpTotal XG t0) as (?,?,Xt,XU).
	revert t' Xt.
	destruct XU.
	intros.
	apply (rtn _ (fun g=>typElS (t' g))).
	exact (tpItrpEl Xt).

	clear H H0.
	apply (IHTreeTypeOK1 _ XG).
	intros A' A's XA.
	apply (IHTreeTypeOK2 (ExtCtx G' (fun g=>typ (A's g))) (ctxItrpCons XG XA)).
	intros B' B's XB.
	apply (rtn _ (fun g=>typPiS (A's g) (fun a=>B's (existT A' g a)))).
	simpl.
	exact (tpItrpPi _ XA XB).
Qed.
Arguments tpItrpTotal' [G T C] _ [G'] XG _.

Lemma tpItrpTotal G T C : TreeTypeOK G T->forall (G':Ctx) (XG:CtxItrp G G'),
	(forall T',TreeTypeItrp G' T T'->C)->
C.
	intros ? ? ? rtn.
	apply (tpItrpTotal' H XG).
	intros ? ? XT.
	exact (rtn _ XT).
Qed.
Arguments tpItrpTotal [G T C] _ [G'] XG _.
