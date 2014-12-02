Require Import List.

Require Import Utils.
Require Import Context.
Require Import SimpSubst.
Require Import SimpSyntax.
Require Import TreeSyntax.

(* Structured semantic types = type codes = universe construction *)

Module Import TypCode <: CTXTYP.

Inductive TypS : Type->Type :=
	typUvS : TypS Type |
	typElS T : TypS T |
	typPiS A (B:A->Type) : TypS A->(forall a,TypS (B a))->TypS (forall a,B a).
Implicit Arguments typPiS [A B].

Example X2s : TypS (forall (X0:Type) (X1:forall (x0:X0),Type),forall (x0:X0) (x1:X1 x0),Type).
	exact (typPiS typUvS (fun X0=>
		typPiS (typPiS (typElS X0) (fun x0=>typUvS)) (fun X1=>
		typPiS (typElS X0) (fun x0=>
		typPiS (typElS (X1 x0)) (fun x1=>
		typUvS))))).
Qed.

Inductive TypR : Type := typ T (s:TypS T).
Implicit Arguments typ [T].

Definition Typ := TypR.

Definition typTp (T:Typ) := match T with typ T _ => T end.
Coercion typTp : Typ >-> Sortclass.

Definition typSc (T:Typ) : TypS T := match T with typ _ s => s end.

Definition typUv : Typ := typ typUvS.
Definition typEl T : Typ := typ (typElS T).
Definition typPi (A:Typ) (B:A->Typ) : Typ := typ (typPiS (typSc A) (fun a=>typSc (B a))).

Definition IsTypPi (T:Typ) := match T with
	typ _ (typPiS _ _ _ _) => True |
	_ => False
end.

Definition typDom (T:Typ) := match T with
	typ _ (typPiS _ _ A _) => typ A |
	_ => T
end.

Definition typCdm T : typDom T->Typ.
	destruct T.
	exact (match s as s return typDom (typ s)->Typ with
		typPiS _ _ _ B => fun a=>typ (B a) |
		_ => fun _=>typUv
	end).
Defined.

End TypCode.

Module Import CodeContex := Contex TypCode.

(* Interpretation relations *)

(*
Inductive SimpParamItrp (G:Ctx) (F:G->Typ) : list nat->forall T:G->Typ,(forall g,F g->T g)->Type :=
	spItrpNil : SimpParamItrp G F nil F (fun g f=>f) |
	spItrpCons a la T P (a':AtCtx G a P) B la' :
		SimpParamItrp G F la (fun g=>typPi (P g) (fun p=>B g p)) la'->
		SimpParamItrp G F (a :: la) (fun g=>B g (ctxProj a' g)) (fun g f=>la' g f (ctxProj a' g)).

Inductive TreeFamItrp (G:Ctx) : treeFam->(G->Typ)->Type :=
	tfItrpUv : TreeFamItrp G Uv (fun g=>typUv) |
	tfItrpEl f la F (f':AtCtx G f F) la' :
		SimpParamItrp G F la (fun g=>typUv) la'->
		TreeFamItrp G (El (f,la)) (fun g=>typEl (la' g (ctxProj f' g))) |
	tfItrpPi A B A' B' : TreeFamItrp G A A'->TreeFamItrp (extCtx G A') B B'->
		TreeFamItrp G (Pi A B) (fun g=>typPi (A' g) (fun a=>B' (existT A' g a))).
*)

Inductive SPItrpNil (G:Ctx) (F:G->Typ) : forall T:G->Typ,(forall g,F g->T g)->Type :=
	spItrpNil : SPItrpNil G F F (fun g f=>f).
Implicit Arguments spItrpNil [G].

Inductive SPItrpCons (G:Ctx) (F:G->Typ) a (R:forall T:G->Typ,(forall g,F g->T g)->Type) :
forall T:G->Typ,(forall g,F g->T g)->Type :=
	spItrpCons P (a':AtCtx G a P) B (BS:forall g p,TypS (B g p)) la' :
		R (fun g=>typPi (P g) (fun p=>typ (BS g p))) la'->
		SPItrpCons G F a R (fun g=>typ (BS g (ctxProj a' g))) (fun g f=>la' g f (ctxProj a' g)).
Implicit Arguments spItrpCons [G F a R P B la'].

Fixpoint SimpParamItrp G F la : forall T,_->Type := match la with
	nil => SPItrpNil G F |
	a :: la => SPItrpCons G F a (SimpParamItrp G F la)
end.

Inductive TFItrpEl (G:Ctx) f la : (G->Typ)->Type :=
	tfItrpEl F (f':AtCtx G f F) la' :
		SimpParamItrp G F la (fun g=>typUv) la'->
		TFItrpEl G f la (fun g=>typEl (la' g (ctxProj f' g))).
Implicit Arguments tfItrpEl [G f la F la'].

Inductive TFItrpPi (G:Ctx) (RA RB:forall G:Ctx,(G->Typ)->Type) : (G->Typ)->Type :=
	tfItrpPi A' B' (B'S:forall g,TypS (B' g)) : RA G A'->RB (extCtx G A') (fun g=>typ (B'S g))->
		TFItrpPi G RA RB (fun g=>typPi (A' g) (fun a=>typ (B'S (existT A' g a)))).
Implicit Arguments tfItrpPi [G RA RB A' B' B'S].

Fixpoint TreeFamItrp (G:Ctx) F : (G->Typ)->Type := match F with
	Uv => eq (fun g=>typUv) |
	El (f,la) => TFItrpEl G f la |
	Pi A B => TFItrpPi G (fun G=>TreeFamItrp G A) (fun G=>TreeFamItrp G B)
end.

(*
Inductive TreeCtxItrp : list treeFam->Ctx->Type :=
	tcItrpNil : TreeCtxItrp nil empCtx |
	tcItrpCons G F G' F' : TreeCtxItrp G G'->TreeFamItrp G' F F'->
		TreeCtxItrp (F :: G) (extCtx G' F').
*)

Inductive TCItrpCons R F : Ctx->Type :=
	tcItrpCons G' F' : R G'->TreeFamItrp G' F F'->TCItrpCons R F (extCtx G' F').
Implicit Arguments tcItrpCons [R F G' F'].

Fixpoint TreeCtxItrp G : Ctx->Type := match G with
	nil => eq empCtx |
	F :: G => TCItrpCons (TreeCtxItrp G) F
end.

Definition sigTEqE A (P:A->Type) (s1 s2:sigT P) : (s1 = s2)->
{p:projT1 s1 = projT1 s2 & tr P p (projT2 s1) = projT2 s2}.
	intro.
	pattern s2.
	apply (tr _ H).
	exists (eq_refl _).
	simpl.
	reflexivity.
Defined.
Implicit Arguments sigTEqE [A P s1 s2].

(* Oops *)
Axiom UIP : forall T (x:T) (p:x = x),eq_refl x = p.
Implicit Arguments UIP [T x].

Definition projT2Eq A (P:A->Type) a (p1 p2:P a) : (existT P a p1 = existT P a p2)->(p1 = p2).
	intro.
	destruct (sigTEqE H).
	simpl in x,e.
	revert e.
	apply (tr (fun x=>tr P x p1 = p2->_) (UIP x)).
	simpl.
	exact (fun p=>p).
Defined.
Implicit Arguments projT2Eq [A P a p1 p2].

Lemma spItrpUniq G F la : forall T1 T2 la1 la2,SimpParamItrp G F la T1 la1->SimpParamItrp G F la T2 la2->
(existT (fun T:G->Typ=>forall g,F g->T g) T1 la1 = existT _ T2 la2).
	set (Tla (T:G->Typ) := forall g,F g->T g).
	induction la;simpl;intros.

	destruct H.
	destruct H0.
	reflexivity.

	destruct X as (P1,a1,B1,BS1,la1).
	destruct X0 as (P2,a2,B2,BS2,la2).
	simpl in la1,la2.
	revert B2 BS2 la2 s0.
	apply (tr (fun xa=>forall B2 (BS2:forall g p,TypS (B2 g p)) la2,
		SimpParamItrp G F la (fun g=>typPi (xa_T xa g) (fun p=>typ (BS2 g p))) la2->
		(_ = existT Tla (fun g=>typ (BS2 g (ctxProj (xa_a xa) g)))
			(fun g f=>la2 g f (ctxProj (xa_a xa) g))))
	(atCtxUniq a1 a2)).
	simpl.
	clear P2 a2.
	intros.
	pose proof (IHla _ _ _ _ s X).
	clear IHla s X.
	pose (PBla1 := existT Tla (fun g=>typPi (P1 g) (fun p=>typ (BS1 g p))) la1).
	pose (PBla2 := existT Tla (fun g=>typPi (P1 g) (fun p=>typ (BS2 g p))) la2).
	change (PBla1 = PBla2) in H.
	pose (P (s:sigT Tla) g := typTp (typDom (projT1 s g))).
	pose (BR (s:sigT Tla) g := typCdm (projT1 s g)).
	change (forall s g,P s g->Typ) in (type of BR).
	assert {p:P PBla1 = P PBla2 & tr (fun P=>forall g,P g->Typ) p (BR PBla1) = BR PBla2}.
		rewrite <- H.
		exists (eq_refl _).
		simpl.
		reflexivity.
	destruct H0 as (PH,BRH).
	rewrite <- (UIP PH) in BRH.
	simpl in BRH.
	clear PH.
	subst P BR.
	simpl in BRH.
	revert la2 PBla2 H.
	apply (tr (fun X=>forall la2,
		let PBla2 := existT Tla (fun g=>typPi (P1 g) (fun p=>X g p)) la2 in
		(PBla1 = PBla2)->
		(_ = existT Tla (fun g=>X g (ctxProj a1 g)) (fun g f=>la2 g f (ctxProj a1 g))))
	BRH).
	unfold Tla at 1.
	simpl typTp.
	clear B2 BS2 BRH.
	intros.
	rewrite <- (projT2Eq H).
	reflexivity.
Qed.
Implicit Arguments spItrpUniq [G F la T1 T2 la1 la2].

Lemma tfItrpUniq F : forall G F1 F2,TreeFamItrp G F F1->TreeFamItrp G F F2->(F1 = F2).
	induction F as [| | A ? B ?];[| destruct p as (f,la) |];simpl;intros.

	rewrite <- H.
	rewrite <- H0.
	reflexivity.

	destruct X as (F1,f1,la1).
	destruct X0 as (F2,f2,la2).
	revert la2 s0.
	apply (tr (fun xa=>forall la2,SimpParamItrp G (xa_T xa) la (fun g=>typUv) la2->
		(_ = fun g=>typEl (la2 g (ctxProj (xa_a xa) g)))) (atCtxUniq f1 f2)).
	simpl.
	clear F2 f2.
	intros.
	pose (el' T la' g :=
		match T g as Tg return (F1 g->typTp Tg)->Typ with typ _ s =>
		match s return (F1 g->typTp (typ s))->Typ with
			typUvS => fun lag=>typEl (lag (ctxProj f1 g)) |
			_ => fun _=>typUv
		end end (la' g)).
	simpl in el'.
	change ((fun g=>typEl (la1 g (ctxProj f1 g))) = el' (fun g=>typUv) la2).
	apply (tr (fun Tla=>_ = el' _ (projT2 Tla)) (spItrpUniq s X)).
	subst el'.
	simpl.
	reflexivity.

	destruct X as (A1,B1,BS1).
	destruct X0 as (A2,B2,BS2).
	revert B2 BS2 t2.
	rewrite <- (IHF1 _ _ _ t t1).
	clear A2 t1.
	intros.
	apply (tr (fun X=>_ = fun g=>typPi (A1 g) (fun a=>X (existT A1 g a))) (IHF2 _ _ _ t0 t2)).
	reflexivity.
Qed.
Implicit Arguments tfItrpUniq [F G F1 F2].

Lemma tcItrpUniq G : forall G1 G2,TreeCtxItrp G G1->TreeCtxItrp G G2->(G1 = G2).
	induction G;simpl;intros.

	rewrite <- H.
	rewrite <- H0.
	reflexivity.

	destruct X as (G1,F1).
	destruct X0 as (G2,F2).
	revert F2 t2.
	rewrite <- (IHG _ _ t t1).
	clear G2 t1.
	intros.
	rewrite <- (tfItrpUniq t0 t2).
	reflexivity.
Qed.
Implicit Arguments tcItrpUniq [G G1 G2].

Lemma spItrpBump G F n l la GL P (xg:ExtCtx GL l G) : forall T la',SimpParamItrp G F (laBump n l la) T la'->
SimpParamItrp (ctxBump P xg) (elBump P xg F) (laBump (S n) l la) (elBump P xg T) (elBump P xg la').
	induction la;simpl.

	intros.
	destruct H.
	apply spItrpNil.

	intros.
	destruct X.
	pose proof (spItrpCons (atBump P xg a') (elBump P xg BS) (IHla _ _ s)).
	rewrite <- ctxProj_Bump in X.
	exact X.
Qed.
Implicit Arguments spItrpBump [G F n l la GL T la'].

Lemma spItrpBump_O G F n la T la' P : SimpParamItrp G F (laBump n O la) T la'->
SimpParamItrp (extCtx G P) (fun g=>F (projT1 g)) (laBump (S n) O la) (fun g=>T (projT1 g)) (fun g=>la' (projT1 g)).
	apply (spItrpBump P (extOCtx G)).
Qed.
Implicit Arguments spItrpBump_O [G F n la T la'].

Lemma tfItrpBump n F GL P : forall G l F' (xg:ExtCtx GL l G),TreeFamItrp G (fBump n l F) F'->
TreeFamItrp (ctxBump P xg) (fBump (S n) l F) (elBump P xg F').
	induction F as [| | A ? B ?];[| destruct p as (f,la) |];simpl;intros.

	rewrite <- H.
	reflexivity.

	destruct X.
	pose proof (tfItrpEl (atBump P xg f') (spItrpBump P xg s)).
	rewrite <- ctxProj_Bump in X.
	exact X.

	destruct X.
	apply (tfItrpPi (A' := elBump P xg A')
	(B'S := fun g=>B'S (existT _ (xc_f' (xcBump P xg) (projT1 g)) (projT2 g)))).
		exact (IHF1 _ _ _ _ t).

		exact (IHF2 _ _ _ (extSCtx xg A') t0).
Qed.
Implicit Arguments tfItrpBump [n F GL G l F'].

Lemma tfItrpBump_O G n F F' P : TreeFamItrp G (fBump n O F) F'->
TreeFamItrp (extCtx G P) (fBump (S n) O F) (fun g=>F' (projT1 g)).
	apply (tfItrpBump P (extOCtx G)).
Qed.
Implicit Arguments tfItrpBump_O [G n F F'].

Lemma spItrpSubst G F la l b GL P (xg:ExtCtx (extCtx GL P) l G) (b':AtCtx GL b P) : forall T la',
	SimpParamItrp G F la T la'->
SimpParamItrp (ctxSubst xg (ctxProj b')) (elSubst xg F (ctxProj b')) (laSubst la l b)
(elSubst xg T (ctxProj b')) (elSubst xg la' (ctxProj b')).
	induction la;simpl;intros.

	destruct H.
	apply spItrpNil.

	destruct X.
	pose proof (spItrpCons (atSubst xg b' a') (elSubst xg BS (ctxProj b')) (IHla _ _ s)).
	rewrite <- ctxProj_Subst in X.
	exact X.
Qed.
Implicit Arguments spItrpSubst [G F la l b GL P T la'].

Lemma spItrpSubst_O G P F la b T la' (b':AtCtx G b P) : SimpParamItrp (extCtx G P) F la T la'->
SimpParamItrp G (fun g=>F (existT _ g (ctxProj b' g))) (laSubst la O b) _ (fun g=>la' (existT _ g (ctxProj b' g))).
	apply (spItrpSubst (extOCtx (extCtx G P)) b').
Qed.
Implicit Arguments spItrpSubst_O [G P F la b T la'].

Lemma tfItrpSubst F b GL P (b':AtCtx GL b P) : forall G l F' (xg:ExtCtx (extCtx GL P) l G),TreeFamItrp G F F'->
TreeFamItrp (ctxSubst xg (ctxProj b')) (fSubst F l b) (elSubst xg F' (ctxProj b')).
	induction F as [| | A ? B ?];[| destruct p as (f,la) |];simpl;intros.

	rewrite <- H.
	reflexivity.

	destruct X.
	pose proof (tfItrpEl (atSubst xg b' f') (spItrpSubst xg b' s)).
	rewrite <- ctxProj_Subst in X.
	exact X.

	destruct X.
	apply (tfItrpPi (A' := elSubst xg A' (ctxProj b'))
	(B'S := fun g=>B'S (existT _ (xc_f' (xcSubst xg _) (projT1 g)) (projT2 g)))).
		exact (IHF1 _ _ _ _ t).

		exact (IHF2 _ _ _ (extSCtx xg A') t0).
Qed.
Implicit Arguments tfItrpSubst [F b GL P G l F'].

Lemma tfItrpSubst_O G P F b F' (b':AtCtx G b P) : TreeFamItrp (extCtx G P) F F'->
TreeFamItrp G (fSubst F O b) (fun g=>F' (existT _ g (ctxProj b' g))).
	apply (tfItrpSubst b' (extOCtx (extCtx G P))).
Qed.
Implicit Arguments tfItrpSubst_O [G P F b F'].

Lemma tcItrpProj i C : forall G G',(ltd i (length G))->TreeCtxItrp G G'->
	(forall F,AtCtx G' i F->TreeFamItrp G' (fBump (S i) O (nth i G Uv)) F->C)->
C.
	induction i;intros ? ?;(destruct G as [| F];intro;[destruct H |]);simpl;intro;
	destruct X;intro rtn.

	apply (rtn _ (topCtx G' F')).
	apply tfItrpBump_O.
	rewrite fBump_O.
	exact t0.

	apply (IHi _ _ H t).
	intros.
	apply (rtn _ (popCtx X F')).
	apply tfItrpBump_O.
	exact X0.
Qed.
Implicit Arguments tcItrpProj [i C G G'].

Inductive ExSimpParamItrp G F la T : Type :=
	exSimpParamItrp T' la' : SimpParamItrp G F la T' la'->TreeFamItrp G T T'->ExSimpParamItrp G F la T.
Implicit Arguments exSimpParamItrp [G F la T].

Lemma tfItrpTotalNest' G F C : TreeFamGood
	(fun G F la T=>forall G' F',TreeCtxItrp G G'->TreeFamItrp G' F F'->ExSimpParamItrp G' F' la T) G F->
forall G',TreeCtxItrp G G'->
	(forall F' (F'S:forall g,TypS (F' g)),TreeFamItrp G' F (fun g=>typ (F'S g))->C)->
C.
	intro.
	induction X;intros ? XG rtn.

	apply (rtn _ (fun g=>typUvS)).
	reflexivity.

	apply (tcItrpProj (lt_ltd l) XG).
	intros ? f' XF.
	destruct (p _ _ XG XF) as (?,?,Xla,XU).
	simpl in XU.
	revert la' Xla.
	rewrite <- XU.
	clear T' XU.
	intros.
	apply (rtn _ (fun g=>typElS (la' g (ctxProj f' g)))).
	exact (tfItrpEl f' Xla).

	clear X1 X2.
	apply (IHX1 _ XG).
	intros A' A'S XA.
	apply (IHX2 (extCtx G' (fun g=>typ (A'S g)))).
		simpl.
		exact (tcItrpCons XG XA).
	intros B' B'S XB.
	apply (rtn _ (fun g=>typPiS (A'S g) (fun a=>B'S (existT (fun g=>A' g) g a)))).
	simpl.
	exact (tfItrpPi XA XB).
Qed.

Lemma tfItrpTotalNest G F C : TreeFamGood
	(fun G F la T=>forall G' F',TreeCtxItrp G G'->TreeFamItrp G' F F'->ExSimpParamItrp G' F' la T) G F->
forall G',TreeCtxItrp G G'->
	(forall F',TreeFamItrp G' F F'->C)->
C.
	intros ? ? XG rtn.
	apply tfItrpTotalNest' with (1 := X) (2 := XG).
	intros ? ? XF.
	exact (rtn _ XF).
Qed.

Lemma spItrpTotal G F la T : SimpParamGood G F la T->forall G' F',TreeCtxItrp G G'->TreeFamItrp G' F F'->
ExSimpParamItrp G' F' la T.
	intro.
	induction H;intros ? ? XG XF.

	apply (exSimpParamItrp F' (fun g f=>f)).
		apply spItrpNil.

		exact XF.

	apply (tcItrpProj (lt_ltd H) XG).
	intros A a' XA.
	destruct (IHSimpParamGood _ _ XG XF) as (?,?,Xla,XT).
	simpl in XT.
	revert la' Xla.
	destruct XT as (A0,B',B'S,XA0,XB).
	simpl.
	revert B' B'S XB.
	rewrite <- (tfItrpUniq XA XA0).
	clear A0 XA0.
	intros.
	apply (exSimpParamItrp (fun g=>typ (B'S (existT _ g (ctxProj a' g))))
	(fun g f=>la' g f (ctxProj a' g))).
		simpl.
		exact (spItrpCons a' (fun g a=>B'S (existT _ g a)) Xla).

		exact (tfItrpSubst_O _ XB).
Qed.

Lemma tfItrpTotal G F G' C : TreeFamGoodPG G F->TreeCtxItrp G G'->
	(forall F',TreeFamItrp G' F F'->C)->
C.
	intros ? XG.
	apply tfItrpTotalNest with (G := G) (2 := XG).
	exact (tfGoodMap spItrpTotal H).
Qed.
