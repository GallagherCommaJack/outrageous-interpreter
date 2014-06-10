(* Structured semantic types = type codes = universe construction *)

Module TypCode <: CTXTYP.

Inductive TypS : Type->Type :=
	typUvS : TypS Type |
	typElS T : TypS T |
	typPiS A (B:A->Type) : TypS A->(forall a,TypS (B a))->TypS (forall a,B a).
Implicit Arguments typPiS [A B].

Inductive TypR : Type := typ T (s:TypS T).
Implicit Arguments typ [T].

Definition Typ := TypR.

Definition typTp (T:Typ) := match T with typ T _ => T end.
Coercion typTp : Typ >-> Sortclass.

Definition typSc (T:Typ) : TypS T := match T with typ _ s => s end.

Example X2s : TypS (forall (X0:Type) (X1:forall (x0:X0),Type),forall (x0:X0) (x1:X1 x0),Type).
	exact (typPiS typUvS (fun X0=>
		typPiS (typPiS (typElS X0) (fun x0=>typUvS)) (fun X1=>
		typPiS (typElS X0) (fun x0=>
		typPiS (typElS (X1 x0)) (fun x1=>
		typUvS))))).
Qed.

Definition typUv : Typ := typ typUvS.
Definition typEl T : Typ := typ (typElS T).
Definition typPi (A:Typ) (B:A->Typ) : Typ := typ (typPiS (typSc A) (fun a=>typSc (B a))).

End TypCode.
Import TypCode.

Module CodeContex := Contex TypCode.
Import CodeContex.

(* Interpretation relations *)

(*
Inductive SimpParamItrp (G:Ctx) (F:G->Typ) : list nat->forall T:G->Typ,(forall g,F g->T g)->Type :=
	spItrpNil : SimpParamItrp G F nil F (fun g f=>f) |
	spItrpCons a la P (a':AtCtx G a P) B la' :
		SimpParamItrp G F la (fun g=>typPi (P g) (fun p=>B (existT P g p))) la'->
		SimpParamItrp G F (a :: la) (fun g=>B (existT P g (ctxProj a' g))) (fun g f=>la' g f (ctxProj a' g)).

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
	spItrpCons P (a':AtCtx G a P) B la' :
		R (fun g=>typPi (P g) (fun p=>B (existT P g p))) la'->
		SPItrpCons G F a R (fun g=>B (existT P g (ctxProj a' g))) (fun g f=>la' g f (ctxProj a' g)).
Implicit Arguments spItrpCons [G F a R P la'].

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
	tfItrpPi A' B' : RA G A'->RB (extCtx G A') B'->
		TFItrpPi G RA RB (fun g=>typPi (A' g) (fun a=>B' (existT A' g a))).
Implicit Arguments tfItrpPi [G RA RB A' B'].

Fixpoint TreeFamItrp (G:Ctx) F : (G->Typ)->Type := match F with
	Uv => eq (fun g=>typUv) |
	El (f,la) => TFItrpEl G f la |
	Pi A B => TFItrpPi G (fun G=>TreeFamItrp G A) (fun G=>TreeFamItrp G B)
end.

Lemma atCtxEta' G n : forall T (a:AtCtx G n T),AtCtx G n (fun g=>typ (typSc (T g))).
Admitted.
Implicit Arguments atCtxEta' [G n T].

Lemma ctxProj_Eta' G n : forall T (a:AtCtx G n T),(fun g=>ctxProj a g) = ctxProj (atCtxEta' a).
Admitted.
Implicit Arguments ctxProj_Eta' [G n T].

Lemma spItrpUniq G F la : forall T1 T2 la1 la2,SimpParamItrp G F la T1 la1->SimpParamItrp G F la T2 la2->
(existT (fun T:G->Typ=>forall g,F g->T g) T1 la1 = existT _ T2 la2).
	induction la;simpl;intros.

	destruct H.
	destruct H0.
	reflexivity.

destruct X as (P1,a1,B1,la1).
destruct X0 as (P2,a2,B2,la2).
simpl in la1,la2.
pose proof (IHla _ _ _ _ s s0).
clear IHla s s0.
assert ((fun g=>typ (typSc (B1 (existT _ g (ctxProj a1 g))))) =
	(fun g=>typ (typSc (B2 (existT _ g (ctxProj a2 g)))))).
pose proof (ap (@projT1 _ _) H).
simpl in H0.
clear la1 la2 H.
change ((fun g=>typ (typSc (B1 (existT _ g (ctxProj a1 g))))) =
	(fun g=>typ (typSc (B2 (existT _ g ((fun g=>ctxProj a2 g) g)))))).
rewrite ctxProj_Eta'.
remember (atCtxEta' a2) as a2'.
clear a2 Heqa2'.
revert a2'.
pose (dom (T:Typ) := match T with
	typ _ (typPiS _ _ A _) => typ A |
	_ => T
end).
pose (cdm (T:Typ) :=
	match T as T return dom T->Typ with typ _ s =>
	match s as s return dom (typ s)->Typ with
		typPiS _ _ _ B => fun a=>typ (B a) |
		_ => fun _=>typUv
	end end).
apply (tr (fun pi=>forall a2':AtCtx G a (fun g=>dom (pi g)),_ =
	fun g=>cdm (pi g) (ctxProj a2' g)) H0).
simpl.
clear P2 B2 H0 dom cdm.
intro.
change ((fun g=>typ (typSc (B1 (existT _ g ((fun g=>ctxProj a1 g) g))))) =
	(fun g=>typ (typSc (B1 (existT _ g (ctxProj a2' g)))))).
rewrite ctxProj_Eta'.
(* Uh oh.
 * I can't fix both the argument and the codomain because they both depend on the domain,
 * but they have different paths for fixing the domain.
 *)
apply (tr (fun xa=>_ = fun g=>typ (typSc (B1 (existT

revert B2 la2 s0.
apply (tr (fun xa=>forall B2 la2,SimpParamItrp G F la
	(fun g=>typPi (xa_T xa g) (fun p=>B2 (existT (xa_T xa) g p))) la2->
(_ = existT (fun T:G->Typ=>forall g,F g->T g) _ (fun g f=>la2 g f (ctxProj (xa_a xa) g)))) (atCtxUniq a1 a2)).
simpl.
clear P2 a2.
intros.
Qed.
Implicit Arguments spItrpUniq [G F la T1 T2 la1 la2].
