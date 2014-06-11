Require Import List.

Require Import Utils.
Require Import Context.
Require Import SimpSyntax.
Require Import TreeSyntax.

Require Import Plus Minus.
Require Import Compare_dec.

(* Structured semantic types = type codes = universe construction *)

Module TypCode <: CTXTYP.

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

Lemma spItrpUniq G F la : forall T1 T2 la1 la2,SimpParamItrp G F la T1 la1->SimpParamItrp G F la T2 la2->
(existT (fun T:G->Typ=>forall g,F g->T g) T1 la1 = existT _ T2 la2).
	induction la;simpl;intros.

	destruct H.
	destruct H0.
	reflexivity.

destruct X as (P1,a1,B1,f1).
destruct X0 as (P2,a2,B2,f2).
simpl in f1,f2.
revert B2 f2 t1 t2.
apply (tr (fun xa=>forall B2 f2,
	TreeFamItrp (extCtx G (xa_T xa)) B B2->
	TreeParamItrp G f (fun g=>typPi (xa_T xa g) (fun p=>B2 (existT _ g p))) f2->
	(_ = existT (fun T:G->Typ,forall g,T g)
		(fun g=>B2 (existT _ g (ctxProj (xa_a xa) g))) (fun g=>f2 g (ctxProj (xa_a xa) g))))
(atCtxUniq a1 a2)).
simpl in B1 |- *.
clear P2 a2.
intros.
revert f2 X0.
rewrite <- (tfItrpUniq t X).
clear t B2 X.
intros.
pose proof (IHf _ _ _ _ _ t0 X0).
(* Crap *)
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

	destruct X as (A1,B1).
	destruct X0 as (A2,B2).
	revert B2 t2.
	rewrite <- (IHF1 _ _ _ t t1).
	clear A2 t1.
	intros.
	rewrite <- (IHF2 _ _ _ t0 t2).
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
	(*induction la;simpl.

	intros.
	apply spItrpNilInv with (1 := X).
	apply spItrpNil.

	intros ? ?.
	destruct (lt_dec a l) as [Ho | Ho].
		rewrite (proj1 (nat_compare_lt _ _) Ho).
		intro.
		apply spItrpConsInv with (1 := X).
		clear T la' X.
		intros.
		pose proof (spItrpCons _ _ _ _ _ _ (atBumpGLo P xg a' Ho)
			(fun d g=>B d (existT _ (xc_f' (xgBumpG P xg) d (projT1 g)) (projT2 g)))
			_ (IHla _ _ X)).
		simpl in X0.
		rewrite ctxProj_BumpGLo in X0.
		exact X0.

		assert (nolt : forall k,k = match nat_compare a l with
			Lt => a |
			_ => k
		end).
			intro.
			destruct (nat_compare_spec a l);try reflexivity.
			destruct (Ho H).
		rewrite <- nolt.
		rewrite <- nolt.
		clear nolt.
		intro.
		apply spItrpConsInv with (1 := X).
		clear T la' X.
		intros.
		assert (l <= n + a).
			rewrite <- plus_comm.
			apply le_plus_trans.
			exact (not_lt _ _ Ho).
		pose proof (spItrpCons _ _ _ _ _ _ (atBumpGHi P xg a' H)
			(fun d g=>B d (existT _ (xc_f' (xgBumpG P xg) d (projT1 g)) (projT2 g)))
			_ (IHla _ _ X)).
		simpl in X0.
		rewrite ctxProj_BumpGHi in X0.
		exact X0.
Qed.*)
Admitted.

Lemma spItrpBump_O G F n la T la' P : SimpParamItrp G F (laBump n O la) T la'->
SimpParamItrp (extCtx G P) (fun g=>F (projT1 g)) (laBump (S n) O la) (fun g=>T (projT1 g)) (fun g=>la' (projT1 g)).
	apply spItrpBump with (P := P) (xg := extOCtx G).
Qed.

Lemma tfItrpBump n F GL P : forall G l F' (xg:ExtCtx GL l G),TreeFamItrp G (fBump n l F) F'->
TreeFamItrp (ctxBump P xg) (fBump (S n) l F) (elBump P xg F').
	(*induction F as [| p];[| destruct p as (f,la)];simpl;intros.

	rewrite sfItrpNilInv with (1 := X).
	apply sfItrpNil.

	apply sfItrpConsInv with (1 := X).
	clear F' X.
	intros B ? ? F'.
	pose (A d g := la' d g (tctxProj f' d)).
	change (forall d,extCtx G A d->Type) in F'.
	pose (F_ d g := forall p,F' d (existT _ g p)).
	change (SimpParamItrp G B (laBumpG n l la) (fun d g=>Type) la'->
		SimpFamItrp D (extCtx G A) (fBumpG n (S l) F) F'->
		SimpFamItrp D (ctxBumpG P xg) ((f,laBumpG (S n) l la) :: fBumpG (S n) (S l) F) (elBumpG P xg F_)).
	intros Xp Xf.
	apply sfItrpCons with (la' := elBumpG P xg la') (2 := IHF _ _ _ (extSCtx xg _) Xf).
	apply spItrpBumpG with (1 := Xp) (xg := xg).
Qed.*)
Admitted.

Lemma tfItrpBump_O G n F F' P : TreeFamItrp G (fBump n O F) F'->
TreeFamItrp (extCtx G P) (fBump (S n) O F) (fun g=>F' (projT1 g)).
	apply tfItrpBump with (P := P) (xg := extOCtx G).
Qed.

Lemma spItrpSubst G F la l b GL P (xg:ExtCtx (extCtx GL P) l G) (b':AtCtx GL b P) : forall T la',
	SimpParamItrp G F la T la'->
SimpParamItrp (ctxSubst xg (ctxProj b')) (elSubst xg F (ctxProj b')) (laSubst la l b)
(elSubst xg T (ctxProj b')) (elSubst xg la' (ctxProj b')).
	(*induction la;intros ? ?;simpl.

	intro.
	apply spItrpNilInv with (1 := X).
	apply spItrpNil.

	destruct (lt_eq_lt_dec a l) as [s | Ho];[destruct s as [Ho | Ho] |].
		intro.
		rewrite (proj1 (nat_compare_lt _ _) Ho).
		apply spItrpConsInv with (1 := X).
		clear T la' X.
		intros.
		pose proof (spItrpCons _ _ _ _ _ _ (atSubstLt xg a' Ho (ctxProj b'))
			(fun d g=>B d (existT _ (xc_f' (xgSubst xg (ctxProj b')) d (projT1 g)) (projT2 g)))
			_ (IHla _ _ X)).
		simpl in X0.
		rewrite ctxProj_SubstLt in X0.
		exact X0.

		intro.
		rewrite (proj2 (nat_compare_eq_iff _ _) Ho).
		revert xg IHla.
		apply (tr (fun _=>_) Ho).
		clear l Ho.
		intros.
		apply spItrpConsInv with (1 := X).
		clear T la' X.
		intros.
		pose (b0 := tr (AtCtx G _) (atCtxExtTEq b' xg a') (ax_a (atCtxExt xg (popCtx b' P)))).
		assert (Ha : a + S b = S (a + b)).
			rewrite <- plus_n_Sm.
			reflexivity.
		pose (b1 := tr (fun n=>AtCtx G n P0) Ha b0).
		simpl in b1.
		assert (Hb : a <= a + b).
			apply le_plus_l.
		pose proof (spItrpCons _ _ _ _ _ _ (atSubstGt xg b1 Hb (ctxProj b'))
			(fun d g=>B d (existT _ (xc_f' (xgSubst xg (ctxProj b')) d (projT1 g)) (projT2 g)))
			_ (IHla _ _ X)).
		simpl in X0.
		rewrite ctxProj_SubstGt in X0.
		subst b1.
		rewrite <- Ha in X0.
		simpl in X0.
		clear Ha Hb.
		subst b0.
		rewrite ctxProj_Ext in X0.
		rewrite ctxProj_SubstEq in X0.
		exact X0.

		rewrite (proj1 (nat_compare_gt _ _) Ho).
		destruct a.
			exact (match lt_n_O _ Ho with end).
		unfold lt in Ho.
		intro.
		simpl.
		apply spItrpConsInv with (1 := X).
		clear T la' X.
		intros.
		pose proof (le_S_n _ _ Ho).
		pose proof (spItrpCons _ _ _ _ _ _ (atSubstGt xg a' H (ctxProj b'))
			(fun d g=>B d (existT _ (xc_f' (xgSubst xg (ctxProj b')) d (projT1 g)) (projT2 g)))
			_ (IHla _ _ X)).
		simpl in X0.
		rewrite ctxProj_SubstGt in X0.
		exact X0.
Qed.*)
Admitted.

Lemma spItrpSubst_O G P F la b T la' (b':AtCtx G b P) : SimpParamItrp (extCtx G P) F la T la'->
SimpParamItrp G (fun g=>F (existT _ g (ctxProj b' g))) (laSubst la O b) _ (fun g=>la' (existT _ g (ctxProj b' g))).
	apply spItrpSubst with (xg := extOCtx (extCtx G P)) (b' := b').
Qed.

Lemma tfItrpSubst F b GL P (b':AtCtx GL b P) : forall G l F' (xg:ExtCtx (extCtx GL P) l G),TreeFamItrp G F F'->
TreeFamItrp (ctxSubst xg (ctxProj b')) (fSubst F l b) (elSubst xg F' (ctxProj b')).
	(*induction F as [| p];[| destruct p as (f,la)];simpl;intros.

	rewrite sfItrpNilInv with (1 := X).
	apply sfItrpNil.

	apply sfItrpConsInv with (1 := X).
	clear F' X.
	intros B ? ? F'.
	pose (A d g := la' d g (tctxProj f' d)).
	change (forall d,extCtx G A d->Type) in F'.
	pose (F_ d g := forall p,F' d (existT _ g p)).
	change (SimpParamItrp G B la (fun d g=>Type) la'->
		SimpFamItrp D (extCtx G A) F F'->
		SimpFamItrp D (ctxSubst xg (ctxProj b')) ((f,laSubstG la l b) :: fSubstG F (S l) b)
			(elSubst xg F_ (ctxProj b'))).
	intros Xp Xf.
	apply sfItrpCons with (la' := elSubst xg la' (ctxProj b')) (2 := IHF _ _ _ (extSCtx xg _) Xf).
	apply spItrpSubst with (1 := Xp) (xg := xg).
Qed.*)
Admitted.

Lemma tfItrpSubst_O G P F b F' (b':AtCtx G b P) : TreeFamItrp (extCtx G P) F F'->
TreeFamItrp G (fSubst F O b) (fun g=>F' (existT _ g (ctxProj b' g))).
	apply tfItrpSubst with (xg := extOCtx (extCtx G P)) (b' := b').
Qed.

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

Inductive ExSimpParamItrp G F la T : Type :=
	exSimpParamItrp T' la' : SimpParamItrp G F la T' la'->TreeFamItrp G T T'->ExSimpParamItrp G F la T.
Implicit Arguments exSimpParamItrp [G F la T].

Lemma tfItrpTotalNest G F C : TreeFamGood
	(fun G F la T=>forall G' F',TreeCtxItrp G G'->TreeFamItrp G' F F'->ExSimpParamItrp G' F' la T) G F->
forall G',TreeCtxItrp G G'->
	(forall F',TreeFamItrp G' F F'->C)->
C.
	intro.
	induction X;intros ? XG rtn.

	apply (rtn (fun g=>Type)).
	reflexivity.

	apply tcItrpProj with (i := f) (2 := XG).
		unfold ltd.
		rewrite (proj1 (nat_compare_lt _ _) l).
		exact I.
	intros ? f' XF.
	destruct (p _ _ XG XF) as (?,?,Xla,XU).
	simpl in XU.
	revert la' Xla.
	rewrite <- XU.
	clear T' XU.
	intros.
	apply (rtn (fun g=>la' g (ctxProj f' g))).
	exact (tfItrpEl f' Xla).

	clear X1 X2.
	apply (IHX1 _ XG).
	intros A' XA.
	apply (IHX2 (extCtx G' A')).
		simpl.
		exact (tcItrpCons XG XA).
	intros B' XB.
	apply (rtn (fun g=>forall a,B' (existT _ g a))).
	simpl.
	exact (tfItrpPi XA XB).
Qed.

Lemma spItrpTotal G F la T : SimpParamGood G F la T->forall G' F',TreeCtxItrp G G'->TreeFamItrp G' F F'->
ExSimpParamItrp G' F' la T.
	intro.
	induction H;intros ? ? XG XF.

	apply (exSimpParamItrp F' (fun g f=>f)).
		apply spItrpNil.

		exact XF.

	apply tcItrpProj with (i := a) (2 := XG).
		unfold ltd.
		rewrite (proj1 (nat_compare_lt _ _) H).
		exact I.
	intros A a' XA.
	destruct (IHSimpParamGood _ _ XG XF) as (?,?,Xla,XT).
	simpl in XT.
	revert la' Xla.
	destruct XT as (A0,B'0,XA0,XB0).
	intros.
	apply tfItrpTotalNest with (1 := X) (G' := extCtx G' A).
		simpl.
		exact (tcItrpCons XG XA).
	clear X.
	intros B' XB.
	(* Aaaaaand we're screwed *)
	apply (exSimpParamItrp (fun g=>B' (existT _ g (ctxProj a' g))) (fun g f=>la'
		apply spItrpCons with (a' := a') (1 := Xp).

		apply sfItrpSubst_O with (1 := Xf).
Qed.

Lemma tfItrpTotal G F C : TreeFamGoodPG G F->forall G',TreeCtxItrp G G'->
	(forall F',TreeFamItrp G' F F'->C)->
C.
Qed.
