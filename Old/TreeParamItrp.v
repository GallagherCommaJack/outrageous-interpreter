(*
Inductive TreeFamItrp (G:Ctx) : treeFam->(G->Typ)->Type :=
	tfItrpUv : TreeFamItrp G Uv (fun g=>typUv) |
	tfItrpEl p p' : TreeParamItrp G p (fun g=>typUv) p'->
		TreeFamItrp G (El p) (fun g=>typEl (p' g)) |
	tfItrpPi A B A' B' : TreeFamItrp G A A'->TreeFamItrp (extCtx G A') B B'->
		TreeFamItrp G (Pi A B) (fun g=>typPi (A' g) (fun a=>B' (existT A' g a)))
with TreeParamItrp (G:Ctx) : treeParam->forall T:G->Typ,(forall g,T g)->Type :=
	tpItrpVar i T (i':AtCtx G i T) : TreeParamItrp G (var i) T (ctxProj i') |
	tpItrpApl f a B P (a':AtCtx G a P) B' f' :
		TreeFamItrp (extCtx G P) B B'->
		TreeParamItrp G f (fun g=>typPi (P g) (fun p=>B' (existT P g p))) f'->
		TreeParamItrp G (apl f a B) (fun g=>B' (existT P g (ctxProj a' g))) (fun g=>f' g (ctxProj a' g)).
*)

Inductive TFItrpEl (G:Ctx) (R:forall G (T:_->Typ),(forall g,T g)->Type) : (G->Typ)->Type :=
	tfItrpEl p' : R G (fun g=>typUv) p'->
		TFItrpEl G R (fun g=>typEl (p' g)).
Implicit Arguments tfItrpEl [G R p'].

Inductive TFItrpPi (G:Ctx) (RA RB:forall G:Ctx,(G->Typ)->Type) : (G->Typ)->Type :=
	tfItrpPi A' B' : RA G A'->RB (extCtx G A') B'->
		TFItrpPi G RA RB (fun g=>typPi (A' g) (fun a=>B' (existT A' g a))).
Implicit Arguments tfItrpPi [G RA RB A' B'].

Inductive TPItrpVar (G:Ctx) i : forall T:G->Typ,(forall g,T g)->Type :=
	tpItrpVar T (i':AtCtx G i T) : TPItrpVar G i T (ctxProj i').
Implicit Arguments tpItrpVar [G i T].

Inductive TPItrpApl (G:Ctx) (Rf:forall G (T:_->Typ),(forall g,T g)->Type) a (RB:forall G:Ctx,(G->Typ)->Type) :
forall T:G->Typ,(forall g,T g)->Type :=
	tpItrpApl P (a':AtCtx G a P) B' f' :
		RB (extCtx G P) B'->
		Rf G (fun g=>typPi (P g) (fun p=>B' (existT P g p))) f'->
		TPItrpApl G Rf a RB (fun g=>B' (existT P g (ctxProj a' g))) (fun g=>f' g (ctxProj a' g)).
Implicit Arguments tpItrpApl [Rf a RB P B' f'].

Fixpoint TreeFamItrp (G:Ctx) F : (G->Typ)->Type := match F with
	Uv => eq (fun g=>typUv) |
	El p => TFItrpEl G (fun G=>TreeParamItrp G p) |
	Pi A B => TFItrpPi G (fun G=>TreeFamItrp G A) (fun G=>TreeFamItrp G B)
end
with TreeParamItrp G p : forall T,_->Type := match p with
	var i => TPItrpVar G i |
	apl f a B => TPItrpApl G (fun G=>TreeParamItrp G f) a (fun G=>TreeFamItrp G B)
end.

----------

Lemma tpItrpBump G n l p GL P (xg:ExtCtx GL l G) : forall T p',TreeParamItrp G (pBump n l p) T p'->
TreeParamItrp (ctxBump P xg) (pBump (S n) l p) (elBump P xg T) (elBump P xg p').
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

Lemma tpItrpBump_O G n p T p' P : TreeParamItrp G (pBump n O p) T p'->
TreeParamItrp (extCtx G P) (pBump (S n) O p) (fun g=>T (projT1 g)) (fun g=>p' (projT1 g)).
	apply tpItrpBump with (P := P) (xg := extOCtx G).
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

Lemma tpItrpSubst G p l b GL P (xg:ExtCtx (extCtx GL P) l G) (b':AtCtx GL b P) : forall T p',
	TreeParamItrp G p T p'->
TreeParamItrp (ctxSubst xg (ctxProj b')) (pSubst l b p)
(elSubst xg T (ctxProj b')) (elSubst xg p' (ctxProj b')).
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

Lemma tpItrpSubst_O G P p b T p' (b':AtCtx G b P) : TreeParamItrp (extCtx G P) p T p'->
TreeParamItrp G (pSubst O b p) _ (fun g=>p' (existT _ g (ctxProj b' g))).
	apply tpItrpSubst with (xg := extOCtx (extCtx G P)) (b' := b').
Qed.

Lemma tfItrpSubst F b GL P (b':AtCtx GL b P) : forall G l F' (xg:ExtCtx (extCtx GL P) l G),TreeFamItrp G F F'->
TreeFamItrp (ctxSubst xg (ctxProj b')) (fSubst l b F) (elSubst xg F' (ctxProj b')).
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
TreeFamItrp G (fSubst O b F) (fun g=>F' (existT _ g (ctxProj b' g))).
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

Inductive ExTreeParamItrp G p T : Type :=
	exTreeParamItrp T' p' : TreeParamItrp G p T' p'->TreeFamItrp G T T'->ExTreeParamItrp G p T.
Implicit Arguments exTreeParamItrp [G p T].

Lemma tfItrpTotalNest G F C : TreeFamGood
	(fun G p T=>forall G',TreeCtxItrp G G'->ExTreeParamItrp G' p T) G F->
forall G',TreeCtxItrp G G'->
	(forall F',TreeFamItrp G' F F'->C)->
C.
	intro.
	induction X;intros ? XG rtn.

	apply (rtn (fun g=>typUv)).
	reflexivity.

	destruct (p0 _ XG) as (?,?,Xp,XU).
	simpl in XU.
	revert p' Xp.
	rewrite <- XU.
	clear T' XU.
	intros.
	apply (rtn (fun g=>typEl (p' g))).
	simpl.
	exact (tfItrpEl Xp).

	clear X1 X2.
	apply (IHX1 _ XG).
	intros A' XA.
	apply (IHX2 (extCtx G' A')).
		simpl.
		exact (tcItrpCons XG XA).
	intros B' XB.
	apply (rtn (fun g=>typPi (A' g) (fun a=>B' (existT _ g a)))).
	simpl.
	exact (tfItrpPi XA XB).
Qed.

Lemma tpItrpTotal G p T : TreeParamGood G p T->forall G',TreeCtxItrp G G'->ExTreeParamItrp G' p T.
	intro.
	induction H;intros ? XG.

	apply tcItrpProj with (i := i) (2 := XG).
		unfold ltd.
		rewrite (proj1 (nat_compare_lt _ _) H).
		exact I.
	intros T i' XT.
	apply (exTreeParamItrp T (ctxProj i')).
		apply tpItrpVar.

		exact XT.

	apply tcItrpProj with (i := a) (2 := XG).
		unfold ltd.
		rewrite (proj1 (nat_compare_lt _ _) H).
		exact I.
	intros P a' XP.
	destruct (IHTreeParamGood _ XG) as (T,f',Xf,XT).
	simpl in XT.
	revert f' Xf.
	destruct XT as (P0,B'0,XP0,XB0).
	simpl.
	intros.
	apply tfItrpTotalNest with (1 := X) (G' := extCtx G' P).
		simpl.
		exact (tcItrpCons XG XP).
	clear X.
	intros B' XB.
	(* Aaaaaand we're screwed *)
	apply (exSimpParamItrp (fun g=>B' (existT _ g (ctxProj a' g))) (fun g f=>la'
		apply spItrpCons with (a' := a') (1 := Xp).

		apply sfItrpSubst_O with (1 := Xf).
Qed.
