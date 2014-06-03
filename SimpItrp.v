Require Import List.

Require Import Utils.
Require Import Context.
Require Import SimpSyntax.

Require Import Plus Minus.
Require Import Compare_dec.

(* Semantic types *)

Inductive TypS G : (G->Type)->Type :=
	uvS : TypS G (fun g=>Type) |
	piS A B : TypS (sigT A) B->TypS G (fun g=>forall a:A g,B (existT _ g a)).
Implicit Arguments TypS [G].
Implicit Arguments piS [G B].

Inductive Typ G : Type := typ (T:G->Type) (s:TypS T).
Implicit Arguments typ [G T].

Definition typTp G (T:Typ G) := match T with typ T _ => T end.
Implicit Arguments typTp [G].
Coercion typTp : Typ >-> Funclass.

Definition typSc G (T:Typ G) : TypS T := match T with typ _ s => s end.
Implicit Arguments typSc [G].

Definition uv G := typ (uvS G).

Definition pi G (A:G->Type) B := typ (piS A (typSc B)).
Implicit Arguments pi [G].

Fixpoint typMapS G G' (f:G'->G) (T:G->Type) (s:TypS T) := match s with
	uvS => uv G' |
	piS A _ s => pi _ (typMapS _ _ (fun (g:sigT (fun g=>A (f g)))=>existT _ (f (projT1 g)) (projT2 g)) _ s)
end.
Implicit Arguments typMapS [G G' T].

Definition typMap G G' (f:G'->G) T := typMapS f (typSc T).
Implicit Arguments typMap [G G'].

Definition typMapEq G G' (f:G'->G) (T:Typ G) : (fun g=>T (f g)) = typMap f T.
	destruct T.
	unfold typMap.
	simpl.
	revert G' f.
	induction s;intros;simpl.

	reflexivity.

	apply (tr (fun X=>_ = fun g=>forall a,X (existT _ g a))
		(IHs _ (fun g:sigT (fun g=>A (f g))=>existT _ (f (projT1 g)) (projT2 g)))).
	simpl.
	reflexivity.
Defined.
Implicit Arguments typMapEq [G G'].

(* Dependent semantic contexts *)

Inductive DCtx D : Type := dctx n G (xg:ExtCtx D n G).
Implicit Arguments dctx [D n G].

Definition dctx_n D (G:DCtx D) := match G with dctx n _ _ => n end.
Implicit Arguments dctx_n [D].

Definition dctx_G D (G:DCtx D) := match G with dctx _ G _ => G end.
Implicit Arguments dctx_G [D].
Coercion dctx_G : DCtx >-> Ctx.

Definition dctx_xg D (G:DCtx D) : ExtCtx D (dctx_n G) (dctx_G G) := match G with dctx _ _ xg => xg end.
Implicit Arguments dctx_xg [D].

Definition dctx_d D (G:DCtx D) := unExt (dctx_xg G).
Implicit Arguments dctx_d [D G].

Definition empDCtx D := dctx (extOCtx D).

Definition extDCtx D (G:DCtx D) T := dctx (extSCtx (dctx_xg G) T).
Implicit Arguments extDCtx [D].

Definition dctxBump D P (G:DCtx D) := dctx (xgBump P (dctx_xg G)).
Implicit Arguments dctxBump [D].

Definition dctxSubst D P (G:DCtx (extCtx D P)) p := dctx (xgSubst (dctx_xg G) p).
Implicit Arguments dctxSubst [D P].

(* Interpretation relations *)

Inductive SimpParamItrp D (G:DCtx D) F : list nat->forall T:G->Type,(forall g,F (dctx_d g)->T g)->Type :=
	spItrpNil : SimpParamItrp D G F nil (fun g=>F (dctx_d g)) (fun g f=>f) |
	spItrpCons a la P (a':AtCtx G a P) B la' :
		SimpParamItrp D G F la (fun g=>forall p,B (existT _ g p)) la'->
		SimpParamItrp D G F (a :: la) (fun g=>B (existT _ g (ctxProj a' g))) (fun g f=>la' g f (ctxProj a' g)).
Implicit Arguments SimpParamItrp [D].

Inductive SimpFamItrp D (G:DCtx D) : simpFam->(G->Type)->Type :=
	sfItrpNil : SimpFamItrp D G nil (fun g=>Type) |
	sfItrpCons f la T F (f':AtCtx D f F) la' T' :
		SimpParamItrp G F la (fun g=>Type) la'->
		SimpFamItrp D (extDCtx G (fun g=>la' g (ctxProj f' (dctx_d g)))) T T'->
		SimpFamItrp D G ((f,la) :: T) (fun g=>forall p,T' (existT _ g p)).

Inductive SimpFCtxItrp : list simpFam->Ctx->Type :=
	sfcItrpNil : SimpFCtxItrp nil empCtx |
	sfcItrpCons F D D' F' :
		SimpFCtxItrp D D'->
		SimpFamItrp D' (empDCtx D') F F'->
		SimpFCtxItrp (F :: D) (extCtx D' F').

Inductive SimpPCtxItrp D : list (nat * list nat)->DCtx D->Type :=
	spcItrpNil : SimpPCtxItrp D nil (empDCtx D) |
	spcItrpCons f la G G' F (f':AtCtx D f F) la' :
		SimpPCtxItrp D G G'->
		SimpParamItrp G' F la (fun g=>Type) la'->
		SimpPCtxItrp D ((f,la) :: G) (extDCtx G' (fun g=>la' g (ctxProj f' (dctx_d g)))).

Definition spItrpNilInv D (G:DCtx D) F T la' (C:forall T:G->Type,(forall g,F (dctx_d g)->T g)->Type)
	(X:SimpParamItrp G F nil T la')
: C (fun g=>F (dctx_d g)) (fun g f=>f)->C T la' :=
match X in SimpParamItrp _ _ nl T la' return (nil = nl)->_->C T la' with
	spItrpNil => fun _ p=>p |
	spItrpCons _ _ _ _ _ _ _ => fun e=>match nil_cons e with end
end (eq_refl _).

Definition spItrpConsInv D (G:DCtx D) F a la T la' (C:forall T:G->Type,(forall g,F (dctx_d g)->T g)->Type)
(X:SimpParamItrp G F (a :: la) T la') :
	(forall P (a':AtCtx G a P) B la',SimpParamItrp G F la (fun g=>forall p,B (existT _ g p)) la'->
	C (fun g=>B (existT _ g (ctxProj a' g))) (fun g f=>la' g f (ctxProj a' g)))->
C T la'.
	simpl.
	refine (match X in SimpParamItrp _ _ ala T la' return (ala = a :: la)->_->C T la' with
		spItrpNil => fun e=>match nil_cons e with end |
		spItrpCons _ _ _ _ _ _ _ => fun e rtn=>_
	end (eq_refl _)).
	revert a' s.
	apply (tr (fun ala=>forall a':AtCtx G (hd O ala) P,SimpParamItrp G F (tl ala) _ la'0->
		C _ (fun g f=>la'0 g f (ctxProj a' g))) (eq_sym e)).
	simpl.
	intro.
	apply rtn.
Defined.

Definition sfItrpNilInv D G T (X:SimpFamItrp D G nil T) := match X in SimpFamItrp _ _ nl T
return (nil = nl)->(T = fun g=>Type) with
	sfItrpNil => fun _=>eq_refl _ |
	sfItrpCons _ _ _ _ _ _ _ _ _ => fun e=>match nil_cons e with end
end (eq_refl _).

Definition sfItrpConsInv D G f la T T' P (X:SimpFamItrp D G ((f,la) :: T) T') :
	(forall F (f':AtCtx D f F) la' T',
		SimpParamItrp G F la (fun g=>Type) la'->
		SimpFamItrp D (extDCtx G (fun g=>la' g (ctxProj f' (dctx_d g)))) T T'->
	P (fun g=>forall p,T' (existT _ g p)))->
P T'.
	simpl.
	refine (match X in SimpFamItrp _ _ flaT T' return (flaT = (f,la) :: T)->_->P T' with
		sfItrpNil => fun e=>match nil_cons e with end |
		sfItrpCons _ _ _ _ _ _ _ _ _ => fun e rtn=>_
	end (eq_refl _)).
	simpl in T'0.
	revert f' T'0 s s0.
	apply (tr (fun flaT=>forall (f':AtCtx D (fst (hd (O,nil) flaT)) F) T'0,
		SimpParamItrp G F (snd (hd (O,nil) flaT)) (fun g=>Type) la'->
		SimpFamItrp D (extDCtx G (fun g=>la' g (ctxProj f' (dctx_d g)))) (tl flaT) T'0->
	P (fun g=>forall p,T'0 (existT _ g p))) (eq_sym e)).
	simpl.
	intro.
	apply rtn.
Defined.

Definition sfcItrpConsInv F D D' P (X:SimpFCtxItrp (F :: D) D') :
	(forall D' F',SimpFCtxItrp D D'->SimpFamItrp D' (empDCtx D') F F'->
	P (sigT F'))->
P D'.
	refine (match X in SimpFCtxItrp FD D' return (FD = F :: D)->_->P D' with
		sfcItrpNil => fun e=>match nil_cons e with end |
		sfcItrpCons _ _ _ _ _ _ => fun e rtn=>_
	end (eq_refl _)).
	revert s s0.
	apply (tr (fun FD=>
		SimpFCtxItrp (tl FD) D'0->
		SimpFamItrp D'0 (empDCtx D'0) (hd nil FD) F'->
	P (sigT F')) (eq_sym e)).
	simpl.
	apply rtn.
Defined.

Definition spcItrpConsInv D f la G G' P (X:SimpPCtxItrp D ((f,la) :: G) G') :
	(forall G' F (f':AtCtx D f F) la',SimpPCtxItrp D G G'->SimpParamItrp G' F la (fun g=>Type) la'->
	P (extDCtx G' (fun g=>la' g (ctxProj f' (dctx_d g)))))->
P G'.
	simpl.
	refine (match X in SimpPCtxItrp _ flaG G' return (flaG = (f,la) :: G)->_->P G' with
		spcItrpNil => fun e=>match nil_cons e with end |
		spcItrpCons _ _ _ _ _ _ _ _ _ => fun e rtn=>_
	end (eq_refl _)).
	revert f' s s0.
	apply (tr (fun flaG=>forall f':AtCtx D (fst (hd (O,nil) flaG)) F,
		SimpPCtxItrp D (tl flaG) G'0->
		SimpParamItrp G'0 F (snd (hd (O,nil) flaG)) (fun g=>Type) la'->
	P (extDCtx G'0 (fun g=>la' g (ctxProj f' (dctx_d g))))) (eq_sym e)).
	simpl.
	intro.
	apply rtn.
Defined.

Lemma spItrpBumpD D (G:DCtx D) F la T la' B : SimpParamItrp G F la T la'->
SimpParamItrp (dctxBumpD B G) (fun d=>F (projT1 d)) la (fun d=>T (projT1 d)) (fun d=>la' (projT1 d)).
	intro.
	induction X.

	apply spItrpNil.

	pose proof (spItrpCons _ _ _ _ _ _ (atBumpD _ a') (fun d=>B0 (projT1 d)) _ IHX).
	simpl in X0.
	rewrite ctxProj_BumpD in X0.
	exact X0.
Qed.

Lemma sfItrpBumpD D n F T : forall G F',SimpFamItrp D G (fBumpD n F) F'->
SimpFamItrp (sigT T) (ctxBumpD T G) (fBumpD (S n) F) (fun d=>F' (projT1 d)).
	induction F;simpl;intros.

	rewrite sfItrpNilInv with (1 := X).
	apply sfItrpNil.

	destruct a as (f,la).
	apply sfItrpConsInv with (1 := X).
	clear F' X.
	intros B ? ? F' Xp Xf.
	apply sfItrpCons with (G := ctxBumpD T G) (f' := popTCtx T f') (la' := fun d=>la' (projT1 d))
		(2 := IHF _ _ Xf).
	apply spItrpBumpD with (1 := Xp).
Qed.

Lemma spItrpBumpG D (G:Ctx D) F n l la GL P (xg:ExtCtx GL l G) : forall T la',SimpParamItrp G F (laBumpG n l la) T la'->
SimpParamItrp (ctxBumpG P xg) F (laBumpG (S n) l la) (elBumpG P xg T) (elBumpG P xg la').
	induction la;simpl.

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
Qed.

Lemma spItrpBumpG_O D (G:Ctx D) F n la T la' P : SimpParamItrp G F (laBumpG n O la) T la'->
SimpParamItrp (extCtx G P) F (laBumpG (S n) O la) (fun d g=>T d (projT1 g)) (fun d g=>la' d (projT1 g)).
	apply spItrpBumpG with (P := P) (xg := extOCtx G).
Qed.

Lemma sfItrpBumpG D n F GL P : forall G l F' (xg:ExtCtx GL l G),SimpFamItrp D G (fBumpG n l F) F'->
SimpFamItrp D (ctxBumpG P xg) (fBumpG (S n) l F) (elBumpG P xg F').
	induction F as [| p];[| destruct p as (f,la)];simpl;intros.

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
Qed.

Lemma sfItrpBumpG_O D G n F F' P : SimpFamItrp D G (fBumpG n O F) F'->
SimpFamItrp D (extCtx G P) (fBumpG (S n) O F) (fun d g=>F' d (projT1 g)).
	apply sfItrpBumpG with (P := P) (xg := extOCtx G).
Qed.

Lemma sfItrpBuildG D G T T' : SimpFamItrp D (empCtx D) T (fun d g=>T' d)->(fBumpG 1 O T = T)->
SimpFamItrp D G T (fun d g=>T' d).
	intros.
	destruct G.
	induction s.

	exact X.

	simpl.
	rewrite <- H.
	rewrite <- fBumpG_O with (l := O) (F := T) in IHs.
	apply sfItrpBumpG_O with (1 := IHs).
Qed.

Lemma spItrpSubst D (G:Ctx D) F la l b GL P (xg:ExtCtx (extCtx GL P) l G) (b':AtCtx GL b P) : forall T la',
	SimpParamItrp G F la T la'->
SimpParamItrp (ctxSubst xg (ctxProj b')) F (laSubstG la l b)
(elSubst xg T (ctxProj b')) (elSubst xg la' (ctxProj b')).
	induction la;intros ? ?;simpl.

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
Qed.

Lemma spItrpSubst_O D (G:Ctx D) P F la b T la' (b':AtCtx G b P) : SimpParamItrp (extCtx G P) F la T la'->
SimpParamItrp G F (laSubstG la O b) _ (fun d g=>la' d (existT _ g (ctxProj b' d g))).
	apply spItrpSubst with (xg := extOCtx (extCtx G P)) (b' := b').
Qed.

Lemma sfItrpSubst D F b GL P (b':AtCtx GL b P) : forall G l F' (xg:ExtCtx (extCtx GL P) l G),SimpFamItrp D G F F'->
SimpFamItrp D (ctxSubst xg (ctxProj b')) (fSubstG F l b) (elSubst xg F' (ctxProj b')).
	induction F as [| p];[| destruct p as (f,la)];simpl;intros.

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
Qed.

Lemma sfItrpSubst_O D G P F b F' (b':AtCtx G b P) : SimpFamItrp D (extCtx G P) F F'->
SimpFamItrp D G (fSubstG F O b) (fun d g=>F' d (existT _ g (ctxProj b' d g))).
	apply sfItrpSubst with (xg := extOCtx (extCtx G P)) (b' := b').
Qed.

Lemma stcItrpAt f C : forall D D',(f < length D)->SimpTCtxItrp D D'->
	(forall F,AtTCtx D' f F->
		SimpFamItrp D' (empCtx D') (fBumpD (S f) (nth f D nil)) (fun d g=>F d)->
	C)->
C.
	induction f;intros ? ?;
	(destruct D as [| F];intro H;[destruct lt_n_O with (1 := H) |]);intro X;
	apply stcItrpConsInv with (1 := X);clear D' X;simpl;intros.

	apply X1 with (1 := topTCtx _).
	apply sfItrpBumpD with (G := empCtx D') (F' := fun d g=>F' d).
	rewrite fBumpD_O.
	exact X0.

	apply IHf with (2 := X).
		apply lt_S_n with (1 := H).
	intros.
	apply X1 with (1 := popTCtx _ X2).
	apply sfItrpBumpD with (1 := X3).
Qed.

Lemma scItrpAt a D C : forall G G',(a < length G)->SimpCtxItrp D G G'->
	(forall f la F (f':AtTCtx D f F) la',((f,la) = pBumpG (S a) O (nth a G (O,nil)))->
		SimpParamItrp G' F la (fun d g=>Type) la'->
		AtCtx G' a (fun d g=>la' d g (tctxProj f' d))->
	C)->
C.
	induction a;intros ? ?;
	(destruct G;intro H;[destruct lt_n_O with (1 := H) |]);
	simpl in H;destruct p as (f,la);intro X;
	apply scItrpConsInv with (1 := X);clear G' X;simpl;intros.

	rewrite <- laBumpG_O with (l := O) (la := la) in X0.
	pose proof (spItrpBumpG_O _ _ _ _ _ _ _ (fun d g=>la' d g (tctxProj f' d)) X0).
	simpl in X2.
	apply X1 with (1 := eq_refl _) (2 := X2) (3 := topCtx _ _).

	apply IHa with (2 := X).
		apply lt_S_n with (1 := H).
	intros.
	destruct (nth a G (O,nil)) as (f_,la_).
	simpl in X1,H0.
	pose proof (tr (fun p=>f0 = fst p) H0 (eq_refl _)).
	pose proof (tr (fun p=>la0 = snd p) H0 (eq_refl _)).
	clear H0.
	simpl in H1,H2.
	subst f0 la0.
	pose proof (spItrpBumpG_O _ _ _ _ _ _ _ (fun d g=>la' d g (tctxProj f' d)) X2).
	simpl in X4.
	apply X1 with (1 := eq_refl _) (2 := X4) (3 := popCtx X3 _).
Qed.

Remark atCtxUniq D (G:Ctx D) n T1 T2 (a1:AtCtx G n T1) (a2:AtCtx G n T2) : existT (AtCtx G n) _ a1 = existT _ _ a2.
	revert T2 a2.
	induction a1 as [| ? ? T1];intros.

	assert (z : IsO O).
		exact I.
	revert z.
	apply (topCtxInv_ext a2 (fun _ _ n _ a2=>forall z:IsO n,
		existT _ _ (topCtx _ _) = existT (AtCtx _ _) _ (tr (fun n=>AtCtx _ n _) (OUnfold z) a2))).
	intro.
	reflexivity.

	assert (nz : IsS (S n)).
		exact I.
	revert nz T1 a1 IHa1.
	apply (popCtxInv_ext a2 (fun G _ n _ a2=>forall (nz:IsS n) T1 a1
		(IHa1:forall T2 (a2:AtCtx G _ T2),existT _ _ a1 = existT _ _ a2),
		existT _ _ (popCtx a1 _) = existT (AtCtx _ _) _ (tr (fun n=>AtCtx _ n _) (SUnfold nz) a2))).
	clear T2 a2.
	simpl.
	intros T2 a2 _ ? ? ?.
	apply (tr (fun s=>_ = existT _ _ (popCtx (projT2 s) T')) (IHa1 _ a2)).
	reflexivity.
Qed.

(* I _could've_ developed TCtx the same way as Ctx, so as to prove this, but I didn't forsee the need. *)
Axiom atTCtxUniq : forall D n T1 T2 (a1:AtTCtx D n T1) (a2:AtTCtx D n T2),
	existT (AtTCtx D n) _ a1 = existT _ _ a2.

Lemma spItrpUniq D (G:Ctx D) F la T1 T2 la'1 la'2 : SimpParamItrp G F la T1 la'1->SimpParamItrp G F la T2 la'2->
(existT (fun T=>forall d g,F d->T d g) T1 la'1 = existT _ T2 la'2).
	intro Xp1.
	revert T2 la'2.
	induction Xp1 as [| ? ? P1 a'1 B1 la'1].

--

	intros ? ? Xp2.
	remember (a :: la) as ala in Xp2.
	destruct Xp2 as [| ? ? P2 a'2 B2 la'2];[destruct (nil_cons Heqala) |].
	revert a'2 Xp2.
	set (a_ := a0).
	set (la_ := la0).
	change a_ with (hd a (a0 :: la0)).
	change la_ with (tl (a0 :: la0)).
	clear a_ la_.
	rewrite Heqala.
	simpl.
	clear a0 la0 Heqala.
	intro.
	revert B2 la'2.
	apply (tr (fun s=>forall B2 la'2 (Xp2:SimpParamItrp G F la (fun d g=>forall p,B2 d (existT _ g p)) la'2),
		_ = existT (fun T=>forall d g,F d->T d g) _ (fun d g f=>la'2 d g f (ctxProj (projT2 s) d g)))
	(atCtxUniq _ _ _ _ _ a'1 a'2)).
	clear P2 a'2.
	simpl.
	intros.
	pose proof (IHXp1 _ _ Xp2).
	pose proof (ap (@projT1 _ _) H).
	simpl in H0.
	(* Rats. Need injectivity of types again. *)
Admitted.

(* The coherence needed to prove this is not currently available. Adding type codes might fix this. *)
Lemma spItrpUniq' D (G:Ctx D) F la la'1 la'2 :
	SimpParamItrp G F la (fun d g=>Type) la'1->SimpParamItrp G F la (fun d g=>Type) la'2->
(la'1 = la'2).
	simpl in *.
	intros.
	pose proof (spItrpUniq _ _ _ _ _ _ _ _ X X0).
	clear X X0.
	revert la'2 H.
	assert (forall T (H:(fun d g=>Type) = T) la'2,(existT (fun T=>forall d g,F d->T d g) _ la'1 = existT _ _ la'2)->
		(tr (fun T=>forall d g,F d->T d g) H la'1 = la'2));[| exact (H _ (eq_refl _))].
	intros.
	revert H.
	apply (tr (fun s=>forall H:(fun d g=>Type) = projT1 s,tr _ H la'1 = projT2 s) H0).
	clear T la'2 H0.
	simpl.
	rename la'1 into la'.
	intro.
	assert (H = eq_refl _).
		Focus 2.
	rewrite H0.
	reflexivity.
Admitted.

(*
 * This lemma effectively says that if we know certain parts of what a family should interpret to,
 * and we know it interprets to something, then the thing it interprets to must match our expectations.
 *)
Lemma sfItrpConsAtInv D G f la T F (f':AtTCtx D f F) la' T' P : SimpFamItrp D G ((f,la) :: T) T'->
	SimpParamItrp G F la (fun d g=>Type) la'->
	(forall T',SimpFamItrp D (extCtx G (fun d g=>la' d g (tctxProj f' d))) T T'->
	P (fun d g=>forall p,T' d (existT _ g p)))->
P T'.
	simpl in la'.
	intros Xf Xp.
	pose (B d g := la' d g (tctxProj f' d)).
	change ((forall T':forall d,extCtx G B d->Type,SimpFamItrp D (extCtx G B) T T'->
		P (fun d g=>forall p,T' d (existT _ g p)))->
	P T').
	intro rtn.
	apply sfItrpConsInv with (1 := Xf).
	clear T' Xf.
	intros ? ? ?.
	pose (B0 d g := la'0 d g (tctxProj f'0 d)).
	change (forall T':forall d,extCtx G B0 d->Type,
		SimpParamItrp G F0 la (fun d g=>Type) la'0->
		SimpFamItrp D (extCtx G B0) T T'->
	P (fun d g=>forall p,T' d (existT _ g p))).
	intros ? Xp0.
	revert T'.
	replace B0 with B.
		exact rtn.
	clear P rtn.
	subst B B0.
	revert la'0 Xp0.
	apply (tr (fun s=>forall la'0 (Xp0:SimpParamItrp G (projT1 s) la (fun d g=>Type) la'0),
		_ = fun d g=>la'0 d g (tctxProj (projT2 s) d)) (atTCtxUniq _ _ _ _ f' f'0)).
	clear F0 f'0.
	simpl.
	intros.
	rewrite <- (spItrpUniq' _ _ _ _ _ _ Xp Xp0).
	reflexivity.
Qed.

Lemma spItrpTotal G F la T D G' F' C : SimpParamOK G F la T->
	SimpCtxItrp D G G'->
	SimpFamItrp D (empCtx D) F (fun d g=>F' d)->
	(forall T' la',
		SimpParamItrp G' F' la T' la'->
		SimpFamItrp D G' T T'->
	C)->
C.
	intros ? Xc XF.
	induction H;intro rtn.

	eapply rtn.
		apply spItrpNil.

		apply sfItrpBuildG with (1 := XF) (2 := e).

	apply scItrpAt with (1 := l) (2 := Xc).
	intros ? ? ? f' la0' ? Xp0 a'.
	pose (P d g := la0' d g (tctxProj f' d)).
	change (AtCtx G' a P) in a'.
	apply IHSimpParamOK.
	intros ? ? Xp.
	rewrite <- H0.
	intro Xf.
	revert la' Xp.
	apply sfItrpConsAtInv with (f' := f') (1 := Xf) (2 := Xp0).
	clear T' Xf.
	intros ? Xf ? ?.
	change (forall d,extCtx G' P d->Type) in T'.
	change (SimpFamItrp D (extCtx G' P) B T') in Xf.
	change (forall d g,F' d->forall p,T' d (existT _ g p)) in la'.
	change (SimpParamItrp G' F' la (fun d g=>forall p,T' d (existT _ g p)) la') in Xp.
	eapply rtn.
		apply spItrpCons with (a' := a') (1 := Xp).

		apply sfItrpSubst_O with (1 := Xf).
Qed.

Lemma sfItrpTotal D G T D' C : SimpFamOK D G T->SimpTCtxItrp D D'->forall G',SimpCtxItrp D' G G'->
	(forall T',SimpFamItrp D' G' T T'->C)->
C.
	intros ? ?.
	induction H;intros.

	eapply X1.
	apply sfItrpNil.

	apply stcItrpAt with (1 := l) (2 := X);intros ? f' ?.
	apply spItrpTotal with (1 := s) (2 := X0) (3 := X2);intros.
	revert la' X3.
	rewrite sfItrpNilInv with (1 := X4).
	clear T' X4.
	intros.
	eapply IHSimpFamOK.
		apply scItrpCons with (f' := f') (1 := X0) (2 := X3).
	simpl.
	intros.
	eapply X1.
	apply sfItrpCons with (1 := X3) (2 := X4).
Qed.

(* Cannot use ad-hoc predicates. No way to compute B. *)
Inductive SimpParamDom D (G:D->Type) F : list nat->Type :=
	spItrpNil : SimpParamDom D G F nil |
	spItrpCons a la P (a':AtCtx G a P) B la' :
		SimpParamDom D G F la->
		SimpParamDom D G F (a :: la).

Inductive SimpFamDom D (G:D->Type) : simpFam->Type :=
	sfDomNil : SimpFamDom D G nil |
	sfDomCons f la T F (f':AtTCtx D f F) la' :
		SimpParamItrp D G F la (fun _ _=>Type) la'->
		SimpFamDom D (fun d=>sigT (fun g=>la' d g (tctxProj f' d))) T->
		SimpFamDom D G ((f,la) :: T).

Lemma spDomItrp D G F la T la' : SimpParamItrp D G F la T la'->SimpParamDom D G F la.
Qed.
Implicit Arguments spDomItrp [D G F la T la'].

Lemma sfDomItrp D G F F' : SimpFamItrp D G F F'->SimpFamDom D G F.
intro.
induction X.

apply sfDomNil.

apply sfDomCons with (1 := s) (2 := IHX).
Qed.
Implicit Arguments sfDomItrp [D G F F'].

Definition itrpSimpParam D G F la (X:SimpParamDom D G F la) : sigT (fun T=>forall d g,F d->T d g).
Defined.

Lemma spItrpUniq D G F la T la' (X:SimpParamItrp D G F la T la') : existT _ T la' = itrpSimpParam D G F la (spDomItrp X).
Qed.

Definition itrpSimpFam D G F (X:SimpFamDom D G F) : forall d,G d->Type.
induction F as [| p];[| destruct p as (f,la)].

exact (fun _ _=>Type).

intros d g.
Defined.
