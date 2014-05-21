Require Import List.
Require Import Compare_dec.

Require Import SimpSyntax.
Require Import Contexts.

Require Import Le Lt.

(* Interpretation relations *)

Inductive SimpParamItrp D (G:D->Type) F : list nat->forall T:forall d,G d->Type,(forall d g,F d->T d g)->Type :=
	spItrpNil : SimpParamItrp D G F nil (fun d _=>F d) (fun _ _ f=>f) |
	spItrpCons a la P (a':AtCtx G a P) B la' :
		SimpParamItrp D G F la (fun d g=>forall p,B d (existT _ g p)) la'->
		SimpParamItrp D G F (a :: la) (fun d g=>B d (existT _ g (ctxProj a' d g))) (fun d g f=>la' d g f (ctxProj a' d g)).

Inductive SimpFamItrp D (G:D->Type) : simpFam->(forall d,G d->Type)->Type :=
	sfItrpNil : SimpFamItrp D G nil (fun _ _=>Type) |
	sfItrpCons f la T F (f':AtTCtx D f F) la' T' :
		SimpParamItrp D G F la (fun _ _=>Type) la'->
		SimpFamItrp D (fun d=>sigT (fun g=>la' d g (tctxProj f' d))) T T'->
		SimpFamItrp D G ((f,la) :: T) (fun d g=>forall p,T' d (existT _ g p)).

Inductive SimpCtxItrp D : list (nat * list nat)->(D->Type)->Type :=
	scItrpNil : SimpCtxItrp D nil (fun _=>unit) |
	scItrpCons f la G G' F (f':AtTCtx D f F) la' :
		SimpCtxItrp D G G'->
		SimpParamItrp D G' F la (fun _ _=>Type) la'->
		SimpCtxItrp D ((f,la) :: G) (fun d=>sigT (fun g=>la' d g (tctxProj f' d))).

Inductive SimpTCtxItrp : list simpFam->Type->Type :=
	stcItrpNil : SimpTCtxItrp nil unit |
	stcItrpCons F D D' F' :
		SimpTCtxItrp D D'->
		SimpFamItrp D' (fun _=>unit) F (fun d _=>F' d)->
		SimpTCtxItrp (F :: D) (sigT F').

Lemma spItrpNilInv D G F T la' (P:forall T:forall d,G d->Type,(forall d g,F d->T d g)->Type) :
SimpParamItrp D G F nil T la'->P (fun d _=>F d) (fun _ _ f=>f)->P T la'.
	intro.
	inversion_clear X.
	intro.
	exact X.
Qed.

Lemma spItrpConsInv D G F a la T la' (C:forall T:forall d,G d->Type,(forall d g,F d->T d g)->Type) :
SimpParamItrp D G F (a :: la) T la'->
	(forall P (a':AtCtx G a P) B la',SimpParamItrp D G F la (fun d g=>forall p,B d (existT _ g p)) la'->
	C (fun d g=>B d (existT _ g (ctxProj a' d g))) (fun d g f=>la' d g f (ctxProj a' d g)))->
C T la'.
	intro.
	inversion_clear X.
	intro.
	apply X with (1 := X0).
Qed.

Lemma sfItrpNilInv D G T : SimpFamItrp D G nil T->(T = fun _ _=>Type).
	assert (forall T_,(nil = T_)->SimpFamItrp D G T_ T->(T = fun _ _=>Type));[| apply H;reflexivity].
	intros.
	destruct X.

	reflexivity.

	destruct nil_cons with (1 := H).
Qed.

Lemma sfItrpConsInv D G f la T T' P : SimpFamItrp D G ((f,la) :: T) T'->
	(forall F (f':AtTCtx D f F) la' T',
		SimpParamItrp D G F la (fun _ _=>Type) la'->
		SimpFamItrp D (fun d=>sigT (fun g=>la' d g (tctxProj f' d))) T T'->
	P (fun d g=>forall p,T' d (existT _ g p)))->
P T'.
	intro.
	inversion_clear X.
	intro.
	apply X with (1 := X0) (2 := X1).
Qed.

Lemma scItrpConsInv D f la G G' P : SimpCtxItrp D ((f,la) :: G) G'->
	(forall G' F (f':AtTCtx D f F) la',SimpCtxItrp D G G'->SimpParamItrp D G' F la (fun _ _=>Type) la'->
	P (fun d=>sigT (fun g=>la' d g (tctxProj f' d))))->
P G'.
	intros.
	inversion_clear X.
	apply X0 with (1 := X1) (2 := X2).
Qed.

Lemma stcItrpConsInv F D D' P : SimpTCtxItrp (F :: D) D'->
	(forall D' F',SimpTCtxItrp D D'->SimpFamItrp D' (fun _=>unit) F (fun d _=>F' d)->
	P (sigT F'))->
P D'.
	intros.
	inversion_clear X.
	apply X0 with (1 := X1) (2 := X2).
Qed.

(*
Lemma spItrpBumpGS D G F n la P : forall T la',SimpParamItrp D G F (laBumpG n O la) T la'->
SimpParamItrp D (fun d=>sigT (P d)) F (laBumpG (S n) O la) (fun d g=>T d (projT1 g)) (fun d g=>la' d (projT1 g)).
	induction la;simpl.

	intros.
	apply spItrpNilInv with (1 := X).
	apply spItrpNil.

	intros ? ?.
	assert (forall k,k = match nat_compare a O with
		Lt => a |
		_ => k
	end) as nolt.
		intro.
		destruct (nat_compare_spec a O);try reflexivity.
		destruct lt_n_O with (1 := H).
	rewrite <- nolt.
	rewrite <- nolt.
	clear nolt.
	intro.
	apply spItrpConsInv with (1 := X).
	clear T la' X.
	intros.
	pose proof (IHla _ _ X).
	apply spItrpCons with (a' := popCtx _ a')
		(B := fun d (g':sigT (fun g=>P0 d (projT1 g)))=>match g' with existT g p=>B d (existT _ (projT1 g) p) end)
		(1 := X0).
Qed.
*)

Definition bumpCtx D GL P l G (xg:ExtCtx D GL l G) := extCtxComp xg (fun d=>sigT (P d)) (fun d=>@projT1 _ _).
Implicit Arguments bumpCtx [D GL l G].

Definition bumpG D GL P l G (xg:ExtCtx D GL l G) := xc_G' (bumpCtx P xg).
Implicit Arguments bumpG [D GL l G].

Definition bumpF D GL P l G (xg:ExtCtx D GL l G) T (F:forall d (g:G d),T d g) d (g:bumpG P xg d) := F d (xc_f' (bumpCtx P xg) d g).
Implicit Arguments bumpF [D GL l G T].

Lemma spItrpBumpGS D G F n l la GL P (xg:ExtCtx D GL l G) : forall T la',SimpParamItrp D G F (laBumpG n l la) T la'->
SimpParamItrp D (bumpG P xg) F (laBumpG (S n) l la) (bumpF P xg T) (bumpF P xg la').
(* Do I need such a general induction pred? *)
	unfold bumpF.
	unfold bumpG.
	set (xc := bumpCtx P xg).
	set (G' := xc_G' xc).
	set (f' := xc_f' xc).
	change (forall d,G' d->G d) in (type of f').
	induction la;simpl.

	intros.
	apply spItrpNilInv with (1 := X).
	apply spItrpNil.

	intros ? ?.
destruct (lt_dec a l) as [Ho | Ho].
Focus 2.
	assert (forall k,k = match nat_compare a l with
		Lt => a |
		_ => k
	end) as nolt.
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
assert (AtCtx G' (S n + a) (fun d g=>P0 d (f' d g))) as a''.
Focus 2.
pose proof (spItrpCons _ _ _ _ _ _ a''
	(fun d (g:sigT (fun g=>P0 d (f' d g)))=>B d (existT _ (f' d (projT1 g)) (projT2 g))) _ (IHla _ _ X)).
simpl in X0.
rewrite in X0.
exact X0.
Qed.

Lemma spItrpBumpGS_O D G F n la T la' P : SimpParamItrp D G F (laBumpG n O la) T la'->
SimpParamItrp D (fun d=>sigT (P d)) F (laBumpG (S n) O la) (fun d g=>T d (projT1 g)) (fun d g=>la' d (projT1 g)).
	apply spItrpBumpGS with (P := P) (xg := extCtxO D G).
Qed.

Lemma sfItrpBumpGS D n F GL P : forall G l F' (xg:ExtCtx D GL l G),SimpFamItrp D G (fBumpG n l F) F'->
SimpFamItrp D (bumpG P xg) (fBumpG (S n) l F) (bumpF P xg F').
	unfold bumpF.
	unfold bumpG.
	induction F as [| p];[| destruct p as (f,la)];simpl;intros until 1.

	rewrite sfItrpNilInv with (1 := X).
	clear n F' X.
	apply sfItrpNil.

	apply sfItrpConsInv with (1 := X).
	clear F' X.
	intros B ? ?.
	pose (A d g := la' d g (tctxProj f' d)).
	change (forall F',SimpParamItrp D G B (laBumpG n l la) (fun _ _=>Type) la'->
		SimpFamItrp D (fun d=>sigT (A d)) (fBumpG n (S l) F) F'->
		SimpFamItrp D (xc_G' (bumpCtx P xg)) ((f,laBumpG (S n) l la) :: fBumpG (S n) (S l) F)
			(fun d g=>forall p,F' d (existT _ (xc_f' (bumpCtx P xg) d g) p))).
	simpl.
	intros ? Xp Xf.
	pose (F_ d g := forall p,F' d (existT _ g p)).
	change (SimpFamItrp D (xc_G' (bumpCtx P xg))
		((f,laBumpG (S n) l la) :: fBumpG (S n) (S l) F)
		(fun d g=>F_ d (xc_f' (bumpCtx P xg) d g))).
	pose proof (IHF _ _ _ (extCtxS xg _) Xf) as Xfb.
	clear Xf.
	pose (GLb d := sigT (P d)).
	pose (u d := @projT1 _ (P d)).
	change (bumpCtx P (extCtxS xg A)) with (extCtxComp (extCtxS xg A) GLb u) in Xfb.
	rewrite extCtxCompSEq in Xfb.
	unfold extCtxSComp' in Xfb.
	pose proof (extCtxSCompRewr (bumpCtx P xg) _
		(fun G' f'=>SimpFamItrp D G' (fBumpG (S n) (S l) F) (fun d g=>F' d (f' d g))) Xfb) as Xfb'.
	simpl in Xfb'.
	clear GLb u Xfb.
	pose (Gb := xc_G' (bumpCtx P xg)).
	pose (u := xc_f' (bumpCtx P xg)).
	change (forall d,Gb d->G d) in (type of u).
	pose (la'b d g := la' d (u d g)).
	pose (F'b d (g:sigT (fun g=>la'b d g (tctxProj f' d))) := F' d (existT (A d) (u d (projT1 g)) (projT2 g))).
	change (SimpFamItrp D (fun d=>sigT (fun g=>la'b d g (tctxProj f' d))) (fBumpG (S n) (S l) F) F'b) in Xfb'.
	apply sfItrpCons with (2 := Xfb').
	clear F'b Xfb'.
	subst la'b.
	apply spItrpBumpGS with (1 := Xp) (xg := xg).
Qed.

Lemma sfItrpBumpGS_O D G n F F' P : SimpFamItrp D G (fBumpG n O F) F'->
SimpFamItrp D (fun d=>sigT (P d)) (fBumpG (S n) O F) (fun d g=>F' d (projT1 g)).
	apply sfItrpBumpGS with (P := P) (xg := extCtxO D G).
Qed.

Lemma spItrpBumpD D G F la T la' B : SimpParamItrp D G F la T la'->
SimpParamItrp (sigT B) (fun d=>G (projT1 d)) (fun d=>F (projT1 d)) la (fun d=>T (projT1 d)) (fun d=>la' (projT1 d)).
	intro.
	induction X.

	apply spItrpNil.

	pose proof (spItrpCons _ _ _ _ _ _ (ctxBumpD _ a') (fun d=>B0 (projT1 d)) _ IHX).
	simpl in X0.
	rewrite ctxProj_BumpD in X0.
	exact X0.
Qed.

Lemma sfItrpBumpDS D n F T : forall G F',SimpFamItrp D G (fBumpD n F) F'->
SimpFamItrp (sigT T) (fun d=>G (projT1 d)) (fBumpD (S n) F) (fun d=>F' (projT1 d)).
	induction F;simpl;intros.

	rewrite sfItrpNilInv with (1 := X).
	apply sfItrpNil.

	destruct a as (f,la).
	apply sfItrpConsInv with (1 := X).
	clear F' X.
	intros B ? ? F'.
	intros.
	pose proof (IHF _ _ X0).
	apply sfItrpCons with (f' := popTCtx T f') (la' := fun d=>la' (projT1 d)) (2 := X1).
	apply spItrpBumpD with (1 := X).
Qed.

Lemma scItrpAt a D C : forall G G',(a < length G)->SimpCtxItrp D G G'->
	(forall f la F (f':AtTCtx D f F) la',((f,la) = pBumpG (S a) O (nth a G (O,nil)))->
		SimpParamItrp D G' F la (fun _ _=>Type) la'->
		AtCtx G' a (fun d g=>la' d g (tctxProj f' d))->
	C)->
C.
	induction a;intros ? ?;
	(destruct G;intro H;[destruct lt_n_O with (1 := H) |]);
	simpl in H;destruct p as (f,la);intro X;
	apply scItrpConsInv with (1 := X);clear G' X;simpl;intros.

	rewrite <- laBumpG_O with (l := O) (la := la) in X0.
	pose proof (spItrpBumpGS_O _ _ _ _ _ _ _ (fun d g=>la' d g (tctxProj f' d)) X0).
	apply X1 with (1 := eq_refl _) (2 := X2) (3 := topCtx _).

	apply IHa with (2 := X).
		apply lt_S_n with (1 := H).
	intros.
	destruct (nth a G (O,nil)) as (f_,la_).
	simpl in X1,H0.
	assert (f0 = f_).
		change (fst (f0,la0) = fst (f_,laBumpG (S a) O la_)).
		rewrite <- H0.
		reflexivity.
	assert (la0 = laBumpG (S a) O la_).
		change (snd (f0,la0) = snd (f_,laBumpG (S a) O la_)).
		rewrite <- H0.
		reflexivity.
	clear H0.
	subst f0 la0.
	pose proof (spItrpBumpGS_O _ _ _ _ _ _ _ (fun d g=>la' d g (tctxProj f' d)) X2).
	apply X1 with (1 := eq_refl _) (2 := X4) (3 := popCtx _ X3).
Qed.

Lemma stcItrpAt f C : forall D D',(f < length D)->SimpTCtxItrp D D'->
	(forall F,AtTCtx D' f F->
		SimpFamItrp D' (fun _=>unit) (fBumpD (S f) (nth f D nil)) (fun d _=>F d)->
	C)->
C.
	induction f;intros ? ?;
	(destruct D as [| F];intro H;[destruct lt_n_O with (1 := H) |]);intro X;
	apply stcItrpConsInv with (1 := X);clear D' X;simpl;intros.

	apply X1 with (1 := topTCtx _).
	apply sfItrpBumpDS with (G := fun _=>unit) (F' := fun d _=>F' d).
	rewrite fBumpD_O.
	exact X0.

	apply IHf with (2 := X).
		apply lt_S_n with (1 := H).
	intros.
	apply X1 with (1 := popTCtx _ X2).
	apply sfItrpBumpDS with (1 := X3).
Qed.

Lemma sfItrpBuildG D G G' T T' : SimpFamItrp D (fun _=>unit) T (fun d _=>T' d)->
	SimpCtxItrp D G G'->(fBumpG 1 O T = T)->
SimpFamItrp D G' T (fun d _=>T' d).
	simpl.
	intros.
	induction X0.

	exact X.

	rewrite <- H.
	rewrite <- fBumpG_O with (l := O) (F := T) in IHX0.
	apply sfItrpBumpGS_O with (1 := IHX0).
Qed.

Lemma sfItrpConsAtInv D G f la T F (f':AtTCtx D f F) la' T' P : SimpFamItrp D G ((f,la) :: T) T'->
	SimpParamItrp D G F la (fun _ _=>Type) la'->
	(forall T',SimpFamItrp D (fun d=>sigT (fun g=>la' d g (tctxProj f' d))) T T'->
	P (fun d g=>forall p,T' d (existT _ g p)))->
P T'.
Admitted.

Lemma spItrpTotal G F la T D G' F' C : SimpParamOK G F la T->
	SimpCtxItrp D G G'->
	SimpFamItrp D (fun _=>unit) F (fun d _=>F' d)->
	(forall T' la',
		SimpParamItrp D G' F' la T' la'->
		SimpFamItrp D G' T T'->
	C)->
C.
	simpl.
intros ? ? ?.
induction H;intro.

eapply X1.
	apply spItrpNil.

	apply sfItrpBuildG with (1 := X0) (2 := X) (3 := e).

apply scItrpAt with (1 := l) (2 := X).
intros ? ? ? f' la0' ? ? a'.
pose (P d g := la0' d g (tctxProj f' d)).
change (AtCtx G' a P) in a'.
apply IHSimpParamOK.
rewrite <- H0.
intros.
revert la' X3.
apply sfItrpConsAtInv with (f' := f') (1 := X4) (2 := X2).
clear T' X4.
intros.
change (forall d,sigT (P d)->Type) in T'.
change (SimpFamItrp D (fun d=>sigT (P d)) B T') in X3.
change (forall d g,F' d->forall p,T' d (existT _ g p)) in la'.
change (SimpParamItrp D G' F' la (fun d g=>forall p,T' d (existT _ g p)) la') in X4.
eapply X1.

apply spItrpCons with (a' := a') (1 := X4).

(* Need substitution lemma *)
Admitted.

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
