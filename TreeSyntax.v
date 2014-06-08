Require Import List.
Require Import Compare_dec.

Require Import Utils.
Require Import SimpSyntax.

Require Import Le Lt.
Require Import Plus Minus.

(* Tree syntax for types, to do typing in one context *)
Inductive treeFam : Set :=
	Uv |
	El (p:nat * list nat) |
	Pi (A B:treeFam).

(* One-context substitutions *)

Definition pBump n l (p:nat * _) := let (f,la) := p in (varBump n l f,laBump n l la).
Definition pSubst (p:nat * _) l b := let (f,la) := p in (varSubst l b f,laSubst la l b).

Fixpoint fBump n l F := match F with
	Uv => Uv |
	El p => El (pBump n l p) |
	Pi A B => Pi (fBump n l A) (fBump n (S l) B)
end.

Fixpoint fSubst F l b := match F with
	Uv => Uv |
	El p => El (pSubst p l b) |
	Pi A B => Pi (fSubst A l b) (fSubst B (S l) b)
end.

Fixpoint tcBump n G := match G with
	nil => nil |
	F :: G => fBump n (length G) F :: tcBump n G
end.

Fixpoint tcSubst G b := match G with
	nil => nil |
	F :: G => fSubst F (length G) b :: tcSubst G b
end.

Lemma pBump_O l p : pBump O l p = p.
	destruct p as (f,la).
	simpl.
	rewrite laBump_O.
	unfold varBump.
	simpl.
	destruct (nat_compare f l);reflexivity.
Qed.

Lemma pBump_Bump n1 n2 l1 l2 p : (l1 <= l2)->(pBump n2 (n1 + l2) (pBump n1 l1 p) = pBump n1 l1 (pBump n2 l2 p)).
	intro.
	destruct p as (f,la).
	simpl.
	rewrite varBump_Bump with (1 := H).
	rewrite laBump_Bump with (1 := H).
	reflexivity.
Qed.

Lemma pBumpDiv a b n l p : (n <= b)->(pBump a (l + n) (pBump b l p) = pBump (a + b) l p).
	intro.
	destruct p as (f,la).
	simpl.
	rewrite varBumpDiv with (1 := H).
	rewrite laBumpDiv with (1 := H).
	reflexivity.
Qed.

Lemma pBump_Subst n x p l b : pBump n (x + l) (pSubst p l b) = pSubst (pBump n (S x + l) p) l (varBump n x b).
	destruct p as (f,la).
	simpl.
	change (S (x + l)) with (S x + l).
	rewrite <- varBump_Subst.
	rewrite <- laBump_Subst.
	reflexivity.
Qed.

Lemma pSubst_Bump n p l1 l2 b : (l1 <= l2)->(pSubst (pBump n l1 p) (n + l2) b = pBump n l1 (pSubst p l2 b)).
	intro.
	destruct p as (f,la).
	simpl.
	rewrite varSubst_Bump with (1 := H).
	rewrite laSubst_Bump with (1 := H).
	reflexivity.
Qed.

Lemma pSubstDiv n p l1 l2 b : (l1 <= l2 <= l1 + n)->(pSubst (pBump (S n) l1 p) l2 b = pBump n l1 p).
	intro.
	destruct p as (f,la).
	simpl.
	rewrite varSubstDiv with (1 := H).
	rewrite laSubstDiv with (1 := H).
	reflexivity.
Qed.

Lemma pSubst_Subst x p l b1 b2 : pSubst (pSubst p l b2) (x + l) b1 =
pSubst (pSubst p (S x + l) b1) l (varSubst x b1 b2).
	destruct p as (f,la).
	simpl.
	change (S (x + l)) with (S x + l).
	rewrite <- varSubst_Subst.
	rewrite <- laSubst_Subst.
	reflexivity.
Qed.

Lemma fBump_O F : forall l,fBump O l F = F.
	induction F;intro;simpl.

	reflexivity.

	rewrite pBump_O.
	reflexivity.

	rewrite IHF1.
	rewrite IHF2.
	reflexivity.
Qed.

Lemma fBump_Bump n1 n2 F : forall l1 l2,(l1 <= l2)->
(fBump n2 (n1 + l2) (fBump n1 l1 F) = fBump n1 l1 (fBump n2 l2 F)).
	induction F;intros;simpl.

	reflexivity.

	rewrite pBump_Bump with (1 := H).
	reflexivity.

	rewrite plus_n_Sm.
	rewrite IHF1 with (1 := H).
	rewrite IHF2 with (1 := le_n_S _ _ H).
	reflexivity.
Qed.

Lemma fBumpDiv a b n F : (n <= b)->forall l,fBump a (l + n) (fBump b l F) = fBump (a + b) l F.
	intro.
	induction F;intro;simpl.

	reflexivity.

	rewrite pBumpDiv with (1 := H).
	reflexivity.

	change (S (l + n)) with (S l + n).
	rewrite IHF1.
	rewrite IHF2.
	reflexivity.
Qed.

Lemma fBump_Subst n x F b : forall l,
fBump n (x + l) (fSubst F l b) = fSubst (fBump n (S x + l) F) l (varBump n x b).
	induction F;intro;simpl.

	reflexivity.

	change (S (x + l)) with (S x + l).
	rewrite <- pBump_Subst.
	reflexivity.

	change (S (x + l)) with (S x + l) at 2.
	rewrite plus_n_Sm.
	change (S (x + S l)) with (S x + S l).
	rewrite <- IHF1.
	rewrite <- IHF2.
	reflexivity.
Qed.

Lemma fSubst_Bump n F b : forall l1 l2,(l1 <= l2)->
(fSubst (fBump n l1 F) (n + l2) b = fBump n l1 (fSubst F l2 b)).
	induction F;intros;simpl.

	reflexivity.

	rewrite pSubst_Bump with (1 := H).
	reflexivity.

	rewrite plus_n_Sm.
	rewrite IHF1 with (1 := H).
	rewrite IHF2 with (1 := le_n_S _ _ H).
	reflexivity.
Qed.

Lemma fSubstDiv n F b : forall l1 l2,(l1 <= l2 <= l1 + n)->(fSubst (fBump (S n) l1 F) l2 b = fBump n l1 F).
	induction F;intros;simpl.

	reflexivity.

	rewrite pSubstDiv with (1 := H).
	reflexivity.

	rewrite IHF1 with (1 := H).
	rewrite IHF2.
		reflexivity.
	destruct H.
	exact (conj (le_n_S _ _ H) (le_n_S _ _ H0)).
Qed.

Lemma fSubst_Subst x F b1 b2 : forall l,fSubst (fSubst F l b2) (x + l) b1 =
fSubst (fSubst F (S x + l) b1) l (varSubst x b1 b2).
	induction F;intros;simpl.

	reflexivity.

	change (S (x + l)) with (S x + l).
	rewrite <- pSubst_Subst.
	reflexivity.

	change (S (x + l)) with (S x + l) at 2.
	rewrite plus_n_Sm.
	change (S (x + S l)) with (S x + S l).
	rewrite <- IHF1.
	rewrite <- IHF2.
	reflexivity.
Qed.

Lemma tcBump_length n G : length (tcBump n G) = length G.
	induction G;simpl.

	reflexivity.

	rewrite IHG.
	reflexivity.
Qed.

Lemma tcBump_nth i n : forall G,(i < length G)->(nth i (tcBump n G) Uv = fBump n (length G - S i) (nth i G Uv)).
	induction i;intro;(destruct G as [| F];intro;[destruct lt_n_O with (1 := H) |]);simpl.

	rewrite <- minus_n_O.
	reflexivity.

	apply IHi.
	apply lt_S_n with (1 := H).
Qed.

Lemma tcSubst_length G b : length (tcSubst G b) = length G.
	induction G;simpl.

	reflexivity.

	rewrite IHG.
	reflexivity.
Qed.

Lemma tcSubst_nth i b : forall G,(i < length G)->
(nth i (tcSubst G b) Uv = fSubst (nth i G Uv) (length G - S i) b).
	induction i;intro;(destruct G as [| F];intro;[destruct lt_n_O with (1 := H) |]);simpl.

	rewrite <- minus_n_O.
	reflexivity.

	apply IHi.
	apply lt_S_n with (1 := H).
Qed.

(* One-context typing rules. SimpParamGood is a "nested" inductive family. *)

Inductive TreeFamGood PG G : treeFam->Type :=
	tfGoodUv : TreeFamGood PG G Uv |
	tfGoodEl f la : (f < length G)->
		PG G (fBump (S f) O (nth f G Uv)) la Uv->
		TreeFamGood PG G (El (f,la)) |
	tfGoodPi A B : TreeFamGood PG G A->TreeFamGood PG (A :: G) B->
		TreeFamGood PG G (Pi A B).

Unset Elimination Schemes.
Inductive SimpParamGood G F : list nat->treeFam->Set :=
	spGoodNil : SimpParamGood G F nil F |
	spGoodCons a la B : (a < length G)->
		SimpParamGood G F la (Pi (fBump (S a) O (nth a G Uv)) B)->
		SimpParamGood G F (a :: la) (fSubst B O a).
Set Elimination Schemes.

(* Mapping the PG in a TreeFamGood *)
Section TFGMap.

Variable A B : list treeFam->treeFam->list nat->treeFam->Type.
Variable X : forall G F la T,A G F la T->B G F la T.

Fixpoint tfGoodMap G F (HF:TreeFamGood A G F) : TreeFamGood B G F := match HF with
	tfGoodUv => tfGoodUv _ _ |
	tfGoodEl _ _ H HP => tfGoodEl _ _ _ _ H (X _ _ _ _ HP) |
	tfGoodPi _ _ HA HB => tfGoodPi _ _ _ _ (tfGoodMap _ _ HA) (tfGoodMap _ _ HB)
end.

End TFGMap.
Implicit Arguments tfGoodMap [A B G F].

(* A (non-dependent) nested recursion principle for SimpParamGood *)
Section SPGRect.

Variable P : list treeFam->treeFam->list nat->treeFam->Type.

Variable Pnil : forall G F,P G F nil F.
Variable Pcons : forall G F a la B,(a < length G)->
	P G F la (Pi (fBump (S a) O (nth a G Uv)) B)->
	P G F (a :: la) (fSubst B O a).

Fixpoint SimpParamGood_rect G F la T (Hla:SimpParamGood G F la T) : P G F la T := match Hla with
	spGoodNil => Pnil _ _ |
	spGoodCons _ _ _ H Hla => Pcons _ _ _ _ _ H (SimpParamGood_rect _ _ _ _ Hla)
end.

End SPGRect.

Definition SimpParamGood_ind (P:list treeFam->treeFam->list nat->treeFam->Prop) := SimpParamGood_rect P.
Definition SimpParamGood_rec (P:list treeFam->treeFam->list nat->treeFam->Set) := SimpParamGood_rect P.

Definition TreeFamGoodPG := TreeFamGood SimpParamGood.

Inductive TreeCtxGood : list treeFam->Set :=
	tcGoodNil : TreeCtxGood nil |
	tcGoodCons F G : TreeFamGoodPG G F->TreeCtxGood G->TreeCtxGood (F :: G).

Lemma ctxProjGood i : forall G,TreeCtxGood G->TreeFamGoodPG (skipn (S i) G) (nth i G Uv).
	induction i;intros;(destruct H;[simpl;apply tfGoodUv |]).

	exact t.

	exact (IHi _ H).
Qed.

Lemma tfGoodBumpNest GL X GR F : TreeFamGood (fun G F la T=>forall GR,(G = GR ++ GL)->
	SimpParamGood (tcBump (length X) GR ++ X ++ GL) (fBump (length X) (length GR) F)
		(laBump (length X) (length GR) la) (fBump (length X) (length GR) T))
	(GR ++ GL) F->
TreeFamGoodPG (tcBump (length X) GR ++ X ++ GL) (fBump (length X) (length GR) F).
	set (P G F la T := forall GR,(G = GR ++ GL)->
		SimpParamGood (tcBump (length X) GR ++ X ++ GL) (fBump (length X) (length GR) F)
			(laBump (length X) (length GR) la) (fBump (length X) (length GR) T)).
	remember (GR ++ GL) as G.
	intro.
	revert GR HeqG.
	induction H;intros;simpl.

	apply tfGoodUv.

	subst P.
	simpl in p.
	pose proof (p _ HeqG).
	clear p.
	destruct (le_lt_dec (length GR) f).
		subst G.
		rewrite varBumpHi with (1 := le_not_lt _ _ l0).
		apply tfGoodEl.
			rewrite app_length.
			rewrite tcBump_length.
			rewrite app_length.
			rewrite plus_assoc.
			rewrite <- (plus_comm (length X)).
			rewrite <- plus_assoc.
			apply plus_lt_compat_l.
			rewrite <- app_length.
			exact l.
		rewrite app_nth2;rewrite tcBump_length;[| apply le_trans with (1 := l0);apply le_plus_r].
		rewrite <- le_plus_minus_assoc with (1 := l0).
		rewrite app_nth2;[| apply le_plus_l].
		rewrite minus_plus.
		rewrite plus_n_Sm.
		rewrite <- fBumpDiv with (1 := le_S _ _ l0).
		simpl.
		rewrite <- app_nth2 with (1 := l0).
		exact H.

		clear l.
		subst G.
		rewrite varBumpLo with (1 := l0).
		apply tfGoodEl.
			rewrite app_length.
			rewrite tcBump_length.
			apply le_trans with (1 := l0).
			apply le_plus_l.
		rewrite app_nth1;[| rewrite tcBump_length;exact l0].
		rewrite tcBump_nth with (1 := l0).
		rewrite <- fBump_Bump with (1 := le_O_n _).
		rewrite <- le_plus_minus with (1 := l0).
		rewrite <- app_nth1 with (l' := GL) (1 := l0).
		exact H.

	apply tfGoodPi.
		exact (IHTreeFamGood1 _ HeqG).

		apply (IHTreeFamGood2 (A :: GR)).
		simpl.
		rewrite <- HeqG.
		reflexivity.
Qed.

Lemma spGoodBump GL X GR F la T : SimpParamGood (GR ++ GL) F la T->
SimpParamGood (tcBump (length X) GR ++ X ++ GL) (fBump (length X) (length GR) F)
(laBump (length X) (length GR) la) (fBump (length X) (length GR) T).
	remember (GR ++ GL) as G.
	intro.
	revert GR HeqG.
	induction H;intros;simpl.

	apply spGoodNil.

	assert (IH := IHSimpParamGood _ HeqG).
	clear IHSimpParamGood.
	set (gr := length GR) at 4.
	rewrite (plus_n_O gr).
	subst gr.
	rewrite fBump_Subst.
	simpl.
	rewrite <- plus_n_O.
	destruct (le_lt_dec (length GR) a).
		subst G.
		rewrite varBumpHi with (1 := le_not_lt _ _ l).
		assert (let a' := length X + a in
		fBump (length X) (length GR) (fBump (S a) O (nth a (GR ++ GL) Uv)) =
		fBump (S a') O (nth a' (tcBump (length X) GR ++ X ++ GL) Uv)).
			simpl.
			rewrite app_nth2 with (1 := l).
			rewrite app_nth2;rewrite tcBump_length;[| apply le_trans with (1 := l);apply le_plus_r].
			rewrite <- le_plus_minus_assoc with (1 := l).
			rewrite app_nth2 with (1 := le_plus_l _ _).
			rewrite minus_plus.
			change (length GR) at 1 with (O + length GR).
			rewrite fBumpDiv with (1 := le_S _ _ l).
			rewrite <- plus_n_Sm.
			reflexivity.
		simpl in H0.
		apply spGoodCons.
			rewrite app_length.
			rewrite tcBump_length.
			rewrite app_length.
			rewrite plus_assoc.
			rewrite <- (plus_comm (length X)).
			rewrite <- plus_assoc.
			apply plus_lt_compat_l.
			rewrite <- app_length.
			exact H.
		rewrite <- H0.
		exact IH.

		clear H.
		subst G.
		rewrite varBumpLo with (1 := l).
		assert (fBump (length X) (length GR) (fBump (S a) O (nth a (GR ++ GL) Uv)) =
		fBump (S a) O (nth a (tcBump (length X) GR ++ X ++ GL) Uv)).
			rewrite app_nth1 with (1 := l).
			rewrite app_nth1;[| rewrite tcBump_length;exact l].
			rewrite tcBump_nth with (1 := l).
			rewrite <- fBump_Bump with (1 := le_O_n _).
			rewrite <- le_plus_minus with (1 := l).
			reflexivity.
		apply spGoodCons.
			rewrite app_length.
			rewrite tcBump_length.
			apply le_trans with (1 := l).
			apply le_plus_l.
		rewrite <- H.
		exact IH.
Qed.

Lemma tfGoodBump GL X GR F : TreeFamGoodPG (GR ++ GL) F->
TreeFamGoodPG (tcBump (length X) GR ++ X ++ GL) (fBump (length X) (length GR) F).
	intro.
	apply tfGoodBumpNest.
	revert H.
	apply tfGoodMap.
	clear GR F.
	intros.
	apply spGoodBump.
	rewrite <- H0.
	exact H.
Qed.

Lemma tfGoodBump_O G X F : TreeFamGoodPG G F->TreeFamGoodPG (X ++ G) (fBump (length X) O F).
	apply (tfGoodBump G X nil).
Qed.

Lemma tfGoodBump_unskip G n F : (n <= length G)->TreeFamGoodPG (skipn n G) F->TreeFamGoodPG G (fBump n O F).
	intros.
	rewrite <- (firstn_skipn n G).
	set n at 3.
	replace n0 with (length (firstn n G));subst n0.
		apply tfGoodBump_O with (1 := H0).
	rewrite firstn_length.
	apply MinMax.min_l with (1 := H).
Qed.

Lemma tfGoodSubstNest GL GR F b : (b < length GL)->let X := fBump (S b) O (nth b GL Uv) in
TreeFamGood (fun G F la T=>forall GR,(G = GR ++ X :: GL)->
	SimpParamGood (tcSubst GR b ++ GL) (fSubst F (length GR) b)
		(laSubst la (length GR) b) (fSubst T (length GR) b))
	(GR ++ X :: GL) F->
TreeFamGoodPG (tcSubst GR b ++ GL) (fSubst F (length GR) b).
	intros ? ?.
	set (P G F la T := forall GR,(G = GR ++ X :: GL)->
		SimpParamGood (tcSubst GR b ++ GL) (fSubst F (length GR) b)
			(laSubst la (length GR) b) (fSubst T (length GR) b)).
	remember (GR ++ X :: GL) as G.
	intro.
	revert GR HeqG.
	induction H0;intros;simpl.

	apply tfGoodUv.

	subst P.
	simpl in p.
	pose proof (p _ HeqG).
	clear p.
	destruct (lt_eq_lt_dec f (length GR));[clear l;destruct s |].
		rewrite varSubstLt with (1 := l).
		subst G.
		apply tfGoodEl.
			rewrite app_length.
			rewrite tcSubst_length.
			apply le_trans with (1 := l).
			apply le_plus_l.
		rewrite app_nth1;[| rewrite tcSubst_length;exact l].
		rewrite tcSubst_nth with (1 := l).
		rewrite <- fSubst_Bump with (1 := le_O_n _).
		rewrite <- le_plus_minus with (1 := l).
		rewrite <- app_nth1 with (l' := X :: GL) (1 := l).
		exact H0.

		rewrite varSubstEq with (1 := e).
		revert H0.
		rewrite HeqG.
		rewrite e.
		clear G f HeqG e.
		rewrite app_nth2 with (1 := le_n _).
		rewrite minus_diag.
		simpl.
		intro.
		apply tfGoodEl.
			rewrite app_length.
			rewrite tcSubst_length.
			apply plus_lt_compat_l with (1 := H).
		rewrite app_nth2;rewrite tcSubst_length;[| apply le_plus_l].
		rewrite minus_plus.
		rewrite plus_n_Sm.
		rewrite <- fSubstDiv with (l2 := length GR) (b := b)
			(1 := conj (le_O_n _) (le_plus_l _ _)).
		change (S (length GR + S b)) with (S (length GR) + S b).
		rewrite <- fBumpDiv with (1 := le_O_n _).
		exact H0.

		rewrite varSubstGt with (1 := l0).
		revert l H0.
		rewrite HeqG.
		clear G HeqG.
		destruct f.
			destruct lt_n_O with (1 := l0).
		rewrite app_length.
		simpl.
		rewrite <- plus_n_Sm.
		intro.
		rewrite app_nth2 with (1 := lt_le_weak _ _ l0).
		pose proof (le_S_n _ _ l0).
		pose proof (lt_S_n _ _ l).
		clear l0 l.
		rewrite <- minus_Sn_m with (1 := H0).
		simpl.
		intro.
		apply tfGoodEl.
			rewrite app_length.
			rewrite tcSubst_length.
			exact H1.
		rewrite app_nth2;rewrite tcSubst_length;[| exact H0].
		rewrite <- fSubstDiv with (l2 := length GR) (b := b)
			(1 := conj (le_O_n _) (le_S _ _ H0)).
		exact H2.

	apply tfGoodPi.
		exact (IHTreeFamGood1 _ HeqG).

		apply (IHTreeFamGood2 (A :: GR)).
		simpl.
		rewrite <- HeqG.
		reflexivity.
Qed.

Lemma spGoodSubst GL GR F la T b : (b < length GL)->
	SimpParamGood (GR ++ fBump (S b) O (nth b GL Uv) :: GL) F la T->
SimpParamGood (tcSubst GR b ++ GL) (fSubst F (length GR) b) (laSubst la (length GR) b) (fSubst T (length GR) b).
	intro.
	set (X := fBump (S b) O (nth b GL Uv)).
	remember (GR ++ X :: GL) as G.
	intro.
	revert GR HeqG.
	induction H0;intros;simpl.

	apply spGoodNil.

	assert (IH := IHSimpParamGood _ HeqG).
	clear IHSimpParamGood.
	set (gr := length GR) at 4.
	rewrite (plus_n_O gr).
	subst gr.
	rewrite fSubst_Subst.
	simpl.
	rewrite <- plus_n_O.
	destruct (lt_eq_lt_dec a (length GR));[clear H0;destruct s |].
		rewrite varSubstLt with (1 := l).
		subst G.
		assert (fSubst (fBump (S a) O (nth a (GR ++ X :: GL) Uv)) (length GR) b =
		fBump (S a) O (nth a (tcSubst GR b ++ GL) Uv)).
			rewrite app_nth1 with (1 := l).
			rewrite app_nth1;[| rewrite tcSubst_length;exact l].
			rewrite tcSubst_nth with (1 := l).
			rewrite <- fSubst_Bump with (1 := le_O_n _).
			rewrite <- le_plus_minus with (1 := l).
			reflexivity.
		apply spGoodCons.
			rewrite app_length.
			rewrite tcSubst_length.
			apply le_trans with (1 := l).
			apply le_plus_l.
		rewrite <- H0.
		exact IH.

		rewrite varSubstEq with (1 := e).
		subst G.
		assert (let a' := length GR + b in
		fSubst (fBump (S a) O (nth a (GR ++ X :: GL) Uv)) (length GR) b =
		fBump (S a') O (nth a' (tcSubst GR b ++ GL) Uv)).
			rewrite e.
			simpl.
			rewrite app_nth2 with (1 := le_n _).
			rewrite minus_diag.
			simpl.
			rewrite app_nth2;rewrite tcSubst_length;[| apply le_plus_l].
			rewrite minus_plus.
			rewrite fSubstDiv with (1 := conj (le_O_n (length GR)) (le_n _)).
			rewrite plus_n_Sm.
			rewrite <- fBumpDiv with (1 := le_O_n _).
			simpl.
			fold X.
			reflexivity.
		simpl in H0.
		apply spGoodCons.
			rewrite app_length.
			rewrite tcSubst_length.
			apply plus_lt_compat_l with (1 := H).
		rewrite <- H0.
		exact IH.

		rewrite varSubstGt with (1 := l).
		subst G.
		revert H0 IH.
		destruct a.
			destruct lt_n_O with (1 := l).
		rewrite app_length.
		simpl.
		rewrite <- plus_n_Sm.
		intro.
		rewrite app_nth2 with (1 := lt_le_weak _ _ l).
		pose proof (le_S_n _ _ l).
		pose proof (lt_S_n _ _ H0).
		clear l H0.
		rewrite <- minus_Sn_m with (1 := H1).
		simpl.
		rewrite fSubstDiv with (1 := conj (le_O_n _) (le_S _ _ H1)).
		intros.
		assert (nth (a - length GR) GL Uv =
		nth a (tcSubst GR b ++ GL) Uv).
			rewrite app_nth2;rewrite tcSubst_length;[| exact H1].
			reflexivity.
		apply spGoodCons.
			rewrite app_length.
			rewrite tcSubst_length.
			exact H2.
		rewrite <- H0.
		exact IH.
Qed.

Lemma tfGoodSubst GL GR F b : (b < length GL)->TreeFamGoodPG (GR ++ fBump (S b) O (nth b GL Uv) :: GL) F->
TreeFamGoodPG (tcSubst GR b ++ GL) (fSubst F (length GR) b).
	intros.
	apply tfGoodSubstNest with (1 := H).
	revert H0.
	apply tfGoodMap.
	clear GR F.
	intros.
	apply spGoodSubst with (1 := H).
	rewrite <- H1.
	exact H0.
Qed.

Lemma tfGoodSubst_O G F b : (b < length G)->TreeFamGoodPG (fBump (S b) O (nth b G Uv) :: G) F->
TreeFamGoodPG G (fSubst F O b).
	apply (tfGoodSubst G nil).
Qed.

(* Conversion from two-context to one-context language *)

Definition spTree l (p:_ * _) := let (f,la) := p in El (l + f,la).

Fixpoint sfTree l (F:simpFam) := match F with
	nil => Uv |
	p :: F => Pi (spTree l p) (sfTree (S l) F)
end.

Definition sfcTree := map (sfTree O).

Fixpoint spcTree G := match G with
	nil => nil |
	p :: G => spTree (length G) p :: spcTree G
end.

Lemma spcTree_length G : length (spcTree G) = length G.
	induction G;simpl.

	reflexivity.

	rewrite IHG.
	reflexivity.
Qed.

Lemma spcTree_nth a : forall G,(a < length G)->
(nth a (spcTree G) Uv = spTree (length G - S a) (nth a G (O,nil))).
	induction a;intro;(destruct G;intro;[destruct lt_n_O with (1 := H) |]);simpl.

	rewrite <- minus_n_O.
	reflexivity.

	exact (IHa _ (lt_S_n _ _ H)).
Qed.

Lemma spTree_BumpG n l1 l2 p : (l1 <= l2)->(spTree (l2 + n) (pBumpG n l1 p) = fBump n l1 (spTree l2 p)).
	intro.
	destruct p as (f,la).
	simpl.
	rewrite varBumpHi;[| apply le_not_lt;apply le_trans with (1 := H);apply le_plus_l].
	rewrite plus_assoc.
	rewrite <- (plus_comm l2).
	reflexivity.
Qed.

Lemma sfTree_BumpG n F : forall l1 l2,(l1 <= l2)->(sfTree (l2 + n) (fBumpG n l1 F) = fBump n l1 (sfTree l2 F)).
	induction F;intros;simpl.

	reflexivity.

	rewrite spTree_BumpG with (1 := H).
	change (S (l2 + n)) with (S l2 + n).
	rewrite (IHF _ _ (le_n_S _ _ H)).
	reflexivity.
Qed.

Lemma sfTree_BumpDG a b F : forall l,(fBumpG 1 l F = F)->
(sfTree (l + a) (fBumpD b F) = fBump (a + b) l (sfTree l F)).
	induction F as [| p].

	simpl.
	intros.
	reflexivity.

	intro.
	destruct p as (f,la).
	simpl.
	intro.
	replace (varBump (a + b) l (l + f)) with (l + a + (b + f));
	[|
		rewrite plus_assoc;
		rewrite <- (plus_assoc l);
		rewrite <- (plus_comm (a + b));
		rewrite <- plus_assoc;
		unfold varBump;
		(destruct (nat_compare_spec (l + f) l);try reflexivity);
		destruct (lt_n_O f);
		apply plus_lt_reg_l with l;
		rewrite <- plus_n_O;
		exact H0
	].
	replace (laBump (a + b) l la) with la;
	[|
		symmetry;
		apply laFreeBump;
		change la at 2 with (snd (hd (O,nil) ((f,la) :: F)));
		rewrite <- H;
		simpl;
		reflexivity
	].
	rewrite <- IHF.
		reflexivity.
	change F at 2 with (tl ((f,la) :: F)).
	rewrite <- H.
	simpl.
	reflexivity.
Qed.

Lemma spTree_SubstG p l1 l2 b : (l1 <= l2)->(spTree l2 (pSubstG p l1 b) = fSubst (spTree (S l2) p) l1 b).
	intro.
	destruct p as (f,la).
	simpl.
	rewrite varSubstGt.
		simpl.
		reflexivity.
	apply le_n_S.
	apply le_trans with (1 := H).
	apply le_plus_l.
Qed.

Lemma sfTree_SubstG F b : forall l1 l2,(l1 <= l2)->(sfTree l2 (fSubstG F l1 b) = fSubst (sfTree (S l2) F) l1 b).
	induction F;intros;simpl.

	reflexivity.

	rewrite <- spTree_SubstG with (1 := H).
	rewrite <- (IHF _ _ (le_n_S _ _ H)).
	reflexivity.
Qed.

Lemma spOKGood D G F la T : let G' := spcTree G ++ sfcTree D in
	TreeFamGoodPG G' (sfTree (length G) F)->
	SimpParamOK G F la T->
SimpParamGood G' (sfTree (length G) F) la (sfTree (length G) T).
	simpl.
	intros.
	induction H0.

	apply spGoodNil.

	simpl in IHSimpParamOK.
	rewrite sfTree_SubstG with (1 := le_O_n _).
	assert (spTree (length G) (pBumpG (S a) O (nth a G (O,nil))) =
	fBump (S a) O (nth a (spcTree G ++ sfcTree D) Uv)).
		rewrite app_nth1;[| rewrite spcTree_length;exact l].
		rewrite spcTree_nth with (1 := l).
		rewrite <- spTree_BumpG with (1 := le_O_n _).
		rewrite <- plus_comm.
		rewrite <- le_plus_minus with (1 := l).
		reflexivity.
	assert (a < length (spcTree G ++ sfcTree D)).
		rewrite app_length.
		rewrite spcTree_length.
		apply le_trans with (1 := l).
		apply le_plus_l.
	apply spGoodCons with (1 := H2).
	rewrite <- H1.
	exact IHSimpParamOK.
Qed.

Lemma sfOKGood D G T : SimpFCtxOK D->SimpFamOK D G T->let G' := spcTree G ++ sfcTree D in TreeCtxGood G'->
TreeFamGoodPG G' (sfTree (length G) T).
	intros HD ?.
	simpl.
	induction H;intro.

	simpl.
	apply tfGoodUv.

	simpl in IHSimpFamOK |- *.
	assert (TreeFamGoodPG (spcTree G ++ sfcTree D) (El (length G + f,la))).
		assert (length G + f < length (spcTree G ++ sfcTree D)).
			rewrite app_length.
			rewrite spcTree_length.
			apply plus_lt_compat_l.
			unfold sfcTree.
			rewrite map_length.
			exact l.
		apply tfGoodEl with (1 := H1).
		assert (sfTree (length G) (fBumpD (S f) (nth f D nil)) =
		fBump (S (length G + f)) O (nth (length G + f) (spcTree G ++ sfcTree D) Uv)).
			rewrite plus_n_Sm.
			rewrite app_nth2;rewrite spcTree_length;[| apply le_plus_l].
			rewrite minus_plus.
			unfold sfcTree.
			change Uv with (sfTree O nil).
			rewrite map_nth.
			apply sfTree_BumpDG with (l := O).
			pose proof (fctxProjOK _ _ HD l).
			apply sfOKFree with (1 := H2).
		refine (let H := spOKGood D _ _ _ _ _ s in _).
			rewrite H2.
			apply tfGoodBump_unskip with (1 := H1).
			apply ctxProjGood with (1 := H0).
		simpl in H3.
		rewrite <- H2.
		exact H3.
	refine (let H := IHSimpFamOK _ in _).
		apply tcGoodCons with (1 := H1) (2 := H0).
	apply tfGoodPi with (1 := H1) (2 := H2).
Qed.
