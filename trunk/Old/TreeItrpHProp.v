(* From TreeItrp.v
 *
 * An attempt to get spItrpUniq working without assuming UIP.
 * I couldn't get it to work.
 *)

Definition HProp T := forall x y:T,x = y.

Definition HPropUIP T (P:HProp T) x := eq_trans
	(match eq_sym (P x x) as p in _ = y return _ = eq_trans (P y x) p with eq_refl => eq_refl (P x x) end)
	(match P x x as p return eq_trans p (eq_sym p) = eq_refl x with eq_refl => eq_refl (eq_refl x) end).
Implicit Arguments HPropUIP [T].

Inductive ExSimpParamItrp G F la : Type :=
	exSimpParamItrp T' la' : SimpParamItrp G F la T' la'->ExSimpParamItrp G F la.
Implicit Arguments exSimpParamItrp [G F la].

(* You were about to prove some lemmas about the structure of ExSimpParamItrp paths. *)

Lemma spItrpProp G F la : forall Tla1 Tla2:ExSimpParamItrp G F la,Tla1 = Tla2.
	induction la;intros.

	destruct Tla1 as (T1,la1,s1).
	destruct Tla2 as (T2,la2,s2).
	destruct s1.
	destruct s2.
	reflexivity.

	destruct Tla1 as (T1,la1,s1).
	destruct Tla2 as (T2,la2,s2).
	simpl in s1,s2.
	destruct s1 as (P1,a1,B1,BS1,la1,s1).
	destruct s2 as (P2,a2,B2,BS2,la2,s2).
	simpl in la1,la2.
	revert B2 BS2 la2 s2.
	apply (tr (fun xa=>forall B2 (BS2:forall g p,TypS (B2 g p)) la2
		(s2:SimpParamItrp G F la (fun g=>typPi (xa_T xa g) (fun p=>typ (BS2 g p))) la2),
		_ = exSimpParamItrp (la := a :: la) (fun g=>typ (BS2 g (ctxProj (xa_a xa) g)))
			(fun g f=>la2 g f (ctxProj (xa_a xa) g)) (spItrpCons (xa_a xa) BS2 s2))
	(atCtxUniq a1 a2)).
	simpl.
	clear P2 a2.
	intros.
	assert (IHlaU := HPropUIP IHla).
=======
	pose (Fn (A:G->Typ) (B:forall g,A g->Typ) g := typPi (A g) (fun a=>B g a)).
	assert (IHP := fun A1 A2 B1 B2 la1 la2 s1 s2=>ap (fun s g=>typDom (projT1 s g)) (IHla (Fn A1 B1) (Fn A2 B2) la1 la2 s1 s2)).
	simpl in IHP.
	pose (AEta A (g:G) := typ (typSc (A g))).
	assert (IHPU : forall A B1 B2 la1 la2 s1 s2,IHP (AEta A) (AEta A) B1 B2 la1 la2 s1 s2 = eq_refl _).
		clear B1 BS1 la1 s B2 BS2 la2 X.
		pose (BlasT (A:G->Typ) := {B:_ & {la':_ & SimpParamItrp G F la (Fn A B) la'}}).
		pose (Blas A B la' s := existT (fun B=>{la':_ & SimpParamItrp G F la (Fn A B) la'}) B (existT (fun la'=>SimpParamItrp G F la (Fn A B) la') la' s)).
		change (forall A B la',SimpParamItrp G F la (Fn A B) la'->BlasT A) in (type of Blas).
		pose (IHP' A1 A2 (Blas1:BlasT A1) (Blas2:BlasT A2) :=
			let B1 := projT1 Blas1 in
			let las1 := projT2 Blas1 in
			let la1 := projT1 las1 in
			let s1 := projT2 las1 in

			let B2 := projT1 Blas2 in
			let las2 := projT2 Blas2 in
			let la2 := projT1 las2 in
			let s2 := projT2 las2 in

			IHP A1 A2 B1 B2 la1 la2 s1 s2).
		intros.
		pose (Blas1 := Blas A B1 la1 s1).
		pose (Blas2 := Blas A B2 la2 s2).
		change (IHP' (AEta A) (AEta A) Blas1 Blas2 = eq_refl (AEta A)).
		set (IHPAA := IHP' (AEta A) (AEta A) Blas1 Blas2).
		change (AEta A = AEta A) in (type of IHPAA).
		transitivity (eq_trans IHPAA (eq_sym IHPAA)).

		generalize (eq_sym IHPAA).
		intro p.
		subst IHPAA.
		revert B1 B2 la1 la2 s1 s2 Blas1 Blas2.
		refine (match p as p in _ = A' return forall B1 B2 la1 la2
			(s1:SimpParamItrp G F la (Fn A' B1) la1) (s2:SimpParamItrp G F la (Fn A B2) la2),
				let Blas1 := Blas A' B1 la1 s1 in let Blas2 := Blas A B2 la2 s2 in
			IHP' A' A' Blas1 (tr BlasT p Blas2) = eq_trans (IHP' A' (AEta A) Blas1 Blas2) p
		with eq_refl => _ end).

		refine (match IHPAA as p return eq_trans p (eq_sym p) = eq_refl (AEta A) with eq_refl => _ end).
		simpl.
		reflexivity.
Qed.
Implicit Arguments spItrpProp [G F la].
