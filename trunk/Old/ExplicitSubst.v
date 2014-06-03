Require Import List.
Require Import SimpSyntax.
Require Import Le Lt.

Inductive simpTm : Set :=
	var (i:nat) |
	app (f a:simpTm) |

	bump (n l:nat) (t:simpTm) |
	subst (b:simpTm) (l:nat) (a:simpTm).

Inductive simpTp : Set :=
	Uv |
	El (T:simpTm) |
	Pi (A B:simpTp) |

	Bump (n l:nat) (T:simpTp) |
	Subst (B:simpTp) (l:nat) (a:simpTm).

Inductive simpTmCtx : Set :=
	hole |
	appL (f:simpTmCtx) (a:simpTm) |
	appR (f:simpTm) (a:simpTmCtx).

Inductive simpTmCtxTp : Set :=
	ElC (T:simpTmCtx) |
	PiLTm (A:simpTmCtxTp) (B:simpTp) |
	PiRTm (A:simpTp) (B:simpTmCtxTp).

Inductive simpTpCtxTp : Set :=
	Hole |
	PiLTp (A:simpTpCtxTp) (B:simpTp) |
	PiRTp (A:simpTp) (B:simpTpCtxTp).

Fixpoint fillTm c t := match c with
	hole => t |
	appL f a => app (fillTm f t) a |
	appR f a => app f (fillTm a t)
end.

Fixpoint fillTmTp C t := match C with
	ElC T => fillTm T t |
	PiLTm A B => Pi (fillTmTp A t) B |
	PiRTm A B => Pi A (fillTmTp B t)
end.

Fixpoint fillTpTp C T := match C with
	Hole => T |
	PiLTp A B => Pi (fillTpTp A T) B |
	PiRTp A B => Pi A (fillTpTp B T)
end.

Inductive IsTp G : simpTp->Set :=
	UvTp : IsTp G Uv |
	ElTp T : HasTp G T Uv->IsTp G (El T) |
	PiTp A B : IsTp G A->IsTp (A :: G) B->IsTp G (Pi A B) |

	BumpTp n l T : (l + n <= length G)->
		IsTp (bumpCtx n (firstn l G) ++ skipn (l + n) G) T->
		IsTp G (Bump n l T) |
	SubstTp A B l a : (l <= length G)->HasTp (skipn l G) a A->
		IsTp (substCtx (firstn l G) a ++ A :: skipn l G) B->
		IsTp G (Subst B l a)
with HasTp G : simpTm->simpTp->Set :=
	varTp i : (i < length G)->HasTp G (var i) (Bump (S i) (nth i G Uv)) |
	appTp A B f a : HasTp G f (Pi A B)->HasTp G a A->IsTp (A :: G) B->HasTp G (app f a) (Subst B a) |

	bumpTp n l t T : (l + n <= length G)->
		HasTp (bumpCtx n (firstn l G) ++ skipn (l + n) G) t T->
		HasTp (skipn n G) t T->
		HasTp G (bump n l t) (Bump n l T) |
	substTp A B b l a : (l <= length G)->HasTp (skipn l G) a A->
		HasTp (substCtx (firstn l G) a ++ A :: skipn l G) b B->
		HasTp G (subst b l a) (Subst B l a) |

	bumpUv : HasTp G t (fillTpTp C (Bump n l Uv))->HasTp G t (fillTpTp C Uv) |

Inductive CtxOK : list pterm->Set :=
	ctxOKNil : CtxOK nil |
	ctxOKCons G T : CtxOK G->IsTp G T->CtxOK (T :: G).

Definition ctxProjOK i : forall G,CtxOK G->(i < length G)->IsTp (skipn (S i) G) (nth i G Uv).
	induction i;intros ? HG;(destruct HG;intro;[simpl;apply UvTp |]).

	exact i.

	change (IsTp (skipn (S i) G) (nth i G Uv)).
	apply (IHi _ HG).
	apply lt_S_n with (1 := H).
Defined.
Implicit Arguments ctxProjOK [i G].

Definition hasTpOK G t T : CtxOK G->HasTp G t T->IsTp G T.
	intros.
	destruct H0.

	apply bumpTp.
	exact (ctxProjOK H l).

	apply substTp with (1 := H0_0) (2 := i).
Defined.
Implicit Arguments hasTpOK [G t T].

Fixpoint spAnnot f la := match la with
	nil => f |
	a :: la => app (spAnnot f la) (var a)
end.

Fixpoint sfAnnot l (F:simpFam) := match F with
	nil => Uv |
	(f,la) :: F => Pi (El (spAnnot (var (l + f)) la)) (sfAnnot (S l) F)
end.

Fixpoint spcAnnot G := match G with
	nil => nil |
	(f,la) :: G => El (spAnnot (var (length G + f)) la) :: spcAnnot G
end.

Fixpoint sfcAnnot D := match D with
	nil => nil |
	F :: D => sfAnnot O F :: sfcAnnot D
end.

Lemma spAnnotOK D G f F la T : SimpParamOK G F la T->HasTp (spcAnnot G ++ D) f (sfAnnot (length G) F)->
HasTp (spcAnnot G ++ D) (spAnnot f la) (sfAnnot (length G) T).
Admitted.

(* This isn't gonna work. Need too many coercion rules. *)
Lemma sfAnnotOK D G T : SimpFamOK D G T->IsTp (spcAnnot G ++ sfcAnnot D) (sfAnnot (length G) T).
intro.
induction H.

simpl.
apply UvTp.

simpl in IHSimpFamOK |- *.
apply PiTp with (2 := IHSimpFamOK).
apply ElTp.
apply spAnnotOK with (1 := s).
Qed.
