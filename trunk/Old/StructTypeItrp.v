Inductive SimpParamItrp D (G:DCtx D) (F:Typ D) : list nat->forall T:Typ G,(forall g,F (dctx_d G g)->T g)->Type :=
	spItrpNil : SimpParamItrp D G F nil (typMap (dctx_d G) F) (fun g f=>tr (fun X=>X g) (typMapEq _ F) f) |
	spItrpCons a la P (a':AtCtx G a P) B la' :
		SimpParamItrp D G F la (pi P B) la'->
		SimpParamItrp D G F (a :: la) (typMap (fun g=>existT _ g (ctxProj a' g)) B)
			(fun g f=>tr (fun X=>X g) (typMapEq _ B) (la' g f (ctxProj a' g))).
Implicit Arguments SimpParamItrp [D].

Inductive SimpFamItrp D (G:DCtx D) : simpFam->Typ G->Type :=
	sfItrpNil : SimpFamItrp D G nil (uv G) |
	sfItrpCons f la T (F:Typ D) (f':AtCtx D f F) la' T' :
		SimpParamItrp G F la (uv G) la'->
		SimpFamItrp D (extDCtx G (fun g=>la' g (ctxProj f' (dctx_d G g)))) T T'->
		SimpFamItrp D G ((f,la) :: T) (pi _ T').

Inductive SimpFCtxItrp : list simpFam->Ctx->Type :=
	sfcItrpNil : SimpFCtxItrp nil empCtx |
	sfcItrpCons F D D' F' :
		SimpFCtxItrp D D'->
		SimpFamItrp D' (empDCtx D') F F'->
		SimpFCtxItrp (F :: D) (extCtx D' F').

Inductive SimpPCtxItrp D : list (nat * list nat)->DCtx D->Type :=
	spcItrpNil : SimpPCtxItrp D nil (empDCtx D) |
	spcItrpCons f la G G' (F:Typ D) (f':AtCtx D f F) la' :
		SimpPCtxItrp D G G'->
		SimpParamItrp G' F la (uv G') la'->
		SimpPCtxItrp D ((f,la) :: G) (extDCtx G' (fun g=>la' g (ctxProj f' (dctx_d G' g)))).
