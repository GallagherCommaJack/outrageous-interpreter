Inductive TreeFamGood G F : treeFam->Set :=
	tfGoodUv : TreeFamGood G F Uv |
	tfGoodEl f la : (f < length G)->
		SimpParamGood G (fBump (S f) O (nth f G Uv)) la Uv->
		TreeFamGood G F (El (f,la)) |
	tfGoodPi A B : TreeFamGood G F A->TreeFamGood (A :: G) F B->
		TreeFamGood G F (Pi A B)
with SimpParamGood G F : list nat->treeFam->Set :=
	spGoodNil : SimpParamGood G F nil F |
	spGoodCons a la B : (a < length G)->
		SimpParamGood G F la (Pi (fBump (S a) O (nth a G Uv)) B)->
		TreeFamGood (fBump (S a) O (nth a G Uv) :: G) F B->
		SimpParamGood G F (a :: la) (fSubst B O a).

Section TFSPGoodMutRec.

Variable PF : list treeFam->treeFam->Type.
Variable PP : list treeFam->treeFam->list nat->treeFam->Type.

Variable PUv : forall G,PF G Uv.
Variable PEl : forall G f la,(f < length G)->
	PP G (fBump (S f) O (nth f G Uv)) la Uv->
	PF G (El (f,la)).
Variable PPi : forall G A B,PF G A->PF (A :: G) B->
	PF G (Pi A B).

Variable PNil : forall G F,PP G F nil F.
Variable PCons : forall G F a la B,(a < length G)->
	PP G F la (Pi (fBump (S a) O (nth a G Uv)) B)->
	PF (fBump (S a) O (nth a G Uv) :: G) B->
	PP G F (a :: la) (fSubst B O a).

Fixpoint TreeFamGood_mr G F T (X:TreeFamGood G F T) : PF G T := match X with
	tfGoodUv => PUv _ |
	tfGoodEl _ _ Hf Hla => PEl _ _ _ Hf (SimpParamGood_mr _ _ _ _ Hla) |
	tfGoodPi _ _ HA HB => PPi _ _ _ (TreeFamGood_mr _ _ _ HA) (TreeFamGood_mr _ _ _ HB)
end
with SimpParamGood_mr G F la T (X:SimpParamGood G F la T) : PP G F la T := match X with
	spGoodNil => PNil _ _ |
	spGoodCons _ _ _ Ha Hla HB => PCons _ _ _ _ _ Ha
		(SimpParamGood_mr _ _ _ _ Hla) (TreeFamGood_mr _ _ _ HB)
end.

Definition TreeFamGood_SimpParamGood_mr := (TreeFamGood_mr,SimpParamGood_mr).

End TFSPGoodMutRec.
