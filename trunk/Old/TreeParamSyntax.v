(* Tree syntax for types and terms, to do typing in one context *)

Inductive treeFam : Set :=
	Uv |
	El (p:treeParam) |
	Pi (A B:treeFam)
with treeParam : Set :=
	var (i:nat) |
	apl (f:treeParam) (a:nat) (B:treeFam).

Fixpoint fBump n l F := match F with
	Uv => Uv |
	El p => El (pBump n l p) |
	Pi A B => Pi (fBump n l A) (fBump n (S l) B)
end
with pBump n l p := match p with
	var i => var (varBump n l i) |
	apl f a B => apl (pBump n l f) (varBump n l a) (fBump n (S l) B)
end.

Fixpoint fSubst l b F := match F with
	Uv => Uv |
	El p => El (pSubst l b p) |
	Pi A B => Pi (fSubst l b A) (fSubst (S l) b B)
end
with pSubst l b p := match p with
	var i => var (varSubst l b i) |
	apl f a B => apl (pSubst l b f) (varSubst l b a) (fSubst (S l) b B)
end.

Fixpoint tcBump n G := match G with
	nil => nil |
	F :: G => fBump n (length G) F :: tcBump n G
end.

Fixpoint tcSubst b G := match G with
	nil => nil |
	F :: G => fSubst (length G) b F :: tcSubst b G
end.

(* One-context, no-inversion typing rules. TreeParamGood is a "nested" inductive family. *)

Inductive TreeFamGood PG G : treeFam->Type :=
	tfGoodUv : TreeFamGood PG G Uv |
	tfGoodEl p : PG G p Uv->TreeFamGood PG G (El p) |
	tfGoodPi A B : TreeFamGood PG G A->TreeFamGood PG (A :: G) B->
		TreeFamGood PG G (Pi A B).

Unset Elimination Schemes.
Inductive TreeParamGood G : treeParam->treeFam->Set :=
	tpGoodVar i : (i < length G)->TreeParamGood G (var i) (fBump (S i) O (nth i G Uv)) |
	tpGoodApl f a B : (a < length G)->
		TreeParamGood G f (Pi (fBump (S a) O (nth a G Uv)) B)->
		TreeFamGood TreeParamGood (fBump (S a) O (nth a G Uv) :: G) B->
		TreeParamGood G (apl f a B) (fSubst O a B).
Set Elimination Schemes.
