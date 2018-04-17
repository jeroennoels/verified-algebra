module Specifications.Order

import public Abbrev

%default total
%access public export

isReflexive : Rel s -> Type
isReflexive rel = (x : _) -> rel x x

isTransitive : Rel s -> Type
isTransitive rel = (x,y,z : _) -> rel x y -> rel y z -> rel x z

isAntisymmetric : Rel s -> Type
isAntisymmetric rel = (x,y : _) -> rel x y -> rel y x -> x = y

data PartialOrderSpec : Rel s -> Type where
  MkPartialOrder : isReflexive rel -> isTransitive rel -> isAntisymmetric rel -> 
    PartialOrderSpec rel

reflexive : PartialOrderSpec rel -> isReflexive rel
reflexive (MkPartialOrder r _ _) = r

transitive : PartialOrderSpec rel -> isTransitive rel
transitive (MkPartialOrder _ t _) = t        

antisymmetric : PartialOrderSpec rel -> isAntisymmetric rel
antisymmetric (MkPartialOrder _ _ a) = a        
