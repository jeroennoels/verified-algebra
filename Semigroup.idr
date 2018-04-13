module Semigroup

import public Abbrev

%default total
%access export

infixl 8 #

public export
isAssociative : Binop s -> Type
isAssociative (#) = (x,y,z : _) -> x # (y # z) = (x # y) # z

data SemigroupSpec : Binop s -> Type where
  MkSemigroup : isAssociative op -> SemigroupSpec op

associative : SemigroupSpec op -> isAssociative op
associative (MkSemigroup law) = law
