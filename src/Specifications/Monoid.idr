module Specifications.Monoid

import public Common.Abbrev
import public Specifications.Semigroup

%default total
%access public export

infixl 8 #

isNeutralL : Binop s -> s -> Type
isNeutralL (#) e = (x : _) -> e # x = x

isNeutralR : Binop s -> s -> Type
isNeutralR (#) e = (x : _) -> x # e = x

data MonoidSpec : Binop s -> s -> Type where
  MkMonoid : isAssociative op -> isNeutralL op e -> isNeutralR op e ->
    MonoidSpec op e

associative : MonoidSpec op _ -> isAssociative op
associative (MkMonoid g _ _) = g

neutralL : MonoidSpec op e -> isNeutralL op e
neutralL (MkMonoid _ l _) = l

neutralR : MonoidSpec op e -> isNeutralR op e
neutralR (MkMonoid _ _ r) = r
