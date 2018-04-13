module Monoid

import public Abbrev
import Semigroup

%default total
%access export

infixl 8 #

public export
isNeutralL : Binop s -> s -> Type
isNeutralL (#) e = (x : _) -> e # x = x

public export
isNeutralR : Binop s -> s -> Type
isNeutralR (#) e = (x : _) -> x # e = x

data MonoidSpec : Binop s -> s -> Type where
  MkMonoid : SemigroupSpec op -> isNeutralL op e -> isNeutralR op e ->
    MonoidSpec op e

semigroup : MonoidSpec op e -> SemigroupSpec op
semigroup (MkMonoid g _ _) = g

neutralL : MonoidSpec op e -> isNeutralL op e
neutralL (MkMonoid _ l _) = l

neutralR : MonoidSpec op e -> isNeutralR op e
neutralR (MkMonoid _ _ r) = r
