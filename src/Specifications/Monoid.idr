module Specifications.Monoid

import public Specifications.Semigroup

%default total
%access public export

infixl 8 #

||| specification 
isNeutralL : Binop s -> s -> Type
isNeutralL (#) e = (x : _) -> e # x = x

||| specification 
isNeutralR : Binop s -> s -> Type
isNeutralR (#) e = (x : _) -> x # e = x

||| composed specification
data MonoidSpec : Binop s -> s -> Type where
  MkMonoid : isAssociative op -> isNeutralL op e -> isNeutralR op e ->
    MonoidSpec op e

||| forget
associative : MonoidSpec op _ -> isAssociative op
associative (MkMonoid g _ _) = g

||| forget
neutralL : MonoidSpec op e -> isNeutralL op e
neutralL (MkMonoid _ l _) = l

||| forget
neutralR : MonoidSpec op e -> isNeutralR op e
neutralR (MkMonoid _ _ r) = r
