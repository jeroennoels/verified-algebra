module Specifications.Group

import public Specifications.Monoid

%default total
%access public export

infixl 8 #

||| specification
isInverseL : Binop s -> s -> (s -> s) -> Type
isInverseL (#) e inv = (x : _) -> inv x # x = e

||| specification
isInverseR : Binop s -> s -> (s -> s) -> Type
isInverseR (#) e inv = (x : _) -> x # inv x = e

||| composed specification
data GroupSpec : Binop s -> s -> (s -> s) -> Type where
  MkGroup : MonoidSpec op e -> isInverseL op e inv -> isInverseR op e inv ->
    GroupSpec op e inv

||| forget
monoid : GroupSpec op e _ -> MonoidSpec op e
monoid (MkGroup m _ _) = m

||| forget
inverseL : GroupSpec op e inv -> isInverseL op e inv
inverseL (MkGroup _ l _) = l

||| forget
inverseR : GroupSpec op e inv -> isInverseR op e inv
inverseR (MkGroup _ _ r) = r

||| composed specification
data AbelianGroupSpec : Binop s -> s -> (s -> s) -> Type where
  MkAbelianGroup : GroupSpec op e inv -> isAbelian op ->
    AbelianGroupSpec op e inv

||| forget
group : AbelianGroupSpec op e inv -> GroupSpec op e inv
group (MkAbelianGroup g _) = g

||| forget
abelian : AbelianGroupSpec op _ _ -> isAbelian op
abelian (MkAbelianGroup _ a) = a
