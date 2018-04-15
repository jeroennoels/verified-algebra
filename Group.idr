module Group

import public Abbrev
import public Monoid

%default total
%access export

infixl 8 #

public export
isInverseL : Binop s -> s -> (s -> s) -> Type
isInverseL (#) e inv = (x : _) -> inv x # x = e

public export
isInverseR : Binop s -> s -> (s -> s) -> Type
isInverseR (#) e inv = (x : _) -> x # inv x = e

data GroupSpec : Binop s -> s -> (s -> s) -> Type where
  MkGroup : MonoidSpec op e -> isInverseL op e inv -> isInverseR op e inv ->
    GroupSpec op e inv

monoid : GroupSpec op e inv -> MonoidSpec op e
monoid (MkGroup m _ _) = m

inverseL : GroupSpec op e inv -> isInverseL op e inv
inverseL (MkGroup _ l _) = l

inverseR : GroupSpec op e inv -> isInverseR op e inv
inverseR (MkGroup _ _ r) = r

public export
data AbelianGroupSpec : Binop s -> s -> (s -> s) -> Type where
  MkAbelianGroup : GroupSpec op e inv -> isAbelian op ->
    AbelianGroupSpec op e inv

group : AbelianGroupSpec op e inv -> GroupSpec op e inv
group (MkAbelianGroup g _) = g

abelian : AbelianGroupSpec op e inv -> isAbelian op
abelian (MkAbelianGroup _ a) = a
