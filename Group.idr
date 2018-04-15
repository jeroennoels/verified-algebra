module Group

import public Abbrev
import Semigroup
import Monoid

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
