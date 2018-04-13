module Monoid

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


groupOpInvOp : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) -> 
  a # (inv b # b) = a
groupOpInvOp spec a b = o3 where
  o1 : inv b # b = e
  o1 = inverseL spec b
  o2 : a # (inv b # b) = a # e
  o2 = cong o1
  o3 : a # (inv b # b) = a
  o3 = o2 `trans` neutralR (monoid spec) a
