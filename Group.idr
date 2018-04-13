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


groupInvOpOp : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  (inv a # a) # b = b
groupInvOpOp spec a b = o2 `trans` o3 where
  o1 : inv a # a = e
  o1 = inverseL spec a
  o2 : (inv a # a) # b = e # b
  o2 = cong {f = (# b)} o1
  o3 : e # b = b
  o3 = neutralL (monoid spec) b


groupInvOpOpBis : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  inv a # (a # b) = b
groupInvOpOpBis spec a b = assoc `trans` groupInvOpOp spec a b where
  assoc : inv a # (a # b) = (inv a # a) # b
  assoc = associative (semigroup (monoid spec)) _ a b


groupOpInvOp : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  a # (inv b # b) = a
groupOpInvOp spec a b = o2 `trans` o3 where
  o1 : inv b # b = e
  o1 = inverseL spec b
  o2 : a # (inv b # b) = a # e
  o2 = cong o1
  o3 : a # e = a
  o3 = neutralR (monoid spec) a


groupOpInvOpBis : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  (a # inv b) # b = a
groupOpInvOpBis spec a b = sym assoc `trans` groupOpInvOp spec a b where
  assoc : a # (inv b # b) = (a # inv b) # b
  assoc = associative (semigroup (monoid spec)) a _ b


uniqueInverse : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  a # b = e -> inv a = b
uniqueInverse {e} spec a b given = sym o4 `trans` o3 where
  o1 : inv a # (a # b) = inv a # e
  o1 = cong given
  o2 : inv a # (a # b) = b
  o2 = groupInvOpOpBis spec a b
  o3 : inv a # e = b
  o3 = sym o1 `trans` o2
  o4 : inv a # e = inv a
  o4 = neutralR (monoid spec) _
