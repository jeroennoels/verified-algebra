module Proofs.GroupTheory

import public Abbrev
import Semigroup
import Monoid
import Group

%default total
%access export

infixl 8 #

groupInverse1 : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  (inv a # a) # b = b
groupInverse1 spec a b = o2 `trans` o3 where
  o1 : inv a # a = e
  o1 = inverseL spec a
  o2 : (inv a # a) # b = e # b
  o2 = cong {f = (# b)} o1
  o3 : e # b = b
  o3 = neutralL (monoid spec) b


groupInverse1Bis : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  inv a # (a # b) = b
groupInverse1Bis spec a b = assoc `trans` groupInverse1 spec a b where
  assoc : inv a # (a # b) = (inv a # a) # b
  assoc = associative (semigroup (monoid spec)) _ a b


groupInverse2 : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  a # (inv b # b) = a
groupInverse2 spec a b = o2 `trans` o3 where
  o1 : inv b # b = e
  o1 = inverseL spec b
  o2 : a # (inv b # b) = a # e
  o2 = cong o1
  o3 : a # e = a
  o3 = neutralR (monoid spec) a


groupInverse2Bis : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  (a # inv b) # b = a
groupInverse2Bis spec a b = sym assoc `trans` groupInverse2 spec a b where
  assoc : a # (inv b # b) = (a # inv b) # b
  assoc = associative (semigroup (monoid spec)) a _ b


uniqueInverse : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  a # b = e -> inv a = b
uniqueInverse {e} spec a b given = sym o4 `trans` o3 where
  o1 : inv a # (a # b) = inv a # e
  o1 = cong given
  o2 : inv a # (a # b) = b
  o2 = groupInverse1Bis spec a b
  o3 : inv a # e = b
  o3 = sym o1 `trans` o2
  o4 : inv a # e = inv a
  o4 = neutralR (monoid spec) _
