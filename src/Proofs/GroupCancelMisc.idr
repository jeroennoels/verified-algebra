module Proofs.GroupCancelMisc

import public Abbrev
import Specifications.Group
import Symmetry.Opposite
import Proofs.GroupCancelationLemmas
import Proofs.GroupTheory

%default total
%access export

infixl 8 #

groupCancelMisc1 : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b,c : s) ->
  a # (b # inv c) # c = a # b
groupCancelMisc1 spec a b c = o1 @== cong o2 where
  o1 : a # ((b # inv c) # c) = a # (b # inv c) # c
  o1 = associative (monoid spec) a _ c
  o2 : (b # inv c) # c = b
  o2 = groupCancel2bis spec b c


groupCancelMisc2 : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b,c : s) ->
  a # b # inv (c # b) = a # inv c
groupCancelMisc2 spec a b c = o4 @== cong o3 where
  o1 : b # inv (c # b) = b # (inv b # inv c)
  o1 = cong (groupInverseAnti spec c b)
  o2 : b # (inv b # inv c) = inv c
  o2 = groupCancel2bis (opposite spec) _ b
  o3 : b # inv (c # b) = inv c
  o3 = o1 === o2
  o4 : a # (b # inv (c # b)) = a # b # inv (c # b)
  o4 = associative (monoid spec) a b _

