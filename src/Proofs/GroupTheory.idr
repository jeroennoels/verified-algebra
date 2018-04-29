module Proofs.GroupTheory

import Specifications.Group
import Proofs.GroupCancelationLemmas

%default total
%access export

infixl 8 #

groupInverseUnique : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  a # b = e -> inv a = b
groupInverseUnique {e} spec a b given = o4 @== o3 where
  o1 : inv a # (a # b) = inv a # e
  o1 = cong given
  o2 : inv a # (a # b) = b
  o2 = groupCancel1bis spec a b
  o3 : inv a # e = b
  o3 = o1 @== o2
  o4 : inv a # e = inv a
  o4 = neutralR (monoid spec) _


groupInverseInvolution : GroupSpec _ _ inv -> (a : s) ->
  inv (inv a) = a
groupInverseInvolution spec a =
  groupInverseUnique spec _ a $
  inverseL spec a


groupInverseMutual : GroupSpec _ _ inv -> (a,b : s) ->
  inv a = b -> inv b = a
groupInverseMutual spec a b given =
  cong given @== groupInverseInvolution spec a


groupInverseUniqueBis : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  a # b = e -> inv b = a
groupInverseUniqueBis spec a b given =
  groupInverseMutual spec a b $
  groupInverseUnique spec a b given


groupInverseNeutral : GroupSpec _ e inv -> inv e = e
groupInverseNeutral {e} spec =
  groupInverseUnique spec e e $
  neutralL (monoid spec) e


groupInverseAnti : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  inv (a # b) = inv b # inv a
groupInverseAnti spec a b = groupInverseUniqueBis spec _ _ o3 where
  o1 : inv b # inv a # a = inv b
  o1 = groupCancel2bis spec _ a
  o2 : inv b # inv a # a # b = inv b # b
  o2 = cong {f = (# b)} o1
  o3 : inv b # inv a # (a # b) = e
  o3 = associative (monoid spec) _ a b === o2 === inverseL spec b


groupInverseAndEquality : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  a # inv b = e -> a = b
groupInverseAndEquality {e} spec a b given = o2 @== o1 where
  o1 : a # inv b # b = b
  o1 = cong {f = (# b)} given === neutralL (monoid spec) b
  o2 : a # inv b # b = a
  o2 = groupCancel2bis spec a b
