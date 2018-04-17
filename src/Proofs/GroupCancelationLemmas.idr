module Proofs.GroupCancelationLemmas

import Specifications.Group

%default total
%access export

infixl 8 #

groupCancel1 : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  (inv a # a) # b = b
groupCancel1 spec a b = o2 `trans` o3 where
  o1 : inv a # a = e
  o1 = inverseL spec a
  o2 : (inv a # a) # b = e # b
  o2 = cong {f = (# b)} o1
  o3 : e # b = b
  o3 = neutralL (monoid spec) b


groupCancel1Bis : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  inv a # (a # b) = b
groupCancel1Bis spec a b = assoc `trans` groupCancel1 spec a b where
  assoc : inv a # (a # b) = (inv a # a) # b
  assoc = associative (monoid spec) _ a b


groupCancel2 : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  a # (inv b # b) = a
groupCancel2 spec a b = o2 `trans` o3 where
  o1 : inv b # b = e
  o1 = inverseL spec b
  o2 : a # (inv b # b) = a # e
  o2 = cong o1
  o3 : a # e = a
  o3 = neutralR (monoid spec) a


groupCancel2Bis : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  (a # inv b) # b = a
groupCancel2Bis spec a b = sym assoc `trans` groupCancel2 spec a b where
  assoc : a # (inv b # b) = (a # inv b) # b
  assoc = associative (monoid spec) a _ b


groupCancel3 : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  a # (b # inv b) = a
groupCancel3 spec a b = o2 `trans` o3 where
  o1 : b # inv b = e
  o1 = inverseR spec b
  o2 : a # (b # inv b) = a # e
  o2 = cong o1
  o3 : a # e = a
  o3 = neutralR (monoid spec) a


groupCancel3Bis : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  (a # b) # inv b = a
groupCancel3Bis spec a b = sym assoc `trans` groupCancel3 spec a b where
  assoc : a # (b # inv b) = (a # b) # inv b
  assoc = associative (monoid spec) a b _
