module Proofs.TranslationInvarianceTheory

import Specifications.Group
import Specifications.Order
import Specifications.TranslationInvariance

import Proofs.GroupTheory
import Proofs.GroupCancelationLemmas

%default total
%access export

infixl 8 #

composeOrder : {(#) : Binop s} -> {(<=) : Rel s} ->
  PartiallyOrderedMagmaSpec (#) (<=) -> (a,b,c,d : s) ->
    a <= b -> c <= d -> a # c <= b # d
composeOrder spec a b c d ab cd =
  let pp = translationInvariantR spec a b c ab
      qq = translationInvariantL spec c d b cd
  in transitive (order spec) (a # c) (b # c) (b # d) pp qq


orderInverseR : {(#) : Binop s} -> {(<=) : Rel s} ->
  PartiallyOrderedGroupSpec (#) e inv (<=) -> (a,b,c : s) ->
    a # c <= b -> a <= b # inv c
orderInverseR spec a b c given = rewrite sym o2 in o1 where
  o1 : a # c # inv c <= b # inv c
  o1 = translationInvariantR (invariantOrder spec) (a # c) b _ given
  o2 : a # c # inv c = a
  o2 = groupCancel3bis (group spec) a c


inverseReversesOrder : {(#) : Binop s} ->
  PartiallyOrderedGroupSpec (#) _ inv leq -> (a,b : s) ->
    leq a b -> inv b `leq` inv a
inverseReversesOrder spec a b given = rewriteRelation leq o3 o4 o2 where
  o1 : inv a # a `leq` inv a # b
  o1 = translationInvariantL (invariantOrder spec) _ _ (inv a) given
  o2 : inv a # a # inv b `leq` inv a # b # inv b
  o2 = translationInvariantR (invariantOrder spec) (inv a # a) (inv a # b) _ o1
  o3 : inv a # a # inv b = inv b
  o3 = groupCancel1 (group spec) a _
  o4 : inv a # b # inv b = inv a
  o4 = groupCancel3bis (group spec) _ b


groupInverseAndOrder : {(#) : Binop s} ->
  PartiallyOrderedGroupSpec (#) e inv leq -> (a,b : s) ->
    a `leq` b -> a # inv b `leq` e
groupInverseAndOrder spec a b given = rewrite sym o2 in o1 where
  o1 : a # inv b `leq` b # inv b
  o1 = translationInvariantR (invariantOrder spec) a b _ given
  o2 : b # inv b = e
  o2 = inverseR (group spec) b
