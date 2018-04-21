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


translateIntervalR : {(#) : Binop s} ->
  PartiallyOrderedMagmaSpec (#) leq -> (c : s) ->
    Between leq x (a,b) -> Between leq (x # c) (a # c, b # c)
translateIntervalR spec c (MkBetween ax xb) = MkBetween
  (translationInvariantR spec _ _ _ ax)
  (translationInvariantR spec _ _ _ xb)


composeIntervals : {(#) : Binop s} ->
  PartiallyOrderedMagmaSpec (#) leq ->
    Between leq x (a,b) ->
    Between leq y (c,d) ->
    Between leq (x # y) (a # c, b # d)
composeIntervals spec (MkBetween ax xb) (MkBetween cy yd) = MkBetween
  (composeOrder spec _ _ _ _ ax cy)
  (composeOrder spec _ _ _ _ xb yd)


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


