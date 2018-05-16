module Proofs.TranslationInvarianceTheory

import Util
import Specifications.TranslationInvariance
import Proofs.GroupTheory
import Proofs.GroupCancelationLemmas
import Symmetry.Opposite

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


orderInverseL : {(#) : Binop s} -> {(<=) : Rel s} ->
  PartiallyOrderedGroupSpec (#) e inv (<=) -> (a,b,c : s) ->
    a # c <= b -> c <= inv a # b
orderInverseL spec a b c given = rewrite sym o2 in o1 where
  o1 : inv a # (a # c) <= inv a # b
  o1 = translationInvariantL (invariantOrder spec) (a # c) b _ given
  o2 : inv a # (a # c) = c
  o2 = groupCancel1bis (group spec) a c


orderInverseR : {(#) : Binop s} -> {(<=) : Rel s} ->
  PartiallyOrderedGroupSpec (#) e inv (<=) -> (a,b,c : s) ->
    a # c <= b -> a <= b # inv c
orderInverseR spec a b c = orderInverseL (opposite spec) c b a


inverseReversesOrder : {(#) : Binop s} ->
  PartiallyOrderedGroupSpec (#) _ inv leq ->
    leq a b -> inv b `leq` inv a
inverseReversesOrder spec {a} {b} given = rewriteRelation leq o3 o4 o2 where
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


invertNegative : {(<=) : Rel s} ->
  PartiallyOrderedGroupSpec _ zero neg (<=) -> (a : s) ->
    a <= zero -> zero <= neg a
invertNegative spec a negative = rewrite sym o2 in o1 where
  o1 : neg zero <= neg a
  o1 = inverseReversesOrder spec negative
  o2 : neg zero = zero
  o2 = groupInverseNeutral (group spec)


invertBetween : PartiallyOrderedGroupSpec op e inv rel ->
  Between rel x (a,b) -> Between rel (inv x) (inv b, inv a)
invertBetween spec (MkBetween ax xb) =
  MkBetween (inverseReversesOrder spec xb)
            (inverseReversesOrder spec ax)
