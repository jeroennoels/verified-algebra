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


translateIntervalR : {(#) : Binop s} ->
  PartiallyOrderedMagmaSpec (#) leq -> (c : s) ->
    Between leq x (a,b) -> Between leq (x # c) (a # c, b # c)
translateIntervalR spec c (MkBetween ax xb) = MkBetween 
  (translationInvariantR spec _ _ _ ax)
  (translationInvariantR spec _ _ _ xb)

