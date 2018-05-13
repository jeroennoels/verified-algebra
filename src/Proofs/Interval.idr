module Proofs.TranslationInvarianceTheory

import Util

import Specifications.Group
import Specifications.Order
import Specifications.TranslationInvariance
import Specifications.DiscreteOrderedGroup

import Proofs.GroupCancelationLemmas
import Proofs.GroupTheory
import Proofs.TranslationInvarianceTheory
import Proofs.DiscreteOrderTheory

%default total
%access export

infixl 8 #

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


decideBetween : decisionProcedure leq -> (x,a,b : s) ->
  Dec (Between leq x (a,b))
decideBetween decide x a b =
  decideBoth MkBetween betweenL betweenR (decide a x) (decide x b)


decidePivot : DiscreteOrderedGroupSpec add zero neg leq unit ->
  decisionProcedure leq -> (p,x : s) ->
    Between leq x (a,b) ->
    EitherErased (Between leq x (a,p))
                 (Between leq x (add unit p, b))
decidePivot spec decide p x (MkBetween ax xb) =
  case separate spec decide x p of
    Left xp => Left (MkBetween ax xp)
    Right px => Right (MkBetween px xb)


decidePivotBis : DiscreteOrderedGroupSpec add zero neg leq unit ->
  decisionProcedure leq -> (p,x : s) ->
    Between leq x (a,b) ->
    EitherErased (Between leq x (a, add (neg unit) p))
                 (Between leq x (p, b))
decidePivotBis spec decide p x (MkBetween ax xb) =
  case separateBis spec decide x p of
    Left xp => Left (MkBetween ax xp)
    Right px => Right (MkBetween px xb)


decidePartition3 : DiscreteOrderedGroupSpec add zero neg leq unit ->
  decisionProcedure leq -> (p,q,x : s) ->
    Between leq x (a,b) ->
    Either3Erased (Between leq x (a,p))
                  (Between leq x (add unit p, add (neg unit) q))
                  (Between leq x (q,b))
decidePartition3 spec decide p q x axb =
  case decidePivot spec decide p x axb of
    Left l => Left l
    Right pxb =>
      case decidePivotBis spec decide q x pxb of
        Left m => Middle m
        Right r => Right r
