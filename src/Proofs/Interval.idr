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


public export
pivot : DiscreteOrderedGroupSpec add zero neg leq unit ->
  decisionProcedure leq -> (p,x : s) ->
    Between leq x (a,b) ->
    EitherErased (Between leq x (a,p))
                 (Between leq x (add unit p, b))
pivot spec decide p x (MkBetween ax xb) =
  case separate spec decide x p of
    EraseL xp => EraseL (MkBetween ax xp)
    EraseR px => EraseR (MkBetween px xb)


public export
pivotBis : DiscreteOrderedGroupSpec add zero neg leq unit ->
  decisionProcedure leq -> (p,x : s) ->
    Between leq x (a,b) ->
    EitherErased (Between leq x (a, add (neg unit) p))
                 (Between leq x (p, b))
pivotBis spec decide p x (MkBetween ax xb) =
  case separateBis spec decide x p of
    EraseL xp => EraseL (MkBetween ax xp)
    EraseR px => EraseR (MkBetween px xb)


decideBetween : decisionProcedure leq -> (x,a,b : s) ->  
  Dec (Between leq x (a,b))
decideBetween decide x a b = case (decide a x, decide x b) of
  (Yes ax, Yes xb) => Yes (MkBetween ax xb)
  (No contra, _) => No (contra . left)
  (_, No contra) => No (contra . right)
  
