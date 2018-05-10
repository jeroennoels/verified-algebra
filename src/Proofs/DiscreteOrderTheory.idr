module Proofs.DiscreteOrderTheory

import public Data.Erased
import Util

import Specifications.Group
import Specifications.Order
import Specifications.TranslationInvariance
import Specifications.OrderedGroup
import Specifications.DiscreteOrderedGroup

import Proofs.GroupTheory
import Proofs.GroupCancelationLemmas
import Proofs.OrderTheory
import Proofs.TranslationInvarianceTheory

%default total
%access export

infixl 8 #

private
lemmaCancel : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b,c : s) ->
  a # (b # inv c) # c = a # b
lemmaCancel spec a b c = o1 @== cong o2 where
  o1 : a # ((b # inv c) # c) = a # (b # inv c) # c
  o1 = associative (monoid spec) a _ c
  o2 : (b # inv c) # c = b
  o2 = groupCancel2bis spec b c


lemmaOrder : {(#) : Binop s} ->
  PartiallyOrderedGroupSpec (#) e inv leq -> (a,b,c : s) ->
    a # (b # inv c) `leq` e -> a # b `leq` c
lemmaOrder spec a b c given = rewriteRelation leq o2 o3 o1 where
  o1 : a # (b # inv c) # c `leq` e # c
  o1 = translationInvariantR (invariantOrder spec) (a # (b # inv c)) e c given
  o2 : a # (b # inv c) # c = a # b
  o2 = lemmaCancel (group spec) _ b c
  o3 : e # c = c
  o3 = neutralL (monoid (group spec)) c


strictOrderSeparates : {(+) : Binop s} -> {(<=) : Rel s} ->
  DiscreteOrderedGroupSpec (+) zero neg (<=) unit -> (a,b : s) ->
    Not (a = b) -> a <= b -> unit + a <= b
strictOrderSeparates spec a b diff given = o4 where
  o1 : a + neg b <= zero
  o1 = groupInverseAndOrder (partiallyOrderedGroup spec) a b given
  o2 : a + neg b = zero -> a = b
  o2 = groupInverseAndEquality (group spec) a b
  o3 : unit + (a + neg b) <= zero
  o3 = discreteOrder spec (a + neg b) (contraposition o2 diff) o1
  o4 : unit + a <= b
  o4 = lemmaOrder (partiallyOrderedGroup spec) unit a b o3


public export
separate : {(+) : Binop s} -> {(<=) : Rel s} ->
 .DiscreteOrderedGroupSpec (+) zero neg (<=) unit ->
  decisionProcedure (<=) -> (a,b : s) ->
    Either (Erased (a <= b)) (Erased (unit + b <= a))
separate spec decide a b = case decide a b of
  Yes prf => Left (Erase prf)
  No contra =>
    let (baLeq, abDiff) = orderContra (totalOrder spec) a b contra
        prf = strictOrderSeparates spec b a (abDiff . sym) baLeq
    in Right (Erase prf)


pivot : .DiscreteOrderedGroupSpec add zero neg leq unit ->
  decisionProcedure leq -> (p,x : s) -> 
    Between leq x (a,b) -> 
    Either (Between leq x (a,p)) 
           (Between leq x (add unit p, b))
pivot spec decide p x (MkBetween ax xb) = 
  case separate spec decide x p of
    Left (Erase xp) => Left (MkBetween ax xp)
    Right (Erase px)  => Right (MkBetween px xb)
