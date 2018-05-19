module Proofs.DiscreteOrderTheory

import Util
import Data.Vect
import Data.Rel
import Decidable.Decidable
import Specifications.DiscreteOrderedGroup
import Proofs.GroupCancelationLemmas
import Proofs.GroupTheory
import Proofs.GroupCancelMisc
import Proofs.OrderTheory
import Proofs.TranslationInvarianceTheory

%default total
%access export

infixl 8 #

lemmaOrder : {(#) : Binop s} ->
  PartiallyOrderedGroupSpec (#) e inv leq -> (a,b,c : s) ->
    a # (b # inv c) `leq` e -> a # b `leq` c
lemmaOrder spec a b c given = rewriteRelation leq o2 o3 o1 where
  o1 : a # (b # inv c) # c `leq` e # c
  o1 = translationInvariantR (invariantOrder spec) (a # (b # inv c)) e c given
  o2 : a # (b # inv c) # c = a # b
  o2 = groupCancelMisc1 (group spec) _ b c
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
separate : Decidable [s,s] leq => {(+) : Binop s} ->
  DiscreteOrderedGroupSpec (+) zero neg leq unit ->
    (a,b : s) ->
    EitherErased (a `leq` b) (unit + b `leq` a)
separate {s} spec a b =
  case dec a b of
    Yes prf => Left prf
    No contra =>
      let (baLeq, diff) = orderContra (totalOrder spec) a b contra
          prf = strictOrderSeparates spec b a (diff . sym) baLeq
      in Right prf
  where
    dec : decisionProcedure leq
    dec = decide {ts = [s,s]}


public export
separateBis : Decidable [s,s] leq => {(+) : Binop s} ->
  DiscreteOrderedGroupSpec (+) zero neg leq unit ->
    (a,b : s) ->
    EitherErased (a `leq` neg unit + b) (b `leq` a)
separateBis spec a b =
  case separate spec b a of
    Left ba => Right ba
    Right ab => Left (orderInverseL (partiallyOrderedGroup spec) unit b a ab)
