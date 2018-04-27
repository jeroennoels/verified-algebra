module Proofs.DiscreteOrderTheory 

import Specifications.Group
import Specifications.Order
import Specifications.TranslationInvariance

import Proofs.GroupTheory
import Proofs.GroupCancelationLemmas

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

  
strictOrderSeparates : {(+) : Binop s} -> {(<=) : Rel s} ->
  DiscreteOrderedGroupSpec (+) zero neg (<=) unit -> (a,b : s) ->
    Not (a = b) -> a <= b -> unit + a <= b
strictOrderSeparates spec a b diff given = o9 where
  o1 : a + neg b <= b + neg b
  o1 = translationInvariantR (invariantOrder (orderedGroup spec)) a b _ given
  o2 : b + neg b = zero
  o2 = inverseR (group (orderedGroup spec)) b
  o3 : a + neg b <= zero
  o3 = rewrite sym o2 in o1
  o4 : a + neg b = zero -> a = b
  o4 = groupInverseAndEquality (group (orderedGroup spec)) a b
  o5 : unit + (a + neg b) <= zero 
  o5 = discreteOrder spec (a + neg b) (contraposition o4 diff) o3
  o6 : unit + (a + neg b) + b <= zero + b
  o6 = translationInvariantR (invariantOrder (orderedGroup spec)) 
         (unit + (a + neg b)) zero b o5
  o7 : unit + (a + neg b) + b = unit + a 
  o7 = lemmaCancel (group (orderedGroup spec)) _ a b
  o8 : zero + b = b
  o8 = neutralL (monoid (group (orderedGroup spec))) b
  o9 : unit + a <= b
  o9 = rewriteRelation (<=) o7 o8 o6
