module Proofs.TranslationInvarianceTheory

import Specifications.Group
import Specifications.TranslationInvariance
import Proofs.GroupTheory
import Proofs.GroupCancelationLemmas

%default total
%access export

infixl 8 #

orderInverseR : {(#) : Binop s} -> {(<=) : Rel s} ->
  PartiallyOrderedGroupSpec (#) e inv (<=) ->
    (a,b,c : s) -> a # c <= b -> a <= b # inv c
orderInverseR spec a b c given = rewrite sym o2 in o1 where
  o1 : a # c # inv c <= b # inv c
  o1 = translationInvariantR spec (a # c) b _ given
  o2 : a # c # inv c = a
  o2 = groupCancel3Bis (group spec) a c
