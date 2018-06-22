module Proofs.RingTheory

import Specifications.Ring
import Proofs.GroupCancelationLemmas
import Proofs.GroupTheory
import Symmetry.Opposite

%default total
%access export

zeroAbsorbsL : {(+) : Binop s} -> {(*) : Binop s} ->
  RingSpec (+) zero neg (*) -> (x : s) -> zero * x = zero
zeroAbsorbsL {zero} spec x = o4 where
  o1 : zero + zero = zero
  o1 = neutralL (monoid (group spec)) zero
  o2 : (zero + zero) * x = zero * x + zero * x
  o2 = distributativeR spec zero zero x
  o3 : zero * x = zero * x + zero * x
  o3 = cong {f = (* x)} o1 @== o2
  o4 : zero * x = zero
  o4 = groupCancelGivesNeutral (group spec) _ _ (sym o3)

zeroAbsorbsR : {(*) : Binop s} ->
  RingSpec _ zero _ (*) -> (x : s) -> x * zero = zero
zeroAbsorbsR spec = zeroAbsorbsL (multiplicativeOpposite spec)

negatedMultiplication : {(+) : Binop s} -> {(*) : Binop s} ->
  RingSpec (+) zero neg (*) -> (x,y : s) ->
    neg (x * y) = x * neg y
negatedMultiplication spec x y = o4 where
  o1 : x * (y + neg y) = x * y + x * neg y
  o1 = distributativeL spec x y _
  o2 : x * (y + neg y) = x * zero
  o2 = cong $ inverseR (group spec) y
  o3 : x * y + x * neg y = zero
  o3 = o1 @== o2 === zeroAbsorbsR spec x
  o4 : neg (x * y) = x * neg y
  o4 = groupInverseUnique (group spec) (x * y) _ o3
