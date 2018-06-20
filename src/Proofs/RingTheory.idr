module Proofs.RingTheory

import Specifications.Ring
import Proofs.GroupCancelationLemmas

%default total
%access export

zeroAbsorbsL : {(+) : Binop s} -> {(*) : Binop s} ->
  RingSpec (+) zero neg (*) -> (x : s) ->
    zero * x = zero
zeroAbsorbsL {zero} spec x = o4 where
  o1 : zero + zero = zero
  o1 = neutralL (monoid (group (abelianGroup spec))) zero
  o2 : (zero + zero) * x = zero * x + zero * x
  o2 = distributativeR spec zero zero x
  o3 : zero * x = zero * x + zero * x
  o3 = cong {f = (* x)} o1 @== o2
  o4 : zero * x = zero
  o4 = groupCancelGivesNeutral (group (abelianGroup spec)) _ _ (sym o3)

zeroAbsorbsR : {(*) : Binop s} ->
  RingSpec _ zero _ (*) -> (x : s) -> 
    x * zero = zero
zeroAbsorbsR spec x = ?qed
