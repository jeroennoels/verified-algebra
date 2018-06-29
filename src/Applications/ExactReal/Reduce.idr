||| This example is inspired by exact real arithmetic.
||| See README for a brief introduction.
module Applications.ExactReal.Reduce

import Data.Vect
import Common.Util
import Common.Interfaces
import Specifications.OrderedRing
import Applications.ExactReal.Carry
import Applications.ExactReal.Absorb
import Applications.ExactReal.AbsorptionLemmas
import public Applications.ExactReal.Digit

%default total
%access export

total
reduce : (AdditiveGroup s, Multiplicative s, Unital s, Decidable [s,s] leq) =>
  DiscreteOrderedRingSpec (+) Zero Ng (*) leq One ->
  (u : s) ->
  (bound : leq One (u + Ng One)) ->
  (inputs : Vect (S k) (Digit leq Ng (u + u))) ->
  Absorption k (Ranges leq Ng u (u + Ng One)) (phi (One + u))
    (map Digit.val inputs)
reduce spec u bound [MkDigit input inRange] =
  absorptionBase spec {u} (One + u)
    (computeCarry (discreteOrderedGroup spec) u bound input inRange)
reduce spec u bound (MkDigit input inRange :: inputs@(_::_)) =
  absorptionStep spec {u} (One + u)
    (computeCarry (discreteOrderedGroup spec) u bound input inRange)
    (reduce spec u bound inputs)
