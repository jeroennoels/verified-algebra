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

||| Recursively reduce the input digits and absorb the carries. 
total
reduce : (AdditiveGroup s, Multiplicative s, Unital s, Decidable [s,s] leq) =>
  DiscreteOrderedRingSpec (+) Zero Ng (*) leq One ->
  (u : s) ->
  (bound : leq One (u + Ng One)) ->
  (digits : Vect (S k) (Digit leq Ng (u + u))) ->
  Absorption k (Ranges leq Ng u (u + Ng One)) (phi (One + u))
      (map Digit.val digits)
-- Base case. Explicitly pass dictionaries to improve compilation time.
reduce @{ia} @{im} @{iu} @{id}
    spec u bound [MkDigit input inRange] =
  absorptionBase @{ia} @{im} @{iu} spec {u} (One + u)
      (computeCarry @{ia} @{iu} @{id}
        (discreteOrderedGroup spec) u bound input inRange)
-- Recursive case.
reduce @{ia} @{im} @{iu} @{id}
    spec u bound (MkDigit input inRange :: digits@(_::_)) =
  absorptionStep @{ia} @{im} @{iu} spec {u} (One + u)
    (computeCarry @{ia} @{iu} @{id}
       (discreteOrderedGroup spec) u bound input inRange)
    (reduce @{ia} @{im} @{iu} @{id} spec u bound digits)
