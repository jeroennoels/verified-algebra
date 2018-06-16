||| This example is inspired by exact real arithmetic.
||| See README for a brief introduction.
module Applications.ExactReal.Explore

import Data.Vect
import Common.Util
import Common.Interfaces
import Specifications.DiscreteOrderedGroup
import Specifications.OrderedRing
import Proofs.GroupTheory
import Applications.ExactReal.Carry
import public Applications.ExactReal.Digit

%default total
%access public export

||| semantics: explicit recursion
phi : (AdditiveGroup s, Multiplicative s) => s -> Vect n s -> s -> s
phi radix (x::xs) acc = phi radix xs (acc * radix + x)
phi radix [] acc = acc

||| this could be extended to become an induction hypothesis
absorb : (AdditiveGroup s, Unital s, Decidable [s,s] leq) =>
  Vect n (CarryResult (+) Zero Ng leq One u) ->
  (Carry, Vect n s)
absorb (x :: xs) = 
    let (c, ys) = absorb xs
        y = output x + scale Zero Ng One c
    in (carry x, y :: ys)
absorb [] = (O, [])
