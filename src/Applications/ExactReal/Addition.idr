||| This example is inspired by exact real arithmetic.
||| See README for a brief introduction.
module Applications.ExactReal.Addition

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

computeCarryForSum : (AdditiveGroup s, Unital s, Decidable [s,s] leq) =>
  DiscreteOrderedGroupSpec (+) Zero Ng leq One ->
  (u : s) -> leq One (u + Ng One) ->
  Digit leq Ng u ->
  Digit leq Ng u ->
  Reduction (+) Zero Ng leq One u (One + u)
computeCarryForSum spec u bound x y =
  let MkDigit z prf = addDigits (partiallyOrderedGroup spec) x y
  in computeCarry spec u bound z prf


carryToLeft : (AdditiveGroup s, Unital s, Decidable [s,s] leq) =>
  Reduction (+) Zero Ng leq One u _ ->
  Reduction (+) Zero Ng leq One u _ ->
  Digit leq Ng u
carryToLeft curr next =
  MkDigit (output curr + scale Zero Ng One (carry next)) ?prf

carryAll : (AdditiveGroup s, Unital s, Decidable [s,s] leq) =>
  Vect n (Reduction (+) Zero Ng leq One u (One + u)) ->
  Vect n (Digit leq Ng u)
carryAll (x::y::ys) = carryToLeft x y :: carryAll (y::ys)
carryAll [x] = [MkDigit (output x) ?prf]
carryAll [] = []

addition : (AdditiveGroup s, Unital s, Decidable [s,s] leq) =>
  DiscreteOrderedGroupSpec (+) Zero Ng leq One ->
  (u : s) -> leq One (u + Ng One) ->
  Vect n (Digit leq Ng u) ->
  Vect n (Digit leq Ng u) ->
  Vect n (Digit leq Ng u)
addition spec u bound xs ys =
  carryAll $ zipWith (computeCarryForSum spec u bound) xs ys

||| semantics
phi : (Foldable t, AdditiveGroup s, Multiplicative s) => s -> t s -> s
phi radix = foldl f Zero where f acc x = acc * radix + x
