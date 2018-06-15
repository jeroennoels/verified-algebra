||| This example is inspired by exact real arithmetic.
||| See README for a brief introduction.
module Applications.ExactReal.Addition

import Data.Vect
import Common.Util
import Common.Interfaces
import Specifications.DiscreteOrderedGroup
import Specifications.OrderedRing
import Proofs.GroupTheory
import Proofs.Interval
import Applications.ExactReal.Carry

%default total
%access public export

data Digit : (leq : Binrel s) -> (neg : s -> s) -> s -> Type where
  MkDigit : (x : s) -> .InSymRange leq neg u x -> Digit leq neg u

implementation Show s => Show (Digit {s} leq neg u) where
  show (MkDigit x _) = show x


||| when full decidability is overkill
maybeDigit : Decidable [s,s] leq => (neg : s -> s) -> (u : s) ->
  s -> Maybe (Digit leq neg u)
maybeDigit {leq} neg u x =
  case decideBetween {leq} (neg u) u x of
    Yes prf => Just (MkDigit x prf)
    No _ => Nothing

maybeDigits : (Traversable trav, Decidable [s,s] leq) =>
  (neg : s -> s) -> (u : s) -> trav s -> Maybe (trav (Digit leq neg u))
maybeDigits {leq} neg u = sequence . map (maybeDigit {leq} neg u)


addDigits : AdditiveGroup s =>
  PartiallyOrderedGroupSpec {s} (+) Zero Ng leq ->
    OuterBinop (Digit leq Ng) u u (u + u)
addDigits spec (MkDigit x p) (MkDigit y q) =
  MkDigit (x + y) (addInSymRange spec p q)

computeCarryForSum : (AdditiveGroup s, Unital s, Decidable [s,s] leq) =>
  DiscreteOrderedGroupSpec (+) Zero Ng leq One ->
  (u : s) -> leq One (u + Ng One) ->
  Digit leq Ng u -> 
  Digit leq Ng u -> 
  CarryResult (+) Zero Ng leq One u
computeCarryForSum spec u bound x y =
  let MkDigit z prf = addDigits (partiallyOrderedGroup spec) x y
  in computeCarry spec u bound z prf


carryToLeft : (AdditiveGroup s, Unital s, Decidable [s,s] leq) =>
  CarryResult (+) Zero Ng leq One u -> 
  CarryResult (+) Zero Ng leq One u -> 
  Digit leq Ng u
carryToLeft curr next = 
  let (_,a) = value curr
      (c,_) = value next
  in MkDigit (a + scale Zero Ng One c) ?prf

carryAll : (AdditiveGroup s, Unital s, Decidable [s,s] leq) =>
  Vect n $ CarryResult (+) Zero Ng leq One u -> 
  Vect n $ Digit leq Ng u
carryAll (x::y::ys) = carryToLeft x y :: carryAll (y::ys)
carryAll [x] = let (_,a) = value x in [MkDigit a ?prf]
carryAll [] = []  

addition : (AdditiveGroup s, Unital s, Decidable [s,s] leq) =>
  DiscreteOrderedGroupSpec (+) Zero Ng leq One ->
  (u : s) -> leq One (u + Ng One) ->
  Vect n $ Digit leq Ng u -> 
  Vect n $ Digit leq Ng u -> 
  Vect n $ Digit leq Ng u
addition spec u bound xs ys = 
  carryAll $ zipWith (computeCarryForSum spec u bound) xs ys
  
  
||| semantics
phi : (Foldable t, AdditiveGroup s, Multiplicative s) => s -> t s -> s
phi r = foldl f Zero where f acc x = acc * r + x

