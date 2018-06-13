||| This example is inspired by exact real arithmetic.
||| See README for a brief introduction.
module Applications.ExactReal.Addition

import Common.Util
import Common.Interfaces
import Specifications.DiscreteOrderedGroup
import Proofs.GroupTheory
import Proofs.Interval
import Applications.ExactReal.Carry

%default total
%access public export

Digit : .(leq : Binrel s) -> .(neg : s -> s) -> s -> Type
Digit leq neg u = (x ** InSymRange leq neg u x)


||| when full decidability is overkill
maybeDigit : Decidable [s,s] leq => (neg : s -> s) -> (u : s) ->
  s -> Maybe (Digit leq neg u)
maybeDigit {leq} neg u x =
  case decideBetween {leq} (neg u) u x of
    Yes prf => Just (x ** prf)
    No _ => Nothing

maybeDigits : (Traversable trav, Decidable [s,s] leq) =>
  (neg : s -> s) -> (u : s) -> trav s -> Maybe (trav (Digit leq neg u))
maybeDigits {leq} neg u = sequence . map (maybeDigit {leq} neg u)


addDigit : AdditiveGroup s =>
  PartiallyOrderedGroupSpec {s} (+) Zero Ng leq ->
    OuterBinop (Digit leq Ng) u u (u + u)
addDigit spec (x ** p) (y ** q) = ((x + y) ** addInSymRange spec p q)

addPairwise : AdditiveGroup s =>
  PartiallyOrderedGroupSpec {s} (+) Zero Ng leq ->
    OuterBinop (List . Digit leq Ng) u u (u + u)
addPairwise spec = zipWith (addDigit spec)
