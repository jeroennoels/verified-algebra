||| This example is inspired by exact real arithmetic.
||| See README for a brief introduction.
module Applications.ExactReal.Addition

import Data.List.Quantifiers
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

decideInSymRange : Decidable [s,s] leq => (neg : s -> s) -> (u : s) ->
  (x : s) -> Dec (InSymRange leq neg u x)
decideInSymRange neg u = decideBetween (neg u) u


allDigits : Decidable [s,s] leq => (neg : s -> s) -> (u : s) ->
  List s -> Maybe $ List (Digit leq neg u)
allDigits {leq} neg u xs =
  case all (decideInSymRange {leq} neg u) xs of
    Yes proofs => Just $ allToDependentPairs {P = InSymRange leq neg u} proofs
    No contra => Nothing

add : AdditiveGroup s => PartiallyOrderedGroupSpec {s} (+) Zero Ng leq ->
  OuterBinop (Digit leq Ng) u u (u + u)
add spec (x ** p) (y ** q) = ((x + y) ** addInSymRange spec p q)

