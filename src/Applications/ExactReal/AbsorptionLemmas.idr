||| This example is inspired by exact real arithmetic.
||| See README for a brief introduction.
module Applications.ExactReal.AbsorptionLemmas

import Data.Vect
import Common.Util
import Common.Interfaces
import Specifications.DiscreteOrderedGroup
import Proofs.GroupTheory
import Applications.ExactReal.Carry
import public Applications.ExactReal.Digit

%default total
%access export

||| Express the constraint that the output is in the allowed digit
||| range.  The output range is [-v, v] before carry absorption, and
||| [-u, u] after.
public export
data Ranges : Binrel s -> (s -> s) -> s -> s -> s -> Vect k s -> Type
  where MkRanges :
    InSymRange leq neg v pending ->
    (digits : Vect k (Digit leq neg u)) ->
    Ranges leq neg u v pending (map Digit.val digits)

absorbCarry : (AdditiveGroup s, Unital s) =>
  DiscreteOrderedGroupSpec {s} (+) Zero Ng leq One ->
    InSymRange leq Ng (u + Ng One) x ->
    (c : Carry) ->
    InSymRange leq Ng u (value c + x)

rangeLemma : (AdditiveGroup s, Unital s) =>
  DiscreteOrderedGroupSpec {s} (+) Zero Ng leq One ->
    Ranges leq Ng u (u + Ng One) oldPending outputs ->
    InSymRange leq Ng (u + Ng One) newPending ->
    (c : Carry) ->
    Ranges leq Ng u (u + Ng One) newPending ((value c + oldPending) :: outputs)
rangeLemma {oldPending} spec (MkRanges old digits) prf c =
  let output = value c + oldPending
      digit = MkDigit output (absorbCarry spec old c)
  in MkRanges prf (digit :: digits)
