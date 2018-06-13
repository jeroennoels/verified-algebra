||| This example is inspired by exact real arithmetic.
||| See README for a brief introduction.
module Applications.ExactReal.Carry

import Common.Util
import Common.Interfaces
import Specifications.DiscreteOrderedGroup
import Proofs.GroupCancelationLemmas
import Proofs.GroupCancelMisc
import Proofs.GroupTheory
import Proofs.TranslationInvarianceTheory
import Proofs.Interval

%default total
%access public export


data Carry = M | O | P

implementation Show Carry where
  show M = "M"
  show O = "O"
  show P = "P"


||| Adhoc lemma.
||| Start with `computeCarry` to understand where it fits.
export
shiftToLeft : {(+) : Binop s} ->
  PartiallyOrderedGroupSpec (+) _ neg leq ->
    (u,a,x : s) ->
    Between leq (neg (u + u), neg u) x ->
    Between leq (a + neg u, a) (a + u + x)
shiftToLeft spec u a x given = rewriteBetween o2 o3 o1 where
  o1 : Between leq (a + u + neg (u + u), a + u + neg u) (a + u + x)
  o1 = translateIntervalL (invariantOrder spec) (a + u) given
  o2 : a + u + neg (u + u) = a + neg u
  o2 = groupCancelMisc2 (group spec) a u _
  o3 : a + u + neg u = a
  o3 = groupCancel3bis (group spec) a u

||| Adhoc lemma.
||| Start with `computeCarry` to understand where it fits.
export
shiftLeftToSymRange : {(+) : Binop s} ->
  PartiallyOrderedGroupSpec (+) _ neg leq ->
    (u,a,x : s) ->
    leq a (u + neg a) ->
    Between leq (neg (u + u), neg u) x ->
    InSymRange leq neg (u + neg a) (a + u + x)
shiftLeftToSymRange {s} spec u a x bound given = o4 where
  sx : s
  sx = a + u + x
  o1 : Between leq (a + neg u, a) sx
  o1 = shiftToLeft spec u a x given
  o2 : Between leq (a + neg u, u + neg a) sx
  o2 = weakenR (order spec) bound o1
  o3 : neg (u + neg a) = a + neg u
  o3 = groupInverseAntiInverse (group spec) u a
  o4 : Between leq (neg (u + neg a), u + neg a) sx
  o4 = rewriteBetween (sym o3) Refl o2

||| Adhoc lemma.
||| Start with `computeCarry` to understand where it fits.
||| Derived from `shiftLeftToSymRange` using symmetry.
export
shiftRightToSymRange : {(+) : Binop s} ->
  PartiallyOrderedGroupSpec (+) _ neg leq ->
    (u,a,x : s) ->
    leq a (u + neg a) ->
    Between leq (u, u + u) x ->
    InSymRange leq neg (u + neg a) (x + neg (a + u))
shiftRightToSymRange spec u a x bound given = rewrite sym o2 in o1 where
  o1 : InSymRange leq neg (u + neg a) (neg (a + u + neg x))
  o1 = invertSymRange spec $
       shiftLeftToSymRange spec u a (neg x) bound $
       invertBetween spec given
  o2 : neg (a + u + neg x) = x + neg (a + u)
  o2 = groupInverseAntiInverse (group spec) (a + u) x

||| Lemma: turn an interval into a proper SymRange.
export
toSymRange : {(+) : Binop s} ->
  PartiallyOrderedGroupSpec (+) _ neg leq ->
  isAbelian (+) ->
    Between leq (a + neg b, neg a + b) x ->
    InSymRange leq neg (b + neg a) x
toSymRange spec abel =
  rewriteBetween (sym $ groupInverseAntiInverse (group spec) _ _) (abel _ _)


||| multiply by Carry
scale : s -> (s -> s) -> s -> Carry -> s
scale zero neg x M = neg x
scale zero neg x O = zero
scale zero neg x P = x


||| u = radix - 1
||| radix = u + 1
||| carry * radix + output = input
||| output in [-v..v] where v = u - 1

data CarryResult : Binop s -> s -> (s -> s) -> Binrel s -> s -> Type where
  MkCarryResult :
    (carry : Carry) -> (output : s) ->
    scale zero neg (add unit u) carry `add` output = input ->
    InSymRange leq neg (add u (neg unit)) output ->
    CarryResult add zero neg leq unit

value : CarryResult {s} _ _ _ _ _ -> (Carry, s)
value (MkCarryResult c r _ _) = (c, r)


||| See README for a brief introduction.
||| 1 <= u - 1 means radix >= 3.

computeCarry : (AdditiveGroup s, Unital s, Decidable [s,s] leq) =>
  DiscreteOrderedGroupSpec (+) Zero Ng leq One ->
  (u : s) -> leq One (u + Ng One) ->
  (x : s) -> InSymRange leq Ng (u + u) x ->
  CarryResult (+) Zero Ng leq One
  
computeCarry spec u bound x range =
  let pog = partiallyOrderedGroup spec
      grp = group (partiallyOrderedGroup spec)
      abel = abelian spec in
  case decidePartition3 spec (Ng u) u x range of
    Left prf
      => MkCarryResult M (One + u + x)
           (groupCancel1bis grp _ x)
           (shiftLeftToSymRange pog u One x bound prf)
    Middle prf
      => MkCarryResult O x
           (neutralL (monoid grp) _)
           (toSymRange pog abel prf)
    Right prf
      => MkCarryResult P (x + Ng (One + u))
           (groupCancelAbelian grp abel _ x)
           (shiftRightToSymRange pog u One x bound prf)
