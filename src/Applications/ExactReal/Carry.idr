||| This example is inspired by exact real arithmetic.
||| See README for a brief introduction.
module Applications.ExactReal.Carry

import Common.Util
import Common.Interfaces
import Specifications.DiscreteOrderedGroup
import Proofs.GroupCancelationLemmas
import Proofs.Interval
import Applications.ExactReal.Lemmas.Carry

%default total
%access public export

data Carry = M | O | P

implementation Show Carry where
  show M = "M"
  show O = "O"
  show P = "P"

||| multiply by Carry
scale : s -> (s -> s) -> s -> Carry -> s
scale zero neg x M = neg x
scale zero neg x O = zero
scale zero neg x P = x

||| u = radix - 1
||| radix = u + 1
||| carry * radix + output = input
||| output in [-v..v] where v = u - 1
data CarryResult : Binop s -> s -> (s -> s) -> Binrel s -> s -> s -> Type where
  MkCarryResult :
    (input : s) -> (carry : Carry) -> (output : s) ->
    scale zero neg (add unit u) carry `add` output = input ->
    InSymRange leq neg (add u (neg unit)) output ->
    CarryResult add zero neg leq unit u

input : CarryResult {s} _ _ _ _ _ _ -> s
input (MkCarryResult i _ _ _ _) = i

carry : CarryResult _ _ _ _ _ _ -> Carry
carry (MkCarryResult _ c _ _ _) = c

output : CarryResult {s} _ _ _ _ _ _ -> s
output (MkCarryResult _ _ o _ _) = o

result : CarryResult {s} _ _ _ _ _ _ -> (Carry, s)
result (MkCarryResult _ c o _ _) = (c, o)

CarryResultShort : .DiscreteOrderedGroupSpec {s} add zero neg leq unit ->
  .(u : s) -> Type
CarryResultShort {add} {zero} {neg} {leq} {unit} spec u =
  CarryResult add zero neg leq unit u


||| See README for a brief introduction.
||| 1 <= u - 1 means radix >= 3.
computeCarry : (AdditiveGroup s, Unital s, Decidable [s,s] leq) =>
  (spec : DiscreteOrderedGroupSpec (+) Zero Ng leq One) ->
  (u : s) -> leq One (u + Ng One) ->
  (x : s) -> InSymRange leq Ng (u + u) x ->
  CarryResult (+) Zero Ng leq One u

computeCarry spec u bound x range =
  let pog = partiallyOrderedGroup spec
      grp = group (partiallyOrderedGroup spec)
      abel = abelian spec in
  case decidePartition3 spec (Ng u) u x range of
    Left prf
      => MkCarryResult x M (One + u + x)
           (groupCancel1bis grp _ x)
           (shiftLeftToSymRange pog u One x bound prf)
    Middle prf
      => MkCarryResult x O x
           (neutralL (monoid grp) _)
           (toSymRange pog abel prf)
    Right prf
      => MkCarryResult x P (x + Ng (One + u))
           (groupCancelAbelian grp abel _ x)
           (shiftRightToSymRange pog u One x bound prf)
