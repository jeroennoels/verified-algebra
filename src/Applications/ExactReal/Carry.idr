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
data Reduction : Binop s -> s -> (s -> s) -> Binrel s -> s -> s -> Type where
  MkReduction :
    (input : s) -> (carry : Carry) -> (output : s) ->
    scale zero neg (add unit u) carry `add` output = input ->
    InSymRange leq neg (add u (neg unit)) output ->
    Reduction add zero neg leq unit u

input : Reduction {s} _ _ _ _ _ _ -> s
input (MkReduction i _ _ _ _) = i

carry : Reduction _ _ _ _ _ _ -> Carry
carry (MkReduction _ c _ _ _) = c

output : Reduction {s} _ _ _ _ _ _ -> s
output (MkReduction _ _ o _ _) = o

result : Reduction {s} _ _ _ _ _ _ -> (Carry, s)
result (MkReduction _ c o _ _) = (c, o)

ReductionShort : .DiscreteOrderedGroupSpec {s} add zero neg leq unit ->
  .(u : s) -> Type
ReductionShort {add} {zero} {neg} {leq} {unit} spec u =
  Reduction add zero neg leq unit u


||| See README for a brief introduction.
||| 1 <= u - 1 means radix >= 3.
computeCarry : (AdditiveGroup s, Unital s, Decidable [s,s] leq) =>
  (spec : DiscreteOrderedGroupSpec (+) Zero Ng leq One) ->
  (u : s) -> leq One (u + Ng One) ->
  (x : s) -> InSymRange leq Ng (u + u) x ->
  Reduction (+) Zero Ng leq One u

computeCarry spec u bound x range =
  let pog = partiallyOrderedGroup spec
      grp = group (partiallyOrderedGroup spec)
      abel = abelian spec in
  case decidePartition3 spec (Ng u) u x range of
    Left prf
      => MkReduction x M (One + u + x)
           (groupCancel1bis grp _ x)
           (shiftLeftToSymRange pog u One x bound prf)
    Middle prf
      => MkReduction x O x
           (neutralL (monoid grp) _)
           (toSymRange pog abel prf)
    Right prf
      => MkReduction x P (x + Ng (One + u))
           (groupCancelAbelian grp abel _ x)
           (shiftRightToSymRange pog u One x bound prf)
