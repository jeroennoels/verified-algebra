module Applications.Carry

import Util
import Specifications.DiscreteOrderedGroup
import Proofs.GroupCancelationLemmas
import Proofs.GroupCancelMisc
import Proofs.GroupTheory
import Proofs.TranslationInvarianceTheory
import Proofs.Interval

%default total
%access public export

interface AdditiveGroup s where
  (+) : s -> s -> s
  Neg : s -> s
  Zero : s
  One : s

data Carry = M | O | P

implementation Show Carry where
  show M = "Carry_M"
  show O = "Carry_O"
  show P = "Carry_P"

export
shiftToLeft : {(+) : Binop s} ->
  PartiallyOrderedGroupSpec (+) zero neg leq ->
    (u,a,x : s) ->
    Between leq x (neg (u + u), neg u) ->
    Between leq (a + u + x) (a + neg u, a)
shiftToLeft spec u a x given = rewriteBetween o2 o3 o1 where
  o1 : Between leq (a + u + x) (a + u + neg (u + u), a + u + neg u)
  o1 = translateIntervalL (invariantOrder spec) (a + u) given
  o2 : a + u + neg (u + u) = a + neg u
  o2 = groupCancelMisc2 (group spec) a u _
  o3 : a + u + neg u = a
  o3 = groupCancel3bis (group spec) a u

export
shiftLeftToSymRange : {(+) : Binop s} ->
  DiscreteOrderedGroupSpec (+) _ neg leq unit ->
    (u,x : s) ->
    leq unit (u + neg unit) ->
    Between leq x (neg (u + u), neg u) ->
    InRange leq neg (unit + u + x) (u + neg unit)
shiftLeftToSymRange {s} spec u x bound given = o4 where
  sx : s
  sx = unit + u + x
  o1 : Between leq sx (unit + neg u, unit)
  o1 = shiftToLeft (partiallyOrderedGroup spec) u unit x given
  o2 : Between leq sx (unit + neg u, u + neg unit)
  o2 = weakenR (partialOrder (totalOrder spec)) bound o1
  o3 : neg (u + neg unit) = unit + neg u
  o3 = groupInverseAntiInverse (group spec) u unit
  o4 : Between leq sx (neg (u + neg unit), u + neg unit)
  o4 = rewriteBetween (sym o3) Refl o2


export
shiftRightToSymRange : {(+) : Binop s} ->
  DiscreteOrderedGroupSpec (+) _ neg leq unit ->
    (u,x : s) ->
    leq unit (u + neg unit) ->
    Between leq x (u, u + u) ->
    InRange leq neg (x + neg (unit + u)) (u + neg unit)
shiftRightToSymRange spec u x bound given = rewrite sym o2 in o1 where
  o1 : InRange leq neg (neg (unit + u + neg x)) (u + neg unit)
  o1 = let pog = partiallyOrderedGroup spec in
       invertSymRange pog $
       shiftLeftToSymRange spec u (neg x) bound $
       invertBetween pog given
  o2 : neg (unit + u + neg x) = x + neg (unit + u)
  o2 = groupInverseAntiInverse (group spec) (unit + u) x


export
toSymRange : {(+) : Binop s} ->
  PartiallyOrderedGroupSpec (+) _ neg leq ->
  isAbelian (+) ->
    Between leq x (a + neg b, neg a + b) ->
    InRange leq neg x (b + neg a)
toSymRange spec abel =
  rewriteBetween (sym $ groupInverseAntiInverse (group spec) _ _) (abel _ _)


data CarryResult : Binop s -> (s -> s) -> Rel s -> s -> Type where
  MkCarryResult :
    Carry -> (x : s) -> InRange leq neg x (add u (neg unit)) ->
    CarryResult add neg leq unit

carry : CarryResult _ _ _ _ -> Carry
carry (MkCarryResult c _ _) = c


computeCarry : AdditiveGroup s =>
  DiscreteOrderedGroupSpec (+) Zero Neg leq One ->
    decisionProcedure leq -> (u,x : s) ->
    InRange leq Neg x (u + u) -> CarryResult (+) Neg leq One
computeCarry spec decide u x prf =
  case decidePartition3 spec decide (Neg u) u x prf of
    Left prf
      => MkCarryResult M (One + u + x)
           (shiftLeftToSymRange spec u x ?bound prf)
    Middle prf
      => MkCarryResult O x
           (toSymRange (partiallyOrderedGroup spec) (abelian spec) prf)
    Right prf
      => MkCarryResult P (x + Neg (One + u))
           (shiftRightToSymRange spec u x ?bound prf)
