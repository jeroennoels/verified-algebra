module Applications.Carry

import Util
import Data.Vect
import Data.Rel
import Decidable.Decidable
import Specifications.DiscreteOrderedGroup
import Proofs.GroupCancelationLemmas
import Proofs.GroupCancelMisc
import Proofs.GroupTheory
import Proofs.TranslationInvarianceTheory
import Proofs.Interval
import Common.Interfaces

%default total
%access public export

data Carry = M | O | P

implementation Show Carry where
  show M = "M"
  show O = "O"
  show P = "P"

export
shiftToLeft : {(+) : Binop s} ->
  PartiallyOrderedGroupSpec (+) _ neg leq ->
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
  PartiallyOrderedGroupSpec (+) _ neg leq ->
    (u,a,x : s) ->
    leq a (u + neg a) ->
    Between leq x (neg (u + u), neg u) ->
    InRange leq neg (a + u + x) (u + neg a)
shiftLeftToSymRange {s} spec u a x bound given = o4 where
  sx : s
  sx = a + u + x
  o1 : Between leq sx (a + neg u, a)
  o1 = shiftToLeft spec u a x given
  o2 : Between leq sx (a + neg u, u + neg a)
  o2 = weakenR (order spec) bound o1
  o3 : neg (u + neg a) = a + neg u
  o3 = groupInverseAntiInverse (group spec) u a
  o4 : Between leq sx (neg (u + neg a), u + neg a)
  o4 = rewriteBetween (sym o3) Refl o2


export
shiftRightToSymRange : {(+) : Binop s} ->
  PartiallyOrderedGroupSpec (+) _ neg leq ->
    (u,a,x : s) ->
    leq a (u + neg a) ->
    Between leq x (u, u + u) ->
    InRange leq neg (x + neg (a + u)) (u + neg a)
shiftRightToSymRange spec u a x bound given = rewrite sym o2 in o1 where
  o1 : InRange leq neg (neg (a + u + neg x)) (u + neg a)
  o1 = invertSymRange spec $
       shiftLeftToSymRange spec u a (neg x) bound $
       invertBetween spec given
  o2 : neg (a + u + neg x) = x + neg (a + u)
  o2 = groupInverseAntiInverse (group spec) (a + u) x


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

value : CarryResult {s} _ _ _ _ -> (Carry, s)
value (MkCarryResult c x _) = (c, x)

computeCarry : (AdditiveGroup s, Unital s, Decidable [s,s] leq) =>
  DiscreteOrderedGroupSpec (+) Zero Neg leq One ->
  (u,x : s) ->
  leq One (u + Neg One) ->
  InRange leq Neg x (u + u) ->
  CarryResult (+) Neg leq One
computeCarry spec u x bound prf =
  let pog = partiallyOrderedGroup spec in
  case decidePartition3 spec (Neg u) u x prf of
    Left prf
      => MkCarryResult M (One + u + x) $
           shiftLeftToSymRange pog u One x bound prf
    Middle prf
      => MkCarryResult O x $
           toSymRange pog (abelian spec) prf
    Right prf
      => MkCarryResult P (x + Neg (One + u)) $
           shiftRightToSymRange pog u One x bound prf
