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
lemmaLeft : {(+) : Binop s} ->
  PartiallyOrderedGroupSpec (+) zero neg leq -> (u,a,x : s) ->
    Between leq x (neg (u + u), neg u) ->
    Between leq (a + u + x) (a + neg u, a)
lemmaLeft spec u a x given = rewriteBetween o2 o3 o1 where
  o1 : Between leq (a + u + x) (a + u + neg (u + u), a + u + neg u)
  o1 = translateIntervalL (invariantOrder spec) (a + u) given
  o2 : a + u + neg (u + u) = a + neg u
  o2 = groupCancelMisc2 (group spec) a u _
  o3 : a + u + neg u = a
  o3 = groupCancel3bis (group spec) a u


data CarryResult : Binop s -> (s -> s) -> Rel s -> s -> Type where
  MkCarryResult : 
    Carry -> (x : s) ->
    InRange leq neg x (add u (neg unit)) ->    
    CarryResult add neg leq unit

carry : CarryResult _ _ _ _ -> Carry
carry (MkCarryResult c _ _) = c


computeCarry : AdditiveGroup s =>
  DiscreteOrderedGroupSpec (+) Zero Neg leq One ->
    decisionProcedure leq -> (u,x : s) ->
    InRange leq Neg x (u + u) -> CarryResult (+) Neg leq One
computeCarry spec decide u x prf =
  case decidePartition3 spec decide (Neg u) u x prf of
    Left prf => let ll = lemmaLeft (partiallyOrderedGroup spec) u One x prf
                    ww = weakenR (partialOrder (totalOrder spec)) ?q ll
                    vv = rewriteBetween 
                           (sym $ groupInverseAntiInverse (group spec) u One) Refl ww
                in MkCarryResult {u} M (One + u + x) vv
    Middle _ => ?m -- (O, x)
    Right _ => ?r --(P, x + Neg (One + u))





export
lemmaRight : {(+) : Binop s} ->
  PartiallyOrderedGroupSpec (+) zero neg leq -> (u,a,x : s) ->
    Between leq x (u, u + u) ->
    Between leq (x + neg (a + u)) (neg a, u + neg a)
lemmaRight spec u a x given =
  rewrite sym o2 in rewrite sym o3 in o1
where
  o1 : Between leq (neg (a + u + neg x)) (neg a, neg (a + neg u))
  o1 = invertBetween spec $ lemmaLeft spec u a (neg x) $ invertBetween spec given
  o2 : neg (a + u + neg x) = x + neg (a + u)
  o2 = groupInverseAntiInverse (group spec) (a + u) x
  o3 : neg (a + neg u) = u + neg a
  o3 = groupInverseAntiInverse (group spec) a u
