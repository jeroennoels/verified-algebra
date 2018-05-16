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

data Carry = M | O | P

export
lemmaLeft : {(+) : Binop s} ->
  PartiallyOrderedGroupSpec (+) zero neg leq -> (u,y,x : s) ->
    Between leq x (neg (u + u), neg u) ->
    Between leq (y + u + x) (y + neg u, y)
lemmaLeft spec u y x given = rewriteBetween o2 o3 o1 where
  o1 : Between leq (y + u + x) (y + u + neg (u + u), y + u + neg u)
  o1 = translateIntervalL (invariantOrder spec) (y + u) given
  o2 : y + u + neg (u + u) = y + neg u
  o2 = groupCancelMisc2 (group spec) y u _
  o3 : y + u + neg u = y
  o3 = groupCancel3bis (group spec) y u


export
lemmaRight : {(+) : Binop s} ->
  PartiallyOrderedGroupSpec (+) zero neg leq -> (u,y,x : s) ->
    Between leq x (u, u + u) ->
    Between leq (x + neg (y + u)) (neg y, u + neg y)
lemmaRight spec u y x given =
  rewrite sym o2 in rewrite sym o3 in o1
 where
  o1 : Between leq (neg (y + u + neg x)) (neg y, neg (y + neg u))
  o1 = invertBetween spec $ lemmaLeft spec u y (neg x) $ invertBetween spec given
  o2 : neg (y + u + neg x) = x + neg (y + u)
  o2 = groupInverseAntiInverse (group spec) (y + u) x
  o3 : neg (y + neg u) = u + neg y
  o3 = groupInverseAntiInverse (group spec) y u


carry : {(+) : Binop s} -> DiscreteOrderedGroupSpec (+) zero neg leq unit ->
  decisionProcedure leq -> (u,x : s) ->
    InRange leq neg x (u + u) -> (Carry, s)
carry spec decide u x prf =
  case decidePartition3 spec decide (neg u) u x prf of
    Left _   => (M, unit + u + x)
    Middle _ => (O, x)
    Right _  => (P, x + neg (unit + u))
