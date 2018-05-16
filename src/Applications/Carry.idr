module Applications.Carry

import Util
import Specifications.DiscreteOrderedGroup
import Proofs.GroupCancelationLemmas
import Proofs.GroupCancelMisc
import Proofs.Interval
%default total
%access public export

data Carry = M | O | P


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


carry : {(+) : Binop s} -> DiscreteOrderedGroupSpec (+) zero neg leq unit ->
  decisionProcedure leq -> (u,x : s) ->
    InRange leq neg x (u + u) -> (Carry, s)
carry spec decide u x prf =
  case decidePartition3 spec decide (neg u) u x prf of
    Left _   => (M, unit + u + x)
    Middle _ => (O, x)
    Right _  => (P, x + neg (u + unit))
