module Applications.Example

import Util
import Specifications.Order
import Specifications.TranslationInvariance
import Specifications.Group
import Specifications.OrderedGroup
import Specifications.DiscreteOrderedGroup
import Proofs.Interval
import Instances.TrustInteger

%default total
%access public export

data Carry = M | O | P


-- data CarryInvariant : Binop s -> s -> (s -> s) -> Rel s -> s -> Type 
--    Between leq x (neg (u + unit), u + unit) 

carry : {(+) : Binop s} -> DiscreteOrderedGroupSpec (+) zero neg leq unit ->
  decisionProcedure leq -> (u,x : s) -> 
    InRange leq neg x (u + u) -> (Carry, s)
carry spec decide u x prf = 
  case decidePartition3 spec decide (neg u) u x prf of
    Left _   => (M, x + (u + unit))
    Middle _ => (O, x)
    Right _  => (P, x + neg (u + unit))
