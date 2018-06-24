module Applications.ExactReal.Adhoc

import Common.Abbrev
import Common.Interfaces
import Specifications.Ring
import Proofs.RingTheory

%default total
%access export

adhocIdentity1 : (AdditiveGroup s, Multiplicative s) =>
  RingSpec {s} (+) Zero Ng (*) -> (b,x,y,z : s) ->
    a = b + c -> x + y * z + y * a = x + y * (z + b + c)
adhocIdentity1 spec {a} b {c} x y z given = o3 where
  o1 : z + a = z + b + c
  o1 = cong given === associative (monoid (group spec)) z b c
  o2 : y * z + y * a = y * (z + b + c)
  o2 = distributativeL spec y z a @== cong o1
  o3 : x + y * z + y * a = x + y * (z + b + c)
  o3 = associative (monoid (group spec)) x _ _ @== cong o2


adhocIdentity2 : (AdditiveGroup s, Multiplicative s) =>
  RingSpec {s} (+) Zero Ng (*) -> (x,a : s) ->
    x = x + a * Zero
adhocIdentity2 spec x a = sym (o1 === o2) where
  o1 : x + a * Zero = x + Zero
  o1 = cong $ zeroAbsorbsR spec a
  o2 : x + Zero = x
  o2 = neutralR (monoid (group spec)) x

