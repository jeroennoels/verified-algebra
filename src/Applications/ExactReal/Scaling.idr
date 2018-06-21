module Applications.ExactReal.Scaling

import Common.Util
import Common.Interfaces
import Specifications.Ring
import Proofs.RingTheory
import Applications.ExactReal.Carry

%default total
%access export

value : (AdditiveGroup s, Unital s) => Carry -> s
value P = One
value O = Zero
value M = Ng One

scalingLemmaP : (AdditiveGroup s, Multiplicative s, Unital s) =>
  UnitalRingSpec {s} (+) Zero Ng (*) One ->
    (radix : s) -> (x : s) ->
    scale Zero Ng radix P + x = x + radix * value P
scalingLemmaP spec radix x = sym (o1 === o2) where
  o1 : x + radix * One = x + radix
  o1 = cong $ neutralR (multiplicativeMonoid spec) radix
  o2 : x + radix = radix + x
  o2 = abelian (abelianGroup (ring spec)) x radix


scalingLemma : (AdditiveGroup s, Multiplicative s, Unital s) =>
  UnitalRingSpec {s} (+) Zero Ng (*) One ->
    (radix : s) -> (x : s) -> (c : Carry) ->
    scale Zero Ng radix c + x = x + radix * value c
scalingLemma spec radix x P = scalingLemmaP spec radix x
scalingLemma spec radix x O = let p = zeroAbsorbsR (ring spec) radix in ?q
scalingLemma spec radix x M = ?qq
-- Zero + x = x + radix * Zero
