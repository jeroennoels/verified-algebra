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
  o2 = plusAbelian (ring spec) x radix

scalingLemmaO : (AdditiveGroup s, Multiplicative s, Unital s) =>
  UnitalRingSpec {s} (+) Zero Ng (*) One ->
    (radix : s) -> (x : s) ->
    scale Zero Ng radix O + x = x + radix * value O
scalingLemmaO spec radix x = sym (o1 === o2) where
  o1 : x + radix * Zero = x + Zero
  o1 = cong $ zeroAbsorbsR (ring spec) radix
  o2 : x + Zero = Zero + x
  o2 = plusAbelian (ring spec) x Zero

scalingLemmaM : (AdditiveGroup s, Multiplicative s, Unital s) =>
  UnitalRingSpec {s} (+) Zero Ng (*) One ->
    (radix : s) -> (x : s) ->
    scale Zero Ng radix M + x = x + radix * value M
scalingLemmaM spec radix x = o4 === o3 where
  o1 : Ng (radix * One) = radix * Ng One
  o1 = negatedMultiplication (ring spec) radix One
  o2 : Ng (radix * One) = Ng radix
  o2 = cong $ neutralR (multiplicativeMonoid spec) radix
  o3 : x + Ng radix = x + radix * Ng One
  o3 = cong $ o2 @== o1
  o4 : Ng radix + x = x + Ng radix
  o4 = plusAbelian (ring spec) _ x


scalingLemma : (AdditiveGroup s, Multiplicative s, Unital s) =>
  UnitalRingSpec {s} (+) Zero Ng (*) One ->
    (radix : s) -> (x : s) -> (c : Carry) ->
    scale Zero Ng radix c + x = x + radix * value c
scalingLemma spec radix x P = scalingLemmaP spec radix x
scalingLemma spec radix x O = scalingLemmaO spec radix x
scalingLemma spec radix x M = scalingLemmaM spec radix x
