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

scalingLemmaM : (AdditiveGroup s, Multiplicative s, Unital s) =>
  UnitalRingSpec {s} (+) Zero Ng (*) One -> (radix : s) ->
    scale Zero Ng radix M = radix * value M
scalingLemmaM spec radix = o2 @== o1 where
  o1 : Ng (radix * One) = radix * Ng One
  o1 = negatedMultiplication (ring spec) radix One
  o2 : Ng (radix * One) = Ng radix
  o2 = cong $ neutralR (multiplicativeMonoid spec) radix

scalingLemma : (AdditiveGroup s, Multiplicative s, Unital s) =>
  UnitalRingSpec {s} (+) Zero Ng (*) One ->
    (radix : s) -> (c : Carry) ->
    scale Zero Ng radix c = radix * value c
scalingLemma spec radix P = sym $ neutralR (multiplicativeMonoid spec) radix
scalingLemma spec radix O = sym $ zeroAbsorbsR (ring spec) radix
scalingLemma spec radix M = scalingLemmaM spec radix
