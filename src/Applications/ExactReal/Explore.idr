||| This example is inspired by exact real arithmetic.
||| See README for a brief introduction.
module Applications.ExactReal.Explore

import Data.Vect
import Common.Util
import Common.Interfaces
import Specifications.DiscreteOrderedGroup
import Specifications.OrderedRing
import Proofs.SemigroupTheory
import Proofs.GroupTheory
import Applications.ExactReal.Carry
import Applications.ExactReal.Scaling
import public Applications.ExactReal.Digit

%default total
%access public export

||| This is a proof friendly semantics function.  Consider a tail
||| recursive variation for run time use.
phi : (AdditiveGroup s, Multiplicative s, Unital s) =>
  (radix : s) -> (lsdf : Vect n s) -> (msc : Carry) -> s
phi radix (x :: xs) c = x + radix * phi radix xs c
phi radix [] c = value c


private
adhocIdentity : (AdditiveGroup s, Multiplicative s) =>
  (spec : RingSpec {s} (+) Zero Ng (*)) -> (b,x,y,z : s) ->
  a = b + c -> x + y * z + y * a = x + y * (z + b + c)
adhocIdentity spec {a} b {c} x y z given = o3 where
  o1 : z + a = z + b + c
  o1 = cong given === associative (monoid (group spec)) z b c
  o2 : y * z + y * a = y * (z + b + c)
  o2 = distributativeL spec y z a @== cong o1
  o3 : x + y * z + y * a = x + y * (z + b + c)
  o3 = associative (monoid (group spec)) x _ _ @== cong o2  


||| The result of absorbing carry digits:
|||
|||           in1    in2    in3
|||           ou1    ou2    pen + unk
|||    msc    abs    abs    unk
|||
||| unk = the least significant carry is still unknown
||| pen = ouput of reduction before absorbing the unknown carry
||| msc = most significant carry
||| abs = carry already absorbed in the corresponding output
export
data Absorption :
  (k : Nat) ->
  (semantics : Vect (S k) s -> Carry -> s) ->
  (inputs : Vect (S k) s) -> Type
  where MkAbsorption :
    (msc : Carry) ->
    (pending : s) ->
    (outputs : Vect k s) ->
    (invariant : semantics inputs O = semantics (pending :: outputs) msc) ->
    Absorption k semantics inputs

export
lemma : (AdditiveGroup s, Multiplicative s, Unital s) =>
  (spec : DiscreteOrderedRingSpec (+) Zero Ng (*) leq One) ->
  (msc : Carry) ->
  (pending : s) ->
  (outputs : Vect k s) ->
  (inputs : Vect (S k) s) ->
  (red : Reduction (+) Zero Ng leq One u radix) ->
  (ih : phi radix inputs O = phi radix (pending :: outputs) msc) ->
  phi radix (input red :: inputs) O =
  phi radix (output red :: (value (carry red) + pending) :: outputs) msc
lemma {s} {radix} spec msc pending outputs inputs red ih =
  let
    MkReduction i c o invariant _ = red
    o1 = the (scale Zero Ng radix c + o = i) invariant
    o2 = the (scale Zero Ng radix c = radix * value c)
             (scalingLemma (unitalRing spec) radix c)
    o3 = the (scale Zero Ng radix c + o = o + radix * value c)
             (abelianCongruence (plusAbelian (ring (unitalRing spec))) o2)
    o4 = the (o + radix * value c = i) (o3 @== o1)
    o5 = the (phi radix inputs O = pending + radix * phi radix outputs msc) ih
    o6 = adhocIdentity (ring (unitalRing spec)) pending o radix (value c) o5
    vv = radix * phi radix inputs O
  in cong {f = (+ vv)} o4 @== o6

export
step : (AdditiveGroup s, Multiplicative s, Unital s) =>
  (spec : DiscreteOrderedRingSpec (+) Zero Ng (*) leq One) ->
  (radix : s) ->
  (red : Reduction (+) Zero Ng leq One u radix) ->
  Absorption k (phi radix) inputs ->
  Absorption (S k) (phi radix) (input red :: inputs)
step spec radix red (MkAbsorption {inputs} msc pending outputs invariant) =
  let out = value (carry red) + pending
  in MkAbsorption msc (output red) (out :: outputs)
       (lemma spec msc pending outputs inputs red invariant)
