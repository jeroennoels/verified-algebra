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

||| the result of absorbing carry digits
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
  in ?qed

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
