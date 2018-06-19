||| This example is inspired by exact real arithmetic.
||| See README for a brief introduction.
module Applications.ExactReal.Explore

import Data.Vect
import Common.Util
import Common.Interfaces
import Specifications.DiscreteOrderedGroup
import Specifications.OrderedRing
import Proofs.GroupTheory
import Applications.ExactReal.Carry
import public Applications.ExactReal.Digit

%default total
%access public export

value : (AdditiveGroup s, Unital s) => Carry -> s
value P = One
value O = Zero
value M = Ng One


||| This is a proof friendly semantics function.  Consider a tail
||| recursive variation for run time use.
phi : (AdditiveGroup s, Multiplicative s, Unital s) =>
  (radix : s) -> (lsdf : Vect n s) -> (msc : Carry) -> s
phi radix (x :: xs) c = x + radix * phi radix xs c
phi radix [] c = value c


||| the result of absorbing carry digits
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


scalingLemma : (AdditiveGroup s, Multiplicative s, Unital s) =>
  UnitalRingSpec {s} (+) Zero Ng (*) One ->
    (radix : s) -> (x : s) -> (c : Carry) ->
    scale Zero Ng radix c + x = x + radix * value c
scalingLemma spec radix x P =
  let o1 = neutralR (multiplicativeMonoid spec) radix
      o2 = abelian (abelianGroup (ring spec)) x radix
  in sym (cong o1 === o2)
scalingLemma spec radix x O = ?q
scalingLemma spec radix x M = ?qq


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
  let MkReduction i c o invariant _ = red
      o1 = the (phi radix inputs O = pending + radix * phi radix outputs msc) ih
      o2 = the (o + radix * value c = i)
             (scalingLemma (unitalRing spec) radix o c @== invariant)
  in ?qed


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
