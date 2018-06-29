||| This example is inspired by exact real arithmetic.
||| See README for a brief introduction.
module Applications.ExactReal.Absorb

import Data.Vect
import Common.Util
import Common.Interfaces
import Specifications.DiscreteOrderedGroup
import Specifications.OrderedRing
import Proofs.GroupTheory
import Applications.ExactReal.Carry
import Applications.ExactReal.Scaling
import Applications.ExactReal.AbsorptionLemmas
import Applications.ExactReal.Adhoc

%default total
%access export

||| This is a proof friendly semantics function.  Consider a tail
||| recursive variation for run time use.
public export
phi : (AdditiveGroup s, Multiplicative s, Unital s) =>
  (radix : s) -> (lsdf : Vect n s) -> (msc : Carry) -> s
phi radix (x :: xs) c = x + radix * phi radix xs c
phi radix [] c = value c


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
data Absorption :
  (k : Nat) ->
  (constraints : s -> Vect k s -> Type) ->
  (semantics : Vect (S k) s -> Carry -> s) ->
  (inputs : Vect (S k) s) -> Type
  where MkAbsorption :
    (msc : Carry) ->
    (pending : s) ->
    (outputs : Vect k s) ->
    (constraints pending outputs) ->
    (semantics inputs O = semantics (pending :: outputs) msc) ->
    Absorption k constraints semantics inputs


outputs : Absorption {s} k _ _ _ -> (Carry, Vect (S k) s)
outputs (MkAbsorption c p o _ _) = (c, reverse (p :: o))


absorptionBase : (AdditiveGroup s, Multiplicative s, Unital s) =>
  DiscreteOrderedRingSpec (+) Zero Ng (*) leq One ->
  (radix : s) ->
  (red : Reduction (+) Zero Ng leq One u radix) ->
  Absorption Z (Ranges leq Ng u (u + Ng One)) (phi radix) [input red]
absorptionBase spec radix (MkReduction i c o invariant outRange) =
  MkAbsorption c o [] (MkRanges outRange []) o3
  where
    o1 : o + radix * value c = i
    o1 = rewriteInvariant (unitalRing spec) radix i o c invariant
    o2 : i = i + radix * value O
    o2 = adhocIdentity2 (ring (unitalRing spec)) i radix
    o3 : phi radix [i] O = phi radix [o] c
    o3 = sym (o1 === o2)


arithLemma : (AdditiveGroup s, Multiplicative s, Unital s) =>
  UnitalRingSpec {s} (+) Zero Ng (*) One ->
  (msc : Carry) ->
  (pending : s) ->
  (outputs : Vect k s) ->
  (inputs : Vect (S k) s) ->
  (red : Reduction (+) Zero Ng _ One u radix) ->
  (ih : phi radix inputs O = phi radix (pending :: outputs) msc) ->
  phi radix (input red :: inputs) O =
  phi radix (output red :: (value (carry red) + pending) :: outputs) msc
arithLemma {s} {radix} spec msc pending outputs inputs
        (MkReduction i c o invariant _) inductionHypothesis =
  let
    adhoc = adhocIdentity1 (ring spec) pending o radix (value c) o2
    shift = radix * phi radix inputs O
    shifted = cong {f = (+ shift)} o1
  in shifted @== adhoc
  where
    o1 : o + radix * value c = i
    o1 = rewriteInvariant spec radix i o c invariant
    o2 : phi radix inputs O = pending + radix * phi radix outputs msc
    o2 = inductionHypothesis


absorptionStep : (AdditiveGroup s, Multiplicative s, Unital s) =>
  DiscreteOrderedRingSpec (+) Zero Ng (*) leq One ->
  (radix : s) ->
  (red : Reduction (+) Zero Ng leq One u radix) ->
  Absorption k (Ranges leq Ng u (u + Ng One)) (phi radix) inputs ->
  Absorption (S k) (Ranges leq Ng u (u + Ng One))
    (phi radix) (input red :: inputs)
absorptionStep spec radix red@(MkReduction _ _ _ _ reducedRange)
       (MkAbsorption {inputs} msc pending outputs ranges invariant) =
  let absorb = value (carry red) + pending
  in MkAbsorption msc (output red) (absorb :: outputs)
      (rangeLemma (discreteOrderedGroup spec) ranges reducedRange (carry red))
      (arithLemma (unitalRing spec) msc pending outputs inputs red invariant)
