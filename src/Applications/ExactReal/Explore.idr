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
import Applications.ExactReal.Scaling
import Applications.ExactReal.Adhoc
import public Applications.ExactReal.Digit

%default total
%access public export

||| This is a proof friendly semantics function.  Consider a tail
||| recursive variation for run time use.
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
base : (AdditiveGroup s, Multiplicative s, Unital s) =>
  DiscreteOrderedRingSpec (+) Zero Ng (*) leq One ->
  (radix : s) ->
  (red : Reduction (+) Zero Ng leq One u radix) ->
  Absorption Z (phi radix) [input red]
base spec radix (MkReduction i c o invariant _) = MkAbsorption c o [] o3 
  where
    o1 : o + radix * value c = i 
    o1 = rewriteInvariant (unitalRing spec) radix i o c invariant
    o2 : i = i + radix * value O
    o2 = adhocIdentity2 (ring (unitalRing spec)) i radix
    o3 : phi radix [i] O = phi radix [o] c
    o3 = sym (o1 === o2)
  
export
lemma : (AdditiveGroup s, Multiplicative s, Unital s) =>
  UnitalRingSpec {s} (+) Zero Ng (*) One ->
  (msc : Carry) ->
  (pending : s) ->
  (outputs : Vect k s) ->
  (inputs : Vect (S k) s) ->
  (red : Reduction (+) Zero Ng _ One u radix) ->
  (ih : phi radix inputs O = phi radix (pending :: outputs) msc) ->
  phi radix (input red :: inputs) O =
  phi radix (output red :: (value (carry red) + pending) :: outputs) msc
lemma {s} {radix} spec msc pending outputs inputs 
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
    

export
step : (AdditiveGroup s, Multiplicative s, Unital s) =>
  DiscreteOrderedRingSpec (+) Zero Ng (*) leq One ->
  (radix : s) ->
  (red : Reduction (+) Zero Ng leq One u radix) ->
  Absorption k (phi radix) inputs ->
  Absorption (S k) (phi radix) (input red :: inputs)
step spec radix red (MkAbsorption {inputs} msc pending outputs invariant) =
  let out = value (carry red) + pending
  in MkAbsorption msc (output red) (out :: outputs)
       (lemma (unitalRing spec) msc pending outputs inputs red invariant)
