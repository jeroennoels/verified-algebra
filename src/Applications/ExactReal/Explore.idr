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

||| Express the constraint that the output is in the allowed digit
||| range.  The output range is [-v, v] before carry absorption, and
||| [-u, u] after.
data Ranges : Binrel s -> (s -> s) -> s -> s -> s -> Vect k s -> Type
  where MkRanges :
    InSymRange leq neg v pending ->
    (digits : Vect k (Digit leq neg u)) ->
    Ranges leq neg u v pending (map Digit.val digits)


absorbCarry : (AdditiveGroup s, Unital s) =>
  DiscreteOrderedGroupSpec {s} (+) Zero Ng leq One ->
    InSymRange leq Ng (u + Ng One) x ->
    (c : Carry) ->
    InSymRange leq Ng u (value c + x)


rangeLemma : (AdditiveGroup s, Unital s) =>
  DiscreteOrderedGroupSpec {s} (+) Zero Ng leq One ->
    Ranges leq Ng u (u + Ng One) oldPending outputs ->
    InSymRange leq Ng (u + Ng One) newPending ->
    (c : Carry) ->
    Ranges leq Ng u (u + Ng One) newPending ((value c + oldPending) :: outputs)
rangeLemma {oldPending} spec (MkRanges old digits) prf c =
  let output = value c + oldPending
      digit = MkDigit output (absorbCarry spec old c)
  in MkRanges prf (digit :: digits)


base : (AdditiveGroup s, Multiplicative s, Unital s) =>
  DiscreteOrderedRingSpec (+) Zero Ng (*) leq One ->
  (radix : s) ->
  (red : Reduction (+) Zero Ng leq One u radix) ->
  Absorption Z (Ranges leq Ng u (u + Ng One)) (phi radix) [input red]
base spec radix (MkReduction i c o invariant outRange) =
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


step : (AdditiveGroup s, Multiplicative s, Unital s) =>
  DiscreteOrderedRingSpec (+) Zero Ng (*) leq One ->
  (radix : s) ->
  (red : Reduction (+) Zero Ng leq One u radix) ->
  Absorption k (Ranges leq Ng u (u + Ng One)) (phi radix) inputs ->
  Absorption (S k) (Ranges leq Ng u (u + Ng One))
    (phi radix) (input red :: inputs)
step spec radix red@(MkReduction _ _ _ _ reducedRange)
       (MkAbsorption {inputs} msc pending outputs ranges invariant) =
  let absorb = value (carry red) + pending
  in MkAbsorption msc (output red) (absorb :: outputs)
      (rangeLemma (discreteOrderedGroup spec) ranges reducedRange (carry red))
      (arithLemma (unitalRing spec) msc pending outputs inputs red invariant)


reduce : (AdditiveGroup s, Multiplicative s, Unital s, Decidable [s,s] leq) =>
  DiscreteOrderedRingSpec (+) Zero Ng (*) leq One ->
  (bound : leq One (u + Ng One)) ->
  (inputs : Vect (S k) (Digit leq Ng (u + u))) ->
  Absorption k (Ranges leq Ng u (u + Ng One)) (phi (One + u))
    (map Digit.val inputs)
reduce {u} spec bound [MkDigit input inRange] = base spec (One + u)
  (computeCarry (discreteOrderedGroup spec) u bound input inRange)
reduce {u} spec bound (MkDigit input inRange :: inputs@(_::_)) = 
  step spec (One + u)
    (computeCarry (discreteOrderedGroup spec) u bound input inRange)
    (reduce {u} spec bound inputs)


outputs : Absorption {s} k _ _ _ -> (Carry, Vect (S k) s)
outputs (MkAbsorption c p o _ _) = (c, reverse (p :: o))
