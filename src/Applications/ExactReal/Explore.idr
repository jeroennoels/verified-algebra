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

||| semantics: explicit recursion
semantics : (AdditiveGroup s, Multiplicative s) => s -> s -> Vect n s -> s
semantics radix acc (x :: xs) = semantics radix (acc * radix + x) xs
semantics radix acc [] = acc

carrySemantics : AdditiveGroup s => s -> s -> Carry -> s
carrySemantics radix x c = x + scale Zero Ng radix c

value : (AdditiveGroup s, Unital s) => Carry -> s
value P = One
value O = Zero
value M = Ng One

data Absorption :
  (psi : s -> Carry -> s) ->
  (phi : Vect n s -> s) ->
  (inputs : Vect n s) ->
  Type where
  MkAbsorption :
    (cout : Carry) ->
    (outputs : Vect n s) ->
    phi inputs = psi (phi outputs) cout ->
    Absorption psi phi inputs

carry : Absorption _ _ _ -> Carry
carry (MkAbsorption c _ _) = c

outputs : Absorption {s} {n} _ _ _ -> Vect n s
outputs (MkAbsorption _ o _) = o

absorb : (AdditiveGroup s, Multiplicative s, Unital s) =>
  (reds : Vect n (Reduction (+) Zero Ng leq One u)) ->
  Absorption {s}
    (carrySemantics (One + u))
    (semantics (One + u) Zero)
    (map Carry.input reds)
absorb (red :: reds) =
    let absorption = absorb reds
        out = output red + value (carry absorption)
    in MkAbsorption (carry red) (out :: outputs absorption) ?pf
absorb [] = MkAbsorption O [] ?pf2
