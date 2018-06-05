module Proofs.TranslationInvarianceTheory

import Common.Util
import Specifications.DiscreteOrderedGroup
import Proofs.GroupCancelationLemmas
import Proofs.GroupTheory
import Proofs.TranslationInvarianceTheory
import Proofs.DiscreteOrderTheory
import Symmetry.Opposite

%default total
%access export

infixl 8 #

rewriteBetween : a = c -> b = d -> Between leq x (a,b) -> Between leq x (c,d)
rewriteBetween p q given = rewrite sym p in rewrite sym q in given


weakenR : PartialOrderSpec rel ->
  rel b c -> Between rel x (a,b) -> Between rel x (a,c)
weakenR spec bc (MkBetween ax xb) =
  MkBetween ax (transitive spec _ _ _ xb bc)


invertBetween : PartiallyOrderedGroupSpec _ _ inv rel ->
  Between rel x (a,b) -> Between rel (inv x) (inv b, inv a)
invertBetween spec (MkBetween ax xb) =
  MkBetween (inverseReversesOrder spec xb)
            (inverseReversesOrder spec ax)


invertSymRange : PartiallyOrderedGroupSpec _ _ inv rel ->
  InSymRange rel inv x b -> InSymRange rel inv (inv x) b
invertSymRange {b} spec given = rewriteBetween Refl o2 o1 where
  o1 : Between rel (inv x) (inv b, inv (inv b))
  o1 = invertBetween spec given
  o2 : inv (inv b) = b
  o2 = groupInverseInvolution (group spec) b


translateIntervalR : {(#) : Binop s} ->
  PartiallyOrderedMagmaSpec (#) leq -> (c : s) ->
    Between leq x (a,b) -> Between leq (x # c) (a # c, b # c)
translateIntervalR spec c (MkBetween ax xb) = MkBetween
  (translationInvariantR spec _ _ _ ax)
  (translationInvariantR spec _ _ _ xb)


translateIntervalL : {(#) : Binop s} ->
  PartiallyOrderedMagmaSpec (#) leq -> (c : s) ->
    Between leq x (a,b) -> Between leq (c # x) (c # a, c # b)
translateIntervalL spec = translateIntervalR (opposite spec)


composeIntervals : {(#) : Binop s} ->
  PartiallyOrderedMagmaSpec (#) leq ->
    Between leq x (a,b) ->
    Between leq y (c,d) ->
    Between leq (x # y) (a # c, b # d)
composeIntervals spec (MkBetween ax xb) (MkBetween cy yd) = MkBetween
  (composeOrder spec _ _ _ _ ax cy)
  (composeOrder spec _ _ _ _ xb yd)

public export
decideBetween : Decidable [s,s] leq => (x,a,b : s) -> Dec (Between leq x (a,b))
decideBetween x a b =
  decideBoth MkBetween betweenL betweenR
    (decision {rel = leq} a x)
    (decision {rel = leq} x b)

public export
decidePivot : Decidable [s,s] leq =>
  DiscreteOrderedGroupSpec add zero neg leq unit ->
    (p,x : s) ->
    Between leq x (a,b) ->
    EitherErased (Between leq x (a,p))
                 (Between leq x (add unit p, b))
decidePivot {s} spec p x (MkBetween ax xb) =
  case separate spec x p of
    Left xp => Left (MkBetween ax xp)
    Right px => Right (MkBetween px xb)

public export
decidePivotBis : Decidable [s,s] leq =>
  DiscreteOrderedGroupSpec add zero neg leq unit ->
    (p,x : s) ->
    Between leq x (a,b) ->
    EitherErased (Between leq x (a, add (neg unit) p))
                 (Between leq x (p, b))
decidePivotBis {s} spec p x (MkBetween ax xb) =
  case separateBis spec x p of
    Left xp => Left (MkBetween ax xp)
    Right px => Right (MkBetween px xb)

public export
decidePartition3 : Decidable [s,s] leq =>
  DiscreteOrderedGroupSpec add zero neg leq unit ->
    (p,q,x : s) ->
    Between leq x (a,b) ->
    Either3Erased (Between leq x (a,p))
                  (Between leq x (add unit p, add (neg unit) q))
                  (Between leq x (q,b))
decidePartition3 spec p q x axb =
  case decidePivot spec p x axb of
    Left l => Left l
    Right pxb =>
      case decidePivotBis spec q x pxb of
        Left m => Middle m
        Right r => Right r
