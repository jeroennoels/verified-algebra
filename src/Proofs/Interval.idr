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

rewriteBetween : a = c -> b = d -> Between leq (a,b) x -> Between leq (c,d) x
rewriteBetween p q given = rewrite sym p in rewrite sym q in given


weakenR : PartialOrderSpec rel ->
  rel b c -> Between rel (a,b) x -> Between rel (a,c) x
weakenR spec bc (MkBetween ax xb) =
  MkBetween ax (transitive spec _ _ _ xb bc)


invertBetween : PartiallyOrderedGroupSpec _ _ inv rel ->
  Between rel (a,b) x -> Between rel (inv b, inv a) (inv x)
invertBetween spec (MkBetween ax xb) =
  MkBetween (inverseReversesOrder spec xb)
            (inverseReversesOrder spec ax)


invertSymRange : PartiallyOrderedGroupSpec _ _ inv rel ->
  InSymRange rel inv b x -> InSymRange rel inv b (inv x)
invertSymRange {b} spec given = rewriteBetween Refl o2 o1 where
  o1 : Between rel (inv b, inv (inv b)) (inv x)
  o1 = invertBetween spec given
  o2 : inv (inv b) = b
  o2 = groupInverseInvolution (group spec) b


translateIntervalR : {(#) : Binop s} ->
  PartiallyOrderedMagmaSpec (#) leq -> (c : s) ->
    Between leq (a,b) x -> Between leq (a # c, b # c) (x # c)
translateIntervalR spec c (MkBetween ax xb) = MkBetween
  (translationInvariantR spec _ _ _ ax)
  (translationInvariantR spec _ _ _ xb)


translateIntervalL : {(#) : Binop s} ->
  PartiallyOrderedMagmaSpec (#) leq -> (c : s) ->
    Between leq (a,b) x -> Between leq (c # a, c # b) (c # x)
translateIntervalL spec = translateIntervalR (opposite spec)


composeIntervals : {(#) : Binop s} ->
  PartiallyOrderedMagmaSpec (#) leq ->
    Between leq (a,b) x ->
    Between leq (c,d) y ->
    Between leq (a # c, b # d) (x # y)
composeIntervals spec (MkBetween ax xb) (MkBetween cy yd) = MkBetween
  (composeOrder spec _ _ _ _ ax cy)
  (composeOrder spec _ _ _ _ xb yd)


addInSymRange : {(+) : Binop s} -> PartiallyOrderedGroupSpec (+) _ neg leq ->
  InSymRange leq neg a x ->
  InSymRange leq neg a y ->
  InSymRange leq neg (a + a) (x + y)
addInSymRange {a} spec p q =
  rewrite groupInverseAnti (group spec) a a in
  composeIntervals (invariantOrder spec) p q


public export
decideBetween : Decidable [s,s] leq => (a,b,x : s) -> Dec (Between leq (a,b) x)
decideBetween a b x =
  decideBoth MkBetween betweenL betweenR
    (decision {rel = leq} a x)
    (decision {rel = leq} x b)

public export
decidePivot : Decidable [s,s] leq =>
  DiscreteOrderedGroupSpec add zero neg leq unit ->
    (p,x : s) ->
    Between leq (a,b) x ->
    EitherErased (Between leq (a,p) x)
                 (Between leq (add unit p, b) x)
decidePivot {s} spec p x (MkBetween ax xb) =
  case separate spec x p of
    Left xp => Left (MkBetween ax xp)
    Right px => Right (MkBetween px xb)

public export
decidePivotBis : Decidable [s,s] leq =>
  DiscreteOrderedGroupSpec add zero neg leq unit ->
    (p,x : s) ->
    Between leq (a,b) x ->
    EitherErased (Between leq (a, add (neg unit) p) x)
                 (Between leq (p, b) x)
decidePivotBis {s} spec p x (MkBetween ax xb) =
  case separateBis spec x p of
    Left xp => Left (MkBetween ax xp)
    Right px => Right (MkBetween px xb)

public export
decidePartition3 : Decidable [s,s] leq =>
  DiscreteOrderedGroupSpec add zero neg leq unit ->
    (p,q,x : s) ->
    Between leq (a,b) x ->
    Either3Erased (Between leq (a,p) x)
                  (Between leq (add unit p, add (neg unit) q) x)
                  (Between leq (q,b) x)
decidePartition3 spec p q x axb =
  case decidePivot spec p x axb of
    Left l => Left l
    Right pxb =>
      case decidePivotBis spec q x pxb of
        Left m => Middle m
        Right r => Right r
