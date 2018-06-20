||| Mathematicians often make an appeal to 'symmetry' to derive
||| variations on a lemma or theorem.
module Symmetry.Opposite

import Specifications.TranslationInvariance
import Specifications.Ring

%default total
%access export

private
oppAssoc : isAssociative op -> isAssociative (flip op)
oppAssoc spec x y z = sym (spec z y x)

namespace Monoid
  opposite : MonoidSpec op e -> MonoidSpec (flip op) e
  opposite (MkMonoid a l r) = MkMonoid (oppAssoc a) r l

namespace Group
  opposite : GroupSpec op e inv -> GroupSpec (flip op) e inv
  opposite (MkGroup m l r) = MkGroup (opposite m) r l

namespace PreRing
  multiplicativeOpposite : PreRingSpec add mul -> PreRingSpec add (flip mul)
  multiplicativeOpposite {add} {mul} (MkPreRing l r abel) =
    MkPreRing rop lop abel where
      rop : isDistributativeL add (flip mul)
      rop a x y = r x y a
      lop : isDistributativeR add (flip mul)
      lop x y a = l a x y

namespace Ring
  multiplicativeOpposite : RingSpec add zero neg mul ->
    RingSpec add zero neg (flip mul)
  multiplicativeOpposite (MkRing pre grp multassoc) =
    MkRing (multiplicativeOpposite pre) grp (oppAssoc multassoc)

namespace PartiallyOrderedMagma
  opposite : PartiallyOrderedMagmaSpec op leq ->
    PartiallyOrderedMagmaSpec (flip op) leq
  opposite (MkPartiallyOrderedMagma o l r) = MkPartiallyOrderedMagma o r l

namespace PartiallyOrderedGroup
  opposite : PartiallyOrderedGroupSpec op inv e leq ->
    PartiallyOrderedGroupSpec (flip op) inv e leq
  opposite (MkPartiallyOrderedGroup g m) =
    MkPartiallyOrderedGroup (opposite g) (opposite m)
