module Symmetry.Opposite

import Specifications.Semigroup
import Specifications.Monoid
import Specifications.Group
import Specifications.Order
import Specifications.TranslationInvariance

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

namespace PartiallyOrderedMagma
  opposite : PartiallyOrderedMagmaSpec op leq ->
    PartiallyOrderedMagmaSpec (flip op) leq
  opposite (MkPartiallyOrderedMagma o l r) = MkPartiallyOrderedMagma o r l

namespace PartiallyOrderedGroup
  opposite : PartiallyOrderedGroupSpec op inv e leq ->
    PartiallyOrderedGroupSpec (flip op) inv e leq
  opposite (MkPartiallyOrderedGroup g m) =
    MkPartiallyOrderedGroup (opposite g) (opposite m)
