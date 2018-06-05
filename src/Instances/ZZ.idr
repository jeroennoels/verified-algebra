module Instances.ZZ

import public Data.ZZ
import Common.Util
import Common.Interfaces
import Specifications.OrderedGroup
import Specifications.DiscreteOrderedGroup
import Specifications.OrderedRing
import Symmetry.Abelian
import Instances.Notation
import public Instances.OrderZZ

%default total
%access public export

implementation AdditiveGroup ZZ where
  (+) = plusZ
  Ng = negate
  Zero = Pos 0

implementation Unital ZZ where
  One = 1

implementation Decidable [ZZ, ZZ] LTEZ where
  decide = isLTEZ

zzMonoid : specifyMonoid {s = ZZ}
zzMonoid = MkMonoid plusAssociativeZ plusZeroLeftNeutralZ plusZeroRightNeutralZ

zzGroup : specifyGroup {s = ZZ}
zzGroup = MkGroup zzMonoid plusNegateInverseRZ plusNegateInverseLZ

zzPartialOrder : specifyPartialOrder {leq = LTEZ}
zzPartialOrder = MkPartialOrder lteReflZ lteTransitiveZ lteAntisymmetricZ

zzTotalOrder : specifyTotalOrder {leq = LTEZ}
zzTotalOrder = MkTotalOrder zzPartialOrder lteTotalZ

zzPartiallyOrderedMagma : specifyPartiallyOrderedMagma {leq = LTEZ}
zzPartiallyOrderedMagma = MkPartiallyOrderedMagma zzPartialOrder
  lteLeftTranslationInvariantZ $
  abelianTranslationInvariantLR plusCommutativeZ lteLeftTranslationInvariantZ

zzPartiallyOrderedGroup : specifyPartiallyOrderedGroup {leq = LTEZ}
zzPartiallyOrderedGroup = MkPartiallyOrderedGroup zzGroup
  zzPartiallyOrderedMagma

zzOrderedGroup : specifyOrderedGroup {leq = LTEZ}
zzOrderedGroup = MkOrderedGroup zzPartiallyOrderedGroup lteTotalZ

zzDiscreteOrderedGroup : specifyDiscreteOrderedGroup {leq = LTEZ}
zzDiscreteOrderedGroup = MkDiscreteOrderedGroup zzOrderedGroup
  plusCommutativeZ lteDiscreteZ
