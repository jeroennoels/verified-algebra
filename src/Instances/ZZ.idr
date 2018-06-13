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

implementation Multiplicative ZZ where
  (*) = multZ

implementation Unital ZZ where
  One = 1

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

zzRing : specifyRing {s = ZZ}
zzRing = MkRing
  (MkPreRing
    multDistributesOverPlusRightZ
    multDistributesOverPlusLeftZ
    plusCommutativeZ)
  zzGroup
  multAssociativeZ

zzOrderedRing : specifyOrderedRing {leq = LTEZ}
zzOrderedRing = MkOrderedRing
  (MkPartiallyOrderedRing zzRing zzPartiallyOrderedMagma)
  lteTotalZ

zzDiscreteOrderedRing : specifyDiscreteOrderedRing {leq = LTEZ}
zzDiscreteOrderedRing = MkDiscreteOrderedRing zzOrderedRing
  lteDiscreteZ multOneLeftNeutralZ multOneRightNeutralZ
