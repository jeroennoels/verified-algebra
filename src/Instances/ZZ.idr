module Instances.ZZ

import Data.ZZ

import Specifications.OrderedRing

%default total
%access public export

ZZnegate : ZZ -> ZZ
ZZnegate = negate

zzMonoid : MonoidSpec ZZ.plusZ 0
zzMonoid = MkMonoid plusAssociativeZ plusZeroLeftNeutralZ plusZeroRightNeutralZ

zzGroup : GroupSpec ZZ.plusZ 0 ZZnegate
zzGroup = MkGroup zzMonoid plusNegateInverseRZ plusNegateInverseLZ

zzAbelianGroup : AbelianGroupSpec ZZ.plusZ 0 ZZnegate
zzAbelianGroup = MkAbelianGroup zzGroup plusCommutativeZ

zzPreRing : PreRingSpec ZZ.plusZ ZZ.multZ
zzPreRing = MkPreRing
  multDistributesOverPlusRightZ
  multDistributesOverPlusLeftZ
  plusCommutativeZ

zzRing : RingSpec ZZ.plusZ 0 ZZnegate ZZ.multZ
zzRing = MkRing zzPreRing zzGroup multAssociativeZ

zzUnitalRing : UnitalRingSpec ZZ.plusZ 0 ZZnegate ZZ.multZ 1
zzUnitalRing = MkUnitalRing zzRing multOneLeftNeutralZ multOneRightNeutralZ
