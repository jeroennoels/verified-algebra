module Instances.Notation

import public Data.Vect
import public Data.Rel
import public Decidable.Decidable
import Common.Abbrev
import Common.Interfaces
import Specifications.DiscreteOrderedGroup
import Specifications.OrderedRing

%default total
%access public export

specifyMonoid : Ringops s => Type
specifyMonoid {s} = MonoidSpec {s} (+) Zero

specifyGroup : Ringops s => Type
specifyGroup {s} = GroupSpec {s} (+) Zero Ng

specifyPartialOrder : Decidable [s,s] leq => Type
specifyPartialOrder {leq} = PartialOrderSpec leq

specifyTotalOrder : Decidable [s,s] leq => Type
specifyTotalOrder {leq} = TotalOrderSpec leq

specifyPartiallyOrderedMagma : (Ringops s, Decidable [s,s] leq) => Type
specifyPartiallyOrderedMagma {leq} = PartiallyOrderedMagmaSpec (+) leq

specifyPartiallyOrderedGroup : (Ringops s, Decidable [s,s] leq) => Type
specifyPartiallyOrderedGroup {leq} = PartiallyOrderedGroupSpec (+) Zero Ng leq

specifyOrderedGroup : (Ringops s, Decidable [s,s] leq) => Type
specifyOrderedGroup {leq} = OrderedGroupSpec (+) Zero Ng leq

specifyDiscreteOrderedGroup : (Ringops s, Decidable [s,s] leq) => Type
specifyDiscreteOrderedGroup {leq} =
  DiscreteOrderedGroupSpec (+) Zero Ng leq One

specifyRing : Ringops s => Type
specifyRing {s} = RingSpec {s} (+) Zero Ng (*)

specifyPartiallyOrderedRing : (Ringops s, Decidable [s,s] leq) => Type
specifyPartiallyOrderedRing {leq} =
  PartiallyOrderedRingSpec (+) Zero Ng (*) leq

specifyOrderedRing : (Ringops s, Decidable [s,s] leq) => Type
specifyOrderedRing {leq} =
  OrderedRingSpec (+) Zero Ng (*) leq

specifyDiscreteOrderedRing : (Ringops s, Decidable [s,s] leq) => Type
specifyDiscreteOrderedRing {leq} =
  DiscreteOrderedRingSpec (+) Zero Ng (*) leq One
