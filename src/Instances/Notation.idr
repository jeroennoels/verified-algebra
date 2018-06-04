module Instances.Notation

import public Data.Vect
import public Data.Rel
import public Decidable.Decidable
import Common.Abbrev
import Common.Interfaces
import Specifications.DiscreteOrderedGroup

%default total
%access public export

specifyMonoid : AdditiveGroup s => Type
specifyMonoid {s} = MonoidSpec {s} (+) Zero

specifyGroup : AdditiveGroup s => Type
specifyGroup {s} = GroupSpec {s} (+) Zero Ng

specifyPartialOrder : Decidable [s,s] leq => Type
specifyPartialOrder {leq} = PartialOrderSpec leq

specifyTotalOrder : Decidable [s,s] leq => Type
specifyTotalOrder {leq} = TotalOrderSpec leq

specifyPartiallyOrderedMagma : (AdditiveGroup s, Decidable [s,s] leq) => Type
specifyPartiallyOrderedMagma {leq} = PartiallyOrderedMagmaSpec (+) leq

specifyPartiallyOrderedGroup : (AdditiveGroup s, Decidable [s,s] leq) => Type
specifyPartiallyOrderedGroup {leq} = PartiallyOrderedGroupSpec (+) Zero Ng leq

specifyOrderedGroup : (AdditiveGroup s, Decidable [s,s] leq) => Type
specifyOrderedGroup {leq} = OrderedGroupSpec (+) Zero Ng leq

specifyDiscreteOrderedGroup :
  (AdditiveGroup s, Unital s, Decidable [s,s] leq) => Type
specifyDiscreteOrderedGroup {leq} =
  DiscreteOrderedGroupSpec (+) Zero Ng leq One
