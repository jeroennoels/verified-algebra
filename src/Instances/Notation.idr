module Instances.Notation

import public Data.Vect
import public Data.Rel
import public Decidable.Decidable
import Common.Abbrev
import Common.Interfaces
import Specifications.DiscreteOrderedGroup

%default total
%access public export

specifyOrderedGroup : (AdditiveGroup s, Decidable [s,s] leq) => Type
specifyOrderedGroup {leq} = OrderedGroupSpec (+) Zero Ng leq


specifyDiscreteOrderedGroup :
  (AdditiveGroup s, Unital s, Decidable [s,s] leq) => Type
specifyDiscreteOrderedGroup {leq} = 
  DiscreteOrderedGroupSpec (+) Zero Ng leq One
