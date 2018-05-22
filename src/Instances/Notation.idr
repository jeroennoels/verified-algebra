module Instances.Notation

import public Data.Vect
import public Data.Rel
import public Decidable.Decidable
import Abbrev
import Common.Interfaces
import Specifications.DiscreteOrderedGroup

%default total
%access public export

specifyDiscreteOrderedGroup :
  (AdditiveGroup s, Unital s, Decidable [s,s] leq) => Type
specifyDiscreteOrderedGroup {leq} = 
  DiscreteOrderedGroupSpec (+) Zero Neg leq One