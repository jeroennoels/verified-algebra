module Applications.Example

import public Data.So
import Data.Vect
import Data.Rel
import Decidable.Decidable
import Common.Util
import Specifications.OrderedGroup
import Proofs.OrderTheory
import Proofs.GroupTheory
import Proofs.GroupCancelationLemmas
import Proofs.TranslationInvarianceTheory
import Common.Interfaces

%default total
%access public export


absoluteValue : (AdditiveGroup s, Decidable [s,s] leq) =>
  OrderedGroupSpec (+) Zero Neg leq -> s -> (a ** leq Zero a)
absoluteValue {s} spec x =
  case dec x Zero of
    Yes prf => (Neg x ** invertNegative (partiallyOrderedGroup spec) x prf)
    No contra =>
        let (positive, _) = orderContra (totalOrder spec) x Zero contra
        in (x ** positive)
  where
    dec : decisionProcedure leq
    dec = decide {ts = [s,s]}
