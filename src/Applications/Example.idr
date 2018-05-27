module Applications.Example

import Common.Util
import Common.Interfaces
import Specifications.OrderedGroup
import Proofs.OrderTheory
import Proofs.GroupTheory
import Proofs.GroupCancelationLemmas
import Proofs.TranslationInvarianceTheory

%default total
%access public export


absoluteValue : (AdditiveGroup s, Decidable [s,s] leq) =>
  .OrderedGroupSpec (+) Zero Ng leq -> s -> (a ** leq Zero a)
absoluteValue spec x =
  case decision {rel = leq} x Zero of
    Yes prf => (Ng x ** invertNegative (partiallyOrderedGroup spec) x prf)
    No contra =>
        let (positive, _) = orderContra (totalOrder spec) x Zero contra
        in (x ** positive)
