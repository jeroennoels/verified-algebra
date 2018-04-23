module TrustInteger

import Specifications.Group
import Specifications.TranslationInvariance
import Specifications.Ring

import Proofs.GroupCancelationLemmas
import Proofs.GroupTheory
import Proofs.TranslationInvarianceTheory

%default total
%access public export


postulate integerUnitalRing : UnitalRingSpec ((+), 0, negate) ((*), 1)

integerRing : RingSpec ((+), 0, negate) (*)
integerRing = ring integerUnitalRing

