module Main

import Common.Abbrev
import Common.Util
import Common.Interfaces
import Specifications.Semigroup
import Specifications.Monoid
import Specifications.Group
import Specifications.Order
import Specifications.Ring
import Specifications.TranslationInvariance
import Specifications.OrderedGroup
import Specifications.DiscreteOrderedGroup
import Specifications.OrderedRing
import Symmetry.Opposite
import Symmetry.Abelian
import Proofs.OrderTheory
import Proofs.SemigroupTheory
import Proofs.GroupCancelationLemmas
import Proofs.GroupTheory
import Proofs.GroupCancelMisc
import Proofs.TranslationInvarianceTheory
import Proofs.DiscreteOrderTheory
import Proofs.Interval
import Proofs.RingTheory
import Instances.Notation
import Instances.TrustInteger
import Instances.OrderZZ
import Instances.ZZ
import Applications.Example

%default total

testAbsoluteValue : Integer -> Integer
testAbsoluteValue x = fst $
  absoluteValue (orderedGroup integerDiscreteOrderedGroup) x

testAbsoluteValueZZ : ZZ -> ZZ
testAbsoluteValueZZ x = fst $ absoluteValue zzOrderedGroup x

main : IO ()
main = do printLn $ map testAbsoluteValue [(-5)..5]
          printLn $ map testAbsoluteValueZZ (map fromInteger [(-10)..10])
