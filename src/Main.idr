module Main

import Specifications.Group
import Specifications.TranslationInvariance
import Specifications.Ring

import Proofs.GroupCancelationLemmas
import Proofs.GroupTheory
import Proofs.TranslationInvarianceTheory

-- Here we bring in the Neg interface to get a succint additive
-- notation for groups
additiveGroup : Neg a => Type
additiveGroup {a} = GroupSpec {s = a} (+) (fromInteger 0) negate

-- In additive terminology we can "double" an element x of a group, and
-- accompany the result with a proof of "double x - x = x"
double : Neg a => .{spec : additiveGroup {a}} ->
  (x : a) -> (y ** y + negate x = x)
double {spec} x = 
  let y = x + x
  in (y ** groupCancel3Bis spec x x)

-- For primitive types we postulate. 
-- For Data.ZZ we would provide proof.
postulate integerGroup : GroupSpec {s = Integer} (+) 0 negate

-- Now we actually compute something, at run time!  :^)
test : Integer -> Integer
test x = fst (double {spec = integerGroup} x)

main : IO ()
main = printLn (test 123)
