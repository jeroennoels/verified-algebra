module Main

import Util
import Data.Vect
import Data.Rel
import Decidable.Decidable
import Specifications.DiscreteOrderedGroup
import Proofs.GroupTheory
import Proofs.TranslationInvarianceTheory
import Proofs.DiscreteOrderTheory
import Proofs.Interval
import Instances.TrustInteger
import Instances.ZZ
import Applications.Example
import Applications.Carry


implementation AdditiveGroup Integer where
  (+) = prim__addBigInt
  Neg = prim__subBigInt 0
  Zero = 0
  One = 1

implementation Decidable [Integer, Integer] IntegerLeq where
  decide = decideLeq 
  
-- integerDiscreteOrderedGroupSpec : Type
-- integerDiscreteOrderedGroupSpec = DiscreteOrderedGroupSpec
--   prim__addBigInt 0 (prim__subBigInt 0) IntegerLeq 1

lala : AdditiveGroup s => Rel s -> Type
lala {s} leq = DiscreteOrderedGroupSpec {s} (+) Zero Neg leq One



postulate integerDiscreteOrderedGroup : lala IntegerLeq


testSeparation : Integer -> Integer -> String
testSeparation a b = show $ separate integerDiscreteOrderedGroup decideLeq a b


partition3 : (x : Integer) -> .Between IntegerLeq x (a,b) -> 
  Integer -> Integer -> String
partition3 x axb p q = show $ 
  decidePartition3 integerDiscreteOrderedGroup decideLeq p q x axb 


testPartition3 : Integer -> Integer -> Integer -> Integer -> Integer -> String
testPartition3 a p q b x = 
  case decideBetween {leq = IntegerLeq} decideLeq x a b of
    Yes axb => partition3 x axb p q
    No _ => "Error"


testCarry : Integer -> String
testCarry x =    
  case decideBetween {leq = IntegerLeq} decideLeq x (-18) 18 of
    Yes inRange => show $ carry $ 
            computeCarry integerDiscreteOrderedGroup 9 x 
              (CheckIntegerLeq Oh) inRange 
    No _ => "Error"


main : IO ()
main = do printLn $ map (testPartition3 0 3 7 10) [(-1)..11]
          printLn $ map testDouble [0..9] 
          printLn $ map testAbsoluteValue [(-5)..5] 
          printLn $ map testCarry [(-20)..20] 
          
