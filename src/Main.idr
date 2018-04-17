module Main

import Specifications.Group
import Specifications.TranslationInvariance
import Specifications.Ring
import Proofs.GroupTheory


private
PrimAdd : Binop Integer
PrimAdd = prim__addBigInt

private
PrimNegate : Integer -> Integer
PrimNegate x = prim__subBigInt 0 x

postulate assoc : isAssociative PrimAdd
postulate zeroL : isNeutralL PrimAdd 0
postulate zeroR : isNeutralR PrimAdd 0
postulate negateL : isInverseL PrimAdd 0 PrimNegate
postulate negateR : isInverseR PrimAdd 0 PrimNegate

integerMonoid : MonoidSpec (+) 0 
integerMonoid = MkMonoid assoc zeroL zeroR 

integerGroup : GroupSpec (+) 0 PrimNegate
integerGroup = MkGroup integerMonoid negateL negateR

main : IO ()
main = printLn True
