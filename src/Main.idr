module Main

import Specifications.Group
import Specifications.TranslationInvariance
import Specifications.Ring
import Proofs.GroupTheory


private
PrimAdd : Binop Integer
PrimAdd = prim__addBigInt

postulate primIntegerGroup : GroupSpec (+) 0 negate

main : IO ()
main = printLn True
