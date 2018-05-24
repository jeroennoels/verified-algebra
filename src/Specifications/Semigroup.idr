module Specifications.Semigroup

import public Common.Abbrev

%default total
%access public export

infixl 8 #

||| specification 
isAssociative : Binop s -> Type
isAssociative (#) = (x,y,z : _) -> x # (y # z) = (x # y) # z

||| specification 
isAbelian : Binop s -> Type
isAbelian (#) = (x,y : _) -> x # y = y # x
