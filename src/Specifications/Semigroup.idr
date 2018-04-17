module Specifications.Semigroup

import public Abbrev

%default total
%access public export

infixl 8 #

isAssociative : Binop s -> Type
isAssociative (#) = (x,y,z : _) -> x # (y # z) = (x # y) # z

isAbelian : Binop s -> Type
isAbelian (#) = (x,y : _) -> x # y = y # x
