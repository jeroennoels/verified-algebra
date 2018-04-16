module Specifications.Semigroup

import public Abbrev

%default total
%access export

infixl 8 #

public export
isAssociative : Binop s -> Type
isAssociative (#) = (x,y,z : _) -> x # (y # z) = (x # y) # z

public export
isAbelian : Binop s -> Type
isAbelian (#) = (x,y : _) -> x # y = y # x
