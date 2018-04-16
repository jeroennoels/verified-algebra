module Abbrev

%default total
%access public export

Binop : Type -> Type
Binop s = s -> s -> s

Rel : Type -> Type
Rel s = s -> s -> Type

