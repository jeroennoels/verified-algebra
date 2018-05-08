module Abbrev

%default total
%access public export

Binop : Type -> Type
Binop s = s -> s -> s

Rel : Type -> Type
Rel s = s -> s -> Type

infixl 5 ===
infixl 5 @==

(===) : a = b -> b = c -> a = c
(===) Refl Refl = Refl

(@==) : a = b -> a = c -> b = c
(@==) Refl Refl = Refl

decisionProcedure : Rel s -> Type
decisionProcedure rel = (a,b : _) -> Dec (rel a b)
