module Common.Abbrev

%default total
%access public export

Binop : Type -> Type
Binop s = s -> s -> s

Binrel : Type -> Type
Binrel s = s -> s -> Type

infixl 5 ===
infixl 5 @==

||| associative infix syntax for `trans`
(===) : a = b -> b = c -> a = c
(===) Refl Refl = Refl

(@==) : a = b -> a = c -> b = c
(@==) Refl Refl = Refl
