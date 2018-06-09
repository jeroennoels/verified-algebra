module Common.Abbrev

%default total
%access public export

Binop : Type -> Type
Binop s = s -> s -> s

Binrel : Type -> Type
Binrel s = s -> s -> Type

OuterBinop : {index : Type} -> (f : index -> Type) -> (a,b,c : index) -> Type
OuterBinop f a b c = f a -> f b -> f c 

infixl 5 ===
infixl 5 @==

||| associative infix syntax for `trans`
(===) : a = b -> b = c -> a = c
(===) Refl Refl = Refl

(@==) : a = b -> a = c -> b = c
(@==) Refl Refl = Refl
