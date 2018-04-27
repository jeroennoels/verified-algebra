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

export
rewriteRelation : (rel : Rel s) -> a = aa -> b = bb -> rel a b -> rel aa bb
rewriteRelation rel p q given = rewrite sym p in rewrite sym q in given

export
contraposition : (p -> q) -> Not q -> Not p
contraposition f contra p = contra (f p)
