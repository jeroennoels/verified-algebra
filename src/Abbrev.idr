module Abbrev

%default total
%access public export

Binop : Type -> Type
Binop s = s -> s -> s

Rel : Type -> Type
Rel s = s -> s -> Type

infixl 5 ===

(===) : a = b -> b = c -> a = c
(===) = trans

export
rewriteRelation : (rel : Rel s) -> a = aa -> b = bb -> rel a b -> rel aa bb
rewriteRelation rel p q given = rewrite sym p in rewrite sym q in given

