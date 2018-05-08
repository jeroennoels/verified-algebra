module Util

import Abbrev
import Data.So
import Decidable.Decidable

%default total
%access export

rewriteRelation : (rel : Rel s) -> a = aa -> b = bb -> rel a b -> rel aa bb
rewriteRelation rel p q given = rewrite sym p in rewrite sym q in given

contraposition : (p -> q) -> Not q -> Not p
contraposition f contra p = contra (f p)

total
butNotLeft : Either a b -> Not a -> b
butNotLeft (Left a) contra = absurd (contra a) 
butNotLeft (Right b) _ = b

total public export
isItSo : (b : Bool) -> Dec (So b)
isItSo True = Yes Oh
isItSo False = No absurd
