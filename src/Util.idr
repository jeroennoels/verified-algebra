module Util

import Abbrev

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
