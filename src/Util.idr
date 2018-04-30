module Util

import Abbrev
import Data.So

%default total
%access public export

export
rewriteRelation : (rel : Rel s) -> a = aa -> b = bb -> rel a b -> rel aa bb
rewriteRelation rel p q given = rewrite sym p in rewrite sym q in given

export
contraposition : (p -> q) -> Not q -> Not p
contraposition f contra p = contra (f p)

total export
contraSo : (b : Bool) -> So (not b) -> Not (So b)
contraSo False Oh = absurd
contraSo True Oh impossible

total
decideBool : (b : Bool) -> Dec (So b)
decideBool b = case choose b of
  Left so => Yes so
  Right soNot => No (contraSo b soNot)
