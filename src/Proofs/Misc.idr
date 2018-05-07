module Proofs.Misc

import Abbrev
import Util
import Specifications.Order

%default total
%access export

rewriteReflexive : isReflexive rel -> (a,b : s) -> a = b -> rel a b
rewriteReflexive {rel} spec a b eq = rewriteRelation rel Refl eq (spec a)


orderContra : TotalOrderSpec leq -> (a,b : s) -> 
  Not (leq a b) -> (leq b a, Not (a = b))
orderContra spec a b given = (o2, contraposition o3 given) where
  o1 : Either (leq a b) (leq b a)
  o1 = totalOrder spec a b
  o2 : leq b a
  o2 = o1 `butNotLeft` given
  o3 : a = b -> leq a b
  o3 = rewriteReflexive (reflexive (partialOrder spec)) a b
