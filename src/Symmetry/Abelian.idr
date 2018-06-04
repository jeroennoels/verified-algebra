module Symmetry.Abelian

import Specifications.TranslationInvariance

%default total
%access export

abelianTranslationInvariantLR : isAbelian op -> 
  isTranslationInvariantL op rel -> 
  isTranslationInvariantR op rel
abelianTranslationInvariantLR abel left x y a given =
  rewrite abel x a in 
  rewrite abel y a in
  left x y a given 
