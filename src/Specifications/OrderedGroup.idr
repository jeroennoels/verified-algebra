module Specifications.OrderedGroup

import public Abbrev
import public Specifications.TranslationInvariance

%default total
%access public export

data OrderedGroupSpec : Binop s -> s -> (s -> s) -> Rel s -> Type where
  MkOrderedGroup :
    PartiallyOrderedGroupSpec op inv e leq ->
    isTotalOrder leq ->
    OrderedGroupSpec op inv e leq


partiallyOrderedGroup : OrderedGroupSpec add zero neg leq ->
  PartiallyOrderedGroupSpec add zero neg leq
partiallyOrderedGroup (MkOrderedGroup p _) = p

totalOrder : OrderedGroupSpec _ _ _ leq -> TotalOrderSpec leq
totalOrder (MkOrderedGroup p t) =
  MkTotalOrder (order (invariantOrder p)) t
