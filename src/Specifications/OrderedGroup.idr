module Specifications.OrderedGroup

import public Specifications.TranslationInvariance

%default total
%access public export

||| composed specification 
data OrderedGroupSpec : Binop s -> s -> (s -> s) -> Binrel s -> Type where
  MkOrderedGroup :
    PartiallyOrderedGroupSpec op inv e leq ->
    isTotalOrder leq ->
    OrderedGroupSpec op inv e leq

||| forget
partiallyOrderedGroup : OrderedGroupSpec add zero neg leq ->
  PartiallyOrderedGroupSpec add zero neg leq
partiallyOrderedGroup (MkOrderedGroup p _) = p

||| forget
totalOrder : OrderedGroupSpec _ _ _ leq -> TotalOrderSpec leq
totalOrder (MkOrderedGroup p t) =
  MkTotalOrder (order (invariantOrder p)) t
