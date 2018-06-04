module Specifications.TranslationInvariance

import public Specifications.Group
import public Specifications.Order

%default total
%access public export

infixl 8 #

||| specification
isTranslationInvariantL : Binop s -> Binrel s -> Type
isTranslationInvariantL (#) rel = (x,y,a : _) -> rel x y -> rel (a # x) (a # y)

||| specification
isTranslationInvariantR : Binop s -> Binrel s -> Type
isTranslationInvariantR (#) rel = (x,y,a : _) -> rel x y -> rel (x # a) (y # a)

||| composed specification
data PartiallyOrderedMagmaSpec : Binop s -> Binrel s -> Type where
  MkPartiallyOrderedMagma :
    PartialOrderSpec leq ->
    isTranslationInvariantL op leq ->
    isTranslationInvariantR op leq ->
    PartiallyOrderedMagmaSpec op leq

||| forget
order : PartiallyOrderedMagmaSpec _ leq -> PartialOrderSpec leq
order (MkPartiallyOrderedMagma o _ _) = o

||| forget
translationInvariantL : PartiallyOrderedMagmaSpec op leq ->
  isTranslationInvariantL op leq
translationInvariantL (MkPartiallyOrderedMagma _ l _) = l

||| forget
translationInvariantR : PartiallyOrderedMagmaSpec op leq ->
  isTranslationInvariantR op leq
translationInvariantR (MkPartiallyOrderedMagma _ _ r) = r

||| composed specification
data PartiallyOrderedGroupSpec :
       Binop s -> s -> (s -> s) -> Binrel s -> Type where
  MkPartiallyOrderedGroup :
    GroupSpec op inv e ->
    PartiallyOrderedMagmaSpec op leq ->
    PartiallyOrderedGroupSpec op inv e leq

||| forget
invariantOrder : PartiallyOrderedGroupSpec op _ _ leq ->
  PartiallyOrderedMagmaSpec op leq
invariantOrder (MkPartiallyOrderedGroup _ m) = m

||| forget
group : PartiallyOrderedGroupSpec op e inv _ -> GroupSpec op e inv
group (MkPartiallyOrderedGroup g _) = g

namespace PartiallyOrderedGroup
  ||| forget more
  order : PartiallyOrderedGroupSpec _ _ _ leq -> PartialOrderSpec leq
  order = order . invariantOrder


||| A symmetric interval [-u, u]
InSymRange : Binrel s -> (s -> s) -> s -> s -> Type
InSymRange rel inv x u = Between rel x (inv u, u)
