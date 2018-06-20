module Proofs.GroupCancelationLemmas

import Specifications.Group
import Symmetry.Opposite

%default total
%access export

infixl 8 #

||| cancel two factors in a product of three
groupCancel1 : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  (inv a # a) # b = b
groupCancel1 spec a b = o2 === o3 where
  o1 : inv a # a = e
  o1 = inverseL spec a
  o2 : (inv a # a) # b = e # b
  o2 = cong {f = (# b)} o1
  o3 : e # b = b
  o3 = neutralL (monoid spec) b

||| cancel two factors in a product of three
groupCancel1bis : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  inv a # (a # b) = b
groupCancel1bis spec a b = assoc === groupCancel1 spec a b where
  assoc : inv a # (a # b) = (inv a # a) # b
  assoc = associative (monoid spec) _ _ _

||| cancel two factors in a product of three
groupCancel2 : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  a # (inv b # b) = a
groupCancel2 spec a b = o2 === o3 where
  o1 : inv b # b = e
  o1 = inverseL spec b
  o2 : a # (inv b # b) = a # e
  o2 = cong o1
  o3 : a # e = a
  o3 = neutralR (monoid spec) a

||| cancel two factors in a product of three
groupCancel2bis : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  (a # inv b) # b = a
groupCancel2bis spec a b = assoc @== groupCancel2 spec a b where
  assoc : a # (inv b # b) = (a # inv b) # b
  assoc = associative (monoid spec) _ _ _

||| cancel two factors in a product of three
groupCancel3 : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  a # (b # inv b) = a
groupCancel3 spec a b = groupCancel1 (opposite spec) b a

||| cancel two factors in a product of three
groupCancel3bis : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  (a # b) # inv b = a
groupCancel3bis spec a b = groupCancel1bis (opposite spec) b a

||| cancel two factors in a product of three
groupCancelAbelian : {(#) : Binop s} ->
  GroupSpec (#) e inv -> isAbelian (#) -> (a,b : s) ->
    a # (b # inv a) = b
groupCancelAbelian spec abel a b = abel a _ === o1 where
  o1 : (b # inv a) # a = b
  o1 = groupCancel2bis spec b a

||| Translations are injective.
groupTranslationInjectiveL : {(#) : Binop s} ->
  GroupSpec (#) e inv -> (a,x,y : s) -> a # x = a # y -> x = y
groupTranslationInjectiveL spec a x y given = o2 where
  o1 : inv a # (a # x) = inv a # (a # y)
  o1 = cong given
  o2 : x = y
  o2 = groupCancel1bis spec a x @== o1 === groupCancel1bis spec a y

||| ab = a implies b = e 
groupCancelGivesNeutral : {(#) : Binop s} ->
  GroupSpec (#) e inv -> (a,b : s) ->
    a # b = a -> b = e
groupCancelGivesNeutral spec a b given = o2 === inverseL spec a where
  o1 : inv a # (a # b) = inv a # a
  o1 = cong given
  o2 : b = inv a # a
  o2 = groupCancel1bis spec a b @== o1
