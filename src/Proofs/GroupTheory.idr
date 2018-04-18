module Proofs.GroupTheory

import Specifications.Group
import Proofs.GroupCancelationLemmas

%default total
%access export

infixl 8 #

groupUniqueInverse : {(#) : Binop s} -> GroupSpec (#) e inv -> (a,b : s) ->
  a # b = e -> inv a = b
groupUniqueInverse {e} spec a b given = sym o4 `trans` o3 where
  o1 : inv a # (a # b) = inv a # e
  o1 = cong given
  o2 : inv a # (a # b) = b
  o2 = groupCancel1bis spec a b
  o3 : inv a # e = b
  o3 = sym o1 `trans` o2
  o4 : inv a # e = inv a
  o4 = neutralR (monoid spec) _

