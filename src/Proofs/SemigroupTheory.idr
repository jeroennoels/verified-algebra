module Proofs.SemigroupTheory

import Specifications.Semigroup

%default total
%access export

abelianCongruence : isAbelian op -> x = y -> op x a = op a y
abelianCongruence {a} {x} abel given = abel x a === cong given
