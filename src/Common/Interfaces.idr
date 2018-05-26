||| These interfaces enable a clean additive or multiplicative
||| notation.  We use capitalized function names because in this
||| package, implicit bounds are usually unwanted.
module Common.Interfaces

%default total
%access public export

interface AdditiveGroup s where
  (+) : s -> s -> s
  Ng : s -> s
  Zero : s

interface Unital s where
  One : s

interface Multiplicative s where
  (*) : s -> s -> s
