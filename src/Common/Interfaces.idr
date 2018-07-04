||| This interface enables a clean additive and multiplicative
||| notation.  We add capitalized names because in this package,
||| implicit bounds are usually unwanted.
module Common.Interfaces

%default total
%access public export

||| This is a compromise.  We want the familiar notation (+ and *)
||| without introducing additional ambiguity.  That means extending
||| the existing numerical hierarchy.  But Num bundles additive with
||| multiplicative structure, whereas sometimes only one is relevant.
||| However the more interesting instances are rings anyway, so this
||| is not such a big deal.
interface Neg s => Ringops s where
  Ng : s -> s
  Zero : s
  One : s
  Ng = negate
  Zero = fromInteger 0
  One = fromInteger 1
