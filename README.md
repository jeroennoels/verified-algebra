# Composable algebraic specifications
 
This Idris package aims to provide:

* Composable specifications for basic algebraic and relational
  properties: associative and distributive laws, identity and inverse,
  translation invariance &mdash; just to name a few.

* A library of standard compositions of the above, defining the usual
  suspects: groups, rings, ordered groups, etc.

* A library of lemmas, theorems, proofs and examples.

The goal is not to prove classic mathematical theorems.  We prove
theorems to support partially verified computation in Idris.  What
this means is best illustrated with a short
[example](https://github.com/jeroennoels/verified-algebra/blob/master/src/Applications/Example.idr):

```idris
||| A clean notation that plays nicely with implicit binding:
interface Neg s => Ringops s where
  Ng : s -> s
  Zero : s
  One : s
  Ng = negate
  Zero = fromInteger 0
  One = fromInteger 1

||| OrderedGroupSpec is a dependent type that requires its 4 parameters
||| to satisfy the laws of an ordered group.  We compute the absolute
||| value of an element and return it, along with a proof that the result
||| is non-negative.

absoluteValue : (Ringops s, Decidable [s,s] leq) =>
  .OrderedGroupSpec (+) Zero Ng leq -> s -> (a ** leq Zero a)
absoluteValue spec x =
  case decision {rel = leq} x Zero of
    Yes prf => (Ng x ** invertNegative (partiallyOrderedGroup spec) x prf)
    No contra =>
        let (positive, _) = orderContra (totalOrder spec) x Zero contra
        in (x ** positive)
```

The type `s` above could for instance be `Integer` with a _postulated_ `OrderedGroupSpec`.  Or it could also be `Data.ZZ` with an explicitly constructed specification proof term.  Or any other ordered group structure.

A more interesting example aims at partially verified
[exact real arithmetic](https://github.com/jeroennoels/verified-exact-real).
