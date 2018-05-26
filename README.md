# Composable algebraic specifications
 
This Idris package aims to provide:

* Composable specifications for basic algebraic and relational
  properties: associative and distributive laws, identity and inverse,
  translation invariance &mdash; just to name a few.

* A library of standard compositions of the above, defining the usual
  suspects: groups, rings, ordered groups, etc.

* A library of lemmas, theorems, proofs and examples.

The goal is not to prove classic mathematical theorems.  We want this
to support partially verified computation in Idris.  What this means
is best illustrated with a short
[example](https://github.com/jeroennoels/verified-algebra/blob/master/src/Applications/Example.idr):

```idris
absoluteValue : (AdditiveGroup s, Decidable [s,s] leq) =>
  OrderedGroupSpec (+) Zero Neg leq -> s -> (a ** leq Zero a)
absoluteValue spec x =
  case decision {rel = leq} x Zero of
    Yes prf => (Neg x ** invertNegative (partiallyOrderedGroup spec) x prf)
    No contra =>
        let (positive, _) = orderContra (totalOrder spec) x Zero contra
        in (x ** positive)
```