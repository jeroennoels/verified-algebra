This application is based on [exact real
arithmetic](https://wiki.haskell.org/Exact_real_arithmetic).  We
implement the addition of real numbers represented as an infinite
stream of symmetrically redundant digits.  The most remarkable feature
here is that you can start with the _most significant_ digits, and
then compute progressively more accurate results if desired.  To
explain what this means, we look at an example in radix `10`.

A real number between `-1` and `1` can be expressed as a stream of
digits in the _symmetric_ range `[-9..9]`.  Consider two numbers, say
`x` and `y`, expressed as such:

```
  x :      4   5  -7   0   9   1  ..     =>      4/10 + 5/100 - 7/1000 ..
  y :     -2   6  -7  -2   9   0  ..     =>    - 2/10 + 6/100 - 7/1000 ..
```

Just as in the usual decimal case, the interpretation is based on
powers of `10`.  The only difference is that we allow negative digits.
As a consequence, many different streams can represent the same real
number.  Now let us try to compute the sum of `x` and `y`.  We proceed
from left to right, adding pairs of equally significant digits from
both streams:

```
  x + y :  2  11 -14  -2  18   1  ..
```

That new stream consists of digits in `[-18..18]`.  We need to fit
these sums back into the original `[-9..9]` range.  Therefor we
reduce them modulo `10`, and track the differences:

```
           2   1  -4  -2   8   1  ..      reduced
           0  10 -10   0  10   0  ..      difference
       0   1  -1   0   1   0  ..          carry
```

Notice that we can always reduce `[-18..18]` into `[-8..8]` if we want
to.  It works precisely because we allow _negative_ digits: `9`
reduces to `-1`, so it cannot be made to fit into `[0..8]`.  This
observation is key.  Just as in ordinary arithmetic, we carry the
differences to the left.  The carry digit can be `-1`, `0` or `1`.

So why did we want to reduce summed digits into `[-8..8]` rather than
`[-9..9]`?  The point is, this offers exactly the necessary wiggle room
to absorb one carry.  Thus we always end up with a digit inside the
original `[-9..9]` range, carry included.  There is no cascade effect!

This allows us to _incrementally_ compute the sum of two real numbers,
i.e. processing digits from left to right, starting with the most
significant ones.  The above example used radix `10` because it is
familiar to everyone, but the same trick works for any radix `r >= 3`.
It does not work with binary representations though.
