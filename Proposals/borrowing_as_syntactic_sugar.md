

[2016.12.16] {Simple syntactic sugar in lieu of borrowing}
==========================================================

In our last call we alluded to the idea of syntatic sugar in lieu of
"borrowing" in the type system.  This is still half baked, but the
below takes one step further on that idea.

## The problem

Is simply that folks will get tired of typing this:

```Haskell
  let a =_1 ...
      b =_1 ...
      (a',b',x,y) = f a b e
```

Too much naming of intermediate results!  Further, in Haskell we have
the minor syntactic quibble that while `do x <- f x` works for
intentional shadowing (rather than burning through names like `x'`,`x''`/`x1`,`x2` etc...), `let` is
recursive by default so you cannot choose to shadow, and thus cannot reuse the
`a`/`b` names above.


## Solution?

Can this problem be solved simply with sugar?  What if we have some
syntactic marker for which arguments to a function call are linear
arguments which are "borrowed"?  That is, they imply additional return
values in the same order as the arguments.  Let's say that these
additional return values are prepended to the regular return values in
a tuple.

Combined with some kind of do notation (say, with a different arrow),
this call syntax could hide the threading of linear arguments that are
updated.  For example this:

```Haskell
 do x,y <~ f &a e &b
    ...
```

Would expand to:


```Haskell
 do (a,b,x,y) <- f a e b
    ...
```

## Complications

The `x,y <~ f ...` syntax above really is one, mixfix syntactic
element.  Sadly, it doesn't seem as easy to do something like this:

```Haskell
 do x,y <~ if _ then f &a e &b
                else g &a &b e2
    ...
```

How would we know how many implicit arguments to attach in addition to
`x,y`?  And what to name them?  This goes beyond syntax, and would
need to get leak into the type system.  Nevertheless, one can always
fall back to spelling out the return values explicitly, possibly with
shadowing:

```Haskell
 do (a,b,x,y) <- if _ then f a e b
                      else g a b e2
    ...
```

