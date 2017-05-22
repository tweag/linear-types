Roadmap towards full integration of linear types in GHC
=======================================================

This document outlines the roadmap for integrating linear types in
GHC. It is laid out in stages which we intend to be successive merge
points into the GHC tree. The _miscellaneous_ section contains issues
which are parallel to the stages.

The roadmap contains concrete implementation actions as well as more
open discussion that needs to be better understood. The _remarks_
section does not contain action, rather items that will eventually be
documented.

Stage 1: mvp
------------

The first iteration implements implements linear types purely in the
type inference (no modification to core or its linter), and has
monomorphic multiplicities

- [x] Expand the representation of types to accommodate linearity.
- [x] Keep track of linearity in equation binders
- [x] Constructors are linear by default
- [x] Wildcard patterns rejected in the linear case
- [x] Constructors support unrestricted argument (`Unrestricted`)
- [ ] Disallow lazy pattern matching of linear data
- [ ] Make linear let/where-bindings available
- [ ] Handle linearity in pattern synonyms
- [ ] Full justification for memory-safety in presence of exceptions
- [ ] Syntax
    - [ ] Syntax for multiplicity-annotated arrows. Options:
        - Mimic Latex and write `a ->_l b` (currently used in this
          roadmap, but this is no suggestion that this is the one to
          be favoured)
        - Edsko de Vries [proposes][edsko-blog] `a ->:l b` (with `l` a
          multiplicity)
        - …
    - [ ] Do we need an ASCII short-hand for linear arrow `a ->_1 b`
         (Unicode has `⊸` which is the standard notation for the
         linear arrow)? Many proposals seen so far:
        - Currently illegal: `-o`
        - Currently legal (but wrong precedence): `-.`, `-*`, `-:`, `->.`
- [ ] Turn into proper extension

Stage 2: multiplicity polymorphism
----------------------------------

- [ ] Extend multiplicity expressions with variables (including
      equality, order, and supremum)
- [ ] Extend unification with multiplicities (otherwise explicit
      multiplicity applications are necessary). This probably implies
      some degree of AC unification.
- [ ] Allow data types and type classes parametrised with
      multiplicities
      - [ ] Probably requires kind for multiplicity arguments.

Stage 3: Core linter
--------------------

This stage is concerned with checking linearity constraints in
Core. There is no existing program transformation, to the best of our
knowledge, which becomes incorrect if linearity constraints are
ignored. But having the linter work with linearity would help ensure
that. It would also make it possible to enable further program
transformation or refine existing analyses, by taking advantage of
linear types.

- [x] Strictness

  There are some cases where strictness of function might affect
  typability with linear types in way it does not for unrestricted
  types.

  ```haskell
  f :: Unrestricted a -> B -- @f@ has an unrestricted arrow

  u :: Unrestricted a -o B
  u x = f $ case x of Unrestricted y -> Unrestricted y  -- doesn't typecheck
  u x = case x of Unrestricted y -> f (Unrestricted y) -- typechecks
  ```

  The latter definition for `u` typechecks whereas the former does
  not. This sort of issue does not appear without linearity.

  It boils down to the definition of consuming an `Unrestricted a`
  exactly once, which is: force the head constructor. If `f` is
  strict, both definitions are correct (as they are equivalent) and
  will consume the argument of `u` exactly once (if the application is
  consumed exactly once). But if `f` is not strict, say it is of the
  form `f _ = B` (for `B::B`), then the ill-typed definition does not
  consume its argument, and is rightly rejected.

  The current type system does not have an understanding of
  strictness, and acts, conservatively, as if every function was
  lazy. Representing strictness in the type system is an open problem.

  This could be an issue in principle as equivalent programs which are
  both typable if we erase multiplicities, do not both type under
  linearity.

  However, it seems that GHC only implements transformations from the
  shape of the ill-typed `u` to the typed `u`. That is, GHC
  optimisation go in the direction of increased typability. So this
  should not be a problem.
- [ ] How would
  ```haskell
  newtype Unrestricted a where a -> Unrestricted a
  ```
  be typed in Core?

  Specifically
  ```haskell
  case v of Unrestricted x -> f x
  ```
  would be translated, in core, as:
  ```haskell
  let x = v in f (x |> g @a)
  g a :: a ~ Unrestricted a
  ```
  In the core form, it is not clear how to keep track of linearity. In
  this example, the coercion changes the linearity of `x`, which is
  linear when `v` is linear, while `(x |> g @a)` must be
  unrestricted. Operationally, we are allowed to return an
  `Unrestricted a` (when defined as a `newtype`) only if we can be
  sure that there are no linear variable in its thunk (if there are
  linear variables, then we need a `data` version, so that forcing
  with a case will consume the variables in the thunk). So,
  effectively any linear variable of type `Unrestricted a` can be
  promoted to being unrestricted. Do we need a special type of
  coercion to do that?

Miscellaneous
-------------

### Monads ###

Linear types induce several flavour of monads depending on the
linearity constraints on the different arrows.

For instance, consider the following, fully linear, variant:

```haskell
class LMonad (m:*->*) where
  lreturn :: a ⊸ m a
  lbind   :: m a ⊸ (a ⊸ m b) ⊸ m b
```

The list monad is not a monad in this sense, because it uses the
continuation `a ⊸ m b` several times (or none at all in the case of
the empty list), so the last arrow must be unrestricted (`(->)`).

On the user side, it is having the continuation be of linear type `a
⊸ m b` which is restrictive. With an `LMonad`, we cannot write the
perfectly reasonable:

```haskell
foo `lbind` \a -> return (a,a)
```

On the other hand, it is a common pattern to have an implementation
of both `Monad m` and `LMonad m` but `m a ⊸ (a->m b) ⊸ m b` has no
meaningful inhabitant (_e.g._ for `m = Reader e`).

See also [_The best of both worlds_, Garrett Morris][best-of-both-worlds]
§3.3.

There is always a way to intersperse linear actions with monads using
a linear continuation-passing style: that is with linear actions
having type `(a⊸m())⊸m()`. This has the advantage of being very
systematic, and also having a built-in notion of duality (that is when
`a` is of the form `a₀⊸m()`, the dual of `a` is `a⊸m()`) which is
convenient for protocol-like applications.

Using continuation-passing style has costs: cps computations are
necessarily fully sequentialised (which we can observe as the fact
that there is no non-trivial `Applicative` instance for `Cont r`).

- [ ] Define a polymorphic notion of monad-with-multiplicities (and
  corresponding functor and applicative). Maybe:

  ```haskell
  class MMonad l0 l1 l2 l3 m where
    return :: a ->_l0 m a
    bind   :: m a ->_l1 (a ->_l2 m b) ->_l3 m c
  ```

  For instance `Reader e` implements `MMonad 1 l l 1`.

  This depends on multiplicity polymorphism being implemented.

    - [ ] Probably make opt-in using rebindable syntax

- [ ] `IO` must be compatible with linear and non-linear action (to be
  able to return linear handles to files, for instance).

  Define `IO l` with
  ```haskell
  return :: a ->_l IO l a
  bind   :: IO l a ⊸ (a ->_l IO l' a) ⊸ IO l' a
  ```

  Remark that `IO l` is an indexed monad, which makes it possible
  to intermingle linear actions with unrestricted action.

    - [ ] Generalise `MMonad` to _indexed_ monad with multiplicities?
          This still ought to work with rebindable syntax
    - [ ] IO is defined with unboxed pairs `(# RealWorld,
          a#)`. Keeping an unboxed representation is probably very
          important for efficiency, do we need a notion of unboxed
          pairs with multiplicities to implement `IO l`? Or can we
          used an unboxed `Unrestricted` (in other words: can
          `Unrestricted` be a `newtype`)?

### Error messages ###

- [ ] Currently errors are reported at the site where the binder is
  introduced, and one has to fish up duplicates of linear binders
  in their definition (except for wildcards violating linearity,
  which raise an error at their own location).

  Maybe it is better to try and raise, as an optimisation, errors
  at erroneous-duplication locations (this would allow to pinpoint
  faulty branches in `case` more easily for instance).

Remarks
-------

- The `seq` function, which forces its first argument and returns the
  second, does not consume its first argument (_e.g._ if the first
  argument is a pair `p`, ``p `seq` x`` will force the head of the
  pair into `(x,y)` but will neither consume `x` nor `y`).

  Therefore the first argument of `seq` cannot be linear, and the more
  general type for `seq` would be:

  ```haskell
  seq :: a -> b ⊸ b
  ```

    - On the other hand, `deepSeq` (See [Control.DeepSeq][DeepSeq])
      forces recursively its first argument, so we can expect

      ```haskell
      deepSeq :: NFData a => a ⊸ b ⊸ b
      ```

      to be a valid type,

      In fact, though this needs to be investigated, it may be that
      giving the type `a ⊸ ()` to `rnf` (instead of `a->()`) would
      enforce the intended semantics of the `NFData` class (except for
      types with unrestricted arguments, such as `Unrestricted`, but
      maybe it is ok).
- Scoped continuation vs source of linearity: there are two ways to
  introduce a linear variables. Either one can use a scoped
  continuation. This is the way which has been used the most in the
  writings in this repository:
  ```haskell
  withFile :: Path -> (FD ⊸ IO a) ⊸ IO a
  ```
  It delimits the scope of linear variables, but it also imposes to
  leave return addresses on the stack, so we can have only so many of
  these opened at the same time.

  An alternative, possibly more idiomatic, is to use a source of
  linearity: if I already have a linear variable (say `World`) I can
  produce new linear variables from it:
  ```haskell
  withFile :: World ⊸ Path -> (World, FD)
  ```
  It may end up being the better strategy.

[best-of-both-worlds]: http://doi.acm.org/10.1145/2951913.2951925
[DeepSeq]: https://www.stackage.org/haddock/lts-8.6/deepseq-1.4.2.0/Control-DeepSeq.html
[edsko-blog]: http://edsko.net/2017/01/08/linearity-in-haskell/
<!--  LocalWords:  monads Roadmap polymorphism monad sequentialised
 -->
<!--  LocalWords:  monomorphic Wildcard roadmap supremum parametrised
 -->
<!--  LocalWords:  linter typability typable wildcards
 -->
