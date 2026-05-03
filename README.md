# Pantomime

`Pantomime` is a full-path symbolic execution engine for `GHC` Core—the internal
language of `GHC`, which is based on System FC. `Pantomime` is a `GHC` Core
plugin, which verifies validity of a boolean statement, given an annotation, as
shown below.

```haskell
import Pantomime (Theory (..))
import Pantomime.BuiltIn qualified as Pantomime

{-# ANN example (Theory mempty) #-}
example :: Pantomime.BitVec 32 -> Pantomime.Bool
example x = Pantomime.bveq (2 * x) (x + x)
```

In this case, `Pantomime` shows validity of the statement, quantified over all
bitvectors of size 32.

**NOTE**: The field supplied value to `Theory` is extremely important in most 
real-world scenarios. An explanation can be found in section
[Embeddings](#embeddings)

## Getting Started

### Dependency

Add `Pantomime` to your project's dependencies and enable the plugin.

- Example `.cabal` file, if using `Cabal` to build.
  ```yaml
  library
    ghc-options: -Wall -fplugin Pantomime 
    build-depends:
        base >=4.7 && <5
      , pantomime
  ```

- Example `package.yaml` file, if using `Stack` to build.
  ```yaml
  library:
    ghc-options:
    - -fplugin Pantomime
    dependencies:
    - base >= 4.7 && < 5
    - pantomime
  ```

Instead of globally enabling `Pantomime` through the package-wide `ghc-options`,
one can also enable it per module by adding a pragma at the top of the
respective modules:
```haskell
{-# OPTIONS_GHC "-fplugin Pantomime" #-}

module Main (main) where
```

### Solver

`Pantomime` assumes that the `Z3` SMT solver is installed and available from
your `PATH`. In the future, we aim to make the solver configurable.

### Annotation

With this, `GHC` will run `Pantomime` on any expression that has an annotation
with the `Theory` type, that returns an argument of type `Pantomime.Bool` when
saturated:

```haskell
{-# ANN expr (Theory mempty) #-}
expr :: ... -> Pantomime.Bool
```

**PITFALL**: `Pantomime` will only run for expressions that are in the export
list of the encapsulating module. Hopefully, we can remove this quirk in the
future!

`Pantomime` will run when `GHC` compiles the program. If the annotated formula
is not valid, `Pantomime` will throw an error and display the arguments that
were used to `False`.

## Built-In Types

`Pantomime` support the following SMT Theories:

- Theory of Bitvectors
- Theory of Integers
- Theory of Arrays

These data types and their functions are regarded as primitives and are
exported from `Pantomime.BuiltIn`, along with the `Bool` primitive.

Note that one can convert from `Haskell`'s normal `Bool` to
`Pantomime.Bool` as follows:

```haskell
example :: Bool -> Pantomime.Bool
example boolean = case boolean of
  True -> Pantomime.True
  False -> Pantomime.False
```

## Embeddings

Pantomime directly supports computation on Algebraic Data Types. For example, we
can check a function that uses `Maybe` and `Bool` as exported by `base`:

```haskell
-- NOTE: This will return a counterexample to validity when run.
{-# ANN example (Theory mempty) #-}
example :: Maybe Bool -> Pantomime.Bool
example x = case x == Just False of
  True -> Pantomime.True
  False -> Pantomime.False
```

For types that are not algebraic, `Pantomime` exposes an interface to interpret
them as SMT solver primitives. For example, the `Int64#` type and its operation
`plusInt64#` have a natural embedding with the SMT primitive `BitVec 64` and its
respective addition operation. In Pantomime, the user can directly encode this
mapping within the annotation:

```haskell
axioms :: PluginAxioms
axioms = PluginAxioms
  { typeAxioms = fromList [(''Int64#, ''Pantomime.BitVec 64)]
  , termAxioms = [('plusInt64#, 'Pantomime.bvadd)]
  }

{-# ANN example (Theory axioms) #-}
example :: ... -> Pantomime.Bool
```

For a reasonable mapping of `base`, check out
[`pantomime-base`](https://github.com/PLSec-VU/pantomime-base). We also provide
a mapping for `CLaSH` types and functions in
[`pantomime-clash`](https://github.com/PLSec-VU/pantomime-clash).

TODO: Writing mappings is a bit more involved, we should have some separate
document where we go more in depth. There are whole lot of pitfalls...
