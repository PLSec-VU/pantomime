# Pantomime

`Pantomime` is a full-path symbolic execution engine for `GHC` Core—the internal language of `GHC`, which is based on System FC. `Pantomime` is a `GHC` Core plugin, which verifies validity of a boolean statement, given an annotation, as shown below.

```haskell
{-# OPTIONS_GHC "-fplugin Pantomime" #-}
{-# LANGUAGE DataKinds #-}

module Example.Module (example) where

import Data.Bits (Bits (..))
import Pantomime (Theory (..))
import qualified Pantomime.BuiltIn as Pantomime

{-# ANN example (Theory mempty) #-}
example :: Pantomime.BitVec 32 -> Pantomime.BitVec 32 -> Pantomime.Bool
example x y = Pantomime.boolean $
  complement x .&. complement y == complement $ x .|. y
```

In this case, `Pantomime` shows validity of the statement, quantified over all pairs of bitvectors of size 32.

**NOTE**: The value supplied to `Theory` is extremely important in most real-world scenarios. An explanation can be found in section [Embeddings](#embeddings).

## Getting Started

See the [installation instructions](./INSTALL.md) on how to install `Pantomime` and its dependencies.

## Documentation

As of writing, this package is not hosted on `Hackage` and thus we do not host the documentation somewhere. We recommend building the documentation through haddock from your own project until we resolve this. Sorry!

## Annotation

With this, `GHC` will run `Pantomime` on any expression that has an annotation with the `Theory` type, that returns an argument of type `Pantomime.Bool` when saturated:

```haskell
{-# ANN expr (Theory mempty) #-}
expr :: ... -> Pantomime.Bool
```

**PITFALL**: `Pantomime` will only run for expressions that are in the export list of the encapsulating module. Hopefully, we can remove this quirk in the future!

`Pantomime` will run when `GHC` compiles the program. If the annotated formula is not valid, `Pantomime` will throw an error and display the arguments that were used to get `False` as a result.

## Built-In Types

`Pantomime` support the following SMT Theories:

- Theory of Bitvectors
- Theory of Integers
- Theory of Arrays

These data types and their functions are regarded as primitives and are exported from `Pantomime.BuiltIn`, along with the `Bool` primitive.

## Embeddings

Pantomime directly supports computation on Algebraic Data Types. For example, we can check a function that uses `Maybe` and `Bool` as exported by `base`:

```haskell
-- NOTE: This will return a counterexample to validity when run.
{-# ANN example (Theory mempty) #-}
example :: Maybe Bool -> Pantomime.Bool
example x = Pantomime.boolean $ x == Just False
```

For types that are not algebraic, `Pantomime` exposes an interface to interpret them as SMT solver primitives. For example, the `Int64#` type and its operation `plusInt64#` have a natural embedding with the SMT primitive `BitVec 64` and its respective addition operation. In Pantomime, the user can directly encode this mapping within the annotation:

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

```haskell
{-# ANN example (Theory Pantomime.Base.axioms) #-}
example :: ... -> Pantomime.Bool
```

TODO: Writing mappings is a bit more involved, we should have some separate document where we go more in depth. There are whole lot of pitfalls...
TODO: Add explanation in the pantomime-clash and pantomime-base repositories.
TODO: Extend explanation on PluginAxiom (at least that its a monoid and how it imports and what order).
TODO: I would actually like to move most of the explanation here into the project documentation. I think it only makes sense once we have a haddock page for it however.
