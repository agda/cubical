{-
This module provides essential definitions and the necessary machinery to enable syntactic sugar for monads and applicatives with instances. The content is split into two main submodules:

1. **Base**: Contains fundamental definitions that only depend on `Agda.Primitive`, ensuring no dependencies on the Cubical library. This makes it universally usable across the library.
2. **Instances**: Provides instances of the defined classes for various entities from the Cubical library.

The organization of this module emphasizes their utility as helper definitions for writing code and macros, rather than for formal reasoning about their categorical nature.
-}

{-# OPTIONS --safe #-}
module Cubical.Reflection.Sugar where

open import Cubical.Reflection.Sugar.Base public
open import Cubical.Reflection.Sugar.Instances public
