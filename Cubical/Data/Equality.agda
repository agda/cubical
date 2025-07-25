{-

This module converts between the path types and the inductively
defined equality types. It provides the following for the inductively
defined equality type _≡_.

- Basic theory for _≡_ (J, ap, transport, ...)

- A proof of function extensionality using _≡_

- A proof of univalence for _≡_ and equivalences using _≡_

- S¹ and propositional truncation with (path) constructors, eliminators
  and β rules all in terms of _≡_.

-}

module Cubical.Data.Equality where

open import Cubical.Data.Equality.Base public
open import Cubical.Data.Equality.Conversion public
open import Cubical.Data.Equality.FunctionExtensionality public
open import Cubical.Data.Equality.Univalence public
open import Cubical.Data.Equality.S1 public
open import Cubical.Data.Equality.PropositionalTruncation public
