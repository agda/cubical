{-# OPTIONS --safe #-}

module Cubical.Data.Nat.Primes.Imports where

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Isomorphism public

open import Cubical.Data.Nat hiding (elim) public
open import Cubical.Data.Nat.Order public
open import Cubical.Data.Nat.Divisibility public
open import Cubical.Data.Empty as ⊥ hiding (elim) public
open import Cubical.Data.Unit public
open import Cubical.Data.Sigma public
open import Cubical.Data.List hiding (elim ; rec ; map) public
open import Cubical.Data.Sum hiding (elim ; rec ; map) public
open import Cubical.Relation.Nullary public
open import Cubical.HITs.PropositionalTruncation hiding (map2 ; rec) public
open import Cubical.Induction.WellFounded public
open import Cubical.Data.Fin hiding (elim) public
