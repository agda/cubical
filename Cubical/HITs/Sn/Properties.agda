{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Sn.Properties where

open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Bool
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.HITs.S1
open import Cubical.HITs.S3
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp
open import Cubical.Data.Unit
open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.PropositionalTruncation

open Iso

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

--- Some silly lemmas on S1 ---

isGroupoidS1 : isGroupoid (S₊ 1)
isGroupoidS1 = isGroupoidS¹

isConnectedS1 : (x : S₊ 1) → ∥ base ≡ x ∥
isConnectedS1 = isConnectedS¹
