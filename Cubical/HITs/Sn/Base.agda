{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Sn.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Bool

open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3

S : ℕ → Type₀
S zero = Bool
S (suc n) = Susp (S n)

S¹≡S1 : S¹ ≡ S 1
S¹≡S1 = S¹≡SuspBool

S²≡S2 : S² ≡ S 2
S²≡S2 = S²≡SuspS¹ ∙ cong Susp S¹≡S1

S³≡S3 : S³ ≡ S 3
S³≡S3 = S³≡SuspS² ∙ cong Susp S²≡S2
