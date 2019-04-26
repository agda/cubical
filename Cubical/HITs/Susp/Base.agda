{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Susp.Base where

open import Cubical.Core.Glue

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool

open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3

data Susp {ℓ} (A : Type ℓ) : Type ℓ where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south

SuspBool : Type₀
SuspBool = Susp Bool

SuspBool→S¹ : SuspBool → S¹
SuspBool→S¹ north = base
SuspBool→S¹ south = base
SuspBool→S¹ (merid false i) = loop i
SuspBool→S¹ (merid true i)  = base

S¹→SuspBool : S¹ → SuspBool
S¹→SuspBool base     = north
S¹→SuspBool (loop i) = (merid false ∙ (sym (merid true))) i

SuspBool→S¹→SuspBool : (x : SuspBool) → Path _ (S¹→SuspBool (SuspBool→S¹ x)) x
SuspBool→S¹→SuspBool north = refl
SuspBool→S¹→SuspBool south = merid true
SuspBool→S¹→SuspBool (merid false i) = λ j → hcomp (λ k → (λ { (j = i1) → merid false i
                                                             ; (i = i0) → north
                                                             ; (i = i1) → merid true (j ∨ ~ k)}))
                                                   (merid false i)
SuspBool→S¹→SuspBool (merid true i)  = λ j → merid true (i ∧ j)

S¹→SuspBool→S¹ : (x : S¹) → SuspBool→S¹ (S¹→SuspBool x) ≡ x
S¹→SuspBool→S¹ base     = refl
S¹→SuspBool→S¹ (loop i) = λ j →
  hfill (λ k → \ { (i = i0) → base; (i = i1) → base }) (inS (loop i)) (~ j)

S¹≃SuspBool : S¹ ≃ SuspBool
S¹≃SuspBool = isoToEquiv (iso S¹→SuspBool SuspBool→S¹ SuspBool→S¹→SuspBool S¹→SuspBool→S¹)

S¹≡SuspBool : S¹ ≡ SuspBool
S¹≡SuspBool = isoToPath (iso S¹→SuspBool SuspBool→S¹ SuspBool→S¹→SuspBool S¹→SuspBool→S¹)

-- Now the sphere

SuspS¹ : Type₀
SuspS¹ = Susp S¹

SuspS¹→S² : SuspS¹ → S²
SuspS¹→S² north = base
SuspS¹→S² south = base
SuspS¹→S² (merid base i) = base
SuspS¹→S² (merid (loop j) i) = (surf i j)

meridian-contraction : I → I → I → SuspS¹
meridian-contraction i j l = hfill (λ k → λ { (i = i0) → north
                              ; (i = i1) → merid base (~ k)
                              ; (j = i0) → merid base (~ k ∧ i)
                              ; (j = i1) → merid base (~ k ∧ i) })
                     (inS (merid (loop j) i)) l

S²→SuspS¹ : S² → SuspS¹
S²→SuspS¹ base = north
S²→SuspS¹ (surf i j) = meridian-contraction i j i1

S²→SuspS¹→S² : ∀ x → SuspS¹→S² (S²→SuspS¹ x) ≡ x
S²→SuspS¹→S² base k = base
S²→SuspS¹→S² (surf i j) k = SuspS¹→S² (meridian-contraction i j (~ k))

SuspS¹→S²→SuspS¹ : ∀ x → S²→SuspS¹ (SuspS¹→S² x) ≡ x
SuspS¹→S²→SuspS¹ north k = north
SuspS¹→S²→SuspS¹ south k = merid base k
SuspS¹→S²→SuspS¹ (merid base j) k = merid base (k ∧ j)
SuspS¹→S²→SuspS¹ (merid (loop j) i) k = meridian-contraction i j (~ k)

S²≡SuspS¹ : S² ≡ SuspS¹
S²≡SuspS¹ = isoToPath (iso S²→SuspS¹ SuspS¹→S² SuspS¹→S²→SuspS¹ S²→SuspS¹→S²)

-- And the 3-sphere

SuspS² : Type₀
SuspS² = Susp S²

SuspS²→S³ : SuspS² → S³
SuspS²→S³ north = base
SuspS²→S³ south = base
SuspS²→S³ (merid base i) = base
SuspS²→S³ (merid (surf j k) i) = surf i j k

meridian-contraction-2 : I → I → I → I → SuspS²
meridian-contraction-2 i j k l = hfill (λ m → λ { (i = i0) → north
                                                ; (i = i1) → merid base (~ m)
                                                ; (j = i0) → merid base (~ m ∧ i)
                                                ; (j = i1) → merid base (~ m ∧ i)
                                                ; (k = i0) → merid base (~ m ∧ i)
                                                ; (k = i1) → merid base (~ m ∧ i) })
                                     (inS (merid (surf j k) i)) l

S³→SuspS² : S³ → SuspS²
S³→SuspS² base = north
S³→SuspS² (surf i j k) = meridian-contraction-2 i j k i1

S³→SuspS²→S³ : ∀ x → SuspS²→S³ (S³→SuspS² x) ≡ x
S³→SuspS²→S³ base l = base
S³→SuspS²→S³ (surf i j k) l = SuspS²→S³ (meridian-contraction-2 i j k (~ l))

SuspS²→S³→SuspS² : ∀ x → S³→SuspS² (SuspS²→S³ x) ≡ x
SuspS²→S³→SuspS² north l = north
SuspS²→S³→SuspS² south l = merid base l
SuspS²→S³→SuspS² (merid base j) l = merid base (l ∧ j)
SuspS²→S³→SuspS² (merid (surf j k) i) l = meridian-contraction-2 i j k (~ l)

S³≡SuspS² : S³ ≡ SuspS²
S³≡SuspS² = isoToPath (iso S³→SuspS² SuspS²→S³ SuspS²→S³→SuspS² S³→SuspS²→S³)
