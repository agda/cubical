
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Foundations.Filler where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

cube-cong : {a b : A}
            {p p' q q' : a ≡ b}
            (P : p ≡ p') (Q : q ≡ q')
            → (p ≡ q) ≡ (p' ≡ q')
cube-cong {p = p} {p' = p'} {q = q} {q' = q'} P Q =
  p ≡ q
    ≡⟨ cong (_≡ q) P ⟩
  p' ≡ q
    ≡⟨ cong (p' ≡_) Q ⟩
  p' ≡ q' ∎
