{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.CommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.CommRing.Base

private
  variable
    ℓ : Level

module Units (R' : CommRing {ℓ}) where
 open CommRingStr (snd R')
 private R = R' .fst

 inverseUniqueness : (r : R) → isProp (Σ[ r' ∈ R ] r · r' ≡ 1r)
 inverseUniqueness r (r' , rr'≡1) (r'' , rr''≡1) = Σ≡Prop (λ _ → is-set _ _) path
  where
  path : r' ≡ r''
  path = r'             ≡⟨ sym (·-rid _) ⟩
         r' · 1r        ≡⟨ cong (r' ·_) (sym rr''≡1) ⟩
         r' · (r · r'') ≡⟨ ·-assoc _ _ _ ⟩
         (r' · r) · r'' ≡⟨ cong (_· r'') (·-comm _ _) ⟩
         (r · r') · r'' ≡⟨ cong (_· r'') rr'≡1 ⟩
         1r · r''       ≡⟨ ·-lid _ ⟩
         r''            ∎


 Rˣ : ℙ R
 Rˣ r = (Σ[ r' ∈ R ] r · r' ≡ 1r) , inverseUniqueness r

 -- some notation using instance arguments
 _⁻¹ : (r : R) → ⦃ r ∈ Rˣ ⦄ → R
 _⁻¹ r ⦃ r∈Rˣ ⦄ = r∈Rˣ .fst

 infix 9 _⁻¹

 -- some results about inverses
 ·-inv : (r : R) ⦃ r∈Rˣ : r ∈ Rˣ ⦄ → r · r ⁻¹ ≡ 1r
 ·-inv r ⦃ r∈Rˣ ⦄ = r∈Rˣ .snd

 RˣMultClosed : (r r' : R) ⦃ r∈Rˣ : r ∈ Rˣ ⦄ ⦃ r'∈Rˣ : r' ∈ Rˣ ⦄
              → (r · r') ∈ Rˣ
 RˣMultClosed r r' = (r ⁻¹ · r' ⁻¹) , path
  where
  path : r · r' · (r ⁻¹ · r' ⁻¹) ≡ 1r
  path = r · r' · (r ⁻¹ · r' ⁻¹) ≡⟨ cong (_· (r ⁻¹ · r' ⁻¹)) (·-comm _ _) ⟩
         r' · r · (r ⁻¹ · r' ⁻¹) ≡⟨ ·-assoc _ _ _ ⟩
         r' · r · r ⁻¹ · r' ⁻¹   ≡⟨ cong (_· r' ⁻¹) (sym (·-assoc _ _ _)) ⟩
         r' · (r · r ⁻¹) · r' ⁻¹ ≡⟨ cong (λ x → r' · x · r' ⁻¹) (·-inv _) ⟩
         r' · 1r · r' ⁻¹         ≡⟨ cong (_· r' ⁻¹) (·-rid _) ⟩
         r' · r' ⁻¹              ≡⟨ ·-inv _ ⟩
         1r ∎

 1∈Rˣ : 1r ∈ Rˣ
 1∈Rˣ = 1r , ·-lid _

 1⁻¹≡1 : ⦃ 1∈Rˣ' : 1r ∈ Rˣ ⦄ → 1r ⁻¹ ≡ 1r
 1⁻¹≡1 ⦃ 1∈Rˣ' ⦄ = (sym (·-lid _)) ∙ 1∈Rˣ' .snd

 ⁻¹-dist-· : (r r' : R) ⦃ r∈Rˣ : r ∈ Rˣ ⦄ ⦃ r'∈Rˣ : r' ∈ Rˣ ⦄ ⦃ rr'∈Rˣ : (r · r') ∈ Rˣ ⦄
           → (r · r') ⁻¹ ≡ r ⁻¹ · r' ⁻¹
 ⁻¹-dist-· r r' ⦃ r∈Rˣ ⦄ ⦃ r'∈Rˣ ⦄ ⦃ rr'∈Rˣ ⦄ = {!rr'∈Rˣ .snd!}

module Exponentiation (R' : CommRing {ℓ}) where
 open CommRingStr (snd R')
 private R = R' .fst

 -- introduce exponentiation
 _^_ : R → ℕ → R
 f ^ zero = 1r
 f ^ suc n = f · (f ^ n)

 infix 9 _^_

 -- and prove some laws
 ·-of-^-is-^-of-+ : (f : R) (m n : ℕ) → (f ^ m) · (f ^ n) ≡ f ^ (m +ℕ n)
 ·-of-^-is-^-of-+ f zero n = ·-lid _
 ·-of-^-is-^-of-+ f (suc m) n = sym (·-assoc _ _ _) ∙ cong (f ·_) (·-of-^-is-^-of-+ f m n)

 ^-ldist-· : (f g : R) (n : ℕ) → (f · g) ^ n ≡ (f ^ n) · (g ^ n)
 ^-ldist-· f g zero = sym (·-lid 1r)
 ^-ldist-· f g (suc n) = path
  where
  path : f · g · ((f · g) ^ n) ≡ f · (f ^ n) · (g · (g ^ n))
  path = f · g · ((f · g) ^ n)       ≡⟨ cong (f · g ·_) (^-ldist-· f g n) ⟩
         f · g · ((f ^ n) · (g ^ n)) ≡⟨ ·-assoc _ _ _ ⟩
         f · g · (f ^ n) · (g ^ n)   ≡⟨ cong (_· (g ^ n)) (sym (·-assoc _ _ _)) ⟩
         f · (g · (f ^ n)) · (g ^ n) ≡⟨ cong (λ r → (f · r) · (g ^ n)) (·-comm _ _) ⟩
         f · ((f ^ n) · g) · (g ^ n) ≡⟨ cong (_· (g ^ n)) (·-assoc _ _ _) ⟩
         f · (f ^ n) · g · (g ^ n)   ≡⟨ sym (·-assoc _ _ _) ⟩
         f · (f ^ n) · (g · (g ^ n)) ∎
