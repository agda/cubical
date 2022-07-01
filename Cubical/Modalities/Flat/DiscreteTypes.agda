{-
  This files shows that a couple of types are crisply discrete,
  where 'discrete' should not be confused with types, that have
  decidable equality types (even though there are relations).
-}
{-# OPTIONS --safe #-}
module Cubical.Modalities.Flat.DiscreteTypes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Modalities.Flat

isCrisplyDiscrete : {@♭ ♭ℓ : Level}
                    → (@♭ A : Type ♭ℓ) → Type ♭ℓ
isCrisplyDiscrete A = isEquiv (counit {A = A})

isDiscreteUnit : isCrisplyDiscrete Unit
isDiscreteUnit = snd (isoToEquiv (iso counit inv linv rinv))
  where
    inv = λ {tt → tt ^♭}
    linv = λ {tt → refl}
    rinv = λ {(tt ^♭) → refl}

private
  counitInvℕ : ℕ → ♭ ℕ
  counitInvℕ zero = zero ^♭
  counitInvℕ (suc x) = ♭map suc (counitInvℕ x)

  linvℕ : (n : ℕ) → counit (counitInvℕ n) ≡ n
  linvℕ zero = refl
  linvℕ (suc x) =
         counit (counitInvℕ (suc x))    ≡⟨ ♭nat suc (counitInvℕ x) ⟩
         suc (counit (counitInvℕ x))    ≡⟨ cong suc (linvℕ x) ⟩
         suc x ∎

  rinvℕ : (n : ♭ ℕ) → counitInvℕ (counit n) ≡ n
  rinvℕ (zero ^♭) = refl
  rinvℕ (suc a ^♭) =
              ♭map suc (counitInvℕ a)  ≡⟨ cong (♭map suc) (rinvℕ (a ^♭)) ⟩
              suc a ^♭ ∎

isDiscreteℕ : isCrisplyDiscrete ℕ
isDiscreteℕ = snd (isoToEquiv (iso counit counitInvℕ linvℕ rinvℕ))

isDiscreteℤ : isCrisplyDiscrete ℤ
isDiscreteℤ = snd (isoToEquiv (iso counit inv linv rinv))
  where
    inv = λ { (pos n) → ♭map pos (counitInvℕ n) ;
              (negsuc n) → ♭map negsuc (counitInvℕ n)}
    linv = λ { (pos n) →
                 counit (inv (pos n))          ≡⟨ ♭nat pos (counitInvℕ n) ⟩
                 pos (counit (counitInvℕ n))   ≡⟨ cong pos (linvℕ n) ⟩
                 (pos n) ∎ ;
               (negsuc n) →
                 counit (inv (negsuc n))         ≡⟨ ♭nat negsuc (counitInvℕ n) ⟩
                 negsuc (counit (counitInvℕ n))  ≡⟨ cong negsuc (linvℕ n) ⟩
                 negsuc n ∎}
    rinv = λ { (pos n ^♭) → cong (♭map pos) (rinvℕ (n ^♭)) ;
               (negsuc n ^♭) → cong (♭map negsuc) (rinvℕ (n ^♭))}


{-
  From the article
  https://arxiv.org/pdf/1908.08034.pdf
  by David Jaz Myers
-}

{- Definition 5.7 (v4) -}
BAut : {ℓ : Level}
       → (X : Type ℓ) → X → Type ℓ
BAut X x = Σ[ y ∈ X ] ∥ y ≡ x ∥₁

♭BAut→BAut♭ : {@♭ ♭ℓ : Level}
            →  (@♭ X : Type ♭ℓ) (@♭ x : X)
            → ♭ (BAut X x) → BAut (♭ X) (x ^♭)
♭BAut→BAut♭ X x ((y , p) ^♭) = (y ^♭) ,
              crispPropRec PropTrunc.isPropPropTrunc f p
              where f : (@♭ p : _) → _
                    f p = ∣ fst (invEquiv (♭≡Comm y x)) (p ^♭) ∣₁
