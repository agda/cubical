{-

  Functions building UARels and DUARels on propositions / propositional families

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Displayed.Prop where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Displayed.Base

private
  variable
    ℓA ℓ≅A ℓB ℓ≅B ℓP : Level

𝒮-prop : (P : hProp ℓP) → UARel (P .fst) ℓ-zero
𝒮-prop P .UARel._≅_ _ _ = Unit
𝒮-prop P .UARel.ua _ _ =
  invEquiv (isContr→≃Unit (isOfHLevelPath' 0 (P .snd) _ _))

𝒮ᴰ-prop : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) (P : A → hProp ℓP)
  → DUARel 𝒮-A (λ a → P a .fst) ℓ-zero
𝒮ᴰ-prop 𝒮-A P .DUARel._≅ᴰ⟨_⟩_ _ _ _ = Unit
𝒮ᴰ-prop 𝒮-A P .DUARel.uaᴰ _ _ _ =
  invEquiv (isContr→≃Unit (isOfHLevelPathP' 0 (P _ .snd) _ _))

𝒮-subtype : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) (P : A → hProp ℓP)
  → UARel (Σ A (fst ∘ P)) ℓ≅A
𝒮-subtype 𝒮-A P .UARel._≅_ (a , _) (a' , _) = 𝒮-A .UARel._≅_ a a'
𝒮-subtype 𝒮-A P .UARel.ua (a , _) (a' , _) =
  compEquiv (𝒮-A .UARel.ua a a') (Σ≡PropEquiv (snd ∘ P))

𝒮ᴰ-subtype : {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  (P : (a : A) → B a → hProp ℓP)
  → DUARel 𝒮-A (λ a → Σ[ b ∈ B a ] (P a b .fst)) ℓ≅B
𝒮ᴰ-subtype 𝒮ᴰ-B P .DUARel._≅ᴰ⟨_⟩_ (b , _) p (b' , _) = 𝒮ᴰ-B .DUARel._≅ᴰ⟨_⟩_ b p b'
𝒮ᴰ-subtype 𝒮ᴰ-B P .DUARel.uaᴰ (b , _) p (b' , _) =
  compEquiv
    (𝒮ᴰ-B .DUARel.uaᴰ b p b')
    (compEquiv
      (invEquiv (Σ-contractSnd λ _ → isOfHLevelPathP' 0 (P _ b' .snd) _ _))
      ΣPath≃PathΣ)
