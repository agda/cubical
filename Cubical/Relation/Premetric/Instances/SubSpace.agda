module Cubical.Relation.Premetric.Instances.SubSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Rationals.Positive
open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings

open PremetricStr
open PremetricTheory

private
  variable
    ℓA ℓB ℓM ℓM' ℓ' : Level

module SubSpace↪
  (M : PremetricSpace ℓM ℓM')
  {A : Type ℓA} (isSetA : isSet A)
  (ι : A → ⟨ M ⟩) (ι-injective : ∀ x y → ι x ≡ ι y → x ≡ y)
  where

  private module M = PremetricStr (snd M)

  open IsPremetric
  open IsIsometry
  open IsNonExpansive

  infix 5 _≈↪[_]_
  _≈↪[_]_ : A → ℚ₊ → A → Type ℓM'
  x ≈↪[ ε ] y = ι x M.≈[ ε ] ι y

  isPremetric↪ : IsPremetric _≈↪[_]_
  isPremetric↪ .is-set        = isSetA
  isPremetric↪ .isProp≈       = λ _ _   → M.isProp≈ _ _
  isPremetric↪ .isRefl≈       = λ _     → M.isRefl≈ _
  isPremetric↪ .isSym≈        = λ _ _   → M.isSym≈ _ _
  isPremetric↪ .isSeparated≈  = λ _ _   → ι-injective _ _ ∘ M.isSeparated≈ _ _
  isPremetric↪ .isTriangular≈ = λ _ _ _ → M.isTriangular≈ _ _ _
  isPremetric↪ .isRounded≈    = λ _ _   → M.isRounded≈ _ _

  ↪PremetricSpace : PremetricSpace ℓA ℓM'
  fst ↪PremetricSpace = A
  _≈[_]_      (snd ↪PremetricSpace) = _≈↪[_]_
  isPremetric (snd ↪PremetricSpace) = isPremetric↪

  ι↪ᴵ : Isometry[ ↪PremetricSpace , M ]
  fst ι↪ᴵ         = ι
  pres≈ (snd ι↪ᴵ) = λ _ _ _ → idEquiv _

  ι↪ⁿ : NE[ ↪PremetricSpace , M ]
  fst ι↪ⁿ         = ι
  pres≈ (snd ι↪ⁿ) = λ _ _ _ → idfun _

  ι↪ᶜ : C[ ↪PremetricSpace , M ]
  ι↪ᶜ = NE→C ι↪ⁿ

  ι↪ᵘᶜ : UC[ ↪PremetricSpace , M ]
  ι↪ᵘᶜ = NE→UC ι↪ⁿ

  ι↪ᴸ : L[ ↪PremetricSpace , M ]
  ι↪ᴸ = NE→L ι↪ⁿ

  lim↪→isComplete : (M-com : isComplete M) → (∀ x xs → fiber ι (M-com (ι ∘ x) xs .fst))
                   → isComplete ↪PremetricSpace
  fst (lim↪→isComplete M-com lim↪ x xs) = fst (lim↪ x xs)
  snd (lim↪→isComplete M-com lim↪ x xs) =
    ((subst≈R M $ sym $ lim↪ x xs .snd) ∘_) ∘ M-com (ι ∘ x) xs .snd

module SubSpace (M : PremetricSpace ℓM ℓM')
  (P : ⟨ M ⟩ → Type ℓ') (is-prop-valued : ∀ x → isProp (P x))
  where

  private
    open module S = SubSpace↪ M (isSetΣSndProp (M .snd .is-set) is-prop-valued)
      fst (λ _ _ → Σ≡Prop is-prop-valued) public using () renaming (
        _≈↪[_]_ to _≈⊆[_]_
      ; isPremetric↪ to isPremetric⊆ ; ↪PremetricSpace to ⊆PremetricSpace
      ; ι↪ᴵ to ι⊆ᴵ ; ι↪ⁿ to ι⊆ⁿ ; ι↪ᴸ to ι⊆ᴸ ; ι↪ᶜ to ι⊆ᶜ ; ι↪ᵘᶜ to ι⊆ᵘᶜ)

  lim∈→isComplete : (M-com : isComplete M) → (∀ x xs → P (fst (M-com (fst ∘ x) xs)))
                  → isComplete ⊆PremetricSpace
  lim∈→isComplete M-com lim∈ = S.lim↪→isComplete M-com λ x xs → (_ , lim∈ x xs) , refl
