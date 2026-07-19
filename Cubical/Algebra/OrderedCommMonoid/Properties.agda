module Cubical.Algebra.OrderedCommMonoid.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP using (TypeWithStr)

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.OrderedCommMonoid.Base

open import Cubical.Relation.Binary.Order.Poset


private
  variable
    ℓ ℓ' ℓ'' : Level


module _
    (M : OrderedCommMonoid ℓ ℓ')
    (P : ⟨ M ⟩ → hProp ℓ'')
    where
  open OrderedCommMonoidStr (snd M)
  module _
    (·Closed : (x y : ⟨ M ⟩) → ⟨ P x ⟩ → ⟨ P y ⟩ → ⟨ P (x · y) ⟩)
    (εContained : ⟨ P ε ⟩)
    where
    private
      subtype = Σ[ x ∈ ⟨ M ⟩ ] ⟨ P x ⟩
      submonoid =  makeSubCommMonoid (OrderedCommMonoid→CommMonoid M) P ·Closed εContained
      _≤ₛ_ : (x y : ⟨ submonoid ⟩) → Type ℓ'
      x ≤ₛ y = (fst x) ≤ (fst y)
      pres≤ : (x y : ⟨ submonoid ⟩) (x≤y : x ≤ₛ y) → (fst x) ≤ (fst y)
      pres≤ x y x≤y = x≤y

    makeOrderedSubmonoid : OrderedCommMonoid _ ℓ'
    fst makeOrderedSubmonoid = subtype
    OrderedCommMonoidStr._≤_ (snd makeOrderedSubmonoid) = _≤ₛ_
    OrderedCommMonoidStr._·_ (snd makeOrderedSubmonoid) = CommMonoidStr._·_ (snd submonoid)
    OrderedCommMonoidStr.ε (snd makeOrderedSubmonoid) = CommMonoidStr.ε (snd submonoid)
    OrderedCommMonoidStr.isOrderedCommMonoid (snd makeOrderedSubmonoid) =
      IsOrderedCommMonoidFromIsCommMonoid
        (CommMonoidStr.isCommMonoid (snd submonoid))
        (λ x y → is-prop-valued (fst x) (fst y))
        (λ x → is-refl (fst x))
        (λ x y z → is-trans (fst x) (fst y) (fst z))
        (λ x y x≤y y≤x
          → Σ≡Prop (λ x → snd (P x))
                   (is-antisym (fst x) (fst y) (pres≤ x y x≤y) (pres≤ y x y≤x)))
        (λ x y z x≤y → MonotoneR (pres≤ x y x≤y))
        λ x y z x≤y → MonotoneL (pres≤ x y x≤y)
