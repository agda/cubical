-- The category of elements of a functor to Set
module Cubical.Categories.Instances.Elements where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Opposite
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.TotalCategory as TotalCategory
open import Cubical.Categories.Displayed.Instances.Element

open Category
open Functor

module Contravariant {ℓ ℓ'} {C : Category ℓ ℓ'} where
  -- same thing but for presheaves
  infix 50 ∫_
  ∫_ : ∀ {ℓS} → Functor (C ^op) (SET ℓS) → Category (ℓ-max ℓ ℓS) (ℓ-max ℓ' ℓS)
  ∫ P = ∫C (Element P)

  -- helpful results
  module _ {ℓS} {F : Functor (C ^op) (SET ℓS)} where
    isUnivalent∫ : isUnivalent C → isUnivalent (∫ F)
    isUnivalent∫ univC = isUnivalent∫C (Element F) univC (isUnivalentᴰElement F)

  module _ {ℓS} (F : Functor (C ^op) (SET ℓS)) where
    -- morphisms are equal as long as the morphisms in C are equal
    ElementHomPathP : ∀ {o1 o1' o2 o2'} (f : (∫ F) [ o1 , o2 ]) (g : (∫ F) [ o1' , o2' ])
            → (p : o1 ≡ o1') (q : o2 ≡ o2')
            → (eqInC : PathP (λ i → C [ fst (p i) , fst (q i) ]) (fst f) (fst g))
            → PathP (λ i → (∫ F) [ p i , q i ]) f g
    ElementHomPathP _ _ _ _ = ΣPathPProp (λ f → snd (F ⟅ _ ⟆) _ _)

    ElementHom≡ : ∀ {o1 o2} {f g : (∫ F) [ o1 , o2 ]}
                 → fst f ≡ fst g → f ≡ g
    ElementHom≡ p = ElementHomPathP _ _ refl refl p

module Covariant {ℓ ℓ'} {C : Category ℓ ℓ'} where
  ∫_ : ∀ {ℓS} → Functor C (SET ℓS) → Category (ℓ-max ℓ ℓS) (ℓ-max ℓ' ℓS)
  ∫ P = (Contravariant.∫_ {C = C ^op} (P ∘F fromOpOp)) ^op

  ForgetElements : ∀ {ℓS} → (F : Functor C (SET ℓS)) → Functor (∫ F) C
  ForgetElements F = fromOpOp ∘F (TotalCategory.Fst ^opF)

  module _ {ℓS} {F : Functor C (SET ℓS)} where
    isUnivalent∫ : (isUnivC : isUnivalent C) → isUnivalent (∫ F)
    isUnivalent∫ isUnivC = isUnivalentOp (isUnivalent∫C (Element (F ∘F fromOpOp)) (isUnivalentOp isUnivC) (isUnivalentᴰElement (F ∘F fromOpOp)))

  module _ {ℓS} (F : Functor C (SET ℓS)) where
    -- morphisms are equal as long as the morphisms in C are equal
    ElementHomPathP : ∀ {o1 o1' o2 o2'} (f : (∫ F) [ o1 , o2 ]) (g : (∫ F) [ o1' , o2' ])
            → (p : o1 ≡ o1') (q : o2 ≡ o2')
            → (eqInC : PathP (λ i → C [ fst (p i) , fst (q i) ]) (fst f) (fst g))
            → PathP (λ i → (∫ F) [ p i , q i ]) f g
    ElementHomPathP _ _ _ _ = ΣPathPProp (λ f → snd (F ⟅ _ ⟆) _ _)

    ElementHom≡ : ∀ {o1 o2} {f g : (∫ F) [ o1 , o2 ]}
                 → fst f ≡ fst g → f ≡ g
    ElementHom≡ p = ElementHomPathP _ _ refl refl p

