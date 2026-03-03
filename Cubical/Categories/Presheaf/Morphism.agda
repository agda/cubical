module Cubical.Categories.Presheaf.Morphism where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Elements
open import Cubical.Categories.Instances.Lift
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable

{-

  Given two presheaves P and Q on the same category C, a morphism
  between them is a natural transformation. Here we generalize this to
  situations where P and Q are presheaves on *different*
  categories. This is equivalent to the notion of morphism of
  fibrations if viewing P and Q as discrete fibrations.

  Given a functor F : C → D, a presheaf P on C and a presheaf Q on D,
  we can define a homomorphism from P to Q over F as a natural
  transformation from P to Q o F^op. (if we had implicit cumulativity)

  These are the homs of a 2-category of presheaves displayed over the
  2-category of categories.

-}
private
  variable
    ℓc ℓc' ℓd ℓd' ℓp ℓq : Level

open Category
open Contravariant
open Functor
open NatTrans
open UniversalElement

module _ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
         (F : Functor C D)
         (P : Presheaf C ℓp)
         (Q : Presheaf D ℓq) where
  PshHom : Type (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓp) ℓq)
  PshHom =
    PresheafCategory C (ℓ-max ℓp ℓq)
      [ LiftF ℓq ∘F P , LiftF ℓp ∘F Q ∘F (F ^opF) ]

  module _ (h : PshHom) where
    -- This should define a functor on the category of elements
    pushElt : Elementᴾ {C = C} P → Elementᴾ {C = D} Q
    pushElt (A , η) = (F ⟅ A ⟆) , (h .N-ob A (lift η) .lower)

    pushEltNat : ∀ {B : C .ob} (η : Elementᴾ {C = C} P) (f : C [ B , η .fst ])
                  → (pushElt η .snd ∘ᴾ⟨ Q ⟩ F .F-hom f)
                    ≡ pushElt (B , η .snd ∘ᴾ⟨ P ⟩ f) .snd
    pushEltNat η f i = h .N-hom f (~ i) (lift (η .snd)) .lower

    pushEltF : Functor (∫ᴾ_ {C = C} P) (∫ᴾ_ {C = D} Q)
    pushEltF .F-ob = pushElt
    pushEltF .F-hom {x}{y} (f , commutes) .fst = F .F-hom f
    pushEltF .F-hom {x}{y} (f , commutes) .snd =
      pushElt _ .snd ∘ᴾ⟨ Q ⟩ F .F-hom f
        ≡⟨ pushEltNat y f ⟩
      pushElt (_ , y .snd ∘ᴾ⟨ P ⟩ f) .snd
        ≡⟨ cong (λ a → pushElt a .snd) (ΣPathP (refl , commutes)) ⟩
      pushElt x .snd ∎
    pushEltF .F-id = Σ≡Prop (λ x → (Q ⟅ _ ⟆) .snd _ _) (F .F-id)
    pushEltF .F-seq f g =
      Σ≡Prop ((λ x → (Q ⟅ _ ⟆) .snd _ _)) (F .F-seq (f .fst) (g .fst))

    preservesRepresentation : ∀ (η : UniversalElement C P)
                            → Type (ℓ-max (ℓ-max ℓd ℓd') ℓq)
    preservesRepresentation η = isUniversal D Q (η' .fst) (η' .snd)
      where η' = pushElt (η .vertex , η .element)

    preservesRepresentations : Type _
    preservesRepresentations = ∀ η → preservesRepresentation η

    -- If C and D are univalent then this follows by representability
    -- being a Prop. But even in non-univalent categories it follows
    -- by uniqueness of representables up to unique isomorphism
    preservesAnyRepresentation→preservesAllRepresentations :
      ∀ η → preservesRepresentation η → preservesRepresentations
    preservesAnyRepresentation→preservesAllRepresentations η preserves-η η' =
      isTerminalToIsUniversal D Q
        (preserveAnyTerminal→PreservesTerminals (∫ᴾ_ {C = C} P)
                                 (∫ᴾ_ {C = D} Q)
                                 pushEltF
                                 (universalElementToTerminalElement C P η)
                                 (isUniversalToIsTerminal D Q _ _ preserves-η)
                                 (universalElementToTerminalElement C P η'))
