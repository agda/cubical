module Cubical.Categories.Presheaf.Morphism where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Elements
open import Cubical.Categories.Instances.Lift
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Element
open import Cubical.Categories.Displayed.HLevels
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
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  PshHom : Type (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓp) ℓq)
  PshHom =
    PresheafCategory C (ℓ-max ℓp ℓq)
      [ LiftF ℓq ∘F P , LiftF ℓp ∘F Q ∘F (F ^opF) ]

  module _ (h : PshHom) where
    pushEltF : Functor (∫ P) (∫ Q)
    pushEltF = ∫F {F = F} (mkPropHomsFunctor (hasPropHomsElement Q)
      (λ {x} z → h .N-ob x (lift z) .lower)
      λ {x} {y} {f} {p} {p'} fp≡p' →
        F ⟪ f ⟫ Q.⋆ (h .N-ob _ (lift p') .lower)
          ≡[ i ]⟨ h .N-hom f (~ i) (lift p') .lower ⟩
        h .N-ob _ (lift (f P.⋆ p')) .lower
          ≡[ i ]⟨ h .N-ob _ (lift (fp≡p' i)) .lower ⟩
        h .N-ob _ (lift p) .lower
          ∎)

    preservesRepresentation : ∀ (η : UniversalElement C P)
                            → Type (ℓ-max (ℓ-max ℓd ℓd') ℓq)
    preservesRepresentation η = isUniversal D Q _ (h .N-ob _ (lift (η .element)) .lower)

    preservesRepresentations : Type _
    preservesRepresentations = ∀ η → preservesRepresentation η

    -- If C and D are univalent then this follows by representability
    -- being a Prop. But even in non-univalent categories it follows
    -- by uniqueness of representables up to unique isomorphism
    preservesAnyRepresentation→preservesAllRepresentations :
      ∀ η → preservesRepresentation η → preservesRepresentations
    preservesAnyRepresentation→preservesAllRepresentations η preserves-η η' =
      isTerminalToIsUniversal D Q
        (preserveAnyTerminal→PreservesTerminals (∫ P)
                                 (∫ Q)
                                 pushEltF
                                 (universalElementToTerminalElement C P η)
                                 (isUniversalToIsTerminal D Q _ _ preserves-η)
                                 (universalElementToTerminalElement C P η'))
