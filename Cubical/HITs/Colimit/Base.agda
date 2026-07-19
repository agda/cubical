{-

  Homotopy colimits of graphs

-}
module Cubical.HITs.Colimit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Graph

-- Cones under a diagram

record Cocone ℓ {ℓd ℓv ℓe} {I : Graph ℓv ℓe} (F : Diag ℓd I) (X : Type ℓ)
              : Type (ℓ-suc (ℓ-max ℓ (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc ℓd)))) where
  field
    leg : ∀ (j : Node I) → F $g j → X
    com : ∀ {j k} (f : Edge I j k) → leg k ∘ F <$g> f ≡ leg j

  postcomp : ∀ {ℓ'} {Y : Type ℓ'} → (X → Y) → Cocone ℓ' F Y
  leg (postcomp h) j = h ∘ leg j
  com (postcomp h) f = cong (h ∘_) (com f)

open Cocone public


-- Σ (Type ℓ) (Cocone ℓ F) forms a category:

module _ {ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} where

  private
    -- the "lower star" functor
    _* : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} → (X → Y) → Cocone _ F X → Cocone _ F Y
    (h *) C = postcomp C h

  CoconeMor : ∀ {ℓ ℓ'} → Σ (Type ℓ) (Cocone ℓ F) → Σ (Type ℓ') (Cocone ℓ' F) → Type _
  CoconeMor (X , C) (Y , D) = Σ[ h ∈ (X → Y) ] (h *) C ≡ D

  idCoconeMor : ∀ {ℓ} (Cp : Σ (Type ℓ) (Cocone ℓ F)) → CoconeMor Cp Cp
  idCoconeMor Cp = (λ x → x) , refl

  compCoconeMor : ∀ {ℓ ℓ' ℓ''} {C : Σ (Type ℓ) (Cocone ℓ F)} {D : Σ (Type ℓ') (Cocone ℓ' F)}
                    {E : Σ (Type ℓ'') (Cocone ℓ'' F)}
                  → CoconeMor D E → CoconeMor C D → CoconeMor C E
  compCoconeMor (g , q) (f , p) = g ∘ f , (cong (g *) p) ∙ q


-- Universal cocones are initial objects in the category Σ (Type ℓ) (Cocone ℓ F)

module _ {ℓ ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} {X : Type ℓ} where

  isUniversalAt : ∀ ℓq → Cocone ℓ F X → Type (ℓ-max ℓ (ℓ-suc (ℓ-max ℓq (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc ℓd)))))
  isUniversalAt ℓq C = ∀ (Y : Type ℓq) → isEquiv {A = (X → Y)} {B = Cocone ℓq F Y} (postcomp C)
                  -- (unfolding isEquiv, this ^ is equivalent to what one might expect:)
                  -- ∀ (Y : Type ℓ) (D : Cocone ℓ F Y) → ∃![ h ∈ (X → Y) ] (h *) C ≡ D
                  --                                  (≡ isContr (CoconeMor (X , C) (Y , D)))

  isPropIsUniversalAt : ∀ ℓq (C : Cocone ℓ F X) → isProp (isUniversalAt ℓq C)
  isPropIsUniversalAt ℓq C = isPropΠ (λ Y → isPropIsEquiv (postcomp C))

  isUniversal : Cocone ℓ F X → Typeω
  isUniversal C = ∀ ℓq → isUniversalAt ℓq C


-- Colimits are universal cocones

record isColimit {ℓ ℓd ℓv ℓe} {I : Graph ℓv ℓe} (F : Diag ℓd I) (X : Type ℓ) : Typeω where
  field
    cone : Cocone ℓ F X
    univ : isUniversal cone
open isColimit public

module _ {ℓ ℓ' ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} {X : Type ℓ} {Y : Type ℓ'} where

  postcomp⁻¹ : isColimit F X → Cocone ℓ' F Y → (X → Y)
  postcomp⁻¹ cl = invEq (_ , univ cl _ Y)

  postcomp⁻¹-inv : (cl : isColimit F X) (D : Cocone ℓ' F Y) → (postcomp (cone cl) (postcomp⁻¹ cl D)) ≡ D
  postcomp⁻¹-inv cl D = secEq (_ , univ cl _ Y) D

  postcomp⁻¹-mor : (cl : isColimit F X) (D : Cocone ℓ' F Y) → CoconeMor (X , cone cl) (Y , D)
  postcomp⁻¹-mor cl D = (postcomp⁻¹ cl D) , (postcomp⁻¹-inv cl D)

-- Colimits are unique

module _ {ℓ ℓ' ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} {X : Type ℓ} {Y : Type ℓ'} where

  uniqColimit : isColimit F X → isColimit F Y → X ≃ Y
  uniqColimit cl cl'
    = isoToEquiv (iso (fst fwd) (fst bwd)
                      (λ x i → fst (isContr→isProp (equiv-proof (univ cl' ℓ' Y) (cone cl'))
                                                   (compCoconeMor fwd bwd)
                                                   (idCoconeMor (Y , cone cl')) i) x)
                      (λ x i → fst (isContr→isProp (equiv-proof (univ cl ℓ  X) (cone cl))
                                                   (compCoconeMor bwd fwd)
                                                   (idCoconeMor (X , cone cl)) i) x))
    where fwd : CoconeMor (X , cone cl ) (Y , cone cl')
          bwd : CoconeMor (Y , cone cl') (X , cone cl )
          fwd = postcomp⁻¹-mor cl (cone cl')
          bwd = postcomp⁻¹-mor cl' (cone cl)

-- Colimits always exist

data colim {ℓd ℓe ℓv} {I : Graph ℓv ℓe} (F : Diag ℓd I) : Type (ℓ-suc (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc ℓd))) where
  colim-leg : ∀ (j : Node I) → F $g j → colim F
  colim-com : ∀ {j k} (f : Edge I j k) → colim-leg k ∘ F <$g> f ≡ colim-leg j

module _ {ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} where

  colimCone : Cocone _ F (colim F)
  leg colimCone = colim-leg
  com colimCone = colim-com

  rec : ∀ {ℓ} {X : Type ℓ} → Cocone ℓ F X → (colim F → X)
  rec C (colim-leg j A)   = leg C j A
  rec C (colim-com f i A) = com C f i A

  colimIsColimit : isColimit F (colim F)
  cone colimIsColimit = colimCone
  univ colimIsColimit ℓq Y
    = isoToIsEquiv record { fun = postcomp colimCone
                          ; inv = rec
                          ; rightInv = λ C → refl
                          ; leftInv  = λ h → funExt (eq h) }
    where eq : ∀ h (x : colim _) → rec (postcomp colimCone h) x ≡ h x
          eq h (colim-leg j A)   = refl
          eq h (colim-com f i A) = refl
