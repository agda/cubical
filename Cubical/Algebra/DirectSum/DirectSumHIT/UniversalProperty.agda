module Cubical.Algebra.DirectSum.DirectSumHIT.UniversalProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectSumHIT
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base


private variable
  ℓ ℓ' ℓ'' : Level

open AbGroupStr
open IsGroupHom

-----------------------------------------------------------------------------
-- Definition

module _
  (Idx              : Type ℓ)
  (G                : (k : Idx) → Type ℓ')
  (Gstr             : (k : Idx) → AbGroupStr (G k))
  (HAbGr@(H , Hstr) : AbGroup ℓ'')
  (fHhom            : (k : Idx) → AbGroupHom ((G k) , (Gstr k)) HAbGr)
  where

  private
    fH : (k : Idx) → G k → H
    fH = λ k → fst (fHhom k)
    fHstr : (k : Idx) → _
    fHstr = λ k → snd (fHhom k)

  injₖ : (k : Idx) → G k → ⊕HIT Idx G Gstr
  injₖ k a = base k a

  injₖ-hom : (k : Idx) → AbGroupHom ((G k) , (Gstr k)) (⊕HIT-AbGr Idx G Gstr)
  injₖ-hom k = injₖ k , (makeIsGroupHom λ a b → sym (base-add _ _ _) )

  -- universalProperty :
  ⊕HIT→H : ⊕HIT Idx G Gstr → H
  ⊕HIT→H = DS-Rec-Set.f _ _ _ _ (is-set Hstr)
            (0g Hstr)
            (λ k a → fH k a)
            (Hstr ._+_)
            (+Assoc Hstr)
            (+IdR Hstr)
            (+Comm Hstr)
            (λ k → pres1 (fHstr k))
            λ k a b → sym (pres· (fHstr k) _ _)

  ⊕HIT→H-hom : AbGroupHom (⊕HIT-AbGr Idx G Gstr) HAbGr
  ⊕HIT→H-hom = ⊕HIT→H , (makeIsGroupHom (λ _ _ → refl))

  -- Universal Property
  up∃⊕HIT : (k : Idx) → fHhom k ≡ compGroupHom (injₖ-hom k) ⊕HIT→H-hom
  up∃⊕HIT k = ΣPathTransport→PathΣ _ _
             ((funExt (λ _ → refl))
             , isPropIsGroupHom _ _ _ _)


  upUnicity⊕HIT : (hhom : AbGroupHom (⊕HIT-AbGr Idx G Gstr) HAbGr) →
                  (eqInj : (k : Idx) → fHhom k ≡ compGroupHom (injₖ-hom k) hhom)
                  → hhom ≡ ⊕HIT→H-hom
  upUnicity⊕HIT (h , hstr) eqInj = ΣPathTransport→PathΣ _ _
                             (helper , isPropIsGroupHom _ _ _ _)
    where

    helper : _
    helper = funExt (DS-Ind-Prop.f _ _ _ _ (λ _ → is-set Hstr _ _)
                    (pres1 hstr)
                    (λ k a → sym (funExt⁻ (cong fst (eqInj k)) a))
                    λ {U V} ind-U ind-V → pres· hstr _ _ ∙ cong₂ (_+_ Hstr) ind-U ind-V)
