{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Algebra.Group.Semidirect where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphism
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Action
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level

module _  where

  semidirectProd : (G : Group {ℓ}) (H : Group {ℓ'}) (Act : GroupAction H G) → Group {ℓ-max ℓ ℓ'}
  semidirectProd G H Act = makeGroup-left {A = sd-carrier} sd-0 _+sd_ -sd_ sd-set sd-assoc sd-lId sd-lCancel
    where
      open ActionNotationα Act
      open ActionLemmas Act
      open GroupNotationG G
      open GroupNotationᴴ H
      -- sd stands for semidirect
      sd-carrier = ⟨ G ⟩ × ⟨ H ⟩
      sd-0 = 0ᴳ , 0ᴴ

      module _ ((g , h) : sd-carrier) where
        -sd_ = (-ᴴ h) α (-ᴳ g) , -ᴴ h

        _+sd_ = λ (g' , h') → g +ᴳ (h α g') , h +ᴴ h'

      abstract
        sd-set = isSetΣ setᴳ (λ _ → setᴴ)
        sd-lId = λ ((g , h) : sd-carrier) → ΣPathP (lIdᴳ (0ᴴ α g) ∙ (α-id g) , lIdᴴ h)
        sd-lCancel = λ ((g , h) : sd-carrier) → ΣPathP ((sym (α-hom (-ᴴ h) (-ᴳ g) g) ∙∙ cong ((-ᴴ h) α_) (lCancelᴳ g) ∙∙ actOnUnit (-ᴴ h)) , lCancelᴴ h)


        sd-assoc = λ (a , x) (b , y) (c , z) → ΣPathP ((a +ᴳ (x α (b  +ᴳ (y α c)))
                                    ≡⟨ cong (a +ᴳ_) (α-hom x b (y α c)) ⟩
                                a +ᴳ ((x α b) +ᴳ (x α (y α c)))
                                    ≡⟨ assocᴳ a (x α b) (x α (y α c)) ⟩
                                (a +ᴳ (x α b)) +ᴳ (x α (y α c))
                                    ≡⟨ cong ((a +ᴳ (x α b)) +ᴳ_) (sym (α-assoc x y c)) ⟩
                                (a +ᴳ (x α b)) +ᴳ ((x +ᴴ y) α c) ∎) , assocᴴ x y z)

  -- this syntax declaration is the reason we can't unify semidirectProd with
  -- the projections module
  syntax semidirectProd G H α = G ⋊⟨ α ⟩ H

module _ {G : Group {ℓ}} {H : Group {ℓ'}} (Act : GroupAction H G) where
  open ActionNotationα Act
  open ActionLemmas Act
  open GroupNotationG G
  open GroupNotationᴴ H

  π₁ : ⟨ G ⋊⟨ Act ⟩ H ⟩ → ⟨ G ⟩
  π₁ = fst

  ι₁ : GroupHom G (G ⋊⟨ Act ⟩ H)
  ι₁ = grouphom (λ g → g , 0ᴴ) λ g g' → ΣPathP (cong (g +ᴳ_) (sym (α-id g')), sym (lIdᴴ 0ᴴ))

  π₂ : GroupHom (G ⋊⟨ Act ⟩ H) H
  -- π₂ = grouphom snd λ _ _ → refl
  π₂ = grouphom snd λ (g , h) (g' , h') → refl {x = h +ᴴ h'}

  ι₂ : GroupHom H (G ⋊⟨ Act ⟩ H)
  ι₂ = grouphom (λ h → 0ᴳ , h) λ h h' → ΣPathP (sym (actOnUnit h) ∙ sym (lIdᴳ (h α 0ᴳ)) , refl)

  π₂-hasSec : isGroupSplitEpi ι₂ π₂
  π₂-hasSec = GroupMorphismExt (λ _ → refl)
