{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Group.Semidirect where

open import Cubical.Core.Everything
open import Cubical.Data.Group.Base
open import Cubical.Data.Group.Action.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Data.Group.Base
open import Cubical.Data.Group.Higher
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels

private
  variable
    ℓ : Level

Semidirect : (H K : Group ℓ) (α : lAction K H) → Group ℓ
Semidirect (group H Hset (group-struct 1H H⁻¹ _∙H_ lUnitH rUnitH assocH lCancelH rCancelH))
           (group K Kset (group-struct 1K K⁻¹ _∙K_ lUnitK rUnitK assocK lCancelK rCancelK))
           (laction act identity coh hom) = group (Σ H (λ _ → K)) (isSetΣ Hset (λ _ → Kset))
  (group-struct
    (1H , 1K)
    (λ (h , k) → (act (K⁻¹ k) (H⁻¹ h)) , K⁻¹ k)
    (λ (h , k) (h' , k') → h ∙H (act k h') , k ∙K k')
    (λ (h , k) → ΣPathP ((lUnitH (act 1K h)) ∙ (identity h) , lUnitK k))
    (λ hk → ΣPathP (cong (hk .fst ∙H_) (actg1≡1 (snd hk)) ∙ rUnitH (fst hk) , rUnitK (snd hk)))
    (λ (a , x) (b , y) (c , z) → ΣPathP
      (cong ((a ∙H (act x b)) ∙H_) (coh x y c) ∙∙
      (assocH a (act x b) (act x (act y c))) ∙∙
      cong (a ∙H_) (sym (hom x b (act y c)))
      , assocK x y z))
    (λ (h , k) → ΣPathP
      (sym (hom (K⁻¹ k) (H⁻¹ h) h) ∙∙
      (cong (act (K⁻¹ k)) (lCancelH h)) ∙∙
      actg1≡1 (K⁻¹ k)
      , lCancelK k))
    λ (h , k) → ΣPathP
      ((cong (h ∙H_)
        (sym (coh k (K⁻¹ k) (H⁻¹ h)) ∙
        (cong (λ z → act z (H⁻¹ h)) (rCancelK k)) ∙
        (identity (H⁻¹ h)))) ∙
      (rCancelH h)
      , (rCancelK k)))
  where
    ℋ = group H Hset (group-struct 1H H⁻¹ _∙H_ lUnitH rUnitH assocH lCancelH rCancelH)
    𝒦 = group K Kset (group-struct 1K K⁻¹ _∙K_ lUnitK rUnitK assocK lCancelK rCancelK)
    α = laction act identity coh hom

    open lActionProperties 𝒦 ℋ α

syntax Semidirect H K α = H ⋊⟨ α ⟩ K

-- BSemidirect : {ℓ ℓ' : Level} {H : 1BGroup ℓ} {N : 1BGroup ℓ'} (α : BAction H (BGroup.base N)) → Pointed (ℓ-max ℓ ℓ')
-- BSemidirect {ℓ} {ℓ'} {(bgroup (H , H∙) _ _)} {N} (α , α∙) = (Σ[ h ∈ H ] (fst (α h))) , (H∙ , snd (α H∙))

-- BSemidirect' : {ℓ ℓ' : Level} {H : 1BGroup ℓ} {N : 1BGroup ℓ'} (α : BAction H (BGroup.base N)) → HigherGroup (ℓ-max ℓ ℓ')
-- BSemidirect' {ℓ} {ℓ'} {(bgroup (H , H∙) _ _)} {N} (α , α∙) =  highergroup ((Σ[ h ∈ H ] (fst (α h))) , (H∙ , snd (α H∙))) {!!}
