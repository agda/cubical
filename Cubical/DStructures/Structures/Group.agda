{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary

open import Cubical.Structures.Group
open import Cubical.Structures.LeftAction

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Meta.Combine
open import Cubical.DStructures.Structures.Type

private
  variable
    ℓ ℓ' : Level

open URGStr

-------------------------------------------
-- URG structure on the type of groups
-------------------------------------------

𝒮-group : (ℓ : Level) → URGStr (Group {ℓ}) ℓ
𝒮-group ℓ ._≅_ = GroupEquiv
𝒮-group ℓ .ρ = idGroupEquiv
𝒮-group ℓ .uni = isUnivalent'→isUnivalent GroupEquiv
                                          idGroupEquiv
                                          λ G H → invEquiv (GroupPath G H)

-------------------------------------------
-- 𝒮ᴰ-hierarchies on top of 𝒮-group
--
-- Notation:
--
-- G - group
-- G² - pair of groups
-- F - morphism forth
-- B - morphism back
--
-- F B (FB)
-- \ | /
--   G
--   |
--   G
-------------------------------------------

module _ (ℓ ℓ' : Level) where

  ---- Underlying types

  -- pairs of groups
  G² = Group {ℓ} × Group {ℓ'}
  -- pairs of groups + a morphism forth
  G²F = Σ[ (G , H) ∈ G² ] GroupHom G H
  -- pairs of groups + a morphism back
  G²B = Σ[ (G , H) ∈ G² ] GroupHom H G
  -- pairs of groups + morphisms forth and back
  G²FB = Σ[ (G , H) ∈ G² ] GroupHom G H × GroupHom H G

  ---- 𝒮 and 𝒮ᴰ-structures

  -- Group morphisms displayed over pairs of groups
  𝒮ᴰ-G²\F : URGStrᴰ (𝒮-group ℓ ×𝒮 𝒮-group ℓ')
                    (λ (G , H) → GroupHom G H)
                    (ℓ-max ℓ ℓ')
  𝒮ᴰ-G²\F =
    make-𝒮ᴰ (λ {(G , H)} {(G' , H')} f (eG , eH) f' → (g : ⟨ G ⟩) → GroupEquiv.eq eH .fst ((f .fun) g) ≡ (f' .fun) (GroupEquiv.eq eG .fst g))
            (λ _ _ → refl)
            λ (G , H) f → isContrRespectEquiv (Σ-cong-equiv-snd (λ f' → isoToEquiv (invIso (GroupMorphismExtIso f f'))))
                                              (isContrSingl f)
    where open GroupHom

  -- URG structure on type of two groups with a group morphism
  𝒮-G²F : URGStr G²F (ℓ-max ℓ ℓ')
  𝒮-G²F = ∫⟨ 𝒮-group ℓ ×𝒮 𝒮-group ℓ' ⟩ 𝒮ᴰ-G²\F

  -- Same as 𝒮-G²F but with the morphism going the other way
  𝒮ᴰ-G²\B : URGStrᴰ (𝒮-group ℓ ×𝒮 𝒮-group ℓ')
                             (λ (G , H) → GroupHom H G)
                             (ℓ-max ℓ ℓ')
  𝒮ᴰ-G²\B =
    make-𝒮ᴰ (λ {(_ , H)} f (eG , eH) f' → (h : ⟨ H ⟩) → GroupEquiv.eq eG .fst (f .fun h) ≡ f' .fun (GroupEquiv.eq eH .fst h))
                (λ _ _ → refl)
                λ _ f → isContrRespectEquiv (Σ-cong-equiv-snd (λ f' → isoToEquiv (invIso (GroupMorphismExtIso f f')))) (isContrSingl f)
    where open GroupHom

  -- Type of two groups with a group morphism going back
  𝒮-G²B : URGStr G²B (ℓ-max ℓ ℓ')
  𝒮-G²B = ∫⟨ 𝒮-group ℓ ×𝒮 𝒮-group ℓ' ⟩ 𝒮ᴰ-G²\B


  -- Morphisms going forth and back displayed over pairs of groups
  𝒮ᴰ-G²\FB : URGStrᴰ (𝒮-group ℓ ×𝒮 𝒮-group ℓ')
                   (λ (G , H) → GroupHom G H × GroupHom H G)
                   (ℓ-max ℓ ℓ')
  𝒮ᴰ-G²\FB = combine-𝒮ᴰ 𝒮ᴰ-G²\F 𝒮ᴰ-G²\B

  -- URG structure on type of pairs of groups with morphisms going forth and back
  𝒮-G²FB : URGStr G²FB (ℓ-max ℓ ℓ')
  𝒮-G²FB = ∫⟨ 𝒮-group ℓ ×𝒮 𝒮-group ℓ' ⟩ 𝒮ᴰ-G²\FB
