{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.ReflGraph where

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
open import Cubical.DStructures.Structures.Group
open import Cubical.DStructures.Structures.SplitEpi

open GroupLemmas
open MorphismLemmas

private
  variable
    ℓ ℓ' : Level

---------------------------------------------
-- Reflexive graphs in the category of groups
--
-- ReflGraph
--     |
-- SplitEpiB
--
---------------------------------------------

module _ (ℓ ℓ' : Level) where
  -- type of internal reflexive graphs in the category of groups
  ReflGraph = Σ[ ((((G₀ , G₁) , ι , σ) , split-σ) , τ) ∈ (SplitEpiB ℓ ℓ') ] isGroupSplitEpi ι τ

  -- reflexive graphs displayed over split epimorphisms with an
  -- extra morphism back
  𝒮ᴰ-ReflGraph : URGStrᴰ (𝒮-SplitEpiB ℓ ℓ')
                        (λ ((((G , H) , f , b) , isRet) , b')
                          → isGroupSplitEpi f b')
                        ℓ-zero
  𝒮ᴰ-ReflGraph = Subtype→Sub-𝒮ᴰ (λ ((((G , H) , f , b) , isRet) , b')
                                   → isGroupSplitEpi f b' , isPropIsGroupHomRet f b')
                                (𝒮-SplitEpiB ℓ ℓ')

  -- the URG structure on the type of reflexive graphs
  𝒮-ReflGraph : URGStr ReflGraph (ℓ-max ℓ ℓ')
  𝒮-ReflGraph = ∫⟨ (𝒮-SplitEpiB ℓ ℓ') ⟩ 𝒮ᴰ-ReflGraph

--------------------------------------------------
-- This module introduces convenient notation
-- when working with a single reflexive graph
---------------------------------------------------
module ReflGraphNotation (𝒢 : ReflGraph ℓ ℓ') where

    -- extract the components of the Σ-type
    G₁ = snd (fst (fst (fst (fst 𝒢))))
    G₀ = fst (fst (fst (fst (fst 𝒢))))
    σ = snd (snd (fst (fst (fst 𝒢))))
    τ = snd (fst 𝒢)
    ι = fst (snd (fst (fst (fst 𝒢))))
    split-τ = snd 𝒢
    split-σ = snd (fst (fst 𝒢))

    -- open other modules containing convenient notation
    open SplitEpiNotation ι σ split-σ public
    open GroupNotation₁ G₁ public
    open GroupNotation₀ G₀ public
    open GroupHom public

    -- underlying maps
    t = GroupHom.fun τ

    -- combinations of maps to reduce
    -- amount of parentheses in proofs
    𝒾s = λ (g : ⟨ G₁ ⟩) → 𝒾 (s g) -- TODO: remove
    𝒾t = λ (g : ⟨ G₁ ⟩) → 𝒾 (t g) -- TODO: remove
    it = λ (g : ⟨ G₁ ⟩) → 𝒾 (t g)
    ti = λ (g : ⟨ G₀ ⟩) → t (𝒾 g)
    -it = λ (x : ⟨ G₁ ⟩) → -₁ (𝒾t x)
    it- = λ (x : ⟨ G₁ ⟩) →  𝒾t (-₁ x)

    ι∘τ : GroupHom G₁ G₁
    ι∘τ = compGroupHom τ ι

    -- extract what it means for σ and τ to be split
    σι-≡-fun : (g : ⟨ G₀ ⟩) → si g ≡ g
    σι-≡-fun = λ (g : ⟨ G₀ ⟩) → funExt⁻ (cong GroupHom.fun split-σ) g
    τι-≡-fun : (g : ⟨ G₀ ⟩) → ti g ≡ g
    τι-≡-fun = λ (g : ⟨ G₀ ⟩) → funExt⁻ (cong GroupHom.fun split-τ) g


-------------------------------------------
-- Lemmas about reflexive graphs in groups
-------------------------------------------

module ReflGraphLemmas (𝒢 : ReflGraph ℓ ℓ') where
    open ReflGraphNotation 𝒢

    -- the property for two morphisms to be composable
    isComposable : (g f : ⟨ G₁ ⟩) → Type ℓ
    isComposable g f = s g ≡ t f

    -- isComposable is a proposition, because G₀ is a set
    isPropIsComposable : (g f : ⟨ G₁ ⟩) → isProp (isComposable g f)
    isPropIsComposable g f c c' = set₀ (s g) (t f) c c'

    -- further reductions that are used often
    abstract
      -- σ (g -₁ ι (σ g)) ≡ 0₀
      σ-g--isg : (g : ⟨ G₁ ⟩) → s (g -₁ 𝒾s g) ≡ 0₀
      σ-g--isg g = s (g -₁ 𝒾s g)
                    ≡⟨ σ .isHom g (-₁ 𝒾s g) ⟩
                  s g +₀ s (-₁ 𝒾s g)
                    ≡⟨ cong (s g +₀_)
                            (mapInv σ (𝒾s g)) ⟩
                  s g -₀ s (𝒾s g)
                    ≡⟨ cong (λ z → s g -₀ z)
                            (σι-≡-fun (s g)) ⟩
                  s g -₀ s g
                    ≡⟨ rCancel₀ (s g) ⟩
                  0₀ ∎

      -- g is composable with ι (σ g)
      isComp-g-isg : (g : ⟨ G₁ ⟩) → isComposable g (𝒾s g)
      isComp-g-isg g = sym (τι-≡-fun (s g))

      -- ι (τ f) is composable with f
      isComp-itf-f : (f : ⟨ G₁ ⟩) → isComposable (it f) f
      isComp-itf-f f = σι-≡-fun (t f)

      -- ι (σ (-₁ ι g)) ≡ -₁ (ι g)
      ισ-ι : (g : ⟨ G₀ ⟩) → 𝒾s (-₁ (𝒾 g)) ≡ -₁ (𝒾 g)
      ισ-ι g = mapInv ι∘σ (𝒾 g) ∙ cong (λ z → -₁ (𝒾 z)) (σι-≡-fun g)
