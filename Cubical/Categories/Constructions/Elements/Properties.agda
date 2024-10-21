{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open Category
open import Cubical.Categories.Functor
open Functor
open import Cubical.Categories.NaturalTransformation
open NatTrans
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Elements
open Covariant

open import Cubical.WildCat.Functor
open import Cubical.WildCat.Instances.Categories
open import Cubical.WildCat.Instances.NonWild

module Cubical.Categories.Constructions.Elements.Properties where

variable
  ℓC ℓC' ℓD ℓD' ℓS : Level
  C : Category ℓC ℓC'
  D : Category ℓD ℓD'

∫-hom : ∀ {F G : Functor C (SET ℓS)} → NatTrans F G → Functor (∫ F) (∫ G)
Functor.F-ob (∫-hom ν) (c , f) = c , N-ob ν c f
Functor.F-hom (∫-hom ν) {c1 , f1} {c2 , f2} (χ , ef) = χ , sym (funExt⁻ (N-hom ν χ) f1) ∙ cong (N-ob ν c2) ef
Functor.F-id (∫-hom {G = G} ν) {c , f} = cong₂ _,_ refl (isOfHLevelPathP' 1 (snd (F-ob G c)) _ _ _ _)
Functor.F-seq (∫-hom {G = G} ν) {c1 , f1} {c2 , f2} {c3 , f3} (χ12 , ef12) (χ23 , ef23) =
  cong₂ _,_ refl (isOfHLevelPathP' 1 (snd (F-ob G c3)) _ _ _ _)

∫-id : ∀ (F : Functor C (SET ℓS)) → ∫-hom (idTrans F) ≡ Id
∫-id F = Functor≡
  (λ _ → refl)
  λ {(c1 , f1)} {(c2 , f2)} (χ , ef) → cong₂ _,_ refl (isOfHLevelPathP' 1 (snd (F-ob F c2)) _ _ _ _)

∫-seq : ∀ {C : Category ℓC ℓC'} {F G H : Functor C (SET ℓS)} → (μ : NatTrans F G) → (ν : NatTrans G H)
  → ∫-hom (seqTrans μ ν) ≡ funcComp (∫-hom ν) (∫-hom μ)
∫-seq {H = H} μ ν = Functor≡
  (λ _ → refl)
  λ {(c1 , f1)} {(c2 , f2)} (χ , ef) → cong₂ _,_ refl (isOfHLevelPathP' 1 (snd (F-ob H c2)) _ _ _ _)

module _ (C : Category ℓC ℓC') (ℓS : Level) where

  ElementsWildFunctor : WildFunctor (AsWildCat (FUNCTOR C (SET ℓS))) (CatWildCat (ℓ-max ℓC ℓS) (ℓ-max ℓC' ℓS))
  WildFunctor.F-ob ElementsWildFunctor = ∫_
  WildFunctor.F-hom ElementsWildFunctor = ∫-hom
  WildFunctor.F-id ElementsWildFunctor {F} = ∫-id F
  WildFunctor.F-seq ElementsWildFunctor μ ν = ∫-seq μ ν
