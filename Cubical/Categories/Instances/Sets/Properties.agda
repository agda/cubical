{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Sets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.Constructions.Slice.Functor

open Functor


module SetLCCC ℓ {X@(_ , isSetX) Y@(_ , isSetY) : hSet ℓ} (f : ⟨ X ⟩ →  ⟨ Y ⟩) where
 open BaseChange (PullbacksSET {ℓ})

 open Cubical.Categories.Adjoint.NaturalBijection
 open _⊣_

 open import Cubical.Categories.Instances.Cospan
 open import Cubical.Categories.Limits.Limits

 Π/ : Functor (SliceCat (SET ℓ) X) (SliceCat (SET ℓ) Y)
 F-ob Π/ (sliceob {S-ob = _ , isSetA} h) =
   sliceob {S-ob = _ , (isSetΣ isSetY $
                     λ y → isSetΠ λ ((x , _) : fiber f y) →
                           isOfHLevelFiber 2 isSetA isSetX h x)} fst
 F-hom Π/ {a} {b} (slicehom g p) =
   slicehom (map-snd (map-sndDep (λ q → (p ≡$ _) ∙ q ) ∘_)) refl
 F-id Π/ = SliceHom-≡-intro' _ _ $
   funExt λ x' → cong ((fst x') ,_)
     (funExt λ y → Σ≡Prop (λ _ → isSetX _ _) refl)
 F-seq Π/ _ _ = SliceHom-≡-intro' _ _ $
   funExt λ x' → cong ((fst x') ,_)
     (funExt λ y → Σ≡Prop (λ _ → isSetX _ _) refl)

 f*⊣Π/ : f ＊ ⊣ Π/
 Iso.fun (adjIso f*⊣Π/) (slicehom h p) =
   slicehom (λ _ → _ , λ (_ , q) → h (_ , q) , (p ≡$ _)) refl
 Iso.inv (adjIso f*⊣Π/) (slicehom h p) =
   slicehom _  $ funExt λ (_ , q) → snd (snd (h _) (_ , q ∙ ((sym p) ≡$ _)))
 Iso.rightInv (adjIso f*⊣Π/) b = SliceHom-≡-intro' _ _ $
    funExt λ _ → cong₂ _,_ (sym (S-comm b ≡$ _))
      $ toPathP $ funExt λ _ →
        Σ≡Prop (λ _ → isSetX _ _) $ transportRefl _ ∙
          cong (fst ∘ snd (S-hom b _))
               (Σ≡Prop (λ _ → isSetY _ _) $ transportRefl _)
 Iso.leftInv (adjIso f*⊣Π/) a = SliceHom-≡-intro' _ _ $
   funExt λ _ → cong (S-hom a) $ Σ≡Prop (λ _ → isSetY _ _) refl
 adjNatInD f*⊣Π/ _ _ = SliceHom-≡-intro' _ _ $
   funExt λ _ → cong₂ _,_ refl $
     funExt λ _ → Σ≡Prop (λ _ → isSetX _ _) refl
 adjNatInC f*⊣Π/ g h = SliceHom-≡-intro' _ _ $
   funExt λ _ → cong (fst ∘ (snd (S-hom g (S-hom h _)) ∘ (_ ,_))) $ isSetY _ _ _ _
