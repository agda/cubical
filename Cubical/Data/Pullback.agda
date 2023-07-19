{-# OPTIONS --safe #-}

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Homotopy.Base

module Cubical.Data.Pullback where

private
  variable
    a b c ℓ : Level
    A : Type a
    B : Type b
    C : Type c

Pullback : (A : Type a) (f : B → A) (g : C → A) → Type _
Pullback {B = B} {C = C} A f g = Σ[ (b , c) ∈ (B × C) ] f b ≡ g c

module UniversalProperty (f : B → A) (g : C → A) where
  pr₁ : Pullback A f g → B
  pr₁ = fst ∘ fst

  pr₂ : Pullback A f g → C
  pr₂ = snd ∘ fst

  comm : f ∘ pr₁ ∼ g ∘ pr₂
  comm = snd

  universalProperty' : (X : Type ℓ) (p1 : X → B) (p2 : X → C) (α : f ∘ p1 ∼ g ∘ p2) → (x : X) →
    isContr (Σ[ ((x₁ , x₂) , β) ∈ Pullback A f g ] Σ[ u₁ ∈ (p1 x ≡ x₁) ] Σ[ u₂ ∈ (x₂ ≡ p2 x) ]
      cong f u₁ ∙ β ∙ cong g u₂ ≡ α x)
  universalProperty' X p1 p2 α x = isOfHLevelRespectEquiv 0 (invEquiv e) isContrUnit
    where
      o : Iso
        (Σ[ ((x₁ , x₂) , β) ∈ Pullback A f g ] Σ[ u₁ ∈ (p1 x ≡ x₁) ] Σ[ u₂ ∈ (x₂ ≡ p2 x) ] cong f u₁ ∙ β ∙ cong g u₂ ≡ α x)
        (Σ[ (x₁ , u₁) ∈ singl (p1 x) ] Σ[ (x₂ , u₂) ∈ singl (p2 x) ] Σ[ β ∈ f x₁ ≡ g x₂ ] cong f u₁ ∙ β ∙ cong g (sym u₂) ≡ α x)
      Iso.fun o (((x₁ , x₂) , β) , u₁ , u₂ , γ) = (x₁ , u₁) , (x₂ , (sym u₂)) , β , γ
      Iso.inv o ((x₁ , u₁) , (x₂ , u₂) , (β , γ)) = ((x₁ , x₂) , β) , u₁ , sym u₂ , γ
      Iso.rightInv o _ = refl
      Iso.leftInv  o _ = refl

      e : _ ≃ _
      e =
        Σ[ ((x₁ , x₂) , β) ∈ Pullback A f g ] Σ[ u₁ ∈ (p1 x ≡ x₁) ] Σ[ u₂ ∈ (x₂ ≡ p2 x) ] cong f u₁ ∙ β ∙ cong g u₂ ≡ α x
          ≃⟨ isoToEquiv o ⟩ -- reorder
        Σ[ (x₁ , u₁) ∈ singl (p1 x) ] Σ[ (x₂ , u₂) ∈ singl (p2 x) ] Σ[ β ∈ f x₁ ≡ g x₂ ] cong f u₁ ∙ β ∙ cong g (sym u₂) ≡ α x
          ≃⟨ Σ-contractFst (isContrSingl (p1 x)) ⟩
        Σ[ (x₂ , u₂) ∈ singl (p2 x) ] Σ[ β ∈ f (p1 x) ≡ g x₂ ] cong f refl ∙ β ∙ cong g (sym u₂) ≡ α x
          ≃⟨ Σ-contractFst (isContrSingl (p2 x)) ⟩
        Σ[ β ∈ f (p1 x) ≡ g (p2 x) ] cong f refl ∙ β ∙ cong g refl ≡ α x
          ≃⟨ Σ-cong-equiv-snd (λ β → isoToEquiv symIso) ⟩
        Σ[ β ∈ f (p1 x) ≡ g (p2 x) ] α x ≡ cong f refl ∙ β ∙ cong g refl
          ≃⟨ Σ-cong-equiv-snd (λ β → compPathrEquiv (sym (lUnit _))) ⟩
        Σ[ β ∈ f (p1 x) ≡ g (p2 x) ] α x ≡ β ∙ cong g refl
          ≃⟨ Σ-cong-equiv-snd (λ β → compPathrEquiv (sym (rUnit _))) ⟩
        Σ[ β ∈ f (p1 x) ≡ g (p2 x) ] α x ≡ β
          ≃⟨ isContr→≃Unit (isContrSingl (α x)) ⟩
        Unit ■

  -- The pullback above satisfies the universal property.
  -- For every other type X with projections p1 : X → B, p2 : X → C the type
  -- of functions h : X → Pullback such that everything commutes and the fillers
  -- match is contractible, that is, such functions are unqiue.
  universalProperty : (X : Type ℓ) (p1 : X → B) (p2 : X → C) (α : f ∘ p1 ∼ g ∘ p2) →
    isContr (Σ[ h ∈ (X → Pullback A f g) ] Σ[ u₁ ∈ (p1 ∼ pr₁ ∘ h) ] Σ[ u₂ ∈ (pr₂ ∘ h ∼ p2) ]
      (f ▪ˡ u₁ ▪ comm ▪ʳ h ▪ g ▪ˡ u₂) ∼ α)
  universalProperty X p1 p2 α = isOfHLevelRespectEquiv 0 e (isContrΠ (universalProperty' X p1 p2 α))
    where
      e : _ ≃ _
      e = isoToEquiv $ iso
        (λ f → fst ∘ f , fst ∘ snd ∘ f , fst ∘ snd ∘ snd ∘ f , snd ∘ snd ∘ snd ∘ f)
        (λ (h , u₁ , u₂ , α) a → h a , u₁ a , u₂ a , α a)
        (λ _ → refl) (λ _ → refl)

  -- The identity is the unique endomorphism of the terminal cone.
  idPullback : Σ[ h ∈ (Pullback A f g → Pullback A f g) ] Σ[ u₁ ∈ (pr₁ ∼ pr₁ ∘ h) ] Σ[ u₂ ∈ (pr₂ ∘ h ∼ pr₂) ]
      (f ▪ˡ u₁ ▪ comm ▪ʳ h ▪ g ▪ˡ u₂) ∼ comm
  idPullback = idfun _ , (λ _ → refl) , (λ _ → refl) , (λ _ → sym (lUnit _) ∙ sym (rUnit _))

PullbackConst≃x≡y : {A : Type ℓ} (x y : A) → Pullback A (λ (_ : Unit) → x) (λ (_ : Unit) → y) ≃ (x ≡ y)
PullbackConst≃x≡y x y = Σ-contractFst (isContrΣ isContrUnit λ _ → isContrUnit)
