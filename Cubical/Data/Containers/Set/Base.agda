{-# OPTIONS --safe #-}

module Cubical.Data.Containers.Set.Base where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor 
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cubical.Foundations.Function
open import Cubical.Data.Unit

private
  variable
    ℓs ℓs' ℓp ℓp' : Level

record SetCon : Type (ℓ-suc (ℓ-max ℓs ℓp)) where
  constructor _◁_&_&_
  field
    Shape : Type ℓs
    Position : Shape → Type ℓp
    isSetShape : isSet Shape
    isSetPos : ∀ {s} → isSet (Position s)
open SetCon 

--------------------------------------------
-- ⟦_⟧f : SetCon → Functor Set Set
--------------------------------------------

⟦_⟧ : ∀ {ℓ : Level} → SetCon {ℓs} {ℓp} → (hSet ℓ → hSet (ℓ-max (ℓ-max ℓs ℓp) ℓ))
fst (⟦ S ◁ P & isSetS & _ ⟧ (X , isSetX)) = Σ[ s ∈ S ] (P s → X)
snd (⟦ S ◁ P & isSetS & _ ⟧ (X , isSetX)) = isSetΣ isSetS (λ s → isSetΠ λ _ → isSetX)

⟦_⟧m : ∀ {ℓ : Level} (C : SetCon {ℓs} {ℓp} ) {X Y : hSet ℓ} → SET ℓ [ X , Y ] →
       SET (ℓ-max (ℓ-max ℓs ℓp) ℓ) [ ⟦ C ⟧ X , ⟦ C ⟧ Y ]
⟦ S ◁ P & isSetS & _ ⟧m {X} {Y} X→Y (s , p) = s , λ ps → X→Y (p ps)

open Functor

⟦_⟧f : SetCon {ℓs} {ℓp} → Functor (SET (ℓ-max ℓs ℓp)) (SET (ℓ-max ℓs ℓp))
F-ob ⟦ C ⟧f X = ⟦ C ⟧ X
F-hom ⟦ C ⟧f {X} {Y} = ⟦ C ⟧m {X} {Y}
F-id ⟦ C ⟧f i (s , p) = s , p
fst (F-seq ⟦ C ⟧f f g i (s , p)) = s
snd (F-seq ⟦ C ⟧f f g i (s , p)) ps = g (f (p ps))

-- Set container morphism
record _⇒ᶜ_ (Γ : SetCon {ℓs} {ℓp}) (Δ : SetCon {ℓs'} {ℓp'}) :
       Type (ℓ-max ℓs (ℓ-max ℓs' (ℓ-max ℓp ℓp'))) where
  constructor _◁m_
  field
    u : Shape Γ → Shape Δ
    f : (s : Shape Γ) → Position Δ (u s) → Position Γ s
    
open _⇒ᶜ_

--------------------------------------------
-- SetCons form a category
--------------------------------------------

isSet⇒ᶜ : ∀ {ℓs ℓp} {C D : SetCon {ℓs} {ℓp}} → isSet (C ⇒ᶜ D)
u (isSet⇒ᶜ {ℓs} {ℓp} {C} {D} (u₁ ◁m f₁) (u₂ ◁m f₂) p q i j) s =
  isSet→SquareP
    (λ _ _ → D .isSetShape)
    (λ k → u (p k) s)
    (λ k → u (q k) s)
    (λ _ → u₁ s)
    (λ _ → u₂ s)
    i j
f (isSet⇒ᶜ {ℓs} {ℓp} {S₁ ◁ P₁ & setS₁ & setP₁} {S₂ ◁ P₂ & setS₂ & setP₂} (u₁ ◁m f₁) (u₂ ◁m f₂) p q i j) s₁ =
  isSet→SquareP
    {A = λ i j → P₂ (isSet→SquareP
      (λ _ _ → setS₂) (λ k → u (p k) s₁) (λ k → u (q k) s₁) (λ _ → u₁ s₁) (λ _ → u₂ s₁) i j) →
      P₁ s₁}
    (λ _ _ → isSetΠ λ _ → setP₁ {s₁})
    (λ k → f (p k) s₁)
    (λ k → f (q k) s₁)
    (λ _ → f₁ s₁)
    (λ _ → f₂ s₁)
    i j

open Category hiding (_∘_)

-- Category of SetCons
SetCont : ∀ {ℓs ℓp : Level} → Category _ _
ob (SetCont {ℓs} {ℓp}) = SetCon {ℓs} {ℓp}
Hom[_,_] SetCont = _⇒ᶜ_
u (id SetCont) s = s
f (id SetCont) s p = p
u ((SetCont ⋆ (u₁ ◁m f₁)) (u₂ ◁m f₂)) = u₂ ∘ u₁ 
f ((SetCont ⋆ (u₁ ◁m f₁)) (u₂ ◁m f₂)) s p = f₁ s (f₂ (u₁ s) p)
⋆IdL SetCont (u ◁m f) = refl
⋆IdR SetCont (u ◁m f)= refl
⋆Assoc SetCont (u₁ ◁m f₁) (u₂ ◁m f₂) (u₃ ◁m f₃) = refl
isSetHom SetCont = isSet⇒ᶜ

-- Identity SetCon
idC : SetCon {ℓs} {ℓp}
Shape idC = Unit*
Position idC _ = Unit*
isSetShape idC = isSetUnit*
isSetPos idC = isSetUnit*

◇ : {S : Type ℓs} {SS : isSet S} {T : Type ℓs'} {TT : isSet T}
    (P : S → Type ℓp) {PP : ∀ {s} → isSet (P s)}(Q : T → Type ℓp') →
    fst (⟦ S ◁ P & SS & PP ⟧ (T , TT)) → Type (ℓ-max ℓp ℓp')
◇ P Q (s , f) = Σ (P s) (Q ∘ f)

-- Composition of SetCons
_∘ᶜ_ : SetCon {ℓs} {ℓp} → SetCon {ℓs'} {ℓp'} → SetCon
Shape (C ∘ᶜ (T ◁ Q & setT & _)) = fst (⟦ C ⟧ (T , setT))
Position ((S ◁ P & setS & setP) ∘ᶜ (T ◁ Q & setT & _)) = ◇ {SS = setS} {TT = setT} P {PP = setP} Q
isSetShape (C ∘ᶜ (T ◁ Q & setT & _)) = snd (⟦ C ⟧ (T , setT))
isSetPos ((S ◁ P & _ & setP) ∘ᶜ (T ◁ Q & _ & setQ)) = isSetΣ setP (λ _ → setQ)

