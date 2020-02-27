{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Structure.AddToStructure where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties renaming (cong≃ to _⋆_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Data.Prod.Base hiding (_×_) renaming (_×Σ_ to _×_)

open import Cubical.Foundations.Structure.Base
open import Cubical.Foundations.Structure.SNS renaming (SNS₂ to SNS)

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level
    S : Type ℓ → Type ℓ'

-- Now, we want to add axioms (i.e. propositions) to our Structure S that don't affect the ι.
-- For this and the remainder of this file we will work with SNS'
-- We use a lemma due to Zesen Qian, which can now be found in Foundations.Prelude:
-- https://github.com/riaqn/cubical/blob/hgroup/Cubical/Data/Group/Properties.agda#L83

add-to-structure : (S : Type ℓ → Type ℓ')
                   (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
                 → Type ℓ → Type (ℓ-max ℓ' ℓ''')
add-to-structure S axioms X = Σ[ s ∈ S X ] (axioms X s)

add-to-iso : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'')
             (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
           → StrIso (add-to-structure S axioms) ℓ''
add-to-iso S ι axioms (X , (s , a)) (Y , (t , b)) f = ι (X , s) (Y , t) f

add-⋆-lemma : (S : Type ℓ → Type ℓ')
              (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
              (axioms-are-Props : (X : Type ℓ) (s : S X) → isProp (axioms X s))
              {X Y : Type ℓ} {s : S X} {t : S Y} {a : axioms X s} {b : axioms Y t}
              (e : X ≃ Y)
            → (equivFun (add-to-structure S axioms ⋆ e) (s , a) ≡ (t , b)) ≃ (equivFun (S ⋆ e) s ≡ t)
add-⋆-lemma S axioms axioms-are-Props {Y = Y} {s = s} {t = t} {a = a} {b = b} e = isoToEquiv (iso φ ψ η ε)
      where
       φ : equivFun ((add-to-structure S axioms) ⋆ e) (s , a) ≡ (t , b)
         → equivFun (S ⋆ e) s ≡ t
       φ r i = r i .fst

       ψ : equivFun (S ⋆ e) s ≡ t
         → equivFun ((add-to-structure S axioms) ⋆ e) (s , a) ≡ (t , b)
       ψ p i = p i , isProp→PathP (λ j → axioms-are-Props Y (p j)) (equivFun (add-to-structure S axioms ⋆ e) (s , a) .snd) b i

       η : section φ ψ
       η p = refl

       ε : retract φ ψ
       ε r i j = r j .fst
               , isProp→isSet-PathP (λ k → axioms-are-Props Y (r k .fst)) _ _
                                    (isProp→PathP (λ j → axioms-are-Props Y (r j .fst))
                                                  (equivFun (add-to-structure S axioms ⋆ e) (s , a) .snd) b)
                                    (λ k → r k .snd) i j

add-axioms-SNS : (S : Type ℓ → Type ℓ') (ι : StrIso S ℓ'')
                 (axioms : (X : Type ℓ) → (S X) → Type ℓ''')
                 (axioms-are-Props : (X : Type ℓ) (s : S X) → isProp (axioms X s))
                 (θ : SNS S ι)
               → SNS (add-to-structure S axioms) (add-to-iso S ι axioms)
add-axioms-SNS S ι axioms axioms-are-Props θ (X , (s , a)) (Y , (t , b)) f =
              equivFun (add-to-structure S axioms ⋆ f) (s , a) ≡ (t , b) ≃⟨ add-⋆-lemma S axioms axioms-are-Props f ⟩
              equivFun (S ⋆ f) s ≡ t                                     ≃⟨ θ (X , s) (Y , t) f ⟩
              add-to-iso S ι axioms (X , (s , a)) (Y , (t , b)) f ■


-- Now, we want to join two structures. Together with the adding of
-- axioms this will allow us to prove that a lot of mathematical
-- structures are a standard notion of structure

private
  technical-×-lemma : {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
                    → A ≃ C → B ≃ D → A × B ≃ C × D
  technical-×-lemma {A = A} {B = B} {C = C} {D = D} f g = isoToEquiv (iso φ ψ η ε)
   where
    φ : (A × B) → (C × D)
    φ (a , b) = equivFun f a , equivFun g b

    ψ : (C × D) → (A × B)
    ψ (c , d) = equivFun (invEquiv f) c , equivFun (invEquiv g) d

    η : section φ ψ
    η (c , d) i = retEq f c i , retEq g d i

    ε : retract φ ψ
    ε (a , b) i = secEq f a i , secEq g b i

join-structure : (S₁ : Type ℓ₁ → Type ℓ₂) (S₂ : Type ℓ₁ → Type ℓ₄)
                → Type ℓ₁ → Type (ℓ-max ℓ₂ ℓ₄)
join-structure S₁ S₂ X = S₁ X × S₂ X

join-iso : {S₁ : Type ℓ₁ → Type ℓ₂} (ι₁ : StrIso S₁ ℓ₃)
           {S₂ : Type ℓ₁ → Type ℓ₄} (ι₂ : StrIso S₂ ℓ₅)
         → StrIso (join-structure S₁ S₂) (ℓ-max ℓ₃ ℓ₅)
join-iso ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) f = (ι₁ (X , s₁) (Y , t₁) f) × (ι₂ (X , s₂) (Y , t₂) f)

join-⋆-lemma : (S₁ : Type ℓ₁ → Type ℓ₂) (S₂ : Type ℓ₁ → Type ℓ₄)
               {X Y : Type ℓ₁} {s₁ : S₁ X} {s₂ : S₂ X} {t₁ : S₁ Y} {t₂ : S₂ Y} (e : X ≃ Y)
             → (equivFun (join-structure S₁ S₂ ⋆ e) (s₁ , s₂) ≡ (t₁ , t₂)) ≃
               (equivFun (S₁ ⋆ e) s₁ ≡ t₁) × (equivFun (S₂ ⋆ e) s₂ ≡ t₂)
join-⋆-lemma S₁ S₂ {Y = Y} {s₁ = s₁} {s₂ = s₂} {t₁ = t₁} {t₂ = t₂} e = isoToEquiv (iso φ ψ η ε)
   where
    φ : equivFun (join-structure S₁ S₂ ⋆ e) (s₁ , s₂) ≡ (t₁ , t₂)
      → (equivFun (S₁ ⋆ e) s₁ ≡ t₁) × (equivFun (S₂ ⋆ e) s₂ ≡ t₂)
    φ p = (λ i → p i .fst) , (λ i → p i .snd)

    ψ : (equivFun (S₁ ⋆ e) s₁ ≡ t₁) × (equivFun (S₂ ⋆ e) s₂ ≡ t₂)
      → equivFun (join-structure S₁ S₂ ⋆ e) (s₁ , s₂) ≡ (t₁ , t₂)
    ψ (p , q) i = (p i) , (q i)

    η : section φ ψ
    η (p , q) = refl

    ε : retract φ ψ
    ε p = refl

join-SNS : (S₁ : Type ℓ₁ → Type ℓ₂) (ι₁ : StrIso S₁ ℓ₃) (θ₁ : SNS S₁ ι₁)
           (S₂ : Type ℓ₁ → Type ℓ₄) (ι₂ : StrIso S₂ ℓ₅) (θ₂ : SNS S₂ ι₂)
         → SNS (join-structure S₁ S₂) (join-iso ι₁ ι₂)
join-SNS S₁ ι₁ θ₁ S₂ ι₂ θ₂ (X , s₁ , s₂) (Y , t₁ , t₂) f =
    equivFun (join-structure S₁ S₂ ⋆ f) (s₁ , s₂) ≡ (t₁ , t₂)
  ≃⟨ join-⋆-lemma S₁ S₂ f ⟩
    (equivFun (S₁ ⋆ f) s₁ ≡ t₁) × (equivFun (S₂ ⋆ f) s₂ ≡ t₂)
  ≃⟨ technical-×-lemma (θ₁ (X , s₁) (Y , t₁) f) (θ₂ (X , s₂) (Y , t₂) f)  ⟩
    join-iso ι₁ ι₂ (X , s₁ , s₂) (Y , t₁ , t₂) f ■
