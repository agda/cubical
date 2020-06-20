{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Pointed.Homotopy where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma

-- _∼_ : {ℓ ℓ' : Level} {X : Type ℓ} {A : X → Type ℓ'} → (f g : (x : X) → A x) → Type (ℓ-max ℓ ℓ')
-- f ∼ g = ∀ x → f x ≡ g x

-- pointed homotopies
module _ {ℓ ℓ'} {A : Pointed ℓ} {B : typ A → Type ℓ'} {ptB : B (pt A)} where

  -- pointed homotopy as pointed Π
  _∙∼_ : (f g : Π∙ A B ptB) → Type (ℓ-max ℓ ℓ')
  f ∙∼ g = Π∙ A (λ x → fst f x ≡ fst g x) (snd f ∙ (snd g) ⁻¹)

  -- pointed homotopy with PathP
  _∙∼P_ : (f g : Π∙ A B ptB) → Type (ℓ-max ℓ ℓ')
  f ∙∼P g = Σ[ h ∈ ((x : typ A) → fst f x ≡ fst g x) ]
               PathP (λ i → h (pt A) i ≡ ptB) (snd f) (snd g)

  -- Aux pointed homotopy
  private
    _∙∼Aux_ : (f g : Π∙ A B ptB) → Type (ℓ-max ℓ ℓ')
    f ∙∼Aux g = Σ[ p ∈ f₁ ∼ g₁ ] ((p ⋆) ⁻¹ ∙∙ f₂ ∙∙ refl ≡ g₂)
      where
        ⋆ = snd A
        f₁ = fst f
        f₂ = snd f
        g₁ = fst g
        g₂ = snd g

  -- PathP and Aux pointed htpy are isomorphic
  private
    module PAuxIso (f g : Π∙ A B ptB) where
      ⋆ = snd A
      f₁ = fst f
      f₂ = snd f
      g₁ = fst g
      g₂ = snd g



      -- the transformation between the two kinds of pointed homotopies does nothing
      -- on the homotopy between the functions, only on the pointedness proofs
      -- here we combine this, together with transportation along the path given by
      -- PathP≡doubleCompPathˡ
      ∙∼PAuxIso : Iso (f ∙∼P g) (f ∙∼Aux g)
      ∙∼PAuxIso = iso (λ (p₁ , p₂) → p₁ , transport (q p₁) p₂)
                        (λ (p₁ , p₂) → p₁ , transport (sym (q p₁)) p₂)
                        (λ (p₁ , p₂) → ΣPathP (refl , transportTransport⁻ (q p₁) p₂))
                        λ (p₁ , p₂) → ΣPathP (refl , transport⁻Transport (q p₁) p₂)
                        where
                          q = λ (p₁ : f₁ ∼ g₁) → PathP≡doubleCompPathˡ (p₁ ⋆) f₂ g₂ refl
  private
    module Aux∼Transform (f g : Π∙ A B ptB) where
      private
        ⋆ = snd A
        f₁ = fst f
        f₂ = snd f
        g₁ = fst g
        g₂ = snd g

      q₁ : (p₁ : f₁ ∼ g₁) → p₁ ⋆ ≡ (p₁ ⋆ ∙ g₂) ∙ g₂ ⁻¹
      q₁ p₁ =
        p₁ ⋆
          ≡⟨ rUnit (p₁ ⋆) ⟩
        p₁ ⋆ ∙ refl
          ≡⟨ cong (p₁ ⋆ ∙_) (sym (rCancel g₂)) ⟩
        p₁ ⋆ ∙ (g₂ ∙ g₂ ⁻¹)
          ≡⟨ assoc (p₁ ⋆) g₂ (g₂ ⁻¹) ⟩
        (p₁ ⋆ ∙ g₂) ∙ g₂ ⁻¹ ≡⟨ refl ⟩ refl

      q₂ : ((p₁ , p₂) : f ∙∼Aux g) → (p₁ ⋆ ∙ g₂) ∙ g₂ ⁻¹ ≡ (p₁ ⋆ ∙ (p₁ ⋆ ⁻¹ ∙∙ f₂ ∙∙ refl)) ∙ g₂ ⁻¹
      q₂ (p₁ , p₂) = cong (λ z → (p₁ ⋆ ∙ z ) ∙ g₂ ⁻¹) (sym p₂)

      q₃ : (p₁ : f₁ ∼ g₁) → (p₁ ⋆ ∙ (p₁ ⋆ ⁻¹ ∙∙ f₂ ∙∙ refl)) ∙ g₂ ⁻¹ ≡ f₂ ∙ g₂ ⁻¹
      q₃ p₁ =
        (p⋆ ∙ (p⋆ ⁻¹ ∙∙ f₂ ∙∙ refl)) ∙ g₂ ⁻¹
          ≡⟨ cong (λ z → (p⋆ ∙ z ) ∙ g₂ ⁻¹) (doubleCompPath-elim' (p⋆ ⁻¹) f₂ refl) ⟩
        (p⋆ ∙ (p⋆ ⁻¹ ∙ f₂ ∙ refl)) ∙ g₂ ⁻¹
          ≡⟨ cong (_∙ g₂ ⁻¹) (assoc p⋆ (p⋆ ⁻¹) (f₂ ∙ refl)) ⟩
        ((p⋆ ∙ p⋆ ⁻¹) ∙ f₂ ∙ refl) ∙ g₂ ⁻¹
          ≡⟨ cong (λ z → (z ∙ f₂ ∙ refl) ∙ g₂ ⁻¹) (rCancel' p⋆) ⟩
        (refl ∙ f₂ ∙ refl) ∙ g₂ ⁻¹
          ≡⟨ cong (_∙ g₂ ⁻¹) (assoc refl f₂ refl) ⟩
        ((refl ∙ f₂) ∙ refl) ∙ g₂ ⁻¹
          ≡⟨ cong (λ z → (z ∙ refl) ∙ g₂ ⁻¹) (sym (lUnit f₂)) ⟩
        (f₂ ∙ refl) ∙ g₂ ⁻¹
          ≡⟨ cong (_∙ g₂ ⁻¹) (sym (rUnit f₂)) ⟩
        f₂ ∙ g₂ ⁻¹ ≡⟨ refl ⟩ refl
        where
          p⋆ = p₁ ⋆



      r₁ : (p₁ : f₁ ∼ g₁) → (p₁ ⋆ ⁻¹) ∙∙ f₂ ∙∙ refl ≡ (refl ⁻¹ ∙∙ p₁ ⋆ ∙∙ refl) ⁻¹ ∙ f₂
      r₁ p₁ =
        (p⋆ ⁻¹) ∙∙ f₂ ∙∙ refl
          ≡⟨ doubleCompPath-elim' (p⋆ ⁻¹) f₂ refl ⟩
        p⋆ ⁻¹ ∙ f₂ ∙ refl
          ≡⟨ cong (p⋆ ⁻¹ ∙_) (sym (rUnit f₂)) ⟩
        p⋆ ⁻¹ ∙ f₂
          ≡⟨ cong (λ z → z ⁻¹ ∙ f₂)
                  (p⋆
                    ≡⟨ rUnit p⋆ ∙ lUnit (p⋆ ∙ refl) ∙ cong (_∙ p⋆ ∙ refl) symRefl ⟩
                  refl ⁻¹ ∙ p⋆ ∙ refl
                    ≡⟨ sym (doubleCompPath-elim' (refl ⁻¹) p⋆ refl) ⟩
                  refl ⁻¹ ∙∙ p⋆ ∙∙ refl ≡⟨ refl ⟩ refl) ⟩
        (refl ⁻¹ ∙∙ p⋆ ∙∙ refl) ⁻¹ ∙ f₂ ≡⟨ refl ⟩ refl
        where
          p⋆ = p₁ ⋆

      r₂ : ((p₁ , p₂) : f ∙∼ g) → (refl ⁻¹ ∙∙ p₁ ⋆ ∙∙ refl) ⁻¹ ∙ f₂ ≡ (f₂ ∙ g₂ ⁻¹) ⁻¹ ∙ f₂
      r₂ (p₁ , p₂) = cong (λ z → z ⁻¹ ∙ f₂) (transport (PathP≡doubleCompPathˡ refl (p₁ ⋆) (f₂ ∙ g₂ ⁻¹) refl) p₂)

      r₃ : (p₁ : f₁ ∼ g₁) → (f₂ ∙ g₂ ⁻¹) ⁻¹ ∙ f₂ ≡ g₂
      r₃ p₁ = (f₂ ∙ g₂ ⁻¹) ⁻¹ ∙ f₂
                  ≡⟨ cong (_∙ f₂) (symDistr f₂ (g₂ ⁻¹)) ⟩
              (g₂ ⁻¹ ⁻¹ ∙ f₂ ⁻¹) ∙ f₂
                  ≡⟨ sym (assoc (g₂ ⁻¹ ⁻¹) (f₂ ⁻¹) f₂) ⟩
              g₂ ⁻¹ ⁻¹ ∙ (f₂ ⁻¹ ∙ f₂) ≡⟨ cong (g₂ ⁻¹ ⁻¹ ∙_) (lCancel f₂) ∙ sym (rUnit (g₂ ⁻¹ ⁻¹)) ⟩
              g₂ ⁻¹ ⁻¹ ≡⟨ sym (symInvo g₂) ⟩
              g₂ ≡⟨ refl ⟩ refl
         where
         p⋆ = p₁ ⋆


  private
    module Aux∼map (f g : Π∙ A B ptB) where

      private
        ⋆ = snd A
        f₁ = fst f
        f₂ = snd f
        g₁ = fst g
        g₂ = snd g
     
      ∙∼Aux→∙∼ : (f ∙∼Aux g) → (f ∙∼ g)
      ∙∼Aux→∙∼ p = p₁ , q₁ p₁ ∙∙ q₂ p ∙∙ q₃ p₁
        where
          open Aux∼Transform f g
          p₁ = fst p
          p₂ = snd p

      ∙∼→∙∼Aux : (f ∙∼ g) → (f ∙∼Aux g)
      ∙∼→∙∼Aux p = p₁ , r₁ p₁ ∙∙ r₂ p ∙∙ r₃ p₁
        where
          open Aux∼Transform f g
          p₁ = fst p
          p₂ = snd p

  private
    module Aux∼inv (f g : Π∙ A B ptB) where
      open Aux∼map f g
      private
        ⋆ = snd A
        f₁ = fst f
        f₂ = snd f
        g₁ = fst g
        g₂ = snd g

      rinv₂ : (p : f ∙∼ g) → snd (∙∼Aux→∙∼ (∙∼→∙∼Aux p)) ≡ snd p
      rinv₂ (p₁ , p₂) = {!!}
      rinv : (p : f ∙∼ g) → ∙∼Aux→∙∼ (∙∼→∙∼Aux p) ≡ p
      rinv = λ p → ΣPathP (refl , rinv₂ p)


      linv₂ : (p : f ∙∼Aux g) → snd (∙∼→∙∼Aux (∙∼Aux→∙∼ p)) ≡ snd p
      linv₂ (p₁ , p₂) = J {x = (p₁ ⋆) ⁻¹ ∙∙ f₂ ∙∙ refl} indStatement indRefl p₂
        where
          indStatement : (g₂' : g₁ ⋆ ≡ ptB) (p₂' : p₁ ⋆ ⁻¹ ∙∙ f₂ ∙∙ refl ≡ g₂') → Type _
          indStatement g₂' p₂' = snd (∙∼→∙∼Aux' (∙∼Aux→∙∼' (p₁ , p₂'))) ≡ p₂'
            where open Aux∼map f (g₁ , g₂') renaming (∙∼→∙∼Aux to ∙∼→∙∼Aux' ; ∙∼Aux→∙∼ to ∙∼Aux→∙∼')

          indRefl : indStatement ((p₁ ⋆ ⁻¹) ∙∙ f₂ ∙∙ (λ _ → ptB)) refl
          indRefl = J {x = f₁ ⋆} (λ b f₂' → indStatement {!g₂!} refl) {!!} f₂
            -- where
              {-
              g₂' = p₁ ⋆ ⁻¹ ∙∙ f₂ ∙∙ refl
              open Aux∼Transform f (g₁ , g₂')

              q₂refl : q₂ (p₁ , refl) ≡ refl 
              q₂refl = refl

              qrefl : q₁ p₁ ∙∙ q₂ (p₁ , refl) ∙∙ q₃ p₁ ≡ (q₁ p₁ ∙∙ refl ∙∙ q₃ p₁)
              qrefl = refl

              r₂refl = r₂ (p₁ , q₁ p₁ ∙∙ refl ∙∙ q₃ p₁) -}

      linv : (p : f ∙∼Aux g) → ∙∼→∙∼Aux (∙∼Aux→∙∼ p) ≡ p
      linv = λ p → ΣPathP (refl , linv₂ p)

  private
    module Aux∼Iso (f g : Π∙ A B ptB) where
      open Aux∼map f g
      open Aux∼inv f g
      Aux∙∼Iso : Iso (f ∙∼Aux g) (f ∙∼ g)
      Aux∙∼Iso = iso ∙∼Aux→∙∼ ∙∼→∙∼Aux rinv linv






{-
  ∙∼→∙∼P : {f g : Π∙ A B ptB} → f ∙∼ g → f ∙∼P g
  ∙∼→∙∼P {f = f} {g = g} p = p₁ ,
    transport (sym (PathP≡doubleCompPathˡ p⋆ f₂ g₂ refl))
              ((p⋆ ⁻¹) ∙∙ f₂ ∙∙ refl
                ≡⟨ doubleCompPath-elim' (p⋆ ⁻¹) f₂ refl ⟩
              p⋆ ⁻¹ ∙ f₂ ∙ refl
                ≡⟨ cong (p⋆ ⁻¹ ∙_) (sym (rUnit f₂)) ⟩
              p⋆ ⁻¹ ∙ f₂
                ≡⟨ cong (λ z → z ⁻¹ ∙ f₂)
                        (p⋆
                          ≡⟨ rUnit p⋆ ∙ lUnit (p⋆ ∙ refl) ∙ cong (_∙ p⋆ ∙ refl) symRefl ⟩
                        refl ⁻¹ ∙ p⋆ ∙ refl
                          ≡⟨ sym (doubleCompPath-elim' (refl ⁻¹) p⋆ refl) ⟩
                        refl ⁻¹ ∙∙ p⋆ ∙∙ refl
                          ≡⟨ transport (PathP≡doubleCompPathˡ refl p⋆ (f₂ ∙ g₂ ⁻¹) refl) p₂ ⟩
                        f₂ ∙ g₂ ⁻¹ ≡⟨ refl ⟩ refl) ⟩
              (f₂ ∙ g₂ ⁻¹) ⁻¹ ∙ f₂
                ≡⟨ cong (_∙ f₂) (symDistr f₂ (g₂ ⁻¹)) ⟩
              (g₂ ⁻¹ ⁻¹ ∙ f₂ ⁻¹) ∙ f₂
                ≡⟨ assoc' (g₂ ⁻¹ ⁻¹) (f₂ ⁻¹) f₂ ⟩
              g₂ ⁻¹ ⁻¹ ∙ (f₂ ⁻¹ ∙ f₂) ≡⟨ cong (g₂ ⁻¹ ⁻¹ ∙_) (lCancel f₂) ∙ sym (rUnit (g₂ ⁻¹ ⁻¹)) ⟩
              g₂ ⁻¹ ⁻¹ ≡⟨ sym (symInvo g₂) ⟩
              g₂ ≡⟨ refl ⟩ refl)
    where
      p₁ = fst p
      p₂ = snd p
      p⋆ = p₁ (snd A)
      f₂ = snd f
      g₂ = snd g

  -- Pointed PathP homotopy gives Π∙ homotopy
  ∙∼P→∙∼ : {f g : Π∙ A B ptB} → f ∙∼P g → f ∙∼ g
  ∙∼P→∙∼ {f = f} {g = g} p = p₁ ,
    (p⋆
      ≡⟨ rUnit p⋆ ⟩
    p⋆ ∙ refl
      ≡⟨ cong (p⋆ ∙_) (sym (rCancel g₂)) ⟩
    p⋆ ∙ (g₂ ∙ g₂ ⁻¹)
      ≡⟨ assoc p⋆ g₂ (g₂ ⁻¹) ⟩
    (p⋆ ∙ g₂) ∙ g₂ ⁻¹
      ≡⟨ cong (λ z → (p⋆ ∙ z ) ∙ g₂ ⁻¹) (sym (transport (PathP≡doubleCompPathˡ p⋆ f₂ g₂ refl) p₂)) ⟩
    (p⋆ ∙ (p⋆ ⁻¹ ∙∙ f₂ ∙∙ refl)) ∙ g₂ ⁻¹
      ≡⟨ cong (λ z → (p⋆ ∙ z ) ∙ g₂ ⁻¹) (doubleCompPath-elim' (p⋆ ⁻¹) f₂ refl) ⟩
    (p⋆ ∙ (p⋆ ⁻¹ ∙ f₂ ∙ refl)) ∙ g₂ ⁻¹
      ≡⟨ cong (_∙ g₂ ⁻¹) (assoc p⋆ (p⋆ ⁻¹) (f₂ ∙ refl)) ⟩
    ((p⋆ ∙ p⋆ ⁻¹) ∙ f₂ ∙ refl) ∙ g₂ ⁻¹
      ≡⟨ cong (λ z → (z ∙ f₂ ∙ refl) ∙ g₂ ⁻¹) (rCancel' p⋆) ⟩
    (refl ∙ f₂ ∙ refl) ∙ g₂ ⁻¹
      ≡⟨ cong (_∙ g₂ ⁻¹) (assoc refl f₂ refl) ⟩
    ((refl ∙ f₂) ∙ refl) ∙ g₂ ⁻¹
      ≡⟨ cong (λ z → (z ∙ refl) ∙ g₂ ⁻¹) (sym (lUnit f₂)) ⟩
    (f₂ ∙ refl) ∙ g₂ ⁻¹
      ≡⟨ cong (_∙ g₂ ⁻¹) (sym (rUnit f₂)) ⟩
    f₂ ∙ g₂ ⁻¹ ≡⟨ refl ⟩ refl)
    where
      p₁ = fst p
      p₂ = snd p
      p⋆ = p₁ (snd A)
      f₂ = snd f
      g₂ = snd g

-}
