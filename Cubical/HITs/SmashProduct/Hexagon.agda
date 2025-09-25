module Cubical.HITs.SmashProduct.Hexagon where

open import Cubical.HITs.SmashProduct.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Pushout.Base
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.Wedge
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv

-- pentagon identity
module _ {ℓ ℓ' ℓ'' : Level}
  {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
  where
  hex₁∙ : A ⋀∙ (B ⋀∙ C) →∙ (A ⋀∙ (C ⋀∙ B))
  hex₁∙ = idfun∙ A ⋀→∙ ⋀comm→∙
  hex₁ = fst hex₁∙

  hex₂∙ : A ⋀∙ (C ⋀∙ B) →∙ ((A ⋀∙ C) ⋀∙ B)
  hex₂∙ = ≃∙map SmashAssocEquiv∙
  hex₂ = fst hex₂∙

  hex₃∙ : ((A ⋀∙ C) ⋀∙ B) →∙ ((C ⋀∙ A) ⋀∙ B)
  hex₃∙ = ⋀comm→∙ ⋀→∙ idfun∙ B
  hex₃ = fst hex₃∙

  hexₗ∙ : A ⋀∙ (B ⋀∙ C) →∙ ((C ⋀∙ A) ⋀∙ B)
  hexₗ∙ = hex₃∙ ∘∙ (hex₂∙ ∘∙ hex₁∙)
  hexₗ = fst hexₗ∙

  hex₄∙ : A ⋀∙ (B ⋀∙ C) →∙ (A ⋀∙ B) ⋀∙ C
  hex₄∙ = ≃∙map SmashAssocEquiv∙
  hex₄ = fst hex₄∙

  hex₅∙ : (A ⋀∙ B) ⋀∙ C →∙ (C ⋀∙ (A ⋀∙ B))
  hex₅∙ = ⋀comm→∙
  hex₅ = fst hex₅∙

  hex₆∙ : C ⋀∙ (A ⋀∙ B) →∙ ((C ⋀∙ A) ⋀∙ B)
  hex₆∙ = ≃∙map SmashAssocEquiv∙
  hex₆ = fst hex₆∙

  hexᵣ∙ : A ⋀∙ (B ⋀∙ C) →∙ ((C ⋀∙ A) ⋀∙ B)
  hexᵣ∙ = hex₆∙ ∘∙ (hex₅∙ ∘∙ hex₄∙)
  hexᵣ = fst hexᵣ∙

  hexagon-main : Σ[ h ∈ ((x : A ⋀ (B ⋀∙ C)) → hexₗ x ≡ hexᵣ x) ]
                    h (inl tt) ≡ refl
  hexagon-main = ⋀-fun≡'.main _ _
    (λ a → r-lem (fst a) (snd a) )
    (λ a → p≡refl
          ◁ λ i j → hex₃ (hex₂ (rUnit (push (inl a)) (~ j) i)))
    (⋀→∙Homogeneous≡ (isHomogeneousPath _ _)
      λ b c → (λ i → push-lem₂ b c i ∙∙ refl ∙∙ sym (push-lem₂ b c i1))
            ∙∙ ∙∙lCancel _
            ∙∙ sym p≡refl)
     , sym (compPath≡compPath' (cong (hexₗ) (push (inr (inl tt)))) refl)
     ∙ sym (rUnit _)
     ∙ cong (cong (hex₃ ∘ hex₂)) (sym (rUnit (push (inr (inl tt)))))
    where
    push-lem : (a : fst A) → cong (hexₗ) (push (inl a)) ≡ refl
    push-lem a = cong (cong (hex₃ ∘ hex₂))
                      (sym (rUnit (push (inl a))))

    r-lem : (a : fst A) (y : B ⋀ C) → hexₗ (inr (a , y)) ≡ hexᵣ (inr (a , y))
    r-lem a = ⋀-fun≡ _ _ refl (λ _ → refl)
      (λ b → flipSquare
        (cong-∙∙ (hex₃ ∘ ⋀comm→)
          (push (inl b)) (λ i → inr (b , (push (inl a) i))) refl
       ∙∙ sym (compPath≡compPath' (push (inr b) ∙ refl)
              (λ i → inr (push (inr a) i , b)))
        ∙ (λ i → rUnit (push (inr b)) (~ i) ∙ λ j → inr (push (inr a) j , b))
       ∙∙ sym
         (cong-∙∙ ⋀comm→ (push (inl b)) (λ i → inr (b , push (inr a) i)) refl
         ∙ sym (compPath≡compPath'
                (push (inr b)) (λ i → inr (push (inr a) i , b))))))
      (λ c → flipSquare (sym (rUnit (push (inl (inr (c , a)))))
                        ∙ sym (lemC c)))
      where
      lem₁ : (c : fst C)
        → cong hex₄ (λ i → inr (a , push (inr c) i))
         ≡ push (inr c) ∙∙ (λ i → inr (push (inl a) i , c)) ∙∙ refl
      lem₁ c =
        cong-∙∙ ⋀comm→ (push (inl c)) (λ i → inr (c , push (inl a) i)) refl

      lemC : (c : fst C)
        → cong (hex₆ ∘ hex₅ ∘ hex₄) (λ i → inr (a , push (inr c) i))
         ≡ push (inl (inr (c , a)))
      lemC c = cong (cong (hex₆ ∘ hex₅)) (lem₁ c)
             ∙ cong-∙∙ (hex₆ ∘ hex₅)
                 (push (inr c)) (λ i → inr (push (inl a) i , c)) refl
             ∙ sym (rUnit _)

    push-lem₂ : (b : fst B) (c : fst C)
      → cong (hexₗ) (push (inr (inr (b , c))))
       ≡ cong (hexᵣ) (push (inr (inr (b , c))))
    push-lem₂ b c =
      cong (cong (hex₃ ∘ hex₂))
         (sym (rUnit (push (inr (inr (c , b))))))
      ∙∙ cong (cong hex₃)
              (cong-∙∙ ⋀comm→
                (push (inl b))
                (λ i → inr (b , push (inr c) i))
                refl
             ∙ sym (compPath≡compPath'
                     (push (inr b))
                     (λ i → inr (push (inr c) i , b))))
      ∙∙ cong-∙ hex₃ (push (inr b)) (λ i → inr (push (inr c) i , b))
      ∙∙ cong (_∙ λ i → inr (push (inl c) i , b)) (sym (rUnit (push (inr b))))
      ∙∙ sym (speedup
      ∙∙ cong-∙ (hex₆ ∘ hex₅)
                (push (inr c)) (λ i → inr (push (inr b) i , c))
      ∙∙ (sym (lUnit _)
       ∙ cong-∙∙ ⋀comm→ (push (inl b)) (λ i → inr (b , push (inl c) i)) refl
       ∙ sym (compPath≡compPath' _ _ )))
      where
      speedup-lem : cong hex₄ (push (inr (inr (b , c))))
               ≡ push (inr c) ∙ λ i → inr (push (inr b) i , c)
      speedup-lem =
        cong-∙∙ ⋀comm→ (push (inl c))
                        (λ i → inr (c , push (inr b) i))
                        refl
        ∙ sym (compPath≡compPath' _ _)

      speedup : cong (hex₆ ∘ hex₅ ∘ hex₄) (push (inr (inr (b , c))))
                   ≡ _
      speedup = cong (cong (hex₆ ∘ hex₅)) speedup-lem

    module M = ⋀-fun≡'  hexₗ hexᵣ (λ a → r-lem (fst a) (snd a))

    p≡refl : M.p ≡ refl
    p≡refl =
        sym (compPath≡compPath'
              (cong (hexₗ) (push (inr (inl tt)))) refl)
      ∙ sym (rUnit _)
      ∙ cong (cong (hex₃ ∘ hex₂))
             (sym (rUnit (push (inr (inl tt)))))

  hexagon∙ : hexₗ∙ ≡ hexᵣ∙
  hexagon∙ = ΣPathP ((funExt (fst hexagon-main))
                  , flipSquare
                    (snd hexagon-main
                    ◁ flipSquare
                       (sym (rUnit _)
                     ∙ cong (cong (fst hex₃∙))
                            (sym (rUnit (refl {x = inl tt})))
                     ∙ sym (sym (rUnit _)
                          ∙ cong (cong (fst hex₆∙))
                            (sym (rUnit (refl {x = inl tt})))))))

  hexagon : (x : _) → hexₗ x ≡ hexᵣ x
  hexagon x = fst hexagon-main x
