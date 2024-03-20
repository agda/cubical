{-# OPTIONS --safe #-}
module Cubical.HITs.Wedge.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Wedge.Base
open import Cubical.HITs.Susp

open import Cubical.Homotopy.Loopspace


private
  variable
    ℓ ℓ' : Level

-- Susp (⋁ᵢ Aᵢ) ≃ ⋁ᵢ (Susp Aᵢ)
private
  Bouquet→ΩBouquetSusp-filler : (A : Type ℓ) (B : A → Pointed ℓ')
    → (a : _) → (i j k : I) → ⋁gen A (λ a → Susp∙ (fst (B a)))
  Bouquet→ΩBouquetSusp-filler A B a i j k =
    hfill (λ k → λ {(i = i0) → inl tt
                   ; (i = i1) → doubleCompPath-filler
                                  (push a)
                                  (λ i → inr (a
                                        , rCancel' (merid (snd (B a))) (~ k) i))
                                  (sym (push a)) k j
                   ; (j = i0) → push a (~ k ∧ i)
                   ; (j = i1) → push a (~ k ∧ i)})
          (inS (push a i))
          k

Bouquet→ΩBouquetSusp : (A : Type ℓ) (B : A → Pointed ℓ')
  → ⋁gen A B → Ω (⋁gen∙ A (λ a → Susp∙ (fst (B a)))) .fst
Bouquet→ΩBouquetSusp A B (inl x) = refl
Bouquet→ΩBouquetSusp A B (inr (a , b)) =
  (push a ∙∙ (λ i → inr (a , toSusp (B a) b i)) ∙∙ sym (push a))
Bouquet→ΩBouquetSusp A B (push a i) j = Bouquet→ΩBouquetSusp-filler A B a i j i1

SuspBouquet→Bouquet : (A : Type ℓ) (B : A → Pointed ℓ')
  → Susp (⋁gen A B) → ⋁gen A (λ a → Susp∙ (fst (B a)))
SuspBouquet→Bouquet A B north = inl tt
SuspBouquet→Bouquet A B south = inl tt
SuspBouquet→Bouquet A B (merid a i) = Bouquet→ΩBouquetSusp A B a i

Bouquet→SuspBouquet : (A : Type ℓ) (B : A → Pointed ℓ')
  → ⋁gen A (λ a → Susp∙ (fst (B a))) → Susp (⋁gen A B)
Bouquet→SuspBouquet A B (inl x) = north
Bouquet→SuspBouquet A B (inr (a , north)) = north
Bouquet→SuspBouquet A B (inr (a , south)) = south
Bouquet→SuspBouquet A B (inr (a , merid b i)) = merid (inr (a , b)) i
Bouquet→SuspBouquet A B (push a i) = north

SuspBouquet-Bouquet-cancel : (A : Type ℓ) (B : A → Pointed ℓ')
    → section (SuspBouquet→Bouquet A B) (Bouquet→SuspBouquet A B)
     × retract (SuspBouquet→Bouquet A B) (Bouquet→SuspBouquet A B)
SuspBouquet-Bouquet-cancel A B = sec , ret
  where
    sec : section (SuspBouquet→Bouquet A B) (Bouquet→SuspBouquet A B)
    sec (inl tt) i = inl tt
    sec (inr (a , north)) = push a
    sec (inr (a , south)) =
         (push a)
      ∙∙ (λ i → inr (a , merid (pt (B a)) i))
      ∙∙ (λ i → inr (a , south))
    sec (inr (a , merid b j)) i =
      hcomp (λ k → λ {(~ i ∧ j = i1) → push a (~ k)
                     ; (i = i1) → inr (a , merid b j)
                     ; (j = i0) → push a (i ∨ (~ k)) })
            (inr (a , (hcomp (λ k → λ {(i = i1) → merid b j
                            ; (j = i0) → north
                            ; (j = i1) → merid (pt (B a)) (i ∨ (~ k))})
                   (merid b j))))
    sec (push a j) i = push a (i ∧ j)

    module _ (a : A) (b : fst (B a)) (i j : I) where
      ret-fill₁ : I →  Susp (⋁gen A B)
      ret-fill₁ k =
        hfill (λ k → λ {(j = i0) → north
                       ; (j = i1) → merid (inr (a , pt (B a))) ((~ k) ∨ i)
                       ; (i = i0) → Bouquet→SuspBouquet A B
                                      (inr (a , compPath-filler (merid b)
                                                 (sym (merid (pt (B a)))) k j))
                       ; (i = i1) → merid (inr (a , b)) j})
              (inS (merid (inr (a , b)) j)) k

      ret-fill₂ : I → Susp (⋁gen A B)
      ret-fill₂ k =
        hfill (λ k → λ {(j = i0) → north
                     ; (j = i1) → merid (push a (~ k)) i
                     ; (i = i0) → Bouquet→SuspBouquet A B
                                    (doubleCompPath-filler (push a)
                                     (λ i → inr (a , toSusp (B a) b i))
                                     (sym (push a)) k j)
                     ; (i = i1) → merid (inr (a , b)) j})
               (inS (ret-fill₁ i1)) k

    ret : retract (SuspBouquet→Bouquet A B) (Bouquet→SuspBouquet A B)
    ret north i = north
    ret south = merid (inl tt)
    ret (merid (inl tt) j) i = merid (inl tt) (i ∧ j)
    ret (merid (inr (a , b)) j) i = ret-fill₂ a b i j i1
    ret (merid (push a k) j) i =
      hcomp (λ r → λ {(i = i0) → Bouquet→SuspBouquet A B
                                   (Bouquet→ΩBouquetSusp-filler A B a k j r)
                     ; (i = i1) → merid (push a (~ r ∨ k)) j
                     ; (j = i0) → north
                     ; (j = i1) → merid (push a (~ r)) i
                     ; (k = i0) → merid (push a (~ r)) (i ∧ j)
                     ; (k = i1) → side r i j}
                     )
            (merid (inr (a , pt (B a))) (i ∧ j))
         where
         side : Cube {A = Susp (⋁gen A B)}
                   (λ i j → merid (inr (a , pt (B a))) (i ∧ j))
                   (λ i j → ret-fill₂ a (pt (B a)) i j i1)
                   (λ r j → Bouquet→SuspBouquet A B
                              (Bouquet→ΩBouquetSusp-filler A B a i1 j r))
                   (λ r j → merid (inr (a , (pt (B a)))) j)
                   (λ r i → north)
                   λ r i → merid (push a (~ r)) i
         side r i j =
           hcomp (λ k
             → λ {(r = i0) → Bouquet→SuspBouquet A B
                                (inr (a , rCancel-filler'
                                           (merid (pt (B a))) i k j))
                 ; (r = i1) →  ret-fill₂ a (pt (B a)) i j k
                 ; (i = i0) → Bouquet→SuspBouquet A B
                                (doubleCompPath-filler
                                  (push a)
                                  (λ j → inr (a
                                    , rCancel' (merid (pt (B a))) (~ r ∧ k) j))
                                  (sym (push a)) (r ∧ k) j)
                 ; (i = i1) → merid (inr (a , snd (B a))) j
                 ; (j = i0) → north
                 ; (j = i1) → merid (push a (~ r ∨ ~ k)) i})
             (hcomp (λ k
               → λ {(r = i0) → Bouquet→SuspBouquet A B
                                  (inr (a , rCancel-filler'
                                             (merid (pt (B a))) (~ k ∨ i) i0 j))
                   ; (r = i1) → ret-fill₁ a (pt (B a)) i j k
                   ; (i = i0) → Bouquet→SuspBouquet A B
                                  (inr (a , compPath-filler
                                             (merid (pt (B a)))
                                             (sym (merid (pt (B a)))) k j))
                   ; (i = i1) → merid (inr (a , snd (B a))) j
                   ; (j = i0) → north
                   ; (j = i1) →  merid (inr (a , snd (B a))) (~ k ∨ i)})
                   (merid (inr (a , snd (B a))) j))

Iso-SuspBouquet-Bouquet : (A : Type ℓ) (B : A → Pointed ℓ')
  → Iso (Susp (⋁gen A B)) (⋁gen A (λ a → Susp∙ (fst (B a))))
Iso.fun (Iso-SuspBouquet-Bouquet A B) = SuspBouquet→Bouquet A B
Iso.inv (Iso-SuspBouquet-Bouquet A B) = Bouquet→SuspBouquet A B
Iso.rightInv (Iso-SuspBouquet-Bouquet A B) = SuspBouquet-Bouquet-cancel A B .fst
Iso.leftInv (Iso-SuspBouquet-Bouquet A B) = SuspBouquet-Bouquet-cancel A B .snd

SuspBouquet≃Bouquet : (A : Type ℓ) (B : A → Pointed ℓ')
  → Susp (⋁gen A B) ≃ ⋁gen A (λ a → Susp∙ (fst (B a)))
SuspBouquet≃Bouquet A B = isoToEquiv (Iso-SuspBouquet-Bouquet A B)
