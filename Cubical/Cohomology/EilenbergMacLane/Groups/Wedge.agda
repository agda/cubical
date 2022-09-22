{-# OPTIONS --safe #-}

module Cubical.Cohomology.EilenbergMacLane.Groups.Wedge where

open import Cubical.Cohomology.EilenbergMacLane.Base

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Connected

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.AbGroup.Base

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as Trunc
open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge

private
  variable
    ℓ ℓ' : Level

module _ {A : Pointed ℓ} {B : Pointed ℓ'} (G : AbGroup ℓ) where
  A∨B = A ⋁ B

  open AbGroupStr (snd G) renaming (_+_ to _+G_ ; -_ to -G_)

  private
    ×H : (n : ℕ) → AbGroup _
    ×H n = dirProdAb (coHomGr (suc n) G (fst A))
                     (coHomGr (suc n) G (fst B))

  Hⁿ×→Hⁿ-⋁ : (n : ℕ) → (A ⋁ B → EM G (suc n))
    → (fst A → EM G (suc n)) × (fst B → EM G (suc n))
  fst (Hⁿ×→Hⁿ-⋁ n f) x = f (inl x)
  snd (Hⁿ×→Hⁿ-⋁ n f) x = f (inr x)

  Hⁿ-⋁→Hⁿ× : (n : ℕ)
    → (f : fst A → EM G (suc n))
    → (g : fst B → EM G (suc n))
    → (A ⋁ B → EM G (suc n))
  Hⁿ-⋁→Hⁿ× n f g (inl x) = f x -[ (suc n) ]ₖ f (pt A)
  Hⁿ-⋁→Hⁿ× n f g (inr x) = g x -[ (suc n) ]ₖ g (pt B)
  Hⁿ-⋁→Hⁿ× n f g (push a i) =
    (rCancelₖ (suc n) (f (pt A)) ∙ sym (rCancelₖ (suc n) (g (pt B)))) i

  Hⁿ⋁-Iso : (n : ℕ)
    → Iso (coHom (suc n) G (A ⋁ B))
           (coHom (suc n) G (fst A)
          × coHom (suc n) G (fst B))
  Iso.fun (Hⁿ⋁-Iso n) =
    ST.rec (isSet× squash₂ squash₂)
      λ f → ∣ f ∘ inl ∣₂ , ∣ f ∘ inr ∣₂
  Iso.inv (Hⁿ⋁-Iso n) =
    uncurry (ST.rec2 squash₂ λ f g → ∣ Hⁿ-⋁→Hⁿ× n f g ∣₂)
  Iso.rightInv (Hⁿ⋁-Iso n) =
    uncurry (ST.elim2
      (λ _ _ → isOfHLevelPath 2 (isSet× squash₂ squash₂) _ _)
      λ f g
      → ΣPathP (Trunc.rec (isProp→isOfHLevelSuc n (squash₂ _ _))
                (λ p → cong ∣_∣₂ (funExt λ x → cong (λ z → f x +[ (suc n) ]ₖ z)
                                 (cong (λ z → -[ (suc n) ]ₖ z) p ∙ -0ₖ (suc n))
                              ∙ rUnitₖ (suc n) (f x)))
              (isConnectedPath (suc n)
               (isConnectedEM (suc n)) (f (pt A)) (0ₖ (suc n)) .fst)
            , Trunc.rec (isProp→isOfHLevelSuc n (squash₂ _ _))
                (λ p → cong ∣_∣₂ (funExt λ x → cong (λ z → g x +[ (suc n) ]ₖ z)
                                 (cong (λ z → -[ (suc n) ]ₖ z) p ∙ -0ₖ (suc n))
                              ∙ rUnitₖ (suc n) (g x)))
              (isConnectedPath (suc n)
               (isConnectedEM (suc n)) (g (pt B)) (0ₖ (suc n)) .fst)))
  Iso.leftInv (Hⁿ⋁-Iso n) =
    ST.elim (λ _ → isSetPathImplicit)
      λ f → Trunc.rec (isProp→isOfHLevelSuc n (squash₂ _ _))
        (λ p → cong ∣_∣₂
          (funExt λ { (inl x) → pgen f p (inl x)
                    ; (inr x) → p₂ f p x
                    ; (push a i) j → Sq f p j i}))
        (Iso.fun (PathIdTruncIso (suc n))
          (isContr→isProp (isConnectedEM {G' = G}  (suc n))
            ∣ f (inl (pt A)) ∣ ∣ 0ₖ (suc n) ∣ ))
    where
    module _ (f : (A ⋁ B → EM G (suc n))) (p : f (inl (pt A)) ≡ 0ₖ (suc n))
      where
      pgen : (x : A ⋁ B) → _ ≡ _
      pgen x =
          (λ j → f x -[ (suc n) ]ₖ (p j))
       ∙∙ (λ j → f x +[ (suc n) ]ₖ (-0ₖ (suc n) j))
       ∙∙ rUnitₖ (suc n) (f x)

      p₂ : (x : typ B) → _ ≡ _
      p₂ x = (λ j → f (inr x) -[ (suc n) ]ₖ (f (sym (push tt) j)))
            ∙ pgen (inr x)


      Sq : Square (rCancelₖ (suc n) (f (inl (pt A)))
                    ∙ sym (rCancelₖ (suc n) (f (inr (pt B)))))
                   (cong f (push tt))
                   (pgen (inl (pt A)))
                   (p₂ (pt B))
      Sq i j =
        hcomp (λ k → λ {(i = i0) → (rCancelₖ (suc n) (f (inl (pt A)))
                                   ∙ sym (rCancelₖ (suc n) (f (push tt k)))) j
                       ; (i = i1) → f (push tt (k ∧ j))
                       ; (j = i0) → pgen (inl (pt A)) i
                       ; (j = i1) → ((λ j → f (push tt k) -[ (suc n) ]ₖ
                                             (f (sym (push tt) (j ∨ ~ k))))
                                    ∙ pgen (push tt k)) i})
         (hcomp (λ k → λ {(i = i0) → rCancel (rCancelₖ (suc n)
                                               (f (inl (pt A)))) (~ k) j
                         ; (i = i1) → f (inl (pt A))
                         ; (j = i0) → pgen (inl (pt A)) i
                         ; (j = i1) → lUnit (pgen (inl (pt A))) k i})
                (pgen (inl (pt A)) i))

  Hⁿ-⋁≅Hⁿ×Hⁿ : (n : ℕ)
    → AbGroupEquiv
        (coHomGr (suc n) G (A ⋁ B))
        (dirProdAb (coHomGr (suc n) G (fst A)) (coHomGr (suc n) G (fst B)))
  fst (Hⁿ-⋁≅Hⁿ×Hⁿ n) = isoToEquiv (Hⁿ⋁-Iso n)
  snd (Hⁿ-⋁≅Hⁿ×Hⁿ n) =
    makeIsGroupHom
      (ST.elim2 (λ _ _ → isOfHLevelPath 2 (isSet× squash₂ squash₂) _ _)
      λ f g → refl)
