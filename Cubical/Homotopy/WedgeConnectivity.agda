{-# OPTIONS --safe #-}
module Cubical.Homotopy.WedgeConnectivity where

open import Cubical.Foundations.Everything
open import Cubical.Data.HomotopyGroup
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.Nullification
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as Trunc
open import Cubical.Homotopy.Connected

module WedgeConnectivity {ℓ ℓ' ℓ''} (n m : ℕ)
  (A : Pointed ℓ) (connA : isConnected (suc n) (typ A))
  (B : Pointed ℓ') (connB : isConnected (suc m) (typ B))
  (P : typ A → typ B → TypeOfHLevel ℓ'' (n + m))
  (f : (a : typ A) → P a (pt B) .fst)
  (g : (b : typ B) → P (pt A) b .fst)
  (p : f (pt A) ≡ g (pt B))
  where

  private
    Q : typ A → TypeOfHLevel _ n
    Q a =
      ( (Σ[ k ∈ ((b : typ B) → P a b .fst) ] k (pt B) ≡ f a)
      , isOfHLevelRetract n
          (λ {(h , q) → h , funExt λ _ → q})
          (λ {(h , q) → h , funExt⁻ q _})
          (λ _ → refl)
          (isOfHLevelPrecomposeConnected n m (P a) (λ _ → pt B)
            (isConnectedPoint m connB (pt B)) (λ _ → f a))
      )

    main : isContr (fiber (λ s _ → s (pt A)) (λ _ → g , p ⁻¹))
    main =
      elim.isEquivPrecompose (λ _ → pt A) n Q
        (isConnectedPoint n connA (pt A))
        .equiv-proof (λ _ → g , p ⁻¹)


  extension : ∀ a b → P a b .fst
  extension a b = main .fst .fst a .fst b

  left : ∀ a → extension a (pt B) ≡ f a
  left a = main .fst .fst a .snd

  right : ∀ b → extension (pt A) b ≡ g b
  right = funExt⁻ (cong fst (funExt⁻ (main .fst .snd) _))

  hom : left (pt A) ⁻¹ ∙ right (pt B) ≡ p
  hom i j = hcomp (λ k → λ { (i = i1) → p j
                           ; (j = i0) → (cong snd (funExt⁻ (main .fst .snd) tt)) i (~ j)
                           ; (j = i1) → right (pt B) (i ∨ k)})
                  (cong snd (funExt⁻ (main .fst .snd) tt) i (~ j))

  hom' : left (pt A) ≡ right (pt B) ∙ sym p
  hom' = (lUnit (left _) ∙ cong (_∙ left (pt A)) (sym (rCancel (right (pt B)))))
       ∙∙ sym (assoc _ _ _)
       ∙∙ cong (right (pt B) ∙_) (sym (symDistr (left (pt A) ⁻¹) (right (pt B))) ∙ (cong sym hom))

  homSquare : PathP (λ i → extension (pt A) (pt B) ≡ p i) (left (pt A)) (right (pt B))
  homSquare i j = hcomp (λ k → λ { (i = i0) → left (pt A) j
                                 ; (i = i1) → compPath-filler (right (pt B)) (sym p) (~ k) j
                                 ; (j = i0) → extension (pt A) (pt B)
                                 ; (j = i1) → p (i ∧ k) })
                        (hom' i j)
