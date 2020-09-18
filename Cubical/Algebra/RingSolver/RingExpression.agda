{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.RingSolver.RingExpression where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
open import Cubical.Algebra.RingSolver.AlmostRing
open import Cubical.Algebra.RingSolver.RawRing renaming (⟨_⟩ to ⟨_⟩ᵣ)

private
  variable
    ℓ : Level

infixl 6 _⊕_
infixl 7 _⊗_

-- Expression in an almost ring on A with n variables
data Expr {ℓ} (A : Type ℓ) (n : ℕ) : Type ℓ where
  K : A → Expr A n
  ∣ : Fin n → Expr A n
  _⊕_ : Expr A n → Expr A n → Expr A n
  _⊗_ : Expr A n → Expr A n → Expr A n
--  _⊛_ : Expr A n → ℕ → Expr A n    -- exponentiation
  ⊝_ : Expr A n → Expr A n

-- there are probably things I don't get yet...
module Eval (R : RawRing {ℓ}) where
  open import Cubical.Data.Vec
  open RawRing R

  ⟦_⟧ : ∀ {n} → Expr ⟨ R ⟩ᵣ n → Vec ⟨ R ⟩ᵣ n → ⟨ R ⟩ᵣ
  ⟦ K r ⟧ v = r
  ⟦ ∣ k ⟧ v = lookup k v
  ⟦ x ⊕ y ⟧ v =  ⟦ x ⟧ v + ⟦ y ⟧ v
  ⟦ x ⊗ y ⟧ v = ⟦ x ⟧ v · ⟦ y ⟧ v
--  ⟦ x ⊛ l ⟧ v =  ⟦ x ⟧ v ^ l
  ⟦ ⊝ x ⟧ v = - ⟦ x ⟧ v

data RawHornerPolynomial (R : RawRing {ℓ}) : Type ℓ where
  0H : RawHornerPolynomial R
  _·X+_ : RawHornerPolynomial R → ⟨ R ⟩ᵣ → RawHornerPolynomial R


module Horner (R : RawRing {ℓ}) where
  open RawRing R

  1H : RawHornerPolynomial R
  1H = 0H ·X+ 1r

  X : RawHornerPolynomial R
  X = 1H ·X+ 0r

  _+H_ : RawHornerPolynomial R → RawHornerPolynomial R → RawHornerPolynomial R
  0H +H Q = Q
  (P ·X+ r) +H 0H = P ·X+ r
  (P ·X+ r) +H (Q ·X+ s) = (P +H Q) ·X+ (r + s)

  _⋆_ : ⟨ R ⟩ᵣ → RawHornerPolynomial R → RawHornerPolynomial R
  r ⋆ 0H = 0H
  r ⋆ (P ·X+ s) = (r ⋆ P) ·X+ (r · s)

  _·H_ : RawHornerPolynomial R → RawHornerPolynomial R → RawHornerPolynomial R
  0H ·H _ = 0H
  (P ·X+ r) ·H Q = ((P ·H Q) ·X+ 0r) +H (r ⋆ Q)

  -H_ : RawHornerPolynomial R → RawHornerPolynomial R
  -H 0H = 0H
  -H (P ·X+ r) = (-H P) ·X+ (- r)

  evalH : RawHornerPolynomial R → ⟨ R ⟩ᵣ → ⟨ R ⟩ᵣ
  evalH 0H x₀ = 0r
  evalH (P ·X+ r) x₀ = (evalH P x₀) · x₀ + r

module Normalize (R : AlmostRing {ℓ}) where
  νR = AlmostRing→RawRing R
  open AlmostRing R
  open Theory R
  open Horner νR
  open Eval νR

  -EvalDist :
    (P : RawHornerPolynomial νR) (x : ⟨ R ⟩)
    → evalH (-H P) x ≡ - evalH P x
  -EvalDist 0H x = 0r ≡⟨ sym 0IsSelfinverse ⟩ - 0r ∎
  -EvalDist (P ·X+ r) x =
         evalH (-H (P ·X+ r)) x        ≡⟨ refl ⟩
         evalH ((-H P) ·X+ (- r)) x    ≡⟨ refl ⟩
         (evalH (-H P) x) · x + (- r)  ≡⟨ cong (λ u → (u · x) + (- r)) (-EvalDist P x) ⟩
         (- evalH P x) · x + (- r)     ≡⟨ cong (λ u → u + (- r)) (sym (-Comm· _ _)) ⟩
         - (evalH P x) · x + (- r)     ≡⟨ sym (-Dist+ _ _) ⟩
         - ((evalH P x) · x + r)       ≡⟨ refl ⟩
         - evalH (P ·X+ r) x ∎

  +HomEval : (P Q : RawHornerPolynomial νR) (x : ⟨ R ⟩)
    → evalH (P +H Q) x ≡ (evalH P x) + (evalH Q x)
  +HomEval 0H Q x = sym (+Lid _)
  +HomEval (P ·X+ r) 0H x = sym (+Rid _)
  +HomEval (P ·X+ r) (Q ·X+ s) x =
    evalH ((P +H Q) ·X+ (r + s)) x              ≡⟨ refl ⟩
    evalH (P +H Q) x · x + (r + s)              ≡⟨ cong (λ u → (u · x) + (r + s)) (+HomEval P Q x) ⟩
    (evalH P x + evalH Q x) · x + (r + s)       ≡⟨ cong (λ u → u + (r + s)) (·DistL+ _ _ _) ⟩
    (evalH P x) · x + (evalH Q x) · x + (r + s) ≡⟨ +ShufflePairs _ _ _ _ ⟩
    evalH (P ·X+ r) x + evalH (Q ·X+ s) x ∎

  ⋆0LeftAnnihilates : (P : RawHornerPolynomial νR) (x : ⟨ R ⟩)
    → evalH (0r ⋆ P) x ≡ 0r
  ⋆0LeftAnnihilates 0H x = cong (λ u → evalH u x) (λ _ → 0H)
  ⋆0LeftAnnihilates (P ·X+ r) x =
    evalH ((0r ⋆ P) ·X+ (0r · r)) x ≡⟨ cong (λ u → evalH ((0r ⋆ P) ·X+ u) x) (0LeftAnnihilates _) ⟩
    evalH ((0r ⋆ P) ·X+ 0r) x       ≡⟨ refl ⟩
    (evalH (0r ⋆ P) x) · x + 0r     ≡⟨ +Rid _ ⟩
    (evalH (0r ⋆ P) x) · x          ≡⟨ cong (λ u → u · x)
                                            (⋆0LeftAnnihilates P x) ⟩
    0r · x                          ≡⟨ 0LeftAnnihilates _ ⟩
    0r ∎

  ⋆HomEval :  (r : ⟨ R ⟩) (P : RawHornerPolynomial νR) (x : ⟨ R ⟩)
           → evalH (r ⋆ P) x ≡ r · evalH P x
  ⋆HomEval r 0H x = 0r ≡⟨ sym (0RightAnnihilates _) ⟩ r · 0r ∎
  ⋆HomEval r (P ·X+ s) x =
    (evalH (r ⋆ P) x) · x + (r · s) ≡⟨ cong (λ u → (u · x) + (r · s)) (⋆HomEval r P x) ⟩
    r · (evalH P x) · x + (r · s)   ≡⟨ cong (λ u → u + (r · s)) (sym (·Assoc _ _ _)) ⟩
    r · ((evalH P x) · x) + (r · s) ≡⟨ sym (·DistR+ r _ _) ⟩
    r · ((evalH P x) · x + s)       ≡⟨ refl ⟩
    r · evalH (P ·X+ s) x ∎

  ·HomEval : (P Q : RawHornerPolynomial νR) (x : ⟨ R ⟩)
    → evalH (P ·H Q) x ≡ (evalH P x) · (evalH Q x)
  ·HomEval 0H Q x = 0r ≡⟨ sym (0LeftAnnihilates _) ⟩ 0r · evalH Q x ∎
  ·HomEval (P ·X+ r) Q x =
    evalH (((P ·H Q) ·X+ 0r) +H (r ⋆ Q)) x           ≡⟨ +HomEval ((P ·H Q) ·X+ 0r) (r ⋆ Q) x ⟩
    evalH ((P ·H Q) ·X+ 0r) x + evalH (r ⋆ Q) x      ≡⟨ cong (λ u → u + evalH (r ⋆ Q) x) (+Rid _) ⟩
    (evalH (P ·H Q) x) · x + evalH (r ⋆ Q) x         ≡⟨ cong (λ u → (u · x) + evalH (r ⋆ Q) x)
                                                             (·HomEval P Q x) ⟩ 
    (evalH P x) · (evalH Q x) · x + evalH (r ⋆ Q) x  ≡⟨ cong (λ u → u + evalH (r ⋆ Q) x)
                                                             (sym (·CommRight _ _ _)) ⟩ 
    (evalH P x) · x · (evalH Q x) + evalH (r ⋆ Q) x  ≡⟨ cong (λ u → ((evalH P x · x) · evalH Q x) + u)
                                                             (⋆HomEval r Q x) ⟩ 
    (evalH P x) · x · (evalH Q x) + r · evalH Q x    ≡⟨ sym (·DistL+ _ _ _) ⟩ 
    ((evalH P x) · x + r) · evalH Q x                ≡⟨ refl ⟩
    evalH (P ·X+ r) x · evalH Q x ∎

  Reify : Expr ⟨ R ⟩ 1 → RawHornerPolynomial νR
  Reify (K r) = 0H ·X+ r
  Reify (∣ k) = X
  Reify (x ⊕ y) = (Reify x) +H (Reify y)
  Reify (x ⊗ y) = (Reify x) ·H (Reify y)
  Reify (⊝ x) =  -H (Reify x)

  sound : (e : Expr ⟨ R ⟩ 1) (x : ⟨ R ⟩)
          → evalH (Reify e) x ≡ ⟦ e ⟧ (x ∷ [])
  sound (K r) x = 0r · x + r ≡⟨ cong (λ u → u + r) (0LeftAnnihilates x) ⟩
                      0r + r ≡⟨ +Lid r ⟩
                           r ∎
  sound (∣ zero) x = (0r · x + 1r) · x + 0r ≡⟨ +Rid _ ⟩
                          (0r · x + 1r) · x ≡⟨ cong (λ u → (u + 1r) · x)
                                                    (0LeftAnnihilates x) ⟩
                              (0r + 1r) · x ≡⟨ cong (λ u → u · x) (+Lid _) ⟩
                                     1r · x ≡⟨ ·Lid _ ⟩
                                          x ∎
  sound (⊝ e) x = evalH (-H (Reify e)) x ≡⟨ -EvalDist (Reify e) x ⟩
                  - evalH (Reify e) x ≡⟨ cong (λ u → - u) (sound e x) ⟩
                  - ⟦ e ⟧ (x ∷ []) ∎
  sound (e ⊕ e₁) x =
        evalH (Reify e +H Reify e₁) x                ≡⟨ +HomEval (Reify e) (Reify e₁) x ⟩
        (evalH (Reify e) x) + (evalH (Reify e₁) x)   ≡⟨
                                                        cong
                                                         (λ u → evalH (Reify e) x + u)
                                                         (sound e₁ x) ⟩
        (evalH (Reify e) x) + (⟦ e₁ ⟧ (x ∷ []))      ≡⟨ cong
                                                          (λ u → u + ⟦ e₁ ⟧ (x ∷ []))
                                                          (sound e x) ⟩
        (⟦ e ⟧ (x ∷ [])) + (⟦ e₁ ⟧ (x ∷ [])) ∎
  sound (e ⊗ e₁) x =
    evalH (Reify e ·H Reify e₁) x          ≡⟨ ·HomEval (Reify e) (Reify e₁) x ⟩
    evalH (Reify e) x · evalH (Reify e₁) x ≡⟨ cong (λ u → evalH (Reify e) x · u) (sound  e₁ x) ⟩
    evalH (Reify e) x · ⟦ e₁ ⟧ (x ∷ [])    ≡⟨ cong (λ u → u · ⟦ e₁ ⟧ (x ∷ [])) (sound e x) ⟩
    ⟦ e ⟧ (x ∷ []) · ⟦ e₁ ⟧ (x ∷ []) ∎
