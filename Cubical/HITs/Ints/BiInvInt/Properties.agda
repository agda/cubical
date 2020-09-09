{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Ints.BiInvInt.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Int as Int
open import Cubical.Data.Bool

open import Cubical.HITs.Ints.BiInvInt.Base renaming (BiInvInt to ℤ)

infixl 6 _+_ _-_
infixl 7 _*_

-- To prove a property P about ℤ, we need to show:
-- * P zero
-- * If P n, then P (suc n)
-- * If P n, then P (pred n)
ℤ-ind-prop :
  ∀ {ℓ} {P : ℤ → Type ℓ} → (∀ n → isProp (P n)) →
  P zero → (∀ n → P n → P (suc n)) → (∀ n → P n → P (pred n)) →
  (n : ℤ) → P n
ℤ-ind-prop {P = P} P-isProp P-zero P-suc P-pred = φ
  where
  P-predr : ∀ n → P n → P (predr n)
  P-predr n x = subst P (predl≡predr n) (P-pred n x)

  P-predl : ∀ n → P n → P (predl n)
  P-predl = P-pred

  P-isProp' : {a b : ℤ} (p : a ≡ b) (x : P a) (y : P b) → PathP (λ i → P (p i)) x y
  P-isProp' _ _ _ = toPathP (P-isProp _ _ _)

  φ : (n : ℤ) → P n
  φ zero = P-zero
  φ (suc n) = P-suc n (φ n)
  φ (predr n) = P-predr n (φ n)
  φ (suc-predr n i) = P-isProp' (suc-predr n) (P-suc (predr n) (P-predr n (φ n))) (φ n) i
  φ (predl n) = P-predl n (φ n)
  φ (predl-suc n i) = P-isProp' (predl-suc n) (P-predl (suc n) (P-suc n (φ n))) (φ n) i

-- A function ℤ → A is the same as a point in A and an equivalence A → A
ℤ-rec : ∀ {ℓ} {A : Type ℓ} → A → A ≃ A → ℤ → A
ℤ-rec {A = A} z e = φ
  where
  e-Iso : Iso A A
  e-Iso = equivToIso e

  φ : ℤ → A
  φ zero = z
  φ (suc n) = Iso.fun e-Iso (φ n)
  φ (predr n) = Iso.inv e-Iso (φ n)
  φ (suc-predr n i) = Iso.rightInv e-Iso (φ n) i
  φ (predl n) = Iso.inv e-Iso (φ n)
  φ (predl-suc n i) = Iso.leftInv e-Iso (φ n) i

sucEquiv : ℤ ≃ ℤ
sucEquiv = isoToEquiv (iso suc pred suc-predl predl-suc)

-- addition

-- the following equalities hold definitionally:
--   zero   + n ≡ n
--   suc m  + n ≡ suc (m + n)
--   pred m + n ≡ pred (m + n)
_+_ : ℤ → ℤ → ℤ
_+_ = ℤ-rec (idfun ℤ) (postCompEquiv sucEquiv)

-- properties of addition

+-zero : ∀ n → n + zero ≡ n
+-zero = ℤ-ind-prop (λ _ → isSetBiInvInt _ _) refl (λ n p → cong suc p) (λ n p → cong pred p)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc = ℤ-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ m → refl)
  (λ m p n → cong suc (p n))
  (λ m p n → cong pred (p n) ∙ predl-suc (m + n) ∙ sym (suc-predl (m + n)))

+-pred : ∀ m n → m + pred n ≡ pred (m + n)
+-pred = ℤ-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ m → refl)
  (λ m p n → cong suc (p n) ∙ suc-predl (m + n) ∙ sym (predl-suc (m + n)))
  (λ m p n → cong pred (p n))

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = +-comm' n m
  where
  +-comm' : ∀ n m → m + n ≡ n + m
  +-comm' = ℤ-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
    +-zero
    (λ n p m → +-suc m n ∙ cong suc (p m))
    (λ n p m → +-pred m n ∙ cong pred (p m))

+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc = ℤ-ind-prop (λ _ → isPropΠ2 λ _ _ → isSetBiInvInt _ _)
  (λ n o → refl)
  (λ m p n o → cong suc (p n o))
  (λ m p n o → cong pred (p n o))

-- negation / subtraction

-- the following equalities hold definitionally:
--   - zero     ≡ zero
--   - (suc m)  ≡ pred m
--   - (pred m) ≡ suc m
-_ : ℤ → ℤ
-_ = ℤ-rec zero (invEquiv sucEquiv)

_-_ : ℤ → ℤ → ℤ
m - n = m + (- n)

+-invˡ : ∀ n → (- n) + n ≡ zero
+-invˡ = ℤ-ind-prop (λ _ → isSetBiInvInt _ _)
  refl
  (λ n p → cong pred (+-suc (- n) n) ∙ predl-suc _ ∙ p)
  (λ n p → cong suc (+-pred (- n) n) ∙ suc-predl _ ∙ p)

+-invʳ : ∀ n → n + (- n) ≡ zero
+-invʳ = ℤ-ind-prop (λ _ → isSetBiInvInt _ _)
  refl
  (λ n p → cong suc (+-pred n (- n)) ∙ suc-predl _ ∙ p)
  (λ n p → cong pred (+-suc n (- n)) ∙ predl-suc _ ∙ p)

inv-hom : ∀ m n → - (m + n) ≡ (- m) + (- n)
inv-hom = ℤ-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ n → refl)
  (λ m p n → cong pred (p n))
  (λ m p n → cong suc (p n))

-- natural injections from ℕ

pos : ℕ → ℤ
pos ℕ.zero = zero
pos (ℕ.suc n) = suc (pos n)

neg : ℕ → ℤ
neg ℕ.zero = zero
neg (ℕ.suc n) = pred (neg n)

-- absolute value and sign
-- (Note that there doesn't appear to be any way around using
--  bwd here! Any direct proof ends up doing the same work...)

abs : ℤ → ℕ
abs n = Int.abs (bwd n)

sgn : ℤ → Bool
sgn n = Int.sgn (bwd n)

isEquiv-n+ : ∀ n → isEquiv (n +_)
isEquiv-n+ n = isoToIsEquiv (iso (n +_) ((- n) +_) sec ret)
  where
  sec : ∀ m → n + ((- n) + m) ≡ m
  sec m = +-assoc n (- n) m ∙ cong (_+ m) (+-invʳ n)

  ret : ∀ m → (- n) + (n + m) ≡ m
  ret m = +-assoc (- n) n m ∙ cong (_+ m) (+-invˡ n)

-- multiplication

-- the following equalities hold definitionally:
--   zero   * n ≡ zero
--   suc m  * n ≡ n + m * n
--   pred m * n ≡ (- n) + m * n
_*_ : ℤ → ℤ → ℤ
m * n = ℤ-rec zero (n +_ , isEquiv-n+ n) m

-- properties of multiplication

*-zero : ∀ n → n * zero ≡ zero
*-zero = ℤ-ind-prop (λ _ → isSetBiInvInt _ _) refl (λ n p → p) (λ n p → p)

*-suc : ∀ m n → m * suc n ≡ m + m * n
*-suc = ℤ-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ n → refl)
  (λ m p n → cong suc
    (cong (n +_) (p n) ∙ +-assoc n m (m * n) ∙
     cong (_+ m * n) (+-comm n m) ∙ sym (+-assoc m n (m * n))))
  (λ m p n → cong pred
    (cong (- n +_) (p n) ∙ +-assoc (- n) m (m * n) ∙
     cong (_+ m * n) (+-comm (- n) m) ∙ sym (+-assoc m (- n) (m * n))))

*-pred : ∀ m n → m * pred n ≡ (- m) + m * n
*-pred = ℤ-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ n → refl)
  (λ m p n → cong pred
    (cong (n +_) (p n) ∙ +-assoc n (- m) (m * n) ∙
     cong (_+ m * n) (+-comm n (- m)) ∙ sym (+-assoc (- m) n (m * n))))
  (λ m p n → cong suc
    (cong (- n +_) (p n) ∙ +-assoc (- n) (- m) (m * n) ∙
     cong (_+ m * n) (+-comm (- n) (- m)) ∙ sym (+-assoc (- m) (- n) (m * n))))

*-comm : ∀ m n → m * n ≡ n * m
*-comm = ℤ-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ n → sym (*-zero n))
  (λ m p n → cong (n +_) (p n) ∙ sym (*-suc n m))
  (λ m p n → cong (- n +_) (p n) ∙ sym (*-pred n m))

*-identityˡ : ∀ m → suc zero * m ≡ m
*-identityˡ = +-zero

*-identityʳ : ∀ m → m * suc zero ≡ m
*-identityʳ m = *-comm m (suc zero) ∙ *-identityˡ m

*-distribʳ : ∀ m n o → (m * o) + (n * o) ≡ (m + n) * o
*-distribʳ = ℤ-ind-prop (λ _ → isPropΠ2 λ _ _ → isSetBiInvInt _ _)
  (λ n o → refl)
  (λ m p n o → sym (+-assoc o (m * o) (n * o)) ∙ cong (o +_) (p n o))
  (λ m p n o → sym (+-assoc (- o) (m * o) (n * o)) ∙ cong (- o +_) (p n o))

*-distribˡ : ∀ o m n → (o * m) + (o * n) ≡ o * (m + n)
*-distribˡ o m n =
  cong (_+ o * n) (*-comm o m) ∙ cong (m * o +_) (*-comm o n) ∙
  *-distribʳ m n o ∙ *-comm (m + n) o

*-inv : ∀ m n → m * (- n) ≡ - (m * n)
*-inv = ℤ-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ n → refl)
  (λ m p n → cong (- n +_) (p n) ∙ sym (inv-hom n (m * n)))
  (λ m p n → cong (- (- n) +_) (p n) ∙ sym (inv-hom (- n) (m * n)))

inv-* : ∀ m n → (- m) * n ≡ - (m * n)
inv-* m n = *-comm (- m) n ∙ *-inv n m ∙ cong (-_) (*-comm n m)

*-assoc : ∀ m n o → m * (n * o) ≡ (m * n) * o
*-assoc = ℤ-ind-prop (λ _ → isPropΠ2 λ _ _ → isSetBiInvInt _ _)
  (λ n o → refl)
  (λ m p n o →
    cong (n * o +_) (p n o) ∙ *-distribʳ n (m * n) o)
  (λ m p n o →
    cong (- (n * o) +_) (p n o) ∙ cong (_+ m * n * o) (sym (inv-* n o)) ∙
    *-distribʳ (- n) (m * n) o)
