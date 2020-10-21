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

open import Cubical.HITs.Ints.BiInvInt.Base

infixl 6 _+_ _-_
infixl 7 _·_

-- To prove a property P about BiInvInt, we need to show:
-- * P zero
-- * If P n, then P (suc n)
-- * If P n, then P (pred n)
BiInvInt-ind-prop :
  ∀ {ℓ} {P : BiInvInt → Type ℓ} → (∀ n → isProp (P n)) →
  P zero → (∀ n → P n → P (suc n)) → (∀ n → P n → P (pred n)) →
  (n : BiInvInt) → P n
BiInvInt-ind-prop {P = P} P-isProp P-zero P-suc P-pred = φ
  where
  P-predr : ∀ n → P n → P (predr n)
  P-predr n x = subst P (predl≡predr n) (P-pred n x)

  P-predl : ∀ n → P n → P (predl n)
  P-predl = P-pred

  P-isProp' : {a b : BiInvInt} (p : a ≡ b) (x : P a) (y : P b) → PathP (λ i → P (p i)) x y
  P-isProp' _ _ _ = toPathP (P-isProp _ _ _)

  φ : (n : BiInvInt) → P n
  φ zero = P-zero
  φ (suc n) = P-suc n (φ n)
  φ (predr n) = P-predr n (φ n)
  φ (suc-predr n i) = P-isProp' (suc-predr n) (P-suc (predr n) (P-predr n (φ n))) (φ n) i
  φ (predl n) = P-predl n (φ n)
  φ (predl-suc n i) = P-isProp' (predl-suc n) (P-predl (suc n) (P-suc n (φ n))) (φ n) i

-- To define a function BiInvInt → A, we need:
-- · a point z : A for zero
-- · an equivalence s : A ≃ A for suc/pred
BiInvInt-rec : ∀ {ℓ} {A : Type ℓ} → A → A ≃ A → BiInvInt → A
BiInvInt-rec {A = A} z e = φ
  where
  e-Iso : Iso A A
  e-Iso = equivToIso e

  φ : BiInvInt → A
  φ zero = z
  φ (suc n) = Iso.fun e-Iso (φ n)
  φ (predr n) = Iso.inv e-Iso (φ n)
  φ (suc-predr n i) = Iso.rightInv e-Iso (φ n) i
  φ (predl n) = Iso.inv e-Iso (φ n)
  φ (predl-suc n i) = Iso.leftInv e-Iso (φ n) i

sucIso : Iso BiInvInt BiInvInt
Iso.fun sucIso = suc
Iso.inv sucIso = pred
Iso.rightInv sucIso = suc-predl
Iso.leftInv sucIso = predl-suc

sucEquiv : BiInvInt ≃ BiInvInt
sucEquiv = isoToEquiv sucIso

-- addition

-- the following equalities hold definitionally:
--   zero   + n ≡ n
--   suc m  + n ≡ suc (m + n)
--   pred m + n ≡ pred (m + n)
_+_ : BiInvInt → BiInvInt → BiInvInt
_+_ = BiInvInt-rec (idfun BiInvInt) (postCompEquiv sucEquiv)

-- properties of addition

+-zero : ∀ n → n + zero ≡ n
+-zero = BiInvInt-ind-prop (λ _ → isSetBiInvInt _ _) refl (λ n p → cong suc p) (λ n p → cong pred p)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc = BiInvInt-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ m → refl)
  (λ m p n → cong suc (p n))
  (λ m p n → cong pred (p n) ∙ predl-suc (m + n) ∙ sym (suc-predl (m + n)))

+-pred : ∀ m n → m + pred n ≡ pred (m + n)
+-pred = BiInvInt-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ m → refl)
  (λ m p n → cong suc (p n) ∙ suc-predl (m + n) ∙ sym (predl-suc (m + n)))
  (λ m p n → cong pred (p n))

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = +-comm' n m
  where
  +-comm' : ∀ n m → m + n ≡ n + m
  +-comm' = BiInvInt-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
    +-zero
    (λ n p m → +-suc m n ∙ cong suc (p m))
    (λ n p m → +-pred m n ∙ cong pred (p m))

+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc = BiInvInt-ind-prop (λ _ → isPropΠ2 λ _ _ → isSetBiInvInt _ _)
  (λ n o → refl)
  (λ m p n o → cong suc (p n o))
  (λ m p n o → cong pred (p n o))

-- negation / subtraction

-- the following equalities hold definitionally:
--   - zero     ≡ zero
--   - (suc m)  ≡ pred m
--   - (pred m) ≡ suc m
-_ : BiInvInt → BiInvInt
-_ = BiInvInt-rec zero (invEquiv sucEquiv)

_-_ : BiInvInt → BiInvInt → BiInvInt
m - n = m + (- n)

+-invˡ : ∀ n → (- n) + n ≡ zero
+-invˡ = BiInvInt-ind-prop (λ _ → isSetBiInvInt _ _)
  refl
  (λ n p → cong pred (+-suc (- n) n) ∙ predl-suc _ ∙ p)
  (λ n p → cong suc (+-pred (- n) n) ∙ suc-predl _ ∙ p)

+-invʳ : ∀ n → n + (- n) ≡ zero
+-invʳ = BiInvInt-ind-prop (λ _ → isSetBiInvInt _ _)
  refl
  (λ n p → cong suc (+-pred n (- n)) ∙ suc-predl _ ∙ p)
  (λ n p → cong pred (+-suc n (- n)) ∙ predl-suc _ ∙ p)

inv-hom : ∀ m n → - (m + n) ≡ (- m) + (- n)
inv-hom = BiInvInt-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ n → refl)
  (λ m p n → cong pred (p n))
  (λ m p n → cong suc (p n))

-- natural injections from ℕ

pos : ℕ → BiInvInt
pos ℕ.zero = zero
pos (ℕ.suc n) = suc (pos n)

neg : ℕ → BiInvInt
neg ℕ.zero = zero
neg (ℕ.suc n) = pred (neg n)

-- Natural number and negative integer literals for BiInvInt

open import Cubical.Data.Nat.Literals public

instance
  fromNatBiInvInt : HasFromNat BiInvInt
  fromNatBiInvInt = record { Constraint = λ _ → Unit ; fromNat = λ n → pos n }

instance
  fromNegBiInvInt : HasFromNeg BiInvInt
  fromNegBiInvInt = record { Constraint = λ _ → Unit ; fromNeg = λ n → neg n }

-- absolute value and sign
-- (Note that there doesn't appear to be any way around using
--  bwd here! Any direct proof ends up doing the same work...)

abs : BiInvInt → ℕ
abs n = Int.abs (bwd n)

sgn : BiInvInt → Bool
sgn n = Int.sgn (bwd n)

Iso-n+ : (n : BiInvInt) → Iso BiInvInt BiInvInt
Iso.fun (Iso-n+ n) = n +_
Iso.inv (Iso-n+ n) = - n +_
Iso.rightInv (Iso-n+ n) m = +-assoc n (- n) m ∙ cong (_+ m) (+-invʳ n)
Iso.leftInv (Iso-n+ n) m = +-assoc (- n) n m ∙ cong (_+ m) (+-invˡ n)

isEquiv-n+ : ∀ n → isEquiv (n +_)
isEquiv-n+ n = isoToIsEquiv (Iso-n+ n)

-- multiplication

-- the following equalities hold definitionally:
--   zero   · n ≡ zero
--   suc m  · n ≡ n + m · n
--   pred m · n ≡ (- n) + m · n
_·_ : BiInvInt → BiInvInt → BiInvInt
m · n = BiInvInt-rec zero (n +_ , isEquiv-n+ n) m

-- properties of multiplication

·-zero : ∀ n → n · zero ≡ zero
·-zero = BiInvInt-ind-prop (λ _ → isSetBiInvInt _ _) refl (λ n p → p) (λ n p → p)

·-suc : ∀ m n → m · suc n ≡ m + m · n
·-suc = BiInvInt-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ n → refl)
  (λ m p n → cong suc
    (cong (n +_) (p n) ∙ +-assoc n m (m · n) ∙
     cong (_+ m · n) (+-comm n m) ∙ sym (+-assoc m n (m · n))))
  (λ m p n → cong pred
    (cong (- n +_) (p n) ∙ +-assoc (- n) m (m · n) ∙
     cong (_+ m · n) (+-comm (- n) m) ∙ sym (+-assoc m (- n) (m · n))))

·-pred : ∀ m n → m · pred n ≡ (- m) + m · n
·-pred = BiInvInt-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ n → refl)
  (λ m p n → cong pred
    (cong (n +_) (p n) ∙ +-assoc n (- m) (m · n) ∙
     cong (_+ m · n) (+-comm n (- m)) ∙ sym (+-assoc (- m) n (m · n))))
  (λ m p n → cong suc
    (cong (- n +_) (p n) ∙ +-assoc (- n) (- m) (m · n) ∙
     cong (_+ m · n) (+-comm (- n) (- m)) ∙ sym (+-assoc (- m) (- n) (m · n))))

·-comm : ∀ m n → m · n ≡ n · m
·-comm = BiInvInt-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ n → sym (·-zero n))
  (λ m p n → cong (n +_) (p n) ∙ sym (·-suc n m))
  (λ m p n → cong (- n +_) (p n) ∙ sym (·-pred n m))

·-identityˡ : ∀ m → suc zero · m ≡ m
·-identityˡ = +-zero

·-identityʳ : ∀ m → m · suc zero ≡ m
·-identityʳ m = ·-comm m (suc zero) ∙ ·-identityˡ m

·-distribʳ : ∀ m n o → (m · o) + (n · o) ≡ (m + n) · o
·-distribʳ = BiInvInt-ind-prop (λ _ → isPropΠ2 λ _ _ → isSetBiInvInt _ _)
  (λ n o → refl)
  (λ m p n o → sym (+-assoc o (m · o) (n · o)) ∙ cong (o +_) (p n o))
  (λ m p n o → sym (+-assoc (- o) (m · o) (n · o)) ∙ cong (- o +_) (p n o))

·-distribˡ : ∀ o m n → (o · m) + (o · n) ≡ o · (m + n)
·-distribˡ o m n =
  cong (_+ o · n) (·-comm o m) ∙ cong (m · o +_) (·-comm o n) ∙
  ·-distribʳ m n o ∙ ·-comm (m + n) o

·-inv : ∀ m n → m · (- n) ≡ - (m · n)
·-inv = BiInvInt-ind-prop (λ _ → isPropΠ λ _ → isSetBiInvInt _ _)
  (λ n → refl)
  (λ m p n → cong (- n +_) (p n) ∙ sym (inv-hom n (m · n)))
  (λ m p n → cong (- (- n) +_) (p n) ∙ sym (inv-hom (- n) (m · n)))

inv-· : ∀ m n → (- m) · n ≡ - (m · n)
inv-· m n = ·-comm (- m) n ∙ ·-inv n m ∙ cong (-_) (·-comm n m)

·-assoc : ∀ m n o → m · (n · o) ≡ (m · n) · o
·-assoc = BiInvInt-ind-prop (λ _ → isPropΠ2 λ _ _ → isSetBiInvInt _ _)
  (λ n o → refl)
  (λ m p n o →
    cong (n · o +_) (p n o) ∙ ·-distribʳ n (m · n) o)
  (λ m p n o →
    cong (- (n · o) +_) (p n o) ∙ cong (_+ m · n · o) (sym (inv-· n o)) ∙
    ·-distribʳ (- n) (m · n) o)

·-neg1 : ∀ x → -1 · x ≡ - x
·-neg1 x = inv-· 1 x ∙ cong -_ (·-identityˡ x)

pred-suc-inj : ∀ a b → pred (suc a) ≡ pred (suc b) → a ≡ b
pred-suc-inj a b p = sym (pred-suc a) ∙∙ p ∙∙ pred-suc b
