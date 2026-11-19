{-# OPTIONS --safe #-}
module Cubical.Homotopy.Serre.LastMinuteLemmas.FinLemmas where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
open import Cubical.Data.Sigma
open import Cubical.Data.Int
open import Cubical.Data.FinData
open import Cubical.Data.Fin renaming (Fin to FinInd)
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Bool

open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

-- basic stuff
Trichotomy→Bool : (a y : ℕ) → Trichotomyᵗ a y → Bool
Trichotomy→Bool a y (lt x) = false
Trichotomy→Bool a y (eq x) = true
Trichotomy→Bool a y (gt x) = false

==-diag : {n : ℕ} (a : Fin n) → a == a ≡ true
==-diag zero = refl
==-diag (suc a) = ==-diag a

==-comm : {n : ℕ} (a b : Fin n) → (a == b) ≡ (b == a)
==-comm zero zero = refl
==-comm zero (suc b) = refl
==-comm (suc a) zero = refl
==-comm (suc a) (suc b) = ==-comm a b

flast' : {n : ℕ} → Fin (suc n)
flast' {n = zero} = zero
flast' {n = suc n} = suc flast'

elimFin-altβ : ∀ {ℓ} {m : ℕ} {A : FinInd (suc m) → Type ℓ}
                 (min : A fzero)
                 (f : (x : FinInd m) → A (fsuc x))
              → ((elimFin-alt {A = A} min f fzero ≡ min))
               × ((x : FinInd m) → elimFin-alt {A = A} min f (fsuc x) ≡ f x)
elimFin-altβ {m = zero} min f = refl , λ()
elimFin-altβ {m = suc m} min f = refl , λ _ → refl

elimFin-alt++ : (n : ℕ) (a a' : ℤ) (b b' : (x : FinInd n) → ℤ) (s : _)
  → elimFin-alt {m = n} {A = λ _ → ℤ} a b s
  + elimFin-alt {m = n} {A = λ _ → ℤ} a' b' s
  ≡ elimFin-alt {m = n} {A = λ _ → ℤ} (a + a') (λ x → b x + b' x) s
elimFin-alt++ zero a a' b b' (zero , p) = refl
elimFin-alt++ (suc n) a a' b b' (zero , p) = refl
elimFin-alt++ (suc n) a a' b b' (suc s , p) = refl

ℤFinGenerator-fsuc : (n : ℕ) (a b : FinInd n)
  → ℤFinGenerator {n = n} a b ≡ ℤFinGenerator {n = suc n} (fsuc a) (fsuc b)
ℤFinGenerator-fsuc n a b with (fst a ≟ᵗ fst b)
... | lt x = refl
... | eq x = refl
... | gt x = refl

-- Iso between two versions of Finc
Fin→FinInd : (n : ℕ) → Fin n → FinInd n
Fin→FinInd .(suc _) zero = fzero
Fin→FinInd .(suc _) (suc x) = fsuc (Fin→FinInd _ x)

FinInd→Fin : (n : ℕ) → FinInd n → Fin n
FinInd→Fin (suc n) (zero , y) = zero
FinInd→Fin (suc n) (suc x , y) = suc (FinInd→Fin n (x , y))

Fin→FinInd→Fin : (n : ℕ) (x : _)
  → Fin→FinInd n (FinInd→Fin n x) ≡ x
Fin→FinInd→Fin (suc n) (zero , y) = refl
Fin→FinInd→Fin (suc n) (suc x , y) =
    cong fsuc (Fin→FinInd→Fin n (x , y))
  ∙ Σ≡Prop (λ r → isProp<ᵗ {r} {suc n}) refl

FinInd→Fin→FinInd : (n : ℕ) (p : n ≡ n) (x : _)
  → FinInd→Fin n (Fin→FinInd n x) ≡ x
FinInd→Fin→FinInd .(suc _) p zero = refl
FinInd→Fin→FinInd .(suc _) p (suc x) i =
  suc {n = n} ((cong (FinInd→Fin n)
    (Fin≡ {m = n}
      (Fin→FinInd n x .fst
      , snd (fsuc {k = n} (Fin→FinInd n x)))
          (Fin→FinInd n x) refl)
   ∙ FinInd→Fin→FinInd n refl x) i)
  where
  n = predℕ (p i0)

-- Iso between both versions of fin
Iso-Fin-FinInd : (n : ℕ) → Iso (Fin n) (FinInd n)
Iso.fun (Iso-Fin-FinInd n) = Fin→FinInd n
Iso.inv (Iso-Fin-FinInd n) = FinInd→Fin n
Iso.sec (Iso-Fin-FinInd n) x = Fin→FinInd→Fin n x
Iso.ret (Iso-Fin-FinInd n) x = FinInd→Fin→FinInd n refl x

-- iso preserves flast
Fin→FinInd-flast : {n : ℕ} → Fin→FinInd (suc n) flast' ≡ flast
Fin→FinInd-flast {n = zero} = refl
Fin→FinInd-flast {n = suc n} = cong fsuc (Fin→FinInd-flast {n})

-- Fin→FinInd commutes with injectSuc
injectSuc-fsuc : {n : ℕ} (w : FinInd n)
  → injectSuc (fsuc {k = n} w) ≡ fsuc {k = suc n} (injectSuc w)
injectSuc-fsuc (zero , t) = refl
injectSuc-fsuc {n = suc n} (suc s , t) = refl

injectSuc-Fin→FinInd : {n : ℕ} (w : Fin n)
  → injectSuc (Fin→FinInd n w) ≡ Fin→FinInd (suc n) (weakenFin w)
injectSuc-Fin→FinInd {n = .(suc _)} zero = refl
injectSuc-Fin→FinInd {n = .(suc _)} (suc w) =
    injectSuc-fsuc (Fin→FinInd _ w)
  ∙ cong fsuc (injectSuc-Fin→FinInd w)

-- commutativity double applications of sumFin
sumFinGenSwap : ∀ {ℓ} {A : Type ℓ} {n m : ℕ}
  → (_+_ : A → A → A) (0A : A) (F : FinInd n → FinInd m → A)
  → (rUnit : (x : A) → (x + 0A) ≡ x)
  → (comm : (x y : A) → (x + y) ≡ (y + x))
  → (assoc : ((x y z : A) → (x + (y + z)) ≡ ((x + y) + z)))
  → sumFinGen {n = n} _+_ 0A (λ x → sumFinGen {n = m} _+_ 0A (F x))
   ≡ sumFinGen {n = m} _+_ 0A (λ y → sumFinGen {n = n} _+_ 0A (λ x → F x y))
sumFinGenSwap {n = zero} {m} _+_ 0A F rUnit comm as =
  sym (sumFinGen0 _+_ 0A rUnit m (λ _ → 0A) λ _ → refl)
sumFinGenSwap {n = suc n} {m} _+_ 0A F rUnit comm as =
  cong (sumFinGen {n = m} _+_ 0A (F (flast {n})) +_)
       (sumFinGenSwap {n = n} {m} _+_ 0A (F ∘ injectSuc) rUnit comm as)
  ∙ sym (sumFinGenHom _+_ 0A rUnit comm as m
          (F flast)
          (λ y → sumFinGen {n = n} _+_ 0A (λ x → F (injectSuc x) y)))

sumFinℤSwap : {n m : ℕ} (F : FinInd n → FinInd m → ℤ)
  → sumFinℤ {n = n} (λ x → sumFinℤ {n = m} (F x))
   ≡ sumFinℤ {n = m} (λ y → sumFinℤ {n = n} (λ x → F x y))
sumFinℤSwap {n = n} {m} F =
  sumFinGenSwap {n = n} {m} _+_ 0 F (λ _ → refl) +Comm +Assoc

-- sumFinℤ commutes with multiplication
sumFinℤMult : {n : ℕ} (a : ℤ) (F : FinInd n → ℤ)
  → a · sumFinℤ {n = n} F ≡ sumFinℤ {n = n} (λ x → a · F x)
sumFinℤMult {n = zero} a F = ·Comm a 0
sumFinℤMult {n = suc n} a F =
   ·DistR+ a (F flast) (sumFinℤ {n = n} (F ∘ injectSuc))
  ∙ cong₂ _+_ refl (sumFinℤMult {n = n} a (F ∘ injectSuc))

-- foldl for Fin
foldlFin : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {n}
  → (A → B → B) → B → (Fin n → A) → B
foldlFin {n = zero}  _ b _ = b
foldlFin {n = suc n} f b l = f (l flast') (foldlFin {n = n} f b (l ∘ weakenFin))

-- foldl = foldr
foldlFin≡foldrFinℤ : (n : ℕ) (v : Fin n → ℤ)
  → foldrFin _+_ 0 v ≡ foldlFin _+_ 0 v
foldlFin≡foldrFinℤ zero v = refl
foldlFin≡foldrFinℤ one v = refl
foldlFin≡foldrFinℤ (suc (suc n)) v =
  cong (v zero +_) (foldlFin≡foldrFinℤ (suc n) (v ∘ suc))
  ∙ +Assoc (v zero) (v (suc flast'))
           (foldlFin {n = n} _+_ 0 (v ∘ suc ∘ weakenFin))
  ∙ cong₂ _+_ (+Comm (v zero) (v (suc flast')))
              (λ _ → foldlFin {n = n} _+_ 0 (v ∘ suc ∘ weakenFin))
  ∙ sym (+Assoc (v (suc flast')) (v zero)
         (foldlFin _+_ (pos 0) (λ x → v (suc (weakenFin x)))))
   ∙ cong (v (suc flast') +_)
          (cong₂ _+_ (λ _ → v zero)
                (sym (foldlFin≡foldrFinℤ n λ x → v (suc (weakenFin x))))
         ∙ (foldlFin≡foldrFinℤ (suc n) λ x → v (weakenFin x)))

-- sumFinℤ = foldrFin
sumFinℤ≡foldrFin : {n : ℕ} (x : FinInd n → ℤ)
  → sumFinℤ {n = n} x
   ≡ foldrFin {n = n} _+_ (pos 0) (x ∘ Fin→FinInd n)
sumFinℤ≡foldrFin {n = zero} x = refl
sumFinℤ≡foldrFin {n = suc n} f =
  cong₂ _+_ (cong f (sym (Fin→FinInd-flast {n = n})))
    (sumFinℤ≡foldrFin {n = n} (f ∘ injectSuc)
    ∙ foldlFin≡foldrFinℤ n (f ∘ injectSuc ∘ Fin→FinInd n)
    ∙ cong (foldlFin {n = n} _+_ (pos 0))
      (funExt λ w → cong f (injectSuc-Fin→FinInd {n = n} w)))
  ∙ sym (foldlFin≡foldrFinℤ (suc n) (f ∘ Fin→FinInd (suc n)))
