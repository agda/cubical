{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Data.Fin.Inductive where

-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Function


-- open import Cubical.Data.Nat
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Unit
-- open import Cubical.Data.Sigma
-- open import Cubical.Data.Nat.Order

-- open import Cubical.Relation.Nullary

-- -- open import Cubical.Algebra.AbGroup.Base using (move4)

-- -- inductive definition of <
-- _<ᵗ_ : (n m : ℕ) → Type
-- n <ᵗ zero = ⊥
-- zero <ᵗ suc m = Unit
-- suc n <ᵗ suc m = n <ᵗ m

-- data Trichotomyᵗ (m n : ℕ) : Type₀ where
--   lt : m <ᵗ n → Trichotomyᵗ m n
--   eq : m ≡ n → Trichotomyᵗ m n
--   gt : n <ᵗ m → Trichotomyᵗ m n

-- Trichotomyᵗ-suc : {n m : ℕ} → Trichotomyᵗ n m → Trichotomyᵗ (suc n) (suc m)
-- Trichotomyᵗ-suc (lt x) = lt x
-- Trichotomyᵗ-suc (eq x) = eq (cong suc x)
-- Trichotomyᵗ-suc (gt x) = gt x

-- _≟ᵗ_ : ∀ m n → Trichotomyᵗ m n
-- zero ≟ᵗ zero = eq refl
-- zero ≟ᵗ suc n = lt tt
-- suc m ≟ᵗ zero = gt tt
-- suc m ≟ᵗ suc n = Trichotomyᵗ-suc (m ≟ᵗ n)

-- isProp<ᵗ : {n m : ℕ} → isProp (n <ᵗ m)
-- isProp<ᵗ {n = n} {zero} = isProp⊥
-- isProp<ᵗ {n = zero} {suc m} = isPropUnit
-- isProp<ᵗ {n = suc n} {suc m} = isProp<ᵗ {n = n} {m = m}
-- -- Fin defined using <ᵗ
-- Fin : (n : ℕ) → Type
-- Fin n = Σ[ m ∈ ℕ ] (m <ᵗ n)

-- fsuc : {n : ℕ} → Fin n → Fin (suc n)
-- fst (fsuc {n = n} (x , p)) = suc x
-- snd (fsuc {n = suc n} (x , p)) = p

-- <ᵗ-trans-suc : {n m : ℕ} → n <ᵗ m → n <ᵗ suc m
-- <ᵗ-trans-suc {n = zero} {suc m} x = tt
-- <ᵗ-trans-suc {n = suc n} {suc m} x = <ᵗ-trans-suc  {n = n} x

-- injectSuc : {n : ℕ} → Fin n → Fin (suc n)
-- fst (injectSuc {n = n} (x , p)) = x
-- snd (injectSuc {n = suc n} (x , p)) = <ᵗ-trans-suc {n = x} p

-- fsuc-injectSuc : {m : ℕ} (n : Fin m) → injectSuc {n = suc m} (fsuc {n = m} n) ≡ fsuc (injectSuc n)
-- fsuc-injectSuc {m = suc m} (x , p) = refl

-- <ᵗsucm : {m : ℕ} → m <ᵗ suc m
-- <ᵗsucm {m = zero} = tt
-- <ᵗsucm {m = suc m} = <ᵗsucm {m = m}

-- flast : {m : ℕ} → Fin (suc m)
-- fst (flast {m = m}) = m
-- snd (flast {m = m}) = <ᵗsucm {m = m}

-- fzero : {m : ℕ} → Fin (suc m)
-- fzero = 0 , tt

-- elimFin : ∀ {ℓ} {m : ℕ} {A : Fin (suc m) → Type ℓ}
--                  (max : A flast)
--                  (f : (x : Fin m) → A (injectSuc x))
--               → (x : _) → A x
-- elimFin {m = zero} {A = A} max f (zero , p) = max
-- elimFin {m = suc m} {A = A} max f (zero , p) = f (zero , tt)
-- elimFin {m = suc zero} {A = A} max f (suc zero , p) = max
-- elimFin {m = suc (suc m)} {A = A} max f (suc x , p) =
--   elimFin {m = suc m} {A = λ x → A (fsuc x)} max (λ t → f (fsuc t)) (x , p)

-- elimFin-alt : ∀ {ℓ} {m : ℕ} {A : Fin (suc m) → Type ℓ}
--                  (max : A fzero)
--                  (f : (x : Fin m) → A (fsuc x))
--               → (x : _) → A x
-- elimFin-alt {m = zero} max f (zero , p) = max
-- elimFin-alt {m = suc m} max f (zero , p) = max
-- elimFin-alt {m = suc m} max f (suc x , p) = f (x , p)

-- elimFinβ : ∀ {ℓ} {m : ℕ} {A : Fin (suc m) → Type ℓ}
--                  (max : A flast)
--                  (f : (x : Fin m) → A (injectSuc x))
--               → ((elimFin {A = A} max f flast ≡ max))
--                × ((x : Fin m) → elimFin {A = A} max f (injectSuc x) ≡ f x)
-- elimFinβ {m = zero} {A = A} max f = refl , λ {()}
-- elimFinβ {m = suc zero} {A = A} max f = refl , λ {(zero , p) → refl}
-- elimFinβ {m = suc (suc m)} {A = A} max f =
--   elimFinβ {m = (suc m)} {A = λ x → A (fsuc x)} max _ .fst
--   , elimFin-alt {m = (suc m)} {A = λ x → elimFin max f (injectSuc {n = suc (suc m)} x) ≡ f x}
--              refl
--              (elimFinβ {m = (suc m)} {A = λ x → A (fsuc x)} max _ .snd)

-- --
-- ¬Fin0 : ¬ Fin 0
-- ¬Fin0 (x , ())

-- -- Sums
-- sumFinGen : ∀ {ℓ} {A : Type ℓ} {n : ℕ} (_+_ : A → A → A) (0A : A) (f : Fin n → A) → A
-- sumFinGen {n = zero} _+_ 0A f = 0A
-- sumFinGen {n = suc n} _+_ 0A f = f flast + sumFinGen _+_ 0A (f ∘ injectSuc)


-- --
-- <ᵗ-trans : {n m k : ℕ} → n <ᵗ m → m <ᵗ k → n <ᵗ k
-- <ᵗ-trans {n = zero} {suc m} {suc k} _ _ = tt
-- <ᵗ-trans {n = suc n} {suc m} {suc k} = <ᵗ-trans {n = n} {m} {k}

-- ¬m<ᵗm : {m : ℕ} → ¬ (m <ᵗ m)
-- ¬m<ᵗm {m = suc m} p = ¬m<ᵗm p

-- ¬squeeze : {n m : ℕ} → ¬ ((n <ᵗ m) × (m <ᵗ suc n))
-- ¬squeeze {n = suc n} {suc m} = ¬squeeze {n = n} {m = m}

-- -- properties of finite sums
-- module _ {ℓ : Level} {A : Type ℓ} (_+A_ : A → A → A) (0A : A)
--   (rUnit : (x : _) → x +A 0A ≡ x)
--    where
--   sumFinGen0 : (n : ℕ) (f : Fin n → A)
--     → ((x : _) → f x ≡ 0A)
--     → sumFinGen _+A_ 0A f
--     ≡ 0A
--   sumFinGen0 zero f ind = refl
--   sumFinGen0 (suc n) f ind =
--     cong₂ _+A_
--       (ind flast)
--       (sumFinGen0 n (f ∘ injectSuc) (λ x → ind (injectSuc x))) ∙ rUnit 0A

--   module _ (comm : (x y : A) → x +A y ≡ y +A x) where
--     private
--       lUnitA : (x : _) → 0A +A x ≡ x
--       lUnitA x = comm _ _ ∙ rUnit x

--     sumFin-choose :
--       {n : ℕ} (f : Fin n → A)
--       → (a : A) (x : Fin n)
--       → (f x ≡ a)
--       → ((x' : Fin n) → ¬ (x' ≡ x) → f x' ≡ 0A)
--       → sumFinGen {n = n} _+A_ 0A f ≡ a
--     sumFin-choose {zero} f a x p t = ⊥.rec (¬Fin0 x)
--     sumFin-choose {suc n} f a (x , q) p t with (n ≟ᵗ x)
--     ... | lt x₁ = ⊥.rec (¬squeeze (q , x₁))
--     ... | eq x₁ =
--       cong (f flast +A_) (sumFinGen0 n _ λ h → t _
--         λ q → ¬m<ᵗm (subst (_<ᵗ n) (cong fst q ∙ sym x₁) (snd h)))
--       ∙ rUnit _ ∙ cong f (sym x=flast) ∙ p
--       where
--       x=flast : (x , q) ≡ flast
--       x=flast = Σ≡Prop (λ _ → isProp<ᵗ) (sym x₁)
--     ... | gt x₁ =
--       cong₂ _+A_
--          (t flast (λ p → ¬m<ᵗm (subst (_<ᵗ n) (sym (cong fst p)) x₁)))
--          refl
--       ∙ lUnitA _
--       ∙ sumFin-choose {n = n} (f ∘ injectSuc) a (x , x₁)
--           (cong f (Σ≡Prop (λ _ → isProp<ᵗ) refl) ∙ p)
--           λ a r → t (injectSuc a) λ d → r (Σ≡Prop (λ _ → isProp<ᵗ)
--           (cong fst d))

--     module _ (assocA : (x y z : A) → x +A (y +A z) ≡ (x +A y) +A z) where
--       sumFinGenHom : (n : ℕ) (f g : Fin n → A)
--         → sumFinGen _+A_ 0A (λ x → f x +A g x)
--          ≡ (sumFinGen _+A_ 0A f +A sumFinGen _+A_ 0A g)
--       sumFinGenHom zero f g = sym (rUnit 0A)
--       sumFinGenHom (suc n) f g =
--           cong ((f flast +A g flast) +A_) (sumFinGenHom n (f ∘ injectSuc) (g ∘ injectSuc))
--         ∙ move4 (f flast) (g flast)
--                 (sumFinGen _+A_ 0A (λ x → f (injectSuc x)))
--                 (sumFinGen _+A_ 0A (λ x → g (injectSuc x)))
--                 _+A_ assocA comm

-- sumFinGenId : ∀ {ℓ} {A : Type ℓ} {n : ℕ} (_+_ : A → A → A) (0A : A)
--   (f g : Fin n → A) → f ≡ g → sumFinGen _+_ 0A f ≡ sumFinGen _+_ 0A g
-- sumFinGenId _+_ 0A f g p i = sumFinGen _+_ 0A (p i)


-- open import Cubical.Data.Fin.Base renaming (Fin to Fin*) hiding (¬Fin0)
-- open import Cubical.Data.Fin.Properties renaming (isSetFin to isSetFin*)

-- <ᵗ→< : {n m : ℕ} → n <ᵗ m → n < m
-- <ᵗ→< {n = zero} {suc m} p = m , +-comm m 1
-- <ᵗ→< {n = suc n} {suc m} p = suc-≤-suc (<ᵗ→< {n = n} {m = m} p)

-- <→<ᵗ : {n m : ℕ} → n < m → n <ᵗ m
-- <→<ᵗ {n = zero} {m = zero} x =
--   snotz (sym (+-suc (fst x) 0) ∙ snd x)
-- <→<ᵗ {n = zero} {m = suc m} _ = tt
-- <→<ᵗ {n = suc n} {m = zero} x =
--   snotz (sym (+-suc (fst x) (suc n)) ∙ snd x)
-- <→<ᵗ {n = suc n} {m = suc m} p = <→<ᵗ {n = n} {m = m} (pred-≤-pred p)

-- Iso-Fin-InductiveFin : (m : ℕ) → Iso (Fin* m) (Fin m)
-- Iso.fun (Iso-Fin-InductiveFin m) (x , p) = x , <→<ᵗ p
-- Iso.inv (Iso-Fin-InductiveFin m) (x , p) = x , <ᵗ→< p
-- Iso.rightInv (Iso-Fin-InductiveFin m) (x , p) =
--   Σ≡Prop (λ w → isProp<ᵗ {n = w} {m}) refl
-- Iso.leftInv (Iso-Fin-InductiveFin m) _ = Σ≡Prop (λ _ → isProp≤) refl


-- isSetFin : {n : ℕ} → isSet (Fin n)
-- isSetFin {n = n} =
--   isOfHLevelRetractFromIso 2 (invIso (Iso-Fin-InductiveFin n))
--     isSetFin*
