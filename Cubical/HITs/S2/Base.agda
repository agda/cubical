{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.S2.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

data S² : Type₀ where
  base : S²
  surf : PathP (λ i → base ≡ base) refl refl

S²ToSetRec : ∀ {ℓ} {A : S² → Type ℓ}
           → ((x : S²) → isSet (A x))
           → A base
           → (x : S²) → A x
S²ToSetRec set b base = b
S²ToSetRec set b (surf i j) =
  isOfHLevel→isOfHLevelDep 2 set b b {a0 = refl} {a1 = refl} refl refl surf i j
{-




open import Cubical.HITs.Rationals.SigmaQ renaming (_·_ to _·ℚ_ ; _+_ to _+ℚ_ ; -_ to -ℚ_)
open import Cubical.Data.Nat renaming (_·_ to _ℕ·_ ; +-comm to +ℕ-comm)
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.HITs.SetQuotients as SetQuotient
  using ([_]; eq/; discreteSetQuotients) renaming (_/_ to _//_) public
open import Cubical.HITs.Ints.QuoInt
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty renaming (rec to ⊥-rec)

{-
_∼'_ : ℕ × ℕ₊₁ → ℕ × ℕ₊₁ → Type₀
(a , b) ∼' (c , d) = pos a · ℕ₊₁→ℤ d ≡ pos c · ℕ₊₁→ℤ b
-}

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Unit
open import Cubical.Foundations.Equiv


IsoEmpty : ∀ {ℓ} {A : Type ℓ} → (A → ⊥) → Iso A ⊥
Iso.fun (IsoEmpty f) = f
Iso.inv (IsoEmpty f) ()
Iso.rightInv (IsoEmpty f) ()
Iso.leftInv (IsoEmpty f) x = ⊥-rec (f x)

help : (n : ℕ) → (0 < suc n) ≃ Unit
help n = isContr→≃Unit
         ((n , +ℕ-comm n 1) , λ y → m≤n-isProp _ _)

_<Int_ : ℤ → ℤ → Type₀
pos n <Int pos n₁ = n < n₁
neg zero <Int pos zero = ⊥
neg zero <Int pos (suc n₁) = Unit
neg (suc n) <Int pos n₁ = Unit
pos n <Int neg n₁ = ⊥
neg n <Int neg n₁ = n₁ < n
pos zero <Int posneg i =
  isoToPath (IsoEmpty (¬-<-zero {m = 0})) i
pos (suc n) <Int posneg i =
  isoToPath (IsoEmpty (¬-<-zero {m = (suc n)})) i
neg zero <Int posneg i =
  isoToPath (IsoEmpty (¬-<-zero {m = 0})) (~ i)
neg (suc n) <Int posneg i = ua (help n) (~ i)
posneg i <Int pos zero = isoToPath (IsoEmpty (¬-<-zero {m = 0})) i
posneg i <Int pos (suc n) = ua (help n) i
posneg i <Int neg n = isoToPath (IsoEmpty (¬-<-zero {m = n})) (~ i)
posneg i <Int posneg j =
  isoToPath (IsoEmpty (¬-<-zero {m = 0})) ((~ j ∧ i) ∨ (j ∧ ~ i))

ℚ₊ : Type₀
ℚ₊ = Σ[ x ∈ ℚ ] {!Σ ? ?!} -- (ℕ × ℕ₊₁) // _∼'_



-}
{-
-- isSetℚ₊ : isSet ℚ₊
-- isSetℚ₊ = SetQuotient.squash/

-- ℚ₊→ℚ : ℚ₊ → ℚ
-- ℚ₊→ℚ [ a ] = [ (pos (fst a)) , (snd a) ]
-- ℚ₊→ℚ (eq/ (a , a₀) (b , b₀) r i) = eq/ (pos a , a₀) (pos b , b₀) r i
-- ℚ₊→ℚ (_//_.squash/ x y p q i j) =
--   isSetℚ _ _ (cong ℚ₊→ℚ p) (cong ℚ₊→ℚ q) i j

-- _-ℚ_ : ℚ → ℚ → ℚ
-- x -ℚ y = x +ℚ (-ℚ y)

-- ℚ-rec : ∀ {ℓ} {A : Type ℓ}
--      → isSet A
--      → (f : (x : ℤ × ℕ₊₁) → A)
--      → ((a b : _) → a ∼ b → f a ≡ f b)
--      → ℚ → A
-- ℚ-rec isset f eq [ a ] = f a
-- ℚ-rec isset f eq (eq/ a b r i) = eq a b r i
-- ℚ-rec isset f eq (_//_.squash/ x x₁ p q i i₁) =
--   isset (ℚ-rec isset f eq x) (ℚ-rec isset f eq x₁)
--          (λ i₁ → ℚ-rec isset f eq (p i₁))
--          ((λ i₁ → ℚ-rec isset f eq (q i₁))) i i₁

-- _<ℚ_ : ℚ → ℚ → Type₀
-- _<ℚ_ p q = {!!}
-- _<ℚ₊_ : ℚ₊ → ℚ₊ → Type₀
-- _<ℚ₊_ = {!!}

-- _+ℚ₊_ : ℚ₊ → ℚ₊ → ℚ₊
-- _+ℚ₊_ = {!!}

-- _-ℚ₊_ : ℚ₊ → ℚ₊ → ℚ₊
-- _-ℚ₊_ = {!!}

-- R' : Type₀
-- ~* : ℚ₊ → R' → R' → Type₀
-- R' = RRR
--   module _ where
--     data RRR : Type₀ where
--       rat : ℚ → RRR
--       lim : (x : ℚ₊ → R') → ((δ ε : ℚ₊) → ~* (δ +ℚ₊ ε) (x δ) (x ε)) → RRR

-- ~* = Rel3
--   module _ where
--     data Rel3 : ℚ₊ → RRR → RRR → Type₀ where
--       cond₁ : (q r : ℚ) (ε : ℚ₊) {-
--         → (-ℚ (ℚ₊→ℚ ε)) <ℚ (q -ℚ r)
--         → (q -ℚ r) <ℚ (ℚ₊→ℚ ε) -}
--         → Rel3 ε (rat q) (rat r)
--       cond₂ : (q : _) (y : _) (ε : _) (δ : _) (pf : _)
--             → Rel3 (ε -ℚ₊ δ) (rat q) (y δ) → Rel3 ε (rat q) (lim y pf)
--       cond₃ : (x : _) (r : _) (ε : _) (δ : _) (pf : _) → Rel3 (ε -ℚ₊ δ) (x δ) (rat r)
--             → Rel3 ε (lim x pf) (rat r)
--       cond₄ : (x y : _) (pf1 : _) (pf2 : _) (ε : _) (δ : _) (η : _)
--            → Rel3 (ε -ℚ₊ (δ -ℚ₊ η)) (x δ) (y η) → Rel3 ε (lim x pf1) (lim y pf2)

--       proppie : (q r : RRR) (ε : ℚ₊) → isProp (Rel3 ε q r)

-- data ℝ : Type₀ where
--   inc : R' → ℝ
--   rel : (x y : R') → ((ε : _) → ~* ε x y) → inc x ≡ inc y


-- elim~* : ∀ {ℓ} → {A : (x y : R') (ε : ℚ₊) → ~* ε x y → Type ℓ}
--      → ((x y : R') (ε : ℚ₊) → (r : _) → isProp (A x y ε r))
--      → {!A _ _ !}
--      → {!!}
--      → {!!}
--      → {!!}
-- elim~* x y r p = {!p!}

-- test : R' → R'
-- testid : (x y : R') (δ ε : ℚ₊) → ~* (δ +ℚ₊ ε) x y →  ~* (δ +ℚ₊ ε) (test x) (test y)
-- test (rat x) = rat (-ℚ x)
-- test (lim x x₁) = lim (λ z → test (x z)) λ δ ε → testid (x δ) (x ε) δ ε (x₁ _ _)
-- testid .(rat q) .(rat r) δ ε (cond₁ q r .(δ +ℚ₊ ε)) = cond₁ (-ℚ q) (-ℚ r) (δ +ℚ₊ ε)
-- testid .(rat q) .(lim y pf) δ ε (cond₂ q y .(δ +ℚ₊ ε) δ₁ pf r) =
--   cond₂ (-ℚ q) (λ z → test (y z)) (δ +ℚ₊ ε)
--         δ₁
--         (λ δ₂ ε₁ → testid (y δ₂) (y ε₁) δ₂ ε₁ (pf δ₂ ε₁))
--         {!!}
-- testid .(lim x pf) .(rat r) δ ε (cond₃ x r .(δ +ℚ₊ ε) δ₁ pf r₁) = {!!}
-- testid .(lim x pf1) .(lim y pf2) δ ε (cond₄ x y pf1 pf2 .(δ +ℚ₊ ε) δ₁ η r) = {!!}
-- testid x y δ ε (proppie .x .y .(δ +ℚ₊ ε) r r₁ i) = {!!}

-- -- data Rel : ℚ₊ → ℚ → ℚ → Type₀ where
-- --   cond₁ : (q r : ℚ) (ε : ℚ₊)
-- --         → (-ℚ (ℚ₊→ℚ ε)) <ℚ (q -ℚ r)
-- --         → (q -ℚ r) <ℚ (ℚ₊→ℚ ε)
-- --         → Rel ε q r
-- --   cond₂ : (q y ε δ : ℚ) (ε : ℚ₊)
-- --         → (-ℚ (ℚ₊→ℚ ε)) <ℚ (q -ℚ r)
-- --         → (q -ℚ r) <ℚ (ℚ₊→ℚ ε)
-- --         → Rel ε q r


-- -- data ℝ : Type₀ where
-- --   rat : ℚ → ℝ
-- --   eqrel₁ : (q r : ℚ) (ε : ℚ₊)
-- --         → (-ℚ (ℚ₊→ℚ ε)) <ℚ (q -ℚ r)
-- --         → (q -ℚ r) <ℚ (ℚ₊→ℚ ε)
-- --         → rat q ≡ rat r
-- --   lim : (x : ℚ₊) →  {!!}

-- -- {-
-- -- _∼_ : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → Type₀
-- -- (a , b) ∼ (c , d) = a · ℕ₊₁→ℤ d ≡ c · ℕ₊₁→ℤ b

-- -- ℚ : Type₀
-- -- ℚ = (ℤ × ℕ₊₁) // _∼_


-- -- isSetℚ : isSet ℚ
-- -- isSetℚ = SetQuotient.squash/
-- -- -}
-}
