{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals.Number.Consequences where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic renaming (inr to inrᵖ; inl to inlᵖ)
open import Function.Base using (it; _∋_; _$_)

open import SyntheticReals.Utils
open import SyntheticReals.MoreLogic.Definitions
open import SyntheticReals.MoreLogic.Properties
open import SyntheticReals.MorePropAlgebra.Definitions
open import SyntheticReals.MorePropAlgebra.Consequences
open import SyntheticReals.MorePropAlgebra.Structures
open import SyntheticReals.MorePropAlgebra.Bundles
open import SyntheticReals.Number.Definitions

-- import Cubical.HITs.Rationals.SigmaQ as ℚ*
-- import Cubical.Data.Nat.Coprime as Coprime
open import Cubical.HITs.Rationals.QuoQ renaming
  ( [_] to [_]ᶠ
  ; [_/_] to [_/_]ᶠ
  ; _+_ to _+ᶠ_
  ; -_  to -ᶠ_
  ; _*_ to _*ᶠ_
  ; +-assoc to +-assocᶠ
  ; +-comm  to +-commᶠ
  ; *-assoc to *-assocᶠ
  ; *-comm  to *-commᶠ
  )
-- open import Cubical.Data.Nat.Literals public
--
-- instance
--   fromNatℚ : HasFromNat ℚ
--   fromNatℚ = record { Constraint = λ _ → Unit ; fromNat = λ n → [ pos n / 1 ] }
--
-- instance
--   fromNegℚ : HasFromNeg ℚ
--   fromNegℚ = record { Constraint = λ _ → Unit ; fromNeg = λ n → [ neg n / 1 ] }

open import Cubical.HITs.SetQuotients renaming ([_] to [_]ˢ)

-- Define the integers as a HIT by identifying +0 and -0
import Cubical.HITs.Ints.QuoInt
import Cubical.Data.NatPlusOne


open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.HITs.PropositionalTruncation.Base -- ∣_∣
import Cubical.HITs.PropositionalTruncation.Properties as PTrunc

-- -- Set quotients as a higher inductive type:
-- data _/_ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
--   [_] : (a : A) → A / R
--   eq/ : (a b : A) → (r : R a b) → [ a ] ≡ [ b ]
--   squash/ : (x y : A / R) → (p q : x ≡ y) → p ≡ q

-- {-# DISPLAY [_]' (Cubical.HITs.Ints.QuoInt.signed Agda.Builtin.Bool.Bool.false 1 / Cubical.Data.NatPlusOne.1+ 0 )= 1ᶠ #-}

{-

we have most properties in `Cubical.HITs.Rationals.QuoQ.Properties`

but we can use `Quoℚ≡Sigmaℚ : Quo.ℚ ≡ Sigma.ℚ` from `Cubical.HITs.Rationals.SigmaQ.Properties`

-}


open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.HITs.Ints.QuoInt hiding (+-identityʳ; *-identityʳ; *-identityˡ; *-distribˡ;*-distribʳ) -- using (ℤ)
  renaming (_*_ to _*ᶻ_)
-- there is `elimProp` in `Cubical.HITs.SetQuotients` to define properties

-- elimProp {A = ℤ × ℕ₊₁} {R = _∼_} {B = λ(x : ℚ) → ?} ?

-- e.g. we have
-- _∼_ : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → Type₀
-- (a , b) ∼ (c , d) = a * ℕ₊₁→ℤ d ≡ c * ℕ₊₁→ℤ b

open import Cubical.Data.Nat as ℕ using (discreteℕ; ℕ; suc; zero) renaming (_+_ to _+ⁿ_; _*_ to _*ⁿ_)
open import Cubical.Data.Nat.Order using () renaming (_<_ to _<ⁿ_; _≤_ to _≤ⁿ_; ≤-suc to ≤ⁿ-suc)
open import Cubical.Data.Nat.Properties using (isSetℕ) renaming (snotz to snotzⁿ; +-suc to +-sucⁿ; inj-+m to inj-+mⁿ; inj-m+ to inj-m+ⁿ; +-zero to +-zeroⁿ; +-comm to +-commⁿ; +-assoc to +-assocⁿ)

_<ⁿᵖ_ : (x y : ℕ) → hProp ℓ-zero
(x <ⁿᵖ y) .fst = x <ⁿ y
(x <ⁿᵖ y) .snd (k₁ , k₁+sx≡y) (k₂ , k₂+sx≡y) = φ where
  abstract φ = Σ≡Prop (λ k → isSetℕ _ _) (inj-+mⁿ (k₁+sx≡y ∙ sym k₂+sx≡y))

isProp⊤ : isProp [ ⊤ ]
isProp⊤ tt tt = refl

private
  abstract
    lemma10 : ∀ n → (n <ⁿ 0) ≡ [ ⊥ ]
    lemma10 n = isoToPath (iso (λ{ (k , p) → snotzⁿ (sym (+-sucⁿ k n) ∙ p) }) ⊥-elim (λ b → isProp⊥ _ _) (λ a → isProp[] (n <ⁿᵖ 0) _ _))

    -- NOTE: we cannot prove `isProp lemma10` because it seems not even provable that `isProp ([ ⊥ ] ≡ [ ⊥ ])`
    -- but we can use propositional truncation
    lemma10' : ∀ n → ∥ (n <ⁿ 0) ≡ [ ⊥ ] ∥
    lemma10' n = ∣ isoToPath (iso (λ{ (k , p) → snotzⁿ (sym (+-sucⁿ k n) ∙ p) }) ⊥-elim (λ b → isProp⊥ _ _) (λ a → isProp[] (n <ⁿᵖ 0) _ _)) ∣

    lemma10'' : ∀ n → (n <ⁿᵖ 0) ≡ ⊥
    lemma10'' n = ⇔toPath (transport (lemma10 n)) (transport (sym (lemma10 n)))

  abstract
    lemma12 : ∀ n → (0 <ⁿ suc n) ≡ [ ⊤ ]
    lemma12 n = isoToPath (iso (λ _ →  tt) (λ _ → n , +-sucⁿ n 0 ∙ (λ i → suc (+-zeroⁿ n i))) (λ b → isProp⊤ _ _) (λ a → isProp[] (0 <ⁿᵖ suc n) _ _))

    lemma12'' : ∀ n → (0 <ⁿᵖ suc n) ≡ ⊤
    lemma12'' n = ⇔toPath (transport (lemma12 n)) (transport (sym (lemma12 n)))

  abstract
    helper : ∀ n → isProp (n <ⁿ 0) ≡ isProp [ ⊥ ]
    helper n = λ i → isProp (lemma10 n i)

    -- -- the following states that all propositions are equal (which is obviously not the case)
    -- isPropΣProp : ∀ {ℓ} → isProp (Σ[ X ∈ Type ℓ ] isProp X)
    -- isPropΣProp (A , isPropA) (B , isPropB) = Σ≡Prop (λ X → isPropIsProp) {! Goal: A ≡ B   !}

    -- isProp' : ∀{ℓ} {A : Type ℓ} → isProp A → A ≡ (A ≡ A)
    -- isProp' isPropA = pathToIso (iso ? ? ? ?)

    -- https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
    -- no-unicorns :

    -- isProp-≡ : ∀{ℓ} {A : Type ℓ} → isProp A → isProp (A ≡ A)

    --
    -- isProp-≡ : ∀{ℓ} {A : Type ℓ} → isProp A → isProp (A ≡ A)
    -- -- ———— Boundary ——————————————————————————————————————————————
    -- -- i = i0 ⊢ p j
    -- -- i = i1 ⊢ q j
    -- -- j = i0 ⊢ A
    -- -- j = i1 ⊢ A
    -- --
    -- -- i j |    |
    -- -- 0 0 | pj | A
    -- -- 0 1 | pj | A
    -- -- 1 0 | qj | A
    -- -- 1 1 | qj | A
    -- -- Σ≡Prop {A = Type ℓ} {B = λ X → isProp X} (λ X → isPropIsProp) {u = (A , isPropA)} {v = (A , isPropA)}
    -- -- isProp→isSet (isPropIsProp {A = A})
    -- isProp-≡ {ℓ} {A} isPropA p q = isProp→isSet {! Goal : isProp (Type ℓ)  !} A A p q

    -- isProp-⊥≡⊥ : isProp ([ ⊥ ] ≡ [ ⊥ ])
    -- isProp-⊥≡⊥ x y = {!   !}

  -- abstract

    -- -- isProp[] (n <ⁿᵖ 0)
    -- isProp-lemma10 : ∀ n → isProp ((n <ⁿ 0) ≡ [ ⊥ ])
    -- -- ———— Boundary ——————————————————————————————————————————————
    -- -- i = i0 ⊢ p j
    -- -- i = i1 ⊢ q j
    -- -- j = i0 ⊢ n <ⁿ 0
    -- -- j = i1 ⊢ [ ⊥ ]
    -- -- (isProp[] (n <ⁿᵖ 0))
    -- isProp-lemma10 n p q =
    --   let γ : isProp ((n <ⁿ 0) ≡ (n <ⁿ 0))
    --       γ x y = {! isProp[] (n <ⁿᵖ 0) ?   !}
    --   -- transport (helper n) (isProp[] (n <ⁿᵖ 0))
    --   in {!    !}


_<ᶻ'_ : ℤ → ℤ → Type ℓ-zero
pos      n₀  <ᶻ' pos      n₁  = [ n₀ <ⁿᵖ n₁ ]
pos      n₀  <ᶻ' neg      n₁  = [ ⊥ ]
neg  zero    <ᶻ' pos  zero    = [ ⊥ ]
neg  zero    <ᶻ' pos (suc n₁) = [ ⊤ ]
neg (suc n₀) <ᶻ' pos  zero    = [ ⊤ ]
neg (suc n₀) <ᶻ' pos (suc n₁) = [ ⊤ ]
neg      n₀  <ᶻ' neg      n₁  = [ n₁ <ⁿᵖ n₀ ]
-- 1D pathes
pos      n₀  <ᶻ' posneg   j   = lemma10 n₀    j
neg  zero    <ᶻ' posneg   j   = lemma10 0  (~ j) -- [F1]
neg (suc n₀) <ᶻ' posneg   j   = lemma12 n₀ (~ j) -- [G1]
posneg   i   <ᶻ' pos  zero    = lemma10 0     i  -- [F2]
posneg   i   <ᶻ' pos (suc n₁) = lemma12 n₁    i  -- [G2]
posneg   i   <ᶻ' neg      n₁  = lemma10 n₁ (~ i)
-- 2D path
-- note, how `lemma12` does not appear in the final, 2D-case
-- this is, because we explitictly split out [F1] from [G1] and [F2] from [G2]
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ lemma10 0 j       [a]
-- i = i1 ⊢ lemma10 0 (~ j)   [b]
-- j = i0 ⊢ lemma10 0 i       [c]
-- j = i1 ⊢ lemma10 0 (~ i)   [d]
--
-- i j | a  b c  d | a b c d |
-- ----|-----------|---------|---
-- 0 0 | j    i    | 0   0   | 0
-- 0 1 | j      ~i | 1     1 | 1     ⇒ "i xor j" ≡ (i ∨ j) ∧ ~(i ∧ j)
-- 1 0 |   ~j i    |   1 1   | 1
-- 1 1 |   ~j   ~i |   0   0 | 0
posneg i <ᶻ' posneg j = lemma10 0 ((i ∨ j) ∧ ~(i ∧ j))

_<ᶻ''_ : ℤ → ℤ → hProp ℓ-zero
pos      n₀  <ᶻ'' pos      n₁  = n₀ <ⁿᵖ n₁  -- point 1: 1a    3a
pos      n₀  <ᶻ'' neg      n₁  = ⊥          -- point 2: 1b       4a
neg  zero    <ᶻ'' pos  zero    = ⊥          -- point 3:    2a 3b
neg  zero    <ᶻ'' pos (suc n₁) = ⊤          --
neg (suc n₀) <ᶻ'' pos  zero    = ⊤          --
neg (suc n₀) <ᶻ'' pos (suc n₁) = ⊤          --
neg      n₀  <ᶻ'' neg      n₁  = n₁ <ⁿᵖ n₀  -- point 4:    2b    4b
-- 1D pathes
pos      n₀  <ᶻ'' posneg   j   = lemma10'' n₀ j             -- face 1: point 1 to 2
neg  zero    <ᶻ'' posneg   j   = lemma10'' 0  (~ j) -- [F1] -- face 2: point 3 to 4
neg (suc n₀) <ᶻ'' posneg   j   = lemma12'' n₀ (~ j) -- [G1]
posneg   i   <ᶻ'' pos  zero    = lemma10'' 0     i  -- [F2] -- face 3: point 1 to 3
posneg   i   <ᶻ'' pos (suc n₁) = lemma12'' n₁    i  -- [G2]
posneg   i   <ᶻ'' neg      n₁  = lemma10'' n₁ (~ i)         -- face 4: point 2 to 4
-- 2D path
-- note, how `lemma12` does not appear in the final, 2D-case
-- this is, because we explitictly split out [F1] from [G1] and [F2] from [G2]
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ lemma10 0 j       [a]
-- i = i1 ⊢ lemma10 0 (~ j)   [b]
-- j = i0 ⊢ lemma10 0 i       [c]
-- j = i1 ⊢ lemma10 0 (~ i)   [d]
--
-- i j | a  b c  d | a b c d |
-- ----|-----------|---------|---
-- 0 0 | j    i    | 0   0   | 0
-- 0 1 | j      ~i | 1     1 | 1     ⇒ "i xor j" ≡ (i ∨ j) ∧ ~(i ∧ j)
-- 1 0 |   ~j i    |   1 1   | 1
-- 1 1 |   ~j   ~i |   0   0 | 0
posneg i <ᶻ'' posneg j = lemma10'' 0 ((i ∨ j) ∧ ~(i ∧ j)) -- square 1: face 1 to 2 to 3 to 4

_<ᶻᵖ_ : hPropRel ℤ ℤ ℓ-zero
(x <ᶻᵖ y) .fst = x <ᶻ' y
(x <ᶻᵖ y) .snd = {!   !}

_<ᶠ''_ : (ℤ × ℕ₊₁) → (ℤ × ℕ₊₁) → Type₀
(aᶻ , aⁿ⁺¹) <ᶠ'' (bᶻ , bⁿ⁺¹) = {! a * ℕ₊₁→ℤ d <ᶻ' c * ℕ₊₁→ℤ b  !}

_<ᶠ'_ : ℚ → ℚ → _
x <ᶠ' y = elimProp2 {A = ℤ × ℕ₊₁} {R = _∼_} {C = C} γ κ x y
  where
  φ : ℚ → ℚ → hProp ℓ-zero
  φ x y = {! ? , ?  !}
  C : ℚ → ℚ → Type
  C x y = [ φ x y ]
  γ : (x y : ℚ) → isProp (C x y)
  γ x y = {!   !}
  κ : (a b : ℤ × ℕ₊₁) → C [ a ]ᶠ [ b ]ᶠ
  κ a b = {!   !}

_<ᶠ_ : hPropRel ℚ ℚ ℓ-zero
x <ᶠ y = {! elimProp2 {A = ℤ × ℕ₊₁} {R = _∼_} {C = C} γ κ x y   !}
  where
  φ : ℚ → ℚ → hProp ℓ-zero
  φ x y = {!   !}
  C : ℚ → ℚ → Type
  C x y = [ φ x y ]
  γ : (x y : ℚ) → isProp (C x y)
  γ x y = {!   !}
  κ : (a b : ℤ × ℕ₊₁) → C [ a ]ᶠ [ b ]ᶠ
  κ a b = {!   !}

-- and there is `onCommonDenom` in `Cubical.HITs.Rationals.QuoQ.Properties` to define operations

-- open import Cubical.HITs.Ints.QuoInt.Base renaming


sucⁿ-creates-<ⁿᵖ : ∀ a b → [ a <ⁿᵖ b ⇔ suc a <ⁿᵖ suc b ]
sucⁿ-creates-<ⁿᵖ a b .fst (k , p) = k , (+-sucⁿ k (suc a)) ∙ (λ i → suc (p i))
sucⁿ-creates-<ⁿᵖ a b .snd (k , p) = k , inj-m+ⁿ {1} (sym (+-sucⁿ k (suc a)) ∙ p)

<ⁿᵖ-irrefl       : (a       : ℕ) → [ ¬ (a <ⁿᵖ a) ]
<ⁿᵖ-trans        : (a b x   : ℕ) → [ a <ⁿᵖ b ] → [ b <ⁿᵖ x ] → [ a <ⁿᵖ x ]
<ⁿᵖ-cotrans      : (a b     : ℕ) → [ a <ⁿᵖ b ] → (x : ℕ) → [ (a <ⁿᵖ x) ⊔ (x <ⁿᵖ b) ]
·ⁿ-preserves-<ⁿᵖ : (x y z   : ℕ) → [ 0 <ⁿᵖ z ] → [ x <ⁿᵖ y ] → [ (x *ⁿ z) <ⁿᵖ (y *ⁿ z) ]

-- abstract
-- <ⁿᵖ-irrefl zero (k , p) = ψ where abstract ψ = snotzⁿ (sym (+-sucⁿ k 0) ∙ p)

-- NOTE: `<-irreflᶻ'' (posneg i) p` forced this ?9 to be constrained to
--   ?9 (k = (fst x)) (p = (snd x)) = transp (λ i → [ lemma10'' 0 (((i1 ∨ i1) ∧ ~ i1 ∨ ~ i1) ∨ i) ]) i0 x : ⊥⊥
-- which demands an implementation in terms of lemma10''
-- <ⁿᵖ-irrefl zero q@(k , p) = transp (λ i → [ lemma10'' 0 (((i1 ∨ i1) ∧ ~ i1 ∨ ~ i1) ∨ i) ]) i0 q
-- <ⁿᵖ-irrefl zero q@(k , p) = transp (λ i → [ lemma10'' 0 ((i1 ∧ ~ i1) ∨ i) ]) i0 q
<ⁿᵖ-irrefl zero q@(k , p) = transp (λ i → [ lemma10'' 0 i ]) i0 q
<ⁿᵖ-irrefl (suc a) (k , p) = φ where
  abstract φ = snotzⁿ (inj-m+ⁿ {a} (+-sucⁿ a k ∙ (λ i → suc (+-commⁿ a k i)) ∙ sym (+-sucⁿ k a) ∙ inj-m+ⁿ {1} (sym (+-sucⁿ k (suc a)) ∙ p) ∙ sym (+-zeroⁿ a)))


<ⁿᵖ-trans a b c = Cubical.Data.Nat.Order.<-trans

-- <ⁿᵖ-trans  zero    zero    zero   q₁@(k₁ , p₁) q₂@(k₂ , p₂) = q₁
-- <ⁿᵖ-trans  zero    zero   (suc c) q₁@(k₁ , p₁) q₂@(k₂ , p₂) = q₂
-- <ⁿᵖ-trans  zero   (suc b)  zero   q₁@(k₁ , p₁) q₂@(k₂ , p₂) = ⊥-elim {A = λ _ → [ zero <ⁿᵖ zero ]} $ snotzⁿ (sym (+-sucⁿ k₂ (suc b)) ∙ p₂)
-- <ⁿᵖ-trans  zero   (suc b) (suc c) q₁@(k₁ , p₁) q₂@(k₂ , p₂) = k₂ +ⁿ (k₁ +ⁿ 1) , sym (+-assocⁿ k₂ _ 1) ∙ (λ i → k₂ +ⁿ +-sucⁿ (k₁ +ⁿ 1) 0 i) ∙ (λ i → k₂ +ⁿ suc (+-zeroⁿ (k₁ +ⁿ 1) i)) ∙ (λ i → k₂ +ⁿ suc (p₁ i)) ∙ p₂
-- <ⁿᵖ-trans (suc a)  zero    zero   q₁@(k₁ , p₁) q₂@(k₂ , p₂) = ⊥-elim {A = λ _ → [ suc a <ⁿᵖ zero ]} $ <ⁿᵖ-irrefl zero q₂
-- <ⁿᵖ-trans (suc a)  zero   (suc c) q₁@(k₁ , p₁) q₂@(k₂ , p₂) = ⊥-elim {A = λ _ → [ suc a <ⁿᵖ suc c ]} $ snotzⁿ (sym (+-sucⁿ k₁ (suc a)) ∙ p₁)
-- <ⁿᵖ-trans (suc a) (suc b)  zero   q₁@(k₁ , p₁) q₂@(k₂ , p₂) = ⊥-elim {A = λ _ → [ suc a <ⁿᵖ zero ]} $ snotzⁿ (sym (+-sucⁿ k₂ (suc b)) ∙ p₂)
-- <ⁿᵖ-trans (suc a) (suc b) (suc c) q₁@(k₁ , p₁) q₂@(k₂ , p₂) = k₂ +ⁿ  (k₁ +ⁿ 1) , (
--   (k₂ +ⁿ  (k₁ +ⁿ 1)) +ⁿ suc (suc a)  ≡⟨ {!   !} ⟩
--    k₂ +ⁿ ((k₁ +ⁿ 1)  +ⁿ suc (suc a)) ≡⟨ {!   !} ⟩
--    k₂ +ⁿ suc ((k₁ +ⁿ  1) +ⁿ  suc a ) ≡⟨ {!   !} ⟩
--    k₂ +ⁿ suc ( k₁ +ⁿ (1  +ⁿ  suc a)) ≡⟨ {!   !} ⟩
--    k₂ +ⁿ suc ( k₁ +ⁿ suc    (suc a)) ≡⟨ (λ i → k₂ +ⁿ suc (p₁ i)) ⟩
--    k₂ +ⁿ suc (suc b)                 ≡⟨ p₂ ⟩
--    suc c                             ∎)

<ⁿᵖ-cotrans  zero    zero        q      c  = ⊥-elim {A = λ _ → [ (zero <ⁿᵖ c) ⊔ (c <ⁿᵖ zero) ]}  (<ⁿᵖ-irrefl _ q)
<ⁿᵖ-cotrans  zero   (suc b)      q  zero   = inrᵖ q
<ⁿᵖ-cotrans  zero   (suc b)      q (suc c) = inlᵖ (c , +-commⁿ c 1)
<ⁿᵖ-cotrans (suc a)  zero   (k , p)     c  = ⊥-elim {A = λ _ → [ (suc a <ⁿᵖ c) ⊔ (c <ⁿᵖ zero) ]} (snotzⁿ (sym (+-sucⁿ k (suc a)) ∙ p))
<ⁿᵖ-cotrans (suc a) (suc b)      q  zero   = inrᵖ (b , +-commⁿ b 1)
<ⁿᵖ-cotrans (suc a) (suc b)      q (suc c) = transport (λ i → [ r i ⊔ s i ]) (<ⁿᵖ-cotrans a b (sucⁿ-creates-<ⁿᵖ a b .snd q) c)
  where abstract r : (a <ⁿᵖ c) ≡ (suc a <ⁿᵖ suc c)
                 s : (c <ⁿᵖ b) ≡ (suc c <ⁿᵖ suc b)
                 r = ⇔toPath (sucⁿ-creates-<ⁿᵖ a c .fst) (sucⁿ-creates-<ⁿᵖ a c .snd)
                 s = ⇔toPath (sucⁿ-creates-<ⁿᵖ c b .fst) (sucⁿ-creates-<ⁿᵖ c b .snd)

·ⁿ-preserves-<ⁿᵖ = {!   !}


<-irreflᶻ''       : (a       : ℤ) → [ ¬ (a <ᶻ'' a) ]
<-transᶻ''        : (a b x   : ℤ) → [ a <ᶻ'' b ] → [ b <ᶻ'' x ] → [ a <ᶻ'' x ]
<-cotransᶻ''      : (a b     : ℤ) → [ a <ᶻ'' b ] → (x : ℤ) → [ (a <ᶻ'' x) ⊔ (x <ᶻ'' b) ]
-- ·ᶻ-preserves-<ᶻ'' : (x y z   : ℤ) → [ 0 <ᶻ'' z ] → [ x <ᶻ'' y ] → [ (x *ᶻ z) <ᶻ'' (y *ᶻ z) ]

-- lemma10'' : ∀ n → (n <ⁿᵖ 0) ≡ ⊥

-- (i ∨ i) ∧ (~ i ∨ ~ i))
-- i0
-- lemma10'' 0 (~ i) = (⊥ ≡ (n <ⁿᵖ 0)) i

-- lemma14 :

<-irreflᶻ'' (pos zero)    = <ⁿᵖ-irrefl 0
<-irreflᶻ'' (pos (suc n)) = <ⁿᵖ-irrefl (suc n)
<-irreflᶻ'' (neg zero)    = <ⁿᵖ-irrefl 0
<-irreflᶻ'' (neg (suc n)) = <ⁿᵖ-irrefl (suc n)
-- <-irreflᶻ'' (posneg i) p  = transport (λ j → [ lemma10'' 0 (((i ∨ i) ∧ (~ i ∨ ~ i)) ∨ j) ]) p
<-irreflᶻ'' (posneg i) p  = transport (λ j → [ lemma10'' 0 ((i ∧ ~ i) ∨ j) ]) p
-- <-irreflᶻ'' (posneg i) p  =
-- <-irreflᶻ'' (posneg i) p  = {! transport (λ j → [ lemma10'' 0 (((i ∨ i) ∧ (~ i ∨ ~ i)) ∨ j) ])     !} where
--   κ : [ lemma10'' 0 i1 ] ≡ {! <ⁿᵖ-irrefl 0    !}
--   κ = {!   !}
-- <-irreflᶻ'' (posneg i) p = transport (λ j → [ lemma10'' 0 ((i ∧ ~ i) ∨ j) ]) p
-- <-irreflᶻ'' (posneg i) p = transport (λ j → [ lemma10'' 0 (i₀ ∨ j) ]) p

-- The problem is that when we write ̀with f x | pr`, `with` decides to call `y`
-- the result `f x` and to replace *all* of the occurences of `f x` in the type
-- of `pr` with `y`. That is to say that if we were to write:
-- ...
-- then `with` would abstract `m + n` as `p` on *both* sides of the equality
-- proven by `refl` thus giving us the following goal with an extra, useless,
-- assumption:
-- ...
-- Given that `inspect` has the type `∀ f n → Reveal f · n is (f n)`, when we
-- write `with f n | inspect f n`, the only `f n` that can be abstracted in the
-- type of `inspect f n` is the third argument to `Reveal_·_is_`.
-- That is to say that the auxiliary definition generated looks like this:
--
-- plus-eq-reveal : ∀ m n → Plus-eq m n (m + n)
-- plus-eq-reveal m n = aux m n (m + n) (my-inspect (m +_) n) where
--
--   aux : ∀ m n p → MyReveal (m +_) · n is p → Plus-eq m n p
--   aux m n zero    [ m+n≡0   ] = m+n≡0⇒m≡0 m m+n≡0 , m+n≡0⇒n≡0 m m+n≡0
--   aux m n (suc p) [ m+n≡1+p ] = m+n≡1+p
--
-- At the cost of having to unwrap the constructor `[_]` around the equality
-- we care about, we can keep relying on `with` and avoid having to roll out
-- handwritten auxiliary definitions.


record Reveal_·_is_ {a b} {A : Type a} {B : A → Type b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Type (ℓ-max a b) where
  eta-equality
  constructor [_]ⁱ
  field eq : f x ≡ y -- lhs stays fix, rhs gets splitted

inspect : ∀{a b} {A : Type a} {B : A → Type b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]ⁱ

record Reveal'_·_is_ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
                   (f⁻¹ : B → A)
                   (y : B) (x : A)
                   : Type ℓ where
  eta-equality
  constructor [_]ⁱ'
  field eq' : x ≡ f⁻¹ y

inspect' : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
          (f⁻¹ : B → A) (f : A → B) (x : A) → f⁻¹ (f x) ≡ x → Reveal' f⁻¹ · (f x) is x
inspect' f⁻¹ f x p = [ sym p ]ⁱ'

reprℤ : ℤ → Sign × ℕ
reprℤ z = sign z , abs z

reprℤ⁻¹ : Sign × ℕ → ℤ
reprℤ⁻¹ (s , n) = signed s n

reprℤ-id : ∀ z → reprℤ⁻¹ (reprℤ z) ≡ z
reprℤ-id (pos  zero  ) = refl
reprℤ-id (pos (suc n)) = refl
reprℤ-id (neg  zero  ) = posneg
reprℤ-id (neg (suc n)) = refl
reprℤ-id (posneg   i ) = λ j → posneg (i ∧ j)

inspect-reprℤ : (x : ℤ) → Reveal' reprℤ⁻¹ · (reprℤ x) is x
inspect-reprℤ a = inspect' reprℤ⁻¹ reprℤ a (reprℤ-id a)

_<ᶻ'''_ : ∀(x y : ℤ) → hProp ℓ-zero
x <ᶻ''' y with reprℤ x | reprℤ y | inspect-reprℤ x | inspect-reprℤ y
... | spos , x' | spos , y' | [ x≡ ]ⁱ' | [ y≡ ]ⁱ' = x' <ⁿᵖ y'
... | spos , x' | sneg , y' | [ x≡ ]ⁱ' | [ y≡ ]ⁱ' = ⊥
... | sneg , x' | spos , y' | [ x≡ ]ⁱ' | [ y≡ ]ⁱ' = ⊤
... | sneg , x' | sneg , y' | [ x≡ ]ⁱ' | [ y≡ ]ⁱ' = y' <ⁿᵖ x'

<ᶻ''≡<ᶻ''' : ∀ x y → x <ᶻ'' y ≡ x <ᶻ''' y
<ᶻ''≡<ᶻ''' (pos  zero  ) (pos  zero  ) = refl
<ᶻ''≡<ᶻ''' (pos  zero  ) (pos (suc y)) = refl
<ᶻ''≡<ᶻ''' (pos (suc x)) (pos  zero  ) = refl
<ᶻ''≡<ᶻ''' (pos (suc x)) (pos (suc y)) = refl
<ᶻ''≡<ᶻ''' (pos  zero  ) (neg  zero  ) = sym (lemma10'' _)
<ᶻ''≡<ᶻ''' (pos  zero  ) (neg (suc y)) = refl
<ᶻ''≡<ᶻ''' (pos (suc x)) (neg  zero  ) = sym (lemma10'' _)
<ᶻ''≡<ᶻ''' (pos (suc x)) (neg (suc y)) = refl
<ᶻ''≡<ᶻ''' (neg  zero  ) (pos  zero  ) = sym (lemma10'' _)
<ᶻ''≡<ᶻ''' (neg  zero  ) (pos (suc y)) = sym (lemma12'' _)
<ᶻ''≡<ᶻ''' (neg (suc x)) (pos  zero  ) = refl
<ᶻ''≡<ᶻ''' (neg (suc x)) (pos (suc y)) = refl
<ᶻ''≡<ᶻ''' (neg  zero  ) (neg  zero  ) = refl
<ᶻ''≡<ᶻ''' (neg  zero  ) (neg (suc y)) = lemma10'' _
<ᶻ''≡<ᶻ''' (neg (suc x)) (neg  zero  ) = lemma12'' _
<ᶻ''≡<ᶻ''' (neg (suc x)) (neg (suc y)) = refl

<ᶻ''≡<ᶻ''' (pos  zero  ) (posneg i) = λ j → lemma10'' 0 (~ j ∧ i)
<ᶻ''≡<ᶻ''' (pos (suc x)) (posneg i) = λ j → lemma10'' (suc x) (~ j ∧ i)
<ᶻ''≡<ᶻ''' (neg  zero  ) (posneg i) = λ j → lemma10'' 0 (~ j ∧ ~ i)
<ᶻ''≡<ᶻ''' (neg (suc x)) (posneg i) = λ j → lemma12'' x (j ∨ ~ i)

<ᶻ''≡<ᶻ''' (posneg i) (pos  zero  ) = λ j → lemma10'' 0 (~ j ∧ i)
<ᶻ''≡<ᶻ''' (posneg i) (pos (suc y)) = λ j → lemma12'' y (~ j ∧ i)
<ᶻ''≡<ᶻ''' (posneg i) (neg  zero  ) = λ j → lemma10'' 0 (~ j ∧ ~ i)
<ᶻ''≡<ᶻ''' (posneg i) (neg (suc y)) = λ j → lemma10'' (suc y) (j ∨ ~ i)

-- Goal lemma10'' 0 ((i ∨ j) ∧ ~ i ∨ ~ j) ≡ (posneg i <ᶻ''' posneg j)
-- Have (0 <ⁿᵖ 0) ≡ ⊥
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ λ k → lemma10'' 0 (~ k ∧ j)
-- i = i1 ⊢ λ k → lemma10'' 0 (~ k ∧ ~ j)
-- j = i0 ⊢ λ k → lemma10'' 0 (~ k ∧ i)
-- j = i1 ⊢ λ k → lemma10'' 0 (~ k ∧ ~ i)
<ᶻ''≡<ᶻ''' (posneg i) (posneg   j ) = λ k → lemma10'' 0 (((i ∨ j) ∧ ~ i ∨ ~ j) ∧ ~ k)

_<ᶻ'''ʳ_ : ∀(x y : Sign × ℕ) → hProp ℓ-zero
-- NOTE: when using this definition, we get `<ᶻ'''≡<ᶻ'''ʳ` proven definitionally
--       but we do not get term normalization as we need it
-- x <ᶻ'''ʳ y = reprℤ⁻¹ x <ᶻ''' reprℤ⁻¹  y
--       and when using this other definition, we get `<ᶻ'''≡'<ᶻ'''ʳ` proven definitionally
(spos , x) <ᶻ'''ʳ (spos , y) = x <ⁿᵖ y -- (pos x) <ᶻ''' (pos y)
(spos , x) <ᶻ'''ʳ (sneg , y) = ⊥       -- (pos x) <ᶻ''' (neg y)
(sneg , x) <ᶻ'''ʳ (spos , y) = ⊤       -- (neg x) <ᶻ''' (pos y)
(sneg , x) <ᶻ'''ʳ (sneg , y) = y <ⁿᵖ x -- (neg x) <ᶻ''' (neg y)

signʳ-≡ : ∀ z → sign z ≡ reprℤ z .fst
signʳ-≡ (signed s zero) = refl
signʳ-≡ (signed s (suc n)) = refl
signʳ-≡ (posneg i) = refl

<ᶻ'''≡<ᶻ'''ʳ : ∀ x y → reprℤ⁻¹ x <ᶻ''' reprℤ⁻¹ y ≡ x <ᶻ'''ʳ y
<ᶻ'''≡<ᶻ'''ʳ x@(sx , nx) y@(sy , ny) with sx | sy | signʳ-≡ (reprℤ⁻¹ x) | signʳ-≡ (reprℤ⁻¹ y)
... | sx' | sy' | px | py = {!   !}
-- <ᶻ'''≡<ᶻ'''ʳ (spos , x) (spos , y) = {! refl   !}
-- <ᶻ'''≡<ᶻ'''ʳ (spos , x) (sneg , y) = {! refl   !}
-- <ᶻ'''≡<ᶻ'''ʳ (sneg , x) (spos , y) = {! refl   !}
-- <ᶻ'''≡<ᶻ'''ʳ (sneg , x) (sneg , y) = {! refl   !}

<ᶻ'''≡'<ᶻ'''ʳ : ∀ x y → x <ᶻ''' y ≡ reprℤ x <ᶻ'''ʳ reprℤ y
<ᶻ'''≡'<ᶻ'''ʳ x y with reprℤ x | reprℤ y {- | inspect-reprℤ x | inspect-reprℤ y -}
... | spos , x' | spos , y' {- | [ x≡ ]ⁱ' | [ y≡ ]ⁱ' -} = refl
... | spos , x' | sneg , y' {- | [ x≡ ]ⁱ' | [ y≡ ]ⁱ' -} = refl
... | sneg , x' | spos , y' {- | [ x≡ ]ⁱ' | [ y≡ ]ⁱ' -} = refl
... | sneg , x' | sneg , y' {- | [ x≡ ]ⁱ' | [ y≡ ]ⁱ' -} = refl

<ᶻ'''≡''<ᶻ'''ʳ : ∀ x y → reprℤ⁻¹ x <ᶻ''' reprℤ⁻¹ y ≡ x <ᶻ'''ʳ y
<ᶻ'''≡''<ᶻ'''ʳ x@(xs , xn) y@(ys , yn) with reprℤ (reprℤ⁻¹ x) | reprℤ (reprℤ⁻¹ y) | inspect-reprℤ (reprℤ⁻¹ x) | inspect-reprℤ (reprℤ⁻¹ y)
... | spos , x' | spos , y' | [ x≡ ]ⁱ' | [ y≡ ]ⁱ' = {! refl    !}
... | spos , x' | sneg , y' | [ x≡ ]ⁱ' | [ y≡ ]ⁱ' = {! refl    !}
... | sneg , x' | spos , y' | [ x≡ ]ⁱ' | [ y≡ ]ⁱ' = {! refl    !}
... | sneg , x' | sneg , y' | [ x≡ ]ⁱ' | [ y≡ ]ⁱ' = {! refl    !}


-- [ reprℤ⁻¹ (spos , a') <ᶻ''' reprℤ⁻¹ (spos , c') ]
-- [ reprℤ a <ᶻ'''ʳ reprℤ c ]
-- [ a <ᶻ''' c ]
-- [ a <ᶻ'' c ]

<ᶻ'''≡'''<ᶻ'''ʳ : ∀ x y → reprℤ⁻¹ x <ᶻ''' reprℤ⁻¹ y ≡ x <ᶻ'''ʳ y
<ᶻ'''≡'''<ᶻ'''ʳ x@(xs , xn) y@(ys , yn) with reprℤ (reprℤ⁻¹ x) | reprℤ (reprℤ⁻¹ y)
... | spos , x' | spos , y' = {!   !}
... | spos , x' | sneg , y' = {!   !}
... | sneg , x' | spos , y' = {!   !}
... | sneg , x' | sneg , y' = {!   !}


-- NOTE: making use of trichotomy might be in-line with the definition of QuoInt
--       because this is what we are likely to use at the end

-- -- {! pathTo⇐ (<ᶻ''≡<ᶻ''' a c ∙ (λ i → a≡ i <ᶻ''' c≡ i)) γ   !}
-- where γ : [ reprℤ⁻¹ (spos , a') <ᶻ''' reprℤ⁻¹ (spos , c') ]
--       γ = pathTo⇐ (<ᶻ'''≡<ᶻ'''ʳ (spos , a') (spos , c')) {!   !}
--       κ : [ reprℤ⁻¹ (spos , a') <ᶻ''' reprℤ⁻¹ (spos , c') ]
--       κ = {! <ᶻ'''≡'<ᶻ'''ʳ a c   !}

-- possible cases
-- NOTE: the "trick" is to with-abstract over `reprℤ a` and `reprℤ c`
--       which turns the type of `pathTo⇐ (<ᶻ''≡<ᶻ''' a c ∙ <ᶻ'''≡'<ᶻ'''ʳ a c)`
--       from `[ (reprℤ a <ᶻ'''ʳ reprℤ c) ⇒ (a <ᶻ'' c) ]`
--       into `a' <ⁿ c' → fst (a <ᶻ'' c)`
<-transᶻ'' a b c a<b b<c
  with reprℤ a | reprℤ b | reprℤ c
     | pathTo⇒ (<ᶻ''≡<ᶻ''' a b ∙ <ᶻ'''≡'<ᶻ'''ʳ a b) a<b
     | pathTo⇒ (<ᶻ''≡<ᶻ''' b c ∙ <ᶻ'''≡'<ᶻ'''ʳ b c) b<c
     | pathTo⇐ (<ᶻ''≡<ᶻ''' a c ∙ <ᶻ'''≡'<ᶻ'''ʳ a c)
... | spos , a' | spos , b' | spos , c' | a<b' | b<c' | p = p (<ⁿᵖ-trans _ _ _ a<b' b<c')
... | spos , a' | spos , b' | sneg , c' | a<b' | b<c' | p = p b<c'
... | spos , a' | sneg , b' | spos , c' | a<b' | b<c' | p = p (⊥-elim a<b')
... | spos , a' | sneg , b' | sneg , c' | a<b' | b<c' | p = p a<b'
... | sneg , a' | spos , b' | spos , c' | a<b' | b<c' | p = p a<b'
... | sneg , a' | spos , b' | sneg , c' | a<b' | b<c' | p = p (⊥-elim b<c')
... | sneg , a' | sneg , b' | spos , c' | a<b' | b<c' | p = p b<c'
... | sneg , a' | sneg , b' | sneg , c' | a<b' | b<c' | p = p (<ⁿᵖ-trans _ _ _ b<c' a<b')


<-cotransᶻ'' a b a<b c
  with reprℤ a | reprℤ b | reprℤ c
     | pathTo⇒ (<ᶻ''≡<ᶻ''' a b ∙ <ᶻ'''≡'<ᶻ'''ʳ a b) a<b
     | pathTo⇐ (λ i → (<ᶻ''≡<ᶻ''' a c ∙ <ᶻ'''≡'<ᶻ'''ʳ a c) i ⊔ (<ᶻ''≡<ᶻ''' c b ∙ <ᶻ'''≡'<ᶻ'''ʳ c b) i)
... | spos , a' | spos , b' | spos , c' | a<b' | p = p (<ⁿᵖ-cotrans _ _ a<b' c')
... | spos , a' | spos , b' | sneg , c' | a<b' | p = p (inrᵖ tt)
... | sneg , a' | spos , b' | spos , c' | a<b' | p = p (inlᵖ tt)
... | sneg , a' | spos , b' | sneg , c' | a<b' | p = p (inrᵖ tt)
... | sneg , a' | sneg , b' | spos , c' | a<b' | p = p (inlᵖ tt)
... | sneg , a' | sneg , b' | sneg , c' | a<b' | p = p (pathTo⇒ (⊔-comm (b' <ⁿᵖ c') (c' <ⁿᵖ a')) (<ⁿᵖ-cotrans _ _ a<b' c'))


-- [_/_] : ℤ → ℕ₊₁ → ℚ
-- [ a / b ] = [ a , b ]

lemma15 : ∀(a@(an , ad) b@(bn , bd) : ℤ × ℕ₊₁) → a ∼ b → ((sign an , abs an) , ad) ≡ ((sign bn , abs bn) , bd)
lemma15 a@(an , ad) b@(bn , bd) a~b = {!   !}


reprℚ : ℚ → (Sign × ℕ) × ℕ₊₁
reprℚ [ n , d ]ᶠ = (sign n , abs n) , d
reprℚ (eq/ a@(an , ad) b@(bn , bd) r i) = lemma15 a b r i
reprℚ (squash/ a b p q i j) = {!   !}

reprℚ⁻¹ : (Sign × ℕ) × ℕ₊₁ → ℚ
reprℚ⁻¹ ((s , n) , d) = [ signed s n , d ]ᶠ

lemma15' : ∀(a@(an , ad) b@(bn , bd) : ℤ × ℕ₊₁) → a ∼ b → (an , ad) ≡ (bn , bd)
lemma15' a@(an , ad) b@(bn , bd) a~b = {!   !}

import Cubical.HITs.SetQuotients.Properties as SetQuotients

reprℚ' : ℚ → ℤ × ℕ₊₁
reprℚ' [ n , d ]ᶠ = n , d
reprℚ' (eq/ a@(an , ad) b@(bn , bd) r i) = lemma15' a b r i
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ reprℚ' (p j)
-- i = i1 ⊢ reprℚ' (q j)
-- j = i0 ⊢ reprℚ' a
-- j = i1 ⊢ reprℚ' b
-- i : p j ≡ q j
-- j : a   ≡ b
--
-- j
-- ∧
-- | p1 = b      q1 = b
-- |
-- | p0 = a      q0 = a
-- +--------------------> i
--
-- i : p ≡ q
-- reprℚ' (squash/ a b p q i j) = reprℚ' (isSetℚ a b p q i j) -- termination checker complains
-- reprℚ' (squash/ a b p q i j) = {!   !} (isSetℚ a b p q i j)
reprℚ' (squash/ a b p q i j) = {! SetQuotients.rec2    !}
-- reprℚ' (squash/ a b p q i j) = {! SetQuotients.elimProp {A = ℤ × ℕ₊₁} {R = _∼_} {B = λ _ → ℤ × ℕ₊₁}   !}

-- NOTE: `onCommonDenom` uses `SetQuotient.rec2 isSetℚ`

reprℚ'' : ℚ → ℤ × ℕ₊₁
reprℚ'' q = SetQuotients.elim {A = ℤ × ℕ₊₁} {R = _∼_} {B = λ _ → ℤ × ℕ₊₁} γ (λ x → x) κ q where
  γ : (x : (ℤ × ℕ₊₁) // _∼_) → isSet (ℤ × ℕ₊₁)
  γ x = {!   !} -- this should work out
  κ : (a b : ℤ × ℕ₊₁) (r : a ∼ b) → a ≡ b
  κ a b a∼b = {!   !} -- this is an issue

reprℚ''' : ℚ → ℤ × ℕ₊₁
reprℚ''' q = SetQuotients.rec {A = ℤ × ℕ₊₁} {R = _∼_} {B = ℤ × ℕ₊₁} γ (λ x → x) κ q where
  γ : isSet (ℤ × ℕ₊₁)
  γ = {!   !} -- this should work out
  κ : (a b : ℤ × ℕ₊₁) (r : a ∼ b) → a ≡ b
  κ (an , ad) (bn , bd) a∼b = {!   !} -- this is an issue

-- is seems that `∀ a b → a ∼ b → a ≡ b` is a necessity to perform this representation operation
-- there is no nominator or denominator being "the" nominator or denominator in QuoQ
--   therefore, we won't get a `reprℚ : ℚ → ℤ × ℕ₊₁` for QuoQ (only for SigmaQ where this is just `fst`)
-- but for two (or more) rationals, we can create a common denominator for them
-- we might be able to get `ℚ ≃ Sign × ℚ⁺` with an identification of +0 and -0 similar to QuoInt
-- with onCommonDenom3 we could treat three rational numbers as integers for an implementation of <-transᶠ
-- I guess that we need to show then, something like
--   κ : ∀ a₁ b₁ c₁ a₂ b₂ c₂
--     → a₁ ∼ a₂ → b₁ ∼ b₂ → c₁ ∼ c₂
--     → (a₁<b₁ : a₁ < b₁) → (b₁<c₁ : b₁ < c₁)
--     → (a₂<b₂ : a₂ < b₂) → (b₂<c₂ : b₂ < c₂)
--     → <-trans a₁ b₁ c₁ a₁<b₁ b₁<c₁ ≡ <-trans a₂ b₂ c₂ a₂<b₂ b₂<c₂
-- i.e. that transitivity respects the equivalence
-- this might be shown with "multiplication preserves transitivity" on ℕ
--   κ : ∀ a b c
--     → (n : ℕ₊₁)
--     → (a<b : a < b) → (b<c : b < c)
--     → (an<bn : a · n < b · n) → (bn<cn : b · n < c · n)
--     → <-trans a b c a<b b<c ≡ <-trans (a · n) (b · n) (c · n) an<bn bn<cn

-- in `Cubical.HITs.Rationals.SigmaQ.Base` (which uses `ℤ` for `QuoInt.ℤ`) we have
--
--   ℚ : Type₀
--   ℚ = Σ[ (a , b) ∈ ℤ × ℕ₊₁ ] areCoprime (abs a , ℕ₊₁→ℕ b)
--
-- in `Cubical.HITs.Ints.QuoInt.Base` we have
--
--   data ℤ : Type₀ where
--     signed : (s : Sign) (n : ℕ) → ℤ
--     posneg : signed spos 0 ≡ signed sneg 0
--
-- in `Cubical.Data.NatPlusOne.Base` we have
--
--   record ℕ₊₁ : Type₀ where
--     constructor 1+_
--     field
--       n : ℕ
--
-- and in `Data.Rational.Base` (which uses `ℤ` for `Builtin.Int`) we have
--
--   record ℚ : Set where
--     constructor mkℚ
--     field
--       numerator     : ℤ
--       denominator-1 : ℕ
--       .isCoprime    : Coprime ∣ numerator ∣ (suc denominator-1)
--
-- in `Agda.Builtin.Int` we have
--
--   data Int : Set where
--     pos    : (n : Nat) → Int
--     negsuc : (n : Nat) → Int
--
-- in `Agda.Builtin.Nat` we have
--
--   data Nat : Set where
--     zero : Nat
--     suc  : (n : Nat) → Nat
--
-- so the difference between the cubical "SigmaQ"-rationals and the non-cubical "Rational"-rationals is that
--   SigmaQ uses QuoInt and NatPlusOne where Rational uses Builtin.Int and Builtin.Nat

reprℚ⁻¹' : ℤ × ℕ₊₁ → ℚ
reprℚ⁻¹' (n , d) = [ n , d ]ᶠ

-- reprℚ-id : ∀ z → reprℚ⁻¹ (reprℚ z) ≡ z
-- reprℚ-id (pos  zero  ) = refl
-- reprℚ-id (pos (suc n)) = refl
-- reprℚ-id (neg  zero  ) = posneg
-- reprℚ-id (neg (suc n)) = refl
-- reprℚ-id (posneg   i ) = λ j → posneg (i ∧ j)
--
-- inspect-reprℚ : (x : ℚ) → Reveal' reprℚ⁻¹ · (reprℚ x) is x
-- inspect-reprℚ a = inspect' reprℚ⁻¹ reprℚ a (reprℚ-id a)

-- _<ᶠ_ : hPropRel ℚ ℚ ℓ-zero
-- x <ᶠ y = {! elimProp2 {A = ℤ × ℕ₊₁} {R = _∼_} {C = C} γ κ x y   !}
--   where
--   φ : ℚ → ℚ → hProp ℓ-zero
--   φ x y = {!   !}
--   C : ℚ → ℚ → Type
--   C x y = [ φ x y ]
--   γ : (x y : ℚ) → isProp (C x y)
--   γ x y = {!   !}
--   κ : (a b : ℤ × ℕ₊₁) → C [ a ]ᶠ [ b ]ᶠ
--   κ a b = {!   !}

-- ... | spos , snd₁ | fst₂ , snd₂ | fst₃ , snd₃ | [ eq ]ⁱ | [ eq₁ ]ⁱ | [ eq₂ ]ⁱ = {!   !}
-- ... | sneg , snd₁ | fst₂ , snd₂ | fst₃ , snd₃ | [ eq ]ⁱ | [ eq₁ ]ⁱ | [ eq₂ ]ⁱ = {!   !}

-- <-transᶻ'' (pos zero) (pos zero) (pos zero) a<b b<c = {!   !}
-- <-transᶻ'' (pos zero) (pos zero) (pos (suc n₂)) a<b b<c = {!   !}
-- <-transᶻ'' (pos zero) (pos (suc n₁)) (pos zero) a<b b<c = {!   !}
-- <-transᶻ'' (pos zero) (pos (suc n₁)) (pos (suc n₂)) a<b b<c = {!   !}
--
-- <-transᶻ'' (pos (suc n₀)) (pos zero) (pos zero) a<b b<c = {!   !}
-- <-transᶻ'' (pos (suc n₀)) (pos zero) (pos (suc n₂)) a<b b<c = {!   !}
-- <-transᶻ'' (pos (suc n₀)) (pos (suc n₁)) (pos zero) a<b b<c = {!   !}
-- <-transᶻ'' (pos (suc n₀)) (pos (suc n₁)) (pos (suc n₂)) a<b b<c = {!   !}
--
-- <-transᶻ'' (neg n₀) (pos n₁) (pos n₂) a<b b<c = {!   !}
-- <-transᶻ'' (neg n₀) (neg n₁) (pos n₂) a<b b<c = {!   !}
-- <-transᶻ'' (neg n₀) (neg n₁) (neg n₂) a<b b<c = {!   !}
--
-- <-transᶻ'' (signed s₀ n₀) (signed s₁ n₁) (posneg i) a<b b<c = {!   !}
--
-- <-transᶻ'' (signed s₀ n₀) (posneg i) (signed s₁ n₁) a<b b<c = {!   !}
--
-- <-transᶻ'' (signed s₀ n₀) (posneg i) (posneg i₁) a<b b<c = {!   !}
--
-- <-transᶻ'' (posneg i) (signed s₁ n₁) (signed s₂ n₂) a<b b<c = {!   !}
--
-- <-transᶻ'' (posneg i) (signed s₁ n₁) (posneg i₁) a<b b<c = {!   !}
--
-- <-transᶻ'' (posneg i) (posneg i₁) (signed s₂ n₂) a<b b<c = {!   !}
--
-- <-transᶻ'' (posneg i) (posneg i₁) (posneg i₂) a<b b<c = {!   !}

{-


-- -- 8 points
-- <-transᶻ'' (pos n₀) (pos n₁) (pos zero) a<b b<c = {! <ⁿᵖ-trans   !} -- point 1
-- <-transᶻ'' (pos n₀) (pos n₁) (pos (suc n₂)) a<b b<c = {!   !}
-- <-transᶻ'' (neg n₀) (pos n₁) (pos zero) a<b b<c = {!   !} -- point 2
-- <-transᶻ'' (neg n₀) (pos n₁) (pos (suc n₂)) a<b b<c = {!   !}
-- <-transᶻ'' (neg n₀) (neg n₁) (neg zero) a<b b<c = {!   !} -- point 3
-- <-transᶻ'' (neg n₀) (neg n₁) (neg (suc n₂)) a<b b<c = {!   !}
-- <-transᶻ'' (neg n₀) (neg n₁) (pos zero) a<b b<c = {!   !} -- point 4
-- <-transᶻ'' (neg n₀) (neg n₁) (pos (suc n₂)) a<b b<c = {!   !}
--
-- -- 12 edges
-- <-transᶻ'' (neg n₀) (pos n₁) (posneg k) a<b b<c = {!   !} -- 21 -- point 2
-- <-transᶻ'' (pos n₀) (pos n₁) (posneg k) a<b b<c = {!   !} -- 22 -- point 1
-- <-transᶻ'' (neg n₀) (neg n₁) (posneg k) a<b b<c = {!   !} -- 23 -- point 3 to 4
-- -- <-transᶻ'' (pos n₀) (neg n₁) (posneg k) a<b b<c = {!   !}
-- <-transᶻ'' (pos n₀) (posneg j) (pos n₂) a<b b<c = {!   !} -- 24
-- <-transᶻ'' (pos n₀) (posneg j) (neg n₂) a<b b<c = {!   !} -- 25
-- <-transᶻ'' (neg n₀) (posneg j) (pos n₂) a<b b<c = {!   !} -- 26
-- <-transᶻ'' (neg n₀) (posneg j) (neg n₂) a<b b<c = {!   !} -- 27
-- <-transᶻ'' (posneg i) (pos n₁) (pos n₂) a<b b<c = {!   !} -- 28
-- <-transᶻ'' (posneg i) (neg n₁) (pos n₂) a<b b<c = {!   !} -- 29
-- <-transᶻ'' (posneg i) (neg n₁) (neg n₂) a<b b<c = {!   !} -- 30
-- -- <-transᶻ'' (posneg i) (pos n₁) (neg n₂) a<b b<c = {!   !}
--
-- --  6 faces
-- <-transᶻ'' (pos n₀) (posneg j) (posneg k) a<b b<c = {!   !} -- 22 24 25
-- <-transᶻ'' (neg n₀) (posneg j) (posneg k) a<b b<c = {!   !} -- 21 23 26
-- <-transᶻ'' (posneg i) (pos n₁) (posneg k) a<b b<c = {!   !} -- 22 21 28
-- <-transᶻ'' (posneg i) (neg n₁) (posneg k) a<b b<c = {!   !} -- 23 29 30
-- <-transᶻ'' (posneg i) (posneg j) (pos n₂) a<b b<c = {!   !} -- 24 26 28 29
-- <-transᶻ'' (posneg i) (posneg j) (neg n₂) a<b b<c = {!   !} -- 25 27 30

-- (i ∨ k) ∧ ~ i ∨ ~ k
-- (i ∨ k) ∧ (~ i ∨ ~ k)
-- (i ∨ k) ∧ ~(i ∧ k)
-- i k | i ∨ k | i ∧ k | ~(i ∧ k) | (i ∨ k) ∧ ~(i ∧ k)
-- 0 0 |   0   |   0   |     1    |         0
-- 0 1 |   1   |   0   |     1    |         1
-- 1 0 |   1   |   0   |     1    |         1
-- 1 1 |   1   |   1   |     0    |         0
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ ?21 (n₀ = 0) (j = j) (k = k) (a<b = a<b) (b<c = b<c) -- : fst (lemma10'' 0 k)
-- i = i1 ⊢ ?22 (n₀ = 0) (j = j) (k = k) (a<b = a<b) (b<c = b<c) -- : fst (lemma10'' 0 (~ k))
-- j = i0 ⊢ ?23 (i = i) (n₁ = 0) (k = k) (a<b = a<b) (b<c = b<c) -- : fst (lemma10'' 0 ((i ∨ k) ∧ ~ i ∨ ~ k))
-- j = i1 ⊢ ?24 (i = i) (n₁ = 0) (k = k) (a<b = a<b) (b<c = b<c) -- : fst (lemma10'' 0 ((i ∨ k) ∧ ~ i ∨ ~ k))
-- k = i0 ⊢ ?25 (i = i) (j = j) (n₂ = 0) (a<b = a<b) (b<c = b<c) -- : fst (lemma10'' 0 i)
-- k = i1 ⊢ ?26 (i = i) (j = j) (n₂ = 0) (a<b = a<b) (b<c = b<c) -- : fst (lemma10'' 0 (~ i))
-- ———— Constraints ———————————————————————————————————————————
-- ?21 (n₀ = 0) (j = j) (k = k) (a<b = a<b) (b<c = b<c) = ?27 (i = i0) : fst (lemma10'' 0 k)
-- ?22 (n₀ = 0) (j = j) (k = k) (a<b = a<b) (b<c = b<c) = ?27 (i = i1) : fst (lemma10'' 0 (~ k))
-- ?23 (i = i) (n₁ = 0) (k = k) (a<b = a<b) (b<c = b<c) = ?27 (j = i0) : fst (lemma10'' 0 ((i ∨ k) ∧ ~ i ∨ ~ k))
-- ?24 (i = i) (n₁ = 0) (k = k) (a<b = a<b) (b<c = b<c) = ?27 (j = i1) : fst (lemma10'' 0 ((i ∨ k) ∧ ~ i ∨ ~ k))
-- ?25 (i = i) (j = j) (n₂ = 0) (a<b = a<b) (b<c = b<c) = ?27 (k = i0) : fst (lemma10'' 0 i)
-- ?26 (i = i) (j = j) (n₂ = 0) (a<b = a<b) (b<c = b<c) = ?27 (k = i1) : fst (lemma10'' 0 (~ i))

-- Goal [ lemma10'' 0 ((i ∨ k) ∧ ~ i ∨ ~ k) ]
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ ?20 (s₀ = spos) (n₀ = 0) (j = j) (k = k) (a<b = a<b) (b<c = b<c) -- : fst (lemma10'' 0 k)
-- i = i1 ⊢ ?20 (s₀ = sneg) (n₀ = 0) (j = j) (k = k) (a<b = a<b) (b<c = b<c) -- : fst (lemma10'' 0 (~ k))
-- j = i0 ⊢ ?22 (i = i) (s₁ = spos) (n₁ = 0) (k = k) (a<b = a<b) (b<c = b<c) -- : fst (lemma10'' 0 ((i ∨ k) ∧ ~ i ∨ ~ k))
-- j = i1 ⊢ ?22 (i = i) (s₁ = sneg) (n₁ = 0) (k = k) (a<b = a<b) (b<c = b<c) -- : fst (lemma10'' 0 ((i ∨ k) ∧ ~ i ∨ ~ k))
-- k = i0 ⊢ ?23 (i = i) (j = j) (s₂ = spos) (n₂ = 0) (a<b = a<b) (b<c = b<c) -- : fst (lemma10'' 0 i)
-- k = i1 ⊢ ?23 (i = i) (j = j) (s₂ = sneg) (n₂ = 0) (a<b = a<b) (b<c = b<c) -- : fst (lemma10'' 0 (~ i))
-- ———— Constraints ———————————————————————————————————————————
-- ?20 (s₀ = spos) (n₀ = 0) (j = j) (k = k) (a<b = a<b) (b<c = b<c) = ?24 (i = i0) : fst (lemma10'' 0 k)
-- ?20 (s₀ = sneg) (n₀ = 0) (j = j) (k = k) (a<b = a<b) (b<c = b<c) = ?24 (i = i1) : fst (lemma10'' 0 (~ k))
-- ?22 (i = i) (s₁ = spos) (n₁ = 0) (k = k) (a<b = a<b) (b<c = b<c) = ?24 (j = i0) : fst (lemma10'' 0 ((i ∨ k) ∧ ~ i ∨ ~ k))
-- ?22 (i = i) (s₁ = sneg) (n₁ = 0) (k = k) (a<b = a<b) (b<c = b<c) = ?24 (j = i1) : fst (lemma10'' 0 ((i ∨ k) ∧ ~ i ∨ ~ k))
-- ?23 (i = i) (j = j) (s₂ = spos) (n₂ = 0) (a<b = a<b) (b<c = b<c) = ?24 (k = i0) : fst (lemma10'' 0 i)
-- ?23 (i = i) (j = j) (s₂ = sneg) (n₂ = 0) (a<b = a<b) (b<c = b<c) = ?24 (k = i1) : fst (lemma10'' 0 (~ i))

-- 1 cube
<-transᶻ'' (posneg    i ) (posneg    j ) (posneg    k ) a<b b<c = {!    !} -- ?24

·ᶻ-preserves-<ᶻ'' = {!   !}


-- _*ᶻ_ = Cubical.HITs.Ints.QuoInt._*_
-- signᶻ = Cubical.HITs.Ints.QuoInt.sign

open import Data.Nat.Base using () renaming
  ( _⊔_ to maxⁿ
  ; _⊓_ to minⁿ
  )

-- NOTE: in `Cubical.HITs.Ints.QuoInt.Base` there is
--         Int→ℤ : Int → ℤ
--         ℤ→Int : ℤ → Int
--         Int≡ℤ : Int ≡ ℤ

open import Cubical.Data.Int using () renaming (pos to ℕ→Int)

ℕ→ℤ : ℕ → ℤ
ℕ→ℤ x = Int→ℤ (ℕ→Int x)


minᶻ : ℤ → ℤ → ℤ
minᶻ x y with sign x | sign y
... | spos | spos = pos (minⁿ (abs x) (abs y))
... | spos | sneg = y
... | sneg | spos = x
... | sneg | sneg = neg (maxⁿ (abs x) (abs y)) -- instead of `- ℕ→ℤ (maxⁿ ...)`

-- maxⁿ' : ℕ → ℕ → ℕ
-- maxⁿ' (zero ) (n    ) = n
-- maxⁿ' (suc m) (zero ) = suc m
-- maxⁿ' (suc m) (suc n) = suc (maxⁿ' m n)
--
-- minⁿ' : ℕ → ℕ → ℕ
-- minⁿ' (zero ) (n    ) = zero
-- minⁿ' (suc m) (zero ) = zero
-- minⁿ' (suc m) (suc n) = suc (minⁿ' m n)

maxⁿ≡0-right : ∀ n  → maxⁿ n 0 ≡ n
maxⁿ≡0-right zero    = refl
maxⁿ≡0-right (suc n) = refl

minⁿ≡0-right : ∀ n  → minⁿ n 0 ≡ 0
minⁿ≡0-right zero    = refl
minⁿ≡0-right (suc n) = refl


lemma : ∀ n → pos 0 ≡ neg (minⁿ n 0)
lemma n = posneg ∙ (λ j → neg (minⁿ≡0-right n (~ j)))
-- lemma n = posneg ∙ (λ j → neg (minⁿ≡0-right n (~ j)))

-- i = i0 ⊢ pos 0
-- i = i1 ⊢ lemma 0 j
-- j = i0 ⊢ pos 0
-- j = i1 ⊢ posneg i
--
-- ———— Constraints ———————————————————————————————————————————
-- posneg i = ?11 (j = i1) : ℤ
-- pos 0 = ?11 (j = i0) : ℤ
-- hcomp (doubleComp-faces (λ _ → pos 0) (λ j₁ → neg zero) j) (posneg j) = ?11 (i = i1) : ℤ
-- pos 0 = ?11 (i = i0) : ℤ

maxᶻ : ℤ → ℤ → ℤ
maxᶻ (pos n₀) (pos n₁) = pos (maxⁿ n₀ n₁)
maxᶻ (pos n₀) (neg n₁) = pos n₀
maxᶻ (neg n₀) (pos n₁) = pos n₁
maxᶻ (neg n₀) (neg n₁) = neg (minⁿ n₀ n₁)
-- pathes
maxᶻ (pos    n) (posneg i) = pos (maxⁿ≡0-right n i)
maxᶻ (neg zero) (posneg i) = posneg i -- `lemma zero i` does not work here
-- NOTE: better not use `lemma (suc n) i` because it creates an unnormalizable term:
--   `hcomp (doubleComp-faces (λ _ → pos 0) (λ j₁ → neg 0) j) (posneg j)`
maxᶻ (neg (suc n)) (posneg i) = posneg i -- lemma (suc n) i -- can also use `posneg i` here
maxᶻ (posneg i) (pos    n) = pos n
maxᶻ (posneg i) (neg    n) = posneg i
maxᶻ (posneg i) (posneg j) = posneg (i ∧ j) -- posneg (i ∧ j)

maxᶻ' : ℤ → ℤ → ℤ
maxᶻ' x y with sign x | sign y
... | spos | spos = pos (maxⁿ (abs x) (abs y))
... | spos | sneg = x
... | sneg | spos = y
... | sneg | sneg = neg (minⁿ (abs x) (abs y))

_ = maxᶻ -1 -1 ≡ -1 ∋ refl
_ = maxᶻ -1  0 ≡  0 ∋ refl
_ = maxᶻ -1  1 ≡  1 ∋ refl
_ = maxᶻ  0 -1 ≡  0 ∋ refl
_ = maxᶻ  0  0 ≡  0 ∋ refl
_ = maxᶻ  0  1 ≡  1 ∋ refl
_ = maxᶻ  1 -1 ≡  1 ∋ refl
_ = maxᶻ  1  0 ≡  1 ∋ refl
_ = maxᶻ  1  1 ≡  1 ∋ refl

_ = maxᶻ' -1 -1 ≡ -1 ∋ refl
_ = maxᶻ' -1  0 ≡  0 ∋ refl
_ = maxᶻ' -1  1 ≡  1 ∋ refl
_ = maxᶻ'  0 -1 ≡  0 ∋ refl
_ = maxᶻ'  0  0 ≡  0 ∋ refl
_ = maxᶻ'  0  1 ≡  1 ∋ refl
_ = maxᶻ'  1 -1 ≡  1 ∋ refl
_ = maxᶻ'  1  0 ≡  1 ∋ refl
_ = maxᶻ'  1  1 ≡  1 ∋ refl

-- sign' : ℤ → Sign
-- sign' (signed _ zero) = spos
-- sign' (signed s (suc _)) = s
-- sign' (posneg i) = spos

lemma2 : ∀ x y → maxᶻ x y ≡ maxᶻ' x y
lemma2 (pos  zero   ) (pos  zero   ) = refl
lemma2 (pos  zero   ) (pos (suc n₁)) = refl
lemma2 (pos (suc n₀)) (pos  zero   ) = refl
lemma2 (pos (suc n₀)) (pos (suc n₁)) = refl
lemma2 (pos  zero   ) (neg  zero   ) = refl
lemma2 (pos  zero   ) (neg (suc n₁)) = refl
lemma2 (pos (suc n₀)) (neg  zero   ) = refl
lemma2 (pos (suc n₀)) (neg (suc n₁)) = refl
lemma2 (neg  zero   ) (pos  zero   ) = refl
lemma2 (neg  zero   ) (pos (suc n₁)) = refl
lemma2 (neg (suc n₀)) (pos  zero   ) = refl
lemma2 (neg (suc n₀)) (pos (suc n₁)) = refl
lemma2 (neg  zero   ) (neg  zero   ) = sym posneg
lemma2 (neg  zero   ) (neg (suc n₁)) = refl
lemma2 (neg (suc n₀)) (neg  zero   ) = refl
lemma2 (neg (suc n₀)) (neg (suc n₁)) = refl
lemma2 (pos  zero   ) (posneg   j  ) = refl
lemma2 (pos (suc n₀)) (posneg   j  ) = refl
lemma2 (neg  zero   ) (posneg   j  ) = λ i → posneg (j ∧ (~ i))
lemma2 (neg (suc n₀)) (posneg   j  ) = refl
lemma2 (posneg   i  ) (pos  zero   ) = refl
lemma2 (posneg   i  ) (pos (suc n₁)) = refl
lemma2 (posneg   i  ) (neg  zero   ) = λ j → posneg (i ∧ (~ j))
lemma2 (posneg   i  ) (neg (suc n₁)) = refl
lemma2 (posneg   i  ) (posneg   j  ) = λ k → posneg (i ∧ j ∧ (~ k))

lemma3 : maxᶻ ≡ maxᶻ'
lemma3 = funExt₂ᶜ lemma2

-- maxᶻ (signed s₀ n₀) (signed s₁ n₁) = {!   !}
-- maxᶻ (signed s₀ n₀) (posneg j) = {!   !}
-- maxᶻ (posneg i) (signed s₁ n₁) = {!   !}
-- maxᶻ (posneg i) (posneg j) = {!   !}

minᶠ : ℚ → ℚ → ℚ
minᶠ x y = onCommonDenom f g h x y where
  f : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
  f a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) = minᶻ (aᶻ *ᶻ (ℕ₊₁→ℤ bⁿ)) (bᶻ *ᶻ (ℕ₊₁→ℤ aⁿ))
  g : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) : ℤ × ℕ₊₁)
    → aᶻ *ᶻ (ℕ₊₁→ℤ bⁿ) ≡ bᶻ *ᶻ (ℕ₊₁→ℤ aⁿ)
    → (ℕ₊₁→ℤ bⁿ) *ᶻ (f a c) ≡ (ℕ₊₁→ℤ aⁿ) *ᶻ (f b c)
  g a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) aᶻ*bⁿ≡bᶻ*aⁿ = {!    !}
  h : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) : ℤ × ℕ₊₁)
    → bᶻ *ᶻ (ℕ₊₁→ℤ cⁿ) ≡ cᶻ *ᶻ (ℕ₊₁→ℤ bⁿ)
    → (f a b) *ᶻ (ℕ₊₁→ℤ cⁿ) ≡ (f a c) *ᶻ (ℕ₊₁→ℤ bⁿ)
  h a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) bᶻ*cⁿ≡cᶻ*bⁿ = {!   !}

maxᶠ : ℚ → ℚ → ℚ
maxᶠ x y = {!   !}

0ᶠ 1ᶠ : ℚ
0ᶠ = 0
1ᶠ = 1

<-irreflᶠ       : (a       : ℚ) → [ ¬ (a <ᶠ a) ]
<-transᶠ        : (a b x   : ℚ) → [ a <ᶠ b ] → [ b <ᶠ x ] → [ a <ᶠ x ]
<-cotransᶠ      : (a b     : ℚ) → [ a <ᶠ b ] → (x : ℚ) → [ (a <ᶠ x) ⊔ (x <ᶠ b) ]
·ᶠ-inv''        : (x       : ℚ) → (∥ Σ[ y ∈ ℚ ] x *ᶠ y ≡ 1ᶠ ∥ → [ x <ᶠ 0ᶠ ] ⊎ [ 0ᶠ <ᶠ x ]) × ([ x <ᶠ 0ᶠ ] ⊎ [ 0ᶠ <ᶠ x ] → ∥ Σ[ y ∈ ℚ ] x *ᶠ y ≡ 1ᶠ ∥)
≤-reflᶠ         : (a       : ℚ) → [ ¬ (a <ᶠ a) ]
≤-antisymᶠ      : (a b     : ℚ) → [ ¬ (b <ᶠ a) ] → [ ¬ (a <ᶠ b) ] → [ a ≡ₚ b ]
≤-transᶠ        : (a b x   : ℚ) → [ ¬ (b <ᶠ a) ] → [ ¬ (x <ᶠ b) ] → [ ¬ (x <ᶠ a) ]
is-minᶠ         : (x y z   : ℚ) → [ ¬ (minᶠ x y <ᶠ z) ⇔ ¬ (x <ᶠ z) ⊓ ¬ (y <ᶠ z) ]
is-maxᶠ         : (x y z   : ℚ) → [ ¬ (z <ᶠ maxᶠ x y) ⇔ ¬ (z <ᶠ x) ⊓ ¬ (z <ᶠ y) ]
+ᶠ-<ᶠ-ext       : (w x y z : ℚ) → [ (w +ᶠ x) <ᶠ (y +ᶠ z) ] → [ (w <ᶠ y) ⊔ (x <ᶠ z) ]
·ᶠ-preserves-<ᶠ : (x y z   : ℚ) → [ 0ᶠ <ᶠ z ] → [ x <ᶠ y ] → [ (x *ᶠ z) <ᶠ (y *ᶠ z) ]

<-irreflᶠ       = {!   !}
<-transᶠ        = {!   !}
<-cotransᶠ      = {!   !}
·ᶠ-inv''        = {!   !}
≤-reflᶠ         = {!   !}
≤-antisymᶠ      = {!   !}
≤-transᶠ        = {!   !}
is-minᶠ         = {!   !}
is-maxᶠ         = {!   !}
+ᶠ-<ᶠ-ext       = {!   !}
·ᶠ-preserves-<ᶠ = {!   !}

open PartiallyOrderedField

ℚF : PartiallyOrderedField {ℓ-zero} {ℓ-zero}
ℚF .PartiallyOrderedField.Carrier                  = ℚ
ℚF .PartiallyOrderedField.0f                       = 0 -- [ signed spos 0 , (1+ 0) ]'
ℚF .PartiallyOrderedField.1f                       = 1
ℚF .PartiallyOrderedField._+_                      = _+ᶠ_
ℚF .PartiallyOrderedField.-_                       = -ᶠ_
ℚF .PartiallyOrderedField._·_                      = _*ᶠ_
ℚF .PartiallyOrderedField.min                      = minᶠ
ℚF .PartiallyOrderedField.max                      = maxᶠ
ℚF .PartiallyOrderedField._<_                      = _<ᶠ_
ℚF .PartiallyOrderedField.is-PartiallyOrderedField = record
  { is-AlmostPartiallyOrderedField  = record
    { is-set               = isSetℚ
    ; is-CommRing          = record
      { is-set  = isSetℚ
      ; is-Ring = record
        { is-set    = isSetℚ
        ; +-AbGroup = record
          { is-set   = isSetℚ
          ; is-Group = record
            { is-set     = isSetℚ
            ; is-Monoid  = record
              { is-set       = isSetℚ
              ; is-Semigroup = record
                { is-set   = isSetℚ
                ; is-assoc = +-assocᶠ
                }
              ; is-identity  = λ x → +-identityʳ x , +-identityˡ x
              }
            ; is-inverse = λ x → (+-inverseʳ x) , (+-inverseˡ x)
            }
          ; is-comm  = +-commᶠ
          }
        ; ·-Monoid  = record
          { is-set       = isSetℚ
          ; is-Semigroup = record
            { is-set   = isSetℚ
            ; is-assoc = *-assocᶠ
            }
          ; is-identity  = λ x → *-identityʳ x , *-identityˡ x
          }
        ; is-dist   = λ x y z → sym (*-distribˡ x y z) , sym (*-distribʳ x y z)
        }
      ; ·-comm  = *-commᶠ
      }
    ; <-StrictPartialOrder = record
      { is-irrefl  = <-irreflᶠ
      ; is-trans   = <-transᶠ
      ; is-cotrans = <-cotransᶠ
      }
    ; ·-inv''              = ·ᶠ-inv''
    ; ≤-isLattice          = record
      { ≤-PartialOrder = record
        { is-refl    = ≤-reflᶠ
        ; is-antisym = ≤-antisymᶠ
        ; is-trans   = ≤-transᶠ
        }
      ; is-min         = is-minᶠ
      ; is-max         = is-maxᶠ
      }
    }
  ; +-<-ext                         = +ᶠ-<ᶠ-ext
  ; ·-preserves-<                   = ·ᶠ-preserves-<ᶠ
  }
  where open PartiallyOrderedField ℚF renaming (Carrier to ℚ')

-- 4.3 Archimedean property
--
-- We now define the notion of Archimedean ordered fields. We phrase this in terms of a certain
-- interpolation property, that can be defined from the fact that there is a unique morphism of
-- ordered fields from the rationals to every ordered field.

-- Lemma 4.3.3. For every ordered field (F, 0 F , 1 F , + F , · F , min F , max F , < F ), there is a unique morphism
-- i of ordered fields from the rationals to F . Additionally, i preserves < in the sense that for every q, r : Q
--   q < r ⇒ i (q) < F i (r ).

-- ∃! : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
-- ∃! A B = isContr (Σ A B)

-- isContr' A = Σ[ x ∈ A ] (∀ y → x ≡ y)

-- ℚ-IsInitialObject : ∀(OF : OrderedField {ℓ} {ℓ'}) → isContr (OrderedFieldMor ℚOF OF)
-- ℚ-IsInitialObject OF = {!!} , {!!}

-- Definition 4.3.5. Let (F, 0 F , 1 F , + F , · F , min F , max F , < F ) be an ordered field, so that we get a
-- canonical morphism i : Q → F of ordered fields, as in Lemma 4.3.3. We say the ordered field
-- (F, 0 F , 1 F , + F , · F , min F , max F , < F ) is Archimedean if
--   (∀x, y : F )(∃q : Q)x < i (q) < y.

-- IsArchimedian : OrderedField {ℓ} {ℓ'} → Type (ℓ-max ℓ ℓ')
-- IsArchimedian OF = let (orderedfieldmor i _) = fst (ℚ-IsInitialObject OF)
--                        open OrderedField OF
--                        ℚ = OrderedField.Carrier ℚOF
--                    in ∀ x y → ∃[ q ∈ ℚ ] (x < i q) × (i q < y)

-- If the ordered field is clear from the context, we will identify rationals q : Q with their in-
-- clusion i (q) in the ordered field, so that we may also say that (F, 0 F , 1 F , + F , · F , min F , max F , < F )
-- is Archimedean if
-- (∀x, y : F )(∃q : Q)x < q < y.

-- Example 4.3.6. In an Archimedean ordered field, all numbers are bounded by rationals. That
-- is, for a given x : F , there exist q, r : Q with q < x < r .

-- Example-4-3-6 : (OF : OrderedField {ℓ} {ℓ'})
--               → IsArchimedian OF
--               → let open OrderedField OF renaming (Carrier to F)
--                     (orderedfieldmor i _) = fst (ℚ-IsInitialObject OF)
--                     ℚ = OrderedField.Carrier ℚOF
--                 in ∀(x : F) → (∃[ q ∈ ℚ ] i q < x) × (∃[ r ∈ ℚ ] x < i r)
-- -- This follows from applying the Archimedean property to x − 1 < x and x < x + 1.
-- Example-4-3-6 OF isArchimedian = {!!}

-- 4.4 Cauchy completeness of real numbers
--
-- We focus on Cauchy completeness, rather than Dedekind or Dedekind-MacNeille completeness,
-- as we will focus on the computation of digit expansions, for which Cauchy completeness suffices.

-- In order to state that an ordered field is Cauchy complete, we need to define when sequences
-- are Cauchy, and when a sequence has a limit. We also take the opportunity to define
-- the set of Cauchy reals in Definition 4.4.9. Surprisingly, this ordered field cannot be shown to
-- be Cauchy complete.

-- Fix an ordered field (F, 0 F , 1 F , + F , · F , min F , max F , < F ).
module _ {ℓ ℓ'} (OF : PartiallyOrderedField {ℓ} {ℓ'}) where
  open PartiallyOrderedField OF renaming (Carrier to F)
  -- module ℚ = PartiallyOrderedField ℚ
  {-
  open PartiallyOrderedField ℚOF using () renaming (_<_ to _<ᵣ_; 0f to 0ᵣ)
  ℚ = PartiallyOrderedField.Carrier ℚOF
  iᵣ = PartiallyOrderedFieldMor.fun (fst (ℚ-IsInitialObject OF))
  open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ₙ_)

  -- We get a notion of distance, given by the absolute value as
  --   |x − y| := max F (x − y, −(x − y)).

  distance : ∀(x y : F) → F
  distance x y = max (x - y) (- (x - y))

  -- Consider a sequence x : N → F of elements of F . Classically, we may state that x is Cauchy as
  -- (∀ε : Q + )(∃N : N)(∀m, n : N)m, n ≥ N ⇒ |x m − x n | < ε,
  IsCauchy : (x : ℕ → F) → Type (ℓ-max ℓ' ℚℓ)
  IsCauchy x = ∀(ε : ℚ) → 0ᵣ <ᵣ ε → ∃[ N ∈ ℕ ] ∀(m n : ℕ) → N ≤ₙ m → N ≤ₙ n → distance (x m) (x n) < iᵣ ε

  -- We can interpret the quantifiers as in Definition 2.4.5.
  -- NOTE: this is the case, since `∃ A B = ∥ Σ A B ∥`

  -- Following a propositions-as-types interpretation, we may also state that x is Cauchy as the
  -- structure
  -- (Πε : Q + )(ΣN : N)(Πm, n : N)m, n ≥ N → |x m − x n | < ε.

  -- The dependent sum represents a choice of index N for every error ε, and so we have arrived at the following definition.

  -- Definition 4.4.1.
  -- For a sequence of reals x : N → F , a a modulus of Cauchy convergence is a map M : Q + → N such that
  -- (∀ε : Q + )(∀m, n : N)m, n ≥ M (ε) ⇒ |x m − x n | < ε.

  -- NOTE: do we already call these x "reals" ?
  -- NOTE: we are using the Modulus-type `((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ)` a few times and might abbreviate it

  IsModulusOfCauchyConvergence : (x : ℕ → F) → (M : ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ)) → Type (ℓ-max ℓ' ℚℓ)
  IsModulusOfCauchyConvergence x M = ∀(ε : ℚ) → (p : 0ᵣ <ᵣ ε) → ∀(m n : ℕ)
                                   → let instance _ = p
                                     in M ε ≤ₙ m → M ε ≤ₙ n → distance (x m) (x n) < iᵣ ε

  -- In constructive mathematics, we typically use such sequences with modulus, for example,
  -- because they can sometimes be used to compute limits of Cauchy sequences, avoiding choice axioms.

  -- Definition 4.4.2.
  -- A number l : F is the limit of a sequence x : N → F if the sequence
  -- converges to l in the usual sense:
  --   (∀ε : Q + )(∃N : N)(∀n : N)n ≥ N ⇒ |x n − l | < ε.

  IsLimit : (x : ℕ → F) → (l : F) → Type (ℓ-max ℓ' ℚℓ)
  IsLimit x l = ∀(ε : ℚ) → (0ᵣ <ᵣ ε) → ∃[ N ∈ ℕ ] ∀(n : ℕ) → N ≤ₙ n → distance (x n) l < iᵣ ε

  -- Remark 4.4.3. We do not consider the statement of convergence in propositions-as-types
  --
  --   (Πε : Q + )(ΣN : N)(Πn : N)n ≥ N → |x n − l | < ε,
  --
  -- because if the sequence has a modulus of Cauchy convergence M, then λε.M (ε/2) is a
  -- modulus of convergence to the limit l, so that we get an element of the above type.

  -- Definition 4.4.4.
  -- The ordered field (F, 0 F , 1 F , + F , · F , min F , max F , < F ) is said to be Cauchy complete
  -- if for every sequence x with modulus of Cauchy convergence M, we have a limit of x.
  -- In other words, an ordered field is Cauchy complete iff from a sequence–modulus pair (x, M), we can compute a limit of x.

  IsCauchyComplete : Type (ℓ-max (ℓ-max ℓ ℓ') ℚℓ)
  IsCauchyComplete = (x : ℕ → F)
                   → (M : ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ))
                   → IsModulusOfCauchyConvergence x M
                   → Σ[ l ∈ F ] IsLimit x l

  -- For the remainder of this section, additionally assume that F is Archimedean.
  module _ (isArchimedian : IsArchimedian OF) where

    -- Lemma 4.4.5.
    -- The type of limits of a fixed sequence x : N → F is a proposition.
    Lemma-4-4-5 : ∀(x : ℕ → F) → isProp (Σ[ l ∈ F ] IsLimit x l)
    -- Proof. This can be shown using the usual proof that limits are unique in Archimedean ordered fields, followed by an application of Lemma 2.6.20.
    Lemma-4-4-5 x = {!!}

    -- Corollary 4.4.6.
    -- Fix a given sequence x : N → F . Suppose that we know that there exists a
    -- limit of the sequence. Then we can compute a limit of the sequence.
    Corollary-4-4-6 : ∀(x : ℕ → F) → (∃[ l ∈ F ] IsLimit x l) → Σ[ l ∈ F ] IsLimit x l
    -- Proof. By applying the induction principle of propositional truncations of Definition 2.4.3.
    Corollary-4-4-6 x p = {!!} , {!!}

    -- Corollary 4.4.7.
    -- Fix a given sequence x : N → F . Suppose that, from a modulus of Cauchy
    -- convergence, we can compute a limit of the sequence. Then from the existence of the modulus of
    -- Cauchy convergence we can compute a limit of the sequence.
    Corollary-4-4-7 : (x : ℕ → F)
                    → ( (M : ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ))
                      → (isMCC : IsModulusOfCauchyConvergence x M)
                      → Σ[ l ∈ F ] IsLimit x l
                      )
                    -----------------------------------------------------------------------
                    → ∃[ M ∈ ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ) ] IsModulusOfCauchyConvergence x M
                    → Σ[ l ∈ F ] IsLimit x l
    -- Proof. By applying the induction principle of propositional truncations of Definition 2.4.3.
    Corollary-4-4-7 x f p = {!!}

    -- We can thus compute the limit of x : N → F as the number lim(x, p), where p is a proof
    -- that the limit of x exists. We will rather use the more traditional notation lim n→∞ x n for this
    -- number.

    -- Example 4.4.8 (Exponential function).
    -- In a Cauchy complete Archimedean ordered field, we can define an exponential function exp : F → F by
    --
    --    exp(x) = Σ_{k=0}^{∞} (xᵏ) / (k!)
    --
    -- For a given input x, we obtain the existence of a modulus of Cauchy convergence for the output from boundedness of
    -- x, that is, from the fact that (∃q, r : Q) q < x < r .

    exp : F → F
    exp x = {!!}

    Example-4-4-8 : ∀(x : F) → ∃[ M ∈ ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ) ] IsModulusOfCauchyConvergence {!!} M
    Example-4-4-8 x with Example-4-3-6 OF isArchimedian x
    ... | q' , r' = let q : ∃[ q ∈ ℚ ] iᵣ q < x
                        q = q'
                        r : ∃[ r ∈ ℚ ] x < iᵣ r
                        r = r'
                    in {!!}

    -- The point of this work is that, because we have a single language for properties and struc-
    -- ture, we can see more precisely what is needed for certain computations. In the above example,
    -- we explicitly do not require that inputs come equipped with a modulus of Cauchy convergence,
    -- but rather that there exists such a modulus. On the one hand, we do need a modulus to obtain
    -- the limit, but as the limit value is independent of the chosen modulus, existence of such a
    -- modulus suffices.
  -}

-}
