{-# OPTIONS --safe #-}
module Cubical.Foundations.HLevels.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Agda.Builtin.Nat renaming (Nat to ℕ)


HLevel : Type₀
HLevel = ℕ


private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : A → Type ℓ'
    w x y z : A
    n : HLevel


isOfHLevel : HLevel → Type ℓ → Type ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc (suc n)) A = (x y : A) → isOfHLevel (suc n) (x ≡ y)


isOfHLevelΩ→isOfHLevel :
  ∀ {ℓ} {A : Type ℓ} (n : ℕ)
  → ((x : A) → isOfHLevel (suc n) (x ≡ x)) → isOfHLevel (2 + n) A
isOfHLevelΩ→isOfHLevel zero hΩ x y =
  J (λ y p → (q : x ≡ y) → p ≡ q) (hΩ x refl)
isOfHLevelΩ→isOfHLevel (suc n) hΩ x y =
  J (λ y p → (q : x ≡ y) → isOfHLevel (suc n) (p ≡ q)) (hΩ x refl)

TypeOfHLevel : ∀ ℓ → HLevel → Type (ℓ-suc ℓ)
TypeOfHLevel ℓ n = TypeWithStr ℓ (isOfHLevel n)

hProp hSet hGroupoid h2Groupoid : ∀ ℓ → Type (ℓ-suc ℓ)
hProp      ℓ = TypeOfHLevel ℓ 1
hSet       ℓ = TypeOfHLevel ℓ 2
hGroupoid  ℓ = TypeOfHLevel ℓ 3
h2Groupoid ℓ = TypeOfHLevel ℓ 4


-- lower h-levels imply higher h-levels

isOfHLevelSuc : (n : HLevel) → isOfHLevel n A → isOfHLevel (suc n) A
isOfHLevelSuc 0 = isContr→isProp
isOfHLevelSuc 1 = isProp→isSet
isOfHLevelSuc (suc (suc n)) h a b = isOfHLevelSuc (suc n) (h a b)

isSet→isGroupoid : isSet A → isGroupoid A
isSet→isGroupoid = isOfHLevelSuc 2

isGroupoid→is2Groupoid : isGroupoid A → is2Groupoid A
isGroupoid→is2Groupoid = isOfHLevelSuc 3

isOfHLevelPlus : (m : HLevel) → isOfHLevel n A → isOfHLevel (m + n) A
isOfHLevelPlus zero hA = hA
isOfHLevelPlus (suc m) hA = isOfHLevelSuc _ (isOfHLevelPlus m hA)

isContr→isOfHLevel : (n : HLevel) → isContr A → isOfHLevel n A
isContr→isOfHLevel zero cA = cA
isContr→isOfHLevel (suc n) cA = isOfHLevelSuc _ (isContr→isOfHLevel n cA)

isProp→isOfHLevelSuc : (n : HLevel) → isProp A → isOfHLevel (suc n) A
isProp→isOfHLevelSuc zero pA = pA
isProp→isOfHLevelSuc (suc n) pA = isOfHLevelSuc _ (isProp→isOfHLevelSuc n pA)

isOfHLevelPlus' : (m : HLevel) → isOfHLevel m A → isOfHLevel (m + n) A
isOfHLevelPlus' {n = n} 0 = isContr→isOfHLevel n
isOfHLevelPlus' {n = n} 1 = isProp→isOfHLevelSuc n
isOfHLevelPlus' {n = n} (suc (suc m)) hA a₀ a₁ = isOfHLevelPlus' (suc m) (hA a₀ a₁)


-- hlevel of path types

isProp→isContrPath : isProp A → (x y : A) → isContr (x ≡ y)
isProp→isContrPath h x y = h x y , isProp→isSet h x y _

isContr→isContrPath : isContr A → (x y : A) → isContr (x ≡ y)
isContr→isContrPath cA = isProp→isContrPath (isContr→isProp cA)

isOfHLevelPath' : (n : HLevel) → isOfHLevel (suc n) A → (x y : A) → isOfHLevel n (x ≡ y)
isOfHLevelPath' 0 = isProp→isContrPath
isOfHLevelPath' (suc n) h x y = h x y

isOfHLevelPath'⁻ : (n : HLevel) → ((x y : A) → isOfHLevel n (x ≡ y)) → isOfHLevel (suc n) A
isOfHLevelPath'⁻ zero h x y = h x y .fst
isOfHLevelPath'⁻ (suc n) h = h

isOfHLevelPath : (n : HLevel) → isOfHLevel n A → (x y : A) → isOfHLevel n (x ≡ y)
isOfHLevelPath 0 h x y = isContr→isContrPath h x y
isOfHLevelPath (suc n) h x y = isOfHLevelSuc n (isOfHLevelPath' n h x y)


-- h-level of isOfHLevel

isPropIsOfHLevel : (n : HLevel) → isProp (isOfHLevel n A)
isPropIsOfHLevel 0 = isPropIsContr
isPropIsOfHLevel 1 = isPropIsProp
isPropIsOfHLevel (suc (suc n)) f g i a b =
  isPropIsOfHLevel (suc n) (f a b) (g a b) i

isPropIsSet : isProp (isSet A)
isPropIsSet = isPropIsOfHLevel 2

isPropIsGroupoid : isProp (isGroupoid A)
isPropIsGroupoid = isPropIsOfHLevel 3

isPropIs2Groupoid : isProp (is2Groupoid A)
isPropIs2Groupoid = isPropIsOfHLevel 4


-- h-level of dependent path types

isOfHLevelPathP' : {A : I → Type ℓ} (n : HLevel)
                   → isOfHLevel (suc n) (A i1)
                   → (x : A i0) (y : A i1) → isOfHLevel n (PathP A x y)
isOfHLevelPathP' {A = A} n h x y =
  transport (λ i → isOfHLevel n (PathP (λ j → A (~ i ∨ j))
    (transport-filler (λ i → A i) x (~ i)) y)) (isOfHLevelPath' n h _ _)

isOfHLevelPathP : {A : I → Type ℓ} (n : HLevel)
                  → isOfHLevel n (A i1)
                  → (x : A i0) (y : A i1) → isOfHLevel n (PathP A x y)
isOfHLevelPathP {A = A} n h x y =
  transport (λ i → isOfHLevel n (PathP (λ j → A (~ i ∨ j))
    (transport-filler (λ i → A i) x (~ i)) y)) (isOfHLevelPath n h _ _)


-- Dependent h-level over a type

isOfHLevelDep : HLevel → {A : Type ℓ} (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isOfHLevelDep 0 {A = A} B = {a : A} → Σ[ b ∈ B a ] ({a' : A} (b' : B a') (p : a ≡ a') → PathP (λ i → B (p i)) b b')
isOfHLevelDep 1 {A = A} B = {a0 a1 : A} (b0 : B a0) (b1 : B a1) (p : a0 ≡ a1) → PathP (λ i → B (p i)) b0 b1
isOfHLevelDep (suc (suc  n)) {A = A} B = {a0 a1 : A} (b0 : B a0) (b1 : B a1) → isOfHLevelDep (suc n) {A = a0 ≡ a1} (λ p → PathP (λ i → B (p i)) b0 b1)

isContrDep : {A : Type ℓ} (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isContrDep = isOfHLevelDep 0

isPropDep : {A : Type ℓ} (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isPropDep = isOfHLevelDep 1

isContrDep∘
  : {A' : Type ℓ} (f : A' → A) → isContrDep B → isContrDep (B ∘ f)
isContrDep∘ f cB {a} = λ where
  .fst → cB .fst
  .snd b' p → cB .snd b' (cong f p)

isPropDep∘ : {A' : Type ℓ} (f : A' → A) → isPropDep B → isPropDep (B ∘ f)
isPropDep∘ f pB b0 b1 = pB b0 b1 ∘ cong f

isOfHLevelDep→isOfHLevel : (n : HLevel)
  → {A : Type ℓ} {B : A → Type ℓ'} → isOfHLevelDep n {A = A} B → (a : A) → isOfHLevel n (B a)
isOfHLevelDep→isOfHLevel 0 h a = h .fst , λ b → h .snd b refl
isOfHLevelDep→isOfHLevel 1 h a x y = h x y refl
isOfHLevelDep→isOfHLevel (suc (suc n)) h a x y = isOfHLevelDep→isOfHLevel (suc n) (h x y) refl

isOfHLevel→isOfHLevelDep : (n : HLevel)
  → {A : Type ℓ} {B : A → Type ℓ'} (h : (a : A) → isOfHLevel n (B a)) → isOfHLevelDep n {A = A} B
isOfHLevel→isOfHLevelDep 0 h {a} =
  (h a .fst , λ b' p → isProp→PathP (λ i → isContr→isProp (h (p i))) (h a .fst) b')
isOfHLevel→isOfHLevelDep 1 h = λ b0 b1 p → isProp→PathP (λ i → h (p i)) b0 b1
isOfHLevel→isOfHLevelDep (suc (suc n)) {A = A} {B} h {a0} {a1} b0 b1 =
  isOfHLevel→isOfHLevelDep (suc n) (λ p → helper p)
  where
  helper : (p : a0 ≡ a1) →
    isOfHLevel (suc n) (PathP (λ i → B (p i)) b0 b1)
  helper p = J (λ a1 p → ∀ b1 → isOfHLevel (suc n) (PathP (λ i → B (p i)) b0 b1))
                     (λ _ → h _ _ _) p b1
