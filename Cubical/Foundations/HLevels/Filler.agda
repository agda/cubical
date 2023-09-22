{-# OPTIONS --safe #-}
module Cubical.Foundations.HLevels.Filler where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels.Base
open import Cubical.Foundations.HLevels.Extend

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    w x y z : A
    B : A → Type ℓ'


-- cube fillers

isSet' : Type ℓ → Type ℓ
isSet' A =
  {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  → Square a₀₋ a₁₋ a₋₀ a₋₁

isGroupoid' : Type ℓ → Type ℓ
isGroupoid' A =
  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
  (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
  (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
  → Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁


 -- types of hlevel n have cube fillers

isProp→isSet' : isProp A → isSet' A
isProp→isSet' h {a} p q r s i j =
  extendProp (λ _ → h) (i ∨ ~ i) (λ j → λ
    { (i = i0) → p j ; (i = i1) → q j
    ; (j = i0) → r i ; (j = i1) → s i }) j

isProp→SquareP : ∀ {B : I → I → Type ℓ} → ((i j : I) → isProp (B i j))
             → {a : B i0 i0} {b : B i0 i1} {c : B i1 i0} {d : B i1 i1}
             → (r : PathP (λ j → B j i0) a c) (s : PathP (λ j → B j i1) b d)
             → (t : PathP (λ j → B i0 j) a b) (u : PathP (λ j → B i1 j) c d)
             → SquareP B t u r s
isProp→SquareP {B = B} isPropB {a = a} r s t u i j =
  hcomp (λ { k (i = i0) → isPropB i0 j (base i0 j) (t j) k
           ; k (i = i1) → isPropB i1 j (base i1 j) (u j) k
           ; k (j = i0) → isPropB i i0 (base i i0) (r i) k
           ; k (j = i1) → isPropB i i1 (base i i1) (s i) k
        }) (base i j) where
    base : (i j : I) → B i j
    base i j = transport (λ k → B (i ∧ k) (j ∧ k)) a

isSet→isSet' : isSet A → isSet' A
isSet→isSet' Aset _ _ _ _ = toPathP (Aset _ _ _ _)

isSet→SquareP :
  {A : I → I → Type ℓ}
  (isSet : (i j : I) → isSet (A i j))
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → SquareP A a₀₋ a₁₋ a₋₀ a₋₁
isSet→SquareP isset a₀₋ a₁₋ a₋₀ a₋₁ i j =
  extendSet isset i0 (λ i j → λ
    { (i = i0) → a₀₋ j ; (i = i1) → a₁₋ j
    ; (j = i0) → a₋₀ i ; (j = i1) → a₋₁ i }) i j

isGroupoid→isGroupoid' : isGroupoid A → isGroupoid' A
isGroupoid→isGroupoid' isgrpd a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ i j k =
  extendGroupoid (λ _ _ _ → isgrpd) i0 (λ i j k → λ
    { (i = i0) → a₀₋₋ j k ; (i = i1) → a₁₋₋ j k
    ; (j = i0) → a₋₀₋ i k ; (j = i1) → a₋₁₋ i k
    ; (k = i0) → a₋₋₀ i j ; (k = i1) → a₋₋₁ i j }) i j k


-- cube fillers characterize hlevels

isContrPartial→isContr : ∀ {ℓ} {A : Type ℓ}
                       → (extend : ∀ φ → Partial φ A → A)
                       → (∀ u → u ≡ (extend i1 λ { _ → u}))
                       → isContr A
isContrPartial→isContr {A = A} extend law
  = ex , λ y → law ex ∙ (λ i → Aux.v y i) ∙ sym (law y)
    where ex = extend i0 empty
          module Aux (y : A) (i : I) where
            φ = ~ i ∨ i
            u : Partial φ A
            u = λ { (i = i0) → ex ; (i = i1) → y }
            v = extend φ u

isSet'→isSet : isSet' A → isSet A
isSet'→isSet Aset' x y p q = Aset' p q refl refl

isGroupoid'→isGroupoid : isGroupoid' A → isGroupoid A
isGroupoid'→isGroupoid Agpd' x y p q r s = Agpd' r s refl refl refl refl


-- dep hlevels

isContrDep→isPropDep : isOfHLevelDep 0 B → isOfHLevelDep 1 B
isContrDep→isPropDep {B = B} Bctr {a0 = a0} b0 b1 p i
  = comp (λ k → B (p (i ∧ k))) (λ k → λ where
        (i = i0) → Bctr .snd b0 refl k
        (i = i1) → Bctr .snd b1 p k)
      (c0 .fst)
  where
  c0 = Bctr {a0}

isPropDep→isSetDep : isOfHLevelDep 1 B → isOfHLevelDep 2 B
isPropDep→isSetDep {B = B} Bprp b0 b1 b2 b3 p i j
  = comp (λ k → B (p (i ∧ k) (j ∧ k))) (λ k → λ where
        (j = i0) → Bprp b0 b0 refl k
        (i = i0) → Bprp b0 (b2 j) (λ k → p i0 (j ∧ k)) k
        (i = i1) → Bprp b0 (b3 j) (λ k → p k (j ∧ k)) k
        (j = i1) → Bprp b0 b1 (λ k → p (i ∧ k) (j ∧ k)) k)
      b0

isPropDep→isSetDep'
  : isOfHLevelDep 1 B
  → {p : w ≡ x} {q : y ≡ z} {r : w ≡ y} {s : x ≡ z}
  → {tw : B w} {tx : B x} {ty : B y} {tz : B z}
  → (sq : Square p q r s)
  → (tp : PathP (λ i → B (p i)) tw tx)
  → (tq : PathP (λ i → B (q i)) ty tz)
  → (tr : PathP (λ i → B (r i)) tw ty)
  → (ts : PathP (λ i → B (s i)) tx tz)
  → SquareP (λ i j → B (sq i j)) tp tq tr ts
isPropDep→isSetDep' {B = B} Bprp {p} {q} {r} {s} {tw} sq tp tq tr ts i j
  = comp (λ k → B (sq (i ∧ k) (j ∧ k))) (λ k → λ where
        (i = i0) → Bprp tw (tp j) (λ k → p (k ∧ j)) k
        (i = i1) → Bprp tw (tq j) (λ k → sq (i ∧ k) (j ∧ k)) k
        (j = i0) → Bprp tw (tr i) (λ k → r (k ∧ i)) k
        (j = i1) → Bprp tw (ts i) (λ k → sq (k ∧ i) (j ∧ k)) k)
      tw
