{-
This module defines the `NPath` type, which conveniently represents a sequence of paths in a given type `A`.
This abstraction is primarily intended to ease the introduction of multiple paths into the context,
facilitating the creation of tests and examples.

The module also provides several utility lemmas for composing squares and cubes, which are frequently used in the accompanying solvers within the `PathSolver` module.
-}

{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order.Recursive

open import Cubical.Data.Sigma.Base




record NPath {ℓ} n (A : Type ℓ) : Type ℓ where
 field
  𝑣 : ∀ k → {k ≤ n} → A
  𝑝 : ∀ k → ∀ {k≤n sk≤n} → 𝑣 k {k≤n} ≡ 𝑣 (suc k) {sk≤n}

 abstract
  𝑣₀ : A
  𝑣₀ = 𝑣 0

  𝑣₁ : {1 ≤ n} → A
  𝑣₁ {k≤} = 𝑣 1 {k≤}

  𝑣₂ : {2 ≤ n} → A
  𝑣₂ {k≤} = 𝑣 2 {k≤}

  𝑣₃ : {3 ≤ n} → A
  𝑣₃ {k≤} = 𝑣 3 {k≤}

  𝑣₄ : {4 ≤ n} → A
  𝑣₄ {k≤} = 𝑣 4 {k≤}

  𝑣₅ : {5 ≤ n} → A
  𝑣₅ {k≤} = 𝑣 5 {k≤}

  𝑣₆ : {6 ≤ n} → A
  𝑣₆ {k≤} = 𝑣 6 {k≤}

  𝑣₇ : {7 ≤ n} → A
  𝑣₇ {k≤} = 𝑣 7 {k≤}


  𝑝₀ : ∀ {sk≤n} → 𝑣₀ ≡ 𝑣₁ {sk≤n}
  𝑝₀ {sk≤n} = 𝑝 zero {tt} {sk≤n}

  𝑝₁ : ∀ {k≤n sk≤n} → 𝑣₁ {k≤n} ≡ 𝑣₂ {sk≤n}
  𝑝₁ {k≤n} {sk≤n} = 𝑝 1 {k≤n} {sk≤n}

  𝑝₂ : ∀ {k≤n sk≤n} → 𝑣₂ {k≤n} ≡ 𝑣₃ {sk≤n}
  𝑝₂ {k≤n} {sk≤n} = 𝑝 2 {k≤n} {sk≤n}

  𝑝₃ : ∀ {k≤n sk≤n} → 𝑣₃ {k≤n} ≡ 𝑣₄ {sk≤n}
  𝑝₃ {k≤n} {sk≤n} = 𝑝 3 {k≤n} {sk≤n}

  𝑝₄ : ∀ {k≤n sk≤n} → 𝑣₄ {k≤n} ≡ 𝑣₅ {sk≤n}
  𝑝₄ {k≤n} {sk≤n} = 𝑝 4 {k≤n} {sk≤n}

  𝑝₅ : ∀ {k≤n sk≤n} → 𝑣₅ {k≤n} ≡ 𝑣₆ {sk≤n}
  𝑝₅ {k≤n} {sk≤n} = 𝑝 5 {k≤n} {sk≤n}

  𝑝₆ : ∀ {k≤n sk≤n} → 𝑣₆ {k≤n} ≡ 𝑣₇ {sk≤n}
  𝑝₆ {k≤n} {sk≤n} = 𝑝 6 {k≤n} {sk≤n}

data Sequence (n : ℕ) : Type where
 𝓿 : ∀ k → {k ≤ n} → Sequence n
 𝓹 : ∀ k → ∀ {k≤n sk≤n} → 𝓿 k {k≤n} ≡ 𝓿 (suc k) {sk≤n}


module _ {ℓ} n (A : Type ℓ) where

 fromNPath : (Sequence n → A) → NPath n A
 fromNPath x .NPath.𝑣 k {k≤n} = x (𝓿 k {k≤n})
 fromNPath x .NPath.𝑝 k {k≤n} {k≤n'} i = x (𝓹 k {k≤n} {k≤n'} i)

 toNPath : NPath n A → (Sequence n → A)
 toNPath x (𝓿 k {k≤n}) = x .NPath.𝑣 k {k≤n}
 toNPath x (𝓹 k {k≤n} {k≤n'} i) = x .NPath.𝑝 k {k≤n} {k≤n'} i

 IsoFunSequenceNPath : Iso (NPath n A) (Sequence n → A)
 IsoFunSequenceNPath .Iso.fun = toNPath
 IsoFunSequenceNPath .Iso.inv = fromNPath
 IsoFunSequenceNPath .Iso.rightInv b i a@(𝓿 k) = b a
 IsoFunSequenceNPath .Iso.rightInv b i a@(𝓹 k i₁) = b a
 IsoFunSequenceNPath .Iso.leftInv a i .NPath.𝑣 = a .NPath.𝑣
 IsoFunSequenceNPath .Iso.leftInv a i .NPath.𝑝 = a .NPath.𝑝







_∙f0_ : ∀ {ℓ} {A : Type ℓ} →
         ∀ {x₀ y₀ y₁ z : A}
         → {p₀ : x₀ ≡ y₀} {q₀ : y₀ ≡ z} {q₁ : y₁ ≡ z}
         → {r : x₀ ≡ y₁} {y≡ : y₀ ≡ y₁}
         → Square p₀ (λ _ → y₁)  r y≡
         → Square q₀ q₁ y≡ (λ _ → z)

         → Square (p₀ ∙' q₀) q₁ r λ _ → z
(u ∙f0 v) j i =
  hcomp (λ k → primPOr (~ i) (i ∨ j) (λ _ → u j (~ k)) λ _ → v j i)
        (v j i)

_∙f1_ : ∀ {ℓ} {A : Type ℓ} →
         ∀ {x₁ y₀ y₁ z : A}
         → {p₁ : x₁ ≡ y₁} {q₀ : y₀ ≡ z} {q₁ : y₁ ≡ z}
         → {r : y₀ ≡ x₁} {y≡ : y₀ ≡ y₁}
         → Square (λ _ → y₀) p₁ r y≡
         → Square q₀ q₁ y≡ (λ _ → z)

         → Square q₀ (p₁ ∙' q₁) r λ _ → z
(u ∙f1 v) j i =
    hcomp (λ k → primPOr (~ i) (i ∨ (~ j)) (λ _ → u j (~ k)) λ _ → v j i)
        (v j i)


_∙∙■_∙∙■_ : ∀ {ℓ} {A : Type ℓ} →
         ∀ {x x₀ x₁ x₂ x₃ : A}
         → {p₀ : x₀ ≡ x₁} {p₁ : x₁ ≡ x₂} {p₂ : x₂ ≡ x₃}
           {q₀ : x₀ ≡ x} {q₁ : x₁ ≡ x} {q₂ : x₂ ≡ x} {q₃ : x₃ ≡ x}
         → Square q₀ q₁ p₀ refl
         → Square q₁ q₂ p₁ refl
         → Square q₂ q₃ p₂ refl
         → Square q₀ q₃ (p₀ ∙∙ p₁ ∙∙ p₂) refl
_∙∙■_∙∙■_ {x = x} s₀ s₁ s₂ j i =
  hcomp (λ k → λ where
     (j = i0) → s₀ (~ k) i
     (j = i1) → s₂ k i
     (i = i1) → x
             ) (s₁ j i)

◪→≡ : ∀ {ℓ} {A : Type ℓ} {x y : A} {p p' : x ≡ y} →
           Square p' refl p refl → p ≡ p'
◪→≡ s i j =
   hcomp (λ k → λ where
     (j = i0) → s i0 (i ∧ ~ k)
     (i = i1) → s i0 (j ∨ ~ k)
     (i = i0) → s j i ; (j = i1) → s j i) (s j i)

◪→◪→≡ : ∀ {ℓ} {A : Type ℓ} {x y : A} {p₀ p₁ p : x ≡ y}
         → Square p refl p₀ refl
         → Square p refl p₁ refl
         → p₀ ≡ p₁
◪→◪→≡ {y = y} {p = p} s₀ s₁ i j =
   hcomp
    (λ k → primPOr (~ i ∨ ~ j ∨ j) i (λ _ →  s₀ j (~ k))
         λ _ → s₁ j (~ k)) y

◪→◪→≡' : ∀ {ℓ} {A : Type ℓ} {x y : A} {p₀ p₁ p : x ≡ y}
         → Square refl p refl p₀
         → Square refl p refl p₁
         → p₀ ≡ p₁
◪→◪→≡' {y = y} {p = p} s₀ s₁ i j =
 ◪→◪→≡ (λ i₁ i₂ → s₀ (~ i₁) (~ i₂))
       (λ i₁ i₂ → s₁ (~ i₁) (~ i₂)) i (~ j)

comp₋₀ : ∀ {ℓ} {A : Type ℓ} →
    {a a₀₀ : A} {a₀₋ : a₀₀ ≡ a}
  {a₁₀ : A} {a₁₋ : a₁₀ ≡ a}
  {a₋₀ a₋₀' : a₀₀ ≡ a₁₀}
  → Square a₀₋ a₁₋ a₋₀ refl
  → a₋₀' ≡ a₋₀
  → Square a₀₋ a₁₋ a₋₀' refl
comp₋₀ s p i j =
  hcomp (λ k → primPOr (~ j) (j ∨ i ∨ ~ i) (λ _ → p (~ k) i) λ _ → s i j)  (s i j)

◪mkSq : ∀ {ℓ} {A : Type ℓ} →
    {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ p₁₀ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ p₀₁ : a₀₁ ≡ a₁₁}
  → {p : a₀₀ ≡ a₁₁}
  → Square p p₀₁ a₀₋ refl
  → Square p₁₀ refl a₁₋ refl
  → Square p p₁₀ a₋₀ refl
  → Square  p₀₁ refl a₋₁ refl
  → Square a₀₋ a₁₋ a₋₀ a₋₁
◪mkSq {a₁₁ = a₁₁} s₀₋ s₁₋ s₋₀ s₋₁ i j =
  hcomp (λ k → λ where
     (i = i0) → s₀₋ j (~ k)
     (i = i1) → s₁₋ j (~ k)
     (j = i0) → s₋₀ i (~ k)
     (j = i1) → s₋₁ i (~ k))
    a₁₁


coh₃helper : ∀ {ℓ} {A : Type ℓ} →
               {x₀ x₁ : A} → {p p₀₀ p₀₁ p₁₀ p₁₁ : x₀ ≡ x₁} →
               {s₀₀ : Square refl p₀₀ refl p}
               {s₀₁ : Square refl p₀₁ refl p}
               {s₁₀ : Square refl p₁₀ refl p}
               {s₁₁ : Square refl p₁₁ refl p}
               →
               Cube _ _ _ _ (λ _ _ → x₀) (λ _ _ → x₁)
coh₃helper {x₀ = x₀} {p = p} {s₀₀ = s₀₀} {s₀₁} {s₁₀} {s₁₁} i j k =
   hcomp
      (λ z → λ {
        (k = i0) → x₀
       ;(k = i1) → p z
       ;(i = i0)(j = i0) → s₀₀ z k
       ;(i = i1)(j = i0) → s₁₀ z k
       ;(i = i0)(j = i1) → s₀₁ z k
       ;(i = i1)(j = i1) → s₁₁ z k
      }) x₀


comp-coh-helper : ∀ {ℓ} {A : Type ℓ} →
               {x₀ x₁ : A} → {p p₀ p₁ p₂ : x₀ ≡ x₁} →
               {s₀ : Square refl p₀ refl p}
               {s₁ : Square refl p₁ refl p}
               {s₂ : Square refl p₂ refl p}
               → Cube _ _ _ _ _ _
comp-coh-helper {x₀ = x₀} {x₁} {p = p} {p₀} {p₁} {p₂} {s₀ = s₀} {s₁} {s₂} =
  λ k i j  →
   hcomp
     (λ z → λ {
        (j = i0) → x₀
      ;(j = i1) → p (~ k ∨ z ∨ ~ i)
      ;(i = i0) → p₀ j
      ;(i = i1) → hcomp (λ k' → λ {(z = i0) → s₁ (k' ∧ ~ k)  j
                         ;(z = i1) → s₂ k' j
                         ;(j = i0) → x₀
                         ;(j = i1) → p (k' ∧ (~ k ∨ z))
                         }) x₀
      ;(k = i1) → hcomp
           (λ k → λ {(i = i0) → s₀ k j
                    ;(i = i1)(z = i0) → x₀
                    ;(i = i1)(z = i1) → s₂ k j
                    ;(j = i0) → x₀
                    ;(j = i1) → p (k ∧ (z ∨ ~ i))
                    }) x₀

       }) (hcomp (λ k' → λ {(i = i0) → s₀ k' j
                      ;(i = i1) → s₁ (k' ∧ ~ k) j
                      ;(j = i0) → x₀
                      ;(j = i1) → p (k' ∧ (~ k ∨ ~ i))
                       }) x₀)


coh-cub : ∀ {ℓ} {A : Type ℓ}  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ p₀₀₁ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ p₀₁₋' : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ p₀₁₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ p₀₋₁' : a₀₀₁ ≡ a₀₁₁}
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ p₁₀₋' : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ p₁₋₀' : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  {a₋₀₀ p₁₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ p₋₀₁' : a₀₀₁ ≡ a₁₀₁}
  {a₋₁₀ p₋₁₀' : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}

  {p₀₁₁ : a₀₀₀ ≡ a₀₁₁}
  {p₁₀₁ : a₀₀₀ ≡ a₁₀₁}
  {p₁₁₀ : a₀₀₀ ≡ a₁₁₀}
  {s₋₀₀ : Square refl p₁₀₀ refl a₋₀₀}
  {s₋₀₁ : Square p₀₀₁ p₁₀₁ refl a₋₀₁}
  {s₋₁₀ : Square p₀₁₀ p₁₁₀ refl a₋₁₀}

  {s₀₀₋ : Square refl p₀₀₁ refl a₀₀₋}
  {s₀₁₋ : Square p₀₁₀ p₀₁₁ refl a₀₁₋}
  {s₁₀₋ : Square p₁₀₀ p₁₀₁ refl a₁₀₋}

  {s₀₋₀ : Square refl p₀₁₀ refl a₀₋₀}
  {s₀₋₁ : Square p₀₀₁ p₀₁₁ refl a₀₋₁}
  {s₁₋₀ : Square p₁₀₀ p₁₁₀ refl a₁₋₀}


  {p₋₁₁ : a₁₀₀ ≡ a₁₁₁}
  {s'₁₋₀ : Square refl p₁₋₀' refl a₁₋₀}
  {s'₁₀₋ : Square refl p₁₀₋' refl a₁₀₋}
  {s'ₓ₁₋ : Square p₁₋₀' p₋₁₁ refl a₁₁₋}
  {s'ₓ₋₁ : Square p₁₀₋' p₋₁₁ refl a₁₋₁}


  {p₁₋₁ : a₀₁₀ ≡ a₁₁₁}
  {s'₀₁₋ : Square refl p₀₁₋' refl a₀₁₋}
  {s'₋₁₀ : Square refl p₋₁₀' refl a₋₁₀}
  {s'₁ₓ₋ : Square p₋₁₀' p₁₋₁ refl a₁₁₋}
  {s'₋ₓ₁ : Square p₀₁₋' p₁₋₁ refl a₋₁₁}


  {p₁₁₋ : a₀₀₁ ≡ a₁₁₁}
  {s'₋₀₁ : Square refl p₋₀₁' refl a₋₀₁}
  {s'₀₋₁ : Square refl p₀₋₁' refl a₀₋₁}
  {s'₁₋ₓ : Square p₋₀₁' p₁₁₋ refl a₁₋₁}
  {s'₋₁ₓ : Square p₀₋₁' p₁₁₋ refl a₋₁₁}

  (s₀q₁ : _)
  (c₀u₁ : Cube
    (λ z z' →  p₁₀₀ (~ z' ∨ z )) s₀q₁
    (λ _ z' → p₁₀₀ (~ z')) s'₁₀₋
    (λ _ _ → a₁₀₀) s₁₀₋ )
  (s₀q₂ : _)
  (c₀u₂ : Cube
    (λ z z' →  p₁₀₀ (~ z' ∨ z )) s₀q₂
    (λ _ z' → p₁₀₀ (~ z')) s'₁₋₀
    (λ _ _ → a₁₀₀) s₁₋₀ )

  (s₁q₀ : _)
  (c₁u₀ : Cube
    (λ z z' →  p₀₁₀ (~ z' ∨ z )) s₁q₀
    (λ _ z' → p₀₁₀ (~ z')) s'₀₁₋
    (λ _ _ → a₀₁₀) s₀₁₋ )
  (s₁q₂ : _)
  (c₁u₂ : Cube
    (λ z z' →  p₀₁₀ (~ z' ∨ z )) s₁q₂
    (λ _ z' → p₀₁₀ (~ z')) s'₋₁₀
    (λ _ _ → a₀₁₀) s₋₁₀ )

  (s₂q₀ : _)
  (c₂u₀ : Cube
    (λ z z' →  p₀₀₁ (~ z' ∨ z )) s₂q₀
    (λ _ z' → p₀₀₁ (~ z')) s'₀₋₁
    (λ _ _ → a₀₀₁) s₀₋₁ )
  (s₂q₁ : _)
  (c₂u₁ : Cube
    (λ z z' →  p₀₀₁ (~ z' ∨ z )) s₂q₁
    (λ _ z' → p₀₀₁ (~ z')) s'₋₀₁
    (λ _ _ → a₀₀₁) s₋₀₁ )
  {p₁₁₁ : a₀₀₀ ≡ a₁₁₁}
  (sp₀ : Square (sym p₁₀₀) p₋₁₁ refl p₁₁₁)
  (sp₁ : Square (sym p₀₁₀) p₁₋₁ refl p₁₁₁)
  (sp₂ : Square (sym p₀₀₁) p₁₁₋ refl p₁₁₁)
  (sp₀₁ : Square p₁₁₀ p₁₁₁ refl a₁₁₋)
  (sp₀₂ : Square p₁₀₁ p₁₁₁ refl a₁₋₁)
  (sp₁₂ : Square p₀₁₁ p₁₁₁ refl a₋₁₁)
  (s₀s₁ : Cube
      s₀q₂ sp₀
      (λ _ z' → p₁₀₀ (~ z')) s'ₓ₁₋
      (λ _ _ → a₁₀₀) sp₀₁)
  (s₀s₂ : Cube
      s₀q₁ sp₀
      (λ _ z' → p₁₀₀ (~ z')) s'ₓ₋₁
      (λ _ _ → a₁₀₀) sp₀₂)

  (s₁s₀ : Cube
      s₁q₂ sp₁
      (λ _ z' → p₀₁₀ (~ z')) s'₁ₓ₋
      (λ _ _ → a₀₁₀) sp₀₁)
  (s₁s₂ : Cube
      s₁q₀ sp₁
      (λ _ z' → p₀₁₀ (~ z')) s'₋ₓ₁
      (λ _ _ → a₀₁₀) sp₁₂)

  (s₂s₀ : Cube
      s₂q₁ sp₂
      (λ _ z' → p₀₀₁ (~ z')) s'₁₋ₓ
      (λ _ _ → a₀₀₁) sp₀₂)
  (s₂s₁ : Cube
      s₂q₀ sp₂
      (λ _ z' → p₀₀₁ (~ z')) s'₋₁ₓ
      (λ _ _ → a₀₀₁) sp₁₂)

  → Cube

       (λ i₁ i₂ → ◪mkSq (λ u v → s₀₁₋ (~ u) (~ v)) (λ u v → s₀₀₋ (~ u) (~ v))
                        (λ u v → s₀₋₁ (~ u) (~ v)) (λ u v → s₀₋₀ (~ u) (~ v)) (~ i₁) (~ i₂))

        (λ i₁ i₂ → ◪mkSq (λ u v → s'ₓ₁₋ (~ u) (~ v)) (λ u v → s'₁₀₋ (~ u) (~ v))
                         (λ u v → s'ₓ₋₁ (~ u) (~ v)) ((λ u v → s'₁₋₀ (~ u) (~ v))) (~ i₁) (~ i₂))

       (λ i₀ i₂ → ◪mkSq (λ u v → s₁₀₋ (~ u) (~ v)) ((λ u v → s₀₀₋ (~ u) (~ v)))
                        ((λ u v → s₋₀₁ (~ u) (~ v))) ((λ u v → s₋₀₀ (~ u) (~ v))) (~ i₀) (~ i₂))



     (λ i₀ i₂ → ◪mkSq (λ u v → s'₁ₓ₋ (~ u) (~ v)) (λ u v → s'₀₁₋ (~ u) (~ v))
                      (λ u v → s'₋ₓ₁ (~ u) (~ v)) (λ u v → s'₋₁₀ (~ u) (~ v)) (~ i₀) (~ i₂))
     (λ i₀ i₁ → ◪mkSq ((λ u v → s₁₋₀ (~ u) (~ v))) (((λ u v → s₀₋₀ (~ u) (~ v))))
                      ((λ u v → s₋₁₀ (~ u) (~ v))) (((λ u v → s₋₀₀ (~ u) (~ v)))) (~ i₀) (~ i₁))
     (λ i₀ i₁ → ◪mkSq (λ u v → s'₁₋ₓ (~ u) (~ v)) (λ u v → s'₀₋₁ (~ u) (~ v))
                      (λ u v → s'₋₁ₓ (~ u) (~ v)) (λ u v → s'₋₀₁ (~ u) (~ v)) (~ i₀) (~ i₁))
coh-cub {a₀₀₀ = a₀₀₀} {p₀₀₁ = p₀₀₁} {p₀₁₀ = p₀₁₀} {p₁₀₀ = p₁₀₀}  {s₋₀₀ = s₋₀₀}  {s₀₀₋ = s₀₀₋}   {s₀₋₀ = s₀₋₀}
   s₀q₁ c₀u₁ s₀q₂ c₀u₂
   s₁q₀ c₁u₀ s₁q₂ c₁u₂
   s₂q₀ c₂u₀ s₂q₁ c₂u₁
   sp₀ sp₁ sp₂
   sp₀₁ sp₀₂ sp₁₂
   s₀s₁ s₀s₂
   s₁s₀ s₁s₂
   s₂s₀ s₂s₁
    i₀ i₁ i₂ =
  hcomp
    (λ z → λ {
        (i₁ = i0)(i₂ = i0) → s₋₀₀ i₀ z
       ;(i₀ = i0)(i₂ = i0) → s₀₋₀ i₁ z
       ;(i₀ = i0)(i₁ = i0) → s₀₀₋ i₂ z
       ;(i₀ = i1) →
         hcomp
           (λ z' → λ {
                (i₁ = i0) → c₀u₁ i₂ z z'
               ;(i₂ = i0) → c₀u₂ i₁ z z'
               ;(i₁ = i1) → s₀s₁ i₂ z z'
               ;(i₂ = i1) → s₀s₂ i₁ z z'
               ;(z = i0) → p₁₀₀ (~ z')
            })
           (p₁₀₀ i1)
       ;(i₁ = i1) → hcomp
           (λ z' → λ {
                (i₀ = i0) → c₁u₀ i₂ z z'
               ;(i₂ = i0) → c₁u₂ i₀ z z'
               ;(i₀ = i1) → s₁s₀ i₂ z z'
               ;(i₂ = i1) → s₁s₂ i₀ z z'
               ;(z = i0) → p₀₁₀ (~ z')
            })
           (p₀₁₀ i1)
       ;(i₂ = i1) → hcomp
           (λ z' → λ {
                (i₀ = i0) → c₂u₀ i₁ z z'
               ;(i₁ = i0) → c₂u₁ i₀ z z'
               ;(i₀ = i1) → s₂s₀ i₁ z z'
               ;(i₁ = i1) → s₂s₁ i₀ z z'
               ;(z = i0) → p₀₀₁ (~ z')
            })
           (p₀₀₁ i1)
       })
    a₀₀₀
