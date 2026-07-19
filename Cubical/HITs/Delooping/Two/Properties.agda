
module Cubical.HITs.Delooping.Two.Properties where

open import Cubical.Functions.Involution

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Unit

open import Cubical.HITs.Delooping.Two.Base
open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ : Level

module Embed where
  isPropDepIsSet : isOfHLevelDep {ℓ' = ℓ} 1 isSet
  isPropDepIsSet = isOfHLevel→isOfHLevelDep 1 (λ _ → isPropIsSet)

  notSet : PathP (λ i → isSet (notEq i)) isSetBool isSetBool
  notSet = isPropDepIsSet isSetBool isSetBool notEq

  notNot² : Square notEq refl refl notEq
  notNot² = involPath² notnot

  notNotSet
    : SquareP (λ i j → isSet (notNot² i j)) notSet refl refl notSet
  notNotSet = isPropDep→isSetDep'
                isPropDepIsSet
                (involPath² notnot)
                notSet refl refl notSet

  Code : Bℤ₂ → hSet ℓ-zero
  Code = Elim.rec
    (Bool , isSetBool)
    (λ i → notEq i , notSet i)
    (λ i j → λ where
      .fst → notNot² i j
      .snd → notNotSet i j)
    (isOfHLevelTypeOfHLevel 2)

  El : Bℤ₂ → Type₀
  El b = Code b .fst

module BINARY where
  open import Cubical.Data.FinSet.Binary.Large

  sem : Bℤ₂ → Binary _
  sem = Elim.rec Base Loop Loop² isGroupoidBinary

  loop? : Bool → base ≡ base
  loop? false = refl
  loop?  true = loop

  Loop²-coh : (a b c : Bool) → Type₀
  Loop²-coh false false false = Unit
  Loop²-coh false  true  true = Unit
  Loop²-coh  true false  true = Unit
  Loop²-coh  true  true false = Unit
  Loop²-coh     _     _     _ = ⊥

  rf : Bool ≡ Bool → Bool
  rf P = transport P false

  Loop²-coh-lemma₀
    : ∀(p q r : Bool)
    → r ⊕ p ≡ q
    → Loop²-coh p q r
  Loop²-coh-lemma₀ false false false sq = _
  Loop²-coh-lemma₀ false  true  true sq = _
  Loop²-coh-lemma₀  true false  true sq = _
  Loop²-coh-lemma₀  true  true false sq = _
  Loop²-coh-lemma₀ false  true false = false≢true
  Loop²-coh-lemma₀ false false  true = true≢false
  Loop²-coh-lemma₀  true false false = true≢false
  Loop²-coh-lemma₀  true  true  true = false≢true

  Loop²-coh-lemma
    : ∀(P Q R : Bool ≡ Bool)
    → Square P Q refl R
    → Loop²-coh (rf P) (rf Q) (rf R)
  Loop²-coh-lemma P Q R sq = Loop²-coh-lemma₀ p q r eqn
    where
    p = rf P
    q = rf Q
    r = rf R

    open BoolReflection

    cmp : P ∙ R ≡ Q
    cmp i j
      = hcomp (λ k → λ where
            (i = i0) → compPath-filler P R k j
            (i = i1) → Q j
            (j = i0) → Bool
            (j = i1) → R (i ∨ k))
          (sq i j)

    rcmp : ⊕-Path (r ⊕ p) ≡ ⊕-Path q
    rcmp = ⊕-Path (r ⊕ p)
             ≡[ i ]⟨ ⊕-comp p r (~ i) ⟩
           ⊕-Path p ∙ ⊕-Path r
             ≡[ i ]⟨ ⊕-complete P (~ i) ∙ ⊕-complete R (~ i) ⟩
           P ∙ R
             ≡⟨ cmp ⟩
           Q
             ≡⟨ ⊕-complete Q ⟩
           ⊕-Path q ∎
    open Iso
    eqn : r ⊕ p ≡ q
    eqn = transport (λ i →
              reflectIso .leftInv (r ⊕ p) i ≡ reflectIso .leftInv q i)
            (cong (reflectIso .inv) rcmp)

  loop²?
    : ∀ p q r → Loop²-coh p q r
    → Square (loop? p) (loop? q) refl (loop? r)
  loop²? false false false _ = refl
  loop²? false  true  true _ = λ i j → loop (i ∧ j)
  loop²?  true false  true _ = loop²
  loop²?  true  true false _ = refl

  module _ (B : Type₀) where
    based : (P : Bool ≃ B) → Bℤ₂
    based _ = base

    pull₀ : (P Q : Bool ≃ B) → Bool ≡ Bool
    pull₀ P Q i
      = hcomp (λ k → λ where
            (i = i0) → ua P (~ k)
            (i = i1) → ua Q (~ k))
          B

    pull₁ : (P Q : Bool ≃ B) → Square (ua P) (ua Q) (pull₀ P Q) refl
    pull₁ P Q i j
      = hcomp (λ k → λ where
            (i = i0) → ua P (~ k ∨ j)
            (i = i1) → ua Q (~ k ∨ j)
            (j = i1) → B)
          B

    pull₂
      : (P Q R : Bool ≃ B)
      → Square (pull₀ P Q) (pull₀ P R) refl (pull₀ Q R)
    pull₂ P Q R i j
      = hcomp (λ k → λ where
            (j = i0) → ua P (~ k)
            (i = i0) (j = i1) → ua Q (~ k)
            (i = i1) (j = i1) → ua R (~ k))
          B

    pull₃
      : (P Q R : Bool ≃ B)
      → Cube (pull₁ P Q) (pull₁ P R)
            (λ _ → ua P)  (pull₁ Q R)
            (pull₂ P Q R) (λ _ _ → B)
    pull₃ P Q R i j k
      = hcomp (λ τ → λ where
            (j = i0) → ua P (~ τ ∨ k)
            (i = i0) (j = i1) → ua Q (~ τ ∨ k)
            (i = i1) (j = i1) → ua R (~ τ ∨ k)
            (k = i1) → B)
          B

    looped : (P Q : Bool ≃ B) → based P ≡ based Q
    looped P Q = loop? b
      where
      b : Bool
      b = rf (pull₀ P Q)

    looped²
      : (P Q R : Bool ≃ B)
      → Square (looped P Q) (looped P R) refl (looped Q R)
    looped² P Q R = loop²? pq pr qr pqr
      where
      pq = rf (pull₀ P Q)
      pr = rf (pull₀ P R)
      qr = rf (pull₀ Q R)

      pqr : Loop²-coh pq pr qr
      pqr = Loop²-coh-lemma (pull₀ P Q) (pull₀ P R) (pull₀ Q R) (pull₂ P Q R)

  syn : Binary _ → Bℤ₂
  syn (B , tP) = rec→Gpd trunc (based B) 3k tP
    where
    open 3-Constant
    3k : 3-Constant (based B)
    3k .link = looped B
    3k .coh₁ = looped² B
