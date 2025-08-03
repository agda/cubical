{-# OPTIONS --lossy-unification #-}

-- This file contains definition of CW complexes and skeleta.

module Cubical.CW.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.Relation.Nullary

open Sequence



private
  variable
    ℓ ℓ' : Level

--- CW complexes ---
-- Definition of (the skeleton) of an arbitrary CW complex
-- New def: X 0 is empty and C (suc n) is pushout
yieldsCWskel : (ℕ → Type ℓ) → Type ℓ
yieldsCWskel X =
  Σ[ f ∈ (ℕ → ℕ) ]
    Σ[ α ∈ ((n : ℕ) → (Fin (f n) × (S⁻ n)) → X n) ]
      ((¬ X zero) ×
      ((n : ℕ) → X (suc n) ≃ Pushout (α n) fst))

CWskel : (ℓ : Level) → Type (ℓ-suc ℓ)
CWskel ℓ = Σ[ X ∈ (ℕ → Type ℓ) ] (yieldsCWskel X)

module CWskel-fields (C : CWskel ℓ) where
  card = C .snd .fst
  A = Fin ∘ card
  α = C .snd .snd .fst
  e = C .snd .snd .snd .snd

  ℤ[A_] : (n : ℕ) → AbGroup ℓ-zero
  ℤ[A n ] = ℤ[Fin (snd C .fst n) ]

-- Technically, a CW complex should be the sequential colimit over the following maps
CW↪ : (T : CWskel ℓ) → (n : ℕ) → fst T n → fst T (suc n)
CW↪ (X , f , α , e₀ , e₊) n x = invEq (e₊ n) (inl x)

-- But if it stabilises, no need for colimits.
yieldsFinCWskel : (n : ℕ) (X : ℕ → Type ℓ) → Type ℓ
yieldsFinCWskel n X =
  Σ[ CWskel ∈ yieldsCWskel X ] ((k : ℕ) → isEquiv (CW↪ (X , CWskel) (k +ℕ n)))

-- ... which should give us finite CW complexes.
finCWskel : (ℓ : Level) → (n : ℕ) → Type (ℓ-suc ℓ)
finCWskel ℓ n = Σ[ C ∈ (ℕ → Type ℓ) ] (yieldsFinCWskel n C)

isFinCWskel : ∀ {ℓ} (C : CWskel ℓ) → Type ℓ
isFinCWskel C = Σ[ m ∈ ℕ ] ((k : ℕ) → isEquiv (CW↪ C (k +ℕ m)))

finCWskel→CWskel : (n : ℕ) → finCWskel ℓ n → CWskel ℓ
finCWskel→CWskel n C = fst C , fst (snd C)

realiseSeq : CWskel ℓ → Sequence ℓ
Sequence.obj (realiseSeq (C , p)) = C
Sequence.map (realiseSeq C) = CW↪ C _

realiseFinSeq : (m : ℕ) → CWskel ℓ → FinSequence m ℓ
realiseFinSeq m C = Sequence→FinSequence m (realiseSeq C)

-- realisation of CW complex from skeleton
realise : CWskel ℓ → Type ℓ
realise C = SeqColim (realiseSeq C)

-- Finally: definition of CW complexes
hasCWskel : (X : Type ℓ) → Type (ℓ-suc ℓ)
hasCWskel {ℓ = ℓ} X = Σ[ X' ∈ CWskel ℓ ] X ≃ realise X'

isCW : (X : Type ℓ) → Type (ℓ-suc ℓ)
isCW X = ∥ hasCWskel X ∥₁

CW : (ℓ : Level) → Type (ℓ-suc ℓ)
CW ℓ = Σ[ A ∈ Type ℓ ] (isCW A)

CWexplicit : (ℓ : Level) → Type (ℓ-suc ℓ)
CWexplicit ℓ = Σ[ A ∈ Type ℓ ] (hasCWskel A)

CWexplicit→CWskel : ∀ {ℓ} → CWexplicit ℓ → CWskel ℓ
CWexplicit→CWskel C = fst (snd C)

CWexplicit→CW : ∀ {ℓ} → CWexplicit ℓ → CW ℓ
CWexplicit→CW C = fst C , ∣ snd C ∣₁

-- Finite CW complexes
isFinIsCW : {X : Type ℓ} → hasCWskel X → Type ℓ
isFinIsCW X = Σ[ n ∈ ℕ ] (((k : ℕ) → isEquiv (CW↪ (X .fst) (k +ℕ n))))

hasFinCWskel : (X : Type ℓ) → Type (ℓ-suc ℓ)
hasFinCWskel {ℓ = ℓ} X =
  Σ[ m ∈ ℕ ] (Σ[ X' ∈ finCWskel ℓ m ] X ≃ realise (finCWskel→CWskel m X'))

isFinCW : (X : Type ℓ) → Type (ℓ-suc ℓ)
isFinCW {ℓ = ℓ} X = ∥ hasFinCWskel X ∥₁

finCW : (ℓ : Level) → Type (ℓ-suc ℓ)
finCW ℓ = Σ[ A ∈ Type ℓ ] (isFinCW A)

finCW∙ : (ℓ : Level) → Type (ℓ-suc ℓ)
finCW∙ ℓ = Σ[ A ∈ Pointed ℓ ] (isFinCW (fst A))

finCWexplicit : (ℓ : Level) → Type (ℓ-suc ℓ)
finCWexplicit ℓ = Σ[ A ∈ Type ℓ ] (hasFinCWskel A)

hasFinCWskel→hasCWskel : (X : Type ℓ) → hasFinCWskel X → hasCWskel X
hasFinCWskel→hasCWskel X (n , X' , str) = (finCWskel→CWskel n X') , str

finCW→CW : finCW ℓ → CW ℓ
finCW→CW (X , p) = X , PT.map (hasFinCWskel→hasCWskel X) p

-- Pointed complexes (with basepoint in X₀)
CWskel∙ : ∀ {ℓ} (X : CWskel ℓ) → fst X 1 → (n : ℕ) → fst X (suc n)
CWskel∙ X x zero = x
CWskel∙ X x (suc n) = CW↪ X (suc n) (CWskel∙ X x n)

CWskel∞∙ : ∀ {ℓ} (X : CWskel ℓ) → fst X 1 → (n : ℕ) → realise X
CWskel∞∙ X x₀ n = incl (CWskel∙ X x₀ n)

CWskel∞∙Id : ∀ {ℓ} (X : CWskel ℓ) (x₀ : fst X 1) (n : ℕ) → CWskel∞∙ X x₀ n ≡ incl x₀
CWskel∞∙Id X x₀ zero = refl
CWskel∞∙Id X x₀ (suc n) = sym (push (CWskel∙ X x₀ n)) ∙ CWskel∞∙Id X x₀ n

incl∙ : ∀ {ℓ} (X : CWskel ℓ) (x₀ : fst X 1) {n : ℕ}
  → (fst X (suc n) , CWskel∙ X x₀ n) →∙ (realise X , incl x₀)
fst (incl∙ X x₀ {n = n}) = incl
snd (incl∙ X x₀ {n = n}) = CWskel∞∙Id X x₀ n

-- morphisms
_→ᶜʷ_ : CW ℓ → CW ℓ' → Type (ℓ-max ℓ ℓ')
C →ᶜʷ D = fst C → fst D

--the cofibre of the inclusion of X n into X (suc n)
cofibCW : ∀ {ℓ} (n : ℕ) (C : CWskel ℓ) → Type ℓ
cofibCW n C = cofib (CW↪ C n)

--...is basically a sphere bouquet
cofibCW≃bouquet : ∀ {ℓ} (n : ℕ) (C : CWskel ℓ)
  → cofibCW n C ≃ SphereBouquet n (Fin (snd C .fst n))
cofibCW≃bouquet n C = Bouquet≃-gen n (snd C .fst n) (α n) e
  where
  s = Bouquet≃-gen
  α = C .snd .snd .fst
  e = C .snd .snd .snd .snd n

--sending X (suc n) into the cofibCW
to_cofibCW : (n : ℕ) (C : CWskel ℓ) → fst C (suc n) → cofibCW n C
to_cofibCW n C x = inr x

--the connecting map of the long exact sequence
δ-pre :  {A : Type ℓ} {B : Type ℓ'} (conn : A → B)
  → cofib conn → Susp A
δ-pre conn (inl x) = north
δ-pre conn (inr x) = south
δ-pre conn (push a i) = merid a i

δ : (n : ℕ) (C : CWskel ℓ) → cofibCW n C → Susp (fst C n)
δ n C = δ-pre (CW↪ C n)

-- send the stage n to the realization (the same as incl, but with explicit args and type)
CW↪∞ : (C : CWskel ℓ) → (n : ℕ) → fst C n → realise C
CW↪∞ C n x = incl x

CW↪Iterate : ∀ {ℓ} (T : CWskel ℓ) (n m : ℕ) → fst T n → fst T (m +ℕ n)
CW↪Iterate T n zero = idfun _
CW↪Iterate T n (suc m) x = CW↪ T (m +ℕ n) (CW↪Iterate T n m x)

finCW↑ : (n m : ℕ) → (m ≥ n) → finCWskel ℓ n → finCWskel ℓ m
fst (finCW↑ m n p C) = fst C
fst (snd (finCW↑ m n p C)) = snd C .fst
snd (snd (finCW↑ m n p C)) k =
  subst (λ r → isEquiv (CW↪ (fst C , snd C .fst) r))
        (sym (+-assoc k (fst p) m) ∙ cong (k +ℕ_) (snd p))
        (snd C .snd (k +ℕ fst p))
