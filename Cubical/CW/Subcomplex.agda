{-# OPTIONS --safe --lossy-unification #-}

module Cubical.CW.Subcomplex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.ChainComplex
open import Cubical.CW.Approximation

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.ChainComplex

private
  variable
    ℓ ℓ' ℓ'' : Level

-- finite subcomplex of a cw complex
module _ (C : CWskel ℓ) where
  subComplexFam : (n : ℕ) (m : ℕ) → Type ℓ
  subComplexFam n m with (m ≟ᵗ n)
  ... | lt x = fst C m
  ... | eq x = fst C m
  ... | gt x = fst C n

  subComplexCard : (n : ℕ) → ℕ → ℕ
  subComplexCard n m with (m ≟ᵗ n)
  ... | lt x = snd C .fst m
  ... | eq x = 0
  ... | gt x = 0

  subComplexα : (n m : ℕ) → Fin (subComplexCard n m) × S⁻ m → subComplexFam n m
  subComplexα n m with (m ≟ᵗ n)
  ... | lt x = snd C .snd .fst m
  ... | eq x = λ x → ⊥.rec (¬Fin0 (fst x))
  ... | gt x = λ x → ⊥.rec (¬Fin0 (fst x))

  subComplex₀-empty : (n : ℕ) → ¬ subComplexFam n zero
  subComplex₀-empty n with (zero ≟ᵗ n)
  ... | lt x = CW₀-empty C
  ... | eq x = CW₀-empty C

  subComplexFam≃Pushout : (n m : ℕ)
    → subComplexFam n (suc m) ≃ Pushout (subComplexα n m) fst
  subComplexFam≃Pushout n m with (m ≟ᵗ n) | ((suc m) ≟ᵗ n)
  ... | lt x | lt x₁ = snd C .snd .snd .snd m
  ... | lt x | eq x₁ = snd C .snd .snd .snd m
  ... | lt x | gt x₁ = ⊥.rec (¬squeeze (x , x₁))
  ... | eq x | lt x₁ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x (<ᵗ-trans <ᵗsucm x₁)))
  ... | eq x | eq x₁ = ⊥.rec (¬m<ᵗm (subst (m <ᵗ_) (x₁ ∙ sym x) <ᵗsucm))
  ... | eq x | gt x₁ =
    compEquiv (pathToEquiv (λ i → fst C (x (~ i))))
              (isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0))
  ... | gt x | lt x₁ =
    ⊥.rec (¬squeeze (x₁ , <ᵗ-trans x (<ᵗ-trans <ᵗsucm <ᵗsucm)))
  ... | gt x | eq x₁ =
    ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) x₁ (<ᵗ-trans x <ᵗsucm)))
  ... | gt x | gt x₁ = isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0)

  subComplexYieldsCWskel : (n : ℕ) → yieldsCWskel (subComplexFam n)
  fst (subComplexYieldsCWskel n) = subComplexCard n
  fst (snd (subComplexYieldsCWskel n)) = subComplexα n
  fst (snd (snd (subComplexYieldsCWskel n))) = subComplex₀-empty n
  snd (snd (snd (subComplexYieldsCWskel n))) m = subComplexFam≃Pushout n m

  subComplex : (n : ℕ) → CWskel ℓ
  fst (subComplex n) = subComplexFam n
  snd (subComplex n) = subComplexYieldsCWskel n

  -- as a finite CWskel
  subComplexFin : (m : ℕ) (n : Fin (suc m))
    → isEquiv (CW↪ (subComplexFam (fst n) , subComplexYieldsCWskel (fst n)) m)
  subComplexFin m (n , r) with (m ≟ᵗ n) | (suc m ≟ᵗ n)
  ... | lt x | p = ⊥.rec (¬squeeze (x , r))
  ... | eq x | lt x₁ =
    ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x (<ᵗ-trans <ᵗsucm x₁)))
  ... | eq x | eq x₁ = ⊥.rec (¬m<ᵗm (subst (m <ᵗ_) (x₁ ∙ sym x) <ᵗsucm))
  ... | eq x | gt x₁ =
    subst isEquiv (funExt λ x → cong (help .fst)
          (retEq (isoToEquiv (PushoutEmptyFam {A = Fin 0 × fst C m}
                  (λ x₃ → ¬Fin0 (fst x₃)) ¬Fin0 {f = snd} {g = fst})) x))
                  (help .snd)
      where
      help : fst C m ≃ fst C n
      help = invEquiv (pathToEquiv (λ i → fst C (x (~ i))))
  ... | gt x | lt x₁ =
    ⊥.rec (¬squeeze (x₁ , <ᵗ-trans x (<ᵗ-trans <ᵗsucm <ᵗsucm)))
  ... | gt x | eq x₁ =
    ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) x₁ r))
  ... | gt x | gt x₁ =
    subst isEquiv (funExt (retEq (isoToEquiv (PushoutEmptyFam {A = Fin 0 × fst C n}
                          (λ x₃ → ¬Fin0 (fst x₃)) ¬Fin0 {f = snd} {g = fst}))))
                  (idEquiv _ .snd)

  subComplexYieldsFinCWskel : (n : ℕ) → yieldsFinCWskel n (subComplexFam n)
  fst (subComplexYieldsFinCWskel n) = subComplexYieldsCWskel n
  snd (subComplexYieldsFinCWskel n) k = subComplexFin (k + n) (n , <ᵗ-+)

  finSubComplex : (n : ℕ) → finCWskel ℓ n
  fst (finSubComplex n) = subComplexFam n
  snd (finSubComplex n) = subComplexYieldsFinCWskel n

  complex≃subcomplex : (n : ℕ) (m : Fin (suc n))
    → fst C (fst m) ≃ subComplex n .fst (fst m)
  complex≃subcomplex n (m , p) with (m ≟ᵗ n)
  ... | lt x = idEquiv _
  ... | eq x = idEquiv _
  ... | gt x = ⊥.rec (¬squeeze (x , p))

realiseSubComplex : (n : ℕ) (C : CWskel ℓ) → Iso (fst C n) (realise (subComplex C n))
realiseSubComplex n C =
  compIso (equivToIso (complex≃subcomplex C n flast))
          (realiseFin n (finSubComplex C n))

-- Goal: Show that a cell complex C and its subcomplex Cₙ share
-- homology in low enough dimensions
module _ (C : CWskel ℓ) where
  ChainSubComplex : (n : ℕ) → snd C .fst n ≡ snd (subComplex C (suc n)) .fst n
  ChainSubComplex n with (n ≟ᵗ suc n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) (sym x) <ᵗsucm))
  ... | gt x = ⊥.rec (¬-suc-n<ᵗn x)

  ≤ChainSubComplex : (n : ℕ) (m : Fin n)
    → snd C .fst (fst m) ≡ snd (subComplex C n) .fst (fst m)
  ≤ChainSubComplex n (m , p) with (m ≟ᵗ n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x p))
  ... | gt x = ⊥.rec (¬m<ᵗm (<ᵗ-trans x p))

subChainIso : (C : CWskel ℓ) (n : ℕ) (m : Fin n)
  → AbGroupIso (CWskel-fields.ℤ[A_] C (fst m))
                (CWskel-fields.ℤ[A_] (subComplex C n) (fst m))
subChainIso C n (m , p) with (m ≟ᵗ n)
... | lt x = idGroupIso
... | eq x = ⊥.rec (¬m<ᵗm (subst (m <ᵗ_) (sym x) p))
... | gt x = ⊥.rec (¬m<ᵗm (<ᵗ-trans x p))

-- main result
subComplexHomology : (C : CWskel ℓ) (n m : ℕ) (p : suc (suc m) <ᵗ n)
  → GroupIso (Hˢᵏᵉˡ C m) (Hˢᵏᵉˡ (subComplex C n) m)
subComplexHomology C n m p =
  homologyIso m _ _
    (subChainIso C n (suc (suc m) , p))
    (subChainIso C n (suc m , <ᵗ-trans <ᵗsucm p))
    (subChainIso C n (m , <ᵗ-trans <ᵗsucm (<ᵗ-trans <ᵗsucm p)))
    lem₁
    lem₂
  where
  lem₁ : {q : _} {r : _}
    → Iso.fun (subChainIso C n (m , q) .fst) ∘ ∂ C m .fst
    ≡ ∂ (subComplex C n) m .fst
     ∘ Iso.fun (subChainIso C n (suc m , r) .fst)
  lem₁ {q} {r} with (m ≟ᵗ n) | (suc m ≟ᵗ n) | (suc (suc m) ≟ᵗ n)
  ... | lt x | lt x₁ | lt x₂ = refl
  ... | lt x | lt x₁ | eq x₂ = refl
  ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze (x₁ , x₂))
  ... | lt x | eq x₁ | t = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x₁ r))
  ... | lt x | gt x₁ | t = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ r))
  ... | eq x | s | t = ⊥.rec (¬-suc-n<ᵗn (subst (suc m <ᵗ_) (sym x) r))
  ... | gt x | s | t = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans r x))

  lem₂ : {q : suc m <ᵗ n} {r : (suc (suc m)) <ᵗ n}
    → Iso.fun (subChainIso C n (suc m , q) .fst)
     ∘ ∂ C (suc m) .fst
     ≡ ∂ (subComplex C n) (suc m) .fst
     ∘ Iso.fun (subChainIso C n (suc (suc m) , r) .fst)
  lem₂ {q} with (suc m ≟ᵗ n) | (suc (suc m) ≟ᵗ n) | (suc (suc (suc m)) ≟ᵗ n)
  ... | lt x | lt x₁ | lt x₂ = refl
  ... | lt x | lt x₁ | eq x₂ = refl
  ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze (x₁ , x₂))
  ... | lt x | eq x₁ | t = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x₁ p))
  ... | lt x | gt x₁ | t = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ p))
  ... | eq x | s | t = ⊥.rec (¬m<ᵗm (subst (suc m <ᵗ_) (sym x) q))
  ... | gt x | s | t = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans p x))
