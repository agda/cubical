{-# OPTIONS --lossy-unification #-}

{-
This file contains a definition of a notion of (strict)
subcomplexes of a CW complex. Here, a subomplex of a complex
C = colim ( C₀ → C₁ → ...)
is simply the complex
C⁽ⁿ⁾ := colim (C₀ → ... → Cₙ = Cₙ = ...)

This file contains.
1. Definition of above
2. A `strictification' of finite CW complexes in terms of above
3. An elmination principle for finite CW complexes
4. A proof that C and C⁽ⁿ⁾ has the same homolog in appropriate dimensions.
-}

module Cubical.CW.Subcomplex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.Data.Nat
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.Map

open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' : Level

-- finite subcomplex C⁽ⁿ⁾ of a cw complex C.
module SubComplexGen (C : CWskel ℓ) (n : ℕ) where
  subComplexFam : (m : ℕ) → Trichotomyᵗ m n → Type ℓ
  subComplexFam m (lt x) = fst C m
  subComplexFam m (eq x) = fst C m
  subComplexFam m (gt x) = fst C n

  subComplexCard : (m : ℕ) → Trichotomyᵗ m n → ℕ
  subComplexCard m (lt x) = snd C .fst m
  subComplexCard m (eq x) = 0
  subComplexCard m (gt x) = 0

  -- Attaching maps
  subComplexα : (m : ℕ) (p : Trichotomyᵗ m n)
    → Fin (subComplexCard m p) × S⁻ m → subComplexFam m p
  subComplexα m (lt x) = snd C .snd .fst m

  subComplex₀-empty : (p : Trichotomyᵗ zero n) → ¬ subComplexFam zero p
  subComplex₀-empty (lt x₁) x = CW₀-empty C x
  subComplex₀-empty (eq x₁) x = CW₀-empty C x

  -- Resulting complex has CW structure
  subComplexFam≃Pushout : (m : ℕ)
    (p : Trichotomyᵗ m n) (q : Trichotomyᵗ (suc m) n)
    → subComplexFam (suc m) q ≃ Pushout (subComplexα m p) fst
  subComplexFam≃Pushout m (lt x) (lt y) = snd C .snd .snd .snd m
  subComplexFam≃Pushout m (lt x) (eq y) = snd C .snd .snd .snd m
  subComplexFam≃Pushout m (lt x) (gt y) = ⊥.rec (¬squeeze {m} {n} (x , y))
  subComplexFam≃Pushout m (eq x) (lt y) =
    ⊥.rec (¬m<ᵗm {n} (subst (_<ᵗ n) x (<ᵗ-trans {m} {suc m} {n} (<ᵗsucm {m}) y)))
  subComplexFam≃Pushout m (eq x) (eq y) =
    ⊥.rec (¬m<ᵗm {m} (subst (m <ᵗ_) (y ∙ sym x) (<ᵗsucm {m})))
  subComplexFam≃Pushout m (eq x) (gt y) =
    compEquiv (pathToEquiv (λ i → fst C (x (~ i))))
              (isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0))
  subComplexFam≃Pushout m (gt x) (lt y) =
    ⊥.rec (¬squeeze {suc m} {n} (y
      , <ᵗ-trans {n} {m} {suc (suc m)} x
         (<ᵗ-trans {m} {suc m} {suc (suc m)} (<ᵗsucm {m}) (<ᵗsucm {suc m}))))
  subComplexFam≃Pushout m (gt x) (eq y) =
    ⊥.rec (¬m<ᵗm {n} (subst (n <ᵗ_) y (<ᵗ-trans {n} {m} {suc m} x (<ᵗsucm {m}))))
  subComplexFam≃Pushout m (gt x) (gt y) =
    isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0)

  subComplexCW↪Gen : (m : ℕ) (p : Trichotomyᵗ m n) (q : Trichotomyᵗ (suc m) n)
    → subComplexFam m p → subComplexFam (suc m) q
  subComplexCW↪Gen m p q x = invEq (subComplexFam≃Pushout m p q) (inl x)

  subComplexFinEquiv' : (m : ℕ) (ineq : n <ᵗ suc m) (p : _)
    → isEquiv {B = Pushout (subComplexα m p) fst} inl
  subComplexFinEquiv' m ineq (lt x) = ⊥.rec (¬squeeze {m} {n} (x , ineq))
  subComplexFinEquiv' m ineq (eq x) =
    isoToIsEquiv (PushoutEmptyFam (¬Fin0 ∘ fst) ¬Fin0)
  subComplexFinEquiv' m ineq (gt x) =
    isoToIsEquiv (PushoutEmptyFam (¬Fin0 ∘ fst) ¬Fin0)

CW↑Gen : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ)
  → Trichotomyᵗ n (suc m) → m <ᵗ n → fst C m → fst C n
CW↑Gen C zero (suc n) s p q = ⊥.rec (C .snd .snd .snd .fst q)
CW↑Gen C (suc m) (suc n) (lt y) p x = ⊥.rec (¬squeeze {m} {n} (p , y))
CW↑Gen C (suc m) (suc n) (eq y) p x =
  CW↪ C n (subst (fst C) (sym (cong predℕ y)) x)
CW↑Gen C (suc m) (suc n) (gt y) p x =
  CW↪ C n (CW↑Gen C (suc m) n (n ≟ᵗ suc (suc m)) y x)

CW↑Gen≡ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ)
     (p : Trichotomyᵗ n (suc m)) (q : m <ᵗ n) (x : fst C m)
  → Path (realise C) (incl x) (incl {n = n} (CW↑Gen C m n p q x))
CW↑Gen≡ C zero (suc n) p q x = ⊥.rec (C .snd .snd .snd .fst x)
CW↑Gen≡ C (suc m) (suc n) (lt x₁) q x = ⊥.rec (¬squeeze {m} {n} (q , x₁))
CW↑Gen≡ C (suc m) (suc n) (eq x₁) q x = help _ (cong predℕ (sym x₁))
  where
  help : (n : ℕ) (p : suc m ≡ n)
    → Path (realise C) (incl x) (incl (CW↪ C n (subst (fst C) p x)))
  help = J> push x
         ∙ λ i → incl {n = suc (suc m)} (CW↪ C (suc m) (transportRefl x (~ i)))
CW↑Gen≡ C (suc m) (suc n) (gt y) q x =
    CW↑Gen≡ C (suc m) n (n ≟ᵗ suc (suc m)) y x
  ∙ push (CW↑Gen C (suc m) n (n ≟ᵗ suc (suc m)) y x)

module subComplexMapGen {ℓ : Level} (C : CWskel ℓ) where
  subComplex→map' : (m n : ℕ) (p : Trichotomyᵗ n m)
    → SubComplexGen.subComplexFam C m n p → fst C n
  subComplex→map' m n (lt x) = idfun _
  subComplex→map' m n (eq x) = idfun _
  subComplex→map' m n (gt x) = CW↑Gen C m n (n ≟ᵗ suc m) x

  subComplex←map' : (m n : ℕ) (ineq : n <ᵗ suc m) (p : Trichotomyᵗ n m)
    → fst C n → SubComplexGen.subComplexFam C m n p
  subComplex←map' m n ineq (lt x) = idfun _
  subComplex←map' m n ineq (eq x) = idfun _
  subComplex←map' m n ineq (gt x) = ⊥.rec (¬squeeze {m} {n} (x , ineq))

  private
    retr-sect : (m n : ℕ) (ineq : n <ᵗ suc m) (p : Trichotomyᵗ n m)
      → retract (subComplex→map' m n p) (subComplex←map' m n ineq p)
       × section (subComplex→map' m n p) (subComplex←map' m n ineq p)
    retr-sect m n ineq (lt x) = (λ x → refl) , λ x → refl
    retr-sect m n ineq (eq x) = (λ x → refl) , (λ x → refl)
    retr-sect m n ineq (gt x) = ⊥.rec (¬squeeze {m} {n} (x , ineq))

  subComplexIso : (m n : ℕ) (ineq : n <ᵗ suc m) (p : Trichotomyᵗ n m)
    → Iso (fst C n) (SubComplexGen.subComplexFam C m n p)
  Iso.fun (subComplexIso m n ineq p) = subComplex←map' m n ineq p
  Iso.inv (subComplexIso m n ineq p) = subComplex→map' m n p
  Iso.rightInv (subComplexIso m n ineq p) = retr-sect m n ineq p .fst
  Iso.leftInv (subComplexIso m n ineq p) = retr-sect m n ineq p .snd

subComplex→map : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ)
  → SubComplexGen.subComplexFam C m n (n ≟ᵗ m) → fst C n
subComplex→map C m n = subComplexMapGen.subComplex→map' C m n (n ≟ᵗ m)


subComplex→Equiv : ∀ {ℓ} (C : CWskel ℓ) (n m : ℕ) (p : m <ᵗ suc n)
  → SubComplexGen.subComplexFam C n m (m ≟ᵗ n) ≃ fst C m
subComplex→Equiv C n m p =
  isoToEquiv (invIso (subComplexMapGen.subComplexIso C n m p (m ≟ᵗ n)))

complex≃subcomplex' : (C : CWskel ℓ) (n m : ℕ) (ineq : m <ᵗ suc n) (p : _)
  → fst C m ≃ SubComplexGen.subComplexFam C n m p
complex≃subcomplex' C n m ineq p =
  isoToEquiv (subComplexMapGen.subComplexIso C n m ineq p)

module _ (C : CWskel ℓ) where
  module _ (n : ℕ) where
    module G = SubComplexGen C n
    subComplexFam : ℕ → Type ℓ
    subComplexFam m = G.subComplexFam m (m ≟ᵗ n)

    subComplexCard : (m : ℕ) → ℕ
    subComplexCard m = G.subComplexCard m (m ≟ᵗ n)

    -- Attaching maps
    subComplexα : (m : ℕ)
      → Fin (subComplexCard m) × S⁻ m → subComplexFam m
    subComplexα m = G.subComplexα m (m ≟ᵗ n)

    subComplex₀-empty : ¬ subComplexFam zero
    subComplex₀-empty = G.subComplex₀-empty (0 ≟ᵗ n)

    -- Resulting complex has CW structure
    subComplexFam≃Pushout : (m : ℕ)
      → subComplexFam (suc m) ≃ Pushout (subComplexα m) fst
    subComplexFam≃Pushout m =
      G.subComplexFam≃Pushout m (m ≟ᵗ n) (suc m ≟ᵗ n)

  -- packaging it all together
  subComplexYieldsCWskel : (n : ℕ) → yieldsCWskel (subComplexFam n)
  fst (subComplexYieldsCWskel n) m = subComplexCard n m
  fst (snd (subComplexYieldsCWskel n)) m = subComplexα n m
  fst (snd (snd (subComplexYieldsCWskel n))) = subComplex₀-empty n
  snd (snd (snd (subComplexYieldsCWskel n))) m = subComplexFam≃Pushout n m

  -- main definition
  subComplex : (n : ℕ) → CWskel ℓ
  fst (subComplex n) m = subComplexFam n m
  snd (subComplex n) = subComplexYieldsCWskel n

  subComplexFin : (m : ℕ) (n : Fin (suc m))
    → isEquiv (CW↪ (subComplex (fst n)) m)
  subComplexFin m n =
    compEquiv
      (_ , SubComplexGen.subComplexFinEquiv' C (fst n) m (snd n) (m ≟ᵗ fst n))
      (invEquiv (subComplexFam≃Pushout (fst n) m)) .snd

  subComplexYieldsFinCWskel : (n : ℕ) → yieldsFinCWskel n (subComplexFam n)
  fst (subComplexYieldsFinCWskel n) = subComplexYieldsCWskel n
  snd (subComplexYieldsFinCWskel n) k = subComplexFin (k + n) (n , <ᵗ-+ {n} {k})

  finSubComplex : (n : ℕ) → finCWskel ℓ n
  fst (finSubComplex n) m = subComplexFam n m
  snd (finSubComplex n) = subComplexYieldsFinCWskel n

-- C⁽ⁿ⁾ₙ ≃ Cₙ
realiseSubComplex : (n : ℕ) (C : CWskel ℓ)
  → Iso (fst C n) (realise (subComplex C n))
realiseSubComplex n C =
  compIso (equivToIso (complex≃subcomplex' C n n (<ᵗsucm {n}) (n ≟ᵗ n)))
          (realiseFin n (finSubComplex C n))

subCWExplicit : ∀ {ℓ} (n : ℕ) → CWexplicit ℓ → CWexplicit ℓ
fst (subCWExplicit n (X , Xsk , e)) = Xsk .fst n
fst (snd (subCWExplicit n (X , Xsk , e))) = subComplex Xsk n
snd (snd (subCWExplicit n (X , Xsk , e))) =
  isoToEquiv (realiseSubComplex n Xsk)

subCW : ∀ {ℓ} (n : ℕ) → CWexplicit ℓ → CW ℓ
subCW n X = CWexplicit→CW (subCWExplicit n X)

-- Strictifying finCWskel
niceFinCWskel : ∀ {ℓ} (n : ℕ) → finCWskel ℓ n → finCWskel ℓ n
fst (niceFinCWskel n (A , AC , fin)) = finSubComplex (A , AC) n .fst
snd (niceFinCWskel n (A , AC , fin)) = finSubComplex (A , AC) n .snd

makeNiceFinCWskel : ∀ {ℓ} {A : Type ℓ} → hasFinCWskel A → hasFinCWskel A
makeNiceFinCWskel {A = A} (dim , cwsk , e) = better
  where
  improved = finSubComplex (cwsk .fst , cwsk .snd .fst) dim

  better : hasFinCWskel A
  fst better = dim
  fst (snd better) = improved
  snd (snd better) =
    compEquiv
      (compEquiv e (invEquiv (isoToEquiv (realiseFin dim cwsk))))
      (isoToEquiv (realiseSubComplex dim (cwsk .fst , cwsk .snd .fst)))


makeNiceFinCW : ∀ {ℓ} → finCW ℓ → finCW ℓ
fst (makeNiceFinCW C) = fst C
snd (makeNiceFinCW C) =
  PT.map makeNiceFinCWskel (snd C)

makeNiceFinCW≡ : ∀ {ℓ} (C : finCW ℓ) → makeNiceFinCW C ≡ C
makeNiceFinCW≡ C = Σ≡Prop (λ _ → squash₁) refl

-- Elimination principles
makeNiceFinCWElim : ∀ {ℓ ℓ'} {A : finCW ℓ → Type ℓ'}
  → ((C : finCW ℓ) → A (makeNiceFinCW C))
  → (C : _) → A C
makeNiceFinCWElim {A = A} ind C = subst A (makeNiceFinCW≡ C) (ind C)

makeNiceFinCWElim' : ∀ {ℓ ℓ'} {C : Type ℓ} {A : isFinCW C → Type ℓ'}
  → ((x : _) → isProp (A x))
  → ((cw : hasFinCWskel C) → A (makeNiceFinCW (C , ∣ cw ∣₁) .snd))
  → (cw : _) → A cw
makeNiceFinCWElim' {A = A} pr ind =
  PT.elim pr λ cw → subst A (squash₁ _ _) (ind cw)

-- Pointed subcomplexes
CWskel∙Gen : ∀ {ℓ} (X : CWskel ℓ) → fst X 1 → (n m : ℕ) (p : _)
  → G.subComplexFam X (suc m) (suc n) p
CWskel∙Gen X x₀ n m (lt x) = CWskel∙ X x₀ n
CWskel∙Gen X x₀ n m (eq x) = CWskel∙ X x₀ n
CWskel∙Gen X x₀ n m (gt x) = CWskel∙ X x₀ m

CWskel∙Gen≡CWskel∙ : ∀ {ℓ} (X : CWskel ℓ) (x : fst X 1) → (n m : ℕ)
  → CWskel∙Gen X x n (suc m) (suc n ≟ᵗ suc (suc m))
   ≡ CWskel∙ (subComplex X (suc (suc m))) x n
CWskel∙Gen≡CWskel∙ X x zero m = refl
CWskel∙Gen≡CWskel∙ X x (suc n) m =
  lem (suc (suc n) ≟ᵗ suc (suc m)) (suc n ≟ᵗ suc (suc m))
  ∙ cong (CW↪ (subComplex X (suc (suc m))) (suc n))
         (CWskel∙Gen≡CWskel∙ X x n m)
  where
  lem : (p : _) (q : _) → CWskel∙Gen X x (suc n) (suc m) p
      ≡ invEq (G.subComplexFam≃Pushout X (suc (suc m)) (suc n) q p)
         (inl (CWskel∙Gen X x n (suc m) q))
  lem (lt x) (lt y) = refl
  lem (lt x) (eq y) =
    ⊥.rec (¬m<ᵗm {suc (suc m)}
           (subst (_<ᵗ suc (suc m)) y
             (<ᵗ-trans {n} {suc n} {suc m} (<ᵗsucm {n}) x)))
  lem (lt x) (gt y) =
    ⊥.rec (¬squeeze {n} {m} (x
          , <ᵗ-trans {suc m} {n} {suc (suc n)} y
             (<ᵗ-trans {n} {suc n} {suc (suc n)}
              (<ᵗsucm {n}) (<ᵗsucm {suc n}))))
  lem (eq x) (lt y) = refl
  lem (eq x) (eq y) =
    ⊥.rec (¬m<ᵗm {suc (suc n)}
             (subst (_<ᵗ suc (suc n)) (y ∙ sym x) (<ᵗsucm {n})))
  lem (eq x) (gt y) =
    ⊥.rec (¬-suc-n<ᵗn {suc (suc n)} (subst (_<ᵗ suc n) (sym x) y))
  lem (gt x) (lt y) =
    ⊥.rec (¬squeeze {n} {suc m} (y , x))
  lem (gt y) (eq z) =
    ((λ j → transp (λ i → fst X (suc (predℕ (z (~ j ∨ i))))) (~ j)
                (CWskel∙ X x (predℕ (z (~ j))))))
    ∙ cong (λ p → subst (fst X) p (CWskel∙ X x n)) (isSetℕ _ _ _ z)
    ∙ sym (transportRefl _)
  lem (gt x) (gt y) = refl

CWskel∙GenSubComplex : ∀ {ℓ} (X : CWskel ℓ) (x₀ : fst X 1) {n m : ℕ}
  (t : m <ᵗ suc (suc n)) (p : _)
  → CWskel∙Gen X x₀ m (suc n) p
  ≡ subComplexMapGen.subComplex←map' X (suc (suc n)) (suc m) t p
     (CWskel∙ X x₀ m)
CWskel∙GenSubComplex X x₌ t (lt x) = refl
CWskel∙GenSubComplex X x₌ t (eq x) = refl
CWskel∙GenSubComplex X x₌ {n} {m} t (gt x) =
  ⊥.rec (¬squeeze {suc n} {m} (x , t))

CWskel∙SubComplex : ∀ {ℓ} (X : CWskel ℓ) (x₀ : fst X 1) {n m : ℕ}
  (t : m <ᵗ suc (suc n))
  → CWskel∙ (subComplex X (suc (suc n))) x₀ m
   ≡ fst (complex≃subcomplex' X (suc (suc n)) (suc m) t
           (suc m ≟ᵗ suc (suc n))) (CWskel∙ X x₀ m)
CWskel∙SubComplex X x₀ {n} {m} t =
  sym (CWskel∙Gen≡CWskel∙ X x₀ m n)
  ∙ CWskel∙GenSubComplex X x₀ t (suc m ≟ᵗ suc (suc n))

-- Homology of subcomplex
CW↪CommSubComplex : ∀ {ℓ} (C : CWskel ℓ) (m k : ℕ) →
    CW↪ C m ∘ subComplex→map C k m
  ≡ subComplex→map C k (suc m) ∘ CW↪ (subComplex C k) m
CW↪CommSubComplex C m k with (m ≟ᵗ k) | (suc m ≟ᵗ k)
... | lt x | lt y = refl
... | lt x | eq y = refl
... | lt x | gt y = ⊥.rec (¬squeeze {m} {k} (x , y))
... | eq x | lt y =
  ⊥.rec (¬m<ᵗm {k} (subst (_<ᵗ k) x (<ᵗ-trans {m} {suc m} {k} (<ᵗsucm {m}) y)))
... | eq x | eq y =
  ⊥.rec (¬m<ᵗm {m} (subst (_<ᵗ_ m) (y ∙ (λ i → x (~ i))) (<ᵗsucm {m})))
... | eq x | gt y = funExt λ s → help _ _ x y s (suc m ≟ᵗ suc k)
  where
  help : (m : ℕ) (k : ℕ) (x : m ≡ k) (y : k <ᵗ suc m) (s : fst C m) (p : _)
    →  CW↪ C m s ≡ CW↑Gen C k (suc m) p y (transport refl (subst (fst C) x s))
  help zero = λ k x y s → ⊥.rec (CW₀-empty C s)
  help (suc m) = J> λ y s
    → λ { (lt x) → ⊥.rec (¬squeeze {m} {suc m} (y , x))
         ; (eq x) → cong (CW↪ C (suc m)) (sym (transportRefl s)
              ∙ λ i → subst (fst C) (isSetℕ _ _ refl (cong predℕ (sym x)) i)
                      (transportRefl (transportRefl s (~ i)) (~ i)))
         ; (gt x) → ⊥.rec (¬m<ᵗm {m} x) }
... | gt x | lt y =
  ⊥.rec (¬squeeze {suc m} {k} (y
    , <ᵗ-trans {k} {m} {suc (suc m)} x
      (<ᵗ-trans {m} {suc m} {suc (suc m)} (<ᵗsucm {m}) (<ᵗsucm {suc m}))))
... | gt x | eq y =
  ⊥.rec (¬m<ᵗm {k} (subst (k <ᵗ_) y (<ᵗ-trans {k} {m} {suc m} x (<ᵗsucm {m}))))
... | gt x | gt y = funExt λ a → help _ _ x y (suc m ≟ᵗ suc k) a
  where
  help : (m k : ℕ) (x : k <ᵗ m) (y : k <ᵗ suc m) (p : _) (a : _)
    → CW↪ C m (CW↑Gen C k m  (m ≟ᵗ suc k) x a) ≡ CW↑Gen C k (suc m) p y a
  help (suc m) zero x y p a = ⊥.rec (C .snd .snd .snd .fst a)
  help (suc m) (suc k) x y (lt z) a = ⊥.rec (¬squeeze {k} {suc m} (y , z))
  help (suc m) (suc k) x y (eq z) a =
    ⊥.rec (¬m<ᵗm {m} (subst (_<ᵗ m) (sym (cong (predℕ ∘ predℕ) z)) x))
  help (suc m) (suc k) x y (gt z) a =
    cong (CW↪ C (suc m))
      λ i → CW↑Gen C (suc k) (suc m)
              (Trichotomyᵗ-suc (m ≟ᵗ suc k)) (isProp<ᵗ {k} {m} x z i) a

CW↪SubComplexCharac : ∀ {ℓ} (C : CWskel ℓ) (m k : ℕ) (q : m <ᵗ k) →
    CW↪ (subComplex C k) m
  ≡ invEq (subComplex→Equiv C k (suc m) q)
  ∘ CW↪ C m ∘ subComplex→map C k m
CW↪SubComplexCharac C m k q = funExt λ x
  → sym (retEq (subComplex→Equiv C k (suc m) q) _)
   ∙ cong (invEq (subComplex→Equiv C k (suc m) q))
          (funExt⁻ (sym (CW↪CommSubComplex C m k)) x)

CW↑GenComm : ∀ {ℓ} (C : CWskel ℓ) (m n k : ℕ)
  (p : Trichotomyᵗ n (suc m)) (t : m <ᵗ n)
  → CW↑Gen C m n p t ∘ subComplex→map C k m
  ≡ subComplex→map C k n ∘ CW↑Gen (subComplex C k) m n p t
CW↑GenComm C zero (suc n) k p t =
  funExt λ x → (⊥.rec (G.subComplex₀-empty C k (0 ≟ᵗ k) x))
CW↑GenComm C (suc m) (suc n) k p t =
  funExt (λ qa → (help n m k p _ t refl qa
  ∙ cong ((subComplex→map C k (suc n) ∘
       CW↑Gen (subComplex C k) (suc m) (suc n) p t)) (transportRefl qa)))
  where
  help : (n m k : ℕ) (p : _) (s : _) (t : _) (pp : s ≡ (suc m ≟ᵗ k))
    → (x : G.subComplexFam C k (suc m) s) →
         CW↑Gen C (suc m) (suc n) p t
         (subComplexMapGen.subComplex→map' C k (suc m) s x)
         ≡
         subComplexMapGen.subComplex→map' C k (suc n) (suc n ≟ᵗ k)
         (CW↑Gen (subComplex C k) (suc m) (suc n) p t
           (subst (G.subComplexFam C k (suc m)) pp x))
  help (suc n) m k (lt y) s t pp x = ⊥.rec (¬squeeze {m} {suc n} (t , y))
  help (suc n) m k (eq y) s t pp x = cong (CW↪ C (suc n))
    (cong (λ p → subst (fst C) p
      (subComplexMapGen.subComplex→map' C k (suc m) s x)) (isSetℕ _ _ _ _)
    ∙ lem m (cong predℕ (cong predℕ y)) s (sym pp) x
    ∙ cong (subComplex→map C k (suc n))
        (cong (λ p → subst (subComplexFam C k) p
          (subst (G.subComplexFam C k (suc m)) pp x))
            (isSetℕ _ _ (cong suc (sym (cong (predℕ ∘ predℕ) y)))
              (cong predℕ (sym y)))))
    ∙ funExt⁻ (CW↪CommSubComplex C (suc n) k)
        ((subst (λ m₁ → subComplexFam C k m₁) (cong predℕ (sym y))
          (subst (G.subComplexFam C k (suc m)) pp x)))
    where
    lem : (m : ℕ) (y : n ≡ m) (s : _) (t : (suc m ≟ᵗ k) ≡ s) (x : _)
      → subst (fst C) (cong suc (sym y))
               (subComplexMapGen.subComplex→map' C k (suc m) s x)
        ≡ subComplex→map C k (suc n)
           (subst (subComplexFam C k) (cong suc (sym y))
             (subst (G.subComplexFam C k (suc m)) (sym t) x))
    lem = J> (J> λ x →
       transportRefl _
     ∙ sym (cong (subComplex→map C k (suc n))
                 (transportRefl _ ∙ transportRefl x)))
  help (suc n) m k (gt y) s t pp x =
    cong (CW↪ C (suc n)) (help n m k (suc n ≟ᵗ suc (suc m)) s y pp x)
    ∙ funExt⁻ (CW↪CommSubComplex C (suc n) k)
      (CW↑Gen (subComplex C k) (suc m) (suc n) (suc n ≟ᵗ suc (suc m)) y
         (subst (G.subComplexFam C k (suc m)) pp x))

subComplex→comm : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ)
    (p : _) (q : _) (x : G.subComplexFam C n m p)
  → CW↪ C m (subComplexMapGen.subComplex→map' C n m p x)
  ≡ subComplexMapGen.subComplex→map' C n (suc m) q
       (SubComplexGen.subComplexCW↪Gen C n m p q x)
subComplex→comm C m zero (eq y) s x = ⊥.rec (CW₀-empty C (subst (fst C) y x))
subComplex→comm C m zero (gt y) q x = ⊥.rec (CW₀-empty C x)
subComplex→comm C m (suc n) (lt y) (lt z) x = refl
subComplex→comm C m (suc n) (lt y) (eq z) x = refl
subComplex→comm C m (suc n) (lt y) (gt z) x =
  ⊥.rec (¬squeeze {m} {suc n} (y , z))
subComplex→comm C m (suc n) (eq y) (lt z) x =
  ⊥.rec (¬m<ᵗm {suc n} (transport (λ i → y i <ᵗ suc n)
           (<ᵗ-trans {m} {suc m} {suc n} (<ᵗsucm {m}) z)))
subComplex→comm C m (suc n) (eq y) (eq z) x =
  ⊥.rec ( falseDichotomies.eq-eq (sym y , sym z))
subComplex→comm C m (suc n) (eq y) (gt z) x with (m ≟ᵗ suc n)
... | lt x₃ = ⊥.rec (¬squeeze {n} {m} (z , x₃))
... | eq x₃ = cong (CW↪ C m) (sym (cong (subst (fst C) (sym x₃))
                (transportRefl _
                ∙ cong (λ p → subst (fst C) p x) (isSetℕ _ _ y x₃))
                ∙ subst⁻Subst (fst C) x₃ x))
... | gt x₃ = ⊥.rec (¬m<ᵗm {suc n} (subst (suc n <ᵗ_) y x₃))
subComplex→comm C m (suc n) (gt y) (lt z) x =
  ⊥.rec (¬squeeze {m} {n}
    (z , <ᵗ-trans {suc n} {m} {suc (suc m)} y
           (<ᵗ-trans {m} {suc m} {suc (suc m)} (<ᵗsucm {m}) (<ᵗsucm {suc m}))))
subComplex→comm C m (suc n) (gt y) (eq z) x = (⊥.rec
       (¬m<ᵗm {suc n} (transport (λ i → suc n <ᵗ z i)
         (<ᵗ-trans {suc n} {m} {suc m} y ( <ᵗsucm {m})))))
subComplex→comm C (suc m) (suc n) (gt y) (gt z) x with m ≟ᵗ n
... | lt x₃ = ⊥.rec (¬squeeze {n} {suc m} (z , x₃))
... | eq x₃ = ⊥.rec (¬m<ᵗm {n} (subst (n <ᵗ_) x₃ y))
... | gt x₃ = cong (CW↪ C (suc m))
  λ j → CW↑Gen C (suc n) (suc m)
          (Trichotomyᵗ-suc (m ≟ᵗ suc n)) (isProp<ᵗ {n} {m} y x₃ j) x

subComplex→Full : ∀ {ℓ} (C : CWskel ℓ) (m : ℕ) → cellMap (subComplex C m) C
SequenceMap.map (subComplex→Full C n) = subComplex→map C n
SequenceMap.comm (subComplex→Full C n) m =
  subComplex→comm C m n (m ≟ᵗ n) (suc m ≟ᵗ n)

subComplex→ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ)
  → finCellMap n (subComplex C m) C
FinSequenceMap.fmap (subComplex→ C m n) = subComplex→map C m ∘ fst
FinSequenceMap.fcomm (subComplex→ C m n) t =
  subComplex→comm C (fst t) m (fst t ≟ᵗ m) (suc (fst t) ≟ᵗ m)

subComplexFam↓ : ∀ {ℓ} (C : CWskel ℓ)  (m : ℕ) (p : _) (q : _)
  → G.subComplexFam C m (suc m) p → G.subComplexFam C m m q
subComplexFam↓ C m (lt x) q = ⊥.rec (¬-suc-n<ᵗn {m} x)
subComplexFam↓ C m (eq x) q = ⊥.rec (falseDichotomies.eq-eq(refl , sym x))
subComplexFam↓ C m (gt x) (lt y) = ⊥.rec (¬m<ᵗm {m} y)
subComplexFam↓ C m (gt x) (eq y) = idfun _
subComplexFam↓ C m (gt x) (gt y) = ⊥.rec (¬m<ᵗm {m} y)

CW↪subComplexFam↓ : ∀ {ℓ} (C : CWskel ℓ)  (m : ℕ) (p : _) (q : _) (x : _)
  → SubComplexGen.subComplexCW↪Gen C m m p q (subComplexFam↓ C m q p x) ≡ x
CW↪subComplexFam↓ C m p (lt y) x = ⊥.rec (¬-suc-n<ᵗn {m} y)
CW↪subComplexFam↓ C m p (eq y) x = ⊥.rec (falseDichotomies.eq-eq(refl , sym y))
CW↪subComplexFam↓ C m (lt z) (gt y) x = ⊥.rec (¬m<ᵗm {m} z)
CW↪subComplexFam↓ C m (eq z) (gt y) x =
  transportRefl _ ∙ cong (λ p → subst (fst C) p x) (isSetℕ _ _ z refl)
                  ∙ transportRefl x
CW↪subComplexFam↓ C m (gt z) (gt y) x = ⊥.rec (¬m<ᵗm {m} z)

subComplex→map'Charac : ∀ {ℓ} (C : CWskel ℓ)  (m : ℕ) (p : _) (q : _)
  → subComplexMapGen.subComplex→map' C m (suc m) p
   ≡ CW↪ C m ∘ subComplexMapGen.subComplex→map' C m m q
             ∘ subComplexFam↓ C m p q
subComplex→map'Charac C m p (lt x) = ⊥.rec (¬m<ᵗm {m} x)
subComplex→map'Charac C m (lt y) (eq x) = ⊥.rec (¬-suc-n<ᵗn {m} y)
subComplex→map'Charac C m (eq y) (eq x) =
  ⊥.rec (falseDichotomies.eq-eq (refl , sym y))
subComplex→map'Charac C zero (gt y) (eq x) =
  funExt (λ q → ⊥.rec (C .snd .snd .snd .fst q))
subComplex→map'Charac C (suc m) (gt y) (eq x) with (m ≟ᵗ m)
... | lt z =  ⊥.rec (¬m<ᵗm {m} z)
... | eq z = funExt λ x
  → cong (CW↪ C (suc m)) (cong (λ p → subst (fst C) p x) (isSetℕ _ _ _ _)
    ∙ transportRefl x)
... | gt z =  ⊥.rec (¬m<ᵗm {m} z)
subComplex→map'Charac C m p (gt x) = ⊥.rec (¬m<ᵗm {m} x)
