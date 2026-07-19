
{-
This file contains a definition of the n-level axiom of coice,
i.e. the statment that the canonical map

∥ Πₐ Bₐ ∥ₙ → (Πₐ ∥ Bₐ ∥ₙ)

is an equivalence.
-}

module Cubical.Axiom.Choice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin as FN
open import Cubical.Data.Fin.Inductive as IndF
open import Cubical.Data.Nat.Order

open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ' ℓ'' : Level

choiceMap : {A : Type ℓ} {B : A → Type ℓ'} (n : ℕ)
  → hLevelTrunc n ((a : A) → B a)
  → (a : A) → hLevelTrunc n (B a)
choiceMap n =
  TR.rec (isOfHLevelΠ n (λ _ → isOfHLevelTrunc n))
         λ f a → ∣ f a ∣ₕ

-- n-level axiom of choice
satAC : (ℓ' : Level) (n : ℕ) (A : Type ℓ)  → Type (ℓ-max ℓ (ℓ-suc ℓ'))
satAC ℓ' n A = (B : A → Type ℓ') → isEquiv (choiceMap {A = A} {B} n)

-- Version of (propositional) AC with ∃
AC∃-map : {A : Type ℓ} {B : A → Type ℓ'}
     {C : (a : A) → B a → Type ℓ''}
  → ∃[ f ∈ ((a : A) → B a) ] ((a : _) → C a (f a))
  → ((a : A) → ∃ (B a) (C a))
AC∃-map =
  PT.rec (isPropΠ (λ _ → squash₁))
    λ f → λ a → ∣ f .fst a , f .snd a ∣₁

satAC∃ : ∀ {ℓ} (ℓ' ℓ'' : Level) (A : Type ℓ) → Type _
satAC∃ ℓ' ℓ'' A = (B : A → Type ℓ') (C : (a : A) → B a → Type ℓ'')
  → isEquiv (AC∃-map {B = B} {C = C})

satAC→satAC∃ : {A : Type ℓ}
  → satAC (ℓ-max ℓ' ℓ'') (suc zero) A → satAC∃ ℓ' ℓ'' A
satAC→satAC∃ F B C = propBiimpl→Equiv squash₁ (isPropΠ (λ _ → squash₁))
  _
  (λ f → invEq propTrunc≃Trunc1 (TR.map (λ f → fst ∘ f , λ a → f a .snd )
          (invEq (_ , F (λ x → Σ (B x) (C x)))
            λ a → fst propTrunc≃Trunc1 (f a)))) .snd

-- All types satisfy (-2) level axiom of choice
satAC₀ : {A : Type ℓ} → satAC ℓ' 0 A
satAC₀ B =
  isoToIsEquiv (iso (λ _ _ → tt*) (λ _ → tt*) (λ _ → refl) λ _ → refl)

-- Fin m satisfies AC for any level n.
FinSatAC : (n m : ℕ) → ∀ {ℓ} → satAC ℓ n (FN.Fin m)
FinSatAC n zero B =
  isoToIsEquiv (iso _
    (λ f → ∣ (λ x → ⊥.rec (FN.¬Fin0 x)) ∣ₕ)
    (λ f → funExt λ x → ⊥.rec (FN.¬Fin0 x))
    (TR.elim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _)
      λ a → cong  ∣_∣ₕ (funExt λ x → ⊥.rec (FN.¬Fin0 x))))
FinSatAC n (suc m) B =
  subst isEquiv (ac-eq n m {B} (FinSatAC n m))
    (isoToIsEquiv (ac-map' n m B (FinSatAC n m)))
  where
  ac-map' : ∀ {ℓ} (n m : ℕ) (B : FN.Fin (suc m) → Type ℓ)
    → (satAC ℓ n (FN.Fin m))
    → Iso (hLevelTrunc n ((x : _) → B x)) ((x : _) → hLevelTrunc n (B x))
  ac-map' n m B ise =
    compIso (mapCompIso (CharacΠFinIso m))
            (compIso (truncOfProdIso n)
              (compIso (Σ-cong-iso-snd λ _ → equivToIso
                (_ , ise (λ x → B (FN.fsuc x))))
                (invIso (CharacΠFinIso m))))

  ac-eq : (n m : ℕ) {B : _} → (eq : satAC ℓ n (FN.Fin m))
       → Iso.fun (ac-map' n m B eq) ≡ choiceMap {B = B} n
  ac-eq zero m {B = B} x = refl
  ac-eq (suc n) m {B = B} x =
    funExt (TR.elim (λ _ → isOfHLevelPath (suc n)
                             (isOfHLevelΠ (suc n)
                              (λ _ → isOfHLevelTrunc (suc n))) _ _)
      λ F → funExt
      λ { (zero , p) j
          → ∣ transp (λ i → B (lem₁ p (j ∨ i))) j (F (lem₁ p j)) ∣ₕ
        ; (suc x , p) j
          → ∣ transp (λ i → B (lem₂ x p (j ∨ i))) j (F (lem₂ x p j)) ∣ₕ})
    where
    lem₁ : (p : _ ) → FN.fzero ≡ (zero , p)
    lem₁ p = Fin-fst-≡ refl

    lem₂ : (x : _) (p : suc x < suc m)
      → Path (FN.Fin _) (FN.fsuc (x , pred-≤-pred p)) (suc x , p)
    lem₂ x p = Fin-fst-≡ refl

-- Key result for construction of cw-approx at lvl 0
satAC∃Fin : (n : ℕ) → satAC∃ ℓ ℓ' (FN.Fin n)
satAC∃Fin n = satAC→satAC∃ (FinSatAC 1 n)

InductiveFinSatAC : (n m : ℕ) → ∀ {ℓ} → satAC ℓ n (IndF.Fin m)
InductiveFinSatAC n m {ℓ} =
  subst (satAC ℓ n) (isoToPath (Iso-Fin-InductiveFin m)) (FinSatAC n m)

InductiveFinSatAC∃ : (n : ℕ) → satAC∃ ℓ ℓ' (IndF.Fin n)
InductiveFinSatAC∃ {ℓ = ℓ} {ℓ'} n =
  subst (satAC∃ ℓ ℓ') (isoToPath (Iso-Fin-InductiveFin n)) (satAC∃Fin n)
