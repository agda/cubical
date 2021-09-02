{-
  Define finitely generated ideals of commutative rings and
  show that they are an ideal.
  Parts of this should be reusable for explicit constructions
  of free modules over a finite set.
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.FGIdeal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.FinData hiding (elim ; rec)
open import Cubical.Data.Nat renaming ( zero to ℕzero ; suc to ℕsuc
                                      ; _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-assoc to +ℕ-assoc ; +-comm to +ℕ-comm
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
                             hiding (elim)
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.Ring.QuotientRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.RingSolver.ReflectionSolving

private
  variable
    ℓ : Level

module _ (Ring@(R , str) : CommRing ℓ) where
  infixr 5 _holds
  _holds : hProp ℓ → Type ℓ
  P holds = fst P
  open CommRingStr str
  open RingTheory (CommRing→Ring Ring)
  open Sum (CommRing→Ring Ring)

  linearCombination : {n : ℕ} → FinVec R n → FinVec R n → R
  linearCombination α V = ∑ (λ i → α i · V i)

  sumDist+ : ∀ {n : ℕ} (α β V : FinVec R n)
           → linearCombination (λ i → α i + β i) V ≡ linearCombination α V + linearCombination β V
  sumDist+ α β V = ∑Ext (λ i → ·Ldist+ (α i) (β i) (V i)) ∙ ∑Split (λ i → α i · V i) (λ i → β i · V i)

  dist- : ∀ {n : ℕ} (α V : FinVec R n)
        → linearCombination (λ i → - α i) V ≡ - linearCombination α V
  dist- α V = ∑Ext (λ i → -DistL· (α i) (V i)) ∙ ∑Dist- (λ i → α i · V i)

  dist0 : ∀ {n : ℕ} (V : FinVec R n)
        → linearCombination (replicateFinVec n 0r) V ≡ 0r
  dist0 {n = n} V = ∑Ext (λ i → 0LeftAnnihilates (V i)) ∙ ∑0r n

  isLinearCombination : {n : ℕ} → FinVec R n → R → Type ℓ
  isLinearCombination V x = ∃[ α ∈ FinVec R _ ] x ≡ linearCombination α V

  {- If x and y are linear combinations of l, then (x + y) is
     a linear combination. -}
  isLinearCombination+ : {n : ℕ} {x y : R} (V : FinVec R n)
                         → isLinearCombination V x
                         → isLinearCombination V y
                         → isLinearCombination V (x + y)
  isLinearCombination+ V = map2 λ α β → (λ i → α .fst i + β .fst i)
                                       , cong₂ (_+_) (α .snd) (β .snd) ∙ sym (sumDist+ _ _ V)

  {- If x is a linear combinations of l, then -x is
     a linear combination. -}
  isLinearCombination- : {n : ℕ} {x : R} (V : FinVec R n)
                       → isLinearCombination V x → isLinearCombination V (- x)
  isLinearCombination- V = map λ α → (λ i → - α .fst i) , cong (-_) (α .snd) ∙ sym (dist- _ V)

  {- 0r is the trivial linear Combination -}
  isLinearCombination0 : {n : ℕ} (V : FinVec R n)
                       → isLinearCombination V 0r
  isLinearCombination0 V = ∣ _ , sym (dist0 V) ∣

  {- Linear combinations are stable under left multiplication -}
  isLinearCombinationL· : {n : ℕ} (V : FinVec R n) (r : R) {x : R}
                        → isLinearCombination V x → isLinearCombination V (r · x)
  isLinearCombinationL· V r = map λ α → (λ i → r · α .fst i) , cong (r ·_) (α .snd)
                                                            ∙∙ ∑Mulrdist r (λ i → α .fst i · V i)
                                                            ∙∙ ∑Ext λ i → ·Assoc r (α .fst i) (V i)

  generatedIdeal : {n : ℕ} → FinVec R n → IdealsIn Ring
  generatedIdeal V = makeIdeal Ring
                               (λ x → isLinearCombination V x , isPropPropTrunc)
                               (isLinearCombination+ V)
                               (isLinearCombination0 V)
                               λ r → isLinearCombinationL· V r


--open CommIdeal
open CommIdeal.isCommIdeal
genIdeal : {n : ℕ} (R : CommRing ℓ) → FinVec (fst R) n → CommIdeal.CommIdeal R
fst (genIdeal R V) x = isLinearCombination R V x , isPropPropTrunc
+Closed (snd (genIdeal R V)) = isLinearCombination+ R V
contains0 (snd (genIdeal R V)) = isLinearCombination0 R V
·Closed (snd (genIdeal R V)) r = isLinearCombinationL· R V r

syntax genIdeal R V = ⟨ V ⟩[ R ]


FGIdealIn : (R : CommRing ℓ) → Type (ℓ-suc ℓ)
FGIdealIn R = Σ[ I ∈ CommIdeal.CommIdeal R ] ∃[ n ∈ ℕ ] ∃[ V ∈ FinVec (fst R) n ] I ≡ ⟨ V ⟩[ R ]

-- The lattice laws
module _ (R' : CommRing ℓ) where
 open CommRingStr (snd R')
 open CommIdeal R'
 open Sum (CommRing→Ring R')
 open KroneckerDelta (CommRing→Ring R')
 private
  R = fst R'
  ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
  ⟨ V ⟩ = ⟨ V ⟩[ R' ]

 foo : {n : ℕ} (V : FinVec R n) (I : CommIdeal)
     → (∀ i → V i ∈ I .fst) → ⟨ V ⟩ .fst ⊆ I .fst
 foo V I ∀i→Vi∈I x = elim (λ _ → I .fst x .snd) fooΣ
  where
  fooΣ : Σ[ α ∈ FinVec R _ ] x ≡ linearCombination R' α V → x ∈ I .fst
  fooΣ (α , x≡α·V) = subst-∈ (I .fst) (sym x≡α·V) (∑Closed I (λ i → α i · V i)
                     λ i → ·Closed (I .snd) _ (∀i→Vi∈I i))

 indInIdeal : ∀ {n : ℕ} (U : FinVec R n) (i : Fin n) → U i ∈ ⟨ U ⟩ .fst
 indInIdeal U i = ∣ (δ i) , sym (∑Mul1r _ U i) ∣

 sucIncl : ∀ {n : ℕ} (U : FinVec R (ℕsuc n)) → ⟨ U ∘ suc ⟩ .fst ⊆ ⟨ U ⟩ .fst
 sucIncl U x = map λ (α , x≡∑αUsuc) → (λ { zero → 0r ; (suc i) → α i }) , x≡∑αUsuc ∙ path _ _
  where
  path : ∀ s u₀ → s ≡ 0r · u₀ + s
  path = solve R'

 emptyFGIdeal : ∀ (V : FinVec R 0) → ⟨ V ⟩ ≡ 0Ideal
 emptyFGIdeal V = Σ≡Prop isPropIsCommIdeal (⊆-extensionality _ _ (incl1 , incl2))
  where
  incl1 : ⟨ V ⟩ .fst ⊆ 0Ideal .fst
  incl1 x = rec (is-set _ _) λ (_ , p) → p

  incl2 : 0Ideal .fst ⊆ ⟨ V ⟩ .fst
  incl2 x x≡0 = ∣ (λ ()) , x≡0 ∣

 FGIdealAddLemma : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
                 → ⟨ U ++Fin V ⟩ ≡ ⟨ U ⟩ +i ⟨ V ⟩
 FGIdealAddLemma {n = ℕzero} U V = sym (cong (_+i ⟨ V ⟩) (emptyFGIdeal U) ∙ +iLid ⟨ V ⟩)
 FGIdealAddLemma {n = ℕsuc n} U V = Σ≡Prop isPropIsCommIdeal (⊆-extensionality _ _ (incl1 , incl2))
  where
  incl1 : ⟨ U ++Fin V ⟩ .fst ⊆ (⟨ U ⟩ +i ⟨ V ⟩) .fst
  incl1 x = rec isPropPropTrunc incl1Σ
   where
   incl1Σ : Σ[ α ∈ FinVec R _ ] (x ≡ ∑ λ i → α i · (U ++Fin V) i) → x ∈ (⟨ U ⟩ +i ⟨ V ⟩) .fst
   incl1Σ (α , p) = subst-∈ ((⟨ U ⟩ +i ⟨ V ⟩) .fst) (sym p) ((⟨ U ⟩ +i ⟨ V ⟩) .snd .+Closed baz bar)
    where
    baz : α zero · U zero ∈ (⟨ U ⟩ +i ⟨ V ⟩) .fst
    baz = +iLincl ⟨ U ⟩ ⟨ V ⟩ (α zero · U zero) (⟨ U ⟩ .snd .·Closed (α zero) (indInIdeal U zero))

    bar : (∑ λ i → (α ∘ suc) i · ((U ∘ suc) ++Fin V) i) ∈ (⟨ U ⟩ +i ⟨ V ⟩) .fst
    bar = let sum = ∑ λ i → (α ∘ suc) i · ((U ∘ suc) ++Fin V) i in
       +iRespLincl ⟨ U ∘ suc ⟩ ⟨ U ⟩ ⟨ V ⟩ (sucIncl U) sum
          (subst (λ I → sum ∈ I .fst) (FGIdealAddLemma (U ∘ suc) V) ∣ (α ∘ suc) , refl ∣)

  incl2 : (⟨ U ⟩ +i ⟨ V ⟩) .fst ⊆  ⟨ U ++Fin V ⟩ .fst
  incl2 = {!!}

 IdealAddAssoc :  {n m k : ℕ} (U : FinVec R n) (V : FinVec R m) (W : FinVec R k)
               → ⟨ U ++Fin (V ++Fin W) ⟩ ≡  ⟨ (U ++Fin V) ++Fin W ⟩
 IdealAddAssoc {n = n} {m = m} {k = k} U V W =
   let genIdealExpl : (n : ℕ) → FinVec R n → CommIdeal
       genIdealExpl _ V = ⟨ V ⟩
   in  cong₂ genIdealExpl (+ℕ-assoc n m k) (++FinAssoc U V W)

 -- ++FinComm : ∀ {n m : ℕ} (V : FinVec R n) (W : FinVec R m)
 --           → ⟨ V ++Fin W ⟩ ≡ ⟨ W ++Fin V ⟩
 -- ++FinComm V W = Σ≡Prop (isPropIsCommIdeal _) (⊆-extensionality _ _
 --                                              (foo _ (⟨ W ++Fin V ⟩) (λ i → {!!})
 --                                             , foo _ (⟨ V ++Fin W ⟩) (λ i → {!!})))
