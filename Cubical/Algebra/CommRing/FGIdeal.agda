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
open import Cubical.Algebra.RingSolver.Reflection
open import Cubical.Algebra.Matrix

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


open CommIdeal.isCommIdeal
genIdeal : {n : ℕ} (R : CommRing ℓ) → FinVec (fst R) n → CommIdeal.CommIdeal R
fst (genIdeal R V) x = isLinearCombination R V x , isPropPropTrunc
+Closed (snd (genIdeal R V)) = isLinearCombination+ R V
contains0 (snd (genIdeal R V)) = isLinearCombination0 R V
·Closed (snd (genIdeal R V)) r = isLinearCombinationL· R V r

syntax genIdeal R V = ⟨ V ⟩[ R ]


FGIdealIn : (R : CommRing ℓ) → Type (ℓ-suc ℓ)
FGIdealIn R = Σ[ I ∈ CommIdeal.CommIdeal R ]
                   ∃[ nV ∈ Σ[ n ∈ ℕ ] FinVec (fst R) n ] I ≡ ⟨ nV .snd ⟩[ R ]

-- The lattice laws
module _ (R' : CommRing ℓ) where
 open CommRingStr (snd R')
 open RingTheory (CommRing→Ring R')
 open CommIdeal R'
 open Sum (CommRing→Ring R')
 open KroneckerDelta (CommRing→Ring R')
 private
  R = fst R'
  ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
  ⟨ V ⟩ = ⟨ V ⟩[ R' ]

 inclOfFGIdeal : {n : ℕ} (V : FinVec R n) (I : CommIdeal)
     → (∀ i → V i ∈ I) → ⟨ V ⟩ ⊆ I
 inclOfFGIdeal V I ∀i→Vi∈I x = elim (λ _ → I .fst x .snd) inclOfFGIdealΣ
  where
  inclOfFGIdealΣ : Σ[ α ∈ FinVec R _ ] x ≡ linearCombination R' α V → x ∈ I
  inclOfFGIdealΣ (α , x≡α·V) = subst-∈ I (sym x≡α·V) (∑Closed I (λ i → α i · V i)
                             λ i → ·Closed (I .snd) _ (∀i→Vi∈I i))

 indInIdeal : ∀ {n : ℕ} (U : FinVec R n) (i : Fin n) → U i ∈ ⟨ U ⟩
 indInIdeal U i = ∣ (δ i) , sym (∑Mul1r _ U i) ∣

 sucIncl : ∀ {n : ℕ} (U : FinVec R (ℕsuc n)) → ⟨ U ∘ suc ⟩ ⊆ ⟨ U ⟩
 sucIncl U x = map λ (α , x≡∑αUsuc) → (λ { zero → 0r ; (suc i) → α i }) , x≡∑αUsuc ∙ path _ _
  where
  path : ∀ s u₀ → s ≡ 0r · u₀ + s
  path = solve R'

 emptyFGIdeal : ∀ (V : FinVec R 0) → ⟨ V ⟩ ≡ 0Ideal
 emptyFGIdeal V = CommIdeal≡Char (λ _ →  rec (is-set _ _) snd)
                                 (λ _ x≡0 → ∣ (λ ()) , x≡0 ∣)

 0FGIdealLIncl : {n : ℕ} → ⟨ replicateFinVec n 0r ⟩ ⊆ 0Ideal
 0FGIdealLIncl x = elim (λ _ → is-set _ _)
         λ (α , x≡∑α0) → subst-∈ 0Ideal (sym x≡∑α0) (∑Closed 0Ideal (λ i → α i · 0r)
         λ i → subst-∈ 0Ideal (sym (0RightAnnihilates _)) refl)

 0FGIdealRIncl : {n : ℕ} → 0Ideal ⊆ ⟨ replicateFinVec n 0r ⟩
 0FGIdealRIncl x x≡0 = subst-∈ ⟨ replicateFinVec _ 0r ⟩ (sym x≡0)
                        (⟨ replicateFinVec _ 0r ⟩ .snd .contains0)

 0FGIdeal : {n : ℕ} → ⟨ replicateFinVec n 0r ⟩ ≡ 0Ideal
 0FGIdeal = CommIdeal≡Char 0FGIdealLIncl 0FGIdealRIncl

 FGIdealAddLemmaLIncl : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
                      → ⟨ U ++Fin V ⟩ ⊆ (⟨ U ⟩ +i ⟨ V ⟩)
 FGIdealAddLemmaLIncl {n = ℕzero} U V x x∈⟨V⟩ =
                                  ∣ (0r , x) , ⟨ U ⟩ .snd .contains0 , x∈⟨V⟩ , sym (+Lid x) ∣
 FGIdealAddLemmaLIncl {n = ℕsuc n} U V x = rec isPropPropTrunc helperΣ
   where
   helperΣ : Σ[ α ∈ FinVec R _ ] (x ≡ ∑ λ i → α i · (U ++Fin V) i) → x ∈ (⟨ U ⟩ +i ⟨ V ⟩)
   helperΣ (α , p) = subst-∈ (⟨ U ⟩ +i ⟨ V ⟩) (sym p)
                              ((⟨ U ⟩ +i ⟨ V ⟩) .snd .+Closed zeroIncl sumIncl)
    where
    zeroIncl : (α zero · U zero) ∈ (⟨ U ⟩ +i ⟨ V ⟩)
    zeroIncl = +iLincl ⟨ U ⟩ ⟨ V ⟩ (α zero · U zero)
                 (⟨ U ⟩ .snd .·Closed (α zero) (indInIdeal U zero))

    sumIncl : (∑ λ i → (α ∘ suc) i · ((U ∘ suc) ++Fin V) i) ∈ (⟨ U ⟩ +i ⟨ V ⟩)
    sumIncl = let sum = ∑ λ i → (α ∘ suc) i · ((U ∘ suc) ++Fin V) i in
         +iRespLincl ⟨ U ∘ suc ⟩ ⟨ U ⟩ ⟨ V ⟩ (sucIncl U) sum
           (FGIdealAddLemmaLIncl (U ∘ suc) V _ ∣ (α ∘ suc) , refl ∣)

 FGIdealAddLemmaRIncl : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
                      → (⟨ U ⟩ +i ⟨ V ⟩) ⊆ ⟨ U ++Fin V ⟩
 FGIdealAddLemmaRIncl U V x = rec isPropPropTrunc (uncurry3 helper)
   where
   helperΣ : ((y , z) : R × R)
           → Σ[ α ∈ FinVec R _ ] (y ≡ ∑ λ i → α i · U i)
           → Σ[ β ∈ FinVec R _ ] (z ≡ ∑ λ i → β i · V i)
           → x ≡ y + z
           → x ∈ ⟨ U ++Fin V ⟩
   helperΣ (y , z) (α , y≡∑αU) (β , z≡∑βV) x≡y+z = ∣ (α ++Fin β) , path ∣
    where
    path : x ≡ ∑ λ i → (α ++Fin β) i · (U ++Fin V) i
    path = x                                               ≡⟨ x≡y+z ⟩
           y + z                                           ≡⟨ cong₂ (_+_) y≡∑αU z≡∑βV ⟩
           (∑ λ i → α i · U i) + (∑ λ i → β i · V i)       ≡⟨ sym (∑Split++ (λ i → α i · U i) _) ⟩
           (∑ ((λ i → α i · U i) ++Fin (λ i → β i · V i))) ≡⟨ ∑Ext (mul++dist α U β V) ⟩
           (∑ λ i → (α ++Fin β) i · (U ++Fin V) i)         ∎

   helper : ((y , z) : R × R)
          → ∃[ α ∈ FinVec R _ ] (y ≡ ∑ λ i → α i · U i)
          → ∃[ β ∈ FinVec R _ ] (z ≡ ∑ λ i → β i · V i)
          → x ≡ y + z
          → x ∈ ⟨ U ++Fin V ⟩
   helper _ = rec2 (isPropΠ (λ _ → isPropPropTrunc)) (helperΣ _)

 FGIdealAddLemma : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
                 → ⟨ U ++Fin V ⟩ ≡ ⟨ U ⟩ +i ⟨ V ⟩
 FGIdealAddLemma U V = CommIdeal≡Char (FGIdealAddLemmaLIncl U V) (FGIdealAddLemmaRIncl U V)


 IdealAddAssoc :  {n m k : ℕ} (U : FinVec R n) (V : FinVec R m) (W : FinVec R k)
               → ⟨ U ++Fin (V ++Fin W) ⟩ ≡  ⟨ (U ++Fin V) ++Fin W ⟩
 IdealAddAssoc {n = n} {m = m} {k = k} U V W =
   let genIdealExpl : (n : ℕ) → FinVec R n → CommIdeal
       genIdealExpl _ V = ⟨ V ⟩
   in  cong₂ genIdealExpl (+ℕ-assoc n m k) (++FinAssoc U V W)

 ++FinComm : ∀ {n m : ℕ} (V : FinVec R n) (W : FinVec R m)
           → ⟨ V ++Fin W ⟩ ≡ ⟨ W ++Fin V ⟩
 ++FinComm V W = FGIdealAddLemma V W ∙∙ +iComm ⟨ V ⟩ ⟨ W ⟩ ∙∙ sym (FGIdealAddLemma W V)

 open ProdFin R'
 prodIn··Ideal : {n m : ℕ} (U : FinVec R n) (V : FinVec R m) (x y : R)
          → (x ∈ ⟨ U ⟩) → (y ∈ ⟨ V ⟩) → (x · y) ∈ ⟨ U ··Fin V ⟩
 prodIn··Ideal {n = n} {m = m} U V x y = map2 Σhelper
  where
  Σhelper : Σ[ α ∈ FinVec R n ] x ≡ linearCombination R' α U
          → Σ[ β ∈ FinVec R m ] y ≡ linearCombination R' β V
          → Σ[ γ ∈ FinVec R (n ·ℕ m) ] (x · y) ≡ linearCombination R' γ (U ··Fin V)
  Σhelper (α , x≡∑αU) (β , y≡∑βV) = α ··Fin β , path
   where
   path : x · y ≡ ∑ λ i → (α ··Fin β) i · (U ··Fin V) i
   path = x · y ≡⟨ cong₂ (_·_) x≡∑αU y≡∑βV ⟩
          (∑ λ i → α i · U i) · (∑ λ i → β i · V i) ≡⟨ ∑Dist··Fin (λ i → α i · U i) _ ⟩
          (∑ λ j → ((λ i → α i · U i) ··Fin (λ i → β i · V i)) j) ≡⟨ ∑Ext (·Dist··Fin α U β V) ⟩
          (∑ λ i → (α ··Fin β) i · (U ··Fin V) i) ∎

 FGIdealMultLemmaLIncl : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
                       → ⟨ U ··Fin V ⟩ ⊆ (⟨ U ⟩ ·i ⟨ V ⟩)
 FGIdealMultLemmaLIncl U V x = elim (λ _ → isPropPropTrunc)
   λ (α , x≡∑αUV) → subst-∈ (⟨ U ⟩ ·i ⟨ V ⟩)  (sym x≡∑αUV) --replace x by ∑αᵢⱼUᵢVⱼ
     (∑Closed (⟨ U ⟩ ·i ⟨ V ⟩) (λ i → α i · (U ··Fin V) i) --show that each αᵢ(U··V)ᵢ is in product
       λ i → (⟨ U ⟩ ·i ⟨ V ⟩) .snd .·Closed (α i) --drop the α's
         (flattenElim {P = _∈ (⟨ U ⟩ ·i ⟨ V ⟩)} (toMatrix U V) --show theat UᵢVⱼ is in product
           (λ j k → prodInProd ⟨ U ⟩ ⟨ V ⟩ (U j) (V k) (indInIdeal U j) (indInIdeal V k)) i))

 FGIdealMultLemmaRIncl : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
                       → (⟨ U ⟩ ·i ⟨ V ⟩) ⊆ ⟨ U ··Fin V ⟩
 FGIdealMultLemmaRIncl U V x = elim (λ _ → isPropPropTrunc)
   λ (_ , (α , β) , ∀α∈⟨U⟩ , ∀β∈⟨V⟩ , x≡∑αβ) → subst-∈ ⟨ U ··Fin V ⟩ (sym x≡∑αβ)
     (∑Closed ⟨ U ··Fin V ⟩ _ (λ i → prodIn··Ideal U V (α i) (β i) (∀α∈⟨U⟩ i) (∀β∈⟨V⟩ i)))

 FGIdealMultLemma : {n m : ℕ} (U : FinVec R n) (V : FinVec R m)
                 → ⟨ U ··Fin V ⟩ ≡ ⟨ U ⟩ ·i ⟨ V ⟩
 FGIdealMultLemma U V = CommIdeal≡Char (FGIdealMultLemmaLIncl U V) (FGIdealMultLemmaRIncl U V)
