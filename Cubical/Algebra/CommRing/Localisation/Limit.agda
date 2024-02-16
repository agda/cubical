{-
  This file contains a proof of the following fact:
  For a commutative ring R with elements f₁ , ... , fₙ ∈ R such that
  ⟨ f₁ , ... , fₙ ⟩ = ⟨ 1 ⟩ = R we get an (exact) equalizer diagram of the following form:
      0 → R → ∏ᵢ R[1/fᵢ] ⇉ ∏ᵢⱼ R[1/fᵢfⱼ]
  where the two maps ∏ᵢ R[1/fᵢ] → ∏ᵢⱼ R[1/fᵢfⱼ] are induced by the two canonical maps
  R[1/fᵢ] → R[1/fᵢfⱼ] and R[1/fⱼ] → R[1/fᵢfⱼ].
  Using the well-known correspondence between equalizers of products and limits,
  we express the above fact through limits over the diagrams defined in
  Cubical.Categories.DistLatticeSheaf.Diagram
-}

{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.CommRing.Localisation.Limit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset renaming (_∈_ to _∈ₚ_)

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Nat.Order hiding (_<_ ; _≟_)
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order renaming (_<'Fin_ to _<_ ; _≟Fin_ to _≟_)

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Algebra.CommRing.Localisation.UniversalProperty
open import Cubical.Algebra.CommRing.Localisation.InvertingElements
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Algebra.Semilattice.Instances.NatMax

open import Cubical.Tactics.CommRingSolver

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.DistLatticeSheaf.Diagram

open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level


-- were not dealing with case 0 here
-- but then R = 0 = lim {} (limit of the empty diagram)
module _ (R' : CommRing ℓ) {n : ℕ} (f : FinVec (fst R') n) where
 open isMultClosedSubset
 open CommRingTheory R'
 open RingTheory (CommRing→Ring R')
 open Sum (CommRing→Ring R')
 open CommIdeal R'
 open InvertingElementsBase R'
 open Exponentiation R'
 open CommRingStr ⦃...⦄

 private
  R = fst R'
  ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
  ⟨ V ⟩ = ⟨ V ⟩[ R' ]
  ⟨f₀,⋯,fₙ⟩ = ⟨ f ⟩[ R' ]

  instance
   _ = R' .snd

  module L i = Loc R' [ f i ⁿ|n≥0] (powersFormMultClosedSubset (f i))
  module U i = S⁻¹RUniversalProp R' [ f i ⁿ|n≥0] (powersFormMultClosedSubset (f i))
  module LP i j = Loc R' [ f i · f j ⁿ|n≥0] (powersFormMultClosedSubset (f i · f j))
  module UP i j = S⁻¹RUniversalProp R' [ f i · f j ⁿ|n≥0] (powersFormMultClosedSubset (f i · f j))

  -- some syntax to make things readable
  0at : (i : Fin n) →  R[1/ (f i) ]
  0at i = R[1/ (f i) ]AsCommRing .snd .CommRingStr.0r

  _/1ˢ : R → {i : Fin n} →  R[1/ (f i) ]
  (r /1ˢ) {i = i} = U._/1 i r

  _/1ᵖ : R → {i j : Fin n} →  R[1/ (f i) · (f j) ]
  (r /1ᵖ) {i = i} {j = j} = UP._/1 i j r


 -- This lemma proves that if ⟨ f₀ ,..., fₙ ⟩ ≡ R,
 -- then we get an exact sequence
 --   0 → R → ∏ᵢ R[1/fᵢ]
 -- sending r : R to r/1 in R[1/fᵢ] for each i
 injectivityLemma : 1r ∈ ⟨f₀,⋯,fₙ⟩ → ∀ (x : R) → (∀ i → x /1ˢ ≡ 0at i) → x ≡ 0r
 injectivityLemma 1∈⟨f₀,⋯,fₙ⟩ x x/1≡0 = recFin (is-set _ _) annihilatorHelper exAnnihilator
  where
  exAnnihilator : ∀ i → ∃[ s ∈ L.S i ] (fst s · x · 1r ≡ fst s · 0r · 1r)
  exAnnihilator i = isEquivRel→TruncIso (L.locIsEquivRel i) _ _ .fun (x/1≡0 i)

  annihilatorHelper : (∀ i → Σ[ s ∈ L.S i ] (fst s · x · 1r ≡ fst s · 0r · 1r))
                    → x ≡ 0r
  annihilatorHelper ann = recFin (is-set _ _) exponentHelper uIsPower
    where
    u : FinVec R n
    u i = ann i .fst .fst

    uIsPower : ∀ i → u i ∈ₚ [ (f i) ⁿ|n≥0]
    uIsPower i = ann i .fst .snd

    ux≡0 : ∀ i → u i · x ≡ 0r
    ux≡0 i = sym (·IdR _) ∙ ann i .snd ∙ cong (_· 1r) (0RightAnnihilates _) ∙ (·IdR _)

    exponentHelper : (∀ i → Σ[ m ∈ ℕ ] u i ≡ f i ^ m)
                   → x ≡ 0r
    exponentHelper pows = PT.rec (is-set _ _) Σhelper (GeneratingPowers.thm R' l _ _ 1∈⟨f₀,⋯,fₙ⟩)
      where
      m : FinVec ℕ n
      m i = pows i .fst

      u≡fᵐ : ∀ i → u i ≡ f i ^ m i
      u≡fᵐ i = pows i .snd

      l = Max m

      fˡ : FinVec R n
      fˡ i = f i ^ l

      fˡx≡0 : ∀ i → f i ^ l · x ≡ 0r
      fˡx≡0 i =
        f i ^ l · x                     ≡⟨ cong (λ k → f i ^ k · x)
                                             (sym (≤-∸-+-cancel (ind≤Max m i))) ⟩
        f i ^ ((l ∸ m i) +ℕ m i) · x    ≡⟨ cong (_· x) (sym (·-of-^-is-^-of-+ _ _ _)) ⟩
        f i ^ (l ∸ m i) · f i ^ m i · x ≡⟨ cong (λ y → f i ^ (l ∸ m i) · y · x)
                                                (sym (u≡fᵐ i)) ⟩
        f i ^ (l ∸ m i) · u i · x       ≡⟨ sym (·Assoc _ _ _) ⟩
        f i ^ (l ∸ m i) · (u i · x)     ≡⟨ cong (f i ^ (l ∸ m i) ·_) (ux≡0 i) ⟩
        f i ^ (l ∸ m i) · 0r            ≡⟨ 0RightAnnihilates _ ⟩
        0r ∎


      Σhelper : Σ[ α ∈ FinVec R n ] 1r ≡ ∑ (λ i → α i · f i ^ l)
              → x ≡ 0r
      Σhelper (α , 1≡∑αfˡ) =
        x                                   ≡⟨ sym (·IdL _) ⟩
        1r · x                              ≡⟨ cong (_· x) 1≡∑αfˡ ⟩
        ∑ (λ i → α i · f i ^ l) · x         ≡⟨ ∑Mulldist _ _ ⟩
        ∑ (λ i → α i · f i ^ l · x)         ≡⟨ ∑Ext (λ i → sym (·Assoc (α i)
                                                                  (f i ^ l) x)) ⟩
        ∑ (λ i → α i · (f i ^ l · x))       ≡⟨ ∑Ext (λ i → cong (α i ·_) (fˡx≡0 i)) ⟩
        ∑ (λ i → α i · 0r)                  ≡⟨ ∑Ext (λ i → 0RightAnnihilates (α i)) ⟩
        ∑ (replicateFinVec n 0r)            ≡⟨ ∑0r n ⟩
        0r ∎


 -- the morphisms into localisations of products from the left/right
 -- we need to define them by hand as using RadicalLemma wouldn't compute later
 χˡUnique : (i j : Fin n)
          → ∃![ χ ∈ CommRingHom R[1/ f i ]AsCommRing R[1/ f i · f j ]AsCommRing ]
                (fst χ) ∘ (U._/1 i) ≡ (UP._/1 i j)
 χˡUnique i j = U.S⁻¹RHasUniversalProp i _ (UP./1AsCommRingHom i j) unitHelper
   where
   unitHelper : ∀ s → s ∈ₚ [ (f i) ⁿ|n≥0] → s /1ᵖ ∈ₚ (R[1/ f i · f j ]AsCommRing) ˣ
   unitHelper = powersPropElim (λ s → Units.inverseUniqueness _ (s /1ᵖ))
                  λ m → [ f j ^ m , (f i · f j) ^ m , ∣ m , refl ∣₁ ]
                        , eq/ _ _ ((1r , powersFormMultClosedSubset (f i · f j) .containsOne)
                        , path m)
     where
     path : (n : ℕ) → 1r · (f i ^ n · f j ^ n) · 1r ≡ (1r · 1r) · (1r · ((f i · f j) ^ n))
     path n = solve! R' ∙ sym (^-ldist-· (f i) (f j) n) ∙ solve! R'

 χˡ : (i j : Fin n) → CommRingHom R[1/ f i ]AsCommRing R[1/ f i · f j ]AsCommRing
 χˡ i j = χˡUnique i j .fst .fst

 χʳUnique : (i j : Fin n)
          →  ∃![ χ ∈ CommRingHom R[1/ f j ]AsCommRing R[1/ f i · f j ]AsCommRing ]
                (fst χ) ∘ (U._/1 j) ≡ (UP._/1 i j)
 χʳUnique i j = U.S⁻¹RHasUniversalProp j _ (UP./1AsCommRingHom i j) unitHelper
   where
   unitHelper : ∀ s → s ∈ₚ [ (f j) ⁿ|n≥0] → s /1ᵖ ∈ₚ (R[1/ f i · f j ]AsCommRing) ˣ
   unitHelper = powersPropElim (λ s → Units.inverseUniqueness _ (s /1ᵖ))
                  λ m → [ f i ^ m , (f i · f j) ^ m , ∣ m , refl ∣₁ ]
                        , eq/ _ _ ((1r , powersFormMultClosedSubset (f i · f j) .containsOne)
                        , path m)
     where
     path : (n : ℕ) → 1r · (f j ^ n · f i ^ n) · 1r ≡ (1r · 1r) · (1r · ((f i · f j) ^ n))
     path n = solve! R' ∙ sym (^-ldist-· (f i) (f j) n) ∙ solve! R'

 χʳ : (i j : Fin n) → CommRingHom R[1/ f j ]AsCommRing R[1/ f i · f j ]AsCommRing
 χʳ i j = χʳUnique i j .fst .fst



 -- super technical stuff, please don't look at it
 private
  χ≡Elim<Only : (x  : (i : Fin n) → R[1/ f i ])
          → (∀ i j → i < j → χˡ i j .fst (x i) ≡ χʳ i j .fst (x j))
          → ∀ i j → χˡ i j .fst (x i) ≡ χʳ i j .fst (x j)
  χ≡Elim<Only x <hyp i j = aux (i ≟ j) -- doesn't type check in reasonable time using with syntax
    where
    aux : FinTrichotomy i j → χˡ i j .fst (x i) ≡ χʳ i j .fst (x j)
    aux (lt i<j) = <hyp _ _ i<j
    aux (eq i≡j) = subst (λ j' → χˡ i j' .fst (x i) ≡ χʳ i j' .fst (x j')) i≡j (χId i (x i))
      where
      χId : ∀ i x → χˡ i i .fst x ≡ χʳ i i .fst x
      χId i = invElPropElim (λ _ → squash/ _ _)
                (λ r m → cong [_] (ΣPathP (refl , Σ≡Prop (∈-isProp _) refl)))

    aux (gt j<i) =
      χˡ i j .fst (x i) ≡⟨ χSwapL→R i j (x i) ⟩
      χʳsubst i j (x i) ≡⟨ cong (subst (λ r → R[1/ r ]) (·Comm (f j) (f i))) (sym (<hyp _ _ j<i)) ⟩
      χˡsubst i j (x j) ≡⟨ sym (χSwapR→L i j (x j)) ⟩
      χʳ i j .fst (x j) ∎
      where
      χʳsubst : (i j : Fin n) → R[1/ f i ] → R[1/ f i · f j ]
      χʳsubst i j x = subst (λ r → R[1/ r ]) (·Comm (f j) (f i)) (χʳ j i .fst x)

      χSwapL→R : ∀ i j x → χˡ i j .fst x ≡ χʳsubst i j x
      χSwapL→R i j = invElPropElim (λ _ → squash/ _ _)
             λ r m → cong [_] (ΣPathP (sym (transportRefl _) , Σ≡Prop (∈-isProp _)
                      (sym (transportRefl _ ∙ cong (λ x → 1r · transport refl (x ^ m)) (·Comm _ _)))))
      χˡsubst : (i j : Fin n) → R[1/ f j ] → R[1/ f i · f j ]
      χˡsubst i j x = subst (λ r → R[1/ r ]) (·Comm (f j) (f i)) (χˡ j i .fst x)

      χSwapR→L : ∀ i j x → χʳ i j .fst x ≡ χˡsubst i j x
      χSwapR→L i j = invElPropElim (λ _ → squash/ _ _)
             λ r m → cong [_] (ΣPathP (sym (transportRefl _) , Σ≡Prop (∈-isProp _)
                      (sym (transportRefl _ ∙ cong (λ x → 1r · transport refl (x ^ m)) (·Comm _ _)))))

 χ≡PropElim : {B : ((i : Fin n) → R[1/ f i ]) → Type ℓ''} (isPropB : ∀ {x} → isProp (B x))
            → (∀ (r : FinVec R n) (m l : ℕ)
                  → (∀ i j → r i · f j ^ m · (f i · f j) ^ l ≡ r j · f i ^ m · (f i · f j) ^ l)
                  → B (λ i → [ r i , f i ^ m , ∣ m , refl ∣₁ ]))
          -------------------------------------------------------------------------------------
           → (x : (i : Fin n) → R[1/ f i ])
           → (∀ i j → χˡ i j .fst (x i) ≡ χʳ i j .fst (x j))
           → B x
 χ≡PropElim {B = B} isPropB baseHyp = invElPropElimN n f _ (λ _ → isProp→ isPropB) baseCase
   where
   baseCase : ∀ (r : FinVec R n) (m : ℕ)
            → (∀ i j → χˡ i j .fst ([ r i , f i ^ m , ∣ m , refl ∣₁ ])
                     ≡ χʳ i j .fst ([ r j , f j ^ m , ∣ m , refl ∣₁ ]))
            → B (λ i → [ r i , f i ^ m , ∣ m , refl ∣₁ ])
   baseCase r m pairHyp = recFin2 isPropB  annihilatorHelper exAnnihilator
     where
     -- This computes because we defined the χ by hand
     exAnnihilator : ∀ i j
                   → ∃[ s ∈ LP.S i j ] -- s.t.
                       fst s · (r i · transport refl (f j ^ m))
                             · (1r · transport refl ((f i · f j) ^ m))
                     ≡ fst s · (r j · transport refl (f i ^ m))
                             · (1r · transport refl ((f i · f j) ^ m))
     exAnnihilator i j = isEquivRel→TruncIso (LP.locIsEquivRel _ _) _ _ .fun
                                             (pairHyp i j)

     annihilatorHelper : (∀ i j
                           → Σ[ s ∈ LP.S i j ] -- s.t.
                               fst s · (r i · transport refl (f j ^ m))
                                     · (1r · transport refl ((f i · f j) ^ m))
                             ≡ fst s · (r j · transport refl (f i ^ m))
                                     · (1r · transport refl ((f i · f j) ^ m)))
                       → B (λ i → [ r i , f i ^ m , ∣ m , refl ∣₁ ])
     annihilatorHelper anns = recFin2 isPropB exponentHelper sIsPow
       where
       -- notation
       s : (i j : Fin n) → R
       s i j = anns i j .fst .fst

       sIsPow : ∀ i j → s i j ∈ₚ [ (f i · f j) ⁿ|n≥0]
       sIsPow i j = anns i j .fst .snd

       sIsAnn : ∀ i j
              → s i j · r i · f j ^ m · (f i · f j) ^ m
              ≡ s i j · r j · f i ^ m · (f i · f j) ^ m
       sIsAnn i j =
           s i j · r i · f j ^ m · (f i · f j) ^ m
         ≡⟨ transpHelper _ _ _ _ ⟩
           s i j · r i · transport refl (f j ^ m) · transport refl ((f i · f j) ^ m)
         ≡⟨ useSolver _ _ _ _ ⟩
           s i j · (r i · transport refl (f j ^ m))
                 · (1r · transport refl ((f i · f j) ^ m))
         ≡⟨ anns i j .snd ⟩
           s i j · (r j · transport refl (f i ^ m))
                 · (1r · transport refl ((f i · f j) ^ m))
         ≡⟨ sym (useSolver _ _ _ _) ⟩
           s i j · r j · transport refl (f i ^ m) · transport refl ((f i · f j) ^ m)
         ≡⟨ sym (transpHelper _ _ _ _) ⟩
           s i j · r j · f i ^ m · (f i · f j) ^ m ∎
         where
         transpHelper : ∀ a b c d → a · b · c · d
                                  ≡ a · b · transport refl c · transport refl d
         transpHelper a b c d i = a · b · transportRefl c (~ i) · transportRefl d (~ i)
         useSolver : ∀ a b c d → a · b · c · d ≡ a · (b · c) · (1r · d)
         useSolver _ _ _ _ = solve! R'

       exponentHelper : (∀ i j
                           → Σ[ l ∈ ℕ ] s i j ≡ (f i · f j) ^ l)
                      → B (λ i → [ r i , f i ^ m , ∣ m , refl ∣₁ ])
       exponentHelper pows = baseHyp r m (m +ℕ k) paths
         where
         -- sᵢⱼ = fᵢfⱼ ^ lᵢⱼ, so need to take max over all of these...
         l : (i j : Fin n) → ℕ
         l i j = pows i j .fst

         k = Max (λ i → Max (l i))

         l≤k : ∀ i j → l i j ≤ k
         l≤k i j = ≤-trans (ind≤Max (l i) j) (ind≤Max (λ i → Max (l i)) i)

         sPath : ∀ i j → s i j ≡ (f i · f j) ^ l i j
         sPath i j = pows i j .snd

         -- the path we get from our assumptions spelled out and cleaned up
         assumPath : ∀ i j
                   → r i · f j ^ m · (f i · f j) ^ (m +ℕ l i j)
                   ≡ r j · f i ^ m · (f i · f j) ^ (m +ℕ l i j)
         assumPath i j =
             r i · f j ^ m · (f i · f j) ^ (m +ℕ l i j)

           ≡⟨ cong (r i · f j ^ m ·_) (sym (·-of-^-is-^-of-+ _ _ _)) ⟩

             r i · f j ^ m · ((f i · f j) ^ m · (f i · f j) ^ l i j)

           ≡⟨ solve! R' ⟩

             (f i · f j) ^ l i j · r i · f j ^ m · (f i · f j) ^ m

           ≡⟨ cong (λ a → a · r i · f j ^ m · (f i · f j) ^ m) (sym (sPath i j)) ⟩

             s i j · r i · f j ^ m · (f i · f j) ^ m

           ≡⟨ sIsAnn i j ⟩

             s i j · r j · f i ^ m · (f i · f j) ^ m

           ≡⟨ cong (λ a → a · r j · f i ^ m · (f i · f j) ^ m) (sPath i j) ⟩

            (f i · f j) ^ l i j  · r j · f i ^ m · (f i · f j) ^ m

           ≡⟨ sym (solve! R') ⟩

             r j · f i ^ m · ((f i · f j) ^ m · (f i · f j) ^ l i j)

           ≡⟨ cong (r j · f i ^ m ·_) (·-of-^-is-^-of-+ _ _ _) ⟩

             r j · f i ^ m · (f i · f j) ^ (m +ℕ l i j) ∎

         paths : ∀ i j → r i · f j ^ m · (f i · f j) ^ (m +ℕ k)
                        ≡ r j · f i ^ m · (f i · f j) ^ (m +ℕ k)
         paths i j =
             r i · f j ^ m · (f i · f j) ^ (m +ℕ k)

           ≡⟨ cong (λ x → r i · f j ^ m · (f i · f j) ^ (m +ℕ x))
                   (sym (≤-∸-+-cancel (l≤k i j))) ⟩

             r i · f j ^ m · (f i · f j) ^ (m +ℕ (k ∸ l i j +ℕ l i j))

           ≡⟨ cong (λ x → r i · f j ^ m · (f i · f j) ^ x)
                   (cong (m +ℕ_) (+ℕ-comm _ _) ∙ +ℕ-assoc _ _ _) ⟩

             r i · f j ^ m · (f i · f j) ^ (m +ℕ l i j +ℕ (k ∸ l i j))

           ≡⟨ cong (r i · f j ^ m ·_) (sym (·-of-^-is-^-of-+ _ _ _)) ⟩

             r i · f j ^ m · ((f i · f j) ^ (m +ℕ l i j) · (f i · f j) ^ (k ∸ l i j))

           ≡⟨ ·Assoc _ _ _ ⟩

             r i · f j ^ m · (f i · f j) ^ (m +ℕ l i j) · (f i · f j) ^ (k ∸ l i j)

           ≡⟨ cong (_· (f i · f j) ^ (k ∸ l i j)) (assumPath i j) ⟩

             r j · f i ^ m · (f i · f j) ^ (m +ℕ l i j) · (f i · f j) ^ (k ∸ l i j)

           ≡⟨ sym (·Assoc _ _ _) ⟩

             r j · f i ^ m · ((f i · f j) ^ (m +ℕ l i j) · (f i · f j) ^ (k ∸ l i j))

           ≡⟨ cong (r j · f i ^ m ·_) (·-of-^-is-^-of-+ _ _ _) ⟩

             r j · f i ^ m · (f i · f j) ^ (m +ℕ l i j +ℕ (k ∸ l i j))

           ≡⟨ cong (λ x → r j · f i ^ m · (f i · f j) ^ x)
                   (sym (+ℕ-assoc _ _ _) ∙ cong (m +ℕ_) (+ℕ-comm _ _)) ⟩

             r j · f i ^ m · (f i · f j) ^ (m +ℕ (k ∸ l i j +ℕ l i j))

           ≡⟨ cong (λ x → r j · f i ^ m · (f i · f j) ^ (m +ℕ x))
                    (≤-∸-+-cancel (l≤k i j)) ⟩

             r j · f i ^ m · (f i · f j) ^ (m +ℕ k) ∎



 -- this will do all the heavy lifting
 equalizerLemma : 1r ∈ ⟨f₀,⋯,fₙ⟩
                → ∀ (x : (i : Fin n) → R[1/ f i ]) -- s.t.
                → (∀ i j → χˡ i j .fst (x i) ≡ χʳ i j .fst (x j))
                → ∃![ y ∈ R ] (∀ i → y /1ˢ ≡ x i)
 equalizerLemma 1∈⟨f₀,⋯,fₙ⟩ = χ≡PropElim isProp∃! baseCase
   where
   baseCase : ∀ (r : FinVec R n) (m l : ℕ)
            → (∀ i j → r i · f j ^ m · (f i · f j) ^ l ≡ r j · f i ^ m · (f i · f j) ^ l)
            → ∃![ y ∈ R ] (∀ i → y /1ˢ ≡ [ r i , f i ^ m , ∣ m , refl ∣₁ ])
   baseCase r m l <Paths = PT.rec isProp∃! Σhelper (GeneratingPowers.thm R' 2m+l _ _ 1∈⟨f₀,⋯,fₙ⟩)
     where
     -- critical exponent
     2m+l = m +ℕ (m +ℕ l)

     f²ᵐ⁺ˡ : FinVec R n
     f²ᵐ⁺ˡ i = f i ^ 2m+l

     Σhelper : Σ[ α ∈ FinVec R n ] 1r ≡ linearCombination R' α f²ᵐ⁺ˡ
             → ∃![ y ∈ R ] (∀ i → y /1ˢ ≡ [ r i , f i ^ m , ∣ m , refl ∣₁ ])
     Σhelper (α , linCombi) = (z , z≡r/fᵐ)
                            , λ y' → Σ≡Prop (λ _ → isPropΠ (λ _ → squash/ _ _)) (unique _ (y' .snd))
       where
       z = ∑ λ i → α i · r i · f i ^ (m +ℕ l)

       z≡r/fᵐ : ∀ i → (z /1ˢ) ≡ [ r i , f i ^ m , ∣ m , refl ∣₁ ]
       z≡r/fᵐ i = eq/ _ _ ((f i ^ (m +ℕ l) , ∣ m +ℕ l , refl ∣₁) , path)
         where
         useSolver1 : ∀ a b c d e g → (a · b) · (c · d · (e · g)) · a
                                    ≡ c · (d · a · (b · g)) · (a · e)
         useSolver1 a b c d e g = solve! R'

         useSolver2 : ∀ a b c d e g → a · (b · c · (d · e)) · (g · c)
                                    ≡ (g · d) · b · (a · (c · (c · e)))
         useSolver2 a b c d e g = solve! R'

         path : f i ^ (m +ℕ l) · z · f i ^ m ≡ f i ^ (m +ℕ l) · r i · 1r
         path =
             f i ^ (m +ℕ l) · z · f i ^ m

           ≡⟨ cong (_· f i ^ m) (∑Mulrdist _ _) ⟩

             (∑ λ j → f i ^ (m +ℕ l) · (α j · r j · f j ^ (m +ℕ l))) · f i ^ m

           ≡⟨ ∑Mulldist _ _ ⟩

             (∑ λ j → f i ^ (m +ℕ l) · (α j · r j · f j ^ (m +ℕ l)) · f i ^ m)

           ≡⟨ ∑Ext (λ j → cong₂ (λ x y → x · (α j · r j · y) · f i ^ m)
                                (sym (·-of-^-is-^-of-+ (f i) m l))
                                (sym (·-of-^-is-^-of-+ (f j) m l))) ⟩

             (∑ λ j → (f i ^ m · f i ^ l) · (α j · r j · (f j ^ m · f j ^ l)) · f i ^ m)

           ≡⟨ ∑Ext (λ j → useSolver1 (f i ^ m) (f i ^ l) (α j) (r j) (f j ^ m) (f j ^ l)) ⟩

             (∑ λ j → α j · (r j · f i ^ m · (f i ^ l · f j ^ l)) · (f i ^ m · f j ^ m))

           ≡⟨ ∑Ext (λ j → cong₂ (λ x y → α j · (r j · f i ^ m · x) · y)
                                (sym (^-ldist-· (f i) (f j) l))
                                (sym (^-ldist-· (f i) (f j) m))) ⟩

             (∑ λ j → α j · (r j · f i ^ m · (f i · f j) ^ l) · (f i · f j) ^ m)

           ≡⟨ ∑Ext (λ j → cong (λ x → α j · x · (f i · f j) ^ m) (sym (<Paths i j))) ⟩

             (∑ λ j → α j · (r i · f j ^ m · (f i · f j) ^ l) · (f i · f j) ^ m)

           ≡⟨ ∑Ext (λ j → cong₂ (λ x y → α j · (r i · f j ^ m · x) · y)
                                (^-ldist-· (f i) (f j) l)
                                (^-ldist-· (f i) (f j) m)) ⟩

             (∑ λ j → α j · (r i · f j ^ m · (f i ^ l · f j ^ l)) · (f i ^ m · f j ^ m))

           ≡⟨ ∑Ext (λ j → useSolver2 (α j) (r i) (f j ^ m) (f i ^ l) (f j ^ l) (f i ^ m)) ⟩

             (∑ λ j → (f i ^ m · f i ^ l) · r i · (α j · (f j ^ m · (f j ^ m · f j ^ l))))

           ≡⟨ sym (∑Mulrdist _ _) ⟩

             (f i ^ m · f i ^ l) · r i · (∑ λ j → α j · (f j ^ m · (f j ^ m · f j ^ l)))

           ≡⟨ cong₂ (λ x y → (x · r i) · y)
                    (·-of-^-is-^-of-+ (f i) m l)
                    (∑Ext (λ j → cong (α j ·_)
                                      (cong (f j ^ m ·_) (·-of-^-is-^-of-+ (f j) m l) ∙
                                                         (·-of-^-is-^-of-+ (f j) m (m +ℕ l))))) ⟩

             f i ^ (m +ℕ l) · r i · (∑ λ j → α j · (f j ^ 2m+l))

           ≡⟨ cong (f i ^ (m +ℕ l) · r i ·_) (sym linCombi) ⟩

             f i ^ (m +ℕ l) · r i · 1r ∎

       unique : ∀ y → (∀ i → (y /1ˢ) ≡ [ r i , f i ^ m , ∣ m , refl ∣₁ ]) → z ≡ y
       unique y y≡r/fᵐ = equalByDifference _ _ (injectivityLemma 1∈⟨f₀,⋯,fₙ⟩ (z - y) [z-y]/1≡0)
         where
         [z-y]/1≡0 : ∀ i → (z - y) /1ˢ ≡ 0at i
         [z-y]/1≡0 i =
             (z - y) /1ˢ

           ≡⟨ U./1AsCommRingHom i .snd .pres+ _ _ ⟩ -- (-a)/1=-(a/1) by refl

             z /1ˢ - y /1ˢ

           ≡⟨ cong₂ (_-_) (z≡r/fᵐ i) (y≡r/fᵐ i) ⟩

             [ r i , f i ^ m , ∣ m , refl ∣₁ ] - [ r i , f i ^ m , ∣ m , refl ∣₁ ]

           ≡⟨ +InvR ([ r i , f i ^ m , ∣ m , refl ∣₁ ]) ⟩

             0at i ∎
           where
           instance _ = L.S⁻¹RAsCommRing i .snd
           open IsRingHom



{-
 Putting everything together with the limit machinery:
 If ⟨ f₁ , ... , fₙ ⟩ = R, then R = lim { R[1/fᵢ] → R[1/fᵢfⱼ] ← R[1/fⱼ] }
-}
 open Category (CommRingsCategory {ℓ})
 open Cone
 open Functor

 locDiagram : Functor (DLShfDiag n ℓ) CommRingsCategory
 F-ob locDiagram (sing i) = R[1/ f i ]AsCommRing
 F-ob locDiagram (pair i j _) = R[1/ f i · f j ]AsCommRing
 F-hom locDiagram idAr = idCommRingHom _
 F-hom locDiagram singPairL = χˡ _ _
 F-hom locDiagram singPairR = χʳ _ _
 F-id locDiagram = refl
 F-seq locDiagram idAr _ = sym (⋆IdL _)
 F-seq locDiagram singPairL idAr = sym (⋆IdR _)
 F-seq locDiagram singPairR idAr = sym (⋆IdR _)

 locCone : Cone locDiagram R'
 coneOut locCone (sing i) = U./1AsCommRingHom i
 coneOut locCone (pair i j _) = UP./1AsCommRingHom i j
 coneOutCommutes locCone idAr = ⋆IdR _
 coneOutCommutes locCone singPairL = RingHom≡ (χˡUnique _ _ .fst .snd)
 coneOutCommutes locCone singPairR = RingHom≡ (χʳUnique _ _ .fst .snd)

 isLimConeLocCone : 1r ∈ ⟨f₀,⋯,fₙ⟩ → isLimCone _ _ locCone
 isLimConeLocCone 1∈⟨f₀,⋯,fₙ⟩ A' cᴬ = (ψ , isConeMorψ) , ψUniqueness
   where
   A = fst A'
   instance
    _ = snd A'

   φ : (i : Fin n) → CommRingHom A' R[1/ f i ]AsCommRing
   φ i = cᴬ .coneOut (sing i)

   applyEqualizerLemma : ∀ a → ∃![ r ∈ R ] ∀ i → r /1ˢ ≡ φ i .fst a
   applyEqualizerLemma a = equalizerLemma 1∈⟨f₀,⋯,fₙ⟩ (λ i → φ i .fst a) (χ≡Elim<Only _ χφSquare<)
    where
    χφSquare< : ∀ i j → i < j → χˡ i j .fst (φ i .fst a) ≡ χʳ i j .fst (φ j .fst a)
    χφSquare< i j i<j =
      χˡ i j .fst (φ i .fst a)          ≡⟨ cong (_$r a) (cᴬ .coneOutCommutes singPairL) ⟩
      cᴬ .coneOut (pair i j i<j) .fst a ≡⟨ cong (_$r a) (sym (cᴬ .coneOutCommutes singPairR)) ⟩
      χʳ i j .fst (φ j .fst a)          ∎


   ψ : CommRingHom A' R'
   fst ψ a = applyEqualizerLemma a .fst .fst
   snd ψ = makeIsRingHom
            (cong fst (applyEqualizerLemma 1r .snd (1r , 1Coh)))
              (λ x y → cong fst (applyEqualizerLemma (x + y) .snd (_ , +Coh x y)))
                λ x y → cong fst (applyEqualizerLemma (x · y) .snd (_ , ·Coh x y))
     where
     open IsRingHom
     1Coh : ∀ i → (1r /1ˢ ≡ φ i .fst 1r)
     1Coh i = sym (φ i .snd .pres1)

     +Coh : ∀ x y i → ((fst ψ x + fst ψ y) /1ˢ ≡ φ i .fst (x + y))
     +Coh x y i = let instance _ = snd R[1/ f i ]AsCommRing in
             U./1AsCommRingHom i .snd .pres+ _ _
          ∙∙ cong₂ _+_ (applyEqualizerLemma x .fst .snd i) (applyEqualizerLemma y .fst .snd i)
          ∙∙ sym (φ i .snd .pres+ x y)

     ·Coh : ∀ x y i → ((fst ψ x · fst ψ y) /1ˢ ≡ φ i .fst (x · y))
     ·Coh x y i = let instance _ = snd R[1/ f i ]AsCommRing in
             U./1AsCommRingHom i .snd .pres· _ _
          ∙∙ cong₂ _·_ (applyEqualizerLemma x .fst .snd i) (applyEqualizerLemma y .fst .snd i)
          ∙∙ sym (φ i .snd .pres· x y)

   -- TODO: Can you use lemma from other PR to eliminate pair case
   isConeMorψ : isConeMor cᴬ locCone ψ
   isConeMorψ (sing i) = RingHom≡ (funExt (λ a → applyEqualizerLemma a .fst .snd i))
   isConeMorψ (pair i j i<j) =
     ψ ⋆ UP./1AsCommRingHom i j         ≡⟨ cong (ψ ⋆_) (sym (RingHom≡ (χˡUnique _ _ .fst .snd))) ⟩
     ψ ⋆ U./1AsCommRingHom i ⋆ χˡ i j   ≡⟨ sym (⋆Assoc _ _ _) ⟩
     (ψ ⋆ U./1AsCommRingHom i) ⋆ χˡ i j ≡⟨ cong (_⋆ χˡ i j) (isConeMorψ (sing i)) ⟩
     φ i ⋆ χˡ i j                       ≡⟨ coneOutCommutes cᴬ singPairL ⟩
     coneOut cᴬ (pair i j i<j)          ∎

   ψUniqueness : (y : Σ[ θ ∈ CommRingHom A' R' ] isConeMor cᴬ locCone θ) → (ψ , isConeMorψ) ≡ y
   ψUniqueness (θ , isConeMorθ) = Σ≡Prop (λ _ → isPropIsConeMor _ _ _)
     (RingHom≡ (funExt λ a → cong fst (applyEqualizerLemma a .snd (θtriple a))))
     where
     θtriple : (a : A) → Σ[ x ∈ R ] ∀ i → x /1ˢ ≡ φ i .fst a
     θtriple a = fst θ a , λ i → cong (_$r a) (isConeMorθ (sing i))
