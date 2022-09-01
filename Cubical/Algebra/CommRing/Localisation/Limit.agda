{-

  This file contains a proof of the following fact:
  For a commutative ring R with elements f₁ , ... , fₙ ∈ R such that
  ⟨ f₁ , ... , fₙ ⟩ = ⟨ 1 ⟩ = R we get an (exact) equalizer diagram of the following form:

      0 → R → ∏ᵢ R[1/fᵢ] ⇉ ∏ᵢⱼ R[1/fᵢfⱼ]

  where the two maps ∏ᵢ R[1/fᵢ] → ∏ᵢⱼ R[1/fᵢfⱼ] are induced by the two canonical maps
  R[1/fᵢ] → R[1/fᵢfⱼ] and R[1/fⱼ] → R[1/fᵢfⱼ].

  But expressed as limits, that's what we need for structure sheaf
  in the case n=2 this will give us what is in Localisation.Pullback

-}




{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommRing.Localisation.Limit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset renaming (_∈_ to _∈ₚ_)
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Nat.Order hiding (_<_ ; _≟_)
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Data.FinData.Order renaming (_<'Fin_ to _<_ ; _≟Fin_ to _≟_)

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Algebra.CommRing.Localisation.UniversalProperty
open import Cubical.Algebra.CommRing.Localisation.InvertingElements
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.RadicalIdeal
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Semilattice.Instances.NatMax

-- open import Cubical.Tactics.NatSolver.Reflection renaming (solve to natSolve)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.DistLatticeSheaf.Diagram

open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level


-- TODO: deal with case zero later
module _ (R' : CommRing ℓ) {n : ℕ} (f : FinVec (fst R') (suc n)) where
 open isMultClosedSubset
 open CommRingTheory R'
 open RingTheory (CommRing→Ring R')
 open Sum (CommRing→Ring R')
 open CommIdeal R' hiding (subst-∈)
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

  -- a lot of syntax to make things readable
  0at : (i : Fin (suc n)) →  R[1/ (f i) ]
  0at i = R[1/ (f i) ]AsCommRing .snd .CommRingStr.0r

  _/1ˢ : R → {i : Fin (suc n)} →  R[1/ (f i) ]
  (r /1ˢ) {i = i} = U._/1 i r

  _/1ᵖ : R → {i j : Fin (suc n)} →  R[1/ (f i) · (f j) ]
  (r /1ᵖ) {i = i} {j = j} = UP._/1 i j r



 -- to be upstreamed; should probably go to PropTrunc.Properties
 recFin : {m : ℕ} {P : Fin m → Type ℓ'}
          {B : Type ℓ''} (isPropB : isProp B)
        → ((∀ i → P i) → B)
       ---------------------
        → ((∀ i → ∥ P i ∥₁) → B)
 recFin {m = zero} _ untruncHyp _ = untruncHyp (λ ())
 recFin {m = suc m} {P = P} {B = B} isPropB untruncHyp truncFam =
   curriedishTrunc (truncFam zero) (truncFam ∘ suc)
   where
   curriedish : P zero → (∀ i → ∥ P (suc i) ∥₁) → B
   curriedish p₀ truncFamSuc = recFin isPropB
                              (λ famSuc → untruncHyp (λ { zero → p₀ ; (suc i) → famSuc i }))
                                truncFamSuc

   curriedishTrunc : ∥ P zero ∥₁ → (∀ i → ∥ P (suc i) ∥₁) → B
   curriedishTrunc = PT.rec (isProp→ isPropB) curriedish

 recFin2 : {m1 m2 : ℕ} {P : Fin m1 → Fin m2 → Type ℓ'}
           {B : Type ℓ''} (isPropB : isProp B)
         → ((∀ i j → P i j) → B)
        --------------------------
         → (∀ i j → ∥ P i j ∥₁)
         → B
 recFin2 {m1 = zero} _ untruncHyp _ = untruncHyp λ ()
 recFin2 {m1 = suc m1} {P = P} {B = B} isPropB untruncHyp truncFam =
   curriedishTrunc (truncFam zero) (truncFam ∘ suc)
   where
   curriedish : (∀ j → P zero j) → (∀ i j → ∥ P (suc i) j ∥₁) → B
   curriedish p₀ truncFamSuc = recFin2 isPropB
                              (λ famSuc → untruncHyp λ { zero → p₀ ; (suc i) → famSuc i })
                                truncFamSuc

   curriedishTrunc : (∀ j → ∥ P zero j ∥₁) → (∀ i j → ∥ P (suc i) j ∥₁) → B
   curriedishTrunc = recFin (isProp→ isPropB) curriedish






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
    u : FinVec R (suc n)
    u i = ann i .fst .fst

    uIsPower : ∀ i → u i ∈ₚ [ (f i) ⁿ|n≥0]
    uIsPower i = ann i .fst .snd

    ux≡0 : ∀ i → u i · x ≡ 0r
    ux≡0 i = sym (·IdR _) ∙ ann i .snd ∙ cong (_· 1r) (0RightAnnihilates _) ∙ (·IdR _)

    exponentHelper : (∀ i → Σ[ m ∈ ℕ ] u i ≡ f i ^ m)
                   → x ≡ 0r
    exponentHelper pows = PT.rec (is-set _ _) Σhelper (GeneratingPowers.thm R' l _ _ 1∈⟨f₀,⋯,fₙ⟩)
      where
      m : FinVec ℕ (suc n)
      m i = pows i .fst

      u≡fᵐ : ∀ i → u i ≡ f i ^ m i
      u≡fᵐ i = pows i .snd

      l = Max m

      fˡ : FinVec R (suc n)
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


      Σhelper : Σ[ α ∈ FinVec R (suc n) ] 1r ≡ ∑ (λ i → α i · f i ^ l)
              → x ≡ 0r
      Σhelper (α , 1≡∑αfˡ) =
        x                                   ≡⟨ sym (·IdL _) ⟩
        1r · x                              ≡⟨ cong (_· x) 1≡∑αfˡ ⟩
        ∑ (λ i → α i · f i ^ l) · x         ≡⟨ ∑Mulldist _ _ ⟩
        ∑ (λ i → α i · f i ^ l · x)         ≡⟨ ∑Ext (λ i → sym (·Assoc (α i)
                                                                  (f i ^ l) x)) ⟩
        ∑ (λ i → α i · (f i ^ l · x))       ≡⟨ ∑Ext (λ i → cong (α i ·_) (fˡx≡0 i)) ⟩
        ∑ (λ i → α i · 0r)                  ≡⟨ ∑Ext (λ i → 0RightAnnihilates (α i)) ⟩
        ∑ (replicateFinVec (suc n) 0r)      ≡⟨ ∑0r (suc n) ⟩
        0r ∎


 -- the morphisms into localisations at products from the left/right
 -- we need to define them by hand as using RadicalLemma wouldn't compute later
 χˡ : (i j : Fin (suc n)) → CommRingHom R[1/ f i ]AsCommRing
                                        R[1/ f i · f j ]AsCommRing
 χˡ i j = U.S⁻¹RHasUniversalProp i _ (UP./1AsCommRingHom i j) unitHelper .fst .fst
   where
   unitHelper : ∀ s → s ∈ₚ [ (f i) ⁿ|n≥0] → s /1ᵖ ∈ₚ (R[1/ f i · f j ]AsCommRing) ˣ
   unitHelper = powersPropElim (λ s → Units.inverseUniqueness _ (s /1ᵖ))
                  λ m → [ f j ^ m , (f i · f j) ^ m , ∣ m , refl ∣₁ ]
                        , eq/ _ _ ((1r , powersFormMultClosedSubset (f i · f j) .containsOne)
                        , path m)
     where
     useSolver1 : ∀ a b → 1r · (a · b) · 1r ≡ a · b
     useSolver1 = solve R'
     useSolver2 : ∀ a → a ≡ (1r · 1r) · (1r · a)
     useSolver2 = solve R'

     path : (n : ℕ) → 1r · (f i ^ n · f j ^ n) · 1r ≡ (1r · 1r) · (1r · ((f i · f j) ^ n))
     path n = useSolver1 _ _ ∙ sym (^-ldist-· (f i) (f j) n) ∙ useSolver2 _


 χʳ : (i j : Fin (suc n)) → CommRingHom R[1/ f j ]AsCommRing
                                        R[1/ f i · f j ]AsCommRing
 χʳ i j = U.S⁻¹RHasUniversalProp j _ (UP./1AsCommRingHom i j) unitHelper .fst .fst
   where
   unitHelper : ∀ s → s ∈ₚ [ (f j) ⁿ|n≥0] → s /1ᵖ ∈ₚ (R[1/ f i · f j ]AsCommRing) ˣ
   unitHelper = powersPropElim (λ s → Units.inverseUniqueness _ (s /1ᵖ))
                  λ m → [ f i ^ m , (f i · f j) ^ m , ∣ m , refl ∣₁ ]
                        , eq/ _ _ ((1r , powersFormMultClosedSubset (f i · f j) .containsOne)
                        , path m)
     where
     useSolver1 : ∀ a b → 1r · (a · b) · 1r ≡ b · a
     useSolver1 = solve R'
     useSolver2 : ∀ a → a ≡ (1r · 1r) · (1r · a)
     useSolver2 = solve R'

     path : (n : ℕ) → 1r · (f j ^ n · f i ^ n) · 1r ≡ (1r · 1r) · (1r · ((f i · f j) ^ n))
     path n = useSolver1 _ _ ∙ sym (^-ldist-· (f i) (f j) n) ∙ useSolver2 _


 -- super technical stuff, please don't look at it
 χSwap : ∀ i j → χˡ i j ≡ subst (λ r → CommRingHom R[1/ f i ]AsCommRing R[1/ r ]AsCommRing)
                                 (·Comm (f j) (f i)) (χʳ j i)
 χSwap i j = RingHom≡ (funExt (invElPropElim (λ _ → squash/ _ _)
     λ r m → cong [_]
              (ΣPathP (sym (transportRefl _ ∙ cong (_· transport refl (f j ^ m)) (transportRefl _))
                , Σ≡Prop (∈-isProp _)
              (sym (transportRefl _ ∙ cong (λ x → 1r · transport refl (x ^ m)) (·Comm _ _)))))))

 χ<To≡ : (x  : (i : Fin (suc n)) → R[1/ f i ])
       → (∀ {i} {j} → i < j → χˡ i j .fst (x i) ≡ χʳ i j .fst (x j))
       → ∀ i j → χˡ i j .fst (x i) ≡ χʳ i j .fst (x j)
 χ<To≡ x <hyp i j = {!i ≟ j!}
   where
   aux : i ≟ j → χˡ i j .fst (x i) ≡ χʳ i j .fst (x j)
   aux a = ?
 -- takes forever to type check
 -- with (i ≟Fin j)
 -- ... | (lt i<j) = ?
 -- ... | (eq i≡j) = ?
 -- ... | (gt j<i) = ?

 -- to be upstreamed / what should it be called
 -- recFin< : {m : ℕ} {P : {i j : Fin m} → i < j → Type ℓ'}
 --            {B : Type ℓ''} (isPropB : isProp B)
 --          → ((∀ {i} {j} (i<j : i < j) → P i<j) → B)
 --         ---------------------------------------------------
 --          → ((∀ {i} {j} (i<j : i < j) → ∥ P i<j ∥₁) → B)
 -- recFin< {m = zero} isPropB untruncHyp truncs = untruncHyp (λ {i} → ⊥.rec (¬Fin0 i))
 -- recFin< {m = suc m} {P = P} {B = B} isPropB untruncHyp truncs =
 --   curriedishTrunc (λ 0<j → truncs 0<j) λ i<j → truncs (s≤s i<j)
 --   where
 --   curriedish : (∀ {j} (0<j : zero < j) → P 0<j)
 --              → (∀ {i j : Fin m} (i<j : i < j) → ∥ P (s≤s i<j) ∥₁)
 --              → B
 --   curriedish p₀ truncFamSuc = recFin< isPropB
 --     (λ famSuc → untruncHyp (λ { {i = zero} 0<j → p₀ 0<j
 --                               ; {i = suc i} {j = zero} ()
 --                               ; {i = suc i} {j = suc j} (s≤s i<j) → famSuc i<j}))
 --          truncFamSuc

 --   recFin0< : {m' : ℕ} {P' : {j : Fin (suc m')} → zero < j → Type ℓ'}
 --            {B' : Type ℓ''} (isPropB' : isProp B')
 --          → ((∀ {j} (0<j : zero < j) → P' 0<j) → B')
 --         ---------------------------------------------------
 --          → ((∀ {j} (0<j : zero < j) → ∥ P' 0<j ∥₁) → B')
 --   recFin0< {P' = P'} isPropB' untruncHyp₀ truncs₀ =
 --      recFin {P = λ j → P' (s≤s (z≤ {toℕ (weakenFin j)}))}
 --              isPropB' (λ famSuc → untruncHyp₀
 --                         λ { {j = zero} → λ () ; {j = suc j} (s≤s z≤) → famSuc j})
 --                          λ _ → truncs₀ (s≤s z≤)

 --   curriedishTrunc : (∀ {j} (0<j : zero < j) → ∥ P 0<j ∥₁)
 --                   → (∀ {i j : Fin m} (i<j : i < j) → ∥ P (s≤s i<j) ∥₁)
 --                   → B
 --   curriedishTrunc = recFin0< {m' = m} (isProp→ isPropB) curriedish



 -- -- very technical stuff
 -- MaxOver< : {m : ℕ} (f : {i j : Fin m} → i < j → ℕ) → ℕ
 -- MaxOver< {m = zero} f = 0
 -- MaxOver< {m = suc m} f = max (Max {n = m} (λ i → f {i = zero} {j = suc i} (s≤s z≤)))
 --                              (MaxOver< (f ∘ s≤s))

 -- ind≤MaxOver< : ∀ {m : ℕ} (f : {i j : Fin m} → i < j → ℕ)
 --              → ∀ {i j : Fin m} (i<j : i < j) → f i<j ≤ MaxOver< f
 -- ind≤MaxOver< {m = suc m} f {i = zero} {j = zero} ()
 -- ind≤MaxOver< {m = suc m} f {i = zero} {j = suc j} (s≤s z≤) = ≤-trans (ind≤Max _ _) left-≤-max
 -- ind≤MaxOver< {m = suc m} f {i = suc i} {j = zero} ()
 -- ind≤MaxOver< {m = suc m} f {i = suc i} {j = suc j} (s≤s i<j) =
 --                ≤-trans (ind≤MaxOver< (f ∘ s≤s) i<j) right-≤-max

 χ≡PropElim : {B : ((i : Fin (suc n)) → R[1/ f i ]) → Type ℓ''} (isPropB : ∀ {x} → isProp (B x))
            → (∀ (r : FinVec R (suc n)) (m l : ℕ)
                  → (∀ i j → r i · f j ^ m · (f i · f j) ^ l ≡ r j · f i ^ m · (f i · f j) ^ l)
                  → B (λ i → [ r i , f i ^ m , ∣ m , refl ∣₁ ]))
          -------------------------------------------------------------------------------------
           → (x : (i : Fin (suc n)) → R[1/ f i ])
           → (∀ i j → χˡ i j .fst (x i) ≡ χʳ i j .fst (x j))
           → B x
 χ≡PropElim {B = B} isPropB baseHyp = invElPropElimN n f _ (λ _ → isProp→ isPropB) baseCase
   where
   baseCase : ∀ (r : FinVec R (suc n)) (m : ℕ)
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
       s : (i j : Fin (suc n)) → R
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
         useSolver = solve R'

       exponentHelper : (∀ i j
                           → Σ[ l ∈ ℕ ] s i j ≡ (f i · f j) ^ l)
                      → B (λ i → [ r i , f i ^ m , ∣ m , refl ∣₁ ])
       exponentHelper pows = baseHyp r m (m +ℕ k) paths
         where
         -- sᵢⱼ = fᵢfⱼ ^ lᵢⱼ, so need to take max over all of these...
         l : (i j : Fin (suc n)) → ℕ
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

           ≡⟨ useSolver _ _ _ _ ⟩

             (f i · f j) ^ l i j · r i · f j ^ m · (f i · f j) ^ m

           ≡⟨ cong (λ a → a · r i · f j ^ m · (f i · f j) ^ m) (sym (sPath i j)) ⟩

             s i j · r i · f j ^ m · (f i · f j) ^ m

           ≡⟨ sIsAnn i j ⟩

             s i j · r j · f i ^ m · (f i · f j) ^ m

           ≡⟨ cong (λ a → a · r j · f i ^ m · (f i · f j) ^ m) (sPath i j) ⟩

            (f i · f j) ^ l i j  · r j · f i ^ m · (f i · f j) ^ m

           ≡⟨ sym (useSolver _ _ _ _) ⟩

             r j · f i ^ m · ((f i · f j) ^ m · (f i · f j) ^ l i j)

           ≡⟨ cong (r j · f i ^ m ·_) (·-of-^-is-^-of-+ _ _ _) ⟩

             r j · f i ^ m · (f i · f j) ^ (m +ℕ l i j) ∎
           where
           useSolver : ∀ a b c d → a · b · (c · d) ≡ d · a · b · c
           useSolver = solve R'

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
                → ∀ (x : (i : Fin (suc n)) → R[1/ f i ]) -- s.t.
                → (∀ i j → χˡ i j .fst (x i) ≡ χʳ i j .fst (x j))
                → ∃![ y ∈ R ] (∀ i → y /1ˢ ≡ x i)
 equalizerLemma 1∈⟨f₀,⋯,fₙ⟩ = χ≡PropElim isProp∃! baseCase
   where
   baseCase : ∀ (r : FinVec R (suc n)) (m l : ℕ)
            → (∀ i j → r i · f j ^ m · (f i · f j) ^ l ≡ r j · f i ^ m · (f i · f j) ^ l)
            → ∃![ y ∈ R ] (∀ i → y /1ˢ ≡ [ r i , f i ^ m , ∣ m , refl ∣₁ ])
   baseCase r m l <Paths = PT.rec isProp∃! Σhelper (GeneratingPowers.thm R' 2m+l _ _ 1∈⟨f₀,⋯,fₙ⟩)
     where
     -- critical exponent
     2m+l = m +ℕ (m +ℕ l)

     f²ᵐ⁺ˡ : FinVec R (suc n)
     f²ᵐ⁺ˡ i = f i ^ 2m+l

     Σhelper : Σ[ α ∈ FinVec R (suc n) ] 1r ≡ linearCombination R' α f²ᵐ⁺ˡ
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
         useSolver1 = solve R'

         useSolver2 : ∀ a b c d e g → a · (b · c · (d · e)) · (g · c)
                                    ≡ (g · d) · b · (a · (c · (c · e)))
         useSolver2 = solve R'

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
