{-

 This file contains a proof of the following fact:
 for a commutative ring R with elements f and g s.t.
 ⟨f,g⟩ = R, we get a get a pullback square

                 _/1
            R   ----> R[1/f]
              ⌟
       _/1  |         | χ₁
            v         v

            R[1/g] -> R[1/fg]
                   χ₂

 where the morphisms χ are induced by the universal property
 of localization.

 -}


{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.CommRing.Localisation.PullbackSquare where

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
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Algebra.CommRing.Localisation.UniversalProperty
open import Cubical.Algebra.CommRing.Localisation.InvertingElements
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.RadicalIdeal

open import Cubical.Tactics.CommRingSolver

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.CommRings
open import Cubical.Categories.Limits.Pullback

open Iso

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ


module _ (R' : CommRing ℓ) (f g : (fst R')) where

 open IsRingHom
 open isMultClosedSubset
 open CommRingTheory R'
 open RingTheory (CommRing→Ring R')
 open CommIdeal R'
 open RadicalIdeal R'
 open Exponentiation R'
 open InvertingElementsBase R'

 open CommRingStr ⦃...⦄
 private
  R = R' .fst
  ⟨_⟩ : {n : ℕ} → FinVec R n → CommIdeal
  ⟨ V ⟩ = ⟨ V ⟩[ R' ]
  fgVec : FinVec R 2
  fgVec zero = f
  fgVec (suc zero) = g
  ⟨f,g⟩ = ⟨ fgVec ⟩
  fⁿgⁿVec : (n : ℕ) → FinVec R 2
  fⁿgⁿVec n zero = f ^ n
  fⁿgⁿVec n (suc zero) = g ^ n
  ⟨fⁿ,gⁿ⟩ : (n : ℕ) → CommIdeal
  ⟨fⁿ,gⁿ⟩ n = ⟨ (fⁿgⁿVec n) ⟩

  instance
   _ = R' .snd
   _ = R[1/ f ]AsCommRing .snd
   _ = R[1/ g ]AsCommRing .snd
   _ = R[1/ (R' .snd .CommRingStr._·_ f g) ]AsCommRing .snd

 open Loc R' [ f ⁿ|n≥0] (powersFormMultClosedSubset f)
      renaming (_≈_ to _≈ᶠ_ ; locIsEquivRel to locIsEquivRelᶠ ; S to Sᶠ)
 open S⁻¹RUniversalProp R' [ f ⁿ|n≥0] (powersFormMultClosedSubset f)
      renaming ( _/1 to _/1ᶠ ; /1AsCommRingHom to /1ᶠAsCommRingHom
               ; S⁻¹RHasUniversalProp to R[1/f]HasUniversalProp)
 open Loc R' [ g ⁿ|n≥0] (powersFormMultClosedSubset g)
      renaming (_≈_ to _≈ᵍ_ ; locIsEquivRel to locIsEquivRelᵍ ; S to Sᵍ)
 open S⁻¹RUniversalProp R' [ g ⁿ|n≥0] (powersFormMultClosedSubset g)
      renaming ( _/1 to _/1ᵍ ; /1AsCommRingHom to /1ᵍAsCommRingHom
               ; S⁻¹RHasUniversalProp to R[1/g]HasUniversalProp)
 open Loc R' [ (f · g) ⁿ|n≥0] (powersFormMultClosedSubset (f · g))
      renaming (_≈_ to _≈ᶠᵍ_ ; locIsEquivRel to locIsEquivRelᶠᵍ ; S to Sᶠᵍ)
 open S⁻¹RUniversalProp R' [ (f · g) ⁿ|n≥0] (powersFormMultClosedSubset (f · g))
      renaming ( _/1 to _/1ᶠᵍ ; /1AsCommRingHom to /1ᶠᵍAsCommRingHom)


 -- the pullback legs
 private
  -- using RadicalLemma doesn't compute...
  χ₁ : CommRingHom R[1/ f ]AsCommRing R[1/ (f · g) ]AsCommRing
  χ₁ = R[1/f]HasUniversalProp _ /1ᶠᵍAsCommRingHom unitHelper .fst .fst
   where
   unitHelper : ∀ s → s ∈ₚ [ f ⁿ|n≥0] → s /1ᶠᵍ ∈ₚ (R[1/ (f · g) ]AsCommRing) ˣ
   unitHelper = powersPropElim (λ s → Units.inverseUniqueness _ (s /1ᶠᵍ))
                  λ n → [ g ^ n , (f · g) ^ n , ∣ n , refl ∣₁ ]
                        , eq/ _ _ ((1r , powersFormMultClosedSubset (f · g) .containsOne)
                        , path n)
    where
    path : (n : ℕ) → 1r · (f ^ n · g ^ n) · 1r ≡ (1r · 1r) · (1r · ((f · g) ^ n))
    path n = solve! R' ∙ sym (^-ldist-· f g n) ∙ solve! R'

  χ₂ : CommRingHom R[1/ g ]AsCommRing R[1/ (f · g) ]AsCommRing
  χ₂ = R[1/g]HasUniversalProp _ /1ᶠᵍAsCommRingHom unitHelper .fst .fst
   where
   unitHelper : ∀ s → s ∈ₚ [ g ⁿ|n≥0] → s /1ᶠᵍ ∈ₚ (R[1/ (f · g) ]AsCommRing) ˣ
   unitHelper = powersPropElim (λ s → Units.inverseUniqueness _ (s /1ᶠᵍ))
                  λ n → [ f ^ n , (f · g) ^ n , ∣ n , refl ∣₁ ]
                        , eq/ _ _ ((1r , powersFormMultClosedSubset (f · g) .containsOne)
                              , path n)
    where
    path : (n : ℕ) → 1r · (g ^ n · f ^ n) · 1r ≡ (1r · 1r) · (1r · ((f · g) ^ n))
    path n = solve! R' ∙ sym (^-ldist-· f g n) ∙ solve! R'



 injectivityLemma : 1r ∈ ⟨f,g⟩ → ∀ (x : R) → x /1ᶠ ≡ 0r → x /1ᵍ ≡ 0r → x ≡ 0r
 injectivityLemma 1∈⟨f,g⟩ x x≡0overF x≡0overG =
                    PT.rec2 (is-set _ _) annihilatorHelper exAnnihilatorF exAnnihilatorG
  where
  exAnnihilatorF : ∃[ s ∈ Sᶠ ] (fst s · x · 1r ≡ fst s · 0r · 1r)
  exAnnihilatorF = isEquivRel→TruncIso locIsEquivRelᶠ _ _ .fun x≡0overF

  exAnnihilatorG : ∃[ s ∈ Sᵍ ] (fst s · x · 1r ≡ fst s · 0r · 1r)
  exAnnihilatorG = isEquivRel→TruncIso locIsEquivRelᵍ _ _ .fun x≡0overG

  annihilatorHelper : Σ[ s ∈ Sᶠ ] (fst s · x · 1r ≡ fst s · 0r · 1r)
                    → Σ[ s ∈ Sᵍ ] (fst s · x · 1r ≡ fst s · 0r · 1r)
                    → x ≡ 0r
  annihilatorHelper ((u , u∈[fⁿ]) , p) ((v , v∈[gⁿ]) , q) =
                      PT.rec2 (is-set _ _) exponentHelper u∈[fⁿ] v∈[gⁿ]
   where
   ux≡0 : u · x ≡ 0r
   ux≡0 = sym (·IdR _) ∙ p ∙ cong (_· 1r) (0RightAnnihilates _) ∙ (·IdR _)

   vx≡0 : v · x ≡ 0r
   vx≡0 = sym (·IdR _) ∙ q ∙ cong (_· 1r) (0RightAnnihilates _) ∙ (·IdR _)

   exponentHelper : Σ[ n ∈ ℕ ] u ≡ f ^ n
                  → Σ[ n ∈ ℕ ] v ≡ g ^ n
                  → x ≡ 0r
   exponentHelper (n , u≡fⁿ) (m , v≡gᵐ) =
                   PT.rec (is-set _ _) Σhelper (GeneratingPowers.thm R' l _ fgVec 1∈⟨f,g⟩)
    where
    l = max n m

    fˡx≡0 : f ^ l · x ≡ 0r
    fˡx≡0 = f ^ l · x               ≡⟨ cong (λ k → f ^ k · x) (sym (≤-∸-+-cancel left-≤-max)) ⟩
            f ^ ((l ∸ n) +ℕ n) · x  ≡⟨ cong (_· x) (sym (·-of-^-is-^-of-+ _ _ _)) ⟩
            f ^ (l ∸ n) · f ^ n · x ≡⟨ cong (λ y → f ^ (l ∸ n) · y · x) (sym u≡fⁿ) ⟩
            f ^ (l ∸ n) · u · x     ≡⟨ sym (·Assoc _ _ _) ⟩
            f ^ (l ∸ n) · (u · x)   ≡⟨ cong (f ^ (l ∸ n) ·_) ux≡0 ⟩
            f ^ (l ∸ n) · 0r        ≡⟨ 0RightAnnihilates _ ⟩
            0r ∎

    gˡx≡0 : g ^ l · x ≡ 0r
    gˡx≡0 = g ^ l · x               ≡⟨ cong (λ k → g ^ k · x) (sym (≤-∸-+-cancel right-≤-max)) ⟩
            g ^ ((l ∸ m) +ℕ m) · x  ≡⟨ cong (_· x) (sym (·-of-^-is-^-of-+ _ _ _)) ⟩
            g ^ (l ∸ m) · g ^ m · x ≡⟨ cong (λ y → g ^ (l ∸ m) · y · x) (sym v≡gᵐ) ⟩
            g ^ (l ∸ m) · v · x     ≡⟨ sym (·Assoc _ _ _) ⟩
            g ^ (l ∸ m) · (v · x)   ≡⟨ cong (g ^ (l ∸ m) ·_) vx≡0 ⟩
            g ^ (l ∸ m) · 0r        ≡⟨ 0RightAnnihilates _ ⟩
            0r ∎

    Σhelper : Σ[ α ∈ FinVec R 2 ] 1r ≡ α zero · f ^ l + (α (suc zero) · g ^ l + 0r)
            → x ≡ 0r
    Σhelper (α , 1≡α₀fˡ+α₁gˡ+0) = path
     where
     α₀ = α zero
     α₁ = α (suc zero)

     1≡α₀fˡ+α₁gˡ : 1r ≡ α₀ · f ^ l + α₁ · g ^ l
     1≡α₀fˡ+α₁gˡ = 1≡α₀fˡ+α₁gˡ+0 ∙ cong (α₀ · f ^ l +_) (+IdR _)

     path : x ≡ 0r
     path = x                                   ≡⟨ sym (·IdL _) ⟩
            1r · x                              ≡⟨ cong (_· x) 1≡α₀fˡ+α₁gˡ ⟩
            (α₀ · f ^ l + α₁ · g ^ l) · x       ≡⟨ ·DistL+ _ _ _ ⟩
            α₀ · f ^ l · x + α₁ · g ^ l · x     ≡⟨ cong₂ _+_ (sym (·Assoc _ _ _))
                                                             (sym (·Assoc _ _ _)) ⟩
            α₀ · (f ^ l · x) + α₁ · (g ^ l · x) ≡⟨ cong₂ (λ y z → α₀ · y + α₁ · z)
                                                         fˡx≡0 gˡx≡0 ⟩
            α₀ · 0r + α₁ · 0r                   ≡⟨ cong₂ _+_ (0RightAnnihilates _)
                                                             (0RightAnnihilates _) ∙ +IdR _ ⟩
            0r ∎


 equalizerLemma : 1r ∈ ⟨f,g⟩
                → ∀ (x : R[1/ f ]) (y : R[1/ g ])
                → χ₁ .fst x ≡ χ₂ .fst y
                → ∃![ z ∈ R ] (z /1ᶠ ≡ x) × (z /1ᵍ ≡ y)
 equalizerLemma 1∈⟨f,g⟩ = invElPropElim2 (λ _ _ → isPropΠ (λ _ → isProp∃!)) baseCase
  where
  baseCase : ∀ (x y : R) (n : ℕ)
           → fst χ₁ ([ x , f ^ n , ∣ n , refl ∣₁ ]) ≡ fst χ₂ ([ y , g ^ n , ∣ n , refl ∣₁ ])
           → ∃![ z ∈ R ] ((z /1ᶠ ≡ [ x , f ^ n , ∣ n , refl ∣₁ ])
                        × (z /1ᵍ ≡ [ y , g ^ n , ∣ n , refl ∣₁ ]))
  baseCase x y n χ₁[x/fⁿ]≡χ₂[y/gⁿ] = PT.rec isProp∃! annihilatorHelper exAnnihilator
   where
   -- doesn't compute that well but at least it computes...
   exAnnihilator : ∃[ s ∈ Sᶠᵍ ] -- s.t.
     (fst s · (x · transport refl (g ^ n)) · (1r · transport refl ((f · g) ^ n))
    ≡ fst s · (y · transport refl (f ^ n)) · (1r · transport refl ((f · g) ^ n)))
   exAnnihilator = isEquivRel→TruncIso locIsEquivRelᶠᵍ _ _ .fun χ₁[x/fⁿ]≡χ₂[y/gⁿ]

   annihilatorHelper : Σ[ s ∈ Sᶠᵍ ]
     (fst s · (x · transport refl (g ^ n)) · (1r · transport refl ((f · g) ^ n))
    ≡ fst s · (y · transport refl (f ^ n)) · (1r · transport refl ((f · g) ^ n)))
    → ∃![ z ∈ R ] ((z /1ᶠ ≡ [ x , f ^ n , ∣ n , refl ∣₁ ])
                 × (z /1ᵍ ≡ [ y , g ^ n , ∣ n , refl ∣₁ ]))
   annihilatorHelper ((s , s∈[fgⁿ]) , p) = PT.rec isProp∃! exponentHelper s∈[fgⁿ]
    where
    sxgⁿ[fg]ⁿ≡syfⁿ[fg]ⁿ : s · x · g ^ n · (f · g) ^ n ≡ s · y · f ^ n · (f · g) ^ n
    sxgⁿ[fg]ⁿ≡syfⁿ[fg]ⁿ =
       s · x · g ^ n · (f · g) ^ n

      ≡⟨ transpHelper _ _ _ _ ⟩

       s · x · transport refl (g ^ n) · transport refl ((f · g) ^ n)

      ≡⟨ useSolver _ _ _ _ ⟩

       s · (x · transport refl (g ^ n)) · (1r · transport refl ((f · g) ^ n))

      ≡⟨ p ⟩

       s · (y · transport refl (f ^ n)) · (1r · transport refl ((f · g) ^ n))

      ≡⟨ sym (useSolver _ _ _ _) ⟩

       s · y · transport refl (f ^ n) · transport refl ((f · g) ^ n)

      ≡⟨ sym (transpHelper _ _ _ _) ⟩

       s · y · f ^ n · (f · g) ^ n ∎

      where
      transpHelper : ∀ a b c d → a · b · c · d
                               ≡ a · b · transport refl c · transport refl d
      transpHelper a b c d i = a · b · transportRefl c (~ i) · transportRefl d (~ i)
      useSolver : ∀ a b c d → a · b · c · d ≡ a · (b · c) · (1r · d)
      useSolver _ _ _ _ = solve! R'


    exponentHelper : Σ[ m ∈ ℕ ] s ≡ (f · g) ^ m
                   → ∃![ z ∈ R ] ((z /1ᶠ ≡ [ x , f ^ n , ∣ n , refl ∣₁ ])
                                × (z /1ᵍ ≡ [ y , g ^ n , ∣ n , refl ∣₁ ]))
    exponentHelper (m , s≡[fg]ᵐ) =
       PT.rec isProp∃! Σhelper (GeneratingPowers.thm R' 2n+m _ fgVec 1∈⟨f,g⟩)
     where
     -- the path we'll actually work with
     xgⁿ[fg]ⁿ⁺ᵐ≡yfⁿ[fg]ⁿ⁺ᵐ : x · g ^ n · (f · g) ^ (n +ℕ m) ≡ y · f ^ n · (f · g) ^ (n +ℕ m)
     xgⁿ[fg]ⁿ⁺ᵐ≡yfⁿ[fg]ⁿ⁺ᵐ =
        x · g ^ n · (f · g) ^ (n +ℕ m)

       ≡⟨ cong (x · (g ^ n) ·_) (sym (·-of-^-is-^-of-+ _ _ _)) ⟩

        x · g ^ n · ((f · g) ^ n · (f · g) ^ m)

       ≡⟨ useSolver _ _ _ _ ⟩

         (f · g) ^ m · x · g ^ n · (f · g) ^ n

       ≡⟨ cong (λ a → a · x · g ^ n · (f · g) ^ n) (sym s≡[fg]ᵐ) ⟩

         s · x · g ^ n · (f · g) ^ n

       ≡⟨ sxgⁿ[fg]ⁿ≡syfⁿ[fg]ⁿ ⟩

         s · y · f ^ n · (f · g) ^ n

       ≡⟨ cong (λ a → a · y · f ^ n · (f · g) ^ n) s≡[fg]ᵐ ⟩

         (f · g) ^ m · y · f ^ n · (f · g) ^ n

       ≡⟨ sym (useSolver _ _ _ _)  ⟩

         y · f ^ n · ((f · g) ^ n · (f · g) ^ m)

       ≡⟨ cong (y · (f ^ n) ·_) (·-of-^-is-^-of-+ _ _ _) ⟩

        y · f ^ n · (f · g) ^ (n +ℕ m) ∎

       where
       useSolver : ∀ a b c d → a · b · (c · d) ≡ d · a · b · c
       useSolver _ _ _ _ = solve! R'

     -- critical exponent
     2n+m = n +ℕ (n +ℕ m)
     -- extracting information from the fact that R=⟨f,g⟩
     Σhelper : Σ[ α ∈ FinVec R 2 ] 1r ≡ linearCombination R' α (fⁿgⁿVec 2n+m)
             → ∃![ z ∈ R ] ((z /1ᶠ ≡ [ x , f ^ n , ∣ n , refl ∣₁ ])
                          × (z /1ᵍ ≡ [ y , g ^ n , ∣ n , refl ∣₁ ]))
     Σhelper (α , linCombi) = uniqueExists z (z/1≡x/fⁿ , z/1≡y/gⁿ)
                                             (λ _ → isProp× (is-set _ _) (is-set _ _))
                                             uniqueness
      where
      α₀ = α zero
      α₁ = α (suc zero)

      1≡α₀f²ⁿ⁺ᵐ+α₁g²ⁿ⁺ᵐ : 1r ≡ α₀ · f ^ 2n+m + α₁ · g ^ 2n+m
      1≡α₀f²ⁿ⁺ᵐ+α₁g²ⁿ⁺ᵐ = linCombi ∙ cong (α₀ · f ^ 2n+m +_) (+IdR _)

      -- definition of the element
      z = α₀ · x · f ^ (n +ℕ m) + α₁ · y · g ^ (n +ℕ m)

      z/1≡x/fⁿ : (z /1ᶠ) ≡ [ x , f ^ n , ∣ n , refl ∣₁ ]
      z/1≡x/fⁿ = eq/ _ _ ((f ^ (n +ℕ m) , ∣ n +ℕ m , refl ∣₁) , path)
       where
       path : f ^ (n +ℕ m) · z · f ^ n ≡ f ^ (n +ℕ m) · x · 1r
       path =
           f ^ (n +ℕ m) · z · f ^ n

         ≡⟨ solve! R' ⟩

           f ^ (n +ℕ m) · (α₀ · x · (f ^ n · f ^ (n +ℕ m))) + α₁ · (y · f ^ n · (f ^ (n +ℕ m) · g ^ (n +ℕ m)))

         ≡⟨ cong₂ (λ a b → f ^ (n +ℕ m) · (α₀ · x · a) + α₁ · ((y · f ^ n) · b))
                  (·-of-^-is-^-of-+ _ _ _) (sym (^-ldist-· _ _ _)) ⟩

           f ^ (n +ℕ m) · (α₀ · x · (f ^ 2n+m)) + α₁ · (y · f ^ n · (f · g) ^ (n +ℕ m))

         ≡⟨ cong (λ a → f ^ (n +ℕ m) · (α₀ · x · f ^ 2n+m) + α₁ · a)
                 (sym xgⁿ[fg]ⁿ⁺ᵐ≡yfⁿ[fg]ⁿ⁺ᵐ) ⟩

           f ^ (n +ℕ m) · (α₀ · x · (f ^ 2n+m)) + α₁ · (x · g ^ n · (f · g) ^ (n +ℕ m))

         ≡⟨ cong (λ a → f ^ (n +ℕ m) · (α₀ · x · (f ^ 2n+m)) + α₁ · (x · g ^ n · a)) (^-ldist-· _ _ _)  ⟩

           f ^ (n +ℕ m) · (α₀ · x · (f ^ 2n+m)) + α₁ · (x · g ^ n · (f ^ (n +ℕ m) · g ^ (n +ℕ m)))

         ≡⟨ cong (λ a → f ^ (n +ℕ m) · (α₀ · x · (f ^ 2n+m)) + α₁ · a) (·CommAssocSwap _ _ _ _) ⟩

           f ^ (n +ℕ m) · (α₀ · x · (f ^ 2n+m)) + α₁ · (x · f ^ (n +ℕ m) · (g ^ n · g ^ (n +ℕ m)))

         ≡⟨ cong (λ a → f ^ (n +ℕ m) · (α₀ · x · (f ^ 2n+m)) + α₁ · (x · f ^ (n +ℕ m) · a))
                 (·-of-^-is-^-of-+ _ _ _) ⟩

           f ^ (n +ℕ m) · (α₀ · x · (f ^ 2n+m)) + α₁ · (x · f ^ (n +ℕ m) · g ^ 2n+m)

         ≡⟨ solve! R' ⟩

           f ^ (n +ℕ m) · x · (α₀ · f ^ 2n+m + α₁ · g ^ 2n+m)

         ≡⟨ cong (f ^ (n +ℕ m) · x ·_) (sym 1≡α₀f²ⁿ⁺ᵐ+α₁g²ⁿ⁺ᵐ) ⟩

           f ^ (n +ℕ m) · x · 1r ∎

      z/1≡y/gⁿ : (z /1ᵍ) ≡ [ y , g ^ n , ∣ n , refl ∣₁ ]
      z/1≡y/gⁿ = eq/ _ _ ((g ^ (n +ℕ m) , ∣ n +ℕ m , refl ∣₁) , path)
       where
       path : g ^ (n +ℕ m) · z · g ^ n ≡ g ^ (n +ℕ m) · y · 1r
       path =
           g ^ (n +ℕ m) · z · g ^ n

         ≡⟨ solve! R' ⟩

           α₀ · (x · g ^ n · (f ^ (n +ℕ m) · g ^ (n +ℕ m))) + g ^ (n +ℕ m) · (α₁ · y · (g ^ n · g ^ (n +ℕ m)))

         ≡⟨ cong₂ (λ a b → α₀ · (x · g ^ n · a) + g ^ (n +ℕ m) · (α₁ · y · b))
                  (sym (^-ldist-· _ _ _)) (·-of-^-is-^-of-+ _ _ _) ⟩

           α₀ · (x · g ^ n · (f · g) ^ (n +ℕ m)) + g ^ (n +ℕ m) · (α₁ · y · g ^ 2n+m)

         ≡⟨ cong (λ a → α₀ · a + g ^ (n +ℕ m) · (α₁ · y · g ^ 2n+m))
                 xgⁿ[fg]ⁿ⁺ᵐ≡yfⁿ[fg]ⁿ⁺ᵐ ⟩

           α₀ · (y · f ^ n · (f · g) ^ (n +ℕ m)) + g ^ (n +ℕ m) · (α₁ · y · g ^ 2n+m)

         ≡⟨ cong (λ a → α₀ · (y · f ^ n · a) + g ^ (n +ℕ m) · (α₁ · y · g ^ 2n+m)) (^-ldist-· _ _ _) ⟩

           α₀ · (y · f ^ n · (f ^ (n +ℕ m) · g ^ (n +ℕ m))) + g ^ (n +ℕ m) · (α₁ · y · g ^ 2n+m)

         ≡⟨ cong (λ a → α₀ · a + g ^ (n +ℕ m) · (α₁ · y · g ^ 2n+m)) (·-assoc2 _ _ _ _) ⟩

           α₀ · (y · (f ^ n · f ^ (n +ℕ m)) · g ^ (n +ℕ m)) + g ^ (n +ℕ m) · (α₁ · y · g ^ 2n+m)

         ≡⟨ cong (λ a → α₀ · (y · a · g ^ (n +ℕ m)) + g ^ (n +ℕ m) · (α₁ · y · g ^ 2n+m))
                 (·-of-^-is-^-of-+ _ _ _) ⟩

           α₀ · (y · f ^ 2n+m · g ^ (n +ℕ m)) + g ^ (n +ℕ m) · (α₁ · y · g ^ 2n+m)

         ≡⟨ solve! R' ⟩

           g ^ (n +ℕ m) · y · (α₀ · f ^ 2n+m + α₁ · g ^ 2n+m)

         ≡⟨ cong (g ^ (n +ℕ m) · y ·_) (sym 1≡α₀f²ⁿ⁺ᵐ+α₁g²ⁿ⁺ᵐ) ⟩

           g ^ (n +ℕ m) · y · 1r ∎


      uniqueness : ∀ a → ((a /1ᶠ) ≡ [ x , f ^ n , ∣ n , refl ∣₁ ])
                       × ((a /1ᵍ) ≡ [ y , g ^ n , ∣ n , refl ∣₁ ])
                       → z ≡ a
      uniqueness a (a/1≡x/fⁿ , a/1≡y/gⁿ) = equalByDifference _ _
                   (injectivityLemma 1∈⟨f,g⟩ (z - a) [z-a]/1≡0overF [z-a]/1≡0overG)
       where
       [z-a]/1≡0overF : (z - a) /1ᶠ ≡ 0r
       [z-a]/1≡0overF = (z - a) /1ᶠ

                      ≡⟨ /1ᶠAsCommRingHom .snd .pres+ _ _ ⟩ -- (-a)/1=-(a/1) by refl!

                        (z /1ᶠ) - (a /1ᶠ)

                      ≡⟨ cong₂ _-_ z/1≡x/fⁿ a/1≡x/fⁿ ⟩

                        [ x , f ^ n , ∣ n , refl ∣₁ ] - [ x , f ^ n , ∣ n , refl ∣₁ ]

                      ≡⟨ +InvR ([ x , f ^ n , ∣ n , refl ∣₁ ]) ⟩

                        0r ∎

       [z-a]/1≡0overG : (z - a) /1ᵍ ≡ 0r
       [z-a]/1≡0overG = (z - a) /1ᵍ

                      ≡⟨ /1ᵍAsCommRingHom .snd .pres+ _ _ ⟩ -- (-a)/1=-(a/1) by refl!

                        (z /1ᵍ) - (a /1ᵍ)

                      ≡⟨ cong₂ _-_ z/1≡y/gⁿ a/1≡y/gⁿ ⟩

                        [ y , g ^ n , ∣ n , refl ∣₁ ] - [ y , g ^ n , ∣ n , refl ∣₁ ]

                      ≡⟨ +InvR ([ y , g ^ n , ∣ n , refl ∣₁ ]) ⟩

                        0r ∎


 {-
 putting everything together with the pullback machinery:
 If ⟨f,g⟩ = R then we get a square

                 _/1ᶠ
            R   ----> R[1/f]
              ⌟
       _/1ᵍ |         | χ₁
            v         v

            R[1/g] -> R[1/fg]
                   χ₂
 -}

 open Category (CommRingsCategory {ℓ})
 open Cospan

 fgCospan : Cospan CommRingsCategory
 l fgCospan = R[1/ g ]AsCommRing
 m fgCospan = R[1/ (f · g) ]AsCommRing
 r fgCospan = R[1/ f ]AsCommRing
 s₁ fgCospan = χ₂
 s₂ fgCospan = χ₁

 -- the commutative square
 private
  /1χComm : ∀ (x : R) → χ₂ .fst (x /1ᵍ) ≡ χ₁ .fst (x /1ᶠ)
  /1χComm x = eq/ _ _ ((1r , powersFormMultClosedSubset (f · g) .containsOne) , refl)

  /1χHomComm : /1ᵍAsCommRingHom ⋆ χ₂ ≡ /1ᶠAsCommRingHom ⋆ χ₁
  /1χHomComm = RingHom≡ (funExt /1χComm)

 fgSquare : 1r ∈ ⟨f,g⟩
          → isPullback _ fgCospan /1ᵍAsCommRingHom /1ᶠAsCommRingHom /1χHomComm
 fgSquare 1∈⟨f,g⟩ {d = A} ψ φ ψχ₂≡φχ₁ = (χ , χCoh) , χUniqueness
  where
  instance
   _ = snd A

  applyEqualizerLemma : ∀ a → ∃![ χa ∈ R ] (χa /1ᶠ ≡ fst φ a) × (χa /1ᵍ ≡ fst ψ a)
  applyEqualizerLemma a =
    equalizerLemma 1∈⟨f,g⟩ (fst φ a) (fst ψ a) (cong (_$r a) (sym ψχ₂≡φχ₁))

  χ : CommRingHom A R'
  fst χ a = applyEqualizerLemma a .fst .fst
  snd χ = makeIsRingHom
       (cong fst (applyEqualizerLemma 1r .snd (1r , 1Coh)))
        (λ x y → cong fst (applyEqualizerLemma (x + y) .snd (_ , +Coh x y)))
         (λ x y → cong fst (applyEqualizerLemma (x · y) .snd (_ , ·Coh x y)))
   where
   open IsRingHom
   1Coh : (1r /1ᶠ ≡ fst φ 1r) × (1r /1ᵍ ≡ fst ψ 1r)
   1Coh = (sym (φ .snd .pres1)) , sym (ψ .snd .pres1)

   +Coh : ∀ x y → ((fst χ x + fst χ y) /1ᶠ ≡ fst φ (x + y))
                × ((fst χ x + fst χ y) /1ᵍ ≡ fst ψ (x + y))
   fst (+Coh x y) = /1ᶠAsCommRingHom .snd .pres+ _ _
                  ∙∙ cong₂ _+_ (applyEqualizerLemma x .fst .snd .fst)
                             (applyEqualizerLemma y .fst .snd .fst)
                  ∙∙ sym (φ .snd .pres+ x y)
   snd (+Coh x y) = /1ᵍAsCommRingHom .snd .pres+ _ _
                  ∙∙ cong₂ _+_ (applyEqualizerLemma x .fst .snd .snd)
                               (applyEqualizerLemma y .fst .snd .snd)
                  ∙∙ sym (ψ .snd .pres+ x y)

   ·Coh : ∀ x y → ((fst χ x · fst χ y) /1ᶠ ≡ fst φ (x · y))
                × ((fst χ x · fst χ y) /1ᵍ ≡ fst ψ (x · y))
   fst (·Coh x y) = /1ᶠAsCommRingHom .snd .pres· _ _
                  ∙∙ cong₂ _·_ (applyEqualizerLemma x .fst .snd .fst)
                             (applyEqualizerLemma y .fst .snd .fst)
                  ∙∙ sym (φ .snd .pres· x y)
   snd (·Coh x y) = /1ᵍAsCommRingHom .snd .pres· _ _
                  ∙∙ cong₂ _·_ (applyEqualizerLemma x .fst .snd .snd)
                               (applyEqualizerLemma y .fst .snd .snd)
                  ∙∙ sym (ψ .snd .pres· x y)


  χCoh : (ψ ≡ χ ⋆ /1ᵍAsCommRingHom) × (φ ≡ χ ⋆ /1ᶠAsCommRingHom)
  fst χCoh = RingHom≡ (funExt (λ a → sym (applyEqualizerLemma a .fst .snd .snd)))
  snd χCoh = RingHom≡ (funExt (λ a → sym (applyEqualizerLemma a .fst .snd .fst)))

  χUniqueness : (y : Σ[ θ ∈ CommRingHom A R' ]
                       (ψ ≡ θ ⋆ /1ᵍAsCommRingHom) × (φ ≡ θ ⋆ /1ᶠAsCommRingHom))
              → (χ , χCoh) ≡ y
  χUniqueness (θ , θCoh) = Σ≡Prop (λ _ → isProp× (isSetRingHom _ _ _ _)
                                                 (isSetRingHom _ _ _ _))
    (RingHom≡ (funExt (λ a → cong fst (applyEqualizerLemma a .snd (θtriple a)))))
      where
      θtriple : ∀ a → Σ[ x ∈ R ] (x /1ᶠ ≡ fst φ a) × (x /1ᵍ ≡ fst ψ a)
      θtriple a = fst θ a , sym (cong (_$r a) (θCoh .snd))
                          , sym (cong (_$r a) (θCoh .fst))


 -- packaging it all up
 open Pullback
 fgPullback : 1r ∈ ⟨f,g⟩ → Pullback _ fgCospan
 pbOb (fgPullback 1r∈⟨f,g⟩) = _
 pbPr₁ (fgPullback 1r∈⟨f,g⟩) = _
 pbPr₂ (fgPullback 1r∈⟨f,g⟩) = _
 pbCommutes (fgPullback 1r∈⟨f,g⟩) = /1χHomComm
 univProp (fgPullback 1r∈⟨f,g⟩) = fgSquare 1r∈⟨f,g⟩
