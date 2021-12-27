{-# OPTIONS --safe --experimental-lossy-unification #-}
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
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_
                                      ; +-comm to +ℕ-comm ; +-assoc to +ℕ-assoc
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Vec
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

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
open import Cubical.Algebra.RingSolver.Reflection

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
                  λ n → [ g ^ n , (f · g) ^ n , ∣ n , refl ∣ ]
                        , eq/ _ _ ((1r , powersFormMultClosedSubset (f · g) .containsOne)
                        , path n)
    where
    -- deal with this later
    -- useSolver1 : ∀ (a b : R) → 1r · (a · b) · 1r
    -- useSolver1 = solve R'
    -- useSolver2 : ∀ a → (1r · 1r) · (1r · a)
    -- useSolver2 = solve R'
    path : (n : ℕ) → 1r · (f ^ n · g ^ n) · 1r ≡ (1r · 1r) · (1r · ((f · g) ^ n))
    path = {!!}

  χ₂ : CommRingHom R[1/ g ]AsCommRing R[1/ (f · g) ]AsCommRing
  χ₂ = R[1/g]HasUniversalProp _ /1ᶠᵍAsCommRingHom unitHelper .fst .fst
   where
   unitHelper : ∀ s → s ∈ₚ [ g ⁿ|n≥0] → s /1ᶠᵍ ∈ₚ (R[1/ (f · g) ]AsCommRing) ˣ
   unitHelper = powersPropElim (λ s → Units.inverseUniqueness _ (s /1ᶠᵍ))
                  λ n → [ f ^ n , (f · g) ^ n , ∣ n , refl ∣ ]
                        , eq/ _ _ ((1r , powersFormMultClosedSubset (f · g) .containsOne)
                              , {!!})

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
   ux≡0 = sym (·Rid _) ∙ p ∙ cong (_· 1r) (0RightAnnihilates _) ∙ (·Rid _)

   vx≡0 : v · x ≡ 0r
   vx≡0 = sym (·Rid _) ∙ q ∙ cong (_· 1r) (0RightAnnihilates _) ∙ (·Rid _)

   exponentHelper : Σ[ n ∈ ℕ ] u ≡ f ^ n
                  → Σ[ n ∈ ℕ ] v ≡ g ^ n
                  → x ≡ 0r
   exponentHelper (n , u≡fⁿ) (m , v≡gᵐ) =
                   PT.rec (is-set _ _) Σhelper (GeneratingExponents.lemma R' f g l 1∈⟨f,g⟩)
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
     1≡α₀fˡ+α₁gˡ = 1≡α₀fˡ+α₁gˡ+0 ∙ cong (α₀ · f ^ l +_) (+Rid _)

     path : x ≡ 0r
     path = x                                   ≡⟨ sym (·Lid _) ⟩
            1r · x                              ≡⟨ cong (_· x) 1≡α₀fˡ+α₁gˡ ⟩
            (α₀ · f ^ l + α₁ · g ^ l) · x       ≡⟨ ·Ldist+ _ _ _ ⟩
            α₀ · f ^ l · x + α₁ · g ^ l · x     ≡⟨ cong₂ _+_ (sym (·Assoc _ _ _))
                                                             (sym (·Assoc _ _ _)) ⟩
            α₀ · (f ^ l · x) + α₁ · (g ^ l · x) ≡⟨ cong₂ (λ y z → α₀ · y + α₁ · z)
                                                         fˡx≡0 gˡx≡0 ⟩
            α₀ · 0r + α₁ · 0r                   ≡⟨ cong₂ _+_ (0RightAnnihilates _)
                                                             (0RightAnnihilates _) ∙ +Rid _ ⟩
            0r ∎


 equalizerLemma : 1r ∈ ⟨f,g⟩
                → ∀ (x : R[1/ f ]) (y : R[1/ g ])
                → χ₁ .fst x ≡ χ₂ .fst y
                → ∃![ z ∈ R ] (z /1ᶠ ≡ x) × (z /1ᵍ ≡ y)
 equalizerLemma 1∈⟨f,g⟩ = InvElPropElim2 (λ _ _ → isPropΠ (λ _ → isPropIsContr)) baseCase
  where
  baseCase : ∀ (x y : R) (n : ℕ)
           → fst χ₁ ([ x , f ^ n , ∣ n , refl ∣ ]) ≡ fst χ₂ ([ y , g ^ n , ∣ n , refl ∣ ])
           → ∃![ z ∈ R ] ((z /1ᶠ ≡ [ x , f ^ n , ∣ n , refl ∣ ])
                        × (z /1ᵍ ≡ [ y , g ^ n , ∣ n , refl ∣ ]))
  baseCase x y n χ₁[x/fⁿ]≡χ₂[y/gⁿ] = {!!}
   where
   -- doesn't compute that well but at least it computes...
   exAnnihilator : ∃[ s ∈ Sᶠᵍ ] -- s.t.
     (fst s · (x · transp (λ _ → R) i0 (g ^ n)) · (1r · transp (λ _ → R) i0 ((f · g) ^ n))
    ≡ fst s · (y · transp (λ _ → R) i0 (f ^ n)) · (1r · transp (λ _ → R) i0 ((f · g) ^ n)))
   exAnnihilator = isEquivRel→TruncIso locIsEquivRelᶠᵍ _ _ .fun χ₁[x/fⁿ]≡χ₂[y/gⁿ]


 {-
 putting everything together with the pullback machinery
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
 l fgCospan = R[1/ f ]AsCommRing
 m fgCospan = R[1/ (f · g) ]AsCommRing
 r fgCospan = R[1/ g ]AsCommRing
 s₁ fgCospan = χ₁
 s₂ fgCospan = χ₂

 -- the commutative square
 private
  /1χComm : ∀ (x : R) → χ₁ .fst (x /1ᶠ) ≡ χ₂ .fst (x /1ᵍ)
  /1χComm x = eq/ _ _ ((1r , powersFormMultClosedSubset (f · g) .containsOne) , refl)

  /1χHomComm : /1ᶠAsCommRingHom ⋆ χ₁ ≡ /1ᵍAsCommRingHom ⋆ χ₂
  /1χHomComm = RingHom≡ (funExt /1χComm)

 fgSquare : 1r ∈ ⟨f,g⟩
          → isPullback _ fgCospan /1ᶠAsCommRingHom /1ᵍAsCommRingHom /1χHomComm
 fgSquare 1∈⟨f,g⟩ {d = A} φ ψ φχ₁≡ψχ₂ = (χ , χCoh) , χUniqueness
  where
  instance
   _ = snd A

  applyEqualizerLemma : ∀ a → ∃![ χa ∈ R ] (χa /1ᶠ ≡ fst φ a) × (χa /1ᵍ ≡ fst ψ a)
  applyEqualizerLemma a =
    equalizerLemma 1∈⟨f,g⟩ (fst φ a) (fst ψ a) (cong (_$ a) φχ₁≡ψχ₂)

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


  χCoh : (φ ≡ χ ⋆ /1ᶠAsCommRingHom) × (ψ ≡ χ ⋆ /1ᵍAsCommRingHom)
  fst χCoh = RingHom≡ (funExt (λ a → sym (applyEqualizerLemma a .fst .snd .fst)))
  snd χCoh = RingHom≡ (funExt (λ a → sym (applyEqualizerLemma a .fst .snd .snd)))

  χUniqueness : (y : Σ[ θ ∈ CommRingHom A R' ]
                       (φ ≡ θ ⋆ /1ᶠAsCommRingHom) × (ψ ≡ θ ⋆ /1ᵍAsCommRingHom))
              → (χ , χCoh) ≡ y
  χUniqueness (θ , θCoh) = Σ≡Prop (λ _ → isProp× (isSetRingHom _ _ _ _)
                                                 (isSetRingHom _ _ _ _))
    (RingHom≡ (funExt (λ a → cong fst (applyEqualizerLemma a .snd (θtriple a)))))
      where
      θtriple : ∀ a → Σ[ x ∈ R ] (x /1ᶠ ≡ fst φ a) × (x /1ᵍ ≡ fst ψ a)
      θtriple a = fst θ a , sym (cong (_$ a) (θCoh .fst))
                          , sym (cong (_$ a) (θCoh .snd))
