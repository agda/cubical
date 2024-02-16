-- In this file we consider the special of localising at a single
-- element f : R (or rather the set of powers of f). This is also
-- known as inverting f.
-- We then prove that localising first at an element f and at an element
-- g (or rather the image g/1) is the same as localising at the product f·g
-- This fact has an important application in algebraic geometry where it's
-- used to define the structure sheaf of a commutative ring.

{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.CommRing.Localisation.InvertingElements where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
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
open import Cubical.Algebra.CommRing.Instances.Unit
open import Cubical.Algebra.CommRing.Localisation.Base
open import Cubical.Algebra.CommRing.Localisation.UniversalProperty
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.RadicalIdeal


open import Cubical.Tactics.CommRingSolver

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT

open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ

module InvertingElementsBase (R' : CommRing ℓ) where
 open isMultClosedSubset
 private R = fst R'
 open CommRingStr (snd R')
 open Exponentiation R'
 open RingTheory (CommRing→Ring R')


 [_ⁿ|n≥0] : R → ℙ R
 [ f ⁿ|n≥0] g = (∃[ n ∈ ℕ ] g ≡ f ^ n) , isPropPropTrunc
 -- Σ[ n ∈ ℕ ] (s ≡ f ^ n) × (∀ m → s ≡ f ^ m → n ≤ m) maybe better, this isProp:
 -- (n,s≡fⁿ,p) (m,s≡fᵐ,q) then n≤m by p and  m≤n by q => n≡m

 powersFormMultClosedSubset : (f : R) → isMultClosedSubset R' [ f ⁿ|n≥0]
 powersFormMultClosedSubset f .containsOne = PT.∣ zero , refl ∣₁
 powersFormMultClosedSubset f .multClosed =
             PT.map2 λ (m , p) (n , q) → (m +ℕ n) , (λ i → (p i) · (q i)) ∙ ·-of-^-is-^-of-+ f m n


 R[1/_] : R → Type ℓ
 R[1/ f ] = Loc.S⁻¹R R' [ f ⁿ|n≥0] (powersFormMultClosedSubset f)

 -- a quick fact
 isContrR[1/0] : isContr R[1/ 0r ]
 fst isContrR[1/0] = [ 1r , 0r , ∣ 1 , sym (·IdR 0r) ∣₁ ] -- everything is equal to 1/0
 snd isContrR[1/0] = elimProp (λ _ → squash/ _ _)
                               λ _ → eq/ _ _ ((0r , ∣ 1 , sym (·IdR 0r) ∣₁) , (solve! R'))

 R[1/_]AsCommRing : R → CommRing ℓ
 R[1/ f ]AsCommRing = Loc.S⁻¹RAsCommRing R' [ f ⁿ|n≥0] (powersFormMultClosedSubset f)

 R[1/0]≡0 : R[1/ 0r ]AsCommRing ≡ UnitCommRing
 R[1/0]≡0 = uaCommRing (e , eIsRHom)
  where
  open IsRingHom

  e : R[1/ 0r ]AsCommRing .fst ≃ UnitCommRing .fst
  e = isContr→Equiv isContrR[1/0] isContrUnit*

  eIsRHom : IsCommRingEquiv (R[1/ 0r ]AsCommRing .snd) e (UnitCommRing .snd)
  pres0 eIsRHom = refl
  pres1 eIsRHom = refl
  pres+ eIsRHom _ _ = refl
  pres· eIsRHom _ _ = refl
  pres- eIsRHom _ = refl

 -- A useful lemma: (gⁿ/1)≡(g/1)ⁿ in R[1/f]
 ^-respects-/1 : {f g : R} (n : ℕ) → [ (g ^ n) , 1r , PT.∣ 0 , (λ _ → 1r) ∣₁ ] ≡
     Exponentiation._^_ R[1/ f ]AsCommRing [ g , 1r , powersFormMultClosedSubset _ .containsOne ] n
 ^-respects-/1 zero = refl
 ^-respects-/1 {f} {g} (suc n) = eq/ _ _ ( (1r , powersFormMultClosedSubset f .containsOne)
                                         , cong (1r · (g · (g ^ n)) ·_) (·IdL 1r))
                           ∙ cong (CommRingStr._·_ (R[1/ f ]AsCommRing .snd)
                           [ g , 1r , powersFormMultClosedSubset f .containsOne ]) (^-respects-/1 n)

 -- A slight improvement for eliminating into propositions
 invElPropElim : {f : R} {P : R[1/ f ] → Type ℓ'}
               → (∀ x →  isProp (P x))
               → (∀ (r : R) (n : ℕ) → P [ r , (f ^ n) , PT.∣ n , refl ∣₁ ])    -- ∀ r n → P (r/fⁿ)
              ----------------------------------------------------------
               → ∀ x → P x
 invElPropElim {f = f} {P = P} PisProp base = elimProp (λ _ → PisProp _) []-case
  where
  S[f] = Loc.S R' [ f ⁿ|n≥0] (powersFormMultClosedSubset f)
  []-case : (a : R × S[f]) → P [ a ]
  []-case (r , s , s∈S[f]) = PT.rec (PisProp _) Σhelper s∈S[f]
   where
   Σhelper : Σ[ n ∈ ℕ ] s ≡ f ^ n → P [ r , s , s∈S[f] ]
   Σhelper (n , p) = subst P (cong [_] (≡-× refl (Σ≡Prop (λ _ → isPropPropTrunc) (sym p)))) (base r n)


 invElPropElim2 : {f g : R} {P : R[1/ f ] → R[1/ g ] → Type ℓ'}
                → (∀ x y →  isProp (P x y))
                → (∀ (r s : R) (n : ℕ) → P [ r , (f ^ n) , PT.∣ n , refl ∣₁ ]
                                           [ s , (g ^ n) , PT.∣ n , refl ∣₁ ])
               ----------------------------------------------------------
                → ∀ x y → P x y
 invElPropElim2 {f = f} {g = g} {P = P} PisProp base =
   invElPropElim (λ _ → isPropΠ (λ _ → PisProp _ _)) reduce1
   where
   reduce1 : ∀ (r : R) (n : ℕ) (y : R[1/ g ]) → P [ r , f ^ n , ∣ n , refl ∣₁ ] y
   reduce1 r n = invElPropElim (λ _ → PisProp _ _) reduce2
     where
     reduce2 : (s : R) (m : ℕ) → P [ r , f ^ n , ∣ n , refl ∣₁ ] [ s , g ^ m , ∣ m , refl ∣₁ ]
     reduce2 s m = subst2 P p q (base _ _ l)
      where
      l = max m n
      x : R[1/ f ]
      x = [ r , f ^ n , ∣ n , refl ∣₁ ]
      y : R[1/ g ]
      y = [ s , g ^ m , ∣ m , refl ∣₁ ]
      x' : R[1/ f ]
      x' = [ r · f ^ (l ∸ n) , f ^ l , ∣ l , refl ∣₁ ]
      y' : R[1/ g ]
      y' = [ s · g ^ (l ∸ m) , g ^ l , ∣ l , refl ∣₁ ]

      p : x' ≡ x
      p = eq/ _ _ ((1r , ∣ 0 , refl ∣₁) , path)
       where
       path : 1r · (r · f ^ (l ∸ n)) · f ^ n ≡ 1r · r · f ^ l
       path = 1r · (r · f ^ (l ∸ n)) · f ^ n ≡⟨ solve! R' ⟩
              r · (f ^ (l ∸ n) · f ^ n)      ≡⟨ cong (r ·_) (·-of-^-is-^-of-+ _ _ _) ⟩
              r · f ^ (l ∸ n +ℕ n)           ≡⟨ cong (λ k → r · f ^ k) (≤-∸-+-cancel right-≤-max) ⟩
              r · f ^ l                      ≡⟨ solve! R' ⟩
              1r · r · f ^ l ∎

      q : y' ≡ y
      q = eq/ _ _ ((1r , ∣ 0 , refl ∣₁) , path)
       where
       path : 1r · (s · g ^ (l ∸ m)) · g ^ m ≡ 1r · s · g ^ l
       path = 1r · (s · g ^ (l ∸ m)) · g ^ m ≡⟨ solve! R' ⟩
              s · (g ^ (l ∸ m) · g ^ m)      ≡⟨ cong (s ·_) (·-of-^-is-^-of-+ _ _ _) ⟩
              s · g ^ (l ∸ m +ℕ m)           ≡⟨ cong (λ k → s · g ^ k) (≤-∸-+-cancel left-≤-max) ⟩
              s · g ^ l                      ≡⟨ solve! R' ⟩
              1r · s · g ^ l ∎


 invElPropElimN : (n : ℕ) (f : FinVec R n) (P : ((i : Fin n) → R[1/ (f i) ]) → Type ℓ')
          → (∀ x → isProp (P x))
          → (∀ (r : FinVec R n) (m : ℕ) → P (λ i → [ r i , (f i ^ m) , PT.∣ m , refl ∣₁ ]))
          -------------------------------------------------------------------------------------
          → ∀ x → P x
 invElPropElimN zero f P isPropP baseCase x =
   subst P (funExt (λ ())) (baseCase (λ ()) zero)

 invElPropElimN (suc n) f P isPropP baseCase x =
   subst P (funExt (λ { zero → refl ; (suc i) → refl }))
           (invElPropElimN n (f ∘ suc) P' (λ _ → isPropP _) baseCase' (x ∘ suc))
   where
   P' : ((i : Fin n) → R[1/ (f (suc i)) ]) → Type _
   P' y = P (λ { zero → x zero ; (suc i) → y i })

   baseCase' : ∀ (rₛ : FinVec R n) (m : ℕ)
             → P' (λ i → [ rₛ i , f (suc i) ^ m , ∣ m , refl ∣₁ ])
   baseCase' rₛ m =
     subst P (funExt (λ { zero → refl ; (suc i) → refl }))
       (invElPropElim {P = P''} (λ _ → isPropP _) baseCase'' (x zero))
     where
     P'' : R[1/ (f zero) ] → Type _
     P'' y = P (λ { zero → y ; (suc i) → [ rₛ i , f (suc i) ^ m , ∣ m , refl ∣₁ ]})

     baseCase'' : ∀ (r₀ : R) (k : ℕ) → P'' [ r₀ , f zero ^ k , ∣ k , refl ∣₁ ]
     baseCase'' r₀ k = subst P (funExt (λ { zero → vecPaths zero ; (suc i) → vecPaths (suc i) }))
                              (baseCase newEnumVec l)
      where
      l = max m k

      newEnumVec : FinVec R (suc n)
      newEnumVec zero = r₀ · (f zero) ^ (l ∸ k)
      newEnumVec (suc i) = rₛ i · (f (suc i)) ^ (l ∸ m)

      oldBaseVec : (i : Fin (suc n)) → R[1/ (f i) ]
      oldBaseVec = λ { zero → [ r₀ , f zero ^ k , ∣ k , refl ∣₁ ]
                     ; (suc i) → [ rₛ i , f (suc i) ^ m , ∣ m , (λ _ → f (suc i) ^ m) ∣₁ ] }

      newBaseVec : (i : Fin (suc n)) → R[1/ (f i) ]
      newBaseVec zero = [ r₀ · (f zero) ^ (l ∸ k) , (f zero) ^ l , ∣ l , refl ∣₁ ]
      newBaseVec (suc i) = [ rₛ i · (f (suc i)) ^ (l ∸ m) , (f (suc i)) ^ l , ∣ l , refl ∣₁ ]

      vecPaths : ∀ i → newBaseVec i ≡ oldBaseVec i
      vecPaths zero = eq/ _ _ ((1r , ∣ 0 , refl ∣₁) , path)
        where
        path : 1r · (r₀ · f zero ^ (l ∸ k)) · f zero ^ k ≡ 1r · r₀ · f zero ^ l
        path = 1r · (r₀ · f zero ^ (l ∸ k)) · f zero ^ k
             ≡⟨ solve! R' ⟩
               r₀ · (f zero ^ (l ∸ k) · f zero ^ k)
             ≡⟨ cong (r₀ ·_) (·-of-^-is-^-of-+ _ _ _) ⟩
               r₀ · f zero ^ (l ∸ k +ℕ k)
             ≡⟨ cong (λ k' → r₀ · f zero ^ k') (≤-∸-+-cancel right-≤-max) ⟩
               r₀ · f zero ^ l
             ≡⟨ solve! R' ⟩
               1r · r₀ · f zero ^ l ∎

      vecPaths (suc i) = eq/ _ _ ((1r , ∣ 0 , refl ∣₁) , path)
        where
        path : 1r · (rₛ i · f (suc i) ^ (l ∸ m)) · f (suc i) ^ m ≡ 1r · rₛ i · f (suc i) ^ l
        path = 1r · (rₛ i · f (suc i) ^ (l ∸ m)) · f (suc i) ^ m
             ≡⟨ solve! R' ⟩
               rₛ i · (f (suc i) ^ (l ∸ m) · f (suc i) ^ m)
             ≡⟨ cong (rₛ i ·_) (·-of-^-is-^-of-+ _ _ _) ⟩
               rₛ i · f (suc i) ^ (l ∸ m +ℕ m)
             ≡⟨ cong (λ m' → rₛ i · f (suc i) ^ m') (≤-∸-+-cancel left-≤-max) ⟩
               rₛ i · f (suc i) ^ l
             ≡⟨ solve! R' ⟩
               1r · rₛ i · f (suc i) ^ l ∎



 -- For predicates over the set of powers
 powersPropElim : {f : R} {P : R → Type ℓ'}
                → (∀ x →  isProp (P x))
                → (∀ n → P (f ^ n))
               ------------------------------
                → ∀ s → s ∈ [ f ⁿ|n≥0] → P s
 powersPropElim {f = f} {P = P} PisProp base s =
                PT.rec (PisProp s) λ (n , p) → subst P (sym p) (base n)



 -- A more specialized universal property.
 -- (Just ask f to become invertible, not all its powers.)
 module UniversalProp (f : R) where
   open S⁻¹RUniversalProp R' [ f ⁿ|n≥0] (powersFormMultClosedSubset f) public
   open CommRingHomTheory

   invElemUniversalProp : (A : CommRing ℓ) (φ : CommRingHom R' A)
                        → (φ .fst f ∈ A ˣ)
                        → ∃![ χ ∈ CommRingHom R[1/ f ]AsCommRing A ]
                            (fst χ) ∘ (fst /1AsCommRingHom) ≡ (fst φ)
   invElemUniversalProp A φ φf∈Aˣ =
     S⁻¹RHasUniversalProp A φ
       (powersPropElim (λ _ → ∈-isProp _ _)
       (λ n → subst-∈ (A ˣ) (sym (pres^ φ f n)) (Exponentiation.^-presUnit A _ n φf∈Aˣ)))


-- "functorial action" of localizing away from an element
module _ {A B : CommRing ℓ} (φ : CommRingHom A B) (f : fst A) where
  open CommRingStr (snd B)
  private
    module A = InvertingElementsBase A
    module B = InvertingElementsBase B
    module AU = A.UniversalProp f
    module BU = B.UniversalProp (φ $r f)

    φ/1 = BU./1AsCommRingHom ∘cr φ

  uniqInvElemHom : ∃![ χ ∈ CommRingHom A.R[1/ f ]AsCommRing B.R[1/ φ $r f ]AsCommRing ]
                     (fst χ) ∘ (fst AU./1AsCommRingHom) ≡ (fst φ/1)
  uniqInvElemHom = AU.invElemUniversalProp _ φ/1 (BU.S/1⊆S⁻¹Rˣ _ ∣ 1 , sym (·IdR _) ∣₁)

module _ (R : CommRing ℓ) (f : fst R) where
 open CommRingTheory R
 open RingTheory (CommRing→Ring R)
 open Units R
 open Exponentiation R
 open InvertingElementsBase R
 open isMultClosedSubset (powersFormMultClosedSubset f)
 open S⁻¹RUniversalProp R [ f ⁿ|n≥0] (powersFormMultClosedSubset f)
 open CommRingStr (snd R)
 open PathToS⁻¹R

 invertingUnitsPath : f ∈ R ˣ → R[1/ f ]AsCommRing ≡ R
 invertingUnitsPath f∈Rˣ = S⁻¹RChar _ _ _ _ (idCommRingHom R) (char f∈Rˣ)
   where
   char : f ∈ R ˣ → PathToS⁻¹R _ _ (powersFormMultClosedSubset f)
                                 _ (idCommRingHom R)
   φS⊆Aˣ (char f∈Rˣ) = powersPropElim (∈-isProp _)
                           λ n → ^-presUnit _ n f∈Rˣ
   kerφ⊆annS (char _) _ r≡0 = ∣ (1r , containsOne) , ·IdL _ ∙ r≡0 ∣₁
   surχ (char _) r = ∣ (r , 1r , containsOne)
                                , cong (r ·_) (transportRefl _) ∙ ·IdR _ ∣₁


module RadicalLemma (R' : CommRing ℓ) (f g : (fst R')) where
 open IsRingHom
 open isMultClosedSubset
 open CommRingTheory R'
 open RingTheory (CommRing→Ring R')
 open CommIdeal R' hiding (subst-∈) renaming (_∈_ to _∈ᵢ_)
 open RadicalIdeal R'
 open Exponentiation R'
 open InvertingElementsBase R'

 open S⁻¹RUniversalProp R' [ f ⁿ|n≥0] (powersFormMultClosedSubset f)
      hiding (S⁻¹RHasUniversalProp)
 open S⁻¹RUniversalProp R' [ g ⁿ|n≥0] (powersFormMultClosedSubset g)
      hiding (_/1 ; /1AsCommRingHom)
 open CommRingStr (R' .snd)

 private
  R = R' .fst
  ⟨_⟩ : R → CommIdeal
  ⟨ f ⟩ = ⟨ replicateFinVec 1 f ⟩[ R' ]

 unitHelper : f ∈ᵢ √ ⟨ g ⟩ → (g /1) ∈ R[1/ f ]AsCommRing ˣ
 unitHelper = PT.rec isPropGoal (uncurry ℕhelper)
  where
  isPropGoal = Units.inverseUniqueness _ (g /1)

  ℕhelper : (n : ℕ) → f ^ n ∈ᵢ ⟨ g ⟩ → (g /1) ∈ R[1/ f ]AsCommRing ˣ
  ℕhelper n = PT.rec isPropGoal -- fⁿ≡αg → g⁻¹≡α/fⁿ
       λ (α , p) → [ (α zero) , (f ^ n) , ∣ n , refl ∣₁ ]
                 , eq/ _ _ ((1r , powersFormMultClosedSubset f .containsOne)
                 , (solve! R') ∙ sym p ∙ (solve! R'))

 toUnit : f ∈ᵢ √ ⟨ g ⟩
       → ∀ s → s ∈ [ g ⁿ|n≥0] → (s /1) ∈ R[1/ f ]AsCommRing ˣ
 toUnit f∈√⟨g⟩ = powersPropElim (λ x → Units.inverseUniqueness _ (x /1))
               λ n → subst-∈ (R[1/ f ]AsCommRing ˣ) (sym (^-respects-/1 n))
                      (Exponentiation.^-presUnit _ _ n (unitHelper f∈√⟨g⟩))


module DoubleLoc (R' : CommRing ℓ) (f g : fst R') where
 open isMultClosedSubset
 open CommRingStr (snd R')
 open CommRingTheory R'
 open Exponentiation R'
 open InvertingElementsBase
 open RingTheory (CommRing→Ring R')
 open CommRingStr (snd (R[1/_]AsCommRing R' f)) renaming ( _·_ to _·ᶠ_ ; 1r to 1ᶠ
                                                         ; _+_ to _+ᶠ_ ; 0r to 0ᶠ
                                                         ; ·IdL to ·ᶠ-lid ; ·IdR to ·ᶠ-rid
                                                         ; ·Assoc to ·ᶠ-assoc ; ·Comm to ·ᶠ-comm)
 open IsRingHom

 private
  R = fst R'
  R[1/f] = R[1/_] R' f
  R[1/f]AsCommRing = R[1/_]AsCommRing R' f
  R[1/fg] = R[1/_] R' (f · g)
  R[1/fg]AsCommRing = R[1/_]AsCommRing R' (f · g)
  R[1/f][1/g] = R[1/_] (R[1/_]AsCommRing R' f)
                                [ g , 1r , powersFormMultClosedSubset R' f .containsOne ]
  R[1/f][1/g]AsCommRing = R[1/_]AsCommRing (R[1/_]AsCommRing R' f)
                                [ g , 1r , powersFormMultClosedSubset R' f .containsOne ]
  R[1/f][1/g]ˣ = R[1/f][1/g]AsCommRing ˣ


 _/1/1 : R → R[1/f][1/g]
 r /1/1 = [ [ r , 1r , PT.∣ 0 , refl ∣₁ ] , 1ᶠ , PT.∣ 0 , refl ∣₁ ]

 /1/1AsCommRingHom : CommRingHom R' R[1/f][1/g]AsCommRing
 fst /1/1AsCommRingHom = _/1/1
 snd /1/1AsCommRingHom = makeIsRingHom refl lem+ lem·
   where
   lem+ : _
   lem+ r r' =
     cong [_]
       (≡-×
         (cong [_]
           (≡-×
             (cong₂ _+_
               (sym (·IdR _) ∙ (λ i → (·IdR r (~ i)) · (·IdR 1r (~ i))))
               (sym (·IdR _) ∙ (λ i → (·IdR r' (~ i)) · (·IdR 1r (~ i)))))
             (Σ≡Prop (λ _ → isPropPropTrunc)
               (sym (·IdL _) ∙ (λ i → (·IdL 1r (~ i)) · (·IdL 1r (~ i)))))))
         (Σ≡Prop (λ _ → isPropPropTrunc) (sym (·ᶠ-lid 1ᶠ))))

   lem· : _
   lem· r r' =
     cong [_]
       (≡-×
         (cong [_] (≡-× refl (Σ≡Prop (λ _ → isPropPropTrunc) (sym (·IdL _)))))
         (Σ≡Prop (λ _ → isPropPropTrunc) (sym (·ᶠ-lid 1ᶠ))))

 -- this will give us a map R[1/fg] → R[1/f][1/g] by the universal property of localisation
 fⁿgⁿ/1/1∈R[1/f][1/g]ˣ : (s : R) → s ∈ ([_ⁿ|n≥0] R' (f · g)) → s /1/1 ∈ R[1/f][1/g]ˣ
 fⁿgⁿ/1/1∈R[1/f][1/g]ˣ = powersPropElim R' (λ s → R[1/f][1/g]ˣ (s /1/1) .snd) ℕcase
  where
  ℕcase : (n : ℕ) → ((f · g) ^ n) /1/1 ∈ R[1/f][1/g]ˣ
  ℕcase n = [ [ 1r , (f ^ n) , PT.∣ n , refl ∣₁ ]
            , [ (g ^ n) , 1r , PT.∣ 0 , refl ∣₁ ] --denominator
            , PT.∣ n , ^-respects-/1 _ n ∣₁ ]
            , eq/ _ _ ((1ᶠ , powersFormMultClosedSubset _ _ .containsOne)
            , eq/ _ _ ((1r , powersFormMultClosedSubset _ _ .containsOne) , path))
   where
   path : 1r · (1r · ((f · g) ^ n · 1r) · 1r) · (1r · 1r · (1r · 1r))
        ≡ 1r · (1r · 1r · (1r · g ^ n)) · (1r · (1r · f ^ n) · 1r)
   path = 1r · (1r · ((f · g) ^ n · 1r) · 1r) · (1r · 1r · (1r · 1r)) ≡⟨ solve! R' ⟩
          (f · g) ^ n                                                 ≡⟨ ^-ldist-· _ _ _ ⟩
          f ^ n · g ^ n                                               ≡⟨ solve! R' ⟩
          1r · (1r · 1r · (1r · g ^ n)) · (1r · (1r · f ^ n) · 1r)    ∎


 open PathToS⁻¹R
 pathtoR[1/fg] : PathToS⁻¹R R' ([_ⁿ|n≥0] R' (f · g)) (powersFormMultClosedSubset R' (f · g))
                            R[1/f][1/g]AsCommRing /1/1AsCommRingHom
 φS⊆Aˣ pathtoR[1/fg] = fⁿgⁿ/1/1∈R[1/f][1/g]ˣ

 kerφ⊆annS pathtoR[1/fg] r p = toGoal helperR[1/f]
  where
  open RingTheory (CommRing→Ring R[1/f]AsCommRing) renaming ( 0RightAnnihilates to 0ᶠRightAnnihilates
                                                        ; 0LeftAnnihilates to 0ᶠ-leftNullifies)
  open Exponentiation R[1/f]AsCommRing renaming (_^_ to _^ᶠ_)
                                       hiding (·-of-^-is-^-of-+ ; ^-ldist-·)

  S[f] = Loc.S R' ([_ⁿ|n≥0] R' f) (powersFormMultClosedSubset R' f)
  S[fg] = Loc.S R' ([_ⁿ|n≥0] R' (f · g)) (powersFormMultClosedSubset R' (f · g))
  g/1 : R[1/_] R' f
  g/1 = [ g , 1r , powersFormMultClosedSubset R' f .containsOne ]
  S[g/1] = Loc.S R[1/f]AsCommRing
                 ([_ⁿ|n≥0] R[1/f]AsCommRing g/1)
                 (powersFormMultClosedSubset R[1/f]AsCommRing g/1)
  r/1 : R[1/_] R' f
  r/1 = [ r , 1r , powersFormMultClosedSubset R' f .containsOne ]

  -- this is the crucial step, modulo truncation we can take p to be generated
  -- by the quotienting relation of localisation. Note that we wouldn't be able
  -- to prove our goal if kerφ⊆annS was formulated with a Σ instead of a ∃
  ∥r/1,1/1≈0/1,1/1∥ : ∃[ u ∈ S[g/1] ] fst u ·ᶠ r/1 ·ᶠ 1ᶠ ≡ fst u ·ᶠ 0ᶠ ·ᶠ 1ᶠ
  ∥r/1,1/1≈0/1,1/1∥ = Iso.fun (SQ.isEquivRel→TruncIso (Loc.locIsEquivRel _ _ _) _ _) p

  helperR[1/f] : ∃[ n ∈ ℕ ] [ g ^ n · r , 1r , PT.∣ 0 , refl ∣₁ ] ≡ 0ᶠ
  helperR[1/f] = PT.rec isPropPropTrunc
                 (uncurry (uncurry (powersPropElim R[1/f]AsCommRing
                                   (λ _ → isPropΠ (λ _ → isPropPropTrunc)) baseCase)))
                 ∥r/1,1/1≈0/1,1/1∥
   where
   baseCase : ∀ n → g/1 ^ᶠ n ·ᶠ r/1 ·ᶠ 1ᶠ ≡ g/1 ^ᶠ n ·ᶠ 0ᶠ ·ᶠ 1ᶠ
                  → ∃[ n ∈ ℕ ] [ g ^ n · r , 1r , PT.∣ 0 , refl ∣₁ ] ≡ 0ᶠ
   baseCase n q = PT.∣ n , path ∣₁
    where
    path : [ g ^ n · r , 1r , PT.∣ 0 , refl ∣₁ ] ≡ 0ᶠ
    path = [ g ^ n · r , 1r , PT.∣ 0 , refl ∣₁ ]

         ≡⟨ cong [_] (≡-× refl (Σ≡Prop (λ _ → isPropPropTrunc) (sym (·IdR _)))) ⟩

           [ g ^ n , 1r , PT.∣ 0 , refl ∣₁ ] ·ᶠ r/1

         ≡⟨ cong (_·ᶠ r/1) (^-respects-/1 _ n) ⟩

           g/1 ^ᶠ n ·ᶠ r/1

         ≡⟨ sym (·ᶠ-rid _) ⟩

           g/1 ^ᶠ n ·ᶠ r/1 ·ᶠ 1ᶠ

         ≡⟨ q ⟩

           g/1 ^ᶠ n ·ᶠ 0ᶠ ·ᶠ 1ᶠ

         ≡⟨ cong (_·ᶠ 1ᶠ) (0ᶠRightAnnihilates _) ∙ 0ᶠ-leftNullifies 1ᶠ ⟩

           0ᶠ ∎


  toGoal : ∃[ n ∈ ℕ ] [ g ^ n · r , 1r , PT.∣ 0 , refl ∣₁ ] ≡ 0ᶠ
         → ∃[ u ∈ S[fg] ] fst u · r ≡ 0r
  toGoal = PT.rec isPropPropTrunc Σhelper
   where
   Σhelper : Σ[ n ∈ ℕ ] [ g ^ n · r , 1r , PT.∣ 0 , refl ∣₁ ] ≡ 0ᶠ
           → ∃[ u ∈ S[fg] ] fst u · r ≡ 0r
   Σhelper (n , q) = PT.map Σhelper2 helperR
    where
    -- now, repeat the above strategy with q
    ∥gⁿr≈0∥ : ∃[ u ∈ S[f] ] fst u · (g ^ n · r) · 1r ≡ fst u · 0r · 1r
    ∥gⁿr≈0∥ = Iso.fun (SQ.isEquivRel→TruncIso (Loc.locIsEquivRel _ _ _) _ _) q

    helperR : ∃[ m ∈ ℕ ] f ^ m · g ^ n · r ≡ 0r
    helperR = PT.rec isPropPropTrunc
              (uncurry (uncurry (powersPropElim R'
                                (λ _ → isPropΠ (λ _ → isPropPropTrunc)) baseCase)))
              ∥gⁿr≈0∥
     where
     baseCase : (m : ℕ) → f ^ m · (g ^ n · r) · 1r ≡ f ^ m · 0r · 1r
              → ∃[ m ∈ ℕ ] f ^ m · g ^ n · r ≡ 0r
     baseCase m q' = PT.∣ m , path ∣₁
      where
      path : f ^ m · g ^ n · r ≡ 0r
      path = (λ i → ·IdR (·Assoc (f ^ m) (g ^ n) r (~ i)) (~ i))
           ∙∙ q' ∙∙ (λ i → ·IdR (0RightAnnihilates (f ^ m) i) i)

    Σhelper2 : Σ[ m ∈ ℕ ] f ^ m · g ^ n · r ≡ 0r
             → Σ[ u ∈ S[fg] ] fst u · r ≡ 0r
    Σhelper2 (m , q') = (((f · g) ^ l) , PT.∣ l , refl ∣₁) , path
     where
     l = max m n

     path : (f · g) ^ l · r ≡ 0r
     path = (f · g) ^ l · r

          ≡⟨ cong (_· r) (^-ldist-· _ _ _) ⟩

            f ^ l · g ^ l · r

          ≡⟨ cong₂ (λ x y → f ^ x · g ^ y · r) (sym (≤-∸-+-cancel {m = m} left-≤-max))
                                               (sym (≤-∸-+-cancel {m = n} right-≤-max)) ⟩

            f ^ (l ∸ m +ℕ m) · g ^ (l ∸ n +ℕ n) · r

          ≡⟨ cong₂ (λ x y → x · y · r) (sym (·-of-^-is-^-of-+ _ _ _))
                                       (sym (·-of-^-is-^-of-+ _ _ _)) ⟩

            f ^ (l ∸ m) · f ^ m · (g ^ (l ∸ n) · g ^ n) · r

          ≡⟨ cong (_· r) (·CommAssocSwap _ _ _ _) ⟩

            f ^ (l ∸ m) · g ^ (l ∸ n) · (f ^ m · g ^ n) · r

          ≡⟨ sym (·Assoc _ _ _) ⟩

            f ^ (l ∸ m) · g ^ (l ∸ n) · (f ^ m · g ^ n · r)

          ≡⟨ cong (f ^ (l ∸ m) · g ^ (l ∸ n) ·_) q' ⟩

            f ^ (l ∸ m) · g ^ (l ∸ n) · 0r

          ≡⟨ 0RightAnnihilates _ ⟩

            0r ∎


 surχ pathtoR[1/fg] = invElPropElim _ (λ _ → isPropPropTrunc) toGoal
  where
  open Exponentiation R[1/f]AsCommRing renaming (_^_ to _^ᶠ_)
                                              hiding (·-of-^-is-^-of-+ ; ^-ldist-·)
  open CommRingStr (snd R[1/f][1/g]AsCommRing) renaming (_·_ to _·R[1/f][1/g]_)
                   hiding (1r ; ·IdL ; ·IdR ; ·Assoc)
  open Units R[1/f][1/g]AsCommRing
  g/1 : R[1/_] R' f
  g/1 = [ g , 1r , powersFormMultClosedSubset R' f .containsOne ]
  S[fg] = Loc.S R' ([_ⁿ|n≥0] R' (f · g)) (powersFormMultClosedSubset R' (f · g))

  baseCase : (r : R) (m n : ℕ) → ∃[ x ∈ R × S[fg] ] (x .fst /1/1)
      ≡ [ [ r , f ^ m , PT.∣ m , refl ∣₁ ]
        , [ g ^ n , 1r , PT.∣ 0 , refl ∣₁ ] , PT.∣ n , ^-respects-/1 _ n ∣₁ ]
      ·R[1/f][1/g] (x .snd .fst /1/1)
  baseCase r m n = PT.∣ ((r · f ^ (l ∸ m) · g ^ (l ∸ n)) -- x .fst
              , (f · g) ^ l , PT.∣ l , refl ∣₁)      -- x .snd
              , eq/ _ _ ((1ᶠ , PT.∣ 0 , refl ∣₁) , eq/ _ _ ((1r , PT.∣ 0 , refl ∣₁) , path)) ∣₁
              -- reduce equality of double fractions into equality in R
   where
   l = max m n

   path : 1r · (1r · (r · f ^ (l ∸ m) · g ^ (l ∸ n)) · (g ^ n · 1r)) · (1r · (f ^ m · 1r) · 1r)
        ≡ 1r · (1r · (r · (f · g) ^ l) · 1r) · (1r · 1r · (1r · 1r))
   path = 1r · (1r · (r · f ^ (l ∸ m) · g ^ (l ∸ n)) · (g ^ n · 1r)) · (1r · (f ^ m · 1r) · 1r)

        ≡⟨ solve! R' ⟩

          r · f ^ (l ∸ m) · (g ^ (l ∸ n) · g ^ n) · f ^ m

        ≡⟨ cong (λ x → r · f ^ (l ∸ m) · x · f ^ m) (·-of-^-is-^-of-+ _ _ _) ⟩

          r · f ^ (l ∸ m) · g ^ (l ∸ n +ℕ n) · f ^ m

        ≡⟨ cong (λ x → r · f ^ (l ∸ m) · g ^ x · f ^ m) (≤-∸-+-cancel right-≤-max) ⟩

          r · f ^ (l ∸ m) · g ^ l · f ^ m

        ≡⟨ solve! R' ⟩

          r · (f ^ (l ∸ m) · f ^ m) · g ^ l

        ≡⟨ cong (λ x → r · x · g ^ l) (·-of-^-is-^-of-+ _ _ _) ⟩

          r · f ^ (l ∸ m +ℕ m) · g ^ l

        ≡⟨ cong (λ x → r · f ^ x · g ^ l) (≤-∸-+-cancel left-≤-max) ⟩

          r · f ^ l · g ^ l

        ≡⟨ sym (·Assoc _ _ _) ⟩

          r · (f ^ l · g ^ l)

        ≡⟨ cong (r ·_) (sym (^-ldist-· _ _ _)) ⟩

          r · (f · g) ^ l

        ≡⟨ solve! R' ⟩

          1r · (1r · (r · (f · g) ^ l) · 1r) · (1r · 1r · (1r · 1r)) ∎


  base-^ᶠ-helper : (r : R) (m n : ℕ) → ∃[ x ∈ R × S[fg] ] (x .fst /1/1)
      ≡ [ [ r , f ^ m , PT.∣ m , refl ∣₁ ]
        , g/1 ^ᶠ n , PT.∣ n , refl ∣₁ ] ·R[1/f][1/g] (x .snd .fst /1/1)
  base-^ᶠ-helper r m n = subst (λ y →  ∃[ x ∈ R × S[fg] ] (x .fst /1/1)
                         ≡ [ [ r , f ^ m , PT.∣ m , refl ∣₁ ] , y ] ·R[1/f][1/g] (x .snd .fst /1/1))
                    (Σ≡Prop (λ _ → isPropPropTrunc) (^-respects-/1 _ n)) (baseCase r m n)

  indStep : (r : R[1/_] R' f) (n : ℕ) → ∃[ x ∈ R × S[fg] ]
        (x .fst /1/1) ≡ [ r , g/1 ^ᶠ n , PT.∣ n , refl ∣₁ ] ·R[1/f][1/g] (x .snd .fst /1/1)
  indStep = invElPropElim _ (λ _ → isPropΠ λ _ → isPropPropTrunc) base-^ᶠ-helper

  toGoal : (r : R[1/_] R' f) (n : ℕ) → ∃[ x ∈ R × S[fg] ]
           (x .fst /1/1) ·R[1/f][1/g]
           ((x .snd .fst /1/1) ⁻¹) ⦃ φS⊆Aˣ pathtoR[1/fg] (x .snd .fst) (x .snd .snd) ⦄
         ≡ [ r , g/1 ^ᶠ n , PT.∣ n , refl ∣₁ ]
  toGoal r n = PT.map Σhelper (indStep r n)
   where
   Σhelper : Σ[ x ∈ R × S[fg] ]
              (x .fst /1/1) ≡ [ r , g/1 ^ᶠ n , PT.∣ n , refl ∣₁ ] ·R[1/f][1/g] (x .snd .fst /1/1)
           → Σ[ x ∈ R × S[fg] ]
              (x .fst /1/1) ·R[1/f][1/g] ((x .snd .fst /1/1) ⁻¹)
              ⦃ φS⊆Aˣ pathtoR[1/fg] (x .snd .fst) (x .snd .snd) ⦄
              ≡ [ r , g/1 ^ᶠ n , PT.∣ n , refl ∣₁ ]
   Σhelper ((r' , s , s∈S[fg]) , p) = (r' , s , s∈S[fg])
                                    , ⁻¹-eq-elim ⦃ φS⊆Aˣ pathtoR[1/fg] s s∈S[fg] ⦄ p

 -- the main result: localising at one element and then at another is
 -- the same as localising at the product.
 -- takes forever to compute without experimental lossy unification
 R[1/fg]≡R[1/f][1/g] : R[1/fg]AsCommRing ≡ R[1/f][1/g]AsCommRing
 R[1/fg]≡R[1/f][1/g] = S⁻¹RChar R' ([_ⁿ|n≥0] R' (f · g))
                         (powersFormMultClosedSubset R' (f · g)) _ /1/1AsCommRingHom pathtoR[1/fg]



 -- In this module we construct the map R[1/fg]→R[1/f][1/g] directly
 -- and show that it is equal (although not judgementally) to the map induced
 -- by the universal property of localisation, i.e. transporting along the path
 -- constructed above. Given that this is the easier direction, we can see that
 -- it is pretty cumbersome to prove R[1/fg]≡R[1/f][1/g] directly,
 -- which illustrates the usefulness of S⁻¹RChar quite well.
 private
  module check where
   φ : R[1/fg] → R[1/f][1/g]
   φ = SQ.rec squash/ ϕ ϕcoh
     where
     S[fg] = Loc.S R' ([_ⁿ|n≥0] R' (f · g)) (powersFormMultClosedSubset R' (f · g))

     curriedϕΣ : (r s : R) → Σ[ n ∈ ℕ ] s ≡ (f · g) ^ n → R[1/f][1/g]
     curriedϕΣ r s (n , s≡fg^n) = [ [ r , (f ^ n) , PT.∣ n , refl ∣₁ ]
                                  , [ (g ^ n) , 1r , PT.∣ 0 , refl ∣₁ ] --denominator
                                  , PT.∣ n , ^-respects-/1 R' n ∣₁ ]

     curriedϕ : (r s : R) → ∃[ n ∈ ℕ ] s ≡ (f · g) ^ n → R[1/f][1/g]
     curriedϕ r s = elim→Set (λ _ → squash/) (curriedϕΣ r s) coh
      where
      coh : (x y : Σ[ n ∈ ℕ ] s ≡ (f · g) ^ n) → curriedϕΣ r s x ≡ curriedϕΣ r s y
      coh (n , s≡fg^n) (m , s≡fg^m) = eq/ _ _ ((1ᶠ , PT.∣ 0 , refl ∣₁) ,
                                      eq/ _ _ ( (1r , powersFormMultClosedSubset R' f .containsOne)
                                              , path))
       where
       path : 1r · (1r · r · (g ^ m)) · (1r · (f ^ m) · 1r)
            ≡ 1r · (1r · r · (g ^ n)) · (1r · (f ^ n) · 1r)
       path = 1r · (1r · r · (g ^ m)) · (1r · (f ^ m) · 1r)

            ≡⟨ solve! R' ⟩

              r · (g ^ m · f ^ m)

            ≡⟨ cong (r ·_) (sym (^-ldist-· g f m)) ⟩

              r · ((g · f) ^ m)

            ≡⟨ cong (λ x → r · (x ^ m)) (·Comm _ _) ⟩

              r · ((f · g) ^ m)

            ≡⟨ cong (r ·_) ((sym s≡fg^m) ∙ s≡fg^n) ⟩

              r · ((f · g) ^ n)

            ≡⟨ cong (λ x → r · (x ^ n)) (·Comm _ _) ⟩

              r · ((g · f) ^ n)

            ≡⟨ cong (r ·_) (^-ldist-· g f n) ⟩

              r · (g ^ n · f ^ n)

            ≡⟨ solve! R' ⟩

              1r · (1r · r · (g ^ n)) · (1r · (f ^ n) · 1r) ∎


     ϕ : R × S[fg] → R[1/f][1/g]
     ϕ = uncurry2 curriedϕ -- λ (r / (fg)ⁿ) → ((r / fⁿ) / gⁿ)

     curriedϕcohΣ : (r s r' s' u : R) → (p : u · r · s' ≡ u · r' · s)
                                      → (α : Σ[ n ∈ ℕ ] s ≡ (f · g) ^ n)
                                      → (β : Σ[ m ∈ ℕ ] s' ≡ (f · g) ^ m)
                                      → (γ : Σ[ l ∈ ℕ ] u ≡ (f · g) ^ l)
                                      → ϕ (r , s , PT.∣ α ∣₁) ≡ ϕ (r' , s' , PT.∣ β ∣₁)
     curriedϕcohΣ r s r' s' u p (n , s≡fgⁿ) (m , s'≡fgᵐ) (l , u≡fgˡ) =
      eq/ _ _ ( ( [ (g ^ l) , 1r , powersFormMultClosedSubset R' f .containsOne ]
                , PT.∣ l , ^-respects-/1 R' l ∣₁)
              , eq/ _ _ ((f ^ l , PT.∣ l , refl ∣₁) , path))
      where
      path : f ^ l · (g ^ l · transp (λ i → R) i0 r · transp (λ i → R) i0 (g ^ m))
                   · (1r · transp (λ i → R) i0 (f ^ m) · transp (λ i → R) i0 1r)
           ≡ f ^ l · (g ^ l · transp (λ i → R) i0 r' · transp (λ i → R) i0 (g ^ n))
                   · (1r · transp (λ i → R) i0 (f ^ n) · transp (λ i → R) i0 1r)
      path = f ^ l · (g ^ l · transp (λ i → R) i0 r · transp (λ i → R) i0 (g ^ m))
                   · (1r · transp (λ i → R) i0 (f ^ m) · transp (λ i → R) i0 1r)

           ≡⟨ (λ i → f ^ l · (g ^ l · transportRefl r i · transportRefl (g ^ m) i)
                           · (1r · transportRefl (f ^ m) i · transportRefl 1r i)) ⟩

             f ^ l · (g ^ l · r · g ^ m) · (1r · f ^ m · 1r)

           ≡⟨ solve! R' ⟩

             f ^ l · g ^ l · r · (g ^ m · f ^ m)

           ≡⟨ (λ i → ^-ldist-· f g l (~ i) · r · ^-ldist-· g f m (~ i)) ⟩

             (f · g) ^ l · r · (g · f) ^ m

           ≡⟨ cong (λ x → (f · g) ^ l · r · x ^ m) (·Comm _ _) ⟩

             (f · g) ^ l · r · (f · g) ^ m

           ≡⟨ (λ i → u≡fgˡ (~ i) · r · s'≡fgᵐ (~ i)) ⟩

             u · r · s'

           ≡⟨ p ⟩

             u · r' · s

           ≡⟨ (λ i → u≡fgˡ i · r' · s≡fgⁿ i) ⟩

             (f · g) ^ l · r' · (f · g) ^ n

           ≡⟨ cong (λ x → (f · g) ^ l · r' · x ^ n) (·Comm _ _) ⟩

             (f · g) ^ l · r' · (g · f) ^ n

           ≡⟨ (λ i → ^-ldist-· f g l i · r' · ^-ldist-· g f n i) ⟩

             f ^ l · g ^ l · r' · (g ^ n · f ^ n)

           ≡⟨ solve! R' ⟩

             f ^ l · (g ^ l · r' · g ^ n) · (1r · f ^ n · 1r)

           ≡⟨ (λ i → f ^ l · (g ^ l · transportRefl r' (~ i) · transportRefl (g ^ n) (~ i))
                           · (1r · transportRefl (f ^ n) (~ i) · transportRefl 1r (~ i))) ⟩

             f ^ l · (g ^ l · transp (λ i → R) i0 r' · transp (λ i → R) i0 (g ^ n))
                   · (1r · transp (λ i → R) i0 (f ^ n) · transp (λ i → R) i0 1r) ∎


     curriedϕcoh : (r s r' s' u : R) → (p : u · r · s' ≡ u · r' · s)
                                     → (α : ∃[ n ∈ ℕ ] s ≡ (f · g) ^ n)
                                     → (β : ∃[ m ∈ ℕ ] s' ≡ (f · g) ^ m)
                                     → (γ : ∃[ l ∈ ℕ ] u ≡ (f · g) ^ l)
                                     → ϕ (r , s , α) ≡ ϕ (r' , s' , β)
     curriedϕcoh r s r' s' u p = PT.elim (λ _ → isPropΠ2 (λ _ _ → squash/ _ _))
                           λ α → PT.elim (λ _ → isPropΠ (λ _ → squash/ _ _))
                           λ β → PT.rec (squash/ _ _)
                           λ γ →  curriedϕcohΣ r s r' s' u p α β γ

     ϕcoh : (a b : R × S[fg])
          → Loc._≈_ R' ([_ⁿ|n≥0] R' (f · g)) (powersFormMultClosedSubset R' (f · g)) a b
          → ϕ a ≡ ϕ b
     ϕcoh (r , s , α) (r' , s' , β) ((u , γ) , p) =  curriedϕcoh r s r' s' u p α β γ




   -- the map induced by the universal property
   open S⁻¹RUniversalProp R' ([_ⁿ|n≥0] R' (f · g)) (powersFormMultClosedSubset R' (f · g))
   χ : R[1/fg] → R[1/f][1/g]
   χ = S⁻¹RHasUniversalProp R[1/f][1/g]AsCommRing /1/1AsCommRingHom fⁿgⁿ/1/1∈R[1/f][1/g]ˣ .fst .fst .fst

   -- the sanity check:
   -- both maps send a fraction r/(fg)ⁿ to a double fraction,
   -- where numerator and denominator are almost the same fraction respectively.
   -- unfortunately the proofs that the denominators are powers are quite different for
   -- the two maps, but of course we can ignore them.
   -- The definition of χ introduces a lot of (1r ·_). Perhaps most surprisingly,
   -- we have to give the path eq1 for the equality of the numerator of the numerator.
   φ≡χ : ∀ r → φ r ≡ χ r
   φ≡χ = invElPropElim _ (λ _ → squash/ _ _) ℕcase
    where
    ℕcase : (r : R) (n : ℕ)
          → φ [ r , (f · g) ^ n , PT.∣ n , refl ∣₁ ] ≡ χ [ r , (f · g) ^ n , PT.∣ n , refl ∣₁ ]
    ℕcase r n = cong [_] (ΣPathP --look into the components of the double-fractions
              ( cong [_] (ΣPathP (eq1 , Σ≡Prop (λ x → S'[f] x .snd) (sym (·IdL _))))
              , Σ≡Prop (λ x → S'[f][g] x .snd) --ignore proof that denominator is power of g/1
              ( cong [_] (ΣPathP (sym (·IdL _) , Σ≡Prop (λ x → S'[f] x .snd) (sym (·IdL _)))))))
     where
     S'[f] = ([_ⁿ|n≥0] R' f)
     S'[f][g] = ([_ⁿ|n≥0] R[1/f]AsCommRing [ g , 1r , powersFormMultClosedSubset R' f .containsOne ])

     eq1 : transp (λ i → fst R') i0 r ≡ r · transp (λ i → fst R') i0 1r
     eq1 = transportRefl r ∙∙ sym (·IdR r) ∙∙ cong (r ·_) (sym (transportRefl 1r))
