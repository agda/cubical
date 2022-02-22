{-
  This file defines cohomology of a type with
  coefficients in a dependent spectrum over it.

  This coincides with ZCohomology when the coefficients
  are constantly the Eilenberg-MacLane spectrum for ℤ
-}
{-# OPTIONS --safe #-}
module Cubical.Cohomology.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.Group.Base using (Group; GroupStr)
open import Cubical.Algebra.AbGroup.Base

open import Cubical.Data.Int.Base hiding (_·_)
open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.HomotopyGroup.Base
open import Cubical.HITs.SetTruncation hiding (map)

open import Cubical.Homotopy.Spectrum
open import Cubical.Homotopy.Prespectrum
open import Cubical.Homotopy.Loopspace renaming (EH to isCommΩ)
open import Cubical.Structures.Successor

private
  variable
    ℓ : Level

open Spectrum

module _ (X : Type ℓ) (A : (x : X) → Spectrum ℓ) where
  CoHomClasses : ℤ → Pointed ℓ
  CoHomClasses k = Πᵘ∙ X (λ x → space (A x) k)
  
  CoHomType : ℤ → Type ℓ
  CoHomType k = ∥  (fst (CoHomClasses k)) ∥₂

  private
    commDegreeΩOnce : (k : ℤ) → (CoHomClasses k) ≃∙ Πᵘ∙ X (λ x → Ω (space (A x) (sucℤ k))) 
    commDegreeΩOnce k =
      (equivΠCod (λ x → fst (equivΩAt x))) ,
       λ i x → snd (equivΩAt x) i
      where equivΩAt : (x : X) → space (A x) k ≃∙ Ω (space (A x) (sucℤ k)) 
            equivΩAt x = (fst (map (A x) k) , equiv (A x) k) , snd (map (A x) k)

    commDegreeΩOnce' : (k : ℤ) → (CoHomClasses k) ≃∙ Ω (CoHomClasses (sucℤ k))
    commDegreeΩOnce' k =
      compEquiv∙ (commDegreeΩOnce k)
                 ((isoToEquiv (iso (λ f → (λ i x → f x i)) (λ f → (λ x i → f i x)) (λ _ → refl) λ _ → refl)) , refl)
                            
  commDegreeΩ : (k : ℤ) (n : ℕ) → (CoHomClasses k) ≃∙ (Ω^ n) (CoHomClasses (k + (pos n)))
  commDegreeΩ k ℕ.zero = idEquiv∙ _
  commDegreeΩ k (ℕ.suc n) =
    (CoHomClasses k)                                   ≃∙⟨ commDegreeΩ k n ⟩
    (Ω^ n) (CoHomClasses (k + (pos n)))                ≃∙⟨ Ω^≃∙ n (commDegreeΩOnce' (k + pos n)) ⟩
    (Ω^ n) (Ω (CoHomClasses (sucℤ (k + (pos n)))))     ≃∙⟨ invEquiv∙ (e n) ⟩
    (Ω^ (ℕ.suc n)) (CoHomClasses (sucℤ (k + (pos n)))) ∎≃∙
    where e : {A : Pointed ℓ} (n : ℕ) → (Ω^ (ℕ.suc n)) A ≃∙ (Ω^ n) (Ω A)
          e ℕ.zero = isoToEquiv (flipΩIso ℕ.zero) , transportRefl refl
          e (ℕ.suc n) = isoToEquiv (flipΩIso (ℕ.suc n)) , flipΩrefl n
    
  {-
    Abelian group structure
  -}
  module abGroupStr (k : ℤ) where
    {-
      Use an equivalent type, where the group structure is just
      given by the homotopy group functor
    -}
    CoHomAsGroup : Group ℓ
    CoHomAsGroup = (π^ 2) (Πᵘ∙ X  (λ x → (space (A x) (2 + k))))

    open GroupStr (snd CoHomAsGroup)

    isComm :  (a b : fst CoHomAsGroup) → a · b ≡ b · a
    isComm = elim2 (λ _ _ → isSetPathImplicit)
                   λ a b → ∣ a ∙ b ∣₂ ≡⟨ cong ∣_∣₂ (isCommΩ 0 a b) ⟩
                           ∣ b ∙ a ∣₂ ∎

  CoHom : ℤ → AbGroup ℓ
  CoHom k = Group→AbGroup (abGroupStr.CoHomAsGroup k) (abGroupStr.isComm k)

{-
  Functoriality in the type argument
-}
module _ {Y X : Type ℓ} (f : Y → X) (A : (x : X) → Spectrum ℓ) where
  {-
    The following will be used as coefficients for the
    cohomology of Y
  -}
  fA : (y : Y) → Spectrum ℓ
  fA y = A (f y)

  coHomMap : (k : ℤ) → AbGroupHom (CoHom X A k) (CoHom Y fA k)
  coHomMap k = (rec isSetSetTrunc λ l → ∣ {! λ  y → l (f y)!} ∣₂) ,
               {!!}
