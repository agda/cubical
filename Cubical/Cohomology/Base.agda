{-
  This file defines cohomology of a type with
  coefficients in a dependent spectrum over it.
  * Cohom and Cohom' are two versions of the cohomology groups
    - the only difference is the carrier type.
  * 'commDegreeΩ' commutes Ωs with degree shifts of the spectrum
  * 'cohomMap' implement the application of the cohomology functors
    to maps between types

  This general cohomology coincides with ZCohomology when the coefficients
  are constantly the Eilenberg-MacLane spectrum for ℤ (not proven here/yet)
-}
module Cubical.Cohomology.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence  using (ua)

open import Cubical.Functions.FunExtEquiv using (funExtEquiv)

open import Cubical.Algebra.Group.Base using (Group; GroupStr)
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Data.Int.Base hiding (_·_)
open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Homotopy.Group.Base
open import Cubical.HITs.SetTruncation hiding (map)

open import Cubical.Homotopy.Spectrum
open import Cubical.Homotopy.Loopspace renaming (EH to isCommΩ)
open import Cubical.Structures.Successor

private
  variable
    ℓ : Level

open Spectrum

module _ (X : Type ℓ) (A : (x : X) → Spectrum ℓ) where
  CohomClasses : ℤ → Pointed ℓ
  CohomClasses k = Πᵘ∙ X (λ x → space (A x) k)

  CohomType : ℤ → Type ℓ
  CohomType k = ∥  (fst (CohomClasses k)) ∥₂

  private
    commDegreeΩOnce : (k : ℤ) → (CohomClasses k) ≃∙ Πᵘ∙ X (λ x → Ω (space (A x) (sucℤ k)))
    commDegreeΩOnce k =
      (equivΠCod (λ x → fst (equivΩAt x))) ,
       λ i x → snd (equivΩAt x) i
      where equivΩAt : (x : X) → space (A x) k ≃∙ Ω (space (A x) (sucℤ k))
            equivΩAt x = (fst (map (A x) k) , equiv (A x) k) , snd (map (A x) k)

    commDegreeΩOnce' : (k : ℤ) → (CohomClasses k) ≃∙ Ω (CohomClasses (sucℤ k))
    commDegreeΩOnce' k =
      compEquiv∙ (commDegreeΩOnce k)
                 (funExtEquiv , refl)

  commDegreeΩ : (k : ℤ) (n : ℕ) → (CohomClasses k) ≃∙ (Ω^ n) (CohomClasses (k + (pos n)))
  commDegreeΩ k ℕ.zero = idEquiv∙ _
  commDegreeΩ k (ℕ.suc n) =
    CohomClasses k                                     ≃∙⟨ commDegreeΩ k n ⟩
    (Ω^ n) (CohomClasses (k + (pos n)))                ≃∙⟨ Ω^≃∙ n (commDegreeΩOnce' (k + pos n)) ⟩
    (Ω^ n) (Ω (CohomClasses (sucℤ (k + (pos n)))))     ≃∙⟨ invEquiv∙ (e n) ⟩
    (Ω^ (ℕ.suc n)) (CohomClasses (sucℤ (k + (pos n)))) ∎≃∙
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
      (index of homotopy groups is off by one below, we actually take π₂,
      to get an abelian group)
    -}
    CohomAsGroup : Group ℓ
    CohomAsGroup = (πGr 1) (Πᵘ∙ X  (λ x → (space (A x) (k + 2))))

    open GroupStr (snd CohomAsGroup)

    isComm :  (a b : fst CohomAsGroup) → a · b ≡ b · a
    isComm = elim2 (λ _ _ → isSetPathImplicit)
                   λ a b → ∣ a ∙ b ∣₂ ≡⟨ cong ∣_∣₂ (isCommΩ 0 a b) ⟩
                           ∣ b ∙ a ∣₂ ∎

    π₂AbGroup : AbGroup ℓ
    π₂AbGroup = Group→AbGroup CohomAsGroup isComm

  module _ (k : ℤ) where
    Cohom' : AbGroup ℓ
    Cohom' = abGroupStr.π₂AbGroup k

    CohomType' : Type ℓ
    CohomType' = fst (abGroupStr.π₂AbGroup k)

    private
      shiftΩTwicePath : fst (abGroupStr.π₂AbGroup k) ≡ CohomType k
      shiftΩTwicePath = sym (cong ∥_∥₂ (ua (fst (commDegreeΩ k 2))))

    Cohom : AbGroup ℓ
    Cohom = CohomType k , subst AbGroupStr shiftΩTwicePath (snd (abGroupStr.π₂AbGroup k))

    CohomPath : Cohom' ≡ Cohom
    CohomPath = ΣPathTransport→PathΣ Cohom' Cohom (shiftΩTwicePath , refl)

    CohomEquiv : AbGroupEquiv Cohom' Cohom
    CohomEquiv = fst (invEquiv (AbGroupPath Cohom' Cohom)) CohomPath

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


  cohomMap' : (k : ℤ) → AbGroupHom (Cohom' X A k) (Cohom' Y fA k)
  cohomMap' k = πHom 1 mapOnClasses  -- apply π₂ to a map on cohomology classes
            where
             mapOnClasses : CohomClasses X A (k + 2) →∙ CohomClasses Y fA (k + 2)
             mapOnClasses = (λ l → (λ y → l (f y))) ,
                            refl

  cohomMap : (k : ℤ) → AbGroupHom (Cohom X A k) (Cohom Y fA k)
  cohomMap k = compGroupHom
                 (compGroupHom (GroupEquiv→GroupHom (invGroupEquiv (CohomEquiv X A k)))
                               (cohomMap' k))
                 (GroupEquiv→GroupHom (CohomEquiv Y fA k))
