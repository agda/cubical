{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.CommRing.Integers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Reflection.Base using (_$_) -- TODO: add this to Foundation.Function

open import Cubical.Data.Nat using (suc; zero)

open import Cubical.Structures.Axioms using (transferAxioms)
open import Cubical.Algebra.Ring as RRing using (ringequiv; RingEquiv)
open import Cubical.Algebra.CommRing

open RRing.RingΣTheory using (RawRingStructure; RawRingEquivStr; rawRingUnivalentStr)
open Cubical.Algebra.CommRing.CommRingΣTheory using (CommRingAxioms; CommRingStructure; CommRing→CommRingΣ; CommRingΣ→CommRing)

module _ where
  open import Cubical.HITs.Ints.BiInvInt
    renaming (
      _+_ to _+ℤ_;
      -_ to _-ℤ_;
      +-assoc to +ℤ-assoc;
      +-comm to +ℤ-comm
    )

  BiInvIntAsCommRing : CommRing {ℓ-zero}
  BiInvIntAsCommRing =
    makeCommRing
      zero (suc zero) _+ℤ_ _·_ _-ℤ_
      isSetBiInvInt
      +ℤ-assoc +-zero +-invʳ +ℤ-comm
      ·-assoc ·-identityʳ
      (λ x y z → sym (·-distribˡ x y z))
      ·-comm

  BiInvIntΣraw : TypeWithStr ℓ-zero RawRingStructure
  BiInvIntΣraw = BiInvInt , _+ℤ_ , 1 , _·_

module _ where
  open import Cubical.Data.Int as Int using (sucInt; predInt; Int) renaming
    ( _+_    to _+'_
    ; _·_    to _·'_
    ; -_     to -'_
    ; pos    to pos'
    ; negsuc to negsuc'
    )
  open import Cubical.HITs.Ints.BiInvInt renaming
    ( fwd to ⟦_⟧
    ; suc to sucᵇ
    )

  private
    suc-⟦⟧ : ∀ x → sucᵇ ⟦ x ⟧ ≡ ⟦ sucInt x ⟧
    suc-⟦⟧ (pos' n) = refl
    suc-⟦⟧ (negsuc' zero) = suc-pred _
    suc-⟦⟧ (negsuc' (suc n)) = suc-pred _

    pred-⟦⟧ : ∀ x → predl ⟦ x ⟧ ≡ ⟦ predInt x ⟧
    pred-⟦⟧ (pos' zero) = refl
    pred-⟦⟧ (pos' (suc n)) = pred-suc _
    pred-⟦⟧ (negsuc' zero) = refl
    pred-⟦⟧ (negsuc' (suc n)) = refl

    neg-⟦⟧ : ∀ x → - ⟦ x ⟧ ≡ ⟦ -' x ⟧
    neg-⟦⟧ (pos' zero) = refl
    neg-⟦⟧ (pos' (suc n)) = (λ i → predl (neg-⟦⟧ (pos' n) i)) ∙ pred-⟦⟧ (-' pos' n) ∙ cong ⟦_⟧ (Int.predInt-neg (pos' n))
    neg-⟦⟧ (negsuc' zero) = refl
    neg-⟦⟧ (negsuc' (suc n)) = (λ i → sucᵇ (neg-⟦⟧ (negsuc' n) i))

    pres1 : 1 ≡ ⟦ 1 ⟧
    pres1 = refl

    isHom+ : ∀ x y → ⟦ x +' y ⟧ ≡ ⟦ x ⟧ + ⟦ y ⟧
    isHom+ (pos' zero) y i = ⟦ Int.+-comm 0 y i ⟧
    isHom+ (pos' (suc n)) y =
      ⟦ pos' (suc n) +' y ⟧     ≡[ i ]⟨ ⟦ Int.sucInt+ (pos' n) y (~ i) ⟧ ⟩
      ⟦ sucInt (pos' n +' y) ⟧  ≡⟨ sym $ suc-⟦⟧ _ ⟩
      sucᵇ  ⟦ pos' n +' y ⟧     ≡[ i ]⟨ sucᵇ $ isHom+ (pos' n) y i ⟩
      sucᵇ (⟦ pos' n ⟧ + ⟦ y ⟧) ≡⟨ refl ⟩
      sucᵇ  ⟦ pos' n ⟧ + ⟦ y ⟧  ∎
    isHom+ (negsuc' zero) y = pred-suc-inj _ _ (λ i → predl (γ i)) where
      γ : sucᵇ (⟦ negsuc' zero +' y ⟧) ≡ sucᵇ (pred zero + ⟦ y ⟧)
      γ = suc-⟦⟧ (negsuc' zero +' y) ∙ (λ i → ⟦ (Int.sucInt+ (negsuc' zero) y ∙ Int.+-comm 0 y) i ⟧) ∙ sym (suc-pred ⟦ y ⟧)
    isHom+ (negsuc' (suc n)) y = (λ i → ⟦ Int.predInt+ (negsuc' n) y (~ i) ⟧) ∙ sym (pred-⟦⟧ (negsuc' n +' y)) ∙ (λ i → pred $ isHom+ (negsuc' n) y i)

    isHom· : ∀ x y → ⟦ x ·' y ⟧ ≡ ⟦ x ⟧ · ⟦ y ⟧
    isHom· (pos' zero) y i = ⟦ Int.signed-zero (Int.sgn y) i ⟧
    isHom· (pos' (suc n)) y =
      ⟦ pos' (suc n) ·' y ⟧      ≡⟨ cong ⟦_⟧ $ Int.·-pos-suc n y ⟩
      ⟦ y +' pos' n ·' y ⟧       ≡⟨ isHom+ y _ ⟩
      ⟦ y ⟧ + ⟦ pos' n ·' y ⟧    ≡[ i ]⟨ ⟦ y ⟧ + isHom· (pos' n) y i ⟩
      ⟦ y ⟧ + ⟦ pos' n ⟧ · ⟦ y ⟧ ≡⟨ (λ i → ⟦ y ⟧ + ·-comm ⟦ pos' n ⟧ ⟦ y ⟧ i) ∙ sym (·-suc ⟦ y ⟧ ⟦ pos' n ⟧) ∙ ·-comm ⟦ y ⟧ _ ⟩
      sucᵇ ⟦ pos' n ⟧ · ⟦ y ⟧ ∎
    isHom· (negsuc' zero) y =
      ⟦ -1 ·'  y ⟧ ≡⟨ cong ⟦_⟧ (Int.·-neg1 y) ⟩
      ⟦ -'     y ⟧ ≡⟨ sym (neg-⟦⟧ y) ⟩
        -    ⟦ y ⟧ ≡⟨ sym (·-neg1 ⟦ y ⟧) ⟩
        -1 · ⟦ y ⟧ ∎
    isHom· (negsuc' (suc n)) y =
      ⟦ negsuc' (suc n) ·' y ⟧         ≡⟨ cong ⟦_⟧ $ Int.·-negsuc-suc n y ⟩
      ⟦ -' y   +'  negsuc' n   ·'  y ⟧ ≡⟨ isHom+ (-' y) _ ⟩
      ⟦ -' y ⟧ + ⟦ negsuc' n   ·'  y ⟧ ≡[ i ]⟨ ⟦ -' y ⟧ + isHom· (negsuc' n) y i ⟩
      ⟦ -' y ⟧ + ⟦ negsuc' n ⟧ · ⟦ y ⟧ ≡⟨ cong₂ _+_ (sym (neg-⟦⟧ y)) refl ⟩
      -  ⟦ y ⟧ + ⟦ negsuc' n ⟧ · ⟦ y ⟧ ≡⟨ (λ i → - ⟦ y ⟧ + ·-comm ⟦ negsuc' n ⟧ ⟦ y ⟧ i) ∙ sym (·-pred ⟦ y ⟧ ⟦ negsuc' n ⟧) ∙ ·-comm ⟦ y ⟧ _ ⟩
      pred ⟦ negsuc' n ⟧ · ⟦ y ⟧       ∎

    ⟦⟧-isEquiv : isEquiv ⟦_⟧
    ⟦⟧-isEquiv = isoToIsEquiv (iso ⟦_⟧ bwd fwd-bwd bwd-fwd)

  IntΣraw : TypeWithStr ℓ-zero RawRingStructure
  IntΣraw = Int , _+'_ , 1 , _·'_

  BiInvInt≃Int-Σraw : BiInvIntΣraw ≃[ RawRingEquivStr ] IntΣraw
  BiInvInt≃Int-Σraw = ≃[]-swap rawRingUnivalentStr IntΣraw BiInvIntΣraw ((_ , ⟦⟧-isEquiv) , (isHom+ , pres1 , isHom·))

  Int-CommRingAxioms : CommRingAxioms Int (str IntΣraw)
  Int-CommRingAxioms = transferAxioms {S = RawRingStructure} rawRingUnivalentStr {axioms = CommRingAxioms} (CommRing→CommRingΣ BiInvIntAsCommRing) IntΣraw BiInvInt≃Int-Σraw

  IntΣ : TypeWithStr _ CommRingStructure
  IntΣ = (typ IntΣraw) , (str IntΣraw) , Int-CommRingAxioms

  IntAsCommRing : CommRing
  IntAsCommRing = CommRingΣ→CommRing IntΣ

  Int≃BiInvInt-CommRingEquiv : Σ[ e ∈ ⟨ IntAsCommRing ⟩ ≃ ⟨ BiInvIntAsCommRing ⟩ ] CommRingEquiv IntAsCommRing BiInvIntAsCommRing e
  Int≃BiInvInt-CommRingEquiv .fst = _ , ⟦⟧-isEquiv
  Int≃BiInvInt-CommRingEquiv .snd = ringequiv pres1 isHom+ isHom·

  Int≡BiInvInt-AsCommRing : IntAsCommRing ≡ BiInvIntAsCommRing
  Int≡BiInvInt-AsCommRing = CommRingPath _ _ .fst Int≃BiInvInt-CommRingEquiv
