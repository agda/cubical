{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.CommAlgebra.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Reflection.StrictEquiv

open import Cubical.Structures.Axioms
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra.Base

private
  variable
    ℓ ℓ′ : Level


-- An R-algebra is the same as a CommRing A with a CommRingHom φ : R → A
module CommAlgChar (R : CommRing ℓ) where
 open Iso
 open IsRingHom
 open CommRingTheory


 CommRingWithHom : Type (ℓ-suc ℓ)
 CommRingWithHom = Σ[ A ∈ CommRing ℓ ] CommRingHom R A

 toCommAlg : CommRingWithHom → CommAlgebra R ℓ
 toCommAlg (A , φ , φIsHom) = ⟨ A ⟩ , ACommAlgStr
  where
  open CommRingStr (snd A)
  ACommAlgStr : CommAlgebraStr R ⟨ A ⟩
  CommAlgebraStr.0a ACommAlgStr = 0r
  CommAlgebraStr.1a ACommAlgStr = 1r
  CommAlgebraStr._+_ ACommAlgStr = _+_
  CommAlgebraStr._·_ ACommAlgStr = _·_
  CommAlgebraStr.- ACommAlgStr = -_
  CommAlgebraStr._⋆_ ACommAlgStr r a = (φ r) · a
  CommAlgebraStr.isCommAlgebra ACommAlgStr = makeIsCommAlgebra
   is-set +Assoc +Rid +Rinv +Comm ·Assoc ·Lid ·Ldist+ ·-comm
   (λ _ _ x → cong (λ y →  y · x) (pres· φIsHom _ _) ∙ sym (·Assoc _ _ _))
   (λ _ _ x → cong (λ y → y · x) (pres+ φIsHom _ _) ∙ ·Ldist+ _ _ _)
   (λ _ _ _ → ·Rdist+ _ _ _)
   (λ x → cong (λ y → y · x) (pres1 φIsHom) ∙ ·Lid x)
   (λ _ _ _ → sym (·Assoc _ _ _))


 fromCommAlg : CommAlgebra R ℓ → CommRingWithHom
 fromCommAlg A = (CommAlgebra→CommRing A) , φ , φIsHom
  where
  open CommRingStr (snd R) renaming (_·_ to _·r_) hiding (·Lid)
  open CommAlgebraStr (snd A)
  open AlgebraTheory (CommRing→Ring R) (CommAlgebra→Algebra A)
  φ : ⟨ R ⟩ → ⟨ A ⟩
  φ r = r ⋆ 1a
  φIsHom : IsRingHom (CommRing→Ring R .snd) φ (CommRing→Ring (CommAlgebra→CommRing A) .snd)
  φIsHom = makeIsRingHom (⋆-lid _) (λ _ _ → ⋆-ldist _ _ _)
           λ x y → cong (λ a → (x ·r y) ⋆ a) (sym (·Lid _)) ∙ ⋆Dist· _ _ _ _


 CommRingWithHomRoundTrip : (Aφ : CommRingWithHom) → fromCommAlg (toCommAlg Aφ) ≡ Aφ
 CommRingWithHomRoundTrip (A , φ) = ΣPathP (APath , φPathP)
  where
  open CommRingStr
  -- note that the proofs of the axioms might differ!
  APath : fst (fromCommAlg (toCommAlg (A , φ))) ≡ A
  fst (APath i) = ⟨ A ⟩
  0r (snd (APath i)) = 0r (snd A)
  1r (snd (APath i)) = 1r (snd A)
  _+_ (snd (APath i)) = _+_ (snd A)
  _·_ (snd (APath i)) = _·_ (snd A)
  -_ (snd (APath i)) = -_ (snd A)
  isCommRing (snd (APath i)) = isProp→PathP (λ i → isPropIsCommRing _ _ _ _ _ )
             (isCommRing (snd (fst (fromCommAlg (toCommAlg (A , φ)))))) (isCommRing (snd A)) i

  -- this only works because fst (APath i) = fst A definitionally!
  φPathP : PathP (λ i → CommRingHom R (APath i)) (snd (fromCommAlg (toCommAlg (A , φ)))) φ
  φPathP = RingHomPathP _ _ _ _ _ _ λ i x → ·Rid (snd A) (fst φ x) i


 CommAlgRoundTrip : (A : CommAlgebra R ℓ) → toCommAlg (fromCommAlg A) ≡ A
 CommAlgRoundTrip A = ΣPathP (refl , AlgStrPathP)
  where
  open CommAlgebraStr ⦃...⦄
  instance
   _ = snd A
  AlgStrPathP : PathP (λ i → CommAlgebraStr R ⟨ A ⟩) (snd (toCommAlg (fromCommAlg A))) (snd A)
  CommAlgebraStr.0a (AlgStrPathP i) = 0a
  CommAlgebraStr.1a (AlgStrPathP i) = 1a
  CommAlgebraStr._+_ (AlgStrPathP i) = _+_
  CommAlgebraStr._·_ (AlgStrPathP i) = _·_
  CommAlgebraStr.-_ (AlgStrPathP i) = -_
  CommAlgebraStr._⋆_ (AlgStrPathP i) r x = (⋆-lassoc r 1a x ∙ cong (r ⋆_) (·Lid x)) i
  CommAlgebraStr.isCommAlgebra (AlgStrPathP i) = isProp→PathP
    (λ i → isPropIsCommAlgebra _ _ _ _ _ _ (CommAlgebraStr._⋆_ (AlgStrPathP i)))
    (CommAlgebraStr.isCommAlgebra (snd (toCommAlg (fromCommAlg A)))) isCommAlgebra i


 CommAlgIso : Iso (CommAlgebra R ℓ) CommRingWithHom
 fun CommAlgIso = fromCommAlg
 inv CommAlgIso = toCommAlg
 rightInv CommAlgIso = CommRingWithHomRoundTrip
 leftInv CommAlgIso = CommAlgRoundTrip
