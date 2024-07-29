{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebraAlt.QuotientAlgebra where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset using (_∈_; _⊆_)
open import Cubical.Foundations.Structure

open import Cubical.HITs.SetQuotients hiding (_/_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Algebra.CommRing
import Cubical.Algebra.CommRing.Quotient as CommRing
import Cubical.Algebra.Ring.Quotient as Ring
open import Cubical.Algebra.CommRing.Ideal hiding (IdealsIn)
open import Cubical.Algebra.CommAlgebraAlt.Base
open import Cubical.Algebra.CommAlgebraAlt.Ideal
-- open import Cubical.Algebra.CommAlgebra.Kernel
-- open import Cubical.Algebra.CommAlgebra.Instances.Unit
-- open import Cubical.Algebra.Algebra.Base using (IsAlgebraHom; isPropIsAlgebraHom)
open import Cubical.Algebra.Ring
-- open import Cubical.Algebra.Ring.Ideal using (isIdeal)
open import Cubical.Tactics.CommRingSolver
-- open import Cubical.Algebra.Algebra.Properties
-- open AlgebraHoms using (_∘a_)

private
  variable
    ℓ : Level

{-
  The definition of the quotient algebra (_/_ below) is marked opaque to avoid
  long type checking times. All other definitions that need to "look into" this
  opaque definition must be in an opaque block that unfolds the definition of _/_.
-}

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn R A) where
  open CommRingStr {{...}} -- hiding (_-_; -_; ·IdL ; ·DistR+) renaming (_·_ to _·R_; _+_ to _+R_)
  open CommAlgebraStr {{...}}
  open RingTheory (CommRing→Ring (fst A)) using (-DistR·)
  open RingHoms
  instance
    _ : CommRingStr ⟨ R ⟩
    _ = snd R
    _ : CommRingStr ⟨ A .fst ⟩
    _ = A .fst .snd
    _ = A

  _/_ : CommAlgebra R ℓ
  _/_ = ((fst A) CommRing./ I) ,
        (CommRing.quotientHom (fst A) I ∘r A .snd)

  quotientHom : CommAlgebraHom {R = R} A (_/_)
  quotientHom = (CommRing.quotientHom (fst A) I) , refl

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn R A) where
  open CommRingStr ⦃...⦄
  open CommAlgebraStr ⦃...⦄


  instance
    _ : CommRingStr ⟨ R ⟩
    _ = snd R
    _ : CommRingStr ⟨ A ⟩ₐ
    _ = A .fst .snd
    _ = A

{-

  opaque
    unfolding _/_

    -- sanity check / maybe a helper function some day
    -- (These two rings are not definitionally equal, but only because of proofs, not data.)
    CommForget/ : RingEquiv (CommAlgebra→Ring (A / I)) ((CommAlgebra→Ring A) Ring./ (CommIdeal→Ideal I))
    fst CommForget/ = idEquiv _
    IsRingHom.pres0 (snd CommForget/) = refl
    IsRingHom.pres1 (snd CommForget/) = refl
    IsRingHom.pres+ (snd CommForget/) = λ _ _ → refl
    IsRingHom.pres· (snd CommForget/) = λ _ _ → refl
    IsRingHom.pres- (snd CommForget/) = λ _ → refl

  module _
    (B : CommAlgebra R ℓ)
    (ϕ : CommAlgebraHom A B)
    (I⊆kernel : (fst I) ⊆ (fst (kernel A B ϕ)))
    where

    open IsAlgebraHom
    open RingTheory (CommRing→Ring (CommAlgebra→CommRing B))

    private
      instance
        _ : CommAlgebraStr R ⟨ B ⟩
        _ = snd B
        _ : CommRingStr ⟨ B ⟩
        _ = snd (CommAlgebra→CommRing B)

    opaque
      unfolding _/_

      inducedHom : CommAlgebraHom (A / I) B
      fst inducedHom =
        rec is-set (λ x → fst ϕ x)
          λ a b a-b∈I →
            equalByDifference
              (fst ϕ a) (fst ϕ b)
              ((fst ϕ a) - (fst ϕ b)     ≡⟨ cong (λ u → (fst ϕ a) + u) (sym (IsAlgebraHom.pres- (snd ϕ) _)) ⟩
               (fst ϕ a) + (fst ϕ (- b)) ≡⟨ sym (IsAlgebraHom.pres+ (snd ϕ) _ _) ⟩
               fst ϕ (a - b)             ≡⟨ I⊆kernel (a - b) a-b∈I ⟩
               0r ∎)
      pres0 (snd inducedHom) = pres0 (snd ϕ)
      pres1 (snd inducedHom) = pres1 (snd ϕ)
      pres+ (snd inducedHom) = elimProp2 (λ _ _ → is-set _ _) (pres+ (snd ϕ))
      pres· (snd inducedHom) = elimProp2 (λ _ _ → is-set _ _) (pres· (snd ϕ))
      pres- (snd inducedHom) = elimProp (λ _ → is-set _ _) (pres- (snd ϕ))
      pres⋆ (snd inducedHom) = λ r → elimProp (λ _ → is-set _ _) (pres⋆ (snd ϕ) r)

    opaque
      unfolding inducedHom quotientHom

      inducedHom∘quotientHom : inducedHom ∘a quotientHom A I ≡ ϕ
      inducedHom∘quotientHom = Σ≡Prop (isPropIsCommAlgebraHom {M = A} {N = B}) (funExt (λ a → refl))

  opaque
    unfolding quotientHom

    injectivePrecomp : (B : CommAlgebra R ℓ) (f g : CommAlgebraHom (A / I) B)
                       → f ∘a (quotientHom A I) ≡ g ∘a (quotientHom A I)
                       → f ≡ g
    injectivePrecomp B f g p =
      Σ≡Prop
        (λ h → isPropIsCommAlgebraHom {M = A / I} {N = B} h)
        (descendMapPath (fst f) (fst g) is-set
                        λ x → λ i → fst (p i) x)
      where
      instance
        _ : CommAlgebraStr R ⟨ B ⟩
        _ = str B


{- trivial quotient -}
module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) where
  open CommAlgebraStr (snd A)

  opaque
    unfolding _/_

    oneIdealQuotient : CommAlgebraEquiv (A / (1Ideal A)) (UnitCommAlgebra R {ℓ' = ℓ})
    fst oneIdealQuotient =
      isoToEquiv (iso (fst (terminalMap R (A / (1Ideal A))))
                      (λ _ → [ 0a ])
                      (λ _ → isPropUnit* _ _)
                      (elimProp (λ _ → squash/ _ _)
                                λ a → eq/ 0a a tt*))
    snd oneIdealQuotient = snd (terminalMap R (A / (1Ideal A)))

  opaque
    unfolding quotientHom

    zeroIdealQuotient : CommAlgebraEquiv A (A / (0Ideal A))
    fst zeroIdealQuotient =
      let open RingTheory (CommRing→Ring (CommAlgebra→CommRing A))
      in isoToEquiv (iso (fst (quotientHom A (0Ideal A)))
                      (rec is-set (λ x → x) λ x y x-y≡0 → equalByDifference x y x-y≡0)
                      (elimProp (λ _ → squash/ _ _) λ _ → refl)
                      λ _ → refl)
    snd zeroIdealQuotient = snd (quotientHom A (0Ideal A))

[_]/ : {R : CommRing ℓ} {A : CommAlgebra R ℓ} {I : IdealsIn A}
       → (a : fst A) → fst (A / I)
[_]/ = fst (quotientHom _ _)



module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn A) where
  open CommIdeal using (isPropIsCommIdeal)

  private
    π : CommAlgebraHom A (A / I)
    π = quotientHom A I

  opaque
    unfolding quotientHom

    kernel≡I : kernel A (A / I) π ≡ I
    kernel≡I =
      kernel A (A / I) π ≡⟨ Σ≡Prop
                              (isPropIsCommIdeal (CommAlgebra→CommRing A))
                              refl ⟩
      _                  ≡⟨  CommRing.kernel≡I {R = CommAlgebra→CommRing A} I ⟩
      I                  ∎


module _
  {R : CommRing ℓ}
  {A : CommAlgebra R ℓ}
  {I : IdealsIn A}
  where

  opaque
    unfolding quotientHom

    isZeroFromIdeal : (x : ⟨ A ⟩) → x ∈ (fst I) → fst (quotientHom A I) x ≡ CommAlgebraStr.0a (snd (A / I))
    isZeroFromIdeal x x∈I = eq/ x 0a (subst (_∈ fst I) (solve! (CommAlgebra→CommRing A)) x∈I )
      where
        open CommAlgebraStr (snd A)
-}
