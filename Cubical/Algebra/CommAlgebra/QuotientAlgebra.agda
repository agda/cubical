{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.CommAlgebra.QuotientAlgebra where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset using (_∈_; _⊆_)
open import Cubical.Foundations.Structure

open import Cubical.HITs.SetQuotients hiding (_/_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Algebra.CommRing
import Cubical.Algebra.CommRing.Quotient as CommRing
open import Cubical.Algebra.CommRing.Ideal hiding (IdealsIn)
open import Cubical.Algebra.CommAlgebra.Base
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.Kernel
open import Cubical.Algebra.CommAlgebra.Instances.Unit
open import Cubical.Algebra.Ring
open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ') (I : IdealsIn R A) where
  open CommRingStr ⦃...⦄
  open CommAlgebraStr ⦃...⦄
  open RingTheory (CommRing→Ring (fst A)) using (-DistR·)
  instance
    _ : CommRingStr ⟨ R ⟩
    _ = snd R
    _ : CommRingStr ⟨ A .fst ⟩
    _ = A .fst .snd
    _ = A

  _/_ : CommAlgebra R ℓ'
  _/_ = ((fst A) CommRing./ I) ,
        (withOpaqueStr $ (CommRing.quotientHom (fst A) I ∘cr A .snd))

  quotientHom : CommAlgebraHom A (_/_)
  quotientHom = CommRingHom→CommAlgebraHom (CommRing.quotientHom (fst A) I) $ CommRingHom≡ refl

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn R A) where
  open CommRingStr ⦃...⦄
  open CommAlgebraStr ⦃...⦄

  instance
    _ : CommRingStr ⟨ R ⟩
    _ = snd R
    _ : CommRingStr ⟨ A ⟩ₐ
    _ = A .fst .snd
    _ = A

  module _
    (B : CommAlgebra R ℓ)
    (ϕ : CommAlgebraHom A B)
    (I⊆kernel : (fst I) ⊆ (fst (kernel A B ϕ)))
    where

    open RingTheory (CommRing→Ring (CommAlgebra→CommRing B))

    open CommAlgebraStr ⦃...⦄
    private
      instance
        _ = B
        _ : CommRingStr ⟨ B ⟩ₐ
        _ = snd (CommAlgebra→CommRing B)

    inducedHom : CommAlgebraHom (A / I) B
    inducedHom =
      CommRingHom→CommAlgebraHom ind (CommRingHom≡ p)
        where
        ind = (CommRing.UniversalProperty.inducedHom
                      (CommAlgebra→CommRing A)
                      (CommAlgebra→CommRing B)
                      I
                      (CommAlgebraHom→CommRingHom ϕ)
                      I⊆kernel)

        step1 = cong (ind .fst ∘_) (sym (cong fst (CommAlgebraHom→Triangle $ quotientHom A I)))
        step2 = cong fst (compAssocCommRingHom (A .snd) (CommRing.quotientHom (A .fst) I) ind)
        step3 = cong (_∘ A .snd .fst) (cong fst (CommRing.UniversalProperty.isSolution (A .fst) (B .fst) I (CommAlgebraHom→CommRingHom ϕ) I⊆kernel))
        opaque
          p : (ind .fst ∘ snd (A / I) .fst) ≡ B .snd .fst
          p = ind .fst ∘ snd (A / I) .fst                     ≡⟨ step1 ⟩
              ind .fst ∘ quotientHom A I .fst ∘ A .snd .fst   ≡⟨ step2 ⟩
              ind .fst ∘ quotientHom A I .fst ∘ A .snd .fst   ≡⟨ step3 ⟩
              ϕ .fst ∘ A .snd .fst                            ≡⟨ cong fst (CommAlgebraHom→Triangle ϕ) ⟩
              B .snd .fst ∎

    opaque
      inducedHom∘quotientHom : inducedHom ∘ca quotientHom A I ≡ ϕ
      inducedHom∘quotientHom = CommAlgebraHom≡ (funExt (λ _ → refl))

    opaque
      isUnique : (ψ : CommAlgebraHom (A / I) B) (ψIsSolution : ⟨ ψ ⟩ₐ→ ∘ ⟨ quotientHom A I ⟩ₐ→ ≡ ⟨ ϕ ⟩ₐ→)
               → ψ ≡ inducedHom
      isUnique ψ ψIsSolution =
        CommAlgebraHom≡
         (cong fst $
          CommRing.UniversalProperty.isUnique
            (A .fst) (B .fst) I ⟨ ϕ ⟩ᵣ→ I⊆kernel ⟨ ψ ⟩ᵣ→ ψIsSolution)



module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ') (I : IdealsIn R A) where
  open CommRingStr {{...}}
  open CommAlgebraStr {{...}}

  opaque
    quotientHomEpi : (S : hSet ℓ'')
                     → (f g : ⟨ A / I ⟩ₐ → ⟨ S ⟩)
                     → f ∘ ⟨ quotientHom A I ⟩ₐ→ ≡ g ∘ ⟨ quotientHom A I ⟩ₐ→
                     → f ≡ g
    quotientHomEpi = CommRing.quotientHomEpi (fst A) I


{- trivial quotient -}
module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) where
  open CommRingStr (A .fst .snd)

  oneIdealQuotient : CommAlgebraEquiv (A / (1Ideal R A)) (UnitCommAlgebra R {ℓ' = ℓ})
  oneIdealQuotient .fst .fst =
    withOpaqueStr $
    isoToEquiv (iso ⟨ terminalMap R (A / 1Ideal R A) ⟩ₐ→
                      (λ _ → [ 0r ])
                      (λ _ → isPropUnit* _ _)
                      (elimProp (λ _ → squash/ _ _) (λ a → eq/ 0r a tt*)))
  oneIdealQuotient .fst .snd = terminalMap R (A / 1Ideal R A) .fst .snd
  oneIdealQuotient .snd = terminalMap R (A / (1Ideal R A)) .snd

{-

  zeroIdealQuotient : CommAlgebraEquiv A (A / (0Ideal R A))
  zeroIdealQuotient .fst .fst =
    withOpaqueStr $
    let open RingTheory (CommRing→Ring (CommAlgebra→CommRing A))
    in isoToEquiv (iso ⟨ (quotientHom A (0Ideal R A)) ⟩ₐ→
                      (rec is-set (λ x → x) λ x y x-y≡0 → equalByDifference x y x-y≡0)
                      (elimProp (λ _ → squash/ _ _) λ _ → refl)
                      λ _ → refl)
  zeroIdealQuotient .fst .snd =  quotientHom A (0Ideal R A) .fst .snd
  zeroIdealQuotient .snd = quotientHom A (0Ideal R A) .snd

[_]/ : {R : CommRing ℓ} {A : CommAlgebra R ℓ} {I : IdealsIn R A}
       → (a : ⟨ A ⟩ₐ) → ⟨ A / I ⟩ₐ
[_]/ = ⟨ quotientHom _ _ ⟩ₐ→

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn R A) where
  open CommIdeal using (isPropIsCommIdeal)

  private
    π : CommAlgebraHom A (A / I)
    π = quotientHom A I

  opaque
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
  {I : IdealsIn R A}
  where
  open CommRingStr ⦃...⦄
  private instance
    _ = A .fst .snd
    _ = (A / I).fst .snd

  opaque
    isZeroFromIdeal : (x : ⟨ A ⟩ₐ) → x ∈ (fst I) → ⟨ quotientHom A I ⟩ₐ→ x ≡ 0r
    isZeroFromIdeal x x∈I = eq/ x 0r (subst (_∈ fst I) (solve! (CommAlgebra→CommRing A)) x∈I )
-}
