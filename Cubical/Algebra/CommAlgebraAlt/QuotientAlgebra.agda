{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebraAlt.QuotientAlgebra where
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
open import Cubical.Algebra.CommAlgebraAlt.Base
open import Cubical.Algebra.CommAlgebraAlt.Ideal
open import Cubical.Algebra.CommAlgebraAlt.Kernel
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

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn R A) where
  open CommRingStr {{...}}
  open CommAlgebraStr {{...}}
  open RingTheory (CommRing→Ring (fst A)) using (-DistR·)
  instance
    _ : CommRingStr ⟨ R ⟩
    _ = snd R
    _ : CommRingStr ⟨ A .fst ⟩
    _ = A .fst .snd
    _ = A

  _/_ : CommAlgebra R ℓ
  _/_ = ((fst A) CommRing./ I) ,
        (CommRing.quotientHom (fst A) I ∘cr A .snd)

  quotientHom : CommAlgebraHom A (_/_)
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
    inducedHom .fst = CommRing.UniversalProperty.inducedHom
                             (CommAlgebra→CommRing A)
                             (CommAlgebra→CommRing B)
                             I
                             (CommAlgebraHom→CommRingHom ϕ)
                             I⊆kernel
    inducedHom .snd = p
      where
      step1 = cong (inducedHom .fst ∘cr_) (sym (quotientHom A I .snd))
      step2 = compAssocCommRingHom (A .snd) (CommRing.quotientHom (A .fst) I) (inducedHom .fst)
      step3 = cong (_∘cr A .snd) (CommRing.UniversalProperty.isSolution
                         (CommAlgebra→CommRing A) (CommAlgebra→CommRing B) I (CommAlgebraHom→CommRingHom ϕ) I⊆kernel)
      opaque
        p : (inducedHom .fst ∘cr snd (A / I)) ≡ snd B
        p = (inducedHom .fst ∘cr snd (A / I))                                  ≡⟨ step1 ⟩
            (inducedHom .fst ∘cr (CommRing.quotientHom (A .fst) I ∘cr A .snd)) ≡⟨ step2 ⟩
            (inducedHom .fst ∘cr CommRing.quotientHom (A .fst) I) ∘cr A .snd   ≡⟨ step3 ⟩
            (ϕ .fst) ∘cr A .snd                                                ≡⟨ ϕ .snd ⟩
            snd B ∎

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
            (A .fst) (B .fst) I (ϕ .fst) I⊆kernel (ψ .fst) ψIsSolution)



module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn R A) where
  open CommRingStr {{...}}
  open CommAlgebraStr {{...}}

  opaque
--    unfolding quotientHom

    injectivePrecomp : (B : CommAlgebra R ℓ) (f g : CommAlgebraHom (A / I) B)
                       → f ∘ca (quotientHom A I) ≡ g ∘ca (quotientHom A I)
                       → f ≡ g
    injectivePrecomp B f g p =
      CommAlgebraHom≡ ?
--        (descendMapPath ⟨ f ⟩ₐ→ ⟨ g ⟩ₐ→ is-set
--                        λ x → λ i → fst (p i) x)
--      where
{-


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
