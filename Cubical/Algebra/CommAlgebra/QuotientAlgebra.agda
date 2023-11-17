{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.QuotientAlgebra where
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
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.Kernel
open import Cubical.Algebra.CommAlgebra.Instances.Unit
open import Cubical.Algebra.Algebra.Base using (IsAlgebraHom; isPropIsAlgebraHom)
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Ideal using (isIdeal)
open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Algebra.Algebra.Properties
open AlgebraHoms using (_∘a_)

private
  variable
    ℓ : Level

{-
  The definition of the quotient algebra (_/_ below) is marked opaque to avoid
  long type checking times. All other definitions that need to "look into" this
  opaque definition must be in an opaque block that unfolds the definition of _/_.
-}

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn A) where
  open CommRingStr {{...}} hiding (_-_; -_; ·IdL ; ·DistR+) renaming (_·_ to _·R_; _+_ to _+R_)
  open CommAlgebraStr {{...}}
  open RingTheory (CommRing→Ring (CommAlgebra→CommRing A)) using (-DistR·)
  instance
    _ : CommRingStr ⟨ R ⟩
    _ = snd R
    _ : CommAlgebraStr R ⟨ A ⟩
    _ = snd A

  opaque
    _/_ : CommAlgebra R ℓ
    _/_ = commAlgebraFromCommRing
           A/IAsCommRing
           (λ r → elim (λ _ → squash/) (λ x → [ r ⋆ x ]) (eq r))
           (λ r s → elimProp (λ _ → squash/ _ _)
                             λ x i → [ ((r ·R s) ⋆ x ≡⟨ ⋆Assoc r s x ⟩
                                         r ⋆ (s ⋆ x) ∎) i ])
           (λ r → elimProp2 (λ _ _ → squash/ _ _)
                            λ x y i → [ (r ⋆ (x + y)  ≡⟨ ⋆DistR+ r x y ⟩
                                        r ⋆ x + r ⋆ y ∎) i ])
           (λ r s → elimProp (λ _ → squash/ _ _)
                             λ x i → [ ((r +R s) ⋆ x ≡⟨ ⋆DistL+ r s x ⟩
                                       r ⋆ x + s ⋆ x ∎) i ])
           (elimProp (λ _ → squash/ _ _)
                     (λ x i →  [ (1r ⋆ x ≡⟨ ⋆IdL x ⟩ x ∎) i ]))
           λ r → elimProp2 (λ _ _ → squash/ _ _)
                           λ x y i → [ ((r ⋆ x) · y ≡⟨ ⋆AssocL r x y ⟩
                                       r ⋆ (x · y) ∎) i ]

          where
                A/IAsCommRing : CommRing ℓ
                A/IAsCommRing = (CommAlgebra→CommRing A) CommRing./ I
                [_]/ : ⟨ A ⟩ → ⟨ A/IAsCommRing ⟩
                [_]/ = CommRing.[_]/ {R = CommAlgebra→CommRing A} {I = I}
                open CommIdeal using (isCommIdeal)
                eq : (r : fst R) (x y : fst A) → x - y ∈ (fst I) → [ r ⋆ x ]/ ≡ [ r ⋆ y ]/
                eq r x y x-y∈I = eq/ _ _
                  (subst (λ u → u ∈ fst I)
                  ((r ⋆ 1a) · (x - y)               ≡⟨ ·DistR+ (r ⋆ 1a) x (- y) ⟩
                    (r ⋆ 1a) · x + (r ⋆ 1a) · (- y) ≡[ i ]⟨ (r ⋆ 1a) · x + -DistR· (r ⋆ 1a) y i ⟩
                    (r ⋆ 1a) · x - (r ⋆ 1a) · y     ≡[ i ]⟨ ⋆AssocL r 1a x i
                                                            - ⋆AssocL r 1a y i ⟩
                    r ⋆ (1a · x) - r ⋆ (1a · y)     ≡[ i ]⟨ r ⋆ (·IdL x i) - r ⋆ (·IdL y i) ⟩
                    r ⋆ x - r ⋆ y                   ∎ )
                  (isCommIdeal.·Closed (snd I) _ x-y∈I))

  opaque
    unfolding _/_

    quotientHom : CommAlgebraHom A (_/_)
    fst quotientHom x = [ x ]
    IsAlgebraHom.pres0 (snd quotientHom) = refl
    IsAlgebraHom.pres1 (snd quotientHom) = refl
    IsAlgebraHom.pres+ (snd quotientHom) _ _ = refl
    IsAlgebraHom.pres· (snd quotientHom) _ _ = refl
    IsAlgebraHom.pres- (snd quotientHom) _ = refl
    IsAlgebraHom.pres⋆ (snd quotientHom) _ _ = refl

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn A) where
  open CommRingStr {{...}}
    hiding (_-_; -_; ·IdL; ·DistR+; is-set)
    renaming (_·_ to _·R_; _+_ to _+R_)
  open CommAlgebraStr ⦃...⦄

  instance
    _ : CommRingStr ⟨ R ⟩
    _ = snd R
    _ : CommAlgebraStr R ⟨ A ⟩
    _ = snd A

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
    isZeroFromIdeal x x∈I = eq/ x 0a (subst (_∈ fst I) (step x) x∈I )
      where
        open CommAlgebraStr (snd A)
        step : (x : ⟨ A ⟩) → x ≡ x - 0a
        step = solve (CommAlgebra→CommRing A)
