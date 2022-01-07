{-# OPTIONS --safe #-}
module Cubical.Algebra.CommAlgebra.QuotientAlgebra where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset using (_∈_; _⊆_)

open import Cubical.HITs.SetQuotients hiding (_/_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.QuotientRing renaming (_/_ to _/CommRing_) hiding ([_]/)
open import Cubical.Algebra.Ring.QuotientRing renaming (_/_ to _/Ring_)
open import Cubical.Algebra.CommRing.Ideal hiding (IdealsIn)
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.Kernel
open import Cubical.Algebra.Algebra.Base using (IsAlgebraHom)
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Ideal using (isIdeal)

private
  variable
    ℓ : Level

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn A) where
  open CommRingStr {{...}} hiding (_-_; -_; dist; ·Lid; ·Rdist+) renaming (_·_ to _·R_; _+_ to _+R_)
  open CommAlgebraStr {{...}}
  open RingTheory (CommRing→Ring (CommAlgebra→CommRing A)) using (-DistR·)
  instance
    _ : CommRingStr _
    _ = snd R
    _ : CommAlgebraStr _ _
    _ = snd A

  _/_ :  CommAlgebra R ℓ
  _/_ = commAlgebraFromCommRing
           ((CommAlgebra→CommRing A) /CommRing I)
           (λ r → elim (λ _ → squash/) (λ x → [ r ⋆ x ]) (eq r))
           (λ r s → elimProp (λ _ → squash/ _ _)
                             λ x i → [ ((r ·R s) ⋆ x ≡⟨ ⋆-assoc r s x ⟩
                                         r ⋆ (s ⋆ x) ∎) i ])
           (λ r s → elimProp (λ _ → squash/ _ _)
                             λ x i → [ ((r +R s) ⋆ x ≡⟨ ⋆-ldist r s x ⟩
                                       r ⋆ x + s ⋆ x ∎) i ])
           (λ r → elimProp2 (λ _ _ → squash/ _ _)
                            λ x y i → [ (r ⋆ (x + y)  ≡⟨ ⋆-rdist r x y ⟩
                                        r ⋆ x + r ⋆ y ∎) i ])
           (elimProp (λ _ → squash/ _ _)
                     (λ x i →  [ (1r ⋆ x ≡⟨ ⋆-lid x ⟩ x ∎) i ]))
           λ r → elimProp2 (λ _ _ → squash/ _ _)
                           λ x y i → [ ((r ⋆ x) · y ≡⟨ ⋆-lassoc r x y ⟩
                                       r ⋆ (x · y) ∎) i ]

          where
                open CommIdeal using (isCommIdeal)
                eq : (r : fst R) (x y : fst A) → x - y ∈ (fst I) →  [ r ⋆ x ] ≡ [ r ⋆ y ]
                eq r x y x-y∈I = eq/ _ _
                  (subst (λ u → u ∈ fst I)
                  ((r ⋆ 1a) · (x - y)               ≡⟨ ·Rdist+ (r ⋆ 1a) x (- y)  ⟩
                    (r ⋆ 1a) · x + (r ⋆ 1a) · (- y) ≡[ i ]⟨ (r ⋆ 1a) · x + -DistR· (r ⋆ 1a) y i ⟩
                    (r ⋆ 1a) · x - (r ⋆ 1a) · y     ≡[ i ]⟨ ⋆-lassoc r 1a x i
                                                            - ⋆-lassoc r 1a y i ⟩
                    r ⋆ (1a · x) - r ⋆ (1a · y)     ≡[ i ]⟨ r ⋆ (·Lid x i) - r ⋆ (·Lid y i) ⟩
                    r ⋆ x - r ⋆ y ∎ )
                  (isCommIdeal.·Closed (snd I) _ x-y∈I))

module _ {R : CommRing ℓ} (A : CommAlgebra R ℓ) (I : IdealsIn A) where
  open CommRingStr {{...}} hiding (_-_; -_; dist; ·Lid; ·Rdist+) renaming (_·_ to _·R_; _+_ to _+R_)
  open CommAlgebraStr ⦃...⦄

  instance
    _ : CommRingStr _
    _ = snd R
    _ : CommAlgebraStr _ _
    _ = snd A

  private
    LRing = CommAlgebra→Ring (A / I)
    RRing = (CommAlgebra→Ring A) /Ring (CommIdeal→Ideal I)

  -- sanity check / maybe a helper function some day
  CommForget/ : RingEquiv (CommAlgebra→Ring (A / I)) ((CommAlgebra→Ring A) /Ring (CommIdeal→Ideal I))
  fst CommForget/ =
    isoToEquiv
      (iso
        (rec (isSetRing LRing) (λ a → [ a ]) λ a b a-b∈I → eq/ a b a-b∈I)
        (rec (isSetRing RRing) (λ a → [ a ]) (λ a b a-b∈I → eq/ a b a-b∈I))
        (elimProp (λ _ → isSetRing LRing _ _) λ _ → refl)
        (elimProp (λ _ → isSetRing RRing _ _) (λ _ → refl)))
  IsRingHom.pres0 (snd CommForget/) = refl
  IsRingHom.pres1 (snd CommForget/) = refl
  IsRingHom.pres+ (snd CommForget/) = elimProp2 (λ _ _ → isSetRing RRing _ _) (λ _ _ → refl)
  IsRingHom.pres· (snd CommForget/) = elimProp2 (λ _ _ → isSetRing RRing _ _) (λ _ _ → refl)
  IsRingHom.pres- (snd CommForget/) = elimProp (λ _ → isSetRing RRing _ _) (λ _ → refl)

  open IsAlgebraHom
  inducedHom : (B : CommAlgebra R ℓ) (ϕ : CommAlgebraHom A B)
               → (fst I) ⊆ (fst (kernel {A = A} {B = B} ϕ))
               → CommAlgebraHom (A / I) B
  fst (inducedHom B ϕ I⊆kernel) =
    let open RingTheory (CommRing→Ring (CommAlgebra→CommRing B))
        instance
          _ : CommAlgebraStr R _
          _ = snd B
          _ : CommRingStr _
          _ = snd (CommAlgebra→CommRing B)
    in rec (isSetCommAlgebra B) (λ x → fst ϕ x)
        λ a b a-b∈I →
          equalByDifference
            (fst ϕ a) (fst ϕ b)
            ((fst ϕ a) - (fst ϕ b)     ≡⟨ cong (λ u → (fst ϕ a) + u) (sym (IsAlgebraHom.pres- (snd ϕ) _)) ⟩
             (fst ϕ a) + (fst ϕ (- b)) ≡⟨ sym (IsAlgebraHom.pres+ (snd ϕ) _ _) ⟩
             fst ϕ (a - b)             ≡⟨ I⊆kernel (a - b) a-b∈I ⟩
             0r ∎)
  pres0 (snd (inducedHom B ϕ kernel⊆I)) = pres0 (snd ϕ)
  pres1 (snd (inducedHom B ϕ kernel⊆I)) = pres1 (snd ϕ)
  pres+ (snd (inducedHom B ϕ kernel⊆I)) = elimProp2 (λ _ _ → isSetCommAlgebra B _ _) (pres+ (snd ϕ))
  pres· (snd (inducedHom B ϕ kernel⊆I)) = elimProp2 (λ _ _ → isSetCommAlgebra B _ _) (pres· (snd ϕ))
  pres- (snd (inducedHom B ϕ kernel⊆I)) = elimProp (λ _ → isSetCommAlgebra B _ _) (pres- (snd ϕ))
  pres⋆ (snd (inducedHom B ϕ kernel⊆I)) = λ r → elimProp (λ _ → isSetCommAlgebra B _ _) (pres⋆ (snd ϕ) r)

[_]/ : {R : CommRing ℓ} {A : CommAlgebra R ℓ} {I : IdealsIn A}
       → (a : fst A) → fst (A / I)
[ a ]/ = [ a ]
