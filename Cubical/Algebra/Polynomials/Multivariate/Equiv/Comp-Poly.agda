{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.Equiv.Comp-Poly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Algebra.Polynomials.Univariate.Base

open import Cubical.Algebra.Polynomials.Multivariate.Base
open import Cubical.Algebra.Polynomials.Multivariate.Properties
open import Cubical.Algebra.CommRing.Instances.MultivariatePoly

private variable
  ℓ ℓ' : Level

module Comp-Poly-nm (A' : CommRing ℓ) (n m : ℕ) where
  private
    A = fst A'
  open CommRingStr (snd A')

  module Mr  = Nth-Poly-structure A' m
  module N+Mr = Nth-Poly-structure A' (n +n m)
  module N∘Mr  = Nth-Poly-structure (PolyCommRing A' m) n


-----------------------------------------------------------------------------
-- direct sens

  N∘M→N+M-b : (v : Vec ℕ n) → Poly A' m → Poly A' (n +n m)
  N∘M→N+M-b v = Poly-Rec-Set.f A' m (Poly A' (n +n m)) trunc
                0P
                (λ v' a → base (v ++ v') a)
                _Poly+_
                Poly+-assoc
                Poly+-Rid
                Poly+-comm
                (λ v' → base-0P (v ++ v'))
                (λ v' a b → base-Poly+ (v ++ v') a b)

  N∘M→N+M : Poly (PolyCommRing A' m) n → Poly A' (n +n m)
  N∘M→N+M = Poly-Rec-Set.f (PolyCommRing A' m) n (Poly A' (n +n m)) trunc
           0P
           N∘M→N+M-b
           _Poly+_
           Poly+-assoc
           Poly+-Rid
           Poly+-comm
           (λ _ → refl)
           (λ v a b → refl)


-- -----------------------------------------------------------------------------
-- -- Converse sens

  N+M→N∘M : Poly A' (n +n m) → Poly (PolyCommRing A' m) n
  N+M→N∘M = Poly-Rec-Set.f A' (n +n m) (Poly (PolyCommRing A' m) n) trunc
            0P
            (λ v a → let v , v'  = sep-vec n m v in
                      base v (base v' a))
            _Poly+_
            Poly+-assoc
            Poly+-Rid
            Poly+-comm
            (λ v → (cong (base (fst (sep-vec n m v))) (base-0P (snd (sep-vec n m v)))) ∙ (base-0P (fst (sep-vec n m v))))
            λ v a b → base-Poly+ (fst (sep-vec n m v)) (base (snd (sep-vec n m v)) a) (base (snd (sep-vec n m v)) b)
                       ∙ cong (base (fst (sep-vec n m v))) (base-Poly+ (snd (sep-vec n m v)) a b)


-----------------------------------------------------------------------------
-- Section

  e-sect : (P : Poly A' (n +n m)) → N∘M→N+M (N+M→N∘M P) ≡ P
  e-sect = Poly-Ind-Prop.f A' (n +n m)
           (λ P → N∘M→N+M (N+M→N∘M P) ≡ P)
           (λ _ → trunc _ _)
           refl
           (λ v a → cong (λ X → base X a) (sep-vec-id n m v))
           (λ {U V} ind-U ind-V → cong₂ _Poly+_ ind-U ind-V)


-----------------------------------------------------------------------------
-- Retraction

  e-retr : (P : Poly (PolyCommRing A' m) n) → N+M→N∘M (N∘M→N+M P) ≡ P
  e-retr = Poly-Ind-Prop.f (PolyCommRing A' m) n
           (λ P → N+M→N∘M (N∘M→N+M P) ≡ P)
           (λ _ → trunc _ _)
           refl
           (λ v → Poly-Ind-Prop.f A' m
                   (λ P → N+M→N∘M (N∘M→N+M (base v P)) ≡ base v P)
                   (λ _ → trunc _ _)
                   (sym (base-0P v))
                   (λ v' a → cong₂ base (sep-vec-fst n m v v') (cong (λ X → base X a) (sep-vec-snd n m v v')))
                   (λ {U V} ind-U ind-V → (cong₂ _Poly+_ ind-U ind-V) ∙ (base-Poly+ v U V)))
           (λ {U V} ind-U ind-V → cong₂ _Poly+_ ind-U ind-V )


-----------------------------------------------------------------------------
-- Morphism of ring

  map-0P : N∘M→N+M (0P) ≡ 0P
  map-0P = refl

  N∘M→N+M-gmorph : (P Q : Poly (PolyCommRing A' m) n) → N∘M→N+M ( P Poly+ Q) ≡ N∘M→N+M P Poly+ N∘M→N+M Q
  N∘M→N+M-gmorph = λ P Q → refl

  map-1P : N∘M→N+M (N∘Mr.1P) ≡ N+Mr.1P
  map-1P = cong (λ X → base X 1r) (rep-concat n m 0 )

  N∘M→N+M-rmorph : (P Q : Poly (PolyCommRing A' m) n) → N∘M→N+M ( P N∘Mr.Poly* Q) ≡ N∘M→N+M P N+Mr.Poly* N∘M→N+M Q
  N∘M→N+M-rmorph =
    -- Ind P
    Poly-Ind-Prop.f (PolyCommRing A' m) n
    (λ P → (Q : Poly (PolyCommRing A' m) n) → N∘M→N+M (P N∘Mr.Poly* Q) ≡ (N∘M→N+M P N+Mr.Poly* N∘M→N+M Q))
    (λ P p q i Q j → trunc _ _ (p Q) (q Q) i j)
    (λ Q → refl)
    (λ v → -- Ind Base P
           Poly-Ind-Prop.f A' m
           (λ P → (Q : Poly (PolyCommRing A' m) n) → N∘M→N+M (base v P N∘Mr.Poly* Q) ≡ (N∘M→N+M (base v P) N+Mr.Poly* N∘M→N+M Q))
           (λ P p q i Q j → trunc _ _ (p Q) (q Q) i j)
           (λ Q → cong (λ X → N∘M→N+M (X N∘Mr.Poly* Q)) (base-0P v))
           (λ v' a → -- Ind Q
                      Poly-Ind-Prop.f (PolyCommRing A' m) n
                      (λ Q → N∘M→N+M (base v (base v' a) N∘Mr.Poly* Q) ≡ (N∘M→N+M (base v (base v' a)) N+Mr.Poly* N∘M→N+M Q))
                      (λ _ → trunc _ _)
                      (sym (N+Mr.0PRightAnnihilatesPoly (N∘M→N+M (base v (base v' a)))))
                      (λ w → -- Ind base Q
                              Poly-Ind-Prop.f A' m
                              _
                              (λ _ → trunc _ _)
                              (sym (N+Mr.0PRightAnnihilatesPoly (N∘M→N+M (base v (base v' a)))))
                              (λ w' b → cong (λ X → base X (a · b)) (+n-vec-concat n m v w v' w'))
                              λ {U V} ind-U ind-V → cong (λ X → N∘M→N+M (base v (base v' a) N∘Mr.Poly* X)) (sym (base-Poly+ w U V))
                                                     ∙ cong₂ (_Poly+_ ) ind-U ind-V
                                                     ∙ sym (cong (λ X → N∘M→N+M (base v (base v' a)) N+Mr.Poly* N∘M→N+M X) (base-Poly+ w U V)) )
                              -- End Ind base Q
                      λ {U V} ind-U ind-V → cong₂ _Poly+_ ind-U ind-V)
                      -- End Ind Q
           λ {U V} ind-U ind-V Q → cong (λ X → N∘M→N+M (X N∘Mr.Poly* Q)) (sym (base-Poly+ v U V))
                                    ∙ cong₂ _Poly+_ (ind-U Q) (ind-V Q)
                                    ∙ sym (cong (λ X → (N∘M→N+M X) N+Mr.Poly* (N∘M→N+M Q)) (sym (base-Poly+ v U V)) ))
           -- End Ind base P
     λ {U V} ind-U ind-V Q → cong₂ _Poly+_ (ind-U Q) (ind-V Q)
     -- End Ind P


-----------------------------------------------------------------------------
-- Ring Equivalence

module _ (A' : CommRing ℓ) (n m : ℕ) where

  open Comp-Poly-nm A' n m

  CRE-PolyN∘M-PolyN+M : CommRingEquiv (PolyCommRing (PolyCommRing A' m) n) (PolyCommRing A' (n +n m))
  fst CRE-PolyN∘M-PolyN+M = isoToEquiv is
    where
    is : Iso _ _
    Iso.fun is = N∘M→N+M
    Iso.inv is = N+M→N∘M
    Iso.rightInv is = e-sect
    Iso.leftInv is = e-retr

  snd CRE-PolyN∘M-PolyN+M = makeIsRingHom map-1P N∘M→N+M-gmorph N∘M→N+M-rmorph
