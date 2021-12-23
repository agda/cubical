{-# OPTIONS --safe #-}
module Cubical.Homotopy.Group.Pi4S3.OmegaS3Pushout where

open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Group.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Morphism

open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; rec2 to sRec2
          ; elim to sElim ; elim2 to sElim2 ; elim3 to sElim3
          ; map to sMap)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.S1 hiding (decode ; encode)

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool

open import Cubical.Algebra.Group
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid

open Iso
open IsGroup
open IsSemigroup
open IsMonoid
open GroupStr


open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge
open import Cubical.Homotopy.Freudenthal hiding (Code ; encode)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.WedgeConnectivity
open import Cubical.HITs.Truncation renaming
  (rec to trRec ; elim to trElim ; elim2 to trElim2 ; map to trMap)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec)

open import Cubical.HITs.S2
open import Cubical.HITs.S3

-- move to HITs.S²
S²∙ : Pointed ℓ-zero
S²∙ = S² , base

ΩS³ = typ ((Ω^ 3) (S³ , base))

-- Give own def?
Pushout⋁↪fold⋁ : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
Pushout⋁↪fold⋁ A = Pushout {A = A ⋁ A} ⋁↪ fold⋁

Pushout⋁↪fold⋁∙ : ∀ {ℓ} (A : Pointed ℓ) → Pointed ℓ
fst (Pushout⋁↪fold⋁∙ A) = Pushout⋁↪fold⋁ A
snd (Pushout⋁↪fold⋁∙ A) = inl (pt A , pt A)

≡→Pushout⋁↪fold⋁≡ : ∀ {ℓ} {A B : Pointed ℓ}
  → (A ≡ B) → Pushout⋁↪fold⋁∙ A ≡ Pushout⋁↪fold⋁∙ B
≡→Pushout⋁↪fold⋁≡ = cong Pushout⋁↪fold⋁∙

-- The type of interest -- ''almost`` equivalent to ΩS³
ΩS³≈ = Pushout {A = S₊∙ 2 ⋁ S₊∙ 2} ⋁↪ fold⋁
-- Same type, using base/surf definition of S² (easier to work with)
Pushout⋁↪fold⋁S² = Pushout⋁↪fold⋁ S²∙
-- Truncated version, to be proved equivalent to ∥ ΩS³ ∥₅
∥Pushout⋁↪fold⋁S²∥₅ = hLevelTrunc 5 Pushout⋁↪fold⋁S²

Ω∥S³∥₆ = Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ ∣ north ∣

-- Elimination into sets for Pushout⋁↪fold⋁S²
module _ {ℓ : Level} {P : Pushout⋁↪fold⋁S² → Type ℓ}
         (hlev : ((x : Pushout⋁↪fold⋁S²) → isSet (P x)))
         (b : P (inl (base , base))) where
  private
    ×fun : (x y : S²) → P (inl (x , y))
    ×fun = S²ToSetRec (λ _ → isSetΠ (λ _ → hlev _))
            (S²ToSetRec (λ _ → hlev _) b)

    inrfun : (x : S²) → P (inr x)
    inrfun = S²ToSetRec (λ _ → hlev _) (subst P (push (inl base)) b)

    inl-pp : (x : S²) → PathP (λ i → P (push (inl x) i)) (×fun x base) (inrfun x)
    inl-pp = S²ToSetRec (λ _ → isOfHLevelPathP 2 (hlev _) _ _)
              λ j → transp (λ i → P (push (inl base) (i ∧ j))) (~ j) b

    inr-pp : (x : S²) → PathP (λ i → P (push (inr x) i)) (×fun base x) (inrfun x)
    inr-pp = S²ToSetRec (λ _ → isOfHLevelPathP 2 (hlev _) _ _)
              (transport (λ j → PathP (λ i → P (push (push tt j) i)) (×fun base base)
                                       (inrfun base))
              (inl-pp base))

  ΩS³≈→Set : (x : Pushout⋁↪fold⋁S²) → P x
  ΩS³≈→Set (inl x) = ×fun (fst x) (snd x)
  ΩS³≈→Set (inr x) = inrfun x
  ΩS³≈→Set (push (inl x) i) = inl-pp x i
  ΩS³≈→Set (push (inr x) i) = inr-pp x i
  ΩS³≈→Set (push (push a j) i) = help j i
    where
    help : SquareP (λ j i → P (push (push tt j) i))
                   (λ i → inl-pp base i)
                   (λ i → inr-pp base i)
                   (λ _ → ×fun base base)
                   (λ _ → inrfun base)
    help = toPathP (isProp→PathP (λ _ → isOfHLevelPathP' 1 (hlev _) _ _) _ _)

{- A wedge connectivity lemma for Pushout⋁↪fold⋁S². It can be
stated for general dependent types, but it's easier to work with
in the special case of path types -}
module Pushout⋁↪fold⋁S²WedgeCon {ℓ : Level } {A : Type ℓ}
  (f g : Pushout⋁↪fold⋁S² → A)
  (h : isOfHLevel 5 A)
  (lp : (x : S²) → f (inl (x , base)) ≡ g (inl (x , base)))
  (rp : (x : S²) → f (inl (base , x)) ≡ g (inl (base , x)))
  (r≡l : (x : S²)
       → (sym (cong f (push (inl x))) ∙∙ lp x ∙∙ cong g (push (inl x)))
        ≡ (sym (cong f (push (inr x))) ∙∙ rp x ∙∙ cong g (push (inr x))))
  where

  z-er : I → I → I → A
  z-er k i j =
    hfill (λ k → λ {(i = i0)
                   → doubleCompPath-filler (sym (cong f (push (inl base))))
                                            (lp base)
                                            (cong g (push (inl base))) (~ k) j
                   ; (i = i1)
                   → doubleCompPath-filler (sym (cong f (push (inr base))))
                                            (rp base)
                                            (cong g (push (inr base))) (~ k) j
                   ; (j = i0) → f (push (push tt i) (~ k))
                   ; (j = i1) → g (push (push tt i) (~ k))})
      (inS (r≡l base i j))
      k

  lp-base≡rp-base : lp base ≡ rp base
  lp-base≡rp-base = (λ i j → z-er i1 i j)

  f∘inl≡g∘inl : (x y : S²) → f (inl (x , y)) ≡ g (inl (x , y))
  f∘inl≡g∘inl = wedgeconFunS² (λ _ _ → h _ _) lp rp lp-base≡rp-base

  f∘inl≡g∘inl-base : (x : S²) → f∘inl≡g∘inl x base ≡ lp x
  f∘inl≡g∘inl-base = wedgeconFunS²Id (λ _ _ → h _ _) lp rp lp-base≡rp-base

  f∘inr≡g∘inr : (x : S²) → f (inr x) ≡ g (inr x)
  f∘inr≡g∘inr x = cong f (sym (push (inl x))) ∙∙ lp x ∙∙ cong g (push (inl x))

  inlfill : (x : S²) → I → I → I → A
  inlfill x k i j =
    hfill (λ k → λ { (i = i0) → f∘inl≡g∘inl-base x (~ k) j
                    ; (i = i1) → doubleCompPath-filler
                                   (cong f (sym (push (inl x))))
                                   (lp x)
                                   (cong g (push (inl x))) k j
                    ; (j = i0) → f (push (inl x) (i ∧ k))
                    ; (j = i1) → g (push (inl x) (i ∧ k))})
          (inS (lp x j))
          k

  inrfill : (x : S²) → I → I → I → A
  inrfill x k i j =
    hfill (λ k → λ { (i = i0) → doubleCompPath-filler
                                   (cong f (sym (push (inr x))))
                                   (rp x)
                                   (cong g (push (inr x))) (~ k) j
                    ; (i = i1) → f∘inr≡g∘inr x j
                    ; (j = i0) → f (push (inr x) (i ∨ ~ k))
                    ; (j = i1) → g (push (inr x) (i ∨ ~ k))})
                      (inS (r≡l x (~ i) j))
                      k

  main : (x : Pushout⋁↪fold⋁S²) → f x ≡ g x
  main (inl x) = f∘inl≡g∘inl (fst x) (snd x)
  main (inr x) = f∘inr≡g∘inr x
  main (push (inl x) i) j = inlfill x i1 i j
  main (push (inr x) i) j = inrfill x i1 i j
  main (push (push a i) j) k =
    hcomp (λ r → λ {(i = i0) → inlfill base i1 j k
                   ; (i = i1) → inrfill-side r j k
                   ; (j = i0) → rp base k
                   ; (j = i1) → r≡l base (~ r ∧ i) k
                   ; (k = i0) → f (push (push a i) j)
                   ; (k = i1) → g (push (push a i) j)})
      (hcomp (λ r → λ {(i = i0) → inlfill base r j k
                   ; (i = i1) → doubleCompPath-filler
                                  (cong f (sym (push (inr base))))
                                  (rp base)
                                  (cong g (push (inr base))) (j ∧ r) k
                   ; (j = i0) → lp-base≡rp-base (r ∨ i) k
                   ; (j = i1) → inlfill-side r i k
                   ; (k = i0) → f (push (push a i) (j ∧ r))
                   ; (k = i1) → g (push (push a i) (j ∧ r))})
              (lp-base≡rp-base i k))
    where
    inlfill-side : I → I → I → A
    inlfill-side r i k =
      hcomp (λ j → λ { (r = i0) → z-er j i k
                      ; (r = i1) → r≡l base i k
                      ; (i = i0) → doubleCompPath-filler
                                  (cong f (sym (push (inl base))))
                                  (lp base)
                                  (cong g (push (inl base))) (r ∨ ~ j) k
                      ; (i = i1) → doubleCompPath-filler
                                  (cong f (sym (push (inr base))))
                                  (rp base)
                                  (cong g (push (inr base))) (r ∨ ~ j) k
                      ; (k = i0) → f (push (push a i) (r ∨ ~ j))
                      ; (k = i1) → g (push (push a i) (r ∨ ~ j))})
            (r≡l base i k)
  
    inrfill-side : I → I → I → A
    inrfill-side r j k =
      hcomp (λ i → λ { (r = i0)
                       → (doubleCompPath-filler
                           (cong f (sym (push (inr base))))
                           (rp base)
                           (cong g (push (inr base)))) (j ∨ ~ i)  k
                      ; (r = i1) → inrfill base i j k
                      ; (j = i0) → inrfill base i i0 k
                      ; (j = i1) → r≡l base (~ r) k
                      ; (k = i0) → f (push (inr base) (j ∨ ~ i))
                      ; (k = i1) → g (push (inr base) (j ∨ ~ i))})
            (r≡l base (~ r ∨ ~ j) k)

{-
Goal: Prove Ω ∥ SuspS² ∥₆ ≃ ∥ Pushout⋁↪fold⋁S² ∥₅
This will by done via the encode-decode method. For this, we nede a family
of equivalences ∥ Pushout⋁↪fold⋁S² ∥₅ ≃ ∥ Pushout⋁↪fold⋁S² ∥₅, indexed by S².
In order to define this, we need the following cubes/coherences in
∥ Pushout⋁↪fold⋁S² ∥₅:
-}

→Ω²∥Pushout⋁↪fold⋁S²∥₅ : (x y : S²)
  → Square {A = ∥Pushout⋁↪fold⋁S²∥₅} (λ _ → ∣ inl (x , y) ∣ₕ)
                            (λ _ → ∣ inl (x , y) ∣ₕ)
                            (λ _ → ∣ inl (x , y) ∣ₕ)
                            (λ _ → ∣ inl (x , y) ∣ₕ)
→Ω²∥Pushout⋁↪fold⋁S²∥₅ =
  wedgeconFunS²
    (λ _ _ → isOfHLevelPath 4 (isOfHLevelTrunc 5 _ _) _ _)
    (λ x → λ i j → ∣ inl (x , surf i j) ∣ₕ)
    (λ x → λ i j → ∣ inl (surf i j , x) ∣ₕ)
    λ r i j → ∣ hcomp (λ k → λ { (i = i0) → push (push tt (~ r)) (~ k)
                               ; (i = i1) → push (push tt (~ r)) (~ k)
                               ; (j = i1) → push (push tt (~ r)) (~ k)
                               ; (j = i0) → push (push tt (~ r)) (~ k)
                               ; (r = i0) → push (inr (surf i j)) (~ k)
                               ; (r = i1) → push (inl (surf i j)) (~ k)})
                     (inr (surf i j)) ∣ₕ

→Ω²∥Pushout⋁↪fold⋁S²∥₅Id : (x : S²)
  → →Ω²∥Pushout⋁↪fold⋁S²∥₅ x base ≡  λ i j → ∣ inl (x , surf i j) ∣ₕ
→Ω²∥Pushout⋁↪fold⋁S²∥₅Id =
  wedgeconFunS²Id
    (λ _ _ → isOfHLevelPath 4 (isOfHLevelTrunc 5 _ _) _ _)
    (λ x → λ i j → ∣ inl (x , surf i j) ∣ₕ)
    (λ x → λ i j → ∣ inl (surf i j , x) ∣ₕ)
    λ r i j → ∣ hcomp (λ k → λ { (i = i0) → push (push tt (~ r)) (~ k)
                               ; (i = i1) → push (push tt (~ r)) (~ k)
                               ; (j = i1) → push (push tt (~ r)) (~ k)
                               ; (j = i0) → push (push tt (~ r)) (~ k)
                               ; (r = i0) → push (inr (surf i j)) (~ k)
                               ; (r = i1) → push (inl (surf i j)) (~ k)})
                     (inr (surf i j)) ∣ₕ

push-inl∙push-inr⁻ : (y : S²) → Path Pushout⋁↪fold⋁S² (inl (y , base)) (inl (base , y))
push-inl∙push-inr⁻ y i = (push (inl y) ∙ sym (push (inr y))) i

push-inl∙push-inr⁻∙ : push-inl∙push-inr⁻ base ≡ refl
push-inl∙push-inr⁻∙ = (λ k i → (push (inl base) ∙ sym (push (push tt (~ k)))) i)
          ∙ rCancel (push (inl base))
