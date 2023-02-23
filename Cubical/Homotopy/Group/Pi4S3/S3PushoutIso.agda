{-# OPTIONS --safe #-}
{-
This file has been split in two due to slow type checking
combined with insufficient reductions when the
lossy-unification flag is included.
Part 2: Cubical.Homotopy.Group.Pi4S3.S3PushoutIso2

The goal of these two files is to show that
π₄(S³) ≅ π₃((S² × S²) ⊔ᴬ S²) where A = S² ∨ S².
This is proved in Brunerie (2016) using the James construction and
via (S² × S²) ⊔ᴬ S² ≃ J₂(S²).

In this file, we prove it directly using the encode-decode method. For
the statement of the isomorphism, see part 2.
-}
module Cubical.Homotopy.Group.Pi4S3.S3PushoutIso where

open import Cubical.Homotopy.Loopspace

open import Cubical.Homotopy.Group.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open Iso
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


open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge
open import Cubical.Homotopy.Freudenthal hiding (Code ; encode)
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation renaming
  (rec to trRec ; elim to trElim ; elim2 to trElim2 ; map to trMap)
open import Cubical.Foundations.Function
open import Cubical.HITs.S2

Pushout⋁↪fold⋁ : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
Pushout⋁↪fold⋁ A = Pushout {A = A ⋁ A} ⋁↪ fold⋁

Pushout⋁↪fold⋁∙ : ∀ {ℓ} (A : Pointed ℓ) → Pointed ℓ
fst (Pushout⋁↪fold⋁∙ A) = Pushout⋁↪fold⋁ A
snd (Pushout⋁↪fold⋁∙ A) = inl (pt A , pt A)

-- The type of interest -- ''almost`` equivalent to ΩS³
Pushout⋁↪fold⋁S₊2 = Pushout {A = S₊∙ 2 ⋁ S₊∙ 2} ⋁↪ fold⋁
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
    ×fun = S²ToSetElim (λ _ → isSetΠ (λ _ → hlev _))
            (S²ToSetElim (λ _ → hlev _) b)

    inrfun : (x : S²) → P (inr x)
    inrfun = S²ToSetElim (λ _ → hlev _) (subst P (push (inl base)) b)

    inl-pp : (x : S²) → PathP (λ i → P (push (inl x) i)) (×fun x base) (inrfun x)
    inl-pp = S²ToSetElim (λ _ → isOfHLevelPathP 2 (hlev _) _ _)
              λ j → transp (λ i → P (push (inl base) (i ∧ j))) (~ j) b

    inr-pp : (x : S²) → PathP (λ i → P (push (inr x) i)) (×fun base x) (inrfun x)
    inr-pp = S²ToSetElim (λ _ → isOfHLevelPathP 2 (hlev _) _ _)
              (transport (λ j → PathP (λ i → P (push (push tt j) i)) (×fun base base)
                                       (inrfun base))
              (inl-pp base))

  Pushout⋁↪fold⋁S²→Set : (x : Pushout⋁↪fold⋁S²) → P x
  Pushout⋁↪fold⋁S²→Set (inl x) = ×fun (fst x) (snd x)
  Pushout⋁↪fold⋁S²→Set (inr x) = inrfun x
  Pushout⋁↪fold⋁S²→Set (push (inl x) i) = inl-pp x i
  Pushout⋁↪fold⋁S²→Set (push (inr x) i) = inr-pp x i
  Pushout⋁↪fold⋁S²→Set (push (push a j) i) = help j i
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
  btm-filler : I → I → I → A
  btm-filler k i j =
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
  lp-base≡rp-base = (λ i j → btm-filler i1 i j)

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
      hcomp (λ j → λ { (r = i0) → btm-filler j i k
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
push-inl∙push-inr⁻∙ =
    (λ k i → (push (inl base) ∙ sym (push (push tt (~ k)))) i)
  ∙ rCancel (push (inl base))

push-inl∙push-inr⁻-filler : I → I → I → I → Pushout⋁↪fold⋁S²
push-inl∙push-inr⁻-filler r i j k =
  hfill (λ r → λ { (i = i0) → push-inl∙push-inr⁻∙ (~ r) k
                  ; (i = i1) → push-inl∙push-inr⁻∙ (~ r) k
                  ; (j = i0) → push-inl∙push-inr⁻∙ (~ r) k
                  ; (j = i1) → push-inl∙push-inr⁻∙ (~ r) k
                  ; (k = i0) → inl (surf i j , base)
                  ; (k = i1) → inl (surf i j , base)})
        (inS (inl (surf i j , base)))
        r

push-inl∙push-inr⁻-hLevFiller : (y : S²)
        → Cube {A = ∥Pushout⋁↪fold⋁S²∥₅}
                (λ j k → ∣ push-inl∙push-inr⁻ y k ∣)
                (λ j k → ∣ push-inl∙push-inr⁻ y k ∣)
                (λ j k → ∣ push-inl∙push-inr⁻ y k ∣)
                (λ j k → ∣ push-inl∙push-inr⁻ y k ∣)
                (→Ω²∥Pushout⋁↪fold⋁S²∥₅ y (pt (S² , base)))
                λ i j → ∣ inl (surf i j , y) ∣
push-inl∙push-inr⁻-hLevFiller =
  S²ToSetElim (λ _ → isOfHLevelPathP' 2
              (isOfHLevelPathP' 3
                (isOfHLevelPathP' 4 (isOfHLevelTrunc 5) _ _) _ _) _ _)
   λ i j k → ∣ push-inl∙push-inr⁻-filler i1 i j k ∣ₕ


{-
We combine the above definitions. The equivalence
∥Pushout⋁↪fold⋁S²∥₅ ≃ ∥Pushout⋁↪fold⋁S²∥₅ (w.r.t. S²) is induced
by the following function
-}
S²→Pushout⋁↪fold⋁S²↺' : (x : S²) → Pushout⋁↪fold⋁S² → ∥Pushout⋁↪fold⋁S²∥₅
S²→Pushout⋁↪fold⋁S²↺' base (inl (x , y)) = ∣ inl (x , y) ∣
S²→Pushout⋁↪fold⋁S²↺' (surf i j) (inl (x , y)) = →Ω²∥Pushout⋁↪fold⋁S²∥₅ x y i j
S²→Pushout⋁↪fold⋁S²↺' base (inr z) = ∣ inl (base , z) ∣ₕ
S²→Pushout⋁↪fold⋁S²↺' (surf i i₁) (inr z) = ∣ inl (surf i i₁ , z) ∣ₕ
S²→Pushout⋁↪fold⋁S²↺' base (push (inl y) k) =
  ∣ (push (inl y) ∙ sym (push (inr y))) k ∣
S²→Pushout⋁↪fold⋁S²↺' (surf i j) (push (inl y) k) =
  push-inl∙push-inr⁻-hLevFiller y i j k
S²→Pushout⋁↪fold⋁S²↺' base (push (inr y) i) = ∣ inl (base , y) ∣
S²→Pushout⋁↪fold⋁S²↺' (surf i j) (push (inr y) k) = ∣ inl (surf i j , y) ∣
S²→Pushout⋁↪fold⋁S²↺' base (push (push a i₁) i) = ∣ push-inl∙push-inr⁻∙ i₁ i ∣
S²→Pushout⋁↪fold⋁S²↺' (surf i j) (push (push a k) l) =
  ∣ hcomp (λ r → λ { (i = i0) → push-inl∙push-inr⁻∙ (k ∨ ~ r) l
                   ; (i = i1) → push-inl∙push-inr⁻∙ (k ∨ ~ r) l
                   ; (j = i0) → push-inl∙push-inr⁻∙ (k ∨ ~ r) l
                   ; (j = i1) → push-inl∙push-inr⁻∙ (k ∨ ~ r) l
                   ; (k = i0) → push-inl∙push-inr⁻-filler r i j l
                   ; (k = i1) → inl (surf i j , base)
                   ; (l = i0) → inl (surf i j , base)
                   ; (l = i1) → inl (surf i j , base)})
         (inl (surf i j , base)) ∣ₕ

{- For easier treatment later, we state its inverse explicitly -}
S²→Pushout⋁↪fold⋁S²↺'⁻ : (x : S²) → Pushout⋁↪fold⋁S² → ∥Pushout⋁↪fold⋁S²∥₅
S²→Pushout⋁↪fold⋁S²↺'⁻ base y = S²→Pushout⋁↪fold⋁S²↺' base y
S²→Pushout⋁↪fold⋁S²↺'⁻ (surf i j) y = S²→Pushout⋁↪fold⋁S²↺' (surf (~ i) j) y


S²→Pushout⋁↪fold⋁S²↺'≡idfun : (x : _) → S²→Pushout⋁↪fold⋁S²↺' base x ≡ ∣ x ∣
S²→Pushout⋁↪fold⋁S²↺'≡idfun (inl x) = refl
S²→Pushout⋁↪fold⋁S²↺'≡idfun (inr x) = cong ∣_∣ₕ (push (inr x))
S²→Pushout⋁↪fold⋁S²↺'≡idfun (push (inl x) i) j =
  ∣ compPath-filler (push (inl x)) (λ i₁ → push (inr x) (~ i₁)) (~ j) i  ∣ₕ
S²→Pushout⋁↪fold⋁S²↺'≡idfun (push (inr x) i) j = ∣ push (inr x) (j ∧ i) ∣
S²→Pushout⋁↪fold⋁S²↺'≡idfun (push (push a i) j) k =
  ∣ coh-lem {A = Pushout⋁↪fold⋁S²}
    (push (inl base)) (push (inr base)) (λ k → push (push tt k)) i j k ∣ₕ
  where
  coh-lem : ∀ {ℓ} {A : Type ℓ} {x y : A} (p q : x ≡ y) (r : p ≡ q)
       → Cube {A = A}
               (λ j k → compPath-filler p (sym q) (~ k) j) (λ k j → q (k ∧ j))
               (λ i k → x) (λ i k → q k)
               (((λ k → p ∙ sym (r (~ k))) ∙ rCancel p))
               r
  coh-lem {A = A} {x = x} {y = y} =
    J (λ y p → (q : x ≡ y) (r : p ≡ q)
             → Cube {A = A}
                     (λ j k → compPath-filler p (sym q) (~ k) j) (λ k j → q (k ∧ j))
                     (λ i k → x) (λ i k → q k)
                     (((λ k → p ∙ sym (r (~ k))) ∙ rCancel p))
                     r)
      λ q → J (λ q r → Cube (λ j k → compPath-filler refl (λ i → q (~ i)) (~ k) j)
                              (λ k j → q (k ∧ j)) (λ i k → x) (λ i k → q k)
                              ((λ k → refl ∙ (λ i → r (~ k) (~ i))) ∙ rCancel refl) r)
               ((λ z j k → lUnit (sym (rUnit (λ _ → x))) z k j)
               ◁ (λ i j k → (refl ∙ (λ i₁ → rUnit (λ _ → x) (~ i₁))) (k ∨ i) j))

S²→Pushout⋁↪fold⋁S²↺ : (x : S²) → ∥Pushout⋁↪fold⋁S²∥₅ → ∥Pushout⋁↪fold⋁S²∥₅
S²→Pushout⋁↪fold⋁S²↺ x = trRec (isOfHLevelTrunc 5) (S²→Pushout⋁↪fold⋁S²↺' x)

isEq-S²→Pushout⋁↪fold⋁S²↺' : (x : _) → isEquiv (S²→Pushout⋁↪fold⋁S²↺ x)
isEq-S²→Pushout⋁↪fold⋁S²↺' =
  S²ToSetElim (λ _ → isProp→isSet (isPropIsEquiv _))
    (subst isEquiv (funExt id≡) (idIsEquiv _))
  where
  id≡ : (x : _) → x ≡ S²→Pushout⋁↪fold⋁S²↺ base x
  id≡ = trElim (λ _ → isOfHLevelPath 5 (isOfHLevelTrunc 5) _ _)
               (sym ∘ S²→Pushout⋁↪fold⋁S²↺'≡idfun)

S²→Pushout⋁↪fold⋁S²↺⁻¹ : (x : S²) → ∥Pushout⋁↪fold⋁S²∥₅ → ∥Pushout⋁↪fold⋁S²∥₅
S²→Pushout⋁↪fold⋁S²↺⁻¹ x = trRec (isOfHLevelTrunc 5) (S²→Pushout⋁↪fold⋁S²↺'⁻ x)

{- S²→Pushout⋁↪fold⋁S²↺⁻¹ is a section of S²→Pushout⋁↪fold⋁S²↺ -}
secS²→Pushout⋁↪fold⋁S²↺ : (x : S²) (y : ∥Pushout⋁↪fold⋁S²∥₅)
  → S²→Pushout⋁↪fold⋁S²↺ x (S²→Pushout⋁↪fold⋁S²↺⁻¹ x y) ≡ y
secS²→Pushout⋁↪fold⋁S²↺ x =
  trElim (λ _ → isOfHLevelPath 5 (isOfHLevelTrunc 5) _ _)
         (h x)
  where
  h : (x : S²) (a : Pushout⋁↪fold⋁S²)
    → S²→Pushout⋁↪fold⋁S²↺ x
        (S²→Pushout⋁↪fold⋁S²↺⁻¹ x ∣ a ∣) ≡ ∣ a ∣
  h base a = cong (S²→Pushout⋁↪fold⋁S²↺ base)
                  (S²→Pushout⋁↪fold⋁S²↺'≡idfun a)
           ∙ S²→Pushout⋁↪fold⋁S²↺'≡idfun a
  h (surf i j) a k = main a k i j
    where
    side : (a : Pushout⋁↪fold⋁S²) → _
    side a = cong (S²→Pushout⋁↪fold⋁S²↺ base) (S²→Pushout⋁↪fold⋁S²↺'≡idfun a)
          ∙ S²→Pushout⋁↪fold⋁S²↺'≡idfun a

    refl-b : Path ∥Pushout⋁↪fold⋁S²∥₅ _ _
    refl-b = (refl {x = ∣ inl (base , base) ∣ₕ})

    main : (a : Pushout⋁↪fold⋁S²)
      → Cube (λ i j → S²→Pushout⋁↪fold⋁S²↺ (surf i j)
                 (S²→Pushout⋁↪fold⋁S²↺⁻¹ (surf i j) ∣ a ∣))
              (λ _ _ → ∣ a ∣)
              (λ i _ → side a i) (λ i _ → side a i)
              (λ i _ → side a i) (λ i _ → side a i)
    main =
      Pushout⋁↪fold⋁S²→Set (λ _ → isOfHLevelPathP' 2
                  (isOfHLevelPathP' 3 (isOfHLevelTrunc 5 _ _) _ _) _ _)
       λ k i j →
         hcomp (λ r → λ { (i = i0) → rUnit refl-b r k
                         ; (i = i1) → rUnit refl-b r k
                         ; (j = i0) → rUnit refl-b r k
                         ; (j = i1) → rUnit refl-b r k
                         ; (k = i0) → →Ω²∥Pushout⋁↪fold⋁S²∥₅Id
                                        (surf (~ i) j) (~ r) i j
                         ; (k = i1) → μ base base})
               (μ-coh k i j)
      where
      μ : (x y : S²) → ∥Pushout⋁↪fold⋁S²∥₅
      μ x y = ∣ inl (x , y) ∣ₕ

      μUnit : (x : S²) → μ x base ≡ μ base x
      μUnit base = refl
      μUnit (surf i j) k = ∣
        hcomp (λ r → λ {(i = i0) → push (push tt k) (~ r)
                       ; (i = i1) → push (push tt k) (~ r)
                       ; (j = i0) → push (push tt k) (~ r)
                       ; (j = i1) → push (push tt k) (~ r)
                       ; (k = i0) → push (inl (surf i j)) (~ r)
                       ; (k = i1) → push (inr (surf i j)) (~ r)})
               (inr (surf i j)) ∣ₕ

      μ-coh : Path (Square {A = ∥Pushout⋁↪fold⋁S²∥₅}
             (λ _ → ∣ inl (base , base) ∣) (λ _ → ∣ inl (base , base) ∣)
             (λ _ → ∣ inl (base , base) ∣) (λ _ → ∣ inl (base , base) ∣))
             (λ i j → ∣ inl (surf (~ i) j , surf i j) ∣ₕ)
             refl
      μ-coh =
            (cong₂Funct (λ (x y : (Path S² base base)) → cong₂ μ x y) (sym surf) surf
           ∙ cong (_∙ cong (cong (μ base)) surf) (λ i → cong (cong (λ x → μUnit x i)) (sym surf))
           ∙ lCancel (cong (cong (μ base)) surf))

retrS²→Pushout⋁↪fold⋁S²↺ : (x : S²) (y : ∥Pushout⋁↪fold⋁S²∥₅)
  → S²→Pushout⋁↪fold⋁S²↺⁻¹ x (S²→Pushout⋁↪fold⋁S²↺ x y) ≡ y
retrS²→Pushout⋁↪fold⋁S²↺ x =
  trElim (λ _ → isOfHLevelPath 5 (isOfHLevelTrunc 5) _ _)
    (main x)
    where
    main : (x : S²) (a : Pushout⋁↪fold⋁S²)
      → S²→Pushout⋁↪fold⋁S²↺⁻¹ x (S²→Pushout⋁↪fold⋁S²↺ x ∣ a ∣) ≡ ∣ a ∣
    main base a = secS²→Pushout⋁↪fold⋁S²↺ base ∣ a ∣
    main (surf i j) a l = secS²→Pushout⋁↪fold⋁S²↺ (surf (~ i) j) ∣ a ∣ l

∥Pushout⋁↪fold⋁S²∥₅≃∥Pushout⋁↪fold⋁S²∥₅ : (x : S²)
  → Iso ∥Pushout⋁↪fold⋁S²∥₅ ∥Pushout⋁↪fold⋁S²∥₅
fun (∥Pushout⋁↪fold⋁S²∥₅≃∥Pushout⋁↪fold⋁S²∥₅ x) = S²→Pushout⋁↪fold⋁S²↺ x
inv (∥Pushout⋁↪fold⋁S²∥₅≃∥Pushout⋁↪fold⋁S²∥₅ x) = S²→Pushout⋁↪fold⋁S²↺⁻¹ x
rightInv (∥Pushout⋁↪fold⋁S²∥₅≃∥Pushout⋁↪fold⋁S²∥₅ x) = secS²→Pushout⋁↪fold⋁S²↺ x
leftInv (∥Pushout⋁↪fold⋁S²∥₅≃∥Pushout⋁↪fold⋁S²∥₅ x) = retrS²→Pushout⋁↪fold⋁S²↺ x

PreCode : (x : Susp S²) → Type
PreCode north = ∥Pushout⋁↪fold⋁S²∥₅
PreCode south = ∥Pushout⋁↪fold⋁S²∥₅
PreCode (merid a i) = isoToPath (∥Pushout⋁↪fold⋁S²∥₅≃∥Pushout⋁↪fold⋁S²∥₅ a) i

hLevPreCode : (x : Susp S²) → isOfHLevel 5 (PreCode x)
hLevPreCode =
  suspToPropElim base (λ _ → isPropIsOfHLevel 5) (isOfHLevelTrunc 5)

Code : (hLevelTrunc 6 (Susp S²)) → Type ℓ-zero
Code =
  fst ∘ trRec {B = TypeOfHLevel ℓ-zero 5} (isOfHLevelTypeOfHLevel 5)
    λ x → (PreCode x) , (hLevPreCode x)

private
  cong-coherence : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (r : refl ≡ p)
                  → cong (p ∙_) (sym r) ∙ sym (rUnit p)
                  ≡ cong (_∙ p) (sym r) ∙ sym (lUnit p)
  cong-coherence p = J (λ p r → cong (p ∙_) (sym r) ∙ sym (rUnit p)
                    ≡ cong (_∙ p) (sym r) ∙ sym (lUnit p)) refl

{- The function Pushout⋁↪fold⋁S² → Ω∥S³∥₆ will be the obvious one -}
Pushout⋁↪fold⋁S²→Ω∥S³∥₆ : Pushout⋁↪fold⋁S² → Ω∥S³∥₆
Pushout⋁↪fold⋁S²→Ω∥S³∥₆ (inl x) = cong ∣_∣ₕ (σ S²∙ (fst x) ∙ σ S²∙ (snd x))
Pushout⋁↪fold⋁S²→Ω∥S³∥₆ (inr x) = cong ∣_∣ₕ (σ S²∙ x)
Pushout⋁↪fold⋁S²→Ω∥S³∥₆ (push (inl x) i) j =
  ∣ (cong (σ S²∙ x ∙_) (rCancel (merid base)) ∙ sym (rUnit (σ S²∙ x))) i j ∣ₕ
Pushout⋁↪fold⋁S²→Ω∥S³∥₆ (push (inr x) i) j =
  ∣ (cong (_∙ σ S²∙ x) (rCancel (merid base)) ∙ sym (lUnit (σ S²∙ x))) i j ∣ₕ
Pushout⋁↪fold⋁S²→Ω∥S³∥₆ (push (push a k) i) j =
  ∣ cong-coherence (σ S²∙ base) (sym (rCancel (merid base))) k i j ∣ₕ

{- Truncated version (the equivalence) -}
∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆ : ∥Pushout⋁↪fold⋁S²∥₅ → Ω∥S³∥₆
∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆ =
  trRec (isOfHLevelTrunc 6 _ _) Pushout⋁↪fold⋁S²→Ω∥S³∥₆

decode' : (x : Susp S²) → Code ∣ x ∣
      → Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ ∣ x ∣
decode' north p = ∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆ p
decode' south p = ∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆ p ∙ cong ∣_∣ₕ (merid base)
decode' (merid a i) = main a i
  where
  baseId : (x : Pushout⋁↪fold⋁S²)
     → ∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆ (S²→Pushout⋁↪fold⋁S²↺' base x)
      ≡ ∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆ ∣ x ∣
  baseId x =
    cong ∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆ (S²→Pushout⋁↪fold⋁S²↺'≡idfun x)

  mainLemma : (a : S²) (x : Pushout⋁↪fold⋁S²)
     → ∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆ (S²→Pushout⋁↪fold⋁S²↺'⁻ a x)
       ∙ (λ i → ∣ merid a i ∣)
     ≡ ∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆ ∣ x ∣ ∙ cong ∣_∣ₕ (merid base)
  mainLemma base x = cong (_∙ cong ∣_∣ₕ (merid base)) (baseId x)
  mainLemma (surf i j) x k = surf-filler x k i j
    where
    ∙ΩbaseId :
      (q : typ (Ω (Susp∙ (typ S²∙)))) → q ≡ q ∙ σ S²∙ base
    ∙ΩbaseId q = rUnit q ∙ cong (q ∙_) (sym (rCancel (merid base)))

    cubeCoherence :
      ∀ {ℓ} {A : Type ℓ} {x : A} {p : x ≡ x}
      → (refl ≡ p)
      → (q : Square {A = x ≡ x} (λ _ → p) (λ _ → p) (λ _ → p) (λ _ → p))
      → Cube {A = Path A x x}
              (λ i j → q i j ∙ q (~ i) j) (λ _ _ → p ∙ p)
              (λ k j → p ∙ p) (λ _ _ → p ∙ p)
              (λ _ _ → p ∙ p) λ _ _ → p ∙ p
    cubeCoherence {A = A} {x = x} {p = p} =
      J (λ p _ → (q : Square {A = x ≡ x}
                        (λ _ → p) (λ _ → p) (λ _ → p) (λ _ → p))
               → Cube {A = Path A x x}
                       (λ i j → q i j ∙ q (~ i) j) (λ _ _ → p ∙ p)
                       (λ k j → p ∙ p) (λ _ _ → p ∙ p)
                       (λ _ _ → p ∙ p) λ _ _ → p ∙ p)
      (λ q →
        (cong₂Funct (λ (x y : Path (x ≡ x) refl refl) → cong₂ _∙_ x y) q (sym q)
      ∙ transport
         (λ i → cong (λ (p : (refl {x = x}) ≡ refl) k → rUnit (p k) i) q
               ∙ cong (λ (p : (refl {x = x}) ≡ refl) k → lUnit (p k) i) (sym q)
               ≡ refl {x = refl {x = lUnit (refl {x = x}) i}})
         (rCancel q)))

    surf-side : (i j r l : I) → hLevelTrunc 6 (Susp S²)
    surf-side i j r l =
      ((cong ∣_∣ₕ (∙ΩbaseId (σ S²∙ (surf (~ i) j)) r))
      ∙ cong ∣_∣ₕ (compPath-filler (merid (surf i j))
                  (sym (merid base)) (~ r))) l

    side : (r l : I) → hLevelTrunc 6 (Susp S²)
    side r l =
      ((cong ∣_∣ₕ (∙ΩbaseId (σ S²∙ base) r))
      ∙ cong ∣_∣ₕ (compPath-filler (merid base)
                  (sym (merid base)) (~ r))) l

    surf-filler : (x : Pushout⋁↪fold⋁S²)
      → Cube {A = Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ ∣ south ∣}
              (λ i j → ∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆
                         (S²→Pushout⋁↪fold⋁S²↺' (surf (~ i) j) x)
                       ∙ (λ k → ∣ merid (surf i j) k ∣))
              (λ _ _ → ∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆ ∣ x ∣
                      ∙ cong ∣_∣ₕ (merid base))
              (λ k j → baseId x k ∙ (λ i₂ → ∣ merid base i₂ ∣))
              (λ k j → baseId x k ∙ (λ i₂ → ∣ merid base i₂ ∣))
              (λ k i → baseId x k ∙ (λ i₂ → ∣ merid base i₂ ∣))
              (λ k i → baseId x k ∙ (λ i₂ → ∣ merid base i₂ ∣))
    surf-filler =
      Pushout⋁↪fold⋁S²→Set
       (λ _ → isOfHLevelPathP' 2
        (isOfHLevelPathP' 3 (isOfHLevelTrunc 6 _ _ _ _) _ _) _ _)
         (λ k i j l → hcomp (λ r
           → λ {(i = i0) → surf-side i0 i0 r l
               ; (i = i1) → surf-side i0 i0 r l
               ; (j = i0) → surf-side i0 i0 r l
               ; (j = i1) → surf-side i0 i0 r l
               ; (k = i0) → surf-side i j r l
               ; (k = i1) → surf-side i0 i0 r l
               ; (l = i0) → ∣ north ∣ₕ
               ; (l = i1) → ∣ merid base r ∣ₕ})
      (cubeCoherence {p = cong ∣_∣ₕ (σ (S²∙) base)}
        (cong (cong ∣_∣ₕ) (sym (rCancel (merid base))))
        (λ i j k → ∣ σ S²∙ (surf (~ i) j) k ∣ₕ) k i j l))

  main : (a : S²)
    → PathP (λ i → Code ∣ merid a i ∣
                  → Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ ∣ merid a i ∣)
                        ∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆
                        λ x → ∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆ x
                             ∙ cong ∣_∣ₕ (merid base)
  main a =
    toPathP (funExt
      (trElim (λ _ → isOfHLevelSuc 4 (isOfHLevelTrunc 6 _ _ _ _))
       (λ x
      → (λ j → transp (λ i → Path
                 (hLevelTrunc 6 (Susp S²)) ∣ north ∣ ∣ merid a (i ∨ j) ∣) j
                  (compPath-filler
                   (∥Pushout⋁↪fold⋁S²∥₅→Ω∥S³∥₆
                    (S²→Pushout⋁↪fold⋁S²↺'⁻ a (transportRefl x j)))
                     (cong ∣_∣ₕ (merid a)) j))
      ∙ mainLemma a x)))

decode : (x : hLevelTrunc 6 (Susp S²))
  → Code x → Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ x
decode =
  trElim (λ _ → isOfHLevelΠ 6 λ _ → isOfHLevelPath 6 (isOfHLevelTrunc 6) _ _)
         decode'

decode∙ : decode ∣ north ∣ ∣ inl (base , base) ∣ ≡ refl
decode∙ =
  cong (cong ∣_∣ₕ) (cong (λ x → x ∙ x) (rCancel (merid base)) ∙ sym (rUnit refl))

encode : (x : hLevelTrunc 6 (Susp S²))
  → Path (hLevelTrunc 6 (Susp S²)) ∣ north ∣ x → Code x
encode x p = subst Code p ∣ inl (base , base) ∣

encode-decode : (x : hLevelTrunc 6 (Susp S²))
  → (p : ∣ north ∣ ≡ x) → decode x (encode x p) ≡ p
encode-decode x = J (λ x p → decode x (encode x p) ≡ p)
              (cong (decode ∣ north ∣) (transportRefl ∣ inl (base , base) ∣ₕ)
             ∙ decode∙)

decode-encode : (p : Code ∣ north ∣) → encode ∣ north ∣ (decode ∣ north ∣ p) ≡ p
decode-encode =
  trElim (λ _ → isOfHLevelPath 5 (isOfHLevelTrunc 5) _ _)
    (Pushout⋁↪fold⋁S²WedgeCon.main ((λ a → encode ∣ north ∣ (decode ∣ north ∣ ∣ a ∣))) ∣_∣ₕ
      (isOfHLevelTrunc 5)
      (λ x → cong (encode ∣ north ∣) (cong (cong ∣_∣ₕ) (cong (σ S²∙ x ∙_)
               (rCancel (merid base)) ∙ sym (rUnit (σ S²∙ x))))
             ∙ surf-filler x)
      (λ x → (cong (encode ∣ north ∣) (cong (cong ∣_∣ₕ) (cong (_∙ σ S²∙ x)
               (rCancel (merid base)) ∙ sym (lUnit (σ S²∙ x))))
             ∙ surf-filler x
             ∙ cong ∣_∣ₕ (push (inl x)) ∙ cong ∣_∣ₕ (sym (push (inr x)))))
      λ x → lem (encode ∣ north ∣)
                (cong (decode ∣ north ∣) (cong ∣_∣ₕ (push (inl x))))
                ((cong (decode ∣ north ∣) (cong ∣_∣ₕ (push (inr x)))))
                (surf-filler x) (cong ∣_∣ₕ (push (inl x))) (cong ∣_∣ₕ (sym (push (inr x)))))
  where
  subber = transport (λ j → Code ∣ merid base (~ j) ∣ₕ)

  lem : ∀ {ℓ} {A B : Type ℓ} {x x' y : A} {l w u : B}
       (f : A → B) (p : x ≡ y) (p' : x' ≡ y) (q : f y ≡ l)
       (r : l ≡ w) (r' : w ≡ u)
     → cong f (sym p) ∙∙ cong f p ∙ q ∙∙ r
     ≡ (cong f (sym p') ∙∙ (cong f p' ∙ q ∙ (r ∙ r')) ∙∙ sym r')
  lem {x = x} {x' = x'} {y = y'} {l = l} {w = w} {u = u} f p p' q r r' =
      (λ i → (λ j → f (p (~ j ∨ i))) ∙∙ (λ j → f (p (j ∨ i))) ∙ q ∙∙ r)
   ∙∙ (λ i → (λ j → f (p' (~ j ∨ ~ i))) ∙∙ (λ j → f (p' (j ∨ ~ i)))
            ∙ compPath-filler q r i ∙∙ λ j → r (i ∨ j))
   ∙∙ λ i → cong f (sym p') ∙∙ cong f p' ∙ q
            ∙ compPath-filler r r' i ∙∙ λ j → r' (~ j ∧ i)

  mainId : (x : S²)
    → (S²→Pushout⋁↪fold⋁S²↺' x (inl (base , base))) ≡ ∣ inl (x , base) ∣ₕ
  mainId base = refl
  mainId (surf i i₁) = refl

  surf-filler : (x : S²)
    → encode ∣ north ∣ (λ i → ∣ σ S²∙ x i ∣) ≡ ∣ inl (x , base) ∣
  surf-filler x =
       (λ i → transp (λ j →  Code (∣ merid base (i ∧ ~ j) ∣ₕ)) (~ i)
                   (encode ∣ merid base i ∣
                    λ j → ∣ compPath-filler
                             (merid x) (sym (merid base)) (~ i) j ∣ₕ))
     ∙ cong subber
        (transportRefl (S²→Pushout⋁↪fold⋁S²↺' x (inl (base , base)))
       ∙ mainId x)

IsoΩ∥SuspS²∥₅∥Pushout⋁↪fold⋁S²∥₅ :
  Iso (hLevelTrunc 5 (typ (Ω (Susp∙ S²))))
      (hLevelTrunc 5 Pushout⋁↪fold⋁S²)
IsoΩ∥SuspS²∥₅∥Pushout⋁↪fold⋁S²∥₅ =
  compIso (invIso (PathIdTruncIso _)) is
  where
  is : Iso _ _
  fun is = encode ∣ north ∣
  inv is = decode ∣ north ∣
  rightInv is = decode-encode
  leftInv is = encode-decode ∣ north ∣
