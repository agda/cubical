{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.CupProduct where

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.Order2
open import Cubical.Homotopy.EilenbergMacLane.GradedCommTensor
  hiding (⌣ₖ-comm)

open import Cubical.Cohomology.EilenbergMacLane.Base

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup.Instances.IntMod


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.SetTruncation as ST

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open AbGroupStr renaming (_+_ to _+Gr_ ; -_ to -Gr_)
open RingStr

open PlusBis

private
  variable
    ℓ ℓ' : Level



module _ {G'' : Ring ℓ} {A : Type ℓ'} where
  private
    G' = Ring→AbGroup G''
    G = fst G'
    _+G_ = _+Gr_ (snd G')

    cup : (n m : ℕ) → EM G' n → EM G' m → EM G' (n +' m)
    cup n m x y = x ⌣ₖ y

  1ₕ : coHom zero G' A
  1ₕ = ∣ (λ _ → 1r (snd G'')) ∣₂

  _⌣_ : {n m : ℕ}
    → coHom n G' A → coHom m G' A → coHom (n +' m) G' A
  _⌣_ = ST.rec2 squash₂ λ f g → ∣ (λ x → f x ⌣ₖ g x) ∣₂

  ⌣-0ₕ : (n m : ℕ) (x : coHom n G' A) → (x ⌣ 0ₕ m) ≡ 0ₕ (n +' m)
  ⌣-0ₕ n m =
    ST.elim (λ _ → isSetPathImplicit)
      λ f → cong ∣_∣₂ (funExt λ x → ⌣ₖ-0ₖ n m (f x))

  0ₕ-⌣ : (n m : ℕ) (x : coHom m G' A) → (0ₕ n ⌣ x) ≡ 0ₕ (n +' m)
  0ₕ-⌣ n m =
    ST.elim (λ _ → isSetPathImplicit)
      λ f → cong ∣_∣₂ (funExt λ x → 0ₖ-⌣ₖ n m (f x))

  ⌣-1ₕ : (n : ℕ) (x : coHom n G' A)
    → (x ⌣ 1ₕ) ≡ subst (λ n → coHom n G' A) (+'-comm zero n) x
  ⌣-1ₕ n =
    ST.elim (λ _ → isSetPathImplicit) λ f → cong ∣_∣₂
            (funExt λ x → ⌣ₖ-1ₖ n (f x)
           ∙ cong (transport (λ i → EM G' (+'-comm zero n i)))
                  (cong f (sym (transportRefl x))))

  1ₕ-⌣ : (n : ℕ) (x : coHom n G' A) → (1ₕ ⌣ x) ≡ x
  1ₕ-⌣ n = ST.elim (λ _ → isSetPathImplicit) λ f → cong ∣_∣₂
            (funExt λ x → 1ₖ-⌣ₖ n (f x))

  distrR⌣ : (n m : ℕ) (x y : coHom n G' A) (z : coHom m G' A)
          → ((x +ₕ y) ⌣ z) ≡ (x ⌣ z) +ₕ (y ⌣ z)
  distrR⌣ n m =
    ST.elim2 (λ _ _ → isSetΠ (λ _ → isSetPathImplicit))
      λ f g → ST.elim (λ _ → isSetPathImplicit)
        λ h → cong ∣_∣₂ (funExt (λ x → distrR⌣ₖ n m (f x) (g x) (h x)))

  distrL⌣ : (n m : ℕ) (x : coHom n G' A) (y z : coHom m G' A)
          → (x ⌣ (y +ₕ z)) ≡ (x ⌣ y) +ₕ (x ⌣ z)
  distrL⌣ n m =
    ST.elim (λ _ → isSetΠ2 (λ _ _ → isSetPathImplicit))
      λ f → ST.elim2 (λ _ _ → isSetPathImplicit)
        λ g h → cong ∣_∣₂ (funExt (λ x → distrL⌣ₖ n m (f x) (g x) (h x)))

  assoc⌣ : (n m l : ℕ)
       (x : coHom n G' A) (y : coHom m G' A) (z : coHom l G' A)
    → ((x ⌣ y) ⌣ z) ≡ subst (λ n → coHom n G' A) (+'-assoc n m l) (x ⌣ (y ⌣ z))
  assoc⌣ n m l =
    ST.elim (λ _ → isSetΠ2 (λ _ _ → isSetPathImplicit))
      λ f → ST.elim (λ _ → isSetΠ (λ _ → isSetPathImplicit))
        λ g → ST.elim (λ _ → isSetPathImplicit)
          λ h → cong ∣_∣₂ (funExt λ x → assoc⌣ₖ n m l (f x) (g x) (h x)
            ∙ cong (transport (λ i → EM G' (+'-assoc n m l i)))
               (cong (λ x → (f x ⌣ₖ (g x ⌣ₖ h x))) (sym (transportRefl x))))

-- Graded commutativity
-ₕ^[_·_] : {G' : AbGroup ℓ} {A : Type ℓ'} (n m : ℕ) {k : ℕ}
  → coHom k G' A → coHom k G' A
-ₕ^[ n · m ] = ST.map λ f x → -ₖ^[ n · m ] (f x)

-ₕ^[_·_]-even : {G' : AbGroup ℓ} {A : Type ℓ'} (n m : ℕ) {k : ℕ}
  → isEvenT n ⊎ isEvenT m
  → (x : coHom k G' A) → -ₕ^[ n · m ] x ≡ x
-ₕ^[ n · m ]-even {k = k} p =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (funExt λ x → -ₖ^[ n · m ]-even p (f x))

-ₕ^[_·_]-odd : {G' : AbGroup ℓ} {A : Type ℓ'} (n m : ℕ) {k : ℕ}
  → isOddT n × isOddT m
  → (x : coHom k G' A) → -ₕ^[ n · m ] x ≡ -ₕ x
-ₕ^[ n · m ]-odd {k = k} p =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (funExt λ x → -ₖ^[ n · m ]-odd p (f x))

comm⌣ : {G'' : CommRing ℓ} {A : Type ℓ'} (n m : ℕ)
  → (x : coHom n (CommRing→AbGroup G'') A)
     (y : coHom m (CommRing→AbGroup G'') A)
  → x ⌣ y ≡ subst (λ n → coHom n (CommRing→AbGroup G'') A)
                   (+'-comm m n)
                   (-ₕ^[ n · m ] (y ⌣ x))
comm⌣ {G'' = R} {A = A} n m =
  ST.elim2 (λ _ _ → isSetPathImplicit)
   λ f g →
     cong ∣_∣₂ (funExt λ x → ⌣ₖ-comm n m (f x) (g x)
            ∙ cong (subst (λ n → EM (CommRing→AbGroup R) n) (+'-comm m n))
                 (cong -ₖ^[ n · m ]
                   (cong₂ _⌣ₖ_ (cong g (sym (transportRefl x)))
                               (cong f (sym (transportRefl x))))))


-- some syntax
⌣[]-syntax : {A : Type ℓ} {n m : ℕ} (R : Ring ℓ')
  → coHom n (Ring→AbGroup R) A
  → coHom m (Ring→AbGroup R) A
  → coHom (n +' m) (Ring→AbGroup R) A
⌣[]-syntax R x y = x ⌣ y

⌣[]C-syntax : {A : Type ℓ} {n m : ℕ} (R : CommRing ℓ')
  → coHom n (CommRing→AbGroup R) A
  → coHom m (CommRing→AbGroup R) A
  → coHom (n +' m) (CommRing→AbGroup R) A
⌣[]C-syntax R x y = x ⌣ y

⌣[,,]-syntax : {A : Type ℓ} (n m : ℕ) (R : Ring ℓ')
  → coHom n (Ring→AbGroup R) A
  → coHom m (Ring→AbGroup R) A
  → coHom (n +' m) (Ring→AbGroup R) A
⌣[,,]-syntax n m R x y = x ⌣ y

⌣[,,]C-syntax : {A : Type ℓ} (n m : ℕ) (R : CommRing ℓ')
  → coHom n (CommRing→AbGroup R) A
  → coHom m (CommRing→AbGroup R) A
  → coHom (n +' m) (CommRing→AbGroup R) A
⌣[,,]C-syntax n m R x y = x ⌣ y

syntax ⌣[]-syntax R x y = x ⌣[ R ] y
syntax ⌣[]C-syntax R x y = x ⌣[ R ]C y
syntax ⌣[,,]-syntax n m R x y = x ⌣[ R , n , m ] y
syntax ⌣[,,]C-syntax n m R x y = x ⌣[ R , n , m ]C y

-- Commutativity in ℤ/2 coeffs
comm⌣ℤ/2 : {A : Type ℓ'} (n m : ℕ)
  → (x : coHom n ℤ/2 A)
     (y : coHom m ℤ/2 A)
  → x ⌣[ ℤ/2Ring ] y
   ≡ subst (λ n → coHom n ℤ/2 A) (+'-comm m n)
           (y ⌣[ ℤ/2Ring ] x)
comm⌣ℤ/2 {A = A} n m x y = comm⌣ {G'' = ℤ/2CommRing} n m x y
                 ∙ cong (subst (λ n₁ → coHom n₁ ℤ/2 A) (+'-comm m n))
                        (lem x y)
  where
  lem : (x : coHom n ℤ/2 A) (y : coHom m ℤ/2 A)
     → -ₕ^[ n · m ] (y ⌣[ ℤ/2Ring ] x) ≡ (y ⌣ x)
  lem = ST.elim2 (λ _ _ → isSetPathImplicit)
          λ _ _ → cong ∣_∣₂ (funExt λ _ → -ₖ^[ n · m ]-const _)

module _ {G'' : Ring ℓ} {A : Type ℓ'} where
  private
    G' = Ring→AbGroup G''

  ⌣-1ₕDep : (n : ℕ) (x : coHom n G' A)
    → PathP (λ i → coHom (+'-comm zero n (~ i)) G' A) (x ⌣ 1ₕ) x
  ⌣-1ₕDep n x = toPathP {A = λ i → coHom (+'-comm zero n (~ i)) G' A}
                        (flipTransport (⌣-1ₕ n x))

  assoc⌣Dep : (n m l : ℕ)
       (x : coHom n G' A) (y : coHom m G' A) (z : coHom l G' A)
    → PathP (λ i → coHom (+'-assoc n m l (~ i)) G' A) ((x ⌣ y) ⌣ z) (x ⌣ (y ⌣ z))
  assoc⌣Dep n m l x y z = toPathP {A = λ i → coHom (+'-assoc n m l (~ i)) G' A}
                                  (flipTransport (assoc⌣ n m l x y z))

module _ {G'' : CommRing ℓ} {A : Type ℓ'} where
  private
    G' = CommRing→AbGroup G''
  comm⌣Dep : (n m : ℕ)  (x : coHom n G' A) (y : coHom m G' A)
    → PathP (λ i → coHom (+'-comm m n (~ i)) G' A)
             (x ⌣ y) (-ₕ^[ n · m ] (y ⌣ x))
  comm⌣Dep n m x y =
    toPathP {A = λ i → coHom (+'-comm m n (~ i)) G' A}
      (flipTransport (comm⌣ n m x y))
