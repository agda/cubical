module Cubical.Algebra.DirectSum.DirectSumFun.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.DirectSum.DirectSumFun.Base

private variable
  ℓ : Level

open GroupTheory
open AbGroupStr

-----------------------------------------------------------------------------
-- AbGroup Properties

module DSF-properties
  (G : ℕ → Type ℓ)
  (Gstr : (n : ℕ) → AbGroupStr (G n))
  where

  private
    GG : ℕ → Group ℓ
    GG n = AbGroup→Group ((G n) , (Gstr n))

  isSet⊕Fun : isSet (⊕Fun G Gstr)
  isSet⊕Fun = isSetΣSndProp (isSetΠ (λ n → is-set (Gstr n))) (λ _ → squash₁)


  -- Object
  0⊕Fun : ⊕Fun G Gstr
  0⊕Fun = (λ n → 0g (Gstr n)) , ∣ (0 , λ n p → refl) ∣₁

  _+⊕Fun_ : ⊕Fun G Gstr → ⊕Fun G Gstr → ⊕Fun G Gstr
  _+⊕Fun_ (f , Anf) (g , Ang) = f+g , Anf+g Anf Ang
    where
    f+g = λ n → Gstr n ._+_ (f n) (g n)
    Anf+g : AlmostNullP G Gstr f → AlmostNullP G Gstr g → AlmostNullP G Gstr f+g
    Anf+g = PT.rec2 squash₁
            (λ { (k , nf) → λ { (l , ng) →
               ∣ ((k +n l) ,
                 (λ n p → cong₂ ((Gstr n)._+_) (nf n (<-+k-trans p)) (ng n (<-k+-trans p))
                           ∙ +IdR (Gstr n) (0g (Gstr n)))) ∣₁ } })


  Inv⊕Fun : ⊕Fun G Gstr → ⊕Fun G Gstr
  Inv⊕Fun (f , Anf) = f- , Anf- Anf
    where
    f- = λ n → (Gstr n).-_ (f n)
    Anf- : AlmostNullP G Gstr f → AlmostNullP G Gstr f-
    Anf- = PT.rec squash₁
           (λ { (k , nf) →
              ∣ (k , λ n p → cong ((Gstr n).-_) (nf n p) ∙ inv1g (GG n)) ∣₁})


  -- AbGroup Properties
  +⊕FunAssoc : (x y z : ⊕Fun G Gstr) → x +⊕Fun (y +⊕Fun z) ≡ (x +⊕Fun y) +⊕Fun z
  +⊕FunAssoc (f , Anf) (g , Ang) (h , Anh) =
             ΣPathTransport→PathΣ _ _
             (funExt (λ n → Gstr n .+Assoc _ _ _) , (squash₁ _ _))

  +⊕FunRid : (x : ⊕Fun G Gstr) → x +⊕Fun 0⊕Fun ≡ x
  +⊕FunRid (f , Anf) = ΣPathTransport→PathΣ _ _
                       ((funExt (λ n → +IdR (Gstr n) _)) , squash₁ _ _)

  +⊕FunInvR : (x : ⊕Fun G Gstr) → x +⊕Fun Inv⊕Fun x ≡ 0⊕Fun
  +⊕FunInvR (f , Anf) = ΣPathTransport→PathΣ _ _
                        ((funExt (λ n → +InvR (Gstr n) _)) , (squash₁ _ _))

  +⊕FunComm : (x y : ⊕Fun G Gstr) →  x +⊕Fun y ≡ y +⊕Fun x
  +⊕FunComm (f , Anf) (g , Ang) = ΣPathTransport→PathΣ _ _
                                  ((funExt (λ n → Gstr n .+Comm _ _)) , (squash₁ _ _))
