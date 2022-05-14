{-# OPTIONS --safe #-}
module Cubical.Algebra.DirectSum.Equiv-DSHIT-DSFun where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectSumHIT
open import Cubical.Algebra.AbGroup.Instances.DirectSumFun
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.DirectSum.DirectSumFun.Base
open import Cubical.Algebra.DirectSum.DirectSumHIT.Properties
open import Cubical.Algebra.DirectSum.DirectSumFun.Properties

private variable
  ℓ : Level

open GroupTheory
open AbGroupStr

-----------------------------------------------------------------------------
-- Notation

module Equiv-Properties
  (G : ℕ → Type ℓ)
  (Gstr : (n : ℕ) → AbGroupStr (G n))
  where

  -- the convention is a bit different and had a -
  -- because otherwise it is unreadable

  open AbGroupStr (snd (⊕HIT-AbGr ℕ G Gstr)) using ()
    renaming
    ( 0g       to 0⊕HIT
    ; _+_      to _+⊕HIT_
    ; -_       to -⊕HIT_
    ; assoc    to +⊕HIT-Assoc
    ; identity to +⊕HIT-IdR×IdL
    ; inverse  to +⊕HIT-InvR×InvL
    ; comm     to +⊕HIT-Comm
    ; is-set   to isSet⊕HIT)

  private
    +⊕HIT-IdR : (x : ⊕HIT ℕ G Gstr) → x +⊕HIT 0⊕HIT ≡ x
    +⊕HIT-IdR = λ x → fst (+⊕HIT-IdR×IdL x)

    +⊕HIT-IdL : (x : ⊕HIT ℕ G Gstr) → 0⊕HIT +⊕HIT x  ≡ x
    +⊕HIT-IdL = λ x → snd (+⊕HIT-IdR×IdL x)

    +⊕HIT-InvR : (x : ⊕HIT ℕ G Gstr) → x +⊕HIT (-⊕HIT x) ≡ 0⊕HIT
    +⊕HIT-InvR = λ x → fst (+⊕HIT-InvR×InvL x)

    +⊕HIT-InvL : (x : ⊕HIT ℕ G Gstr) → (-⊕HIT x) +⊕HIT x ≡ 0⊕HIT
    +⊕HIT-InvL = λ x → snd (+⊕HIT-InvR×InvL x)


  open AbGroupStr (snd (⊕Fun-AbGr G Gstr)) using ()
    renaming
    ( 0g       to 0⊕Fun
    ; _+_      to _+⊕Fun_
    ; -_       to -⊕Fun_
    ; assoc    to +⊕Fun-Assoc
    ; identity to +⊕Fun-IdR×IdL
    ; inverse  to +⊕Fun-InvR×InvL
    ; comm     to +⊕Fun-Comm
    ; is-set   to isSet⊕Fun)

  private
    +⊕Fun-IdR : (x : ⊕Fun G Gstr) → x +⊕Fun 0⊕Fun ≡ x
    +⊕Fun-IdR = λ x → fst (+⊕Fun-IdR×IdL x)

    +⊕Fun-IdL : (x : ⊕Fun G Gstr) → 0⊕Fun +⊕Fun x  ≡ x
    +⊕Fun-IdL = λ x → snd (+⊕Fun-IdR×IdL x)

    +⊕Fun-InvR : (x : ⊕Fun G Gstr) → x +⊕Fun (-⊕Fun x) ≡ 0⊕Fun
    +⊕Fun-InvR = λ x → fst (+⊕Fun-InvR×InvL x)

    +⊕Fun-InvL : (x : ⊕Fun G Gstr) → (-⊕Fun x) +⊕Fun x ≡ 0⊕Fun
    +⊕Fun-InvL = λ x → snd (+⊕Fun-InvR×InvL x)

-----------------------------------------------------------------------------
-- Transport

  subst0 : {k n : ℕ} → (p : k ≡ n) → subst G p (0g (Gstr k)) ≡ 0g (Gstr n)
  subst0 {k} {n} p = J (λ n p → subst G p (0g (Gstr k)) ≡ 0g (Gstr n))
                       (transportRefl (0g (Gstr k)))
                       p

  subst+ : {k : ℕ} →  (x y : G k) → {n : ℕ} → (p : k ≡ n)
           → subst G p ((Gstr k)._+_ x y) ≡ (Gstr n)._+_ (subst G p x) (subst G p y)
  subst+ {k} x y {l} p = J (λ n p → subst G p ((Gstr k)._+_ x y) ≡ (Gstr n)._+_ (subst G p x) (subst G p y))
                         (transportRefl _ ∙ cong₂ ((Gstr k)._+_) (sym (transportRefl _)) (sym (transportRefl _)))
                         p

-----------------------------------------------------------------------------
-- Direct Sens

  ⊕HIT→⊕Fun : ⊕HIT ℕ G Gstr → ⊕Fun G Gstr
  ⊕HIT→⊕Fun = DS-Rec-Set.f _ _ _ _ isSet⊕Fun
               0⊕Fun
               base-trad
               _+⊕Fun_
               +⊕Fun-Assoc
               +⊕Fun-IdR
               +⊕Fun-Comm
               base-0
               base-+
            where
            base-trad : _
            base-trad k a = f , Anf
              where
              f : (n : ℕ) → G n
              f n with (discreteℕ k n)
              ... | yes p = subst G p a
              ... | no ¬p = 0g (Gstr n)

              Anf : _
              Anf = ∣ (k , nf) ∣₁
                where
                nf : _
                nf n q with (discreteℕ k n)
                ... | yes p = ⊥.rec (<→≢ q p)
                ... | no ¬p = refl

            base-0 : _
            base-0 k = ΣPathTransport→PathΣ _ _
                       (funExt f-eq , (squash₁ _ _))
                   where
                   f-eq : _
                   f-eq n with discreteℕ k n
                   ... | yes p = subst0 p
                   ... | no ¬p = refl

            base-+ : _
            base-+ k a b = ΣPathTransport→PathΣ _ _
                           ((funExt f-eq) , (squash₁ _ _))
                   where
                   f-eq : _
                   f-eq n with discreteℕ k n
                   ... | yes p = sym (subst+ a b p)
                   ... | no ¬p = fst (identity (Gstr n) (0g (Gstr n)))

  ⊕HIT→⊕Fun-pres0 : ⊕HIT→⊕Fun 0⊕HIT ≡ 0⊕Fun
  ⊕HIT→⊕Fun-pres0 = refl

  ⊕HIT→⊕Fun-pres+ : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→⊕Fun (x +⊕HIT y) ≡ ((⊕HIT→⊕Fun x) +⊕Fun (⊕HIT→⊕Fun y))
  ⊕HIT→⊕Fun-pres+ x y = refl
