{-# OPTIONS --safe #-}
module Cubical.Algebra.DirectSum.Equiv-DSHIT-DSFun where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectSumFun
open import Cubical.Algebra.DirectSum.DirectSumFun.Base
open import Cubical.Algebra.DirectSum.DirectSumFun.Properties
open import Cubical.Algebra.AbGroup.Instances.DirectSumHIT
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.DirectSum.DirectSumHIT.Properties

open import Cubical.Algebra.Polynomials.Univariate.Base

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

  substG : (g : (n : ℕ) → G n) → {k n : ℕ} → (p : k ≡ n) → subst G p (g k) ≡ g n
  substG g {k} {n} p = J (λ n p → subst G p (g k) ≡ g n) (transportRefl _) p


-----------------------------------------------------------------------------
-- Direct Sens

  -- trad on function
  fun-trad : (k : ℕ) → (a : G k) → (n : ℕ) → G n
  fun-trad k a n with (discreteℕ k n)
  ... | yes p = subst G p a
  ... | no ¬p = 0g (Gstr n)

  ⊕HIT→Fun : ⊕HIT ℕ G Gstr → (n : ℕ) → G n
  ⊕HIT→Fun = DS-Rec-Set.f _ _ _ _ (isSetΠ λ n → is-set (Gstr n))
              (λ n → 0g (Gstr n))
              fun-trad
              (λ f g n → Gstr n ._+_ (f n) (g n))
              (λ f g h → funExt λ n → assoc (Gstr n) (f n) (g n) (h n))
              (λ f → funExt λ n → fst (identity (Gstr n) (f n)))
              (λ f g → funExt λ n → comm (Gstr n) (f n) (g n))
              (λ k → funExt (λ n → base0-eq k n))
              λ k a b → funExt (λ n → base-add-eq k a b n)
           where
           base0-eq : (k : ℕ) → (n : ℕ) → fun-trad k (0g (Gstr k)) n ≡ 0g (Gstr n)
           base0-eq k n with (discreteℕ k n)
           ... | yes p = J (λ n p → subst G p (0g (Gstr k)) ≡ 0g (Gstr n))
                           (transportRefl _)
                           p
           ... | no ¬p = refl

           base-add-eq : (k : ℕ) → (a b : G k) → (n : ℕ) →
                         PathP (λ _ → G n) (Gstr n ._+_ (fun-trad k a n) (fun-trad k b n))
                                                         (fun-trad k ((Gstr k + a) b) n)
           base-add-eq k a b n with (discreteℕ k n)
           ... | yes p = J (λ n p → Gstr n ._+_ (transp (λ i → G (p i)) i0 a)
                                                (transp (λ i → G (p i)) i0 b)
                                     ≡ transp (λ i → G (p i)) i0 ((Gstr k + a) b))
                         (cong₂ ((Gstr k)._+_) (transportRefl _) (transportRefl _) ∙ sym (transportRefl _))
                         p
           ... | no ¬p = fst (identity (Gstr n) (0g (Gstr n)))

  -- trad on AlmostNull
  nfun-trad : (k : ℕ) → (a : G k) → AlmostNull G Gstr (fun-trad k a)
  nfun-trad k a = k , fix-eq
    where
    fix-eq : (n : ℕ) → k < n → fun-trad k a n ≡ 0g (Gstr n)
    fix-eq n q with (discreteℕ k n)
    ... | yes p = ⊥.rec (<→≢ q p)
    ... | no ¬p = refl

  ⊕HIT→⊕AlmostNull : (x : ⊕HIT ℕ G Gstr) → AlmostNullP G Gstr (⊕HIT→Fun x)
  ⊕HIT→⊕AlmostNull = DS-Ind-Prop.f _ _ _ _ (λ x → squash₁)
                      ∣ (0 , (λ n q → refl)) ∣₁
                      (λ r a → ∣ (nfun-trad r a) ∣₁)
                      λ {U} {V} → PT.elim (λ _ → isPropΠ (λ _ → squash₁))
                                   (λ { (k , nu) → PT.elim (λ _ → squash₁)
                                   λ { (l , nv) →
                                   ∣ ((k +n l) , (λ n q → cong₂ ((Gstr n)._+_) (nu n (<-+k-trans q)) (nv n (<-k+-trans q))
                                                          ∙ fst (identity (Gstr n) _))) ∣₁} })


  -- ⊕HIT→⊕Fun : ⊕HIT ℕ G Gstr → ⊕Fun G Gstr
  -- ⊕HIT→⊕Fun = DS-Rec-Set.f _ _ _ _ isSet⊕Fun
  --              0⊕Fun
  --              (λ k a → (fun-trad k a) , ∣ (nfun-trad k a) ∣₁)
  --              _+⊕Fun_
  --              +⊕Fun-Assoc
  --              +⊕Fun-IdR
  --              +⊕Fun-Comm
  --              base-0-eq
  --              base-add-eq
  --           where
  --           base-0-eq : _
  --           base-0-eq k = ΣPathTransport→PathΣ _ _
  --                         (funExt f-eq , (squash₁ _ _))
  --                     where
  --                     f-eq : _
  --                     f-eq n with discreteℕ k n
  --                     ... | yes p = subst0 p
  --                     ... | no ¬p = refl

  --           base-add-eq : _
  --           base-add-eq k a b = ΣPathTransport→PathΣ _ _
  --                          ((funExt f-eq) , (squash₁ _ _))
  --                       where
  --                       f-eq : _
  --                       f-eq n with discreteℕ k n
  --                       ... | yes p = sym (subst+ a b p)
  --                       ... | no ¬p = fst (identity (Gstr n) (0g (Gstr n)))

  ⊕HIT→⊕Fun : ⊕HIT ℕ G Gstr → ⊕Fun G Gstr
  ⊕HIT→⊕Fun x = (⊕HIT→Fun x) , (⊕HIT→⊕AlmostNull x)

  ⊕HIT→⊕Fun-pres0 : ⊕HIT→⊕Fun 0⊕HIT ≡ 0⊕Fun
  ⊕HIT→⊕Fun-pres0 = refl

  ⊕HIT→⊕Fun-pres+ : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→⊕Fun (x +⊕HIT y) ≡ ((⊕HIT→⊕Fun x) +⊕Fun (⊕HIT→⊕Fun y))
  ⊕HIT→⊕Fun-pres+ x y = ΣPathTransport→PathΣ _ _ (refl , (squash₁ _ _))


-----------------------------------------------------------------------------
-- Converse sens

  inj-⊕HIT→Fun : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→Fun x ≡ ⊕HIT→Fun y → x ≡ y
  inj-⊕HIT→Fun = {!!}

  inj-⊕HIT→⊕Fun : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→⊕Fun x ≡ ⊕HIT→⊕Fun y → x ≡ y
  inj-⊕HIT→⊕Fun x y p = inj-⊕HIT→Fun x y (fst (PathΣ→ΣPathTransport _ _ p))

  lemProp : (g : ⊕Fun G Gstr) → isProp (Σ[ x ∈ ⊕HIT ℕ G Gstr ] ⊕HIT→⊕Fun x ≡ g )
  lemProp g (x , p) (y , q) = ΣPathTransport→PathΣ _ _
                              ((inj-⊕HIT→⊕Fun x y (p ∙ sym q)) , isSet⊕Fun _ _ _ _)

  Strad : (g : (n : ℕ) → G n) → (i : ℕ) → ⊕HIT ℕ G Gstr
  Strad g zero = base 0 (g 0)
  Strad g (suc i) = (base (suc i) (g (suc i))) +⊕HIT (Strad g i)

  trad-< : (g : (n : ℕ) → G n) → (k : ℕ) → (ng : (n : ℕ) → ( k < n) → g n ≡ 0g (Gstr n))
           → (i : ℕ) → (n : ℕ) → (r : (k < n)) → ⊕HIT→Fun (Strad g i) n ≡ 0g (Gstr n)
  trad-< g k ng zero n r with discreteℕ 0 n
  ... | yes p = substG g p ∙ ng n r
  ... | no ¬p = refl
  trad-< g k ng (suc i) n r with discreteℕ (suc i) n
  ... | yes p = cong₂ ((Gstr n)._+_) (substG g p) (trad-< g k ng i n r)
                ∙ cong (λ X → Gstr n ._+_ X (0g (Gstr n))) (ng n r)
                ∙ fst (identity (Gstr n) _)
  ... | no ¬p = snd (identity (Gstr n) _) ∙ trad-< g k ng i n r

  trad-<< : (g : (n : ℕ) → G n) → (i : ℕ) → (n : ℕ) → (r : i < n)
            → ⊕HIT→Fun (Strad g i) n ≡ 0g (Gstr n)
  trad-<< g zero n r with discreteℕ 0 n
  ... | yes p = ⊥.rec (<→≢ r p)
  ... | no ¬p = refl
  trad-<< g (suc i) n r with discreteℕ (suc i) n
  ... | yes p = ⊥.rec (<→≢ r p)
  ... | no ¬p = snd (identity (Gstr n) _) ∙ trad-<< g i n (<-trans ≤-refl r)

  trad-≤ : (g : (n : ℕ) → G n) → (k : ℕ) → (n : ℕ) → (r : n ≤ k) → ⊕HIT→Fun (Strad g k) n ≡ g n
  trad-≤ g zero n r with discreteℕ 0 n
  ... | yes p = substG g p
  ... | no ¬p = ⊥.rec (¬p (sym (≤0→≡0 r)))
  trad-≤ g (suc k) n r with discreteℕ (suc k) n
  ... | yes p = cong₂ ((Gstr n)._+_) (substG g p) (trad-<< g k n (0 , p)) ∙ fst (identity (Gstr n) _)
  ... | no ¬p = snd (identity (Gstr n) _) ∙ trad-≤ g k n (≤-suc-≢ r λ x → ¬p (sym x))

  trad-eq : (g : (n : ℕ) → G n) → (k : ℕ) → (ng : (n : ℕ) → ( k < n) → g n ≡ 0g (Gstr n))
            → (n : ℕ) → ⊕HIT→Fun (Strad g k) n ≡ g n
  trad-eq g k ng n with splitℕ-< n k
  ... | inl x = trad-≤ g k n x
  ... | inr x = trad-<< g k n x ∙ sym (ng n x)

  ⊕Fun→⊕HIT+ : (g : ⊕Fun G Gstr) → Σ[ x ∈ ⊕HIT ℕ G Gstr ] ⊕HIT→⊕Fun x ≡ g
  ⊕Fun→⊕HIT+ (g , Ang) = PT.rec (lemProp (g , Ang))
                          (λ { (k , ng)
                               → Strad g k , ΣPathTransport→PathΣ _ _
                                              ((funExt (trad-eq g k ng)) , (squash₁ _ _)) })
                          Ang

  ⊕Fun→⊕HIT : ⊕Fun G Gstr → ⊕HIT ℕ G Gstr
  ⊕Fun→⊕HIT g = fst (⊕Fun→⊕HIT+ g)
