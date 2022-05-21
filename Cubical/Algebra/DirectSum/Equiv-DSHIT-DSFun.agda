{-# OPTIONS --safe #-}
module Cubical.Algebra.DirectSum.Equiv-DSHIT-DSFun where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Vec
open import Cubical.Data.Vec.DepVec

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectSumFun
open import Cubical.Algebra.DirectSum.DirectSumFun.Base
open import Cubical.Algebra.DirectSum.DirectSumFun.Properties
open import Cubical.Algebra.AbGroup.Instances.DirectSumHIT
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.DirectSum.DirectSumHIT.Properties
open import Cubical.Algebra.DirectSum.DirectSumHIT.PseudoNormalForm

open import Cubical.Algebra.Polynomials.Univariate.Base

private variable
  ℓ : Level

open GroupTheory
open AbGroupTheory
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
-- AbGroup on Fun -> produit ? sequence ?

    Fun-AbGroup : AbGroup ℓ
    fst Fun-AbGroup = (n : ℕ) → G n
    0g (snd Fun-AbGroup) =  λ n → 0g (Gstr n)
    _+_ (snd Fun-AbGroup) = λ f g n → Gstr n ._+_ (f n) (g n)
    - snd Fun-AbGroup = λ f n → (Gstr n).-_ (f n)
    isAbGroup (snd Fun-AbGroup) = makeIsAbGroup
                                  (isSetΠ (λ n → is-set (Gstr n)))
                                  (λ f g h → funExt (λ n → (Gstr n).assoc _ _ _))
                                  (λ f → funExt (λ n → fst (identity (Gstr n) _)))
                                  (λ f → funExt (λ n → fst (inverse (Gstr n) _)))
                                  (λ f g → funExt (λ n → comm (Gstr n) _ _))

  open AbGroupStr (snd Fun-AbGroup) using ()
      renaming
    ( 0g       to 0Fun
    ; _+_      to _+Fun_
    ; -_       to -Fun_
    ; assoc    to +FunAssoc
    ; identity to +FunIdR×IdL
    ; inverse  to +FunInvR×InvL
    ; comm     to +FunComm
    ; is-set   to isSetFun)

  private
    Fun : (G : (n : ℕ) → Type ℓ) → (Gstr : (n : ℕ) → AbGroupStr (G n)) → Type ℓ
    Fun G Gstr = (n : ℕ) → G n

    +⊕FunIdR : (x : Fun G Gstr) → x +Fun 0Fun ≡ x
    +⊕FunIdR = λ x → fst (+FunIdR×IdL x)

    +⊕FunIdL : (x : Fun G Gstr) → 0Fun +Fun x  ≡ x
    +⊕FunIdL = λ x → snd (+FunIdR×IdL x)

    +⊕FunInvR : (x : Fun G Gstr) → x +Fun (-Fun x) ≡ 0Fun
    +⊕FunInvR = λ x → fst (+FunInvR×InvL x)

    +⊕FunInvL : (x : Fun G Gstr) → (-Fun x) +Fun x ≡ 0Fun
    +⊕FunInvL = λ x → snd (+FunInvR×InvL x)


-----------------------------------------------------------------------------
-- Some simplification for transport

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

  -- To facilitate the proof the traduction to the function
  -- and its properties are done in two times

  ---------------------------------------------------------------------------
  -- Traduction to the function

  fun-trad : (k : ℕ) → (a : G k) → (n : ℕ) → G n
  fun-trad k a n with (discreteℕ k n)
  ... | yes p = subst G p a
  ... | no ¬p = 0g (Gstr n)

  fun-trad-eq : (k : ℕ) → (a : G k) → fun-trad k a k ≡ a
  fun-trad-eq k a with discreteℕ k k
  ... | yes p = cong (λ X → subst G X a) (isSetℕ _ _ _ _) ∙ transportRefl a
  ... | no ¬p = ⊥.rec (¬p refl)

  fun-trad-neq : (k : ℕ) → (a : G k) → (n : ℕ) → (k ≡ n → ⊥) → fun-trad k a n ≡ 0g (Gstr n)
  fun-trad-neq k a n ¬q with discreteℕ k n
  ... | yes p = ⊥.rec (¬q p)
  ... | no ¬p = refl

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

  ⊕HIT→Fun-pres0 : ⊕HIT→Fun 0⊕HIT ≡ 0Fun
  ⊕HIT→Fun-pres0 = refl

  ⊕HIT→Fun-pres+ : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→Fun (x +⊕HIT y) ≡ ((⊕HIT→Fun x) +Fun (⊕HIT→Fun y))
  ⊕HIT→Fun-pres+ x y = refl

  ---------------------------------------------------------------------------
  -- Traduction to the properties

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

  ---------------------------------------------------------------------------
  -- Traduction + Morphism

  ⊕HIT→⊕Fun : ⊕HIT ℕ G Gstr → ⊕Fun G Gstr
  ⊕HIT→⊕Fun x = (⊕HIT→Fun x) , (⊕HIT→⊕AlmostNull x)

  ⊕HIT→⊕Fun-pres0 : ⊕HIT→⊕Fun 0⊕HIT ≡ 0⊕Fun
  ⊕HIT→⊕Fun-pres0 = refl

  ⊕HIT→⊕Fun-pres+ : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→⊕Fun (x +⊕HIT y) ≡ ((⊕HIT→⊕Fun x) +⊕Fun (⊕HIT→⊕Fun y))
  ⊕HIT→⊕Fun-pres+ x y = ΣPathTransport→PathΣ _ _ (refl , (squash₁ _ _))


-----------------------------------------------------------------------------
-- Converse sens

  open DefPNF G Gstr

  sumFun : {m : ℕ} → depVec G m → Fun G Gstr
  sumFun {0} ⋆ = 0Fun
  sumFun {suc m} (a □ dv) = (⊕HIT→Fun (base m a)) +Fun (sumFun dv)

  SHIT→SFun : {m : ℕ} → (dv : depVec G m) → ⊕HIT→Fun (sumHIT dv) ≡ sumFun dv
  SHIT→SFun {0} ⋆ = refl
  SHIT→SFun {suc m} (a □ dv) = cong₂ _+Fun_ refl (SHIT→SFun dv)

  sumFun< : {m : ℕ} → (dva : depVec G m) → (i : ℕ) → (m ≤ i) → sumFun dva i ≡ 0g (Gstr i)
  sumFun< {0} ⋆ i r = refl
  sumFun< {suc m} (a □ dva) i r with discreteℕ m i
  ... | yes p = ⊥.rec (<→≢ r p)
  ... | no ¬p = snd (identity (Gstr i) (sumFun dva i)) ∙ sumFun< dva i (≤-trans ≤-sucℕ r)

  sumFunHead : {m : ℕ} → (a b : (G m)) → (dva dvb : depVec G m) →
               (x : sumFun (a □ dva) ≡ sumFun (b □ dvb)) → a ≡ b
  sumFunHead {m} a b dva dvb x =
               a
                        ≡⟨ sym (fst (identity (Gstr m) a)) ⟩
               (Gstr m)._+_ a (0g (Gstr m))
                        ≡⟨ cong₂ (Gstr m ._+_) (sym (fun-trad-eq m a)) (sym (sumFun< dva m ≤-refl)) ⟩
               (Gstr m)._+_ (fun-trad m a m) (sumFun dva m)
                        ≡⟨ funExt⁻ x m ⟩
               (Gstr m)._+_ (fun-trad m b m) (sumFun dvb m)
                        ≡⟨ cong₂ (Gstr m ._+_) (fun-trad-eq m b) (sumFun< dvb m ≤-refl) ⟩
               (Gstr m)._+_ b (0g (Gstr m))
                        ≡⟨ fst (identity (Gstr m) b) ⟩
               b ∎

  substSumFun : {m : ℕ} → (dv : depVec G m) → (n : ℕ) → (p : m ≡ n)
                → subst G p (sumFun dv m) ≡ sumFun dv n
  substSumFun {m} dv n p = J (λ n p → subst G p (sumFun dv m) ≡ sumFun dv n)
                             (transportRefl _)
                             p

  sumFunTail : {m : ℕ} → (a b : (G m)) → (dva dvb : depVec G m) →
             (x : sumFun (a □ dva) ≡ sumFun (b □ dvb)) → (n : ℕ) →
             sumFun dva n ≡ sumFun dvb n
  sumFunTail {m} a b dva dvb x n with discreteℕ m n
  ... | yes p = sumFun dva n                   ≡⟨ sym (substSumFun dva n p) ⟩
                subst G p (sumFun dva m)       ≡⟨ cong (subst G p) (sumFun< dva m ≤-refl) ⟩
                subst G p (0g (Gstr m))        ≡⟨ subst0 p ⟩
                0g (Gstr n)                    ≡⟨ sym (subst0 p) ⟩
                subst G p (0g (Gstr m))        ≡⟨ sym (cong (subst G p) (sumFun< dvb m ≤-refl)) ⟩
                subst G p (sumFun dvb m)       ≡⟨ substSumFun dvb n p ⟩
                sumFun dvb n ∎
  ... | no ¬p = sumFun dva n                                 ≡⟨ sym (snd (identity (Gstr n) _)) ⟩
                (Gstr n)._+_ (0g (Gstr n)) (sumFun dva n)    ≡⟨ cong (λ X → (Gstr n)._+_ X (sumFun dva n))
                                                                             (sym (fun-trad-neq m a n ¬p)) ⟩
                Gstr n ._+_ (fun-trad m a n) (sumFun dva n)  ≡⟨ funExt⁻ x n ⟩
                Gstr n ._+_ (fun-trad m b n) (sumFun dvb n)  ≡⟨ cong (λ X → Gstr n ._+_ X (sumFun dvb n))
                                                                             (fun-trad-neq m b n ¬p) ⟩
                (Gstr n)._+_ (0g (Gstr n)) (sumFun dvb n)    ≡⟨ snd (identity (Gstr n) _) ⟩
                sumFun dvb n ∎

  injDJJ : {m : ℕ} → (dva dvb : depVec G m) → sumFun dva ≡ sumFun dvb → dva ≡ dvb
  injDJJ {0} ⋆ ⋆ x = refl
  injDJJ {suc m} (a □ dva) (b □ dvb) x = depVecPath.decode G (a □ dva) (b □ dvb)
                                         ((sumFunHead a b dva dvb x)
                                         , (injDJJ dva dvb (funExt (sumFunTail a b dva dvb x))))

  injDJ : {m : ℕ} → (a b : depVec G m) → ⊕HIT→Fun (sumHIT a) ≡ ⊕HIT→Fun (sumHIT b) → a ≡ b
  injDJ a b r = injDJJ a b (sym (SHIT→SFun a) ∙ r ∙ SHIT→SFun b)

  inj-⊕HIT→Fun : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→Fun x ≡ ⊕HIT→Fun y → x ≡ y
  inj-⊕HIT→Fun x y r = helper (⊕HIT→PNF2 x y) r
    where
    helper : PNF2 x y → ⊕HIT→Fun x ≡ ⊕HIT→Fun y → x ≡ y
    helper = PT.elim (λ _ → isPropΠ (λ _ → isSet⊕HIT _ _))
                     λ { (m , dva , dvb , p , q) r →
                         p
                         ∙ cong sumHIT (injDJ dva dvb (sym (cong ⊕HIT→Fun p) ∙ r ∙ cong ⊕HIT→Fun q))
                         ∙ sym q}

  inj-⊕HIT→⊕Fun : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→⊕Fun x ≡ ⊕HIT→⊕Fun y → x ≡ y
  inj-⊕HIT→⊕Fun x y p = inj-⊕HIT→Fun x y (fst (PathΣ→ΣPathTransport _ _ p))

  lemProp : (g : ⊕Fun G Gstr) → isProp (Σ[ x ∈ ⊕HIT ℕ G Gstr ] ⊕HIT→⊕Fun x ≡ g )
  lemProp g (x , p) (y , q) = ΣPathTransport→PathΣ _ _
                              ((inj-⊕HIT→⊕Fun x y (p ∙ sym q)) , isSet⊕Fun _ _ _ _)


  --  General traduction for underliyng function
  Strad : (g : (n : ℕ) → G n) → (i : ℕ) → ⊕HIT ℕ G Gstr
  Strad g zero = base 0 (g 0)
  Strad g (suc i) = (base (suc i) (g (suc i))) +⊕HIT (Strad g i)

  Strad-pres+ : (f g : (n : ℕ) → G n) → (i : ℕ) → Strad (f +Fun g) i ≡ Strad f i +⊕HIT Strad g i
  Strad-pres+ f g zero = sym (base-add 0 (f 0) (g 0))
  Strad-pres+ f g (suc i) = cong₂ _+⊕HIT_ (sym (base-add _ _ _))
                                          (Strad-pres+ f g i)
                            ∙ comm-4 (⊕HIT-AbGr ℕ G Gstr) _ _ _ _

  -- Properties in the converse sens
  Strad-max : (f : (n : ℕ) → G n) → (k : ℕ) → (ng : AlmostNullProof G Gstr f k)
              → (i : ℕ) → (r : k ≤ i) → Strad f i ≡ Strad f k
  Strad-max f k ng zero r = sym (cong (Strad f) (≤0→≡0 r))
  Strad-max f k ng (suc i) r with ≤-split r
  ... | inl x = cong₂ _+⊕HIT_
                      (cong (base (suc i)) (ng (suc i) x) ∙ base-neutral (suc i))
                      (Strad-max f k ng i (pred-≤-pred x))
                ∙ +⊕HIT-IdL _
  ... | inr x = cong (Strad f) (sym x)

  -- if m < n then the traduction of sum up to i is 0
  Strad-m<n : (g : (n : ℕ) → G n) → (m : ℕ) → (n : ℕ) → (r : m < n)
            → ⊕HIT→Fun (Strad g m) n ≡ 0g (Gstr n)
  Strad-m<n g zero n r with discreteℕ 0 n
  ... | yes p = ⊥.rec (<→≢ r p)
  ... | no ¬p = refl
  Strad-m<n g (suc m) n r with discreteℕ (suc m) n
  ... | yes p = ⊥.rec (<→≢ r p)
  ... | no ¬p = snd (identity (Gstr n) _) ∙ Strad-m<n g m n (<-trans ≤-refl r)

  {- if n ≤ m, prove ⊕HIT→Fun (∑_{i ∈〚0, m〛} base i (g i)) ≡ g n
     then n is equal to only one〚0, m〛=> induction on m
     case 0 : ok
     case suc m : if n ≡ suc m, then the rest of the sum is 0 by trad-m<n
                  if n ≢ suc m, then it is in the rest of the sum => recursive call -}
  Strad-n≤m : (g : (n : ℕ) → G n) → (m : ℕ) → (n : ℕ) → (r : n ≤ m) → ⊕HIT→Fun (Strad g m) n ≡ g n
  Strad-n≤m g zero n r with discreteℕ 0 n
  ... | yes p = substG g p
  ... | no ¬p = ⊥.rec (¬p (sym (≤0→≡0 r)))
  Strad-n≤m g (suc m) n r with discreteℕ (suc m) n
  ... | yes p = cong₂ ((Gstr n)._+_) (substG g p) (Strad-m<n g m n (0 , p)) ∙ fst (identity (Gstr n) _)
  ... | no ¬p = snd (identity (Gstr n) _) ∙ Strad-n≤m g m n (≤-suc-≢ r λ x → ¬p (sym x))


  ---------------------------------------------------------------------------
  -- Traduction + Morphsim

  -- traduction
  ⊕Fun→⊕HIT+ : (g : ⊕Fun G Gstr) → Σ[ x ∈ ⊕HIT ℕ G Gstr ] ⊕HIT→⊕Fun x ≡ g
  ⊕Fun→⊕HIT+ (g , Ang) = PT.rec (lemProp (g , Ang))
                          (λ { (k , ng)
                               → Strad g k , ΣPathTransport→PathΣ _ _
                                              ((funExt (trad-section g k ng)) , (squash₁ _ _)) })
                          Ang
             where
             trad-section : (g : (n : ℕ) → G n) → (k : ℕ) → (ng : (n : ℕ) → ( k < n) → g n ≡ 0g (Gstr n))
                            → (n : ℕ) → ⊕HIT→Fun (Strad g k) n ≡ g n
             trad-section g k ng n with splitℕ-≤ n k
             ... | inl x = Strad-n≤m g k n x
             ... | inr x = Strad-m<n g k n x ∙ sym (ng n x)


  ⊕Fun→⊕HIT : ⊕Fun G Gstr → ⊕HIT ℕ G Gstr
  ⊕Fun→⊕HIT g = fst (⊕Fun→⊕HIT+ g)

  -- morphism
  ⊕Fun→⊕HIT-pres0 : ⊕Fun→⊕HIT 0⊕Fun ≡ 0⊕HIT
  ⊕Fun→⊕HIT-pres0 = base-neutral 0

  ⊕Fun→⊕HIT-pres+ : (f g : ⊕Fun G Gstr) → ⊕Fun→⊕HIT (f +⊕Fun g) ≡ (⊕Fun→⊕HIT f) +⊕HIT (⊕Fun→⊕HIT g)
  ⊕Fun→⊕HIT-pres+ (f , Anf) (g , Ang) = PT.elim2 (λ x y → isSet⊕HIT (⊕Fun→⊕HIT ((f , x) +⊕Fun (g , y)))
                                                                   ((⊕Fun→⊕HIT (f , x)) +⊕HIT (⊕Fun→⊕HIT (g , y))))
                                                  (λ x y → AN f x g y)
                                                   Anf Ang

    where
    AN : (f : (n : ℕ) → G n) → (x : AlmostNull G Gstr f) → (g : (n : ℕ) → G n) → (y : AlmostNull G Gstr g)
                     → ⊕Fun→⊕HIT ((f , ∣ x ∣₁) +⊕Fun (g , ∣ y ∣₁)) ≡ (⊕Fun→⊕HIT (f , ∣ x ∣₁)) +⊕HIT (⊕Fun→⊕HIT (g , ∣ y ∣₁))
    AN f (k , nf) g (l , ng) = Strad-pres+ f g (k +n l)
                               ∙ cong₂ _+⊕HIT_ (Strad-max f k nf (k +n l) (l , (+-comm l k)))
                                               (Strad-max g l ng (k +n l) (k , refl))


-----------------------------------------------------------------------------
-- Section

  e-sect : (g : ⊕Fun G Gstr) → ⊕HIT→⊕Fun (⊕Fun→⊕HIT g) ≡ g
  e-sect g = snd (⊕Fun→⊕HIT+ g)


-----------------------------------------------------------------------------
-- Retraction

  lemmaSkk : (k : ℕ) → (a : G k) → (i : ℕ) → (r : i < k) → Strad (λ n → fun-trad k a n) i ≡ 0⊕HIT
  lemmaSkk k a zero r with discreteℕ k 0
  ... | yes p = ⊥.rec (<→≢ r (sym p))
  ... | no ¬p = base-neutral 0
  lemmaSkk k a (suc i) r with discreteℕ k (suc i)
  ... | yes p = ⊥.rec (<→≢ r (sym p))
  ... | no ¬p = cong₂ _+⊕HIT_ (base-neutral (suc i)) (lemmaSkk k a i (<-trans ≤-refl r)) ∙ +⊕HIT-IdR _

  lemmakk : (k : ℕ) → (a : G k) → ⊕Fun→⊕HIT (⊕HIT→⊕Fun (base k a)) ≡ base k a
  lemmakk zero a = cong (base 0) (transportRefl a)
  lemmakk (suc k) a with (discreteℕ (suc k) (suc k)) | (discreteℕ k k)
  ... | yes p | yes q = cong₂ _add_
                             (sym (constSubstCommSlice G (⊕HIT ℕ G Gstr) base (cong suc q) a))
                             (lemmaSkk (suc k) a k ≤-refl)
                        ∙ +⊕HIT-IdR _
  ... | yes p | no ¬q = ⊥.rec (¬q refl)
  ... | no ¬p | yes q = ⊥.rec (¬p refl)
  ... | no ¬p | no ¬q = ⊥.rec (¬q refl)


  e-retr : (x : ⊕HIT ℕ G Gstr) → ⊕Fun→⊕HIT (⊕HIT→⊕Fun x) ≡ x
  e-retr = DS-Ind-Prop.f _ _ _ _ (λ _ → isSet⊕HIT _ _)
           (base-neutral 0)
           lemmakk
           λ {U} {V} ind-U ind-V → cong ⊕Fun→⊕HIT (⊕HIT→⊕Fun-pres+ U V)
                                    ∙ ⊕Fun→⊕HIT-pres+ (⊕HIT→⊕Fun U) (⊕HIT→⊕Fun V)
                                    ∙ cong₂ _+⊕HIT_ ind-U ind-V

module _
  (G : ℕ → Type ℓ)
  (Gstr : (n : ℕ) → AbGroupStr (G n))
  where

  open Iso
  open Equiv-Properties G Gstr

  Equiv-DirectSum : AbGroupEquiv (⊕HIT-AbGr ℕ G Gstr) (⊕Fun-AbGr G Gstr)
  fst Equiv-DirectSum = isoToEquiv is
    where
    is : Iso (⊕HIT ℕ G Gstr) (⊕Fun G Gstr)
    fun is = ⊕HIT→⊕Fun
    Iso.inv is = ⊕Fun→⊕HIT
    rightInv is = e-sect
    leftInv is = e-retr
  snd Equiv-DirectSum = makeIsGroupHom ⊕HIT→⊕Fun-pres+
