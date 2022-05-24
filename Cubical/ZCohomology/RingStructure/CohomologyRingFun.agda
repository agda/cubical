{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.RingStructure.CohomologyRingFun where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ≡assoc)

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.NProd
open import Cubical.Algebra.Ring

open import Cubical.Algebra.DirectSum.DirectSumFun.Base
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.AbGroup.Instances.DirectSumFun
open import Cubical.Algebra.AbGroup.Instances.DirectSumHIT
open import Cubical.Algebra.DirectSum.Equiv-DSHIT-DSFun

open import Cubical.HITs.SetTruncation as ST

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.GradedCommutativity
open import Cubical.ZCohomology.RingStructure.CohomologyRing

private variable
  ℓ ℓ' : Level

open Iso


-----------------------------------------------------------------------------
-- Notation

module DefH*Fun where
  H*Fun-AbGr : (A : Type ℓ) → AbGroup ℓ
  H*Fun-AbGr A = ⊕Fun-AbGr (λ n → coHom n A) (λ n → snd (coHomGroup n A))

  H*Fun : (A : Type ℓ) → Type ℓ
  H*Fun A = fst (H*Fun-AbGr A)

module CupH*FunProperties (A : Type ℓ) where
  open DefH*Fun
  open AbGroupStr (snd (H*Fun-AbGr A))
  open AbGroupTheory

  private
    G : (n : ℕ) → Type ℓ
    G = λ n → coHom n A
    Gstr : (n : ℕ) → AbGroupStr (G n)
    Gstr n = snd (coHomGroup n A)


  open AbGroupStr (snd (NProd-AbGroup G Gstr)) using ()
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
    Fun G Gstr = fst (NProd-AbGroup G Gstr)

    +FunIdR : (x : Fun G Gstr) → x +Fun 0Fun ≡ x
    +FunIdR = λ x → fst (+FunIdR×IdL x)

    +FunIdL : (x : Fun G Gstr) → 0Fun +Fun x  ≡ x
    +FunIdL = λ x → snd (+FunIdR×IdL x)

-----------------------------------------------------------------------------
-- Definition of the cup product

  -- Underlying function
  eqSameFiber : {i n : ℕ} → (i ≤ n) → i +' (n ∸ i) ≡ n
  eqSameFiber {zero} {zero} r = refl
  eqSameFiber {zero} {suc n} r = refl
  eqSameFiber {suc i} {zero} r = ⊥.rec (¬-<-zero r)
  eqSameFiber {suc i} {suc n} r = +'≡+ (suc i) (suc n ∸ suc i)
                                  ∙ cong suc (sym (+'≡+ i (n ∸ i)))
                                  ∙ cong suc (eqSameFiber (pred-≤-pred r))

  sumFun : (i n : ℕ) → (i ≤ n) → (f g : (n : ℕ) → coHom n A) → coHom n A
  sumFun zero n r f g = (f 0 ⌣ g n)
  sumFun (suc i) n r f g = subst (λ X → coHom X A) (eqSameFiber r) ((f (suc i)) ⌣ (g (n ∸ (suc i))))
                           +ₕ sumFun i n (≤-trans ≤-sucℕ r) f g

  _cupFun_ : (f g : (n : ℕ) → coHom n A) → (n : ℕ) → coHom n A
  _cupFun_ f g n = sumFun n n ≤-refl f g

  -- Proof that it is an almost null sequence
  -- cupAn : (f g : (n : ℕ) → coHom n A) → AlmostNull G Gstr f → AlmostNull G Gstr g → AlmostNull G Gstr (f cupFun g)
  -- cupAn f g (k , nf) (l , ng) = (k +n l) , λ n r → {!!}
  --   {- proof for sumFun i n ≤-refl f g -> apply on n (for rec call)
  --      i ≤ n & n > k+l
  --      Case analysis :
  --      k     < suc i -> 0 + rec-call
  --      suc i ≤ k     -> n - (suc i) > k+l - k = l -> ok + rec-call
  --   -}


-----------------------------------------------------------------------------
-- Requiered lemma for preserving the cup product

  -- lemma for 0 case
  substCoHom0 : {n m : ℕ} → (p : n ≡ m) → subst (λ X → coHom X A) p (0ₕ n) ≡ 0ₕ m
  substCoHom0 {n} {m} p = J (λ m p → subst (λ X → coHom X A) p (0ₕ n) ≡ 0ₕ m)
                          (transportRefl _) p

  cupFunAnnihilL : (f : (n : ℕ) → coHom n A) → 0Fun cupFun f ≡ 0Fun
  cupFunAnnihilL f = funExt (λ n → sumF0 n n ≤-refl)
    where
    sumF0 : (i n : ℕ) → (r : i ≤ n) → sumFun i n r 0Fun f ≡ 0ₕ n
    sumF0 zero n r = 0ₕ-⌣ _ _ _
    sumF0 (suc i) n r = cong₂ _+ₕ_
                              (cong (subst (λ X → coHom X A) (eqSameFiber r)) (0ₕ-⌣ _ _ _))
                              (sumF0 i n (≤-trans ≤-sucℕ r))
                        ∙ rUnitₕ n _
                        ∙ substCoHom0 (eqSameFiber r)


  cupFunAnnihilR : (f : (n : ℕ) → (G n)) → f cupFun 0Fun ≡ 0Fun
  cupFunAnnihilR f = funExt (λ n → sumF0 n n ≤-refl)
    where
    sumF0 : (i n : ℕ) → (r : i ≤ n) → sumFun i n r f 0Fun ≡ 0ₕ n
    sumF0 zero n r = ⌣-0ₕ _ _ _
    sumF0 (suc i) n r = cong₂ _+ₕ_
                              (cong (subst (λ X → coHom X A) (eqSameFiber r)) (⌣-0ₕ _ _ _))
                              (sumF0 i n (≤-trans ≤-sucℕ r))
                        ∙ rUnitₕ n _
                        ∙ substCoHom0 (eqSameFiber r)


  -- lemma for +
  substCoHom+ : {n m : ℕ} → (p : n ≡ m) → (x y : coHom n A) →
                subst (λ X → coHom X A) p (x +ₕ y) ≡ subst (λ X → coHom X A) p x +ₕ subst (λ X → coHom X A) p y
  substCoHom+ {n} {m} p x y = J (λ m p → subst (λ X → coHom X A) p (x +ₕ y) ≡ subst (λ X → coHom X A) p x +ₕ subst (λ X → coHom X A) p y)
                                (transportRefl _ ∙ sym (cong₂ _+ₕ_ (transportRefl _) (transportRefl _)))
                                p


  cupFunDistR : (f g h : (n : ℕ) → coHom n A) → f cupFun (g +Fun h) ≡ (f cupFun g) +Fun (f cupFun h)
  cupFunDistR f g h = funExt (λ n → sumFAssoc n n ≤-refl)
   where
   sumFAssoc : (i n : ℕ) → (r : i ≤ n) → sumFun i n r f (g +Fun h) ≡ (sumFun i n r f g) +ₕ (sumFun i n r f h)
   sumFAssoc zero n r = leftDistr-⌣ _ _ _ _ _
   sumFAssoc (suc i) n r = cong (λ X → X +ₕ (sumFun i n (≤-trans ≤-sucℕ r) f (g +Fun h)))
                                (cong (subst (λ X → coHom X A) (eqSameFiber r)) (leftDistr-⌣ _ _ _ _ _))
                           ∙ cong₂ _+ₕ_ (substCoHom+ (eqSameFiber r) _ _) (sumFAssoc i n (≤-trans ≤-sucℕ r))
                           ∙ comm-4 (coHomGroup n A) _ _ _ _

  cupFunDistL : (f g h : (n : ℕ) → coHom n A) → (f +Fun g) cupFun h ≡ (f cupFun h) +Fun (g cupFun h)
  cupFunDistL f g h = funExt (λ n → sumFAssoc n n ≤-refl)
   where
   sumFAssoc : (i n : ℕ) → (r : i ≤ n) → sumFun i n r (f +Fun g) h ≡ (sumFun i n r f h) +ₕ (sumFun i n r g h)
   sumFAssoc zero n r = rightDistr-⌣ _ _ _ _ _
   sumFAssoc (suc i) n r = cong (λ X → X +ₕ (sumFun i n (≤-trans ≤-sucℕ r) (f +Fun g) h))
                                (cong (subst (λ X → coHom X A) (eqSameFiber r)) (rightDistr-⌣ _ _ _ _ _))
                           ∙ cong₂ _+ₕ_ (substCoHom+ (eqSameFiber r) _ _) (sumFAssoc i n (≤-trans ≤-sucℕ r))
                           ∙ comm-4 (coHomGroup n A) _ _ _ _

  -- lemma for the base case
  open Equiv-Properties G Gstr using
    ( subst0
    ; subst+
    ; substG
    ; fun-trad
    ; fun-trad-eq
    ; fun-trad-neq
    ; ⊕HIT→Fun    )


  sumFun≠ : (k : ℕ) → (a : coHom k A) → (l : ℕ) →  (b : coHom l A) →
            (i n : ℕ) → (r : i ≤ n) → (¬pp : k +' l ≡ n → ⊥) →
            sumFun i n r (fun-trad k a) (fun-trad l b) ≡ 0ₕ n
  sumFun≠ k a l b zero n r ¬pp with discreteℕ k 0 | discreteℕ l n
  ... | yes p | yes q = ⊥.rec (¬pp (cong₂ _+'_ p q))
  ... | yes p | no ¬q = ⌣-0ₕ 0 n (subst G p a)
  ... | no ¬p | yes q = 0ₕ-⌣ 0 n (subst G q b)
  ... | no ¬p | no ¬q = 0ₕ-⌣ 0 n (0ₕ n)
  sumFun≠ k a l b (suc i) n r ¬pp with discreteℕ k (suc i) | discreteℕ l (n ∸ (suc i))
  ... | yes p | yes q = ⊥.rec (¬pp (cong₂ _+'_ p q ∙ eqSameFiber r))
  ... | yes p | no ¬q = cong₂ _+ₕ_
                              (cong (subst (λ X → coHom X A) (eqSameFiber r)) (⌣-0ₕ (suc i) (n ∸ suc i) _))
                              (sumFun≠ k a l b i n (≤-trans ≤-sucℕ r) ¬pp)
                        ∙ rUnitₕ n _
                        ∙ substCoHom0 _
  ... | no ¬p | yes q = cong₂ _+ₕ_
                              (cong (subst (λ X → coHom X A) (eqSameFiber r)) (0ₕ-⌣ (suc i) (n ∸ suc i) _))
                              (sumFun≠ k a l b i n (≤-trans ≤-sucℕ r) ¬pp)
                        ∙ rUnitₕ n _
                        ∙ substCoHom0 _
  ... | no ¬p | no ¬q = cong₂ _+ₕ_
                              (cong (subst (λ X → coHom X A) (eqSameFiber r)) (0ₕ-⌣ (suc i) (n ∸ suc i) (0ₕ (n ∸ suc i))))
                              (sumFun≠ k a l b i n (≤-trans ≤-sucℕ r) ¬pp)
                        ∙ rUnitₕ n _
                        ∙ substCoHom0 _

  sumFun< : (k : ℕ) → (a : coHom k A) → (l : ℕ) →  (b : coHom l A) →
            (i n : ℕ) → (r : i ≤ n) → (i < k) →
            sumFun i n r (fun-trad k a) (fun-trad l b) ≡ 0ₕ n
  sumFun< k a l b zero n r pp with discreteℕ k 0
  ... | yes p = ⊥.rec (<→≢ pp (sym p))
  ... | no ¬p = 0ₕ-⌣ 0 n _
  sumFun< k a l b (suc i) n r pp with discreteℕ k (suc i)
  ... | yes p = ⊥.rec (<→≢ pp (sym p))
  ... | no ¬p = cong₂ _+ₕ_
                      (cong (subst (λ X → coHom X A) (eqSameFiber r)) (0ₕ-⌣ (suc i) (n ∸ suc i) _))
                      (sumFun< k a l b i n (≤-trans ≤-sucℕ r) (<-trans ≤-refl pp))
                ∙ rUnitₕ n _
                ∙ substCoHom0 _

  substCoHom⌣ : {m n k l : ℕ} → (p : m ≡ n) → (q : k ≡ l) → (r : m +' k ≡ n +' l) →
                (a : coHom m A) → (b : coHom k A) →
                subst G p a ⌣ subst G q b ≡ subst G r (a ⌣ b)
  substCoHom⌣ p q r a b = J (λ n p → subst G p a ⌣ subst G q b ≡ subst G (cong₂ _+'_ p q) (a ⌣ b))
                            (J (λ l q → subst G refl a ⌣ subst G q b ≡ subst G (cong₂ _+'_ refl q) (a ⌣ b))
                               (cong₂ _⌣_ (transportRefl _) (transportRefl _)
                                ∙ sym (transportRefl _))
                               q)
                             p
                           ∙ cong (λ X → subst (λ X → coHom X A) X (a ⌣ b)) (isSetℕ _ _ _ _)

  sumFun≤ : (k : ℕ) → (a : coHom k A) → (l : ℕ) →  (b : coHom l A) →
            (i n : ℕ) → (r : i ≤ n) → (pp : k +' l ≡ n) → (k ≤ i) →
            sumFun i n r (fun-trad k a) (fun-trad l b) ≡ subst G pp (a ⌣ b)
  sumFun≤ k a l b zero n r pp rr with discreteℕ k 0 | discreteℕ l n
  ... | yes p | yes q = substCoHom⌣ p q pp a b
  ... | yes p | no ¬q = ⊥.rec (¬q (cong (λ X → X +' l) (sym p) ∙ pp))
  ... | no ¬p | yes q = ⊥.rec (¬p (≤0→≡0 rr))
  ... | no ¬p | no ¬q = ⊥.rec (¬p (≤0→≡0 rr))
  sumFun≤ k a l b (suc i) n r pp rr with discreteℕ k (suc i) | discreteℕ l (n ∸ suc i)
  ... | yes p | yes q = cong₂ _+ₕ_
                              (cong (subst (λ X → coHom X A) (eqSameFiber r)) (substCoHom⌣ p q (pp ∙ sym (eqSameFiber r)) a b))
                              (sumFun< k a l b i n (≤-trans ≤-sucℕ r) (0 , (sym p)))
                        ∙ rUnitₕ n _
                        ∙ sym (substComposite G (pp ∙ sym (eqSameFiber r)) (eqSameFiber r) (a ⌣ b))
                          -- more elegant than isSetℕ _ _ _ _
                        ∙ cong (λ X → subst G X (a ⌣ b))
                               (sym (≡assoc _ _ _)
                               ∙ cong (λ X → pp ∙ X) (lCancel (eqSameFiber r))
                               ∙ sym (rUnit pp) )
  ... | yes p | no ¬q = ⊥.rec (¬q (inj-m+ (sym (+'≡+ (suc i) l)
                                          ∙ cong (λ X → X +' l) (sym p)
                                          ∙ pp
                                          ∙ sym (eqSameFiber r)
                                          ∙ +'≡+ (suc i) (n ∸ suc i))))
  ... | no ¬p | yes q = ⊥.rec (¬p (inj-+m (sym (+'≡+ k (n ∸ suc i))
                                            ∙ cong (λ X → k +' X) (sym q)
                                            ∙ pp
                                            ∙ sym (eqSameFiber r)
                                            ∙ +'≡+ (suc i) (n ∸ suc i))))
  ... | no ¬p | no ¬q = cong₂ _+ₕ_
                              (cong (λ X → subst (λ X → coHom X A) (eqSameFiber r) X) (0ₕ-⌣ _ _ (0ₕ (n ∸ suc i))))
                              (sumFun≤ k a l b i n (≤-trans ≤-sucℕ r) pp (≤-suc-≢ rr ¬p))
                        ∙ cong (λ X → X +ₕ subst G pp (a ⌣ b)) (substCoHom0 (eqSameFiber r))
                        ∙ lUnitₕ n _


  sumFBase : (k : ℕ) → (a : coHom k A) → (l : ℕ) →  (b : coHom l A) → (n : ℕ) →
             fun-trad (k +' l) (a ⌣ b) n ≡ sumFun n n ≤-refl (fun-trad k a) (fun-trad l b)
  sumFBase k a l b n with discreteℕ (k +' l) n
  ... | yes p = sym (sumFun≤ k a l b n n ≤-refl p (l , (+-comm l k ∙ sym (+'≡+ k l) ∙ p)))
  ... | no ¬p = sym (sumFun≠ k a l b n n ≤-refl ¬p)


  -----------------------------------------------------------------------------
  -- Proof that ⊕HIT→⊕Fun preserve the cup product

  open CupRingProperties A

  open AbGroupStr (snd (⊕HIT-AbGr ℕ G Gstr)) using ()
      renaming
    ( 0g       to 0⊕HIT
    ; _+_      to _+⊕HIT_
    ; -_       to -⊕HIT_
    ; assoc    to +⊕HITAssoc
    ; identity to +⊕HITIdR×IdL
    ; inverse  to +⊕HITInvR×InvL
    ; comm     to +⊕HITComm
    ; is-set   to isSet⊕HIT)

  private
    +⊕HITIdR : (x : ⊕HIT ℕ G Gstr) → x +⊕HIT 0⊕HIT ≡ x
    +⊕HITIdR = λ x → fst (+⊕HITIdR×IdL x)

    +⊕HITIdL : (x : ⊕HIT ℕ G Gstr) → 0⊕HIT +⊕HIT x  ≡ x
    +⊕HITIdL = λ x → snd (+⊕HITIdR×IdL x)

  ⊕HIT→Fun-pres⌣ : (x y : H* A) → ⊕HIT→Fun (x cup y) ≡ ((⊕HIT→Fun x) cupFun (⊕HIT→Fun y))
  ⊕HIT→Fun-pres⌣ = DS-Ind-Prop.f _ _ _ _
                    (λ x → isPropΠ (λ _ → isSetFun _ _))
                    (λ y → sym (cupFunAnnihilL (⊕HIT→Fun y)))
                    (λ k a → DS-Ind-Prop.f _ _ _ _ (λ _ → isSetFun _ _)
                              (sym (cupFunAnnihilR (⊕HIT→Fun (base k a))))
                              (λ l b → funExt (λ n → sumFBase k a l b n))
                              λ {U V} ind-U ind-V → cong₂ _+Fun_ ind-U ind-V
                                                     ∙ sym (cupFunDistR _ _ _))
                    λ {U} {V} ind-U ind-V y → cong₂ _+Fun_ (ind-U y) (ind-V y)
                                               ∙ sym (cupFunDistL _ _ _)
