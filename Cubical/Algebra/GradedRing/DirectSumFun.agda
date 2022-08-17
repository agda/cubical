{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.GradedRing.DirectSumFun where

{-
   This file give a graded ring construction in the case of the fun direct sum.
   Because of the current proofs this is done only in the case where
   - Idx is ℕ and for a monoid on it
   - For the usual ∸ of the Nat library

   The proof consists in :
   - Defining a _prod_ operation on the structure
   - Proving the underlying equivalence respect it
   - Transporting the proof of RingStr
   - Deducing an equivalence proof
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _∸_ to _-ℕ_ )
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.DirectSum.Equiv-DSHIT-DSFun
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.DirectSum.DirectSumHIT.Properties
open import Cubical.Algebra.DirectSum.DirectSumFun.Base
open import Cubical.Algebra.AbGroup.Instances.NProd
open import Cubical.Algebra.AbGroup.Instances.DirectSumFun
open import Cubical.Algebra.Ring
open import Cubical.Algebra.GradedRing.Base
open import Cubical.Algebra.GradedRing.DirectSumHIT
open import Cubical.Algebra.CommRing

open import Cubical.HITs.PropositionalTruncation as PT

private variable
  ℓ ℓ' : Level

open AbGroupStr
open AbGroupTheory

-----------------------------------------------------------------------------
-- Def, notation, lemma

module _

  -- monoid
  (_+n_ : ℕ → ℕ → ℕ) -- need to instantiate on +'
  (isM : IsMonoid 0 _+n_)
  (_+≡_ : (n m : ℕ) →  n +n m ≡ n +ℕ m) -- needed for the behaviour under -ℕ
  --
  (G : ℕ → Type ℓ)
  (Gstr : (n : ℕ) → AbGroupStr (G n))
  where

  sameFiber+ : {i n : ℕ} → i ≤ n → i +ℕ (n -ℕ i) ≡ n
  sameFiber+ {zero} {zero} p = refl
  sameFiber+ {zero} {suc n} p = refl
  sameFiber+ {suc i} {zero} p = ⊥.rec (¬-<-zero p)
  sameFiber+ {suc i} {suc n} p = cong suc (sameFiber+ (pred-≤-pred p))

  sameFiber : {i n : ℕ} → (i ≤ n) → i +n (n -ℕ i) ≡ n
  sameFiber {i} {n} p = (i +≡ (n -ℕ i)) ∙ sameFiber+ p

  open SubstLemma ℕ G Gstr
  open IsMonoid isM using ()
    renaming
    ( ·Assoc to +nAssoc
    ; ·IdR   to +nIdR
    ; ·IdL   to +nIdL   )

  open AbGroupStr (snd (NProd-AbGroup G Gstr)) using ()
    renaming
    ( 0g     to 0Fun
    ; _+_    to _+Fun_
    ; is-set to isSetFun )

  module _
    (1⋆      : G 0)
    (_⋆_     : {k l : ℕ} → G k → G l → G (k +n l))
    (0-⋆     : {k l : ℕ} → (b : G l) → (0g (Gstr k)) ⋆ b ≡ 0g (Gstr (k +n l)))
    (⋆-0     : {k l : ℕ} → (a : G k) → a ⋆ (0g (Gstr l)) ≡ 0g (Gstr (k +n l)))
    (⋆Assoc  : {k l m : ℕ} → (a : G k) → (b : G l) → (c : G m) →
                _≡_ {A = Σ[ k ∈ ℕ ] G k} ((k +n (l +n m)) , (a ⋆ (b ⋆ c))) (((k +n l) +n m) , ((a ⋆ b) ⋆ c)))
    (⋆IdR    : {k : ℕ} → (a : G k) → _≡_ {A = Σ[ k ∈ ℕ ] G k} ( k +n 0 , a ⋆ 1⋆ ) (k , a))
    (⋆IdL    : {l : ℕ} → (b : G l) → _≡_ {A = Σ[ k ∈ ℕ ] G k} ( 0 +n l , 1⋆ ⋆ b ) (l , b))
    (⋆DistR+ : {k l : ℕ} → (a : G k) → (b c : G l) →
               a ⋆ ((Gstr l) ._+_ b c) ≡ Gstr (k +n l) ._+_ (a ⋆ b) (a ⋆ c))
    (⋆DistL+ : {k l : ℕ} → (a b : G k) → (c : G l) →
               ((Gstr k) ._+_ a b) ⋆ c ≡ Gstr (k +n l) ._+_ (a ⋆ c) (b ⋆ c))
    where

-----------------------------------------------------------------------------
-- Definition of 1

    -- import for pres
    open Equiv-Properties G Gstr using
      ( fun-trad
      ; fun-trad-eq
      ; fun-trad-neq
      ; ⊕HIT→Fun
      ; ⊕HIT→⊕Fun
      ; ⊕HIT→⊕Fun-pres+)

    1Fun : (n : ℕ) → G n
    1Fun zero = 1⋆
    1Fun (suc n) = 0g (Gstr (suc n))

    1⊕Fun : ⊕Fun G Gstr
    1⊕Fun = 1Fun , ∣ 0 , helper ∣₁
      where
      helper : AlmostNullProof G Gstr 1Fun 0
      helper zero r = ⊥.rec (¬-<-zero r)
      helper (suc n) r = refl

    ⊕HIT→Fun-pres1 : (n : ℕ) → ⊕HIT→Fun (base 0 1⋆) n ≡ 1Fun n
    ⊕HIT→Fun-pres1 zero with discreteℕ 0 0
    ... | yes p = cong (λ X → subst G X 1⋆) (isSetℕ _ _ _ _) ∙ transportRefl _
    ... | no ¬p = ⊥.rec (¬p refl)
    ⊕HIT→Fun-pres1 (suc n) with discreteℕ (suc n) 0
    ... | yes p = ⊥.rec (snotz p)
    ... | no ¬p = refl

    ⊕HIT→⊕Fun-pres1 : ⊕HIT→⊕Fun (base 0 1⋆) ≡ 1⊕Fun
    ⊕HIT→⊕Fun-pres1 = ΣPathTransport→PathΣ _ _
                       ((funExt (λ n → ⊕HIT→Fun-pres1 n)) , (squash₁ _ _))

-----------------------------------------------------------------------------
-- Definition of the ring product

    sumFun : (i n : ℕ) → (i ≤ n) → (f g : (n : ℕ) → G n) → G n
    sumFun zero n r f g = subst G (sameFiber r) ((f 0) ⋆ (g (n -ℕ 0)))
    sumFun (ℕ.suc i) n r f g = Gstr n ._+_ (subst G (sameFiber r) ((f (suc i)) ⋆ (g (n -ℕ suc i))))
                                            (sumFun i n (≤-trans ≤-sucℕ r) f g)

    _prodFun_ : (f g : (n : ℕ) → G n) → (n : ℕ) → G n
    _prodFun_ f g n = sumFun n n ≤-refl f g

    -- Proof that it is an almost null sequence
    prodAn : (f g : (n : ℕ) → G n) → AlmostNull G Gstr f → AlmostNull G Gstr g → AlmostNull G Gstr (f prodFun g)
    prodAn f g (k , nf) (l , ng) = (k +ℕ l) , λ n pp → sumF0 n n pp ≤-refl
      where
      sumF0 : (i n : ℕ) → (pp : k +ℕ l < n) → (r : i ≤ n) → sumFun i n r f g ≡ 0g (Gstr n)
      sumF0 zero n pp r = cong (subst G (sameFiber r))
                               (cong (λ X → f 0 ⋆ X) (ng (n -ℕ zero) (<-k+-trans pp)) ∙ ⋆-0 _) ∙ substG0 _
      sumF0 (suc i) n pp r with splitℕ-≤ (suc i) k
      ... | inl x = cong₂ (Gstr n ._+_)
                        (cong (subst G (sameFiber r))
                              (cong (λ X → f (suc i) ⋆ X) (ng (n -ℕ suc i)
                                    -- Goal  : l < n - suc i
                                    -- Proof : l = k + l - k < n - k < n - suc i
                                    (subst (λ X → X < n -ℕ suc i) (∸+ l k)
                                            (≤<-trans (≤-∸-≥ (k +ℕ l) (suc i) k x)
                                            (<-∸-< (k +ℕ l) n (suc i) pp (≤<-trans x (<-+k-trans pp))))))
                              ∙ ⋆-0 (f (suc i))))
                        (sumF0 i n pp (≤-trans ≤-sucℕ r))
                  ∙ +IdR (Gstr n) _
                  ∙ substG0 _

      ... | inr x = cong₂ (Gstr n ._+_)
                          (cong (subst G (sameFiber r))
                                (cong (λ X → X ⋆ g (n -ℕ (suc i))) (nf (suc i) x)
                                ∙ 0-⋆ _))
                          (sumF0 i n pp (≤-trans ≤-sucℕ r))
                    ∙ +IdR (Gstr n) _
                    ∙ substG0 _

    _prodF_ : ⊕Fun G Gstr → ⊕Fun G Gstr → ⊕Fun G Gstr
    _prodF_(f , Anf) (g , Ang) = (f prodFun g) , helper Anf Ang
      where
      helper :  AlmostNullP G Gstr f →  AlmostNullP G Gstr g →  AlmostNullP G Gstr (f prodFun g)
      helper = PT.rec2 squash₁ (λ x y → ∣ (prodAn f g x y) ∣₁)


-----------------------------------------------------------------------------
-- Some Ring properties that are needed

    -- lemma for 0 case
    prodFunAnnihilL : (f : (n : ℕ) → G n) → 0Fun prodFun f ≡ 0Fun
    prodFunAnnihilL f = funExt (λ n → sumF0 n n ≤-refl)
      where
      sumF0 : (i n : ℕ) → (r : i ≤ n) → sumFun i n r 0Fun f ≡ 0g (Gstr n)
      sumF0 zero n r = cong (subst G (sameFiber r)) (0-⋆ _) ∙ substG0 _
      sumF0 (suc i) n r = cong₂ (Gstr n ._+_)
                                (cong (subst G (sameFiber r)) (0-⋆ _))
                                (sumF0 i n (≤-trans ≤-sucℕ r))
                          ∙ +IdR (Gstr n) _
                          ∙ substG0 _


    prodFunAnnihilR : (f : (n : ℕ) → (G n)) → f prodFun 0Fun ≡ 0Fun
    prodFunAnnihilR f = funExt (λ n → sumF0 n n ≤-refl)
      where
      sumF0 : (i n : ℕ) → (r : i ≤ n) → sumFun i n r f 0Fun ≡ 0g (Gstr n)
      sumF0 zero n r = cong (subst G (sameFiber r)) (⋆-0 _) ∙ substG0 _
      sumF0 (suc i) n r = cong₂ (Gstr n ._+_)
                                (cong (subst G (sameFiber r)) (⋆-0 _))
                                (sumF0 i n (≤-trans ≤-sucℕ r))
                          ∙ +IdR (Gstr n) _
                          ∙ substG0 _

    prodFunDistR : (f g h : (n : ℕ) → G n) → f prodFun (g +Fun h) ≡ (f prodFun g) +Fun (f prodFun h)
    prodFunDistR f g h = funExt (λ n → sumFAssoc n n ≤-refl)
     where
     sumFAssoc : (i n : ℕ) → (r : i ≤ n) → sumFun i n r f (g +Fun h) ≡ (Gstr n) ._+_ (sumFun i n r f g) (sumFun i n r f h)
     sumFAssoc zero n r = cong (subst G (sameFiber r)) (⋆DistR+ _ _ _)
                          ∙ sym (substG+ _ _ _)
     sumFAssoc (suc i) n r = cong₂ (Gstr n ._+_)
                                   (cong (subst G (sameFiber r)) (⋆DistR+ _ _ _) ∙ sym (substG+ _ _ _))
                                   (sumFAssoc i n (≤-trans ≤-sucℕ r))
                             ∙ comm-4 ((G n) , (Gstr n)) _ _ _ _

    prodFunDistL : (f g h : (n : ℕ) → G n) → (f +Fun g) prodFun h ≡ (f prodFun h) +Fun (g prodFun h)
    prodFunDistL f g h = funExt (λ n → sumFAssoc n n ≤-refl)
     where
     sumFAssoc : (i n : ℕ) → (r : i ≤ n) → sumFun i n r (f +Fun g) h ≡ (Gstr n) ._+_ (sumFun i n r f h) (sumFun i n r g h)
     sumFAssoc zero n r = cong (subst G (sameFiber r)) (⋆DistL+ _ _ _)
                          ∙ sym (substG+ _ _ _)
     sumFAssoc (suc i) n r = cong₂ (Gstr n ._+_)
                                   (cong (subst G (sameFiber r)) (⋆DistL+ _ _ _) ∙ sym (substG+ _ _ _))
                                   (sumFAssoc i n (≤-trans ≤-sucℕ r))
                             ∙ comm-4 ((G n) , (Gstr n)) _ _ _ _


-----------------------------------------------------------------------------
-- Preserving the product

   -- A substitution lemma
    subst⋆ : {m n k l : ℕ} → (p : m ≡ n) → (q : k ≡ l) → (r : m +n k ≡ n +n l) →
                  (a : G m) → (b : G k) → subst G p a ⋆ subst G q b ≡ subst G r (a ⋆ b)
    subst⋆ p q r a b = J (λ n p → subst G p a ⋆ subst G q b ≡ subst G (cong₂ _+n_ p q) (a ⋆ b))
                              (J (λ l q → subst G refl a ⋆ subst G q b ≡ subst G (cong₂ _+n_ refl q) (a ⋆ b))
                                 (cong₂ _⋆_ (transportRefl _) (transportRefl _) ∙ sym (transportRefl _))
                                 q)
                               p
                             ∙ cong (λ X → subst G X (a ⋆ b)) (isSetℕ _ _ _ _)

    -- Proving the base case
    open GradedRing-⊕HIT-index (ℕ , (monoidstr 0 _+n_ isM)) G Gstr
    open GradedRing-⊕HIT-⋆ 1⋆ _⋆_ 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+

    sumFun≠ : (k : ℕ) → (a : G k) → (l : ℕ) →  (b : G l) →
              (i n : ℕ) → (r : i ≤ n) → (¬pp : k +n l ≡ n → ⊥) →
              sumFun i n r (fun-trad k a) (fun-trad l b) ≡ 0g (Gstr n)
    sumFun≠ k a l b zero n r ¬pp with discreteℕ k 0 | discreteℕ l n
    ... | yes p | yes q = ⊥.rec (¬pp ((k +≡ l) ∙ cong₂ _+ℕ_ p q) )
    ... | yes p | no ¬q = cong (subst G (sameFiber r)) (⋆-0 _) ∙ substG0 _
    ... | no ¬p | yes q = cong (subst G (sameFiber r)) (0-⋆ _) ∙ substG0 _
    ... | no ¬p | no ¬q = cong (subst G (sameFiber r)) (0-⋆ _) ∙ substG0 _
    sumFun≠ k a l b (suc i) n r ¬pp with discreteℕ k (suc i) | discreteℕ l (n -ℕ (suc i))
    ... | yes p | yes q = ⊥.rec (¬pp (cong₂ _+n_ p q ∙ sameFiber r))
    ... | yes p | no ¬q = cong₂ (Gstr n ._+_)
                                (cong (subst G (sameFiber r)) (⋆-0 _))
                                (sumFun≠ k a l b i n (≤-trans ≤-sucℕ r) ¬pp)
                          ∙ +IdR (Gstr n) _
                          ∙ substG0 _
    ... | no ¬p | yes q = cong₂ (Gstr n ._+_)
                                (cong (subst G (sameFiber r)) (0-⋆ _))
                                (sumFun≠ k a l b i n (≤-trans ≤-sucℕ r) ¬pp)
                          ∙ +IdR (Gstr n) _
                          ∙ substG0 _
    ... | no ¬p | no ¬q = cong₂ (Gstr n ._+_)
                                (cong (subst G (sameFiber r)) (0-⋆ _))
                                (sumFun≠ k a l b i n (≤-trans ≤-sucℕ r) ¬pp)
                          ∙ +IdR (Gstr n) _
                          ∙ substG0 _


    -- If k +n l ≡ n then, we unwrap the sum until we reach k.
    -- Before it is 0, in k the value, then it is 0
    sumFun< : (k : ℕ) → (a : G k) → (l : ℕ) →  (b : G l) →
              (i n : ℕ) → (r : i ≤ n) → (i < k) →
              sumFun i n r (fun-trad k a) (fun-trad l b) ≡ 0g (Gstr n)
    sumFun< k a l b zero n r pp with discreteℕ k 0
    ... | yes p = ⊥.rec (<→≢ pp (sym p))
    ... | no ¬p = cong (subst G (sameFiber r)) (0-⋆ _) ∙ substG0 _
    sumFun< k a l b (suc i) n r pp with discreteℕ k (suc i)
    ... | yes p = ⊥.rec (<→≢ pp (sym p))
    ... | no ¬p = cong₂ (Gstr n ._+_)
                        (cong (subst G (sameFiber r)) (0-⋆ _))
                        (sumFun< k a l b i n (≤-trans ≤-sucℕ r) (<-trans ≤-refl pp))
                  ∙ +IdR (Gstr n) _
                  ∙ substG0 _

    sumFun≤ : (k : ℕ) → (a : G k) → (l : ℕ) →  (b : G l ) →
              (i n : ℕ) → (r : i ≤ n) → (pp : k +n l ≡ n) → (k ≤ i) →
              sumFun i n r (fun-trad k a) (fun-trad l b) ≡ subst G pp (a ⋆ b)
    sumFun≤ k a l b zero n r pp rr with discreteℕ k 0 | discreteℕ l n
    ... | yes p | yes q = cong (subst G (sameFiber r)) (subst⋆ p q (pp ∙ sym (+nIdL _)) a b)
                          ∙ sym (substComposite G _ _ _)
                          ∙ cong (λ X → subst G X (a ⋆ b)) (isSetℕ _ _ _ _)
    ... | yes p | no ¬q = ⊥.rec (¬q (sym (+nIdL l) ∙ cong (λ X → X +n l) (sym p) ∙ pp))
    ... | no ¬p | yes q = ⊥.rec (¬p (≤0→≡0 rr))
    ... | no ¬p | no ¬q = ⊥.rec (¬p (≤0→≡0 rr))
    sumFun≤ k a l b (suc i) n r pp rr with discreteℕ k (suc i) | discreteℕ l (n -ℕ suc i)
    ... | yes p | yes q = cong₂ (Gstr n ._+_)
                                (cong (subst G (sameFiber r))
                                      (subst⋆ p q (pp ∙ sym (sameFiber r)) a b)
                                      ∙ sym (substComposite G _ _ _))
                                (sumFun< k a l b i n (≤-trans ≤-sucℕ r) (0 , (sym p)))
                          ∙ +IdR (Gstr n) _
                          ∙ cong (λ X → subst G X (a ⋆ b)) (isSetℕ _ _ _ _)
    ... | yes p | no ¬q = ⊥.rec (¬q (inj-m+ (sym ((suc i) +≡ l)
                                            ∙ cong (λ X → X +n l) (sym p)
                                            ∙ pp
                                            ∙ sym (sameFiber r)
                                            ∙ ((suc i) +≡ (n -ℕ suc i)))))
    ... | no ¬p | yes q = ⊥.rec (¬p (inj-+m (sym (k +≡ (n -ℕ suc i))
                                              ∙ cong (λ X → k +n X) (sym q)
                                              ∙ pp
                                              ∙ sym (sameFiber r)
                                              ∙ ((suc i) +≡ (n -ℕ suc i)))))
    ... | no ¬p | no ¬q = cong₂ (Gstr n ._+_)
                                (cong (subst G (sameFiber r)) (0-⋆ _) ∙ substG0 _)
                                (sumFun≤ k a l b i n (≤-trans ≤-sucℕ r) pp (≤-suc-≢ rr ¬p))
                          ∙ +IdL (Gstr n) _


     -- If k +n l ≢ n, then it is both zero
     -- Otherwise, it coincide in (k,l)
    sumFBase : (k : ℕ) → (a : G k) → (l : ℕ) →  (b : G l) → (n : ℕ) →
               fun-trad (k +n l) (a ⋆ b) n ≡ sumFun n n ≤-refl (fun-trad k a) (fun-trad l b)
    sumFBase k a l b n with discreteℕ (k +n l) n
    ... | yes p = sym (sumFun≤ k a l b n n ≤-refl p (l , (+-comm l k ∙ sym (k +≡ l) ∙ p)))
    ... | no ¬p = sym (sumFun≠ k a l b n n ≤-refl ¬p)


    -- Proof that ⊕HIT→⊕Fun preserve the cup product
    ⊕HIT→Fun-pres-prodFun : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→Fun (x prod y) ≡ ((⊕HIT→Fun x) prodFun (⊕HIT→Fun y))
    ⊕HIT→Fun-pres-prodFun = DS-Ind-Prop.f _ _ _ _
                         (λ x → isPropΠ (λ _ → isSetFun _ _))
                         (λ y → sym (prodFunAnnihilL (⊕HIT→Fun y)))
                         (λ k a → DS-Ind-Prop.f _ _ _ _ (λ _ → isSetFun _ _)
                                   (sym (prodFunAnnihilR (⊕HIT→Fun (base k a))))
                                   (λ l b → funExt λ n → sumFBase k a l b n)
                                   λ {U V} ind-U ind-V → cong₂ _+Fun_ ind-U ind-V
                                                          ∙ sym (prodFunDistR _ _ _))
                         λ {U} {V} ind-U ind-V y → cong₂ _+Fun_ (ind-U y) (ind-V y)
                                                    ∙ sym (prodFunDistL _ _ _)


    ⊕HIT→⊕Fun-pres-prodF : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→⊕Fun (x prod y) ≡ ((⊕HIT→⊕Fun x) prodF (⊕HIT→⊕Fun y))
    ⊕HIT→⊕Fun-pres-prodF x y = ΣPathTransport→PathΣ _ _
                                ((⊕HIT→Fun-pres-prodFun x y) , (squash₁ _ _))


-----------------------------------------------------------------------------
-- Graded Ring Structure

    open AbGroupStr (snd (⊕Fun-AbGr G Gstr)) using ()
        renaming
      ( 0g       to 0⊕Fun
      ; _+_      to _+⊕Fun_
      ; -_       to -⊕Fun_
      ; is-set   to isSet⊕Fun)

    open IsGroupHom

    ⊕FunGradedRing-Ring : Ring ℓ
    ⊕FunGradedRing-Ring = InducedRing ⊕HITgradedRing-Ring
                                      0⊕Fun 1⊕Fun _+⊕Fun_ _prodF_ -⊕Fun_
                                      (fst (Equiv-DirectSum G Gstr))
                                      (pres1 (snd (Equiv-DirectSum G Gstr)))
                                      ⊕HIT→⊕Fun-pres1
                                      (pres· (snd (Equiv-DirectSum G Gstr)))
                                      ⊕HIT→⊕Fun-pres-prodF
                                      (presinv (snd (Equiv-DirectSum G Gstr)))

    RingEquiv-DirectSumGradedRing : RingEquiv ⊕HITgradedRing-Ring ⊕FunGradedRing-Ring
    RingEquiv-DirectSumGradedRing = InducedRingEquiv ⊕HITgradedRing-Ring
                                      0⊕Fun 1⊕Fun _+⊕Fun_ _prodF_ -⊕Fun_
                                      (fst (Equiv-DirectSum G Gstr))
                                      (pres1 (snd (Equiv-DirectSum G Gstr)))
                                      ⊕HIT→⊕Fun-pres1
                                      (pres· (snd (Equiv-DirectSum G Gstr)))
                                      ⊕HIT→⊕Fun-pres-prodF
                                      (presinv (snd (Equiv-DirectSum G Gstr)))

    ⊕Fun-GradedRing : GradedRing ℓ-zero ℓ
    ⊕Fun-GradedRing = makeGradedRing
                      ⊕FunGradedRing-Ring
                      (ℕ , (monoidstr 0 _+n_ isM))
                      G Gstr
                      1⋆ _⋆_
                      0-⋆ ⋆-0
                      ⋆Assoc ⋆IdR ⋆IdL
                      ⋆DistR+ ⋆DistL+
                      (RingEquivs.invRingEquiv RingEquiv-DirectSumGradedRing)


-----------------------------------------------------------------------------
-- CommRing extension

    module _
      (⋆Comm : {k l : ℕ} → (a : G k) → (b : G l) →
               _≡_ {A = Σ[ k ∈ ℕ ] G k} ((k +n l) , (a ⋆ b)) ((l +n k) , (b ⋆ a)))
      where

      open ExtensionCommRing ⋆Comm

      ⊕FunGradedRing-CommRing : CommRing ℓ
      ⊕FunGradedRing-CommRing = InducedCommRing ⊕HITgradedRing-CommRing
                                        0⊕Fun 1⊕Fun _+⊕Fun_ _prodF_ -⊕Fun_
                                        (fst (Equiv-DirectSum G Gstr))
                                        (pres1 (snd (Equiv-DirectSum G Gstr)))
                                        ⊕HIT→⊕Fun-pres1
                                        (pres· (snd (Equiv-DirectSum G Gstr)))
                                        ⊕HIT→⊕Fun-pres-prodF
                                        (presinv (snd (Equiv-DirectSum G Gstr)))

      CommRingEquiv-DirectSumGradedRing : CommRingEquiv ⊕HITgradedRing-CommRing ⊕FunGradedRing-CommRing
      CommRingEquiv-DirectSumGradedRing = InducedCommRingEquiv ⊕HITgradedRing-CommRing
                                        0⊕Fun 1⊕Fun _+⊕Fun_ _prodF_ -⊕Fun_
                                        (fst (Equiv-DirectSum G Gstr))
                                        (pres1 (snd (Equiv-DirectSum G Gstr)))
                                        ⊕HIT→⊕Fun-pres1
                                        (pres· (snd (Equiv-DirectSum G Gstr)))
                                        ⊕HIT→⊕Fun-pres-prodF
                                        (presinv (snd (Equiv-DirectSum G Gstr)))
