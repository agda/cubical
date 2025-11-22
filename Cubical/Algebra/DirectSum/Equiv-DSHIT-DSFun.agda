module Cubical.Algebra.DirectSum.Equiv-DSHIT-DSFun where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+n_)
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
open import Cubical.Algebra.AbGroup.Instances.DirectSumHIT
open import Cubical.Algebra.AbGroup.Instances.NProd

open import Cubical.Algebra.DirectSum.DirectSumFun.Base
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.DirectSum.DirectSumHIT.Properties
open import Cubical.Algebra.DirectSum.DirectSumHIT.PseudoNormalForm

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
    ; +Assoc   to +⊕HIT-Assoc
    ; +IdR     to +⊕HIT-IdR
    ; +IdL     to +⊕HIT-IdL
    ; +InvR    to +⊕HIT-InvR
    ; +InvL    to +⊕HIT-InvL
    ; +Comm     to +⊕HIT-Comm
    ; is-set   to isSet⊕HIT)


  open AbGroupStr (snd (⊕Fun-AbGr G Gstr)) using ()
    renaming
    ( 0g       to 0⊕Fun
    ; _+_      to _+⊕Fun_
    ; -_       to -⊕Fun_
    ; +Assoc   to +⊕Fun-Assoc
    ; +IdR     to +⊕Fun-IdR
    ; +IdL     to +⊕Fun-IdL
    ; +InvR    to +⊕Fun-InvR
    ; +InvL    to +⊕Fun-InvL
    ; +Comm     to +⊕Fun-Comm
    ; is-set   to isSet⊕Fun)

-----------------------------------------------------------------------------
-- AbGroup on Fun -> produit ? sequence ?

  open AbGroupStr (snd (NProd-AbGroup G Gstr)) using ()
      renaming
    ( 0g       to 0Fun
    ; _+_      to _+Fun_
    ; -_       to -Fun_
    ; +Assoc   to +FunAssoc
    ; +IdR     to +FunIdR
    ; +IdL     to +FunIdL
    ; +InvR    to +FunInvR
    ; +InvL    to +FunInvL
    ; +Comm     to +FunComm
    ; is-set   to isSetFun)

-----------------------------------------------------------------------------
-- Some simplification for transport

  open SubstLemma ℕ G Gstr

  substG-fct : (g : (n : ℕ) → G n) → {k n : ℕ} → (p : k ≡ n) → subst G p (g k) ≡ g n
  substG-fct g {k} {n} p = J (λ n p → subst G p (g k) ≡ g n) (transportRefl _) p


-----------------------------------------------------------------------------
-- Direct Sense

  -- To facilitate the proof the translation to the function
  -- and its properties are done in two times

  ---------------------------------------------------------------------------
  -- Translation to the function

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
  ⊕HIT→Fun = DS-Rec-Set.f _ _ _ _ isSetFun
              0Fun
              fun-trad
              _+Fun_
              +FunAssoc
              +FunIdR
              +FunComm
              (λ k → funExt (λ n → base0-eq k n))
              λ k a b → funExt (λ n → base-add-eq k a b n)
           where
           base0-eq : (k : ℕ) → (n : ℕ) → fun-trad k (0g (Gstr k)) n ≡ 0g (Gstr n)
           base0-eq k n with (discreteℕ k n)
           ... | yes p = substG0 _
           ... | no ¬p = refl

           base-add-eq : (k : ℕ) → (a b : G k) → (n : ℕ) →
                         PathP (λ _ → G n) (Gstr n ._+_ (fun-trad k a n) (fun-trad k b n))
                                                         (fun-trad k ((Gstr k + a) b) n)
           base-add-eq k a b n with (discreteℕ k n)
           ... | yes p = substG+ _ _ _
           ... | no ¬p = +IdR (Gstr n)_

  ⊕HIT→Fun-pres0 : ⊕HIT→Fun 0⊕HIT ≡ 0Fun
  ⊕HIT→Fun-pres0 = refl

  ⊕HIT→Fun-pres+ : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→Fun (x +⊕HIT y) ≡ ((⊕HIT→Fun x) +Fun (⊕HIT→Fun y))
  ⊕HIT→Fun-pres+ x y = refl

  ---------------------------------------------------------------------------
  -- Translation to the properties

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
                                                          ∙ +IdR (Gstr n) _)) ∣₁} })

  ---------------------------------------------------------------------------
  -- Translation + Morphism

  ⊕HIT→⊕Fun : ⊕HIT ℕ G Gstr → ⊕Fun G Gstr
  ⊕HIT→⊕Fun x = (⊕HIT→Fun x) , (⊕HIT→⊕AlmostNull x)

  ⊕HIT→⊕Fun-pres0 : ⊕HIT→⊕Fun 0⊕HIT ≡ 0⊕Fun
  ⊕HIT→⊕Fun-pres0 = refl

  ⊕HIT→⊕Fun-pres+ : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→⊕Fun (x +⊕HIT y) ≡ ((⊕HIT→⊕Fun x) +⊕Fun (⊕HIT→⊕Fun y))
  ⊕HIT→⊕Fun-pres+ x y = ΣPathTransport→PathΣ _ _ (refl , (squash₁ _ _))


-----------------------------------------------------------------------------
-- Converse sense

  -----------------------------------------------------------------------------
  -- Prood that ⊕HIT→⊕Fun is injective

  open DefPNF G Gstr

  sumFun : {m : ℕ} → depVec G m → (n : ℕ) → G n
  sumFun {0} ⋆ = 0Fun
  sumFun {suc m} (a □ dv) = (⊕HIT→Fun (base m a)) +Fun (sumFun dv)

  SumHIT→SumFun : {m : ℕ} → (dv : depVec G m) → ⊕HIT→Fun (sumHIT dv) ≡ sumFun dv
  SumHIT→SumFun {0} ⋆ = refl
  SumHIT→SumFun {suc m} (a □ dv) = cong₂ _+Fun_ refl (SumHIT→SumFun dv)

  sumFun< : {m : ℕ} → (dv : depVec G m) → (i : ℕ) → (m ≤ i) → sumFun dv i ≡ 0g (Gstr i)
  sumFun< {0} ⋆ i r = refl
  sumFun< {suc m} (a □ dv) i r with discreteℕ m i
  ... | yes p = ⊥.rec (<→≢ r p)
  ... | no ¬p = +IdL (Gstr i) _ ∙ sumFun< dv i (≤-trans ≤-sucℕ r)

  sumFunHead : {m : ℕ} → (a b : (G m)) → (dva dvb : depVec G m) →
               (x : sumFun (a □ dva) ≡ sumFun (b □ dvb)) → a ≡ b
  sumFunHead {m} a b dva dvb x =
               a
                        ≡⟨ sym (+IdR (Gstr m) _) ⟩
               (Gstr m)._+_ a (0g (Gstr m))
                        ≡⟨ cong₂ (Gstr m ._+_) (sym (fun-trad-eq m a)) (sym (sumFun< dva m ≤-refl)) ⟩
               (Gstr m)._+_ (fun-trad m a m) (sumFun dva m)
                        ≡⟨ funExt⁻ x m ⟩
               (Gstr m)._+_ (fun-trad m b m) (sumFun dvb m)
                        ≡⟨ cong₂ (Gstr m ._+_) (fun-trad-eq m b) (sumFun< dvb m ≤-refl) ⟩
               (Gstr m)._+_ b (0g (Gstr m))
                        ≡⟨ +IdR (Gstr m) _ ⟩
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
                subst G p (0g (Gstr m))        ≡⟨ sym (cong (subst G p) (sumFun< dvb m ≤-refl)) ⟩
                subst G p (sumFun dvb m)       ≡⟨ substSumFun dvb n p ⟩
                sumFun dvb n ∎
  ... | no ¬p = sumFun dva n                                 ≡⟨ sym (+IdL (Gstr n) _) ⟩
                (Gstr n)._+_ (0g (Gstr n)) (sumFun dva n)    ≡⟨ cong (λ X → (Gstr n)._+_ X (sumFun dva n))
                                                                             (sym (fun-trad-neq m a n ¬p)) ⟩
                Gstr n ._+_ (fun-trad m a n) (sumFun dva n)  ≡⟨ funExt⁻ x n ⟩
                Gstr n ._+_ (fun-trad m b n) (sumFun dvb n)  ≡⟨ cong (λ X → Gstr n ._+_ X (sumFun dvb n))
                                                                             (fun-trad-neq m b n ¬p) ⟩
                (Gstr n)._+_ (0g (Gstr n)) (sumFun dvb n)    ≡⟨ +IdL (Gstr n) _ ⟩
                sumFun dvb n ∎

  injSumFun : {m : ℕ} → (dva dvb : depVec G m) → sumFun dva ≡ sumFun dvb → dva ≡ dvb
  injSumFun {0} ⋆ ⋆ x = refl
  injSumFun {suc m} (a □ dva) (b □ dvb) x = depVecPath.decode G (a □ dva) (b □ dvb)
                                         ((sumFunHead a b dva dvb x)
                                         , (injSumFun dva dvb (funExt (sumFunTail a b dva dvb x))))

  injSumHIT : {m : ℕ} → (dva dvb : depVec G m) → ⊕HIT→Fun (sumHIT dva) ≡ ⊕HIT→Fun (sumHIT dvb) → dva ≡ dvb
  injSumHIT dva dvb r = injSumFun dva dvb (sym (SumHIT→SumFun dva) ∙ r ∙ SumHIT→SumFun dvb)

  inj-⊕HIT→Fun : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→Fun x ≡ ⊕HIT→Fun y → x ≡ y
  inj-⊕HIT→Fun x y r = helper (⊕HIT→PNF2 x y) r
    where
    helper : PNF2 x y → ⊕HIT→Fun x ≡ ⊕HIT→Fun y → x ≡ y
    helper = PT.elim (λ _ → isPropΠ (λ _ → isSet⊕HIT _ _))
                     λ { (m , dva , dvb , p , q) r →
                         p
                         ∙ cong sumHIT (injSumHIT dva dvb (sym (cong ⊕HIT→Fun p) ∙ r ∙ cong ⊕HIT→Fun q))
                         ∙ sym q}

  inj-⊕HIT→⊕Fun : (x y : ⊕HIT ℕ G Gstr) → ⊕HIT→⊕Fun x ≡ ⊕HIT→⊕Fun y → x ≡ y
  inj-⊕HIT→⊕Fun x y p = inj-⊕HIT→Fun x y (fst (PathΣ→ΣPathTransport _ _ p))

  lemProp : (g : ⊕Fun G Gstr) → isProp (Σ[ x ∈ ⊕HIT ℕ G Gstr ] ⊕HIT→⊕Fun x ≡ g )
  lemProp g (x , p) (y , q) = ΣPathTransport→PathΣ _ _
                              ((inj-⊕HIT→⊕Fun x y (p ∙ sym q)) , isSet⊕Fun _ _ _ _)


  ---------------------------------------------------------------------------
  --  General translation for underliyng function

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

  -- if m < n then the translation of sum up to i is 0
  Strad-m<n : (g : (n : ℕ) → G n) → (m : ℕ) → (n : ℕ) → (r : m < n)
            → ⊕HIT→Fun (Strad g m) n ≡ 0g (Gstr n)
  Strad-m<n g zero n r with discreteℕ 0 n
  ... | yes p = ⊥.rec (<→≢ r p)
  ... | no ¬p = refl
  Strad-m<n g (suc m) n r with discreteℕ (suc m) n
  ... | yes p = ⊥.rec (<→≢ r p)
  ... | no ¬p = +IdL (Gstr n) _ ∙ Strad-m<n g m n (<-trans ≤-refl r)

  {- if n ≤ m, prove ⊕HIT→Fun (∑_{i ∈〚0, m〛} base i (g i)) ≡ g n
     then n is equal to only one〚0, m〛=> induction on m
     case 0 : ok
     case suc m : if n ≡ suc m, then the rest of the sum is 0 by trad-m<n
                  if n ≢ suc m, then it is in the rest of the sum => recursive call -}
  Strad-n≤m : (g : (n : ℕ) → G n) → (m : ℕ) → (n : ℕ) → (r : n ≤ m) → ⊕HIT→Fun (Strad g m) n ≡ g n
  Strad-n≤m g zero n r with discreteℕ 0 n
  ... | yes p = substG-fct g p
  ... | no ¬p = ⊥.rec (¬p (sym (≤0→≡0 r)))
  Strad-n≤m g (suc m) n r with discreteℕ (suc m) n
  ... | yes p = cong₂ ((Gstr n)._+_) (substG-fct g p) (Strad-m<n g m n (0 , p)) ∙ +IdR (Gstr n) _
  ... | no ¬p = +IdL (Gstr n) _ ∙ Strad-n≤m g m n (≤-suc-≢ r λ x → ¬p (sym x))


  ---------------------------------------------------------------------------
  -- Translation + Morphsim

  -- translation
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
                             (sym (constSubstCommSlice G (⊕HIT ℕ G Gstr) base p a))
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
