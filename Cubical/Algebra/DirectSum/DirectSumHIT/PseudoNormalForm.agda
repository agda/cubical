module Cubical.Algebra.DirectSum.DirectSumHIT.PseudoNormalForm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_ ; _·_ to _·n_)
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Vec.DepVec

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectSumHIT
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base

private variable
  ℓ : Level

open AbGroupStr
open AbGroupTheory


-----------------------------------------------------------------------------
-- Notation

module DefPNF
  (G : (n : ℕ) → Type ℓ)
  (Gstr : (n : ℕ) → AbGroupStr (G n))
  where

  open AbGroupStr (snd (⊕HIT-AbGr ℕ G Gstr)) using ()
    renaming
    ( 0g       to 0⊕HIT
    ; _+_      to _+⊕HIT_
    ; -_       to -⊕HIT_
    ; +Assoc    to +⊕HIT-Assoc
    ; +IdR     to +⊕HIT-IdR
    ; +IdL     to +⊕HIT-IdL
    ; +InvR    to +⊕HIT-InvR
    ; +InvL    to +⊕HIT-InvL
    ; +Comm     to +⊕HIT-Comm
    ; is-set   to isSet⊕HIT)


-----------------------------------------------------------------------------
-- Lemma

  -- def pseudo normal form
  sumHIT : {n : ℕ} → depVec G n → ⊕HIT ℕ G Gstr
  sumHIT {0} ⋆ = 0⊕HIT
  sumHIT {suc n} (a □ dv) = (base n a) +⊕HIT (sumHIT dv)

  -- 0 and sum
  replicate0g : (n : ℕ) → depVec G n
  replicate0g (zero) = ⋆
  replicate0g (suc n) = (0g (Gstr n)) □ (replicate0g n)

  sumHIT0g : (n : ℕ) → sumHIT (replicate0g n) ≡ 0⊕HIT
  sumHIT0g (zero) = refl
  sumHIT0g (suc n) = cong₂ _+⊕HIT_ (base-neutral n) (sumHIT0g n)
                     ∙ +⊕HIT-IdL _

  -- extension and sum
  extendDVL : (k l : ℕ) → (dv : depVec G l) → depVec G (k +n l)
  extendDVL zero  l dv = dv
  extendDVL (suc k) l dv = (0g (Gstr (k +n l))) □ (extendDVL k l dv)

  extendDVLeq : (k l : ℕ) → (dv : depVec G l) → sumHIT (extendDVL k l dv) ≡ sumHIT dv
  extendDVLeq (zero)  l dv = refl
  extendDVLeq (suc k) l dv = cong (λ X → X +⊕HIT sumHIT (extendDVL k l dv)) (base-neutral (k +n l))
                             ∙ +⊕HIT-IdL _
                             ∙ extendDVLeq k l dv

  extendDVR : (k l : ℕ) → (dv : depVec G k) → depVec G (k +n l)
  extendDVR k l dv = subst (λ X → depVec G X) (+-comm l k) (extendDVL l k dv)

  extendDVReq : (k l : ℕ) → (dv : depVec G k) → sumHIT (extendDVR k l dv) ≡ sumHIT dv
  extendDVReq k l dv = J (λ m p → sumHIT (subst (λ X → depVec G X) p (extendDVL l k dv)) ≡ sumHIT dv)
                       (sumHIT (subst (λ X → depVec G X) refl (extendDVL l k dv))
                               ≡⟨ cong sumHIT (transportRefl (extendDVL l k dv)) ⟩
                       sumHIT (extendDVL l k dv)
                               ≡⟨ extendDVLeq l k dv ⟩
                       sumHIT dv ∎)
                       (+-comm l k)

  -- pointwise add
  _pt+DV_ : {n : ℕ} → (dva dvb : depVec G n) → depVec G n
  _pt+DV_ {0} ⋆ ⋆ = ⋆
  _pt+DV_ {suc n} (a □ dva) (b □ dvb) = Gstr n ._+_ a b □ (dva pt+DV dvb)

  sumHIT+ : {n : ℕ} → (dva dvb : depVec G n) → sumHIT (dva pt+DV dvb) ≡ sumHIT dva +⊕HIT sumHIT dvb
  sumHIT+ {0} ⋆ ⋆ = sym (+⊕HIT-IdR _)
  sumHIT+ {suc n} (a □ dva) (b □ dvb) = cong₂ _+⊕HIT_ (sym (base-add _ _ _)) (sumHIT+ dva dvb)
                                        ∙ comm-4 (⊕HIT-AbGr ℕ G Gstr) _ _ _ _


-----------------------------------------------------------------------------
-- Case Traduction

  {- WARNING :
     The pseudo normal form is not unique.
     It is actually not unique enough so that it is not possible to raise one from ⊕HIT.
     Hence we actually need to make it a prop to be able to eliminate.
  -}

  untruncatedPNF : (x : ⊕HIT ℕ G Gstr) → Type ℓ
  untruncatedPNF x = Σ[ m ∈ ℕ ] Σ[ dv ∈ depVec G m ] x ≡ sumHIT dv

  PNF : (x : ⊕HIT ℕ G Gstr) → Type ℓ
  PNF x = ∥ untruncatedPNF x ∥₁

  untruncatedPNF2 : (x y : ⊕HIT ℕ G Gstr) → Type ℓ
  untruncatedPNF2 x y = Σ[ m ∈ ℕ ] Σ[ a ∈ depVec G m ] Σ[ b ∈ depVec G m ] (x ≡ sumHIT a) × (y ≡ sumHIT b)

  PNF2 :  (x y : ⊕HIT ℕ G Gstr) → Type ℓ
  PNF2 x y = ∥ untruncatedPNF2 x y ∥₁

-----------------------------------------------------------------------------
-- Translation

  ⊕HIT→PNF : (x : ⊕HIT ℕ G Gstr) → ∥ Σ[ m ∈ ℕ ] Σ[ a ∈ depVec G m ] x ≡ sumHIT a ∥₁
  ⊕HIT→PNF = DS-Ind-Prop.f _ _ _ _
        (λ _ → squash₁)
        ∣ (0 , (⋆ , refl)) ∣₁
        base→PNF
        add→PNF
    where
    base→PNF : (n : ℕ) → (a : G n) → PNF (base n a)
    base→PNF n a = ∣ (suc n) , ((a □ replicate0g n) , sym (cong (λ X → base n a +⊕HIT X) (sumHIT0g n)
                    ∙ +⊕HIT-IdR _)) ∣₁

    add→PNF : {U V : ⊕HIT ℕ G Gstr} → (ind-U : PNF U) → (ind-V : PNF V) → PNF (U +⊕HIT V)
    add→PNF {U} {V} = elim2 (λ _ _ → squash₁)
                      (λ { (k , dva , p) →
                      λ { (l , dvb , q) →
                      ∣ ((k +n l)
                        , (((extendDVR k l dva) pt+DV (extendDVL k l dvb))
                        , cong₂ _+⊕HIT_ p q
                          ∙ cong₂ _+⊕HIT_ (sym (extendDVReq k l dva)) (sym (extendDVLeq k l dvb))
                          ∙ sym (sumHIT+ (extendDVR k l dva) (extendDVL k l dvb)) )) ∣₁}})



  ⊕HIT→PNF2 : (x y : ⊕HIT ℕ G Gstr) → ∥ Σ[ m ∈ ℕ ] Σ[ a ∈ depVec G m ] Σ[ b ∈ depVec G m ] (x ≡ sumHIT a) × (y ≡ sumHIT b) ∥₁
  ⊕HIT→PNF2 x y = helper (⊕HIT→PNF x) (⊕HIT→PNF y)
    where
    helper : PNF x → PNF y →
             ∥ Σ[ m ∈ ℕ ] Σ[ a ∈ depVec G m ] Σ[ b ∈ depVec G m ] (x ≡ sumHIT a) × (y ≡ sumHIT b) ∥₁
    helper = elim2 (λ _ _ → squash₁)
                   (λ { (k , dva , p) →
                   λ { (l , dvb , q) →
                       ∣   ((k +n l)
                         , ((extendDVR k l dva)
                         , (extendDVL k l dvb
                         , p ∙ sym (extendDVReq k l dva)
                         , q ∙ sym (extendDVLeq k l dvb)))) ∣₁}})

-----------------------------------------------------------------------------
-- Some idea

{-
   This file should be generalizable to a general decidable index by adding a second vector
-}


{-
   It maybe possible to give a normal for without need the prop truncation.
   The issue with the current one is that we rely on a underline data type depVec
   which forces us to give an explict length. That's what forces the ∥_∥₁.
   Hence by getting rid of it and be rewrittinf the term it might be possible
   to get a normal form without the PT.

   Indeed this basically about pemuting and summing them by G n
   ∑ base (σ i) a (σ i) -> ∑[i ∈ ℕ] ∑[j ∈ I] base i (b i j) -> ∑ base i (c i)
   where a b c are informal "sequences"

   Then prove that if we extract the integer, we get an inceasing list
   with no coefficient being present twice.
-}
