{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Sn.Properties where

open import Cubical.Data.Int
open import Cubical.Data.Bool
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.HITs.S1
open import Cubical.Data.Prod
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout

variable
  ℓ ℓ' : Level
  A : Type ℓ
  B : Type ℓ'



--- Some silly lemmas on S1 ---

S¹≡S1 : S₊ 1 ≡ S¹
S¹≡S1 = cong Susp (sym (ua Bool≃Susp⊥)) ∙ sym S¹≡SuspBool

isOfHLevelS1 : isOfHLevel 3 (S₊ 1)
isOfHLevelS1 = transport (λ i → isOfHLevel 3 (S¹≡S1 (~ i)))
                          λ x y → J (λ y p → (q : x ≡ y) → isProp (p ≡ q))
                                     (transport (λ i → isSet (basedΩS¹≡Int x (~ i))) isSetInt refl)

SuspBool→S1 : Susp Bool → S₊ 1
SuspBool→S1 north = north
SuspBool→S1 south = south
SuspBool→S1 (merid false i) = merid south i
SuspBool→S1 (merid true i) = merid north i

S1→SuspBool : S₊ 1 → Susp Bool
S1→SuspBool north = north
S1→SuspBool south = south
S1→SuspBool (merid north i) = merid true i
S1→SuspBool (merid south i) = merid false i

SuspBool≃S1 : Susp Bool ≃ S₊ 1
SuspBool≃S1 = isoToEquiv iso1
  where
  iso1 : Iso (Susp Bool) (S₊ 1)
  Iso.fun iso1 = SuspBool→S1
  Iso.inv iso1 = S1→SuspBool
  Iso.rightInv iso1 north = refl
  Iso.rightInv iso1 south = refl
  Iso.rightInv iso1 (merid north i) = refl
  Iso.rightInv iso1 (merid south i) = refl
  Iso.leftInv iso1 north = refl
  Iso.leftInv iso1 south = refl
  Iso.leftInv iso1 (merid false i) = refl
  Iso.leftInv iso1 (merid true i) = refl


private
  f* : {a : A} → S¹ → A → Susp A
  f* base b = north
  f* {a = a} (loop i) = funExt (λ x → merid x ∙ sym (merid a)) i


proj : {A : Pointed ℓ} {B : Pointed ℓ'} → typ A → typ B → A smash B
proj a b = inr (a , b)

projᵣ : {A : Pointed ℓ} {B : Pointed ℓ'} (a : typ A) → proj {A = A} a (pt B) ≡ inl tt
projᵣ a = sym (push (inl a))

projₗ : {A : Pointed ℓ} {B : Pointed ℓ'} (b : typ B) → proj {B = B} (pt A) b ≡ inl tt
projₗ b = sym (push (inr b))

projᵣₗ : {A : Pointed ℓ} {B : Pointed ℓ'} → projᵣ (pt A) ≡ projₗ (pt B)
projᵣₗ {A = A} {B = B} = cong sym (cong push (push tt))


module S1-smash-Iso ((A , pt) : Pointed ℓ) where
  fun : (S¹ , base) smash (A , pt) → (Susp A)
  fun (inl tt) = north
  fun (inr (x , x₁)) = f* {a = pt} x x₁ 
  fun (push (inl base) i) = north
  fun (push (inl (loop i₁)) i) = rCancel (merid pt) (~ i) i₁
  fun (push (inr x) i) = north
  fun (push (push a i₁) i) = north

  funInv : Susp A → (S¹ , base) smash (A , pt)
  funInv north = inl tt
  funInv south = inl tt
  funInv (merid a i) = (sym (projₗ a) ∙
                       cong (λ x → proj {A = S¹ , base} {B = A , pt} x a) loop ∙
                       projₗ a) i

  funSect : (x : Susp A) → fun (funInv x) ≡ x
  funSect north = refl
  funSect south = merid pt
  funSect (merid a i) = hcomp (λ k → λ {(i = i0) → ((λ j → (refl ∙ refl) ∙ refl ∙ refl) ∙
                                                     (λ j → rCancel refl j ∙ refl ∙ refl) ∙
                                                     λ j → lUnit (lUnit refl (~ j)) (~ j)) k ;
                                        (i = i1) → ((λ j → (refl ∙ refl) ∙ sym (refl ∙ (merid a ∙ sym (merid pt)) ∙ refl) ∙ merid a) ∙
                                                     (λ j → lUnit refl (~ j) ∙ sym (lUnit (rUnit (merid a ∙ sym (merid pt)) (~ j)) (~ j)) ∙ merid a) ∙
                                                     (λ j → lUnit (symDistr (merid a) (sym (merid pt)) j ∙ merid a) (~ j)) ∙
                                                     (sym (assoc (merid pt) (sym (merid a)) (merid a))) ∙
                                                     (λ j → merid pt ∙ lCancel (merid a) j) ∙
                                                     sym (rUnit (merid pt)) ) k})
                                                                (helper2 i ∙ filler i)
    where

    filler : (i : I) → (refl ∙ (merid a ∙ sym (merid pt)) ∙ refl) i ≡ merid a i
    filler i = (λ j → (refl ∙ (merid a ∙ sym (merid pt)) ∙ refl) (i ∧ (~ j))) ∙ λ j → merid a (j ∧ i)

    helper2 : (i : I) → fun ((sym (projₗ a) ∙
                              cong (λ x → proj {A = S¹ , base} {B = A , pt} x a) loop ∙
                              projₗ a) i)
                      ≡ ((λ i → fun (sym (projₗ a) i)) ∙
                         (λ i → fun (cong (λ x → proj {A = S¹ , base} {B = A , pt} x a) loop i)) ∙
                         λ i → fun (projₗ a i)) i
    helper2 i = (λ j → congFunct fun (sym (projₗ a)) (cong (λ x → proj {A = S¹ , base} {B = A , pt} x a) loop ∙ projₗ a) j i) ∙
                (λ j → (cong fun (sym (projₗ a)) ∙ congFunct fun (cong (λ x → proj {A = S¹ , base} {B = A , pt} x a) loop) (projₗ a) j) i)


  retrHelper : (x : S¹) (a : A) → funInv (f* {a = pt} x a) ≡ proj x a
  retrHelper base a = sym (projₗ a)
  retrHelper (loop i) a = hcomp (λ k → λ { (i = i0) → {!!}
                                          ; (i = i1) → {!!} })
                                filler

    where
    filler : funInv (f* {a = pt} (loop i) a) ≡ proj (loop i) a
    filler = (λ j → funInv (funExt (λ x → merid x ∙ sym (merid pt)) (i ∨ j) a)) ∙ sym (projₗ a) ∙ λ j → proj (loop (i ∧ j)) a

    id1 : funInv (f* {a = pt} (loop i) a) ≡ cong funInv (merid a ∙ sym (merid pt)) i
    id1 = refl

    id2 : funInv (f* {a = pt} (loop i) a) ≡ ((sym (projₗ a) ∙ cong (λ x → proj {A = S¹ , base} {B = A , pt} x a) loop ∙ (projₗ a)) ∙ sym (projₗ pt) ∙ sym (cong (λ x → proj {A = S¹ , base} {B = A , pt} x pt) loop) ∙ projₗ pt) i
    id2 = (λ j → congFunct funInv (merid a) (sym (merid pt)) j i) ∙
          (λ j → (((sym (projₗ a) ∙ cong (λ x → proj {A = S¹ , base} {B = A , pt} x a) loop ∙ (projₗ a))) ∙ symDistr (sym (projₗ pt)) (cong (λ x → proj {A = S¹ , base} {B = A , pt} x pt) loop ∙ projₗ pt) j) i) ∙ 
          (λ j → (((sym (projₗ a) ∙ cong (λ x → proj {A = S¹ , base} {B = A , pt} x a) loop ∙ (projₗ a))) ∙ symDistr (cong (λ x → proj {A = S¹ , base} {B = A , pt} x pt) loop) (projₗ pt) j ∙ projₗ pt) i) ∙
          λ j → (((sym (projₗ a) ∙ cong (λ x → proj {A = S¹ , base} {B = A , pt} x a) loop ∙ (projₗ a))) ∙ assoc (sym (projₗ pt)) (sym (cong (λ x → proj {A = S¹ , base} {B = A , pt} x pt) loop)) (projₗ pt) (~ j)) i

    id4 : sym (projᵣ base) ∙ cong ((λ x → proj {A = S¹ , base} {B = A , pt} x pt)) loop ∙ projᵣ base ≡ refl
    id4 = (λ i → (push (inl (loop i))) ∙ (λ j → inr (loop (i ∨ j) , pt)) ∙ sym (push (inl base))) ∙
          (λ i → push (inl base) ∙ lUnit (sym (push (inl base))) (~ i)) ∙
          rCancel (push (inl base))

    id3 : funInv ((merid pt) (~ i)) ≡ inl tt
    id3 = (λ j → (sym (projₗ pt) ∙ (cong (λ x → proj {A = S¹ , base} {B = A , pt} x pt) loop) ∙ projₗ pt) (~ i)) ∙
          (λ j → (sym ((projᵣₗ (~ j))) ∙ cong (λ x → proj {A = S¹ , base} {B = A , pt} x pt) loop ∙ projᵣₗ (~ j)) (~ i)) ∙
          (λ j → id4 j (~ i))


