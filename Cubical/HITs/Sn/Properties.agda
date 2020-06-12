{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Sn.Properties where

open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Bool
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.HITs.S1
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp
open import Cubical.Data.Unit
open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.PropositionalTruncation

private
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

isGroupoidS1 : isGroupoid (S₊ 1)
isGroupoidS1 = transport (λ i → isGroupoid (S¹≡S1 (~ i))) isGroupoidS¹

isConnectedS1 : (x : S₊ 1) → ∥ north ≡ x ∥
isConnectedS1 x = rec propTruncIsProp
                       (λ p → ∣ cong (transport (sym (S¹≡S1))) p ∙ transport⁻Transport (S¹≡S1) x ∣)
                       (isConnectedS¹ (transport S¹≡S1 x))


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

SuspBool→S1-sect : section SuspBool→S1 S1→SuspBool
SuspBool→S1-sect north = refl
SuspBool→S1-sect south = refl
SuspBool→S1-sect (merid north i) = refl
SuspBool→S1-sect (merid south i) = refl

SuspBool→S1-retr : retract SuspBool→S1 S1→SuspBool
SuspBool→S1-retr north = refl
SuspBool→S1-retr south = refl
SuspBool→S1-retr (merid false i) = refl
SuspBool→S1-retr (merid true i) = refl

SuspBool≃S1 : Susp Bool ≃ S₊ 1
SuspBool≃S1 = isoToEquiv iso1
  where
  iso1 : Iso (Susp Bool) (S₊ 1)
  Iso.fun iso1 = SuspBool→S1
  Iso.inv iso1 = S1→SuspBool
  Iso.rightInv iso1 = SuspBool→S1-sect
  Iso.leftInv iso1 = SuspBool→S1-retr


S1→S¹ : S₊ 1 → S¹
S1→S¹ x = SuspBool→S¹ (S1→SuspBool x)

S¹→S1 : S¹ → S₊ 1
S¹→S1 x = SuspBool→S1 (S¹→SuspBool x)

S1→S¹-sect : section S1→S¹ S¹→S1
S1→S¹-sect x =
    cong SuspBool→S¹ (SuspBool→S1-retr (S¹→SuspBool x))
  ∙ S¹→SuspBool→S¹ x

S1→S¹-retr : retract S1→S¹ S¹→S1
S1→S¹-retr x =
    cong SuspBool→S1 (SuspBool→S¹→SuspBool (S1→SuspBool x))
  ∙ SuspBool→S1-sect x


-- map between S¹ ∧ A and Susp A.
private
  f' : {a : A} → A → S₊ 1 → Susp A
  f' {a = pt} A north = north
  f' {a = pt} A south = north
  f' {a = pt} a (merid p i) = ((merid a) ∙ sym (merid pt)) i

  proj' : {A : Pointed ℓ} {B : Pointed ℓ'} → typ A → typ B → A ⋀ B
  proj' a b = inr (a , b)

module smashS1→susp {(A , pt) : Pointed ℓ} where
  fun : (S₊ 1 , north) ⋀ (A , pt) → (Susp A)
  fun (inl tt) = north
  fun (inr (x , x₁)) = f' {a = pt} x₁ x
  fun  (push (inl north) i) = north
  fun (push (inl south) i) = north
  fun (push (inl (merid a i₁)) i) = rCancel (merid pt) (~ i) i₁
  fun (push (inr x) i) = north
  fun (push (push tt i₁) i) = north

  fun⁻ : Susp A → (S₊ 1 , north) ⋀ (A , pt)
  fun⁻ north = inl tt
  fun⁻ south = inl tt
  fun⁻ (merid a i) =
    (push (inr a) ∙∙ cong (λ x → proj' {A = S₊ 1 , north} {B = A , pt} x a) (merid south ∙ sym (merid north)) ∙∙ sym (push (inr a))) i

  {- TODO : Prove that they cancel out -}

{- Map used in definition of cup product. Maybe mover there later -}
sphereSmashMap : (n m : ℕ) → (S₊ (suc n) , north) ⋀ (S₊ (suc m) , north) → S₊ (2 + n + m)
sphereSmashMap zero m = smashS1→susp.fun
sphereSmashMap (suc n) m =
  smashS1→susp.fun ∘
  (idfun∙ _ ⋀→ (sphereSmashMap n m , refl)) ∘
  ⋀-associate ∘
  ((smashS1→susp.fun⁻ , refl) ⋀→ idfun∙ _)
