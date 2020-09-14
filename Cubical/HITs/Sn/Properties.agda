{-# OPTIONS --cubical --no-import-sorts --safe #-}
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
open import Cubical.HITs.S1 hiding (inv)
open import Cubical.HITs.S3
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp
open import Cubical.Data.Unit
open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.PropositionalTruncation

open Iso

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

--- Some silly lemmas on S1 ---

S¹≡S1 : S₊ 1 ≡ S¹
S¹≡S1 = refl

isGroupoidS1 : isGroupoid (S₊ 1)
isGroupoidS1 = isGroupoidS¹

isConnectedS1 : (x : S₊ 1) → ∥ base ≡ x ∥
isConnectedS1 x = rec propTruncIsProp
                       ∣_∣
                       (isConnectedS¹ (transport S¹≡S1 x))

joinBool : ∀ {ℓ} {A : Type ℓ}(pt : A) → Iso (Susp A) (join A A)
fun (joinBool pt) north = inl pt
fun (joinBool pt) south = inr pt
fun (joinBool pt) (merid a i) = {!!}
inv (joinBool pt) = {!!}
rightInv (joinBool pt) = {!!}
leftInv (joinBool pt) = {!!}

IsoS3-join : Iso (S₊ 3) (join S¹ S¹)
fun IsoS3-join = fun'
  where
  fun' : S₊ 3 → join S¹ S¹
  fun' north = inl base
  fun' south = inr base
  fun' (merid north i) = (refl ∙∙ (λ j → inl (loop j)) ∙∙ push base base) i --
  fun' (merid south i) = ((push base base) ∙∙ (λ j → inr (loop j)) ∙∙ refl) i -- push  (loop i) base i
  fun' (merid (merid base j) i) = ((λ k → push base base (k ∧ j)) ∙∙ (λ k → push (loop k) (loop k) j) ∙∙ λ k → push base base (k ∨ j)) i
  fun' (merid (merid (loop k) j) i) = ({!!} ∙∙ (λ l → push (loop l) (loop l) j) ∙∙ {!λ k → ?!}) i
inv IsoS3-join = {!!}
  where
  fun' : join S¹ S¹ → Susp (Susp S¹)
  fun' (inl base) = north
  fun' (inl (loop i)) = {!!}
  fun' (inr x) = north
  fun' (push base base i) = north
  fun' (push base (loop j) i) = north -- merid (merid base j) i
  fun' (push (loop i₁) base i) = north
  fun' (push (loop z) (loop j) i) = {!!}
rightInv IsoS3-join = {!!}
leftInv IsoS3-join = {!!}

-- SuspBool→S1 : Susp Bool → S₊ 1
-- SuspBool→S1 north           = north
-- SuspBool→S1 south           = south
-- SuspBool→S1 (merid false i) = merid south i
-- SuspBool→S1 (merid true i)  = merid north i

-- S1→SuspBool : S₊ 1 → Susp Bool
-- S1→SuspBool north           = north
-- S1→SuspBool south           = south
-- S1→SuspBool (merid north i) = merid true i
-- S1→SuspBool (merid south i) = merid false i

-- SuspBool→S1-sect : section SuspBool→S1 S1→SuspBool
-- SuspBool→S1-sect north = refl
-- SuspBool→S1-sect south = refl
-- SuspBool→S1-sect (merid north i) = refl
-- SuspBool→S1-sect (merid south i) = refl

-- SuspBool→S1-retr : retract SuspBool→S1 S1→SuspBool
-- SuspBool→S1-retr north = refl
-- SuspBool→S1-retr south = refl
-- SuspBool→S1-retr (merid false i) = refl
-- SuspBool→S1-retr (merid true i) = refl

-- S1→S¹ : S₊ 1 → S¹
-- S1→S¹ x = SuspBool→S¹ (S1→SuspBool x)

-- S¹→S1 : S¹ → S₊ 1
-- S¹→S1 x = SuspBool→S1 (S¹→SuspBool x)

-- S1→S¹-sect : section S1→S¹ S¹→S1
-- S1→S¹-sect x =
--     cong SuspBool→S¹ (SuspBool→S1-retr (S¹→SuspBool x))
--   ∙ S¹→SuspBool→S¹ x

-- S1→S¹-retr : retract S1→S¹ S¹→S1
-- S1→S¹-retr x =
--     cong SuspBool→S1 (SuspBool→S¹→SuspBool (S1→SuspBool x))
--   ∙ SuspBool→S1-sect x

-- SuspBoolIsoS1 : Iso (Susp Bool) (S₊ 1)
-- fun SuspBoolIsoS1                      = SuspBool→S1
-- inv SuspBoolIsoS1                      = S1→SuspBool
-- rightInv SuspBoolIsoS1 north           = refl
-- rightInv SuspBoolIsoS1 south           = refl
-- rightInv SuspBoolIsoS1 (merid north i) = refl
-- rightInv SuspBoolIsoS1 (merid south i) = refl
-- leftInv SuspBoolIsoS1 north            = refl
-- leftInv SuspBoolIsoS1 south            = refl
-- leftInv SuspBoolIsoS1 (merid false i)  = refl
-- leftInv SuspBoolIsoS1 (merid true i)   = refl

-- SuspBool≃S1 : Susp Bool ≃ S₊ 1
-- SuspBool≃S1 = isoToEquiv SuspBoolIsoS1

-- -- map between S¹ ∧ A and Susp A.
-- private
--   f' : {a : A} → A → S₊ 1 → Susp A
--   f' {a = pt} A north = north
--   f' {a = pt} A south = north
--   f' {a = pt} a (merid p i) = ((merid a) ∙ sym (merid pt)) i

--   proj' : {A : Pointed ℓ} {B : Pointed ℓ'} → typ A → typ B → A ⋀ B
--   proj' a b = inr (a , b)

-- module smashS1→susp {(A , pt) : Pointed ℓ} where
--   f : (S₊ 1 , north) ⋀ (A , pt) → (Susp A)
--   f (inl tt)                    = north
--   f (inr (x , x₁))              = f' {a = pt} x₁ x
--   f  (push (inl north) i)       = north
--   f (push (inl south) i)        = north
--   f (push (inl (merid a i₁)) i) = rCancel (merid pt) (~ i) i₁
--   f (push (inr x) i)            = north
--   f (push (push tt i₁) i)       = north

--   f⁻ : Susp A → (S₊ 1 , north) ⋀ (A , pt)
--   f⁻ north = inl tt
--   f⁻ south = inl tt
--   f⁻ (merid a i) =
--     (push (inr a) ∙∙ cong (λ x → proj' {A = S₊ 1 , north} {B = A , pt} x a) (merid south ∙ sym (merid north)) ∙∙ sym (push (inr a))) i

--   {- TODO : Prove that they cancel out -}

-- {- Map used in definition of cup product. Maybe mover there later -}
-- sphereSmashMap : (n m : ℕ) → (S₊ (suc n) , north) ⋀ (S₊ (suc m) , north) → S₊ (2 + n + m)
-- sphereSmashMap zero m = smashS1→susp.f
-- sphereSmashMap (suc n) m =
--   smashS1→susp.f ∘
--   (idfun∙ _ ⋀→ (sphereSmashMap n m , refl)) ∘
--   ⋀-associate ∘
--   ((smashS1→susp.f⁻ , refl) ⋀→ idfun∙ _)
