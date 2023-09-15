{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.GradedRing.Instances.TrivialGradedRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; +-assoc ; +-zero)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.Instances.Nat
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Unit
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.GradedRing.Base
open import Cubical.Algebra.GradedRing.DirectSumHIT

private variable
  ℓ : Level

open Iso
open GradedRing-⊕HIT-index
open GradedRing-⊕HIT-⋆

module _
  (ARing@(A , Astr) : Ring ℓ)
  where

  open RingStr Astr
  open RingTheory ARing

  private

    G : ℕ → Type ℓ
    G zero = A
    G (suc k) = Unit*

    Gstr : (k : ℕ) → AbGroupStr (G k)
    Gstr zero = snd (Ring→AbGroup ARing)
    Gstr (suc k) = snd UnitAbGroup

    ⋆ : {k l : ℕ} → G k → G l → G (k Cubical.Data.Nat.+ l)
    ⋆ {zero} {zero} x y = x · y
    ⋆ {zero} {suc l} x y = tt*
    ⋆ {suc k} {l} x y = tt*

    0-⋆ : {k l : ℕ} (b : G l) → ⋆ (AbGroupStr.0g (Gstr k)) b ≡ AbGroupStr.0g (Gstr (k Cubical.Data.Nat.+ l))
    0-⋆ {zero} {zero} b = 0LeftAnnihilates _
    0-⋆ {zero} {suc l} b = refl
    0-⋆ {suc k} {l} b = refl

    ⋆-0 : {k l : ℕ} (a : G k) → ⋆ a (AbGroupStr.0g (Gstr l)) ≡ AbGroupStr.0g (Gstr (k Cubical.Data.Nat.+ l))
    ⋆-0 {zero} {zero} a = 0RightAnnihilates _
    ⋆-0 {zero} {suc l} a = refl
    ⋆-0 {suc k} {l} a = refl

    ⋆Assoc : {k l m : ℕ} (a : G k) (b : G l) (c : G m) →
             _≡_ {A = Σ[ k ∈ ℕ ] G k}
             (k Cubical.Data.Nat.+ (l Cubical.Data.Nat.+ m) , ⋆ a (⋆ b c))
             (k Cubical.Data.Nat.+ l Cubical.Data.Nat.+ m , ⋆ (⋆ a b) c)
    ⋆Assoc {zero} {zero} {zero} a b c =  ΣPathTransport→PathΣ _ _ (+-assoc _ _ _ , transportRefl _ ∙ ·Assoc _ _ _)
    ⋆Assoc {zero} {zero} {suc m} a b c = ΣPathTransport→PathΣ _ _ (+-assoc _ _ _ , transportRefl _)
    ⋆Assoc {zero} {suc l} {m} a b c =  ΣPathTransport→PathΣ _ _ (+-assoc _ _ _ , transportRefl _)
    ⋆Assoc {suc k} {l} {m} a b c = ΣPathTransport→PathΣ _ _ (+-assoc _ _ _ , transportRefl _)

    ⋆IdR : {k : ℕ} (a : G k) → _≡_ {A = Σ[ k ∈ ℕ ] G k} (k Cubical.Data.Nat.+ 0 , ⋆ a 1r) (k , a)
    ⋆IdR {zero} a = ΣPathTransport→PathΣ _ _ (refl , (transportRefl _ ∙ ·IdR _))
    ⋆IdR {suc k} a = ΣPathTransport→PathΣ _ _ ((+-zero _) , (transportRefl _))

    ⋆IdL : {l : ℕ} (b : G l) → _≡_ {A = Σ[ k ∈ ℕ ] G k} (l , ⋆ 1r b) (l , b)
    ⋆IdL {zero} b = ΣPathTransport→PathΣ _ _ (refl , (transportRefl _ ∙ ·IdL _))
    ⋆IdL {suc l} b = ΣPathTransport→PathΣ _ _ (refl , (transportRefl _))

    ⋆DistR+ : {k l : ℕ} (a : G k) (b c : G l) →
              ⋆ a (Gstr l .AbGroupStr._+_ b c) ≡ Gstr (k Cubical.Data.Nat.+ l) .AbGroupStr._+_ (⋆ a b) (⋆ a c)
    ⋆DistR+ {zero} {zero} a b c = ·DistR+ _ _ _
    ⋆DistR+ {zero} {suc l} a b c = refl
    ⋆DistR+ {suc k} {l} a b c = refl

    ⋆DistL+ : {k l : ℕ} (a b : G k) (c : G l) →
              ⋆ (Gstr k .AbGroupStr._+_ a b) c ≡ Gstr (k Cubical.Data.Nat.+ l) .AbGroupStr._+_ (⋆ a c) (⋆ b c)
    ⋆DistL+ {zero} {zero} a b c = ·DistL+ _ _ _
    ⋆DistL+ {zero} {suc l} a b c = refl
    ⋆DistL+ {suc k} {l} a b c = refl

  trivialGradedRing : GradedRing ℓ-zero ℓ
  trivialGradedRing = makeGradedRing ARing NatMonoid
                      G Gstr 1r ⋆  0-⋆ ⋆-0
                      ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+
                      equivRing
    where
    equivRing : RingEquiv ARing (⊕HITgradedRing-Ring
                                 NatMonoid G Gstr 1r ⋆ 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+)
    fst equivRing = isoToEquiv is
      where
      is : Iso A (⊕HIT ℕ G Gstr)
      fun is a = base 0 a
      inv is = DS-Rec-Set.f _ _ _ _ is-set
               0r (λ {zero a → a ; (suc k) a → 0r }) _+_ +Assoc +IdR +Comm
               (λ { zero → refl ; (suc k) → refl}) (λ {zero a b → refl ; (suc n) a b → +IdR _})
      rightInv is = DS-Ind-Prop.f _ _ _ _ (λ _ → trunc _ _)
                    (base-neutral _)
                    (λ { zero a → refl ; (suc k) a → base-neutral _ ∙ sym (base-neutral _)} )
                    λ {U V} ind-U ind-V → sym (base-add _ _ _) ∙ cong₂ _add_ ind-U ind-V
      leftInv is = λ _ → refl
    snd equivRing = makeIsRingHom
                    -- issue agda have trouble infering the Idx, G, Gstr
                    {R = ARing}
                    {S = ⊕HITgradedRing-Ring NatMonoid G Gstr 1r ⋆ 0-⋆ ⋆-0 ⋆Assoc ⋆IdR ⋆IdL ⋆DistR+ ⋆DistL+}
                    {f = λ a → base 0 a}
                    refl (λ _ _ → sym (base-add _ _ _)) λ _ _ → refl
