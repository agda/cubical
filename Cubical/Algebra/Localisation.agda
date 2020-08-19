{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Localisation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool
open import Cubical.Data.Nat hiding (_+_ ; +-comm ; +-assoc)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma.Base
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary

open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup hiding (⟨_⟩)
open import Cubical.Structures.Monoid hiding (⟨_⟩)
open import Cubical.Structures.Ring hiding (⟨_⟩)
open import Cubical.Structures.CommRing

open Iso

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

record isSubMonoid (R' : CommRing {ℓ}) (S : ℙ ⟨ R' ⟩) : Type ℓ where
 constructor
   submonoid
 field
   containsOne : (R' .CommRing.1r) ∈ S
   multClosed : ∀ {s t} → s ∈ S → t ∈ S → (R' .CommRing._·_ s t) ∈ S

module _(R' : CommRing {ℓ}) (S : ℙ ⟨ R' ⟩) (SsubMonoid : isSubMonoid R' S) where
 open isSubMonoid
 open CommRing R' renaming (Carrier to R)
 open Theory (CommRing→Ring R')


 data S⁻¹R : Type ℓ where
  _/_ : (r s : R) → ⦃ a : s ∈ S ⦄ → S⁻¹R
  zd : (r₁ r₂ s s₁ s₂ : R) → ⦃ c : s ∈ S ⦄ → ⦃ a : s₁ ∈ S ⦄ → ⦃ b : s₂ ∈ S ⦄
     → s · ((r₁ · s₂) - (r₂ · s₁)) ≡ 0r
     → r₁ / s₁ ≡ r₂ / s₂
  trunc : isSet S⁻¹R

 infixr 5 _/_

 module Elim {ℓ'} {B : S⁻¹R → Type ℓ'}
     (_/*_ : (r s : R) → ⦃ a : s ∈ S ⦄ → B (r / s))
     (zd* : (r₁ r₂ s s₁ s₂ : R) → ⦃ c : s ∈ S ⦄ → ⦃ a : s₁ ∈ S ⦄ → ⦃ b : s₂ ∈ S ⦄
          → (p : s · ((r₁ · s₂) - (r₂ · s₁)) ≡ 0r)
          → PathP (λ i → B (zd r₁ r₂ s s₁ s₂ p i))  (r₁ /* s₁) (r₂ /* s₂))
     (trunc* : (q : S⁻¹R) → isSet (B q)) where


  f : (q : S⁻¹R) → B q
  f (r / s) = r /* s
  f (zd r₁ r₂ s s₁ s₂ p i) = zd* r₁ r₂ s s₁ s₂ p i
  f (trunc q₁ q₂ x y i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f q₁) (f q₂) (cong f x) (cong f y)
                                                      (trunc q₁ q₂ x y) i j


 module ElimProp {ℓ'} {B : S⁻¹R → Type ℓ'} (Bprop : {q : S⁻¹R} → isProp (B q))
                 (_/*_ : (r s : R) → ⦃ a : s ∈ S ⦄ → B (r / s)) where


  f : (q : S⁻¹R) → B q
  f = Elim.f _/*_ (λ r₁ r₂ s s₁ s₂ p
    → toPathP (Bprop (transp (λ i → B (zd r₁ r₂ s s₁ s₂ p i)) i0 (r₁ /* s₁))
              (r₂ /* s₂)))
             λ q → isProp→isSet Bprop


 module Rec {ℓ'} {B : Type ℓ'} (BType : isSet B)
     (_/*_ : (r s : R) → ⦃ s ∈ S ⦄ → B)
     (zd* : (r₁ r₂ s s₁ s₂ : R) → ⦃ c : s ∈ S ⦄ → ⦃ a : s₁ ∈ S ⦄ → ⦃ b : s₂ ∈ S ⦄
          → (p : s · ((r₁ · s₂) - (r₂ · s₁)) ≡ 0r)
          → r₁ /* s₁ ≡ r₂ /* s₂)
     where

  f : S⁻¹R → B
  f = Elim.f _/*_ zd* (λ _ → BType)



 module BinRec {ℓ'} {B : Type ℓ'} (BType : isSet B)
               (f[_/_][_/_] : (r s r' s' : R) → ⦃ c : s ∈ S ⦄ → ⦃ c' : s' ∈ S ⦄ → B)
               (zdcong : (r₁ r₂ s s₁ s₂ : R) → ⦃ c : s ∈ S ⦄ → ⦃ a : s₁ ∈ S ⦄ → ⦃ b : s₂ ∈ S ⦄
                       → (p : s · ((r₁ · s₂) - (r₂ · s₁)) ≡ 0r)
                       → (r'₁ r'₂ s' s'₁ s'₂ : R)
                       → ⦃ c' : s' ∈ S ⦄ → ⦃ a' : s'₁ ∈ S ⦄ → ⦃ b' : s'₂ ∈ S ⦄
                       → (p' : s' · ((r'₁ · s'₂) - (r'₂ · s'₁)) ≡ 0r)
                       → f[ r₁ / s₁ ][ r'₁ / s'₁ ] ≡ f[ r₂ / s₂ ][ r'₂ / s'₂ ])
               where

  f : S⁻¹R → S⁻¹R → B
  f = Rec.f (isSetΠ (λ _ → BType)) g θ
    where

    zdcongr : (r s : R) → ⦃ a : s ∈ S ⦄
            → (r'₁ r'₂ s' s'₁ s'₂ : R) → ⦃ c' : s' ∈ S ⦄ → ⦃ a' : s'₁ ∈ S ⦄ → ⦃ b' : s'₂ ∈ S ⦄
            → (p' : s' · ((r'₁ · s'₂) - (r'₂ · s'₁)) ≡ 0r)
            → f[ r / s ][ r'₁ / s'₁ ] ≡ f[ r / s ][ r'₂ / s'₂ ]
    zdcongr r s r'₁ r'₂ s' s'₁ s'₂ p' =
     zdcong r r 1r s s ⦃ SsubMonoid .containsOne ⦄ p r'₁ r'₂ s' s'₁ s'₂ p'
      where
      p : 1r · ((r · s) - (r · s)) ≡ 0r
      p = 1r · ((r · s) - (r · s)) ≡⟨ ·-identity _ .snd ⟩
          (r · s) - (r · s)        ≡⟨ +-rinv _ ⟩
          0r                       ∎

    g : (r s : R) → ⦃ c : s ∈ S ⦄ → S⁻¹R → B
    g r s = Rec.f BType (λ r' s' → f[ r / s ][ r' / s' ]) (zdcongr r s)

    zdcongl : (r₃ s₃ : R) → ⦃ d : s₃ ∈ S ⦄
            → (r₁ r₂ s s₁ s₂ : R) → ⦃ c : s ∈ S ⦄ → ⦃ a : s₁ ∈ S ⦄ → ⦃ b : s₂ ∈ S ⦄
            → (p : s · ((r₁ · s₂) - (r₂ · s₁)) ≡ 0r)
            → f[ r₁ / s₁ ][ r₃ / s₃ ] ≡ f[ r₂ / s₂ ][ r₃ / s₃ ]
    zdcongl r₃ s₃ r₁ r₂ s s₁ s₂ p =
     zdcong r₁ r₂ s s₁ s₂ p r₃ r₃ 1r s₃ s₃ ⦃ SsubMonoid .containsOne ⦄ p'
      where
      p' : 1r · ((r₃ · s₃) - (r₃ · s₃)) ≡ 0r
      p' = 1r · ((r₃ · s₃) - (r₃ · s₃)) ≡⟨ ·-identity _ .snd ⟩
           (r₃ · s₃) - (r₃ · s₃)        ≡⟨ +-rinv _ ⟩
           0r                           ∎

    θ : (r₁ r₂ s s₁ s₂ : R) ⦃ c : s ∈ S ⦄ ⦃ a : s₁ ∈ S ⦄ ⦃ b : s₂ ∈ S ⦄
      → (s · ((r₁ · s₂) - (r₂ · s₁))) ≡ 0r
      → g r₁ s₁ ≡ g r₂ s₂
    θ r₁ r₂ s s₁ s₂ p =
      funExt (ElimProp.f (BType _ _) λ r₃ s₃ → zdcongl r₃ s₃ r₁ r₂ s s₁ s₂ p)



 _+ₗ_ : S⁻¹R → S⁻¹R → S⁻¹R
 _+ₗ_ = BinRec.f trunc g θ
  where
  g : (r s r' s' : R) ⦃ c : s ∈ S ⦄ ⦃ c' : s' ∈ S ⦄ → S⁻¹R
  g  r s r' s' ⦃ c ⦄ ⦃ c' ⦄ = (r · s' + r' · s / s · s') ⦃ SsubMonoid .multClosed c c' ⦄

  θ : (r₁ r₂ s s₁ s₂ : R) ⦃ c : s ∈ S ⦄ ⦃ a : s₁ ∈ S ⦄ ⦃ b : s₂ ∈ S ⦄
    → (p : s · ((r₁ · s₂) - (r₂ · s₁)) ≡ 0r)
    → (r'₁ r'₂ s' s'₁ s'₂ : R) ⦃ c' : s' ∈ S ⦄ ⦃ a' : s'₁ ∈ S ⦄ ⦃ b' : s'₂ ∈ S ⦄
    → (p' : s' · ((r'₁ · s'₂) - (r'₂ · s'₁)) ≡ 0r)
    → (r₁ · s'₁ + r'₁ · s₁ / s₁ · s'₁) ⦃ SsubMonoid .multClosed _ _ ⦄
    ≡ (r₂ · s'₂ + r'₂ · s₂ / s₂ · s'₂) ⦃ SsubMonoid .multClosed _ _ ⦄
  θ r₁ r₂ s s₁ s₂ ⦃ c ⦄ p r'₁ r'₂ s' s'₁ s'₂ ⦃ c' ⦄ p' =
    zd _ _ (s · s') _ _ ⦃ SsubMonoid .multClosed c c' ⦄ ⦃ _ ⦄ ⦃ _ ⦄ path
    where
    eq : (r₁ · s'₁ + r'₁ · s₁) · (s₂ · s'₂) - (r₂ · s'₂ + r'₂ · s₂) · (s₁ · s'₁)
       ≡ (r₁ · s₂ - r₂ · s₁) · (s'₁ · s'₂) + (r'₁ · s'₂ - r'₂ · s'₁) · (s₁ · s₂)
    eq = {!!}

    path : s · s' · ((r₁ · s'₁ + r'₁ · s₁) · (s₂ · s'₂) - (r₂ · s'₂ + r'₂ · s₂) · (s₁ · s'₁))
         ≡ 0r
    path =
     s · s' · ((r₁ · s'₁ + r'₁ · s₁) · (s₂ · s'₂) - (r₂ · s'₂ + r'₂ · s₂) · (s₁ · s'₁))
      ≡⟨ cong (λ t → s · s' · t) eq ⟩
     s · s' · ((r₁ · s₂ - r₂ · s₁) · (s'₁ · s'₂) + (r'₁ · s'₂ - r'₂ · s'₁) · (s₁ · s₂))
      ≡⟨ {!!} ⟩
     s · s' · (r₁ · s₂ - r₂ · s₁) · (s'₁ · s'₂) + s · s' · (r'₁ · s'₂ - r'₂ · s'₁) · (s₁ · s₂)
      ≡⟨ {!!} ⟩
     0r ∎


 -- _·ₗ_ : S⁻¹R → S⁻¹R → S⁻¹R
 -- _·ₗ_ = BinRec.f trunc g θ
 --  where
 --  g : (r s r' s' : R) {a : s ∈ S} {b : s' ∈ S} → S⁻¹R
 --  g  r s r' s' {a} {b} = (r · r' / s · s') {SsubMonoid .multClosed a b}

 --  θ : (r₁ r₂ s s₁ s₂ : R) {c : s ∈ S} {a : s₁ ∈ S} {b : s₂ ∈ S}
 --    → (p : s · ((r₁ · s₂) - (r₂ · s₁)) ≡ 0r)
 --    → (r'₁ r'₂ s' s'₁ s'₂ : R) {c' : s' ∈ S} {a' : s'₁ ∈ S} {b' : s'₂ ∈ S}
 --    → (p' : s' · ((r'₁ · s'₂) - (r'₂ · s'₁)) ≡ 0r)
 --    → (r₁ · r'₁ / s₁ · s'₁) {SsubMonoid .multClosed a a'}
 --    ≡ (r₂ · r'₂ / s₂ · s'₂) {SsubMonoid .multClosed b b'}
 --  θ r₁ r₂ s s₁ s₂ {c} {a} {b} p r'₁ r'₂ s' s'₁ s'₂ {c'} {a'} {b'} p' =
 --    zd _ _ (s · s') _ _ {SsubMonoid .multClosed c c'} {!!}


 -- Definition of zero and one in a localization
 0l = (0r / 1r) ⦃ SsubMonoid .containsOne ⦄
 1l = (1r / 1r) ⦃ SsubMonoid .containsOne ⦄

 LocLeftIdentity : (x : S⁻¹R) → 0l +ₗ x ≡ x
 LocLeftIdentity = ElimProp.f (trunc _ _) θ
  where
  θ : (r s : R) → ⦃ a : s ∈ S ⦄
    → (0r · s + r · 1r / 1r · s) ⦃ SsubMonoid .multClosed (SsubMonoid .containsOne) _ ⦄
    ≡ (r / s)

  θ r s = zd _ _ 1r _ _ ⦃ SsubMonoid .containsOne ⦄ ⦃ _ ⦄ ⦃ _ ⦄ path
   where
   p : 0r · s + r · 1r ≡ r
   p = 0r · s + r · 1r ≡⟨ cong (_+ r · 1r) (0-leftNullifies _) ⟩
       0r + r · 1r     ≡⟨ +-lid _ ⟩
       r · 1r          ≡⟨ ·-rid _ ⟩
       r               ∎

   path : 1r · ((0r · s + r · 1r) · s - r · (1r · s)) ≡ 0r
   path = 1r · ((0r · s + r · 1r) · s - r · (1r · s)) ≡⟨ ·-lid _ ⟩
          (0r · s + r · 1r) · s - r · (1r · s)        ≡⟨ cong (λ t → t · s - r · (1r · s)) p ⟩
          r · s - r · (1r · s)                        ≡⟨ cong (λ t → r · s - r · t) (·-lid s) ⟩
          r · s - r · s                               ≡⟨ +-rinv _ ⟩
          0r                                          ∎
