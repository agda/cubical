{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Localistation where

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

record isSubMonoid (RX : CommRing {ℓ}) (S : ℙ ⟨ RX ⟩) : Type ℓ where
 constructor
   submonoid
 field
   containsOne : (RX .CommRing.1r) ∈ S
   multClosed : ∀ {s t} → s ∈ S → t ∈ S → (RX .CommRing._·_ s t) ∈ S

module _(RX : CommRing {ℓ}) (S : ℙ ⟨ RX ⟩) (SsubMonoid : isSubMonoid RX S) where
 open isSubMonoid
 open CommRing

 R = ⟨ RX ⟩
 0ᴿ = RX .0r
 1ᴿ = RX .1r
 _+ᴿ_ = RX ._+_
 _·ᴿ_ = RX ._·_
 -ᴿ_ = RX .-_
 _-ᴿ_ : R → R → R
 _-ᴿ_ = λ x y → x +ᴿ (-ᴿ y)

 infixr 20 _·ᴿ_
 infixr 19 _+ᴿ_
 infixr 19 _-ᴿ_

 data S⁻¹R : Type ℓ where
  _/_ : (r s : R) → {s ∈ S} → S⁻¹R
  zd : (r₁ r₂ s s₁ s₂ : R) → {s ∈ S} → {a : s₁ ∈ S} → {b : s₂ ∈ S}
     → s ·ᴿ ((r₁ ·ᴿ s₂) -ᴿ (r₂ ·ᴿ s₁)) ≡ 0ᴿ
     → ((r₁ / s₁) {a}) ≡ ((r₂ / s₂) {b})
  trunc : isSet S⁻¹R

 infixr 15 _/_

 module Elim {ℓ'} {B : S⁻¹R → Type ℓ'}
     (_/*_ : (r s : R) → {a : s ∈ S} → B ((r / s) {a}))
     (zd* : (r₁ r₂ s s₁ s₂ : R) → {c : s ∈ S} → {a : s₁ ∈ S} → {b : s₂ ∈ S}
          → (p : s ·ᴿ ((r₁ ·ᴿ s₂) -ᴿ (r₂ ·ᴿ s₁)) ≡ 0ᴿ)
          → PathP (λ i → B (zd r₁ r₂ s s₁ s₂ {c} {a} {b} p i))  ((r₁ /* s₁) {a}) ((r₂ /* s₂) {b}))
     (trunc* : (q : S⁻¹R) → isSet (B q)) where


  f : (q : S⁻¹R) → B q
  f (r / s) = r /* s
  f (zd r₁ r₂ s s₁ s₂ p i) = zd* r₁ r₂ s s₁ s₂ p i
  f (trunc q₁ q₂ x y i j) = isOfHLevel→isOfHLevelDep 2 trunc*  (f q₁) (f q₂) (cong f x) (cong f y)
                                                      (trunc q₁ q₂ x y) i j


 module ElimProp {ℓ'} {B : S⁻¹R → Type ℓ'} (Bprop : {q : S⁻¹R} → isProp (B q))
                 (_/*_ : (r s : R) → {a : s ∈ S} → B ((r / s) {a})) where


  f : (q : S⁻¹R) → B q
  f = Elim.f _/*_ (λ r₁ r₂ s s₁ s₂ {c} {a} {b} p
    → toPathP (Bprop (transp (λ i → B (zd r₁ r₂ s s₁ s₂ {c} {a} {b} p i)) i0 (r₁ /* s₁))
              (r₂ /* s₂)))
             λ q → isProp→isSet Bprop


 module Rec {ℓ'} {B : Type ℓ'} (BType : isSet B)
     (_/*_ : (r s : R) → {s ∈ S} → B)
     (zd* : (r₁ r₂ s s₁ s₂ : R) → {c : s ∈ S} → {a : s₁ ∈ S} → {b : s₂ ∈ S}
          → (p : s ·ᴿ ((r₁ ·ᴿ s₂) -ᴿ (r₂ ·ᴿ s₁)) ≡ 0ᴿ)
          → ((r₁ /* s₁) {a}) ≡ ((r₂ /* s₂) {b}))
     where

  f : S⁻¹R → B
  f = Elim.f _/*_ zd* (λ _ → BType)



 module BinRec {ℓ'} {B : Type ℓ'} (BType : isSet B)
               (f[_/_][_/_] : (r s r' s' : R) → {s ∈ S} → {s' ∈ S} → B)
               (zdcong : (r₁ r₂ s s₁ s₂ : R) → {c : s ∈ S} → {a : s₁ ∈ S} → {b : s₂ ∈ S}
                       → (p : s ·ᴿ ((r₁ ·ᴿ s₂) -ᴿ (r₂ ·ᴿ s₁)) ≡ 0ᴿ)
                       → (r'₁ r'₂ s' s'₁ s'₂ : R) → {c' : s' ∈ S} → {a' : s'₁ ∈ S} → {b' : s'₂ ∈ S}
                       → (p' : s' ·ᴿ ((r'₁ ·ᴿ s'₂) -ᴿ (r'₂ ·ᴿ s'₁)) ≡ 0ᴿ)
                       → f[ r₁ / s₁ ][ r'₁ / s'₁ ] {a} {a'} ≡ f[ r₂ / s₂ ][ r'₂ / s'₂ ] {b} {b'})
               where

  f : S⁻¹R → S⁻¹R → B
  f = Rec.f (isSetΠ (λ _ → BType)) g θ
    where
    open IsCommRing
    open IsRing
    open IsMonoid
    open IsAbGroup
    open IsGroup

    zdcongr : (r s : R) → {a : s ∈ S}
            → (r'₁ r'₂ s' s'₁ s'₂ : R) → {c' : s' ∈ S} → {a' : s'₁ ∈ S} → {b' : s'₂ ∈ S}
            → (p' : s' ·ᴿ ((r'₁ ·ᴿ s'₂) -ᴿ (r'₂ ·ᴿ s'₁)) ≡ 0ᴿ)
            → f[ r / s ][ r'₁ / s'₁ ] {a} {a'} ≡ f[ r / s ][ r'₂ / s'₂ ] {a} {b'}
    zdcongr r s {a} r'₁ r'₂ s' s'₁ s'₂ {c'} {a'} {b'} p' =
     zdcong r r 1ᴿ s s {SsubMonoid .containsOne} {a} {a} p r'₁ r'₂ s' s'₁ s'₂ {c'} {a'} {b'} p'
      where
      p : 1ᴿ ·ᴿ ((r ·ᴿ s) -ᴿ (r ·ᴿ s)) ≡ 0ᴿ
      p = 1ᴿ ·ᴿ ((r ·ᴿ s) -ᴿ (r ·ᴿ s))
            ≡⟨ RX .isCommRing .isRing .·-isMonoid .identity ((r ·ᴿ s) -ᴿ (r ·ᴿ s)) .snd ⟩
          (r ·ᴿ s) -ᴿ (r ·ᴿ s)
            ≡⟨ RX .isCommRing .isRing .+-isAbGroup .isGroup .inverse (r ·ᴿ s) .fst ⟩
          0ᴿ ∎

    g : (r s : R) → {s ∈ S} → S⁻¹R → B
    g r s {a} = Rec.f BType (λ r' s' {a'} → f[ r / s ][ r' / s' ] {a} {a'}) (zdcongr r s {a})

    zdcongl : (r₃ s₃ : R) → {d : s₃ ∈ S}
            → (r₁ r₂ s s₁ s₂ : R) → {c : s ∈ S} → {a : s₁ ∈ S} → {b : s₂ ∈ S}
            → (p : s ·ᴿ ((r₁ ·ᴿ s₂) -ᴿ (r₂ ·ᴿ s₁)) ≡ 0ᴿ)
            → f[ r₁ / s₁ ][ r₃ / s₃ ] {a} {d} ≡ f[ r₂ / s₂ ][ r₃ / s₃ ] {b} {d}
    zdcongl r₃ s₃ {d} r₁ r₂ s s₁ s₂ {c} {a} {b} p =
     zdcong r₁ r₂ s s₁ s₂ {c} {a} {b} p r₃ r₃ 1ᴿ s₃ s₃ {SsubMonoid .containsOne} {d} {d} p'
      where
      p' : 1ᴿ ·ᴿ ((r₃ ·ᴿ s₃) -ᴿ (r₃ ·ᴿ s₃)) ≡ 0ᴿ
      p' = 1ᴿ ·ᴿ ((r₃ ·ᴿ s₃) -ᴿ (r₃ ·ᴿ s₃))
            ≡⟨ RX .isCommRing .isRing .·-isMonoid .identity ((r₃ ·ᴿ s₃) -ᴿ (r₃ ·ᴿ s₃)) .snd ⟩
          (r₃ ·ᴿ s₃) -ᴿ (r₃ ·ᴿ s₃)
            ≡⟨ RX .isCommRing .isRing .+-isAbGroup .isGroup .inverse (r₃ ·ᴿ s₃) .fst ⟩
          0ᴿ ∎

    θ : (r₁ r₂ s s₁ s₂ : R) {c : s ∈ S} {a : s₁ ∈ S} {b : s₂ ∈ S}
      → (s ·ᴿ ((r₁ ·ᴿ s₂) -ᴿ (r₂ ·ᴿ s₁))) ≡ 0ᴿ
      → g r₁ s₁ {a} ≡ g r₂ s₂ {b}
    θ r₁ r₂ s s₁ s₂ {c} {a} {b} p =
      funExt (ElimProp.f (BType _ _) λ r₃ s₃ {d} → zdcongl r₃ s₃ {d} r₁ r₂ s s₁ s₂ {c} {a} {b} p)



 _+ₗ_ : S⁻¹R → S⁻¹R → S⁻¹R
 _+ₗ_ = BinRec.f trunc g θ
  where
  g : (r s r' s' : R) {a : s ∈ S} {b : s' ∈ S} → S⁻¹R
  g  r s r' s' {a} {b} = (r ·ᴿ s' +ᴿ r' ·ᴿ s / s ·ᴿ s') {SsubMonoid .multClosed a b}

  θ : (r₁ r₂ s s₁ s₂ : R) {c : s ∈ S} {a : s₁ ∈ S} {b : s₂ ∈ S}
    → (p : s ·ᴿ ((r₁ ·ᴿ s₂) -ᴿ (r₂ ·ᴿ s₁)) ≡ 0ᴿ)
    → (r'₁ r'₂ s' s'₁ s'₂ : R) {c' : s' ∈ S} {a' : s'₁ ∈ S} {b' : s'₂ ∈ S}
    → (p' : s' ·ᴿ ((r'₁ ·ᴿ s'₂) -ᴿ (r'₂ ·ᴿ s'₁)) ≡ 0ᴿ)
    → (r₁ ·ᴿ s'₁ +ᴿ r'₁ ·ᴿ s₁ / s₁ ·ᴿ s'₁) {SsubMonoid .multClosed a a'}
    ≡ (r₂ ·ᴿ s'₂ +ᴿ r'₂ ·ᴿ s₂ / s₂ ·ᴿ s'₂) {SsubMonoid .multClosed b b'}
  θ r₁ r₂ s s₁ s₂ {c} {a} {b} p r'₁ r'₂ s' s'₁ s'₂ {c'} {a'} {b'} p' =
    zd _ _ (s ·ᴿ s') _ _ {SsubMonoid .multClosed c c'} path
    where
    open IsCommRing
    open IsRing
    open IsMonoid
    open IsAbGroup
    open IsGroup

    -- eq : (r₁ ·ᴿ s'₁ +ᴿ r'₁ ·ᴿ s₁) ·ᴿ s₂ ·ᴿ s'₂ -ᴿ (r₂ ·ᴿ s'₂ +ᴿ r'₂ ·ᴿ s₂) ·ᴿ s₁ ·ᴿ s'₁
    --    ≡ (r₁ ·ᴿ s₂ -ᴿ r₂ ·ᴿ s₁) ·ᴿ s'₁ ·ᴿ s'₂ +ᴿ (r'₁ ·ᴿ s'₂ -ᴿ r'₂ ·ᴿ s'₁) ·ᴿ s₁ ·ᴿ s₂
    -- eq =
    --   (r₁ ·ᴿ s'₁ +ᴿ r'₁ ·ᴿ s₁) ·ᴿ s₂ ·ᴿ s'₂ -ᴿ (r₂ ·ᴿ s'₂ +ᴿ r'₂ ·ᴿ s₂) ·ᴿ s₁ ·ᴿ s'₁
    --  ≡⟨ cong (_-ᴿ(r₂ ·ᴿ s'₂ +ᴿ r'₂ ·ᴿ s₂) ·ᴿ s₁ ·ᴿ s'₁) (RX .isCommRing .isRing .dist _ _ _ .snd) ⟩
    --   ((r₁ ·ᴿ s'₁) ·ᴿ s₂ ·ᴿ s'₂ +ᴿ (r'₁ ·ᴿ s₁) ·ᴿ s₂ ·ᴿ s'₂) -ᴿ (r₂ ·ᴿ s'₂ +ᴿ r'₂ ·ᴿ s₂) ·ᴿ s₁ ·ᴿ s'₁
    --  ≡⟨ {!!} ⟩
    --   (r₁ ·ᴿ s₂ -ᴿ r₂ ·ᴿ s₁) ·ᴿ s'₁ ·ᴿ s'₂ +ᴿ (r'₁ ·ᴿ s'₂ -ᴿ r'₂ ·ᴿ s'₁) ·ᴿ s₁ ·ᴿ s₂
    --  ∎

    path : (s ·ᴿ s') ·ᴿ
           ((r₁ ·ᴿ s'₁ +ᴿ r'₁ ·ᴿ s₁) ·ᴿ s₂ ·ᴿ s'₂ -ᴿ (r₂ ·ᴿ s'₂ +ᴿ r'₂ ·ᴿ s₂) ·ᴿ s₁ ·ᴿ s'₁)
         ≡ 0ᴿ
    path = {!!}
     -- (s ·ᴿ s') ·ᴿ ((r₁ ·ᴿ s'₁ +ᴿ r'₁ ·ᴿ s₁) ·ᴿ s₂ ·ᴿ s'₂ -ᴿ (r₂ ·ᴿ s'₂ +ᴿ r'₂ ·ᴿ s₂) ·ᴿ s₁ ·ᴿ s'₁)
     --  ≡⟨ ? ⟩
     -- (s ·ᴿ s') ·ᴿ ((r₁ ·ᴿ s₂ -ᴿ r₂ ·ᴿ s₁) ·ᴿ s'₁ ·ᴿ s'₂ +ᴿ (r'₁ ·ᴿ s'₂ -ᴿ r'₂ ·ᴿ s'₁) ·ᴿ s₁ ·ᴿ s₂)
     --  ≡⟨ ? ⟩
     -- (s ·ᴿ s') ·ᴿ ((r₁ ·ᴿ s₂ -ᴿ r₂ ·ᴿ s₁) ·ᴿ s'₁ ·ᴿ s'₂ +ᴿ (s ·ᴿ s') ·ᴿ (r'₁ ·ᴿ s'₂ -ᴿ r'₂ ·ᴿ s'₁) ·ᴿ s₁ ·ᴿ s₂
     --  ≡⟨ ? ⟩
     -- 0ᴿ ∎

 0ₗ = (0ᴿ / 1ᴿ) {SsubMonoid .containsOne}

 LocLeftIdentity : (x : S⁻¹R) → 0ₗ +ₗ x ≡ x
 LocLeftIdentity = ElimProp.f (trunc _ _) θ
  where
  θ : (r s : R) {a : s ∈ S}
    → (0ᴿ ·ᴿ s +ᴿ r ·ᴿ 1ᴿ / 1ᴿ ·ᴿ s) {SsubMonoid .multClosed (SsubMonoid .containsOne) a}
    ≡ (r / s) {a}
  θ r s {a} = zd _ _ 1ᴿ _ _ {SsubMonoid .containsOne} {!!}
   where
   open IsCommRing
   open IsRing
   open IsMonoid
   open IsAbGroup
   open IsGroup

   -- p : 0ᴿ ·ᴿ s +ᴿ r ·ᴿ 1ᴿ ≡ r
   -- p = 0ᴿ ·ᴿ s +ᴿ r ·ᴿ 1ᴿ
   --   ≡⟨ cong (_+ᴿ r ·ᴿ 1ᴿ) {!!} ⟩
   --     0ᴿ +ᴿ r ·ᴿ 1ᴿ
   --   ≡⟨ {!!} ⟩
   --     r ·ᴿ 1ᴿ
   --   ≡⟨ {!!} ⟩
   --     r
   --   ∎

   q : 1ᴿ ·ᴿ s ≡ s
   q = RX .isCommRing .isRing .·-isMonoid .identity _ .snd



 -- _·ₗ_ : S⁻¹R → S⁻¹R → S⁻¹R
 -- _·ₗ_ = BinRec.f trunc g θ
 --  where
 --  g : (r s r' s' : R) {a : s ∈ S} {b : s' ∈ S} → S⁻¹R
 --  g  r s r' s' {a} {b} = (r ·ᴿ r' / s ·ᴿ s') {SsubMonoid .multClosed a b}

 --  θ : (r₁ r₂ s s₁ s₂ : R) {c : s ∈ S} {a : s₁ ∈ S} {b : s₂ ∈ S}
 --    → (p : s ·ᴿ ((r₁ ·ᴿ s₂) -ᴿ (r₂ ·ᴿ s₁)) ≡ 0ᴿ)
 --    → (r'₁ r'₂ s' s'₁ s'₂ : R) {c' : s' ∈ S} {a' : s'₁ ∈ S} {b' : s'₂ ∈ S}
 --    → (p' : s' ·ᴿ ((r'₁ ·ᴿ s'₂) -ᴿ (r'₂ ·ᴿ s'₁)) ≡ 0ᴿ)
 --    → (r₁ ·ᴿ r'₁ / s₁ ·ᴿ s'₁) {SsubMonoid .multClosed a a'}
 --    ≡ (r₂ ·ᴿ r'₂ / s₂ ·ᴿ s'₂) {SsubMonoid .multClosed b b'}
 --  θ r₁ r₂ s s₁ s₂ {c} {a} {b} p r'₁ r'₂ s' s'₁ s'₂ {c'} {a'} {b'} p' =
 --    zd _ _ (s ·ᴿ s') _ _ {SsubMonoid .multClosed c c'} {!!}
