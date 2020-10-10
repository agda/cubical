{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Algebra.Group.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

module GroupLemmas (G : Group {ℓ}) where
  open Group G public
  abstract
    simplL : (a : Carrier) {b c : Carrier} → a + b ≡ a + c → b ≡ c
    simplL a {b} {c} p =
      b
        ≡⟨ sym (lid b) ∙ cong (_+ b) (sym (invl a)) ∙ sym (assoc _ _ _) ⟩
      - a + (a + b)
        ≡⟨ cong (- a +_) p ⟩
      - a + (a + c)
        ≡⟨ assoc _ _ _ ∙ cong (_+ c) (invl a) ∙ lid c ⟩
      c ∎

    simplR : {a b : Carrier} (c : Carrier) → a + c ≡ b + c → a ≡ b
    simplR {a} {b} c p =
      a
        ≡⟨ sym (rid a) ∙ cong (a +_) (sym (invr c)) ∙ assoc _ _ _ ⟩
      (a + c) - c
        ≡⟨ cong (_- c) p ⟩
      (b + c) - c
        ≡⟨ sym (assoc _ _ _) ∙ cong (b +_) (invr c) ∙ rid b ⟩
      b ∎

    invInvo : (a : Carrier) → - (- a) ≡ a
    invInvo a = simplL (- a) (invr (- a) ∙ sym (invl a))

    invId : - 0g ≡ 0g
    invId = simplL 0g (invr 0g ∙ sym (lid 0g))

    idUniqueL : {e : Carrier} (x : Carrier) → e + x ≡ x → e ≡ 0g
    idUniqueL {e} x p = simplR x (p ∙ sym (lid _))

    idUniqueR : (x : Carrier) {e : Carrier} → x + e ≡ x → e ≡ 0g
    idUniqueR x {e} p = simplL x (p ∙ sym (rid _))

    invUniqueL : {g h : Carrier} → g + h ≡ 0g → g ≡ - h
    invUniqueL {g} {h} p = simplR h (p ∙ sym (invl h))

    invUniqueR : {g h : Carrier} → g + h ≡ 0g → h ≡ - g
    invUniqueR {g} {h} p = simplL g (p ∙ sym (invr g))

    invDistr : (a b : Carrier) → - (a + b) ≡ - b - a
    invDistr a b = sym (invUniqueR γ) where
      γ : (a + b) + (- b - a) ≡ 0g
      γ = (a + b) + (- b - a)
            ≡⟨ sym (assoc _ _ _) ⟩
          a + b + (- b) + (- a)
            ≡⟨ cong (a +_) (assoc _ _ _ ∙ cong (_+ (- a)) (invr b)) ⟩
          a + (0g - a)
            ≡⟨ cong (a +_) (lid (- a)) ∙ invr a ⟩
          0g ∎

isPropIsGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G)
             → isProp (IsGroup 0g _+_ -_)
IsGroup.isMonoid (isPropIsGroup 0g _+_ -_ g1 g2 i) = isPropIsMonoid _ _ (IsGroup.isMonoid g1) (IsGroup.isMonoid g2) i
IsGroup.inverse (isPropIsGroup 0g _+_ -_ g1 g2 i) = isPropInv (IsGroup.inverse g1) (IsGroup.inverse g2) i
  where
  isSetG : isSet _
  isSetG = IsSemigroup.is-set (IsMonoid.isSemigroup (IsGroup.isMonoid g1))

  isPropInv : isProp ((x : _) → ((x + (- x)) ≡ 0g) × (((- x) + x) ≡ 0g))
  isPropInv = isPropΠ λ _ → isProp× (isSetG _ _) (isSetG _ _)
