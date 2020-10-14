{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module SyntheticReals.Number.Operations.Details where

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Data.Unit.Base -- Unit
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
open import Function.Base using (_$_)

open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s)

open import SyntheticReals.MoreNatProperties renaming (0≤x to 0≤xⁿ)

open import SyntheticReals.Number.Postulates
open import SyntheticReals.Number.Structures
open import SyntheticReals.Number.Bundles
open import SyntheticReals.Number.Inclusions
open import SyntheticReals.Number.Base
open import SyntheticReals.Number.Coercions

open ℕⁿ
open ℤᶻ
open ℚᶠ
open ℝʳ
open ℂᶜ

infix  9 _⁻¹
infix  8 -_

open import SyntheticReals.Number.Operations.Specification

open PatternsProp

_⁻¹ : ∀{l p} → (x : Number (l , p)) → ⁻¹-Types x

_⁻¹ {isNat    } {⁇x⁇} (x ,, q) {{h}} = let r = Isℕ↪ℚ.preserves-#0 ℕ↪ℚinc _ h in _⁻¹ᶠ (ℕ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-#0 _ r
_⁻¹ {isNat    } {x#0} (x ,, q) {{h}} = let r = Isℕ↪ℚ.preserves-#0 ℕ↪ℚinc _ q in _⁻¹ᶠ (ℕ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-#0 _ r
_⁻¹ {isNat    } {0≤x} (x ,, q) {{h}} = let p = Isℕ↪ℚ.preserves-0< ℕ↪ℚinc _ (ℕ.≤-#-implies-< _ _ q (ℕ.#-sym _ _ h))
                                           r = Isℕ↪ℚ.preserves-#0 ℕ↪ℚinc _ h
                                       in  _⁻¹ᶠ (ℕ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-0< _ p r
_⁻¹ {isNat    } {0<x} (x ,, q) {{h}} = let p = Isℕ↪ℚ.preserves-0< ℕ↪ℚinc _ q
                                           r = Isℕ↪ℚ.preserves-#0 ℕ↪ℚinc _ (ℕ.#-sym _ _ (ℕ.<-implies-# _ _ q))
                                       in  _⁻¹ᶠ (ℕ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-0< _ p r
_⁻¹ {isNat    } {x≤0} (x ,, q) {{h}} = let p = Isℕ↪ℚ.preserves-<0 ℕ↪ℚinc _ (ℕ.≤-#-implies-< _ _ q h)
                                           r = Isℕ↪ℚ.preserves-#0 ℕ↪ℚinc _ h
                                       in  _⁻¹ᶠ (ℕ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-<0 _ p r

_⁻¹ {isInt    } {⁇x⁇} (x ,, q) {{h}} = let r = Isℤ↪ℚ.preserves-#0 ℤ↪ℚinc _ h in _⁻¹ᶠ (ℤ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-#0 _ r
_⁻¹ {isInt    } {x#0} (x ,, q) {{h}} = let r = Isℤ↪ℚ.preserves-#0 ℤ↪ℚinc _ q in _⁻¹ᶠ (ℤ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-#0 _ r
_⁻¹ {isInt    } {0≤x} (x ,, q) {{h}} = let p = Isℤ↪ℚ.preserves-0< ℤ↪ℚinc _ (ℤ.≤-#-implies-< _ _ q (ℤ.#-sym _ _ h))
                                           r = Isℤ↪ℚ.preserves-#0 ℤ↪ℚinc _ h
                                       in  _⁻¹ᶠ (ℤ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-0< _ p r
_⁻¹ {isInt    } {0<x} (x ,, q) {{h}} = let p = Isℤ↪ℚ.preserves-0< ℤ↪ℚinc _ q
                                           r = Isℤ↪ℚ.preserves-#0 ℤ↪ℚinc _ (ℤ.#-sym _ _ (ℤ.<-implies-# _ _ q))
                                       in  _⁻¹ᶠ (ℤ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-0< _ p r
_⁻¹ {isInt    } {x<0} (x ,, q) {{h}} = let p = Isℤ↪ℚ.preserves-<0 ℤ↪ℚinc _ q
                                           r = Isℤ↪ℚ.preserves-#0 ℤ↪ℚinc _ (ℤ.<-implies-# _ _ q)
                                       in  _⁻¹ᶠ (ℤ↪ℚ x) {{r}} ,,  ℚ.⁻¹-preserves-<0 _ p r
_⁻¹ {isInt    } {x≤0} (x ,, q) {{h}} = let p = Isℤ↪ℚ.preserves-<0 ℤ↪ℚinc _ (ℤ.≤-#-implies-< _ _ q h)
                                           r = Isℤ↪ℚ.preserves-#0 ℤ↪ℚinc _ h
                                       in  _⁻¹ᶠ (ℤ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-<0 _ p r

_⁻¹ {isRat    } {⁇x⁇} (x ,, q) {{h}} =  _⁻¹ᶠ x  {{h}} ,, ℚ.⁻¹-preserves-#0 x h
_⁻¹ {isRat    } {x#0} (x ,, q) {{h}} =  _⁻¹ᶠ x  {{q}} ,, ℚ.⁻¹-preserves-#0 x q
_⁻¹ {isRat    } {0≤x} (x ,, q) {{h}} =  _⁻¹ᶠ x  {{h}} ,, ℚ.⁻¹-preserves-0< x (ℚ.≤-#-implies-< _ _ q (ℚ.#-sym _ _ h)) h
_⁻¹ {isRat    } {0<x} (x ,, q) {{h}} = let r = ℚ.#-sym _ _ (ℚ.<-implies-# _ _ q) in _⁻¹ᶠ x  {{r}} ,,  ℚ.⁻¹-preserves-0< _ q r
_⁻¹ {isRat    } {x<0} (x ,, q) {{h}} = let r = ℚ.<-implies-# _ _ q in _⁻¹ᶠ x  {{r}} ,, ℚ.⁻¹-preserves-<0 _ q r
_⁻¹ {isRat    } {x≤0} (x ,, q) {{h}} =  _⁻¹ᶠ x  {{h}} ,,  ℚ.⁻¹-preserves-<0 x (ℚ.≤-#-implies-< _ _ q h) h

_⁻¹ {isReal   } {⁇x⁇} (x ,, q) {{h}} =  _⁻¹ʳ x  {{h}} ,, ℝ.⁻¹-preserves-#0 x h
_⁻¹ {isReal   } {x#0} (x ,, q) {{h}} =  _⁻¹ʳ x  {{q}} ,, ℝ.⁻¹-preserves-#0 x q
_⁻¹ {isReal   } {0≤x} (x ,, q) {{h}} =  _⁻¹ʳ x  {{h}} ,, ℝ.⁻¹-preserves-0< x (ℝ.≤-#-implies-< _ _ q (ℝ.#-sym _ _ h)) h
_⁻¹ {isReal   } {0<x} (x ,, q) {{h}} = let r = ℝ.#-sym _ _ (ℝ.<-implies-# _ _ q) in _⁻¹ʳ x {{r}} ,,  ℝ.⁻¹-preserves-0< _ q r
_⁻¹ {isReal   } {x<0} (x ,, q) {{h}} = let r = ℝ.<-implies-# _ _ q in _⁻¹ʳ x  {{r}} ,, ℝ.⁻¹-preserves-<0 _ q r
_⁻¹ {isReal   } {x≤0} (x ,, q) {{h}} =  _⁻¹ʳ      x  {{h}} ,, ℝ.⁻¹-preserves-<0 x (ℝ.≤-#-implies-< _ _ q h) h

_⁻¹ {isComplex} {⁇x⁇} (x ,, q) {{h}} =  _⁻¹ᶜ      x  {{h}} ,, ℂ.⁻¹-preserves-#0 x h
_⁻¹ {isComplex} {x#0} (x ,, q) {{h}} =  _⁻¹ᶜ      x  {{q}} ,, ℂ.⁻¹-preserves-#0 x q

-_ : ∀{l p} → (x : Number (l , p)) → -Types x
-_ {isNat    } {⁇x⁇} (x ,, p) = (-ᶻ (ℕ↪ℤ x)) ,, (ℤ.-flips-0≤ _ $ Isℕ↪ℤ.preserves-0≤ ℕ↪ℤinc _ (0≤xⁿ x))
-_ {isNat    } {x#0} (x ,, p) = (-ᶻ (ℕ↪ℤ x)) ,, (ℤ.-preserves-#0 _ $ Isℕ↪ℤ.preserves-#0 ℕ↪ℤinc _ p)
-_ {isNat    } {0≤x} (x ,, p) = (-ᶻ (ℕ↪ℤ x)) ,, (ℤ.-flips-0≤ _ $ Isℕ↪ℤ.preserves-0≤ ℕ↪ℤinc _ p)
-_ {isNat    } {0<x} (x ,, p) = (-ᶻ (ℕ↪ℤ x)) ,, (ℤ.-flips-0< _ $ Isℕ↪ℤ.preserves-0< ℕ↪ℤinc _ p)
-_ {isNat    } {x≤0} (x ,, p) = (-ᶻ (ℕ↪ℤ x)) ,, (ℤ.-flips-≤0 _ $ Isℕ↪ℤ.preserves-≤0 ℕ↪ℤinc _ p)
-_ {isInt    } {⁇x⁇} (x ,, p) = (-ᶻ      x ) ,, lift tt
-_ {isInt    } {x#0} (x ,, p) = (-ᶻ      x ) ,, ℤ.-preserves-#0 _ p
-_ {isInt    } {0≤x} (x ,, p) = (-ᶻ      x ) ,, ℤ.-flips-0≤ _ p
-_ {isInt    } {0<x} (x ,, p) = (-ᶻ      x ) ,, ℤ.-flips-0< _ p
-_ {isInt    } {x<0} (x ,, p) = (-ᶻ      x ) ,, ℤ.-flips-<0 _ p
-_ {isInt    } {x≤0} (x ,, p) = (-ᶻ      x ) ,, ℤ.-flips-≤0 _ p
-_ {isRat    } {⁇x⁇} (x ,, p) = (-ᶠ      x ) ,, lift tt
-_ {isRat    } {x#0} (x ,, p) = (-ᶠ      x ) ,, ℚ.-preserves-#0 _ p
-_ {isRat    } {0≤x} (x ,, p) = (-ᶠ      x ) ,, ℚ.-flips-0≤ _ p
-_ {isRat    } {0<x} (x ,, p) = (-ᶠ      x ) ,, ℚ.-flips-0< _ p
-_ {isRat    } {x<0} (x ,, p) = (-ᶠ      x ) ,, ℚ.-flips-<0 _ p
-_ {isRat    } {x≤0} (x ,, p) = (-ᶠ      x ) ,, ℚ.-flips-≤0 _ p
-_ {isReal   } {⁇x⁇} (x ,, p) = (-ʳ      x ) ,, lift tt
-_ {isReal   } {x#0} (x ,, p) = (-ʳ      x ) ,, ℝ.-preserves-#0 _ p
-_ {isReal   } {0≤x} (x ,, p) = (-ʳ      x ) ,, ℝ.-flips-0≤ _ p
-_ {isReal   } {0<x} (x ,, p) = (-ʳ      x ) ,, ℝ.-flips-0< _ p
-_ {isReal   } {x<0} (x ,, p) = (-ʳ      x ) ,, ℝ.-flips-<0 _ p
-_ {isReal   } {x≤0} (x ,, p) = (-ʳ      x ) ,, ℝ.-flips-≤0 _ p
-_ {isComplex} {⁇x⁇} (x ,, p) = (-ᶜ      x ) ,, lift tt
-_ {isComplex} {x#0} (x ,, p) = (-ᶜ      x ) ,, ℂ.-preserves-#0 _ p

_+ʰⁿ_ : ∀{p q} → (x : Number (isNat , p)) → (y : Number (isNat , q)) → PositivityKindInterpretation isNat (+-Positivityʰ isNat p q) (num x +ⁿ num y)
_+ʰⁿ_ {⁇x⁇} {⁇x⁇} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {⁇x⁇} {x#0} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {⁇x⁇} {0≤x} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {⁇x⁇} {0<x} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {⁇x⁇} {x≤0} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {x#0} {⁇x⁇} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {x#0} {x#0} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {x#0} {0≤x} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {x#0} {0<x} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {x#0} {x≤0} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {0≤x} {⁇x⁇} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {0≤x} {x#0} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {0≤x} {0≤x} (a ,, pa) (b ,, pb) = ℕ.+-0≤-0≤-implies-0≤ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ a + b
_+ʰⁿ_ {0≤x} {0<x} (a ,, pa) (b ,, pb) = ℕ.+-0≤-0<-implies-0< a b pa pb -- 0 ≤ a → 0 < b → 0 < a + b
_+ʰⁿ_ {0≤x} {x≤0} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {0<x} {⁇x⁇} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {0<x} {x#0} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {0<x} {0≤x} (a ,, pa) (b ,, pb) = ℕ.+-0<-0≤-implies-0< a b pa pb -- 0 < a → 0 ≤ b → 0 < a + b
_+ʰⁿ_ {0<x} {0<x} (a ,, pa) (b ,, pb) = ℕ.+-0<-0<-implies-0< a b pa pb -- 0 < a → 0 < b → 0 < a + b
_+ʰⁿ_ {0<x} {x≤0} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {x≤0} {⁇x⁇} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {x≤0} {x#0} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {x≤0} {0≤x} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {x≤0} {0<x} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {x≤0} {x≤0} (a ,, pa) (b ,, pb) = ℕ.+-≤0-≤0-implies-≤0 a b pa pb -- a ≤ 0 → b ≤ 0 → (a + b) ≤ 0

_+ʰᶻ_ : ∀{p q} → (x : Number (isInt , p)) → (y : Number (isInt , q)) → PositivityKindInterpretation isInt (+-Positivityʰ isInt p q) (num x +ᶻ num y)
_+ʰᶻ_ {⁇x⁇} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {⁇x⁇} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {⁇x⁇} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {⁇x⁇} {0<x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {⁇x⁇} {x<0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {⁇x⁇} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x#0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x#0} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x#0} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x#0} {0<x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x#0} {x<0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x#0} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {0≤x} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {0≤x} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {0≤x} {0≤x} (a ,, pa) (b ,, pb) = ℤ.+-0≤-0≤-implies-0≤ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ a + b
_+ʰᶻ_ {0≤x} {0<x} (a ,, pa) (b ,, pb) = ℤ.+-0≤-0<-implies-0< a b pa pb -- 0 ≤ a → 0 < b → 0 < a + b
_+ʰᶻ_ {0≤x} {x<0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {0≤x} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {0<x} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {0<x} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {0<x} {0≤x} (a ,, pa) (b ,, pb) = ℤ.+-0<-0≤-implies-0< a b pa pb -- 0 < a → 0 ≤ b → 0 < a + b
_+ʰᶻ_ {0<x} {0<x} (a ,, pa) (b ,, pb) = ℤ.+-0<-0<-implies-0< a b pa pb -- 0 < a → 0 < b → 0 < a + b
_+ʰᶻ_ {0<x} {x<0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {0<x} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x<0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x<0} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x<0} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x<0} {0<x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x<0} {x<0} (a ,, pa) (b ,, pb) = ℤ.+-<0-<0-implies-<0 a b pa pb -- a < 0 → b < 0 → (a + b) < 0
_+ʰᶻ_ {x<0} {x≤0} (a ,, pa) (b ,, pb) = ℤ.+-<0-≤0-implies-<0 a b pa pb -- a < 0 → b ≤ 0 → (a + b) < 0
_+ʰᶻ_ {x≤0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x≤0} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x≤0} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x≤0} {0<x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {x≤0} {x<0} (a ,, pa) (b ,, pb) = ℤ.+-≤0-<0-implies-<0 a b pa pb -- a ≤ 0 → b < 0 → (a + b) < 0
_+ʰᶻ_ {x≤0} {x≤0} (a ,, pa) (b ,, pb) = ℤ.+-≤0-≤0-implies-≤0 a b pa pb -- a ≤ 0 → b ≤ 0 → (a + b) ≤ 0

_+ʰᶠ_ : ∀{p q} → (x : Number (isRat , p)) → (y : Number (isRat , q)) → PositivityKindInterpretation isRat (+-Positivityʰ isRat p q) (num x +ᶠ num y)
_+ʰᶠ_ {⁇x⁇} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {⁇x⁇} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {⁇x⁇} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {⁇x⁇} {0<x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {⁇x⁇} {x<0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {⁇x⁇} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x#0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x#0} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x#0} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x#0} {0<x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x#0} {x<0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x#0} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {0≤x} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {0≤x} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {0≤x} {0≤x} (a ,, pa) (b ,, pb) = ℚ.+-0≤-0≤-implies-0≤ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ a + b
_+ʰᶠ_ {0≤x} {0<x} (a ,, pa) (b ,, pb) = ℚ.+-0≤-0<-implies-0< a b pa pb -- 0 ≤ a → 0 < b → 0 < a + b
_+ʰᶠ_ {0≤x} {x<0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {0≤x} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {0<x} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {0<x} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {0<x} {0≤x} (a ,, pa) (b ,, pb) = ℚ.+-0<-0≤-implies-0< a b pa pb -- 0 < a → 0 ≤ b → 0 < a + b
_+ʰᶠ_ {0<x} {0<x} (a ,, pa) (b ,, pb) = ℚ.+-0<-0<-implies-0< a b pa pb -- 0 < a → 0 < b → 0 < a + b
_+ʰᶠ_ {0<x} {x<0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {0<x} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x<0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x<0} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x<0} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x<0} {0<x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x<0} {x<0} (a ,, pa) (b ,, pb) = ℚ.+-<0-<0-implies-<0 a b pa pb -- a < 0 → b < 0 → (a + b) < 0
_+ʰᶠ_ {x<0} {x≤0} (a ,, pa) (b ,, pb) = ℚ.+-<0-≤0-implies-<0 a b pa pb -- a < 0 → b ≤ 0 → (a + b) < 0
_+ʰᶠ_ {x≤0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x≤0} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x≤0} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x≤0} {0<x} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {x≤0} {x<0} (a ,, pa) (b ,, pb) = ℚ.+-≤0-<0-implies-<0 a b pa pb -- a ≤ 0 → b < 0 → (a + b) < 0
_+ʰᶠ_ {x≤0} {x≤0} (a ,, pa) (b ,, pb) = ℚ.+-≤0-≤0-implies-≤0 a b pa pb -- a ≤ 0 → b ≤ 0 → (a + b) ≤ 0

_+ʰʳ_ : ∀{p q} → (x : Number (isReal , p)) → (y : Number (isReal , q)) → PositivityKindInterpretation isReal (+-Positivityʰ isReal p q) (num x +ʳ num y)
_+ʰʳ_ {⁇x⁇} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {⁇x⁇} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {⁇x⁇} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {⁇x⁇} {0<x} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {⁇x⁇} {x<0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {⁇x⁇} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x#0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x#0} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x#0} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x#0} {0<x} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x#0} {x<0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x#0} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {0≤x} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {0≤x} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {0≤x} {0≤x} (a ,, pa) (b ,, pb) = ℝ.+-0≤-0≤-implies-0≤ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ a + b
_+ʰʳ_ {0≤x} {0<x} (a ,, pa) (b ,, pb) = ℝ.+-0≤-0<-implies-0< a b pa pb -- 0 ≤ a → 0 < b → 0 < a + b
_+ʰʳ_ {0≤x} {x<0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {0≤x} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {0<x} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {0<x} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {0<x} {0≤x} (a ,, pa) (b ,, pb) = ℝ.+-0<-0≤-implies-0< a b pa pb -- 0 < a → 0 ≤ b → 0 < a + b
_+ʰʳ_ {0<x} {0<x} (a ,, pa) (b ,, pb) = ℝ.+-0<-0<-implies-0< a b pa pb -- 0 < a → 0 < b → 0 < a + b
_+ʰʳ_ {0<x} {x<0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {0<x} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x<0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x<0} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x<0} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x<0} {0<x} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x<0} {x<0} (a ,, pa) (b ,, pb) = ℝ.+-<0-<0-implies-<0 a b pa pb -- a < 0 → b < 0 → (a + b) < 0
_+ʰʳ_ {x<0} {x≤0} (a ,, pa) (b ,, pb) = ℝ.+-<0-≤0-implies-<0 a b pa pb -- a < 0 → b ≤ 0 → (a + b) < 0
_+ʰʳ_ {x≤0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x≤0} {x#0} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x≤0} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x≤0} {0<x} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {x≤0} {x<0} (a ,, pa) (b ,, pb) = ℝ.+-≤0-<0-implies-<0 a b pa pb -- a ≤ 0 → b < 0 → (a + b) < 0
_+ʰʳ_ {x≤0} {x≤0} (a ,, pa) (b ,, pb) = ℝ.+-≤0-≤0-implies-≤0 a b pa pb -- a ≤ 0 → b ≤ 0 → (a + b) ≤ 0

_+ʰᶜ_ : ∀{p q} → (x : Number (isComplex , p)) → (y : Number (isComplex , q)) → PositivityKindInterpretation isComplex (+-Positivityʰ isComplex p q) (num x +ᶜ num y)
_+ʰᶜ_ x y = lift tt

_·ʰⁿ_ : ∀{p q} → (x : Number (isNat , p)) → (y : Number (isNat , q)) → PositivityKindInterpretation isNat (·-Positivityʰ isNat p q) (num x ·ⁿ num y)
_·ʰⁿ_ {⁇x⁇} {⁇x⁇} (a ,, pa) (b ,, pb) = tt
_·ʰⁿ_ {⁇x⁇} {x#0} (a ,, pa) (b ,, pb) = tt
_·ʰⁿ_ {⁇x⁇} {0≤x} (a ,, pa) (b ,, pb) = tt
_·ʰⁿ_ {⁇x⁇} {0<x} (a ,, pa) (b ,, pb) = tt
_·ʰⁿ_ {⁇x⁇} {x≤0} (a ,, pa) (b ,, pb) = tt
_·ʰⁿ_ {x#0} {⁇x⁇} (a ,, pa) (b ,, pb) = tt
_·ʰⁿ_ {x#0} {x#0} (a ,, pa) (b ,, pb) = ℕ.·-#0-#0-implies-#0 a b pa pb -- a # 0 → b # 0 → (a · b) # 0
_·ʰⁿ_ {x#0} {0≤x} (a ,, pa) (b ,, pb) = tt
_·ʰⁿ_ {x#0} {0<x} (a ,, pa) (b ,, pb) = ℕ.·-#0-0<-implies-#0 a b pa pb -- a # 0 → 0 < b → (a · b) # 0
_·ʰⁿ_ {x#0} {x≤0} (a ,, pa) (b ,, pb) = tt
_·ʰⁿ_ {0≤x} {⁇x⁇} (a ,, pa) (b ,, pb) = tt
_·ʰⁿ_ {0≤x} {x#0} (a ,, pa) (b ,, pb) = tt
_·ʰⁿ_ {0≤x} {0≤x} (a ,, pa) (b ,, pb) = ℕ.·-0≤-0≤-implies-0≤ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ (a · b)
_·ʰⁿ_ {0≤x} {0<x} (a ,, pa) (b ,, pb) = ℕ.·-0≤-0<-implies-0≤ a b pa pb -- 0 ≤ a → 0 < b → 0 ≤ (a · b)
_·ʰⁿ_ {0≤x} {x≤0} (a ,, pa) (b ,, pb) = ℕ.·-0≤-≤0-implies-≤0 a b pa pb -- 0 ≤ a → b ≤ 0 → (a · b) ≤ 0
_·ʰⁿ_ {0<x} {⁇x⁇} (a ,, pa) (b ,, pb) = tt
_·ʰⁿ_ {0<x} {x#0} (a ,, pa) (b ,, pb) = ℕ.·-0<-#0-implies-#0 a b pa pb -- 0 < a → b # 0 → (a · b) # 0
_·ʰⁿ_ {0<x} {0≤x} (a ,, pa) (b ,, pb) = ℕ.·-0<-0≤-implies-0≤ a b pa pb -- 0 < a → 0 ≤ b → 0 ≤ (a · b)
_·ʰⁿ_ {0<x} {0<x} (a ,, pa) (b ,, pb) = ℕ.·-0<-0<-implies-0< a b pa pb -- 0 < a → 0 < b → 0 < (a · b)
_·ʰⁿ_ {0<x} {x≤0} (a ,, pa) (b ,, pb) = ℕ.·-0<-≤0-implies-≤0 a b pa pb -- 0 < a → b ≤ 0 → (a · b) ≤ 0
_·ʰⁿ_ {x≤0} {⁇x⁇} (a ,, pa) (b ,, pb) = tt
_·ʰⁿ_ {x≤0} {x#0} (a ,, pa) (b ,, pb) = tt
_·ʰⁿ_ {x≤0} {0≤x} (a ,, pa) (b ,, pb) = ℕ.·-≤0-0≤-implies-≤0 a b pa pb -- a ≤ 0 → 0 ≤ b → (a · b) ≤ 0
_·ʰⁿ_ {x≤0} {0<x} (a ,, pa) (b ,, pb) = ℕ.·-≤0-0<-implies-≤0 a b pa pb -- a ≤ 0 → 0 < b → (a · b) ≤ 0
_·ʰⁿ_ {x≤0} {x≤0} (a ,, pa) (b ,, pb) = ℕ.·-≤0-≤0-implies-0≤ a b pa pb -- a ≤ 0 → b ≤ 0 → 0 ≤ (a · b)

_·ʰᶻ_ : ∀{p q} → (x : Number (isInt , p)) → (y : Number (isInt , q)) → PositivityKindInterpretation isInt (·-Positivityʰ isInt p q) (num x ·ᶻ num y)
_·ʰᶻ_ {⁇x⁇} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {⁇x⁇} {x#0} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {⁇x⁇} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {⁇x⁇} {0<x} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {⁇x⁇} {x<0} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {⁇x⁇} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {x#0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {x#0} {x#0} (a ,, pa) (b ,, pb) = ℤ.·-#0-#0-implies-#0 a b pa pb -- a # 0 → b # 0 → (a · b) # 0
_·ʰᶻ_ {x#0} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {x#0} {0<x} (a ,, pa) (b ,, pb) = ℤ.·-#0-0<-implies-#0 a b pa pb -- a # 0 → 0 < b → (a · b) # 0
_·ʰᶻ_ {x#0} {x<0} (a ,, pa) (b ,, pb) = ℤ.·-#0-<0-implies-#0 a b pa pb -- a # 0 → b < 0 → (a · b) # 0
_·ʰᶻ_ {x#0} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {0≤x} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {0≤x} {x#0} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {0≤x} {0≤x} (a ,, pa) (b ,, pb) = ℤ.·-0≤-0≤-implies-0≤ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ (a · b)
_·ʰᶻ_ {0≤x} {0<x} (a ,, pa) (b ,, pb) = ℤ.·-0≤-0<-implies-0≤ a b pa pb -- 0 ≤ a → 0 < b → 0 ≤ (a · b)
_·ʰᶻ_ {0≤x} {x<0} (a ,, pa) (b ,, pb) = ℤ.·-0≤-<0-implies-≤0 a b pa pb -- 0 ≤ a → b < 0 → (a · b) ≤ 0
_·ʰᶻ_ {0≤x} {x≤0} (a ,, pa) (b ,, pb) = ℤ.·-0≤-≤0-implies-≤0 a b pa pb -- 0 ≤ a → b ≤ 0 → (a · b) ≤ 0
_·ʰᶻ_ {0<x} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {0<x} {x#0} (a ,, pa) (b ,, pb) = ℤ.·-0<-#0-implies-#0 a b pa pb -- 0 < a → b # 0 → (a · b) # 0
_·ʰᶻ_ {0<x} {0≤x} (a ,, pa) (b ,, pb) = ℤ.·-0<-0≤-implies-0≤ a b pa pb -- 0 < a → 0 ≤ b → 0 ≤ (a · b)
_·ʰᶻ_ {0<x} {0<x} (a ,, pa) (b ,, pb) = ℤ.·-0<-0<-implies-0< a b pa pb -- 0 < a → 0 < b → 0 < (a · b)
_·ʰᶻ_ {0<x} {x<0} (a ,, pa) (b ,, pb) = ℤ.·-0<-<0-implies-<0 a b pa pb -- 0 < a → b < 0 → (a · b) < 0
_·ʰᶻ_ {0<x} {x≤0} (a ,, pa) (b ,, pb) = ℤ.·-0<-≤0-implies-≤0 a b pa pb -- 0 < a → b ≤ 0 → (a · b) ≤ 0
_·ʰᶻ_ {x<0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {x<0} {x#0} (a ,, pa) (b ,, pb) = ℤ.·-<0-#0-implies-#0 a b pa pb -- a < 0 → b # 0 → (a · b) # 0
_·ʰᶻ_ {x<0} {0≤x} (a ,, pa) (b ,, pb) = ℤ.·-<0-0≤-implies-≤0 a b pa pb -- a < 0 → 0 ≤ b → (a · b) ≤ 0
_·ʰᶻ_ {x<0} {0<x} (a ,, pa) (b ,, pb) = ℤ.·-<0-0<-implies-<0 a b pa pb -- a < 0 → 0 < b → (a · b) < 0
_·ʰᶻ_ {x<0} {x<0} (a ,, pa) (b ,, pb) = ℤ.·-<0-<0-implies-0< a b pa pb -- a < 0 → b < 0 → 0 < (a · b)
_·ʰᶻ_ {x<0} {x≤0} (a ,, pa) (b ,, pb) = ℤ.·-<0-≤0-implies-0≤ a b pa pb -- a < 0 → b ≤ 0 → 0 ≤ (a · b)
_·ʰᶻ_ {x≤0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {x≤0} {x#0} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶻ_ {x≤0} {0≤x} (a ,, pa) (b ,, pb) = ℤ.·-≤0-0≤-implies-≤0 a b pa pb -- a ≤ 0 → 0 ≤ b → (a · b) ≤ 0
_·ʰᶻ_ {x≤0} {0<x} (a ,, pa) (b ,, pb) = ℤ.·-≤0-0<-implies-≤0 a b pa pb -- a ≤ 0 → 0 < b → (a · b) ≤ 0
_·ʰᶻ_ {x≤0} {x<0} (a ,, pa) (b ,, pb) = ℤ.·-≤0-<0-implies-0≤ a b pa pb -- a ≤ 0 → b < 0 → 0 ≤ (a · b)
_·ʰᶻ_ {x≤0} {x≤0} (a ,, pa) (b ,, pb) = ℤ.·-≤0-≤0-implies-0≤ a b pa pb -- a ≤ 0 → b ≤ 0 → 0 ≤ (a · b)

_·ʰᶠ_ : ∀{p q} → (x : Number (isRat , p)) → (y : Number (isRat , q)) → PositivityKindInterpretation isRat (·-Positivityʰ isRat p q) (num x ·ᶠ num y)
_·ʰᶠ_ {⁇x⁇} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {⁇x⁇} {x#0} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {⁇x⁇} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {⁇x⁇} {0<x} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {⁇x⁇} {x<0} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {⁇x⁇} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {x#0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {x#0} {x#0} (a ,, pa) (b ,, pb) = ℚ.·-#0-#0-implies-#0 a b pa pb -- a # 0 → b # 0 → (a · b) # 0
_·ʰᶠ_ {x#0} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {x#0} {0<x} (a ,, pa) (b ,, pb) = ℚ.·-#0-0<-implies-#0 a b pa pb -- a # 0 → 0 < b → (a · b) # 0
_·ʰᶠ_ {x#0} {x<0} (a ,, pa) (b ,, pb) = ℚ.·-#0-<0-implies-#0 a b pa pb -- a # 0 → b < 0 → (a · b) # 0
_·ʰᶠ_ {x#0} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {0≤x} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {0≤x} {x#0} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {0≤x} {0≤x} (a ,, pa) (b ,, pb) = ℚ.·-0≤-0≤-implies-0≤ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ (a · b)
_·ʰᶠ_ {0≤x} {0<x} (a ,, pa) (b ,, pb) = ℚ.·-0≤-0<-implies-0≤ a b pa pb -- 0 ≤ a → 0 < b → 0 ≤ (a · b)
_·ʰᶠ_ {0≤x} {x<0} (a ,, pa) (b ,, pb) = ℚ.·-0≤-<0-implies-≤0 a b pa pb -- 0 ≤ a → b < 0 → (a · b) ≤ 0
_·ʰᶠ_ {0≤x} {x≤0} (a ,, pa) (b ,, pb) = ℚ.·-0≤-≤0-implies-≤0 a b pa pb -- 0 ≤ a → b ≤ 0 → (a · b) ≤ 0
_·ʰᶠ_ {0<x} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {0<x} {x#0} (a ,, pa) (b ,, pb) = ℚ.·-0<-#0-implies-#0 a b pa pb -- 0 < a → b # 0 → (a · b) # 0
_·ʰᶠ_ {0<x} {0≤x} (a ,, pa) (b ,, pb) = ℚ.·-0<-0≤-implies-0≤ a b pa pb -- 0 < a → 0 ≤ b → 0 ≤ (a · b)
_·ʰᶠ_ {0<x} {0<x} (a ,, pa) (b ,, pb) = ℚ.·-0<-0<-implies-0< a b pa pb -- 0 < a → 0 < b → 0 < (a · b)
_·ʰᶠ_ {0<x} {x<0} (a ,, pa) (b ,, pb) = ℚ.·-0<-<0-implies-<0 a b pa pb -- 0 < a → b < 0 → (a · b) < 0
_·ʰᶠ_ {0<x} {x≤0} (a ,, pa) (b ,, pb) = ℚ.·-0<-≤0-implies-≤0 a b pa pb -- 0 < a → b ≤ 0 → (a · b) ≤ 0
_·ʰᶠ_ {x<0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {x<0} {x#0} (a ,, pa) (b ,, pb) = ℚ.·-<0-#0-implies-#0 a b pa pb -- a < 0 → b # 0 → (a · b) # 0
_·ʰᶠ_ {x<0} {0≤x} (a ,, pa) (b ,, pb) = ℚ.·-<0-0≤-implies-≤0 a b pa pb -- a < 0 → 0 ≤ b → (a · b) ≤ 0
_·ʰᶠ_ {x<0} {0<x} (a ,, pa) (b ,, pb) = ℚ.·-<0-0<-implies-<0 a b pa pb -- a < 0 → 0 < b → (a · b) < 0
_·ʰᶠ_ {x<0} {x<0} (a ,, pa) (b ,, pb) = ℚ.·-<0-<0-implies-0< a b pa pb -- a < 0 → b < 0 → 0 < (a · b)
_·ʰᶠ_ {x<0} {x≤0} (a ,, pa) (b ,, pb) = ℚ.·-<0-≤0-implies-0≤ a b pa pb -- a < 0 → b ≤ 0 → 0 ≤ (a · b)
_·ʰᶠ_ {x≤0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {x≤0} {x#0} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶠ_ {x≤0} {0≤x} (a ,, pa) (b ,, pb) = ℚ.·-≤0-0≤-implies-≤0 a b pa pb -- a ≤ 0 → 0 ≤ b → (a · b) ≤ 0
_·ʰᶠ_ {x≤0} {0<x} (a ,, pa) (b ,, pb) = ℚ.·-≤0-0<-implies-≤0 a b pa pb -- a ≤ 0 → 0 < b → (a · b) ≤ 0
_·ʰᶠ_ {x≤0} {x<0} (a ,, pa) (b ,, pb) = ℚ.·-≤0-<0-implies-0≤ a b pa pb -- a ≤ 0 → b < 0 → 0 ≤ (a · b)
_·ʰᶠ_ {x≤0} {x≤0} (a ,, pa) (b ,, pb) = ℚ.·-≤0-≤0-implies-0≤ a b pa pb -- a ≤ 0 → b ≤ 0 → 0 ≤ (a · b)

_·ʰʳ_ : ∀{p q} → (x : Number (isReal , p)) → (y : Number (isReal , q)) → PositivityKindInterpretation isReal (·-Positivityʰ isReal p q) (num x ·ʳ num y)
_·ʰʳ_ {⁇x⁇} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {⁇x⁇} {x#0} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {⁇x⁇} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {⁇x⁇} {0<x} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {⁇x⁇} {x<0} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {⁇x⁇} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {x#0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {x#0} {x#0} (a ,, pa) (b ,, pb) = ℝ.·-#0-#0-implies-#0 a b pa pb -- a # 0 → b # 0 → (a · b) # 0
_·ʰʳ_ {x#0} {0≤x} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {x#0} {0<x} (a ,, pa) (b ,, pb) = ℝ.·-#0-0<-implies-#0 a b pa pb -- a # 0 → 0 < b → (a · b) # 0
_·ʰʳ_ {x#0} {x<0} (a ,, pa) (b ,, pb) = ℝ.·-#0-<0-implies-#0 a b pa pb -- a # 0 → b < 0 → (a · b) # 0
_·ʰʳ_ {x#0} {x≤0} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {0≤x} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {0≤x} {x#0} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {0≤x} {0≤x} (a ,, pa) (b ,, pb) = ℝ.·-0≤-0≤-implies-0≤ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ (a · b)
_·ʰʳ_ {0≤x} {0<x} (a ,, pa) (b ,, pb) = ℝ.·-0≤-0<-implies-0≤ a b pa pb -- 0 ≤ a → 0 < b → 0 ≤ (a · b)
_·ʰʳ_ {0≤x} {x<0} (a ,, pa) (b ,, pb) = ℝ.·-0≤-<0-implies-≤0 a b pa pb -- 0 ≤ a → b < 0 → (a · b) ≤ 0
_·ʰʳ_ {0≤x} {x≤0} (a ,, pa) (b ,, pb) = ℝ.·-0≤-≤0-implies-≤0 a b pa pb -- 0 ≤ a → b ≤ 0 → (a · b) ≤ 0
_·ʰʳ_ {0<x} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {0<x} {x#0} (a ,, pa) (b ,, pb) = ℝ.·-0<-#0-implies-#0 a b pa pb -- 0 < a → b # 0 → (a · b) # 0
_·ʰʳ_ {0<x} {0≤x} (a ,, pa) (b ,, pb) = ℝ.·-0<-0≤-implies-0≤ a b pa pb -- 0 < a → 0 ≤ b → 0 ≤ (a · b)
_·ʰʳ_ {0<x} {0<x} (a ,, pa) (b ,, pb) = ℝ.·-0<-0<-implies-0< a b pa pb -- 0 < a → 0 < b → 0 < (a · b)
_·ʰʳ_ {0<x} {x<0} (a ,, pa) (b ,, pb) = ℝ.·-0<-<0-implies-<0 a b pa pb -- 0 < a → b < 0 → (a · b) < 0
_·ʰʳ_ {0<x} {x≤0} (a ,, pa) (b ,, pb) = ℝ.·-0<-≤0-implies-≤0 a b pa pb -- 0 < a → b ≤ 0 → (a · b) ≤ 0
_·ʰʳ_ {x<0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {x<0} {x#0} (a ,, pa) (b ,, pb) = ℝ.·-<0-#0-implies-#0 a b pa pb -- a < 0 → b # 0 → (a · b) # 0
_·ʰʳ_ {x<0} {0≤x} (a ,, pa) (b ,, pb) = ℝ.·-<0-0≤-implies-≤0 a b pa pb -- a < 0 → 0 ≤ b → (a · b) ≤ 0
_·ʰʳ_ {x<0} {0<x} (a ,, pa) (b ,, pb) = ℝ.·-<0-0<-implies-<0 a b pa pb -- a < 0 → 0 < b → (a · b) < 0
_·ʰʳ_ {x<0} {x<0} (a ,, pa) (b ,, pb) = ℝ.·-<0-<0-implies-0< a b pa pb -- a < 0 → b < 0 → 0 < (a · b)
_·ʰʳ_ {x<0} {x≤0} (a ,, pa) (b ,, pb) = ℝ.·-<0-≤0-implies-0≤ a b pa pb -- a < 0 → b ≤ 0 → 0 ≤ (a · b)
_·ʰʳ_ {x≤0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {x≤0} {x#0} (a ,, pa) (b ,, pb) = lift tt
_·ʰʳ_ {x≤0} {0≤x} (a ,, pa) (b ,, pb) = ℝ.·-≤0-0≤-implies-≤0 a b pa pb -- a ≤ 0 → 0 ≤ b → (a · b) ≤ 0
_·ʰʳ_ {x≤0} {0<x} (a ,, pa) (b ,, pb) = ℝ.·-≤0-0<-implies-≤0 a b pa pb -- a ≤ 0 → 0 < b → (a · b) ≤ 0
_·ʰʳ_ {x≤0} {x<0} (a ,, pa) (b ,, pb) = ℝ.·-≤0-<0-implies-0≤ a b pa pb -- a ≤ 0 → b < 0 → 0 ≤ (a · b)
_·ʰʳ_ {x≤0} {x≤0} (a ,, pa) (b ,, pb) = ℝ.·-≤0-≤0-implies-0≤ a b pa pb -- a ≤ 0 → b ≤ 0 → 0 ≤ (a · b)

_·ʰᶜ_ : ∀{p q} → (x : Number (isComplex , p)) → (y : Number (isComplex , q)) → PositivityKindInterpretation isComplex (·-Positivityʰ isComplex p q) (num x ·ᶜ num y)
_·ʰᶜ_ {⁇x⁇} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶜ_ {⁇x⁇} {x#0} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶜ_ {x#0} {⁇x⁇} (a ,, pa) (b ,, pb) = lift tt
_·ʰᶜ_ {x#0} {x#0} (a ,, pa) (b ,, pb) = ℂ.·-#0-#0-implies-#0 a b pa pb -- a # 0 → b # 0 → (a · b) # 0


open PatternsType

-- abs x = max x (- x)

abs : ∀{l p} → (x : Number (l , p)) → abs-Types x
abs {isNat    } {X  } (x ,, p) = (absⁿ x ,, 0≤xⁿ x)
abs {isNat    } {X⁺⁻} (x ,, p) = (absⁿ x ,, ℕ.0≤-#0-implies-0< x (0≤xⁿ x) p)
abs {isNat    } {X₀⁺} (x ,, p) = (absⁿ x ,, p)
abs {isNat    } {X⁺ } (x ,, p) = (absⁿ x ,, p)
abs {isNat    } {X₀⁻} (x ,, p) = (absⁿ x ,, (0ⁿ , (sym $ ≤0→≡0 p)))
abs {isInt    } {X  } (x ,, p) = (absᶻ x ,, {!!}) -- ∀ x → 0 ≤ abs x
abs {isInt    } {X⁺⁻} (x ,, p) = (absᶻ x ,, {!!}) -- ∀ x → x # 0 → 0 < abs x
abs {isInt    } {X₀⁺} (x ,, p) = (absᶻ x ,, {!!}) -- ∀ x → 0 ≤ abs x
abs {isInt    } {X⁺ } (x ,, p) = (absᶻ x ,, {!!}) -- ∀ x → 0 < x → 0 < abs x
abs {isInt    } {X⁻ } (x ,, p) = (absᶻ x ,, {!!}) -- ∀ x → x < 0 → 0 < abs x
abs {isInt    } {X₀⁻} (x ,, p) = (absᶻ x ,, {!!}) -- ∀ x → 0 ≤ abs x
abs {isRat    } {X  } (x ,, p) = (absᶠ x ,, {!!}) -- ∀ x → 0 ≤ abs x
abs {isRat    } {X⁺⁻} (x ,, p) = (absᶠ x ,, {!!}) -- ∀ x → x # 0 → 0 < abs x
abs {isRat    } {X₀⁺} (x ,, p) = (absᶠ x ,, {!!}) -- ∀ x → 0 ≤ abs x
abs {isRat    } {X⁺ } (x ,, p) = (absᶠ x ,, {!!}) -- ∀ x → 0 < x → 0 < abs x
abs {isRat    } {X⁻ } (x ,, p) = (absᶠ x ,, {!!}) -- ∀ x → x < 0 → 0 < abs x
abs {isRat    } {X₀⁻} (x ,, p) = (absᶠ x ,, {!!}) -- ∀ x → 0 ≤ abs x
abs {isReal   } {X  } (x ,, p) = (absʳ x ,, {!!}) -- ∀ x → 0 ≤ abs x
abs {isReal   } {X⁺⁻} (x ,, p) = (absʳ x ,, {!!}) -- ∀ x → x # 0 → 0 < abs x
abs {isReal   } {X₀⁺} (x ,, p) = (absʳ x ,, {!!}) -- ∀ x → 0 ≤ abs x
abs {isReal   } {X⁺ } (x ,, p) = (absʳ x ,, {!!}) -- ∀ x → 0 < x → 0 < abs x
abs {isReal   } {X⁻ } (x ,, p) = (absʳ x ,, {!!}) -- ∀ x → x < 0 → 0 < abs x
abs {isReal   } {X₀⁻} (x ,, p) = (absʳ x ,, {!!}) -- ∀ x → 0 ≤ abs x
abs {isComplex} {X  } (x ,, p) = (absᶜ x ,, 0≤abs x)
abs {isComplex} {X⁺⁻} (x ,, p) = (absᶜ x ,, γ) where
  pʳ = ℂ.0≤abs x
  γ : 0ʳ <ʳ absᶜ x
  γ =  ℝ.0≤-#0-implies-0< (absᶜ x) pʳ (ℂ.abs-preserves-#0 x p)


-- a < b → ¬(b ≤ a) = ¬¬(a < b)

-- 0≤abs       : ∀ x → 0ʳ ≤ʳ abs x
-- abs-preserves-0 : ∀ x → x ≡ 0f → abs x ≡ 0ʳ
-- abs-reflects-0  : ∀ x → abs x ≡ 0ʳ → x ≡ 0f
-- abs-preserves-· : ∀ x y → abs (x · y) ≡ (abs x) ·ʳ (abs y)
-- #-tight : ∀ x y → ¬(x # y) → x ≡ y
-- a ≤ b = ¬(b < a)
