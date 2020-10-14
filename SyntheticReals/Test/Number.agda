{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module SyntheticReals.Test.Number where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base -- Rel
open import Cubical.Data.Unit.Base -- Unit
open import Cubical.Data.Empty -- ⊥
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
open import Function.Base using (it; _∋_; _$_)

-- open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ₙ_)
-- open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
-- open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_)
-- open import Cubical.Data.Fin.Base
-- import Cubical.Data.Fin.Properties
-- open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
-- open import Cubical.Data.Nat.Properties using (+-suc; injSuc; snotz; +-comm; +-assoc; +-zero; inj-m+)
-- open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_; _≟_ to _≟ₙ_)
-- open import Data.Nat.Base using (ℕ; z≤n; s≤s; zero; suc) renaming (_≤_ to _≤ₙ_; _<_ to _<ₙ_; _+_ to _+ₙ_)
-- open import Agda.Builtin.Bool renaming (true to TT; false to FF)
-- import Cubical.Data.Fin.Properties
-- open import Data.Nat.Properties using (+-mono-<)

-- open import Bundles

open import SyntheticReals.Number.Postulates
open import SyntheticReals.Number.Structures
open import SyntheticReals.Number.Bundles
open import SyntheticReals.Number.Inclusions
open import SyntheticReals.Number.Base
open import SyntheticReals.Number.Coercions
open import SyntheticReals.Number.Operations

open ℕⁿ
open ℤᶻ
open ℚᶠ
open ℝʳ
open ℂᶜ

import Data.Nat.Properties


-- NOTE: well, for 15 allowed coercions, we might just enumerate them
--   unfortunately with overlapping patterns a style as in `Cl` is not possible
--   we need to explicitly write out all the 5×5 combinations
--   or, we implement a min operator which might work even with overlapping patterns

-- num {isNat     ,, p} (x ,, q) = x
-- num {isInt     ,, p} (x ,, q) = x
-- num {isRat     ,, p} (x ,, q) = x
-- num {isReal    ,, p} (x ,, q) = x
-- num {isComplex ,, p} (x ,, q) = x


-- TODO: name this "inject" instead of "coerce"
-- TODO: make the module ℤ and the Carrier ℤ.ℤ
-- TODO: for a binary relation `a # b` it would be nice to have a way to compose ≡-pathes to the left and the right
--       similar to how ∙ can be used for pathes
--       this reasoning might extend to transitive relations
--       `cong₂ _#_ refl x` and `cong₂ _#_ x refl` to this (together with `transport`)
-- NOTE: maybe ℕ↪ℤ should be a postfix operation

-- module _ where
-- module ℕ' = ROrderedCommSemiring ℕ.Bundle
-- module ℤ' = ROrderedCommRing     ℤ.Bundle
-- module ℚ' = ROrderedField        ℚ.Bundle
-- module ℝ' = ROrderedField        ℝ.Bundle
-- module ℂ' = RField               ℂ.Bundle--



-- coerce-OCSR : ∀{l p} {ll : NumberKind} {𝕏OCSR 𝕐OCSR : ROrderedCommSemiring {ℝℓ} {ℝℓ'}}
--             → (x : Number (l ,, p))
--             → {f : Il l → Il ll}
--             → IsROrderedCommSemiringInclusion 𝕏OCSR 𝕐OCSR f
--             → Ip ll p (f (num x))
-- coerce-OCSR {l} {ll} {p} {𝕏OCSR} {𝕐OCSR} {f} (x ,, q) = ?

{-
private
  instance
    z≤n' : ∀ {n}                 → zero  ≤ₙ n
    z≤n' {n} = z≤n
    s≤s' : ∀ {m n} {{m≤n : m ≤ₙ n}} → suc m ≤ₙ suc n
    s≤s' {m} {n} {{m≤n}} = s≤s m≤n
-}

{-
-- TODO: why does `it` not work here?
⁻¹-Levels : (a : NumberKind) → Σ[ b ∈ NumberKind ] a ≤ₙₗ b
⁻¹-Levels isNat     = isRat     , z≤n -- it
⁻¹-Levels isInt     = isRat     , s≤s z≤n -- s≤s' {{z≤n'}}
⁻¹-Levels isRat     = isRat     , s≤s (s≤s z≤n)
⁻¹-Levels isReal    = isReal    , s≤s (s≤s (s≤s z≤n)) -- it
⁻¹-Levels isComplex = isComplex , s≤s (s≤s (s≤s (s≤s z≤n)))

⁻¹-Levels' : (a : NumberKind) → NumberKind
⁻¹-Levels' x = maxₙₗ x isRat
-}

open PatternsType

{-
private
  pattern X   = anyPositivity
  pattern X⁺⁻ = isNonzero
  pattern X₀⁺ = isNonnegative
  pattern X⁺  = isPositive
  pattern X⁻  = isNegative
  pattern X₀⁻ = isNonpositive
-}

{-
⁻¹-Types : NumberProp → Maybe NumberProp
⁻¹-Types (level ,, X  ) = nothing
⁻¹-Types (level ,, X₀⁺) = nothing
⁻¹-Types (level ,, X₀⁻) = nothing
⁻¹-Types (level ,, p  ) = just (fst (⁻¹-Levels level) ,, p)
-}

-- ∀{{ q : Unit }} → Number (level ,, X⁺⁻)
-- ∀{{ q : Unit }} → Number (level ,, X⁺ )
-- ∀{{ q : Unit }} → Number (level ,, X⁻ )

-- pattern [ℝ₀⁺] = (isReal , X₀⁺)
-- [ℝ₀⁺] = Number (isReal , isNonnegativeᵒʳ)
-- [ℝ⁺]  = Number (isReal , isPositiveᵒʳ)
-- [ℕ⁺]  = Number (isNat  , isPositiveᵒʳ)
-- [ℝ]   = Number (isReal , anyPositivityᵒʳ)

open import SyntheticReals.Number.Prettyprint

-- {-# DISPLAY maxₙₗ' isReal isReal = isReal #-}
-- {-# DISPLAY Number (isReal , isNonnegative) = [ℝ₀⁺] #-}
-- {-# DISPLAY Number (isReal , isPositive)    = [ℝ⁺]  #-}


[1ʳ] : [ℝ⁺]
[1ʳ] = 1ʳ ,, ℝ.0<1

[1]-Type : (l : NumberKind) → Type (NumberLevel l)
[1]-Type isNat     = [ℕ⁺]
[1]-Type isInt     = [ℤ⁺]
[1]-Type isRat     = [ℚ⁺]
[1]-Type isReal    = [ℝ⁺]
[1]-Type isComplex = [ℂ⁺⁻]

-- NOTE: this is ambiguous with generic operations such as _+_
[1] : ∀{l} → [1]-Type l
[1] {isNat}     = 1ⁿ ,, ℕ.0<1
[1] {isInt}     = 1ᶻ ,, ℤ.0<1
[1] {isRat}     = 1ᶠ ,, ℚ.0<1
[1] {isReal}    = 1ʳ ,, ℝ.0<1
[1] {isComplex} = 1ᶜ ,, ℂ.1#0


-- test101 : Number (isNat , isPositiveᵒʳ) → Number (isReal ,  isNonnegativeᵒʳ) → {!!}

open import Function.Base using (typeOf)


test201 : [ℕ⁺] → [ℝ₀⁺] → [ℝ]
-- As-patterns (or @-patterns) go well with resolving things in our approach
test201 n@(nn ,, np) r@(rn ,, rp) = let
-- generic operations are provided
-- q : [ℕ⁺]
-- z : [ℝ₀⁺]
   q = n + n
   z = r + r

-- we can project-out the underlying number of a `Number` with `num`
-- zʳ : ℝ
   zʳ = num z

-- and we can project-out the property of a `Number` with `prp`
-- zp : 0ʳ ≤ʳ (rn +ʳ rn)
   zp = prp z

-- since the generic `_+_` makes use of `_+ʳ_` on ℝ, we get definitional equality
   _ : zʳ ≡ rn +ʳ rn
   _ = refl

-- we can turn a generic number into a Σ pair with `pop`
-- qʳ   : ℕ₀
-- qʳ   = nn +ⁿ nn
-- qp   : 0ⁿ <ⁿ (nn +ⁿ nn)
-- qp   = +-<-<-implies-<ʳ nn nn np np
   (qʳ , qp) = pop q

-- and we can create a number with `_,,_`
-- this needs some type annotation for help
   q' : typeOf q
   q' = qʳ ,, qp

-- if the two parts of q and q' are in scope, then we get definitional equality
   _ : q ≡ q'
   _ = refl

-- r is nonnegative from [ℝ₀⁺], [1ʳ] is positive from [ℝ⁺]
-- and _+_ makes use of the fact that "positive + nonnegative = positive"
-- y : [ℝ⁺]
-- y = (rn +ʳ 1ʳ) ,, +-≤-<-implies-<ʳ rn 1ʳ rp 0<1
   y =  r + [1ʳ]

-- _+_ automatically coerces n from ℕ⁺ to ℝ⁺
-- and uses the fact that "positive + nonnegative = positive"
-- n+r : [ℝ⁺]
-- n+r = (ℕ↪ℝ nn +ʳ rn) ,, +-<-≤-implies-<ʳ (ℕ↪ℝ nn) rn (coerce-ℕ↪ℝ (nn ,, np)) rp
   n+r = n + r

-- generic relations like _<_ also make use of their underlying relations
-- and therefore we also get definitional equality, no matter how the relation is stated
   pp   : [1ʳ] <      (r  + [1ʳ])
   pp   = {!!}
   pp'  :  1ʳ  <ʳ num (r  + [1ʳ])
   pp'  = {!!}
   pp'' :  1ʳ  <ʳ     (rn +ʳ 1ʳ )
   pp'' = {!!}
   _ : (pp ≡ pp') × (pp ≡ pp'')
   _ = refl , refl
   in {! - [1ʳ]!}


_ = {! ℕ!}


{-

distance : ∀(x y : [ℝ]) → [ℝ]
distance x y = max (x + (- y)) (- (x + (- y)))

IsCauchy : (x : ℕ → ℝ) → Type (ℓ-max ℓ' ℚℓ)
IsCauchy x = ∀(ε : [ℚ⁺]) → ∃[ N ∈ ℕ ] ∀(m n : ℕ) → N ≤ⁿ m → N ≤ⁿ n → distance (x m) (x n) < ε

-}

test : [ℕ⁺] → [ℝ₀⁺] → [ℝ]
test n@(nn ,, np) r@(rn ,, rp) = let
  q : [ℕ⁺]
  q = n + n
  z : [ℝ₀⁺]
  z = r + r
  k : [ℝ⁺]
  k = n + r
  in {!!}
