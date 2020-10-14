{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module SyntheticReals.Number.Instances.QuoInt where

open import Cubical.Foundations.Everything hiding (⋆) renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)

open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool as Bool using (Bool; not; true; false)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_; inl to inlᵖ; inr to inrᵖ)
open import Function.Base using (it; _∋_; _$_)
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation --.Properties

open import SyntheticReals.Utils using (!_; !!_)
open import SyntheticReals.MoreLogic.Reasoning
open import SyntheticReals.MoreLogic.Definitions
open import SyntheticReals.MoreLogic.Properties
open import SyntheticReals.MorePropAlgebra.Definitions hiding (_≤''_)
open import SyntheticReals.MorePropAlgebra.Structures
open import SyntheticReals.MorePropAlgebra.Bundles
open import SyntheticReals.MorePropAlgebra.Consequences
open import SyntheticReals.Number.Structures2
open import SyntheticReals.Number.Bundles2

open import Cubical.Data.Nat.Literals
open import Cubical.Data.Nat using (suc; zero; ℕ; HasFromNat)
open import SyntheticReals.Number.Prelude.Nat using (¬-<ⁿ-zero; +ⁿ-comm; ¬suc<ⁿ0; _+ⁿ_; _·ⁿ_; ·ⁿ-reflects-≡ˡ')
open import SyntheticReals.Number.Instances.QuoIntFromInt public
open import Cubical.HITs.Ints.QuoInt as QuoInt using
  ( ℤ
  ; HasFromNat
  ; _+_
  ; Int≡ℤ
  ; signed
  ; posneg
  ; ℤ→Int
  ; sucℤ
  ; predℤ
  ; sign
  ; abs
  ; pos
  ; neg
  ; +-comm
  ; +-assoc
  ; sucℤ-+ʳ
  ; sucℤ-+ˡ
  ; spos
  ; sneg
  ; *-pos-suc
  ; negate-invol
  ) renaming
  ( isSetℤ to is-set
  ; _*_ to _·_
  ; -_ to infixl 6 -_
  ; *-comm to ·-comm
  )
open IsLinearlyOrderedCommRing is-LinearlyOrderedCommRing using
  ( _-_
  ; <-irrefl
  ; <-trans
  ; +-<-ext
  ; +-rinv
  ; +-identity
  ; ·-identity
  ; _≤_
  ; ·-preserves-<
  ; <-tricho
  ; <-asym
  ; _#_
  ; +-inverse
  ; ·-assoc
  )

0<1 : [ 0 < 1 ]
0<1 = 0 , refl

-- TODO: import these properties from somewhere else
+-reflects-<      : ∀ x y z → [ (x + z < y + z) ⇒ (    x < y    ) ]
+-preserves-<     : ∀ x y z → [ (    x < y    ) ⇒ (x + z < y + z) ]
+-creates-<       : ∀ x y z → [ (    x < y    ) ⇔ (x + z < y + z) ]

+-preserves-< a b x = snd (
  ( a            <  b           ) ⇒ᵖ⟨ transport (λ i → [ sym (fst (+-identity a)) i < sym (fst (+-identity b)) i ]) ⟩
  ( a +    0     <  b +    0    ) ⇒ᵖ⟨ transport (λ i → [ a + sym (+-rinv x) i < b + sym (+-rinv x) i ]) ⟩
  ( a + (x  - x) <  b + (x  - x)) ⇒ᵖ⟨ transport (λ i → [ +-assoc a x (- x) i < +-assoc b x (- x) i ]) ⟩
  ((a +  x) - x  < (b +  x) - x ) ⇒ᵖ⟨ +-<-ext (a + x) (- x) (b + x) (- x) ⟩
  ((a + x < b + x) ⊔ (- x < - x)) ⇒ᵖ⟨ (λ q → case q as (a + x < b + x) ⊔ (- x < - x) ⇒ a + x < b + x of λ
                                      { (inl a+x<b+x) → a+x<b+x -- somehow ⊥-elim needs a hint in the next line
                                      ; (inr  -x<-x ) → ⊥-elim {A = λ _ → [ a + x < b + x ]} (<-irrefl (- x) -x<-x)
                                      }) ⟩
   a + x < b + x ◼ᵖ)

+-reflects-< x y z = snd
  ( x + z < y + z              ⇒ᵖ⟨ +-preserves-< (x + z) (y + z) (- z) ⟩
    (x + z) - z  < (y + z) - z ⇒ᵖ⟨ transport (λ i → [ +-assoc x z (- z) (~ i) < +-assoc y z (- z) (~ i) ]) ⟩
    x + (z - z) < y + (z - z)  ⇒ᵖ⟨ transport (λ i → [ x + +-rinv z i < y + +-rinv z i ]) ⟩
    x + 0 < y + 0              ⇒ᵖ⟨ transport (λ i → [ fst (+-identity x) i < fst (+-identity y) i ]) ⟩
    x < y                      ◼ᵖ)

+-creates-< x y z .fst = +-preserves-< x y z
+-creates-< x y z .snd = +-reflects-<  x y z

suc-creates-< : ∀ x y → [ (x < y) ⇔ (sucℤ x < sucℤ y) ]
suc-creates-< x y .fst p = substₚ (λ p → sucℤ x < p) (∣ +-comm y (pos 1) ∣) $ substₚ (λ p → p < y + pos 1) (∣ +-comm x (pos 1) ∣) (+-preserves-< x y (pos 1) p)
suc-creates-< x y .snd p = +-reflects-< x y (pos 1) $ substₚ (λ p → p < y + pos 1) (∣ +-comm (pos 1) x ∣) $ substₚ (λ p → sucℤ x < p) (∣ +-comm (pos 1) y ∣) p

·-creates-< : ∀ a b x → [ 0 < x ] → [ (a < b) ⇔ ((a · x) < (b · x)) ]
·-creates-< a b x p .fst q = ·-preserves-< a b x p q
·-creates-< a b x p .snd q = ·-reflects-< a b x p q

·-creates-<ˡ : ∀ a b x → [ 0 < x ] → [ (a < b) ⇔ ((x · a) < (x · b)) ]
·-creates-<ˡ a b x p .fst q = transport (λ i → [ ·-comm a x i < ·-comm b x i ]) $ ·-preserves-< a b x p q
·-creates-<ˡ a b x p .snd q = ·-reflects-< a b x p (transport (λ i → [ ·-comm x a i < ·-comm x b i ]) q)

·-creates-<-≡ : ∀ a b x → [ 0 < x ] → (a < b) ≡ ((a · x) < (b · x))
·-creates-<-≡ a b x p = ⇔toPath' (·-creates-< a b x p)

·-creates-<ˡ-≡ : ∀ a b x → [ 0 < x ] → (a < b) ≡ ((x · a) < (x · b))
·-creates-<ˡ-≡ a b x p = ⇔toPath' (·-creates-<ˡ a b x p)

+-creates-≤ : ∀ a b x → [ (a ≤ b) ⇔ ((a + x) ≤ (b + x)) ]
+-creates-≤ a b x = {!   !}

·-creates-≤ : ∀ a b x → [ 0 ≤ x ] → [ (a ≤ b) ⇔ ((a · x) ≤ (b · x)) ]
·-creates-≤ a b x 0≤x .fst p = {!   !}
·-creates-≤ a b x 0≤x .snd p = {!   !}

·-creates-≤-≡ : ∀ a b x → [ 0 ≤ x ] → (a ≤ b) ≡ ((a · x) ≤ (b · x))
·-creates-≤-≡ a b x 0≤x = uncurry ⇔toPath $ ·-creates-≤ a b x 0≤x

≤-dicho : ∀ x y → [ (x ≤ y) ⊔ (y ≤ x) ]
≤-dicho x y with <-tricho x y
... | inl (inl x<y) = inlᵖ $ <-asym x y x<y
... | inl (inr y<x) = inrᵖ $ <-asym y x y<x
... | inr      x≡y  = inlᵖ $ subst (λ p → [ ¬(p < x) ]) x≡y (<-irrefl x)

ℤlattice : Lattice {ℓ-zero} {ℓ-zero}
ℤlattice = record { LinearlyOrderedCommRing bundle renaming (≤-Lattice to is-Lattice) }

open import SyntheticReals.MorePropAlgebra.Properties.Lattice ℤlattice
open OnSet is-set hiding (+-min-distribʳ; ·-min-distribʳ; +-max-distribʳ; ·-max-distribʳ)

≤-min-+ : ∀ a b c w → [ w ≤ (a + c) ] → [ w ≤ (b + c) ] → [ w ≤ (min a b + c) ]
≤-max-+ : ∀ a b c w → [ (a + c) ≤ w ] → [ (b + c) ≤ w ] → [ (max a b + c) ≤ w ]
≤-min-· : ∀ a b c w → [ w ≤ (a · c) ] → [ w ≤ (b · c) ] → [ w ≤ (min a b · c) ]
≤-max-· : ∀ a b c w → [ (a · c) ≤ w ] → [ (b · c) ≤ w ] → [ (max a b · c) ≤ w ]

≤-min-+ = OnType.≤-dicho⇒+.≤-min-+ _+_ ≤-dicho
≤-max-+ = OnType.≤-dicho⇒+.≤-max-+ _+_ ≤-dicho
≤-min-· = OnType.≤-dicho⇒·.≤-min-· _·_ ≤-dicho
≤-max-· = OnType.≤-dicho⇒·.≤-max-· _·_ ≤-dicho

+-min-distribʳ : ∀ x y z             → (min x y + z) ≡ min (x + z) (y + z)
·-min-distribʳ : ∀ x y z → [ 0 ≤ z ] → (min x y · z) ≡ min (x · z) (y · z)
+-max-distribʳ : ∀ x y z             → (max x y + z) ≡ max (x + z) (y + z)
·-max-distribʳ : ∀ x y z → [ 0 ≤ z ] → (max x y · z) ≡ max (x · z) (y · z)
+-min-distribˡ : ∀ x y z             → (z + min x y) ≡ min (z + x) (z + y)
·-min-distribˡ : ∀ x y z → [ 0 ≤ z ] → (z · min x y) ≡ min (z · x) (z · y)
+-max-distribˡ : ∀ x y z             → (z + max x y) ≡ max (z + x) (z + y)
·-max-distribˡ : ∀ x y z → [ 0 ≤ z ] → (z · max x y) ≡ max (z · x) (z · y)

+-min-distribʳ = OnSet.+-min-distribʳ is-set _+_ +-creates-≤ ≤-min-+
·-min-distribʳ = OnSet.·-min-distribʳ is-set 0 _·_ ·-creates-≤ ≤-min-·
+-max-distribʳ = OnSet.+-max-distribʳ is-set _+_ +-creates-≤ ≤-max-+
·-max-distribʳ = OnSet.·-max-distribʳ is-set 0 _·_ ·-creates-≤ ≤-max-·

+-min-distribˡ x y z   = +-comm z (min x y) ∙ +-min-distribʳ x y z   ∙ (λ i → min (+-comm x z i) (+-comm y z i))
·-min-distribˡ x y z p = ·-comm z (min x y) ∙ ·-min-distribʳ x y z p ∙ (λ i → min (·-comm x z i) (·-comm y z i))
+-max-distribˡ x y z   = +-comm z (max x y) ∙ +-max-distribʳ x y z   ∙ (λ i → max (+-comm x z i) (+-comm y z i))
·-max-distribˡ x y z p = ·-comm z (max x y) ∙ ·-max-distribʳ x y z p ∙ (λ i → max (·-comm x z i) (·-comm y z i))

pos<pos[suc] : ∀ x → [ pos x < pos (suc x) ]
pos<pos[suc] 0 = 0<1
pos<pos[suc] (suc x) = suc-creates-< (pos x) (pos (suc x)) .fst (pos<pos[suc] x)

0<ᶻpos[suc] : ∀ x → [ 0 < pos (suc x) ]
0<ᶻpos[suc]      0  = 0<1
0<ᶻpos[suc] (suc x) = <-trans 0 (pos (suc x)) (pos (suc (suc x))) (0<ᶻpos[suc] x) (suc-creates-< (pos x) (pos (suc x)) .fst (pos<pos[suc] x))

·-nullifiesˡ : ∀(x : ℤ) → 0 · x ≡ 0
·-nullifiesˡ (pos zero) = refl
·-nullifiesˡ (neg zero) = refl
·-nullifiesˡ (posneg i) = refl
·-nullifiesˡ (pos (suc n)) = refl
·-nullifiesˡ (neg (suc n)) = sym posneg

·-nullifiesʳ : ∀(x : ℤ) → x · 0 ≡ 0
·-nullifiesʳ x = ·-comm x 0 ∙ ·-nullifiesˡ x

·-preserves-0< : ∀ a b → [ 0 < a ] → [ 0 < b ] → [ 0 < a · b ]
·-preserves-0< a b p q = subst (λ p → [ p < a · b ]) (·-nullifiesˡ b) (·-preserves-< 0 a b q p)

private
  term : ∀ b x → Type ℓ-zero
  term b x = [ ((pos 0 < x) ⇒ (pos 0 < b)) ⊓ ((pos 0 < b) ⇒ (pos 0 < x)) ]

·-reflects-<ˡ : (x y z : ℤ) → [ pos 0 < z ] → [ z · x < z · y ] → [ x < y ]
·-reflects-<ˡ x y z p q = ·-reflects-< x y z p  (transport (λ i → [ ·-comm z x i < ·-comm z y i ]) q)

-flips-<0 : ∀ x → [ (x < 0) ⇔ (0 < (- x)) ]
-flips-<0 (signed spos zero) = (λ x → x) , (λ x → x)
-flips-<0 (signed sneg zero) = (λ x → x) , (λ x → x)
-flips-<0 (ℤ.posneg i)       = (λ x → x) , (λ x → x)
-flips-<0 (signed spos (suc n)) .fst p  = ¬-<ⁿ-zero p
-flips-<0 (signed sneg (suc n)) .fst tt = n , +ⁿ-comm n 1
-flips-<0 (signed sneg (suc n)) .snd p  = tt

-- NOTE: this could be a path, if we make `+-creates-<` into a path
-flips-< : ∀ x y → [ x < y ] → [ - y < - x ]
-flips-< x y p = (
  (    x            < y    ) ⇒ᵖ⟨ +-creates-< x y (- y) .fst ⟩
  (    x  - y       < y - y) ⇒ᵖ⟨ transport (λ i → [ +-comm x (- y) i < +-rinv y i ]) ⟩
  ( (- y) + x       < 0    ) ⇒ᵖ⟨ +-creates-< ((- y) + x) 0 (- x) .fst ⟩
  (((- y) + x) - x  < 0 - x) ⇒ᵖ⟨ transport (λ i → [ +-assoc (- y) x (- x) (~ i) < +-identity (- x) .snd i ]) ⟩
  ( (- y) + (x - x) < - x  ) ⇒ᵖ⟨ transport (λ i → [ (- y) + +-rinv x i < - x ]) ⟩
  ( (- y) +    0    < - x  ) ⇒ᵖ⟨ transport (λ i → [ +-identity (- y) .fst i < - x ]) ⟩
  (  - y            < - x  ) ◼ᵖ) .snd p

-flips-<-⇔ : ∀ x y → [ (x < y) ⇔ (- y < - x) ]
-flips-<-⇔ x y .fst = -flips-< x y
-flips-<-⇔ x y .snd p = transport (λ i → [ negate-invol x i < negate-invol y i ]) $ -flips-< (- y) (- x) p

-flips-<-≡ : ∀ x y → (x < y) ≡ (- y < - x)
-flips-<-≡ x y = ⇔toPath' (-flips-<-⇔ x y)

-identity-· : ∀ a → (- 1) · a ≡ - a
-identity-· (pos zero) j = posneg (~ i0 ∨ ~ j)
-identity-· (neg zero) j = posneg (~ i1 ∨ ~ j)
-identity-· (posneg i) j = posneg (~ i  ∨ ~ j)
-identity-· (pos (suc n)) i = neg (suc (+ⁿ-comm n 0 i))
-identity-· (neg (suc n)) i = pos (suc (+ⁿ-comm n 0 i))

-distˡ : ∀ a b → -(a · b) ≡ (- a) · b
-distˡ a b =
  -(a · b)        ≡⟨ sym $ -identity-· (a · b) ⟩
  (- 1) · (a · b) ≡⟨ ·-assoc (- 1) a b ⟩
  ((- 1) · a) · b ≡⟨ (λ i → -identity-· a i · b) ⟩
  (- a) · b       ∎

private
  lem : ∀ z → [ z < 0 ] → [ 0 < - z ]
  lem z p = subst (λ p → [ p < - z ]) (sym posneg) $ -flips-< z 0 p

·-creates-<-flippedˡ-≡ : (x y z : ℤ) → [ z < 0 ] → (z · x < z · y) ≡ (y < x)
·-creates-<-flippedˡ-≡ x y z p =
     z  · x  <    z ·  y  ≡⟨ -flips-<-≡ (z · x) (z · y) ⟩
  - (z  · y) < - (z ·  x) ≡⟨ (λ i → -distˡ z y i < -distˡ z x i) ⟩
  (- z) · y  < (- z) · x  ≡⟨ sym $ ·-creates-<ˡ-≡ y x (- z) (lem z p) ⟩
          y  <         x  ∎

·-creates-<-flippedʳ-≡ : (x y z : ℤ) → [ z < 0 ] → (x · z < y · z) ≡ (y < x)
·-creates-<-flippedʳ-≡ x y z p = (λ i → ·-comm x z i < ·-comm y z i) ∙ ·-creates-<-flippedˡ-≡ x y z p

·-reflects-<-flippedˡ : (x y z : ℤ) → [ z < 0 ] → [ z · x < z · y ] → [ y < x ]
·-reflects-<-flippedˡ x y z p q = pathTo⇒ (·-creates-<-flippedˡ-≡ x y z p) q
  --   (z  · x  <    z ·  y  ⇒ᵖ⟨ -flips-< (z · x) (z · y) ⟩
  -- - (z  · y) < - (z ·  x) ⇒ᵖ⟨ transport (λ i → [ -distˡ z y i < -distˡ z x i ]) ⟩
  -- (- z) · y  < (- z) · x  ⇒ᵖ⟨ ·-creates-<ˡ y x (- z) (lem z p) .snd ⟩
  --         y  <         x  ◼ᵖ) .snd q

·-reflects-<-flippedʳ : (x y z : ℤ) → [ z < 0 ] → [ x · z < y · z ] → [ y < x ]
·-reflects-<-flippedʳ x y z p q = ·-reflects-<-flippedˡ x y z p (transport (λ i → [ ·-comm x z i < ·-comm y z i ]) q)

-- ·-preserves-<-flippedˡ : (x y z : ℤ) → [ z < 0 ] → [ x < y ] → [ z · y < z · x ]
-- ·-preserves-<-flippedˡ x y z p q = {!   !}

·-reflects-0< : ∀ a b → [ 0 < a · b ] → [ ((0 < a) ⇔ (0 < b)) ⊓ ((a < 0) ⇔ (b < 0)) ]
·-reflects-0< a b p .fst .fst q = ·-reflects-<ˡ 0 b a q (transport (λ i → [ ·-nullifiesʳ a (~ i) < a · b ]) p)
·-reflects-0< a b p .fst .snd q = ·-reflects-<  0 a b q (transport (λ i → [ ·-nullifiesˡ b (~ i) < a · b ]) p)
·-reflects-0< a b p .snd .fst q = ·-reflects-<-flippedˡ 0 b a q (transport (λ i → [ ·-nullifiesʳ a (~ i) < a · b ]) p)
·-reflects-0< a b p .snd .snd q = ·-reflects-<-flippedʳ 0 a b q (transport (λ i → [ ·-nullifiesˡ b (~ i) < a · b ]) p)

#-dicho : ∀ x → [ x # 0 ] ⊎ (x ≡ 0)
#-dicho x = <-tricho x 0

⊕-identityʳ : ∀ s → (s Bool.⊕ spos) ≡ s
⊕-identityʳ spos = refl
⊕-identityʳ sneg = refl

·-preserves-signˡ : ∀ x y → [ 0 < y ] → sign (x · y) ≡ sign x
·-preserves-signˡ x (signed spos zero) p = ⊥-elim {A = λ _ → sign (x · ℤ.posneg i0) ≡ sign x} (¬-<ⁿ-zero p)
·-preserves-signˡ x (signed sneg  zero) p = ⊥-elim {A = λ _ → sign (x · ℤ.posneg i1) ≡ sign x} (¬-<ⁿ-zero p)
·-preserves-signˡ x (ℤ.posneg i)        p = ⊥-elim {A = λ _ → sign (x · ℤ.posneg i ) ≡ sign x} (¬-<ⁿ-zero p)
·-preserves-signˡ (signed spos zero) (signed spos (suc n)) p = refl
·-preserves-signˡ (signed sneg  zero) (signed spos (suc n)) p = refl
·-preserves-signˡ (ℤ.posneg i)        (signed spos (suc n)) p = refl
·-preserves-signˡ (signed s (suc n₁)) (signed spos (suc n)) p = ⊕-identityʳ s

#⇒≢ : ∀ x → [ x # 0 ] → ¬ᵗ(0 ≡ x)
#⇒≢ x (inl p) q = <-irrefl 0 $ subst (λ p → [ p < pos 0 ]) (sym q) p
#⇒≢ x (inr p) q = <-irrefl 0 $ subst (λ p → [ pos 0 < p ]) (sym q) p

<-split-pos : ∀ z → [ 0 < z ] → Σ[ n ∈ ℕ ] z ≡ pos (suc n)
<-split-pos (pos zero)    p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] posneg i0 ≡ pos (suc n)} (<-irrefl 0 p)
<-split-pos (neg zero)    p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] posneg i1 ≡ pos (suc n)} (<-irrefl 0 p)
<-split-pos (posneg i)    p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] posneg i  ≡ pos (suc n)} (<-irrefl 0 p)
<-split-pos (pos (suc n)) p = n , refl

<-split-neg : ∀ z → [ z < 0 ] → Σ[ n ∈ ℕ ] z ≡ neg (suc n)
<-split-neg (pos zero)    p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] posneg i0   ≡ neg (suc n)} (<-irrefl 0 p)
<-split-neg (neg zero)    p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] posneg i1   ≡ neg (suc n)} (<-irrefl 0 p)
<-split-neg (posneg i)    p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] posneg i    ≡ neg (suc n)} (<-irrefl 0 p)
<-split-neg (pos (suc m)) p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] pos (suc m) ≡ neg (suc n)} (¬suc<ⁿ0 m p)
<-split-neg (neg (suc m)) p = m , refl

#-split-abs : ∀ a → [ a # 0 ] → Σ[ x ∈ _ ] (abs a ≡ suc (abs x))
#-split-abs a (inl a<0) with <-split-neg a a<0; ... | (n , p) = neg n , λ i → abs (p i)
#-split-abs a (inr 0<a) with <-split-pos a 0<a; ... | (n , p) = pos n , λ i → abs (p i)

-- this is  QuoInt.signed-zero
signed0≡0 : ∀ s → signed s 0 ≡ 0
signed0≡0 spos   = refl
signed0≡0 sneg i = posneg (~ i)

·-sucIntʳ⁺ : ∀ m n → m · pos (suc n) ≡ m + m · pos n
·-sucIntʳ⁺ m n = ·-comm m (pos (suc n)) ∙ *-pos-suc n m ∙ (λ i → m + ·-comm (pos n) m i)

signed-respects-+ : ∀ s a b → signed s (a +ⁿ b) ≡ signed s a + signed s b
signed-respects-+ spos  zero   b   = refl
signed-respects-+ sneg  zero   b   = refl
signed-respects-+ spos (suc a) b i = sucℤ  $ signed-respects-+ spos a b i
signed-respects-+ sneg (suc a) b i = predℤ $ signed-respects-+ sneg a b i

-- this is QuoInt.signed-inv
sign-abs-identity : ∀ a → signed (sign a) (abs a) ≡ a
sign-abs-identity (pos zero) j  = posneg (i0 ∧ j)
sign-abs-identity (neg zero) j  = posneg (i1 ∧ j)
sign-abs-identity (posneg i) j  = posneg (i  ∧ j)
sign-abs-identity (pos (suc n)) = refl
sign-abs-identity (neg (suc n)) = refl

signed-reflects-≡₁ : ∀ s₁ s₂ n → signed s₁ (suc n) ≡ signed s₂ (suc n) → s₁ ≡ s₂
signed-reflects-≡₁ s₁ s₂ n p i = sign (p i)

signed-reflects-≡₂ : ∀ s₁ s₂ a b → signed s₁ a ≡ signed s₂ b → a ≡ b
signed-reflects-≡₂ s₁ s₂ a b p i = abs (p i)

-abs : ∀ a → abs (- a) ≡ abs a
-abs (signed s n) = refl
-abs (posneg i) = refl

-reflects-≡ : ∀ a b → - a ≡ - b → a ≡ b
-reflects-≡ a b p = sym (negate-invol a) ∙ (λ i → - p i) ∙ negate-invol b

abs-preserves-· : ∀ a b → abs (a · b) ≡ abs a ·ⁿ abs b
abs-preserves-· a b = refl

sign-abs-≡ : ∀ a b → sign a ≡ sign b → abs a ≡ abs b → a ≡ b
sign-abs-≡ a b p q = transport (λ i → sign-abs-identity a i ≡ sign-abs-identity b i) λ i → signed (p i) (q i)

0<-sign : ∀ z → [ 0 < z ] → sign z ≡ spos
0<-sign z p i = sign $ <-split-pos z p .snd i

<0-sign : ∀ z → [ z < 0 ] → sign z ≡ sneg
<0-sign z p i = sign $ <-split-neg z p .snd i

sign-pos : ∀ n → sign (pos n) ≡ spos
sign-pos zero = refl
sign-pos (suc n) = refl

-- inj-*sm : l * suc m ≡ n * suc m → l ≡ n
-- inj-*sm {zero} {m} {n} p = 0≡n*sm→0≡n p
-- inj-*sm {l} {m} {zero} p = sym (0≡n*sm→0≡n (sym p))
-- inj-*sm {suc l} {m} {suc n} p = cong suc (inj-*sm (inj-m+ {m = suc m} p))

private
  lem1 : ∀ a x → sign a ≡ sign (signed (sign a) (abs a +ⁿ x ·ⁿ abs a))
  lem1 (pos zero)    x = sym $ sign-pos (x ·ⁿ 0)
  lem1 (neg zero)    x = sym $ sign-pos (x ·ⁿ 0)
  lem1 (posneg i)    x = sym $ sign-pos (x ·ⁿ 0)
  lem1 (pos (suc n)) x = refl
  lem1 (neg (suc n)) x = refl

·-reflects-≡ˡ⁺ : ∀ a b x → (pos (suc x)) · a ≡ (pos (suc x)) · b → a ≡ b
·-reflects-≡ˡ⁺ a b x p = sym (sign-abs-identity a) ∙ (λ i → signed (κ i) (γ i)) ∙ sign-abs-identity b where
  φ : suc x ·ⁿ abs a ≡ suc x ·ⁿ abs b
  φ = signed-reflects-≡₂ _ _ _ _ p
  γ : abs a ≡ abs b
  γ = ·ⁿ-reflects-≡ˡ' {x} {abs a} {abs b} φ
  κ = transport ( sign (signed (sign a) (suc x ·ⁿ abs a))
                ≡ sign (signed (sign b) (suc x ·ⁿ abs b)) ≡⟨ (λ i → lem1 a x (~ i) ≡ lem1 b x (~ i)) ⟩
                  sign a ≡ sign b                         ∎) (λ i → sign (p i))

·-reflects-≡ˡ⁻ : ∀ a b x → (neg (suc x)) · a ≡ (neg (suc x)) · b → a ≡ b
·-reflects-≡ˡ⁻ a b x p = sym (sign-abs-identity a) ∙ γ ∙ sign-abs-identity b  where
  φ : suc x ·ⁿ abs a ≡ suc x ·ⁿ abs b
  φ = signed-reflects-≡₂ _ _ _ _ p
  κ : abs a ≡ abs b
  κ = ·ⁿ-reflects-≡ˡ' {x} {abs a} {abs b} φ
  γ : signed (sign a) (abs a) ≡ signed (sign b) (abs b)
  γ with #-dicho a
  ... | inl a#0 = -reflects-≡ _ _ (λ i → signed (θ i) (κ i)) where
    abstract
      c = #-split-abs a a#0 .fst
      q₁ : abs a ≡ suc (abs c)
      q₁ = #-split-abs a a#0 .snd
      q₂ : abs b ≡ suc (abs c)
      q₂ = sym κ ∙ q₁
    θ : not (sign a) ≡ not (sign b)
    θ = signed-reflects-≡₁ _ _ _ (transport (λ i → signed (not (sign a)) (suc x ·ⁿ q₁ i) ≡ signed (not (sign b)) (suc x ·ⁿ q₂ i)) p)
  ... | inr a≡0 = cong₂ signed refl (λ i → abs (a≡0 i)) ∙ signed0≡0 (sign a) ∙ sym (signed0≡0 (sign b)) ∙ cong₂ signed refl ((λ i → abs (a≡0 (~ i))) ∙ κ)

·-reflects-≡ˡ : ∀ a b x → [ x # 0 ] → x · a ≡ x · b → a ≡ b
·-reflects-≡ˡ a b x (inl x<0) q = let (y , r) = <-split-neg x x<0 in ·-reflects-≡ˡ⁻ a b y (transport (λ i → r i · a ≡ r i · b) q)
·-reflects-≡ˡ a b x (inr 0<x) q = let (y , r) = <-split-pos x 0<x in ·-reflects-≡ˡ⁺ a b y (transport (λ i → r i · a ≡ r i · b) q)

·-reflects-≡ʳ : ∀ a b x → [ x # 0 ] → a · x ≡ b · x → a ≡ b
·-reflects-≡ʳ a b x p q = ·-reflects-≡ˡ a b x p (·-comm x a ∙ q ∙ ·-comm b x)
