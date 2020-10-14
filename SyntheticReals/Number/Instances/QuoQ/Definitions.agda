{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module SyntheticReals.Number.Instances.QuoQ.Definitions where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
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

open import Cubical.Data.NatPlusOne using (HasFromNat; 1+_; ℕ₊₁; ℕ₊₁→ℕ)
open import Cubical.HITs.SetQuotients as SetQuotient using () renaming (_/_ to _//_)

open import Cubical.Data.Nat.Literals
open import Cubical.Data.Bool
open import SyntheticReals.Number.Prelude.Nat
open import SyntheticReals.Number.Prelude.QuoInt
open import Cubical.HITs.Ints.QuoInt using (HasFromNat)
open import Cubical.HITs.Rationals.QuoQ using
  ( ℚ
  ; onCommonDenom
  ; onCommonDenomSym
  ; eq/
  ; _//_
  ; _∼_
  )
  renaming
  ( [_] to [_]ᶠ
  ; ℕ₊₁→ℤ to [1+_ⁿ]ᶻ
  )

abstract
  private
    lemma1 : ∀ a b₁ b₂ c → (a ·ᶻ b₁) ·ᶻ (b₂ ·ᶻ c) ≡ (a ·ᶻ c) ·ᶻ (b₂ ·ᶻ b₁)
    lemma1 a b₁ b₂ c =
      (a ·ᶻ b₁) ·ᶻ (b₂ ·ᶻ c) ≡⟨ sym $ ·ᶻ-assoc a b₁ (b₂ ·ᶻ c) ⟩
      a ·ᶻ (b₁ ·ᶻ (b₂ ·ᶻ c)) ≡⟨ (λ i → a ·ᶻ ·ᶻ-assoc b₁ b₂ c i) ⟩
      a ·ᶻ ((b₁ ·ᶻ b₂) ·ᶻ c) ≡⟨ (λ i → a ·ᶻ ·ᶻ-comm (b₁ ·ᶻ b₂) c i) ⟩
      a ·ᶻ (c ·ᶻ (b₁ ·ᶻ b₂)) ≡⟨ ·ᶻ-assoc a c (b₁ ·ᶻ b₂) ⟩
      (a ·ᶻ c) ·ᶻ (b₁ ·ᶻ b₂) ≡⟨ (λ i → (a ·ᶻ c) ·ᶻ ·ᶻ-comm b₁ b₂ i) ⟩
      (a ·ᶻ c) ·ᶻ (b₂ ·ᶻ b₁) ∎

    ·ᶻ-commʳ : ∀ a b c → (a ·ᶻ b) ·ᶻ c ≡ (a ·ᶻ c) ·ᶻ b
    ·ᶻ-commʳ a b c = (a ·ᶻ  b) ·ᶻ c  ≡⟨ sym $ ·ᶻ-assoc a b c ⟩
                      a ·ᶻ (b  ·ᶻ c) ≡⟨ (λ i → a ·ᶻ ·ᶻ-comm b c i) ⟩
                      a ·ᶻ (c  ·ᶻ b) ≡⟨ ·ᶻ-assoc a c b ⟩
                     (a ·ᶻ  c) ·ᶻ b  ∎

∼-preserves-<ᶻ : ∀ aᶻ aⁿ bᶻ bⁿ → (aᶻ , aⁿ) ∼ (bᶻ , bⁿ) → [ ((aᶻ <ᶻ 0) ⇒ (bᶻ <ᶻ 0)) ⊓ ((0 <ᶻ aᶻ) ⇒ (0 <ᶻ bᶻ)) ]
∼-preserves-<ᶻ aᶻ aⁿ bᶻ bⁿ r = γ where
  aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
  bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
  0<aⁿᶻ : [ 0 <ᶻ aⁿᶻ ]
  0<aⁿᶻ = ℕ₊₁.n aⁿ , +ⁿ-comm (ℕ₊₁.n aⁿ) 1
  0<bⁿᶻ : [ 0 <ᶻ bⁿᶻ ]
  0<bⁿᶻ = ℕ₊₁.n bⁿ , +ⁿ-comm (ℕ₊₁.n bⁿ) 1
  γ : [ ((aᶻ <ᶻ 0) ⇒ (bᶻ <ᶻ 0)) ⊓ ((0 <ᶻ aᶻ) ⇒ (0 <ᶻ bᶻ)) ]
  γ .fst aᶻ<0 = (
    aᶻ <ᶻ 0               ⇒ᵖ⟨ ·ᶻ-preserves-<ᶻ aᶻ 0 bⁿᶻ 0<bⁿᶻ ⟩
    aᶻ ·ᶻ bⁿᶻ <ᶻ 0 ·ᶻ bⁿᶻ ⇒ᵖ⟨ (subst (λ p → [ aᶻ ·ᶻ bⁿᶻ <ᶻ p ]) $ ·ᶻ-nullifiesˡ bⁿᶻ) ⟩
    aᶻ ·ᶻ bⁿᶻ <ᶻ 0        ⇒ᵖ⟨ subst (λ p → [ p <ᶻ 0 ]) r ⟩
    bᶻ ·ᶻ aⁿᶻ <ᶻ 0        ⇒ᵖ⟨ subst (λ p → [ bᶻ ·ᶻ aⁿᶻ <ᶻ p ]) (sym (·ᶻ-nullifiesˡ aⁿᶻ)) ⟩
    bᶻ ·ᶻ aⁿᶻ <ᶻ 0 ·ᶻ aⁿᶻ ⇒ᵖ⟨ ·ᶻ-reflects-<ᶻ bᶻ 0 aⁿᶻ 0<aⁿᶻ ⟩
    bᶻ        <ᶻ 0        ◼ᵖ) .snd aᶻ<0
  γ .snd 0<aᶻ = (
    0        <ᶻ aᶻ        ⇒ᵖ⟨ ·ᶻ-preserves-<ᶻ 0 aᶻ bⁿᶻ 0<bⁿᶻ ⟩
    0 ·ᶻ bⁿᶻ <ᶻ aᶻ ·ᶻ bⁿᶻ ⇒ᵖ⟨ (subst (λ p → [ p <ᶻ aᶻ ·ᶻ bⁿᶻ ]) $ ·ᶻ-nullifiesˡ bⁿᶻ) ⟩
    0        <ᶻ aᶻ ·ᶻ bⁿᶻ ⇒ᵖ⟨ subst (λ p → [ 0 <ᶻ p ]) r ⟩
    0        <ᶻ bᶻ ·ᶻ aⁿᶻ ⇒ᵖ⟨ subst (λ p → [ p <ᶻ bᶻ ·ᶻ aⁿᶻ ]) (sym (·ᶻ-nullifiesˡ aⁿᶻ)) ⟩
    0 ·ᶻ aⁿᶻ <ᶻ bᶻ ·ᶻ aⁿᶻ ⇒ᵖ⟨ ·ᶻ-reflects-<ᶻ 0 bᶻ aⁿᶻ 0<aⁿᶻ ⟩
    0        <ᶻ bᶻ        ◼ᵖ) .snd 0<aᶻ

-- < on ℤ × ℕ₊₁ in terms of < on ℤ
_<'_ : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → hProp ℓ-zero
(aᶻ , aⁿ) <' (bᶻ , bⁿ) =
  let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
      bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
  in (aᶻ ·ᶻ bⁿᶻ) <ᶻ (bᶻ ·ᶻ aⁿᶻ)

private
  lem1 : ∀ x y z → [ 0 <ᶻ y ] → [ 0 <ᶻ z ] → (0 <ᶻ (x ·ᶻ y)) ≡ (0 <ᶻ (x ·ᶻ z))
  lem1 x y z p q =
     0       <ᶻ (x ·ᶻ y) ≡⟨ (λ i → ·ᶻ-nullifiesˡ y (~ i) <ᶻ x ·ᶻ y) ⟩
    (0 ·ᶻ y) <ᶻ (x ·ᶻ y) ≡⟨ sym $ ·ᶻ-creates-<ᶻ-≡ 0 x y p ⟩
     0       <ᶻ  x       ≡⟨ ·ᶻ-creates-<ᶻ-≡ 0 x z q ⟩
    (0 ·ᶻ z) <ᶻ (x ·ᶻ z) ≡⟨ (λ i → ·ᶻ-nullifiesˡ z i <ᶻ x ·ᶻ z) ⟩
     0       <ᶻ (x ·ᶻ z) ∎

<'-respects-∼ˡ : ∀ a b x → a ∼ b → a <' x ≡ b <' x
<'-respects-∼ˡ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) a~b = γ where
  aⁿᶻ = [1+ aⁿ ⁿ]ᶻ; 0<aⁿᶻ : [ 0 <ᶻ aⁿᶻ ]; 0<aⁿᶻ = 0<ᶻpos[suc] _
  bⁿᶻ = [1+ bⁿ ⁿ]ᶻ; 0<bⁿᶻ : [ 0 <ᶻ bⁿᶻ ]; 0<bⁿᶻ = 0<ᶻpos[suc] _
  xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
  p : aᶻ ·ᶻ bⁿᶻ ≡ bᶻ ·ᶻ aⁿᶻ
  p = a~b
  γ : ((aᶻ ·ᶻ xⁿᶻ) <ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡ ((bᶻ ·ᶻ xⁿᶻ) <ᶻ (xᶻ ·ᶻ bⁿᶻ))
  γ = aᶻ ·ᶻ xⁿᶻ        <ᶻ xᶻ ·ᶻ aⁿᶻ        ≡⟨ ·ᶻ-creates-<ᶻ-≡ (aᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ aⁿᶻ) bⁿᶻ 0<bⁿᶻ ⟩
      aᶻ ·ᶻ xⁿᶻ ·ᶻ bⁿᶻ <ᶻ xᶻ ·ᶻ aⁿᶻ ·ᶻ bⁿᶻ ≡⟨ (λ i → ·ᶻ-commʳ aᶻ xⁿᶻ bⁿᶻ i <ᶻ xᶻ ·ᶻ aⁿᶻ ·ᶻ bⁿᶻ) ⟩
      aᶻ ·ᶻ bⁿᶻ ·ᶻ xⁿᶻ <ᶻ xᶻ ·ᶻ aⁿᶻ ·ᶻ bⁿᶻ ≡⟨ (λ i → p i ·ᶻ xⁿᶻ <ᶻ xᶻ ·ᶻ aⁿᶻ ·ᶻ bⁿᶻ) ⟩
      bᶻ ·ᶻ aⁿᶻ ·ᶻ xⁿᶻ <ᶻ xᶻ ·ᶻ aⁿᶻ ·ᶻ bⁿᶻ ≡⟨ (λ i → ·ᶻ-commʳ bᶻ aⁿᶻ xⁿᶻ i <ᶻ ·ᶻ-commʳ xᶻ aⁿᶻ bⁿᶻ i) ⟩
      bᶻ ·ᶻ xⁿᶻ ·ᶻ aⁿᶻ <ᶻ xᶻ ·ᶻ bⁿᶻ ·ᶻ aⁿᶻ ≡⟨ sym $ ·ᶻ-creates-<ᶻ-≡ (bᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ bⁿᶻ) aⁿᶻ 0<aⁿᶻ ⟩
      bᶻ ·ᶻ xⁿᶻ        <ᶻ xᶻ ·ᶻ bⁿᶻ        ∎

<'-respects-∼ʳ : ∀ x a b → a ∼ b → x <' a ≡ x <' b
<'-respects-∼ʳ x@(xᶻ , xⁿ) a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) a~b =
  let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ; 0<aⁿᶻ : [ 0 <ᶻ aⁿᶻ ]; 0<aⁿᶻ = 0<ᶻpos[suc] _
      bⁿᶻ = [1+ bⁿ ⁿ]ᶻ; 0<bⁿᶻ : [ 0 <ᶻ bⁿᶻ ]; 0<bⁿᶻ = 0<ᶻpos[suc] _
      xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
      p : aᶻ ·ᶻ bⁿᶻ ≡ bᶻ ·ᶻ aⁿᶻ
      p = a~b
  in xᶻ ·ᶻ aⁿᶻ        <ᶻ aᶻ  ·ᶻ  xⁿᶻ        ≡⟨ (λ i → xᶻ ·ᶻ aⁿᶻ <ᶻ ·ᶻ-comm aᶻ xⁿᶻ i) ⟩
     xᶻ ·ᶻ aⁿᶻ        <ᶻ xⁿᶻ ·ᶻ  aᶻ         ≡⟨ ·ᶻ-creates-<ᶻ-≡ (xᶻ ·ᶻ aⁿᶻ) (xⁿᶻ ·ᶻ  aᶻ) bⁿᶻ 0<bⁿᶻ ⟩
     xᶻ ·ᶻ aⁿᶻ ·ᶻ bⁿᶻ <ᶻ xⁿᶻ ·ᶻ  aᶻ ·ᶻ bⁿᶻ  ≡⟨ (λ i → xᶻ ·ᶻ aⁿᶻ ·ᶻ bⁿᶻ <ᶻ ·ᶻ-assoc xⁿᶻ aᶻ bⁿᶻ (~ i)) ⟩
     xᶻ ·ᶻ aⁿᶻ ·ᶻ bⁿᶻ <ᶻ xⁿᶻ ·ᶻ (aᶻ ·ᶻ bⁿᶻ) ≡⟨ (λ i → xᶻ ·ᶻ aⁿᶻ ·ᶻ bⁿᶻ <ᶻ xⁿᶻ ·ᶻ (p i)) ⟩
     xᶻ ·ᶻ aⁿᶻ ·ᶻ bⁿᶻ <ᶻ xⁿᶻ ·ᶻ (bᶻ ·ᶻ aⁿᶻ) ≡⟨ (λ i → ·ᶻ-commʳ xᶻ aⁿᶻ bⁿᶻ i <ᶻ ·ᶻ-assoc xⁿᶻ bᶻ aⁿᶻ i) ⟩
     xᶻ ·ᶻ bⁿᶻ ·ᶻ aⁿᶻ <ᶻ xⁿᶻ ·ᶻ  bᶻ ·ᶻ aⁿᶻ  ≡⟨ sym $ ·ᶻ-creates-<ᶻ-≡ (xᶻ ·ᶻ bⁿᶻ) (xⁿᶻ ·ᶻ bᶻ) aⁿᶻ 0<aⁿᶻ ⟩
     xᶻ ·ᶻ bⁿᶻ        <ᶻ xⁿᶻ ·ᶻ  bᶻ         ≡⟨ (λ i → xᶻ ·ᶻ bⁿᶻ <ᶻ ·ᶻ-comm xⁿᶻ bᶻ i) ⟩
     xᶻ ·ᶻ bⁿᶻ        <ᶻ bᶻ  ·ᶻ  xⁿᶻ        ∎

infixl 4 _<_
_<_ : hPropRel ℚ ℚ ℓ-zero
a < b = SetQuotient.rec2 {R = _∼_} {B = hProp ℓ-zero} isSetHProp _<'_ <'-respects-∼ˡ <'-respects-∼ʳ a b

_≤_ : hPropRel ℚ ℚ ℓ-zero
x ≤ y = ¬ᵖ (y < x)

min' : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
min' (aᶻ , aⁿ) (bᶻ , bⁿ) =
  let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
      bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
  in minᶻ (aᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ aⁿᶻ)

max' : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
max' (aᶻ , aⁿ) (bᶻ , bⁿ) =
  let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
      bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
  in maxᶻ (aᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ aⁿᶻ)

min'-sym : ∀ x y → min' x y ≡ min' y x
min'-sym (aᶻ , aⁿ) (bᶻ , bⁿ) = minᶻ-comm (aᶻ ·ᶻ [1+ bⁿ ⁿ]ᶻ) (bᶻ ·ᶻ [1+ aⁿ ⁿ]ᶻ)

max'-sym : ∀ x y → max' x y ≡ max' y x
max'-sym (aᶻ , aⁿ) (bᶻ , bⁿ) = maxᶻ-comm (aᶻ ·ᶻ [1+ bⁿ ⁿ]ᶻ) (bᶻ ·ᶻ [1+ aⁿ ⁿ]ᶻ)

min'-respects-∼ : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) : ℤ × ℕ₊₁)
                → a ∼ b
                → [1+ bⁿ ⁿ]ᶻ ·ᶻ min' a x ≡ [1+ aⁿ ⁿ]ᶻ ·ᶻ min' b x
min'-respects-∼ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) a~b =
  bⁿᶻ ·ᶻ minᶻ (aᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ aⁿᶻ)            ≡⟨ ·ᶻ-minᶻ-distribˡ (aᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ aⁿᶻ) bⁿᶻ 0≤bⁿᶻ ⟩
  minᶻ (bⁿᶻ ·ᶻ (aᶻ ·ᶻ xⁿᶻ)) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → minᶻ (·ᶻ-assoc bⁿᶻ aᶻ xⁿᶻ i) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ))) ⟩
  minᶻ ((bⁿᶻ ·ᶻ aᶻ) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → minᶻ ((·ᶻ-comm bⁿᶻ aᶻ i) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ))) ⟩
  minᶻ ((aᶻ ·ᶻ bⁿᶻ) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → minᶻ (p i ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ))) ⟩
  minᶻ ((bᶻ ·ᶻ aⁿᶻ) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → minᶻ (·ᶻ-comm bᶻ aⁿᶻ i ·ᶻ xⁿᶻ) (·ᶻ-assoc bⁿᶻ xᶻ aⁿᶻ i)) ⟩
  minᶻ ((aⁿᶻ ·ᶻ bᶻ) ·ᶻ xⁿᶻ) ((bⁿᶻ ·ᶻ xᶻ) ·ᶻ aⁿᶻ) ≡⟨ (λ i → minᶻ (·ᶻ-assoc aⁿᶻ bᶻ xⁿᶻ (~ i)) (·ᶻ-comm (bⁿᶻ ·ᶻ xᶻ) aⁿᶻ i)) ⟩
  minᶻ (aⁿᶻ ·ᶻ (bᶻ ·ᶻ xⁿᶻ)) (aⁿᶻ ·ᶻ (bⁿᶻ ·ᶻ xᶻ)) ≡⟨ sym $ ·ᶻ-minᶻ-distribˡ (bᶻ ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ xᶻ) aⁿᶻ 0≤aⁿᶻ ⟩
  aⁿᶻ ·ᶻ minᶻ (bᶻ ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ xᶻ)            ≡⟨ (λ i → aⁿᶻ ·ᶻ minᶻ (bᶻ ·ᶻ xⁿᶻ) (·ᶻ-comm bⁿᶻ xᶻ i)) ⟩
  aⁿᶻ ·ᶻ minᶻ (bᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ bⁿᶻ)            ∎
  where
    aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
    bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
    xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
    p : aᶻ ·ᶻ bⁿᶻ ≡ bᶻ ·ᶻ aⁿᶻ
    p = a~b
    0≤aⁿᶻ : [ 0 ≤ᶻ aⁿᶻ ]
    0≤aⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p
    0≤bⁿᶻ : [ 0 ≤ᶻ bⁿᶻ ]
    0≤bⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p

-- same proof as for min
max'-respects-∼ : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) : ℤ × ℕ₊₁)
  → a ∼ b
  → [1+ bⁿ ⁿ]ᶻ ·ᶻ max' a x ≡ [1+ aⁿ ⁿ]ᶻ ·ᶻ max' b x
max'-respects-∼ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) a~b =
  bⁿᶻ ·ᶻ maxᶻ (aᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ aⁿᶻ)            ≡⟨ ·ᶻ-maxᶻ-distribˡ (aᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ aⁿᶻ) bⁿᶻ 0≤bⁿᶻ ⟩
  maxᶻ (bⁿᶻ ·ᶻ (aᶻ ·ᶻ xⁿᶻ)) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → maxᶻ (·ᶻ-assoc bⁿᶻ aᶻ xⁿᶻ i) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ))) ⟩
  maxᶻ ((bⁿᶻ ·ᶻ aᶻ) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → maxᶻ ((·ᶻ-comm bⁿᶻ aᶻ i) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ))) ⟩
  maxᶻ ((aᶻ ·ᶻ bⁿᶻ) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → maxᶻ (p i ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ))) ⟩
  maxᶻ ((bᶻ ·ᶻ aⁿᶻ) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → maxᶻ (·ᶻ-comm bᶻ aⁿᶻ i ·ᶻ xⁿᶻ) (·ᶻ-assoc bⁿᶻ xᶻ aⁿᶻ i)) ⟩
  maxᶻ ((aⁿᶻ ·ᶻ bᶻ) ·ᶻ xⁿᶻ) ((bⁿᶻ ·ᶻ xᶻ) ·ᶻ aⁿᶻ) ≡⟨ (λ i → maxᶻ (·ᶻ-assoc aⁿᶻ bᶻ xⁿᶻ (~ i)) (·ᶻ-comm (bⁿᶻ ·ᶻ xᶻ) aⁿᶻ i)) ⟩
  maxᶻ (aⁿᶻ ·ᶻ (bᶻ ·ᶻ xⁿᶻ)) (aⁿᶻ ·ᶻ (bⁿᶻ ·ᶻ xᶻ)) ≡⟨ sym $ ·ᶻ-maxᶻ-distribˡ (bᶻ ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ xᶻ) aⁿᶻ 0≤aⁿᶻ ⟩
  aⁿᶻ ·ᶻ maxᶻ (bᶻ ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ xᶻ)            ≡⟨ (λ i → aⁿᶻ ·ᶻ maxᶻ (bᶻ ·ᶻ xⁿᶻ) (·ᶻ-comm bⁿᶻ xᶻ i)) ⟩
  aⁿᶻ ·ᶻ maxᶻ (bᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ bⁿᶻ)            ∎
  where
    aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
    bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
    xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
    p : aᶻ ·ᶻ bⁿᶻ ≡ bᶻ ·ᶻ aⁿᶻ
    p = a~b
    0≤aⁿᶻ : [ 0 ≤ᶻ aⁿᶻ ]
    0≤aⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p
    0≤bⁿᶻ : [ 0 ≤ᶻ bⁿᶻ ]
    0≤bⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p

min : ℚ → ℚ → ℚ
min a b = onCommonDenomSym min' min'-sym min'-respects-∼ a b

max : ℚ → ℚ → ℚ
max a b = onCommonDenomSym max' max'-sym max'-respects-∼ a b

-- injᶻⁿ⁺¹ : ∀ x → [ 0 <ᶻ x ] → Σ[ y ∈ ℕ₊₁ ] x ≡ [1+ y ⁿ]ᶻ
-- injᶻⁿ⁺¹ (signed spos zero) p = ⊥-elim {A = λ _ → Σ[ y ∈ ℕ₊₁ ] ℤ.posneg i0 ≡ [1+ y ⁿ]ᶻ}  (¬-<ⁿ-zero p)
-- injᶻⁿ⁺¹ (signed sneg  zero) p = ⊥-elim {A = λ _ → Σ[ y ∈ ℕ₊₁ ] ℤ.posneg i1 ≡ [1+ y ⁿ]ᶻ}  (¬-<ⁿ-zero p)
-- injᶻⁿ⁺¹ (ℤ.posneg i)        p = ⊥-elim {A = λ _ → Σ[ y ∈ ℕ₊₁ ] ℤ.posneg i  ≡ [1+ y ⁿ]ᶻ}  (¬-<ⁿ-zero p)
-- injᶻⁿ⁺¹ (signed spos (suc n)) p =  1+ n , refl

absᶻ⁺¹ : ℤ → ℕ₊₁
absᶻ⁺¹ (pos zero)    = 1+ 0
absᶻ⁺¹ (neg zero)    = 1+ 0
absᶻ⁺¹ (posneg i)    = 1+ 0
absᶻ⁺¹ (pos (suc n)) = 1+ n
absᶻ⁺¹ (neg (suc n)) = 1+ n

-- absᶻ⁺¹-identity⁺ : ∀ x → [ 0 <ⁿ x ] → [1+ absᶻ⁺¹ (pos x) ⁿ]ᶻ ≡ pos x
-- absᶻ⁺¹-identity⁺ zero    p = ⊥-elim {A = λ _ → [1+ absᶻ⁺¹ (pos zero) ⁿ]ᶻ ≡ pos zero} (<ⁿ-irrefl 0 p)
-- absᶻ⁺¹-identity⁺ (suc x) p = refl
--
-- absᶻ⁺¹-identity⁻ : ∀ x → [ 0 <ⁿ x ] → [1+ absᶻ⁺¹ (neg x) ⁿ]ᶻ ≡ pos x
-- absᶻ⁺¹-identity⁻ zero p = ⊥-elim {A = λ _ → [1+ absᶻ⁺¹ (neg zero) ⁿ]ᶻ ≡ pos zero} (<ⁿ-irrefl 0 p)
-- absᶻ⁺¹-identity⁻ (suc x) p = refl

absᶻ⁺¹-identity : ∀ x → [ x #ᶻ 0 ] → [1+ absᶻ⁺¹ x ⁿ]ᶻ ≡ pos (absᶻ x)
absᶻ⁺¹-identity (pos zero)    p = ⊥-elim {A = λ _ → pos 1 ≡ pos 0} $ #ᶻ⇒≢ (posneg i0) p refl
absᶻ⁺¹-identity (neg zero)    p = ⊥-elim {A = λ _ → pos 1 ≡ pos 0} $ #ᶻ⇒≢ (posneg i1) p posneg
absᶻ⁺¹-identity (posneg i)    p = ⊥-elim {A = λ _ → pos 1 ≡ pos 0} $ #ᶻ⇒≢ (posneg i ) p (λ j → posneg (i ∧ j))
absᶻ⁺¹-identity (pos (suc n)) p = refl
absᶻ⁺¹-identity (neg (suc n)) p = refl

absᶻ⁺¹-identityⁿ : ∀ x → [ x #ᶻ 0 ] → suc (ℕ₊₁.n (absᶻ⁺¹ x)) ≡ absᶻ x
absᶻ⁺¹-identityⁿ x p i = absᶻ (absᶻ⁺¹-identity x p i)

sign' : ℤ × ℕ₊₁ → Sign
sign' (z , n) = signᶻ z

sign'-preserves-∼ : (a b : ℤ × ℕ₊₁) → a ∼ b → sign' a ≡ sign' b
sign'-preserves-∼ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) p =  sym (lem aᶻ bⁿ) ∙ ψ ∙ lem bᶻ aⁿ where
  a' = absᶻ aᶻ ·ⁿ suc (ℕ₊₁.n bⁿ)
  b' = absᶻ bᶻ ·ⁿ suc (ℕ₊₁.n aⁿ)
  γ : signed (signᶻ aᶻ ⊕ spos) a' ≡ signed (signᶻ bᶻ ⊕ spos) b'
  γ = p
  ψ : signᶻ (signed (signᶻ aᶻ ⊕ spos) a') ≡ signᶻ (signed (signᶻ bᶻ ⊕ spos) b')
  ψ i = signᶻ (γ i)
  lem : ∀ x y → signᶻ (signed (signᶻ x ⊕ spos) (absᶻ x ·ⁿ suc (ℕ₊₁.n y))) ≡ signᶻ x
  lem (pos zero)    y = refl
  lem (neg zero)    y = refl
  lem (posneg i)    y = refl
  lem (pos (suc n)) y = refl
  lem (neg (suc n)) y = refl

sign : ℚ → Sign
sign = SetQuotient.rec {R = _∼_} {B = Sign} Bool.isSetBool sign' sign'-preserves-∼

sign-signᶻ-identity : ∀ z n → sign [ z , n ]ᶠ ≡ signᶻ z
sign-signᶻ-identity z n = refl
