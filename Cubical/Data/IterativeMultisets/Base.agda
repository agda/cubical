module Cubical.Data.IterativeMultisets.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Sigma
open import Cubical.Functions.Fibration
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Univalence
open import Cubical.Data.W.W

open import Cubical.Data.Empty renaming (elim* to ⊥*-elim ; elim to ⊥-elim)
open import Cubical.Data.Unit
open import Cubical.Data.Bool

private
  variable
    ℓ ℓ' : Level

V∞ : Type (ℓ-suc ℓ)
V∞ {ℓ} = W (Type ℓ) (λ x → x)

open Cubical.Data.W.W.W renaming (sup-W to sup-∞) public

private
  variable
    x y : V∞ {ℓ}

overline : (x : V∞ {ℓ}) → Type ℓ
overline = getShape

tilde : (A : V∞ {ℓ}) → overline A → V∞ {ℓ}
tilde = getSubtree

V∞-overline-tilde : x ≡ sup-∞ (overline x) (tilde x)
V∞-overline-tilde = W-shape-subtree

_∈∞_ : V∞ {ℓ} → V∞ {ℓ} → Type (ℓ-suc ℓ)
_∈∞_ = _∈W_

∈∞-irrefl : ¬ x ∈∞ x
∈∞-irrefl = ∈W-irrefl

toFib : V∞ {ℓ} → Fibration (V∞ {ℓ}) ℓ
toFib x .fst = overline x
toFib x .snd = tilde x

fromFib : Fibration (V∞ {ℓ}) ℓ → V∞ {ℓ}
fromFib fib = sup-∞ (fib .fst) (fib .snd)

secFib : section (toFib {ℓ}) (fromFib {ℓ})
secFib _ = refl

retFib : retract (toFib {ℓ}) (fromFib {ℓ})
retFib (sup-∞ _ _) = refl

Iso-V∞-Fib : Iso (V∞ {ℓ}) (Fibration (V∞ {ℓ}) ℓ)
Iso-V∞-Fib .Iso.fun = toFib
Iso-V∞-Fib .Iso.inv = fromFib
Iso-V∞-Fib .Iso.sec = secFib
Iso-V∞-Fib .Iso.ret = retFib

V∞≃Fib : V∞ {ℓ} ≃ Fibration (V∞ {ℓ}) ℓ
V∞≃Fib = isoToEquiv Iso-V∞-Fib

≡V∞-≃-≡Fib : {ℓ : Level} {x y : V∞ {ℓ}} → (x ≡ y) ≃ (toFib x ≡ toFib y)
≡V∞-≃-≡Fib {x = x} {y = y} .fst = cong toFib
≡V∞-≃-≡Fib {x = x} {y = y} .snd = iso→isEmbedding Iso-V∞-Fib x y

-- explicitly writing down the isomorphism
Iso-≡V∞-≡Fib' : Iso (x ≡ y) (Path (Fibration (V∞ {ℓ}) ℓ) (overline x , tilde x) (overline y , tilde y))
Iso-≡V∞-≡Fib' {x = sup-∞ x α} {y = sup-∞ y β} .Iso.fun = cong (λ s → overline s , tilde s)
Iso-≡V∞-≡Fib' {x = sup-∞ x α} {y = sup-∞ y β} .Iso.inv = cong (λ s → sup-∞ (s .fst) (s .snd))
Iso-≡V∞-≡Fib' {x = sup-∞ x α} {y = sup-∞ y β} .Iso.sec _ = refl
Iso-≡V∞-≡Fib' {x = sup-∞ x α} {y = sup-∞ y β} .Iso.ret p = cong (λ s → cong s p) (funExt (λ s → sym (V∞-overline-tilde {x = s})))

≡V∞-≃-≡Fib' : (x ≡ y) ≃ Path (Fibration (V∞ {ℓ}) ℓ) (overline x , tilde x) (overline y , tilde y)
≡V∞-≃-≡Fib' = isoToEquiv Iso-≡V∞-≡Fib'

≡V∞-≃-≃Fib : (x ≡ y) ≃ ((overline x , tilde x) ≃Fib (overline y , tilde y))
≡V∞-≃-≃Fib = compEquiv ≡V∞-≃-≡Fib (invEquiv (FibrationIP _ _))

_≡Equiv_ : {B : Type ℓ} (f g : Fibration B ℓ') → Type (ℓ-max ℓ ℓ')
f ≡Equiv g = Σ[ e ∈ f .fst ≃ g .fst ] f .snd ≡ (g .snd ∘ e .fst)

_≡Transp_ : {B : Type ℓ} (f g : Fibration B ℓ') → Type (ℓ-max ℓ (ℓ-suc ℓ'))
f ≡Transp g = Σ[ p ∈ f .fst ≡ g .fst ] f .snd ≡ (g .snd ∘ transport p)

≡V∞-≃-≡Transp : {ℓ : Level} {x y : V∞ {ℓ}} →
                   (x ≡ y) ≃ ((overline x , tilde x) ≡Transp (overline y , tilde y))
≡V∞-≃-≡Transp {ℓ} {x} {y} = compEquiv (compEquiv ≡V∞-≃-≡Fib (invEquiv (ΣPathTransport≃PathΣ _ _)))
                                         (pathToEquiv (Σ-cong-snd (λ p → transport→≡∘ (tilde x) (tilde y) p)))

≡V∞-≃-≡Equiv : (x ≡ y) ≃ ((overline x , tilde x) ≡Equiv (overline y , tilde y))
≡V∞-≃-≡Equiv = compEquiv ≡V∞-≃-≡Transp (Σ-cong-equiv-fst univalence)

-- examples

emptySet-∞ : V∞ {ℓ}
emptySet-∞ = sup-∞ ⊥* ⊥*-elim

singleton-∞ : V∞ {ℓ} → V∞ {ℓ}
singleton-∞ x = sup-∞ Unit* λ _ → x

unorderedPair-∞ : V∞ → V∞ → V∞
unorderedPair-∞ x y = sup-∞ Bool (λ b → if b then x else y)
