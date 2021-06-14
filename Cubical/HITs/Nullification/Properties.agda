{-# OPTIONS --safe #-}
module Cubical.HITs.Nullification.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence

open import Cubical.Modalities.Modality

open import Cubical.Functions.FunExtEquiv
open import Cubical.HITs.Localization renaming (rec to Localize-rec)
open import Cubical.Data.Unit

open import Cubical.HITs.Nullification.Base

open Modality
open isPathSplitEquiv

rec : ∀ {ℓ ℓ' ℓ''} {S : Type ℓ} {A : Type ℓ'} {B : Type ℓ''}
      → (nB : isNull S B) → (A → B) → Null S A → B
rec nB g ∣ x ∣ = g x
rec nB g (hub f) = fst (sec nB) (λ s → rec nB g (f s))
rec nB g (spoke f s i) = snd (sec nB) (λ s → rec nB g (f s)) i s
rec nB g (≡hub {x} {y} p i) = fst (secCong nB (rec nB g x) (rec nB g y)) (λ i s → rec nB g (p s i)) i
rec nB g (≡spoke {x} {y} p s i j) = snd (secCong nB (rec nB g x) (rec nB g y)) (λ i s → rec nB g (p s i)) i j s

toPathP⁻ : ∀ {ℓ} (A : I → Type ℓ) {x : A i0} {y : A i1} → x ≡ transport⁻ (λ i → A i) y → PathP A x y
toPathP⁻ A p i = toPathP {A = λ i → A (~ i)} (sym p) (~ i)

toPathP⁻-sq : ∀ {ℓ} {A : Type ℓ} (x : A) → Square (toPathP⁻ (λ _ → A) (λ _ → transport refl x)) refl
                                                  (transportRefl x) refl
toPathP⁻-sq x j i = hcomp (λ l → λ { (i = i0) → transportRefl x j
                                   ; (i = i1) → x ; (j = i1) → x })
                          (transportRefl x (i ∨ j))

module _ {ℓ ℓ' ℓ''} {S : Type ℓ} {A : Type ℓ'} {B : Null S A → Type ℓ''} where

  private
    secCongDep' : ∀ (nB : (x : Null S A) → isNull S (B x)) {x y : Null S A} (p : x ≡ y)
                  → (∀ (bx : B x) (by : B y) → hasSection (cong₂ (λ x (b : B x) (_ : S) → b) p))
    secCongDep' nB p = secCongDep (λ _ → const) p (λ a → secCong (nB a))

  elim : (nB : (x : Null S A) → isNull S (B x)) → ((a : A) → B ∣ a ∣) → (x : Null S A) → B x
  elim nB g ∣ x ∣ = g x
  elim nB g (hub f)
    = fst (sec (nB (hub f)))
          (λ s → transport (λ i → B (spoke f s (~ i))) (elim nB g (f s)))

  elim nB g (spoke f s i)
    = toPathP⁻ (λ i → B (spoke f s i))
               (funExt⁻ ( snd (sec (nB (hub f)))
                              (λ s → transport (λ i → B (spoke f s (~ i))) (elim nB g (f s))) ) s) i

  elim nB g (≡hub {x} {y} p i)
    = hcomp (λ k → λ { (i = i0) → transportRefl (elim nB g x) k
                     ; (i = i1) → transportRefl (elim nB g y) k })
            (fst (secCongDep' nB (≡hub p) (transport refl (elim nB g x)) (transport refl (elim nB g y)))
                 (λ i s → transport (λ j → B (≡spoke p s (~ j) i)) (elim nB g (p s i))) i)

  elim nB g (≡spoke {x} {y} p s j i)
    = hcomp (λ k → λ { (i = i0) → toPathP⁻-sq (elim nB g x) k j
                     ; (i = i1) → toPathP⁻-sq (elim nB g y) k j
                     ; (j = i1) → elim nB g (p s i) })
            (q₂ j i)

    where q₁ : Path (PathP (λ i → B (≡hub p i)) (transport refl (elim nB g x)) (transport refl (elim nB g y)))
                    (fst (secCongDep' nB (≡hub p) (transport refl (elim nB g x)) (transport refl (elim nB g y)))
                         (λ i s → transport (λ j → B (≡spoke p s (~ j) i)) (elim nB g (p s i))))
                    (λ i → transport (λ j → B (≡spoke p s (~ j) i)) (elim nB g (p s i)))
          q₁ j i = snd (secCongDep' nB (≡hub p) (transport refl (elim nB g x)) (transport refl (elim nB g y)))
                       (λ i s → transport (λ j → B (≡spoke p s (~ j) i)) (elim nB g (p s i))) j i s

          q₂ : PathP (λ j → PathP (λ i → B (≡spoke p s j i)) (toPathP⁻ (λ _ → B x) (λ _ → transport refl (elim nB g x)) j)
                                                             (toPathP⁻ (λ _ → B y) (λ _ → transport refl (elim nB g y)) j))
                     (fst (secCongDep' nB (≡hub p) (transport refl (elim nB g x)) (transport refl (elim nB g y)))
                        (λ i s → transport (λ j → B (≡spoke p s (~ j) i)) (elim nB g (p s i))))
                     (λ i → elim nB g (p s i))
          q₂ j i = toPathP⁻ (λ j → B (≡spoke p s j i)) (λ j → q₁ j i) j

-- nullification is a modality

NullModality : ∀ {ℓ} (S : Type ℓ) → Modality ℓ
isModal       (NullModality S) = isNull S
isPropIsModal (NullModality S) = isPropIsPathSplitEquiv _
◯             (NullModality S) = Null S
◯-isModal     (NullModality S) = isNull-Null
η             (NullModality S) = ∣_∣
◯-elim        (NullModality S) = elim
◯-elim-β      (NullModality S) = λ _ _ _ → refl
◯-=-isModal   (NullModality S) x y = fromIsEquiv _ e
  where e : isEquiv (λ (p : x ≡ y) → const {B = S} p)
        e = transport (λ i → isEquiv {B = funExtPath {A = S} {f = const x} {g = const y} (~ i)}
                                     (λ p → ua-gluePath funExtEquiv {x = const p} {y = cong const p} refl (~ i)))
                      (isEquivCong (_ , toIsEquiv _ isNull-Null))

idemNull : ∀ {ℓ} (S A : Type ℓ) → isNull S A → A ≃ Null S A
idemNull S A nA = ∣_∣ , isModalToIsEquiv (NullModality S) nA

-- nullification is localization at a map (S → 1)

module Null-iso-Localize {ℓ ℓ'} (S : Type ℓ) (A : Type ℓ') where

  to : Null S A → Localize {A = Unit} (λ _ → const {B = S} tt) A
  to ∣ x ∣ = ∣ x ∣
  to (hub f) = ext tt (to ∘ f) tt
  to (spoke f s i) = isExt tt (to ∘ f) s i
  to (≡hub {x} {y} p i) = ≡ext tt (const (to x)) (const (to y)) (cong to ∘ p) tt i
  to (≡spoke {x} {y} p s i j) = ≡isExt tt (const (to x)) (const (to y)) (cong to ∘ p) s i j

  from : Localize {A = Unit} (λ _ → const {B = S} tt) A → Null S A
  from ∣ x ∣ = ∣ x ∣
  from (ext tt f tt) = hub (from ∘ f)
  from (isExt tt f s i) = spoke (from ∘ f) s i
  from (≡ext tt g h p tt i) = ≡hub {x = from (g tt)} {from (h tt)} (cong from ∘ p) i
  from (≡isExt tt g h p s i j) = ≡spoke {x = from (g tt)} {from (h tt)} (cong from ∘ p) s i j

  to-from : ∀ (x : Localize {A = Unit} (λ _ → const {B = S} tt) A) → to (from x) ≡ x
  to-from ∣ x ∣ k = ∣ x ∣
  to-from (ext tt f tt) k = ext tt (λ s → to-from (f s) k) tt
  to-from (isExt tt f s i) k = isExt tt (λ s → to-from (f s) k) s i
  to-from (≡ext tt g h p tt i) k = ≡ext tt (λ _ → to-from (g tt) k) (λ _ → to-from (h tt) k) (λ s j → to-from (p s j) k) tt i
  to-from (≡isExt tt g h p s i j) k = ≡isExt tt (λ _ → to-from (g tt) k) (λ _ → to-from (h tt) k) (λ s j → to-from (p s j) k) s i j

  from-to : ∀ (x : Null S A) → from (to x) ≡ x
  from-to ∣ x ∣ k = ∣ x ∣
  from-to (hub f) k = hub (λ s → from-to (f s) k)
  from-to (spoke f s i) k = spoke (λ s → from-to (f s) k) s i
  from-to (≡hub {x} {y} p i) k = ≡hub {x = from-to x k} {from-to y k} (λ s j → from-to (p s j) k) i
  from-to (≡spoke {x} {y} p s i j) k = ≡spoke {x = from-to x k} {from-to y k} (λ s j → from-to (p s j) k) s i j

  isom : Iso (Null S A) (Localize {A = Unit} (λ _ → const {B = S} tt) A)
  isom = iso to from to-from from-to

Null≃Localize : ∀ {ℓ ℓ'} (S : Type ℓ) (A : Type ℓ') → Null S A ≃ Localize (λ _ → const tt) A
Null≃Localize S A = isoToEquiv (Null-iso-Localize.isom S A)
