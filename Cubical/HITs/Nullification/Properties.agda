{-# OPTIONS --safe #-}
module Cubical.HITs.Nullification.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
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

rec : ∀ {ℓα ℓs ℓ ℓ'} {A : Type ℓα} {S : A → Type ℓs} {X : Type ℓ} {Y : Type ℓ'}
      → (nB : isNull S Y) → (X → Y) → Null S X → Y
rec nB g ∣ x ∣ = g x
rec nB g (hub α f) = fst (sec (nB α)) (λ s → rec nB g (f s))
rec nB g (spoke α f s i) = snd (sec (nB α)) (λ s → rec nB g (f s)) i s
rec nB g (≡hub {x} {y} {α} p i) = fst (secCong (nB α) (rec nB g x) (rec nB g y)) (λ i s → rec nB g (p s i)) i
rec nB g (≡spoke {x} {y} {α} p s i j) = snd (secCong (nB α) (rec nB g x) (rec nB g y)) (λ i s → rec nB g (p s i)) i j s

toPathP⁻ : ∀ {ℓ} (A : I → Type ℓ) {x : A i0} {y : A i1} → x ≡ transport⁻ (λ i → A i) y → PathP A x y
toPathP⁻ A p i = toPathP {A = λ i → A (~ i)} (sym p) (~ i)

toPathP⁻-sq : ∀ {ℓ} {A : Type ℓ} (x : A) → Square (toPathP⁻ (λ _ → A) (λ _ → transport refl x)) refl
                                                  (transportRefl x) refl
toPathP⁻-sq x j i = hcomp (λ l → λ { (i = i0) → transportRefl x j
                                   ; (i = i1) → x ; (j = i1) → x })
                          (transportRefl x (i ∨ j))

module _ {ℓα ℓs ℓ ℓ'} {A : Type ℓα} {S : A → Type ℓs} {X : Type ℓ} {Y : Null S X → Type ℓ'} where

  private
    secCongDep' : ∀ (nY : (x : Null S X) → isNull S (Y x)) {x y : Null S X} {α} (p : x ≡ y)
                  → (∀ (bx : Y x) (by : Y y) → hasSection (cong₂ (λ x (b : Y x) (_ : S α) → b) p))
    secCongDep' nY {α = α} p = secCongDep (λ _ → const) p (λ a → secCong (nY a α))

  elim : (nY : (x : Null S X) → isNull S (Y x)) → ((a : X) → Y ∣ a ∣) → (x : Null S X) → Y x
  elim nY g ∣ x ∣ = g x
  elim nY g (hub α f)
    = fst (sec (nY (hub α f) α))
          (λ s → transport (λ i → Y (spoke α f s (~ i))) (elim nY g (f s)))

  elim nY g (spoke α f s i)
    = toPathP⁻ (λ i → Y (spoke α f s i))
               (funExt⁻ ( snd (sec (nY (hub α f) α))
                              (λ s → transport (λ i → Y (spoke α f s (~ i))) (elim nY g (f s))) ) s) i

  elim nY g (≡hub {x} {y} p i)
    = hcomp (λ k → λ { (i = i0) → transportRefl (elim nY g x) k
                     ; (i = i1) → transportRefl (elim nY g y) k })
            (fst (secCongDep' nY (≡hub p) (transport refl (elim nY g x)) (transport refl (elim nY g y)))
                 (λ i s → transport (λ j → Y (≡spoke p s (~ j) i)) (elim nY g (p s i))) i)

  elim nY g (≡spoke {x} {y} p s j i)
    = hcomp (λ k → λ { (i = i0) → toPathP⁻-sq (elim nY g x) k j
                     ; (i = i1) → toPathP⁻-sq (elim nY g y) k j
                     ; (j = i1) → elim nY g (p s i) })
            (q₂ j i)

    where q₁ : Path (PathP (λ i → Y (≡hub p i)) (transport refl (elim nY g x)) (transport refl (elim nY g y)))
                    (fst (secCongDep' nY (≡hub p) (transport refl (elim nY g x)) (transport refl (elim nY g y)))
                         (λ i s → transport (λ j → Y (≡spoke p s (~ j) i)) (elim nY g (p s i))))
                    (λ i → transport (λ j → Y (≡spoke p s (~ j) i)) (elim nY g (p s i)))
          q₁ j i = snd (secCongDep' nY (≡hub p) (transport refl (elim nY g x)) (transport refl (elim nY g y)))
                       (λ i s → transport (λ j → Y (≡spoke p s (~ j) i)) (elim nY g (p s i))) j i s

          q₂ : PathP (λ j → PathP (λ i → Y (≡spoke p s j i)) (toPathP⁻ (λ _ → Y x) (λ _ → transport refl (elim nY g x)) j)
                                                             (toPathP⁻ (λ _ → Y y) (λ _ → transport refl (elim nY g y)) j))
                     (fst (secCongDep' nY (≡hub p) (transport refl (elim nY g x)) (transport refl (elim nY g y)))
                        (λ i s → transport (λ j → Y (≡spoke p s (~ j) i)) (elim nY g (p s i))))
                     (λ i → elim nY g (p s i))
          q₂ j i = toPathP⁻ (λ j → Y (≡spoke p s j i)) (λ j → q₁ j i) j

-- nullification is a modality

NullModality : ∀ {ℓα ℓs} {A : Type ℓα} (S : A → Type ℓs) → Modality (ℓ-max ℓα ℓs)
isModal       (NullModality S) = isNull S
isPropIsModal (NullModality S) = isPropΠ (λ α → isPropIsPathSplitEquiv _)
◯             (NullModality S) = Null S
◯-isModal     (NullModality S) = isNull-Null S -- isNull-Null
η             (NullModality S) = ∣_∣
◯-elim        (NullModality S) = elim
◯-elim-β      (NullModality S) = λ _ _ _ → refl
◯-=-isModal   (NullModality S) x y α = fromIsEquiv _ e
  where e : isEquiv (λ (p : x ≡ y) → const {B = S α} p)
        e = transport (λ i → isEquiv {B = funExtPath {A = S α} {f = const x} {g = const y} (~ i)}
                                     (λ p → ua-gluePath funExtEquiv {x = const p} {y = cong const p} refl (~ i)))
                      (isEquivCong (_ , toIsEquiv _ (isNull-Null S α)))

idemNull : ∀ {ℓ} {A : Type ℓ} (S : A → Type ℓ) (X : Type ℓ) → isNull S A → A ≃ Null S A
idemNull S A nA = ∣_∣ , isModalToIsEquiv (NullModality S) nA

-- nullification is localization at a family of maps (S α → 1)

module Null-iso-Localize {ℓα ℓs ℓ} {A : Type ℓα} (S : A → Type ℓs) (X : Type ℓ) where

  to : Null S X → Localize {A = A} (λ α → const {B = S α} tt) X
  to ∣ x ∣ = ∣ x ∣
  to (hub α f) = ext α (to ∘ f) tt
  to (spoke α f s i) = isExt α (to ∘ f) s i
  to (≡hub {x} {y} {α} p i) = ≡ext α (const (to x)) (const (to y)) (cong to ∘ p) tt i
  to (≡spoke {x} {y} {α} p s i j) = ≡isExt α (const (to x)) (const (to y)) (cong to ∘ p) s i j

  from : Localize {A = A} (λ α → const {B = S α} tt) X → Null S X
  from ∣ x ∣ = ∣ x ∣
  from (ext α f tt) = hub α (from ∘ f)
  from (isExt α f s i) = spoke α (from ∘ f) s i
  from (≡ext α g h p tt i) = ≡hub {x = from (g tt)} {from (h tt)} (cong from ∘ p) i
  from (≡isExt α g h p s i j) = ≡spoke {x = from (g tt)} {from (h tt)} (cong from ∘ p) s i j

  to-from : ∀ (x : Localize {A = A} (λ α → const {B = S α} tt) X) → to (from x) ≡ x
  to-from ∣ x ∣ k = ∣ x ∣
  to-from (ext α f tt) k = ext α (λ s → to-from (f s) k) tt
  to-from (isExt α f s i) k = isExt α (λ s → to-from (f s) k) s i
  to-from (≡ext α g h p tt i) k = ≡ext α (λ _ → to-from (g tt) k) (λ _ → to-from (h tt) k) (λ s j → to-from (p s j) k) tt i
  to-from (≡isExt α g h p s i j) k = ≡isExt α (λ _ → to-from (g tt) k) (λ _ → to-from (h tt) k) (λ s j → to-from (p s j) k) s i j

  from-to : ∀ (x : Null S X) → from (to x) ≡ x
  from-to ∣ x ∣ k = ∣ x ∣
  from-to (hub α f) k = hub α (λ s → from-to (f s) k)
  from-to (spoke α f s i) k = spoke α (λ s → from-to (f s) k) s i
  from-to (≡hub {x} {y} p i) k = ≡hub {x = from-to x k} {from-to y k} (λ s j → from-to (p s j) k) i
  from-to (≡spoke {x} {y} p s i j) k = ≡spoke {x = from-to x k} {from-to y k} (λ s j → from-to (p s j) k) s i j

  isom : Iso (Null S X) (Localize {A = A} (λ α → const {B = S α} tt) X)
  isom = iso to from to-from from-to

Null≃Localize : ∀ {ℓα ℓs ℓ} {A : Type ℓα} (S : A → Type ℓs) (X : Type ℓ) → Null S X ≃ Localize (λ α → const {B = S α} tt) X
Null≃Localize S X = isoToEquiv (Null-iso-Localize.isom S X)
