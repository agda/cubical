module Cubical.HITs.Nullification.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv

open import Cubical.Modalities.Modality

open import Cubical.Functions.FunExtEquiv
open import Cubical.HITs.Localization renaming (rec to Localize-rec)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)

open import Cubical.HITs.Nullification.Base

open Modality
open isPathSplitEquiv

private
  variable
    ℓα ℓs ℓ ℓ' ℓ'' : Level
    A : Type ℓα
    S : A → Type ℓs
    X : Type ℓ

isNull≡ : (nX : isNull S X) {x y : X} → isNull S (x ≡ y)
isNull≡ nX α =
  fromIsEquiv (λ p _ i → p i)
              (isEquiv[equivFunA≃B∘f]→isEquiv[f] (λ p _ → p) funExtEquiv (isEquivCong (const , toIsEquiv _ (nX α))))

isNullΠ : {Y : X → Type ℓ'} → ((x : X) → isNull S (Y x)) → isNull S ((x : X) → Y x)
isNullΠ {X = X} {S = S} {Y = Y} nY α = fromIsEquiv _ (snd e)
  where
    flipIso : Iso ((x : X) → S α → Y x) (S α → (x : X) → Y x)
    Iso.fun flipIso f = flip f
    Iso.inv flipIso f = flip f
    Iso.rightInv flipIso f = refl
    Iso.leftInv flipIso f = refl

    e : ((x : X) → Y x) ≃ (S α → ((x : X) → Y x))
    e =
      ((x : X) → Y x)
        ≃⟨ equivΠCod (λ x → const , (toIsEquiv _ (nY x α))) ⟩
      ((x : X) → (S α → Y x))
        ≃⟨ isoToEquiv flipIso ⟩
      (S α → ((x : X) → Y x))
        ■

isNullΣ : {Y : X → Type ℓ'} → (isNull S X) → ((x : X) → isNull S (Y x)) →
  isNull S (Σ X Y)
isNullΣ {X = X} {S = S} {Y = Y} nX nY α = fromIsEquiv _ (snd e)
  where
    e : Σ X Y ≃ (S α → Σ X Y)
    e =
      Σ X Y
        ≃⟨ Σ-cong-equiv-snd (λ x → pathSplitToEquiv (_ , (nY x α))) ⟩
      Σ[ x ∈ X ] (S α → Y x)
        ≃⟨ Σ-cong-equiv-fst (pathSplitToEquiv (_ , (nX α))) ⟩
      Σ[ f ∈ (S α → X) ] ((z : S α) → Y (f z))
        ≃⟨ isoToEquiv (invIso Σ-Π-Iso) ⟩
      (S α → Σ X Y)
        ■

equivPreservesIsNull : {Y : Type ℓ'} → (e : X ≃ Y) → (isNull S X) → isNull S Y
equivPreservesIsNull e nullX α =
  fromIsEquiv _
    (isEquiv[f∘equivFunA≃B]→isEquiv[f]
      (λ y _ → y) e
      (snd (compEquiv (pathSplitToEquiv ((λ x _ → x) , (nullX α))) (postCompEquiv e))))

rec : {Y : Type ℓ'} → (nB : isNull S Y) → (X → Y) → Null S X → Y
rec nB g ∣ x ∣ = g x
rec nB g (hub α f) = fst (sec (nB α)) (λ s → rec nB g (f s))
rec nB g (spoke α f s i) = snd (sec (nB α)) (λ s → rec nB g (f s)) i s
rec nB g (≡hub {x} {y} {α} p i) = fst (secCong (nB α) (rec nB g x) (rec nB g y)) (λ i s → rec nB g (p s i)) i
rec nB g (≡spoke {x} {y} {α} p s i j) = snd (secCong (nB α) (rec nB g x) (rec nB g y)) (λ i s → rec nB g (p s i)) i j s

toPathP⁻ : (A : I → Type ℓ) {x : A i0} {y : A i1} → x ≡ transport⁻ (λ i → A i) y → PathP A x y
toPathP⁻ A p i = toPathP {A = λ i → A (~ i)} (sym p) (~ i)

toPathP⁻-sq : ∀ {ℓ} {A : Type ℓ} (x : A) → Square (toPathP⁻ (λ _ → A) (λ _ → transport refl x)) refl
                                                  (transportRefl x) refl
toPathP⁻-sq x j i = hcomp (λ l → λ { (i = i0) → transportRefl x j
                                   ; (i = i1) → x ; (j = i1) → x })
                          (transportRefl x (i ∨ j))

module _ {Y : Null S X → Type ℓ'} where

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

NullRecIsPathSplitEquiv : {Y : Type ℓ'} → (isNull S Y) → isPathSplitEquiv {A = (Null S X) → Y} (λ f → f ∘ ∣_∣)
sec (NullRecIsPathSplitEquiv nY) = rec nY , λ _ → refl
secCong (NullRecIsPathSplitEquiv nY) f f' = (λ p → funExt (elim (λ _ → isNull≡ nY) (funExt⁻ p))) , λ _ → refl

NullRecIsEquiv : {Y : Type ℓ'} → (isNull S Y) → isEquiv {A = (Null S X) → Y} (λ f → f ∘ ∣_∣)
NullRecIsEquiv nY = toIsEquiv _ (NullRecIsPathSplitEquiv nY)

NullRecEquiv : {Y : Type ℓ'} → (isNull S Y) → ((Null S X) → Y) ≃ (X → Y)
NullRecEquiv nY = (λ f → f ∘ ∣_∣) , (NullRecIsEquiv nY)

NullPreservesProp : isProp X → isProp (Null S X)

NullPreservesProp {S = S} pX u = elim (λ v' → isNull≡ (isNull-Null S))
  (λ y → elim (λ u' → isNull≡ (isNull-Null S) {x = u'}) (λ x → cong ∣_∣ (pX x y)) u)

NullPreservesContr : isContr X → isContr (Null S X)
NullPreservesContr l = inhProp→isContr ∣ fst l ∣ (NullPreservesProp (isContr→isProp l))

isPropIsNull : isProp (isNull S X)
isPropIsNull = isPropΠ (λ _ → isPropIsPathSplitEquiv _)

{-
  We check that a few common definitions in type theory are null,
  assuming they are given null types as input.
-}
isNullIsContr : isNull S X → isNull S (isContr X)
isNullIsContr nullX = isNullΣ nullX λ _ → isNullΠ (λ _ → isNull≡ nullX)

isNullIsEquiv :
  {Y : Type ℓ'} (nullX : isNull S X)
  (nullY : isNull S Y) (f : X → Y) → isNull S (isEquiv f)
isNullIsEquiv nullX nullY f =
  equivPreservesIsNull (invEquiv (isEquiv≃isEquiv' f))
    (isNullΠ λ _ → isNullIsContr (isNullΣ nullX λ _ → isNull≡ nullY))

isNullEquiv :
  ∀ {ℓα ℓs ℓ} {A : Type ℓα} {S : A → Type ℓs}
  {X : Type ℓ} {Y : Type ℓ'} → isNull S X → isNull S Y → isNull S (X ≃ Y)
isNullEquiv nullX nullY = isNullΣ (isNullΠ (λ _ → nullY)) (isNullIsEquiv nullX nullY)

isNullIsOfHLevel : (n : HLevel) → isNull S X → isNull S (isOfHLevel n X)
isNullIsOfHLevel zero nullX = isNullIsContr nullX
isNullIsOfHLevel (suc zero) nullX = isNullΠ (λ _ → isNullΠ (λ _ → isNull≡ nullX))
isNullIsOfHLevel (suc (suc n)) nullX =
  isNullΠ (λ _ → isNullΠ (λ _ → isNullIsOfHLevel (suc n) (isNull≡ nullX)))

-- nullification is a modality

NullModality : {A : Type ℓα} (S : A → Type ℓs) → Modality (ℓ-max ℓ (ℓ-max ℓα ℓs))
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

idemNull : ∀ {ℓa ℓs ℓ} {A : Type ℓa} (S : A → Type ℓs) (X : Type (ℓ-max ℓ (ℓ-max ℓa ℓs))) → isNull S X → X ≃ Null S X
idemNull {ℓ = ℓ} S A nA = ∣_∣ , isModalToIsEquiv (NullModality {ℓ = ℓ} S) nA

-- nullification is localization at a family of maps (S α → 1)

module Null-iso-Localize (S : A → Type ℓs) (X : Type ℓ) where

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

Null≃Localize : (S : A → Type ℓs) (X : Type ℓ) → Null S X ≃ Localize (λ α → const {B = S α} tt) X
Null≃Localize S X = isoToEquiv (Null-iso-Localize.isom S X)

SeparatedAndInjective→Null :
  (X : Type ℓ) (sep : (x y : X) → isNull S (x ≡ y))
  (inj : (α : A) → hasSection (const {A = X} {B = S α})) →
  isNull S X
sec (SeparatedAndInjective→Null X sep inj α) = inj α
secCong (SeparatedAndInjective→Null X sep inj α) x y =
  fst s ∘ funExt⁻ , λ p i j α → snd s (funExt⁻ p) i α j
  where
    s = sec (sep x y α)

generatorsConnected : {A : Type ℓα} (S : A → Type ℓ) →
  (a : A) → isContr (Null S (S a))
generatorsConnected S a = (hub a ∣_∣) ,
  elim (λ _ → isNull≡ (isNull-Null S)) (spoke a ∣_∣)

nullMap : {A : Type ℓα} (S : A → Type ℓ) →
  {X : Type ℓ'} {Y : Type ℓ''} → (X → Y) → Null S X → Null S Y
nullMap S f ∣ x ∣ = ∣ f x ∣
nullMap S f (hub α g) = hub α (λ z → nullMap S f (g z))
nullMap S f (spoke α g s i) = spoke α (λ z → nullMap S f (g z)) s i
nullMap S f (≡hub p i) = ≡hub (λ z j → nullMap S f (p z j)) i
nullMap S f (≡spoke p s i i₁) = ≡spoke (λ z j → nullMap S f (p z j)) s i i₁

nullPreservesIso : {A : Type ℓα} (S : A → Type ℓ) → {X : Type ℓ'} →
  {Y : Type ℓ''} → Iso X Y → Iso (Null S X) (Null S Y)
Iso.fun (nullPreservesIso S e) = nullMap S (Iso.fun e)
Iso.inv (nullPreservesIso S e) = nullMap S (Iso.inv e)
Iso.leftInv (nullPreservesIso S e) =
  elim (λ _ → isNull≡ (isNull-Null S)) (λ x → cong ∣_∣ (Iso.leftInv e x))
Iso.rightInv (nullPreservesIso S e) =
  elim (λ _ → isNull≡ (isNull-Null S)) (λ y → cong ∣_∣ (Iso.rightInv e y))

nullPreservesEquiv : {A : Type ℓα} (S : A → Type ℓ) → {X : Type ℓ'} →
  {Y : Type ℓ''} → X ≃ Y → Null S X ≃ Null S Y
nullPreservesEquiv S {X = X} {Y = Y} e = isoToEquiv (nullPreservesIso S (equivToIso e))
