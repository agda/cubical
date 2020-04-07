{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.PathSplitEquiv
open isPathSplitEquiv
open import Cubical.Modalities.Everything
open Modality

open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.NatMinusOne as ℕ₋₁
  using (ℕ₋₁; ℕ→ℕ₋₁; suc₋₁)
open import Cubical.Data.NatMinusTwo
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification as Null hiding (rec; elim)

open import Cubical.HITs.Truncation.Base

import Cubical.HITs.PropositionalTruncation as T₋₁
import Cubical.HITs.SetTruncation as T₀
import Cubical.HITs.GroupoidTruncation as T₁
import Cubical.HITs.2GroupoidTruncation as T₂

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

sphereFill : (n : ℕ₋₁) (f : S n → A) → Type _
sphereFill {A = A} n f = Σ[ top ∈ A ] ((x : S n) → top ≡ f x)

isSphereFilled : ℕ₋₁ → Type ℓ → Type ℓ
isSphereFilled n A = (f : S n → A) → sphereFill n f

isSphereFilled∥∥ : {n : ℕ₋₂} → isSphereFilled (1+ n) (∥ A ∥ n)
isSphereFilled∥∥ {n = neg2}  f = hub f , ⊥.elim
isSphereFilled∥∥ {n = -1+ n} f = hub f , spoke f

isSphereFilled→isOfHLevelSuc : {n : ℕ} → isSphereFilled (ℕ→ℕ₋₁ n) A → isOfHLevel (suc n) A
isSphereFilled→isOfHLevelSuc {A = A} {zero} h x y = sym (snd (h f) north) ∙ snd (h f) south
  where
    f : Susp ⊥ → A
    f north = x
    f south = y
    f (merid () i)
isSphereFilled→isOfHLevelSuc {A = A} {suc n} h x y = isSphereFilled→isOfHLevelSuc (helper h x y)
  where
    helper : isSphereFilled (ℕ→ℕ₋₁ (suc n)) A → (x y : A) → isSphereFilled (ℕ→ℕ₋₁ n) (x ≡ y)
    helper h x y f = l , r
      where
        f' : Susp (S (ℕ→ℕ₋₁ n)) → A
        f' north = x
        f' south = y
        f' (merid u i) = f u i

        u : sphereFill (ℕ→ℕ₋₁ (suc n)) f'
        u = h f'

        z : A
        z = fst u

        p : z ≡ x
        p = snd u north

        q : z ≡ y
        q = snd u south

        l : x ≡ y
        l = sym p ∙ q

        r : (s : S (ℕ→ℕ₋₁ n)) → l ≡ f s
        r s i j = hcomp
                    (λ k →
                       λ { (i = i0) → compPath-filler (sym p) q k j
                         ; (i = i1) → snd u (merid s j) k
                         ; (j = i0) → p (k ∨ (~ i))
                         ; (j = i1) → q k
                         })
                  (p ((~ i) ∧ (~ j)))

isOfHLevel→isSphereFilled : {n : ℕ₋₂} → isOfHLevel (2+ n) A → isSphereFilled (1+ n) A
isOfHLevel→isSphereFilled {A = A} {neg2} h f = fst h , λ _ → snd h _
isOfHLevel→isSphereFilled {A = A} {neg1} h f = f north , λ _ → h _ _
isOfHLevel→isSphereFilled {A = A} {ℕ→ℕ₋₂ n} h = helper λ x y → isOfHLevel→isSphereFilled (h x y)
  where
    helper : {n : ℕ₋₂} → ((x y : A) → isSphereFilled (1+ n) (x ≡ y)) → isSphereFilled (suc₋₁ (1+ n)) A
    helper {n = n} h f = l , r
      where
      l : A
      l = f north

      f' : S (1+ n) → f north ≡ f south
      f' x i = f (merid x i)

      h' : sphereFill (1+ n) f'
      h' = h (f north) (f south) f'

      r : (x : S (suc₋₁ (1+ n))) → l ≡ f x
      r north = refl
      r south = h' .fst
      r (merid x i) j = hcomp (λ k → λ { (i = i0) → f north
                                        ; (i = i1) → h' .snd x (~ k) j
                                        ; (j = i0) → f north
                                        ; (j = i1) → f (merid x i) }) (f (merid x (i ∧ j)))

-- isNull (S n) A ≃ (isSphereFilled n A) × (∀ (x y : A) → isSphereFilled n (x ≡ y))

isOfHLevel→isSnNull : {n : ℕ₋₂} → isOfHLevel (2+ n) A → isNull (S (1+ n)) A
fst (sec (isOfHLevel→isSnNull h)) f     = fst (isOfHLevel→isSphereFilled h f)
snd (sec (isOfHLevel→isSnNull h)) f i s = snd (isOfHLevel→isSphereFilled h f) s i
fst (secCong (isOfHLevel→isSnNull h) x y) p       = fst (isOfHLevel→isSphereFilled (isOfHLevelPath _ h x y) (funExt⁻ p))
snd (secCong (isOfHLevel→isSnNull h) x y) p i j s = snd (isOfHLevel→isSphereFilled (isOfHLevelPath _ h x y) (funExt⁻ p)) s i j

isSnNull→isOfHLevel : {n : ℕ₋₂} → isNull (S (1+ n)) A → isOfHLevel (2+ n) A
isSnNull→isOfHLevel {n = neg2}  nA = fst (sec nA) ⊥.rec , λ y → fst (secCong nA _ y) (funExt ⊥.elim)
isSnNull→isOfHLevel {n = -1+ n} nA = isSphereFilled→isOfHLevelSuc (λ f → fst (sec nA) f , λ s i → snd (sec nA) f i s)

isOfHLevel∥∥ : (n : ℕ₋₂) → isOfHLevel (2+ n) (∥ A ∥ n)
isOfHLevel∥∥ neg2    = hub ⊥.rec , λ _ → ≡hub ⊥.rec
isOfHLevel∥∥ (-1+ n) = isSphereFilled→isOfHLevelSuc isSphereFilled∥∥

-- isOfHLevel∥∥ n = isSnNull→isOfHLevel isNull-Null

-- ∥_∥ n is a modality

rec : {n : ℕ₋₂}
      {B : Type ℓ'} →
      (isOfHLevel (2+ n) B) →
      (g : (a : A) → B) →
      (∥ A ∥ n → B)
rec {B = B} h = Null.elim {B = λ _ → B} λ x → isOfHLevel→isSnNull h

elim : {n : ℕ₋₂}
  {B : ∥ A ∥ n → Type ℓ'}
  (hB : (x : ∥ A ∥ n) → isOfHLevel (2+ n) (B x))
  (g : (a : A) → B (∣ a ∣))
  (x : ∥ A ∥ n) →
  B x
elim hB = Null.elim (λ x → isOfHLevel→isSnNull (hB x))

elim2 : {n : ℕ₋₂}
  {B : ∥ A ∥ n → ∥ A ∥ n → Type ℓ'}
  (hB : ((x y : ∥ A ∥ n) → isOfHLevel (2+ n) (B x y)))
  (g : (a b : A) → B ∣ a ∣ ∣ b ∣)
  (x y : ∥ A ∥ n) →
  B x y
elim2 {n = n} hB g =
  elim (λ _ → isOfHLevelPi (2+ n) (λ _ → hB _ _))
    (λ a → elim (λ _ → hB _ _) (λ b → g a b))

elim3 : {n : ℕ₋₂}
  {B : (x y z : ∥ A ∥ n) → Type ℓ'}
  (hB : ((x y z : ∥ A ∥ n) → isOfHLevel (2+ n) (B x y z)))
  (g : (a b c : A) → B (∣ a ∣) ∣ b ∣ ∣ c ∣)
  (x y z : ∥ A ∥ n) →
  B x y z
elim3 {n = n} hB g =
  elim2 (λ _ _ → isOfHLevelPi (2+ n) (hB _ _))
    (λ a b → elim (λ _ → hB _ _ _) (λ c → g a b c))

∥_∥-fun : ∀ {ℓ'} {B : Type ℓ'} (f : A → B) (n : ℕ₋₂) → ∥ A ∥ n → ∥ B ∥ n
∥ f ∥-fun n = elim (λ _ → isOfHLevel∥∥ n) λ a → ∣ f a ∣

TruncModality : ∀ {ℓ} (n : ℕ₋₂) → Modality ℓ
isModal       (TruncModality n) = isOfHLevel (2+ n)
isModalIsProp (TruncModality n) = isPropIsOfHLevel (2+ n)
◯             (TruncModality n) = ∥_∥ n
◯-isModal     (TruncModality n) = isOfHLevel∥∥ n
η             (TruncModality n) = ∣_∣
◯-elim        (TruncModality n) = elim
◯-elim-β      (TruncModality n) = λ _ _ _ → refl
◯-=-isModal   (TruncModality n) = isOfHLevelPath (2+ n) (isOfHLevel∥∥ n)

idemTrunc : (n : ℕ₋₂) → isOfHLevel (2+ n) A → A ≃ (∥ A ∥ n)
idemTrunc n hA = ∣_∣ , isModalToIsEquiv (TruncModality n) hA


-- universal property

module univTrunc where
  fun : ∀ {ℓ} (n : ℕ₋₂) {B : HLevel ℓ (2+ n)} → (∥ A ∥ n → (fst B)) → (A → (fst B))
  fun n {B , lev} = λ g a → g ∣ a ∣

  inv : ∀ {ℓ} (n : ℕ₋₂) {B : HLevel ℓ (2+ n)} → (A → (fst B)) → (∥ A ∥ n → (fst B))
  inv n {B , lev} = elim (λ _ → lev)

  sect : ∀ {ℓ} (n : ℕ₋₂) {B : HLevel ℓ (2+ n)} → section {A = (∥ A ∥ n → (fst B))} {B = (A → (fst B))} (fun n {B}) (inv n {B})
  sect n {B , lev} b = refl

  retr : ∀ {ℓ} (n : ℕ₋₂) {B : HLevel ℓ (2+ n)} → retract {A = (∥ A ∥ n → (fst B))} {B = (A → (fst B))} (fun n {B}) (inv n {B})
  retr neg2 {B , lev} b = funExt λ x → sym ((snd lev) (elim (λ _ → lev) (λ a → b ∣ a ∣) x)) ∙ (snd lev) (b x)
  retr (-1+ n) {B , lev} b = funExt (elim (λ x → (isOfHLevelSuc (2+ (-1+ n) ) lev) ((elim (λ _ → lev) (λ a → b ∣ a ∣) x)) (b x)) λ a → refl)

  univTrunc : ∀ {ℓ} (n : ℕ₋₂) {B : HLevel ℓ (2+ n)} → (∥ A ∥ n → (fst B)) ≃ (A → (fst B))
  univTrunc n {B} = isoToEquiv (iso (fun n {B}) (inv n {B}) (sect n {B}) (retr n {B}))



-- equivalences to prop/set/groupoid truncations

propTrunc≃Trunc-1 : T₋₁.∥ A ∥ ≃ ∥ A ∥ -1
propTrunc≃Trunc-1 =
  isoToEquiv
    (iso
      (T₋₁.elim (λ _ → isOfHLevel∥∥ -1) ∣_∣)
      (elim (λ _ → T₋₁.squash) T₋₁.∣_∣)
      (elim (λ _ → isOfHLevelPath 1 (isOfHLevel∥∥ -1) _ _) (λ _ → refl))
      (T₋₁.elim (λ _ → isOfHLevelPath 1 T₋₁.squash _ _) (λ _ → refl)))

setTrunc≃Trunc0 : T₀.∥ A ∥₀ ≃ ∥ A ∥ 0
setTrunc≃Trunc0 =
  isoToEquiv
    (iso
      (T₀.elim (λ _ → isOfHLevel∥∥ 0) ∣_∣)
      (elim (λ _ → T₀.squash₀) T₀.∣_∣₀)
      (elim (λ _ → isOfHLevelPath 2 (isOfHLevel∥∥ 0) _ _) (λ _ → refl))
      (T₀.elim (λ _ → isOfHLevelPath 2 T₀.squash₀ _ _) (λ _ → refl)))

groupoidTrunc≃Trunc1 : T₁.∥ A ∥₁ ≃ ∥ A ∥ 1
groupoidTrunc≃Trunc1 =
  isoToEquiv
    (iso
      (T₁.elim (λ _ → isOfHLevel∥∥ 1) ∣_∣)
      (elim (λ _ → T₁.squash₁) T₁.∣_∣₁)
      (elim (λ _ → isOfHLevelPath 3 (isOfHLevel∥∥ 1) _ _) (λ _ → refl))
      (T₁.elim (λ _ → isOfHLevelPath 3 T₁.squash₁ _ _) (λ _ → refl)))

2GroupoidTrunc≃Trunc2 : T₂.∥ A ∥₂ ≃ ∥ A ∥ 2
2GroupoidTrunc≃Trunc2 =
  isoToEquiv
    (iso
      (T₂.elim (λ _ → isOfHLevel∥∥ 2) ∣_∣)
      (elim (λ _ → T₂.squash₂) T₂.∣_∣₂)
      (elim (λ _ → isOfHLevelPath 4 (isOfHLevel∥∥ 2) _ _) (λ _ → refl))
      (T₂.elim (λ _ → isOfHLevelPath 4 T₂.squash₂ _ _) (λ _ → refl)))

---- ∥ Ω A ∥ ₙ ≡ Ω ∥ A ∥ₙ₊₁  ----

  {- Proofs of Theorem 7.3.12. and Corollary 7.3.13. in the HoTT book  -}

private
  {- We define the fibration P to show a more general result  -}
  P :  ∀ {ℓ} {B : Type ℓ}{n : ℕ₋₂} → ∥ B ∥  (suc₋₂ n) → ∥ B ∥  (suc₋₂ n) → Type ℓ
  P x y = fst (P₁ x y)
    where
    P₁ : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} → ∥ B ∥  (suc₋₂ n) → ∥ B ∥  (suc₋₂ n) → (HLevel  ℓ (2+ n))
    P₁ {ℓ} {n = n}  x y =
      elim2 (λ _ _  → isOfHLevelHLevel (2+ n)) (λ a b → ∥ a ≡ b ∥  n , isOfHLevel∥∥ n) x y

  {- We will need P to be of hLevel n + 3  -}
  hLevelP : ∀{ℓ} {n : ℕ₋₂} {B : Type ℓ} (a b : ∥ B ∥ (suc₋₂ n)) → isOfHLevel (2+ (suc₋₂ n)) (P a b )
  hLevelP {n = n} =
    elim2
      (λ x y → isProp→isOfHLevelSuc (2+ n) (isPropIsOfHLevel (2+ suc₋₂ n)) )
      (λ a b → isOfHLevelSuc (2+ n) (isOfHLevel∥∥ n))

  {- decode function from P x y to x ≡ y -}
  decode-fun :  ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} (x y : ∥ B ∥ (suc₋₂ n)) → P x y → x ≡ y
  decode-fun {B = B} {n = n} =
    elim2
      (λ u v → isOfHLevelPi
        (2+ suc₋₂ n)
        (λ _ → isOfHLevelSuc (2+ suc₋₂ n) (isOfHLevel∥∥ (suc₋₂ n)) u v))
      decode*
      where
      decode* :  ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂}(u v : B)
        → (P {n = n} ∣ u ∣ ∣ v ∣) → _≡_ {A = ∥ B ∥ (suc₋₂ n)} ∣ u ∣ ∣ v ∣
      decode* {B = B} {n = neg2} u v =
        rec
          ( isOfHLevel∥∥ (suc₋₂ neg2) ∣ u ∣ ∣ v ∣
          , λ _ →
            isOfHLevelSuc (suc zero) (isOfHLevel∥∥ (suc₋₂ neg2)) _ _ _ _
          )
          (λ p → cong (λ z → ∣ z ∣) p)
      decode* {n = -1+ n} u v =
        rec (isOfHLevel∥∥ (-1+ (suc n)) ∣ u ∣ ∣ v ∣) (λ p → cong (λ z → ∣ z ∣) p)

  {- auxilliary function r used to define encode -}
  r :  ∀ {ℓ} {B : Type ℓ} {m : ℕ₋₂} (u : ∥ B ∥ (suc₋₂ m)) → P u u
  r {m = m}  = elim (λ x → hLevelP x x) (λ a → ∣ refl ∣)

  {- encode function from x ≡ y to P x y -}
  encode-fun : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} (x y : ∥ B ∥ (suc₋₂ n)) → x ≡ y → P x y
  encode-fun x y p = transport (λ i → P x (p i)) (r x)

  {- We need the following two lemmas on the functions behaviour for refl -}
  dec-refl : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂}
    (x : ∥ B ∥ (suc₋₂ n)) → decode-fun x x (r x) ≡ refl {x = x}
  dec-refl {B = B} {n = neg2} =
    elim
      (λ x →
        isOfHLevelSuc (suc zero)
          (isOfHLevelSuc (suc zero) (isOfHLevel∥∥ (suc₋₂ neg2)) x x)
          _ _)
      (λ a → refl)
  dec-refl {n = -1+ n} =
    elim
      (λ x →
        isOfHLevelSuc (suc n)
         (isOfHLevelSuc (suc n)
            (isOfHLevel∥∥ (-1+ suc n) x x)
            (decode-fun x x (r x)) refl))
      (λ c → refl)

  enc-refl : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂}
    (x : ∥ B ∥ (suc₋₂ n)) → encode-fun x x refl ≡ r x
  enc-refl x j = transp (λ i → P x (refl {x = x} i)) j (r x)

  {- decode-fun is a right-inverse -}
  P-rinv : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} (u v : ∥ B ∥  (suc₋₂ n)) →
    (x : _≡_ {A = ∥ B ∥ (suc₋₂ n)} u v) → decode-fun u v (encode-fun u v x) ≡ x
  P-rinv {ℓ = ℓ} {B = B} {n = n} u v =
    J (λ y p → decode-fun u y (encode-fun u y p) ≡ p)
      ((λ i → (decode-fun u u (enc-refl u i))) ∙ dec-refl u)

  {- decode-fun is a left-inverse -}
  P-linv : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} (u v : ∥ B ∥ (suc₋₂ n )) →
    (x : P u v) → encode-fun u v (decode-fun u v x) ≡ x
  P-linv {n = n} =
    elim2
      (λ x y → isOfHLevelPi (2+ suc₋₂ n)
        (λ z → isOfHLevelSuc (2+ suc₋₂ n) (hLevelP x y) _ _))
      helper
    where
    helper : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} (a b : B) (x : P {n = n} ∣ a ∣ ∣ b ∣)
      → encode-fun ∣ a ∣ ∣ b ∣ (decode-fun ∣ a ∣ ∣ b ∣ x) ≡ x
    helper {n = neg2} a b =
      elim
        (λ x →
          ( sym (isOfHLevel∥∥ neg2 .snd (encode-fun ∣ a ∣ ∣ b ∣ (decode-fun ∣ a ∣ ∣ b ∣ x)))
            ∙ (isOfHLevel∥∥ neg2 .snd x)
          , λ y →
            isOfHLevelSuc (suc zero)
              (isOfHLevelSuc zero (isOfHLevel∥∥ {A = a ≡ b} neg2))
              _ _ _ _
          ))
        (J
          (λ y p → encode-fun ∣ a ∣ ∣ y ∣ ((decode-fun ∣ a ∣ ∣ y ∣) ∣ p ∣) ≡ ∣ p ∣)
          (enc-refl ∣ a ∣))
    helper {n = -1+ n} a b =
      elim
        (λ x → hLevelP {n = -1+ n} ∣ a ∣ ∣ b ∣ _ _)
        (J (λ y p → encode-fun {n = -1+ n} ∣ a ∣ ∣ y ∣ ((decode-fun ∣ a ∣ ∣ y ∣) ∣ p ∣) ≡ ∣ p ∣)
           (enc-refl ∣ a ∣))

  {- The final Iso established -}
  IsoFinal : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} (x y : ∥ B ∥ (suc₋₂ n)) → Iso (x ≡ y) (P x y)
  IsoFinal x y = iso (encode-fun x y ) (decode-fun x y) (P-linv x y) (P-rinv x y)

  IsoFinal2 : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} (x y : ∥ B ∥ (suc₋₂ n)) → Iso (P x y) (x ≡ y)
  IsoFinal2 x y = iso (decode-fun x y) (encode-fun x y ) (P-rinv x y) (P-linv x y)

PathIdTrunc : {a b : A} (n : ℕ₋₂) → (_≡_ {A = ∥ A ∥ (suc₋₂ n)} ∣ a ∣ ∣ b ∣) ≡ (∥ a ≡ b ∥ n)
PathIdTrunc {a = a} {b = b} n = isoToPath (IsoFinal ∣ a ∣ ∣ b ∣)

PathΩ : {a : A} (n : ℕ₋₂) → (_≡_ {A = ∥ A ∥ (suc₋₂ n)} ∣ a ∣ ∣ a ∣) ≡ (∥ a ≡ a ∥ n)
PathΩ {a = a} n = PathIdTrunc {a = a} {b = a} n

truncEquivΩ : {a : A} (n : ℕ₋₂) → (∥ a ≡ a ∥ n) ≃ (_≡_ {A = ∥ A ∥ (suc₋₂ n)} ∣ a ∣ ∣ a ∣)
truncEquivΩ {a = a} n = isoToEquiv (IsoFinal2 ∣ a ∣ ∣ a ∣)

--------------------------


truncOfTruncEq : (n m : ℕ) → ∥ A ∥ (-2+ n) ≃ ∥ ∥ A ∥ (-2+ (n + m)) ∥ (-2+ n)
truncOfTruncEq {A = A} n m = isoToEquiv (iso fun funInv sect retr)
  where
  fun : ∥ A ∥ (-2+ n) → ∥ ∥ A ∥ (-2+ (n + m)) ∥ (-2+ n)
  fun = elim (λ _ → isOfHLevel∥∥ (-2+ n)) λ a → ∣ ∣ a ∣ ∣
  funInv : ∥ ∥ A ∥ (-2+ (n + m)) ∥ (-2+ n) → ∥ A ∥ (-2+ n)
  funInv = elim (λ _ → isOfHLevel∥∥ (-2+ n))
                (elim (λ _ → transport (λ i → isOfHLevel (+-comm n m (~ i)) (∥ A ∥ (-2+ n)))
                                        (isOfHLevelPlus m (isOfHLevel∥∥ (-2+ n))))
                      λ a → ∣ a ∣)

  sect : section fun funInv
  sect = elim (λ x → isOfHLevelPath n (isOfHLevel∥∥ (-2+ n)) _ _ )
                  (elim (λ x → isOfHLevelPath (n + m) (transport (λ i → isOfHLevel (+-comm n m (~ i))
                                                                                     (∥ ∥ A ∥ (-2+ (n + m)) ∥ (-2+ n)))
                                                                  (isOfHLevelPlus m (isOfHLevel∥∥ (-2+ n)))) _ _ )
                        λ a → refl)

  retr : retract fun funInv
  retr = elim (λ x → isOfHLevelPath n (isOfHLevel∥∥ (-2+ n)) _ _) λ a → refl
