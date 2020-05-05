{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Truncation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.PathSplit
open isPathSplitEquiv
open import Cubical.Modalities.Modality
open Modality

open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.NatMinusOne as ℕ₋₁
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification as Null hiding (rec; elim)

open import Cubical.HITs.Truncation.Base

open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (∥_∥ to ∥_∥₁; ∣_∣ to ∣_∣₁; squash to squash₁) using ()
open import Cubical.HITs.SetTruncation       as SetTrunc  using (∥_∥₂; ∣_∣₂; squash₂)
open import Cubical.HITs.GroupoidTruncation  as GpdTrunc  using (∥_∥₃; ∣_∣₃; squash₃)
open import Cubical.HITs.2GroupoidTruncation as 2GpdTrunc using (∥_∥₄; ∣_∣₄; squash₄)

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

sphereFill : (n : ℕ₋₁) (f : S n → A) → Type _
sphereFill {A = A} n f = Σ[ top ∈ A ] ((x : S n) → top ≡ f x)

isSphereFilled : ℕ₋₁ → Type ℓ → Type ℓ
isSphereFilled n A = (f : S n → A) → sphereFill n f

isSphereFilledTrunc : {n : HLevel} → isSphereFilled (-1+ n) (hLevelTrunc n A)
isSphereFilledTrunc {n = zero}  f = hub f , ⊥.elim
isSphereFilledTrunc {n = suc n} f = hub f , spoke f

isSphereFilled→isOfHLevelSuc : {n : HLevel} → isSphereFilled (ℕ→ℕ₋₁ n) A → isOfHLevel (suc n) A
isSphereFilled→isOfHLevelSuc {A = A} {zero} h x y = sym (snd (h f) north) ∙ snd (h f) south
  where
    f : Susp ⊥ → A
    f north = x
    f south = y
isSphereFilled→isOfHLevelSuc {A = A} {suc n} h x y = isSphereFilled→isOfHLevelSuc (helper h x y)
  where
    helper : isSphereFilled (ℕ→ℕ₋₁ (suc n)) A → (x y : A) → isSphereFilled (ℕ→ℕ₋₁ n) (x ≡ y)
    helper h x y f = sym p ∙ q , r
      where
        f' : Susp (S (ℕ→ℕ₋₁ n)) → A
        f' north = x
        f' south = y
        f' (merid u i) = f u i

        p = snd (h f') north
        q = snd (h f') south

        r : (s : S (ℕ→ℕ₋₁ n)) → sym p ∙ q ≡ f s
        r s i j = hcomp (λ k → λ { (i = i0) → compPath-filler (sym p) q k j
                                 ; (i = i1) → snd (h f') (merid s j) k
                                 ; (j = i0) → p (k ∨ ~ i)
                                 ; (j = i1) → q k })
                        (p (~ i ∧ ~ j))

isOfHLevel→isSphereFilled : {n : HLevel} → isOfHLevel n A → isSphereFilled (-1+ n) A
isOfHLevel→isSphereFilled {n = zero} h f = fst h , λ _ → snd h _
isOfHLevel→isSphereFilled {n = suc zero} h f = f north , λ _ → h _ _
isOfHLevel→isSphereFilled {A = A} {suc (suc n)} h = helper λ x y → isOfHLevel→isSphereFilled (h x y)
  where
    helper : {n : HLevel} → ((x y : A) → isSphereFilled (-1+ n) (x ≡ y)) → isSphereFilled (suc₋₁ (-1+ n)) A
    helper {n} h f = l , r
      where
      l : A
      l = f north

      f' : S (-1+ n) → f north ≡ f south
      f' x i = f (merid x i)

      h' : sphereFill (-1+ n) f'
      h' = h (f north) (f south) f'

      r : (x : S (suc₋₁ (-1+ n))) → l ≡ f x
      r north = refl
      r south = h' .fst
      r (merid x i) j = hcomp (λ k → λ { (i = i0) → f north
                                       ; (i = i1) → h' .snd x (~ k) j
                                       ; (j = i0) → f north
                                       ; (j = i1) → f (merid x i) })
                              (f (merid x (i ∧ j)))

-- isNull (S n) A ≃ (isSphereFilled n A) × (∀ (x y : A) → isSphereFilled n (x ≡ y))

isOfHLevel→isSnNull : {n : HLevel} → isOfHLevel n A → isNull (S (-1+ n)) A
fst (sec (isOfHLevel→isSnNull h)) f     = fst (isOfHLevel→isSphereFilled h f)
snd (sec (isOfHLevel→isSnNull h)) f i s = snd (isOfHLevel→isSphereFilled h f) s i
fst (secCong (isOfHLevel→isSnNull h) x y) p = fst (isOfHLevel→isSphereFilled (isOfHLevelPath _ h x y) (funExt⁻ p))
snd (secCong (isOfHLevel→isSnNull h) x y) p i j s = snd (isOfHLevel→isSphereFilled (isOfHLevelPath _ h x y) (funExt⁻ p)) s i j

isSnNull→isOfHLevel : {n : HLevel} → isNull (S (-1+ n)) A → isOfHLevel n A
isSnNull→isOfHLevel {n = zero}  nA = fst (sec nA) ⊥.rec , λ y → fst (secCong nA _ y) (funExt ⊥.elim)
isSnNull→isOfHLevel {n = suc n} nA = isSphereFilled→isOfHLevelSuc (λ f → fst (sec nA) f , λ s i → snd (sec nA) f i s)

isOfHLevelTrunc : (n : HLevel) → isOfHLevel n (hLevelTrunc n A)
isOfHLevelTrunc zero    = hub ⊥.rec , λ _ → ≡hub ⊥.rec
isOfHLevelTrunc (suc n) = isSphereFilled→isOfHLevelSuc isSphereFilledTrunc
-- isOfHLevelTrunc n = isSnNull→isOfHLevel isNull-Null

-- hLevelTrunc n is a modality

rec : {n : HLevel}
      {B : Type ℓ'} →
      (isOfHLevel n B) →
      (g : (a : A) → B) →
      (hLevelTrunc n A → B)
rec {B = B} h = Null.elim {B = λ _ → B} λ x → isOfHLevel→isSnNull h

elim : {n : HLevel}
  {B : hLevelTrunc n A → Type ℓ'}
  (hB : (x : hLevelTrunc n A) → isOfHLevel n (B x))
  (g : (a : A) → B (∣ a ∣))
  (x : hLevelTrunc n A) →
  B x
elim hB = Null.elim (λ x → isOfHLevel→isSnNull (hB x))

elim2 : {n : HLevel}
  {B : hLevelTrunc n A → hLevelTrunc n A → Type ℓ'}
  (hB : ((x y : hLevelTrunc n A) → isOfHLevel n (B x y)))
  (g : (a b : A) → B ∣ a ∣ ∣ b ∣)
  (x y : hLevelTrunc n A) →
  B x y
elim2 {n = n} hB g =
  elim (λ _ → isOfHLevelΠ n (λ _ → hB _ _))
    (λ a → elim (λ _ → hB _ _) (λ b → g a b))

elim3 : {n : HLevel}
  {B : (x y z : hLevelTrunc n A) → Type ℓ'}
  (hB : ((x y z : hLevelTrunc n A) → isOfHLevel n (B x y z)))
  (g : (a b c : A) → B (∣ a ∣) ∣ b ∣ ∣ c ∣)
  (x y z : hLevelTrunc n A) →
  B x y z
elim3 {n = n} hB g =
  elim2 (λ _ _ → isOfHLevelΠ n (hB _ _))
    (λ a b → elim (λ _ → hB _ _ _) (λ c → g a b c))

HLevelTruncModality : ∀ {ℓ} (n : HLevel) → Modality ℓ
isModal       (HLevelTruncModality n) = isOfHLevel n
isModalIsProp (HLevelTruncModality n) = isPropIsOfHLevel n
◯             (HLevelTruncModality n) = hLevelTrunc n
◯-isModal     (HLevelTruncModality n) = isOfHLevelTrunc n
η             (HLevelTruncModality n) = ∣_∣
◯-elim        (HLevelTruncModality n) = elim
◯-elim-β      (HLevelTruncModality n) = λ _ _ _ → refl
◯-=-isModal   (HLevelTruncModality n) = isOfHLevelPath n (isOfHLevelTrunc n)

truncIdempotent≃ : (n : HLevel) → isOfHLevel n A → A ≃ hLevelTrunc n A
truncIdempotent≃ n hA = ∣_∣ , isModalToIsEquiv (HLevelTruncModality n) hA

truncIdempotent : (n : HLevel) → isOfHLevel n A → hLevelTrunc n A ≡ A
truncIdempotent n hA = ua (invEquiv (truncIdempotent≃ n hA))

-- functorial action

map : {n : HLevel} {B : Type ℓ'} (g : A → B)
  → hLevelTrunc n A → hLevelTrunc n B
map g = rec (isOfHLevelTrunc _) (λ a → ∣ g a ∣)

mapId : {n : HLevel} → ∀ t → map {n = n} (idfun A) t ≡ t
mapId {n = n} =
  elim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) (λ _ → refl)

-- equivalences to prop/set/groupoid truncations

propTrunc≃Trunc1 : ∥ A ∥₁ ≃ ∥ A ∥ 1
propTrunc≃Trunc1 =
  isoToEquiv
    (iso
      (PropTrunc.elim (λ _ → isOfHLevelTrunc 1) ∣_∣)
      (elim (λ _ → squash₁) ∣_∣₁)
      (elim (λ _ → isOfHLevelPath 1 (isOfHLevelTrunc 1) _ _) (λ _ → refl))
      (PropTrunc.elim (λ _ → isOfHLevelPath 1 squash₁ _ _) (λ _ → refl)))

propTrunc≡Trunc1 : ∥ A ∥₁ ≡ ∥ A ∥ 1
propTrunc≡Trunc1 = ua propTrunc≃Trunc1

setTrunc≃Trunc2 : ∥ A ∥₂ ≃ ∥ A ∥ 2
setTrunc≃Trunc2 =
  isoToEquiv
    (iso
      (SetTrunc.elim (λ _ → isOfHLevelTrunc 2) ∣_∣)
      (elim (λ _ → squash₂) ∣_∣₂)
      (elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _) (λ _ → refl))
      (SetTrunc.elim (λ _ → isOfHLevelPath 2 squash₂ _ _) (λ _ → refl)))

propTrunc≡Trunc2 : ∥ A ∥₂ ≡ ∥ A ∥ 2
propTrunc≡Trunc2 = ua setTrunc≃Trunc2

groupoidTrunc≃Trunc3 : ∥ A ∥₃ ≃ ∥ A ∥ 3
groupoidTrunc≃Trunc3 =
  isoToEquiv
    (iso
      (GpdTrunc.elim (λ _ → isOfHLevelTrunc 3) ∣_∣)
      (elim (λ _ → squash₃) ∣_∣₃)
      (elim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) (λ _ → refl))
      (GpdTrunc.elim (λ _ → isOfHLevelPath 3 squash₃ _ _) (λ _ → refl)))

groupoidTrunc≡Trunc3 : ∥ A ∥₃ ≡ ∥ A ∥ 3
groupoidTrunc≡Trunc3 = ua groupoidTrunc≃Trunc3

2GroupoidTrunc≃Trunc4 : ∥ A ∥₄ ≃ ∥ A ∥ 4
2GroupoidTrunc≃Trunc4 =
  isoToEquiv
    (iso
      (2GpdTrunc.elim (λ _ → isOfHLevelTrunc 4) ∣_∣)
      (elim (λ _ → squash₄) ∣_∣₄)
      (elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _) (λ _ → refl))
      (2GpdTrunc.elim (λ _ → isOfHLevelPath 4 squash₄ _ _) (λ _ → refl)))

2GroupoidTrunc≡Trunc4 : ∥ A ∥₄ ≡ ∥ A ∥ 4
2GroupoidTrunc≡Trunc4 = ua 2GroupoidTrunc≃Trunc4

---- ∥ Ω A ∥ ₙ ≡ Ω ∥ A ∥ₙ₊₁  ----

  {- Proofs of Theorem 7.3.12. and Corollary 7.3.13. in the HoTT book  -}

private
  {- We define the fibration P to show a more general result  -}
  P : {X : Type ℓ} {n : HLevel} → ∥ X ∥ (suc n) → ∥ X ∥ (suc n) → Type ℓ
  P {n = n} x y = elim2 (λ _ _  → isOfHLevelTypeOfHLevel (n))
                        (λ a b → ∥ a ≡ b ∥ n , isOfHLevelTrunc (n)) x y .fst

  {- We will need P to be of hLevel n + 3  -}
  hLevelP : {n : HLevel} (a b : ∥ B ∥ (suc n)) → isOfHLevel ((suc n)) (P a b)
  hLevelP {n = n} =
    elim2 (λ x y → isProp→isOfHLevelSuc (n) (isPropIsOfHLevel (suc n)))
          (λ a b → isOfHLevelSuc (n) (isOfHLevelTrunc (n)))

  {- decode function from P x y to x ≡ y -}
  decode-fun : {n : HLevel} (x y : ∥ B ∥ (suc n)) → P x y → x ≡ y
  decode-fun {n = n} =
    elim2 (λ u v → isOfHLevelΠ (suc n)
                                (λ _ → isOfHLevelSuc (suc n) (isOfHLevelTrunc (suc n)) u v))
          decode*
      where
      decode* : ∀ {n : HLevel} (u v : B)
              → P {n = n} ∣ u ∣ ∣ v ∣ → Path (∥ B ∥ (suc n)) ∣ u ∣ ∣ v ∣
      decode* {B = B} {n = zero} u v =
        rec ( isOfHLevelTrunc 1 ∣ u ∣ ∣ v ∣
            , λ _ → isOfHLevelSuc 1 (isOfHLevelTrunc 1) _ _ _ _) (λ p i → ∣ p i ∣)
      decode* {n = suc n} u v =
        rec (isOfHLevelTrunc (suc (suc n)) ∣ u ∣ ∣ v ∣) (λ p i → ∣ p i ∣)

  {- auxiliary function r used to define encode -}
  r : {m : HLevel} (u : ∥ B ∥ (suc m)) → P u u
  r = elim (λ x → hLevelP x x) (λ a → ∣ refl ∣)

  {- encode function from x ≡ y to P x y -}
  encode-fun : {n : HLevel} (x y : ∥ B ∥ (suc n)) → x ≡ y → P x y
  encode-fun x y p = transport (λ i → P x (p i)) (r x)

  {- We need the following two lemmas on the functions behaviour for refl -}
  dec-refl : {n : HLevel} (x : ∥ B ∥ (suc n)) → decode-fun x x (r x) ≡ refl
  dec-refl {n = zero} =
    elim (λ x → isOfHLevelSuc 1 (isOfHLevelSuc 1 (isOfHLevelTrunc 1) x x) _ _) (λ _ → refl)
  dec-refl {n = suc n} =
    elim (λ x → isOfHLevelSuc (suc n)
                  (isOfHLevelSuc (suc n)
                     (isOfHLevelTrunc (suc (suc n)) x x)
                     (decode-fun x x (r x)) refl))
         (λ _ → refl)

  enc-refl : {n : HLevel} (x : ∥ B ∥ (suc n)) → encode-fun x x refl ≡ r x
  enc-refl x j = transp (λ _ → P x x) j (r x)

  {- decode-fun is a right-inverse -}
  P-rinv : {n : HLevel} (u v : ∥ B ∥  (suc n)) (x : Path (∥ B ∥ (suc n)) u v)
         → decode-fun u v (encode-fun u v x) ≡ x
  P-rinv u v = J (λ y p → decode-fun u y (encode-fun u y p) ≡ p)
                 (cong (decode-fun u u) (enc-refl u) ∙ dec-refl u)

  {- decode-fun is a left-inverse -}
  P-linv : {n : HLevel} (u v : ∥ B ∥ (suc n )) (x : P u v)
         → encode-fun u v (decode-fun u v x) ≡ x
  P-linv {n = n} =
    elim2 (λ x y → isOfHLevelΠ (suc n)
                               (λ z → isOfHLevelSuc (suc n) (hLevelP x y) _ _))
          helper
    where
    helper : {n : HLevel} (a b : B) (p : P {n = n} ∣ a ∣ ∣ b ∣)
           → encode-fun _ _ (decode-fun ∣ a ∣ ∣ b ∣ p) ≡ p
    helper {n = zero} a b =
      elim (λ x → ( sym (isOfHLevelTrunc 0 .snd _) ∙ isOfHLevelTrunc 0 .snd x
                  , λ y → isOfHLevelSuc 1 (isOfHLevelSuc 0 (isOfHLevelTrunc 0)) _ _ _ _))
           (J (λ y p → encode-fun ∣ a ∣ ∣ y ∣ (decode-fun _ _ ∣ p ∣) ≡ ∣ p ∣)
              (enc-refl ∣ a ∣))
    helper {n = suc n} a b =
      elim (λ x → hLevelP {n = suc n} ∣ a ∣ ∣ b ∣ _ _)
           (J (λ y p → encode-fun {n = suc n} ∣ a ∣ ∣ y ∣ (decode-fun _ _ ∣ p ∣) ≡ ∣ p ∣)
              (enc-refl ∣ a ∣))

  {- The final Iso established -}
  IsoFinal : (n : HLevel) (x y : ∥ B ∥ (suc n)) → Iso (x ≡ y) (P x y)
  IsoFinal _ x y = iso (encode-fun x y ) (decode-fun x y) (P-linv x y) (P-rinv x y)

PathIdTrunc : {a b : A} (n : HLevel) → (Path (∥ A ∥ (suc n)) ∣ a ∣ ∣ b ∣) ≡ (∥ a ≡ b ∥ n)
PathIdTrunc n = isoToPath (IsoFinal n _ _)

PathΩ : {a : A} (n : HLevel) → (Path (∥ A ∥ (suc n)) ∣ a ∣ ∣ a ∣) ≡ (∥ a ≡ a ∥ n)
PathΩ n = PathIdTrunc n
