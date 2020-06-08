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
open import Cubical.Data.NatMinusOne as ℕ₋₁ hiding (1+_)
open import Cubical.Data.NatMinusTwo as ℕ₋₂ hiding (-1+_)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification as Null hiding (rec; elim)

open import Cubical.HITs.Truncation.Base

open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (∥_∥ to ∥_∥₋₁; ∣_∣ to ∣_∣₋₁; squash to squash₋₁) using ()
open import Cubical.HITs.SetTruncation       as SetTrunc  using (∥_∥₀; ∣_∣₀; squash₀)
open import Cubical.HITs.GroupoidTruncation  as GpdTrunc  using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.HITs.2GroupoidTruncation as 2GpdTrunc using (∥_∥₂; ∣_∣₂; squash₂)

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

sphereFill : (n : ℕ₋₁) (f : S n → A) → Type _
sphereFill {A = A} n f = Σ[ top ∈ A ] ((x : S n) → top ≡ f x)

isSphereFilled : ℕ₋₁ → Type ℓ → Type ℓ
isSphereFilled n A = (f : S n → A) → sphereFill n f

isSphereFilledTrunc : {n : ℕ} → isSphereFilled (-1+ n) (hLevelTrunc n A)
isSphereFilledTrunc {n = zero}  f = hub f , ⊥.elim
isSphereFilledTrunc {n = suc n} f = hub f , spoke f

isSphereFilled→isOfHLevelSuc : {n : ℕ} → isSphereFilled (ℕ→ℕ₋₁ n) A → isOfHLevel (suc n) A
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

isOfHLevel→isSphereFilled : {n : ℕ} → isOfHLevel n A → isSphereFilled (-1+ n) A
isOfHLevel→isSphereFilled {n = zero} h f = fst h , λ _ → snd h _
isOfHLevel→isSphereFilled {n = suc zero} h f = f north , λ _ → h _ _
isOfHLevel→isSphereFilled {A = A} {suc (suc n)} h = helper λ x y → isOfHLevel→isSphereFilled (h x y)
  where
    helper : {n : ℕ} → ((x y : A) → isSphereFilled (-1+ n) (x ≡ y)) → isSphereFilled (suc₋₁ (-1+ n)) A
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

isOfHLevel→isSnNull : {n : ℕ} → isOfHLevel n A → isNull (S (-1+ n)) A
fst (sec (isOfHLevel→isSnNull h)) f     = fst (isOfHLevel→isSphereFilled h f)
snd (sec (isOfHLevel→isSnNull h)) f i s = snd (isOfHLevel→isSphereFilled h f) s i
fst (secCong (isOfHLevel→isSnNull h) x y) p = fst (isOfHLevel→isSphereFilled (isOfHLevelPath _ h x y) (funExt⁻ p))
snd (secCong (isOfHLevel→isSnNull h) x y) p i j s = snd (isOfHLevel→isSphereFilled (isOfHLevelPath _ h x y) (funExt⁻ p)) s i j

isSnNull→isOfHLevel : {n : ℕ} → isNull (S (-1+ n)) A → isOfHLevel n A
isSnNull→isOfHLevel {n = zero}  nA = fst (sec nA) ⊥.rec , λ y → fst (secCong nA _ y) (funExt ⊥.elim)
isSnNull→isOfHLevel {n = suc n} nA = isSphereFilled→isOfHLevelSuc (λ f → fst (sec nA) f , λ s i → snd (sec nA) f i s)

isOfHLevelTrunc : (n : ℕ) → isOfHLevel n (hLevelTrunc n A)
isOfHLevelTrunc zero    = hub ⊥.rec , λ _ → ≡hub ⊥.rec
isOfHLevelTrunc (suc n) = isSphereFilled→isOfHLevelSuc isSphereFilledTrunc
-- isOfHLevelTrunc n = isSnNull→isOfHLevel isNull-Null

-- hLevelTrunc n is a modality

rec : {n : ℕ}
      {B : Type ℓ'} →
      isOfHLevel n B →
      (A → B) →
      hLevelTrunc n A →
      B
rec h = Null.rec (isOfHLevel→isSnNull h)

elim : {n : ℕ}
       {B : hLevelTrunc n A → Type ℓ'}
       (hB : (x : hLevelTrunc n A) → isOfHLevel n (B x))
       (g : (a : A) → B (∣ a ∣))
       (x : hLevelTrunc n A) →
       B x
elim hB = Null.elim (λ x → isOfHLevel→isSnNull (hB x))


elim2 : {n : ℕ}
  {B : hLevelTrunc n A → hLevelTrunc n A → Type ℓ'}
  (hB : ((x y : hLevelTrunc n A) → isOfHLevel n (B x y)))
  (g : (a b : A) → B ∣ a ∣ ∣ b ∣)
  (x y : hLevelTrunc n A) →
  B x y
elim2 {n = n} hB g =
  elim (λ _ → isOfHLevelΠ n (λ _ → hB _ _))
    (λ a → elim (λ _ → hB _ _) (λ b → g a b))

elim3 : {n : ℕ}
  {B : (x y z : hLevelTrunc n A) → Type ℓ'}
  (hB : ((x y z : hLevelTrunc n A) → isOfHLevel n (B x y z)))
  (g : (a b c : A) → B (∣ a ∣) ∣ b ∣ ∣ c ∣)
  (x y z : hLevelTrunc n A) →
  B x y z
elim3 {n = n} hB g =
  elim2 (λ _ _ → isOfHLevelΠ n (hB _ _))
    (λ a b → elim (λ _ → hB _ _ _) (λ c → g a b c))

HLevelTruncModality : ∀ {ℓ} (n : ℕ) → Modality ℓ
isModal       (HLevelTruncModality n) = isOfHLevel n
isModalIsProp (HLevelTruncModality n) = isPropIsOfHLevel n
◯             (HLevelTruncModality n) = hLevelTrunc n
◯-isModal     (HLevelTruncModality n) = isOfHLevelTrunc n
η             (HLevelTruncModality n) = ∣_∣
◯-elim        (HLevelTruncModality n) = elim
◯-elim-β      (HLevelTruncModality n) = λ _ _ _ → refl
◯-=-isModal   (HLevelTruncModality n) = isOfHLevelPath n (isOfHLevelTrunc n)

truncIdempotent≃ : (n : ℕ) → isOfHLevel n A → A ≃ hLevelTrunc n A
truncIdempotent≃ n hA = ∣_∣ , isModalToIsEquiv (HLevelTruncModality n) hA

truncIdempotent : (n : ℕ) → isOfHLevel n A → hLevelTrunc n A ≡ A
truncIdempotent n hA = ua (invEquiv (truncIdempotent≃ n hA))

-- universal property

univTrunc : ∀ {ℓ} (n : ℕ) {B : HLevel ℓ n} → Iso (hLevelTrunc n A → B .fst) (A → B .fst)
Iso.fun (univTrunc n {B , lev}) g a = g ∣ a ∣
Iso.inv (univTrunc n {B , lev}) = elim λ _ → lev
Iso.rightInv (univTrunc n {B , lev}) b = refl
Iso.leftInv (univTrunc n {B , lev}) b = funExt (elim (λ x → isOfHLevelPath _ lev _ _)
                                                     λ a → refl)

-- functorial action

map : {n : ℕ} {B : Type ℓ'} (g : A → B)
  → hLevelTrunc n A → hLevelTrunc n B
map g = rec (isOfHLevelTrunc _) (λ a → ∣ g a ∣)

mapCompIso : {n : ℕ} {B : Type ℓ'} → (Iso A B) → Iso (hLevelTrunc n A) (hLevelTrunc n B)
Iso.fun (mapCompIso g) = map (Iso.fun g)
Iso.inv (mapCompIso g) = map (Iso.inv g)
Iso.rightInv (mapCompIso g) = elim (λ x → isOfHLevelPath _ (isOfHLevelTrunc _) _ _) λ b → cong ∣_∣ (Iso.rightInv g b)
Iso.leftInv (mapCompIso g) = elim (λ x → isOfHLevelPath _ (isOfHLevelTrunc _) _ _) λ a → cong ∣_∣ (Iso.leftInv g a)

mapId : {n : ℕ} → ∀ t → map {n = n} (idfun A) t ≡ t
mapId {n = n} =
  elim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _) (λ _ → refl)

-- equivalences to prop/set/groupoid truncations

propTrunc≃Trunc-1 : ∥ A ∥₋₁ ≃ ∥ A ∥ -1
propTrunc≃Trunc-1 =
  isoToEquiv
    (iso
      (PropTrunc.elim (λ _ → isOfHLevelTrunc 1) ∣_∣)
      (elim (λ _ → squash₋₁) ∣_∣₋₁)
      (elim (λ _ → isOfHLevelPath 1 (isOfHLevelTrunc 1) _ _) (λ _ → refl))
      (PropTrunc.elim (λ _ → isOfHLevelPath 1 squash₋₁ _ _) (λ _ → refl)))

propTrunc≡Trunc-1 : ∥ A ∥₋₁ ≡ ∥ A ∥ -1
propTrunc≡Trunc-1 = ua propTrunc≃Trunc-1

setTrunc≃Trunc0 : ∥ A ∥₀ ≃ ∥ A ∥ 0
setTrunc≃Trunc0 =
  isoToEquiv
    (iso
      (SetTrunc.elim (λ _ → isOfHLevelTrunc 2) ∣_∣)
      (elim (λ _ → squash₀) ∣_∣₀)
      (elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _) (λ _ → refl))
      (SetTrunc.elim (λ _ → isOfHLevelPath 2 squash₀ _ _) (λ _ → refl)))

propTrunc≡Trunc0 : ∥ A ∥₀ ≡ ∥ A ∥ -0
propTrunc≡Trunc0 = ua setTrunc≃Trunc0

groupoidTrunc≃Trunc1 : ∥ A ∥₁ ≃ ∥ A ∥ 1
groupoidTrunc≃Trunc1 =
  isoToEquiv
    (iso
      (GpdTrunc.elim (λ _ → isOfHLevelTrunc 3) ∣_∣)
      (elim (λ _ → squash₁) ∣_∣₁)
      (elim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) (λ _ → refl))
      (GpdTrunc.elim (λ _ → isOfHLevelPath 3 squash₁ _ _) (λ _ → refl)))

groupoidTrunc≡Trunc1 : ∥ A ∥₁ ≡ ∥ A ∥ 1
groupoidTrunc≡Trunc1 = ua groupoidTrunc≃Trunc1

2GroupoidTrunc≃Trunc2 : ∥ A ∥₂ ≃ ∥ A ∥ 2
2GroupoidTrunc≃Trunc2 =
  isoToEquiv
    (iso
      (2GpdTrunc.elim (λ _ → isOfHLevelTrunc 4) ∣_∣)
      (elim (λ _ → squash₂) ∣_∣₂)
      (elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _) (λ _ → refl))
      (2GpdTrunc.elim (λ _ → isOfHLevelPath 4 squash₂ _ _) (λ _ → refl)))

2GroupoidTrunc≡Trunc2 : ∥ A ∥₂ ≡ ∥ A ∥ 2
2GroupoidTrunc≡Trunc2 = ua 2GroupoidTrunc≃Trunc2

---- ∥ Ω A ∥ ₙ ≡ Ω ∥ A ∥ₙ₊₁  ----

abstract
  isOfHLevelHLevel2 : ∀ n → isOfHLevel (suc n) (HLevel ℓ n)
  isOfHLevelHLevel2 n = isOfHLevelHLevel n

  {- Proofs of Theorem 7.3.12. and Corollary 7.3.13. in the HoTT book  -}

module ΩTrunc where
  {- We define the fibration P to show a more general result  -}
  P : {X : Type ℓ} {n : ℕ₋₂} → ∥ X ∥ (suc₋₂ n) → ∥ X ∥ (suc₋₂ n) → Type ℓ
  P {n = n} x y =  elim2 (λ _ _  → isOfHLevelHLevel2 (2+ n))
                         (λ a b → ∥ a ≡ b ∥ n , isOfHLevelTrunc (2+ n)) x y .fst

  {- We will need P to be of hLevel n + 3 -}
  hLevelP : {n : ℕ₋₂} (a b : ∥ B ∥ (suc₋₂ n)) → isOfHLevel (2+ (suc₋₂ n)) (P a b)
  hLevelP {n = n} =
    elim2 (λ x y → isProp→isOfHLevelSuc (2+ n) (isPropIsOfHLevel (2+ suc₋₂ n)))
          (λ a b → isOfHLevelSuc (2+ n) (isOfHLevelTrunc (2+ n)))

  {- decode function from P x y to x ≡ y -}
  decode-fun : {n : ℕ₋₂} (x y : ∥ B ∥ (suc₋₂ n)) → P x y → x ≡ y
  decode-fun {n = n} =
    elim2 (λ u v → isOfHLevelΠ (2+ suc₋₂ n)
                                (λ _ → isOfHLevelSuc (2+ suc₋₂ n) (isOfHLevelTrunc (2+ suc₋₂ n)) u v))
          decode*
      where
      decode* : ∀ {n : ℕ₋₂} (u v : B)
              → P {n = n} ∣ u ∣ ∣ v ∣ → Path (∥ B ∥ (suc₋₂ n)) ∣ u ∣ ∣ v ∣
      decode* {B = B} {n = neg2} u v =
        rec ( isOfHLevelTrunc 1 ∣ u ∣ ∣ v ∣
            , λ _ → isOfHLevelSuc 1 (isOfHLevelTrunc 1) _ _ _ _) (cong ∣_∣)
      decode* {n = ℕ₋₂.-1+ n} u v =
        rec (isOfHLevelTrunc (suc (suc n)) ∣ u ∣ ∣ v ∣) (cong ∣_∣)

  {- auxiliary function r used to define encode -}
  r : {m : ℕ₋₂} (u : ∥ B ∥ (suc₋₂ m)) → P u u
  r = elim (λ x → hLevelP x x) (λ a → ∣ refl ∣)

  {- encode function from x ≡ y to P x y -}
  encode-fun : {n : ℕ₋₂} (x y : ∥ B ∥ (suc₋₂ n)) → x ≡ y → P x y
  encode-fun x y p = transport (λ i → P x (p i)) (r x)

  {- We need the following two lemmas on the functions behaviour for refl -}
  dec-refl : {n : ℕ₋₂} (x : ∥ B ∥ (suc₋₂ n)) → decode-fun x x (r x) ≡ refl
  dec-refl {n = neg2} =
    elim (λ x → isOfHLevelSuc 1 (isOfHLevelSuc 1 (isOfHLevelTrunc 1) x x) _ _) (λ _ → refl)
  dec-refl {n = ℕ₋₂.-1+ n} =
    elim (λ x → isOfHLevelSuc (suc n)
                  (isOfHLevelSuc (suc n)
                     (isOfHLevelTrunc (suc (suc n)) x x)
                     (decode-fun x x (r x)) refl))
         (λ _ → refl)

  enc-refl : {n : ℕ₋₂} (x : ∥ B ∥ (suc₋₂ n)) → encode-fun x x refl ≡ r x
  enc-refl x j = transp (λ _ → P x x) j (r x)

  {- decode-fun is a right-inverse -}
  P-rinv : {n : ℕ₋₂} (u v : ∥ B ∥  (suc₋₂ n)) (x : Path (∥ B ∥ (suc₋₂ n)) u v)
         → decode-fun u v (encode-fun u v x) ≡ x
  P-rinv u v = J (λ y p → decode-fun u y (encode-fun u y p) ≡ p)
                 (cong (decode-fun u u) (enc-refl u) ∙ dec-refl u)

  {- decode-fun is a left-inverse -}
  P-linv : {n : ℕ₋₂} (u v : ∥ B ∥ (suc₋₂ n )) (x : P u v)
         → encode-fun u v (decode-fun u v x) ≡ x
  P-linv {n = n} =
    elim2 (λ x y → isOfHLevelΠ (2+ suc₋₂ n)
                                (λ z → isOfHLevelSuc (2+ suc₋₂ n) (hLevelP x y) _ _))
          helper
    where
    helper : {n : ℕ₋₂} (a b : B) (p : P {n = n} ∣ a ∣ ∣ b ∣)
           → encode-fun _ _ (decode-fun ∣ a ∣ ∣ b ∣ p) ≡ p
    helper {n = neg2} a b =
      elim (λ x → ( sym (isOfHLevelTrunc 0 .snd _) ∙ isOfHLevelTrunc 0 .snd x
                  , λ y → isOfHLevelSuc 1 (isOfHLevelSuc 0 (isOfHLevelTrunc 0)) _ _ _ _))
           (J (λ y p → encode-fun ∣ a ∣ ∣ y ∣ (decode-fun _ _ ∣ p ∣) ≡ ∣ p ∣)
              (enc-refl ∣ a ∣))
    helper {n = ℕ₋₂.-1+ n} a b =
      elim (λ x → hLevelP {n = ℕ₋₂.-1+ n} ∣ a ∣ ∣ b ∣ _ _)
           (J (λ y p → encode-fun {n = ℕ₋₂.-1+ n} ∣ a ∣ ∣ y ∣ (decode-fun _ _ ∣ p ∣) ≡ ∣ p ∣)
              (enc-refl ∣ a ∣))

  {- The final Iso established -}
  IsoFinal : (n : ℕ₋₂) (x y : ∥ B ∥ (suc₋₂ n)) → Iso (x ≡ y) (P x y)
  Iso.fun (IsoFinal _ x y) = encode-fun x y
  Iso.inv (IsoFinal _ x y) = decode-fun x y
  Iso.rightInv (IsoFinal _ x y) = P-linv x y
  Iso.leftInv (IsoFinal _ x y) = P-rinv x y

PathIdTrunc : {a b : A} (n : ℕ₋₂) → (Path (∥ A ∥ (suc₋₂ n)) ∣ a ∣ ∣ b ∣) ≡ (∥ a ≡ b ∥ n)
PathIdTrunc n = isoToPath (ΩTrunc.IsoFinal n _ _)

PathΩ : {a : A} (n : ℕ₋₂) → (Path (∥ A ∥ (suc₋₂ n)) ∣ a ∣ ∣ a ∣) ≡ (∥ a ≡ a ∥ n)
PathΩ n = PathIdTrunc n

--------------------------


truncOfTruncIso : (n m : ℕ) → Iso (hLevelTrunc n A) (hLevelTrunc n (hLevelTrunc (m + n) A))
Iso.fun (truncOfTruncIso n m) = elim (λ _ → isOfHLevelTrunc n) λ a → ∣ ∣ a ∣ ∣
Iso.inv (truncOfTruncIso {A = A} n m) =
  elim (λ _ → isOfHLevelTrunc n)
       (elim (λ _ → (isOfHLevelPlus m (isOfHLevelTrunc n )))
             λ a → ∣ a ∣)
Iso.rightInv (truncOfTruncIso {A = A} n m) =
  elim (λ x → isOfHLevelPath n (isOfHLevelTrunc n) _ _ )
               (elim (λ x → isOfHLevelPath (m + n) (isOfHLevelPlus m (isOfHLevelTrunc n)) _ _ )
                      λ a → refl)
Iso.leftInv (truncOfTruncIso n m) = elim (λ x → isOfHLevelPath n (isOfHLevelTrunc n) _ _) λ a → refl

truncOfTruncEq : (n m : ℕ) → (hLevelTrunc n A) ≃ (hLevelTrunc n (hLevelTrunc (m + n) A))
truncOfTruncEq n m = isoToEquiv (truncOfTruncIso n m)
