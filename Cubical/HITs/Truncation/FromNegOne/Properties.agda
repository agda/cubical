{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Truncation.FromNegOne.Properties where
open import Cubical.Data.NatMinusOne
open import Cubical.HITs.Truncation.FromNegOne.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv.PathSplit
open isPathSplitEquiv
open import Cubical.Modalities.Modality
open Modality

open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.NatMinusOne as ℕ₋₁
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification as Null hiding (rec; elim)

open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (∥_∥ to ∥_∥₁; ∣_∣ to ∣_∣₁; squash to squash₁) using ()
open import Cubical.HITs.SetTruncation       as SetTrunc  using (∥_∥₂; ∣_∣₂; squash₂)
open import Cubical.HITs.GroupoidTruncation  as GpdTrunc  using (∥_∥₃; ∣_∣₃; squash₃)
open import Cubical.HITs.2GroupoidTruncation as 2GpdTrunc using (∥_∥₄; ∣_∣₄; squash₄)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

open import Cubical.HITs.Truncation.Properties using (sphereFill; isSphereFilled)

isSphereFilled∥∥ : {n : ℕ₋₁} → isSphereFilled (suc₋₁ n) (∥ A ∥⁻¹ n)
isSphereFilled∥∥ f = (hub f) , (spoke f)

isSphereFilled→isOfHLevel : (n : ℕ₋₁) → isSphereFilled (suc₋₁ n) A → isOfHLevel (1 + 1+ n) A
isSphereFilled→isOfHLevel {A = A} neg1 h x y = sym (snd (h f) north) ∙ snd (h f) south
  where
    f : Susp ⊥ → A
    f north = x
    f south = y
    f (merid () i)
isSphereFilled→isOfHLevel {A = A} (ℕ→ℕ₋₁ n) h x y = isSphereFilled→isOfHLevel (-1+ n) (helper h x y)
  where
    helper : {n : ℕ₋₁} → isSphereFilled (suc₋₁ n) A → (x y : A) → isSphereFilled n (x ≡ y)
    helper {n = n} h x y f = l , r
      where
        f' : Susp (S n) → A
        f' north = x
        f' south = y
        f' (merid u i) = f u i

        u : sphereFill (suc₋₁ n) f'
        u = h f'

        z : A
        z = fst u

        p : z ≡ x
        p = snd u north

        q : z ≡ y
        q = snd u south

        l : x ≡ y
        l = sym p ∙ q

        r : (s : S n) → l ≡ f s
        r s i j = hcomp
                    (λ k →
                       λ { (i = i0) → compPath-filler (sym p) q k j
                         ; (i = i1) → snd u (merid s j) k
                         ; (j = i0) → p (k ∨ (~ i))
                         ; (j = i1) → q k
                         })
                  (p ((~ i) ∧ (~ j)))

isOfHLevel→isSphereFilled : (n : ℕ₋₁) → isOfHLevel (1 + 1+ n) A → isSphereFilled (suc₋₁ n) A
isOfHLevel→isSphereFilled neg1 h f = (f north) , (λ _ → h _ _)
isOfHLevel→isSphereFilled {A = A} (ℕ→ℕ₋₁ n) h = helper λ x y → isOfHLevel→isSphereFilled (-1+ n) (h x y)
  where
    helper : {n : ℕ₋₁} → ((x y : A) → isSphereFilled n (x ≡ y)) → isSphereFilled (suc₋₁ n) A
    helper {n = n} h f = l , r
      where
      l : A
      l = f north

      f' : S n → f north ≡ f south
      f' x i = f (merid x i)

      h' : sphereFill n f'
      h' = h (f north) (f south) f'

      r : (x : S (suc₋₁ n)) → l ≡ f x
      r north = refl
      r south = h' .fst
      r (merid x i) j = hcomp (λ k → λ { (i = i0) → f north
                                        ; (i = i1) → h' .snd x (~ k) j
                                        ; (j = i0) → f north
                                        ; (j = i1) → f (merid x i) }) (f (merid x (i ∧ j)))

isOfHLevelTrunc : (n : ℕ) → isOfHLevel n (∥ A ∥ n)
isOfHLevelTrunc zero = isOfHLevelUnit* 0
isOfHLevelTrunc (suc n) = isSphereFilled→isOfHLevel (-1+ n) isSphereFilled∥∥

rec : {n : HLevel}
      {B : Type ℓ'} →
      isOfHLevel (suc n) B →
      (A → B) →
      hLevelTrunc (suc n) A →
      B
rec h g ∣ x ∣ = g x
rec {n = n} {B = B} hB g (hub f) = isOfHLevel→isSphereFilled (-1+ n) hB (λ x → rec hB g (f x)) .fst
rec {n = n} hB g (spoke f x i) =
  isOfHLevel→isSphereFilled (-1+ n) hB (λ x → rec hB g (f x)) .snd x i

elim : {n : ℕ}
      {B : ∥ A ∥ (suc n) → Type ℓ'}
      (hB : (x : ∥ A ∥ (suc n)) → isOfHLevel (suc n) (B x))
      (g : (a : A) → B (∣ a ∣))
      (x : ∥ A ∥ (suc n)) →
      B x
elim hB g (∣ a ∣ ) = g a
elim {B = B} hB g (hub f) =
  isOfHLevel→isSphereFilled _ (hB (hub f)) (λ x → subst B (sym (spoke f x)) (elim hB g (f x)) ) .fst
elim {B = B} hB g (spoke f x i) =
  toPathP {A = λ i → B (spoke f x (~ i))}
    (sym (isOfHLevel→isSphereFilled _ (hB (hub f)) (λ x → subst B (sym (spoke f x)) (elim hB g (f x))) .snd x))
    (~ i)

elim2 : {n : ℕ}
       {B : ∥ A ∥ (suc n) → ∥ A ∥ (suc n) → Type ℓ'}
       (hB : ((x y : ∥ A ∥ (suc n)) → isOfHLevel (suc n) (B x y)))
       (g : (a b : A) → B ∣ a ∣ ∣ b ∣)
       (x y : ∥ A ∥ (suc n)) →
       B x y
elim2 {n = n} hB g = elim (λ _ → isOfHLevelΠ (suc n) (λ _ → hB _ _)) λ a →
                    elim (λ _ → hB _ _) (λ b → g a b)

elim3 : {n : ℕ}
       {B : (x y z : ∥ A ∥ (suc n)) → Type ℓ'}
       (hB : ((x y z : ∥ A ∥ (suc n)) → isOfHLevel (suc n) (B x y z)))
       (g : (a b c : A) → B (∣ a ∣) ∣ b ∣ ∣ c ∣)
       (x y z : ∥ A ∥ (suc n)) →
       B x y z
elim3 {n = n} hB g = elim2 (λ _ _ → isOfHLevelΠ (suc n) (hB _ _)) λ a b →
                    elim (λ _ → hB _ _ _) (λ c → g a b c)

minΣ : (n m : ℕ) → Σ[ x ∈ ℕ ] x + min n m ≡ n
minΣ zero m = 0 , refl
minΣ (suc n) zero = (suc n) , cong suc (+-zero n)
minΣ (suc n) (suc m) = (minΣ n m .fst) , +-suc _ _ ∙ cong suc (minΣ n m .snd)

minComm : (n m : ℕ) → min n m ≡ min m n
minComm zero zero = refl
minComm zero (suc m) = refl
minComm (suc n) zero = refl
minComm (suc n) (suc m) = cong suc (minComm n m)

isOfHLevelMin→isOfHLevel : {n m : ℕ} → isOfHLevel (min n m) A → isOfHLevel n A × isOfHLevel m A
isOfHLevelMin→isOfHLevel {n = zero} {m = m} h = h , isContr→isOfHLevel m h
isOfHLevelMin→isOfHLevel {n = suc n} {m = zero} h = (isContr→isOfHLevel (suc n) h) , h
isOfHLevelMin→isOfHLevel {A = A} {n = suc n} {m = suc m} h = (subst (λ x → isOfHLevel x A) (minΣ (suc n) (suc m) .snd) (isOfHLevelPlus _ h))
                                                           , subst (λ x → isOfHLevel x A) (cong (λ y → minΣ m n .fst + suc y) (minComm n m) ∙ minΣ (suc m) (suc n) .snd) (isOfHLevelPlus _ h)

open import Cubical.Data.Nat hiding (elim )
ΣTruncElim : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {n m : ℕ}
              {B : (x : ∥ A ∥ (suc n)) → Type ℓ'}
              {C : (Σ[ a ∈ (∥ A ∥ (suc n)) ] (∥ B a ∥ (suc m))) → Type ℓ''}
              → ((x : (Σ[ a ∈ (∥ A ∥ (suc n)) ] (∥ B a ∥ (suc m)))) → isOfHLevel (min (suc n) (suc m)) (C x))
              → ((a : A) (b : B (∣ a ∣)) → C (∣ a ∣ , ∣ b ∣))
              → (x : (Σ[ a ∈ (∥ A ∥ (suc n)) ] (∥ B a ∥ (suc m)))) → (C x)
ΣTruncElim {n = n} {m = m} {B = B} {C = C} hB g (a , b) = (elim {B = λ a → (b :  (∥ B a ∥ (suc m))) → C (a , b)} (λ x → isOfHLevelΠ (suc n) λ b → isOfHLevelMin→isOfHLevel (hB (x , b)) .fst ) (λ a → elim (λ _ → isOfHLevelMin→isOfHLevel (hB (∣ a ∣ , _)) .snd) λ b → g a b) a) b

truncIdempotentIso : (n : ℕ) → isOfHLevel n A → Iso (∥ A ∥ n) A
truncIdempotentIso zero hA = isContr→Iso (isOfHLevelUnit* 0) hA
Iso.fun (truncIdempotentIso (suc n) hA) = rec hA λ a → a
Iso.inv (truncIdempotentIso (suc n) hA) = ∣_∣
Iso.rightInv (truncIdempotentIso (suc n) hA) _ = refl
Iso.leftInv (truncIdempotentIso (suc n) hA) = elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) λ _ → refl

truncIdempotent≃ : (n : ℕ) → isOfHLevel n A → ∥ A ∥ n ≃ A
truncIdempotent≃ n hA = isoToEquiv (truncIdempotentIso n hA)

truncIdempotent : (n : ℕ) → isOfHLevel n A → ∥ A ∥ n ≡ A
truncIdempotent n hA = ua (truncIdempotent≃ n hA)

HLevelTruncModality : ∀ {ℓ} (n : HLevel) → Modality ℓ
isModal       (HLevelTruncModality n) = isOfHLevel n
isModalIsProp (HLevelTruncModality n) = isPropIsOfHLevel n
◯             (HLevelTruncModality n) = hLevelTrunc n
◯-isModal     (HLevelTruncModality n) = isOfHLevelTrunc n
η (HLevelTruncModality zero) _ = tt*
η (HLevelTruncModality (suc n)) = ∣_∣
◯-elim (HLevelTruncModality zero) cB _ tt* = cB tt* .fst
◯-elim (HLevelTruncModality (suc n)) = elim
◯-elim-β (HLevelTruncModality zero) cB f a = cB tt* .snd (f a)
◯-elim-β (HLevelTruncModality (suc n)) = λ _ _ _ → refl
◯-=-isModal (HLevelTruncModality zero) x y = (isOfHLevelUnit* 1 x y) , (isOfHLevelUnit* 2 x y _)
◯-=-isModal (HLevelTruncModality (suc n)) = isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n))

-- universal property

univTrunc : ∀ {ℓ} (n : HLevel) {B : TypeOfHLevel ℓ n} → Iso (hLevelTrunc n A → B .fst) (A → B .fst)
univTrunc zero {B , lev} = isContr→Iso (isOfHLevelΠ 0 (λ _ → lev)) (isOfHLevelΠ 0 λ _ → lev)
Iso.fun (univTrunc (suc n) {B , lev}) g a = g ∣ a ∣
Iso.inv (univTrunc (suc n) {B , lev}) = elim λ _ → lev
Iso.rightInv (univTrunc (suc n) {B , lev}) b = refl
Iso.leftInv (univTrunc (suc n) {B , lev}) b = funExt (elim (λ x → isOfHLevelPath _ lev _ _)
                                                            λ a → refl)

-- functorial action

map : {n : HLevel} {B : Type ℓ'} (g : A → B)
  → hLevelTrunc n A → hLevelTrunc n B
map {n = zero} g = λ _ → tt*
map {n = suc n} g = rec (isOfHLevelTrunc _) (λ a → ∣ g a ∣)

mapCompIso : {n : HLevel} {B : Type ℓ'} → (Iso A B) → Iso (hLevelTrunc n A) (hLevelTrunc n B)
mapCompIso {n = zero} {B} _ = isContr→Iso (isOfHLevelUnit* 0) (isOfHLevelUnit* 0)
Iso.fun (mapCompIso {n = (suc n)} g) = map (Iso.fun g)
Iso.inv (mapCompIso {n = (suc n)} g) = map (Iso.inv g)
Iso.rightInv (mapCompIso {n = (suc n)} g) = elim (λ x → isOfHLevelPath _ (isOfHLevelTrunc _) _ _) λ b → cong ∣_∣ (Iso.rightInv g b)
Iso.leftInv (mapCompIso {n = (suc n)} g) = elim (λ x → isOfHLevelPath _ (isOfHLevelTrunc _) _ _) λ a → cong ∣_∣ (Iso.leftInv g a)

mapId : {n : HLevel} → ∀ t → map {n = n} (idfun A) t ≡ t
mapId {n = 0} tt* = refl
mapId {n = (suc n)} =
  elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) (λ _ → refl)

-- equivalences to prop/set/groupoid truncations

propTruncTrunc1Iso : Iso ∥ A ∥₁ (∥ A ∥ 1)
Iso.fun propTruncTrunc1Iso = PropTrunc.elim (λ _ → isOfHLevelTrunc 1) ∣_∣
Iso.inv propTruncTrunc1Iso = elim (λ _ → squash₁) ∣_∣₁
Iso.rightInv propTruncTrunc1Iso = elim (λ _ → isOfHLevelPath 1 (isOfHLevelTrunc 1) _ _) (λ _ → refl)
Iso.leftInv propTruncTrunc1Iso = PropTrunc.elim (λ _ → isOfHLevelPath 1 squash₁ _ _) (λ _ → refl)

propTrunc≃Trunc1 : ∥ A ∥₁ ≃ ∥ A ∥ 1
propTrunc≃Trunc1 = isoToEquiv propTruncTrunc1Iso

propTrunc≡Trunc1 : ∥ A ∥₁ ≡ ∥ A ∥ 1
propTrunc≡Trunc1 = ua propTrunc≃Trunc1


setTruncTrunc2Iso : Iso ∥ A ∥₂ (∥ A ∥ 2)
Iso.fun setTruncTrunc2Iso = SetTrunc.elim (λ _ → isOfHLevelTrunc 2) ∣_∣
Iso.inv setTruncTrunc2Iso = elim (λ _ → squash₂) ∣_∣₂
Iso.rightInv setTruncTrunc2Iso = elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _) (λ _ → refl)
Iso.leftInv setTruncTrunc2Iso = SetTrunc.elim (λ _ → isOfHLevelPath 2 squash₂ _ _) (λ _ → refl)

setTrunc≃Trunc2 : ∥ A ∥₂ ≃ ∥ A ∥ 2
setTrunc≃Trunc2 = isoToEquiv setTruncTrunc2Iso

propTrunc≡Trunc2 : ∥ A ∥₂ ≡ ∥ A ∥ 2
propTrunc≡Trunc2 = ua setTrunc≃Trunc2

groupoidTrunc≃Trunc3Iso : Iso ∥ A ∥₃ (∥ A ∥ 3)
Iso.fun groupoidTrunc≃Trunc3Iso = GpdTrunc.elim (λ _ → isOfHLevelTrunc 3) ∣_∣
Iso.inv groupoidTrunc≃Trunc3Iso = elim (λ _ → squash₃) ∣_∣₃
Iso.rightInv groupoidTrunc≃Trunc3Iso = elim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _) (λ _ → refl)
Iso.leftInv groupoidTrunc≃Trunc3Iso = GpdTrunc.elim (λ _ → isOfHLevelPath 3 squash₃ _ _) (λ _ → refl)

groupoidTrunc≃Trunc3 : ∥ A ∥₃ ≃ ∥ A ∥ 3
groupoidTrunc≃Trunc3 = isoToEquiv groupoidTrunc≃Trunc3Iso

groupoidTrunc≡Trunc3 : ∥ A ∥₃ ≡ ∥ A ∥ 3
groupoidTrunc≡Trunc3 = ua groupoidTrunc≃Trunc3


2GroupoidTrunc≃Trunc4Iso : Iso ∥ A ∥₄ (∥ A ∥ 4)
Iso.fun 2GroupoidTrunc≃Trunc4Iso = 2GpdTrunc.elim (λ _ → isOfHLevelTrunc 4) ∣_∣
Iso.inv 2GroupoidTrunc≃Trunc4Iso = elim (λ _ → squash₄) ∣_∣₄
Iso.rightInv 2GroupoidTrunc≃Trunc4Iso = elim (λ _ → isOfHLevelPath 4 (isOfHLevelTrunc 4) _ _) (λ _ → refl)
Iso.leftInv 2GroupoidTrunc≃Trunc4Iso = 2GpdTrunc.elim (λ _ → isOfHLevelPath 4 squash₄ _ _) (λ _ → refl)

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


isContr→isContrTrunc : ∀ {ℓ} {A : Type ℓ} (n : ℕ) → isContr A → isContr (hLevelTrunc n A)
isContr→isContrTrunc zero contr = isOfHLevelUnit* 0
isContr→isContrTrunc (suc n) contr =
  ∣ fst contr ∣ , (elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) λ a → cong ∣_∣ (snd contr a))


truncOfProdIso : (n : ℕ) → Iso (hLevelTrunc n (A × B)) (hLevelTrunc n A × hLevelTrunc n B)
truncOfProdIso 0 = isContr→Iso (isOfHLevelUnit* 0) (isOfHLevel× 0 (isOfHLevelUnit* 0) (isOfHLevelUnit* 0))
Iso.fun (truncOfProdIso (suc n)) = rec (isOfHLevelΣ (suc n) (isOfHLevelTrunc (suc n)) (λ _ → isOfHLevelTrunc (suc n))) λ {(a , b) → ∣ a ∣ , ∣ b ∣}
Iso.inv (truncOfProdIso (suc n)) (a , b) = rec (isOfHLevelTrunc (suc n))
                                          (λ a → rec (isOfHLevelTrunc (suc n))
                                                      (λ b → ∣ a , b ∣)
                                                       b)
                                          a
Iso.rightInv (truncOfProdIso (suc n)) (a , b) =
  elim {B = λ a → Iso.fun (truncOfProdIso (suc n)) (Iso.inv (truncOfProdIso (suc n)) (a , b)) ≡ (a , b)}
       (λ _ → isOfHLevelPath (suc n) (isOfHLevelΣ (suc n) (isOfHLevelTrunc (suc n)) (λ _ → isOfHLevelTrunc (suc n))) _ _)
       (λ a → elim {B = λ b → Iso.fun (truncOfProdIso (suc n)) (Iso.inv (truncOfProdIso (suc n)) (∣ a ∣ , b)) ≡ (∣ a ∣ , b)}
                    (λ _ → isOfHLevelPath (suc n) (isOfHLevelΣ (suc n) (isOfHLevelTrunc (suc n)) (λ _ → isOfHLevelTrunc (suc n))) _ _)
                    (λ b → refl) b) a
Iso.leftInv (truncOfProdIso (suc n)) = elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) λ a → refl

---- ∥ Ω A ∥ ₙ ≡ Ω ∥ A ∥ₙ₊₁  ----


  {- Proofs of Theorem 7.3.12. and Corollary 7.3.13. in the HoTT book  -}

module ΩTrunc where
  {- We define the fibration P to show a more general result  -}
  P : {X : Type ℓ} {n : HLevel} → ∥ X ∥ (2 + n) → ∥ X ∥ (2 + n) → Type ℓ
  P {n = n} x y =  elim2 (λ _ _  → isOfHLevelTypeOfHLevel (suc n))
                         (λ a b → ∥ a ≡ b ∥ (suc n) , isOfHLevelTrunc (suc n)) x y .fst

  {- We will need P to be of hLevel n + 3  -}
  hLevelP : {X : Type ℓ} {n : HLevel} (a b : ∥ X ∥ (2 + n)) → isOfHLevel ((2 + n)) (P a b)
  hLevelP {n = n} =
    elim2 (λ x y → isProp→isOfHLevelSuc (suc n) (isPropIsOfHLevel (2 + n)))
          (λ a b → isOfHLevelSuc (suc n) (isOfHLevelTrunc (suc n)))

  {- decode function from P x y to x ≡ y -}
  decode-fun : {X : Type ℓ} {n : HLevel} (x y : ∥ X ∥ (2 + n)) → P x y → x ≡ y
  decode-fun {n = n} =
    elim2 (λ u v → isOfHLevelΠ (2 + n)
                                (λ _ → isOfHLevelSuc (2 + n) (isOfHLevelTrunc (2 + n)) u v))
          decode*
      where
      decode* : ∀ {n : HLevel} (u v : B)
              → P {n = n} ∣ u ∣ ∣ v ∣ → Path (∥ B ∥ (2 + n)) ∣ u ∣ ∣ v ∣
      decode* {B = B} {n = zero} u v = rec (isOfHLevelTrunc 2 _ _) (cong ∣_∣)
      decode* {n = suc n} u v =
        rec (isOfHLevelTrunc (3 + n) ∣ u ∣ ∣ v ∣) (cong ∣_∣)

  {- auxiliary function r used to define encode -}
  r : {X : Type ℓ} {n : HLevel} (u : ∥ X ∥ (2 + n)) → P u u
  r = elim (λ x → hLevelP x x) (λ a → ∣ refl ∣)

  {- encode function from x ≡ y to P x y -}
  encode-fun : {X : Type ℓ} {n : HLevel} (x y : ∥ X ∥ (2 + n)) → x ≡ y → P x y
  encode-fun x y p = subst (P x) p (r x)

  {- We need the following two lemmas on the functions behaviour for refl -}
  dec-refl : {X : Type ℓ} {n : HLevel} (x : ∥ X ∥ (2 + n)) → decode-fun x x (r x) ≡ refl
  dec-refl {n = zero} =
    elim (λ _ → isOfHLevelSuc 2 (isOfHLevelSuc 1 (isOfHLevelTrunc 2 _ _)) _ _) λ _ → refl
  dec-refl {n = suc n} =
    elim (λ x → isOfHLevelSuc (2 + n)
                  (isOfHLevelSuc (2 + n)
                     (isOfHLevelTrunc (3 + n) x x)
                     (decode-fun x x (r x)) refl))
         (λ _ → refl)

  enc-refl : {X : Type ℓ} {n : HLevel} (x : ∥ X ∥ (2 + n)) → encode-fun x x refl ≡ r x
  enc-refl x j = transp (λ _ → P x x) j (r x)

  {- decode-fun is a right-inverse -}
  P-rinv : {X : Type ℓ} {n : HLevel} (u v : ∥ X ∥ (2 + n)) (x : Path (∥ X ∥ (2 + n)) u v)
         → decode-fun u v (encode-fun u v x) ≡ x
  P-rinv u v = J (λ y p → decode-fun u y (encode-fun u y p) ≡ p)
                 (cong (decode-fun u u) (enc-refl u) ∙ dec-refl u)

  {- decode-fun is a left-inverse -}
  P-linv : {X : Type ℓ} {n : HLevel} (u v : ∥ X ∥ (2 + n)) (x : P u v)
         → encode-fun u v (decode-fun u v x) ≡ x
  P-linv {n = n} =
    elim2 (λ x y → isOfHLevelΠ (2 + n)
                               (λ z → isOfHLevelSuc (2 + n) (hLevelP x y) _ _))
          helper
    where
    helper : {X : Type ℓ} {n : HLevel} (a b : X) (p : P {n = n} ∣ a ∣ ∣ b ∣)
           → encode-fun _ _ (decode-fun ∣ a ∣ ∣ b ∣ p) ≡ p
    helper {n = zero} a b =
      elim (λ _ → isOfHLevelPath 1 (isOfHLevelTrunc 1) _ _)
           (J (λ y p → encode-fun ∣ a ∣ ∣ y ∣ (decode-fun _ _ ∣ p ∣) ≡ ∣ p ∣)
              (enc-refl ∣ a ∣))
    helper {n = suc n} a b =
      elim (λ x → hLevelP {n = suc n} ∣ a ∣ ∣ b ∣ _ _)
           (J (λ y p → encode-fun {n = (suc n)} ∣ a ∣ ∣ y ∣ (decode-fun _ _ ∣ p ∣) ≡ ∣ p ∣)
              (enc-refl ∣ a ∣))

  {- The final Iso established -}
  IsoFinal : {B : Type ℓ} (n : HLevel) (x y : ∥ B ∥ (2 + n)) → Iso (x ≡ y) (P x y)
  Iso.fun (IsoFinal _ x y) = encode-fun x y
  Iso.inv (IsoFinal _ x y) = decode-fun x y
  Iso.rightInv (IsoFinal _ x y) = P-linv x y
  Iso.leftInv (IsoFinal _ x y) = P-rinv x y

PathIdTruncIso : {a b : A} (n : HLevel) → Iso (Path (∥ A ∥ (suc n)) ∣ a ∣ ∣ b ∣) (∥ a ≡ b ∥ n)
PathIdTruncIso zero = isContr→Iso ((isOfHLevelTrunc 1 _ _)
                    , isOfHLevelPath 1 (isOfHLevelTrunc 1) ∣ _ ∣ ∣ _ ∣ _) (isOfHLevelUnit* 0)
PathIdTruncIso (suc n) = ΩTrunc.IsoFinal n ∣ _ ∣ ∣ _ ∣

PathIdTrunc : {a b : A} (n : HLevel) → (Path (∥ A ∥ (suc n)) ∣ a ∣ ∣ b ∣) ≡ (∥ a ≡ b ∥ n)
PathIdTrunc n = isoToPath (PathIdTruncIso n)

PathΩ : {a : A} (n : HLevel) → (Path (∥ A ∥ (suc n)) ∣ a ∣ ∣ a ∣) ≡ (∥ a ≡ a ∥ n)
PathΩ n = PathIdTrunc n

{- Special case using direct defs of truncations -}
PathIdTrunc₀Iso : {a b : A} → Iso (∣ a ∣₂ ≡ ∣ b ∣₂) ∥ a ≡ b ∥₁
PathIdTrunc₀Iso = compIso (congIso setTruncTrunc2Iso)
                    (compIso (ΩTrunc.IsoFinal _ ∣ _ ∣ ∣ _ ∣)
                             (invIso propTruncTrunc1Iso))

-------------------------

truncOfTruncIso : (n m : HLevel) → Iso (hLevelTrunc n A) (hLevelTrunc n (hLevelTrunc (m + n) A))
truncOfTruncIso zero m = isContr→Iso (isOfHLevelUnit* 0) (isOfHLevelUnit* 0)
Iso.fun (truncOfTruncIso (suc n) zero) = elim (λ _ → isOfHLevelTrunc (suc n)) λ a → ∣ ∣ a ∣ ∣
Iso.fun (truncOfTruncIso (suc n) (suc m)) = elim (λ _ → isOfHLevelTrunc (suc n)) λ a → ∣ ∣ a ∣ ∣
Iso.inv (truncOfTruncIso (suc n) zero) =  elim (λ _ → isOfHLevelTrunc (suc n))
                                               (elim (λ _ → (isOfHLevelTrunc (suc n)))
                                                     λ a → ∣ a ∣)
Iso.inv (truncOfTruncIso (suc n) (suc m)) =  elim (λ _ → isOfHLevelTrunc (suc n))
                                                  (elim (λ _ → (isOfHLevelPlus (suc m) (isOfHLevelTrunc (suc n))))
                                                        λ a → ∣ a ∣)
Iso.rightInv (truncOfTruncIso (suc n) zero) =
  elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _ )
       (elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _ )
              λ a → refl)
Iso.rightInv (truncOfTruncIso (suc n) (suc m)) =
  elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _ )
               (elim (λ x → isOfHLevelPath ((suc m) + (suc n)) (isOfHLevelPlus (suc m) (isOfHLevelTrunc (suc n))) _ _ )
                      λ a → refl)
Iso.leftInv (truncOfTruncIso (suc n) zero) = elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) λ a → refl
Iso.leftInv (truncOfTruncIso (suc n) (suc m)) = elim (λ x → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _) λ a → refl

truncOfTruncEq : (n m : ℕ) → (hLevelTrunc n A) ≃ (hLevelTrunc n (hLevelTrunc (m + n) A))
truncOfTruncEq n m = isoToEquiv (truncOfTruncIso n m)
