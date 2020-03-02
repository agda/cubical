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

open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.NatMinusOne  using (ℕ₋₁; neg1; suc; ℕ→ℕ₋₁) renaming (-1+_ to -1+₋₁_ ; 1+_ to 1+₋₁_)
import Cubical.Data.NatMinusOne as ℕ₋₁
open import Cubical.Data.NatMinusTwo
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Nullification

open import Cubical.HITs.Truncation.Base

open import Cubical.HITs.PropositionalTruncation renaming (∥_∥ to ∥_∥₋₁)
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.GroupoidTruncation
open import Cubical.HITs.2GroupoidTruncation

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

sphereFill : (n : ℕ₋₁) (f : S n → A) → Type _
sphereFill {A = A} n f = Σ[ top ∈ A ] ((x : S n) → top ≡ f x)

isSphereFilled : ℕ₋₁ → Type ℓ → Type ℓ
isSphereFilled n A = (f : S n → A) → sphereFill n f

isSphereFilled∥∥ : {n : ℕ₋₂} → isSphereFilled (1+ n) (∥ A ∥ n)
isSphereFilled∥∥ {n = neg2}  f = hub f , ⊥-elimDep
isSphereFilled∥∥ {n = suc _} f = hub f , spoke f

isSphereFilled→isOfHLevelSuc : {n : ℕ₋₂} → isSphereFilled (1+ suc n) A → isOfHLevel (2+ suc n) A
isSphereFilled→isOfHLevelSuc {A = A} {neg2} h x y = sym (snd (h f) north) ∙ snd (h f) south
  where
    f : Susp ⊥ → A
    f north = x
    f south = y
    f (merid () i)
isSphereFilled→isOfHLevelSuc {A = A} {suc n} h x y = isSphereFilled→isOfHLevelSuc (helper h x y)
  where
    helper : {n : ℕ₋₂} → isSphereFilled (suc (1+ suc n)) A → (x y : A) → isSphereFilled (1+ suc n) (x ≡ y)
    helper {n = n} h x y f = l , r
      where
        f' : Susp (S (1+ suc n)) → A
        f' north = x
        f' south = y
        f' (merid u i) = f u i

        u : sphereFill (suc (1+ suc n)) f'
        u = h f'

        z : A
        z = fst u

        p : z ≡ x
        p = snd u north

        q : z ≡ y
        q = snd u south

        l : x ≡ y
        l = sym p ∙ q

        r : (s : S (1+ suc n)) → l ≡ f s
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
isOfHLevel→isSphereFilled {A = A} {suc neg2} h f = f north , λ _ → h _ _
isOfHLevel→isSphereFilled {A = A} {suc (suc n)} h = helper λ x y → isOfHLevel→isSphereFilled (h x y)
  where
    helper : {n : ℕ₋₂} → ((x y : A) → isSphereFilled (1+ n) (x ≡ y)) → isSphereFilled (suc (1+ n)) A
    helper {n = n} h f = l , r
      where
      l : A
      l = f north

      f' : S (1+ n) → f north ≡ f south
      f' x i = f (merid x i)

      h' : sphereFill (1+ n) f'
      h' = h (f north) (f south) f'

      r : (x : S (suc (1+ n))) → l ≡ f x
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
isSnNull→isOfHLevel {n = neg2}  nA = fst (sec nA) ⊥-elim , λ y → fst (secCong nA _ y) (funExt ⊥-elimDep)
isSnNull→isOfHLevel {n = suc n} nA = isSphereFilled→isOfHLevelSuc (λ f → fst (sec nA) f , λ s i → snd (sec nA) f i s)

isOfHLevel∥∥ : (n : ℕ₋₂) → isOfHLevel (2+ n) (∥ A ∥ n)
isOfHLevel∥∥ neg2    = hub ⊥-elim , λ _ → ≡hub ⊥-elim
isOfHLevel∥∥ (suc n) = isSphereFilled→isOfHLevelSuc isSphereFilled∥∥

-- isOfHLevel∥∥ n = isSnNull→isOfHLevel isNull-Null

-- ∥_∥ n is a modality

rec : {n : ℕ₋₂}
      {B : Type ℓ'} →
      (isOfHLevel (2+ n) B) →
      (g : (a : A) → B) →
      (∥ A ∥ n → B)
rec {B = B} h = Null-ind {B = λ _ → B} λ x → isOfHLevel→isSnNull h

ind : {n : ℕ₋₂}
      {B : ∥ A ∥ n → Type ℓ'}
      (hB : (x : ∥ A ∥ n) → isOfHLevel (2+ n) (B x))
      (g : (a : A) → B (∣ a ∣))
      (x : ∥ A ∥ n) →
      B x
ind hB = Null-ind (λ x → isOfHLevel→isSnNull (hB x))

ind2 : {n : ℕ₋₂}
       {B : ∥ A ∥ n → ∥ A ∥ n → Type ℓ'}
       (hB : ((x y : ∥ A ∥ n) → isOfHLevel (2+ n) (B x y)))
       (g : (a b : A) → B ∣ a ∣ ∣ b ∣)
       (x y : ∥ A ∥ n) →
       B x y
ind2 {n = n} hB g = ind (λ _ → isOfHLevelPi (2+ n) (λ _ → hB _ _)) λ a →
                    ind (λ _ → hB _ _) (λ b → g a b)

ind3 : {n : ℕ₋₂}
       {B : (x y z : ∥ A ∥ n) → Type ℓ'}
       (hB : ((x y z : ∥ A ∥ n) → isOfHLevel (2+ n) (B x y z)))
       (g : (a b c : A) → B (∣ a ∣) ∣ b ∣ ∣ c ∣)
       (x y z : ∥ A ∥ n) →
       B x y z
ind3 {n = n} hB g = ind2 (λ _ _ → isOfHLevelPi (2+ n) (hB _ _)) λ a b →
                    ind (λ _ → hB _ _ _) (λ c → g a b c)

TruncModality : ∀ {ℓ} (n : ℕ₋₂) → Modality ℓ
isModal       (TruncModality n) = isOfHLevel (2+ n)
isModalIsProp (TruncModality n) = isPropIsOfHLevel (2+ n)
◯             (TruncModality n) = ∥_∥ n
◯-isModal     (TruncModality n) = isOfHLevel∥∥ n
η             (TruncModality n) = ∣_∣
◯-elim        (TruncModality n) = ind
◯-elim-β      (TruncModality n) = λ _ _ _ → refl
◯-=-isModal   (TruncModality n) = isOfHLevelPath (2+ n) (isOfHLevel∥∥ n)

idemTrunc : (n : ℕ₋₂) → isOfHLevel (2+ n) A → A ≃ (∥ A ∥ n)
idemTrunc n hA = ∣_∣ , isModalToIsEquiv (TruncModality n) hA

-- equivalences to prop/set/groupoid truncations

propTrunc≃Trunc-1 : ∥ A ∥₋₁ ≃ ∥ A ∥ -1
propTrunc≃Trunc-1 =
  isoToEquiv
    (iso
      (elimPropTrunc (λ _ → isOfHLevel∥∥ -1) ∣_∣)
      (ind (λ _ → propTruncIsProp) ∣_∣)
      (ind (λ _ → isOfHLevelPath 1 (isOfHLevel∥∥ -1) _ _) (λ _ → refl))
      (elimPropTrunc (λ _ → isOfHLevelPath 1 squash _ _) (λ _ → refl)))

setTrunc≃Trunc0 : ∥ A ∥₀ ≃ ∥ A ∥ 0
setTrunc≃Trunc0 =
  isoToEquiv
    (iso
      (elimSetTrunc (λ _ → isOfHLevel∥∥ 0) ∣_∣)
      (ind (λ _ → squash₀) ∣_∣₀)
      (ind (λ _ → isOfHLevelPath 2 (isOfHLevel∥∥ 0) _ _) (λ _ → refl))
      (elimSetTrunc (λ _ → isOfHLevelPath 2 squash₀ _ _) (λ _ → refl)))

groupoidTrunc≃Trunc1 : ∥ A ∥₁ ≃ ∥ A ∥ 1
groupoidTrunc≃Trunc1 =
  isoToEquiv
    (iso
      (groupoidTruncElim _ _ (λ _ → isOfHLevel∥∥ 1) ∣_∣)
      (ind (λ _ → squash₁) ∣_∣₁)
      (ind (λ _ → isOfHLevelPath 3 (isOfHLevel∥∥ 1) _ _) (λ _ → refl))
      (groupoidTruncElim _ _ (λ _ → isOfHLevelPath 3 squash₁ _ _) (λ _ → refl)))

2groupoidTrunc≃Trunc2 : ∥ A ∥₂ ≃ ∥ A ∥ 2
2groupoidTrunc≃Trunc2 =
  isoToEquiv
    (iso
      (g2TruncElim _ _ (λ _ → isOfHLevel∥∥ 2) ∣_∣)
      (ind (λ _ → squash₂) ∣_∣₂)
      (ind (λ _ → isOfHLevelPath 4 (isOfHLevel∥∥ 2) _ _) (λ _ → refl))
      (g2TruncElim _ _ (λ _ → isOfHLevelPath 4 squash₂ _ _) (λ _ → refl)))

---- ∥ Ω A ∥ ₙ ≡ Ω ∥ A ∥ₙ₊₁  ----

  {- Proofs of Theorem 7.3.12. and Corollary 7.3.13. in the HoTT book  -}

private
        {- We define the fibration P to show a more general result  -}
        P :  ∀ {ℓ} {B : Type ℓ}{n : ℕ₋₂} → ∥ B ∥  (suc n) → ∥ B ∥  (suc n) → Type ℓ
        P x y = fst (P₁ x y)

          where
          P₁ : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} → ∥ B ∥  (suc n) → ∥ B ∥  (suc n) → (HLevel  ℓ (2+ n))
          P₁ {ℓ} {n = n}  x y = ind2 (λ _ _  → isOfHLevelHLevel (2+ n))
                                        (λ a b → (∥ a ≡ b ∥  n , isOfHLevel∥∥ n ))
                                        x
                                        y

        {- We will need P to be of hLevel n + 3  -}
        hLevelP : ∀{ℓ} {n : ℕ₋₂} {B : Type ℓ}
                    (a b : ∥ B ∥ (suc n)) →
                    isOfHLevel (2+ (suc n)) (P a b )
        hLevelP {n = n} {B = B} = ind2 {A = B}
                                       {n =  (suc n)}
                                       {B = λ x y → isOfHLevel (2+ (suc n)) (P x y)}
                                       (λ x y → isProp→isOfHLevelSuc (2+ n) (isPropIsOfHLevel (2+ suc n)) )
                                       λ a b  → ( isOfHLevelSuc (2+ n) )
                                       (isOfHLevel∥∥ {A = a ≡ b} n)

        {- decode function from P x y to x ≡ y -}
        decode-fun :  ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} (x y : ∥ B ∥ (suc n)) →
                      P x y →
                      _≡_ {A = ∥ B ∥ (suc n)} x y

        decode-fun {B = B} {n = n} x y = ind2 {B = λ u v  → P u v →  _≡_ {A = ∥ B ∥ (suc n)} u v }
                                              (λ u v → isOfHLevelPi {A = P u v} {B = λ _ → u ≡ v}
                                              (2+ suc n)
                                              λ _ →  (((isOfHLevelSuc (2+ suc n) (isOfHLevel∥∥ {A = B} (suc n))) u v)) )
                                              decode* x y
            where
            decode* :  ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂}(u v : B) →
                         (P {n = n}
                            (∣_∣ {S = (S (1+ (suc n)))} u)
                            (∣_∣ {S = (S (1+ (suc n)))} v)) →
                         _≡_ {A = ∥ B ∥ (suc n) }
                             ∣ u ∣
                             ∣ v ∣
            decode* {B = B} {n = neg2} u v = rec {A = u ≡ v} {n = neg2}
                                                 {B = _≡_ {A = ∥ B ∥  (suc (neg2)) } (∣ u ∣)  (∣ v ∣)}
                                                 ((isOfHLevel∥∥ {A = B} (suc neg2) ∣ u ∣ ∣ v ∣) ,
                                                   λ y  → (isOfHLevelSuc (2+ suc neg2)
                                                                         (isOfHLevel∥∥ {A = B} (suc neg2)) ∣ u ∣ ∣ v ∣)
                                                   (isOfHLevel∥∥ {A = B} (suc neg2) ∣ u ∣ ∣ v ∣) y )
                                                 (λ p → cong (λ z → ∣ z ∣) p)
            decode* {B = B} {n = suc n} u v =  rec {A = u ≡ v} {n = suc n}
                                                   {B = _≡_ {A = ∥ B ∥  (suc (suc n)) } (∣ u ∣)  (∣ v ∣)}
                                                   (isOfHLevel∥∥ {A = B} (suc (suc n)) ∣ u ∣  ∣ v ∣)
                                                   (λ p → cong (λ z → ∣ z ∣) p)

        {- auxilliary function r used to define encode -}
        r :  ∀ {ℓ} {B : Type ℓ} {m : ℕ₋₂} (u : ∥ B ∥ (suc m)) → P u u
        r {m = m}  = ind {B = (λ u → P u u)}
                              (λ x → hLevelP x x)
                              (λ a → ∣ refl {x = a} ∣)

        {- encode function from x ≡ y to P x y -}
        encode-fun : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} (x y : ∥ B ∥ (suc n)) →
                    _≡_ {A = ∥ B ∥ (suc n)} x y →
                    P x y
        encode-fun x y p = transport (λ i → P x (p i )) (r x)

        {- We need the following two lemmas on the functions behaviour for refl -}
        dec-refl : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} (x : ∥ B ∥ (suc n)) →
                         decode-fun x x (r x) ≡ refl {x = x}
        dec-refl {B = B} {n = neg2} x = ind {A = B} {n = suc neg2}
                                            {B = λ x → decode-fun x x (r x) ≡ refl {x = x} }
                                            (λ x → (isOfHLevelSuc (2+ (suc neg2))
                                                     (isOfHLevelSuc (2+ (suc neg2))
                                                       (isOfHLevel∥∥ {A = B} (suc neg2)) x x))
                                                   (decode-fun x x (r x)) refl)
                                            (λ a → refl) x
        dec-refl {B = B} {n = suc n} = ind {A = B} {n = suc (suc n)}
                                           {B = λ x → decode-fun x x (r x) ≡ refl {x = x} }
                                           (λ x  → isOfHLevelSuc (2+ suc n)
                                                    (isOfHLevelSuc (2+ suc n)
                                                      (isOfHLevel∥∥ {A = B} (suc (suc n)) x x )
                                                    (decode-fun x x (r x)) refl))
                                           λ c → refl

        enc-refl : ∀ {ℓ} {B : Type ℓ}
                   {n : ℕ₋₂}
                   (x : ∥ B ∥ (suc n)) →
                   encode-fun x x (refl {x = x}) ≡ r x
        enc-refl x j = transp (λ i → P x (refl {x = x} i)) j (r x)

        {- decode-fun is a right-inverse -}
        P-rinv : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} (u v : ∥ B ∥  (suc n)) →
                     (x : _≡_ {A = ∥ B ∥ (suc n)} u v) →
                     decode-fun u v (encode-fun u v x) ≡ x
        P-rinv {ℓ = ℓ} {B = B} {n = n} u v = J {ℓ} { ∥ B ∥  (suc n)} {u} {ℓ}
                                              (λ y p → decode-fun u y (encode-fun u y p) ≡ p)
                                              ((λ i → (decode-fun u u (enc-refl u i))) ∙ dec-refl u)
                                              {v}

        {- decode-fun is a left-inverse -}
        P-linv : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} (u v : ∥ B ∥ (suc n )) →
                   (x : P u v) →
                   encode-fun u v (decode-fun u v x) ≡ x
        P-linv {ℓ = ℓ} {B = B} {n = n} u v = ind2 {A = B}
                                                 {n = (suc n)}
                                                 {B = λ u v → (x : P u v) → encode-fun u v (decode-fun u v x) ≡ x}
                                                 (λ x y → isOfHLevelPi {A = P x y}
                                                                       (2+ suc n)
                                                                       λ z → isOfHLevelSuc (2+ suc n)
                                                                                           (hLevelP {n = n} x y) (encode-fun x y (decode-fun x y z)) z)
                                                 helper u v
          where
          helper : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂}
                   (a b : B)
                   (x : P {n = n} ∣ a ∣ ∣ b ∣) →
                   encode-fun ∣ a ∣ ∣ b ∣ (decode-fun ∣ a ∣ ∣ b ∣ x) ≡ x
          helper {ℓ = ℓ} {B = B} {n = neg2} a b = ind {A = (a ≡ b)}
                                                     {n =  neg2}
                                                     {B = λ x → encode-fun ∣ a ∣ ∣ b ∣ (decode-fun ∣ a ∣ ∣ b ∣ x) ≡ x}
                                                     (λ x → (sym ((snd (isOfHLevel∥∥ {A = a ≡ b} neg2))
                                                                  (encode-fun ∣ a ∣ ∣ b ∣ (decode-fun ∣ a ∣ ∣ b ∣ x)))
                                                               ∙ ((snd (isOfHLevel∥∥ {A = a ≡ b} neg2)) x))
                                                            ,
                                                            λ y  → isOfHLevelSuc (2+ (suc neg2))
                                                                     (isOfHLevelSuc (2+ neg2) (isOfHLevel∥∥ {A = a ≡ b} (neg2)))
                                                                     (encode-fun ∣ a ∣ ∣ b ∣ (decode-fun ∣ a ∣ ∣ b ∣ x)) x
                                                                      ((sym ((snd (isOfHLevel∥∥ {A = a ≡ b} neg2))
                                                                             (encode-fun ∣ a ∣ ∣ b ∣ (decode-fun ∣ a ∣ ∣ b ∣ x)))
                                                                          ∙ ((snd (isOfHLevel∥∥ {A = a ≡ b} neg2)) x)))
                                                                          y)
                                                     (J {ℓ}{B}{a}{ℓ}
                                                     ((λ y p → (encode-fun {n = neg2}) ∣ a ∣ ∣ y ∣
                                                                           ((decode-fun ∣ a ∣ ∣ y ∣) ∣ p ∣) ≡ ∣ p ∣))
                                                     (enc-refl {n = neg2} ∣ a ∣ )
                                                     {b})
          helper {ℓ = ℓ} {B = B} {n = suc n} a b = ind {A = (a ≡ b)}
                                                      {n =  suc n}
                                                      {B = λ x → encode-fun ∣ a ∣ ∣ b ∣ (decode-fun ∣ a ∣ ∣ b ∣ x) ≡ x}
                                                      (λ x → (hLevelP {n = suc n} ∣ a ∣ ∣ b ∣ (encode-fun ∣ a ∣ ∣ b ∣ (decode-fun ∣ a ∣ ∣ b ∣ x)) x) )
                                                      (J {ℓ}{B}{a}{ℓ} ((λ y p → (encode-fun {n = suc n}) ∣ a ∣ ∣ y ∣ ((decode-fun ∣ a ∣ ∣ y ∣) ∣ p ∣) ≡ ∣ p ∣))
                                                      (enc-refl {n = suc n} ∣ a ∣ )
                                                      {b})

        {- The final Iso established -}
        IsoFinal : ∀ {ℓ} {B : Type ℓ} {n : ℕ₋₂} (x y : ∥ B ∥ (suc n)) → Iso (x ≡ y) (P x y)
        IsoFinal x y = iso (encode-fun x y ) (decode-fun x y) (P-linv x y) (P-rinv x y)

PathIdTrunc : {a b : A} (n : ℕ₋₂) → (_≡_ {A = ∥ A ∥ (suc n)} ∣ a ∣ ∣ b ∣) ≡ (∥ a ≡ b ∥ n)
PathIdTrunc {a = a} {b = b} n = isoToPath (IsoFinal {n = n} ∣ a ∣ ∣ b ∣)

PathΩ : {a : A} (n : ℕ₋₂) → (_≡_ {A = ∥ A ∥ (suc n)} ∣ a ∣ ∣ a ∣) ≡ (∥ a ≡ a ∥ n)
PathΩ {a = a} n = PathIdTrunc {a = a} {b = a} n
