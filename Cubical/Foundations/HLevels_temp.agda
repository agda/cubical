{-# OPTIONS --safe #-}
module Cubical.Foundations.HLevels_temp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Core.Glue public
  using (Glue ; glue ; unglue)
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Sigma

private
  variable
    ℓ : Level
    A : Type ℓ
    B : A → Type ℓ

ua : ∀ {A B : Type ℓ} → A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                   ; (i = i1) → (B , idEquiv B) })
pathToEquiv : {A B : Type ℓ} → A ≡ B → A ≃ B
pathToEquiv p .fst = transport p
pathToEquiv p .snd = {!!} -- isEquivTransport p

pathToEquivRefl : {A : Type ℓ} → pathToEquiv refl ≡ idEquiv A
pathToEquivRefl {A = A} = equivEq (λ i x → transp (λ _ → A) i x)

uaIdEquiv : {A : Type ℓ} → ua (idEquiv A) ≡ refl
uaIdEquiv {A = A} i j = Glue A {φ = i ∨ ~ j ∨ j} (λ _ → A , idEquiv A)

ua-pathToEquiv : {A B : Type ℓ} (p : A ≡ B) → ua (pathToEquiv p) ≡ p
ua-pathToEquiv =
  J (λ _ p → ua (pathToEquiv p) ≡ p) (cong ua pathToEquivRefl ∙ uaIdEquiv)

hContr hSet hGroupoid : ∀ ℓ → Type (ℓ-suc ℓ)
hContr     ℓ = Σ[ A ∈ Type ℓ ] isContr A
hSet       ℓ = Σ[ A ∈ Type ℓ ] isSet A
hGroupoid  ℓ = Σ[ A ∈ Type ℓ ] isGroupoid A

isPropIsSet : isProp (isSet A)
isPropIsSet f g i a b = isPropIsProp (f a b) (g a b) i

isPropIsGroupoid : isProp (isGroupoid A)
isPropIsGroupoid f g i a b = isPropIsSet (f a b) (g a b) i

isPropΣ : isProp A → ((x : A) → isProp (B x)) → isProp (Σ A B)
isPropΣ pA pB t u = Σ≡Prop pB (pA (t .fst) (u .fst))

isPropRetract : {B : Type ℓ} (f : A → B) (g : B → A) (h : (x : A) → g (f x) ≡ x) → isProp B → isProp A
isPropRetract f g h p x y i =
  hcomp (λ j → λ { (i = i0) → h x j
                 ; (i = i1) → h y j})
        (g (p (f x) (f y) i))

isSetRetract : {B : Type ℓ} (f : A → B) (g : B → A) (h : (x : A) → g (f x) ≡ x) → isSet B → isSet A
isSetRetract f g h set x y p q i j =
  hcomp (λ k → λ { (i = i0) → h (p j) k
                 ; (i = i1) → h (q j) k
                 ; (j = i0) → h x k
                 ; (j = i1) → h y k})
        (g (set (f x) (f y) (cong f p) (cong f q) i j))

isGroupoidRetract : {B : Type ℓ} (f : A → B) (g : B → A) (h : (x : A) → g (f x) ≡ x) → isGroupoid B → isGroupoid A
isGroupoidRetract f g h grp x y p q P Q i j k =
  hcomp ((λ l → λ { (i = i0) → h (P j k) l
                  ; (i = i1) → h (Q j k) l
                  ; (j = i0) → h (p k) l
                  ; (j = i1) → h (q k) l
                  ; (k = i0) → h x l
                  ; (k = i1) → h y l}))
       (g (grp (f x) (f y) (cong f p) (cong f q) (cong (cong f) P) (cong (cong f) Q) i j k))

congFst⁻ : (pB : (x : A) → isProp (B x)) (t u : Σ A B) → t .fst ≡ u .fst → t ≡ u
congFst⁻ {B = B} pB t u q i = (q i) ,
          hcomp (λ j → λ { (i = i0) → pB (t .fst) (t .snd) (t .snd) j
                         ; (i = i1) → pB (u .fst) (coe0→1 (λ k → B (q k)) (t .snd)) (u .snd) j })
                (coe0→i (λ x → B (q x)) i (t .snd))

congFst⁻-congFst : (pB : (x : A) → isProp (B x)) (t u : Σ A B) → (p : t ≡ u) → congFst⁻ pB t u (cong fst p) ≡ p
congFst⁻-congFst {B = B} pB t u p j i =
  (p i .fst) ,
  (hcomp {A = B (p i .fst)} 
         (λ k → λ { (i = i0) → pB (t .fst) (t .snd) (t .snd) k
                  ; (i = i1) → pB (u .fst) (coe0→1 (λ k → B (p k .fst)) (t .snd)) (u .snd) k
                  ; (j = i1) → pB (p i .fst) (coe0→i (λ k → B (p k .fst)) i (t .snd)) (p i .snd) k })
         (coe0→i (λ x → B (p x .fst)) i (t .snd)))

isSetSndProp : (pB : (x : A) → isProp (B x)) (sA : (t u : Σ A B) → isProp (t .fst ≡ u .fst)) → isSet (Σ A B)
isSetSndProp pB sA t u =
  isPropRetract (cong fst) (congFst⁻ pB t u) (congFst⁻-congFst pB t u) (sA t u)

isGroupoidSndProp : (pB : (x : A) → isProp (B x)) → (sA : (t u : Σ A B) → isSet (t .fst ≡ u .fst)) → isGroupoid (Σ A B)
isGroupoidSndProp pB sA t u =
  isSetRetract (cong fst) (congFst⁻ pB t u) (congFst⁻-congFst pB t u) (sA t u)

is2GroupoidSndProp : (pB : (x : A) → isProp (B x)) → (sA : (t u : Σ A B) → isGroupoid (t .fst ≡ u .fst)) → is2Groupoid (Σ A B)
is2GroupoidSndProp pB sA t u = isGroupoidRetract (cong fst) (congFst⁻ pB t u) (congFst⁻-congFst pB t u) (sA t u)

isSetΠ : ((x : A) → isSet (B x)) → isSet ((x : A) → B x)
isSetΠ h x y p q i j z = h z (x z) (y z) (λ k → p k z) (λ k → q k z)  i j

setPath : (A B : Type ℓ) (sB : isSet B) → isSet (A ≡ B)
setPath A B sB = isSetRetract pathToEquiv ua ua-pathToEquiv (isSetSndProp isPropIsEquiv λ e1 e2 → isSetΠ (λ _ → sB) (e1 .fst) (e2 .fst))

isGroupoid-hSet : isGroupoid (hSet ℓ)
isGroupoid-hSet = isGroupoidSndProp (λ _ → isPropIsSet) λ t u → setPath (t .fst) (u .fst) (u .snd)


-- Next result
isGroupoidΠ : ((x : A) → isGroupoid (B x)) → isGroupoid ((x : A) → B x)
isGroupoidΠ h x y p q r s i j k z = h z (x z) (y z) (λ k → p k z) (λ k → q k z) (λ k l → r k l z) (λ k l → s k l z) i j k

groupoidPath : (A B : Type ℓ) (sB : isGroupoid B) → isGroupoid (A ≡ B)
groupoidPath A B sB = isGroupoidRetract pathToEquiv ua ua-pathToEquiv (isGroupoidSndProp isPropIsEquiv λ e1 e2 → isGroupoidΠ (λ _ → sB) (e1 .fst) (e2 .fst))

is2Groupoid-hGroupoid : is2Groupoid (hGroupoid ℓ)
is2Groupoid-hGroupoid = is2GroupoidSndProp (λ _ → isPropIsGroupoid) (λ t u → groupoidPath (t .fst) (u .fst) (u .snd))











-- ΣPathCoe : (a b : Σ A B) → Type _
-- ΣPathCoe {B = B} a b = Σ[ p ∈ (fst a ≡ fst b) ] transport (λ i → B (p i)) (snd a) ≡ snd b

-- f : (a b : Σ A B) → ΣPathCoe a b → (a ≡ b)
-- fst (f a b h i) = h .fst i
-- snd (f {B = B} a b h i) = toPathP {A = λ i → B (h .fst i)} (h .snd) i

-- isSetΣ : isSet A → ((x : A) → isSet (B x)) → isSet (Σ A B)
-- isSetΣ sA sB a b = isSetRetract {!!} {!!} {!!} {!!} a b

-- isOfHLevelΣ : ∀ n → isOfHLevel n A → ((x : A) → isOfHLevel n (B x))
--                   → isOfHLevel n (Σ A B)
-- isOfHLevelΣ 0 = isContrΣ
-- isOfHLevelΣ 1 = isPropΣ
-- isOfHLevelΣ {B = B} (suc (suc n)) h1 h2 x y =
--   isOfHLevelRetractFromIso (suc n)
--     (invIso (IsoΣPathTransportPathΣ _ _))
--     (isOfHLevelΣ (suc n) (h1 (fst x) (fst y)) λ x → h2 _ _ _)

-- isSetΣSndProp : isSet A → ((x : A) → isProp (B x)) → isSet (Σ A B)
-- isSetΣSndProp h p = isSetΣ h (λ x → isProp→isSet (p x))

{-
HLevel : Type₀
HLevel = ℕ

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ''''' : Level
    A A' : Type ℓ
    B : A → Type ℓ
    C : (x : A) → B x → Type ℓ
    D : (x : A) (y : B x) → C x y → Type ℓ
    E : (x : A) (y : B x) → (z : C x y) → D x y z → Type ℓ
    F : (x : A) (y : B x) (z : C x y) (w : D x y z) (v : E x y z w) → Type ℓ
    G : (x : A) (y : B x) (z : C x y) (w : D x y z) (v : E x y z w) (u : F x y z w v) → Type ℓ
    w x y z : A
    n : HLevel

isOfHLevel : HLevel → Type ℓ → Type ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc (suc n)) A = (x y : A) → isOfHLevel (suc n) (x ≡ y)

TypeOfHLevel : ∀ ℓ → HLevel → Type (ℓ-suc ℓ)
TypeOfHLevel ℓ n = TypeWithStr ℓ (isOfHLevel n)

isContrRetract
  : ∀ {B : Type ℓ}
  → (f : A → B) (g : B → A)
  → (h : retract f g)
  → (v : isContr B) → isContr A
fst (isContrRetract f g h (b , p)) = g b
snd (isContrRetract f g h (b , p)) x = (cong g (p (f x))) ∙ (h x)

isPropRetract
  : {B : Type ℓ}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isProp B → isProp A
isPropRetract f g h p x y i =
  hcomp
    (λ j → λ
      { (i = i0) → h x j
      ; (i = i1) → h y j})
    (g (p (f x) (f y) i))

isSetRetract
  : {B : Type ℓ}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isSet B → isSet A
isSetRetract f g h set x y p q i j =
  hcomp (λ k → λ { (i = i0) → h (p j) k
                 ; (i = i1) → h (q j) k
                 ; (j = i0) → h x k
                 ; (j = i1) → h y k})
        (g (set (f x) (f y)
                (cong f p) (cong f q) i j))

isGroupoidRetract
  : {B : Type ℓ}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isGroupoid B → isGroupoid A
isGroupoidRetract f g h grp x y p q P Q i j k =
  hcomp ((λ l → λ { (i = i0) → h (P j k) l
                  ; (i = i1) → h (Q j k) l
                  ; (j = i0) → h (p k) l
                  ; (j = i1) → h (q k) l
                  ; (k = i0) → h x l
                  ; (k = i1) → h y l}))
       (g (grp (f x) (f y) (cong f p) (cong f q)
                           (cong (cong f) P) (cong (cong f) Q) i j k))

is2GroupoidRetract
  : {B : Type ℓ}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → is2Groupoid B → is2Groupoid A
is2GroupoidRetract f g h grp x y p q P Q R S i j k l =
  hcomp (λ r → λ { (i = i0) → h (R j k l) r
                 ; (i = i1) → h (S j k l) r
                 ; (j = i0) → h (P k l) r
                 ; (j = i1) → h (Q k l) r
                 ; (k = i0) → h (p l) r
                 ; (k = i1) → h (q l) r
                 ; (l = i0) → h x r
                 ; (l = i1) → h y r})
       (g (grp (f x) (f y) (cong f p) (cong f q)
               (cong (cong f) P) (cong (cong f) Q)
               (cong (cong (cong f)) R) (cong (cong (cong f)) S) i j k l))

isOfHLevelRetract
  : (n : HLevel) {B : Type ℓ}
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isOfHLevel n B → isOfHLevel n A
isOfHLevelRetract 0 = isContrRetract
isOfHLevelRetract 1 = isPropRetract
isOfHLevelRetract 2 = isSetRetract
isOfHLevelRetract 3 = isGroupoidRetract
isOfHLevelRetract 4 = is2GroupoidRetract
isOfHLevelRetract (suc (suc (suc (suc (suc n))))) f g h ofLevel x y p q P Q R S =
  isOfHLevelRetract (suc n) (cong (cong (cong (cong f))))
                    (λ s i j k l →
                      hcomp (λ r → λ { (i = i0) → h (R j k l) r
                                     ; (i = i1) → h (S j k l) r
                                     ; (j = i0) → h (P k l) r
                                     ; (j = i1) → h (Q k l) r
                                     ; (k = i0) → h (p l) r
                                     ; (k = i1) → h (q l) r
                                     ; (l = i0) → h x r
                                     ; (l = i1) → h y r})
                            (g (s i j k l)))
                    (λ s i j k l m →
                    hcomp (λ n → λ { (i = i1) → s j k l m
                                   ; (j = i0) → h (R k l m) (i ∨ n)
                                   ; (j = i1) → h (S k l m) (i ∨ n)
                                   ; (k = i0) → h (P l m) (i ∨ n)
                                   ; (k = i1) → h (Q l m) (i ∨ n)
                                   ; (l = i0) → h (p m) (i ∨ n)
                                   ; (l = i1) → h (q m) (i ∨ n)
                                   ; (m = i0) → h x (i ∨ n)
                                   ; (m = i1) → h y (i ∨ n) })
                          (h (s j k l m) i))
                    (ofLevel (f x) (f y)
                             (cong f p) (cong f q)
                             (cong (cong f) P) (cong (cong f) Q)
                             (cong (cong (cong f)) R) (cong (cong (cong f)) S))


isContrΣ : isContr A → ((x : A) → isContr (B x)) → isContr (Σ A B)
isContrΣ {A = A} {B = B} (a , p) q =
  let h : (x : A) (y : B x) → (q x) .fst ≡ y
      h x y = (q x) .snd y
  in (( a , q a .fst)
     , ( λ x i → p (x .fst) i
       , h (p (x .fst) i) (transp (λ j → B (p (x .fst) (i ∨ ~ j))) i (x .snd)) i))

isPropΣ : isProp A → ((x : A) → isProp (B x)) → isProp (Σ A B)
isPropΣ pA pB t u = Σ≡Prop pB (pA (t .fst) (u .fst))

isOfHLevelΣ : ∀ n → isOfHLevel n A → ((x : A) → isOfHLevel n (B x))
                  → isOfHLevel n (Σ A B)
isOfHLevelΣ 0 = isContrΣ
isOfHLevelΣ 1 = isPropΣ
isOfHLevelΣ {B = B} (suc (suc n)) h1 h2 x y = isOfHLevelRetract (suc n) {!ΣPathP!} {!!} {!!} {!!}
  -- isOfHLevelRetractFromIso (suc n)
  --   (invIso (IsoΣPathTransportPathΣ _ _))
  --   (isOfHLevelΣ (suc n) (h1 (fst x) (fst y)) λ x → h2 _ _ _)

isOfHLevelΠ : ∀ n → ((x : A) → isOfHLevel n (B x))
                  → isOfHLevel n ((x : A) → B x)
isOfHLevelΠ 0 h = (λ x → fst (h x)) , λ f i y → snd (h y) (f y) i
isOfHLevelΠ 1 h f g i x = (h x) (f x) (g x) i
isOfHLevelΠ 2 h f g F G i j z = h z (f z) (g z) (funExt⁻ F z) (funExt⁻ G z) i j
isOfHLevelΠ 3 h f g p q P Q i j k z =
  h z (f z) (g z)
      (funExt⁻ p z) (funExt⁻ q z)
      (cong (λ f → funExt⁻ f z) P) (cong (λ f → funExt⁻ f z) Q) i j k
isOfHLevelΠ 4 h f g p q P Q R S i j k l z =
  h z (f z) (g z)
      (funExt⁻ p z) (funExt⁻ q z)
      (cong (λ f → funExt⁻ f z) P) (cong (λ f → funExt⁻ f z) Q)
      (cong (cong (λ f → funExt⁻ f z)) R) (cong (cong (λ f → funExt⁻ f z)) S) i j k l
isOfHLevelΠ (suc (suc (suc (suc (suc n))))) h f g p q P Q R S =
  isOfHLevelRetract (suc n)
    (cong (cong (cong funExt⁻))) (cong (cong (cong funExt))) (λ _ → refl)
    (isOfHLevelΠ (suc (suc (suc (suc n)))) (λ x → h x (f x) (g x))
                  (funExt⁻ p) (funExt⁻ q)
                  (cong funExt⁻ P) (cong funExt⁻ Q)
                  (cong (cong funExt⁻) R) (cong (cong funExt⁻) S))

isOfHLevelSuc : (n : HLevel) → isOfHLevel n A → isOfHLevel (suc n) A
isOfHLevelSuc 0 = isContr→isProp
isOfHLevelSuc 1 = isProp→isSet
isOfHLevelSuc (suc (suc n)) h a b = isOfHLevelSuc (suc n) (h a b)

isProp→isOfHLevelSuc : (n : HLevel) → isProp A → isOfHLevel (suc n) A
isProp→isOfHLevelSuc zero pA = pA
isProp→isOfHLevelSuc (suc n) pA = isOfHLevelSuc _ (isProp→isOfHLevelSuc n pA)

isOfHLevel≃
  : ∀ n {A : Type ℓ} {B : Type ℓ'}
  → (hA : isOfHLevel n A) (hB : isOfHLevel n B) → isOfHLevel n (A ≃ B)
isOfHLevel≃ zero {A = A} {B = B} hA hB = isContr→Equiv hA hB , contr
  where
  contr : (y : A ≃ B) → isContr→Equiv hA hB ≡ y
  contr y = Σ≡Prop isPropIsEquiv (funExt (λ a → snd hB (fst y a)))
isOfHLevel≃ (suc n) {A = A} {B = B} hA hB =
  isOfHLevelΣ (suc n) (isOfHLevelΠ _ λ _ → hB)
              (λ f → isProp→isOfHLevelSuc n (isPropIsEquiv f))

isOfHLevel≡ : ∀ n → {A B : Type ℓ} (hA : isOfHLevel n A) (hB : isOfHLevel n B) →
  isOfHLevel n (A ≡ B)
isOfHLevel≡ n hA hB = isOfHLevelRetract n pathToEquiv ua ua-pathToEquiv (isOfHLevel≃ n hA hB)

isPropHContr : isProp (TypeOfHLevel ℓ 0)
isPropHContr x y = Σ≡Prop (λ _ → isPropIsContr) (isOfHLevel≡ 0 (x .snd) (y .snd) .fst)

isPropIsOfHLevel : (n : HLevel) → isProp (isOfHLevel n A)
isPropIsOfHLevel 0 = isPropIsContr
isPropIsOfHLevel 1 = isPropIsProp
isPropIsOfHLevel (suc (suc n)) f g i a b =
  isPropIsOfHLevel (suc n) (f a b) (g a b) i

isProp→isContrPath : isProp A → (x y : A) → isContr (x ≡ y)
isProp→isContrPath h x y = h x y , isProp→isSet h x y _

isContr→isContrPath : isContr A → (x y : A) → isContr (x ≡ y)
isContr→isContrPath cA = isProp→isContrPath (isContr→isProp cA)

isOfHLevelPath' : (n : HLevel) → isOfHLevel (suc n) A → (x y : A) → isOfHLevel n (x ≡ y)
isOfHLevelPath' 0 = isProp→isContrPath
isOfHLevelPath' (suc n) h x y = h x y

isOfHLevelPath : (n : HLevel) → isOfHLevel n A → (x y : A) → isOfHLevel n (x ≡ y)
isOfHLevelPath 0 h x y = isContr→isContrPath h x y
isOfHLevelPath (suc n) h x y = isOfHLevelSuc n (isOfHLevelPath' n h x y)

section-Σ≡Prop
  : (pB : (x : A) → isProp (B x)) {u v : Σ A B}
  → section (Σ≡Prop pB {u} {v}) (cong fst)
section-Σ≡Prop {A = A} pB {u} {v} p j i =
  (p i .fst) , isProp→PathP (λ i → isOfHLevelPath 1 (pB (fst (p i)))
                                       (Σ≡Prop pB {u} {v} (cong fst p) i .snd)
                                       (p i .snd) )
                                       refl refl i j

isOfHLevelTypeOfHLevel : ∀ n → isOfHLevel (suc n) (TypeOfHLevel ℓ n)
isOfHLevelTypeOfHLevel zero = isPropHContr
isOfHLevelTypeOfHLevel (suc n) (X , a) (Y , b) = isOfHLevelRetract (suc n) (cong fst) (Σ≡Prop λ _ → isPropIsOfHLevel (suc n)) (section-Σ≡Prop (λ _ → isPropIsOfHLevel (suc n))) (isOfHLevel≡ (suc n) a b)
-}
