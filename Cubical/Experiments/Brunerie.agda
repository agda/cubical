{-# OPTIONS --cubical #-}
module Cubical.Experiments.Brunerie where

open import Cubical.Core.Everything
open import Cubical.Foundations.Equiv
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Join
open import Cubical.HITs.Hopf
open import Cubical.HITs.SetTruncation

ptType : Set₁
ptType = Σ[ A ∈ Set ] A

pt : ∀ (A : ptType) → A .fst
pt A = A .snd

ptBool ptS¹ ptS² ptS³ : ptType
ptBool = (Bool , true)
ptS¹ = (S¹ , base)
ptS² = (S² , base)
ptS³ = (S³ , base)

Ω Ω² Ω³ : ptType → ptType
Ω (A , a) = (Path A a a) , refl
Ω² A = Ω (Ω A)
Ω³ A = Ω (Ω² A)

mapΩrefl : {A : ptType} {B : Set} (f : A .fst → B) → Ω A .fst → Ω (B , f (pt A)) .fst
mapΩrefl f p i = f (p i)

mapΩ²refl : {A : ptType} {B : Set} (f : A .fst → B) → Ω² A .fst → Ω² (B , f (pt A)) .fst
mapΩ²refl f p i j = f (p i j)

mapΩ³refl : {A : ptType} {B : Set} (f : A .fst → B) → Ω³ A .fst → Ω³ (B , f (pt A)) .fst
mapΩ³refl f p i j k = f (p i j k)

ptjoin : ptType → Set → ptType
ptjoin (A , a) B = join A B , inl a

meridS² : S¹ → Path S² base base
meridS² base _ = base
meridS² (loop i) j = surf i j

alpha : join S¹ S¹ → S²
alpha (inl x) = base
alpha (inr y) = base
alpha (push x y i) = (meridS² y ∙ meridS² x) i

connectionBoth : {A : Set} {a : A} (p : Path A a a) → PathP (λ i → Path A (p i) (p i)) p p
connectionBoth {a = a} p i j =
  hcomp
    (λ k → λ
      { (i = i0) → p (j ∨ ~ k)
      ; (i = i1) → p (j ∧ k)
      ; (j = i0) → p (i ∨ ~ k)
      ; (j = i1) → p (i ∧ k)
      })
    a

isGroupoid : ∀ {ℓ} → Set ℓ → Set ℓ
isGroupoid A = ∀ a b → isSet (Path A a b)

isTwoGroupoid : ∀ {ℓ} → Set ℓ → Set ℓ
isTwoGroupoid A = ∀ a b → isGroupoid (Path A a b)

PROP SET GROUPOID TWOGROUPOID : ∀ ℓ → Set (ℓ-suc ℓ)
PROP ℓ = Σ (Set ℓ) isProp
SET ℓ = Σ (Set ℓ) isSet
GROUPOID ℓ = Σ (Set ℓ) isGroupoid
TWOGROUPOID ℓ = Σ (Set ℓ) isTwoGroupoid

data PostTotalHopf : Set where
  base : S¹ → PostTotalHopf
  loop : (x : S¹) → PathP (λ i → Path PostTotalHopf (base x) (base (rotLoop x (~ i)))) refl refl

tee12 : (x : S²) → HopfS² x → PostTotalHopf
tee12 base y = base y
tee12 (surf i j) y =
  hcomp
    (λ k → λ
      { (i = i0) → base y
      ; (i = i1) → base y
      ; (j = i0) → base y
      ; (j = i1) → base (rotLoopInv y (~ i) k)
      })
    (loop (unglue (i ∨ ~ i ∨ j ∨ ~ j) y) i j)

tee34 : PostTotalHopf → join S¹ S¹
tee34 (base x) = inl x
tee34 (loop x i j) =
  hcomp
    (λ k → λ
      { (i = i0) → push x x (j ∧ ~ k)
      ; (i = i1) → push x x (j ∧ ~ k)
      ; (j = i0) → inl x
      ; (j = i1) → push (rotLoop x (~ i)) x (~ k)
      })
    (push x x j)

tee : (x : S²) → HopfS² x → join S¹ S¹
tee x y = tee34 (tee12 x y)

fibΩ : {B : ptType} (P : B .fst → Set) → P (pt B) → Ω B .fst → Set
fibΩ P f p = PathP (λ i → P (p i)) f f

fibΩ² : {B : ptType} (P : B .fst → Set) → P (pt B) → Ω² B .fst → Set
fibΩ² P f = fibΩ (fibΩ P f) refl

fibΩ³ : {B : ptType} (P : B .fst → Set) → P (pt B) → Ω³ B .fst → Set
fibΩ³ P f = fibΩ² (fibΩ P f) refl

Ω³Hopf : Ω³ ptS² .fst → Set
Ω³Hopf = fibΩ³ HopfS² base

fibContrΩ³Hopf : ∀ p → Ω³Hopf p
fibContrΩ³Hopf p i j k =
  hcomp
    (λ m → λ
      { (i = i0) → base
      ; (i = i1) → base
      ; (j = i0) → base
      ; (j = i1) → base
      ; (k = i0) → base
      ; (k = i1) →
        isSetΩS¹ refl refl
          (λ i j → transp (λ n → HopfS² (p i j n)) (i ∨ ~ i ∨ j ∨ ~ j) base)
          (λ _ _ → base)
          m i j
      })
    (transp (λ n → HopfS² (p i j (k ∧ n))) (i ∨ ~ i ∨ j ∨ ~ j ∨ ~ k) base)

h : Ω³ ptS² .fst → Ω³ (ptjoin ptS¹ S¹) .fst
h p i j k = tee (p i j k) (fibContrΩ³Hopf p i j k)

Trunc₀Rec : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (sB : isSet B) → (A → B) → (∥ A ∥₀ → B)
Trunc₀Rec sB f ∣ x ∣₀ = f x
Trunc₀Rec sB f (squash₀ x y p q i j) =
  sB _ _
    (λ m → Trunc₀Rec sB f (p m))
    (λ m → Trunc₀Rec sB f (q m))
    i j

data ∥_∥₁ {ℓ} (A : Set ℓ) : Set ℓ where
  ∣_∣₁ : A → ∥ A ∥₁
  squash₁ : ∀ {x y : ∥ A ∥₁} {p q : x ≡ y} (r s : p ≡ q) → r ≡ s

pt∥_∥₁ : ptType → ptType
pt∥ A , a ∥₁ = ∥ A ∥₁ , ∣ a ∣₁

Trunc₁Rec : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (gB : isGroupoid B) → (A → B) → (∥ A ∥₁ → B)
Trunc₁Rec gB f ∣ x ∣₁ = f x
Trunc₁Rec gB f (squash₁ r s i j k) =
  gB _ _ _ _
    (λ m n → Trunc₁Rec gB f (r m n))
    (λ m n → Trunc₁Rec gB f (s m n))
    i j k

Trunc₁Groupoid : {A : Set} → isGroupoid ∥ A ∥₁
Trunc₁Groupoid _ _ _ _ = squash₁

data ∥_∥₂ {ℓ} (A : Set ℓ) : Set ℓ where
  ∣_∣₂ : A → ∥ A ∥₂
  squash₂ : ∀ {x y : ∥ A ∥₂} {p q : x ≡ y} {r s : p ≡ q} (t u : r ≡ s) → t ≡ u

pt∥_∥₂ : ptType → ptType
pt∥ A , a ∥₂ = ∥ A ∥₂ , ∣ a ∣₂

Trunc₂Rec : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (gB : isTwoGroupoid B) → (A → B) → (∥ A ∥₂ → B)
Trunc₂Rec gB f ∣ x ∣₂ = f x
Trunc₂Rec gB f (squash₂ t u i j k l) =
  gB _ _ _ _ _ _
    (λ m n o → Trunc₂Rec gB f (t m n o))
    (λ m n o → Trunc₂Rec gB f (u m n o))
    i j k l

Trunc₂TwoGroupoid : {A : Set} → isTwoGroupoid ∥ A ∥₂
Trunc₂TwoGroupoid _ _ _ _ _ _ = squash₂

multTwoAux : (x : S²) → Path (Path ∥ S² ∥₂ ∣ x ∣₂ ∣ x ∣₂) refl refl
multTwoAux base i j = ∣ surf i j ∣₂
multTwoAux (surf k l) i j =
  hcomp
    (λ m → λ
      { (i = i0) → ∣ surf k l ∣₂
      ; (i = i1) → ∣ surf k l ∣₂
      ; (j = i0) → ∣ surf k l ∣₂
      ; (j = i1) → ∣ surf k l ∣₂
      ; (k = i0) → ∣ surf i j ∣₂
      ; (k = i1) → ∣ surf i j ∣₂
      ; (l = i0) → ∣ surf i j ∣₂
      ; (l = i1) → squash₂ (λ k i j → step₁ k i j) refl m k i j
      })
    (step₁ k i j)
    
  where
  step₁ : I → I → I → ∥ S² ∥₂
  step₁ k i j =
    hcomp {A = ∥ S² ∥₂}
      (λ m → λ
        { (i = i0) → ∣ surf k (l ∧ m) ∣₂
        ; (i = i1) → ∣ surf k (l ∧ m) ∣₂
        ; (j = i0) → ∣ surf k (l ∧ m) ∣₂
        ; (j = i1) → ∣ surf k (l ∧ m) ∣₂
        ; (k = i0) → ∣ surf i j ∣₂
        ; (k = i1) → ∣ surf i j ∣₂
        ; (l = i0) → ∣ surf i j ∣₂
        })
     ∣ surf i j ∣₂

multTwoTildeAux : (t : ∥ S² ∥₂) → Path (Path ∥ S² ∥₂ t t) refl refl
multTwoTildeAux ∣ x ∣₂ = multTwoAux x
multTwoTildeAux (squash₂ t u k l m n) i j =
  squash₂
    (λ k l m → multTwoTildeAux (t k l m) i j)
    (λ k l m → multTwoTildeAux (u k l m) i j)
    k l m n

multTwoEquivAux : Path (Path (∥ S² ∥₂ ≃ ∥ S² ∥₂) (idEquiv _) (idEquiv _)) refl refl
multTwoEquivAux i j =
  ( f i j
  , hcomp
      (λ l → λ
        { (i = i0) → isPropIsEquiv _ (idIsEquiv _) (idIsEquiv _) l
        ; (i = i1) → isPropIsEquiv _ (idIsEquiv _) (idIsEquiv _) l
        ; (j = i0) → isPropIsEquiv _ (idIsEquiv _) (idIsEquiv _) l
        ; (j = i1) →
          isPropIsEquiv _
            (transp (λ k → isEquiv (f i k)) (i ∨ ~ i) (idIsEquiv _))
            (idIsEquiv _)
            l
        })
      (transp (λ k → isEquiv (f i (j ∧ k))) (i ∨ ~ i ∨ ~ j) (idIsEquiv _))
  )
  where
  f : I → I → ∥ S² ∥₂ → ∥ S² ∥₂
  f i j t = multTwoTildeAux t i j

tHopf³ : S³ → Set
tHopf³ base = ∥ S² ∥₂
tHopf³ (surf i j k) =
  Glue ∥ S² ∥₂
    (λ { (i = i0) → (∥ S² ∥₂ , idEquiv _)
       ; (i = i1) → (∥ S² ∥₂ , idEquiv _)
       ; (j = i0) → (∥ S² ∥₂ , idEquiv _)
       ; (j = i1) → (∥ S² ∥₂ , idEquiv _)
       ; (k = i0) → (∥ S² ∥₂ , multTwoEquivAux i j)
       ; (k = i1) → (∥ S² ∥₂ , idEquiv _)
       })

π₃S³ : Ω³ ptS³ .fst → Ω² pt∥ ptS² ∥₂ .fst
π₃S³ p i j = transp (λ k → tHopf³ (p j k i)) i0 ∣ base ∣₂

postulate
  isTwoGroupoidGROUPOID : ∀ {ℓ} → isTwoGroupoid (GROUPOID ℓ)
  isGroupoidSET : ∀ {ℓ} → isGroupoid (SET ℓ)

codeS² : S² → GROUPOID _
codeS² s = ∥ HopfS² s ∥₁ , Trunc₁Groupoid

codeTruncS² : ∥ S² ∥₂ → GROUPOID _
codeTruncS² = Trunc₂Rec isTwoGroupoidGROUPOID codeS²

encodeTruncS² : Ω pt∥ ptS² ∥₂ .fst → ∥ S¹ ∥₁
encodeTruncS² p = transp (λ i → codeTruncS² (p i) .fst) i0 ∣ base ∣₁

codeS¹ : S¹ → SET _
codeS¹ s = ∥ helix s ∥₀ , squash₀

codeTruncS¹ : ∥ S¹ ∥₁ → SET _
codeTruncS¹ = Trunc₁Rec isGroupoidSET codeS¹

encodeTruncS¹ : Ω pt∥ ptS¹ ∥₁ .fst → ∥ Int ∥₀
encodeTruncS¹ p = transp (λ i → codeTruncS¹ (p i) .fst) i0 ∣ pos zero ∣₀


-- THE BIG GAME

f3 : Ω³ ptS³ .fst → Ω³ (ptjoin ptS¹ S¹) .fst
f3 = mapΩ³refl S³→joinS¹S¹

f4 : Ω³ (ptjoin ptS¹ S¹) .fst → Ω³ ptS² .fst
f4 = mapΩ³refl alpha

f5 : Ω³ ptS² .fst → Ω³ (ptjoin ptS¹ S¹) .fst
f5 = h

f6 : Ω³ (ptjoin ptS¹ S¹) .fst → Ω³ ptS³ .fst
f6 = mapΩ³refl joinS¹S¹→S³

f7 : Ω³ ptS³ .fst → Ω² pt∥ ptS² ∥₂ .fst
f7 = π₃S³

g8 : Ω² pt∥ ptS² ∥₂ .fst → Ω pt∥ ptS¹ ∥₁ .fst
g8 = mapΩrefl encodeTruncS²

g9 : Ω pt∥ ptS¹ ∥₁ .fst → ∥ Int ∥₀
g9 = encodeTruncS¹

g10 : ∥ Int ∥₀ → Int
g10 = Trunc₀Rec isSetInt (idfun Int)
