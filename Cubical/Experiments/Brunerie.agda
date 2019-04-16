{-# OPTIONS --cubical #-}
module Cubical.Experiments.Brunerie where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
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
open import Cubical.HITs.GroupoidTruncation
open import Cubical.HITs.2GroupoidTruncation

-- This code is adapted from examples/brunerie3.ctt on the pi4s3_nobug branch of cubicaltt

ptType : Type₁
ptType = Σ[ A ∈ Type₀ ] A

pt : ∀ (A : ptType) → A .fst
pt A = A .snd

ptBool ptS¹ ptS² ptS³ : ptType
ptBool = (Bool , true)
ptS¹ = (S¹ , base)
ptS² = (S² , base)
ptS³ = (S³ , base)

pt∥_∥₁ pt∥_∥₂ : ptType → ptType
pt∥ A , a ∥₁ = ∥ A ∥₁ , ∣ a ∣₁
pt∥ A , a ∥₂ = ∥ A ∥₂ , ∣ a ∣₂

ptjoin : ptType → Type₀ → ptType
ptjoin (A , a) B = join A B , inl a

Ω Ω² Ω³ : ptType → ptType
Ω (A , a) = (Path A a a) , refl
Ω² A = Ω (Ω A)
Ω³ A = Ω (Ω² A)

mapΩrefl : {A : ptType} {B : Type₀} (f : A .fst → B) → Ω A .fst → Ω (B , f (pt A)) .fst
mapΩrefl f p i = f (p i)

mapΩ²refl : {A : ptType} {B : Type₀} (f : A .fst → B) → Ω² A .fst → Ω² (B , f (pt A)) .fst
mapΩ²refl f p i j = f (p i j)

mapΩ³refl : {A : ptType} {B : Type₀} (f : A .fst → B) → Ω³ A .fst → Ω³ (B , f (pt A)) .fst
mapΩ³refl f p i j k = f (p i j k)

PROP SET GROUPOID TWOGROUPOID : ∀ ℓ → Type (ℓ-suc ℓ)
PROP ℓ = Σ (Type ℓ) isProp
SET ℓ = Σ (Type ℓ) isSet
GROUPOID ℓ = Σ (Type ℓ) isGroupoid
TWOGROUPOID ℓ = Σ (Type ℓ) is2Groupoid

meridS² : S¹ → Path S² base base
meridS² base _ = base
meridS² (loop i) j = surf i j

alpha : join S¹ S¹ → S²
alpha (inl x) = base
alpha (inr y) = base
alpha (push x y i) = (meridS² y ∙ meridS² x) i

connectionBoth : {A : Type₀} {a : A} (p : Path A a a) → PathP (λ i → Path A (p i) (p i)) p p
connectionBoth {a = a} p i j =
  hcomp
    (λ k → λ
      { (i = i0) → p (j ∨ ~ k)
      ; (i = i1) → p (j ∧ k)
      ; (j = i0) → p (i ∨ ~ k)
      ; (j = i1) → p (i ∧ k)
      })
    a

data PostTotalHopf : Type₀ where
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

fibΩ : {B : ptType} (P : B .fst → Type₀) → P (pt B) → Ω B .fst → Type₀
fibΩ P f p = PathP (λ i → P (p i)) f f

fibΩ² : {B : ptType} (P : B .fst → Type₀) → P (pt B) → Ω² B .fst → Type₀
fibΩ² P f = fibΩ (fibΩ P f) refl

fibΩ³ : {B : ptType} (P : B .fst → Type₀) → P (pt B) → Ω³ B .fst → Type₀
fibΩ³ P f = fibΩ² (fibΩ P f) refl

Ω³Hopf : Ω³ ptS² .fst → Type₀
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
      ; (l = i1) → squash₂ _ _ _ _ _ _ (λ k i j → step₁ k i j) refl m k i j
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
multTwoTildeAux (squash₂ _ _ _ _ _ _ t u k l m n) i j =
  squash₂ _ _ _ _ _ _
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

tHopf³ : S³ → Type₀
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
  is2GroupoidGROUPOID : ∀ {ℓ} → is2Groupoid (GROUPOID ℓ)
  isGroupoidSET : ∀ {ℓ} → isGroupoid (SET ℓ)

codeS² : S² → GROUPOID _
codeS² s = ∥ HopfS² s ∥₁ , squash₁

codeTruncS² : ∥ S² ∥₂ → GROUPOID _
codeTruncS² = rec2GroupoidTrunc is2GroupoidGROUPOID codeS²

encodeTruncS² : Ω pt∥ ptS² ∥₂ .fst → ∥ S¹ ∥₁
encodeTruncS² p = transp (λ i → codeTruncS² (p i) .fst) i0 ∣ base ∣₁

codeS¹ : S¹ → SET _
codeS¹ s = ∥ helix s ∥₀ , squash₀

codeTruncS¹ : ∥ S¹ ∥₁ → SET _
codeTruncS¹ = recGroupoidTrunc isGroupoidSET codeS¹

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
g10 = elimSetTrunc (λ _ → isSetInt) (idfun Int)

-- don't run me
brunerie : Int
brunerie = g10 (g9 (g8 (f7 (f6 (f5 (f4 (f3 (λ i j k → surf i j k))))))))

-- simpler tests

test63 : ℕ → Int
test63 n = g10 (g9 (g8 (f7 (63n n))))
  where
  63n : ℕ → Ω³ ptS³ .fst
  63n zero i j k = surf i j k
  63n (suc n) = f6 (f3 (63n n))

foo : Ω³ ptS² .fst
foo i j k =
  hcomp
    (λ l → λ
      { (i = i0) → surf l l
      ; (i = i1) → surf l l
      ; (j = i0) → surf l l
      ; (j = i1) → surf l l
      ; (k = i0) → surf l l
      ; (k = i1) → surf l l
      })
    base

sorghum : Ω³ ptS² .fst
sorghum i j k =
  hcomp
    (λ l → λ
      { (i = i0) → surf j l
      ; (i = i1) → surf k (~ l)
      ; (j = i0) → surf k (i ∧ ~ l)
      ; (j = i1) → surf k (i ∧ ~ l)
      ; (k = i0) → surf j (i ∨ l)
      ; (k = i1) → surf j (i ∨ l)
      })
    (hcomp
      (λ l → λ
        { (i = i0) → base
        ; (i = i1) → surf j l
        ; (j = i0) → surf k i
        ; (j = i1) → surf k i
        ; (k = i0) → surf j (i ∧ l)
        ; (k = i1) → surf j (i ∧ l)
        })
      (surf k i))


goo : Ω³ ptS² .fst → Int
goo x = g10 (g9 (g8 (f7 (f6 (f5 x)))))
