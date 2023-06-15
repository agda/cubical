{- This code is adapted from examples/brunerie.ctt and
   examples/brunerie4.ctt on the pi4s3_nobug branch of cubicaltt -}
{-# OPTIONS --safe #-}
module Cubical.Homotopy.Group.Pi4S3.BrunerieExperiments2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Int

open import Cubical.HITs.S1 hiding (encode)
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.Join
open import Cubical.HITs.SetTruncation as SetTrunc
open import Cubical.HITs.GroupoidTruncation as GroupoidTrunc
open import Cubical.HITs.2GroupoidTruncation as 2GroupoidTrunc
open import Cubical.HITs.Truncation as Trunc
open import Cubical.HITs.Susp renaming (toSusp to σ)

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Hopf
open S¹Hopf

Bool∙ S¹∙ SuspS¹∙ S³∙ : Pointed₀
Bool∙ = (Bool , true)
S¹∙ = (S¹ , base)
SuspS¹∙ = (SuspS¹ , north)
S³∙ = (S³ , base)

∥_∥₃∙ ∥_∥₄∙ : Pointed₀ → Pointed₀
∥ A , a ∥₃∙ = ∥ A ∥₃ , ∣ a ∣₃
∥ A , a ∥₄∙ = ∥ A ∥₄ , ∣ a ∣₄

join∙ : Pointed₀ → Type₀ → Pointed₀
join∙ (A , a) B = join A B , inl a

Ω² Ω³ : Pointed₀ → Pointed₀
Ω² = Ω^ 2
Ω³ = Ω^ 3

mapΩrefl : {A : Pointed₀} {B : Type₀} (f : A .fst → B) → Ω A .fst → Ω (B , f (pt A)) .fst
mapΩrefl f p i = f (p i)

mapΩ²refl : {A : Pointed₀} {B : Type₀} (f : A .fst → B) → Ω² A .fst → Ω² (B , f (pt A)) .fst
mapΩ²refl f p i j = f (p i j)

mapΩ³refl : {A : Pointed₀} {B : Type₀} (f : A .fst → B) → Ω³ A .fst → Ω³ (B , f (pt A)) .fst
mapΩ³refl f p i j k = f (p i j k)

alpha : join S¹ S¹ → SuspS¹
alpha (inl x) = north
alpha (inr x) = north
alpha (push x y i) = (merid x ∙ sym (merid y)) i

subst⁻ : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} (B : A → Type ℓ') (p : x ≡ y) → B y → B x
subst⁻ B p pa = coe1→0 (λ i → B (p i)) pa

funExt1 : {C B : Type₀} (P : C → Type₀) {a b : C} (p : a ≡ b)
          (f : P a → B) (g : P b → B) (h : (x : P b) → f (subst⁻ P p x) ≡ g x)
        → PathP (λ i → P (p i) → B) f g
funExt1 {B = B} P p f g h = toPathP (funExt (λ x → transportRefl (f (subst⁻ P p x)) ∙ h x))

t : (x : SuspS¹) → HopfSuspS¹ x → join S¹ S¹
t north x = inl x
t south x = inr x
t (merid x i) =
  funExt1 HopfSuspS¹ (merid x) inl inr
          (λ y → push (subst⁻ HopfSuspS¹ (merid x) y) y) i

fibΩ : {B : Pointed₀} (P : B .fst → Type₀) → P (pt B) → Ω B .fst → Type₀
fibΩ P f p = PathP (λ i → P (p i)) f f

fibΩ² : {B : Pointed₀} (P : B .fst → Type₀) → P (pt B) → Ω² B .fst → Type₀
fibΩ² P f = fibΩ (fibΩ P f) refl

fibΩ³ : {B : Pointed₀} (P : B .fst → Type₀) → P (pt B) → Ω³ B .fst → Type₀
fibΩ³ P f = fibΩ² (fibΩ P f) refl


-- The map h from 9.3
ΩHopf : Ω SuspS¹∙ .fst → Type₀
ΩHopf = fibΩ HopfSuspS¹ base

Ω²Hopf : Ω² SuspS¹∙ .fst → Type₀
Ω²Hopf = fibΩ² HopfSuspS¹ base

Ω³Hopf : Ω³ SuspS¹∙ .fst → Type₀
Ω³Hopf = fibΩ³ HopfSuspS¹ base

inhOrTrunc : (A : Type₀) → ℕ → Type₀
inhOrTrunc A zero = A
inhOrTrunc A (suc n) = (x y : A) → inhOrTrunc (x ≡ y) n

funDepTr : (A : Type₀) (P : A → Type₀) (a0 a1 : A) (p : a0 ≡ a1) (u0 : P a0) (u1 : P a1)
         → (subst P p u0 ≡ u1) ≡ (PathP (λ i → P (p i)) u0 u1)
funDepTr A P a0 a1 =
  J (λ (a1 : A) (p : a0 ≡ a1) → ((u0 : P a0) (u1 : P a1) → (subst P p u0 ≡ u1) ≡ (PathP (λ i → P (p i)) u0 u1)))
    λ u0 u1 i → transportRefl u0 i ≡ u1
-- With connections: PathP (λ i → P (p (~ j ∨ i))) (transp (λ i → P (p (~ j ∧ i))) j u0) u1

truncFibOmega : (n : ℕ) (B : Pointed₀) (P : B .fst → Type₀) (f : P (snd B))
                (tr : inhOrTrunc (P (snd B)) (suc n))
                (p : Ω B .fst)
              → inhOrTrunc (fibΩ P f p) n
truncFibOmega n B P f tr p =
  subst (λ x → inhOrTrunc x n)
        (funDepTr (B .fst) P (snd B) (snd B) p f f)
        (tr (subst P p f) f)

fibContrΩ³Hopf : ∀ p → Ω³Hopf p
fibContrΩ³Hopf =
  truncFibOmega 0 (Ω² SuspS¹∙) Ω²Hopf (λ _ _ → base)
    (truncFibOmega 1 (Ω SuspS¹∙) ΩHopf (λ _ → base)
    (truncFibOmega 2 SuspS¹∙ HopfSuspS¹ base isGroupoidS¹ (λ _ → north)) λ i j → north)

h : Ω³ SuspS¹∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
h p i j k = t (p i j k) (fibContrΩ³Hopf p i j k)


-- The final maps without connections:

setTruncFib : {A : Type₀} (P : A → Type₀) (gP : (x : A) -> isSet (P x))
              {a b : A} (p q : a ≡ b) (r : p ≡ q)
              (a1 : P a) (b1 : P b)
              (p1 : PathP (λ i → P (p i)) a1 b1)
              (q1 : PathP (λ i → P (q i)) a1 b1) →
              PathP (λ i → PathP (λ j → P (r i j)) a1 b1) p1 q1
setTruncFib P gP p q r a1 b1 p1 q1 = isOfHLevel→isOfHLevelDep 2 gP a1 b1 p1 q1 r

multTwoAux : (x : S²) → Path (Path ∥ S² ∥₄ ∣ x ∣₄ ∣ x ∣₄) refl refl
multTwoAux base i j = ∣ surf i j ∣₄
multTwoAux (surf k l) =
  setTruncFib (λ x → Path (Path ∥ S² ∥₄ ∣ x ∣₄ ∣ x ∣₄) refl refl)
              (λ x → squash₄ ∣ x ∣₄ ∣ x ∣₄ refl refl)
              refl refl
              surf (λ i j → ∣ surf i j ∣₄) (λ i j → ∣ surf i j ∣₄)
              (λ _ i j → ∣ surf i j ∣₄) (λ _ i j → ∣ surf i j ∣₄) k l

multTwo : S² → S² → ∥ S² ∥₄
multTwo base x = ∣ x ∣₄
multTwo (surf i j) x = multTwoAux x i j

multTwoTilde : S² → ∥ S² ∥₄ → ∥ S² ∥₄
multTwoTilde x = 2GroupoidTrunc.rec squash₄ (multTwo x)

lemPropF : {A : Type₀} (P : A → Type₀) (pP : (x : A) → isProp (P x))
           {a0 a1 : A} (p : a0 ≡ a1) (b0 : P a0) (b1 : P a1) → PathP (λ i → P (p i)) b0 b1
lemPropF P pP p b0 b1 i = pP (p i) (coe0→i (λ k → P (p k)) i b0) (coe1→i (λ k → P (p k)) i b1) i

lemPropS² : (P : S² → Type₀) (pP : (x : S²) → isProp (P x)) (pB : P base) (x : S²) → P x
lemPropS² P pP pB base = pB
lemPropS² P pP pB (surf i j) =
  hcomp (λ k → λ { (i = i0) → isProp→isSet (pP base) pB pB (lemPropF P pP (surf i) pB pB) refl k j
                 ; (i = i1) → isProp→isSet (pP base) pB pB (lemPropF P pP (surf i) pB pB) refl k j
                 ; (j = i0) → pB
                 ; (j = i1) → pB })
        (lemPropF P pP (surf i) pB pB j)

multEquivBase : isEquiv (multTwoTilde base)
multEquivBase = subst isEquiv (funExt rem) (idEquiv ∥ S² ∥₄ .snd)
  where
  rem : (x : ∥ S² ∥₄) → idfun ∥ S² ∥₄ x ≡ multTwoTilde base x
  rem = 2GroupoidTrunc.elim (λ x → isOfHLevelSuc 4 squash₄ x (multTwoTilde base x)) (λ _ → refl)

multTwoTildeIsEquiv : (x : S²) → isEquiv (multTwoTilde x)
multTwoTildeIsEquiv = lemPropS² (λ x → isEquiv (multTwoTilde x)) (λ x → isPropIsEquiv (multTwoTilde x)) multEquivBase

multTwoTildeEquiv : (x : S²) → ∥ S² ∥₄ ≃ ∥ S² ∥₄
multTwoTildeEquiv x = (multTwoTilde x) , (multTwoTildeIsEquiv x)

tHopf³ : S³ → Type₀
tHopf³ base = ∥ S² ∥₄
tHopf³ (surf i j k) =
  Glue ∥ S² ∥₄
    (λ { (i = i0) → (∥ S² ∥₄ , multTwoTildeEquiv base)
       ; (i = i1) → (∥ S² ∥₄ , multTwoTildeEquiv base)
       ; (j = i0) → (∥ S² ∥₄ , multTwoTildeEquiv base)
       ; (j = i1) → (∥ S² ∥₄ , multTwoTildeEquiv base)
       ; (k = i0) → (∥ S² ∥₄ , multTwoTildeEquiv (surf i j))
       ; (k = i1) → (∥ S² ∥₄ , multTwoTildeEquiv base)
       })

π₃S³ : Ω³ S³∙ .fst → Ω² ∥ S²∙ ∥₄∙ .fst
π₃S³ p i j = coe0→1 (λ k → tHopf³ (p j k i)) ∣ base ∣₄

codeS² : S² → hGroupoid _
codeS² s = ∥ HopfS² s ∥₃ , squash₃

codeTruncS² : ∥ S² ∥₄ → hGroupoid _
codeTruncS² = 2GroupoidTrunc.rec (isOfHLevelTypeOfHLevel 3) codeS²

encodeTruncS² : Ω ∥ S²∙ ∥₄∙ .fst → ∥ S¹ ∥₃
encodeTruncS² p = coe0→1 (λ i → codeTruncS² (p i) .fst) ∣ base ∣₃

codeS¹ : S¹ → hSet _
codeS¹ s = ∥ helix s ∥₂ , squash₂

codeTruncS¹ : ∥ S¹ ∥₃ → hSet _
codeTruncS¹ = GroupoidTrunc.rec (isOfHLevelTypeOfHLevel 2) codeS¹

encodeTruncS¹ : Ω ∥ S¹∙ ∥₃∙ .fst → ∥ ℤ ∥₂
encodeTruncS¹ p = coe0→1 (λ i → codeTruncS¹ (p i) .fst) ∣ pos zero ∣₂


-- THE BIG GAME

f3 : Ω³ S³∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
f3 = mapΩ³refl S³→joinS¹S¹

f4 : Ω³ (join∙ S¹∙ S¹) .fst → Ω³ SuspS¹∙ .fst
f4 = mapΩ³refl alpha

f5 : Ω³ SuspS¹∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
f5 = h

f6 : Ω³ (join∙ S¹∙ S¹) .fst → Ω³ S³∙ .fst
f6 = mapΩ³refl joinS¹S¹→S³

f7 : Ω³ S³∙ .fst → Ω² ∥ S²∙ ∥₄∙ .fst
f7 = π₃S³

g8 : Ω² ∥ S²∙ ∥₄∙ .fst → Ω ∥ S¹∙ ∥₃∙ .fst
g8 = mapΩrefl encodeTruncS²

g9 : Ω ∥ S¹∙ ∥₃∙ .fst → ∥ ℤ ∥₂
g9 = encodeTruncS¹

g10 : ∥ ℤ ∥₂ → ℤ
g10 = SetTrunc.rec isSetℤ (idfun ℤ)

brunerie : ℤ
brunerie = g10 (g9 (g8 (f7 (f6 (f5 (f4 (f3 (λ i j k → surf i j k))))))))

