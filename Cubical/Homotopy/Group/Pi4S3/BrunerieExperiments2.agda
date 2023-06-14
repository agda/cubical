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

transport⁻ : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → B → A
transport⁻ p = transport (λ i → p (~ i))

subst⁻ : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} (B : A → Type ℓ') (p : x ≡ y) → B y → B x
subst⁻ B p pa = transport⁻ (λ i → B (p i)) pa

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
         → (PathP (λ i → P (p i)) u0 u1) ≡ (subst P p u0 ≡ u1)
funDepTr A P a0 a1 p u0 u1 j = PathP (λ i → P (p (j ∨ i))) (transp (λ i → P (p (j ∧ i))) (~ j) u0)

truncFibOmega : (n : ℕ) (B : Pointed₀) (P : B .fst → Type₀) (f : P (snd B))
                (tr : inhOrTrunc (P (snd B)) (suc n))
                (p : Ω B .fst)
              → inhOrTrunc (fibΩ P f p) n
truncFibOmega n B P f tr p = subst (λ x → inhOrTrunc x n) (λ i → funDepTr (B .fst) P (snd B) (snd B) p f f (~ i)) (tr (subst P p f) f)

fibContrΩ³Hopf : ∀ p → Ω³Hopf p
fibContrΩ³Hopf =
  truncFibOmega 0 (Ω² SuspS¹∙) Ω²Hopf (λ _ _ → base)
    (truncFibOmega 1 (Ω SuspS¹∙) ΩHopf (λ _ → base)
    (truncFibOmega 2 SuspS¹∙ HopfSuspS¹ base isGroupoidS¹ (λ _ → north)) λ i j → north)

h : Ω³ SuspS¹∙ .fst → Ω³ (join∙ S¹∙ S¹) .fst
h p i j k = t (p i j k) (fibContrΩ³Hopf p i j k)


------- 

multTwoAux : (x : S²) → Path (Path ∥ S² ∥₄ ∣ x ∣₄ ∣ x ∣₄) refl refl
multTwoAux base i j = ∣ surf i j ∣₄
multTwoAux (surf k l) i j =
  hcomp
    (λ m → λ
      { (i = i0) → ∣ surf k l ∣₄
      ; (i = i1) → ∣ surf k l ∣₄
      ; (j = i0) → ∣ surf k l ∣₄
      ; (j = i1) → ∣ surf k l ∣₄
      ; (k = i0) → ∣ surf i j ∣₄
      ; (k = i1) → ∣ surf i j ∣₄
      ; (l = i0) → ∣ surf i j ∣₄
      ; (l = i1) → squash₄ _ _ _ _ _ _ (λ k i j → step₁ k i j) refl m k i j
      })
    (step₁ k i j)

  where
  step₁ : I → I → I → ∥ S² ∥₄
  step₁ k i j =
    hcomp {A = ∥ S² ∥₄}
      (λ m → λ
        { (i = i0) → ∣ surf k (l ∧ m) ∣₄
        ; (i = i1) → ∣ surf k (l ∧ m) ∣₄
        ; (j = i0) → ∣ surf k (l ∧ m) ∣₄
        ; (j = i1) → ∣ surf k (l ∧ m) ∣₄
        ; (k = i0) → ∣ surf i j ∣₄
        ; (k = i1) → ∣ surf i j ∣₄
        ; (l = i0) → ∣ surf i j ∣₄
        })
     ∣ surf i j ∣₄

multTwoTildeAux : (t : ∥ S² ∥₄) → Path (Path ∥ S² ∥₄ t t) refl refl
multTwoTildeAux ∣ x ∣₄ = multTwoAux x
multTwoTildeAux (squash₄ _ _ _ _ _ _ t u k l m n) i j =
  squash₄ _ _ _ _ _ _
    (λ k l m → multTwoTildeAux (t k l m) i j)
    (λ k l m → multTwoTildeAux (u k l m) i j)
    k l m n

multTwoEquivAux : Path (Path (∥ S² ∥₄ ≃ ∥ S² ∥₄) (idEquiv _) (idEquiv _)) refl refl
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
  f : I → I → ∥ S² ∥₄ → ∥ S² ∥₄
  f i j t = multTwoTildeAux t i j

tHopf³ : S³ → Type₀
tHopf³ base = ∥ S² ∥₄
tHopf³ (surf i j k) =
  Glue ∥ S² ∥₄
    (λ { (i = i0) → (∥ S² ∥₄ , idEquiv _)
       ; (i = i1) → (∥ S² ∥₄ , idEquiv _)
       ; (j = i0) → (∥ S² ∥₄ , idEquiv _)
       ; (j = i1) → (∥ S² ∥₄ , idEquiv _)
       ; (k = i0) → (∥ S² ∥₄ , multTwoEquivAux i j)
       ; (k = i1) → (∥ S² ∥₄ , idEquiv _)
       })

π₃S³ : Ω³ S³∙ .fst → Ω² ∥ S²∙ ∥₄∙ .fst
π₃S³ p i j = transp (λ k → tHopf³ (p j k i)) i0 ∣ base ∣₄

codeS² : S² → hGroupoid _
codeS² s = ∥ HopfS² s ∥₃ , squash₃

codeTruncS² : ∥ S² ∥₄ → hGroupoid _
codeTruncS² = 2GroupoidTrunc.rec (isOfHLevelTypeOfHLevel 3) codeS²

encodeTruncS² : Ω ∥ S²∙ ∥₄∙ .fst → ∥ S¹ ∥₃
encodeTruncS² p = transp (λ i → codeTruncS² (p i) .fst) i0 ∣ base ∣₃

codeS¹ : S¹ → hSet _
codeS¹ s = ∥ helix s ∥₂ , squash₂

codeTruncS¹ : ∥ S¹ ∥₃ → hSet _
codeTruncS¹ = GroupoidTrunc.rec (isOfHLevelTypeOfHLevel 2) codeS¹

encodeTruncS¹ : Ω ∥ S¹∙ ∥₃∙ .fst → ∥ ℤ ∥₂
encodeTruncS¹ p = transp (λ i → codeTruncS¹ (p i) .fst) i0 ∣ pos zero ∣₂


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

-- don't run me
brunerie : ℤ
brunerie = g10 (g9 (g8 (f7 (f6 (f5 (f4 (f3 (λ i j k → surf i j k))))))))


{-
{-

Computation of an alternative definition of the Brunerie number based
on https://github.com/agda/cubical/pull/741. One should note that this
computation is quite different to the one of the term "brunerie"
defined above. This computation starts in π₃S³ rather than π₃S².

-}

-- The brunerie element can be shown to correspond to the following map
η₃ : (join S¹ S¹ , inl base) →∙ (Susp S² , north)
fst η₃ (inl x) = north
fst η₃ (inr x) = north
fst η₃ (push a b i) =
  (σ (S² , base) (S¹×S¹→S² a b) ∙ σ (S² , base) (S¹×S¹→S² a b)) i
snd η₃ = refl

K₂ = ∥ S² ∥₄
-- We will need a map Ω (Susp S²) → K₂. It turns out that the
-- following map is fast. It need a bit of work, however. It's
-- esentially the same map as you find in ZCohomology from ΩKₙ₊₁ to
-- Kₙ. This gives another definition of f7 which appears to work better.

module f7stuff where
  _+₂_ : K₂ → K₂ → K₂
  _+₂_ = 2GroupoidTrunc.elim (λ _ → isOfHLevelΠ 4 λ _ → squash₄)
          λ { base x → x
          ; (surf i j) x → surfc x i j}
    where
    surfc : (x : K₂) → typ ((Ω^ 2) (K₂ , x))
    surfc =
      2GroupoidTrunc.elim
        (λ _ → isOfHLevelPath 4 (isOfHLevelPath 4 squash₄ _ _) _ _)
        (S²ToSetElim (λ _ → squash₄ _ _ _ _) λ i j → ∣ surf i j ∣₄)

  K₂≃K₂ : (x : S²) → K₂ ≃ K₂
  fst (K₂≃K₂ x) y = ∣ x ∣₄ +₂ y
  snd (K₂≃K₂ x) = help x
    where
    help : (x : _) → isEquiv (λ y → ∣ x ∣₄ +₂ y)
    help = S²ToSetElim (λ _ → isProp→isSet (isPropIsEquiv _))
                       (idEquiv _ .snd)

  Code : Susp S² → Type ℓ-zero
  Code north = K₂
  Code south = K₂
  Code (merid a i) = ua (K₂≃K₂ a) i

  encode : (x : Susp S²) →  north ≡ x → Code x
  encode x = J (λ x p → Code x) ∣ base ∣₄

-- We now get an alternative definition of f7
f7' : typ (Ω (Susp∙ S²)) → K₂
f7' = f7stuff.encode north

-- We can define the Brunerie number by
brunerie' : ℤ
brunerie' = g10 (g9 (g8 λ i j → f7' λ k → η₃ .fst (push (loop i) (loop j) k)))

-- Computing it takes ~1s
brunerie'≡-2 : brunerie' ≡ -2
brunerie'≡-2 = refl

-- Proving that this indeed corresponds to the Brunerie number
-- requires us to phrase things slightly more carefully. For this, see
-- the second part of the Cubical.Homotopy.Group.Pi4S3.DirectProof.
-}
