{-

Proof of the standard formulation of the univalence theorem and
various consequences of univalence

- Equivalence induction ([EquivJ], [elimEquiv])
- Univalence theorem ([univalence])
- The computation rule for ua ([uaβ])
- Isomorphism induction ([elimIso])

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Basics.Univalence where

open import Cubical.Core.Everything

open import Cubical.Basics.NTypes
open import Cubical.Basics.Equiv

-- Give detailed type to unglue, mainly for documentation purposes
unglueua : ∀ {A B : Set} → (e : A ≃ B) → (i : I) (x : ua e i) →
           B [ _ ↦ (λ { (i = i0) → e .fst x ; (i = i1) → x }) ]
unglueua e i x = inc (unglue {φ = i ∨ ~ i} x)


contrSinglEquiv : ∀ {ℓ} {A B : Set ℓ} (e : A ≃ B) → (B , idEquiv B) ≡ (A , e)
contrSinglEquiv {A = A} {B = B} e =
  isContr→isProp (EquivContr B) (B , idEquiv B) (A , e)

-- Equivalence induction
EquivJ : ∀ {ℓ ℓ′} (P : (A B : Set ℓ) → (e : B ≃ A) → Set ℓ′)
         → (r : (A : Set ℓ) → P A A (idEquiv A))
         → (A B : Set ℓ) → (e : B ≃ A) → P A B e
EquivJ P r A B e = subst (λ x → P A (x .fst) (x .snd)) (contrSinglEquiv e) (r A)

-- Eliminate equivalences by just looking at the underlying function
elimEquivFun : ∀ {ℓ} (B : Set ℓ) (P : (A : Set ℓ) → (A → B) → Set ℓ)
             → (r : P B (λ x → x))
             → (A : Set ℓ) → (e : A ≃ B) → P A (e .fst)
elimEquivFun B P r a e = subst (λ x → P (x .fst) (x .snd .fst)) (contrSinglEquiv e) r

-- ua is defined in Cubical/Core/Glue
uaIdEquiv : ∀ {ℓ} {A : Set ℓ} → ua (idEquiv A) ≡ refl
uaIdEquiv {A = A} i j = Glue A {φ = i ∨ ~ j ∨ j} (λ _ → A , idEquiv A)

-- Assuming that we have an inverse to ua we can easily prove univalence
module Univalence (au : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B)
                  (auid : ∀ {ℓ} {A B : Set ℓ} → au refl ≡ idEquiv A) where
  thm : ∀ {ℓ} {A B : Set ℓ} → isEquiv au
  thm {A = A} {B = B} =
    isoToIsEquiv {B = A ≃ B} au ua
      (EquivJ (λ _ _ e → au (ua e) ≡ e) (λ X → compPath (cong au uaIdEquiv) (auid {B = B})) _ _)
      (J (λ X p → ua (au p) ≡ p) (compPath (cong ua (auid {B = B})) uaIdEquiv))

pathToEquiv : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
pathToEquiv p = lineToEquiv (λ i → p i)

pathToEquivRefl : ∀ {ℓ} {A : Set ℓ} → pathToEquiv refl ≡ idEquiv A
pathToEquivRefl {A = A} = equivEq _ _ (λ i x → transp (λ _ → A) i x)

-- Univalence
univalence : ∀ {ℓ} {A B : Set ℓ} → (A ≡ B) ≃ (A ≃ B)
univalence = ( pathToEquiv , Univalence.thm pathToEquiv pathToEquivRefl  )

-- The original map from UniMath/Foundations
eqweqmap : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
eqweqmap {A = A} e = J (λ X _ → A ≃ X) (idEquiv A) e

eqweqmapid : ∀ {ℓ} {A : Set ℓ} → eqweqmap refl ≡ idEquiv A
eqweqmapid {A = A} = JRefl (λ X _ → A ≃ X) (idEquiv A)

univalenceStatement : ∀ {ℓ} {A B : Set ℓ} → isEquiv (eqweqmap {ℓ} {A} {B})
univalenceStatement = Univalence.thm eqweqmap eqweqmapid

univalenceUAH : ∀ {ℓ} {A B : Set ℓ} → (A ≡ B) ≃ (A ≃ B)
univalenceUAH = ( _ , univalenceStatement )

-- TODO: upstream
record Lift {i j} (A : Set i) : Set (ℓ-max i j) where
  instance constructor lift
  field
    lower : A

open Lift public

LiftEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} → A ≃ Lift {i = ℓ} {j = ℓ'} A
LiftEquiv = isoToEquiv lift lower (λ _ → refl) (λ _ → refl)

univalencePath : ∀ {ℓ} {A B : Set ℓ} → (A ≡ B) ≡ Lift (A ≃ B)
univalencePath = ua (compEquiv univalence LiftEquiv)


-- The computation rule for ua (could be proved a bit more compactly)
uaβ : ∀ {ℓ} {A B : Set ℓ} (e : A ≃ B) (x : A) → transp (λ i → ua e i) i0 x ≡ e .fst x
uaβ {B = B} e x =
  transp (λ i → ua e i) i0 x
    ≡⟨ refl ⟩
  hcomp (λ _ → empty)
        (transp (λ _ → B) i0
                (hcomp (λ _ → empty)
                       (transp (λ _ → B) i0 (e .fst x))))
    ≡⟨ (λ j → hfill (λ _ → empty)
                    (inc (transp (λ _ → B) i0
                                 (hcomp (λ _ → empty)
                                        (transp (λ _ → B) i0 (e .fst x)))))
                    (~ j)) ⟩
  transp (λ _ → B) i0
         (hcomp (λ _ → empty)
                (transp (λ _ → B) i0 (e .fst x)))
    ≡⟨ (λ j → transp (λ _ → B) j
                     (hcomp (λ _ → empty)
                            (transp (λ i → B) i0 (e .fst x)))) ⟩
  hcomp (λ _ → empty)
        (transp (λ _ → B) i0 (e .fst x))
    ≡⟨ (λ j → hfill (λ _ → empty)
                    (inc (transp (λ _ → B) i0 (e .fst x)))
                    (~ j))⟩
  transp (λ _ → B) i0 (e .fst x)
    ≡⟨ (λ j → transp (λ _ → B) j (e .fst x)) ⟩
  e .fst x ∎


-- Alternative version of EquivJ that only requires a predicate on
-- functions
elimEquiv : ∀ {ℓ ℓ'} → {B : Set ℓ} (P : {A : Set ℓ} → (A → B) → Set ℓ') →
            (d : P (idfun B)) → {A : Set ℓ} → (e : A ≃ B) → P (e .fst)
elimEquiv P d e = subst (λ x → P (x .snd .fst)) (contrSinglEquiv e) d

-- Isomorphism induction
elimIso : ∀ {ℓ ℓ'} → {B : Set ℓ} → (Q : {A : Set ℓ} → (A → B) → (B → A) → Set ℓ') →
          (h : Q (idfun B) (idfun B)) → {A : Set ℓ} →
          (f : A → B) → (g : B → A) → section f g → retract f g → Q f g
elimIso {ℓ} {ℓ'} {B} Q h {A} f g sfg rfg = rem1 f g sfg rfg
  where
  P : {A : Set ℓ} → (f : A → B) → Set (ℓ-max ℓ' ℓ)
  P {A} f = (g : B → A) → section f g → retract f g → Q f g

  rem : P (idfun B)
  rem g sfg rfg = subst (Q (idfun B)) (λ i b → (sfg b) (~ i)) h

  rem1 : {A : Set ℓ} → (f : A → B) → P f
  rem1 f g sfg rfg = elimEquiv P rem (f , isoToIsEquiv f g sfg rfg) g sfg rfg

