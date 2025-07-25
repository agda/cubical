
module Cubical.Algebra.Group.Exact where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Vec

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.Instances.Unit

open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ' : Level

record IsExactAt {ℓ ℓ' ℓ'' : Level}
                 {A : Group ℓ} {B : Group ℓ'} {C : Group ℓ''}
                 (f : GroupHom A B) (g : GroupHom B C) (b : ⟨ B ⟩)
                 : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  field
    im∈ker : isInIm f b → isInKer g b
    ker∈im : isInKer g b → isInIm f b
open IsExactAt public

IsExact : {A B C : Group ℓ} (f : GroupHom A B) (g : GroupHom B C) → Type ℓ
IsExact {B = B} f g = (b : ⟨ B ⟩) → IsExactAt f g b

SES→isEquiv : {L R : Group ℓ-zero}
  → {G : Group ℓ} {H : Group ℓ'}
  → UnitGroup₀ ≡ L
  → UnitGroup₀ ≡ R
  → (lhom : GroupHom L G) (midhom : GroupHom G H) (rhom : GroupHom H R)
  → ((x : _) → isInKer midhom x → isInIm lhom x)
  → ((x : _) → isInKer rhom x → isInIm midhom x)
  → isEquiv (fst midhom)
SES→isEquiv {R = R} {G = G} {H = H} =
  J (λ L _ → UnitGroup₀ ≡ R →
      (lhom : GroupHom L G) (midhom : GroupHom G H)
      (rhom : GroupHom H R) →
      ((x : fst G) → isInKer midhom x → isInIm lhom x) →
      ((x : fst H) → isInKer rhom x → isInIm midhom x) →
      isEquiv (fst midhom))
      ((J (λ R _ → (lhom : GroupHom UnitGroup₀ G) (midhom : GroupHom G H)
                   (rhom : GroupHom H R) →
                   ((x : fst G) → isInKer midhom x → isInIm lhom x) →
                   ((x : _) → isInKer rhom x → isInIm midhom x) →
                   isEquiv (fst midhom))
         main))
  where
  main : (lhom : GroupHom UnitGroup₀ G) (midhom : GroupHom G H)
         (rhom : GroupHom H UnitGroup₀) →
         ((x : fst G) → isInKer midhom x → isInIm lhom x) →
         ((x : fst H) → isInKer rhom x → isInIm midhom x) →
         isEquiv (fst midhom)
  main lhom midhom rhom lexact rexact =
    BijectionIsoToGroupEquiv {G = G} {H = H}
      bijIso' .fst .snd
    where
    bijIso' : BijectionIso G H
    BijectionIso.fun bijIso' = midhom
    BijectionIso.inj bijIso' x inker =
      PT.rec (GroupStr.is-set (snd G) _ _)
           (λ s → sym (snd s) ∙ IsGroupHom.pres1 (snd lhom))
           (lexact _ inker)
    BijectionIso.surj bijIso' x = rexact x refl

-- exact sequence of 4 groups. Useful for the proof of π₄S³
record Exact4 {ℓ ℓ' ℓ'' ℓ''' : Level} (G : Group ℓ)
  (H : Group ℓ') (L : Group ℓ'') (R : Group ℓ''')
  (G→H : GroupHom G H) (H→L : GroupHom H L) (L→R : GroupHom L R)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓ'''))) where
  field
    ImG→H⊂KerH→L : (x : fst H) → isInIm G→H x → isInKer H→L x
    KerH→L⊂ImG→H : (x : fst H) → isInKer H→L x → isInIm G→H x

    ImH→L⊂KerL→R : (x : fst L) → isInIm H→L x → isInKer L→R x
    KerL→R⊂ImH→L : (x : fst L) → isInKer L→R x → isInIm H→L x

open Exact4

extendExact4Surjective : {ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level}
  (G : Group ℓ) (H : Group ℓ') (L : Group ℓ'') (R : Group ℓ''') (S : Group ℓ'''')
  (G→H : GroupHom G H) (H→L : GroupHom H L) (L→R : GroupHom L R) (R→S : GroupHom R S)
  → isSurjective G→H
  → Exact4 H L R S H→L L→R R→S
  → Exact4 G L R S (compGroupHom G→H H→L) L→R R→S
ImG→H⊂KerH→L (extendExact4Surjective G H L R S G→H H→L L→R R→S surj ex) x =
  PT.rec (GroupStr.is-set (snd R) _ _)
    (uncurry λ g → J (λ x _ → isInKer L→R x)
      (ImG→H⊂KerH→L ex (fst H→L (fst G→H g))
        ∣ (fst G→H g) , refl ∣₁))
KerH→L⊂ImG→H (extendExact4Surjective G H L R S G→H H→L L→R R→S surj ex) x ker =
  PT.rec squash₁
    (uncurry λ y → J (λ x _ → isInIm (compGroupHom G→H H→L) x)
      (PT.map (uncurry
        (λ y → J (λ y _ → Σ[ g ∈ fst G ] fst H→L (fst G→H g) ≡ H→L .fst y)
        (y , refl))) (surj y)))
    (KerH→L⊂ImG→H ex x ker)
ImH→L⊂KerL→R (extendExact4Surjective G H L R S G→H H→L L→R R→S surj ex) =
  ImH→L⊂KerL→R ex
KerL→R⊂ImH→L (extendExact4Surjective G H L R S G→H H→L L→R R→S surj ex) =
  KerL→R⊂ImH→L ex

-- Useful lemma in the proof of π₄S³≅ℤ
transportExact4 : {ℓ ℓ' ℓ'' : Level}
                   {G G₂ : Group ℓ} {H H₂ : Group ℓ'} {L L₂ : Group ℓ''} {R : Group₀}
                   (G≡G₂ : G ≡ G₂) (H≡H₂ : H ≡ H₂) (L≡L₂ : L ≡ L₂)
                → UnitGroup₀ ≡ R
                → (G→H : GroupHom G H) (G₂→H₂ : GroupHom G₂ H₂)
                   (H→L : GroupHom H L) (H₂→L₂ : GroupHom H₂ L₂)
                   (L→R : GroupHom L R)
                → Exact4 G H L R G→H H→L L→R
                → PathP (λ i → GroupHom (G≡G₂ i) (H≡H₂ i)) G→H G₂→H₂
                → PathP (λ i → GroupHom (H≡H₂ i) (L≡L₂ i)) H→L H₂→L₂
                → Exact4 G₂ H₂ L₂ UnitGroup₀ G₂→H₂ H₂→L₂ (→UnitHom L₂)
transportExact4 {G = G} {G₂ = G₂} {H = H} {H₂ = H₂} {L = L} {L₂ = L₂} {R = R} =
  J4 (λ G₂ H₂ L₂ R G≡G₂ H≡H₂ L≡L₂ Unit≡R
                → (G→H : GroupHom G H) (G₂→H₂ : GroupHom G₂ H₂)
                   (H→L : GroupHom H L) (H₂→L₂ : GroupHom H₂ L₂)
                   (L→R : GroupHom L R)
                → Exact4 G H L R G→H H→L L→R
                → PathP (λ i → GroupHom (G≡G₂ i) (H≡H₂ i)) G→H G₂→H₂
                → PathP (λ i → GroupHom (H≡H₂ i) (L≡L₂ i)) H→L H₂→L₂
                → Exact4 G₂ H₂ L₂ UnitGroup₀ G₂→H₂ H₂→L₂ (→UnitHom L₂))
      (λ G→H G₂→H₂ H→L H₂→L₂ L→R ex pp1 pp2
        → J4 (λ G₂→H₂ H₂→L₂ (x : Unit) (y : Unit)
                 pp1 pp2 (_ : tt ≡ x) (_ : tt ≡ x)
             → Exact4 G H L UnitGroup₀ G₂→H₂ H₂→L₂ (→UnitHom L))
               ex G₂→H₂ H₂→L₂ tt tt pp1 pp2 refl refl )
      G₂ H₂ L₂ R
  where
  J4 : ∀ {ℓ ℓ₂ ℓ₃ ℓ₄ ℓ'} {A : Type ℓ}
       {A₂ : Type ℓ₂} {A₃ : Type ℓ₃} {A₄ : Type ℓ₄}
       {x : A} {x₂ : A₂} {x₃ : A₃} {x₄ : A₄}
       (B : (y : A) (z : A₂) (w : A₃) (u : A₄)
       → x ≡ y → x₂ ≡ z → x₃ ≡ w → x₄ ≡ u → Type ℓ')
    → B x x₂ x₃ x₄ refl refl refl refl
    → (y : A) (z : A₂) (w : A₃) (u : A₄)
       (p : x ≡ y) (q : x₂ ≡ z) (r : x₃ ≡ w) (s : x₄ ≡ u)
    → B y z w u p q r s
  J4 {x = x} {x₂ = x₂} {x₃ = x₃} {x₄ = x₄} B b y z w u =
    J (λ y p → (q : x₂ ≡ z) (r : x₃ ≡ w) (s : x₄ ≡ u) →
      B y z w u p q r s)
      (J (λ z q → (r : x₃ ≡ w) (s : x₄ ≡ u) → B x z w u refl q r s)
        (J (λ w r → (s : x₄ ≡ u) → B x x₂ w u refl refl r s)
          (J (λ u s → B x x₂ x₃ u refl refl refl s) b)))

