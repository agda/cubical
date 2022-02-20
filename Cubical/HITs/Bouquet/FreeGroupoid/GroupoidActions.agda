{-

This file contains:

- Natural functions from FreeGroupoid into FreeGroupoid
- Proofs that they induce equivalences
- Natural paths in Universe from FreeGroupoid to FreeGroupoid
- Proofs that these functions and paths respect the groupoid structure of FreeGroupoid

-}
{-# OPTIONS --safe #-}

module Cubical.HITs.Bouquet.FreeGroupoid.GroupoidActions where

open import Cubical.HITs.Bouquet.FreeGroupoid.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Function

private
  variable
    ℓ : Level
    A : Type ℓ

-- A function for every element of FreeGroupoid A

action : ∀ (a : FreeGroupoid A) → FreeGroupoid A → FreeGroupoid A
action a g = m g a

invAction :  FreeGroupoid A → FreeGroupoid A → FreeGroupoid A
invAction a = action (inv a)

-- Naturality properties of the FreeGroupoid operations

multNaturality : (g1 g2 : FreeGroupoid A) → action (m g1 g2) ≡ (action g2 ∘ action g1)
multNaturality g1 g2 = funExt (pointwise g1 g2) where
  pointwise : (g1 g2 g3 : FreeGroupoid A) → action (m g1 g2) g3 ≡ (action g2 ∘ action g1) g3
  pointwise g1 g2 g3 =
    action (m g1 g2) g3
    ≡⟨ refl ⟩
    m g3 (m g1 g2)
    ≡⟨ assoc g3 g1 g2 ⟩
    m (m g3 g1) g2
    ≡⟨ refl ⟩
    action g2 (m g3 g1)
    ≡⟨ refl ⟩
    action g2 (action g1 g3)
    ≡⟨ refl ⟩
    (action g2 ∘ action g1) g3 ∎

idNaturality : action e ≡ idfun (FreeGroupoid A)
idNaturality = funExt pointwise where
  pointwise : (g : FreeGroupoid A) → action e g ≡ idfun (FreeGroupoid A) g
  pointwise g =
    action e g
    ≡⟨ refl ⟩
    m g e
    ≡⟨ sym (idr g) ⟩
    g
    ≡⟨ refl ⟩
    idfun _ g ∎

rCancelAction : ∀ (a : FreeGroupoid A) → action a ∘ invAction a ≡ idfun (FreeGroupoid A)
rCancelAction a =
  action a ∘ invAction a
  ≡⟨ sym (multNaturality (inv a) a) ⟩
  action (m (inv a) a)
  ≡⟨ cong action (invl a) ⟩
  action e
  ≡⟨ idNaturality ⟩
  idfun _ ∎

lCancelAction : ∀ (a : FreeGroupoid A) → invAction a ∘ action a ≡ idfun (FreeGroupoid A)
lCancelAction a =
  invAction a ∘ action a
  ≡⟨ sym (multNaturality a (inv a)) ⟩
  action (m a (inv a))
  ≡⟨ cong action (invr a) ⟩
  action e
  ≡⟨ idNaturality ⟩
  idfun _ ∎

-- Characterization of the action functions

actionCharacterization : ∀ (f : FreeGroupoid A → FreeGroupoid A)
      → (∀ g1 g2 → f (m g1 g2) ≡ m g1 (f g2))
      → Σ[ a ∈ FreeGroupoid A ] (f ≡ action a)
actionCharacterization f property = f e , (funExt pointwise) where
  pointwise : ∀ g → f g ≡ action (f e) g
  pointwise g =
    f g
    ≡⟨ cong f (idr g) ⟩
    f (m g e)
    ≡⟨ property g e ⟩
    action (f e) g ∎

-- Actions induce equivalences

biInvAction : FreeGroupoid A → BiInvEquiv (FreeGroupoid A) (FreeGroupoid A)
biInvAction a = biInvEquiv (action a) (invAction a) (rhomotopy a) (invAction a) (lhomotopy a) where
  rhomotopy : ∀ a g → (action a ∘ invAction a) g ≡ g
  rhomotopy a g = cong (λ f → f g) (rCancelAction a)
  lhomotopy : ∀ a g → (invAction a ∘ action a) g ≡ g
  lhomotopy a g = cong (λ f → f g) (lCancelAction a)

equivs : FreeGroupoid A → (FreeGroupoid A) ≃ (FreeGroupoid A)
equivs a = biInvEquiv→Equiv-right (biInvAction a)

-- Naturality properties of the equivs group

multEquivsNaturality : ∀ (k1 k2 : FreeGroupoid A) → equivs (m k1 k2) ≡ compEquiv (equivs k1) (equivs k2)
multEquivsNaturality k1 k2 = equivEq h where
  h : (equivs (m k1 k2)) .fst ≡ (compEquiv (equivs k1) (equivs k2)) .fst
  h =
    equivs (m k1 k2) .fst
    ≡⟨ refl ⟩
    action (m k1 k2)
    ≡⟨ multNaturality k1 k2 ⟩
    (action k2) ∘ (action k1)
    ≡⟨ refl ⟩
    ((equivs k2) .fst) ∘ ((equivs k1) .fst)
    ≡⟨ refl ⟩
    compEquiv (equivs k1) (equivs k2) .fst ∎

idEquivsNaturality : equivs e ≡ idEquiv (FreeGroupoid A)
idEquivsNaturality = equivEq h where
  h : (equivs e) .fst ≡ idEquiv (FreeGroupoid A) .fst
  h =
    (equivs e) .fst
    ≡⟨ refl ⟩
    action e
    ≡⟨ idNaturality ⟩
    idfun _
    ≡⟨ refl ⟩
    idEquiv _ .fst ∎

invEquivsNaturality : ∀ (g : FreeGroupoid A) → equivs (inv g) ≡ invEquiv (equivs g)
invEquivsNaturality g = equivEq refl

-- Actions induce paths in Universe

pathsInU : {A : Type ℓ} → FreeGroupoid A → (FreeGroupoid A) ≡ (FreeGroupoid A)
pathsInU a = ua (equivs a)

-- Naturality properties of the paths group

multPathsInUNaturality : ∀ (g1 g2 : FreeGroupoid A) → pathsInU (m g1 g2) ≡ (pathsInU g1) ∙ (pathsInU g2)
multPathsInUNaturality g1 g2 =
  pathsInU (m g1 g2)
  ≡⟨ refl ⟩
  ua (equivs (m g1 g2))
  ≡⟨ cong ua (multEquivsNaturality g1 g2) ⟩
  ua (compEquiv (equivs g1) (equivs g2))
  ≡⟨ uaCompEquiv (equivs g1) (equivs g2) ⟩
  (pathsInU g1) ∙ (pathsInU g2) ∎

idPathsInUNaturality : pathsInU {A = A} e ≡ refl
idPathsInUNaturality =
  pathsInU e
  ≡⟨ refl ⟩
  ua (equivs e)
  ≡⟨ cong ua idEquivsNaturality ⟩
  ua (idEquiv _)
  ≡⟨ uaIdEquiv ⟩
  refl ∎

invPathsInUNaturality : ∀ (g : FreeGroupoid A) → pathsInU (inv g) ≡ sym (pathsInU g)
invPathsInUNaturality g =
  pathsInU (inv g)
  ≡⟨ refl ⟩
  ua (equivs (inv g))
  ≡⟨ cong ua (invEquivsNaturality g) ⟩
  ua (invEquiv (equivs g))
  ≡⟨ uaInvEquiv (equivs g) ⟩
  sym (pathsInU g) ∎
