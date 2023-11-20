{-

This file contains:

Properties of the FreeGroup:
- FreeGroup A is Set, SemiGroup, Monoid, Group
- Recursion principle for the FreeGroup
- Induction principle for the FreeGroup on hProps
- Condition for the equality of Group Homomorphisms from FreeGroup
- Equivalence of the types (A → Group .fst) (GroupHom (freeGroupGroup A) Group)

-}
{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.Properties where

open import Cubical.HITs.FreeGroup.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Isomorphism

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base

open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Groups

import Cubical.Data.Int as ℤ
open import Cubical.Algebra.Group.Instances.Int

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

freeGroupIsSet : isSet (FreeGroup A)
freeGroupIsSet = trunc

freeGroupIsSemiGroup : IsSemigroup {A = FreeGroup A} _·_
freeGroupIsSemiGroup = issemigroup freeGroupIsSet assoc

freeGroupIsMonoid : IsMonoid {A = FreeGroup A} ε _·_
freeGroupIsMonoid = ismonoid freeGroupIsSemiGroup (λ x → sym (idr x)) (λ x → sym (idl x))

freeGroupIsGroup : IsGroup {G = FreeGroup A} ε _·_ inv
freeGroupIsGroup = isgroup freeGroupIsMonoid invr invl

freeGroupGroupStr : GroupStr (FreeGroup A)
freeGroupGroupStr = groupstr ε _·_ inv freeGroupIsGroup

-- FreeGroup is indeed a group
freeGroupGroup : Type ℓ → Group ℓ
freeGroupGroup A = FreeGroup A , freeGroupGroupStr

-- The recursion principle for the FreeGroup
rec : {Group : Group ℓ'} → (A → Group .fst) → GroupHom (freeGroupGroup A) Group
rec {Group = G , groupstr 1g _·g_ invg (isgroup (ismonoid isSemigroupg ·gIdR ·gIdL) ·gInvR ·gInvL)} f = f' , isHom
  where
  f' : FreeGroup _ → G
  f' (η a)                  = f a
  f' (g1 · g2)              = (f' g1) ·g (f' g2)
  f' ε                      = 1g
  f' (inv g)                = invg (f' g)
  f' (assoc g1 g2 g3 i)     = IsSemigroup.·Assoc isSemigroupg (f' g1) (f' g2) (f' g3) i
  f' (idr g i)              = sym (·gIdR (f' g)) i
  f' (idl g i)              = sym (·gIdL (f' g)) i
  f' (invr g i)             = ·gInvR (f' g) i
  f' (invl g i)             = ·gInvL (f' g) i
  f' (trunc g1 g2 p q i i₁) = IsSemigroup.is-set isSemigroupg (f' g1) (f' g2) (cong f' p) (cong f' q) i i₁

  isHom : IsGroupHom freeGroupGroupStr f' _
  IsGroupHom.pres·   isHom = λ g1 g2 → refl
  IsGroupHom.pres1   isHom = refl
  IsGroupHom.presinv isHom = λ g → refl

-- The induction principle for the FreeGroup for hProps
elimProp : {B : FreeGroup A → Type ℓ'}
         → ((x : FreeGroup A) → isProp (B x))
         → ((a : A) → B (η a))
         → ((g1 g2 : FreeGroup A) → B g1 → B g2 → B (g1 · g2))
         → (B ε)
         → ((g : FreeGroup A) → B g → B (inv g))
         → (x : FreeGroup A)
         → B x
elimProp {B = B} Bprop η-ind ·-ind ε-ind inv-ind = induction where
  induction : ∀ g → B g
  induction (η a) = η-ind a
  induction (g1 · g2) = ·-ind g1 g2 (induction g1) (induction g2)
  induction ε = ε-ind
  induction (inv g) = inv-ind g (induction g)
  induction (assoc g1 g2 g3 i) = path i where
    p1 : B g1
    p1 = induction g1
    p2 : B g2
    p2 = induction g2
    p3 : B g3
    p3 = induction g3
    path : PathP (λ i → B (assoc g1 g2 g3 i)) (·-ind g1 (g2 · g3) p1 (·-ind g2 g3 p2 p3))
                                              (·-ind (g1 · g2) g3 (·-ind g1 g2 p1 p2) p3)
    path = isProp→PathP (λ i → Bprop (assoc g1 g2 g3 i)) (·-ind g1 (g2 · g3) p1 (·-ind g2 g3 p2 p3))
                                                         (·-ind (g1 · g2) g3 (·-ind g1 g2 p1 p2) p3)
  induction (idr g i) = path i where
    p : B g
    p = induction g
    pε : B ε
    pε = induction ε
    path : PathP (λ i → B (idr g i)) p (·-ind g ε p pε)
    path = isProp→PathP (λ i → Bprop (idr g i)) p (·-ind g ε p pε)
  induction (idl g i) = path i where
    p : B g
    p = induction g
    pε : B ε
    pε = induction ε
    path : PathP (λ i → B (idl g i)) p (·-ind ε g pε p)
    path = isProp→PathP (λ i → Bprop (idl g i)) p (·-ind ε g pε p)
  induction (invr g i) = path i where
    p : B g
    p = induction g
    pinv : B (inv g)
    pinv = inv-ind g p
    pε : B ε
    pε = induction ε
    path : PathP (λ i → B (invr g i)) (·-ind g (inv g) p pinv) pε
    path = isProp→PathP (λ i → Bprop (invr g i)) (·-ind g (inv g) p pinv) pε
  induction (invl g i) = path i where
    p : B g
    p = induction g
    pinv : B (inv g)
    pinv = inv-ind g p
    pε : B ε
    pε = induction ε
    path : PathP (λ i → B (invl g i)) (·-ind (inv g) g pinv p) pε
    path = isProp→PathP (λ i → Bprop (invl g i)) (·-ind (inv g) g pinv p) pε
  induction (trunc g1 g2 q1 q2 i i₁) = square i i₁ where
    p1 : B g1
    p1 = induction g1
    p2 : B g2
    p2 = induction g2
    dq1 : PathP (λ i → B (q1 i)) p1 p2
    dq1 = cong induction q1
    dq2 : PathP (λ i → B (q2 i)) p1 p2
    dq2 = cong induction q2
    square : SquareP (λ i i₁ → B (trunc g1 g2 q1 q2 i i₁))
                {a₀₀ = p1} {a₀₁ = p2} dq1
                {a₁₀ = p1} {a₁₁ = p2} dq2
                (cong induction (refl {x = g1})) (cong induction (refl {x = g2}))
    square = isProp→SquareP (λ i i₁ → Bprop (trunc g1 g2 q1 q2 i i₁))
             (cong induction (refl {x = g1})) (cong induction (refl {x = g2}))
             dq1 dq2

-- Two group homomorphisms from FreeGroup to G are the same if they agree on every a : A
freeGroupHom≡ : {Group : Group ℓ'}{f g : GroupHom (freeGroupGroup A) Group}
               → (∀ a → (fst f) (η a) ≡ (fst g) (η a)) → f ≡ g
freeGroupHom≡ {Group = G , (groupstr 1g _·g_ invg isGrp)} {f} {g} eqOnA = GroupHom≡ (funExt pointwise) where
  open IsGroup isGrp using (is-set)
  B : ∀ x → Type _
  B x = (fst f) x ≡ (fst g) x
  Bprop : ∀ x → isProp (B x)
  Bprop x = is-set ((fst f) x) ((fst g) x)
  η-ind : ∀ a → B (η a)
  η-ind = eqOnA
  ·-ind : ∀ g1 g2 → B g1 → B g2 → B (g1 · g2)
  ·-ind g1 g2 ind1 ind2 =
    (fst f) (g1 · g2)
    ≡⟨ IsGroupHom.pres· (f .snd) g1 g2 ⟩
    ((fst f) g1) ·g ((fst f) g2)
    ≡⟨ cong (λ x → x ·g ((fst f) g2)) ind1 ⟩
    ((fst g) g1) ·g ((fst f) g2)
    ≡⟨ cong (λ x → ((fst g) g1) ·g x) ind2 ⟩
    ((fst g) g1) ·g ((fst g) g2)
    ≡⟨ sym (IsGroupHom.pres· (g .snd) g1 g2) ⟩
    (fst g) (g1 · g2) ∎
  ε-ind : B ε
  ε-ind =
    (fst f) ε
    ≡⟨ IsGroupHom.pres1 (f .snd) ⟩
    1g
    ≡⟨ sym (IsGroupHom.pres1 (g .snd)) ⟩
    (fst g) ε ∎
  inv-ind : ∀ x → B x → B (inv x)
  inv-ind x ind =
    (fst f) (inv x)
    ≡⟨ IsGroupHom.presinv (f .snd) x ⟩
    invg ((fst f) x)
    ≡⟨ cong invg ind ⟩
    invg ((fst g) x)
    ≡⟨ sym (IsGroupHom.presinv (g .snd) x) ⟩
    (fst g) (inv x) ∎
  pointwise : ∀ x → (fst f) x ≡ (fst g) x
  pointwise = elimProp Bprop η-ind ·-ind ε-ind inv-ind

-- The type of Group Homomorphisms from the FreeGroup A into G
-- is equivalent to the type of functions from A into G .fst
A→Group≃GroupHom : {Group : Group ℓ'} → (A → Group .fst) ≃ GroupHom (freeGroupGroup A) Group
A→Group≃GroupHom {Group = Group} = biInvEquiv→Equiv-right biInv where
  biInv : BiInvEquiv (A → Group .fst) (GroupHom (freeGroupGroup A) Group)
  BiInvEquiv.fun  biInv              = rec
  BiInvEquiv.invr biInv (hom , _) a  = hom (η a)
  BiInvEquiv.invr-rightInv biInv hom = freeGroupHom≡ (λ a → refl)
  BiInvEquiv.invl biInv (hom ,  _) a = hom (η a)
  BiInvEquiv.invl-leftInv biInv f    = funExt (λ a → refl)

freeGroupFunctor : Functor (SET ℓ) (GroupCategory {ℓ})
Functor.F-ob freeGroupFunctor (A , _) = freeGroupGroup A
Functor.F-hom freeGroupFunctor f = rec (η ∘ f)
Functor.F-id freeGroupFunctor =
  freeGroupHom≡ λ _ → refl
Functor.F-seq freeGroupFunctor _ _ =
  freeGroupHom≡ λ _ → refl

freeGroupFunctor⊣Forget : freeGroupFunctor NaturalBijection.⊣ (Forget {ℓ})
NaturalBijection._⊣_.adjIso freeGroupFunctor⊣Forget =
 invIso (equivToIso A→Group≃GroupHom)
NaturalBijection._⊣_.adjNatInD freeGroupFunctor⊣Forget _ _ = refl
NaturalBijection._⊣_.adjNatInC freeGroupFunctor⊣Forget _ _ = freeGroupHom≡ λ _ → refl

windingHom : GroupHom (freeGroupGroup A) ℤGroup
windingHom = rec λ _ → ℤ.pos 1

winding : FreeGroup A → ℤ.ℤ
winding = fst windingHom
