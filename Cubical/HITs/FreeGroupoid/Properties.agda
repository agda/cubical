{-

This file contains:

Properties of FreeGroupoid:
- Induction principle for the FreeGroupoid on hProps
- ∥freeGroupoid∥₂ is a Group
- FreeGroup A ≡ ∥ FreeGroupoid A ∥₂

-}

module Cubical.HITs.FreeGroupoid.Properties where

open import Cubical.HITs.FreeGroupoid.Base
open import Cubical.HITs.FreeGroup renaming (elimProp to freeGroupElimProp)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.HITs.SetTruncation renaming (rec to recTrunc)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

-- The induction principle for the FreeGroupoid for hProps
elimProp : ∀ {B : FreeGroupoid A → Type ℓ'}
         → ((x : FreeGroupoid A) → isProp (B x))
         → ((a : A) → B (η a))
         → ((g1 g2 : FreeGroupoid A) → B g1 → B g2 → B (g1 · g2))
         → (B ε)
         → ((g : FreeGroupoid A) → B g → B (inv g))
         → (x : FreeGroupoid A)
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

-- The truncation of the FreeGroupoid is a group and is equal to FreeGroup

∥freeGroupoid∥₂IsSet : isSet ∥ FreeGroupoid A ∥₂
∥freeGroupoid∥₂IsSet = squash₂

_∣·∣₂_ : ∥ FreeGroupoid A ∥₂ → ∥ FreeGroupoid A ∥₂ → ∥ FreeGroupoid A ∥₂
_∣·∣₂_ = rec2 ∥freeGroupoid∥₂IsSet (λ g1 g2 → ∣ g1 · g2 ∣₂)

∥freeGroupoid∥₂IsSemiGroup : ∀ {ℓ}{A : Type ℓ} → IsSemigroup _∣·∣₂_
∥freeGroupoid∥₂IsSemiGroup {A = A} = issemigroup ∥freeGroupoid∥₂IsSet |assoc∣₂ where
  inuctionBase : ∀ g1 g2 g3 → ∣ g1 ∣₂ ∣·∣₂ (∣ g2 ∣₂ ∣·∣₂ ∣ g3 ∣₂) ≡ (∣ g1 ∣₂ ∣·∣₂ ∣ g2 ∣₂) ∣·∣₂ ∣ g3 ∣₂
  inuctionBase g1 g2 g3 = cong (λ x → ∣ x ∣₂) (assoc g1 g2 g3)
  Bset : ∀ x y z → isSet (x ∣·∣₂ (y ∣·∣₂ z) ≡ (x ∣·∣₂ y) ∣·∣₂ z)
  Bset x y z = isProp→isSet (squash₂ (x ∣·∣₂ (y ∣·∣₂ z)) ((x ∣·∣₂ y) ∣·∣₂ z))
  |assoc∣₂ : (x y z : ∥ FreeGroupoid A ∥₂) → x ∣·∣₂ (y ∣·∣₂ z) ≡ (x ∣·∣₂ y) ∣·∣₂ z
  |assoc∣₂ = elim3 Bset inuctionBase

∣ε∣₂ : ∥ FreeGroupoid A ∥₂
∣ε∣₂ = ∣ ε ∣₂

∥freeGroupoid∥₂IsMonoid : IsMonoid {A = ∥ FreeGroupoid A ∥₂} ∣ε∣₂ _∣·∣₂_
∥freeGroupoid∥₂IsMonoid = ismonoid ∥freeGroupoid∥₂IsSemiGroup
  (λ x → elim (λ g → isProp→isSet (squash₂ (g ∣·∣₂ ∣ε∣₂) g)) (λ g → cong (λ g' → ∣ g' ∣₂) (sym (idr g))) x)
  (λ x → elim (λ g → isProp→isSet (squash₂ (∣ε∣₂ ∣·∣₂ g) g)) (λ g → cong (λ g' → ∣ g' ∣₂) (sym (idl g))) x)

∣inv∣₂ : ∥ FreeGroupoid A ∥₂ → ∥ FreeGroupoid A ∥₂
∣inv∣₂ = map inv

∥freeGroupoid∥₂IsGroup : IsGroup {G = ∥ FreeGroupoid A ∥₂} ∣ε∣₂ _∣·∣₂_ ∣inv∣₂
∥freeGroupoid∥₂IsGroup = isgroup ∥freeGroupoid∥₂IsMonoid
  (λ x → elim (λ g → isProp→isSet (squash₂ (g ∣·∣₂ (∣inv∣₂ g)) ∣ε∣₂)) (λ g → cong (λ g' → ∣ g' ∣₂) (invr g)) x)
  (λ x → elim (λ g → isProp→isSet (squash₂ ((∣inv∣₂ g) ∣·∣₂ g) ∣ε∣₂)) (λ g → cong (λ g' → ∣ g' ∣₂) (invl g)) x)

∥freeGroupoid∥₂GroupStr : GroupStr ∥ FreeGroupoid A ∥₂
∥freeGroupoid∥₂GroupStr = groupstr ∣ε∣₂ _∣·∣₂_ ∣inv∣₂ ∥freeGroupoid∥₂IsGroup

∥freeGroupoid∥₂Group : Type ℓ → Group ℓ
∥freeGroupoid∥₂Group A = ∥ FreeGroupoid A ∥₂ , ∥freeGroupoid∥₂GroupStr


forgetfulHom : GroupHom (freeGroupGroup A) (∥freeGroupoid∥₂Group A)
forgetfulHom = rec (λ a → ∣ η a ∣₂)

forgetfulHom⁻¹ : GroupHom (∥freeGroupoid∥₂Group A) (freeGroupGroup A)
forgetfulHom⁻¹ = invf , isHom where
  invf : ∥ FreeGroupoid A ∥₂ → FreeGroup A
  invf = recTrunc freeGroupIsSet aux where
    aux : FreeGroupoid A → FreeGroup A
    aux (η a)              = η a
    aux (g1 · g2)          = (aux g1) · (aux g2)
    aux ε                  = ε
    aux (inv g)            = inv (aux g)
    aux (assoc g1 g2 g3 i) = assoc (aux g1) (aux g2) (aux g3) i
    aux (idr g i)          = idr (aux g) i
    aux (idl g i)          = idl (aux g) i
    aux (invr g i)         = invr (aux g) i
    aux (invl g i)         = invl (aux g) i
  isHom : IsGroupHom {A = ∥ FreeGroupoid A ∥₂} {B = FreeGroup A} ∥freeGroupoid∥₂GroupStr invf freeGroupGroupStr
  IsGroupHom.pres· isHom x y = elim2 (λ x y → isProp→isSet (freeGroupIsSet (invf (x ∣·∣₂ y)) ((invf x) · (invf y)))) ind x y where
    ind : ∀ g1 g2 → invf (∣ g1 ∣₂ ∣·∣₂ ∣ g2 ∣₂) ≡ (invf ∣ g1 ∣₂) · (invf ∣ g2 ∣₂)
    ind g1 g2 = refl
  IsGroupHom.pres1 isHom = refl
  IsGroupHom.presinv isHom x = elim (λ x → isProp→isSet (freeGroupIsSet (invf (∣inv∣₂ x)) (inv (invf x)))) ind x where
    ind : ∀ g → invf (∣inv∣₂ ∣ g ∣₂) ≡ inv (invf ∣ g ∣₂)
    ind g = refl


freeGroupTruncIdempotentBiInvEquiv : BiInvEquiv (FreeGroup A) ∥ FreeGroupoid A ∥₂
freeGroupTruncIdempotentBiInvEquiv = biInvEquiv f invf rightInv invf leftInv where
  f : FreeGroup A → ∥ FreeGroupoid A ∥₂
  f = fst forgetfulHom
  invf : ∥ FreeGroupoid A ∥₂ → FreeGroup A
  invf = fst forgetfulHom⁻¹
  rightInv : ∀ (x : ∥ FreeGroupoid A ∥₂) → f (invf x) ≡ x
  rightInv x = elim (λ x → isProp→isSet (squash₂ (f (invf x)) x)) ind x where
    ind : ∀ (g : FreeGroupoid A) → f (invf ∣ g ∣₂) ≡ ∣ g ∣₂
    ind g = elimProp Bprop η-ind ·-ind ε-ind inv-ind g where
      Bprop : ∀ g → isProp (f (invf ∣ g ∣₂) ≡ ∣ g ∣₂)
      Bprop g = squash₂ (f (invf ∣ g ∣₂)) ∣ g ∣₂
      η-ind : ∀ a → f (invf ∣ η a ∣₂) ≡ ∣ η a ∣₂
      η-ind a = refl
      ·-ind : ∀ g1 g2 → f (invf ∣ g1 ∣₂) ≡ ∣ g1 ∣₂ → f (invf ∣ g2 ∣₂) ≡ ∣ g2 ∣₂ → f (invf ∣ g1 · g2 ∣₂) ≡ ∣ g1 · g2 ∣₂
      ·-ind g1 g2 ind1 ind2 =
        f (invf ∣ g1 · g2 ∣₂)
        ≡⟨ cong f (IsGroupHom.pres· (snd forgetfulHom⁻¹) ∣ g1 ∣₂ ∣ g2 ∣₂) ⟩
        f ((invf ∣ g1 ∣₂) · (invf ∣ g2 ∣₂))
        ≡⟨ IsGroupHom.pres· (snd forgetfulHom) (invf ∣ g1 ∣₂) (invf ∣ g2 ∣₂) ⟩
        (f (invf ∣ g1 ∣₂)) ∣·∣₂ (f (invf ∣ g2 ∣₂))
        ≡⟨ cong (λ x → x ∣·∣₂ (f (invf ∣ g2 ∣₂))) ind1 ⟩
        ∣ g1 ∣₂ ∣·∣₂ (f (invf ∣ g2 ∣₂))
        ≡⟨ cong (λ x → ∣ g1 ∣₂ ∣·∣₂ x) ind2 ⟩
        ∣ g1 · g2 ∣₂ ∎
      ε-ind : f (invf ∣ ε ∣₂) ≡ ∣ ε ∣₂
      ε-ind  = refl
      inv-ind : ∀ g → f (invf ∣ g ∣₂) ≡ ∣ g ∣₂ → f (invf ∣ inv g ∣₂) ≡ ∣ inv g ∣₂
      inv-ind g ind =
        f (invf ∣ inv g ∣₂)
        ≡⟨ refl ⟩
        f (invf (∣inv∣₂ ∣ g ∣₂))
        ≡⟨ cong f (IsGroupHom.presinv (snd forgetfulHom⁻¹) ∣ g ∣₂) ⟩
        f (inv (invf ∣ g ∣₂))
        ≡⟨ IsGroupHom.presinv (snd forgetfulHom) (invf ∣ g ∣₂) ⟩
        ∣inv∣₂ (f (invf ∣ g ∣₂))
        ≡⟨ cong ∣inv∣₂ ind ⟩
        ∣inv∣₂ ∣ g ∣₂
        ≡⟨ refl ⟩
        ∣ inv g ∣₂ ∎
  leftInv : ∀ (g : FreeGroup A) → invf (f g) ≡ g
  leftInv g = freeGroupElimProp Bprop η-ind ·-ind ε-ind inv-ind g where
      Bprop : ∀ g → isProp (invf (f g) ≡ g)
      Bprop g = freeGroupIsSet (invf (f g)) g
      η-ind : ∀ a → invf (f (η a)) ≡ (η a)
      η-ind a = refl
      ·-ind : ∀ g1 g2 → invf (f g1) ≡ g1 → invf (f g2) ≡ g2 → invf (f (g1 · g2)) ≡ g1 · g2
      ·-ind g1 g2 ind1 ind2 =
        invf (f (g1 · g2))
        ≡⟨ cong invf (IsGroupHom.pres· (snd forgetfulHom) g1 g2) ⟩
        invf ((f g1) ∣·∣₂ (f g2))
        ≡⟨ IsGroupHom.pres· (snd forgetfulHom⁻¹) (f g1) (f g2) ⟩
        (invf (f g1)) · (invf (f g2))
        ≡⟨ cong (λ x → x · (invf (f g2))) ind1 ⟩
        g1 · (invf (f g2))
        ≡⟨ cong (λ x → g1 · x) ind2 ⟩
        g1 · g2 ∎
      ε-ind : invf (f ε) ≡ ε
      ε-ind  = refl
      inv-ind : ∀ g → invf (f g) ≡ g → invf (f (inv g)) ≡ inv g
      inv-ind g ind =
        invf (f (inv g))
        ≡⟨ cong invf (IsGroupHom.presinv (snd forgetfulHom) g) ⟩
        invf (∣inv∣₂ (f g))
        ≡⟨ IsGroupHom.presinv (snd forgetfulHom⁻¹) (f g) ⟩
        inv (invf (f g))
        ≡⟨ cong inv ind ⟩
        inv g ∎

freeGroupTruncIdempotent≃ : FreeGroup A ≃ ∥ FreeGroupoid A ∥₂
freeGroupTruncIdempotent≃ = biInvEquiv→Equiv-right freeGroupTruncIdempotentBiInvEquiv

freeGroupTruncIdempotent : FreeGroup A ≡ ∥ FreeGroupoid A ∥₂
freeGroupTruncIdempotent = ua freeGroupTruncIdempotent≃
