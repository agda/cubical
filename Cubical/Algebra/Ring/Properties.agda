{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.Ring.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

open import Cubical.Functions.Embedding

import Cubical.Data.Nat.Base as ℕ
import Cubical.Data.Int.Base as ℤ
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Semiring.Base

open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

{-
  some basic calculations (used for example in Quotient.agda),
  that should become obsolete or subject to change once we have a
  ring solver (see https://github.com/agda/cubical/issues/297)
-}
module RingTheory (R' : Ring ℓ) where

  open RingStr (snd R')
  private R = ⟨ R' ⟩
  implicitInverse : (x y : R)
                 → x + y ≡ 0r
                 → y ≡ - x
  implicitInverse x y p =
    y               ≡⟨ sym (+IdL y) ⟩
    0r + y          ≡⟨ congL _+_ (sym (+InvL x)) ⟩
    (- x + x) + y   ≡⟨ sym (+Assoc _ _ _) ⟩
    (- x) + (x + y) ≡⟨ congR _+_ p ⟩
    (- x) + 0r      ≡⟨ +IdR _ ⟩
    - x             ∎

  equalByDifference : (x y : R)
                      → x - y ≡ 0r
                      → x ≡ y
  equalByDifference x y p =
    x               ≡⟨ sym (+IdR _) ⟩
    x + 0r          ≡⟨ congR _+_ (sym (+InvL y)) ⟩
    x + ((- y) + y) ≡⟨ +Assoc _ _ _ ⟩
    (x - y) + y     ≡⟨ congL _+_ p ⟩
    0r + y          ≡⟨ +IdL _ ⟩
    y               ∎

  0Selfinverse : - 0r ≡ 0r
  0Selfinverse = sym (implicitInverse _ _ (+IdR 0r))

  0Idempotent : 0r + 0r ≡ 0r
  0Idempotent = +IdL 0r

  +Idempotency→0 : (x : R) → x ≡ x + x → x ≡ 0r
  +Idempotency→0 = let open GroupTheory (AbGroup→Group (Ring→AbGroup R'))
                   in idFromIdempotency

  -Idempotent : (x : R) → -(- x) ≡ x
  -Idempotent x =  - (- x)   ≡⟨ sym (implicitInverse (- x) x (+InvL _)) ⟩
                   x ∎

  0RightAnnihilates : (x : R) → x · 0r ≡ 0r
  0RightAnnihilates x =
              let x·0-is-idempotent : x · 0r ≡ x · 0r + x · 0r
                  x·0-is-idempotent =
                    x · 0r               ≡⟨ congR _·_ (sym 0Idempotent) ⟩
                    x · (0r + 0r)        ≡⟨ ·DistR+ _ _ _ ⟩
                    (x · 0r) + (x · 0r)  ∎
              in (+Idempotency→0 _ x·0-is-idempotent)

  0LeftAnnihilates : (x : R) → 0r · x ≡ 0r
  0LeftAnnihilates x =
              let 0·x-is-idempotent : 0r · x ≡ 0r · x + 0r · x
                  0·x-is-idempotent =
                    0r · x               ≡⟨ congL _·_ (sym 0Idempotent) ⟩
                    (0r + 0r) · x        ≡⟨ ·DistL+ _ _ _ ⟩
                    (0r · x) + (0r · x)  ∎
              in +Idempotency→0 _ 0·x-is-idempotent

  -DistR· : (x y : R) →  x · (- y) ≡ - (x · y)
  -DistR· x y = implicitInverse (x · y) (x · (- y))

                               (x · y + x · (- y)     ≡⟨ sym (·DistR+ _ _ _) ⟩
                               x · (y + (- y))        ≡⟨ congR _·_ (+InvR y) ⟩
                               x · 0r                 ≡⟨ 0RightAnnihilates x ⟩
                               0r ∎)

  -DistL· : (x y : R) →  (- x) · y ≡ - (x · y)
  -DistL· x y = implicitInverse (x · y) ((- x) · y)

                              (x · y + (- x) · y     ≡⟨ sym (·DistL+ _ _ _) ⟩
                              (x - x) · y            ≡⟨ congL _·_ (+InvR x) ⟩
                              0r · y                 ≡⟨ 0LeftAnnihilates y ⟩
                              0r ∎)

  -Swap· : (x y : R) → (- x) · y ≡ x · (- y)
  -Swap· _ _ = -DistL· _ _ ∙ sym (-DistR· _ _)

  -IsMult-1 : (x : R) → - x ≡ (- 1r) · x
  -IsMult-1 _ = sym (·IdL _) ∙ sym (-Swap· _ _)

  -Dist : (x y : R) → (- x) + (- y) ≡ - (x + y)
  -Dist x y =
    implicitInverse _ _
         ((x + y) + ((- x) + (- y)) ≡⟨ sym (+Assoc _ _ _) ⟩
          x + (y + ((- x) + (- y))) ≡⟨ congR _+_ (congR _+_ (+Comm _ _)) ⟩
          x + (y + ((- y) + (- x))) ≡⟨ congR _+_ (+Assoc _ _ _) ⟩
          x + ((y + (- y)) + (- x)) ≡⟨ congR _+_ (congL _+_ (+InvR _)) ⟩
          x + (0r + (- x))          ≡⟨ congR _+_ (+IdL _) ⟩
          x + (- x)                 ≡⟨ +InvR _ ⟩
          0r ∎)

  translatedDifference : (x a b : R) → a - b ≡ (x + a) - (x + b)
  translatedDifference x a b =
              a - b                       ≡⟨ congR _+_ (sym (+IdL _)) ⟩
              (a + (0r + (- b)))          ≡⟨ congR _+_ (congL _+_ (sym (+InvR _))) ⟩
              (a + ((x + (- x)) + (- b))) ≡⟨ congR _+_ (sym (+Assoc _ _ _)) ⟩
              (a + (x + ((- x) + (- b)))) ≡⟨ (+Assoc _ _ _) ⟩
              ((a + x) + ((- x) + (- b))) ≡⟨ congL _+_ (+Comm _ _) ⟩
              ((x + a) + ((- x) + (- b))) ≡⟨ congR _+_ (-Dist _ _) ⟩
              ((x + a) - (x + b)) ∎

  +Assoc-comm1 : (x y z : R) → x + (y + z) ≡ y + (x + z)
  +Assoc-comm1 x y z = +Assoc x y z ∙∙ congL _+_ (+Comm x y) ∙∙ sym (+Assoc y x z)

  +Assoc-comm2 : (x y z : R) → x + (y + z) ≡ z + (y + x)
  +Assoc-comm2 x y z = +Assoc-comm1 x y z ∙∙ congR _+_ (+Comm x z) ∙∙ +Assoc-comm1 y z x

  +ShufflePairs : (a b c d : R)
                → (a + b) + (c + d) ≡ (a + c) + (b + d)
  +ShufflePairs a b c d =
    (a + b) + (c + d) ≡⟨ +Assoc _ _ _ ⟩
    ((a + b) + c) + d ≡⟨ congL _+_ (sym (+Assoc _ _ _)) ⟩
    (a + (b + c)) + d ≡⟨ congL _+_ (congR _+_ (+Comm _ _)) ⟩
    (a + (c + b)) + d ≡⟨ congL _+_ (+Assoc _ _ _) ⟩
    ((a + c) + b) + d ≡⟨ sym (+Assoc _ _ _) ⟩
    (a + c) + (b + d) ∎

  ·-assoc2 : (x y z w : R) → (x · y) · (z · w) ≡ x · (y · z) · w
  ·-assoc2 x y z w = ·Assoc (x · y) z w ∙ congL _·_ (sym (·Assoc x y z))

  fromℕ : ℕ.ℕ → R
  fromℕ ℕ.zero = 0r
  fromℕ (ℕ.suc ℕ.zero) = 1r
  fromℕ (ℕ.suc (ℕ.suc n)) = 1r + fromℕ (ℕ.suc n)

  fromℤ : ℤ.ℤ → R
  fromℤ (ℤ.pos n) = fromℕ n
  fromℤ (ℤ.negsuc n) = - (fromℕ (ℕ.suc n))

Ring→Semiring : Ring ℓ → Semiring ℓ
Ring→Semiring R =
  let open RingStr (snd R)
      open RingTheory R
  in SemiringFromMonoids (fst R) 0r 1r _+_ _·_
       (CommMonoidStr.isCommMonoid (snd (AbGroup→CommMonoid (Ring→AbGroup R))))
       (MonoidStr.isMonoid (snd (Ring→MultMonoid R)))
       ·DistR+ ·DistL+
       0RightAnnihilates 0LeftAnnihilates

module RingHoms where
  open IsRingHom

  idRingHom : (R : Ring ℓ) → RingHom R R
  fst (idRingHom R) = idfun (fst R)
  snd (idRingHom R) = makeIsRingHom refl (λ _ _ → refl) (λ _ _ → refl)

  compIsRingHom : {A : Ring ℓ} {B : Ring ℓ'} {C : Ring ℓ''}
    {g : ⟨ B ⟩ → ⟨ C ⟩} {f : ⟨ A ⟩ → ⟨ B ⟩}
    → IsRingHom (B .snd) g (C .snd)
    → IsRingHom (A .snd) f (B .snd)
    → IsRingHom (A .snd) (g ∘ f) (C .snd)
  compIsRingHom {g = g} {f} gh fh .pres0 = cong g (fh .pres0) ∙ gh .pres0
  compIsRingHom {g = g} {f} gh fh .pres1 = cong g (fh .pres1) ∙ gh .pres1
  compIsRingHom {g = g} {f} gh fh .pres+ x y = cong g (fh .pres+ x y) ∙ gh .pres+ (f x) (f y)
  compIsRingHom {g = g} {f} gh fh .pres· x y = cong g (fh .pres· x y) ∙ gh .pres· (f x) (f y)
  compIsRingHom {g = g} {f} gh fh .pres- x = cong g (fh .pres- x) ∙ gh .pres- (f x)

  compRingHom : {R : Ring ℓ} {S : Ring ℓ'} {T : Ring ℓ''}
              → RingHom R S → RingHom S T → RingHom R T
  fst (compRingHom f g) x = g .fst (f .fst x)
  snd (compRingHom f g) = compIsRingHom (g .snd) (f .snd)

  _∘r_ : {R : Ring ℓ} {S : Ring ℓ'} {T : Ring ℓ''} → RingHom S T → RingHom R S → RingHom R T
  _∘r_ = flip compRingHom

  compIdRingHom : {R : Ring ℓ} {S : Ring ℓ'} (φ : RingHom R S) → compRingHom (idRingHom R) φ ≡ φ
  compIdRingHom φ = RingHom≡ refl

  idCompRingHom : {R : Ring ℓ} {S : Ring ℓ'} (φ : RingHom R S) → compRingHom φ (idRingHom S) ≡ φ
  idCompRingHom φ = RingHom≡ refl

  compAssocRingHom : {R : Ring ℓ} {S : Ring ℓ'} {T : Ring ℓ''} {U : Ring ℓ'''}
                   → (φ : RingHom R S) (ψ : RingHom S T) (χ : RingHom T U)
                   → compRingHom (compRingHom φ ψ) χ ≡ compRingHom φ (compRingHom ψ χ)
  compAssocRingHom _ _ _ = RingHom≡ refl

module RingEquivs where
  open RingStr
  open IsRingHom
  open RingHoms

  compIsRingEquiv : {A : Ring ℓ} {B : Ring ℓ'} {C : Ring ℓ''}
    {g : ⟨ B ⟩ ≃ ⟨ C ⟩} {f : ⟨ A ⟩ ≃ ⟨ B ⟩}
    → IsRingEquiv (B .snd) g (C .snd)
    → IsRingEquiv (A .snd) f (B .snd)
    → IsRingEquiv (A .snd) (compEquiv f g) (C .snd)
  compIsRingEquiv {g = g} {f} gh fh = compIsRingHom {g = g .fst} {f .fst} gh fh

  compRingEquiv : {A : Ring ℓ} {B : Ring ℓ'} {C : Ring ℓ''}
                → RingEquiv A B → RingEquiv B C → RingEquiv A C
  fst (compRingEquiv f g) = compEquiv (f .fst) (g .fst)
  snd (compRingEquiv f g) = compIsRingEquiv {g = g .fst} {f = f .fst} (g .snd) (f .snd)

  isRingHomInv : {A : Ring ℓ} → {B : Ring ℓ'} → (e : RingEquiv A B) → IsRingHom (snd B) (invEq (fst e)) (snd A)
  isRingHomInv {A = A} {B = B} e = makeIsRingHom
                         ((cong g (sym (pres1 fcrh))) ∙ retEq et (1r (snd A)))
                         (λ x y → g (snd B ._+_ x y)                 ≡⟨ cong g (sym (cong₂ (snd B ._+_) (secEq et x) (secEq et y))) ⟩
                                   g (snd B ._+_ (f (g x)) (f (g y))) ≡⟨ cong g (sym (pres+ fcrh (g x) (g y))) ⟩
                                   g (f (snd A ._+_ (g x) (g y)))     ≡⟨ retEq et (snd A ._+_ (g x) (g y)) ⟩
                                   snd A ._+_ (g x) (g y)  ∎)
                         (λ x y → g (snd B ._·_ x y)                 ≡⟨ cong g (sym (cong₂ (snd B ._·_) (secEq et x) (secEq et y))) ⟩
                                   g (snd B ._·_ (f (g x)) (f (g y))) ≡⟨ cong g (sym (pres· fcrh (g x) (g y))) ⟩
                                   g (f (snd A ._·_ (g x) (g y)))     ≡⟨ retEq et (snd A ._·_ (g x) (g y)) ⟩
                                   snd A ._·_ (g x) (g y)  ∎)
               where
               et = fst e
               f = fst et
               fcrh = snd e
               g = invEq et

  invRingEquiv : {A : Ring ℓ} → {B : Ring ℓ'} → RingEquiv A B → RingEquiv B A
  fst (invRingEquiv e) = invEquiv (fst e)
  snd (invRingEquiv e) = isRingHomInv e

  idRingEquiv : (A : Ring ℓ) → RingEquiv A A
  fst (idRingEquiv A) = idEquiv (fst A)
  snd (idRingEquiv A) = makeIsRingHom refl (λ _ _ → refl) (λ _ _ → refl)

module RingHomTheory {R : Ring ℓ} {S : Ring ℓ'} (φ : RingHom R S) where
  open RingTheory ⦃...⦄
  open RingStr ⦃...⦄
  open IsRingHom (φ .snd)
  private
    instance
      _ = snd R
      _ = snd S
    f = fst φ

  ker≡0→inj : ({x : ⟨ R ⟩} → f x ≡ 0r → x ≡ 0r)
            → ({x y : ⟨ R ⟩} → f x ≡ f y → x ≡ y)
  ker≡0→inj ker≡0 {x} {y} p = equalByDifference _ _ (ker≡0 path)
   where
   path : f (x - y) ≡ 0r
   path = f (x - y)     ≡⟨ pres+ _ _ ⟩
          f x + f (- y) ≡⟨ congR _+_ (pres- _) ⟩
          f x - f y     ≡⟨ congL _-_ p ⟩
          f y - f y     ≡⟨ +InvR _ ⟩
          0r            ∎


isSetRingStr : (R : Type ℓ) → isSet (RingStr R)
isSetRingStr R =
  let open RingStr
  in isOfHLevelSucIfInhabited→isOfHLevelSuc 1 λ str →
  isOfHLevelRetractFromIso 2 RingStrIsoΣ $
  isSetΣ (str .is-set) (λ _ →
  isSetΣ (str .is-set) (λ _ →
  isSetΣ (isSet→ (isSet→ (str .is-set))) λ _ →
  isSetΣ (isSet→ (isSet→ (str .is-set))) (λ _ →
  isSetΣSndProp (isSet→ (str .is-set)) (λ _ → isPropIsRing _ _ _ _ _))))

-- the Ring version of uaCompEquiv
module RingUAFunctoriality where
 open RingStr
 open RingEquivs

 caracRing≡ : {A B : Ring ℓ} (p q : A ≡ B) → cong ⟨_⟩ p ≡ cong ⟨_⟩ q → p ≡ q
 caracRing≡ _ _ α =
   isEmbedding→Inj (iso→isEmbedding (invIso ΣPathIsoPathΣ)) _ _ $
   Σ≡Prop (λ _ → isOfHLevelPathP' 1 (isSetRingStr _) _ _) α

 uaCompRingEquiv : {A B C : Ring ℓ} (f : RingEquiv A B) (g : RingEquiv B C)
                  → uaRing (compRingEquiv f g) ≡ uaRing f ∙ uaRing g
 uaCompRingEquiv f g = caracRing≡ _ _ (
   cong ⟨_⟩ (uaRing (compRingEquiv f g))
     ≡⟨ uaCompEquiv _ _ ⟩
   cong ⟨_⟩ (uaRing f) ∙ cong ⟨_⟩ (uaRing g)
     ≡⟨ sym (cong-∙ ⟨_⟩ (uaRing f) (uaRing g)) ⟩
   cong ⟨_⟩ (uaRing f ∙ uaRing g) ∎)



open RingEquivs
open RingUAFunctoriality
recPT→Ring : {A : Type ℓ'} (𝓕  : A → Ring ℓ)
           → (σ : ∀ x y → RingEquiv (𝓕 x) (𝓕 y))
           → (∀ x y z → σ x z ≡ compRingEquiv (σ x y) (σ y z))
          ------------------------------------------------------
           → ∥ A ∥₁ → Ring ℓ
recPT→Ring 𝓕 σ compCoh = rec→Gpd isGroupoidRing 𝓕
  (3-ConstantCompChar 𝓕 (λ x y → uaRing (σ x y))
                          λ x y z → sym (  cong uaRing (compCoh x y z)
                                         ∙ uaCompRingEquiv (σ x y) (σ y z)))
