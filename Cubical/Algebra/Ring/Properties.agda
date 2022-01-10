{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Algebra.Ring.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

open import Cubical.Data.Sigma
open import Cubical.Relation.Binary.Poset

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring.Base

open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

{-
  some basic calculations (used for example in QuotientRing.agda),
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
    y               ≡⟨ sym (+Lid y) ⟩
    0r + y          ≡⟨ cong (λ u → u + y) (sym (+Linv x)) ⟩
    (- x + x) + y   ≡⟨ sym (+Assoc _ _ _) ⟩
    (- x) + (x + y) ≡⟨ cong (λ u → (- x) + u) p ⟩
    (- x) + 0r      ≡⟨ +Rid _ ⟩
    - x             ∎

  equalByDifference : (x y : R)
                      → x - y ≡ 0r
                      → x ≡ y
  equalByDifference x y p =
    x               ≡⟨ sym (+Rid _) ⟩
    x + 0r          ≡⟨ cong (λ u → x + u) (sym (+Linv y)) ⟩
    x + ((- y) + y) ≡⟨ +Assoc _ _ _ ⟩
    (x - y) + y     ≡⟨ cong (λ u → u + y) p ⟩
    0r + y          ≡⟨ +Lid _ ⟩
    y               ∎

  0Selfinverse : - 0r ≡ 0r
  0Selfinverse = sym (implicitInverse _ _ (+Rid 0r))

  0Idempotent : 0r + 0r ≡ 0r
  0Idempotent = +Lid 0r

  +Idempotency→0 : (x : R) → x ≡ x + x → x ≡ 0r
  +Idempotency→0 x p =
    x               ≡⟨ sym (+Rid x) ⟩
    x + 0r          ≡⟨ cong (λ u → x + u) (sym (+Rinv _)) ⟩
    x + (x + (- x)) ≡⟨ +Assoc _ _ _ ⟩
    (x + x) + (- x) ≡⟨ cong (λ u → u + (- x)) (sym p) ⟩
    x + (- x)       ≡⟨ +Rinv _ ⟩
    0r              ∎

  -Idempotent : (x : R) → -(- x) ≡ x
  -Idempotent x =  - (- x)   ≡⟨ sym (implicitInverse (- x) x (+Linv _)) ⟩
                   x ∎

  0RightAnnihilates : (x : R) → x · 0r ≡ 0r
  0RightAnnihilates x =
              let x·0-is-idempotent : x · 0r ≡ x · 0r + x · 0r
                  x·0-is-idempotent =
                    x · 0r               ≡⟨ cong (λ u → x · u) (sym 0Idempotent) ⟩
                    x · (0r + 0r)        ≡⟨ ·Rdist+ _ _ _ ⟩
                    (x · 0r) + (x · 0r)  ∎
              in (+Idempotency→0 _ x·0-is-idempotent)

  0LeftAnnihilates : (x : R) → 0r · x ≡ 0r
  0LeftAnnihilates x =
              let 0·x-is-idempotent : 0r · x ≡ 0r · x + 0r · x
                  0·x-is-idempotent =
                    0r · x               ≡⟨ cong (λ u → u · x) (sym 0Idempotent) ⟩
                    (0r + 0r) · x        ≡⟨ ·Ldist+ _ _ _ ⟩
                    (0r · x) + (0r · x)  ∎
              in +Idempotency→0 _ 0·x-is-idempotent

  -DistR· : (x y : R) →  x · (- y) ≡ - (x · y)
  -DistR· x y = implicitInverse (x · y) (x · (- y))

                               (x · y + x · (- y)     ≡⟨ sym (·Rdist+ _ _ _) ⟩
                               x · (y + (- y))        ≡⟨ cong (λ u → x · u) (+Rinv y) ⟩
                               x · 0r                 ≡⟨ 0RightAnnihilates x ⟩
                               0r ∎)

  -DistL· : (x y : R) →  (- x) · y ≡ - (x · y)
  -DistL· x y = implicitInverse (x · y) ((- x) · y)

                              (x · y + (- x) · y     ≡⟨ sym (·Ldist+ _ _ _) ⟩
                              (x - x) · y            ≡⟨ cong (λ u → u · y) (+Rinv x) ⟩
                              0r · y                 ≡⟨ 0LeftAnnihilates y ⟩
                              0r ∎)

  -Swap· : (x y : R) → (- x) · y ≡ x · (- y)
  -Swap· _ _ = -DistL· _ _ ∙ sym (-DistR· _ _)

  -IsMult-1 : (x : R) → - x ≡ (- 1r) · x
  -IsMult-1 _ = sym (·Lid _) ∙ sym (-Swap· _ _)

  -Dist : (x y : R) → (- x) + (- y) ≡ - (x + y)
  -Dist x y =
    implicitInverse _ _
         ((x + y) + ((- x) + (- y)) ≡⟨ sym (+Assoc _ _ _) ⟩
          x + (y + ((- x) + (- y))) ≡⟨ cong
                                         (λ u → x + (y + u))
                                         (+Comm _ _) ⟩
          x + (y + ((- y) + (- x))) ≡⟨ cong (λ u → x + u) (+Assoc _ _ _) ⟩
          x + ((y + (- y)) + (- x)) ≡⟨ cong (λ u → x + (u + (- x)))
                                            (+Rinv _) ⟩
          x + (0r + (- x))           ≡⟨ cong (λ u → x + u) (+Lid _) ⟩
          x + (- x)                 ≡⟨ +Rinv _ ⟩
          0r ∎)

  translatedDifference : (x a b : R) → a - b ≡ (x + a) - (x + b)
  translatedDifference x a b =
              a - b                       ≡⟨ cong (λ u → a + u)
                                                  (sym (+Lid _)) ⟩
              (a + (0r + (- b)))          ≡⟨ cong (λ u → a + (u + (- b)))
                                                  (sym (+Rinv _)) ⟩
              (a + ((x + (- x)) + (- b))) ≡⟨ cong (λ u → a + u)
                                                  (sym (+Assoc _ _ _)) ⟩
              (a + (x + ((- x) + (- b)))) ≡⟨ (+Assoc _ _ _) ⟩
              ((a + x) + ((- x) + (- b))) ≡⟨ cong (λ u → u + ((- x) + (- b)))
                                                  (+Comm _ _) ⟩
              ((x + a) + ((- x) + (- b))) ≡⟨ cong (λ u → (x + a) + u)
                                                  (-Dist _ _) ⟩
              ((x + a) - (x + b)) ∎

  +Assoc-comm1 : (x y z : R) → x + (y + z) ≡ y + (x + z)
  +Assoc-comm1 x y z = +Assoc x y z ∙∙ cong (λ x → x + z) (+Comm x y) ∙∙ sym (+Assoc y x z)

  +Assoc-comm2 : (x y z : R) → x + (y + z) ≡ z + (y + x)
  +Assoc-comm2 x y z = +Assoc-comm1 x y z ∙∙ cong (λ x → y + x) (+Comm x z) ∙∙ +Assoc-comm1 y z x

  +ShufflePairs : (a b c d : R)
                → (a + b) + (c + d) ≡ (a + c) + (b + d)
  +ShufflePairs a b c d =
    (a + b) + (c + d) ≡⟨ +Assoc _ _ _ ⟩
    ((a + b) + c) + d ≡⟨ cong (λ u → u + d) (sym (+Assoc _ _ _)) ⟩
    (a + (b + c)) + d ≡⟨ cong (λ u → (a + u) + d) (+Comm _ _) ⟩
    (a + (c + b)) + d ≡⟨ cong (λ u → u + d) (+Assoc _ _ _) ⟩
    ((a + c) + b) + d ≡⟨ sym (+Assoc _ _ _) ⟩
    (a + c) + (b + d) ∎

  ·-assoc2 : (x y z w : R) → (x · y) · (z · w) ≡ x · (y · z) · w
  ·-assoc2 x y z w = ·Assoc (x · y) z w ∙ cong (_· w) (sym (·Assoc x y z))


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

  syntax compRingHom f g = g ∘r f

  compIdRingHom : {R S : Ring ℓ} (φ : RingHom R S) → compRingHom (idRingHom R) φ ≡ φ
  compIdRingHom φ = RingHom≡ refl

  idCompRingHom : {R S : Ring ℓ} (φ : RingHom R S) → compRingHom φ (idRingHom S) ≡ φ
  idCompRingHom φ = RingHom≡ refl

  compAssocRingHom : {R S T U : Ring ℓ} (φ : RingHom R S) (ψ : RingHom S T) (χ : RingHom T U) →
                     compRingHom (compRingHom φ ψ) χ ≡ compRingHom φ (compRingHom ψ χ)
  compAssocRingHom _ _ _ = RingHom≡ refl


module RingEquivs where
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


module RingHomTheory {R S : Ring ℓ} (φ : RingHom R S) where
  open RingTheory ⦃...⦄
  open RingStr ⦃...⦄
  open IsRingHom (φ .snd)
  private
    instance
      _ = R
      _ = S
      _ = snd R
      _ = snd S
    f = fst φ

  ker≡0→inj : ({x : ⟨ R ⟩} → f x ≡ 0r → x ≡ 0r)
            → ({x y : ⟨ R ⟩} → f x ≡ f y → x ≡ y)
  ker≡0→inj ker≡0 {x} {y} p = equalByDifference _ _ (ker≡0 path)
   where
   path : f (x - y) ≡ 0r
   path = f (x - y)     ≡⟨ pres+ _ _ ⟩
          f x + f (- y) ≡⟨ cong (f x +_) (pres- _) ⟩
          f x - f y     ≡⟨ cong (_- f y) p ⟩
          f y - f y     ≡⟨ +Rinv _ ⟩
          0r            ∎


-- the Ring version of uaCompEquiv
module RingUAFunctoriality where
 open RingStr
 open RingEquivs

 Ring≡ : (A B : Ring ℓ) → (
   Σ[ p ∈ ⟨ A ⟩ ≡ ⟨ B ⟩ ]
   Σ[ q0 ∈ PathP (λ i → p i) (0r (snd A)) (0r (snd B)) ]
   Σ[ q1 ∈ PathP (λ i → p i) (1r (snd A)) (1r (snd B)) ]
   Σ[ r+ ∈ PathP (λ i → p i → p i → p i) (_+_ (snd A)) (_+_ (snd B)) ]
   Σ[ r· ∈ PathP (λ i → p i → p i → p i) (_·_ (snd A)) (_·_ (snd B)) ]
   Σ[ s ∈ PathP (λ i → p i → p i) (-_ (snd A)) (-_ (snd B)) ]
   PathP (λ i → IsRing (q0 i) (q1 i) (r+ i) (r· i) (s i)) (isRing (snd A)) (isRing (snd B)))
   ≃ (A ≡ B)
 Ring≡ A B = isoToEquiv theIso
   where
   open Iso
   theIso : Iso _ _
   fun theIso (p , q0 , q1 , r+ , r· , s , t) i = p i
                                                , ringstr (q0 i) (q1 i) (r+ i) (r· i) (s i) (t i)
   inv theIso x = cong ⟨_⟩ x , cong (0r ∘ snd) x , cong (1r ∘ snd) x
                , cong (_+_ ∘ snd) x , cong (_·_ ∘ snd) x , cong (-_ ∘ snd) x , cong (isRing ∘ snd) x
   rightInv theIso _ = refl
   leftInv theIso _ = refl

 caracRing≡ : {A B : Ring ℓ} (p q : A ≡ B) → cong ⟨_⟩ p ≡ cong ⟨_⟩ q → p ≡ q
 caracRing≡ {A = A} {B = B} p q P =
   sym (transportTransport⁻ (ua (Ring≡ A B)) p)
                                    ∙∙ cong (transport (ua (Ring≡ A B))) helper
                                    ∙∙ transportTransport⁻ (ua (Ring≡ A B)) q
     where
     helper : transport (sym (ua (Ring≡ A B))) p ≡ transport (sym (ua (Ring≡ A B))) q
     helper = Σ≡Prop
                (λ _ → isPropΣ
                          (isOfHLevelPathP' 1 (is-set (snd B)) _ _)
                          λ _ → isPropΣ (isOfHLevelPathP' 1 (is-set (snd B)) _ _)
                          λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set (snd B)) _ _)
                          λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ2 λ _ _ → is-set (snd B)) _ _)
                          λ _ → isPropΣ (isOfHLevelPathP' 1 (isSetΠ λ _ → is-set (snd B)) _ _)
                          λ _ → isOfHLevelPathP 1 (isPropIsRing _ _ _ _ _) _ _)
               (transportRefl (cong ⟨_⟩ p) ∙ P ∙ sym (transportRefl (cong ⟨_⟩ q)))

 uaCompRingEquiv : {A B C : Ring ℓ} (f : RingEquiv A B) (g : RingEquiv B C)
                  → uaRing (compRingEquiv f g) ≡ uaRing f ∙ uaRing g
 uaCompRingEquiv f g = caracRing≡ _ _ (
   cong ⟨_⟩ (uaRing (compRingEquiv f g))
     ≡⟨ uaCompEquiv _ _ ⟩
   cong ⟨_⟩ (uaRing f) ∙ cong ⟨_⟩ (uaRing g)
     ≡⟨ sym (cong-∙ ⟨_⟩ (uaRing f) (uaRing g)) ⟩
   cong ⟨_⟩ (uaRing f ∙ uaRing g) ∎)



open RingHoms
open RingEquivs
open RingUAFunctoriality
-- A useful lemma when defining presheaves
recPT→Ring : {A : Type ℓ'} (𝓕  : A → Ring ℓ)
           → (σ : ∀ x y → RingEquiv (𝓕 x) (𝓕 y))
           → (∀ x y z → σ x z ≡ compRingEquiv (σ x y) (σ y z))
          ------------------------------------------------------
           → ∥ A ∥ → Ring ℓ
recPT→Ring 𝓕 σ compCoh = rec→Gpd isGroupoidRing 𝓕 is3-Constant𝓕
 where
 open 3-Constant
 open GpdElim

 is3-Constant𝓕 : 3-Constant 𝓕
 link is3-Constant𝓕 x y = uaRing (σ x y)
 coh₁ is3-Constant𝓕 x y z = transport⁻ (PathP≡compPath _ _ _)
                              (sym (cong uaRing (compCoh x y z) ∙ uaCompRingEquiv (σ x y) (σ y z)))


uniqueHom→uniqueEquiv : {A : Type ℓ'} (σ : A → Ring ℓ) (P : {x y : A} → RingHom (σ x) (σ y) → Type ℓ'')
                        (isPropP : {x y : A} (f : RingHom (σ x) (σ y)) → isProp (P f))
                        (Pid : {x : A} → P (idRingHom (σ x)))
                        (Pcomp : {x y z : A} {f : RingHom (σ x) (σ y)} {g : RingHom (σ y) (σ z)}
                               → P f → P g → P (g ∘r f))
                      → (∀ x y → ∃![ f ∈ RingHom (σ x) (σ y) ] P f)
                     ----------------------------------------------------------------------------
                      → ∀ x y → ∃![ e ∈ RingEquiv (σ x) (σ y) ] P (RingEquiv→RingHom e)
uniqueHom→uniqueEquiv σ P isPropP Pid Pcomp uniqueHom x y = (σEquiv , Pχ₁) ,
  λ e → Σ≡Prop (λ _ → isPropP _)
         (Σ≡Prop (λ _ → isPropIsRingHom _ _ _)
           (Σ≡Prop isPropIsEquiv (cong (fst ∘ fst)
                                       (uniqueHom _ _ .snd (RingEquiv→RingHom (e .fst) , e .snd)))))
  where
  open Iso
  χ₁ = uniqueHom x y .fst .fst
  Pχ₁ = uniqueHom x y .fst .snd
  χ₂ = uniqueHom y x .fst .fst
  Pχ₂ = uniqueHom y x .fst .snd
  χ₁∘χ₂≡id : χ₁ ∘r χ₂ ≡ idRingHom _
  χ₁∘χ₂≡id = cong fst (isContr→isProp (uniqueHom _ _)
                                      (χ₁ ∘r χ₂ , Pcomp Pχ₂ Pχ₁) (idRingHom _ , Pid))
  χ₂∘χ₁≡id : χ₂ ∘r χ₁ ≡ idRingHom _
  χ₂∘χ₁≡id = cong fst (isContr→isProp (uniqueHom _ _)
                                      (χ₂ ∘r χ₁ , Pcomp Pχ₁ Pχ₂) (idRingHom _ , Pid))

  σIso : Iso ⟨ σ x ⟩ ⟨ σ y ⟩
  fun σIso = fst χ₁
  inv σIso = fst χ₂
  rightInv σIso = funExt⁻ (cong fst χ₁∘χ₂≡id)
  leftInv σIso = funExt⁻ (cong fst χ₂∘χ₁≡id)

  σEquiv : RingEquiv (σ x) (σ y)
  fst σEquiv = isoToEquiv σIso
  snd σEquiv = snd χ₁



module _ (L' : Poset ℓ ℓ') (P : (fst L') → Type ℓ'') where
 private
  L = fst L'
  A = Σ L P
 open PosetStr (snd L')

 ourLemma : (𝓕 : A → Ring ℓ''') (Q : {x y : A} → RingHom (𝓕 x) (𝓕 y) → Type ℓ'''')
            (IsPropQ : {x y : A} (f : RingHom (𝓕 x) (𝓕 y)) → isProp (Q f))
            (Qid : {x : A} → Q (idRingHom (𝓕 x)))
            (Qcomp : {x y z : A} {f : RingHom (𝓕 x) (𝓕 y)} {g : RingHom (𝓕 y) (𝓕 z)}
                   → Q f → Q g → Q (g ∘r f))
          → (∀ (x y : A) → fst x ≤ fst y → ∃![ f ∈ RingHom (𝓕 x) (𝓕 y) ] Q f)
          → (x : L) → ∥ P x ∥ → Ring ℓ'''
 ourLemma 𝓕 Q isPropQ Qid Qcomp ≤→uniqheHom x = recPT→Ring (curry 𝓕 x)
   (λ p q → 𝓕UniqueEquiv p q .fst .fst)
     λ p q r → cong fst (𝓕UniqueEquiv p r .snd (_ , Qcomp (𝓕UniqueEquiv p q .fst .snd)
                                                           (𝓕UniqueEquiv q r .fst .snd)))
  where
  𝓕UniqueEquiv : ∀ (p q : P x) → ∃![ e ∈ RingEquiv (𝓕 (x , p)) (𝓕 (x , q)) ] Q (RingEquiv→RingHom e)
  𝓕UniqueEquiv = uniqueHom→uniqueEquiv (curry 𝓕 x) Q isPropQ Qid Qcomp
                                        (λ p q → ≤→uniqheHom _ _ (is-refl x))
