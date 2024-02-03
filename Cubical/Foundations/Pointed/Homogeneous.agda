{-

Definition of a homogeneous pointed type, and proofs that pi, product, path, and discrete types are homogeneous

Portions of this file adapted from Nicolai Kraus' code here:
  https://bitbucket.org/nicolaikraus/agda/src/e30d70c72c6af8e62b72eefabcc57623dd921f04/trunc-inverse.lagda

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Pointed.Homogeneous where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties
open import Cubical.Structures.Pointed

{-
  We might say that a type is homogeneous if its automorphism group acts transitively;
  this could be phrased with a propositional truncation.
  Here we demand something much stronger, namely that we are given automorphisms
  that carry the base point to any given point y.
  If in addition we require this automorphism to be the identity for the base point,
  then we recover the notion of a left-invertible H-space, and indeed,
  any homogeneous type in our sense gives rise to such, as shown in:

    Cubical.Homotopy.HSpace
-}
isHomogeneous : ∀ {ℓ} → Pointed ℓ → Type (ℓ-suc ℓ)
isHomogeneous {ℓ} (A , x) = ∀ y → Path (Pointed ℓ) (A , x) (A , y)

-- Pointed functions into a homogeneous type are equal as soon as they are equal
-- as unpointed functions
→∙Homogeneous≡ : ∀ {ℓ ℓ'} {A∙ : Pointed ℓ} {B∙ : Pointed ℓ'} {f∙ g∙ : A∙ →∙ B∙}
  (h : isHomogeneous B∙) → f∙ .fst ≡ g∙ .fst → f∙ ≡ g∙
→∙Homogeneous≡ {A∙ = A∙@(_ , a₀)} {B∙@(B , _)} {f∙@(_ , f₀)} {g∙@(_ , g₀)} h p =
  subst (λ Q∙ → PathP (λ i → A∙ →∙ Q∙ i) f∙ g∙) (sym (flipSquare fix)) badPath
  where
  badPath : PathP (λ i → A∙ →∙ (B , (sym f₀ ∙∙ funExt⁻ p a₀ ∙∙ g₀) i)) f∙ g∙
  badPath i .fst = p i
  badPath i .snd j = doubleCompPath-filler (sym f₀) (funExt⁻ p a₀) g₀ j i

  fix : PathP (λ i → B∙ ≡ (B , (sym f₀ ∙∙ funExt⁻ p a₀ ∙∙ g₀) i)) refl refl
  fix i =
    hcomp
      (λ j → λ
        { (i = i0) → lCancel (h (pt B∙)) j
        ; (i = i1) → lCancel (h (pt B∙)) j
        })
      (sym (h (pt B∙)) ∙ h ((sym f₀ ∙∙ funExt⁻ p a₀ ∙∙ g₀) i))

→∙HomogeneousPathP :
  ∀ {ℓ ℓ'} {A∙ A∙' : Pointed ℓ} {B∙ B∙' : Pointed ℓ'}
  {f∙ : A∙ →∙ B∙} {g∙ : A∙' →∙ B∙'} (p : A∙ ≡ A∙') (q : B∙ ≡ B∙')
  (h : isHomogeneous B∙')
  → PathP (λ i → fst (p i) → fst (q i)) (f∙ .fst) (g∙ .fst)
  → PathP (λ i → p i →∙ q i) f∙ g∙
→∙HomogeneousPathP p q h r = toPathP (→∙Homogeneous≡ h (fromPathP r))

→∙Homogeneous≡Path : ∀ {ℓ ℓ'} {A∙ : Pointed ℓ} {B∙ : Pointed ℓ'} {f∙ g∙ : A∙ →∙ B∙}
  (h : isHomogeneous B∙) → (p q : f∙ ≡ g∙) → cong fst p ≡ cong fst q → p ≡ q
→∙Homogeneous≡Path {A∙ = A∙@(A , a₀)} {B∙@(B , b)} {f∙@(f , f₀)} {g∙@(g , g₀)} h p q r =
  transport (λ k
      → PathP (λ i
        → PathP (λ j → (A , a₀) →∙ newPath-refl p q r i j (~ k))
                 (f , f₀) (g , g₀)) p q)
      (badPath p q r)
  where
  newPath : (p q : f∙ ≡ g∙) (r : cong fst p ≡ cong fst q)
    → Square (refl {x = b}) refl refl refl
  newPath p q r i j =
    hcomp (λ k → λ {(i = i0) → cong snd p j k
                   ; (i = i1) → cong snd q j k
                   ; (j = i0) → f₀ k
                   ; (j = i1) → g₀ k})
          (r i j a₀)

  newPath-refl : (p q : f∙ ≡ g∙) (r : cong fst p ≡ cong fst q)
         → PathP (λ i → (PathP (λ j → B∙ ≡ (B , newPath p q r i j))) refl refl) refl refl
  newPath-refl p q r i j k =
    hcomp (λ w → λ { (i = i0) → lCancel (h b) w k
                    ; (i = i1) → lCancel (h b) w k
                    ; (j = i0) → lCancel (h b) w k
                    ; (j = i1) → lCancel (h b) w k
                    ; (k = i0) → lCancel (h b) w k
                    ; (k = i1) → B , newPath p q r i j})
          ((sym (h b) ∙ h (newPath p q r i j)) k)

  badPath : (p q : f∙ ≡ g∙) (r : cong fst p ≡ cong fst q)
    → PathP (λ i →
        PathP (λ j → A∙ →∙ (B , newPath p q r i j))
             (f , f₀) (g , g₀))
              p q
  fst (badPath p q r i j) = r i j
  snd (badPath p q s i j) k =
    hcomp (λ r → λ { (i = i0) → snd (p j) (r ∧ k)
                    ; (i = i1) → snd (q j) (r ∧ k)
                    ; (j = i0) → f₀ (k ∧ r)
                    ; (j = i1) → g₀ (k ∧ r)
                    ; (k = i0) → s i j a₀})
          (s i j a₀)

→∙HomogeneousSquare : ∀ {ℓ ℓ'} {A∙ : Pointed ℓ} {B∙ : Pointed ℓ'} {f∙ g∙ h∙ l∙ : A∙ →∙ B∙}
  (h : isHomogeneous B∙) → (s : f∙ ≡ h∙) (t : g∙ ≡ l∙) (p : f∙ ≡ g∙) (q : h∙ ≡ l∙)
    → Square (cong fst p) (cong fst q) (cong fst s) (cong fst t)
    → Square p q s t
→∙HomogeneousSquare {f∙ = f∙} {g∙ = g∙} {h∙ = h∙} {l∙ = l∙} h =
  J (λ h∙ s → (t : g∙ ≡ l∙) (p : f∙ ≡ g∙) (q : h∙ ≡ l∙) →
      Square (cong fst p) (cong fst q) (cong fst s) (cong fst t) →
      Square p q s t)
   (J (λ l∙ t → (p : f∙ ≡ g∙) (q : f∙ ≡ l∙)
      → Square (cong fst p) (cong fst q) refl (cong fst t)
      → Square p q refl t)
      (→∙Homogeneous≡Path {f∙ = f∙} {g∙ = g∙} h))

isHomogeneousPi : ∀ {ℓ ℓ'} {A : Type ℓ} {B∙ : A → Pointed ℓ'}
                 → (∀ a → isHomogeneous (B∙ a)) → isHomogeneous (Πᵘ∙ A B∙)
isHomogeneousPi h f i .fst = ∀ a → typ (h a (f a) i)
isHomogeneousPi h f i .snd a = pt (h a (f a) i)

isHomogeneousΠ∙ : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : typ A → Type ℓ')
                  → (b₀ : B (pt A))
                  → ((a : typ A) (x : B a) → isHomogeneous (B a , x))
                  → (f : Π∙ A B b₀)
                  → isHomogeneous (Π∙ A B b₀ , f)
fst (isHomogeneousΠ∙ A B b₀ h f g i) =
  Σ[ r ∈ ((a : typ A) → fst ((h a (fst f a) (fst g a)) i)) ]
    r (pt A) ≡ hcomp (λ k → λ {(i = i0) → snd f k
                              ; (i = i1) → snd g k})
                     (snd (h (pt A) (fst f (pt A)) (fst g (pt A)) i))
snd (isHomogeneousΠ∙ A B b₀ h f g i) =
    (λ a → snd (h a (fst f a) (fst g a) i))
  , λ j → hcomp (λ k → λ { (i = i0) → snd f (k ∧ j)
                          ; (i = i1) → snd g (k ∧ j)
                          ; (j = i0) → snd (h (pt A) (fst f (pt A))
                                                      (fst g (pt A)) i)})
                 (snd (h (pt A) (fst f (pt A)) (fst g (pt A)) i))

isHomogeneous→∙ : ∀ {ℓ ℓ'} {A∙ : Pointed ℓ} {B∙ : Pointed ℓ'}
  → isHomogeneous B∙ → isHomogeneous (A∙ →∙ B∙ ∙)
isHomogeneous→∙ {A∙ = A∙} {B∙} h f∙ =
  ΣPathP
    ( (λ i → Π∙ A∙ (λ a → T a i) (t₀ i))
    , PathPIsoPath _ _ _ .Iso.inv
        (→∙Homogeneous≡ h
          (PathPIsoPath (λ i → (a : typ A∙) → T a i) (λ _ → pt B∙) _ .Iso.fun
            (λ i a → pt (h (f∙ .fst a) i))))
    )
  where
  T : ∀ a → typ B∙ ≡ typ B∙
  T a i = typ (h (f∙ .fst a) i)

  t₀ : PathP (λ i → T (pt A∙) i) (pt B∙) (pt B∙)
  t₀ = cong pt (h (f∙ .fst (pt A∙))) ▷ f∙ .snd

isHomogeneousProd : ∀ {ℓ ℓ'} {A∙ : Pointed ℓ} {B∙ : Pointed ℓ'}
                   → isHomogeneous A∙ → isHomogeneous B∙ → isHomogeneous (A∙ ×∙ B∙)
isHomogeneousProd hA hB (a , b) i .fst = typ (hA a i) × typ (hB b i)
isHomogeneousProd hA hB (a , b) i .snd .fst = pt (hA a i)
isHomogeneousProd hA hB (a , b) i .snd .snd = pt (hB b i)

isHomogeneousPath : ∀ {ℓ} (A : Type ℓ) {x y : A} (p : x ≡ y) → isHomogeneous ((x ≡ y) , p)
isHomogeneousPath A {x} {y} p q
  = pointed-sip ((x ≡ y) , p) ((x ≡ y) , q) (eqv , compPathr-cancel p q)
  where eqv : (x ≡ y) ≃ (x ≡ y)
        eqv = compPathlEquiv (q ∙ sym p)

module HomogeneousDiscrete {ℓ} {A∙ : Pointed ℓ} (dA : Discrete (typ A∙)) (y : typ A∙) where

  -- switches pt A∙ with y
  switch : typ A∙ → typ A∙
  switch x with dA x (pt A∙)
  ...         | yes _ = y
  ...         | no _ with dA x y
  ...                | yes _  = pt A∙
  ...                | no  _  = x

  switch-ptA∙ : switch (pt A∙) ≡ y
  switch-ptA∙ with dA (pt A∙) (pt A∙)
  ...         | yes _ = refl
  ...         | no ¬p = ⊥.rec (¬p refl)

  switch-idp : ∀ x → switch (switch x) ≡ x
  switch-idp x with dA x (pt A∙)
  switch-idp x | yes p with dA y (pt A∙)
  switch-idp x | yes p | yes q = q ∙ sym p
  switch-idp x | yes p | no  _ with dA y y
  switch-idp x | yes p | no  _ | yes _ = sym p
  switch-idp x | yes p | no  _ | no ¬p = ⊥.rec (¬p refl)
  switch-idp x | no ¬p with dA x y
  switch-idp x | no ¬p | yes p with dA y (pt A∙)
  switch-idp x | no ¬p | yes p | yes q = ⊥.rec (¬p (p ∙ q))
  switch-idp x | no ¬p | yes p | no  _ with dA (pt A∙) (pt A∙)
  switch-idp x | no ¬p | yes p | no  _ | yes _ = sym p
  switch-idp x | no ¬p | yes p | no  _ | no ¬q = ⊥.rec (¬q refl)
  switch-idp x | no ¬p | no ¬q with dA x (pt A∙)
  switch-idp x | no ¬p | no ¬q | yes p = ⊥.rec (¬p p)
  switch-idp x | no ¬p | no ¬q | no  _ with dA x y
  switch-idp x | no ¬p | no ¬q | no  _ | yes q = ⊥.rec (¬q q)
  switch-idp x | no ¬p | no ¬q | no  _ | no  _ = refl

  switch-eqv : typ A∙ ≃ typ A∙
  switch-eqv = isoToEquiv (iso switch switch switch-idp switch-idp)

isHomogeneousDiscrete : ∀ {ℓ} {A∙ : Pointed ℓ} (dA : Discrete (typ A∙)) → isHomogeneous A∙
isHomogeneousDiscrete {ℓ} {A∙} dA y
  = pointed-sip (typ A∙ , pt A∙) (typ A∙ , y) (switch-eqv , switch-ptA∙)
  where open HomogeneousDiscrete {ℓ} {A∙} dA y
