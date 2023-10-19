{-

Whitehead's lemma for truncated spaces.

-}
{-# OPTIONS --safe #-}
module Cubical.Homotopy.WhiteheadsLemma where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; elim to sElim)
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ : Level

-- lots of easy helper lemmas, some of which are probably duplicating lemmas
-- proved elsewhere.
private
  SetTrunc→PropTrunc : {A : Type ℓ} → ∥ A ∥₂ → ∥ A ∥₁
  SetTrunc→PropTrunc = sRec (isProp→isSet isPropPropTrunc) ∣_∣₁

  isoPostComp : {A : Type ℓ} {a b c : A} (p : b ≡ c)
    → Iso (a ≡ b) (a ≡ c)
  Iso.fun (isoPostComp p) = λ r → r ∙ p
  Iso.inv (isoPostComp p) = λ r → r ∙ (sym p)
  Iso.rightInv (isoPostComp p) =
    λ r → (sym (assoc r (sym p) p)) ∙ cong (r ∙_) (lCancel p) ∙ sym (rUnit r)
  Iso.leftInv (isoPostComp p) =
    λ r → (sym (assoc r p (sym p))) ∙ cong (r ∙_) (rCancel p) ∙ sym (rUnit r)

  isoPostComp≃∙ : {A : Type ℓ} {a b c : A} {q : a ≡ b} (p : b ≡ c)
    → ((a ≡ b) , q) ≃∙ ((a ≡ c) , q ∙ p)
  fst (isoPostComp≃∙ p) = isoToEquiv (isoPostComp p)
  snd (isoPostComp≃∙ p) = refl

  isoPreComp : {A : Type ℓ} {a b c : A} (p : a ≡ b)
    → Iso (b ≡ c) (a ≡ c)
  Iso.fun (isoPreComp p) = λ r → p ∙ r
  Iso.inv (isoPreComp p) = λ r → (sym p) ∙ r
  Iso.rightInv (isoPreComp p) =
    λ r → assoc p (sym p) r ∙ cong (_∙ r) (rCancel p) ∙ sym (lUnit r)
  Iso.leftInv (isoPreComp p) =
    λ r → assoc (sym p) p r ∙ cong (_∙ r) (lCancel p) ∙ sym (lUnit r)

  isoPreComp≃∙ : {A : Type ℓ} {a b c : A} {q : b ≡ c} (p : a ≡ b)
    → ((b ≡ c) , q) ≃∙ ((a ≡ c) , p ∙ q)
  fst (isoPreComp≃∙ p) = isoToEquiv (isoPreComp p)
  snd (isoPreComp≃∙ p) = refl

  PathPCongLemma : {A B : Type ℓ}
    (f : A → B)
    (a a' : A)
    (r : a ≡ a')
    (b : B)
    (p : f a ≡ b)
    (q : f a' ≡ b)
    → cong f r ≡ p ∙ (sym q)
    → PathP (λ i → f (r i) ≡ b) p q
  PathPCongLemma {B = B} f a a' =
    J (λ a'' r → (b : B) (p : f a ≡ b) (q : f a'' ≡ b)
       → cong f r ≡ p ∙ (sym q)
       → PathP (λ i → f (r i) ≡ b) p q)
      (λ b p q r →
       sym (lUnit q ∙ cong (_∙ q) r ∙ sym (assoc p (sym q) q)
                    ∙ cong (p ∙_) (lCancel q) ∙ sym (rUnit p)))

  module _ (F : Pointed ℓ → Pointed ℓ)
           (F' : {A B : Pointed ℓ} → (A →∙ B) → (F A →∙ F B)) where

    specialCong∙ : {A B C D : Pointed ℓ} (p : A ≡ C) (q : B ≡ D)
                   (f : A →∙ B) (g : C →∙ D)
                   (r : PathP (λ i → (p i) →∙ (q i)) f g)
                → PathP (λ i → (cong F p) i →∙ (cong F q) i) (F' f) (F' g)
    specialCong∙ {A = A} {B = B} {C = C} {D = D} =
      J ( λ C' p →
                    (q : B ≡ D) (f : A →∙ B) (g : C' →∙ D)
                    (r : PathP (λ i → (p i) →∙ (q i)) f g)
                 → PathP (λ i → (cong F p) i →∙ (cong F q) i) (F' f) (F' g))
        ( J ( λ D' q →
                        (f : A →∙ B) (g : A →∙ D')
                        (r : PathP (λ i → A →∙ (q i)) f g)
                     → PathP (λ i → F A →∙ (cong F q) i) (F' f) (F' g))
            ( λ f g r → cong F' r))

  ∙PathP→Square : {A B C D : Pointed ℓ} (p : A ≡ C) (q : B ≡ D)
    (f : A →∙ B) (g : C →∙ D)
    → PathP (λ i → (p i) →∙ (q i)) f g
    → (Iso.inv (pathToIso (λ i → fst (q i))))
     ∘ (fst g)
     ∘ (Iso.fun (pathToIso (λ i → fst (p i))))
     ≡ (fst f)
  ∙PathP→Square {A = A} {B = B} {C = C} {D = D} =
    J ( λ C' p →
                  (q : B ≡ D) (f : A →∙ B) (g : C' →∙ D)
               → PathP (λ i → (p i) →∙ (q i)) f g
               → (Iso.inv (pathToIso (λ i → fst (q i))))
                 ∘ (fst g)
                 ∘ (Iso.fun (pathToIso (λ i → fst (p i))))
                 ≡ (fst f))
      ( J ( λ D' q →
                      (f : A →∙ B) (g : A →∙ D')
                   → PathP (λ i → A →∙ (q i)) f g
                   → (Iso.inv (pathToIso (λ i → fst (q i))))
                    ∘ (fst g)
                    ∘ (Iso.fun (pathToIso (λ i → (fst A))))
                    ≡ (fst f))
          ( λ f g r →
            funExt ( λ a → transportRefl (fst g (transport refl a))
                          ∙ cong (fst g) (transportRefl a)
                          ∙ λ i → (fst (r (~ i))) a)))

  doubleCompPath-filler-refl : {A : Type ℓ} {a b : A} (p : a ≡ b)
    → p ≡ refl ∙∙ p ∙∙ refl
  doubleCompPath-filler-refl p = doubleCompPath-filler refl p refl

  isContr→isContr→isEquiv : {A B : Type ℓ} (f : A → B)
    → isContr A → isContr B → isEquiv f
  equiv-proof (isContr→isContr→isEquiv f (a , hA) (b , hB)) b' =
    ( a , isContr→isProp (b , hB) (f a) b') ,
    ( λ (a' : fiber f b') → ΣPathP
              ( isContr→isProp (a , hA) a (fst a')
              , ( toPathP
                  ( isProp→isSet
                    ( isContr→isProp (b , hB))
                    ( f _) b'
                    ( transport (λ i → f _ ≡ b') _) (snd a')))))

  isPointedTarget→isEquiv→isEquiv : {A B : Type ℓ} (f : A → B)
    → (B → isEquiv f) → isEquiv f
  equiv-proof (isPointedTarget→isEquiv→isEquiv f hf) =
    λ y → equiv-proof (hf y) y

  squareWithEquivs→Equiv : {A B C D : Type ℓ}
    (f : A → B) (e1 : C → D) (e2 : A → C) (e3 : D → B)
    → isEquiv e1 → isEquiv e2 → isEquiv e3 → e3 ∘ e1 ∘ e2 ≡ f
    → isEquiv f
  squareWithEquivs→Equiv f e1 e2 e3 e1Eq e2Eq e3Eq p =
    transport
    ( λ i → isEquiv (p i))
    ( snd (compEquiv
           ( e2 , e2Eq)
           ( (e3 ∘ e1) , (snd (compEquiv (e1 , e1Eq) (e3 , e3Eq))))))
-- end of the long private block of helper lemmas

-- some useful paths between different maps 

{-

a ≡ b ------> f a ≡ f b
  |               ^
  |               |
  |               |
  v               |
a ≡ a ------> f a ≡ f a

-}
ΩCongSquare : {A B : Type ℓ} {a b : A} (f : A → B) (p : a ≡ b)
  → (λ q → q ∙ (cong f p))
   ∘ fst (Ω→ (f , refl))
   ∘ (λ q → q ∙ sym p)
   ≡ cong f
ΩCongSquare f =
  J ( λ b p → (λ q → q ∙ (cong f p))
             ∘ fst (Ω→ (f , refl))
             ∘ (λ q → q ∙ sym p)
             ≡ cong f)
    ( funExt (λ x → sym (rUnit _)
                   ∙ sym (doubleCompPath-filler-refl _)
                   ∙ cong (cong f) (sym (rUnit _))))

private
  setMapFunctorial : {A B C : Type ℓ} (f : A → B) (g : B → C)
    → map g ∘ map f ≡ map (g ∘ f)
  setMapFunctorial f g =
    funExt (sElim (λ x → isSetPathImplicit) λ a → refl)

  πHomπHomCongSquareAux : {A B : Type ℓ} {a : A} {n : ℕ} (f : A → B)
    → Iso.inv (Iso-πΩ-π (1 + n))
     ∘ (fst (πHom {A = (A , a)} {B = (B , f a)} (1 + n) (f , refl)))
     ∘ (Iso.fun (Iso-πΩ-π (1 + n)))
     ≡ map (Iso.inv (invIso (flipΩIso (1 + n)))
         ∘ fst ((Ω^→ (2 + n)) (f , refl))
         ∘ Iso.fun (invIso (flipΩIso (1 + n))))
  πHomπHomCongSquareAux {n = n} f =
      cong
      ( λ g → g ∘ (Iso.fun (Iso-πΩ-π (1 + n))))
      ( setMapFunctorial
        ( fst ((Ω^→ (2 + n)) (f , refl)))
        ( Iso.fun (flipΩIso (1 + n))))
    ∙ setMapFunctorial
      ( Iso.inv (flipΩIso (1 + n)))
      ( Iso.fun (flipΩIso (1 + n)) ∘ fst ((Ω^→ (2 + n)) (f , refl)))

-- Ω (Ω→ f) ≡ Ω→ (Ω f)
PathPΩ^→Ω : {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → PathP (λ i → (flipΩPath {A = A} n) i
                   →∙ (flipΩPath {A = B} n) i)
           ((Ω^→ (1 + n)) f) ((Ω^→ n) (Ω→ f))
PathPΩ^→Ω zero f = refl
PathPΩ^→Ω (suc n) f =
  specialCong∙ Ω Ω→
  ( flipΩPath n)
  ( flipΩPath n)
  ( Ω^→ (1 + n) f)
  ( (Ω^→ n) (Ω→ f))
  ( PathPΩ^→Ω n f)

private
  flipIsoSquare : {A B C D : Type ℓ} (f : A → B) (g : C → D)
    (H : Iso A C) (J : Iso B D)
    → Iso.inv J ∘ g ∘ (Iso.fun H) ≡ f
    → Iso.inv (invIso J) ∘ f ∘ Iso.fun (invIso H) ≡ g
  flipIsoSquare f g H J p =
    sym
    ( funExt
      ( λ x →
          sym ((Iso.rightInv J) (g x))
          ∙ cong (λ y → Iso.fun J (Iso.inv J (g y)))
                 (sym ((Iso.rightInv H) x))
          ∙ cong (λ h → (Iso.fun J ∘ h ∘ Iso.inv H) x) p))

{-

Ωⁿ⁺¹ (Ω (A, a)) -------> Ωⁿ⁺¹ (Ω (B, f a))
        |                        ^
        |                        |
        |                        |
        v                        |
Ω (Ωⁿ⁺¹ (A, a)) -------> Ω (Ωⁿ⁺¹ (B, f a))

-}
Ω+1ΩCongSquare : {A B : Type ℓ} {a : A} {n : ℕ} (f : A → B)
  → Iso.inv (invIso (flipΩIso (1 + n)))
   ∘ fst ((Ω^→ {A = (A , a)} (2 + n)) (f , refl))
   ∘ Iso.fun (invIso (flipΩIso (1 + n)))
  ≡ fst ((Ω^→ (1 + n)) (Ω→ (f , refl)))
Ω+1ΩCongSquare {A = A} {a = a} {n = n} f =
  flipIsoSquare
  ( fst ((Ω^→ {A = (A , a)} (2 + n)) (f , refl)))
  ( fst ((Ω^→ (1 + n)) (Ω→ (f , refl))))
  ( flipΩIso (1 + n))
  ( flipΩIso (1 + n))
  ( ∙PathP→Square
    ( flipΩPath (1 + n))
    ( flipΩPath (1 + n))
    ( (Ω^→ {A = (A , a)} (2 + n)) (f , refl))
    ( (Ω^→ (1 + n)) (Ω→ (f , refl)))
    ( PathPΩ^→Ω (1 + n) (f , refl)))

private
  ∙∙Lemma : {A B : Type ℓ} {f : A → B} {a b : A} (p : a ≡ b)
            → (refl ∙∙ cong f p ∙∙ refl) ≡ cong f p
  ∙∙Lemma {f = f} =
    J (λ b p → (refl ∙∙ cong f p ∙∙ refl) ≡ cong f p)
      (∙∙lCancel refl)

{-

πₙ (Ω (A, a)) ------> πₙ (Ω (B, f a))
     |                        ^
     |                        |
     |                        |
     v                        |
πₙ₊₁ (A, a) ---------> πₙ₊₁ (B, f a) 

-}
πHomπHomCongSquare : {A B : Type ℓ} {a : A} {n : ℕ} (f : A → B)
  →  Iso.inv (Iso-πΩ-π (1 + n))
   ∘ (fst (πHom {A = (A , a)} {B = (B , f a)} (1 + n) (f , refl)))
   ∘ (Iso.fun (Iso-πΩ-π (1 + n)))
   ≡ (fst (πHom n (cong f , refl)))
πHomπHomCongSquare {A = A} {B = B} {a = a} {n = n} f =
  πHomπHomCongSquareAux {A = A} {B = B} {a = a} {n = n} f
  ∙ cong map (Ω+1ΩCongSquare {A = A} {B = B} {a = a} {n = n} f)
  ∙ cong map (cong (fst ∘ (Ω^→ (1 + n)))
                   ( funExt∙
                     ( ∙∙Lemma {f = f}
                     , JRefl ( λ b p → (refl ∙∙ cong f p ∙∙ refl) ≡ cong f p)
                             ( ∙∙lCancel refl)
                       ∙ rUnit (∙∙lCancel refl))))

πHomEquiv→πHomCongEquiv : {A B : Type ℓ} {a : A} {n : ℕ} (f : A → B)
  → isEquiv (fst (πHom {A = (A , a)} {B = (B , f a)} (1 + n) (f , refl)))
  → isEquiv (fst (πHom {A = Ω (A , a)} n (cong f , refl)))
πHomEquiv→πHomCongEquiv {A = A} {a = a} {n = n} f hf =
  squareWithEquivs→Equiv
  ( fst (πHom n (cong f , refl)))
  ( fst (πHom {A = (A , a)} (1 + n) (f , refl)))
  ( Iso.fun (Iso-πΩ-π (1 + n)))
  ( Iso.inv (Iso-πΩ-π (1 + n)))
  ( hf)
  ( snd (isoToEquiv (Iso-πΩ-π (1 + n))))
  ( snd (isoToEquiv (invIso (Iso-πΩ-π (1 + n)))))
  ( πHomπHomCongSquare {A = A} {a = a} {n = n} f)

-- helper lemmas for stronger statement:
-- (map f) is equiv and (cong f) is equiv together imply f is equiv
private
  congEquiv→EquivAux : {A B : Type ℓ}
    (f : A → B)
    (hf0 : isEquiv (map f))
    (b : B) → Σ[ a ∈ ∥ A ∥₂ ] ((map f) a ≡ ∣ b ∣₂)
  congEquiv→EquivAux f hf0 b = fst (equiv-proof hf0 ∣ b ∣₂)

  congEquiv→EquivAux''' : {A B : Type ℓ}
    (f : A → B)
    (b : B)
    → Σ[ a ∈ ∥ A ∥₂ ] ((map f) a ≡ ∣ b ∣₂)
    → ∥ Σ[ a ∈ A ] (f a ≡ b) ∥₁
  congEquiv→EquivAux''' {A = A} f b (a , p) =
    ( sElim
      { B = λ a → ((map f) a ≡ ∣ b ∣₂) → ∥ Σ[ a ∈ A ] (f a ≡ b) ∥₁}
      ( λ a → isSet→ (isProp→isSet isPropPropTrunc))
      ( λ a p → rec isPropPropTrunc ( λ p' → ∣ a , p' ∣₁)
                                     ( Iso.fun PathIdTrunc₀Iso p))
      ( a))
    ( p)

  congEquiv→EquivAux'' : {A B : Type ℓ}
    (f : A → B)
    (hf : (a b : A) → isEquiv {A = (a ≡ b)} (cong f))
    (b : B)
    → (x y : Σ[ a ∈ A ] (f a ≡ b))
    → Σ[ r ∈ ((fst x) ≡ (fst y)) ] ((cong f) r ≡ (snd x) ∙ (sym (snd y)))
  congEquiv→EquivAux'' f hf b x y =
    fst (equiv-proof (hf (fst x) (fst y)) (snd x ∙ (sym (snd y))))

  congEquiv→EquivAux' : {A B : Type ℓ}
    (f : A → B)
    (hf : (a b : A) → isEquiv {A = (a ≡ b)} (cong f))
    (b : B) → Σ[ a ∈ A ] (f a ≡ b) → isContr (Σ[ a ∈ A ] (f a ≡ b))
  congEquiv→EquivAux' f hf b (a , p) =
    ( a , p)
    , (λ y → ΣPathP ( fst (congEquiv→EquivAux'' f hf b (a , p) y)
                     , PathPCongLemma f a (fst y)
                                    _ b p (snd y)
                       ( snd (congEquiv→EquivAux'' f hf b (a , p) y))))

-- Stronger statement
congEquiv→Equiv : {A B : Type ℓ}
  (f : A → B)
  (hf0 : isEquiv (map f))
  (hf : (a b : A) → isEquiv {A = (a ≡ b)} (cong f))
  → isEquiv f
equiv-proof (congEquiv→Equiv f hf0 hf) b =
  rec isPropIsContr
  ( congEquiv→EquivAux' f hf b)
  ( congEquiv→EquivAux''' f b (congEquiv→EquivAux f hf0 b))

mapEquiv→imId→Id₋₁ : {A B : Type ℓ} {a b : A} (f : A → B)
  (hf0 : isEquiv (map f))
  → (f a ≡ f b) → ∥ a ≡ b ∥₁
mapEquiv→imId→Id₋₁ {a = a} {b = b} f hf0 p =
  Iso.fun PathIdTrunc₀Iso
  ( sym (fst (PathPΣ (snd (equiv-proof hf0 ∣ f b ∣₂) (∣ a ∣₂ , cong ∣_∣₂ p))))
  ∙ fst (PathPΣ (snd (equiv-proof hf0 ∣ f b ∣₂) (∣ b ∣₂ , refl))))

-- Stronger statement for Ω→ instead of cong
ΩEquiv→Equiv : {A B : Type ℓ}
  (f : A → B)
  (hf0 : isEquiv (map f))
  (hf : (a : A)
        → isEquiv
           ( fst (Ω→ {A = (A , a)} {B = (B , f a)} (f , refl))))
  → isEquiv f
ΩEquiv→Equiv {A = A} f hf0 hf =
  congEquiv→Equiv f hf0
  (λ a b → isPointedTarget→isEquiv→isEquiv
            ( cong f)
            ( λ q → rec
                     ( isPropIsEquiv _)
                     ( λ p → squareWithEquivs→Equiv
                              ( cong f)
                              ( fst (Ω→ {A = (A , a)} (f , refl)))
                              ( λ r → r ∙ sym p)
                              ( λ r → r ∙ (cong f p))
                              ( hf a)
                              ( snd (isoToEquiv (isoPostComp (sym p))))
                              ( snd (isoToEquiv (isoPostComp (cong f p))))
                              ( ΩCongSquare f p))
                     ( mapEquiv→imId→Id₋₁ f hf0 q)))

-- Appears as Theorem 8.8.3 in the HoTT Book
-- Proof similar to one there
WhiteheadsLemma : {A B : Type ℓ} {n : ℕ}
  (hA : isOfHLevel n A) (hB : isOfHLevel n B) (f : A → B)
  (hf0 : isEquiv (map f))
  (hf : (a : A) (k : ℕ)
        → isEquiv (fst (πHom {A = (A , a)} {B = (B , f a)} k (f , refl))))
  → isEquiv f
WhiteheadsLemma {n = zero} hA hB f hf0 hf = isContr→isContr→isEquiv f hA hB
WhiteheadsLemma {A = A} {B = B} {n = suc n} hA hB f hf0 hf =
  ΩEquiv→Equiv 
  ( f)
  ( hf0)
  ( λ a → WhiteheadsLemma
           ( isOfHLevelPath' n hA a a)
           ( isOfHLevelPath' n hB (f a) (f a))
           ( fst (Ω→ {A = (A , a)} {B = (B , f a)} (f , refl))) 
           ( hf a 0)
           ( ΩWhiteheadHyp a))
  where
    congWhiteheadHyp : (a a' : A) (p : a ≡ a') (k : ℕ)
                      → isEquiv
                         ( fst (πHom
                                { A = ((a ≡ a') , p)}
                                { B = (((f a) ≡ (f a')) , cong f p)}
                                ( k)
                                ( cong f , refl)))
    congWhiteheadHyp a a' =
                            J ( λ b p → (k : ℕ)
                                      → isEquiv
                                         ( fst (πHom
                                         { A = ((a ≡ b) , p)}
                                         { B = (((f a) ≡ (f b)) , cong f p)}
                                         ( k)
                                         ( cong f , refl))))
                            ( λ k → πHomEquiv→πHomCongEquiv
                                     { A = A}
                                     { B = B}
                                     { n = k}
                                     ( f)
                                     ( hf a (1 + k)))

    ΩWhiteheadHyp : (a : A) (p : fst (Ω (A , a))) (k : ℕ)
                  → isEquiv (fst (πHom k (fst (Ω→ (f , refl)) , refl)))
    ΩWhiteheadHyp a p k = transport
                          ( λ i → isEquiv
                          ( fst (πHom {A = (typ (Ω (A , a)) , p)} k
                                ( (λ p → (doubleCompPath-filler-refl
                                          ( cong f p)) i)
                                  , refl))))
                          ( congWhiteheadHyp a a p k)
