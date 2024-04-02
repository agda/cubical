{-# OPTIONS --safe #-}
module Cubical.HITs.SmashProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Fin

open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Wedge

data Smash {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') : Type (ℓ-max ℓ ℓ') where
  basel : Smash A B
  baser : Smash A B
  proj  : (x : typ A) → (y : typ B) → Smash A B
  gluel : (a : typ A) → proj a (pt B) ≡ basel
  gluer : (b : typ B) → proj (pt A) b ≡ baser

private
  variable
    ℓ ℓ' : Level
    A B C D : Pointed ℓ

infixl 30 _⋀∙_

SmashPt : (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
SmashPt A B = (Smash A B , basel)

SmashPtProj : (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
SmashPtProj A B = Smash A B , (proj (snd A) (snd B))

Smash-map : (f : A →∙ C) (g : B →∙ D) → Smash A B → Smash C D
Smash-map f g basel = basel
Smash-map f g baser = baser
Smash-map (f , fpt) (g , gpt) (proj x y) = proj (f x) (g y)
Smash-map (f , fpt) (g , gpt) (gluel a i) = ((λ j → proj (f a) (gpt j)) ∙ gluel (f a)) i
Smash-map (f , fpt) (g , gpt) (gluer b i) = ((λ j → proj (fpt j) (g b)) ∙ gluer (g b)) i

-- Commutativity
comm : Smash A B → Smash B A
comm basel       = baser
comm baser       = basel
comm (proj x y)  = proj y x
comm (gluel a i) = gluer a i
comm (gluer b i) = gluel b i

commK : (x : Smash A B) → comm (comm x) ≡ x
commK basel       = refl
commK baser       = refl
commK (proj x y)  = refl
commK (gluel a x) = refl
commK (gluer b x) = refl

--- Alternative definition

i∧ : {A : Pointed ℓ} {B : Pointed ℓ'} → A ⋁ B → (typ A) × (typ B)
i∧ {A = A , ptA} {B = B , ptB} (inl x) = x , ptB
i∧ {A = A , ptA} {B = B , ptB} (inr x) = ptA , x
i∧ {A = A , ptA} {B = B , ptB} (push tt i) = ptA , ptB

_⋀_ : Pointed ℓ → Pointed ℓ' → Type (ℓ-max ℓ ℓ')
A ⋀ B = Pushout {A = (A ⋁ B)} (λ _ → tt) i∧

_⋀∙_ : Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
A ⋀∙ B = (A ⋀ B) , (inl tt)

-- iterated products
⋀^ : (n : ℕ) (A : Fin (suc n) → Pointed ℓ) → Pointed ℓ
⋀^ zero A = A fzero
⋀^ (suc n) A = ⋀^ n (predFinFamily∙ A) ⋀∙ (A flast)

⋀comm→ : A ⋀ B → B ⋀ A
⋀comm→ (inl x) = inl x
⋀comm→ (inr (x , y)) = inr (y , x)
⋀comm→ (push (inl x) i) = push (inr x) i
⋀comm→ (push (inr x) i) = push (inl x) i
⋀comm→ (push (push a i₁) i) = push (push tt (~ i₁)) i

⋀comm→² : {A : Pointed ℓ} {B : Pointed ℓ' }
  (x : A ⋀ B) → ⋀comm→ (⋀comm→ {A = A} {B = B} x) ≡ x
⋀comm→² (inl x) = refl
⋀comm→² (inr x) = refl
⋀comm→² (push (inl x) i) = refl
⋀comm→² (push (inr x) i) = refl
⋀comm→² (push (push a i₁) i) = refl

⋀CommIso : Iso (A ⋀ B) (B ⋀ A)
Iso.fun ⋀CommIso = ⋀comm→
Iso.inv ⋀CommIso = ⋀comm→
Iso.rightInv ⋀CommIso = ⋀comm→²
Iso.leftInv ⋀CommIso = ⋀comm→²

⋀comm→∙ : A ⋀∙ B →∙ B ⋀∙ A
fst ⋀comm→∙ = ⋀comm→
snd ⋀comm→∙ = refl

SmashAdjIso : Iso ((A ⋀∙ B) →∙ C) (A →∙ (B →∙ C ∙))
SmashAdjIso {A = A} {B = B} {C = C} =
  compIso is₃ (compIso iso₄ (invIso is₂))
  where
  is₁ : Iso (A →∙ (B →∙ C ∙))
    (Σ[ f ∈ (fst A → fst B → fst C) ]
      Σ[ l ∈ ((x : fst A) → f x (pt B) ≡ pt C) ]
        Σ[ r ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
          PathP (λ i → r (snd B) i ≡ snd C) (l (snd A)) refl)
  Iso.fun is₁ f = (λ x y → f .fst x .fst y)
                , (λ x → f .fst x .snd)
                , (λ x i → f .snd i .fst x)
                , λ i j → f .snd i .snd j
  fst (fst (Iso.inv is₁ (f , l , r , p)) x) = f x
  snd (fst (Iso.inv is₁ (f , l , r , p)) x) = l x
  fst (snd (Iso.inv is₁ (f , l , r , p)) i) b = r b i
  snd (snd (Iso.inv is₁ (f , l , r , p)) i) j = p i j
  Iso.rightInv is₁ _ = refl
  Iso.leftInv is₁ _ = refl

  is₂ : Iso (A →∙ (B →∙ C ∙)) (
    (Σ[ f ∈ (fst A → fst B → fst C) ]
      Σ[ l ∈ ((x : fst A) → f x (pt B) ≡ pt C) ]
        Σ[ r ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
          l (pt A) ≡ r (pt B)))
  is₂ = compIso is₁ (Σ-cong-iso-snd
    λ f → Σ-cong-iso-snd
      λ l → Σ-cong-iso-snd
        λ r → pathToIso (PathP≡doubleCompPathʳ _ _ _ _
            ∙ cong (l (snd A) ≡_)
               (sym (compPath≡compPath' (r (snd B)) refl)
              ∙ sym (rUnit (r (pt B))))))

  is₃ : Iso ((A ⋀∙ B) →∙ C)
    (Σ[ f ∈ (fst A → fst B → fst C) ]
      Σ[ p ∈ singl (snd C) ]
        Σ[ l ∈ ((x : fst A) → f x (pt B) ≡ fst p) ]
        Σ[ r ∈ ((b : fst B) → f (pt A) b ≡ fst p) ]
          l (pt A) ≡ r (pt B))
  fst (Iso.fun is₃ f) x y = fst f (inr (x , y))
  fst (fst (snd (Iso.fun is₃ f))) = fst f (inl tt)
  snd (fst (snd (Iso.fun is₃ f))) = sym (snd f)
  fst (snd (snd (Iso.fun is₃ f))) x = cong (fst f) (sym (push (inl x)))
  fst (snd (snd (snd (Iso.fun is₃ f)))) x = cong (fst f) (sym (push (inr x)))
  snd (snd (snd (snd (Iso.fun is₃ f)))) i j = fst f (push (push tt i) (~ j))
  fst (Iso.inv is₃ (f , (c* , p) , l , r , q)) (inl x) = c*
  fst (Iso.inv is₃ (f , (c* , p) , l , r , q)) (inr (x , y)) = f x y
  fst (Iso.inv is₃ (f , (c* , p) , l , r , q)) (push (inl x) i) = l x (~ i)
  fst (Iso.inv is₃ (f , (c* , p) , l , r , q)) (push (inr x) i) = r x (~ i)
  fst (Iso.inv is₃ (f , (c* , p) , l , r , q)) (push (push a j) i) = q j (~ i)
  snd (Iso.inv is₃ (f , (c* , p) , l , r , q)) = sym p
  Iso.rightInv is₃ _ = refl
  Iso.leftInv is₃ f =
    ΣPathP ((funExt (λ { (inl x) → refl
                       ; (inr x) → refl
                       ; (push (inl x) i) → refl
                       ; (push (inr x) i) → refl
                       ; (push (push a i₁) i) → refl}))
                       , refl)

  isContrIso : ∀ {ℓ ℓ'} {A : Type ℓ} (a : A) (B : singl a → Type ℓ')
    → Iso (Σ _ B) (B (a , refl))
  isContrIso a B =
    compIso (invIso
      (Σ-cong-iso-fst (isContr→Iso isContrUnit (isContrSingl a))))
      lUnit×Iso

  iso₄ : Iso (isoToPath is₃ i1)
            (isoToPath is₂ i1)
  iso₄ = Σ-cong-iso-snd λ f → isContrIso (snd C) _

-- induction priciples for maps into pointed types
⋀→∙Homogeneous≡ : isHomogeneous C
  → {f g : (A ⋀∙ B) →∙ C}
  → ((x : fst A) (y : fst B) → fst f (inr (x , y)) ≡ fst g (inr (x , y)))
  → f ≡ g
⋀→∙Homogeneous≡ C {f = f} {g = g} p =
     sym (Iso.leftInv SmashAdjIso f)
  ∙∙ cong (Iso.inv SmashAdjIso) main
  ∙∙ Iso.leftInv SmashAdjIso g
  where
  main : Iso.fun SmashAdjIso f ≡ Iso.fun SmashAdjIso g
  main =
    →∙Homogeneous≡ (isHomogeneous→∙ C)
      (funExt λ x → →∙Homogeneous≡ C (funExt (p x)))

prod→⋀^ : (n : ℕ) (A : Fin (suc n) → Pointed ℓ)
  → prodFinFamily n (fst ∘ A) → ⋀^ n A .fst
prod→⋀^ zero A x = x
prod→⋀^ (suc n) A x =
  inr ((prod→⋀^ n (predFinFamily∙ A) (fst x)) , (snd x))

⋀→Homogeneous≡ : {A B : Pointed ℓ} {D : Type ℓ'}
  → {f g : A ⋀ B → D}
  → (isHomogeneous (D , f (inl tt)))
  → ((x : _) (y : _) → f (inr (x , y)) ≡ g (inr (x , y)))
  → f ≡ g
⋀→Homogeneous≡ {A = A} {B} {D} {f = f} {g} hom p = cong fst f^≡g^
  where
  f^ g^ : A ⋀∙ B →∙ (D , f (inl tt))
  f^ = f , refl
  g^ = g , (cong g (push (inr (pt B)))
        ∙∙ sym (p (pt A) (pt B))
        ∙∙ cong f (sym (push (inr (pt B)))))

  f^≡g^ : f^ ≡ g^
  f^≡g^ = ⋀→∙Homogeneous≡ hom p

⋀^→Homogeneous≡ : (n : ℕ) (A : Fin (suc n) → Pointed ℓ) {B : Type ℓ'}
  → {f g : ⋀^ n A .fst → B}
  → isHomogeneous (B , f (⋀^ n A .snd))
  → ((x : _) → f (prod→⋀^ n A x) ≡ g (prod→⋀^ n A x))
  → f ≡ g
⋀^→Homogeneous≡ zero A hom ind = funExt ind
⋀^→Homogeneous≡ (suc n) A {B = B} {f = f} {g} hom ind =
  ⋀→Homogeneous≡ hom λ x y
    → funExt⁻ (⋀^→Homogeneous≡ n (predFinFamily∙ A)
        {f = λ x → f (inr (x , y))} {g = λ x → g (inr (x , y))}
        (subst (isHomogeneous ∘ (B ,_))
          (cong f (push (inr y))) hom )
        λ _ → ind _) x

⋀^→Homogeneous : (n : ℕ) (A : Fin (suc n) → Pointed ℓ) (B : Pointed ℓ')
  → (isHomogeneous B)
  → (f g : ⋀^ n A →∙ B)
  → ((x : _) → f .fst (prod→⋀^ n A x) ≡ g .fst (prod→⋀^ n A x))
  → f ≡ g
⋀^→Homogeneous zero A B ishom f g ind = →∙Homogeneous≡ ishom (funExt ind)
⋀^→Homogeneous (suc n) A B ishom f g ind =
  ⋀→∙Homogeneous≡ ishom λ x y i
    → ⋀^→Homogeneous n (predFinFamily∙ A) B ishom
        (f' y) (g' y) (λ x → ind (x , y)) i .fst x
  where
  module _ (y : A flast .fst) where
    f' g' : ⋀^ n (predFinFamily∙ A) →∙ B
    f' = (λ x → f .fst (inr (x , y)))
       , cong (fst f) (sym (push (inr y))) ∙ snd f
    g' = (λ x → g .fst (inr (x , y)))
       , cong (fst g) (sym (push (inr y))) ∙ snd g

_⋀→_ : (f : A →∙ C) (g : B →∙ D) → A ⋀ B → C ⋀ D
(f ⋀→ g) (inl tt) = inl tt
((f , fpt) ⋀→ (g , gpt)) (inr (x , x₁)) = inr (f x , g x₁)
_⋀→_ {B = B} {D = D} (f ,  fpt) (b , gpt)  (push (inl x) i) = (push (inl (f x)) ∙ (λ i → inr (f x , gpt (~ i)))) i
_⋀→_ (f , fpt) (g , gpt) (push (inr x) i) = (push (inr (g x)) ∙ (λ i → inr (fpt (~ i) , g x))) i
_⋀→_ {A = A} {C = C} {B = B} {D = D} (f , fpt) (g , gpt) (push (push tt j) i) =
  hcomp (λ k → λ { (i = i0) → inl tt
                  ; (i = i1) → inr (fpt (~ k) , gpt (~ k))
                  ; (j = i0) → compPath-filler (push (inl (fpt (~ k))))
                                                ((λ i → inr (fpt (~ k) , gpt (~ i)))) k i
                  ; (j = i1) → compPath-filler (push (inr (gpt (~ k))))
                                                ((λ i → inr (fpt (~ i) , gpt (~ k)))) k i})
        (push (push tt j) i)

_⋀→∙_ : (f : A →∙ C) (g : B →∙ D) → A ⋀∙ B →∙ C ⋀∙ D
fst (f ⋀→∙ g) = f ⋀→ g
snd (f ⋀→∙ g) = refl


_⋀→refl_ : ∀ {ℓ ℓ'} {C : Type ℓ} {D : Type ℓ'}
  → (f : typ A → C)
  → (g : typ B → D)
  → (A ⋀ B) → ((C , f (pt A)) ⋀ (D , g (pt B)))
(f ⋀→refl g) (inl x) = inl tt
(f ⋀→refl g) (inr (x , y)) = inr (f x , g y)
(f ⋀→refl g) (push (inl x) i) = push (inl (f x)) i
(f ⋀→refl g) (push (inr x) i) = push (inr (g x)) i
(f ⋀→refl g) (push (push a i₁) i) = push (push tt i₁) i

_⋀∙→refl_ : ∀ {ℓ ℓ'} {C : Type ℓ} {D : Type ℓ'}
  → (f : typ A → C)
  → (g : typ B → D)
  → (A ⋀∙ B) →∙ ((C , f (pt A)) ⋀∙ (D , g (pt B)))
fst (f ⋀∙→refl g) = f ⋀→refl g
snd (f ⋀∙→refl g) = refl

⋀→Smash : A ⋀ B → Smash A B
⋀→Smash (inl x) = basel
⋀→Smash (inr (x , x₁)) = proj x x₁
⋀→Smash (push (inl x) i) = gluel x (~ i)
⋀→Smash {A = A} {B = B} (push (inr x) i) =
  (sym (gluel (snd A)) ∙∙ gluer (snd B) ∙∙ sym (gluer x)) i
⋀→Smash {A = A} {B = B} (push (push a j) i) =
  hcomp (λ k → λ { (i = i0) → gluel (snd A) (k ∨ ~ j)
                  ; (i = i1) → gluer (snd B) (~ k ∧ j)
                  ; (j = i0) → gluel (snd A) (~ i)})
        (invSides-filler (gluel (snd A)) (gluer (snd B)) j (~ i))

Smash→⋀ : Smash A B → A ⋀ B
Smash→⋀ basel = inl tt
Smash→⋀ baser = inl tt
Smash→⋀ (proj x y) = inr (x , y)
Smash→⋀ (gluel a i) = push (inl a) (~ i)
Smash→⋀ (gluer b i) = push (inr b) (~ i)

{- Associativity -}
module _ {ℓ ℓ' ℓ'' : Level} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') where

  -- HIT corresponding to A ⋀ B ⋀ C
  data ⋀×2 : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    base : ⋀×2
    proj : typ A → typ B → typ C → ⋀×2

    gluel : (x : typ A) (y : typ B) → proj x y (pt C) ≡ base
    gluem : (x : typ A) (z : typ C) → proj x (pt B) z ≡ base
    gluer : (y : typ B) (z : typ C) → proj (pt A) y z ≡ base

    gluel≡gluem : (a : typ A) → gluel a (pt B) ≡ gluem a (pt C)
    gluel≡gluer : (y : typ B) → Path (Path (⋀×2) _ _) (gluel (pt A) y) (gluer y (pt C))
    gluem≡gluer : (z : typ C) → gluem (pt A) z ≡ gluer (pt B) z

    coh : Cube (gluel≡gluer (snd B)) (gluem≡gluer (pt C))
               (gluel≡gluem (pt A)) (λ _ → gluer (snd B) (pt C))
               refl refl

  -- Step 1 (main step): show A ⋀ (B ⋀ C) ≃ ⋀×2 A B C

  -- some fillers needed for the maps back and forth
  filler₁ : typ B → (i j k : I) → ⋀×2
  filler₁ a i j r =
    hfill (λ k → λ {(i = i0) → gluer a (pt C) (j ∧ k)
                   ; (i = i1) → base
                   ; (j = i0) → gluel (pt A) a i
                   ; (j = i1) → gluer a (pt C) (i ∨ k)})
       (inS (gluel≡gluer a j i))
       r

  filler₂ : typ C → (i j k : I) → ⋀×2
  filler₂ c i j r =
    hfill (λ k → λ {(i = i0) → gluer (pt B) c (j ∧ k)
                    ; (i = i1) → base
                    ; (j = i0) → gluem (pt A) c i
                    ; (j = i1) → gluer (pt B) c (i ∨ k)})
        (inS (gluem≡gluer c j i))
        r

  filler₃ : typ B → (i j r : I) → A ⋀ (B ⋀∙ C)
  filler₃ b i j r =
    hfill (λ k → λ {(i = i0) → compPath-filler'
                                  (λ j → inr (pt A , (push (inl b) (~ j))))
                                  (sym (push (inl (pt A)))) k j
                   ; (i = i1) → push (inr (push (inl b) k)) (~ j)
                   ; (j = i0) → inr (pt A , push (inl b) k)
                   ; (j = i1) → inl tt})
           (inS (push (push tt i) (~ j)))
           r

  filler₄ : typ C → (i j r : I) → A ⋀ (B ⋀∙ C)
  filler₄ c i j r =
    hfill (λ k → λ {(i = i0) → compPath-filler'
                                  (λ j → inr (pt A , (push (inr c) (~ j))))
                                  (sym (push (inl (pt A)))) k j
                   ; (i = i1) → push (inr (push (inr c) k)) (~ j)
                   ; (j = i0) → inr (pt A , push (inr c) k)
                   ; (j = i1) → inl tt})
           (inS (push (push tt i) (~ j)))
           r

  filler₅ : (i j k : I) → A ⋀ (B ⋀∙ C)
  filler₅ i j r =
    hfill (λ k → λ {(i = i0) → push (inl (pt A)) j
                   ; (i = i1) → push (inr (inl tt)) (j ∧ ~ k)
                   ; (j = i0) → inl tt
                   ; (j = i1) → push (inr (inl tt)) (~ i ∨ ~ k)})
          (inS (push (push tt i) j))
          r

  coh-filler : (i j k r : I) → ⋀×2
  coh-filler i j k r =
    hfill (λ r → λ {(i = i0) → filler₁ (pt B) j k r
                   ; (i = i1) → filler₂ (pt C) j k r
                   ; (j = i0) → gluer (snd B) (snd C) (k ∧ r)
                   ; (j = i1) → base
                   ; (k = i0) → gluel≡gluem (pt A) i j
                   ; (k = i1) → gluer (snd B) (snd C) (j ∨ r)})
          (inS (coh i k j))
          r

  coh-filler₂ : (i j k r : I) → A ⋀ (B ⋀∙ C)
  coh-filler₂ i j k r =
    hfill (λ r → λ {(i = i0) → filler₃ (snd B) j k r
                   ; (i = i1) → filler₄ (pt C) j k r
                   ; (j = i0) → compPath-filler'
                                  (λ k₁ → inr (pt A , push (push tt i) (~ k₁)))
                                  (sym (push (inl (pt A)))) r k
                   ; (j = i1) → push (inr (push (push tt i) r)) (~ k)
                   ; (k = i0) → inr (pt A , push (push tt i) r)
                   ; (k = i1) → inl tt})
          (inS (push (push tt j) (~ k)))
          r

  ⋀→⋀×2 : A ⋀ (B ⋀∙ C) → ⋀×2
  ⋀→⋀×2 (inl x) = base
  ⋀→⋀×2 (inr (x , inl y)) = base
  ⋀→⋀×2 (inr (x , inr (y , z))) = proj x y z
  ⋀→⋀×2 (inr (x , push (inl a) i)) = gluel x a (~ i)
  ⋀→⋀×2 (inr (x , push (inr b) i)) = gluem x b (~ i)
  ⋀→⋀×2 (inr (x , push (push a i) j)) = gluel≡gluem x i (~ j)
  ⋀→⋀×2 (push (inl x) i) = base
  ⋀→⋀×2 (push (inr (inl x)) i) = base
  ⋀→⋀×2 (push (inr (inr (x , y))) i) = gluer x y (~ i)
  ⋀→⋀×2 (push (inr (push (inl x) i)) j) = filler₁ x (~ i) (~ j) i1
  ⋀→⋀×2 (push (inr (push (inr x) i)) j) = filler₂ x (~ i) (~ j) i1
  ⋀→⋀×2 (push (inr (push (push a i) j)) k) = coh-filler i (~ j) (~ k) i1
  ⋀→⋀×2 (push (push a i₁) i) = base

  ⋀×2→⋀ : ⋀×2 → A ⋀ (B ⋀∙ C)
  ⋀×2→⋀ base = inl tt
  ⋀×2→⋀ (proj x x₁ x₂) = inr (x , inr (x₁ , x₂))
  ⋀×2→⋀ (gluel x y i) =
    ((λ i → inr (x , (push (inl y) (~ i)))) ∙ sym (push (inl x))) i
  ⋀×2→⋀ (gluem x z i) =
    ((λ i → inr (x , (push (inr z) (~ i)))) ∙ sym (push (inl x))) i
  ⋀×2→⋀ (gluer y z i) = push (inr (inr (y , z))) (~ i)
  ⋀×2→⋀ (gluel≡gluem a i j) =
    ((λ k → inr (a , (push (push tt i) (~ k)))) ∙ sym (push (inl a))) j
  ⋀×2→⋀ (gluel≡gluer b i j) = filler₃ b i j i1
  ⋀×2→⋀ (gluem≡gluer c i j) = filler₄ c i j i1
  ⋀×2→⋀ (coh i j k) = coh-filler₂ i j k i1

  -- fillers for cancellation
  gluel-fill : (x : typ A) (b : typ B) (i j k : I) → ⋀×2
  gluel-fill x y i j k =
    hfill (λ k → λ {(i = i0) → gluel x y (~ k)
                   ; (i = i1) → base
                   ; (j = i0) →
                      ⋀→⋀×2 (compPath-filler'
                        (λ i → (inr (x , (push (inl y) (~ i)))))
                        (sym (push (inl x))) k i)
                   ; (j = i1) → gluel x y (i ∨ ~ k) })
          (inS base)
          k

  gluem-fill : (x : typ A) (z : typ C) (i j k : I) → ⋀×2
  gluem-fill x z i j k =
    hfill (λ k → λ {(i = i0) → gluem x z (~ k)
                   ; (i = i1) → base
                   ; (j = i0) → ⋀→⋀×2 (compPath-filler'
                                  (λ i → (inr (x , (push (inr z) (~ i)))))
                                  (sym (push (inl x))) k i)
                   ; (j = i1) → gluem x z (i ∨ ~ k)})
          (inS base)
          k

  gluel≡gluer₁ : (y : typ B) (i j r k : I) → ⋀×2
  gluel≡gluer₁ y i j r k =
    hfill (λ k → λ {(r = i0) → base
                     ; (r = i1) → gluer y (snd C) (i ∧ k)
                     ; (i = i0) → gluel≡gluer y j (~ r)
                     ; (i = i1) → gluer y (snd C) (~ r ∨ k)
                     ; (j = i0) → filler₁ y (~ r) i k
                     ; (j = i1) → gluer y (snd C) ((i ∧ k) ∨ ~ r)})
            (inS (gluel≡gluer y (j ∨ i) (~ r)))
           k


  gluem≡gluer₁ : (y : typ C) (i j r k : I) → ⋀×2
  gluem≡gluer₁ z i j r k =
    hfill (λ k → λ {(i = i0) → gluem≡gluer z j (~ r)
                   ; (i = i1) → gluer (snd B) z (~ r ∨ k)
                   ; (j = i0) → filler₂ z (~ r) i k
                   ; (j = i1) → gluer (snd B) z (~ r ∨ (k ∧ i))
                   ; (r = i0) → base
                   ; (r = i1) → gluer (snd B) z (i ∧ k)})
              (inS (gluem≡gluer z (j ∨ i) (~ r)))
              k

  gluel≡gluer₂ : (y : typ B) (k i j r : I) → ⋀×2
  gluel≡gluer₂ y k i j r =
    hfill (λ r → λ {(i = i0) → gluel≡gluer y (k ∧ j) (~ r)
                   ; (i = i1) → base
                   ; (j = i0) → ⋀→⋀×2 (filler₃ y k i r)
                   ; (j = i1) → gluel≡gluer y k (i ∨ ~ r)
                   ; (k = i0) → gluel-fill (pt A) y i j r
                   ; (k = i1) → gluel≡gluer₁ y i j r i1})
           (inS base)
           r

  gluem≡gluer₂ : (y : typ C) (k i j r : I) → ⋀×2
  gluem≡gluer₂ y k i j r =
    hfill (λ r → λ {(i = i0) → gluem≡gluer y (k ∧ j) (~ r)
                   ; (i = i1) → base
                   ; (j = i0) → ⋀→⋀×2 (filler₄ y k i r)
                   ; (j = i1) → gluem≡gluer y k (i ∨ ~ r)
                   ; (k = i0) → gluem-fill (pt A) y i j r
                   ; (k = i1) → gluem≡gluer₁ y i j r i1})
           (inS base)
           r

  gluel≡gluem-fill : (a : typ A) (i j k r : I) → ⋀×2
  gluel≡gluem-fill a i j k r =
    hfill (λ r → λ {(i = i0) → gluel≡gluem a k (~ r)
                   ; (i = i1) → base
                   ; (j = i0) → ⋀→⋀×2 (compPath-filler'
                      (λ i → inr (a , push (push tt k) (~ i))) (sym (push (inl a))) r i)
                   ; (j = i1) → gluel≡gluem a k (i ∨ ~ r)
                   ; (k = i0) → gluel-fill a (pt B) i j r
                   ; (k = i1) → gluem-fill a (pt C) i j r})
           (inS base)
           r

  ⋀×2→⋀→⋀×2 : (x : ⋀×2) → ⋀→⋀×2 (⋀×2→⋀ x) ≡ x
  ⋀×2→⋀→⋀×2 base = refl
  ⋀×2→⋀→⋀×2 (proj x x₁ x₂) = refl
  ⋀×2→⋀→⋀×2 (gluel x y i) j = gluel-fill x y i j i1
  ⋀×2→⋀→⋀×2 (gluem x z i) j = gluem-fill x z i j i1
  ⋀×2→⋀→⋀×2 (gluer y z i) = refl
  ⋀×2→⋀→⋀×2 (gluel≡gluem a k i) j = gluel≡gluem-fill a i j k i1
  ⋀×2→⋀→⋀×2 (gluel≡gluer y k i) j = gluel≡gluer₂ y k i j i1
  ⋀×2→⋀→⋀×2 (gluem≡gluer z k i) j = gluem≡gluer₂ z k i j i1
  ⋀×2→⋀→⋀×2 (coh i j k) r =
    hcomp (λ l → λ {(i = i0) → gluel≡gluer₂ (snd B) j k r l
                   ; (i = i1) → gluem≡gluer₂ (pt C) j k r l
                   ; (j = i0) → gluel≡gluem-fill (pt A) k r i l
                   ; (j = i1) → coh-lem l i k r
                   ; (k = i0) → coh i (j ∧ r) (~ l)
                   ; (k = i1) → base
                   ; (r = i0) → ⋀→⋀×2 (coh-filler₂ i j k l)
                   ; (r = i1) → coh i j (k ∨ ~ l)})
          base
    where
    coh-lem : PathP
         (λ l → Cube (λ k r → gluel≡gluer₂ (snd B) i1 k r l)
                      (λ k r → gluem≡gluer₂ (pt C) i1 k r l)
                      (λ i r → coh i r (~ l))
                      (λ i r → base)
                      (λ i k → coh-filler i (~ l) k i1)
                      λ i k → gluer (snd B) (snd C) (k ∨ ~ l))
                 (λ _ _ _ → base)
                 λ i k r → gluer (snd B) (pt C) k
    coh-lem l i k r =
      hcomp (λ j → λ {(i = i0) → gluel≡gluer₁ (pt B) k r l j
                      ; (i = i1) → gluem≡gluer₁ (pt C) k r l j
                      ; (l = i0) → base
                      ; (l = i1) → gluer (snd B) (pt C) (k ∧ j)
                      ; (k = i0) → coh i r (~ l)
                      ; (k = i1) → gluem≡gluer₁ (pt C) k r l j
                      ; (r = i0) → coh-filler i (~ l) k j
                      ; (r = i1) → gluer (snd B) (snd C) (~ l ∨ (j ∧ k))})
        (hcomp (λ j → λ {(i = i0) → gluel≡gluer (snd B) (r ∨ k) (~ l)
                      ; (i = i1) → gluem≡gluer (snd C) (r ∨ k) (~ l)
                      ; (l = i0) → base
                      ; (l = i1) → proj (pt A) (pt B) (snd C)
                      ; (k = i0) → coh i r (~ l)
                      ; (k = i1) → gluer (snd B) (snd C) (~ l)
                      ; (r = i0) → coh i k (~ l)
                      ; (r = i1) → gluer (snd B) (snd C) (~ l)})
               (coh i (r ∨ k) (~ l)))

  filler₆ : (x : typ A) (a : typ B) (i j k : I) → A ⋀ (B ⋀ C , inl tt)
  filler₆ x a i j k =
    hfill (λ k → λ {(i = i0) → inr (x , push (inl a) k)
                   ; (i = i1) → push (inl x) j
                   ; (j = i0) → compPath-filler'
                                  (λ i₁ → inr (x , (push (inl a) (~ i₁))))
                                  (sym (push (inl x))) k i
                   ; (j = i1) → inr (x , push (inl a) (~ i ∧ k)) })
          (inS (push (inl x) (j ∨ ~ i)))
          k

  filler₇ : (x : typ A) (a : typ C) (i j k : I) → A ⋀ (B ⋀ C , inl tt)
  filler₇ x a i j k =
    hfill (λ k → λ {(i = i0) → inr (x , push (inr a) k)
                   ; (i = i1) → push (inl x) j
                   ; (j = i0) → compPath-filler'
                                  (λ i₁ → inr (x , (push (inr a) (~ i₁))))
                                  (sym (push (inl x))) k i
                   ; (j = i1) → inr (x , push (inr a) (~ i ∧ k)) })
          (inS (push (inl x) (j ∨ ~ i)))
          k

  filler₈ : (x : typ A) (i j k r : I) → A ⋀ (B ⋀ C , inl tt)
  filler₈ x i j k r =
    hfill (λ r → λ {(i = i0) → inr (x , push (push tt k) r)
                   ; (i = i1) → push (inl x) j
                   ; (j = i0) → compPath-filler'
                                  (λ j → inr (x , push (push tt k) (~ j)))
                                  (sym (push (inl x))) r i
                   ; (j = i1) → inr (x , push (push tt k) (~ i ∧ r)) })
          (inS ((push (inl x) (j ∨ ~ i))))
          r

  btm-fill : (i j k r : I) → A ⋀ (B ⋀∙ C)
  btm-fill i j k r =
    hfill (λ r → λ {(i = i0) → push (inr (inl tt)) (~ j ∨ (r ∧ ~ k))
                              ; (i = i1) → filler₅ j k i1
                              ; (j = i1) → push (inr (inl tt)) (~ i ∧ (r ∧ ~ k))
                              ; (j = i0) → push (inl (pt A)) (~ i ∨ k)
                              ; (k = i0) → filler₅ j (~ i) (~ r)
                              ; (k = i1) → push (inr (inl tt)) (~ j)})
                     (inS (filler₅ j (~ i ∨ k) i1))
           r

  lr-fill₁ : (b : typ C) (i j k r : I) → A ⋀ (B ⋀∙ C)
  lr-fill₁ a i j k r =
    hfill (λ r → λ {(i = i0) → push (inr (push (inr a) r)) (~ j ∨ ~ k)
                   ; (i = i1) → filler₅ j k i1
                   ; (j = i1) → push (inr (push (inr a) r)) (~ i ∧ ~ k)
                   ; (j = i0) → filler₇ (pt A) a i k r
                   ; (k = i0) → filler₄ a j i r
                   ; (k = i1) → push (inr (push (inr a) (~ i ∧ r))) (~ j)})
              (inS (btm-fill i j k i1))
             r

  ll-fill₁ : (a : typ B) (i j k r : I) →  A ⋀ (B ⋀∙ C)
  ll-fill₁ a i j k r =
    hfill (λ r → λ {(i = i0) → push (inr (push (inl a) r)) (~ j ∨ ~ k)
                   ; (i = i1) → filler₅ j k i1
                   ; (j = i1) → push (inr (push (inl a) r)) (~ i ∧ ~ k)
                   ; (j = i0) → filler₆ (pt A) a i k r
                   ; (k = i0) → filler₃ a j i r
                   ; (k = i1) → push (inr (push (inl a) (~ i ∧ r))) (~ j)})
             (inS (btm-fill i j k i1))
             r

  ll-fill₂ : (a : typ B) (i j k r : I) → A ⋀ (B ⋀∙ C)
  ll-fill₂ a i j k r =
    hfill (λ r → λ {(i = i0) → push (inr (inr (a , pt C))) (~ j ∨ (~ r ∧ ~ k))
                   ; (i = i1) → filler₅ j k i1
                   ; (j = i1) → push (inr (inr (a , (snd C)))) ((~ r ∧ ~ i) ∧ ~ k)
                   ; (j = i0) → filler₆ (pt A) a i k i1
                   ; (k = i0) → ⋀×2→⋀ (filler₁ a i j r)
                   ; (k = i1) → push (inr (push (inl a) (~ i))) (~ j) })
      (inS (ll-fill₁ a i j k i1))
      r

  lr-fill₂ : (a : typ C) (i j k r : I) → A ⋀ (B ⋀∙ C)
  lr-fill₂ a i j k r =
    hfill (λ r → λ {(i = i0) → push (inr (inr (pt B , a))) (~ j ∨ (~ r ∧ ~ k))
                   ; (i = i1) → filler₅ j k i1
                   ; (j = i1) → push (inr (inr (pt B , a))) ((~ r ∧ ~ i) ∧ ~ k)
                   ; (j = i0) → filler₇ (pt A) a i k i1
                   ; (k = i0) → ⋀×2→⋀ (filler₂ a i j r)
                   ; (k = i1) → push (inr (push (inr a) (~ i))) (~ j) })
      (inS (lr-fill₁ a i j k i1))
      r

  ⋀→⋀×2→⋀ : (x : A ⋀ (B ⋀∙ C))
    → ⋀×2→⋀ (⋀→⋀×2 x) ≡ x
  ⋀→⋀×2→⋀ (inl x) = refl
  ⋀→⋀×2→⋀ (inr (x , inl x₁)) = push (inl x)
  ⋀→⋀×2→⋀ (inr (x , inr x₁)) = refl
  ⋀→⋀×2→⋀ (inr (x , push (inl a) i)) j = filler₆ x a (~ i) j i1
  ⋀→⋀×2→⋀ (inr (x , push (inr b) i)) j = filler₇ x b (~ i) j i1
  ⋀→⋀×2→⋀ (inr (x , push (push a r) i)) j = filler₈ x (~ i) j r i1
  ⋀→⋀×2→⋀ (push (inl x) i) j = push (inl x) (j ∧ i)
  ⋀→⋀×2→⋀ (push (inr (inl x)) i) j = filler₅ (~ i) j i1
  ⋀→⋀×2→⋀ (push (inr (inr x)) i) j = push (inr (inr x)) i
  ⋀→⋀×2→⋀ (push (inr (push (inl x) i)) j) k = ll-fill₂ x (~ i) (~ j) k i1
  ⋀→⋀×2→⋀ (push (inr (push (inr x) i)) j) k = lr-fill₂ x (~ i) (~ j) k i1
  ⋀→⋀×2→⋀ (push (inr (push (push a r) i)) j) k =
    hcomp (λ s → λ {(i = i0) → filler₅ (~ j) k i1
                   ; (i = i1) → push (inr (inr (snd B , snd C))) (j ∨ ~ s ∧ ~ k)
                   ; (j = i0) → push (inr (inr (pt B , pt C))) ((~ s ∧ i) ∧ ~ k)
                   ; (j = i1) → filler₈ (pt A) (~ i) k r i1
                   ; (k = i0) → ⋀×2→⋀ (coh-filler r (~ i) (~ j) s)
                   ; (k = i1) → push (inr (push (push tt r) i)) j
                   ; (r = i0) → ll-fill₂ (pt B) (~ i) (~ j) k s
                   ; (r = i1) → lr-fill₂ (pt C) (~ i) (~ j) k s })
           (hcomp (λ s → λ {(i = i0) → filler₅ (~ j) k i1
                   ; (i = i1) → push (inr (push (push tt r) s)) (j ∨ ~ k)
                   ; (j = i0) → push (inr (push (push tt r) s)) (i ∧ ~ k)
                   ; (j = i1) → filler₈ (pt A) (~ i) k r s
                   ; (k = i0) → coh-filler₂ r (~ j) (~ i) s
                   ; (k = i1) → push (inr (push (push tt r) (i ∧ s))) j
                   ; (r = i0) → ll-fill₁ (pt B) (~ i) (~ j) k s
                   ; (r = i1) → lr-fill₁ (pt C) (~ i) (~ j) k s})
                  (hcomp (λ s → λ {(i = i0) → filler₅ (~ j) k i1
                   ; (i = i1) → push (inr (inl tt)) (j ∨ (s ∧ ~ k))
                   ; (j = i0) → push (inr (inl tt)) (i ∧ s ∧ ~ k)
                   ; (j = i1) → push (inl (snd A)) (i ∨ k)
                   ; (k = i0) → filler₅ (~ j) i (~ s)
                   ; (k = i1) → push (inr (inl tt)) j
                   ; (r = i0) → btm-fill (~ i) (~ j) k s
                   ; (r = i1) → btm-fill (~ i) (~ j) k s})
                     (filler₅ (~ j) (i ∨ k) i1)))
  ⋀→⋀×2→⋀ (push (push a i) j) k =
    hcomp (λ r → λ {(i = i0) → push (inl (pt A)) (k ∧ j ∨ ~ r)
                   ; (i = i1) → filler₅ (~ j) k r
                   ; (j = i0) → push (push tt i) (k ∧ ~ r)
                   ; (j = i1) → push (inl (snd A)) k
                   ; (k = i0) → inl tt
                   ; (k = i1) → push (push tt i) (j ∨ ~ r)})
          (push (push tt (~ j ∧ i)) k)

  -- The main result of step 1
  Iso-⋀-⋀×2 : Iso (A ⋀ (B ⋀∙ C)) ⋀×2
  Iso.fun Iso-⋀-⋀×2 = ⋀→⋀×2
  Iso.inv Iso-⋀-⋀×2 = ⋀×2→⋀
  Iso.rightInv Iso-⋀-⋀×2 = ⋀×2→⋀→⋀×2
  Iso.leftInv Iso-⋀-⋀×2 = ⋀→⋀×2→⋀

module _ {ℓ ℓ' ℓ'' : Level} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') where
  -- Step 2: show that ⋀×2 A B C ≃ ⋀×2 C A B

  -- some fillers
  permute-fill→ : (i j k r : I) → ⋀×2 C A B
  permute-fill→ i j k r =
    hfill (λ r → λ {(i = i0) → gluem≡gluer (snd B) (~ j ∨ ~ r) k
                   ; (i = i1) → gluel≡gluem (pt C) j k
                   ; (j = i0) → gluel≡gluer (pt A) (~ i) k
                   ; (j = i1) → gluem≡gluer (snd B) (~ i ∧ ~ r) k
                   ; (k = i0) → proj (pt C) (pt A) (snd B)
                   ; (k = i1) → base})
          (inS (coh j (~ i) k))
          r

  permute-fill← : (i j k r : I) → ⋀×2 A B C
  permute-fill← i j k r =
    hfill (λ r → λ {(i = i0) → gluel≡gluem (snd A) (~ j) k
                   ; (i = i1) → gluel≡gluer (pt B) (~ j ∨ ~ r) k
                   ; (j = i0) → gluem≡gluer (pt C) i k
                   ; (j = i1) → gluel≡gluer (pt B) (i ∧ ~ r) k
                   ; (k = i0) → proj (snd A) (pt B) (pt C)
                   ; (k = i1) → base})
          (inS (coh (~ j) i k))
          r

  ⋀×2-permuteFun : ⋀×2 A B C → ⋀×2 C A B
  ⋀×2-permuteFun base = base
  ⋀×2-permuteFun (proj x x₁ x₂) = proj x₂ x x₁
  ⋀×2-permuteFun (gluel x y i) = gluer x y i
  ⋀×2-permuteFun (gluem x z i) = gluel z x i
  ⋀×2-permuteFun (gluer y z i) = gluem z y i
  ⋀×2-permuteFun (gluel≡gluem a i j) = gluel≡gluer a (~ i) j
  ⋀×2-permuteFun (gluel≡gluer y i j) = gluem≡gluer y (~ i) j
  ⋀×2-permuteFun (gluem≡gluer z i j) = gluel≡gluem z i j
  ⋀×2-permuteFun (coh i j k) =
    hcomp (λ r → λ {(i = i0) → gluem≡gluer (snd B) (~ j ∨ ~ r) k
                   ; (i = i1) → gluel≡gluem (pt C) j k
                   ; (j = i0) → gluel≡gluer (pt A) (~ i) k
                   ; (j = i1) → gluem≡gluer (snd B) (~ i ∧ ~ r) k
                   ; (k = i0) → proj (pt C) (pt A) (snd B)
                   ; (k = i1) → base})
          (coh j (~ i) k)

  ⋀×2-permuteInv : ⋀×2 C A B → ⋀×2 A B C
  ⋀×2-permuteInv base = base
  ⋀×2-permuteInv (proj x x₁ x₂) = proj x₁ x₂ x
  ⋀×2-permuteInv (gluel x y i) = gluem y x i
  ⋀×2-permuteInv (gluem x z i) = gluer z x i
  ⋀×2-permuteInv (gluer y z i) = gluel y z i
  ⋀×2-permuteInv (gluel≡gluem a i j) = gluem≡gluer a i j
  ⋀×2-permuteInv (gluel≡gluer y i j) = gluel≡gluem y (~ i) j
  ⋀×2-permuteInv (gluem≡gluer z i j) = gluel≡gluer z (~ i) j
  ⋀×2-permuteInv (coh i j k) = permute-fill← i j k i1

  ⋀×2-permuteIso : Iso (⋀×2 A B C) (⋀×2 C A B)
  Iso.fun ⋀×2-permuteIso = ⋀×2-permuteFun
  Iso.inv ⋀×2-permuteIso = ⋀×2-permuteInv
  Iso.rightInv ⋀×2-permuteIso base = refl
  Iso.rightInv ⋀×2-permuteIso (proj x x₁ x₂) = refl
  Iso.rightInv ⋀×2-permuteIso (gluel x y i) = refl
  Iso.rightInv ⋀×2-permuteIso (gluem x z i) = refl
  Iso.rightInv ⋀×2-permuteIso (gluer y z i) = refl
  Iso.rightInv ⋀×2-permuteIso (gluel≡gluem a i i₁) = refl
  Iso.rightInv ⋀×2-permuteIso (gluel≡gluer y x x₁) = refl
  Iso.rightInv ⋀×2-permuteIso (gluem≡gluer z i i₁) = refl
  Iso.rightInv ⋀×2-permuteIso (coh i j k) r =
    hcomp (λ l → λ { (i = i0) → gluel≡gluer (snd A) j k
                    ; (i = i1) → gluem≡gluer (snd B) (j ∧ (r ∨ l)) k
                    ; (j = i0) → gluel≡gluem (snd C) i k
                    ; (j = i1) → gluem≡gluer (snd B) (~ i ∨ (l ∨ r)) k
                    ; (k = i0) → proj (snd C) (snd A) (snd B)
                    ; (k = i1) → base
                    ; (r = i0) → ⋀×2-permuteFun (permute-fill← i j k l)
                    ; (r = i1) → coh i j k})
     (hcomp (λ l → λ { (i = i0) → gluel≡gluer (snd A) j k
                    ; (i = i1) → gluem≡gluer (snd B) (j ∧ (~ l ∨ r)) k
                    ; (j = i0) → gluel≡gluem (snd C) i k
                    ; (j = i1) → gluem≡gluer (snd B) (~ i ∨ (~ l ∨ r)) k
                    ; (k = i0) → proj (snd C) (snd A) (snd B)
                    ; (k = i1) → base
                    ; (r = i0) → permute-fill→ (~ j) i k l
                    ; (r = i1) → coh i j k})
           (coh i j k))
  Iso.leftInv ⋀×2-permuteIso base = refl
  Iso.leftInv ⋀×2-permuteIso (proj x x₁ x₂) = refl
  Iso.leftInv ⋀×2-permuteIso (gluel x y i) = refl
  Iso.leftInv ⋀×2-permuteIso (gluem x z i) = refl
  Iso.leftInv ⋀×2-permuteIso (gluer y z i) = refl
  Iso.leftInv ⋀×2-permuteIso (gluel≡gluem a i i₁) = refl
  Iso.leftInv ⋀×2-permuteIso (gluel≡gluer y x x₁) = refl
  Iso.leftInv ⋀×2-permuteIso (gluem≡gluer z i i₁) = refl
  Iso.leftInv ⋀×2-permuteIso (coh i j k) r =
    hcomp (λ l → λ { (i = i0) → gluel≡gluer (snd B) (j ∧ (l ∨ r)) k
                    ; (i = i1) → gluem≡gluer (snd C) j k
                    ; (j = i0) → gluel≡gluem (snd A) i k
                    ; (j = i1) → gluel≡gluer (snd B) (i ∨ (l ∨ r)) k
                    ; (k = i0) → proj (pt A) (pt B) (pt C)
                    ; (k = i1) → base
                    ; (r = i0) → ⋀×2-permuteInv (permute-fill→ i j k l)
                    ; (r = i1) → coh i j k})
     (hcomp (λ l → λ { (i = i0) → gluel≡gluer (snd B) (j ∧ (~ l ∨ r)) k
                    ; (i = i1) → gluem≡gluer (snd C) j k
                    ; (j = i0) → gluel≡gluem (snd A) i k
                    ; (j = i1) → gluel≡gluer (snd B) (i ∨ (~ l ∨ r)) k
                    ; (k = i0) → proj (pt A) (pt B) (pt C)
                    ; (k = i1) → base
                    ; (r = i0) → permute-fill← j (~ i) k l
                    ; (r = i1) → coh i j k})
            (coh i j k))

-- Step 3: Combine the previous steps with commutativity of ⋀, and we are done
SmashAssocIso : Iso (A ⋀ (B ⋀∙ C)) ((A ⋀∙ B) ⋀ C)
SmashAssocIso {A = A} {B = B} {C = C} =
  compIso
    (Iso-⋀-⋀×2 A B C)
    (compIso
      (⋀×2-permuteIso A B C)
      (compIso
        (invIso (Iso-⋀-⋀×2 C A B))
        ⋀CommIso))

SmashAssocEquiv∙ : A ⋀∙ (B ⋀∙ C) ≃∙ (A ⋀∙ B) ⋀∙ C
fst SmashAssocEquiv∙ = isoToEquiv SmashAssocIso
snd SmashAssocEquiv∙ = refl

module _ {C : Type ℓ} (f g : A ⋀ B → C)
  (bp : f (inl tt) ≡ g (inl tt))
  (proj : (x : _) → f (inr x) ≡ g (inr x))
  (pl : (x : typ A) → PathP (λ i → f (push (inl x) i) ≡ g (push (inl x) i))
                             bp (proj (x , pt B)))
  (p-r : (x : typ B) → PathP (λ i → f (push (inr x) i) ≡ g (push (inr x) i))
                             bp (proj (pt A , x)))
  where
  private
    ⋆act : bp ≡ bp
    ⋆act i j =
      hcomp (λ k → λ { (i = i0) → pl (pt A) (~ k) j
                      ; (i = i1) → p-r (pt B) (~ k) j
                      ; (j = i0) → f (push (push tt i) (~ k))
                      ; (j = i1) → g (push (push tt i) (~ k))})
            (proj (snd A , snd B) j)

  ⋀-fun≡ : (x : _) → f x ≡ g x
  ⋀-fun≡ (inl x) = bp
  ⋀-fun≡ (inr x) = proj x
  ⋀-fun≡ (push (inl x) i) = pl x i
  ⋀-fun≡ (push (inr x) i) j =
    hcomp (λ r → λ {(i = i0) → bp j
                   ; (i = i1) → p-r x r j
                   ; (j = i0) → f (push (inr x) (r ∧ i))
                   ; (j = i1) → g (push (inr x) (r ∧ i)) })
          (⋆act i j)
  ⋀-fun≡ (push (push a i) j) k =
    hcomp (λ r → λ { (i = i0) → pl (snd A) (j ∧ r) k
                    ; (j = i0) → bp k
                    ; (j = i1) → side i k r
                    ; (k = i0) → f (push (push a i) (j ∧ r))
                    ; (k = i1) → g (push (push a i) (j ∧ r))})
          (⋆act (i ∧ j) k)
    where
    side : Cube (λ k r → pl (snd A) r k)
              (λ k r → p-r (snd B) r k)
              (λ i r → f (push (push a i) r))
              (λ i r → g (push (push a i) r))
              ⋆act λ i → proj (snd A , snd B)
    side i k r =
      hcomp (λ j → λ { (i = i0) → pl (pt A) (~ j ∨ r) k
                      ; (i = i1) → p-r (snd B) (~ j ∨ r) k
                      ; (k = i0) → f (push (push a i) (~ j ∨ r))
                      ; (k = i1) → g (push (push a i) (~ j ∨ r))
                      ; (r = i1) → proj (snd A , snd B) k})
                (proj (snd A , snd B) k)

-- Techincal lemma allowing for use of ⋀→∙Homogeneous≡ on
-- when proving equalities of functions A ⋀ B → C
module ⋀-fun≡' {C : Type ℓ} (f g : A ⋀ B → C)
         (pr : (x : _) → f (inr x) ≡ g (inr x)) where

  p : f (inl tt) ≡ g (inl tt)
  p = cong f (push (inr (pt B)))
    ∙∙ pr (pt A , pt B)
    ∙∙ sym (cong g (push (inr (pt B))))


  p' : f (inl tt) ≡ g (inl tt)
  p' = cong f (push (inl (pt A)))
    ∙∙ pr (pt A , pt B)
    ∙∙ sym (cong g (push (inl (pt A))))

  p≡p' : p ≡ p'
  p≡p' i = (cong f (push (push tt (~ i))))
        ∙∙ pr (pt A , pt B)
        ∙∙ sym (cong g (push (push tt (~ i))))

  Fₗ : B →∙ ((f (inl tt) ≡ g (inl tt)) , p)
  fst Fₗ b = cong f (push (inr b)) ∙∙ pr (pt A , b) ∙∙ sym (cong g (push (inr b)))
  snd Fₗ = refl

  Fᵣ : B →∙ ((f (inl tt) ≡ g (inl tt)) , p)
  fst Fᵣ b = p
  snd Fᵣ = refl

  module _
    (lp : (x : fst A) → PathP (λ i → f (push (inl x) i) ≡ g (push (inl x) i))
                                      p (pr (x , pt B)))
    (q : Fₗ ≡ Fᵣ) where
    private
      lem : (b : fst B)
       → Square p (pr (snd A , b))
                 (cong f (push (inr b))) (cong g (push (inr b)))
      lem b i j =
        hcomp (λ k → λ {(i = i0) → p j
                       ; (i = i1) → doubleCompPath-filler
                                      (cong f (push (inr b)))
                                      (pr (pt A , b))
                                      (sym (cong g (push (inr b)))) (~ k) j
                       ; (j = i0) → f (push (inr b) (i ∧ k))
                       ; (j = i1) → g (push (inr b) (i ∧ k))})
              (q (~ i) .fst b j)

    main : (x : _) → f x ≡ g x
    main = ⋀-fun≡ {A = A} {B = B} f g p pr lp lem
