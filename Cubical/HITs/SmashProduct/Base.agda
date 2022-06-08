{-# OPTIONS --safe #-}
module Cubical.HITs.SmashProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Pushout.Base
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.Wedge
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

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

-- WIP below

SmashPt : (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
SmashPt A B = (Smash A B , basel)

SmashPtProj : (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
SmashPtProj A B = Smash A B , (proj (snd A) (snd B))

--- Alternative definition

i∧ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → A ⋁ B → (typ A) × (typ B)
i∧ {A = A , ptA} {B = B , ptB} (inl x) = x , ptB
i∧ {A = A , ptA} {B = B , ptB} (inr x) = ptA , x
i∧ {A = A , ptA} {B = B , ptB} (push tt i) = ptA , ptB

_⋀_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Type (ℓ-max ℓ ℓ')
A ⋀ B = Pushout {A = (A ⋁ B)} (λ _ → tt) i∧

⋀comm→ : A ⋀ B → B ⋀ A
⋀comm→ (inl x) = inl x
⋀comm→ (inr (x , y)) = inr (y , x)
⋀comm→ (push (inl x) i) = push (inr x) i
⋀comm→ (push (inr x) i) = push (inl x) i
⋀comm→ (push (push a i₁) i) = push (push tt (~ i₁)) i

⋀comm→² : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ' } (x : A ⋀ B) → ⋀comm→ (⋀comm→ {A = A} {B = B} x) ≡ x
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

_·×_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
fst (A ·× B) = fst A × fst B
snd (A ·× B) = pt A , pt B


_⋀∙_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
A ⋀∙ B = Pushout {A = (A ⋁ B)} (λ _ → tt) i∧ , (inl tt)


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

-- _≃∙_
{-
open import Cubical.Foundations.Equiv

⋀∙Equiv : (f : A ≃∙ C) (g : B ≃∙ D) → A ⋀∙ B ≃∙ C ⋀∙ D
fst (⋀∙Equiv {A = A}  {C = C} {B = B}{D = D} f g) = isoToEquiv help
  where
  m1 : (A ⋀ B) → (C ⋀ D)
  m1 = {!!}

  sect-lem : {!!}
  sect-lem = {!!}

  help : Iso (A ⋀ B) (C ⋀ D)
  Iso.fun help = (≃∙map f) ⋀→ (≃∙map g)
  Iso.inv help = (≃∙map (invEquiv∙ f)) ⋀→ (≃∙map (invEquiv∙ g))
  Iso.rightInv help = {!Equiv∙J!}
  Iso.leftInv help = {!!}
snd (⋀∙Equiv f g) = refl
-}


⋀→Smash : A ⋀ B → Smash A B
⋀→Smash (inl x) = basel
⋀→Smash (inr (x , x₁)) = proj x x₁
⋀→Smash (push (inl x) i) = gluel x (~ i)
⋀→Smash {A = A} {B = B} (push (inr x) i) = (sym (gluel (snd A)) ∙∙ gluer (snd B) ∙∙ sym (gluer x)) i
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

module _ {ℓ ℓ' ℓ'' : Level} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') where
  data smot : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    bs : smot
    proj : typ A → typ B → typ C → smot
    gluel : (x : typ A) (y : typ B) → proj x y (pt C) ≡ bs
    gluem : (x : typ A) (z : typ C) → proj x (pt B) z ≡ bs
    gluer : (y : typ B) (z : typ C) → proj (pt A) y z ≡ bs

    gluel≡gluem : (a : typ A) → gluel a (pt B) ≡ gluem a (pt C)
    gluel≡gluer : (y : typ B) → Path (Path (smot) _ _) (gluel (pt A) y) (gluer y (pt C))
    gluem≡gluer : (z : typ C) → gluem (pt A) z ≡ gluer (pt B) z

    coh : Cube (gluel≡gluer (snd B)) (gluem≡gluer (pt C))
               (gluel≡gluem (pt A)) (λ _ → gluer (snd B) (pt C))
               refl refl


  fill1 : typ B → (i j k : I) → smot
  fill1 a i j r =
    hfill (λ k → λ {(i = i0) → gluer a (pt C) (j ∧ k)
                   ; (i = i1) → bs
                   ; (j = i0) → gluel (pt A) a i
                   ; (j = i1) → gluer a (pt C) (i ∨ k)})
       (inS (gluel≡gluer a j i))
       r

  fill2 : typ C → (i j k : I) → smot
  fill2 c i j r =
    hfill (λ k → λ {(i = i0) → gluer (pt B) c (j ∧ k)
                    ; (i = i1) → bs
                    ; (j = i0) → gluem (pt A) c i
                    ; (j = i1) → gluer (pt B) c (i ∨ k)})
        (inS (gluem≡gluer c j i))
        r

  fill3 : typ B → (i j r : I) → A ⋀ (B ⋀∙ C)
  fill3 b i j r = 
    hfill (λ k → λ {(i = i0) → (compPath-filler' (λ j → inr (pt A , (push (inl b) (~ j))))
                                                  (sym (push (inl (pt A))))) k j
                   ; (i = i1) → push (inr (push (inl b) k)) (~ j)
                   ; (j = i0) → inr (pt A , push (inl b) k)
                   ; (j = i1) → inl tt})
           (inS (push (push tt i) (~ j)))
           r

  fill4 : typ C → (i j r : I) → A ⋀ (B ⋀∙ C)
  fill4 c i j r = 
    hfill (λ k → λ {(i = i0) → (compPath-filler' (λ j → inr (pt A , (push (inr c) (~ j))))
                                                  (sym (push (inl (pt A))))) k j
                   ; (i = i1) → push (inr (push (inr c) k)) (~ j)
                   ; (j = i0) → inr (pt A , push (inr c) k)
                   ; (j = i1) → inl tt})
           (inS (push (push tt i) (~ j)))
           r

  fill4' : (i j r k : I) → A ⋀ (B ⋀∙ C)
  fill4' i j r k =
    hfill (λ k → λ {(i = i0) → (compPath-filler' (λ j → inr (pt A , (push (push tt r) (~ j))))
                                                  (sym (push (inl (pt A))))) k j
                   ; (i = i1) → push (inr (push (push tt r) k)) (~ j)
                   ; (j = i0) → inr (pt A , push (push tt r) k)
                   ; (j = i1) → inl tt})
           ((inS (push (push tt i) (~ j))))
           k

  fill5 : (i j k : I) → A ⋀ (B ⋀∙ C)
  fill5 i j r =
    hfill (λ k → λ {(i = i0) → push (inl (pt A)) j
                   ; (i = i1) → push (inr (inl tt)) (j ∧ ~ k)
                   ; (j = i0) → inl tt
                   ; (j = i1) → push (inr (inl tt)) (~ i ∨ ~ k)})
          (inS (push (push tt i) j))
          r

  r-high : (i j k r : I) → smot
  r-high i j k r =
    hfill (λ r → λ {(i = i0) → fill1 (pt B) j k r
                   ; (i = i1) → fill2 (pt C) j k r
                   ; (j = i0) → gluer (snd B) (snd C) (k ∧ r)
                   ; (j = i1) → bs
                   ; (k = i0) → gluel≡gluem (pt A) i j
                   ; (k = i1) → gluer (snd B) (snd C) (j ∨ r)})
          (inS (coh i k j))
          r


  sm→smot : A ⋀ (B ⋀∙ C) → smot
  sm→smot (inl x) = bs
  sm→smot (inr (x , inl y)) = bs
  sm→smot (inr (x , inr (y , z))) = proj x y z
  sm→smot (inr (x , push (inl a) i)) = gluel x a (~ i)
  sm→smot (inr (x , push (inr b) i)) = gluem x b (~ i)
  sm→smot (inr (x , push (push a i) j)) = gluel≡gluem x i (~ j)
  sm→smot (push (inl x) i) = bs
  sm→smot (push (inr (inl x)) i) = bs
  sm→smot (push (inr (inr (x , y))) i) = gluer x y (~ i)
  sm→smot (push (inr (push (inl x) i)) j) = fill1 x (~ i) (~ j) i1
  sm→smot (push (inr (push (inr x) i)) j) = fill2 x (~ i) (~ j) i1
  sm→smot (push (inr (push (push a i) j)) k) = r-high i (~ j) (~ k) i1
  sm→smot (push (push a i₁) i) = bs

  coh-case : (i j k r : I) → A ⋀ (B ⋀∙ C)
  coh-case i j k r =
    hfill (λ r → λ {(i = i0) → fill3 (snd B) j k r
                   ; (i = i1) → fill4 (pt C) j k r
                   ; (j = i0) → compPath-filler'
                                  (λ k₁ → inr (pt A , push (push tt i) (~ k₁)))
                                  (sym (push (inl (pt A)))) r k
                   ; (j = i1) → push (inr (push (push tt i) r)) (~ k)
                   ; (k = i0) → inr (pt A , push (push tt i) r)
                   ; (k = i1) → inl tt})
          (inS (push (push tt j) (~ k)))
          r

  smot→sm : smot → A ⋀ (B ⋀∙ C)
  smot→sm bs = inl tt
  smot→sm (proj x x₁ x₂) = inr (x , inr (x₁ , x₂))
  smot→sm (gluel x y i) = ((λ i → inr (x , (push (inl y) (~ i)))) ∙ sym (push (inl x))) i
  smot→sm (gluem x z i) = ((λ i → inr (x , (push (inr z) (~ i)))) ∙ sym (push (inl x))) i
  smot→sm (gluer y z i) = push (inr (inr (y , z))) (~ i)
  smot→sm (gluel≡gluem a i j) = ((λ k → inr (a , (push (push tt i) (~ k)))) ∙ sym (push (inl a))) j
  smot→sm (gluel≡gluer b i j) = fill3 b i j i1
  smot→sm (gluem≡gluer c i j) = fill4 c i j i1
  smot→sm (coh i j k) = coh-case i j k i1

  gluel-fill : (x : typ A) (b : typ B) (i j k : I) → smot
  gluel-fill x y i j k =
    hfill (λ k → λ {(i = i0) → gluel x y (~ k)
                   ; (i = i1) → bs
                   ; (j = i0) →
                      sm→smot (compPath-filler'
                        (λ i → (inr (x , (push (inl y) (~ i))))) (sym (push (inl x))) k i)
                   ; (j = i1) → gluel x y (i ∨ ~ k) })
          (inS bs)
          k

  gluem-fill : (x : typ A) (z : typ C) (i j k : I) → smot
  gluem-fill x z i j k =
    hfill (λ k → λ {(i = i0) → gluem x z (~ k)
                   ; (i = i1) → bs
                   ; (j = i0) → sm→smot (compPath-filler'
                                  (λ i → (inr (x , (push (inr z) (~ i))))) (sym (push (inl x))) k i)
                   ; (j = i1) → gluem x z (i ∨ ~ k)})
          (inS bs)
          k

  gluel≡gluer₁ : (y : typ B) (i j r k : I) → smot
  gluel≡gluer₁ y i j r k =
    hfill (λ k → λ {(r = i0) → bs
                     ; (r = i1) → gluer y (snd C) (i ∧ k)
                     ; (i = i0) → gluel≡gluer y j (~ r)
                     ; (i = i1) → gluer y (snd C) (~ r ∨ k)
                     ; (j = i0) → fill1 y (~ r) i k
                     ; (j = i1) → gluer y (snd C) ((i ∧ k) ∨ ~ r)})
            (inS (gluel≡gluer y (j ∨ i) (~ r)))
           k


  gluem≡gluer₁ : (y : typ C) (i j r k : I) → smot
  gluem≡gluer₁ z i j r k = 
    hfill (λ k → λ {(i = i0) → gluem≡gluer z j (~ r)
                   ; (i = i1) → gluer (snd B) z (~ r ∨ k)
                   ; (j = i0) → fill2 z (~ r) i k
                   ; (j = i1) → gluer (snd B) z (~ r ∨ (k ∧ i))
                   ; (r = i0) → bs
                   ; (r = i1) → gluer (snd B) z (i ∧ k)})
              (inS (gluem≡gluer z (j ∨ i) (~ r)))
              k

  gluel≡gluer₂ : (y : typ B) (k i j r : I) → smot
  gluel≡gluer₂ y k i j r =
    hfill (λ r → λ {(i = i0) → gluel≡gluer y (k ∧ j) (~ r)
                   ; (i = i1) → bs
                   ; (j = i0) → sm→smot (fill3 y k i r)
                   ; (j = i1) → gluel≡gluer y k (i ∨ ~ r)
                   ; (k = i0) → gluel-fill (pt A) y i j r
                   ; (k = i1) → gluel≡gluer₁ y i j r i1})
           (inS bs)
           r

  gluem≡gluer₂ : (y : typ C) (k i j r : I) → smot
  gluem≡gluer₂ y k i j r =
    hfill (λ r → λ {(i = i0) → gluem≡gluer y (k ∧ j) (~ r)
                   ; (i = i1) → bs
                   ; (j = i0) → sm→smot (fill4 y k i r)
                   ; (j = i1) → gluem≡gluer y k (i ∨ ~ r) 
                   ; (k = i0) → gluem-fill (pt A) y i j r
                   ; (k = i1) → gluem≡gluer₁ y i j r i1})
           (inS bs)
           r

  gluel≡gluem-fill : (a : typ A) → (i j k r : I) → smot
  gluel≡gluem-fill a i j k r =
    hfill (λ r → λ {(i = i0) → gluel≡gluem a k (~ r)
                   ; (i = i1) → bs
                   ; (j = i0) → sm→smot (compPath-filler'
                      (λ i → inr (a , push (push tt k) (~ i))) (sym (push (inl a))) r i)
                   ; (j = i1) → gluel≡gluem a k (i ∨ ~ r)
                   ; (k = i0) → gluel-fill a (pt B) i j r
                   ; (k = i1) → gluem-fill a (pt C) i j r})
           (inS bs)
           r
  sm→smot'' : (x : smot) → sm→smot (smot→sm x) ≡ x
  sm→smot'' bs = refl
  sm→smot'' (proj x x₁ x₂) = refl
  sm→smot'' (gluel x y i) j = gluel-fill x y i j i1
  sm→smot'' (gluem x z i) j = gluem-fill x z i j i1
  sm→smot'' (gluer y z i) = refl
  sm→smot'' (gluel≡gluem a k i) j = gluel≡gluem-fill a i j k i1
  sm→smot'' (gluel≡gluer y k i) j = gluel≡gluer₂ y k i j i1
  sm→smot'' (gluem≡gluer z k i) j = gluem≡gluer₂ z k i j i1
  sm→smot'' (coh i j k) r =
    hcomp (λ l → λ {(i = i0) → gluel≡gluer₂ (snd B) j k r l
                   ; (i = i1) → gluem≡gluer₂ (pt C) j k r l
                   ; (j = i0) → gluel≡gluem-fill (pt A) k r i l
                   ; (j = i1) → help l i k r
                   ; (k = i0) → coh i (j ∧ r) (~ l)
                   ; (k = i1) → bs
                   ; (r = i0) → sm→smot (coh-case i j k l)
                   ; (r = i1) → coh i j (k ∨ ~ l)})
          bs
    where
    help : PathP
         (λ l → Cube (λ k r → gluel≡gluer₂ (snd B) i1 k r l)
                      (λ k r → gluem≡gluer₂ (pt C) i1 k r l)
                      (λ i r → coh i r (~ l))
                      (λ i r → bs)
                      (λ i k → r-high i (~ l) k i1)
                      λ i k → gluer (snd B) (snd C) (k ∨ ~ l))
                 (λ _ _ _ → bs)
                 λ i k r → gluer (snd B) (pt C) k
    help l i k r =    
      hcomp (λ j → λ {(i = i0) → gluel≡gluer₁ (pt B) k r l j
                      ; (i = i1) → gluem≡gluer₁ (pt C) k r l j
                      ; (l = i0) → bs
                      ; (l = i1) → gluer (snd B) (pt C) (k ∧ j)
                      ; (k = i0) → coh i r (~ l)
                      ; (k = i1) → gluem≡gluer₁ (pt C) k r l j
                      ; (r = i0) → r-high i (~ l) k j
                      ; (r = i1) → gluer (snd B) (snd C) (~ l ∨ (j ∧ k))})
        (hcomp (λ j → λ {(i = i0) → gluel≡gluer (snd B) (r ∨ k) (~ l)
                      ; (i = i1) → gluem≡gluer (snd C) (r ∨ k) (~ l)
                      ; (l = i0) → bs
                      ; (l = i1) → proj (pt A) (pt B) (snd C)
                      ; (k = i0) → coh i r (~ l)
                      ; (k = i1) → gluer (snd B) (snd C) (~ l)
                      ; (r = i0) → coh i k (~ l)
                      ; (r = i1) → gluer (snd B) (snd C) (~ l)})
               (coh i (r ∨ k) (~ l)))

  fill90 : (x : typ A) (a : typ B) → (i j k : I) → A ⋀ (B ⋀ C , inl tt)
  fill90 x a i j k = 
    hfill (λ k → λ {(i = i0) → inr (x , push (inl a) k)
                   ; (i = i1) → push (inl x) j
                   ; (j = i0) → compPath-filler' (λ i₁ → inr (x , (push (inl a) (~ i₁)))) (sym (push (inl x))) k i
                   ; (j = i1) → inr (x , push (inl a) (~ i ∧ k)) })
          (inS (push (inl x) (j ∨ ~ i)))
          k

  fill91 : (x : typ A) (a : typ C) → (i j k : I) → A ⋀ (B ⋀ C , inl tt)
  fill91 x a i j k =
    hfill (λ k → λ {(i = i0) → inr (x , push (inr a) k)
                   ; (i = i1) → push (inl x) j
                   ; (j = i0) → compPath-filler' (λ i₁ → inr (x , (push (inr a) (~ i₁)))) (sym (push (inl x))) k i
                   ; (j = i1) → inr (x , push (inr a) (~ i ∧ k)) })
          (inS (push (inl x) (j ∨ ~ i)))
          k

  fill92 : (x : typ A) → (i j k r : I) → A ⋀ (B ⋀ C , inl tt)
  fill92 x i j k r =
    hfill (λ r → λ {(i = i0) → inr (x , push (push tt k) r)
                   ; (i = i1) → push (inl x) j -- push (inl x) j
                   ; (j = i0) → compPath-filler' (λ j → inr (x , push (push tt k) (~ j))) (sym (push (inl x))) r i
                   ; (j = i1) → inr (x , push (push tt k) (~ i ∧ r)) })
          (inS ((push (inl x) (j ∨ ~ i))))
          r

  btm-fill : (i j k r : I) → A ⋀ (B ⋀∙ C)
  btm-fill i j k r =
    hfill (λ r → λ {(i = i0) → push (inr (inl tt)) (~ j ∨ (r ∧ ~ k))
                              ; (i = i1) → fill5 j k i1
                              ; (j = i1) → push (inr (inl tt)) (~ i ∧ (r ∧ ~ k))
                              ; (j = i0) → push (inl (pt A)) (~ i ∨ k)
                              ; (k = i0) → fill5 j (~ i) (~ r)
                              ; (k = i1) → push (inr (inl tt)) (~ j)})
                     (inS (fill5 j (~ i ∨ k) i1))
           r

  lr-fill₁ : (b : typ C) (i j k r : I) → A ⋀ (B ⋀∙ C)
  lr-fill₁ a i j k r =
    hfill (λ r → λ {(i = i0) → push (inr (push (inr a) r)) (~ j ∨ ~ k)
                   ; (i = i1) → fill5 j k i1
                   ; (j = i1) → push (inr (push (inr a) r)) (~ i ∧ ~ k)
                   ; (j = i0) → fill91 (pt A) a i k r
                   ; (k = i0) → fill4 a j i r
                   ; (k = i1) → push (inr (push (inr a) (~ i ∧ r))) (~ j)})
              (inS (btm-fill i j k i1))
             r

  ll-fill₁ : (a : typ B) (i j k r : I) →  A ⋀ (B ⋀∙ C)
  ll-fill₁ a i j k r =
    hfill (λ r → λ {(i = i0) → push (inr (push (inl a) r)) (~ j ∨ ~ k)
                   ; (i = i1) → fill5 j k i1
                   ; (j = i1) → push (inr (push (inl a) r)) (~ i ∧ ~ k)
                   ; (j = i0) → fill90 (pt A) a i k r
                   ; (k = i0) → fill3 a j i r
                   ; (k = i1) → push (inr (push (inl a) (~ i ∧ r))) (~ j)})
             (inS (btm-fill i j k i1))
             r

  ll-fill₂ : (a : typ B) (i j k r : I) → A ⋀ (B ⋀∙ C)
  ll-fill₂ a i j k r =
    hfill (λ r → λ {(i = i0) → push (inr (inr (a , pt C))) (~ j ∨ (~ r ∧ ~ k))
                   ; (i = i1) → fill5 j k i1
                   ; (j = i1) → push (inr (inr (a , (snd C)))) ((~ r ∧ ~ i) ∧ ~ k)
                   ; (j = i0) → fill90 (pt A) a i k i1
                   ; (k = i0) → smot→sm (fill1 a i j r)
                   ; (k = i1) → push (inr (push (inl a) (~ i))) (~ j) })
      (inS (ll-fill₁ a i j k i1))
      r

  lr-fill₂ : (a : typ C) (i j k r : I) → A ⋀ (B ⋀∙ C)
  lr-fill₂ a i j k r =
    hfill (λ r → λ {(i = i0) → push (inr (inr (pt B , a))) (~ j ∨ (~ r ∧ ~ k))
                   ; (i = i1) → fill5 j k i1
                   ; (j = i1) → push (inr (inr (pt B , a))) ((~ r ∧ ~ i) ∧ ~ k)
                   ; (j = i0) → fill91 (pt A) a i k i1
                   ; (k = i0) → smot→sm (fill2 a i j r)
                   ; (k = i1) → push (inr (push (inr a) (~ i))) (~ j) })
      (inS (lr-fill₁ a i j k i1))
      r


  sm→smot' : (x : A ⋀ (B ⋀∙ C))
    → smot→sm (sm→smot x) ≡ x
  sm→smot' (inl x) = refl
  sm→smot' (inr (x , inl x₁)) = push (inl x)
  sm→smot' (inr (x , inr x₁)) = refl
  sm→smot' (inr (x , push (inl a) i)) j = fill90 x a (~ i) j i1
  sm→smot' (inr (x , push (inr b) i)) j = fill91 x b (~ i) j i1
  sm→smot' (inr (x , push (push a r) i)) j = fill92 x (~ i) j r i1
  sm→smot' (push (inl x) i) j = push (inl x) (j ∧ i)
  sm→smot' (push (inr (inl x)) i) j = fill5 (~ i) j i1
  sm→smot' (push (inr (inr x)) i) j = push (inr (inr x)) i
  sm→smot' (push (inr (push (inl x) i)) j) k = ll-fill₂ x (~ i) (~ j) k i1
  sm→smot' (push (inr (push (inr x) i)) j) k = lr-fill₂ x (~ i) (~ j) k i1
  sm→smot' (push (inr (push (push a r) i)) j) k =
    hcomp (λ s → λ {(i = i0) → fill5 (~ j) k i1
                   ; (i = i1) → push (inr (inr (snd B , snd C))) (j ∨ ~ s ∧ ~ k)
                   ; (j = i0) → push (inr (inr (pt B , pt C))) ((~ s ∧ i) ∧ ~ k)
                   ; (j = i1) → fill92 (pt A) (~ i) k r i1
                   ; (k = i0) → smot→sm (r-high r (~ i) (~ j) s)
                   ; (k = i1) → push (inr (push (push tt r) i)) j
                   ; (r = i0) → ll-fill₂ (pt B) (~ i) (~ j) k s
                   ; (r = i1) → lr-fill₂ (pt C) (~ i) (~ j) k s })
           (hcomp (λ s → λ {(i = i0) → fill5 (~ j) k i1
                   ; (i = i1) → push (inr (push (push tt r) s)) (j ∨ ~ k)
                   ; (j = i0) → push (inr (push (push tt r) s)) (i ∧ ~ k)
                   ; (j = i1) → fill92 (pt A) (~ i) k r s
                   ; (k = i0) → coh-case r (~ j) (~ i) s
                   ; (k = i1) → push (inr (push (push tt r) (i ∧ s))) j
                   ; (r = i0) → ll-fill₁ (pt B) (~ i) (~ j) k s
                   ; (r = i1) → lr-fill₁ (pt C) (~ i) (~ j) k s})
                  (hcomp (λ s → λ {(i = i0) → fill5 (~ j) k i1
                   ; (i = i1) → push (inr (inl tt)) (j ∨ (s ∧ ~ k))
                   ; (j = i0) → push (inr (inl tt)) (i ∧ s ∧ ~ k)
                   ; (j = i1) → push (inl (snd A)) (i ∨ k)
                   ; (k = i0) → fill5 (~ j) i (~ s)
                   ; (k = i1) → push (inr (inl tt)) j
                   ; (r = i0) → btm-fill (~ i) (~ j) k s
                   ; (r = i1) → btm-fill (~ i) (~ j) k s})
                     (fill5 (~ j) (i ∨ k) i1))) 
  sm→smot' (push (push a i) j) k =
    hcomp (λ r → λ {(i = i0) → push (inl (pt A)) (k ∧ j ∨ ~ r)
                   ; (i = i1) → fill5 (~ j) k r
                   ; (j = i0) → push (push tt i) (k ∧ ~ r)
                   ; (j = i1) → push (inl (snd A)) k
                   ; (k = i0) → inl tt
                   ; (k = i1) → push (push tt i) (j ∨ ~ r)})
          (push (push tt (~ j ∧ i)) k)

  Iso₁ : Iso (A ⋀ (B ⋀∙ C)) (smot)
  Iso.fun Iso₁ = sm→smot
  Iso.inv Iso₁ = smot→sm
  Iso.rightInv Iso₁ = sm→smot''
  Iso.leftInv Iso₁ = sm→smot'

module _ {ℓ ℓ' ℓ'' : Level} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') where
  comm-fill→ : (i j k r : I) → smot C A B
  comm-fill→ i j k r =
    hfill (λ r → λ {(i = i0) → gluem≡gluer (snd B) (~ j ∨ ~ r) k
                   ; (i = i1) → gluel≡gluem (pt C) j k
                   ; (j = i0) → gluel≡gluer (pt A) (~ i) k
                   ; (j = i1) → gluem≡gluer (snd B) (~ i ∧ ~ r) k
                   ; (k = i0) → proj (pt C) (pt A) (snd B)
                   ; (k = i1) → bs})
          (inS (coh j (~ i) k))
          r

  comm-fill← : (i j k r : I) → smot A B C
  comm-fill← i j k r =
    hfill (λ r → λ {(i = i0) → gluel≡gluem (snd A) (~ j) k
                   ; (i = i1) → gluel≡gluer (pt B) (~ j ∨ ~ r) k
                   ; (j = i0) → gluem≡gluer (pt C) i k
                   ; (j = i1) → gluel≡gluer (pt B) (i ∧ ~ r) k
                   ; (k = i0) → proj (snd A) (pt B) (pt C)
                   ; (k = i1) → bs})
          (inS (coh (~ j) i k))
          r

  smot-comm-fun : smot A B C → smot C A B
  smot-comm-fun bs = bs
  smot-comm-fun (proj x x₁ x₂) = proj x₂ x x₁
  smot-comm-fun (gluel x y i) = gluer x y i
  smot-comm-fun (gluem x z i) = gluel z x i
  smot-comm-fun (gluer y z i) = gluem z y i
  smot-comm-fun (gluel≡gluem a i j) = gluel≡gluer a (~ i) j
  smot-comm-fun (gluel≡gluer y i j) = gluem≡gluer y (~ i) j
  smot-comm-fun (gluem≡gluer z i j) = gluel≡gluem z i j
  smot-comm-fun (coh i j k) =
    hcomp (λ r → λ {(i = i0) → gluem≡gluer (snd B) (~ j ∨ ~ r) k
                   ; (i = i1) → gluel≡gluem (pt C) j k
                   ; (j = i0) → gluel≡gluer (pt A) (~ i) k
                   ; (j = i1) → gluem≡gluer (snd B) (~ i ∧ ~ r) k
                   ; (k = i0) → proj (pt C) (pt A) (snd B)
                   ; (k = i1) → bs})
          (coh j (~ i) k)

  smot-comm-inv : smot C A B → smot A B C
  smot-comm-inv bs = bs
  smot-comm-inv (proj x x₁ x₂) = proj x₁ x₂ x
  smot-comm-inv (gluel x y i) = gluem y x i
  smot-comm-inv (gluem x z i) = gluer z x i
  smot-comm-inv (gluer y z i) = gluel y z i
  smot-comm-inv (gluel≡gluem a i j) = gluem≡gluer a i j
  smot-comm-inv (gluel≡gluer y i j) = gluel≡gluem y (~ i) j
  smot-comm-inv (gluem≡gluer z i j) = gluel≡gluer z (~ i) j
  smot-comm-inv (coh i j k) = comm-fill← i j k i1
 
  cool2 : Iso (smot A B C) (smot C A B)
  Iso.fun cool2 = smot-comm-fun
  Iso.inv cool2 = smot-comm-inv
  Iso.rightInv cool2 bs = refl
  Iso.rightInv cool2 (proj x x₁ x₂) = refl
  Iso.rightInv cool2 (gluel x y i) = refl
  Iso.rightInv cool2 (gluem x z i) = refl
  Iso.rightInv cool2 (gluer y z i) = refl
  Iso.rightInv cool2 (gluel≡gluem a i i₁) = refl
  Iso.rightInv cool2 (gluel≡gluer y x x₁) = refl
  Iso.rightInv cool2 (gluem≡gluer z i i₁) = refl
  Iso.rightInv cool2 (coh i j k) r =
    hcomp (λ l → λ { (i = i0) → gluel≡gluer (snd A) j k
                    ; (i = i1) → gluem≡gluer (snd B) (j ∧ (r ∨ l)) k
                    ; (j = i0) → gluel≡gluem (snd C) i k
                    ; (j = i1) → gluem≡gluer (snd B) (~ i ∨ (l ∨ r)) k
                    ; (k = i0) → proj (snd C) (snd A) (snd B)
                    ; (k = i1) → bs
                    ; (r = i0) → smot-comm-fun (comm-fill← i j k l)
                    ; (r = i1) → coh i j k})
     (hcomp (λ l → λ { (i = i0) → gluel≡gluer (snd A) j k
                    ; (i = i1) → gluem≡gluer (snd B) (j ∧ (~ l ∨ r)) k
                    ; (j = i0) → gluel≡gluem (snd C) i k
                    ; (j = i1) → gluem≡gluer (snd B) (~ i ∨ (~ l ∨ r)) k
                    ; (k = i0) → proj (snd C) (snd A) (snd B)
                    ; (k = i1) → bs
                    ; (r = i0) → comm-fill→ (~ j) i k l
                    ; (r = i1) → coh i j k})
           (coh i j k))
  Iso.leftInv cool2 bs = refl
  Iso.leftInv cool2 (proj x x₁ x₂) = refl
  Iso.leftInv cool2 (gluel x y i) = refl
  Iso.leftInv cool2 (gluem x z i) = refl
  Iso.leftInv cool2 (gluer y z i) = refl
  Iso.leftInv cool2 (gluel≡gluem a i i₁) = refl
  Iso.leftInv cool2 (gluel≡gluer y x x₁) = refl
  Iso.leftInv cool2 (gluem≡gluer z i i₁) = refl
  Iso.leftInv cool2 (coh i j k) r =
    hcomp (λ l → λ { (i = i0) → gluel≡gluer (snd B) (j ∧ (l ∨ r)) k
                    ; (i = i1) → gluem≡gluer (snd C) j k
                    ; (j = i0) → gluel≡gluem (snd A) i k
                    ; (j = i1) → gluel≡gluer (snd B) (i ∨ (l ∨ r)) k
                    ; (k = i0) → proj (pt A) (pt B) (pt C)
                    ; (k = i1) → bs
                    ; (r = i0) → smot-comm-inv (comm-fill→ i j k l)
                    ; (r = i1) → coh i j k})
     (hcomp (λ l → λ { (i = i0) → gluel≡gluer (snd B) (j ∧ (~ l ∨ r)) k
                    ; (i = i1) → gluem≡gluer (snd C) j k
                    ; (j = i0) → gluel≡gluem (snd A) i k
                    ; (j = i1) → gluel≡gluer (snd B) (i ∨ (~ l ∨ r)) k
                    ; (k = i0) → proj (pt A) (pt B) (pt C)
                    ; (k = i1) → bs
                    ; (r = i0) → comm-fill← j (~ i) k l
                    ; (r = i1) → coh i j k})
            (coh i j k))

SmashAssocIso : Iso (A ⋀ (B ⋀∙ C)) ((A ⋀∙ B) ⋀ C)
SmashAssocIso {A = A} {B = B} {C = C} =
  compIso
    (Iso₁ A B C)
    (compIso
      (cool2 A B C)
      (compIso
        (invIso (Iso₁ C A B))
        ⋀CommIso))
