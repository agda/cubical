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

SmashAssocIso→ : (A ⋀ (B ⋀∙ C)) → ((A ⋀∙ B) ⋀ C)
SmashAssocIso→ = Iso.fun SmashAssocIso

SmashAssocIso← : ((A ⋀∙ B) ⋀ C) → A ⋀ (B ⋀∙ C)
SmashAssocIso← = Iso.inv SmashAssocIso

module _ (A B C D : Pointed ℓ)
  where
  pentagon-l₁ : ((A ⋀∙ B) ⋀∙ C) ⋀ D → (A ⋀∙ B) ⋀ (C ⋀∙ D)
  pentagon-l₁ = SmashAssocIso←

  pentagon-l₂ : (A ⋀∙ B) ⋀ (C ⋀∙ D) → A ⋀ (B ⋀∙ (C ⋀∙ D))
  pentagon-l₂ = SmashAssocIso←

  pentagon-r₁ : ((A ⋀∙ B) ⋀∙ C) ⋀ D → (A ⋀∙ (B ⋀∙ C)) ⋀ D
  pentagon-r₁ = (SmashAssocIso← , refl) ⋀→ idfun∙ D

  pentagon-r₁' : ((A ⋀∙ B) ⋀∙ C) ⋀ D → (A ⋀∙ (B ⋀∙ C)) ⋀ D
  pentagon-r₁' (inl tt) = inl tt
  pentagon-r₁' (inr (x , y)) = inr (SmashAssocIso← x , y)
  pentagon-r₁' (push (inl x) i) = push (inl (SmashAssocIso← x)) i
  pentagon-r₁' (push (inr x) i) = push (inr x) i
  pentagon-r₁' (push (push a i₁) i) = push (push a i₁) i

  conn₁' : (A ⋀∙ (B ⋀∙ C)) ⋀ D → (A ⋀∙ B) ⋀ (C ⋀∙ D)
  conn₁' (inl x) = inl x
  conn₁' (inr (inl x , d)) = inl tt
  conn₁' (inr (inr (a , inl x) , d)) = {!!}
  conn₁' (inr (inr (a , inr x) , d)) = {!!}
  conn₁' (inr (inr (a , push a₁ i) , d)) = {!!}
  conn₁' (inr (push a i , d)) = {!!}
  conn₁' (push a i) = {!!}

  conn₁ : (A ⋀∙ (B ⋀∙ C)) ⋀ D → (A ⋀∙ B) ⋀ (C ⋀∙ D)
  conn₁ (inl x) = inl x
  conn₁ (inr (inl x , d)) = inl x
  conn₁ (inr (inr (a , inl x) , d)) = inl x
  conn₁ (inr (inr (a , inr (b , c)) , d)) = inr ((inr (a , b)) , (inr (c , d)))
  conn₁ (inr (inr (a , push (inl x) i) , d)) =
    (push (inl (inr (a , x))) ∙ (λ i → inr (inr (a , x) , push (inr d) i))) i
  conn₁ (inr (inr (a , push (inr x) i) , d)) =
    (push (inr (inr (x , d))) ∙ (λ i → inr (push (inl a) i , inr (x , d)))) i
  conn₁ (inr (inr (a , push (push tt i₁) i) , d)) = {!!}
  conn₁ (inr (push (inl x) i , d)) = inl tt
  conn₁ (inr (push (inr (inl x)) i , d)) = inl tt
  conn₁ (inr (push (inr (inr (x , y))) i , d)) =
    (push (inr (inr (y , d))) ∙ (λ i → inr (push (inr x) i , inr (y , d)))) i
  conn₁ (inr (push (inr (push a i₁)) i , d)) = {!!}
  conn₁ (inr (push (push a i₁) i , d)) = inl tt
  conn₁ (push (inl (inl x)) i) = inl tt
  conn₁ (push (inl (inr (x , inl y))) i) = inl tt
  conn₁ (push (inl (inr (x , inr y))) i) =
    {!!}
  conn₁ (push (inl (inr (x , push a i₁))) i) = {!!}
  conn₁ (push (inl (push (inl x) i₁)) i) = inl tt
  conn₁ (push (inl (push (inr (inl x)) i₁)) i) = inl tt
  conn₁ (push (inl (push (inr (inr x)) i₁)) i) = {!!}
  conn₁ (push (inl (push (inr (push a i₂)) i₁)) i) = {!!}
  conn₁ (push (inl (push (push a i₂) i₁)) i) = inl tt
  conn₁ (push (inr x) i) = inl tt
  conn₁ (push (push tt i₁) i) = inl tt

  gali : (f : A ⋀ B → A ⋀ B)
         (p : f (inl tt) ≡ inl tt)
      → (pr : (x : typ A) (y : typ B) → f (inr (x , y)) ≡ inr (x , y))
      → ((a : typ A) → PathP (λ i → p i ≡ (pr a (pt B)) i) (cong f (push (inl a))) (push (inl a)))
      → ((b : typ B) → PathP (λ i → p i ≡ (pr (pt A) b) i) (cong f (push (inr b))) (push (inr b)))
      → (x : _) → f x ≡ x
  gali f p pr l r (inl x) = p ∙ (push (inl (pt A)) ∙ sym (push (inr (pt B))))
  gali f p pr l r (inr (x , y)) = pr x y
  gali f p pr l r (push (inl x) i) j =
    hcomp (λ r → λ {(i = i0) → (cong (λ q → p ∙ push (inl (pt A)) ∙ sym q) (λ i → push (push tt (~ i)))
                                   ∙∙ cong (p ∙_) (rCancel (push (inl (pt A))))
                                   ∙∙ sym (rUnit p)) (~ r) j
                   ; (i = i1) → pr x (snd B) j
                   ; (j = i0) → f (push (inl x) i)
                   ; (j = i1) → push (inl x) i })
          (l x j i)
  gali f p pr l r (push (inr x) i) j =
    hcomp (λ r → λ {(i = i0) → (cong (λ q → p ∙ push (inl (pt A)) ∙ sym q) (λ i → push (push tt (~ i)))
                                   ∙∙ cong (p ∙_) (rCancel (push (inl (pt A))))
                                   ∙∙ sym (rUnit p)) (~ r) j
                   ; (i = i1) → pr (snd A) x j
                   ; (j = i0) → f (push (inr x) i)
                   ; (j = i1) → push (inr x) i })
          (r x j i)
  gali f p pr l r (push (push a k) i) j =
    {!l!}

  gala : (f : A ⋀ B → A ⋀ B)
    → (f (inl tt) ≡ inl tt) → ((x : typ A) (y : typ B) → f (inr (x , y)) ≡ inr (x , y))
    → (x : _) → f x ≡ x
  gala f b p (inl x) = b ∙ (push (inl (pt A))) ∙ sym (push (inr (pt B)))
  gala f b p (inr x) = p (fst x) (snd x)
  gala f b p (push (inl x) i) = {!!}
  gala f b p (push (inr x) i) = {!!}
  gala f b p (push (push a i₁) i) = {!!}


  open import Cubical.Foundations.Path
  ⋀Fun : ∀ {ℓ} {C : Type ℓ}
       → (c₀ : C)
       → (pr : typ A × typ B → C)
       → (l : (a : typ A) → c₀ ≡ (pr (a , snd B)))
       → (r : (b : typ B) → c₀ ≡ (pr (snd A , b)))
       → l (pt A) ≡ r (pt B)
       → A ⋀ B → C
  ⋀Fun c₀ pr l r p (inl x) = c₀
  ⋀Fun c₀ pr l r p (inr x) = pr x
  ⋀Fun c₀ pr l r p (push (inl x) i) = l x i
  ⋀Fun c₀ pr l r p (push (inr x) i) = r x i
  ⋀Fun c₀ pr l r p (push (push a i₁) i) = p i₁ i

  →ss : ∀ {ℓ} {C : Type ℓ} (f g : A ⋀ B → C)
       → (b : f (inl tt) ≡ g (inl tt))
     → (p : (x : fst A × fst B) → f (inr x) ≡ g (inr x))
     → (l : ((a : fst A)
          → PathP (λ i → b i ≡ p (a , snd B) i)
             (cong f (push (inl a))) (cong g (push (inl a)))))
     → (r : ((y : fst B)
          → PathP (λ i → b i ≡ p (snd A , y) i)
             (cong f (push (inr y))) (cong g (push (inr y)))))
     → Cube (l (pt A)) (r (pt B))
             (λ i j → f (push (push tt i) j)) (λ i j → g (push (push tt i) j))
             refl refl
     → (x : _) → f x ≡ g x
  →ss f g b p l r c (inl x) = b
  →ss f g b p l r c (inr x) = p x
  →ss f g b p l r c (push (inl x) i) j = l x j i
  →ss f g b p l r c (push (inr x) i) j = r x j i
  →ss f g b p l r c (push (push a k) i) j = c k j i

  br : ∀ {ℓ} {C : Type ℓ} (f g : A ⋀ B → C) (inltt r₀ r1 : A ⋀ B) (l r : inltt ≡ r₀)
       (pus : l ≡ r) (b : f inltt ≡ g inltt) (l₂ : inltt ≡ r1)
     → (p : f r1 ≡ g r1)
     → PathP (λ i → b i ≡ p i) (cong f l₂) (cong g l₂)
     → PathP (λ i → (cong f (l ∙ sym r) ∙∙ b ∙∙ cong g (l ∙ sym r)) i ≡ p i)
              (cong f l₂)
              (cong g l₂)
  br f g inltt r₀ r1 l r pus b l2 p pp =
    flipSquare ((cong (λ x → cong f x ∙∙ b ∙∙ cong g x) (cong (λ x → l ∙ sym x) (sym pus) ∙ rCancel l) ∙ sym (rUnit b)) ◁ flipSquare pp)

  brpp : {!∀ {ℓ} {C : Type ℓ} (f g : A ⋀ B → C) (inltt r₀ r1 : A ⋀ B) (l r : inltt ≡ r₀)
       (pus : l ≡ r) (b : f inltt ≡ g inltt) (l₂ : inltt ≡ r1)
     → (p : f r1 ≡ g r1)
     → PathP (λ i → b i ≡ p i) (cong f l₂) (cong g l₂)
     → PathP (λ i → (cong f (l ∙ sym r) ∙∙ b ∙∙ cong g (l ∙ sym r)) i ≡ p i)
              (cong f l₂)
              (cong g l₂)!}
  brpp = {!!}

  ⋁fun : ∀ {ℓ} (C : A ⋁ B → Type ℓ)
    (f : (x : typ A) → C (inl x))
    (g : (x : typ B) → C (inr x))
    → PathP (λ i → C (push tt i)) (f (pt A)) (g (pt B))
    →  (x : A ⋁ B) → C x
  ⋁fun C f g pp (inl x) = f x
  ⋁fun C f g pp (inr x) = g x
  ⋁fun C f g pp (push a i) = pp i

  data Id {ℓ : Level} {A : Type ℓ} (x : A) : A → Type ℓ where
    idp : Id x x

  idconv : ∀ {ℓ} {A : Type ℓ} (x y : A) → Id x y → x ≡ y
  idconv x y idp = refl

  idconv⁻ : ∀ {ℓ} {A : Type ℓ} (x y : A) → x ≡ y → Id x y
  idconv⁻ x y = J (λ y p → Id x y) idp

  Id≡ : ∀ {ℓ} {A : Type ℓ} (x y : A) → Iso (Id x y) (x ≡ y)
  Iso.fun (Id≡ x y) = idconv x y
  Iso.inv (Id≡ x y) = idconv⁻ x y
  Iso.rightInv (Id≡ x y) = J (λ y b → idconv x y (idconv⁻ x y b) ≡ b) (cong (idconv x x) (transportRefl idp))
  Iso.leftInv (Id≡ x .x) idp = transportRefl idp

  ∙p : ∀ {ℓ} {A : Type ℓ} {x y z : A} → (p : Id x y) (q : Id y z) → Id x z 
  ∙p p idp = p

  wedge→ :  ∀ {ℓ} {C : A ⋁ B → Type ℓ}
    (f₁ f₂ : (x : typ A) → C (inl x))
    → f₁ ≡ f₂
    → (g₁ g₂ : (x : typ B) → C (inr x))
    → g₁ ≡ g₂
    → (p₁ : PathP (λ i → C (push tt i)) (f₁ (pt A)) (g₁ (pt B)))
      (p₂ : PathP (λ i → C (push tt i)) (f₂ (pt A)) (g₂ (pt B)))
    → (x : _)
    → ⋁fun C f₁ g₁ p₁ x ≡ ⋁fun C f₂ g₂ p₂ x
  wedge→ {C = C} f₁ f₂ =
    J (λ f₂ _ → (g₁ g₂ : (x : typ B) → C (inr x))
    → g₁ ≡ g₂
    → (p₁ : PathP (λ i → C (push tt i)) (f₁ (pt A)) (g₁ (pt B)))
      (p₂ : PathP (λ i → C (push tt i)) (f₂ (pt A)) (g₂ (pt B)))
    → (x : _)
    → ⋁fun C f₁ g₁ p₁ x ≡ ⋁fun C f₂ g₂ p₂ x)
    λ g₁ g₂ → J (λ g₂ _ → (p₁ : PathP (λ i → C (push tt i)) (f₁ (pt A)) (g₁ (pt B)))
      (p₂ : PathP (λ i → C (push tt i)) (f₁ (pt A)) (g₂ (pt B)))
      (x : A ⋁ B) →
      ⋁fun C f₁ g₁ p₁ x ≡ ⋁fun C f₁ g₂ p₂ x)
      {!!}
      where
      help : (f : _) (g : _) → (p₁ p₂ : PathP (λ i → C (push tt i)) (f (pt A)) (g (pt B)))
        (x : A ⋁ B) →
        ⋁fun C f g p₁ x ≡ ⋁fun C f g p₂ x
      help f g p1 p2 (inl x) = {!!} -- refl
      help f g p1 p2 (inr x) = {!!} -- refl
      help f g p1 p2 (push a i) = {!!}

  →s' : ∀ {ℓ} {C : Type ℓ} (f g : A ⋀ B → C)
     → (b : f (inl tt) ≡ g (inl tt))
     → (p : (x : fst A × fst B) → f (inr x) ≡ g (inr x))
     → ((a : fst A)
          → PathP (λ i → b i ≡ p (a , snd B) i)
             (cong f (push (inl a))) (cong g (push (inl a))))
     → ((y : fst B)
          → PathP (λ i → b i ≡ p (snd A , y) i)
             (cong f (push (inr y))) (cong g (push (inr y))))
     → (x : _) → f x ≡ g x
  →s' f g b p l r (inl x) = {!cong f (push (!} ∙∙ b ∙∙ {!!}
  →s' f g b p l r (inr x) = {!!}
  →s' f g b p l r (push a i) = {!!}

  →s : ∀ {ℓ} {C : Type ℓ} (f g : A ⋀ B → C)
     → (b : f (inl tt) ≡ g (inl tt))
     → (p : (x : fst A × fst B) → f (inr x) ≡ g (inr x))
     → ((a : fst A)
          → PathP (λ i → b i ≡ p (a , snd B) i)
             (cong f (push (inl a))) (cong g (push (inl a))))
     → ((y : fst B)
          → PathP (λ i → b i ≡ p (snd A , y) i)
             (cong f (push (inr y))) (cong g (push (inr y))))
     → (x : _) → f x ≡ g x
  →s f g b p l r (inl x) =
    cong f ((push (inl (snd A))) ∙ (sym (push (inr (snd B)))))
    ∙∙ b
    ∙∙ cong g ((push (inl (snd A))) ∙ (sym (push (inr (snd B)))))
  →s f g b p l r (inr x) = p x
  →s f g b p l r (push (inl x) i) j =
    br f g (inl tt) (inr (pt A , pt B)) (inr (x , pt B)) (push (inl (pt A)))
       (push (inr (pt B))) (λ i → push (push tt i))
       b (push (inl x)) (p (x , pt B)) (l x) j i
  →s f g b p l r (push (inr x) i) j =
    br f g (inl tt) (inr (pt A , pt B)) (inr (pt A , x)) (push (inl (pt A)))
       (push (inr (pt B))) (λ i → push (push tt i))
       b (push (inr x)) (p (pt A , x)) (r x) j i
  →s f g b p l r (push (push a k) i) j = {!!}

  pathsp-contr : (a : typ A) (x : A ⋀ B) (p : inr (a , pt B) ≡ x) → Type ℓ
  pathsp-contr a (inl x) = λ p → sym (push (inl a)) ≡ p
  pathsp-contr a (inr x) = λ p → p ≡ p
  pathsp-contr a (push b i) = {!!}
    where
    help : PathP (λ i → Path (A ⋀ B) (inr (a , pt B)) (push b i) → Type ℓ) (λ p → sym (push (inl a)) ≡ p) λ p → p ≡ p
    help = toPathP (funExt λ p → {!!})

  t1 : (x : ((A ⋀∙ B) ⋀∙ C) ⋀ D) → pentagon-l₁ x ≡ conn₁ (pentagon-r₁ x)
  t1 (inl x) = refl
  t1 (inr (inl x , d)) = refl
  t1 (inr (inr (inl x , c) , d)) = sym (push (inr (inr (c , d))))
  t1 (inr (inr (inr (x , b) , c) , d)) = refl
  t1 (inr (inr (push (inl x) i , c) , d)) = {!!}
  t1 (inr (inr (push (inr x) i , c) , d)) j = {!!}
  t1 (inr (inr (push (push a i₁) i , c) , d)) = {!!}
  t1 (inr (push (inl (inl x)) i , d)) j = {!!}
  t1 (inr (push (inl (inr x)) i , d)) j = {!!}
  t1 (inr (push (inl (push (inl x) i₁)) i , d)) j = {!!}
  t1 (inr (push (inl (push (inr x) i₁)) i , d)) j = {!!}
  t1 (inr (push (inl (push (push a i₂) i₁)) i , d)) j = {!!}
  t1 (inr (push (inr x) i , d)) j = {!!}
  t1 (inr (push (push a i₁) i , d)) = {!a!}
  t1 (push a i) = {!!}


--   pentagon-r₂ : (A ⋀∙ (B ⋀∙ C)) ⋀ D → A ⋀ ((B ⋀∙ C) ⋀∙ D)
--   pentagon-r₂ = SmashAssocIso←

--   pentagon-r₃ : A ⋀ ((B ⋀∙ C) ⋀∙ D) → A ⋀ (B ⋀∙ (C ⋀∙ D))
--   pentagon-r₃ = idfun∙ A ⋀→ (SmashAssocIso← , refl)

--   pentagon-r₃' : A ⋀ ((B ⋀∙ C) ⋀∙ D) → A ⋀ (B ⋀∙ (C ⋀∙ D))
--   pentagon-r₃' (inl x) = inl tt
--   pentagon-r₃' (inr (x , y)) = inr (x , SmashAssocIso← y)
--   pentagon-r₃' (push (inl x) i) = push (inl x) i
--   pentagon-r₃' (push (inr x) i) = push (inr (SmashAssocIso← x)) i
--   pentagon-r₃' (push (push a i₁) i) = push (push tt i₁) i

--   indi-easy : (f g : (A ⋀ B) → (C ⋀ D))
--             → (b : f (inl tt) ≡ g (inl tt))
--             → (p : ((x : typ A) (y : typ B) → f (inr (x , y)) ≡ g (inr (x , y))))
--             → ((x : typ A) → PathP (λ i → b i ≡ p x (pt B) i)
--                   (cong f (push (inl x))) (cong g (push (inl x))))
--             → (((x : typ B) → PathP (λ i → b i ≡ p (pt A) x i)
--                   (cong f (push (inr x))) (cong g (push (inr x)))))
--             → (((x : _) → f x ≡ g x))
--   indi-easy f g b p l r (inl x) = b
--   indi-easy f g b p l r (inr x) = p (fst x) (snd x)
--   indi-easy f g b p l r (push (inl x) i) j = l x j i
--     where
--     help : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
--       → (b : B)
--       → (f g : A → B)
--       → (λ _ → b) ≡ f
--       → (λ _ → b) ≡ g
--       → (p : f ≡ g)
--       → {!!}
--     help = {!!}
--   indi-easy f g b p l r (push (inr x) i) j = r x j i
--   indi-easy f g b p l r (push (push a i₁) i) k = {!b!}

--   indi : (f g : (((A ⋀∙ B) ⋀∙ C) ⋀∙ D) →∙ (A ⋀∙ (B ⋀∙ (C ⋀∙ D))))
--        → ((x : typ A) (y : typ B) (c : typ C) (d : typ D)
--              → fst f (inr (inr (inr (x , y) , c) , d))
--              ≡ fst g (inr (inr (inr (x , y) , c) , d)))
--        → (x : _) → fst f x ≡ fst g x
--   indi f g p (inl x) = snd f ∙ (sym (snd g))
--   indi f g p (inr (x , y)) = {!!}
--   indi f g p (push a i) = {!!}


--   cube₁ : (x : fst A) (y : fst D) (z : fst C) (i j k : I) → A ⋀ (B ⋀∙ (C ⋀∙ D))
--   cube₁ x y z i j k =
--     hfill (λ k → λ {(i = i0)
--                     → pentagon-r₃' (doubleCompPath-filler (push (inl x)) (λ j → inr (x , push (inr y) j)) refl k j)
--                    ; (i = i1) → inr (x , inr (snd B , inr (z , y)))
--                    ; (j = i0) → doubleCompPath-filler (push (inl x)) (λ j → (inr (x , push (inr (inr (z , y))) j))) refl k i
--                    ; (j = i1) → inr (x , push (inr (inr (z , y))) i)}
--                   )
--           (inS ((inr (x , push (inr (inr (z , y))) i)))) k

--   cube₂ : (x : fst A) (y : fst D) (z : fst C) (i j k : I) → A ⋀ (B ⋀∙ (C ⋀∙ D))
--   cube₂ x y z i j k =
--     hfill (λ k → λ {(i = i0) → pentagon-r₃' (pentagon-r₂
--                                     (inr (push (inl x) (~ k ∧ j) , y)))
--                    ; (i = i1) → inr (x , inr (snd B , inr (z , y)))
--                    ; (j = i0) → pentagon-l₂ (pentagon-l₁ (inr (inr (push (inl x) i , z) , y)))
--                    ; (j = i1) → pentagon-r₃'
--                                   (pentagon-r₂
--                                     (inr (doubleCompPath-filler (λ i₁ → push (inl x) (i₁)) (λ i → (inr (x , push (inr z) i))) refl k i , y)))})
--            (inS (cube₁ x y z i j i1))
--            k
       
--   cube₂̣₅ : (x : typ A) (y : typ B) (z : typ D) → (j k i : I) → A ⋀ (B ⋀∙ (C ⋀∙ D)) 
--   cube₂̣₅ x y z j k i =
--     hfill (λ i → λ {(j = i0) → doubleCompPath-filler refl (λ k → (inr (x , push (inl y) (~ k)))) (sym (push (inl x))) i k
--                    ; (j = i1) → inr (x , (push (inl y) (~ k)))
--                    ; (k = i0) → inr (x , inr (y , inl tt))
--                    ; (k = i1) → pentagon-r₃' (doubleCompPath-filler (push (inl x)) (λ j → (inr (x , push (inr z) j))) refl i j) })
--           (inS (inr (x , (push (inl y) (~ k)))))
--           i

--   cube₃ : (x : typ A) (y : typ B) (z : typ D) → (i j k : I) → A ⋀ (B ⋀∙ (C ⋀∙ D))
--   cube₃ x y z i j k =
--     hfill (λ k → λ {(i = i0) → cube₂̣₅ x y z j k i1
--                    ; (i = i1) → inr (x , inr (y , inr (snd C , z)))
--                    ; (j = i0) → pentagon-l₂ (doubleCompPath-filler (push (inl (inr (x , y)))) (λ i → inr (inr (x , y) , push (inr z) i)) refl k i)
--                    ; (j = i1) → inr (x , doubleCompPath-filler (push (inl y)) (λ i → inr (y , push (inr z) i)) refl k i)})
--           (inS (inr (x , inr (y , push (inr z) i))))
--           k

--   cube₄ : (x : typ A) (y : typ B) (z : typ D) → (i j k : I) → A ⋀ (B ⋀∙ (C ⋀∙ D))
--   cube₄ x y z i j k =
--     hfill (λ k → λ {(i = i0) → pentagon-r₃' (pentagon-r₂
--                                   (inr (push (inl x) (j ∧ ~ k) , z)))
--                    ; (i = i1) → inr (x , inr (y , inr (snd C , z)))
--                    ; (j = i0) →
--                      pentagon-l₂
--                        (pentagon-l₁ (inr (push (inl (inr (x , y))) i , z)))
--                    ; (j = i1) →
--                      pentagon-r₃' (pentagon-r₂
--                        (inr (doubleCompPath-filler (push (inl x)) (λ i → inr (x , push (inl y) i)) refl k i , z)))})
--           (inS (cube₃ x y z i j i1))
--           k

--   pentagon' : (x : _) → pentagon-l₂ (pentagon-l₁ x)
--                        ≡ pentagon-r₃' (pentagon-r₂ (pentagon-r₁' x))
--   pentagon' (inl x) = refl
--   pentagon' (inr (inl x , y)) = refl
--   pentagon' (inr (inr (inl x , z) , y)) = refl
--   pentagon' (inr (inr (inr x , z) , y)) = refl
--   pentagon' (inr (inr (push (inl x) i , z) , y)) j = cube₂ x y z i j i1
--   pentagon' (inr (inr (push (inr x) i , z) , y)) = refl
--   pentagon' (inr (inr (push (push a k) i , z) , y)) j = {! (i∧ (inl (push (inl ?) ?)))!}
--   pentagon' (inr (push (inl (inl x)) i , y)) j =
--     pentagon-l₂ (doubleCompPath-filler (push (inl (inl x)))
--                 (λ i → (inr (inl x , push (inr y) i))) refl (~ j) i)
--   pentagon' (inr (push (inl (inr (x , y))) i , z)) j = cube₄ x y z i j i1
--   pentagon' (inr (push (inl (push (inl x) k)) i , y)) j =
--     hcomp (λ r → λ {(i = i0) → {!!}
--                    ; (i = i1) → {!!}
--                    ; (j = i0) → {!cube₄ x (pt B) y i j r!}
--                    ; (j = i1) → {!!}
--                    ; (k = i0) → {!pentagon-r₁' (inr (push (inl (push (inl x) k)) i , y))!}
--                    ; (k = i1) → cube₄ x (pt B) y i j i1})
--           {!!}
--   pentagon' (inr (push (inl (push (inr x) k)) i , y)) j =
--     {!k = i0 ⊢ pentagon-l₂ (doubleCompPath-filler (push (inl (inl x)))
--                 (λ i → (inr (inl x , push (inr y) i))) refl (~ j) i)
-- k = i1 ⊢ cube₄ x y z i j i1
-- i = i0 ⊢ inl tt
-- i = i1 ⊢ pentagon' (inr (inr (i∧ (inl (push (inl x) k))) , y)) j
-- j = i0 ⊢ pentagon-l₂
--   (pentagon-l₁ (inr (push (inl (push (inl x) k)) i , y)))
-- j = i1 ⊢ pentagon-r₃'
--          (pentagon-r₂
--           (pentagon-r₁' (inr (push (inl (push (inl x) k)) i , y))))!}
--   pentagon' (inr (push (inl (push (push a k) r)) i , y)) j = {!!}
--   pentagon' (inr (push (inr x) i , y)) = refl
--   pentagon' (inr (push (push a i₁) i , y)) j = {!a!}
--   pentagon' (push (inl (inl x)) i) = refl -- refl
--   pentagon' (push (inl (inr (inl x , y))) i) j = {!!}
--   pentagon' (push (inl (inr (inr (x , y) , z))) i) j = {!y!}
--   pentagon' (push (inl (inr (push a i₁ , y))) i) j = {!!}
--   pentagon' (push (inl (push a i₁)) i) j = {!!}
--   pentagon' (push (inr x) i) = refl -- refl
--   pentagon' (push (push a i₁) i) = refl -- refl

-- kn : {!∀ {ℓ ℓ'} {A : Type ℓ'} (S : Type ℓ → Type ℓ' → Type ℓ'')!}
-- kn = {!!}
