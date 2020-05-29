{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SmashProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Pushout.Base
open import Cubical.Data.Unit
open import Cubical.Data.Prod
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

_⋀∙_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
A ⋀∙ B = Pushout {A = (A ⋁ B)} (λ _ → tt) i∧ , (inl tt)


_⋀→_ : (f : A →∙ C) (g : B →∙ D)  → A ⋀ B → C ⋀ D
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

{- associativity maps for smash produts. Proof pretty much direcly translated from https://github.com/ecavallo/redtt/blob/master/library/pointed/smash.red -}
private
  pivotl : (b b' : typ B)
         → Path (Smash A B) (proj (snd A) b) (proj (snd A) b')
  pivotl b b' i = (gluer b ∙ sym (gluer b')) i

  pivotr : (a a' : typ A)
         → Path (Smash A B) (proj a (snd B)) (proj a' (snd B))
  pivotr a a' i = (gluel a ∙ sym (gluel a')) i

  pivotlrId : {A : Pointed ℓ} {B : Pointed ℓ'} → _
  pivotlrId {A = A} {B = B} = rCancel (gluer (snd B)) ∙ sym (rCancel (gluel (snd A)))

  rearrange-proj : (c : fst C)
                → (Smash A B) → Smash (SmashPtProj C B) A
  rearrange-proj c basel = baser
  rearrange-proj c baser = basel
  rearrange-proj c (proj x y) = proj (proj c y) x
  rearrange-proj {C = C} c (gluel a i) =
    hcomp (λ k → λ { (i = i0) → proj (pivotr (snd C) c k) a
                    ; (i = i1) → baser})
          (gluer a i)
  rearrange-proj c (gluer b i) = gluel (proj c b) i

  rearrange-gluel : (s : Smash A B)
                 → Path (Smash (SmashPtProj C B) A) basel (rearrange-proj (snd C) s)
  rearrange-gluel {A = A} {B = B} {C = C} basel = sym (gluel (proj (snd C) (snd B))) ∙
                                                  gluer (snd A)
  rearrange-gluel baser = refl
  rearrange-gluel {A = A} {B = B} {C = C} (proj a b) i =
    hcomp (λ k → λ { (i = i0) → (sym (gluel (proj (snd C) (snd B))) ∙
                                                  gluer (snd A)) (~ k)
                    ; (i = i1) → proj (pivotl (snd B) b k) a})
          (gluer a (~ i))
  rearrange-gluel {A = A} {B = B} {C = C} (gluel a i) j =
    hcomp (λ k → λ { (i = i1) → ((λ i₁ → gluel (proj (snd C) (snd B)) (~ i₁)) ∙
                                  gluer (snd A)) (~ k ∨ j)
                    ; (j = i0) → ((λ i₁ → gluel (proj (snd C) (snd B)) (~ i₁)) ∙
                                  gluer (snd A)) (~ k)
                    ; (j = i1) → top-filler i k})
          (gluer a (i ∨ ~ j))
    where
      top-filler : I → I → Smash (SmashPtProj C B) A
      top-filler i j =
        hcomp (λ k → λ { (i = i0) → side-filler k j
                        ; (i = i1) → gluer a (j ∨ k)
                        ; (j = i0) → gluer a (i ∧ k)})
              (gluer a (i ∧ j))
       where
       side-filler : I → I → Smash (SmashPtProj C B) A
       side-filler i j =
         hcomp (λ k → λ { (i = i0) → proj (proj (snd C) (snd B)) a
                        ; (i = i1) → proj ((rCancel (gluel (snd C)) ∙ sym (rCancel (gluer (snd B)))) k j) a
                        ; (j = i0) → proj (proj (snd C) (snd B)) a
                        ; (j = i1) → (proj ((gluel (snd C) ∙ sym (gluel (snd C))) i) a)})
                (proj ((gluel (snd C) ∙ sym (gluel (snd C))) (j ∧ i)) a)
  rearrange-gluel {A = A} {B = B} {C = C} (gluer b i) j =
    hcomp (λ k → λ {(i = i1) → ((sym (gluel (proj (snd C) (snd B)))) ∙ gluer (snd A)) (~ k)
                   ; (j = i0) → ((sym (gluel (proj (snd C) (snd B)))) ∙ gluer (snd A)) (~ k)
                   ; (j = i1) → top-filler1 i k})
          (gluer (snd A) (i ∨ (~ j)))
    where
    top-filler1 : I → I → Smash (SmashPtProj C B) A
    top-filler1 i j =
      hcomp (λ k → λ { (i = i0) → congFunct (λ x → proj x (snd A)) (gluer (snd B)) (sym (gluer b)) (~ k) j
                   ; (i = i1) → (sym (gluel (proj (snd C) (snd B))) ∙ gluer (snd A)) (~ j)
                   ; (j = i0) → gluer (snd A) i
                   ; (j = i1) → gluel (proj (snd C) b) i})
          (top-filler2 i j)
      where
      top-filler2 : I → I → Smash (SmashPtProj C B) A
      top-filler2 i j =
        hcomp (λ k → λ { (j = i0) → gluer (snd A) (i ∧ k)
                          ; (j = i1) → gluel (gluer b (~ k)) i})
                (hcomp (λ k → λ { (j = i0) → gluel (gluer (snd B) i0) (~ k ∧ (~ i))
                                 ; (j = i1) → gluel (baser) (~ k ∨ i)
                                 ; (i = i0) → gluel (gluer (snd B) j) (~ k)
                                 ; (i = i1) → gluel (proj (snd C) (snd B)) j })
                       (gluel (proj (snd C) (snd B)) (j ∨ (~ i))))

  rearrange : Smash (SmashPtProj A B) C → Smash (SmashPtProj C B) A
  rearrange basel = basel
  rearrange baser = baser
  rearrange (proj x y) = rearrange-proj y x
  rearrange (gluel a i) = rearrange-gluel a (~ i)
  rearrange {A = A} {B = B} {C = C} (gluer b i) = ((λ j → proj (pivotr b (snd C) j) (snd A)) ∙
                                                  gluer (snd A)) i

  ⋀∙→SmashPtProj : (A ⋀∙ B) →∙ SmashPtProj A B
  ⋀∙→SmashPtProj {A = A} {B = B} = fun , refl
    where
    fun : (A ⋀ B) → Smash A B
    fun (inl x) = proj (snd A) (snd B)
    fun (inr (x , x₁)) = proj x x₁
    fun (push (inl x) i) = pivotr (snd A) x i
    fun (push (inr x) i) = pivotl (snd B) x i
    fun (push (push a j) i) = pivotlrId (~ j) i

  SmashPtProj→⋀∙ : (SmashPtProj A B) →∙ (A ⋀∙ B)
  SmashPtProj→⋀∙ {A = A} {B = B} = Smash→⋀ , sym (push (inr (snd B)))

SmashAssociate : Smash (SmashPtProj A B) C → Smash A (SmashPtProj B C)
SmashAssociate = comm ∘ Smash-map  (comm , refl) (idfun∙ _) ∘ rearrange

SmashAssociate⁻ : Smash A (SmashPtProj B C) → Smash (SmashPtProj A B) C
SmashAssociate⁻ = rearrange ∘ comm ∘ Smash-map (idfun∙ _) (comm , refl)

⋀-associate : (A ⋀∙ B) ⋀ C → A ⋀ (B ⋀∙ C)
⋀-associate = (idfun∙ _ ⋀→ SmashPtProj→⋀∙) ∘ Smash→⋀ ∘ SmashAssociate ∘ ⋀→Smash ∘ (⋀∙→SmashPtProj ⋀→ idfun∙ _)

⋀-associate⁻ : A ⋀ (B ⋀∙ C) → (A ⋀∙ B) ⋀ C
⋀-associate⁻ = (SmashPtProj→⋀∙ ⋀→ idfun∙ _) ∘ Smash→⋀ ∘ SmashAssociate⁻ ∘ ⋀→Smash ∘ (idfun∙ _ ⋀→ ⋀∙→SmashPtProj)
