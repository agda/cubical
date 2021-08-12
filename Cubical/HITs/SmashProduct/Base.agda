{-# OPTIONS --safe #-}
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

private
  rCancelPathP : ∀ {ℓ} {A B : Type ℓ} {x y : A} (p : x ≡ y) (f : A → B)
              → PathP (λ i → cong-∙ f p (sym p) i ≡ refl)
                       (cong (cong f) (rCancel p))
                       (rCancel (cong f p))
  rCancelPathP {x = x} {y = y} p f i j k =
    hcomp (λ r → λ { (i = i0) → f (rCancel-filler p r j k)
                    ; (j = i1) → f x
                    ; (k = i0) → f x
                    ; (k = i1) → f (p (~ r ∧ ~ j))})
          (f (p (k ∧ ~ j)))

  mainGen : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x)
          → (P : refl ≡ p)
          → Cube (λ j k → (cong (p ∙_) (cong sym (sym P)) ∙ sym (rUnit _)) k j)
                  refl
                  refl
                  refl
                  (rCancel p)
                  (sym P)
  mainGen {x = x} p = J (λ p P → Cube (λ j k → (cong (p ∙_) (cong sym (sym P)) ∙ sym (rUnit _)) k j)
                  refl
                  refl
                  refl
                  (rCancel p)
                  (sym P))
                 (transport (λ i → Cube (λ j k → (lUnit (sym (rUnit (refl {x = x}))) i) k j)
                            l l l (rCancel (λ _ → x)) l)
                            λ i j k → rCancel (λ _ → x) (k ∨ i) j)
    where
    l = refl {x = refl {x = x}}

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

{- associativity maps for smash produts. Proof pretty much direcly translated from
   https://github.com/ecavallo/redtt/blob/master/library/pointed/smash.red -}
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


data _⋀'_ {ℓ ℓ' : Level} (A : Pointed ℓ) (B : Pointed ℓ') : Type (ℓ-max ℓ ℓ') where
  incl : typ A → typ B → A ⋀' B
  pathl : (a : typ A) → incl a (pt B) ≡ incl (pt A) (pt B)
  pathr : (b : typ B) → incl (pt A) b ≡ incl (pt A) (pt B)
  pathlCoh : pathl (pt A) ≡ refl
  pathrCoh : pathr (pt B) ≡ refl

module _ {ℓ'' : Level} (P P' : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ'))
         (d : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') → Iso (typ (P (P A B) C)) (typ (P A (P B C))))
         (d' : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') → Iso (typ (P' (P' A B) C)) (typ (P' A (P' B C))))
         (∧-map : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → typ (P A B) → typ (P' A B))
         (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'')
         (is1 : Iso (typ (P A ((Pushout {A = typ (P B C)} ∧-map λ _ → tt) , inl (pt (P' B C)))))
                    (typ (P ((Pushout {A = typ (P A B)} ∧-map λ _ → tt) , inl (pt (P' A B))) C)))
         (is2 : Iso (typ (P' A ((Pushout {A = typ (P B C)} ∧-map λ _ → tt) , inl (pt (P' B C)))))
                    (typ (P' ((Pushout {A = typ (P A B)} ∧-map λ _ → tt) , inl (pt (P' A B))) C)))

         (coherence1 : (a : _) → Iso.fun is2 (∧-map a) ≡ ∧-map (Iso.fun is1 a))
         (coherence2 : (a : _) → Iso.inv is2 (∧-map a) ≡ ∧-map (Iso.inv is1 a))
          where

  _⊚_ : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') → Type _
  A ⊚ B = Pushout {A = typ (P A B)} ∧-map λ _ → tt

  typL = A ⊚ ((B ⊚ C) , inl (pt (P' B C)))
  typR = ((A ⊚ B) , inl (pt (P' A B))) ⊚ C

  f : typL → typR
  f (inl x) = inl (Iso.fun is2 x) -- inl (Iso.fun is1 x )
  f (inr x) = inr x
  f (push a i) = s i
    where
    s : inl (Iso.fun is2 (∧-map a)) ≡ inr tt
    s = cong inl (coherence1 a) ∙ push (Iso.fun is1 a)

  f⁻ : typR → typL
  f⁻ (inl x) = inl (Iso.inv is2 x)
  f⁻ (inr x) = inr x
  f⁻ (push a i) = s i
    where
    s : inl (Iso.inv is2 (∧-map a)) ≡ inr tt
    s = cong inl (coherence2 a)
      ∙ push (Iso.inv is1 a)

  module _ (pp1 : (a : _) → PathP (λ i → inl (Iso.rightInv is2 (∧-map a) i) ≡ inr tt)
                                   (cong f (cong inl (coherence2 a)) ∙ cong f (push (Iso.inv is1 a))) (push a))

           (pp2 : (a : _) → PathP (λ i → inl (Iso.leftInv is2 (∧-map a) i) ≡ inr tt)
                                   (cong f⁻ (cong inl (coherence1 a)) ∙ cong f⁻ (push (Iso.fun is1 a)))
                                   (push a))
            where
      f→f⁻→f : (a : _) → f (f⁻ a) ≡ a
      f→f⁻→f (inl x) = cong inl (Iso.rightInv is2 x)
      f→f⁻→f (inr x) = refl
      f→f⁻→f (push a i) j =
        hcomp (λ k → λ { (i = i0) → inl (Iso.rightInv is2 (∧-map a) j)
                        ; (i = i1) → inr tt
                        ; (j = i0) → cong-∙ f (cong inl (coherence2 a)) (push (Iso.inv is1 a)) (~ k) i
                        ; (j = i1) → push a i})
              (pp1 a j i)

      f⁻→f→f⁻ : (a : _) → f⁻ (f a) ≡ a
      f⁻→f→f⁻ (inl x) = cong inl (Iso.leftInv is2 x)
      f⁻→f→f⁻ (inr x) = refl
      f⁻→f→f⁻ (push a i) j =
        hcomp (λ k → λ { (i = i0) → inl (Iso.leftInv is2 (∧-map a) j)
                        ; (i = i1) → inr tt
                        ; (j = i0) → cong-∙ f⁻ (cong inl (coherence1 a)) (push (Iso.fun is1 a)) (~ k) i
                        ; (j = i1) → push a i})
              (pp2 a j i)

      mainIso : Iso typL typR
      Iso.fun mainIso = f
      Iso.inv mainIso = f⁻
      Iso.rightInv mainIso = f→f⁻→f
      Iso.leftInv mainIso = f⁻→f→f⁻


wedge : ∀ {ℓ ℓ'} → {A : Pointed ℓ} → {B : Pointed ℓ'} → A ⋁ B → fst A × fst B 
wedge {B = B} (inl x) = x , pt B
wedge {A = A} (inr x) = (pt A) , x
wedge {A = A} {B = B} (push a i) = (pt A) , (pt B)

_Sm_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Type (ℓ-max ℓ ℓ')
A Sm B = Pushout {A = A ⋁ B} wedge λ _ → tt

SmashIso : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'')
        → Iso (A Sm (B Sm C , inl (pt B , pt C))) ((A Sm B , inl (pt A , pt B)) Sm C)
SmashIso A B C =
  mainIso (λ A B → A ⋁ B , inl (pt A))
          (λ A B → (typ A × typ B) , ((pt A) , (pt B)))
          ∨-assoc
          (λ _ _ _ → invIso ×Assoc)
          wedge
          A
          B
          C
          is1
          {!!}
          {!!}
          {!!}
          {!!}
          {!!}
  where
  is1 : Iso _ _
  Iso.fun is1 (inl x) = {!!}
  Iso.fun is1 (inr x) = {!!}
  Iso.fun is1 (push a i) = {!!}
  Iso.inv is1 = {!!}
  Iso.rightInv is1 = {!!}
  Iso.leftInv is1 = {!!}
  ×Assoc : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → Iso (A × (B × C)) ((A × B) × C)
  Iso.fun ×Assoc (x , (y , z)) = (x , y) , z
  Iso.inv ×Assoc ((x , y) , z) = x , (y , z)
  Iso.rightInv ×Assoc ((x , x₂) , x₁) = refl
  Iso.leftInv ×Assoc (x , (y , z)) = refl

  FF : ∀ {ℓ₁ ℓ''' ℓ'''' : Level}
      {A : Pointed ℓ₁} {B : Pointed ℓ'''} {C : Pointed ℓ''''}
      → ((A ⋁ B) , inl (pt A)) ⋁ C →
         A ⋁ ((B ⋁ C) , inl (pt B))
  FF (inl (inl x)) = inl x
  FF (inl (inr x)) = inr (inl x)
  FF (inl (push a i)) = push a i
  FF (inr x) = inr (inr x)
  FF (push a i) = (push a ∙ cong inr (push tt)) i

  FF⁻ : ∀ {ℓ₁ ℓ''' ℓ'''' : Level}
      {A : Pointed ℓ₁} {B : Pointed ℓ'''} {C : Pointed ℓ''''}
      →  A ⋁ ((B ⋁ C) , inl (pt B))
      → ((A ⋁ B) , inl (pt A)) ⋁ C
  FF⁻ (inl x) = inl (inl x)
  FF⁻ (inr (inl x)) = inl (inr x)
  FF⁻ (inr (inr x)) = inr x
  FF⁻ (inr (push a i)) = (cong inl (sym (push a)) ∙ push a) i
  FF⁻ (push a i) = inl (push a i)

  FF→FF⁻→FF : ∀ {ℓ₁ ℓ''' ℓ'''' : Level}
      {A : Pointed ℓ₁} {B : Pointed ℓ'''} {C : Pointed ℓ''''}
      (x : A ⋁ ((B ⋁ C) , inl (pt B))) → FF (FF⁻ x) ≡ x
  FF→FF⁻→FF (inl x) = refl
  FF→FF⁻→FF (inr (inl x)) = refl
  FF→FF⁻→FF (inr (inr x)) = refl
  FF→FF⁻→FF (inr (push a i)) k = h k i
    where
    h : cong FF ((cong inl (sym (push a)) ∙ push a)) ≡ cong inr (push a)
    h = cong-∙ FF (cong inl (sym (push a))) (push a)
     ∙∙ assoc _ _ _
     ∙∙ cong (_∙ cong inr (push a)) (lCancel _)
      ∙ sym (lUnit _)
  FF→FF⁻→FF (push a i) = refl

  FF⁻→FF→FF⁻ : ∀ {ℓ₁ ℓ''' ℓ'''' : Level}
      {A : Pointed ℓ₁} {B : Pointed ℓ'''} {C : Pointed ℓ''''}
      (x : ((A ⋁ B) , inl (pt A)) ⋁ C)  → FF⁻ (FF x) ≡ x
  FF⁻→FF→FF⁻ (inl (inl x)) = refl
  FF⁻→FF→FF⁻ (inl (inr x)) = refl
  FF⁻→FF→FF⁻ (inl (push a i)) = refl
  FF⁻→FF→FF⁻ (inr x) = refl
  FF⁻→FF→FF⁻ (push a i) k = h k i
    where
    h : cong FF⁻ (push a ∙ cong inr (push tt)) ≡ push a
    h = cong-∙ FF⁻ (push a) (cong inr (push a))
     ∙∙ assoc _ _ _
     ∙∙ cong (_∙ push a) (rCancel _)
      ∙ sym (lUnit _)

  ∨-assoc : ∀ {ℓ₁ ℓ''' ℓ'''' : Level}
      (A : Pointed ℓ₁) (B : Pointed ℓ''') (C : Pointed ℓ'''') →
      Iso (((A ⋁ B) , inl (pt A)) ⋁ C)
          (A ⋁ ((B ⋁ C) , inl (pt B)))
  Iso.fun (∨-assoc A B C) = FF
  Iso.inv (∨-assoc A B C) = FF⁻
  Iso.rightInv (∨-assoc A B C) = FF→FF⁻→FF
  Iso.leftInv (∨-assoc A B C) = FF⁻→FF→FF⁻

    {-
    i = i0 ⊢ cong f (cong inl (coherence2 a) ∙ push (Iso.inv is1 a)) j
i = i1 ⊢ push a j
j = i0 ⊢ inl (Iso.rightInv is2 (∧-map a) i)
j = i1 ⊢ inr tt
    -}


--   s : Iso (A ⊚ ((B ⊚ C) , inl tt)) (((A ⊚ B) , inl tt) ⊚ C)
--   Iso.fun s = {!!}
--   Iso.inv s = {!!}
--   Iso.rightInv s = {!!}
--   Iso.leftInv s = {!!}


-- -- module _ {ℓ'' : Level} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') where
-- --   assocFun : ((A ⋀' B) , (incl (pt A) (pt B))) ⋀' C
-- --            → A ⋀' (B ⋀' C , incl (pt B) (pt C))
-- --   assocFun (incl (incl x x₁) y) = incl x (incl x₁ y)
-- --   assocFun (incl (pathl a i) y) = (cong (incl a) (pathr y) ∙∙ pathl a ∙∙ sym (pathr (incl (pt B) y))) i
-- --   assocFun (incl (pathr b i) y) = (pathr (incl b y) ∙ cong (incl (pt A)) (sym (pathr y))) i
-- --   assocFun (incl (pathlCoh i j) y) = {!!}
-- --   assocFun (incl (pathrCoh i j) y) = {!!}
-- --   assocFun (pathl (incl x x₁) i) = {!!}
-- --   assocFun (pathl (pathl a i₁) i) = {!!}
-- --   assocFun (pathl (pathr b i₁) i) = {!!}
-- --   assocFun (pathl (pathlCoh i₁ i₂) i) = {!!}
-- --   assocFun (pathl (pathrCoh i₁ i₂) i) = {!!}
-- --   assocFun (pathr b i) =
-- --     {!Goal: A ⋀' ((B ⋀' C) , incl (pt B) (pt C))
-- -- ———— Boundary ——————————————————————————————————————————————
-- -- i = i0 ⊢ incl (pt A) (incl b y)
-- -- i = i1 ⊢ incl (pt A) (incl (pt B) y)!}
-- --   assocFun (pathlCoh i i₁) = {!!}
-- --   assocFun (pathrCoh i i₁) = {!!}

-- -- module _ (A : Pointed ℓ) (B : Pointed ℓ') where
-- --   smashFun : (A ⋀' B) → (Smash A B)
-- --   smashFun (incl x y) = proj x y
-- --   smashFun (pathl a i) = pivotr a (pt A) i
-- --   smashFun (pathr b i) = pivotl b (pt B) i
-- --   smashFun (pathlCoh i j) = rCancel (gluel (pt A)) i j
-- --   smashFun (pathrCoh i j) = rCancel (gluer (pt B)) i j
  
-- --   smashFun⁻ : (Smash A B) → A ⋀' B
-- --   smashFun⁻ basel = incl (pt A) (pt B)
-- --   smashFun⁻ baser = incl (pt A) (pt B)
-- --   smashFun⁻ (proj x y) = incl x y
-- --   smashFun⁻ (gluel a i) = pathl a i
-- --   smashFun⁻ (gluer b i) = pathr b i

-- --   sectSmashFun : section smashFun smashFun⁻
-- --   sectSmashFun basel = gluel (pt A)
-- --   sectSmashFun baser = gluer (pt B)
-- --   sectSmashFun (proj x y) = refl
-- --   sectSmashFun (gluel a i) j = compPath-filler (gluel a) (sym (gluel (pt A))) (~ j) i
-- --   sectSmashFun (gluer b i) j = compPath-filler (gluer b) (sym (gluer (pt B))) (~ j) i

-- --   retrSmashFun : retract smashFun smashFun⁻
-- --   retrSmashFun (incl x x₁) = refl
-- --   retrSmashFun (pathl a i) k = help k i
-- --     module _ where
-- --     help : cong smashFun⁻ (cong smashFun (pathl a)) ≡ pathl a
-- --     help = congFunct smashFun⁻ (gluel a) (sym (gluel (pt A))) ∙ cong (cong smashFun⁻ (gluel a) ∙_) (cong sym pathlCoh) ∙ sym (rUnit _)
-- --   retrSmashFun (pathr b i) k = help2 k i
-- --     module _ where
-- --     help2 : cong smashFun⁻ (cong smashFun (pathr b)) ≡ pathr b
-- --     help2 = congFunct smashFun⁻ (gluer b) (sym (gluer (pt B)))
-- --          ∙ cong (cong smashFun⁻ (gluer b) ∙_) (cong sym pathrCoh)
-- --          ∙ sym (rUnit _)
-- --   retrSmashFun (pathlCoh i j) k = main i j k
-- --     where

-- --     h = help (pt A) i0 i0
-- --     main : PathP (λ i → PathP (λ j → smashFun⁻ (smashFun (pathlCoh i j)) ≡ pathlCoh i j)
-- --                  refl refl)
-- --                  (λ j k → h k j) refl
-- --     main i j k =
-- --       hcomp (λ r → λ { (i = i0) → compPath-filler' (congFunct smashFun⁻ (gluel (pt A)) (sym (gluel (pt A))))
-- --                                                      (cong (cong smashFun⁻ (gluel (pt A)) ∙_) (cong sym pathlCoh) ∙ sym (rUnit _)) r k j
-- --                       ; (i = i1) → incl (pt A) (pt B)
-- --                       ; (j = i0) → incl (pt A) (pt B)
-- --                       ; (j = i1) → incl (pt A) (pt B)
-- --                       ; (k = i0) → rCancelPathP (gluel (pt A)) smashFun⁻ (~ r) i j
-- --                       ; (k = i1) → pathlCoh i j})
-- --             (mainGen (pathl (pt A)) (sym (pathlCoh)) i j k)
-- --   retrSmashFun (pathrCoh i j) k =
-- --     hcomp (λ r → λ {(i = i0) → compPath-filler' (congFunct smashFun⁻ (gluer (pt B)) (sym (gluer (pt B))))
-- --                                                   (cong (cong smashFun⁻ (gluer (pt B)) ∙_) (cong sym pathrCoh) ∙ sym (rUnit _)) r k j
-- --                    ; (i = i1) → incl (pt A) (pt B)
-- --                    ; (j = i0) → incl (pt A) (pt B)
-- --                    ; (j = i1) → incl (pt A) (pt B)
-- --                    ; (k = i0) → rCancelPathP (gluer (pt B)) smashFun⁻ (~ r) i j
-- --                    ; (k = i1) → pathrCoh i j})
-- --           (mainGen (pathr (pt B)) (sym (pathrCoh)) i j k)

-- --   smashIso : Iso (A ⋀' B) (Smash A B)
-- --   Iso.fun smashIso = smashFun
-- --   Iso.inv smashIso = smashFun⁻
-- --   Iso.rightInv smashIso = sectSmashFun
-- --   Iso.leftInv smashIso = retrSmashFun
