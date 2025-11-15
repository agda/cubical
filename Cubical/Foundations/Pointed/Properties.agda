module Cubical.Foundations.Pointed.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓA ℓB ℓC ℓD : Level

-- the default pointed Π-type: A is pointed, and B has a base point in the chosen fiber
Π∙ : (A : Pointed ℓ) (B : typ A → Type ℓ') (ptB : B (pt A)) → Type (ℓ-max ℓ ℓ')
Π∙ A B ptB = Σ[ f ∈ ((a : typ A) → B a) ] f (pt A) ≡ ptB

-- the unpointed Π-type becomes a pointed type if the fibers are all pointed
Πᵘ∙ : (A : Type ℓ) (B : A → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
Πᵘ∙ A B .fst = ∀ a → typ (B a)
Πᵘ∙ A B .snd a = pt (B a)

-- if the base and all fibers are pointed, we have the pointed pointed Π-type
Πᵖ∙ : (A : Pointed ℓ) (B : typ A → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
Πᵖ∙ A B .fst = Π∙ A (typ ∘ B) (pt (B (pt A)))
Πᵖ∙ A B  .snd .fst a = pt (B a)
Πᵖ∙ A B  .snd .snd = refl

-- the default pointed Σ-type is just the Σ-type, but as a pointed type
Σ∙ : (A : Pointed ℓ) (B : typ A → Type ℓ') (ptB : B (pt A)) → Pointed (ℓ-max ℓ ℓ')
Σ∙ A B ptB .fst = Σ[ a ∈ typ A ] B a
Σ∙ A B ptB .snd .fst = pt A
Σ∙ A B ptB .snd .snd = ptB

-- version if B is a family of pointed types
Σᵖ∙ : (A : Pointed ℓ) (B : typ A → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
Σᵖ∙ A B = Σ∙ A (typ ∘ B) (pt (B (pt A)))

_×∙_ : (A∙ : Pointed ℓ) (B∙ : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
(A∙ ×∙ B∙) .fst = (typ A∙) × (typ B∙)
(A∙ ×∙ B∙) .snd .fst = pt A∙
(A∙ ×∙ B∙) .snd .snd = pt B∙

-- composition of pointed maps
_∘∙_ : {A : Pointed ℓA} {B : Pointed ℓB} {C : Pointed ℓC}
       (g : B →∙ C) (f : A →∙ B) → (A →∙ C)
((g , g∙) ∘∙ (f , f∙)) .fst x = g (f  x)
((g , g∙) ∘∙ (f , f∙)) .snd = (cong g f∙) ∙ g∙

-- post composition
post∘∙ : ∀ {ℓX ℓ ℓ'} (X : Pointed ℓX) {A : Pointed ℓ} {B : Pointed ℓ'}
  → (A →∙ B) → ((X →∙ A ∙) →∙ (X →∙ B ∙))
post∘∙ X f .fst g = f ∘∙ g
post∘∙ X f .snd =
  ΣPathP
    ( (funExt λ _ → f .snd)
    , (sym (lUnit (f .snd)) ◁ λ i j → f .snd (i ∨ j)))

-- pointed identity
id∙ : (A : Pointed ℓA) → (A →∙ A)
id∙ A .fst x = x
id∙ A .snd = refl

-- constant pointed map
const∙ : (A : Pointed ℓA) (B : Pointed ℓB) → (A →∙ B)
const∙ _ B .fst _ = B .snd
const∙ _ B .snd = refl

-- left identity law for pointed maps
∘∙-idˡ : {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B) → f ∘∙ id∙ A ≡ f
∘∙-idˡ f = ΣPathP ( refl , (lUnit (f .snd)) ⁻¹ )

-- right identity law for pointed maps
∘∙-idʳ : {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B) → id∙ B ∘∙ f ≡ f
∘∙-idʳ f = ΣPathP ( refl , (rUnit (f .snd)) ⁻¹ )

-- associativity for composition of pointed maps
∘∙-assoc : {A : Pointed ℓA} {B : Pointed ℓB} {C : Pointed ℓC} {D : Pointed ℓD}
           (h : C →∙ D) (g : B →∙ C) (f : A →∙ B)
           → (h ∘∙ g) ∘∙ f ≡ h ∘∙ (g ∘∙ f)
∘∙-assoc (h , h∙) (g , g∙) (f , f∙) = ΣPathP (refl , q)
  where
    q : (cong (h ∘ g) f∙) ∙ (cong h g∙ ∙ h∙) ≡ cong h (cong g f∙ ∙ g∙) ∙ h∙
    q = ( (cong (h ∘ g) f∙) ∙ (cong h g∙ ∙ h∙)
        ≡⟨ refl ⟩
        (cong h (cong g f∙)) ∙ (cong h g∙ ∙ h∙)
        ≡⟨ assoc (cong h (cong g f∙)) (cong h g∙) h∙ ⟩
        (cong h (cong g f∙) ∙ cong h g∙) ∙ h∙
        ≡⟨ cong (λ p → p ∙ h∙) ((cong-∙ h (cong g f∙) g∙) ⁻¹) ⟩
        (cong h (cong g f∙ ∙ g∙) ∙ h∙) ∎ )

module _ {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B) where
  isInIm∙ : (x : typ B) → Type (ℓ-max ℓ ℓ')
  isInIm∙ x = Σ[ z ∈ typ A ] fst f z ≡ x

  isInKer∙ : (x : fst A) → Type ℓ'
  isInKer∙ x = fst f x ≡ snd B

private module _ {ℓA ℓB ℓC : Level} (A : Pointed ℓA) (B : Pointed ℓB) (C : Pointed ℓC) (e : A ≃∙ B) where
  toEq : (A →∙ C) → (B →∙ C)
  toEq = _∘∙ ≃∙map (invEquiv∙ e)

  fromEq : B →∙ C → (A →∙ C)
  fromEq = _∘∙ ≃∙map e

  toEq' : (C →∙ A) → C →∙ B
  toEq' = ≃∙map e ∘∙_

  fromEq' : C →∙ B → (C →∙ A)
  fromEq' = ≃∙map (invEquiv∙ e) ∘∙_

pre∘∙equiv : ∀ {ℓA ℓB ℓC} {A : Pointed ℓA} {B : Pointed ℓB} {C : Pointed ℓC}
 → (B ≃∙ C) → Iso (A →∙ B) (A →∙ C)
Iso.fun (pre∘∙equiv {A = A} {B = B} {C = C} e) = toEq' B C A e
Iso.inv (pre∘∙equiv {A = A} {B = B} {C = C} e) = fromEq' B C A e
Iso.rightInv (pre∘∙equiv {A = A} {B = B} {C = C} e) =
  J (λ ptC p → section (toEq' B (fst C , ptC) A (fst e , p))
                         (fromEq' B (fst C , ptC) A (fst e , p)))
     (uncurry (λ f p → ΣPathP (funExt (λ x → isHAEquiv.rinv (HAe .snd) (f x))
       , ((sym (rUnit _)
        ∙ cong (cong (fst (fst e)))
           λ i → cong (invEq (fst e)) p
           ∙ (lUnit (retEq (fst e) (pt B)) (~ i)))
           ∙ cong-∙ (fst (fst e))
              (cong (invEq (fst e)) p)
              (retEq (fst e) (pt B))
           ∙ refl
         ◁ flipSquare (((λ _ → isHAEquiv.rinv (HAe .snd) (f (pt A)))
                      ∙ refl)
                      ◁ lem _ _ _ _ (cong (isHAEquiv.rinv (HAe .snd)) p
                                  ▷ sym (isHAEquiv.com (HAe .snd) (pt B))))))))
     (snd e)
  where
  HAe = equiv→HAEquiv (fst e)
  lem : ∀ {ℓ} {A : Type ℓ} {x y z w : A}
      (p : x ≡ y) (q : y ≡ z) (r : x ≡ w) (l : w ≡ z)
    → PathP (λ i → p i ≡ l i) r q
    → PathP (λ i → (p ∙ q) i ≡ l i) r refl
  lem p q r l P i j =
    hcomp (λ k → λ{ (i = i0) → r j
                   ; (i = i1) → q (j ∨ k)
                   ; (j = i1) → l i})
          (P i j)
Iso.leftInv (pre∘∙equiv {A = A} {B = B} {C = C} e) =
  J (λ pt p → retract (toEq' B (fst C , pt) A (fst e , p))
                       (fromEq' B (fst C , pt) A (fst e , p)))
    (uncurry (λ f →
      J (λ ptB p
       → fromEq' (fst B , ptB)
                  (fst C , fst (fst e) ptB) A (fst e , refl)
           (toEq' (fst B , ptB)
                  (fst C , fst (fst e) ptB) A (fst e , refl) (f , p))
         ≡ (f , p))
         (ΣPathP
          (funExt (λ x → retEq (fst e) (f x))
         , ((cong₂ _∙_ ((λ i → cong (invEq (fst e)) (lUnit refl (~ i))))
                       (sym (lUnit _) ∙ λ _ → retEq (fst e) (f (pt A)))
          ∙ sym (lUnit _))
         ◁ λ i j → retEq (fst e) (f (pt A)) (i ∨ j))))))
    (snd e)

post∘∙equiv : ∀ {ℓA ℓB ℓC} {A : Pointed ℓA} {B : Pointed ℓB} {C : Pointed ℓC}
  → (A ≃∙ B) → Iso (A →∙ C) (B →∙ C)
Iso.fun (post∘∙equiv {A = A} {B = B} {C = C} e) = toEq A B C e
Iso.inv (post∘∙equiv {A = A} {B = B} {C = C} e) = fromEq A B C e
Iso.rightInv (post∘∙equiv {A = A}{B = B , ptB} {C = C} e) =
  J (λ pt p → section (toEq A (B , pt) C (fst e , p))
                        (fromEq A (B , pt) C (fst e , p)))
     (uncurry (λ f →
       J (λ ptC p → toEq A (B , fst (fst e) (pt A)) (fst C , ptC) (fst e , refl)
                      (fromEq A (B , fst (fst e) (pt A)) (fst C , ptC) (fst e , refl)
                        (f , p))
                   ≡ (f , p))
         (ΣPathP (funExt (λ x → cong f (isHAEquiv.rinv (snd HAe) x))
           , (cong₂ _∙_
               (λ i → cong f (cong (fst (fst e)) (lUnit (retEq (fst e) (pt A)) (~ i))))
               (sym (rUnit refl))
           ∙ sym (rUnit _)
           ∙ cong (cong f) (isHAEquiv.com (snd HAe) (pt A)))
         ◁ λ i j → f (isHAEquiv.rinv (snd HAe) (fst HAe (pt A)) (i ∨ j))))))
     (snd e)
  where
  HAe = equiv→HAEquiv (fst e)
Iso.leftInv (post∘∙equiv {A = A} {B = B , ptB} {C = C} e) =
  J (λ pt p → retract (toEq A (B , pt) C (fst e , p))
                        (fromEq A (B , pt) C (fst e , p)))
     (uncurry (λ f → J (λ ptC y →
       fromEq A (B , fst (fst e) (pt A)) (fst C , ptC) (fst e , refl)
        (toEq A (B , fst (fst e) (pt A)) (fst C , ptC) (fst e , refl)
        (f , y))
      ≡ (f , y))
      (ΣPathP (funExt (λ x → cong f (retEq (fst e) x))
            , (sym (lUnit _)
              ∙ sym (rUnit _)
              ∙ cong (cong f) (sym (lUnit _))
              ∙ (λ _ → cong f (retEq (fst e) (pt A)))
             ◁ λ i j → f (retEq (fst e) (pt A) (i ∨ j)))))))
     (snd e)

flip→∙∙ : {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓA}
  → (A →∙ (B →∙ C ∙)) → B →∙ (A →∙ C ∙)
fst (fst (flip→∙∙ f) x) a = fst f a .fst x
snd (fst (flip→∙∙ f) x) i = snd f i .fst x
fst (snd (flip→∙∙ f) i) a = fst f a .snd i
snd (snd (flip→∙∙ f) i) j = snd f j .snd i

flip→∙∙Iso : {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓA}
  → Iso (A →∙ (B →∙ C ∙)) (B →∙ (A →∙ C ∙))
Iso.fun flip→∙∙Iso = flip→∙∙
Iso.inv flip→∙∙Iso = flip→∙∙
Iso.rightInv flip→∙∙Iso _ = refl
Iso.leftInv flip→∙∙Iso _ = refl

≃∙→ret/sec∙ : ∀ {ℓ} {A B : Pointed ℓ}
  (f : A ≃∙ B) → ((≃∙map (invEquiv∙ f) ∘∙ ≃∙map f) ≡ idfun∙ A)
                × (≃∙map f ∘∙ ≃∙map (invEquiv∙ f) ≡ idfun∙ B)
≃∙→ret/sec∙ {A = A} {B = B} =
  Equiv∙J (λ A f → ((≃∙map (invEquiv∙ f) ∘∙ ≃∙map f) ≡ idfun∙ A)
                × (≃∙map f ∘∙ ≃∙map (invEquiv∙ f) ≡ idfun∙ B))
          ((ΣPathP (refl , sym (lUnit _) ∙ sym (rUnit refl)))
         , (ΣPathP (refl , sym (rUnit _) ∙ sym (rUnit refl))))

pointedSecIso : ∀ {ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} (Q : fst A → Pointed ℓ'')
  → Iso ((a : fst A) → Q a →∙ B)
         (Σ[ F ∈ (Σ (fst A) (fst ∘ Q) → fst B) ]
           ((a : fst A) → F (a , pt (Q a)) ≡ pt B))
Iso.fun (pointedSecIso Q) F = (λ x → F (fst x) .fst (snd x)) , (λ x → F x .snd)
Iso.inv (pointedSecIso Q) F a = (fst F ∘ (a ,_)) , snd F a
Iso.rightInv (pointedSecIso Q) F = refl
Iso.leftInv (pointedSecIso Q) F = refl

compPathrEquiv∙ : {A : Type ℓ} {a b c : A} {q : a ≡ b} (p : b ≡ c)
    → ((a ≡ b) , q) ≃∙ ((a ≡ c) , q ∙ p)
fst (compPathrEquiv∙ p) = compPathrEquiv p
snd (compPathrEquiv∙ p) = refl

compPathlEquiv∙ : {A : Type ℓ} {a b c : A} {q : b ≡ c} (p : a ≡ b)
    → ((b ≡ c) , q) ≃∙ ((a ≡ c) , p ∙ q)
fst (compPathlEquiv∙ p) = compPathlEquiv p
snd (compPathlEquiv∙ p) = refl

-- Pointed version of Σ-cong-equiv-snd
Σ-cong-equiv-snd∙ : ∀ {ℓ ℓ'} {A : Type ℓ} {B₁ B₂ : A → Type ℓ'}
  → {a : A} {b₁ : B₁ a} {b₂ : B₂ a}
  → (e : ∀ a → B₁ a ≃ B₂ a)
  → fst (e a) b₁ ≡ b₂
  → Path (Pointed _) (Σ∙ (A , a) B₁ b₁) (Σ∙ (A , a) B₂ b₂)
Σ-cong-equiv-snd∙ e p = ua∙ (Σ-cong-equiv-snd e) (ΣPathP (refl , p))

-- a pointed map is constant iff its non-pointed part is constant
constantPointed≡ : {A B : Pointed ℓ} (f : A →∙ B)
                 → fst f ≡ fst (const∙ A B) → f ≡ const∙ A B
constantPointed≡ {A = A} {B = B , b} f Hf i =
  (λ x → ((λ j → Hf j x) ∙∙ (λ j → Hf (~ j) (pt A)) ∙∙ (snd f)) i)
  , λ j → hcomp (λ k
    → λ { (i = i0) → invSides-filler (λ i → Hf i (pt A)) (λ i → snd f i) k (~ j)
         ; (i = i1) → snd f k
         ; (j = i1) → snd f k })
    (Hf ((~ i) ∧ (~ j)) (pt A))
