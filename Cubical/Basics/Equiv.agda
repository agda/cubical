{-

Theory about equivalences (definitions are in Core/Glue.agda)

- isEquiv is a proposition ([isPropIsEquiv])
- Any isomorphism is an equivalence ([isoToEquiv])
- Equivalence induction ([EquivJ])

-}
{-# OPTIONS --cubical #-}
module Cubical.Basics.Equiv where

open import Cubical.Core.Everything

open import Cubical.Basics.NTypes

-- Proof using isPropIsContr. This is slow and the direct proof below is better
isPropIsEquiv' : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → isProp (isEquiv f)
equiv-proof (isPropIsEquiv' f u0 u1 i) y =
  isPropIsContr (u0 .equiv-proof y) (u1 .equiv-proof y) i

-- Direct proof that computes quite ok (can be optimized further if
-- necessary, see:
-- https://github.com/mortberg/cubicaltt/blob/pi4s3_dimclosures/examples/brunerie2.ctt#L562
isPropIsEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → isProp (isEquiv f)
equiv-proof (isPropIsEquiv f p q i) y =
  let p2 = p .equiv-proof y .snd
      q2 = q .equiv-proof y .snd
  in p2 (q .equiv-proof y .fst) i
   , λ w j → hcomp (λ k → λ { (i = i0) → p2 w j
                            ; (i = i1) → q2 w (j ∨ ~ k)
                            ; (j = i0) → p2 (q2 w (~ k)) i
                            ; (j = i1) → w })
                   (p2 w (i ∨ j))

equivEq : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (e f : A ≃ B) → (h : e .fst ≡ f .fst) → e ≡ f
equivEq e f h = λ i → (h i) , isProp→PathP isPropIsEquiv h (e .snd) (f .snd) i

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (g : B → A)
         (s : (y : B) → f (g y) ≡ y) (t : (x : A) → g (f x) ≡ x) where

  private
    module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
      fill0 : I → I → A
      fill0 i = hfill (λ k → λ { (i = i1) → t x0 k; (i = i0) → g y })
                      (inc (g (p0 (~ i))))

      fill1 : I → I → A
      fill1 i = hfill (λ k → λ { (i = i1) → t x1 k; (i = i0) → g y })
                      (inc (g (p1 (~ i))))

      fill2 : I → I → A
      fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1; (i = i0) → fill0 k i1 })
                      (inc (g y))

      p : x0 ≡ x1
      p i = fill2 i i1

      sq : I → I → A
      sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                              ; (i = i0) → fill0 j (~ k)
                              ; (j = i1) → t (fill2 i i1) (~ k)
                              ; (j = i0) → g y })
                     (fill2 i j)

      sq1 : I → I → B
      sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 (~ j)) k
                               ; (i = i0) → s (p0 (~ j)) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k })
                      (f (sq i j))

      lemIso : (x0 , p0) ≡ (x1 , p1)
      lemIso i .fst = p i
      lemIso i .snd = λ j → sq1 i (~ j)

  isoToIsEquiv : isEquiv f
  isoToIsEquiv .equiv-proof y .fst .fst = g y
  isoToIsEquiv .equiv-proof y .fst .snd = s y
  isoToIsEquiv .equiv-proof y .snd z = lemIso y (g y) (fst z) (s y) (snd z)

  isoToEquiv : A ≃ B
  isoToEquiv = _ , isoToIsEquiv

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (w : A ≃ B) where
  invEq : (y : B) → A
  invEq y = fst (fst (snd w .equiv-proof y))

  secEq : (x : A) → invEq (fst w x) ≡ x
  secEq x = λ i → fst (snd (snd w .equiv-proof (fst w x)) (x , (λ j → fst w x)) i)

  retEq : (y : B) → fst w (invEq y) ≡ y
  retEq y = λ i → snd (fst (snd w .equiv-proof y)) i

isoToPath : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (g : B → A)
  (s : (y : B) → f (g y) ≡ y) (t : (x : A) → g (f x) ≡ x) → A ≡ B
isoToPath f g s t = ua (isoToEquiv f g s t)

invEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → B ≃ A
invEquiv f = isoToEquiv (invEq f) (fst f) (secEq f) (retEq f)

-- module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}  where
--   invEquivInvol : (f : A ≃ B) → invEquiv (invEquiv f) ≡ f
--   invEquivInvol f i .fst = fst f
--   invEquivInvol f i .snd = propIsEquiv (fst f) (snd (invEquiv (invEquiv f))) (snd f) i


contrSinglEquiv : ∀ {ℓ} {A B : Set ℓ} (e : A ≃ B) → (B , idEquiv B) ≡ (A , e)
contrSinglEquiv {A = A} {B = B} e =
  isContr→isProp (EquivContr B) (B , idEquiv B) (A , e)

-- Equivalence induction
EquivJ : ∀ {ℓ ℓ′} (P : (A B : Set ℓ) → (e : B ≃ A) → Set ℓ′)
         → (r : (A : Set ℓ) → P A A (idEquiv A))
         → (A B : Set ℓ) → (e : B ≃ A) → P A B e
EquivJ P r A B e = subst (λ x → P A (x .fst) (x .snd)) (contrSinglEquiv e) (r A)

-- Eliminate equivalences by just looking at the underlying function
elimEquivFun : ∀ {ℓ} (B : Set ℓ) (P : (A : Set ℓ) → (A → B) → Set ℓ)
             → (r : P B (λ x → x))
             → (A : Set ℓ) → (e : A ≃ B) → P A (e .fst)
elimEquivFun B P r a e = subst (λ x → P (x .fst) (x .snd .fst)) (contrSinglEquiv e) r


-- TODO: move to a new file and clean!
idtoeqv : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
idtoeqv {ℓ} {A = A} p = pathToEquiv {ℓ = λ _ → ℓ} (λ i → p i)

[idtoeqv]refl=id : ∀ {ℓ} {A : Set ℓ} → idtoeqv refl ≡ idEquiv A
[idtoeqv]refl=id {A = A} = equivEq _ _ (λ i x → transp (λ j → A) i x)

module UAEquiv {ℓ : Level} 
  -- To derive univalence it's sufficient to provide the following three
  -- maps, regardless of the implementation.
    (ua : ∀ {A B : Set ℓ} → A ≃ B → A ≡ B)
    (uaid=id : ∀ {A : Set ℓ} → ua (idEquiv A) ≡ refl)
    (uaβ : ∀ {A B : Set ℓ} → (e : A ≃ B) (a : A) → transp (λ i → ua e i) i0 a ≡ e .fst a) where

  lemma' : {A B : Set ℓ} (e : A ≃ B) → idtoeqv (ua e) .fst ≡ e .fst
  lemma' {A} e = λ i x → uaβ e x i
  
  [ua∘idtoeqv]refl≡refl : {A : Set ℓ} → ua (idtoeqv {A = A} refl) ≡ refl
  [ua∘idtoeqv]refl≡refl {A = A} = compPath (cong ua [idtoeqv]refl=id) uaid=id

  univEquiv : {A B : Set ℓ} → isEquiv {A = A ≡ B} {B = A ≃ B} idtoeqv
  univEquiv {A} {B} = 
     isoToIsEquiv idtoeqv (ua {A = A} {B = B})
                            (λ y → equivEq _ _ (lemma' y))
               (J (λ y p → ua (idtoeqv p) ≡ p) [ua∘idtoeqv]refl≡refl)

uaid=id : ∀ {ℓ} {A : Set ℓ} → (ua (idEquiv A)) ≡ (λ i → A)
uaid=id {A = A} = λ j → λ i → Glue A {φ = (~ i ∨ i) ∨ j} (λ _ → A , idEquiv A .fst , idEquiv A .snd)

uaβ : ∀ {ℓ} {A B : Set ℓ} → (e : A ≃ B) (a : A) → transp (λ i → ua e i) i0 a ≡ e .fst a
uaβ e a = {!!}

univalence : ∀ {ℓ} {A B : Set ℓ} → (A ≡ B) ≃ (A ≃ B)
univalence .fst = idtoeqv
univalence .snd = UAEquiv.univEquiv ua uaid=id uaβ
