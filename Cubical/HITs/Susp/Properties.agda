{-# OPTIONS --safe #-}
module Cubical.HITs.Susp.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.HITs.Join
open import Cubical.HITs.Susp.Base
open import Cubical.Homotopy.Loopspace

private
  variable
    ℓ : Level

open Iso

Susp-iso-joinBool : ∀ {ℓ} {A : Type ℓ} → Iso (Susp A) (join A Bool)
fun Susp-iso-joinBool north = inr true
fun Susp-iso-joinBool south = inr false
fun Susp-iso-joinBool (merid a i) = (sym (push a true) ∙ push a false) i
inv Susp-iso-joinBool (inr true ) = north
inv Susp-iso-joinBool (inr false) = south
inv Susp-iso-joinBool (inl _) = north
inv Susp-iso-joinBool (push a true  i) = north
inv Susp-iso-joinBool (push a false i) = merid a i
rightInv Susp-iso-joinBool (inr true ) = refl
rightInv Susp-iso-joinBool (inr false) = refl
rightInv Susp-iso-joinBool (inl a) = sym (push a true)
rightInv Susp-iso-joinBool (push a true  i) j = push a true (i ∨ ~ j)
rightInv Susp-iso-joinBool (push a false i) j
  = hcomp (λ k → λ { (i = i0) → push a true (~ j)
                   ; (i = i1) → push a false k
                   ; (j = i1) → push a false (i ∧ k) })
          (push a true (~ i ∧ ~ j))
leftInv Susp-iso-joinBool north = refl
leftInv Susp-iso-joinBool south = refl
leftInv (Susp-iso-joinBool {A = A}) (merid a i) j
  = hcomp (λ k → λ { (i = i0) → transp (λ _ → Susp A) (k ∨ j) north
                   ; (i = i1) → transp (λ _ → Susp A) (k ∨ j) (merid a k)
                   ; (j = i1) → merid a (i ∧ k) })
          (transp (λ _ → Susp A) j north)

Susp≃joinBool : ∀ {ℓ} {A : Type ℓ} → Susp A ≃ join A Bool
Susp≃joinBool = isoToEquiv Susp-iso-joinBool

Susp≡joinBool : ∀ {ℓ} {A : Type ℓ} → Susp A ≡ join A Bool
Susp≡joinBool = isoToPath Susp-iso-joinBool

congSuspIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Iso A B → Iso (Susp A) (Susp B)
fun (congSuspIso is) = suspFun (fun is)
inv (congSuspIso is) = suspFun (inv is)
rightInv (congSuspIso is) north = refl
rightInv (congSuspIso is) south = refl
rightInv (congSuspIso is) (merid a i) j = merid (rightInv is a j) i
leftInv (congSuspIso is) north = refl
leftInv (congSuspIso is) south = refl
leftInv (congSuspIso is) (merid a i) j = merid (leftInv is a j) i

congSuspEquiv : ∀ {ℓ} {A B : Type ℓ} → A ≃ B → Susp A ≃ Susp B
congSuspEquiv {ℓ} {A} {B} h = isoToEquiv (congSuspIso (equivToIso h))

suspToPropElim : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Susp A → Type ℓ'} (a : A)
                 → ((x : Susp A) → isProp (B x))
                 → B north
                 → (x : Susp A) → B x
suspToPropElim a isProp Bnorth north = Bnorth
suspToPropElim {B = B} a isProp Bnorth south = subst B (merid a) Bnorth
suspToPropElim {B = B} a isProp Bnorth (merid a₁ i) =
  isOfHLevel→isOfHLevelDep 1 isProp Bnorth (subst B (merid a) Bnorth) (merid a₁) i

suspToPropElim2 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Susp A → Susp A → Type ℓ'} (a : A)
                 → ((x y : Susp A) → isProp (B x y))
                 → B north north
                 → (x y : Susp A) → B x y
suspToPropElim2 _ _ Bnorth north north = Bnorth
suspToPropElim2 {B = B} a _ Bnorth north south = subst (B north) (merid a) Bnorth
suspToPropElim2 {B = B} a isprop Bnorth north (merid x i) =
  isProp→PathP (λ i → isprop north (merid x i))
               Bnorth (subst (B north) (merid a) Bnorth) i
suspToPropElim2 {B = B} a _ Bnorth south north = subst (λ x → B x north) (merid a) Bnorth
suspToPropElim2 {B = B} a _ Bnorth south south = subst (λ x → B x x) (merid a) Bnorth
suspToPropElim2 {B = B} a isprop Bnorth south (merid x i) =
  isProp→PathP (λ i → isprop south (merid x i))
               (subst (λ x → B x north) (merid a) Bnorth)
               (subst (λ x → B x x) (merid a) Bnorth) i
suspToPropElim2 {B = B} a isprop Bnorth (merid x i) north =
  isProp→PathP (λ i → isprop (merid x i) north)
               Bnorth (subst (λ x → B x north) (merid a) Bnorth) i
suspToPropElim2 {B = B} a isprop Bnorth (merid x i) south =
  isProp→PathP (λ i → isprop (merid x i) south)
               (subst (B north) (merid a) Bnorth)
               (subst (λ x → B x x) (merid a) Bnorth) i
suspToPropElim2 {B = B} a isprop Bnorth (merid x i) (merid y j) =
  isSet→SquareP (λ i j → isOfHLevelSuc 1 (isprop _ _))
     (isProp→PathP (λ i₁ → isprop north (merid y i₁)) Bnorth
                   (subst (B north) (merid a) Bnorth))
     (isProp→PathP (λ i₁ → isprop south (merid y i₁))
                   (subst (λ x₁ → B x₁ north) (merid a) Bnorth)
                   (subst (λ x₁ → B x₁ x₁) (merid a) Bnorth))
     (isProp→PathP (λ i₁ → isprop (merid x i₁) north) Bnorth
                   (subst (λ x₁ → B x₁ north) (merid a) Bnorth))
     (isProp→PathP (λ i₁ → isprop (merid x i₁) south)
                   (subst (B north) (merid a) Bnorth)
                   (subst (λ x₁ → B x₁ x₁) (merid a) Bnorth)) i j
{- Clever proof:
suspToPropElim2 a isProp Bnorth =
  suspToPropElim a (λ x → isOfHLevelΠ 1 λ y → isProp x y)
                   (suspToPropElim a (λ x → isProp north x) Bnorth)
-}

funSpaceSuspIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
                   → Iso (Σ[ x ∈ B ] Σ[ y ∈ B ] (A → x ≡ y)) (Susp A → B)
Iso.fun funSpaceSuspIso (x , y , f) north = x
Iso.fun funSpaceSuspIso (x , y , f) south = y
Iso.fun funSpaceSuspIso (x , y , f) (merid a i) = f a i
Iso.inv funSpaceSuspIso f = (f north) , (f south , (λ x → cong f (merid x)))
Iso.rightInv funSpaceSuspIso f = funExt λ {north → refl
                                             ; south → refl
                                             ; (merid a i) → refl}
Iso.leftInv funSpaceSuspIso _ = refl

toSusp : (A : Pointed ℓ) → typ A → typ (Ω (Susp∙ (typ A)))
toSusp A x = merid x ∙ merid (pt A) ⁻¹

toSuspPointed : (A : Pointed ℓ) → A →∙ Ω (Susp∙ (typ A))
fst (toSuspPointed A) = toSusp A
snd (toSuspPointed A) = rCancel (merid (pt A))

module _ {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} where
  fromSusp→toΩ : Susp∙ (typ A) →∙ B → (A →∙ Ω B)
  fst (fromSusp→toΩ f) x = sym (snd f) ∙∙ cong (fst f) (toSusp A x) ∙∙ snd f
  snd (fromSusp→toΩ f) =
    cong (sym (snd f) ∙∙_∙∙ (snd f))
          (cong (cong (fst f))
           (rCancel (merid (pt A))))
       ∙ ∙∙lCancel (snd f)

  toΩ→fromSusp : A →∙ Ω B → Susp∙ (typ A) →∙ B
  fst (toΩ→fromSusp f) north = pt B
  fst (toΩ→fromSusp f) south = pt B
  fst (toΩ→fromSusp f) (merid a i) = fst f a i
  snd (toΩ→fromSusp f) = refl

  ΩSuspAdjointIso : Iso (A →∙ Ω B) (Susp∙ (typ A) →∙ B)
  fun ΩSuspAdjointIso = toΩ→fromSusp
  inv ΩSuspAdjointIso = fromSusp→toΩ
  rightInv ΩSuspAdjointIso f =
    ΣPathP (funExt
      (λ { north → sym (snd f)
         ; south → sym (snd f) ∙ cong (fst f) (merid (pt A))
         ; (merid a i) j →
           hcomp (λ k → λ { (i = i0) → snd f (~ j ∧ k)
                           ; (i = i1) → compPath-filler'
                                          (sym (snd f))
                                          (cong (fst f) (merid (pt A))) k j
                           ; (j = i1) → fst f (merid a i)})
                 (fst f (compPath-filler (merid a) (sym (merid (pt A))) (~ j) i))})
         , λ i j → snd f (~ i ∨ j))
  leftInv ΩSuspAdjointIso f =
    →∙Homogeneous≡ (isHomogeneousPath _ _)
      (funExt λ x → sym (rUnit _)
             ∙ cong-∙ (fst (toΩ→fromSusp f)) (merid x) (sym (merid (pt A)))
             ∙ cong (fst f x ∙_) (cong sym (snd f))
             ∙ sym (rUnit _))

  IsoΩFunSuspFun : Iso (typ (Ω (A →∙ B ∙))) (Susp∙ (typ A) →∙ B)
  IsoΩFunSuspFun = compIso (ΩfunExtIso A B) ΩSuspAdjointIso

-- inversion
invSusp : ∀ {ℓ} {A : Type ℓ} → Susp A → Susp A
invSusp north = south
invSusp south = north
invSusp (merid a i) = merid a (~ i)

invSusp² : ∀ {ℓ} {A : Type ℓ} (x : Susp A) → invSusp (invSusp x) ≡ x
invSusp² north = refl
invSusp² south = refl
invSusp² (merid a i) = refl

invSuspIso : ∀ {ℓ} {A : Type ℓ} → Iso (Susp A) (Susp A)
fun invSuspIso = invSusp
inv invSuspIso = invSusp
rightInv invSuspIso = invSusp²
leftInv invSuspIso = invSusp²


-- Explicit definition of the iso
-- join (Susp A) B ≃ Susp (join A B)
-- for pointed types A and B. This is useful for obtaining a ``nice'' iso
-- join Sⁿ Sᵐ ≃ Sⁿ⁺ᵐ⁺¹
module _ {A B : Pointed ℓ} where

  private -- some useful fillers
    rinv-filler : (b : typ B) → I → I → I → join (Susp (typ A)) (typ B)
    rinv-filler b i j k =
      hfill (λ k → λ {(i = i0) → push south b (~ k)
                     ; (i = i1) → push north b (~ k ∨ j)
                     ; (j = i0) → push (merid (pt A) (~ i)) b (~ k)
                     ; (j = i1) → push south b (~ k ∨ i)})
            (inS (inr b))
            k

    suspJoin→joinSuspFiller :
      I → I → I → (a : typ A) (b : typ B) → join (Susp (typ A)) (typ B)
    suspJoin→joinSuspFiller i j k a b =
      hfill (λ k → λ {(i = i0) → push north b (~ k)
                     ; (i = i1) → push south b (~ k)
                     ; (j = i0) → push (merid a i) b (~ k)
                     ; (j = i1) → push (merid (pt A) i) b (~ k)})
            (inS (inr b))
            k

    joinSuspFiller :
      I → I → I → (a : typ A) (b : typ B) → Susp (join (typ A) (typ B))
    joinSuspFiller i j k a b =
      hfill (λ k → λ {(i = i0) → merid (push a b (~ k)) j
                     ; (i = i1) → north
                     ; (j = i0) → north
                     ; (j = i1) → merid (push (pt A) b (~ k)) (~ i)})
            (inS (merid (inr b) (~ i ∧ j)))
            k

  suspJoin→joinSusp : Susp (join (typ A) (typ B)) → join (Susp (typ A)) (typ B)
  suspJoin→joinSusp north = inl north
  suspJoin→joinSusp south = inl south
  suspJoin→joinSusp (merid (inl x) i) = inl ((merid x) i)
  suspJoin→joinSusp  (merid (inr x) i) = inl (merid (pt A) i)
  suspJoin→joinSusp  (merid (push a b j) i) = suspJoin→joinSuspFiller i j i1 a b

  joinSusp→suspJoin : join (Susp (typ A)) (typ B) → Susp (join (typ A) (typ B))
  joinSusp→suspJoin (inl north) = north
  joinSusp→suspJoin (inl south) = south
  joinSusp→suspJoin (inl (merid a i)) = merid (inl a) i
  joinSusp→suspJoin (inr x) = north
  joinSusp→suspJoin (push north b i) = north
  joinSusp→suspJoin (push south b i) = merid (inl (pt A)) (~ i)
  joinSusp→suspJoin (push (merid a j) b i) = joinSuspFiller i j i1 a b


  suspJoin→joinSusp→suspJoin : (x : Susp (join (typ A) (typ B)))
    → joinSusp→suspJoin (suspJoin→joinSusp x) ≡ x
  suspJoin→joinSusp→suspJoin north = refl
  suspJoin→joinSusp→suspJoin south = refl
  suspJoin→joinSusp→suspJoin (merid (inl x) i) = refl
  suspJoin→joinSusp→suspJoin (merid (inr x) i) j = merid (push (pt A) x j) i
  suspJoin→joinSusp→suspJoin (merid (push a b j) i) k =
    hcomp (λ r → λ {(i = i0) → north
                   ; (i = i1) → merid (push (snd A) b (k ∧ (~ r ∨ j))) r
                   ; (j = i0) → joinSuspFiller (~ r) i (~ k ∨ r) a b
                   ; (j = i1) → joinSuspFiller (~ r) i (~ k) (pt A) b
                   ; (k = i0) → joinSusp→suspJoin (suspJoin→joinSuspFiller i j r a b)
                   ; (k = i1) → k=i1 i j r})
          north
     where
     k=i1 :
       Cube
         (λ j r → north)
         (λ j r → merid (push (snd A) b (~ r ∨ j)) r)
         (λ i r → joinSuspFiller (~ r) i r a b)
         (λ i r → merid (inr b) (r ∧ i))
         refl
         λ i j → merid (push a b j) i
     k=i1 i j r =
       hcomp (λ k → λ {(i = i0) → north
                      ; (i = i1) → merid (push (snd A) b (~ r ∨ ~ k ∨ j)) r
                      ; (j = i0) → joinSuspFiller (~ r) i (r ∧ k) a b
                      ; (j = i1) → merid (inr b) (r ∧ i)
                      ; (r = i0) → north
                      ; (r = i1) → merid (push a b (~ k ∨ j)) i})
             (merid (inr b) (i ∧ r))

  joinSusp→suspJoin→joinSusp : (x : join (Susp (typ A)) (typ B))
    → suspJoin→joinSusp (joinSusp→suspJoin x) ≡ x
  joinSusp→suspJoin→joinSusp (inl north) = refl
  joinSusp→suspJoin→joinSusp (inl south) = refl
  joinSusp→suspJoin→joinSusp (inl (merid a i)) = refl
  joinSusp→suspJoin→joinSusp (inr x) = push north x
  joinSusp→suspJoin→joinSusp (push north b i) j = push north b (j ∧ i)
  joinSusp→suspJoin→joinSusp (push south b i) j = rinv-filler b i j i1
  joinSusp→suspJoin→joinSusp (push (merid a j) b i) k =
    hcomp (λ r → λ { (j = i0) → push north b (k ∧ i)
                     ; (j = i1) → lem i k r
                     ; (i = i0) → suspJoin→joinSuspFiller j (~ r ∧ ~ k) i1 a b
                     ; (i = i1) → push north b k
                     ; (k = i0) → suspJoin→joinSusp (joinSuspFiller i j r a b)
                     ; (k = i1) → push (merid a j) b i})
          (hcomp (λ r → λ { (j = i0) → push north b (~ r ∨ (k ∧ i))
                     ; (j = i1) → rinv-filler b i k r
                     ; (i = i0) → suspJoin→joinSuspFiller j (~ k) r a b
                     ; (i = i1) → push north b (~ r ∨ k)
                     ; (k = i0) → push (merid (snd A) (~ i ∧ j)) b (~ r)
                     ; (k = i1) → push (merid a j) b (~ r ∨ i)})
                 (inr b))
    where
    lem : Cube (λ k r → inl south)
               (λ k r → push north b k)
               (λ i r → suspJoin→joinSuspFiller (~ i) r i1 (pt A) b)
               (λ i r → push south b i)
               (λ i k → rinv-filler b i k i1)
               λ i k → rinv-filler b i k i1
    lem i k r =
      hcomp (λ j → λ { (r = i0) → rinv-filler b i k j
                     ; (r = i1) → rinv-filler b i k j
                     ; (i = i0) → push south b (~ j)
                     ; (i = i1) → push north b (k ∨ ~ j)
                     ; (k = i0) → suspJoin→joinSuspFiller (~ i) r j (pt A) b
                     ; (k = i1) → push south b (i ∨ ~ j)})
                 (inr b)

  Iso-joinSusp-suspJoin :
    Iso (join (Susp (typ A)) (typ B)) (Susp (join (typ A) (typ B)))
  Iso.fun Iso-joinSusp-suspJoin = joinSusp→suspJoin
  Iso.inv Iso-joinSusp-suspJoin = suspJoin→joinSusp
  Iso.rightInv Iso-joinSusp-suspJoin = suspJoin→joinSusp→suspJoin
  Iso.leftInv Iso-joinSusp-suspJoin = joinSusp→suspJoin→joinSusp

-- interaction between invSusp and toSusp
toSusp-invSusp : (A : Pointed ℓ) (x : Susp (typ A))
  → toSusp (Susp∙ (typ A)) (invSusp x) ≡ sym (toSusp (Susp∙ (typ A)) x)
toSusp-invSusp A north =
  cong (toSusp (Susp∙ (typ A))) (sym (merid (snd A)))
                  ∙∙ rCancel (merid north)
                  ∙∙ cong sym (sym (rCancel (merid north)))
toSusp-invSusp A south =
     rCancel (merid north)
   ∙∙ cong sym (sym (rCancel (merid north)))
   ∙∙ cong sym (cong (toSusp (Susp∙ (typ A))) (merid (pt A)))
toSusp-invSusp A (merid a i) j =
  lem (toSusp (Susp∙ (typ A)) north) (toSusp (Susp∙ (typ A)) south)
         (sym (rCancel (merid north)))
         (cong (toSusp (Susp∙ (typ A))) ((merid (pt A))))
         (cong (toSusp (Susp∙ (typ A))) (merid a)) (~ j) i
  where
  lem : {A : Type ℓ} {x : A} (p q : x ≡ x) (l : refl ≡ p)
        (coh r : p ≡ q)
      → PathP (λ i → (cong sym (sym l) ∙∙ l ∙∙ coh) i
                     ≡ (cong sym (sym coh) ∙∙ cong sym (sym l) ∙∙ l) i)
               (cong sym r)
               (sym r)
  lem p q =
    J (λ p l → (coh r : p ≡ q)
            → PathP (λ i → (cong sym (sym l) ∙∙ l ∙∙ coh) i
                           ≡ (cong sym (sym coh) ∙∙ cong sym (sym l) ∙∙ l) i)
                     (cong sym r)
                     (sym r))
       (J (λ q coh → (r : refl ≡ q)
                   → PathP (λ i → (refl ∙ coh) i
                           ≡ (cong sym (sym coh) ∙∙ refl ∙∙ refl) i)
                     (cong sym r)
                     (sym r))
          λ r → flipSquare (sym (rUnit refl)
                ◁ (flipSquare (sym (sym≡cong-sym r))
                ▷ rUnit refl)))
