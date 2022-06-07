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

data Smash' {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') : Type (ℓ-max ℓ ℓ') where
  base : Smash' A B
  proj  : (x : typ A) → (y : typ B) → Smash' A B
  gluel : (a : typ A) → proj a (pt B) ≡ base
  gluer : (b : typ B) → proj (pt A) b ≡ base
  high : Path (Path (Smash' A B) _ _) (gluel (pt A)) (gluer (pt B))

data smot {ℓ ℓ' ℓ''} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  bs : smot A B C
  proj : typ A → typ B → typ C → smot A B C
  gluel : (x : typ A) (y : typ B) → proj x y (pt C) ≡ bs
  gluem : (x : typ A) (z : typ C) → proj x (pt B) z ≡ bs
  gluer : (y : typ B) (z : typ C) → proj (pt A) y z ≡ bs

  gluel≡gluem : (a : typ A) → gluel a (pt B) ≡ gluem a (pt C)
  gluel≡gluer : (y : typ B) → Path (Path (smot A B C) _ _) (gluel (pt A) y) (gluer y (pt C))
  gluem≡gluer : (z : typ C) → gluem (pt A) z ≡ gluer (pt B) z

  coh : Cube (gluel≡gluer (snd B)) (gluem≡gluer (pt C))
             (gluel≡gluem (pt A)) (λ _ → gluer (snd B) (pt C))
             refl refl

module _ {ℓ : Level} (A B C D : Pointed ℓ) where

  fill1 : typ B → (i j k : I) → smot A B C
  fill1 a i j r =
    hfill (λ k → λ {(i = i0) → gluer a (pt C) (j ∧ k)
                   ; (i = i1) → bs
                   ; (j = i0) → gluel (pt A) a i
                   ; (j = i1) → gluer a (pt C) (i ∨ k)})
       (inS (gluel≡gluer a j i))
       r

  fill2 : typ C → (i j k : I) → smot A B C
  fill2 c i j r =
    hfill (λ k → λ {(i = i0) → gluer (pt B) c (j ∧ k)
                    ; (i = i1) → bs
                    ; (j = i0) → gluem (pt A) c i
                    ; (j = i1) → gluer (pt B) c (i ∨ k)})
        (inS (gluem≡gluer c j i))
        r

  fill3 : typ B → (i j r : I) → Smash' A (Smash' B C , base)
  fill3 b i j r = 
    hfill (λ k → λ {(i = i0) → (compPath-filler' (λ j → proj (pt A) (gluel b j))
                                                  (gluel (pt A))) k j
                   ; (i = i1) → gluer (gluel b (~ k)) j
                   ; (j = i0) → proj (pt A) (gluel b (~ k))
                   ; (j = i1) → base})
           (inS (high i j))
           r

  fill4 : typ C → (i j r : I) → Smash' A (Smash' B C , base)
  fill4 c i j r = 
    hfill (λ k → λ {(i = i0) → (compPath-filler' (λ j → proj (pt A) (gluer c j))
                                                  (gluel (pt A))) k j
                   ; (i = i1) → gluer (gluer c (~ k)) j
                   ; (j = i0) → proj (pt A) (gluer c (~ k))
                   ; (j = i1) → base})
           (inS (high i j))
           r

  fill4' : (i j r k : I) → Smash' A (Smash' B C , base)
  fill4' i j r k =
    hfill (λ k → λ {(i = i0) → (compPath-filler' (λ j → proj (pt A) (high r j)) (gluel (pt A))) k j
                   ; (i = i1) → gluer (high r (~ k)) j
                   ; (j = i0) → proj (pt A) (high r (~ k))
                   ; (j = i1) → base})
           (inS (high i j))
           k

  fill5' : (i j k : I) → Smash' A (Smash' B C , base)
  fill5' i j r =
    hfill (λ k → λ {(i = i0) → gluel (pt A) (~ j ∧ k)
                   ; (i = i1) → base
                   ; (j = i0) → gluel (pt A) (i ∨ k) -- base
                   ; (j = i1) → gluer base i }) -- gluer base (i ∧ k)})
          (inS (high j i)) -- (inS (high i (~ j)))
          r


  fill5 : (i j k : I) → Smash' A (Smash' B C , base)
  fill5 i j r =
    hfill (λ k → λ {(i = i0) → gluel (pt A) (~ j)
                   ; (i = i1) → gluer base (~ j ∨ k)
                   ; (j = i0) → base
                   ; (j = i1) → gluer base (i ∧ k)})
          (inS (high i (~ j)))
          r

  fill6 : (a : typ B) → (i j k : I) → Smash' A (Smash' B C , base)
  fill6 a i j k =
    hfill (λ k → λ {(i = i0) → proj (pt A) (gluel a (~ k))
                   ; (i = i1) → gluer base (~ j)
                   ; (j = i0) → gluer (gluel a (~ k)) i
                   ; (j = i1) → proj (pt A) (gluel a (i ∨ ~ k)) })
           (inS (gluer base (i ∧ ~ j)))
           k


  fill7 : (a : typ B) (i j k r : I)
    → Smash' A (Smash' B C , base)
  {-
    → Cube {A = Smash' A (Smash' B C , base)}
           (λ k r → gluer (proj a (snd C)) r)
           (λ k r → gluer base (~ k ∨ r))
           (λ i r → gluer (proj a (snd C)) (i ∨ r))
           (λ i r → gluer (gluel a i) r)
           (λ i k → fill6 a i k i1)
           refl -}
  fill7 b i j k r =
    hfill (λ r → λ {(i = i0) → gluer (gluel b (~ r)) k
                   ; (i = i1) → gluer base (~ j ∨ k)
                   ; (j = i0) → gluer (gluel b (~ r)) (i ∨ k)
                   ; (j = i1) → gluer (gluel b (i ∨ ~ r)) k
                   ; (k = i0) → fill6 b i j r
                   ; (k = i1) → base})
           (inS (gluer base ((~ j ∧ i) ∨ k)))
           r

{--
hcomp (λ k → λ {(i = i0) → gluel (pt A) (~ j)
                   ; (i = i1) → gluer base (~ j ∨ k)
                   ; (j = i0) → base
                   ; (j = i1) → gluer base (i ∧ k)})
          (high i (~ j))
-}
  flipCompPath-filler : {ℓ : Level} {A : Type ℓ} {x y z w : A}
    (p : x ≡ y) (q : y ≡ z) (Q : PathP (λ i → {!q i0!} ≡ {!!}) p q)
    → Cube (λ i j → compPath-filler p q i j) (λ i j → compPath-filler' p q i j)
            {!!} (λ _ → p ∙ q)
            {!λ j → q ? ?!} λ i j → q (j ∨ i)
  flipCompPath-filler = {!!}

  r-high : (i j k r : I) → smot A B C
  r-high i j k r =
    hfill (λ r → λ {(i = i0) → fill1 (pt B) j k r
                   ; (i = i1) → fill2 (pt C) j k r
                   ; (j = i0) → gluer (snd B) (snd C) (k ∧ r)
                   ; (j = i1) → bs
                   ; (k = i0) → gluel≡gluem (pt A) i j
                   ; (k = i1) → gluer (snd B) (snd C) (j ∨ r)})
          (inS (coh i k j))
          r

  sm→smot : Smash' A (Smash' B C , base) → smot A B C
  sm→smot base = bs
  sm→smot (proj x base) = bs
  sm→smot (proj x (proj y z)) = proj x y z
  sm→smot (proj x (gluel a i)) = gluel x a i
  sm→smot (proj x (gluer b i)) = gluem x b i
  sm→smot (proj x (high i j)) = gluel≡gluem x i j
  sm→smot (gluel a i) = bs
  sm→smot (gluer base i) = bs
  sm→smot (gluer (proj x y) i) = gluer x y i
  sm→smot (gluer (gluel a i) j) = fill1 a i j i1
  sm→smot (gluer (gluer b i) j) = fill2 b i j i1
  sm→smot (gluer (high i j) k) = r-high i j k i1
  sm→smot (high x x₁) = bs

  coh-case : (i j k r : I) → Smash' A (Smash' B C , base)
  coh-case i j k r = 
    hfill (λ r → λ {(i = i0) → fill3 (snd B) j k r
                   ; (i = i1) → fill4 (pt C) j k r
                   ; (j = i0) → (compPath-filler' (λ k₁ → proj (pt A) (high i k₁))
                                                  (gluel (pt A))) r k
                   ; (j = i1) → gluer (high i (~ r)) k
                   ; (k = i0) → proj (pt A) (high i (~ r))
                   ; (k = i1) → base})
          (inS (high j k))
          r

  smot→sm : smot A B C → Smash' A (Smash' B C , base)
  smot→sm bs = base
  smot→sm (proj x x₁ x₂) = proj x (proj x₁ x₂)
  smot→sm (gluel x y i) = ((λ i → proj x (gluel y i)) ∙ gluel x) i
  smot→sm (gluem x z i) = ((λ i → proj x (gluer z i)) ∙ gluel x) i
  smot→sm (gluer y z i) = gluer (proj y z) i
  smot→sm (gluel≡gluem a i j) = ((λ k → proj a (high i k)) ∙ gluel a) j
  smot→sm (gluel≡gluer b i j) = fill3 b i j i1
  smot→sm (gluem≡gluer c i j) = fill4 c i j i1
  smot→sm (coh i j k) = coh-case i j k i1

  gluel-fill : (x : typ A) (b : typ B) (i j k : I) → smot A B C
  gluel-fill x y i j k =
    hfill (λ k → λ {(i = i0) → gluel x y (~ k)
                   ; (i = i1) → bs
                   ; (j = i0) → sm→smot (compPath-filler' (λ i → (proj x (gluel y i))) (gluel x) k i)
                   ; (j = i1) → gluel x y (i ∨ ~ k)})
          (inS bs)
          k

  gluem-fill : (x : typ A) (z : typ C) (i j k : I) → smot A B C
  gluem-fill x z i j k =
    hfill (λ k → λ {(i = i0) → gluem x z (~ k)
                   ; (i = i1) → bs
                   ; (j = i0) → sm→smot (compPath-filler' (λ i → (proj x (gluer z i))) (gluel x) k i)
                   ; (j = i1) → gluem x z (i ∨ ~ k)})
          (inS bs)
          k


  sm→smot'' : (x : smot A B C) → sm→smot (smot→sm x) ≡ x
  sm→smot'' bs = refl
  sm→smot'' (proj x x₁ x₂) = refl
  sm→smot'' (gluel x y i) j = gluel-fill x y i j i1
  sm→smot'' (gluem x z i) j = gluem-fill x z i j i1
  sm→smot'' (gluer y z i) = refl
  sm→smot'' (gluel≡gluem a k i) j =
    hcomp (λ r → λ {(i = i0) → gluel≡gluem a k (~ r)
                   ; (i = i1) → bs
                   ; (j = i0) → sm→smot ((compPath-filler' (λ j → proj a (high k j)) (gluel a) r) i)
                   ; (j = i1) → gluel≡gluem a k (i ∨ ~ r)
                   ; (k = i0) → gluel-fill a (pt B) i j r
                   ; (k = i1) → gluem-fill a (pt C) i j r})
           bs
  sm→smot'' (gluel≡gluer y k i) j =
    hcomp (λ r → λ {(i = i0) → gluel≡gluer y (k ∧ j) (~ r)
                   ; (i = i1) → bs
                   ; (j = i0) → sm→smot (fill3 y k i r)
                   ; (j = i1) → gluel≡gluer y k (i ∨ ~ r) -- s r i k
                   ; (k = i0) → gluel-fill (pt A) y i j r
                   ; (k = i1) → ss r i j})
           bs
    where
    ss : Cube (λ _ _ → bs)
              (λ i j →  gluer y (pt C) i)
              (λ r j → gluel≡gluer y j (~ r))
              (λ r j → bs)
              (λ r i → fill1 y (~ r) i i1)
              λ r i → gluer y (snd C) (i ∨ ~ r)
    ss r i j =
      hcomp (λ k → λ {(r = i0) → bs
                     ; (r = i1) → gluer y (snd C) (i ∧ k)
                     ; (i = i0) → gluel≡gluer y j (~ r)
                     ; (i = i1) → gluer y (snd C) (~ r ∨ k)
                     ; (j = i0) → fill1 y (~ r) i k
                     ; (j = i1) → gluer y (snd C) ((i ∧ k) ∨ ~ r)})
            (gluel≡gluer y (j ∨ i) (~ r))
  sm→smot'' (gluem≡gluer z k i) j =
    hcomp (λ r → λ {(i = i0) → gluem≡gluer z (k ∧ j) (~ r)
                   ; (i = i1) → bs
                   ; (j = i0) → sm→smot (fill4 z k i r)
                   ; (j = i1) → gluem≡gluer z k (i ∨ ~ r) 
                   ; (k = i0) → gluem-fill (pt A) z i j r
                   ; (k = i1) → ss r i j})
           bs
    where
    ss : Cube (λ _ _ → bs) (λ i j → gluer (pt B) z i)
              (λ r j → gluem≡gluer z j (~ r))
              (λ r j → bs)
              (λ r i → fill2 z (~ r) i i1)
              λ r i → gluer (pt B) z (i ∨ ~ r) 
    ss r i j =
      hcomp (λ k → λ {(i = i0) → gluem≡gluer z j (~ r)
                   ; (i = i1) → gluer (snd B) z (~ r ∨ k)
                   ; (j = i0) → fill2 z (~ r) i k
                   ; (j = i1) → gluer (snd B) z (~ r ∨ (k ∧ i))
                   ; (r = i0) → bs
                   ; (r = i1) → gluer (snd B) z (i ∧ k)})
              (gluem≡gluer z (j ∨ i) (~ r))
  sm→smot'' (coh i j k) r =
    {!
r = i0 ⊢ bs
r = i1 ⊢ gluer (pt B) z i
i = i0 ⊢ gluem≡gluer z j (~ r)
i = i1 ⊢ bs
j = i0 ⊢ fill2 z (~ r) i i1
j = i1 ⊢ gluer (pt B) z (i ∨ ~ r)
!}

--   fill90 : (x : typ A) (a : typ B) → (i j k : I) → Smash' A (Smash' B C , base)
--   fill90 x a i j k = 
--     hfill (λ k → λ {(i = i0) → proj x (gluel a (~ k))
--                    ; (i = i1) → gluel x (~ j)
--                    ; (j = i0) → compPath-filler' (λ i₁ → proj x (gluel a i₁)) (gluel x) k i
--                    ; (j = i1) → proj x (gluel a (i ∨ ~ k))})
--           (inS (gluel x (~ j ∧ i)))
--           k

--   fill91 : (x : typ A) (a : typ C) → (i j k : I) → Smash' A (Smash' B C , base)
--   fill91 x a i j k =
--     hfill (λ k → λ {(i = i0) → proj x (gluer a (~ k))
--                    ; (i = i1) → gluel x (~ j)
--                    ; (j = i0) → compPath-filler' (λ i₁ → proj x (gluer a i₁)) (gluel x) k i
--                    ; (j = i1) → proj x (gluer a (i ∨ ~ k))})
--           (inS (gluel x (~ j ∧ i)))
--           k

--   fill92 : (x : typ A) → (i j k r : I) → Smash' A (Smash' B C , base)
--   fill92 x i j k r =
--     hfill (λ r → λ {(i = i0) → proj x (high k (~ r))
--                    ; (i = i1) → gluel x (~ j)
--                    ; (j = i0) → compPath-filler' (λ i₁ → proj x (high k i₁)) (gluel x) r i
--                    ; (j = i1) → proj x (high k (i ∨ ~ r))})
--           (inS (gluel x (~ j ∧ i)))
--           r

--   btm-fill : (i j k r : I) → Smash' A (Smash' B C , base)
--   btm-fill i j k r =
--     hfill (λ r → λ {(i = i0) → gluer base (j ∧ (~ r ∨ k))
--                               ; (i = i1) → fill5 j k i1
--                               ; (j = i1) → gluer base (i ∨ (~ r ∨ k))
--                               ; (j = i0) → gluel (snd A) (i ∧ ~ k)
--                               ; (k = i0) → fill5 j (~ i) (~ r)
--                               ; (k = i1) → gluer base j})
--                      (inS (fill5 j (~ i ∨ k) i1))
--            r


--   ll-fill₁ : (a : typ B) (i j k r : I) → Smash' A (Smash' B C , base)
--   ll-fill₁ a i j k r =
--     hfill (λ r → λ {(i = i0) → gluer (gluel a (~ r)) (j ∧ k)
--                    ; (i = i1) → fill5 j k i1
--                    ; (j = i1) → gluer (gluel a (~ r)) (i ∨ k)
--                    ; (j = i0) → fill90 (pt A) a i k r
--                    ; (k = i0) → fill3 a j i r
--                    ; (k = i1) → gluer (gluel a (i ∨ ~ r)) j})
--               (inS (btm-fill i j k i1))
--              r

--   lr-fill₁ : (b : typ C) (i j k r : I) → Smash' A (Smash' B C , base)
--   lr-fill₁ a i j k r =
--     hfill (λ r → λ {(i = i0) → gluer (gluer a (~ r)) (j ∧ k)
--                    ; (i = i1) → fill5 j k i1
--                    ; (j = i1) → gluer (gluer a (~ r)) (i ∨ k)
--                    ; (j = i0) → fill91 (pt A) a i k r
--                    ; (k = i0) → fill4 a j i r
--                    ; (k = i1) → gluer (gluer a (i ∨ ~ r)) j})
--               (inS (btm-fill i j k i1))
--              r

--   ll-fill₂ : (a : typ B) (i j k r : I) → Smash' A (Smash' B C , base)
--   ll-fill₂ a i j k r =
--     hfill (λ r → λ {(i = i0) → gluer (proj a (snd C)) (j ∧ (r ∨ k))
--                    ; (i = i1) → fill5 j k i1
--                    ; (j = i1) → gluer (proj a (snd C)) ((r ∨ i) ∨ k)
--                    ; (j = i0) → fill90 (pt A) a i k i1
--                    ; (k = i0) → smot→sm (fill1 a i j r)
--                    ; (k = i1) → gluer (gluel a i) j})
--       (inS (ll-fill₁ a i j k i1))
--       r

--   lr-fill₂ : (a : typ C) (i j k r : I) → Smash' A (Smash' B C , base)
--   lr-fill₂ a i j k r =
--     hfill (λ r → λ {(i = i0) → gluer (proj (pt B) a) (j ∧ (r ∨ k))
--                    ; (i = i1) → fill5 j k i1
--                    ; (j = i1) → gluer (proj (pt B) a) ((r ∨ i) ∨ k)
--                    ; (j = i0) → fill91 (pt A) a i k i1
--                    ; (k = i0) → smot→sm (fill2 a i j r)
--                    ; (k = i1) → gluer (gluer a i) j})
--       (inS (lr-fill₁ a i j k i1))
--       r

--   sm→smot' : (x : Smash' A (Smash' B C , base))
--     → smot→sm (sm→smot x) ≡ x
--   sm→smot' base = refl
--   sm→smot' (proj x base) = sym (gluel x)
--   sm→smot' (proj x (proj x₁ y)) = refl
--   sm→smot' (proj x (gluel a i)) j = fill90 x a i j i1
--   sm→smot' (proj x (gluer b i)) j = fill91 x b i j i1
--   sm→smot' (proj x (high r i)) j = fill92 x i j r i1
--   sm→smot' (gluel a i) j = gluel a (~ j ∨ i)
--   sm→smot' (gluer base i) j = fill5 i j i1
--   sm→smot' (gluer (proj x y) i) j = gluer (proj x y) i
--   sm→smot' (gluer (gluel a i) j) k = ll-fill₂ a i j k i1
--   sm→smot' (gluer (gluer b i) j) k = lr-fill₂ b i j k i1
--   sm→smot' (gluer (high r i) j) k =
--     hcomp (λ s → λ {(i = i0) → gluer (proj (pt B) (pt C)) ((j ∧ (s ∨ k)))
--                    ; (i = i1) → fill5 j k i1
--                    ; (j = i0) → fill92 (pt A) i k r i1
--                    ; (j = i1) → gluer (proj (snd B) (snd C)) ((s ∨ i) ∨ k)
--                    ; (k = i0) → smot→sm (r-high r i j s)
--                    ; (k = i1) → gluer (high r i) j
--                    ; (r = i0) → ll-fill₂ (pt B) i j k s
--                    ; (r = i1) → lr-fill₂ (pt C) i j k s})
--       (hcomp (λ s → λ {(i = i0) → gluer (high r (~ s)) (j ∧ k)
--                    ; (i = i1) → fill5 j k i1
--                    ; (j = i0) → fill92 (pt A) i k r s
--                    ; (j = i1) → gluer (high r (~ s)) (i ∨ k)
--                    ; (k = i0) → coh-case r j i s
--                    ; (k = i1) → gluer (high r (i ∨ ~ s)) j
--                    ; (r = i0) → ll-fill₁ (pt B) i j k s
--                    ; (r = i1) → lr-fill₁ (pt C) i j k s})
--          (hcomp (λ s → λ {(i = i0) → gluer base (j ∧ (~ s ∨ k))
--                    ; (i = i1) → fill5 j k i1
--                    ; (j = i0) → gluel (snd A) (i ∧ ~ k)
--                    ; (j = i1) → gluer base (i ∨ ~ s ∨ k)
--                    ; (k = i0) → fill5 j (~ i) (~ s)
--                    ; (k = i1) → gluer base j
--                    ; (r = i0) → btm-fill i j k s
--                    ; (r = i1) → btm-fill i j k s})
--                 (fill5 j (~ i ∨ k) i1)))
--   sm→smot' (high i j) k =
--     hcomp (λ r → λ {(i = i0) → gluel (pt A) (~ k ∨ (j ∧ r))
--                    ; (i = i1) → fill5 j k r
--                    ; (j = i0) → gluel (snd A) (~ k)
--                    ; (j = i1) → high i (~ k ∨ r)
--                    ; (k = i0) → base
--                    ; (k = i1) → high i (j ∧ r)})
--           (high (j ∧ i) (~ k))



-- private
--   variable
--     ℓ ℓ' : Level
--     A B C D : Pointed ℓ

-- Smash-map : (f : A →∙ C) (g : B →∙ D) → Smash A B → Smash C D
-- Smash-map f g basel = basel
-- Smash-map f g baser = baser
-- Smash-map (f , fpt) (g , gpt) (proj x y) = proj (f x) (g y)
-- Smash-map (f , fpt) (g , gpt) (gluel a i) = ((λ j → proj (f a) (gpt j)) ∙ gluel (f a)) i
-- Smash-map (f , fpt) (g , gpt) (gluer b i) = ((λ j → proj (fpt j) (g b)) ∙ gluer (g b)) i

-- -- Commutativity
-- comm : Smash A B → Smash B A
-- comm basel       = baser
-- comm baser       = basel
-- comm (proj x y)  = proj y x
-- comm (gluel a i) = gluer a i
-- comm (gluer b i) = gluel b i

-- commK : (x : Smash A B) → comm (comm x) ≡ x
-- commK basel       = refl
-- commK baser       = refl
-- commK (proj x y)  = refl
-- commK (gluel a x) = refl
-- commK (gluer b x) = refl

-- -- WIP below

-- SmashPt : (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
-- SmashPt A B = (Smash A B , basel)

-- SmashPtProj : (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
-- SmashPtProj A B = Smash A B , (proj (snd A) (snd B))

-- --- Alternative definition

-- i∧ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → A ⋁ B → (typ A) × (typ B)
-- i∧ {A = A , ptA} {B = B , ptB} (inl x) = x , ptB
-- i∧ {A = A , ptA} {B = B , ptB} (inr x) = ptA , x
-- i∧ {A = A , ptA} {B = B , ptB} (push tt i) = ptA , ptB

-- _⋀_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Type (ℓ-max ℓ ℓ')
-- A ⋀ B = Pushout {A = (A ⋁ B)} (λ _ → tt) i∧

-- _·×_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
-- fst (A ·× B) = fst A × fst B
-- snd (A ·× B) = pt A , pt B


-- ⋀≃smot : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → Iso (A ⋀ B) (Smash' A B)
-- Iso.fun ⋀≃smot (inl x) = base
-- Iso.fun ⋀≃smot (inr (x , y)) = proj x y
-- Iso.fun ⋀≃smot (push (inl x) i) = gluel x (~ i)
-- Iso.fun ⋀≃smot (push (inr x) i) = gluer x (~ i)
-- Iso.fun ⋀≃smot (push (push a i₁) i) = high i₁ (~ i)
-- Iso.inv ⋀≃smot base = inl tt
-- Iso.inv ⋀≃smot (proj x y) = inr (x , y)
-- Iso.inv ⋀≃smot (gluel a i) = push (inl a) (~ i)
-- Iso.inv ⋀≃smot (gluer b i) = push (inr b) (~ i)
-- Iso.inv ⋀≃smot (high x x₁) = push (push tt x) (~ x₁)
-- Iso.rightInv ⋀≃smot base = refl
-- Iso.rightInv ⋀≃smot (proj x y) = refl
-- Iso.rightInv ⋀≃smot (gluel a i) = refl
-- Iso.rightInv ⋀≃smot (gluer b i) = refl
-- Iso.rightInv ⋀≃smot (high x x₁) = refl
-- Iso.leftInv ⋀≃smot (inl x) = refl
-- Iso.leftInv ⋀≃smot (inr x) = refl
-- Iso.leftInv ⋀≃smot (push (inl x) i) = refl
-- Iso.leftInv ⋀≃smot (push (inr x) i) = refl
-- Iso.leftInv ⋀≃smot (push (push a i₁) i) = refl

-- ∨map : ∀ {ℓ ℓ' ℓ''} → {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
--      → (A ·× B) ⋁ (A ·× C)
--      → typ A × typ B × typ C
-- ∨map {C = C} (inl x) = fst x , (snd x) , pt C
-- ∨map {B = B} (inr x) = (fst x) , (snd B , snd x)
-- ∨map {A = A} {B = B} {C = C} (push a i) = pt A , pt B , pt C

-- kill : ∀ {ℓ ℓ' ℓ''} → {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
--      → (A ·× B) ⋁ (A ·× C)
--      → typ A
-- kill (inl x) = fst x
-- kill (inr x) = fst x
-- kill {A = A} (push a i) = pt A

-- smashDef' : ∀ {ℓ ℓ' ℓ''} → Pointed ℓ → Pointed ℓ' → Pointed ℓ'' → Type _
-- smashDef' A B C = Pushout {A = (A ·× B) ⋁ (A ·× C)} ∨map kill

-- smashDef : ∀ {ℓ ℓ' ℓ''} → Pointed ℓ → Pointed ℓ' → Pointed ℓ'' → Type _
-- smashDef A B C = Pushout {A = (A ·× B) ⋁ (A ·× C)} ∨map λ _ → tt

-- fake∨ : ∀ {ℓ ℓ' ℓ''} → (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'')
--   → Type _
-- fake∨ A B C = Pushout {A = typ A} (λ x → (x , pt B)) λ x → (x , pt C )

-- fake∨→ : ∀ {ℓ ℓ' ℓ''} → {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
--   → fake∨ A B C → typ A × typ B × typ C
-- fake∨→ {C = C} (inl (x , y)) = x , y , pt C
-- fake∨→ {B = B} (inr (x , z)) = x , pt B , z
-- fake∨→ {B = B} {C = C} (push a i) = a , pt B , pt C



-- smashDef'' : ∀ {ℓ ℓ' ℓ''} → (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'')
--   → Type _
-- smashDef'' A B C = Pushout {A = fake∨ A B C} {B = fst A} {C = typ A × typ B × typ C} (λ x → fake∨→ {A = A} x .fst) (fake∨→ {A = A}) 

-- {-
-- (A ∧ B) × C

-- 1 → B
-- ↓    ↓
-- A → A∨B → 1
--      ↓      ↓
--      A×B → A ∧ B

-- A ∧ B <-- 1 --> C

--     <---        A          --->       ?

--     <---        1          --->       ?

--     <---      B ∧ C        --->       A ∧ 

  
--     <---        A          --->       A × B × C

--     <---        1          --->       fake∨

--     <---      B ∧ C        --->       A

-- -}

-- module _ {A B C : Pointed ℓ} where

--   haha : A ⋁ (B ⋀ C , inl tt) → smashDef'' A B C
--   haha (inl x) = inr (x , pt B , pt C)
--   haha (inr x) = inl (pt A)
--   haha (push a i) = push (inl (pt A , pt B)) (~ i)

--   PASHAUT : Type _
--   PASHAUT = Pushout (λ _ → tt) haha

--   F∙F : Iso PASHAUT (A ⋀ (B ⋀ C , (inl tt)))
--   Iso.fun F∙F (inl x) = inl x
--   Iso.fun F∙F (inr (inl x)) = inr (x , inl tt)
--   Iso.fun F∙F (inr (inr x)) = inr (fst x , inr ((fst (snd x)) , (snd (snd x))))
--   Iso.fun F∙F (inr (push (inl x) i)) = inr (fst x , push (inl (snd x)) i)
--   Iso.fun F∙F (inr (push (inr x) i)) = inr (fst x , push (inr (snd x)) i)
--   Iso.fun F∙F (inr (push (push a i₁) i)) = inr (a , push (push tt i₁) i)
--   Iso.fun F∙F (push (inl x) i) = (push (inl x) ∙ λ i → inr (x , push (inl (pt B)) i)) i
--   Iso.fun F∙F (push (inr (inl x)) i) = push (inl (pt A)) i
--   Iso.fun F∙F (push (inr (inr x)) i) =
--     (push (inr (inr (fst x , pt C)))
--     ∙∙ (λ i → inr (snd A , push (inl (fst x)) (~ i)))
--     ∙∙ ((λ i → inr (snd A , push (inr (snd x)) i))
--     ∙∙ sym (push (inr (inr (pt B , snd x))))
--     ∙∙ (push (inr (inr (pt B , pt C))) ∙ λ i → inr (pt A , push (inr (pt C)) (~ i))))) i
--   Iso.fun F∙F (push (inr (push (inl x) i₁)) i) = {!!}
--   Iso.fun F∙F (push (inr (push (inr x) i₁)) i) = {!!}
--   Iso.fun F∙F (push (inr (push (push a i₂) i₁)) i) = {!!}
--   Iso.fun F∙F (push (push a i₁) i) = {!a!}
--   Iso.inv F∙F (inl x) = inl tt
--   Iso.inv F∙F (inr (fst₁ , inl x)) = inr (inl fst₁)
--   Iso.inv F∙F (inr (fst₁ , inr x)) = inr (inr (fst₁ , fst x , snd x))
--   Iso.inv F∙F (inr (fst₁ , push (inl x) i)) = inr ((push (inl (fst₁ , x))) i)
--   Iso.inv F∙F (inr (fst₁ , push (inr x) i)) = inr ((push (inr (fst₁ , x))) i)
--   Iso.inv F∙F (inr (fst₁ , push (push a i₁) i)) = {!!}
--   Iso.inv F∙F (push (inl x) i) = (push (inl x) ∙ λ i → inr (push (inl (x , pt B)) (~ i))) i
--   Iso.inv F∙F (push (inr (inl x)) i) = (push (inl (pt A)) ∙ λ i → inr (push (inl (pt A , pt B)) (~ i))) i
--   Iso.inv F∙F (push (inr (inr x)) i) = (push (inr (inr x)) ∙ {!λ i → inr (push (inl (pt A , pt B)) (~ i))!}) i
--   Iso.inv F∙F (push (inr (push a i₁)) i) = {!a!}
--   Iso.inv F∙F (push (push a i₁) i) = {!!}
--   Iso.rightInv F∙F (inl x) = refl
--   Iso.rightInv F∙F (inr (x , inl x₁)) = refl
--   Iso.rightInv F∙F (inr (x , inr x₁)) = refl
--   Iso.rightInv F∙F (inr (x , push (inl x₁) i)) = refl
--   Iso.rightInv F∙F (inr (x , push (inr x₁) i)) = refl
--   Iso.rightInv F∙F (inr (x , push (push a i₁) i)) = {!!}
--   Iso.rightInv F∙F (push (inl x) i) = {!refl!}
--   Iso.rightInv F∙F (push (inr x) i) = {!x!}
--   Iso.rightInv F∙F (push (push a i₁) i) = {!!}
--   Iso.leftInv F∙F = {!i = i0 ⊢ inr (inl fst₁)
-- i = i1 ⊢ inr (inr (fst₁ , x , snd C))!}


--   F : typ A × (B ⋀ C) → smashDef'' A B C
--   F (x , inl x₁) = inl x
--   F (x , inr x₁) = inr (x , fst x₁ , snd x₁)
--   F (x , push (inl x₁) i) = push (inl (x , x₁)) i
--   F (x , push (inr x₁) i) = push (inr (x , x₁)) i
--   F (x , push (push a i₁) i) = push (push x i₁) i

--   F⁻ : smashDef'' A B C → typ A × (B ⋀ C)
--   F⁻ (inl x) = x , inl tt
--   F⁻ (inr (x , y , z)) = x , inr (y , z)
--   F⁻ (push (inl (x , y)) i) = x , push (inl y) i
--   F⁻ (push (inr (x , z)) i) = x , push (inr z) i
--   F⁻ (push (push a i₁) i) = a , push (push tt i₁) i

--   F⁻→F→F⁻ : (x : smashDef'' A B C) → F (F⁻ x) ≡ x
--   F⁻→F→F⁻ (inl x) = refl
--   F⁻→F→F⁻ (inr x) = refl
--   F⁻→F→F⁻ (push (inl x) i) = refl
--   F⁻→F→F⁻ (push (inr x) i) = refl
--   F⁻→F→F⁻ (push (push a i₁) i) = refl

--   F→F⁻→F : (x : typ A × (B ⋀ C)) → F⁻ (F x) ≡ x
--   F→F⁻→F (x , inl x₁) = refl
--   F→F⁻→F (x , inr x₁) = refl
--   F→F⁻→F (x , push (inl x₁) i) = refl
--   F→F⁻→F (x , push (inr x₁) i) = refl
--   F→F⁻→F (x , push (push a i₁) i) = refl
  
--   main : Iso (typ A × (B ⋀ C)) (smashDef'' A B C)
--   Iso.fun main = F
--   Iso.inv main = F⁻
--   Iso.rightInv main = F⁻→F→F⁻
--   Iso.leftInv main = F→F⁻→F

-- _⋀∙_ : ∀ {ℓ ℓ'} → Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
-- A ⋀∙ B = Pushout {A = (A ⋁ B)} (λ _ → tt) i∧ , (inl tt)


-- _⋀→_ : (f : A →∙ C) (g : B →∙ D)  → A ⋀ B → C ⋀ D
-- (f ⋀→ g) (inl tt) = inl tt
-- ((f , fpt) ⋀→ (g , gpt)) (inr (x , x₁)) = inr (f x , g x₁)
-- _⋀→_ {B = B} {D = D} (f ,  fpt) (b , gpt)  (push (inl x) i) = (push (inl (f x)) ∙ (λ i → inr (f x , gpt (~ i)))) i
-- _⋀→_ (f , fpt) (g , gpt) (push (inr x) i) = (push (inr (g x)) ∙ (λ i → inr (fpt (~ i) , g x))) i
-- _⋀→_ {A = A} {C = C} {B = B} {D = D} (f , fpt) (g , gpt) (push (push tt j) i) =
--   hcomp (λ k → λ { (i = i0) → inl tt
--                   ; (i = i1) → inr (fpt (~ k) , gpt (~ k))
--                   ; (j = i0) → compPath-filler (push (inl (fpt (~ k))))
--                                                 ((λ i → inr (fpt (~ k) , gpt (~ i)))) k i
--                   ; (j = i1) → compPath-filler (push (inr (gpt (~ k))))
--                                                 ((λ i → inr (fpt (~ i) , gpt (~ k)))) k i})
--         (push (push tt j) i)

-- ⋀→Smash : A ⋀ B → Smash A B
-- ⋀→Smash (inl x) = basel
-- ⋀→Smash (inr (x , x₁)) = proj x x₁
-- ⋀→Smash (push (inl x) i) = gluel x (~ i)
-- ⋀→Smash {A = A} {B = B} (push (inr x) i) = (sym (gluel (snd A)) ∙∙ gluer (snd B) ∙∙ sym (gluer x)) i
-- ⋀→Smash {A = A} {B = B} (push (push a j) i) =
--   hcomp (λ k → λ { (i = i0) → gluel (snd A) (k ∨ ~ j)
--                   ; (i = i1) → gluer (snd B) (~ k ∧ j)
--                   ; (j = i0) → gluel (snd A) (~ i)})
--         (invSides-filler (gluel (snd A)) (gluer (snd B)) j (~ i))

-- Smash→⋀ : Smash A B → A ⋀ B
-- Smash→⋀ basel = inl tt
-- Smash→⋀ baser = inl tt
-- Smash→⋀ (proj x y) = inr (x , y)
-- Smash→⋀ (gluel a i) = push (inl a) (~ i)
-- Smash→⋀ (gluer b i) = push (inr b) (~ i)

-- {- associativity maps for smash produts. Proof pretty much direcly translated from https://github.com/ecavallo/redtt/blob/master/library/pointed/smash.red -}
-- private
--   pivotl : (b b' : typ B)
--          → Path (Smash A B) (proj (snd A) b) (proj (snd A) b')
--   pivotl b b' i = (gluer b ∙ sym (gluer b')) i

--   pivotr : (a a' : typ A)
--          → Path (Smash A B) (proj a (snd B)) (proj a' (snd B))
--   pivotr a a' i = (gluel a ∙ sym (gluel a')) i

--   pivotlrId : {A : Pointed ℓ} {B : Pointed ℓ'} → _
--   pivotlrId {A = A} {B = B} = rCancel (gluer (snd B)) ∙ sym (rCancel (gluel (snd A)))

--   rearrange-proj : (c : fst C)
--                 → (Smash A B) → Smash (SmashPtProj C B) A
--   rearrange-proj c basel = baser
--   rearrange-proj c baser = basel
--   rearrange-proj c (proj x y) = proj (proj c y) x
--   rearrange-proj {C = C} c (gluel a i) =
--     hcomp (λ k → λ { (i = i0) → proj (pivotr (snd C) c k) a
--                     ; (i = i1) → baser})
--           (gluer a i)
--   rearrange-proj c (gluer b i) = gluel (proj c b) i

--   rearrange-gluel : (s : Smash A B)
--                  → Path (Smash (SmashPtProj C B) A) basel (rearrange-proj (snd C) s)
--   rearrange-gluel {A = A} {B = B} {C = C} basel = sym (gluel (proj (snd C) (snd B))) ∙
--                                                   gluer (snd A)
--   rearrange-gluel baser = refl
--   rearrange-gluel {A = A} {B = B} {C = C} (proj a b) i =
--     hcomp (λ k → λ { (i = i0) → (sym (gluel (proj (snd C) (snd B))) ∙
--                                                   gluer (snd A)) (~ k)
--                     ; (i = i1) → proj (pivotl (snd B) b k) a})
--           (gluer a (~ i))
--   rearrange-gluel {A = A} {B = B} {C = C} (gluel a i) j =
--     hcomp (λ k → λ { (i = i1) → ((λ i₁ → gluel (proj (snd C) (snd B)) (~ i₁)) ∙
--                                   gluer (snd A)) (~ k ∨ j)
--                     ; (j = i0) → ((λ i₁ → gluel (proj (snd C) (snd B)) (~ i₁)) ∙
--                                   gluer (snd A)) (~ k)
--                     ; (j = i1) → top-filler i k})
--           (gluer a (i ∨ ~ j))
--     where
--       top-filler : I → I → Smash (SmashPtProj C B) A
--       top-filler i j =
--         hcomp (λ k → λ { (i = i0) → side-filler k j
--                         ; (i = i1) → gluer a (j ∨ k)
--                         ; (j = i0) → gluer a (i ∧ k)})
--               (gluer a (i ∧ j))
--        where
--        side-filler : I → I → Smash (SmashPtProj C B) A
--        side-filler i j =
--          hcomp (λ k → λ { (i = i0) → proj (proj (snd C) (snd B)) a
--                         ; (i = i1) → proj ((rCancel (gluel (snd C)) ∙ sym (rCancel (gluer (snd B)))) k j) a
--                         ; (j = i0) → proj (proj (snd C) (snd B)) a
--                         ; (j = i1) → (proj ((gluel (snd C) ∙ sym (gluel (snd C))) i) a)})
--                 (proj ((gluel (snd C) ∙ sym (gluel (snd C))) (j ∧ i)) a)
--   rearrange-gluel {A = A} {B = B} {C = C} (gluer b i) j =
--     hcomp (λ k → λ {(i = i1) → ((sym (gluel (proj (snd C) (snd B)))) ∙ gluer (snd A)) (~ k)
--                    ; (j = i0) → ((sym (gluel (proj (snd C) (snd B)))) ∙ gluer (snd A)) (~ k)
--                    ; (j = i1) → top-filler1 i k})
--           (gluer (snd A) (i ∨ (~ j)))
--     where
--     top-filler1 : I → I → Smash (SmashPtProj C B) A
--     top-filler1 i j =
--       hcomp (λ k → λ { (i = i0) → congFunct (λ x → proj x (snd A)) (gluer (snd B)) (sym (gluer b)) (~ k) j
--                    ; (i = i1) → (sym (gluel (proj (snd C) (snd B))) ∙ gluer (snd A)) (~ j)
--                    ; (j = i0) → gluer (snd A) i
--                    ; (j = i1) → gluel (proj (snd C) b) i})
--           (top-filler2 i j)
--       where
--       top-filler2 : I → I → Smash (SmashPtProj C B) A
--       top-filler2 i j =
--         hcomp (λ k → λ { (j = i0) → gluer (snd A) (i ∧ k)
--                           ; (j = i1) → gluel (gluer b (~ k)) i})
--                 (hcomp (λ k → λ { (j = i0) → gluel (gluer (snd B) i0) (~ k ∧ (~ i))
--                                  ; (j = i1) → gluel (baser) (~ k ∨ i)
--                                  ; (i = i0) → gluel (gluer (snd B) j) (~ k)
--                                  ; (i = i1) → gluel (proj (snd C) (snd B)) j })
--                        (gluel (proj (snd C) (snd B)) (j ∨ (~ i))))

--   rearrange : Smash (SmashPtProj A B) C → Smash (SmashPtProj C B) A
--   rearrange basel = basel
--   rearrange baser = baser
--   rearrange (proj x y) = rearrange-proj y x
--   rearrange (gluel a i) = rearrange-gluel a (~ i)
--   rearrange {A = A} {B = B} {C = C} (gluer b i) = ((λ j → proj (pivotr b (snd C) j) (snd A)) ∙
--                                                   gluer (snd A)) i

--   ⋀∙→SmashPtProj : (A ⋀∙ B) →∙ SmashPtProj A B
--   ⋀∙→SmashPtProj {A = A} {B = B} = fun , refl
--     where
--     fun : (A ⋀ B) → Smash A B
--     fun (inl x) = proj (snd A) (snd B)
--     fun (inr (x , x₁)) = proj x x₁
--     fun (push (inl x) i) = pivotr (snd A) x i
--     fun (push (inr x) i) = pivotl (snd B) x i
--     fun (push (push a j) i) = pivotlrId (~ j) i

--   SmashPtProj→⋀∙ : (SmashPtProj A B) →∙ (A ⋀∙ B)
--   SmashPtProj→⋀∙ {A = A} {B = B} = Smash→⋀ , sym (push (inr (snd B)))

-- SmashAssociate : Smash (SmashPtProj A B) C → Smash A (SmashPtProj B C)
-- SmashAssociate = comm ∘ Smash-map  (comm , refl) (idfun∙ _) ∘ rearrange

-- SmashAssociate⁻ : Smash A (SmashPtProj B C) → Smash (SmashPtProj A B) C
-- SmashAssociate⁻ = rearrange ∘ comm ∘ Smash-map (idfun∙ _) (comm , refl)

-- ⋀-associate : (A ⋀∙ B) ⋀ C → A ⋀ (B ⋀∙ C)
-- ⋀-associate = (idfun∙ _ ⋀→ SmashPtProj→⋀∙) ∘ Smash→⋀ ∘ SmashAssociate ∘ ⋀→Smash ∘ (⋀∙→SmashPtProj ⋀→ idfun∙ _)

-- ⋀-associate⁻ : A ⋀ (B ⋀∙ C) → (A ⋀∙ B) ⋀ C
-- ⋀-associate⁻ = (SmashPtProj→⋀∙ ⋀→ idfun∙ _) ∘ Smash→⋀ ∘ SmashAssociate⁻ ∘ ⋀→Smash ∘ (idfun∙ _ ⋀→ ⋀∙→SmashPtProj)
