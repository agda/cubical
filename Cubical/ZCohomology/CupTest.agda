{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.ZCohomology.CupTest where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to sRec2 ; elim to sElim ; elim2 to sElim2)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; elim to pElim ; elim2 to pElim2 ; ∥_∥ to ∥_∥₁ ; ∣_∣ to ∣_∣₁)
open import Cubical.Data.Nat
open import Cubical.Algebra.Group
open import Cubical.HITs.Truncation renaming (elim to trElim ; map to trMap ; rec to trRec ; elim3 to trElim3)

open import Cubical.HITs.SmashProduct


open import Cubical.Data.Bool
open import Cubical.Foundations.Pointed




private
  variable
    ℓ : Level
    A : Pointed ℓ
    B : Pointed ℓ

open import Cubical.Data.Prod

f̂ : S¹ → typ A → Susp (typ A)
f̂ base a = north
f̂ {A = A , a} (loop i) x = (merid x ∙ (sym (merid a))) i

g : Susp (typ A) → (S¹ , base) ⋀ A
g north = inl tt
g south = inl tt
g (merid a i) = (push (inr a) ∙∙ (λ i → inr (loop i , a)) ∙∙ sym (push (inr a))) i

f : (S¹ , base) ⋀ A → Susp (typ A)
f (inl x) = north
(f {A = A}) (inr (x , y)) = f̂ {A = A} x y
f (push (inl base) i) = north
f {A = A} (push (inl (loop j)) i) = rCancel (merid (pt A)) (~ i) j
f (push (inr x) i) = north
f (push (push a i₁) i) = north

projᵣₗ : Path (Path (A ⋀ B) (inl tt) (inr (pt A , pt B))) (push (inl (pt A))) (push (inr (pt B)))
projᵣₗ i j = push (push tt i) j
{-
f∘g : ∀ {A : Pointed ℓ} (x : Susp (typ A)) → f (g {A = A} x) ≡ x
f∘g {A = A} north = refl
f∘g {A = A , a} south = merid a
f∘g {A = A , a} (merid x i) j = {!!} -}

nat-inr : I → I → I → (S¹ , base) ⋀ A
{- filler : PathP (λ i → Path ((S¹ , base) ⋀ A)
                             (push (inr (pt A)) (~ i))
                             (push (inr (pt A)) (~ i)))
                (λ i → inr (loop i , (pt A))) refl -}
nat-inr {A = A} i j k =
  hfill (λ k → λ { (i = i0) → {!!}
                  ; (i = i1) → {!!}
                  ; (j = i0) → {!!}
                  ; (j = i1) → {!!}})
        (inS {!!})
        k

g-done : cong (g {A = A}) (merid (pt A)) ≡ refl
g-done = {!!}

inl-base : I → I → I → {!!}
inl-base = {!!}

g∘f : ∀ {A : Pointed ℓ} (x : _) → g {A = A} (f x) ≡ x
g∘f (inl x) = refl
g∘f (inr (base , y)) = push (inr y)
g∘f {A = A , a} (inr (loop i , y)) j = sq₀ i j
  where
  sq₃ : I → I → I → (S¹ , base) ⋀ (A , a)
  sq₃ i j k =
    hfill (λ k → λ { (i = i0) → inl tt
                    ; (i = i1) → g-done (~ k) (~ j)
                    ; (j = i0) → g (merid y i)
                    ; (j = i1) → g (merid y i)})
          (inS (g (merid y i)))
          k

  sq₂ : I → I → I → (S¹ , base) ⋀ (A , a)
  sq₂ i j k =
    hfill (λ k → λ { (i = i0) → inl tt
                    ; (i = i1) → g (merid a (~ j ∧ ~ k))
                    ; (j = i0) → compPath-filler (cong g (merid y)) (cong g (sym (merid a))) k i
                    ; (j = i1) → g (merid y i)})
          (inS (sq₃ i j i1))
          k

  sq₀ : Square (push (inr y)) (push (inr y))
              (cong g (merid y ∙ (sym (merid a)))) (λ i → inr (loop i , y))
  sq₀ i j = hcomp (λ k → λ {(i = i0) → push (inr y) j
                           ; (i = i1) → push (inr y) j
                           ; (j = i0) → cong-∙ g (merid y) (sym (merid a)) (~ k) i
                           ; (j = i1) → inr (loop i , y)})
                  (hcomp (λ k → λ {(i = i0) → push (inr y) (j ∧ k)
                           ; (i = i1) → push (inr y) (j ∧ k)
                           ; (j = i0) → (cong g (merid y) ∙ cong g (sym (merid a))) i
                           ; (j = i1) → doubleCompPath-filler (push (inr y))
                                                               (λ i → inr (loop i , y))
                                                               (sym (push (inr y))) (~ k) i})
                         (sq₂ i j i1))

g∘f (push (inl base) i) j = {!push !}
g∘f (push (inl (loop j)) i) = {!!}
g∘f (push (inr x) i) = {!!}
g∘f (push (push a i₁) i) = {!!}

-- test : Susp (Smash A B) → Smash (Susp (typ A) , north) B
-- test {A = A , a} {B = B , b} north = baser
-- test {A = A , a} {B = B , b} south = baser
-- test {A = A , a} {B = B , b} (merid basel i) = baser
-- test {A = A , a} {B = B , b} (merid baser i) = baser
-- test {A = A , a} {B = B , b} (merid (proj x y) i) =
--   (sym (gluer y) ∙∙ ((λ i → proj (merid x i) y) ∙ (λ i → proj (merid a (~ i)) y)) ∙∙ gluer y) i
-- test {A = A , a} {B = B , b} (merid (gluel x j) i) =
--   {!!}
-- test {A = A , a} {B = B , b} (merid (gluer b₁ i₁) i) =
--   {!!}


-- -- meinProof : {A : Pointed ℓ} → Path (Path (Smash A (Susp Bool , north))
-- --                        _ _)
-- --                  (((λ i₁ → gluel (pt A) (~ i₁)) ∙∙
-- --                  (λ i₁ → proj (pt A) (merid true i₁)) ∙
-- --                  (λ i₁ → proj (pt A) (merid false (~ i₁)))
-- --                  ∙∙ gluel (pt A)))
-- --                  refl
-- -- meinProof {A = A} = {!!}

-- -- staahp₁ : I → I → I → (x : typ A) → Smash A (Susp Bool , north)
-- -- staahp₁ {A = A , a} i j z x = 
-- --   (hfill (λ k → λ { (i = i0) → gluel x (~ j)
-- --                    ; (j = i0) → basel
-- --                    ; (j = i1) → proj x (merid false (i ∧ k))})
-- --                 (inS (gluel x (~ j))))
-- --                 z
-- -- staahp₂ : I → I → I → (x : typ A) → Smash A (Susp Bool , north)
-- -- staahp₂ {A = A , a} i j z x =
-- --   hfill (λ k → λ { (i = i0) → gluel x (~ j)
-- --                   ; (i = i1) → ((λ i₁ → gluel x (~ i₁)) ∙ (λ i₁ → proj x (merid false i₁))) j
-- --                   ; (j = i0) → meinProof {A = A , a} (~ k) i
-- --                   ; (j = i1) → proj x (merid false i)})
-- --          (inS (staahp₁ i j i1 x))
-- --          z


-- -- {-
-- --   hfill (λ k → λ { (i = i0) → gluel x (~ j)
-- --                   ; (i = i1) → ((λ i₁ → gluel x (~ i₁)) ∙ (λ i₁ → proj x (merid false i₁))) j
-- --                   ; (j = i0) → meinProof {A = A , a} (~ k) i
-- --                   ; (j = i1) → proj x (merid false i)})
-- -- -}


-- -- smashMap : (Smash A (Susp Bool , north)) → (Susp (typ A))
-- -- smashMap basel = south
-- -- smashMap baser = north
-- -- smashMap (proj x north) = north
-- -- smashMap (proj x south) = south
-- -- smashMap {A = A , a} (proj x (merid false i)) = merid a i
-- -- smashMap {A = A , a} (proj x (merid true i)) = merid x i
-- -- (smashMap {A = A , a}) (gluel x i) = merid a i
-- -- smashMap (gluer north i) = north
-- -- (smashMap {A = A , a}) (gluer south i) = merid a (~ i)
-- -- (smashMap {A = A , a}) (gluer (merid false j) i) = merid a (~ i ∧ j)
-- -- (smashMap {A = A , a}) (gluer (merid true j) i) = merid a (~ i ∧ j)

-- -- smashMap< : (Susp (typ A)) → Smash A (Susp Bool , north)
-- -- smashMap< north = basel
-- -- smashMap< south = basel
-- -- smashMap< (merid a i) =
-- --   (sym (gluel a) ∙∙ (λ i → proj a (merid true i)) ∙ (λ i → proj a (merid false (~ i))) ∙∙ gluel a) i


-- -- Iso1 : Iso (Smash A (Susp Bool , north)) (Susp (typ A))
-- -- Iso.fun (Iso1 {A = A , a}) = smashMap
-- -- Iso.inv (Iso1 {A = A , a}) = smashMap<
-- -- Iso.rightInv (Iso1 {A = A , a}) north = sym (merid a)
-- -- Iso.rightInv (Iso1 {A = A , a}) south = refl
-- -- Iso.rightInv (Iso1 {A = A , a}) (merid b i) j =
-- --   hcomp (λ k → λ { (i = i0) → merid a (~ j)
-- --                   ; (i = i1) → merid b (~ j ∨ k)
-- --                   ; (j = i0) → cong-∙∙ (smashMap {A = A , a}) (sym (gluel b)) ((λ i → proj b (merid true i)) ∙ (λ i → proj b (merid false (~ i)))) (gluel b) (~ k) i
-- --                   ; (j = i1) → merid b (i ∧ k) })
-- --         (hcomp (λ k → λ { (i = i0) → merid a (~ j ∧ k)
-- --                          ; (i = i1) → compPath-filler (merid a) (sym (merid b)) j k
-- --                          ; (j = i1) → ((merid a) ∙ (sym (merid b))) (~ i ∨ k)})
-- --                (hcomp (λ k → λ { (i = i0) → north
-- --                                 ; (i = i1) → north
-- --                                 ; (j = i0) → cong-∙ (smashMap {A = A , a}) (λ i → proj b (merid true i)) (λ i → proj b (merid false (~ i))) (~ k) i 
-- --                                 ; (j = i1) → symDistr (merid a) (sym (merid b)) (~ k) i})
-- --                       ((merid b ∙ sym (merid a)) i)))



-- -- Iso.leftInv (Iso1 {A = A , a}) basel = refl
-- -- Iso.leftInv (Iso1 {A = A , a}) baser = sym (gluel a) ∙ gluer north
-- -- Iso.leftInv (Iso1 {A = A , a}) (proj x north) = sym (gluel x)
-- -- Iso.leftInv (Iso1 {A = A , a}) (proj x south) = sym (gluel x) ∙ λ i → proj x (merid false i)
-- -- Iso.leftInv (Iso1 {A = A , a}) (proj x (merid false i)) j = staahp₂ i j i1 x
-- -- Iso.leftInv (Iso1 {A = A , a}) (proj x (merid true i)) j =
-- --   hcomp (λ k → λ { (i = i0) → gluel x (~ j)
-- --                   ; (j = i0) → ((λ i₁ → gluel x (~ i₁)) ∙∙
-- --                                  (λ i₁ → proj x (merid true i₁)) ∙
-- --                                  (λ i₁ → proj x (merid false (~ i₁)))
-- --                                  ∙∙ gluel x) i
-- --                   ; (j = i1) → compPath-filler (λ i → proj x (merid true i))
-- --                                                  (λ i → proj x (merid false (~ i))) (~ k) i})
-- --         (hcomp (λ k → λ { (i = i0) → gluel x (~ j ∧ k)
-- --                          ; (i = i1) → gluel x (~ j ∧ k)
-- --                          ; (j = i1) → ((λ i₁ → proj x (merid true i₁)) ∙
-- --                                         (λ i₁ → proj x (merid false (~ i₁)))) i})
-- --                (((λ i₁ → proj x (merid true i₁)) ∙
-- --                                         (λ i₁ → proj x (merid false (~ i₁)))) i))
-- -- Iso.leftInv (Iso1 {A = A , a}) (gluel x i) j = 
-- --   hcomp (λ k → λ { (i = i0) → gluel x (~ j ∨ ~ k)
-- --                   ; (i = i1) → basel
-- --                   ; (j = i0) → meinProof (~ k) i
-- --                   ; (j = i1) → gluel x (i ∨ ~ k)})
-- --         basel
-- -- Iso.leftInv (Iso1 {A = A , a}) (gluer north i) j =
-- --   compPath-filler (sym (gluel a)) (gluer north) i j
-- -- Iso.leftInv (Iso1 {A = A , a}) (gluer south i) j =
-- --   {!!}
-- -- Iso.leftInv (Iso1 {A = A , a}) (gluer (merid false j) i) z =
-- --     hcomp (λ k → λ { (j = i0) → compPath-filler (sym (gluel a)) (gluer north) (i ∧ k) z
-- --                      ; (i = i0) → staahp₂ j z k a
-- --                      ; (i = i1) → compPath-filler (sym (gluel a)) (gluer north) k z
-- --                      ; (z = i0) → meinProof {A = A , a} (~ k) (~ i ∧ j) -- (meinProof {A = A , a}) (~ k) (~ i ∧ j)
-- --                      ; (z = i1) → t4 k i j -- gluer (merid false j) i
-- --                      })
-- --           {!!}
-- --   where
-- --     t4 : Cube {!!} (λ i j → gluer (merid false j) i)
-- --                (λ k j → proj a (merid false j)) (λ k j → gluer north k)
-- --                (λ k i → gluer north (i ∧ k)) {!!}
-- --     t4 k i j =
-- --       hcomp (λ r → λ {(k = i0) → gluer (merid false (j ∨ (~ r ∧ ~ i))) (~ r)
-- --                      ; (k = i1) → gluer (merid false (j ∨ (~ r ∧ ~ i))) (~ r ∨ i)
-- --                      ; (i = i0) → gluer (merid false (j ∨ ~ r)) (~ r) -- proj a (merid false (j ∨ ~ r)) 
-- --                      ; (i = i1) → gluer north (k ∨ ~ r) -- gluer north (k ∨ ~ r) -- gluer (merid false (~ r ∧ ~ j)) (k)
-- --                      ; (j = i0) → gluer (merid false (~ i ∧ ~ r)) ((i ∧ k) ∨ ~ r)
-- --                      ; (j = i1) → {!!} -- gluer (merid false {!~ r!}) ((i ∧ k) ∨ ~ r)
-- --                      })
-- --             {!!}
-- --     t2 : PathP (λ i → basel ≡ (gluer south i)) (((λ i₁ → gluel a (~ i₁)) ∙ (λ i₁ → proj a (merid false i₁)))) (((λ i₁ → gluel a (~ i₁)) ∙ gluer north))
-- --     t2 = {!m!}
-- --     test : I → I → I → Smash (A , a) (Susp Bool , north)
-- --     test i z k =
-- --       hfill
-- --         (λ k → λ { (i = i0) → ((λ i₁ → gluel a (~ i₁)) ∙
-- --                                         (λ i₁ → proj a (merid false i₁)))
-- --                                        z
-- --                      ; (i = i1) → ((λ i₁ → gluel a (~ i₁)) ∙ gluer north) z
-- --                      ; (z = i0) → meinProof (~ k) (~ i)
-- --                      ; (z = i1) → gluer south i })
-- --         (inS (t2 i z))
-- --         k

-- --     t3 : Cube (λ i z → compPath-filler (sym (gluel a)) (gluer north) i z)
-- --               t2
-- --               (λ j z → hcomp (λ k → λ {(j = i0) → gluel a (~ z)
-- --                                      ; (j = i1)  → ((sym (gluel a)) ∙
-- --                                             (λ i₁ → proj (pt (A , a)) (merid false i₁)))
-- --                                            z
-- --                                      ; (z = i0) → meinProof {A = A , a} i1 (~ i ∧ j)
-- --                                      ; (z = i1) → proj (pt (A , a)) (merid false j)
-- --                                      })
-- --                               (hcomp
-- --                                (λ k → λ { (j = i0) → gluel a (~ z)
-- --                                   ; (z = i0) → basel
-- --                                   ; (z = i1) → proj a (merid false (j ∧ k))
-- --                                   })
-- --                                (gluel a (~ z))))
-- --               {!!}
-- --               {!!}
-- --               {!!}
-- --     t3 = {!!}

-- -- Iso.leftInv (Iso1 {A = A , a}) (gluer (merid true j) i) z =
-- --   {!Goal: Smash (A , a) (Susp Bool , north)
-- -- ———— Boundary ——————————————————————————————————————————————
-- -- !}


-- -- -- {-
-- -- -- test : ∀ {ℓ} {A : Type ℓ} (n : ℕ) {x : A} → (P : (y : A) (p : Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ y ∣) → Type ℓ) → ((x : _) (p : _) → isOfHLevel n (P x p))
-- -- --      → P x refl → (y : A) (i : I) (p : Path (hLevelTrunc (suc n) A) ∣ x ∣ ∣ y ∣) → P y p 
-- -- -- test zero P hlev b y p = {!!}
-- -- -- test (suc zero) {x = x} P hlev b y i p = {!p i!}
-- -- --   where
-- -- --   hm? : P y p ≡ P x refl
-- -- --   hm? i = {!P _ (λ j → p (i ∨ j))!}

-- -- -- test (suc (suc n)) P hlev b y p = {!!}

-- -- -- -}

-- -- -- {-
-- -- -- main3-fun : (Smash A B → typ C)
-- -- --         → (Σ[ f ∈ (typ A → typ B → typ C) ]
-- -- --               ( Σ[ fl ∈ ((x : _) → f (pt A) x ≡ f (pt A) (pt B)) ]
-- -- --                 Σ[ fr ∈ ((x : _) → f x (pt B) ≡ f (pt A) (pt B)) ]
-- -- --                   (fl (pt B) ≡ refl) × (fr (pt A) ≡ refl)))
-- -- -- fst (main3-fun f) x y = f (proj x y)
-- -- -- fst (snd (main3-fun f)) x = cong f (gluer x ∙ sym (gluer _))
-- -- -- fst (snd (snd (main3-fun f))) x = cong f (gluel x ∙ sym (gluel _))
-- -- -- fst (snd (snd (snd (main3-fun f)))) = cong (cong f) (rCancel _)
-- -- -- snd (snd (snd (snd (main3-fun f)))) = cong (cong f) (rCancel _)

-- -- -- main3-inv : (Σ[ f ∈ (typ A → typ B → typ C) ]
-- -- --               ( Σ[ fl ∈ ((x : _) → f (pt A) x ≡ f (pt A) (pt B)) ]
-- -- --                 Σ[ fr ∈ ((x : _) → f x (pt B) ≡ f (pt A) (pt B)) ]
-- -- --                   (fl (pt B) ≡ refl) × (fr (pt A) ≡ refl)))
-- -- --           → (Smash A B → typ C)
-- -- -- main3-inv {A = A , a} {B = B , b} {C = C , c} (f , fl , fr , flp , frp) basel = f a b
-- -- -- main3-inv {A = A , a} {B = B , b} {C = C , c} (f , fl , fr , flp , frp) baser = f a b
-- -- -- main3-inv {A = A , a} {B = B , b} {C = C , c} (f , fl , fr , flp , frp) (proj x y) = f x y
-- -- -- main3-inv {A = A , a} {B = B , b} {C = C , c} (f , fl , fr , flp , frp) (gluel x i) = fr x i
-- -- -- main3-inv {A = A , a} {B = B , b} {C = C , c} (f , fl , fr , flp , frp) (gluer y i) = fl y i


-- -- -- main3 : Iso (Σ[ f ∈ (typ A → typ B → typ C) ]
-- -- --               ( Σ[ fl ∈ ((x : _) → f (pt A) x ≡ f (pt A) (pt B)) ]
-- -- --                 Σ[ fr ∈ ((x : _) → f x (pt B) ≡ f (pt A) (pt B)) ]
-- -- --                   (fl (pt B) ≡ refl) × (fr (pt A) ≡ refl)))
-- -- --              (Smash A B → typ C)
-- -- -- Iso.fun (main3 {A = A} {B = B} {C = C}) = main3-inv {A = A} {B = B} {C = C}
-- -- -- Iso.inv (main3 {A = A} {B = B} {C = C}) = main3-fun {A = A} {B = B} {C = C}
-- -- -- Iso.rightInv (main3 {A = A} {B = B} {C = C}) f x = {!x!}
-- -- -- Iso.leftInv (main3 {A = A} {B = B} {C = C}) (f , fl , fr , flp , frp) =
-- -- --   ΣPathP (refl , (ΣPathP (funExt (λ x → cong-∙ (main3-inv {A = A} {B = B} {C = C} (f , fl , fr , flp , frp)) (gluer x) (sym (gluer (pt B))) ∙∙ (λ i → fl x ∙ sym (flp i))
-- -- --   ∙∙ sym (rUnit (fl x))) , ΣPathP ({!!} , ΣPathP (compPathL→PathP help , {!compPathR→PathP!})))))
-- -- --   where
-- -- --   help : sym (cong-∙ (main3-inv {A = A} {B = B} {C = C} (f , fl , fr , flp , frp)) (gluer (pt B)) (sym (gluer (pt B))) ∙∙ (λ i → fl (pt B) ∙ sym (flp i))
-- -- --                      ∙∙ sym (rUnit (fl (pt B))))
-- -- --        ∙ cong (cong (main3-inv {A = A} {B = B} {C = C} (f , fl , fr , flp , frp))) (rCancel (gluer (pt B))) ∙ refl ≡ flp
-- -- --   help = (λ i → sym (cong-∙ (main3-inv {A = A} {B = B} {C = C} (f , fl , fr , flp , frp)) (gluer (pt B)) (sym (gluer (pt B)))
-- -- --                      ∙∙ (λ i → fl (pt B) ∙ sym (flp i))
-- -- --                      ∙∙ sym (rUnit (fl (pt B))))
-- -- --               ∙ rUnit (cong (cong (main3-inv {A = A} {B = B} {C = C} (f , fl , fr , flp , frp))) (rCancel (gluer (pt B)))) (~ i))
-- -- --       ∙∙ {!flp!}
-- -- --       ∙∙ {!!}

-- -- --   h2 : ∀{ℓ} {A B : Type ℓ} {x y : A} (f : A → B) (p : x ≡ y) → cong-∙ f p (sym p)  ≡ cong (cong f) (rCancel _) ∙ sym (rCancel _) 
-- -- --   h2 {y = y} f = J (λ y p → cong-∙ f p (sym p)  ≡ cong (cong f) (rCancel _) ∙ sym (rCancel _))
-- -- --                    {!!}
-- -- -- {-
-- -- -- fst (Iso.leftInv (main3 {A = A} {B = B} {C = C}) (f , fl , fr , flp , frp) i) = f
-- -- -- fst (snd (Iso.leftInv (main3 {A = A} {B = B} {C = C}) (f , fl , fr , flp , frp) i)) x =
-- -- --      (cong-∙ (main3-inv {A = A} {B = B} {C = C} (f , fl , fr , flp , frp)) (gluer x) (sym (gluer (pt B)))
-- -- --   ∙∙ (λ i → fl x ∙ sym (flp i))
-- -- --   ∙∙ sym (rUnit (fl x))) i
-- -- -- fst (snd (snd (Iso.leftInv (main3 {A = A} {B = B} {C = C}) (f , fl , fr , flp , frp) i))) = {!!}
-- -- -- fst (snd (snd (snd (Iso.leftInv (main3 {A = A} {B = B} {C = C}) (f , fl , fr , flp , frp) i)))) j k = {!fst (snd (Iso.leftInv main3 (f , fl , fr , flp , frp) i))
-- -- --          (pt B) k!}
-- -- -- snd (snd (snd (snd (Iso.leftInv (main3 {A = A} {B = B} {C = C}) (f , fl , fr , flp , frp) i)))) = {!!} -}

-- -- -- main2-fun : (Smash A B → typ C)
-- -- --         → (Σ[ f ∈ (typ A → typ B → typ C) ]
-- -- --           ((x : _) → f (pt A) x ≡ f (pt A) (pt B)) × ((x : _) → f x (pt B) ≡ f (pt A) (pt B)))
-- -- -- fst (main2-fun f) x y = f (proj x y)
-- -- -- fst (snd (main2-fun {B = (_ , b)} f)) x = cong f (gluer x ∙ sym (gluer b))
-- -- -- snd (snd (main2-fun {A = (_ , a)} f)) y = cong f (gluel y ∙ sym (gluel a))

-- -- -- main2-inv : (Σ[ f ∈ (typ A → typ B → typ C) ]
-- -- --           ((x : _) → f (pt A) x ≡ f (pt A) (pt B))
-- -- --         × ((x : _) → f x (pt B) ≡ f (pt A) (pt B)))
-- -- --         → (Smash A B → typ C)
-- -- -- main2-inv {A = A , a} {B = B , b} {C = C , c} (f , fl , fr) basel = f a b
-- -- -- main2-inv {A = A , a} {B = B , b} {C = C , c} (f , fl , fr) baser = f a b
-- -- -- main2-inv {A = A , a} {B = B , b} {C = C , c} (f , fl , fr) (proj x y) = f x y
-- -- -- main2-inv {A = A , a} {B = B , b} {C = C , c} (f , fl , fr) (gluel x i) = fr x i
-- -- -- main2-inv {A = A , a} {B = B , b} {C = C , c} (f , fl , fr) (gluer y i) = fl y i

-- -- -- main2 : Iso (Smash A B → typ C)
-- -- --         (Σ[ f ∈ (typ A → typ B → typ C) ]
-- -- --           ((x : _) → f (pt A) x ≡ f (pt A) (pt B)) × ((x : _) → f x (pt B) ≡ f (pt A) (pt B)))
-- -- -- Iso.fun (main2 {A = A} {B = B} {C = C}) = main2-fun {A = A} {B = B} {C = C}
-- -- -- Iso.inv (main2 {A = A} {B = B} {C = C}) = main2-inv {A = A} {B = B} {C = C}
-- -- -- fst (Iso.rightInv (main2 {A = A} {B = B} {C = C}) (f , fl , fr) i) = f
-- -- -- fst (snd (Iso.rightInv (main2 {A = A} {B = B} {C = C}) (f , fl , fr) i)) x j = helper i j
-- -- --   where
-- -- --   helper : cong (main2-inv {A = A} {B = B} {C = C} (f , fl , fr)) (gluer x ∙ sym (gluer (pt B))) ≡ fl x
-- -- --   helper = cong-∙ (main2-inv {A = A} {B = B} {C = C} (f , fl , fr)) (gluer x) (sym (gluer (pt B)))
-- -- --          ∙∙ (λ i → fl x ∙ sym (fl (pt B)))
-- -- --          ∙∙ {!fl (pt B)!}
-- -- -- snd (snd (Iso.rightInv (main2 {A = A} {B = B} {C = C}) (f , fl , fr) i)) a j = {!fl!}
-- -- -- Iso.leftInv (main2 {A = A} {B = B} {C = C}) = {!!}

-- -- -- main? : Iso (Smash A B → typ C) (typ A → typ B → typ C)
-- -- -- Iso.fun (main? {A = A , a} {B = B , b} {C = C , c}) f x y = f (proj x y)
-- -- -- Iso.inv (main? {A = A , a} {B = B , b} {C = C , c}) f basel = f a b
-- -- -- Iso.inv (main? {A = A , a} {B = B , b} {C = C , c}) f baser = f a b
-- -- -- Iso.inv (main? {A = A , a} {B = B , b} {C = C , c}) f (proj x y) = f x y
-- -- -- Iso.inv (main? {A = A , a} {B = B , b} {C = C , c}) f (gluel x i) = {!x!} -- (cong (λ x → f x b) {!!} ∙ {!!}) i
-- -- -- Iso.inv (main? {A = A , a} {B = B , b} {C = C , c}) f (gluer x i) = {!!}
-- -- -- Iso.rightInv (main? {A = A , a} {B = B , b} {C = C , c}) = {!!}
-- -- -- Iso.leftInv (main? {A = A , a} {B = B , b} {C = C , c}) = {!!}


-- -- -- mainC : Iso ((Smash A B , basel) →∙ C) (A →∙ (B →∙ C , (λ _ → pt C) , refl))
-- -- -- fst (fst (Iso.fun mainC (f , p)) x) y = f (proj x y)
-- -- -- snd (fst (Iso.fun mainC (f , p)) x) = cong f (gluel x) ∙ p
-- -- -- fst (snd (Iso.fun (mainC {A = A} {B = B}) (f , p)) i) x = (cong f ((gluer x ∙ sym (gluer (pt B)))  ∙ gluel (pt A)) ∙ p) i
-- -- -- snd (snd (Iso.fun (mainC {A = A} {B = B} {C = C}) (f , p)) i) j =
-- -- --   hcomp (λ k → λ {(i = i0) → (cong f (gluel (snd A)) ∙ p) j
-- -- --                  ; (i = i1) → pt C
-- -- --                  ; (j = i0) → helper (~ k) i
-- -- --                  ; (j = i1) → pt C})
-- -- --         ((cong f (gluel (snd A)) ∙ p) (j ∨ i))
-- -- --   where
-- -- --   helper : (cong f ((gluer (pt B) ∙ sym (gluer (pt B)))  ∙ gluel (pt A)) ∙ p) ≡ cong f (gluel (pt A)) ∙ p
-- -- --   helper = (λ i → cong f (rCancel (gluer (pt B)) i ∙ gluel (pt A)) ∙ p) ∙ λ i → cong f (lUnit (gluel (pt A)) (~ i)) ∙ p
-- -- -- fst (Iso.inv (mainC {A = A} {B = B} {C = C}) (f , p)) basel = fst (f (pt A)) (pt B)
-- -- -- fst (Iso.inv (mainC {A = A} {B = B} {C = C}) (f , p)) baser = fst (f (pt A)) (pt B)
-- -- -- fst (Iso.inv (mainC {A = A} {B = B} {C = C}) (f , p)) (proj x y) = fst (f x) y
-- -- -- fst (Iso.inv (mainC {A = A} {B = B} {C = C}) (f , p)) (gluel a i) = (snd (f a) ∙ sym (snd (f (pt A)))) i
-- -- -- fst (Iso.inv (mainC {A = A} {B = B} {C = C}) (f , p)) (gluer b i) = (funExt⁻ (cong fst p) b ∙ sym (funExt⁻ (cong fst p) (pt B))) i
-- -- -- snd (Iso.inv (mainC {A = A} {B = B} {C = C}) (f , p)) i = fst (p i) (pt B)
-- -- -- fst (fst (Iso.rightInv (mainC {A = A} {B = B} {C = C}) (f , p) i) a) b = fst (f a) b
-- -- -- snd (fst (Iso.rightInv (mainC {A = A} {B = B} {C = C}) (f , p) i) a) j = {!snd (fst (Iso.fun mainC (Iso.inv mainC (f , p))) a) j !}
-- -- -- fst (snd (Iso.rightInv (mainC {A = A} {B = B} {C = C}) (f , p) i) j) x = {!!}
-- -- -- snd (snd (Iso.rightInv (mainC {A = A} {B = B} {C = C}) (f , p) i) j) k = {!!}
-- -- -- Iso.leftInv mainC = {!!}


-- -- -- smashFunAlt : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ) (B : Pointed ℓ') (C : Type ℓ'') → Type _
-- -- -- smashFunAlt A B C = (Σ[ l ∈ C ] Σ[ r ∈ C ]
-- -- --                             Σ[ pr ∈ (typ A → typ B → C) ]
-- -- --                             Σ[ glel ∈ ((a : typ A) → pr a (pt B) ≡ l) ]
-- -- --                             ((b : typ B) → pr (pt A) b ≡ r))

-- -- -- test1 : (C : Type ℓ) → Iso (Smash A B → C)
-- -- --                             (smashFunAlt A B C)
-- -- -- Iso.fun (test1 C) f =
-- -- --   (f basel) , (f baser , (λ x y → f (proj x y))
-- -- --             , ((λ a i → f (gluel a i))
-- -- --             , λ b i → f (gluer b i)))
-- -- -- Iso.inv (test1 C) (l , r , pr , glel , gler) basel = l
-- -- -- Iso.inv (test1 C) (l , r , pr , glel , gler) baser = r
-- -- -- Iso.inv (test1 C) (l , r , pr , glel , gler) (proj x y) = pr x y
-- -- -- Iso.inv (test1 C) (l , r , pr , glel , gler) (gluel a i) = glel a i
-- -- -- Iso.inv (test1 C) (l , r , pr , glel , gler) (gluer b i) = gler b i
-- -- -- Iso.rightInv (test1 C) _ = refl
-- -- -- Iso.leftInv (test1 C) f =
-- -- --   funExt λ {basel → refl ; baser → refl ; (proj x y) → refl ; (gluel a i) → refl ; (gluer b i) → refl}

-- -- -- woho : Smash A B → Unit
-- -- -- woho basel = {!!}
-- -- -- woho baser = {!!}
-- -- -- woho (proj x y) = {!!}
-- -- -- woho (gluel a i) = {!gluel a!}
-- -- -- woho (gluer b i) = {!!}



-- -- -- pFunAlt : (C : Type ℓ) → Iso ((A →∙ B) → C) (smashFunAlt A B C) -- (Σ[ g ∈ (typ A → typ B → C) ] {!!})
-- -- -- Iso.fun (pFunAlt {A = A} {B = B} C) f = f ((λ _ → pt B) , refl) , (f ((λ _ → pt B) , refl))
-- -- --                                       , {!!} , {!!}
-- -- -- Iso.inv (pFunAlt C) = {!!}
-- -- -- Iso.rightInv (pFunAlt C) = {!!}
-- -- -- Iso.leftInv (pFunAlt C) = {!!}

-- -- -- test : (C : Type ℓ) → Iso (Smash A B → C) ((A →∙ B) → C)
-- -- -- Iso.fun (test C) f = {!!}
-- -- -- Iso.inv (test C) = {!!}
-- -- -- Iso.rightInv (test C) = {!!}
-- -- -- Iso.leftInv (test C) = {!!}
-- -- -- -}





-- -- -- loop2 : Path (S₊ 2) north north
-- -- -- loop2 i = (merid (loop i) ∙ sym (merid base)) i

-- -- -- loop2' : Path (S₊ 2) north north
-- -- -- loop2' i = (merid (loop (~ i)) ∙ sym (merid base)) i

-- -- -- surf' : Path (Path (S₊ 2) north north) refl refl
-- -- -- surf' i j = hcomp (λ k → λ { (i = i0) → rCancel(merid base) k j
-- -- --                             ; (i = i1) → rCancel(merid base) k j
-- -- --                             ; (j = i0) → north
-- -- --                             ; (j = i1) → north})
-- -- --                   ((merid (loop i) ∙ sym (merid base)) j)



-- -- -- Test : Smash (S¹ , base) (S¹ , base) → S₊ 2
-- -- -- Test basel = north
-- -- -- Test baser = north
-- -- -- Test (proj base base) = north
-- -- -- Test (proj base (loop i)) = north
-- -- -- Test (proj (loop i) base) = north
-- -- -- Test (proj (loop i) (loop j)) =
-- -- --   hcomp (λ k → λ {(i = i0) → rCancel(merid base) k j ; (i = i1) → rCancel(merid base) k j ; (j = i0) → north ; (j = i1) → north})
-- -- --         ((merid (loop i) ∙ sym (merid base)) j)
-- -- -- Test (gluel base i) = loop2 i
-- -- -- Test (gluel (loop j) i) = {!!}
-- -- -- Test (gluer base i) = loop2' i
-- -- -- Test (gluer (loop j) i) = {!!}

-- -- -- fillSq : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → PathP (λ i → p i ≡ p i) refl refl
-- -- -- fillSq {x = x} = J (λ y p → PathP (λ i → p i ≡ p i) refl refl) refl

-- -- -- Test2 : Smash (S¹ , base) (S¹ , base) → S²
-- -- -- Test2 basel = base
-- -- -- Test2 baser = base
-- -- -- Test2 (proj base base) = base
-- -- -- Test2 (proj base (loop i)) = base
-- -- -- Test2 (proj (loop i) base) = base
-- -- -- Test2 (proj (loop i) (loop j)) = surf i j
-- -- -- Test2 (gluel base i) = surf i i
-- -- -- Test2 (gluel (loop j) i) = fillSq (λ i → surf i i) i j
-- -- -- Test2 (gluer base i) = surf (~ i) (~ i)
-- -- -- Test2 (gluer (loop j) i) = fillSq (λ i → surf (~ i) (~ i) ) i j

-- -- -- S²→S2 : S² → S₊ 2
-- -- -- S²→S2 base = north
-- -- -- S²→S2 (surf i j) = surf' i j


-- -- -- remTrunc : hLevelTrunc 3 S¹ → S¹
-- -- -- remTrunc = trRec isGroupoidS¹ λ x → x

-- -- -- _⌣_ : ∀ {ℓ} {A : Type ℓ} → coHom 1 A → coHom 1 A → coHom 2 A
-- -- -- _⌣_ = sRec2 setTruncIsSet λ f g → ∣ (λ x → ∣ S²→S2 (Test2 (proj (remTrunc (f x)) (remTrunc (g x)))) ∣) ∣₂

-- -- -- open import Cubical.ZCohomology.Groups.Torus as T2
-- -- -- open import Cubical.ZCohomology.Groups.WedgeOfSpheres as Wedge
-- -- -- open import Cubical.Data.Int


-- -- -- left : Int × Int
-- -- -- left = (1 , 0)

-- -- -- right : Int × Int
-- -- -- right = (0 , 1)

-- -- -- c : Int
-- -- -- c = T2.to₂ (T2.from₁ left ⌣ T2.from₁ right)

-- -- -- private
-- -- --   variable
-- -- --     ℓ : Level
-- -- --     A B : Type ℓ
-- -- --     a : A
-- -- -- open import Cubical.Data.Prod
-- -- -- smashS1>' : ((A , a) ⋀ (S¹ , base)) → (Susp A)
-- -- -- smashS1>' (inl x) = north
-- -- -- smashS1>' (inr (x , base)) = north
-- -- -- (smashS1>' {a = a}) (inr (x , loop i)) = ((merid x) ∙ sym (merid a)) i
-- -- -- smashS1>' (push (inl x) i) = north
-- -- -- smashS1>' (push (inr base) i) = north
-- -- -- (smashS1>' {a = a}) (push (inr (loop j)) i) = rCancel (merid a) (~ i) j
-- -- -- (smashS1>' {a = a}) (push (push x j) i) = north

-- -- -- smashS1<' : Susp A → ((A , a) ⋀ (S¹ , base)) 
-- -- -- smashS1<' north = inl tt
-- -- -- smashS1<' south = inl tt
-- -- -- (smashS1<' {a = a}) (merid x i) =
-- -- --            (push (inl x) ∙∙ (λ i → inr (x , loop i)) ∙∙ sym (push (inl x))) i

-- -- -- fillerSq : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (q : x ≡ y)
-- -- --         → (p ≡ q) → I → I → I → A  
-- -- -- fillerSq {x = x} p q PQ i j z =
-- -- --   hfill (λ k → λ { (i = i0) → q (j ∧ ~ k)
-- -- --                   ; (i = i1) → p j
-- -- --                   ; (j = i0) → x
-- -- --                   ; (j = i1) → q (i ∨ (~ k))})
-- -- --         (inS (PQ (~ i) j))
-- -- --         z

-- -- -- test2-filler : (a : A) → I → I → I → (A , a) ⋀ (S¹ , base)
-- -- -- test2-filler a i j k =
-- -- --   hfill (λ k → λ { (i = i0) → doubleCompPath-filler
-- -- --                                              (push (push tt (~ k)))
-- -- --                                              (λ i → inr (a , loop (~ i)))
-- -- --                                              (sym (push (push tt (~ k)))) k j
-- -- --                             ; (i = i1) → inl tt
-- -- --                             ; (j = i0) → push (push tt (~ k ∨ i)) (~ k ∧ ~ i)
-- -- --                             ; (j = i1) → push (push tt (~ k ∨ i)) (~ k ∧ ~ i) })
-- -- --                   (inS (push (inr (loop (~ j))) (~ i)))
-- -- --                   k

-- -- -- test2 : (a : A) → cong (smashS1<' {a = a}) (sym (merid a)) ≡ refl
-- -- -- test2 a i j = test2-filler a i j i1

-- -- -- diff-helper₁ : ∀ {ℓ} {A : Type ℓ} (x a : A) → Square (push (inl x)) (push (inl x))
-- -- --                   (cong (smashS1<' {a = a}) (merid x ∙ sym (merid a)))
-- -- --                   λ i → inr (x , loop i)
-- -- -- diff-helper₁ x a i j =
-- -- --   hcomp (λ k → λ { (i = i0) → push (inl x) j
-- -- --                   ; (i = i1) → push (inl x) j
-- -- --                   ; (j = i0) → (cong-∙ (smashS1<' {a = a}) (merid x) (sym (merid a))) (~ k) i
-- -- --                   ; (j = i1) → inr (x , loop i)})
-- -- --     (hcomp (λ k → λ { (i = i0) → {!!}
-- -- --                      ; (i = i1) → {!cong (smashS1<' {a = a}) (sym (merid a))!}
-- -- --                      ; (j = i0) → compPath-filler (cong (smashS1<' {a = a}) (merid x)) (cong (smashS1<' {a = a}) (sym (merid a))) k i
-- -- --                      ; (j = i1) → {!!}})
-- -- --                   {!!})

-- -- -- diff-helper : ∀ {ℓ} {A : Type ℓ} (x a : A) → Square (push (inl x)) (push (inl x))
-- -- --                   (cong (smashS1<' {a = a}) (merid x ∙ sym (merid a)))
-- -- --                   λ i → inr (x , loop i)
-- -- -- diff-helper x a i j = hcomp (λ k → λ { (i = i0) → push (inl x) (j ∧ k)
-- -- --                                       ; (i = i1) → push (inl x) (j ∧ k)
-- -- --                                       ; (j = i0) → (cong-∙ (smashS1<' {a = a}) (merid x) (sym (merid a))) (~ k) i
-- -- --                                       ; (j = i1) → doubleCompPath-filler (push (inl x))
-- -- --                                                                           (λ i → inr (x , loop i))
-- -- --                                                                           (sym (push (inl x))) (~ k) i})
-- -- --                             (hcomp (λ k → λ { (i = i0) → inl tt
-- -- --                                              ; (i = i1) → test2 a j k
-- -- --                                              ; (j = i1) → smashS1<' {a = a} (merid x i)})
-- -- --                                    (smashS1<' {a = a} (merid x i)))

-- -- -- diff-helper'' : ∀ {ℓ} {A : Type ℓ} (a : A) → Square (push (inl a)) (push (inl a))
-- -- --                   (cong (smashS1<' {a = a}) (merid a ∙ sym (merid a)))
-- -- --                   λ i → inr (a , loop i)
-- -- -- diff-helper'' a i j = hcomp (λ k → λ { (i = i0) → push (inl a) (j ∧ k)
-- -- --                                       ; (i = i1) → push (inl a) (j ∧ k)
-- -- --                                       ; (j = i0) → (cong (cong (smashS1<' {a = a})) (rCancel (merid a))
-- -- --                                                    ∙ sym (rCancel (cong (smashS1<' {a = a}) (merid a)))) (~ k) i
-- -- --                                       ; (j = i1) → doubleCompPath-filler (push (inl a))
-- -- --                                                                           (λ i → inr (a , loop i))
-- -- --                                                                           (sym (push (inl a))) (~ k) i})
-- -- --                             (hcomp (λ k → λ { (i = i0) → inl tt
-- -- --                                              ; (i = i1) → test2 a j k
-- -- --                                              ; (j = i1) → smashS1<' {a = a} (merid a i)})
-- -- --                                    (smashS1<' {a = a} (merid a i)))

-- -- -- diff-helper-part2 : ∀ {ℓ} {A : Type ℓ} (a : A) → I → I → I → (A , a) ⋀ (S¹ , base)
-- -- -- diff-helper-part2 a i j k =
-- -- --    hfill (λ k → λ { (i = i0) → inl tt
-- -- --                    ; (i = i1) → test2 a j k
-- -- --                    ; (j = i1) → smashS1<' {a = a} (merid a i)})
-- -- --          (inS (smashS1<' {a = a} (merid a i)))
-- -- --          k

-- -- -- diff-helper₀ : diff-helper a a ≡ diff-helper'' a
-- -- -- diff-helper₀ {a = a} z i j =
-- -- --   hcomp (λ k → λ { (i = i0) → push (inl a) (j ∧ k)
-- -- --                   ; (i = i1) → push (inl a) (j ∧ k)
-- -- --                   ; (j = i0) → helper z (~ k) i
-- -- --                   ; (j = i1) → doubleCompPath-filler (push (inl a))
-- -- --                                                       (λ i → inr (a , loop i))
-- -- --                                                       (sym (push (inl a))) (~ k) i})
-- -- --         (hcomp (λ k → λ { (i = i0) → inl tt
-- -- --                          ; (i = i1) → test2 a j k
-- -- --                          ; (j = i1) → smashS1<' {a = a} (merid a i)})
-- -- --                (smashS1<' {a = a} (merid a i)))
-- -- --   where
-- -- --   helper : (cong-∙ (smashS1<' {a = a}) (merid a) (sym (merid a)))
-- -- --           ≡ cong (cong (smashS1<' {a = a})) (rCancel (merid a)) ∙ sym (rCancel (cong (smashS1<' {a = a}) (merid a)))
-- -- --   helper = (rUnit (cong-∙ smashS1<' (merid a) (sym (merid a)))
-- -- --           ∙ cong (cong-∙ smashS1<' (merid a) (sym (merid a)) ∙_) (sym (rCancel (rCancel (cong (smashS1<' {a = a}) (merid a))))))
-- -- --         ∙∙ assoc _ _ _
-- -- --         ∙∙ cong (_∙ sym (rCancel (cong (smashS1<' {a = a}) (merid a)))) (cong-∙+rCancel (smashS1<' {a = a}) (merid a))

-- -- -- {-
-- -- -- diff-helper₀ : diff-helper a a ≡ {!!}
-- -- -- diff-helper₀ {a = a} =
-- -- --   (λ r i j → hcomp (λ k → λ { (i = i0) → push (inl a) (j ∧ (k ∨ r))
-- -- --                               ; (i = i1) → push (inl a) (j ∧ (k ∨ r))
-- -- --                               ; (j = i0) → (cong-∙ (smashS1<' {a = a}) (merid a) (sym (merid a))) (~ k ∧ ~ r) i
-- -- --                               ; (j = i1) → doubleCompPath-filler (push (inl a))
-- -- --                                                                           (λ i → inr (a , loop i))
-- -- --                                                                           (sym (push (inl a))) (~ k ∧ ~ r) i})
-- -- --                     (hcomp (λ k → λ { (i = i0) → push (inl a) (j ∧ r)
-- -- --                                      ; (j = i0) → {!(-cong-∙∙ (smashS1<' {a = a}) (merid a) (sym (merid a))) (~ k ∧ ~ r) i!}
-- -- --                                      ; (i = i1) → {!!}
-- -- --                                      ; (j = i1) → {!!}})
-- -- --                             {!!}))
-- -- --    ∙∙ {!!} ∙∙ {!!}
-- -- -- -}

-- -- -- smashS1' : Iso ((A , a) ⋀ (S¹ , base)) (Susp A)
-- -- -- Iso.fun smashS1' = smashS1>'
-- -- -- Iso.inv smashS1' = smashS1<'
-- -- -- Iso.rightInv smashS1' north = refl
-- -- -- Iso.rightInv (smashS1' {a = a}) south = merid a
-- -- -- Iso.rightInv (smashS1' {a = a}) (merid x i) j =
-- -- --   helper j i
-- -- --   where
-- -- --   helper : PathP (λ i → north ≡ merid a i)
-- -- --                  (cong (smashS1>' {a = a}) (push (inl x)
-- -- --                               ∙∙ (λ j → inr (x , loop j))
-- -- --                                ∙∙ sym (push (inl x))))
-- -- --                  (merid x)
-- -- --   helper i j =
-- -- --     hcomp (λ k → λ { (i = i0) → cong-∙∙ (smashS1>' {a = a}) (push (inl x))
-- -- --                                                     (λ j₂ → inr (x , loop j₂))
-- -- --                                                     (sym (push (inl x))) (~ k) j
-- -- --                     ; (i = i1) → compPath-filler (merid x) (λ i → merid a ((~ i) ∨ k)) (~ k) j
-- -- --                     ; (j = i0) → north
-- -- --                     ; (j = i1) → merid a (i ∧ k) })
-- -- --           (rUnit (merid x ∙ sym (merid a)) (~ i) j)
-- -- -- Iso.leftInv (smashS1' {a = a}) (inl x) = refl
-- -- -- Iso.leftInv (smashS1' {a = a}) (inr (x , base)) = push (inl x)
-- -- -- Iso.leftInv (smashS1' {a = a}) (push (push tt i) j) k =
-- -- --   hcomp (λ r → λ {(i = i0) → push (inl a) ((j ∨ ~ r) ∧ k)
-- -- --                  ; (j = i0) →  (push (push tt i)) (k ∧ ~ r)
-- -- --                  ; (j = i1) →  (push (inl a)) k
-- -- --                  ; (k = i0) →  inl tt
-- -- --                  ; (k = i1) → (push (push tt i)) (j ∨ ~ r) })
-- -- --         (push (push tt (i ∧ ~ j)) k)
-- -- -- Iso.leftInv (smashS1' {a = a}) (inr (x , loop i)) j = diff-helper x a i j
-- -- -- Iso.leftInv (smashS1' {a = a}) (push (inl x) i) k = push (inl x) (i ∧ k)
-- -- -- Iso.leftInv (smashS1' {a = a}) (push (inr base) i) j =
-- -- --   fillerSq (push (inl a)) (push (inr base)) (cong push (push tt)) i j i1
-- -- -- Iso.leftInv (smashS1' {a = a}) (push (inr (loop j)) i) k =
-- -- --   hcomp (λ r → λ { (i = i0) → inl tt
-- -- --                   ; (i = i1) → helper (~ r) j k
-- -- --                   ; (j = i0) → fillerSq (push (inl a)) (push (inr base))
-- -- --                                          (λ i₁ → push (push tt i₁)) i k i1
-- -- --                   ; (j = i1) → fillerSq (push (inl a)) (push (inr base))
-- -- --                                          (λ i₁ → push (push tt i₁)) i k i1
-- -- --                   ; (k = i0) → (smashS1<' {a = a}) (rCancel (merid a) (~ i) j)
-- -- --                   ; (k = i1) → push (inr (loop j)) i})
-- -- --         (hcomp (λ r → λ { (i = i0) → inl tt
-- -- --                          ; (i = i1) → helpie j k r
-- -- --                          ; (j = i0) → fillerSq (push (inl a)) (push (inr base))
-- -- --                                                 (λ i₁ → push (push tt i₁)) i k i1
-- -- --                          ; (j = i1) → fillerSq (push (inl a)) (push (inr base))
-- -- --                                                 (λ i₁ → push (push tt i₁)) i k i1
-- -- --                          ; (k = i0) → (smashS1<' {a = a}) (rCancel (merid a) (~ i ∨ ~ r) j)
-- -- --                          ; (k = i1) → push (inr (loop j)) i})
-- -- --                (hcomp (λ r → λ { (i = i0) → push (inr (loop j)) (k ∧ ~ r)
-- -- --                                 ; (i = i1) → helpie2 j k r
-- -- --                                 ; (j = i0) → fillerSq (push (push tt (~ r))) (push (inr base))
-- -- --                                                        (λ j → push (push tt (~ r ∨ j))) i k r
-- -- --                                 ; (j = i1) → fillerSq (push (push tt (~ r))) (push (inr base))
-- -- --                                                        (λ j → push (push tt (~ r ∨ j))) i k r
-- -- --                                 ; (k = i0) → inl tt
-- -- --                                 ; (k = i1) → push (inr (loop j)) (i ∨ ~ r)})
-- -- --                        (push (inr (loop j)) k)))
-- -- --   where
-- -- --   helpie2 : I → I → I → (_ , a) ⋀ (S¹ , base)
-- -- --   helpie2 i j z = hfill (λ k → λ {(i = i0) → push (push tt (~ k)) j
-- -- --                                  ; (i = i1) → push (push tt (~ k)) j
-- -- --                                  ; (j = i0) → inl tt
-- -- --                                  ; (j = i1) → inr (a , loop i)})
-- -- --                             (inS (push (inr (loop i)) j))
-- -- --                             z

-- -- --   helpie : I → I → I → (_ , a) ⋀ (S¹ , base)
-- -- --   helpie i j z =
-- -- --     hfill (λ k → λ { (i = i0) → push (inl a) j
-- -- --                     ; (i = i1) → push (inl a) j
-- -- --                     ; (j = i0) → smashS1<' {a = a} (rCancel(merid a) (~ k) i)
-- -- --                     ; (j = i1) → inr (a , loop i)})
-- -- --           (inS (helpie2 i j i1))
-- -- --           z

-- -- --   helppath :  PathP
-- -- --       (λ i₁ →
-- -- --          cong (smashS1<' {a = a}) (merid a ∙ sym (merid a)) i₁ ≡ inr (a , loop i₁))
-- -- --       (push (inl a)) (push (inl a))
-- -- --   helppath i j = helpie i j i1

-- -- -- {-
-- -- -- diff-helper : ∀ {ℓ} {A : Type ℓ} (x a : A) → Square (push (inl x)) (push (inl x))
-- -- --                   (cong (smashS1<' {a = a}) (merid x ∙ sym (merid a)))
-- -- --                   λ i → inr (x , loop i)
-- -- -- diff-helper x a i j = hcomp (λ k → λ { (i = i0) → push (inl x) (j ∧ k)
-- -- --                                       ; (i = i1) → push (inl x) (j ∧ k)
-- -- --                                       ; (j = i0) → (cong-∙ (smashS1<' {a = a}) (merid x) (sym (merid a))) (~ k) i
-- -- --                                       ; (j = i1) → doubleCompPath-filler (push (inl x))
-- -- --                                                                           (λ i → inr (x , loop i))
-- -- --                                                                           (sym (push (inl x))) (~ k) i})
-- -- --                             (hcomp (λ k → λ { (i = i0) → inl tt
-- -- --                                              ; (i = i1) → test2 a j k
-- -- --                                              ; (j = i1) → smashS1<' {a = a} (merid x i)})
-- -- --                                    (smashS1<' {a = a} (merid x i)))
-- -- -- -}


-- -- --   {-
-- -- -- r = i0 ⊢ ?5 (j = j₁) (i = i₁) (k = k) (k = i1) (i = i) (j = j)
-- -- -- r = i1 ⊢ helppath i j
-- -- -- i = i0 ⊢ push (inl a) (r ∧ j)
-- -- -- i = i1 ⊢ push (inl a) (r ∧ j)
-- -- -- j = i0 ⊢ cong-∙ smashS1<' (merid a) (sym (merid a)) (~ r) i
-- -- -- j = i1 ⊢ doubleCompPath-filler (push (inl a))
-- -- --          (λ i₂ → inr (a , loop i₂)) (sym (push (inl a))) (~ r) i
-- -- --   -}

-- -- --   te : Cube (λ i j → rCancel (cong (smashS1<' {a = a}) (merid a)) i j)
-- -- --             (λ i j → smashS1<' {a = a} (rCancel (merid a) i j))
-- -- --             (λ i j → ((cong (cong (smashS1<' {a = a})) (rCancel (merid a))) ∙ (sym (rCancel (cong (smashS1<' {a = a}) (merid a))))) (~ i) j) (λ _ _ → inl tt)
-- -- --             (λ _ _ → inl tt) λ _ _ → inl tt
-- -- --   te r i j =
-- -- --     hcomp (λ k → λ { (i = i0) → compPath-filler ((cong (cong (smashS1<' {a = a})) (rCancel (merid a))))
-- -- --                                                            (sym (rCancel (cong (smashS1<' {a = a}) (merid a)))) k (~ r) j
-- -- --                     ; (i = i1) → inl tt
-- -- --                     ; (j = i0) → inl tt
-- -- --                     ; (j = i1) → inl tt
-- -- --                     ; (r = i0) → rCancel (cong (smashS1<' {a = a}) (merid a)) (i ∨ ~ k) j
-- -- --                     ; (r = i1) → smashS1<' {a = a} (rCancel (merid a) i j)})
-- -- --                    (smashS1<' {a = a} (rCancel (merid a) (i ∨ ~ r) j))


-- -- --   ti : Cube {A = (_ , a) ⋀ (S¹ , base)} (λ i j → test2 a i (~ j)) (λ i j → inr (a , loop j))
-- -- --             (λ r j → doubleCompPath-filler (push (inl a)) (λ i → inr (a , loop i)) (sym (push (inl a))) (~ r) j) (λ r j → push (inr (loop j)) r)
-- -- --             (λ j r → push (push tt r) j) λ j r → push (push tt r) j
-- -- --   ti = {!!}

-- -- --   test4-annoying : Path (Path ((_ , a) ⋀ (S¹ , base)) (inr (a , base)) (inr (a , base))) (λ i → inr (a , loop i)) refl
 
-- -- --   test4-annoying = {!!}


-- -- --   test3-annoying : Cube {A = (_ , a) ⋀ (S¹ , base)}
-- -- --                    (λ k r → {!push (push tt (~ r)) (k ∨ r)!}) (λ r k → helpie r k i0)
-- -- --                    (λ j k → push (push tt (~ j)) k)
-- -- --                    (λ j k → push (push tt (~ k ∧ ~ j)) k)
-- -- --                    (λ j r → inl tt)
-- -- --                     λ j r → inr (a , loop r)
-- -- --   test3-annoying j k r =
-- -- --      hcomp (λ i → λ { (j = i0) → {!!}
-- -- --                      ; (j = i1) → {!!} -- helpie2 (k ∨ ~ i) r i
-- -- --                      ; (k = i0) → {!!} -- push (push tt (~ j ∨ ~ i)) r
-- -- --                      ; (k = i1) → {!!} -- push (push tt ((~ r ∧ ~ j) ∨ (~ i))) r
-- -- --                      ; (r = i0) → inl tt
-- -- --                      ; (r = i1) → test4-annoying i k})
-- -- --              {!!}
-- -- -- {-
-- -- -- j = i0 ⊢ ?9 k r
-- -- -- j = i1 ⊢ helpie k r i0
-- -- -- k = i0 ⊢ push (push tt (~ j)) r
-- -- -- k = i1 ⊢ push (push tt (~ r ∧ ~ j)) r
-- -- -- r = i0 ⊢ refl k
-- -- -- r = i1 ⊢ inr (a , loop k)
-- -- -- -}

-- -- --   test2-annoying : Cube {A = (_ , a) ⋀ (S¹ , base)} (λ i k → push (inl a) (i ∧ k)) (λ i k → push (inl a) (i ∧ k))
-- -- --                         (λ r k → diff-helper-part2 a r k i1) (λ r k → helpie r k i0)
-- -- --                         (λ r i → rCancel (cong smashS1<' (merid a)) i r)
-- -- --                         λ r i → doubleCompPath-filler (push (inl a)) (λ i → inr (a , loop i))
-- -- --                                                                           (sym (push (inl a))) (~ i) r
                        
-- -- --   test2-annoying r i k =
-- -- --     hcomp (λ j → λ { (i = i0) → diff-helper-part2 a r k i1 -- i1
-- -- --                     ; (i = i1) → {!!} -- test3-annoying j r k
-- -- --                     ; (k = i0) → rCancel (cong smashS1<' (merid a)) i r
-- -- --                     ; (k = i1) → doubleCompPath-filler (push (push tt (~ j ∧ ~ r ∧ i)))
-- -- --                                                          (λ i₂ → inr (a , loop i₂)) (sym (push (push tt (~ j ∧ ~ r ∧ i)))) (~ i) r
-- -- --                     ; (r = i0) → push (push tt (~ j ∧ i)) (i ∧ k)
-- -- --                     ; (r = i1) → push (push tt (~ k ∧ ~ j ∧ i)) (i ∧ k) })
-- -- --           {!diff-helper-part2 a r k i1!}

-- -- -- {-
-- -- -- r = i0 ⊢ push (inl a) (i ∧ k)
-- -- -- r = i1 ⊢ push (inl a) (i ∧ k)
-- -- -- i = i0 ⊢ diff-helper-part2 a r k i1
-- -- -- i = i1 ⊢ helpie r k i0
-- -- -- k = i0 ⊢ rCancel (cong smashS1<' (merid a)) i r
-- -- -- k = i1 ⊢ doubleCompPath-filler (push (inl a))
-- -- --          (λ i₂ → inr (a , loop i₂)) (sym (push (inl a))) (~ i) r
-- -- -- -}

-- -- --   helper2' : diff-helper'' a ≡ helppath
-- -- --   helper2' i j k =
-- -- --     hcomp (λ r → λ { (i = i1) → helpie j k r
-- -- --                     ; (j = i0) → push (inl a) ((r ∨ i) ∧ k)
-- -- --                     ; (j = i1) → push (inl a) ((r ∨ i) ∧ k)
-- -- --                     ; (k = i0) → compPath-filler (cong (cong (smashS1<' {a = a})) (rCancel (merid a)))
-- -- --                                                    (sym (rCancel (cong (smashS1<' {a = a}) (merid a)))) (~ i) (~ r) j
-- -- --                     ; (k = i1) → doubleCompPath-filler (push (inl a)) (λ i → inr (a , loop i))
-- -- --                                                                           (sym (push (inl a))) (~ r ∧ ~ i) j})
-- -- --            (hcomp (λ r → λ { (i = i0) → diff-helper-part2 a (j ∧ r) k i1
-- -- --                              ; (i = i1) → helpie (j ∧ r) k i0
-- -- --                              ; (j = i0) → push (inl a) (i ∧ k) -- push (push tt (i ∧ ~ r)) (i ∧ k)
-- -- --                              ; (j = i1) → {!!}
-- -- --                              ; (k = i0) → compPath-filler (cong (cong (smashS1<' {a = a})) (rCancel (merid a)))
-- -- --                                                    (sym (rCancel (cong (smashS1<' {a = a}) (merid a)))) (~ i) i1 (j ∧ r)
-- -- --                              ; (k = i1) → doubleCompPath-filler (push (inl a)) (λ i → inr (a , loop i))
-- -- --                                                                           (sym (push (inl a))) (~ i) (j ∧ r)})
-- -- --                             {!!})


-- -- -- {-
-- -- -- helpie2
-- -- -- -}

-- -- -- {-
-- -- -- i = i0 ⊢ diff-helper'' a j k
-- -- -- i = i1 ⊢ helppath j k
-- -- -- j = i0 ⊢ push (inl a) k
-- -- -- j = i1 ⊢ push (inl a) k
-- -- -- k = i0 ⊢ cong smashS1<' (merid a ∙ sym (merid a)) j
-- -- -- k = i1 ⊢ inr (a , loop j)
-- -- -- -}
    
-- -- --   {-
-- -- --     hcomp (λ r → λ { (i = i0) → diff-helper'' a j k
-- -- --                     ; (i = i1) → helpie j k r
-- -- --                     ; (j = i0) → push (inl a) k
-- -- --                     ; (j = i1) → push (inl a) k
-- -- --                     ; (k = i0) → smashS1<' {a = a} (rCancel (merid a) (i ∧ ~ r) j)
-- -- --                     ; (k = i1) → inr (a , loop j)})
-- -- --           (hcomp (λ r → λ { (i = i0) → diff-helper'' a j k
-- -- --                            ; (i = i1) → helpie2 j k r
-- -- --                            ; (j = i0) → push (push tt (~ r ∧ i)) k
-- -- --                            ; (j = i1) → push (push tt (~ r ∧ i)) k
-- -- --                            ; (k = i0) → smashS1<' {a = a} (rCancel (merid a) i j)
-- -- --                            ; (k = i1) → inr (a , loop j)})
-- -- --                      (hcomp (λ r → λ { (i = i1) → push (inr (loop j)) (k ∧ r)
-- -- --                                       ; (j = i0) → push (push tt i) (k ∧ r)
-- -- --                                       ; (j = i1) → push (push tt i) (k ∧ r)
-- -- --                                       ; (k = i0) → te r i j
-- -- --                                       ; (k = i1) → ti r i j})
-- -- --                             (hcomp (λ r → λ { (i = i1) → {!push (inl a) (i ∨ r)!}
-- -- --                                       ; (j = i0) → inl tt -- inl tt
-- -- --                                       ; (j = i1) → test2 a i (~ r ∧ k) -- test2 a i (r ∨ k) -- test2 a r k
-- -- --                                       ; (k = i0) → rCancel (cong (smashS1<' {a = a}) (merid a)) i j -- rCancel (cong (smashS1<' {a = a}) (merid a)) i j
-- -- --                                       ; (k = i1) → test2 a i (~ j ∨ ~ r)})
-- -- --                                    {!!}))) -}

-- -- --   {-
-- -- -- k = i0 ⊢ diff-helper'' a i j
-- -- -- k = i1 ⊢ helppath i j
-- -- -- i = i0 ⊢ push (inl a) j
-- -- -- i = i1 ⊢ push (inl a) j
-- -- -- j = i0 ⊢ cong smashS1<' (merid a ∙ sym (merid a)) i
-- -- -- j = i1 ⊢ inr (a , loop i)
-- -- --   -}

-- -- --   helper : diff-helper a a ≡ helppath
-- -- --   helper i j k =
-- -- --     hcomp (λ r → λ { (i = i0) → diff-helper a a j k
-- -- --                     ; (i = i1) → helpie j k r
-- -- --                     ; (j = i0) → push (inl a) k
-- -- --                     ; (j = i1) → push (inl a) k
-- -- --                     ; (k = i0) → smashS1<' {a = a} (rCancel (merid a) (i ∧ ~ r) j)
-- -- --                     ; (k = i1) → inr (a , loop j)})
-- -- --           (hcomp (λ r → λ { (i = i0) → diff-helper a a j k
-- -- --                            ; (i = i1) → helpie2 j k r
-- -- --                            ; (j = i0) → push (push tt (~ r ∧ i)) k
-- -- --                            ; (j = i1) → push (push tt (~ r ∧ i)) k
-- -- --                            ; (k = i0) → smashS1<' {a = a} (rCancel (merid a) i j)
-- -- --                            ; (k = i1) → inr (a , loop j)})
-- -- --                         (hcomp (λ r → λ { (i = i1) → {!(cong-∙ (smashS1<' {a = a}) (merid ?) (sym (merid a)))!}
-- -- --                                          ; (j = i0) → push (push tt i) (k ∧ r)
-- -- --                                          ; (j = i1) → push (push tt i) (k ∧ r)
-- -- --                                          ; (k = i0) → smashS1<' {a = a} (rCancel-filler' (merid a) (~ r) i {!~ j!})
-- -- --                                          ; (k = i1) → {!!}})
-- -- --                                         {!doubleCompPath-filler (λ j → push (push tt (j ∧ i)) j)
-- -- --                                                                           (λ i → inr (a , loop i))
-- -- --                                                                           (sym (push (push tt i)))!}))
-- -- --     where
-- -- --     taha : {!!}
-- -- --     taha = {!!}
-- -- -- {-
-- -- -- i = i0 ⊢ diff-helper a a j z
-- -- -- i = i1 ⊢ helppath j z
-- -- -- j = i0 ⊢ push (inl a) z
-- -- -- j = i1 ⊢ push (inl a) z
-- -- -- z = i0 ⊢ cong smashS1<' (merid a ∙ sym (merid a)) j
-- -- -- z = i1 ⊢ inr (a , loop j)
-- -- -- -}
-- -- -- {-
-- -- -- j = i0 ⊢ fillerSq (push (inl a)) (push (inr base))
-- -- --          (λ i₁ → push (push tt i₁)) i k i1
-- -- -- j = i1 ⊢ fillerSq (push (inl a)) (push (inr base))
-- -- --          (λ i₁ → push (push tt i₁)) i k i1
-- -- -- i = i0 ⊢ inl tt
-- -- -- i = i1 ⊢ Cubical.ZCohomology.CupTest.helper a j k j k
-- -- -- k = i0 ⊢ hcomp
-- -- --          (λ i₁ .o →
-- -- --             transp (λ i₂ → Pushout (λ _ → tt) i∧) i₁
-- -- --             (smashS1<'
-- -- --              ((λ { ((~ j ∨ j ∨ ~ i) = i1)
-- -- --                      → (λ { (j = i0) → north
-- -- --                           ; (j = i1) → merid a (~ (i1 ∧ i₁) ∧ ~ (~ i))
-- -- --                           ; ((~ i) = i1) → north
-- -- --                           })
-- -- --                        _
-- -- --                  })
-- -- --               _)))
-- -- --          (hcomp
-- -- --           (λ j₁ .o →
-- -- --              transp (λ i₁ → Pushout (λ _ → tt) i∧) i0
-- -- --              (doubleComp-faces (push (inl a)) (λ i₁ → push (inl a) (~ i₁))
-- -- --               (j ∧ i) j₁ _))
-- -- --           (Cubical.HITs.Pushout.Base.transp-Pushout (λ i₁ _ → tt) (λ i₁ → i∧)
-- -- --            i0 (inr (a , loop (j ∧ i)))))
-- -- -- k = i1 ⊢ push (inr (loop j)) i
-- -- -- -}




-- -- -- open import Cubical.Data.Bool
-- -- -- open import Cubical.Foundations.Pointed
-- -- -- projlr : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} → Path (Path (A ⋀ B) _ _) (push (inl (pt A))) (push (inr (pt B))) 
-- -- -- projlr = cong push (push tt)



-- -- -- -- smashS1> : (Smash (A , a) (S¹ , base)) → (Susp A) 
-- -- -- -- smashS1> {a = a} basel = north
-- -- -- -- smashS1> {a = a} baser = south
-- -- -- -- smashS1> {a = a} (proj x base) = north
-- -- -- -- smashS1> {a = a} (proj x (loop i)) = ((merid x) ∙ sym (merid a)) i
-- -- -- -- smashS1> {a = a} (gluel x i) = north
-- -- -- -- smashS1> {a = a} (gluer base i) = merid a i
-- -- -- -- smashS1> {a = a} (gluer (loop j) i) =
-- -- -- --   hcomp (λ k → λ {(i = i0) → rCancel(merid a) (~ k) j
-- -- -- --                  ; (i = i1) → south
-- -- -- --                  ; (j = i1) → merid a i
-- -- -- --                  ; (j = i0) → merid a i})
-- -- -- --         (merid a i)

-- -- -- -- smashS1< : Susp A → (Smash (A , a) (S¹ , base))
-- -- -- -- smashS1< north = basel
-- -- -- -- smashS1< south = base
-- -- -- -- smashS1< {a = a} (merid x i) = {!!}

-- -- -- -- {- ((sym (gluel x) ∙∙ cong (proj x) loop ∙∙ gluel x)
-- -- -- --                ∙∙ sym (gluel a) ∙∙ gluer base) i
-- -- -- -- -}

-- -- -- -- -- smashS1 : Iso (Smash (A , a) (S¹ , base)) (Susp A) 
-- -- -- -- -- Iso.fun smashS1 = smashS1>
-- -- -- -- -- Iso.inv smashS1 = smashS1<
-- -- -- -- -- Iso.rightInv smashS1 north = refl
-- -- -- -- -- Iso.rightInv (smashS1 {a = a}) south = refl
-- -- -- -- -- Iso.rightInv (smashS1 {a = a}) (merid x i) j = helper j i
-- -- -- -- --   where
-- -- -- -- --   helper : cong smashS1> ((sym (gluel x) ∙∙ cong (proj x) loop ∙∙ gluel x)  ∙∙ sym (gluel a) ∙∙ gluer base) ≡ merid x
-- -- -- -- --   helper = cong-∙∙ smashS1> (sym (gluel x) ∙∙ cong (proj x) loop ∙∙ gluel x) (sym (gluel a)) (gluer base)
-- -- -- -- --         ∙∙ (λ i → cong-∙∙ (smashS1> {a = a}) (sym (gluel x))
-- -- -- -- --                                               (cong (proj x) loop) (gluel x) i
-- -- -- -- --                ∙∙ refl ∙∙ merid a)
-- -- -- -- --         ∙∙ (λ i → (rUnit (merid x ∙ (λ j →  merid a (~ j ∨ i))) (~ i)) ∙∙ (λ j → merid a i)  ∙∙ (λ j → merid a (i ∨ j)))
-- -- -- -- --         ∙∙ doubleCompPath-elim (merid x ∙ refl) refl refl
-- -- -- -- --         ∙∙ λ i → rUnit (rUnit (rUnit (merid x) (~ i)) (~ i)) (~ i)

-- -- -- -- -- Iso.leftInv smashS1 basel = refl
-- -- -- -- -- Iso.leftInv smashS1 baser = refl
-- -- -- -- -- Iso.leftInv smashS1 (proj x base) = sym (gluel x)
-- -- -- -- -- Iso.leftInv smashS1 (proj x (loop i)) j = {!!}
-- -- -- -- -- Iso.leftInv smashS1 (gluel a i) = {!!}
-- -- -- -- -- Iso.leftInv smashS1 (gluer base i) j = {!!}
-- -- -- -- -- Iso.leftInv smashS1 (gluer (loop j) i) = {!!}

-- -- -- -- -- test : isSet A → isProp (Smash (A , a) (A , a))
-- -- -- -- -- test {a = a} isSet basel basel = refl
-- -- -- -- -- test {a = a} isSet basel baser = sym (gluel a) ∙ gluer a
-- -- -- -- -- test {a = a} isSet basel (proj x y) = {!!}
-- -- -- -- -- test {a = a} isSet basel (gluel a₁ i) = {!!}
-- -- -- -- -- test {a = a} isSet basel (gluer b i) = {!!}
-- -- -- -- -- test {a = a} isSet baser y = {!!}
-- -- -- -- -- test {a = a} isSet (proj x y₁) y = {!!}
-- -- -- -- -- test {a = a} isSet (gluel a₁ i) y = {!!}
-- -- -- -- -- test {a = a} isSet (gluer b i) y = {!!}

-- -- -- -- -- -- module Torus where
-- -- -- -- -- --   to₂ : coHom 2 (S₊ 1 × S₊ 1) → Int
-- -- -- -- -- --   to₂ = fun (map H²-T²≅ℤ)

-- -- -- -- -- --   from₂ : Int → coHom 2 (S₊ 1 × S₊ 1)
-- -- -- -- -- --   from₂ = inv H²-T²≅ℤ

-- -- -- -- -- --   to₁ : coHom 1 (S₊ 1 × S₊ 1) → Int × Int
-- -- -- -- -- --   to₁ = fun (map H¹-T²≅ℤ×ℤ)

-- -- -- -- -- --   from₁ : Int × Int → coHom 1 (S₊ 1 × S₊ 1)
-- -- -- -- -- --   from₁ = inv H¹-T²≅ℤ×ℤ

-- -- -- -- -- --   to₀ : coHom 0 (S₊ 1 × S₊ 1) → Int
-- -- -- -- -- --   to₀ = fun (map H⁰-T²≅ℤ)

-- -- -- -- -- --   from₀ : Int → coHom 0 (S₊ 1 × S₊ 1)
-- -- -- -- -- --   from₀ = inv H⁰-T²≅ℤ
