{-# OPTIONS --safe #-}
module Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Multiplication
open import Cubical.HITs.Join
open import Cubical.HITs.Join.CoHSpace
open import Cubical.HITs.Wedge
open import Cubical.HITs.SmashProduct

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.WhiteheadProducts.Generalised.Join.Base

open Iso
open 3x3-span

-- Left bilinearity of generalised Whitehead product
module _ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
  (B : Pointed ℓ') {C : Pointed ℓ''}
  (f g : Susp∙ (Susp (typ A)) →∙ C)
  (h : Susp∙ (typ B) →∙ C) where
  private
    σΣA = σ (Susp∙ (typ A))
    Ω→f∙ = cong (Ω→ f .fst) (rCancel (merid north)) ∙ Ω→ f .snd
    Ω→g∙ = cong (Ω→ g .fst) (rCancel (merid north)) ∙ Ω→ g .snd

  WhiteheadProdBilinₗ : ·wh (Susp∙ (typ A)) B (·Susp (Susp∙ (typ A)) f g) h
                     ≡ _+*_ {A = Susp∙ (typ A)} {B = B}
                     (·wh (Susp∙ (typ A)) B f h)
                     (·wh (Susp∙ (typ A)) B g h)
  fst (WhiteheadProdBilinₗ i) (inl x) =
    (Ω→ g .fst (σΣA x) ∙ Ω→ f .fst (σΣA x)) i
  fst (WhiteheadProdBilinₗ i) (inr x) = Ω→ h .fst (σ B x) (~ i)
  fst (WhiteheadProdBilinₗ i) (push a b j) = main i j
    where
    x = Ω→ f .fst (σΣA a)
    y = Ω→ g .fst (σΣA a)
    z = Ω→ h .fst (σ B b)

    fun1 fun2 fun3 : Susp∙ (typ A) →∙ Ω C
    fst fun1 a = z ⁻¹ ∙ (Ω→ g .fst (σΣA a)) ⁻¹ ∙ z
    snd fun1 = cong (z ⁻¹ ∙_) (cong (_∙ z) (cong sym Ω→g∙)
                            ∙ sym (lUnit z))
             ∙ lCancel z
    fst fun2 a = ((z ∙ Ω→ f .fst (σΣA a)) ∙ Ω→ g .fst (σΣA a)) ∙ z ⁻¹
    snd fun2 = cong (_∙ z ⁻¹)
                   (cong₂ _∙_ (cong (z ∙_)
                               Ω→f∙ ∙ sym (rUnit _))
                               Ω→g∙
                 ∙ sym (rUnit _))
            ∙ rCancel z
    fun3 = Ω→ g ∘∙ toSuspPointed (Susp∙ (typ A))

    lem : y ⁻¹ ∙ ((z ∙ x) ∙ y) ∙ z ⁻¹
       ≡ (z ∙ x ∙ z ⁻¹) ∙ ((y ⁻¹ ∙ z) ∙ y) ∙ z ⁻¹
    lem = (sym (funExt⁻ (cong fst
                  (Susp·→Ωcomm A fun2 ((sym , refl) ∘∙ fun3))) a)
        ∙ sym (assoc _ _ _)
        ∙ sym (assoc _ _ _))
        ∙ (λ j → (z ∙ x) ∙ y ∙ z ⁻¹ ∙ (rUnit (y ⁻¹) j))
        ∙ rUnit _
        ∙ (λ i → ((z ∙ x) ∙ y ∙ z ⁻¹ ∙ y ⁻¹
                 ∙ λ j → z (j ∧ i)) ∙ λ j → z (~ j ∧ i))
        ∙ cong (_∙ z ⁻¹)
        (cong ((z ∙ x) ∙_)
            (sym (funExt⁻ (cong fst (Susp·→Ωcomm A fun1 fun3)) a)
           ∙ sym (assoc _ _ _))
        ∙ assoc _ _ _
        ∙ cong₂ _∙_ (sym (assoc z x (z ⁻¹)))
                    refl)
        ∙ sym (assoc _ _ _)

    main : Square (cong (·wh (Susp∙ (typ A)) B
                          (·Susp (Susp∙ (typ A)) f g) h .fst) (push a b))
                  (cong (((·wh (Susp∙ (typ A)) B f h)
                       +* (·wh (Susp∙ (typ A)) B g h)) .fst) (push a b))
                  (y ∙ x) (z ⁻¹)
    main = cong₂ _∙_ refl (sym (rUnit _) ∙ ·Suspσ f g a)
        ∙ assoc z x y
       ◁ doubleCompPath-filler (sym (y ∙ x)) ((z ∙ x) ∙ y) (z ⁻¹)
       ▷ (doubleCompPath≡compPath _ _ _
        ∙ cong₂ _∙_ (symDistr y x) refl
        ∙ sym (assoc (x ⁻¹) (y ⁻¹) _)
        ∙ cong (x ⁻¹ ∙_) lem
        ∙ assoc (x ⁻¹) (z ∙ x ∙ z ⁻¹) (((y ⁻¹ ∙ z) ∙ y) ∙ z ⁻¹)
         ∙ cong₂ _∙_ (cong (x ⁻¹ ∙_) (assoc z x (z ⁻¹)))
                     (cong (_∙ z ⁻¹) (sym (assoc (y ⁻¹) z y))
                     ∙ sym (assoc (y ⁻¹) (z ∙ y) _))
         ∙ sym (cong₂ _∙_ (sym (rUnit _) ∙ cong·wh-ℓ* f h a b
                          ∙ doubleCompPath≡compPath _ _ _)
                          (sym (rUnit _) ∙ cong·wh-ℓ* g h a b
                          ∙ doubleCompPath≡compPath _ _ _)))

  snd (WhiteheadProdBilinₗ i) j = lem j i
    where
    lem : Ω→ g .fst (σΣA north) ∙ Ω→ f .fst (σΣA north)
       ≡ refl
    lem = cong₂ _∙_ Ω→g∙ Ω→f∙
        ∙ sym (rUnit refl)

  -- -- ·whΣ version
  -- WhiteheadProdΣBilinₗ : ·whΣ (Susp∙ (typ A)) B (·Susp (Susp∙ (typ A)) f g) h
  --                    ≡ ·Susp (Susp∙ (typ A) ⋀∙ B)
  --                            (·whΣ (Susp∙ (typ A)) B f h)
  --                            (·whΣ (Susp∙ (typ A)) B g h)
  -- WhiteheadProdΣBilinₗ =
  --   transport (λ j
  --     → PathP-·wh-·whΣ (Susp∙ (typ A)) B
  --         (·Susp (Susp∙ (typ A)) f g) h (~ j)
  --     ≡ ·Susp-+*-PathP {A = Susp∙ (typ A)} {B} {C} (~ j)
  --       (PathP-·wh-·whΣ (Susp∙ (typ A)) B f h (~ j))
  --       (PathP-·wh-·whΣ  (Susp∙ (typ A)) B g h (~ j)))
  --     WhiteheadProdBilinₗ

-- Right bilinearity of generalised whitehead product
module _ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
  (B : Pointed ℓ') {C : Pointed ℓ''}
  (f : Susp∙ (typ A) →∙ C)
  (g h : Susp∙ (Susp (typ B)) →∙ C) where
  private
    σΣB = σ (Susp∙ (typ B))
    Ω→f∙ = cong (Ω→ f .fst) (rCancel (merid (pt A))) ∙ Ω→ f .snd
    Ω→g∙ = cong (Ω→ g .fst) (rCancel (merid north)) ∙ Ω→ g .snd
    Ω→h∙ = cong (Ω→ h .fst) (rCancel (merid north)) ∙ Ω→ h .snd

  WhiteheadProdBilinᵣ : ·wh A (Susp∙ (typ B)) f (·Susp (Susp∙ (typ B)) g h)
                     ≡ _+*_ {A = A} {B = Susp∙ (typ B)}
                            (·wh A (Susp∙ (typ B)) f g)
                            (·wh A (Susp∙ (typ B)) f h)
  fst (WhiteheadProdBilinᵣ i) (inl x) = Ω→ f .fst (σ A x) i
  fst (WhiteheadProdBilinᵣ i) (inr x) =
    (Ω→ h .fst (σΣB x) ∙ Ω→ g .fst (σΣB x)) (~ i)
  fst (WhiteheadProdBilinᵣ i) (push a b j) = main i j
    where
    x = Ω→ f .fst (σ A a)
    y = Ω→ g .fst (σΣB b)
    z = Ω→ h .fst (σΣB b)

    fun1 fun2 : Susp∙ (typ B) →∙ Ω C
    fst fun1 b = x ∙ Ω→ g .fst (σΣB b) ⁻¹ ∙ x ⁻¹
    snd fun1 = cong₂ _∙_ refl
                (cong₂ _∙_ (cong sym Ω→g∙) refl
                ∙ sym (lUnit (Ω→ f .fst (sym (σ A a)))))
             ∙ rCancel x
    fun2 = Ω→ h ∘∙ (σΣB , rCancel (merid north))

    main : Square (cong (·wh A (Susp∙ (typ B)) f
                        (·Susp (Susp∙ (typ B)) g h) .fst) (push a b))
                  (cong (_+*_ {A = A} {B = Susp∙ (typ B)}
                          (·wh A (Susp∙ (typ B)) f g)
                          (·wh A (Susp∙ (typ B)) f h) .fst) (push a b))
                  x ((z ∙ y) ⁻¹)
    main = {!!}
    {-
    cong₂ _∙_ (·Suspσ' g h b) refl
         ∙ sym (assoc y z x)
         ∙ (λ _ → y ∙ (z ∙ x))
         ◁ doubleCompPath-filler (x ⁻¹) (y ∙ (z ∙ x)) ((z ∙ y) ⁻¹)
        ▷ (doubleCompPath≡compPath _ _ _
         ∙ cong (x ⁻¹ ∙_) (sym (assoc _ _ _)
           ∙ cong₂ _∙_ refl (cong₂ _∙_ refl (symDistr z y)
                          ∙ assoc _ _ _ ∙ cong₂ _∙_ (sym (assoc z x _)) refl))
         ∙ assoc _ _ _
         ∙ cong₂ _∙_ refl
            ((cong₂ _∙_ refl (lUnit _
                           ∙ cong (_∙ z ⁻¹) (sym (lCancel x))
                           ∙ sym (assoc _ _ _))
           ∙ (assoc _ _ _))
           ∙ cong₂ _∙_ ((sym (assoc _ _ _) ∙ cong₂ _∙_ refl (sym (assoc _ _ _)))
                      ∙ sym (funExt⁻ (cong fst (Susp·→Ωcomm B fun1 fun2)) b))
                       refl
           ∙ sym (assoc _ _ _))
         ∙ assoc _ _ _
         ∙ cong₂ _∙_ (cong ((x ⁻¹ ∙ y) ∙_) (assoc _ _ _)
                   ∙ assoc _ _ _) refl
         ∙ sym (assoc _ _ _)
         ∙ sym (cong₂ _∙_
                 (sym (rUnit _)
                 ∙ cong·wh-ℓ* f g a b
                 ∙ doubleCompPath≡compPath _ _ _
                 ∙  (assoc _ _ _)
                  ∙ cong (_∙ y ⁻¹) (assoc _ _ _)
                  ∙ sym (assoc _ _ _))
                 (sym (rUnit _)
                 ∙ cong·wh-ℓ* f h a b
                 ∙ doubleCompPath≡compPath _ _ _
                 ∙ cong (x ⁻¹ ∙_) (sym (assoc _ _ _)
                 ∙ refl))))
                 -}
  snd (WhiteheadProdBilinᵣ i) j = {!!} -- Ω→f∙ j i

--   -- -- ·whΣ version
--   -- WhiteheadProdΣBilinᵣ : ·whΣ A (Susp∙ (typ B)) f (·Susp (Susp∙ (typ B)) g h)
--   --                      ≡ ·Susp (A ⋀∙ Susp∙ (typ B))
--   --                              (·whΣ A (Susp∙ (typ B)) f g)
--   --                              (·whΣ A (Susp∙ (typ B)) f h)
--   -- WhiteheadProdΣBilinᵣ =
--   --   transport (λ j
--   --     → PathP-·wh-·whΣ A (Susp∙ (typ B)) f
--   --         (·Susp (Susp∙ (typ B)) g h) (~ j)
--   --     ≡ ·Susp-+*-PathP {A = A} {Susp∙ (typ B)} {C} (~ j)
--   --       (PathP-·wh-·whΣ  A (Susp∙ (typ B)) f g (~ j))
--   --       (PathP-·wh-·whΣ  A (Susp∙ (typ B)) f h (~ j)))
--   --     WhiteheadProdBilinᵣ

-- -- Distributivity for suspension versions
-- WhiteheadProdIdL : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
--          (B : Pointed ℓ') {C : Pointed ℓ''}
--          (f : Susp∙ (typ B) →∙ C)
--       → ·wh A B (const∙ _ _) f ≡ const∙ _ _
-- fst (WhiteheadProdIdL A B {C = C} f i) (inl x) = pt C
-- fst (WhiteheadProdIdL A B f i) (inr x) = Ω→ f .fst (σ B x) (~ i)
-- fst (WhiteheadProdIdL A B f i) (push a b j) = lem i j
--   where
--   lem : Square (Ω→ f .fst (σ B b) ∙ refl ∙ refl) refl
--                 refl (sym (Ω→ f .fst (σ B b)))
--   lem = (cong₂ _∙_  refl (sym (rUnit refl)) ∙ sym (rUnit _))
--          ◁ λ i j → (Ω→ f .fst (σ B b) (~ i ∧ j))
-- snd (WhiteheadProdIdL A B f i) = refl

-- -- WhiteheadProdΣIdL : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
-- --          (B : Pointed ℓ') {C : Pointed ℓ''}
-- --          (f : Susp∙ (typ B) →∙ C)
-- --       → ·whΣ A B (const∙ _ _) f ≡ const∙ _ _
-- -- WhiteheadProdΣIdL A B {C = C} f =
-- --   transport (λ i → PathP-·wh-·whΣ A B (const∙ _ _) f (~ i)
-- --                  ≡ ·Susp-0*-PathP (~ i))
-- --             (WhiteheadProdIdL A B f)

-- WhiteheadProdIdR : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
--          (B : Pointed ℓ') {C : Pointed ℓ''}
--          (f : Susp∙ (typ A) →∙ C)
--       → ·wh A B f (const∙ _ _) ≡ const∙ _ _
-- fst (WhiteheadProdIdR A B f i) (inl x) = Ω→ f .fst (σ A x) i
-- fst (WhiteheadProdIdR A B {C = C} f i) (inr x) = pt C
-- fst (WhiteheadProdIdR A B f i) (push a b j) = lem i j
--   where
--   lem : Square ((refl ∙ refl) ∙ Ω→ f .fst (σ A a)) refl
--                (Ω→ f .fst (σ A a)) refl
--   lem = (cong₂ _∙_ (sym (rUnit refl)) refl ∙ sym (lUnit _))
--          ◁ λ i j → (Ω→ f .fst (σ A a) (i ∨ j))
-- snd (WhiteheadProdIdR A B f i) j =
--   (cong (Ω→ f .fst) (rCancel (merid (pt A))) ∙ Ω→ f .snd) j i

-- -- WhiteheadProdΣIdR : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
-- --          (B : Pointed ℓ') {C : Pointed ℓ''}
-- --          (f : Susp∙ (typ A) →∙ C)
-- --       → ·whΣ A B f (const∙ _ _) ≡ const∙ _ _
-- -- WhiteheadProdΣIdR A B {C = C} f =
-- --   transport (λ i → PathP-·wh-·whΣ A B f (const∙ _ _) (~ i)
-- --                  ≡ ·Susp-0*-PathP (~ i))
-- --             (WhiteheadProdIdR A B f)

-- -- inversion distributes over the generalised Whitehead product
-- -*DistrWhitehead : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
--            (B : Pointed ℓ') {C : Pointed ℓ''}
--            (f : Susp∙ (Susp (typ A)) →∙ C)
--            (g : Susp∙ (typ B) →∙ C)
--       → -* (·wh (Susp∙ (typ A)) B f g)
--       ≡ ·wh (Susp∙ (typ A)) B (-Susp (_ , north) f) g
-- -*DistrWhitehead A B f g = sym (+*IdL _)
--   ∙∙ cong (_+* (-* lhs)) (sym -*DistrWhiteheadLem)
--   ∙∙ (sym (+*Assoc _ _ _)
--   ∙ cong (rhs +*_) (+*InvR lhs)
--   ∙ +*IdR rhs)
--   where
--   lhs = ·wh (Susp∙ (typ A)) B f g
--   rhs = ·wh (Susp∙ (typ A)) B (-Susp (_ , north) f) g

--   -*DistrWhiteheadLem : rhs +* lhs ≡ const∙ _ _
--   -*DistrWhiteheadLem =
--       sym (WhiteheadProdBilinₗ A B _ f g)
--     ∙ cong₂ (·wh (Susp∙ (typ A)) B) (·SuspInvL (_ , north) f) refl --
--     ∙ WhiteheadProdIdL _ _ g --

-- -- Inversion is compatible with the equivalence A * B ≃ B * A
-- -*Swap : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'}
--       {C : Pointed ℓ''} (f : join∙ A B →∙ C)
--    → -* (f ∘∙ join-commFun∙) ≡ ((-* f) ∘∙ join-commFun∙)
-- fst (-*Swap {C = C} f i) (inl x) = pt C
-- fst (-*Swap {C = C} f i) (inr x) = pt C
-- fst (-*Swap {A = A} {B = B} f i) (push b a j) = main i j
--   where
--   main : (Ω→ (f ∘∙ join-commFun∙) .fst (ℓ* B A b a)) ⁻¹
--        ≡ (Ω→ f .fst (ℓ* A B a b))
--   main = cong sym (Ω→∘ f join-commFun∙ (ℓ* B A b a)
--            ∙ cong (Ω→ f .fst)
--                   (cong₃ _∙∙_∙∙_ refl
--                          (cong-∙ (fst join-commFun∙) _ _
--                        ∙ cong₂ _∙_ refl
--                            (cong-∙∙ (fst join-commFun∙) _ _ _))
--                          refl
--                 ∙ doubleCompPath≡compPath _ _ _
--                 ∙ assoc _ _ _
--                 ∙ cong (_∙ push (pt (fst A , snd A)) (pt (fst B , snd B)) ⁻¹)
--                        (assoc _ _ _
--                      ∙ cong₂ _∙_ (rCancel _) refl
--                      ∙ sym (lUnit _))))
--       ∙ cong (Ω→ f .fst) (symDistr _ _)
-- snd (-*Swap {A = A} {B = B} f i) =
--    (sym (rUnit _)
--   ∙ cong (Ω→ f .fst) (ℓ*IdL A B (pt B)) ∙ Ω→ f .snd) (~ i)

-- {-
-- `Anti-commutativity' of generalised whitehead products:
--                        [f ∶ g]
-- (Susp A) * (Susp B) ------------------> C
--          |                              |
--          |                              |
--          |                              |
--     flip |                              | id
--          |                              |
--          v                              v
-- (Susp B) * (Susp A) ------------------> C
--                        [g ∶ f]
-- -}
-- module _ {ℓ ℓ' ℓ''} (A : Pointed ℓ)
--          (B : Pointed ℓ') {C : Pointed ℓ''}
--          (f : Susp∙ (Susp (typ A)) →∙ C)
--          (g : Susp∙ (Susp (typ B)) →∙ C)
--   where
--   private
--     σΣA = σ (Susp∙ (typ A))
--     σΣB = σ (Susp∙ (typ B))

--     Ω→f∙ = cong (Ω→ f .fst) (rCancel (merid north)) ∙ Ω→ f .snd
--     Ω→g∙ = cong (Ω→ g .fst) (rCancel (merid north)) ∙ Ω→ g .snd
--     Ω→-g∙ =
--         cong (Ω→ (-Susp (Susp∙ (typ B)) g) .fst) (rCancel (merid north))
--       ∙ Ω→ (-Susp (Susp∙ (typ B)) g) .snd

--     wh' : join∙ (Susp∙ (typ A)) (Susp∙ (typ B)) →∙ C
--     wh' = ·wh (Susp∙ (typ B)) (Susp∙ (typ A)) (-Susp _ g) f
--                            ∘∙ (Iso.fun join-comm , push north north ⁻¹)

--     -- equivalent statement (easier to prove)
--     anticomm : -* (·wh (Susp∙ (typ A)) (Susp∙ (typ B)) f g)
--              ≡  (·wh (Susp∙ (typ B)) (Susp∙ (typ A))
--                      (-Susp (Susp∙ (typ B)) g) f
--               ∘∙ join-commFun∙)
--     fst (anticomm i) (inl x) = Ω→ f .fst (σΣA x) i
--     fst (anticomm i) (inr x) = Ω→ g .fst (σΣB x) i
--     fst (anticomm i) (push a b i₁) = l i i₁
--       where
--       x = Ω→ f .fst (σΣA a)
--       y = Ω→ g .fst (σΣB b)

--       fun1 fun2 : Susp∙ (typ A) →∙ Ω C
--       fst fun1 a = y ∙ (Ω→ f .fst (σΣA a) ⁻¹) ∙ y ⁻¹
--       snd fun1 =
--         cong (y ∙_)
--           (cong (_∙ y ⁻¹)
--             (cong sym ((Ω→ f ∘∙ toSuspPointed _) .snd))
--                       ∙ sym (lUnit _) )
--         ∙ rCancel y
--       fun2 = Ω→ f ∘∙ toSuspPointed _

--       l : Square (cong (fst (-* ((·wh (Susp∙ (typ A))
--                                       (Susp∙ (typ B)) f g))))
--                                       (push a b))
--                  (cong (fst wh') (push a b))
--                  x y
--       l = sym (rUnit _)
--         ∙ cong sym (cong·wh-ℓ* f g a b)
--         ∙ cong₃ _∙∙_∙∙_ refl (symDistr _ _) refl
--         ∙ doubleCompPath≡compPath _ _ _
--         ∙ assoc _ _ _
--         ∙ (λ i → fst (Susp·→Ωcomm _ fun1 fun2 i) a)
--         ∙ cong (x ∙_) (assoc _ _ _)
--         ∙ sym (doubleCompPath≡compPath _ _ _)
--         ◁ symP (doubleCompPath-filler x (y ∙ x ⁻¹) (y ⁻¹))
--         ▷ cong (_∙ x ⁻¹) (cong sym (sym
--                  (cong-∙ (fst (-Susp (Susp (typ B) , north) g))
--                    (merid b)
--                    (sym (merid north))
--               ∙ cong₂ _∙_ refl Ω→g∙ ∙ sym (rUnit _)) ∙ rUnit _))
--         ∙ compPath≡compPath' _ _
--     snd (anticomm i) j = lem i j
--       where
--       lem : Square refl (snd wh') (Ω→ f .fst (σΣA north)) refl
--       lem = flipSquare Ω→f∙
--           ▷ (cong sym (rUnit refl ∙ cong₂ _∙_ (sym Ω→f∙) (sym (Ω→-g∙)))
--            ∙ rUnit _)

--   WhiteheadProdComm : ·wh (Susp∙ (typ A)) (Susp∙ (typ B)) f g
--                    ≡ (·wh (Susp∙ (typ B)) (Susp∙ (typ A)) g f ∘∙ join-commFun∙)
--   WhiteheadProdComm =
--        preWhiteheadProdComm
--      ∙ cong₂ _∘∙_ (-*DistrWhitehead _ _ (-Susp (Susp∙ (typ B)) g) f
--                   ∙ cong₂ (·wh (Susp∙ (typ B)) (Susp∙ (typ A)))
--                           (-Susp² (Susp∙ (typ B)) g)
--                           refl)
--                   refl
--     where
--     preWhiteheadProdComm : ·wh (Susp∙ (typ A)) (Susp∙ (typ B)) f g
--                        ≡ (-* (·wh (Susp∙ (typ B)) (Susp∙ (typ A))
--                                   (-Susp (Susp∙ (typ B)) g) f)
--                         ∘∙ join-commFun∙)
--     preWhiteheadProdComm = sym (-*² _) ∙ cong -* anticomm ∙ -*Swap _

--   -- version for ·whΣ
--   -- WhiteheadProdΣComm : ·whΣ (Susp∙ (typ A)) (Susp∙ (typ B)) f g
--   --                    ≡ -Susp (Susp∙ (typ A) ⋀∙ Susp∙ (typ B))
--   --                            (·whΣ (Susp∙ (typ B)) (Susp∙ (typ A)) g f
--   --                           ∘∙ suspFun∙ ⋀comm→)
--   -- WhiteheadProdΣComm =
--   --     sym (·wh≡·whΣ (Susp∙ (typ A)) (Susp∙ (typ B)) f g)
--   --   ∙ cong₂ _∘∙_ WhiteheadProdComm refl
--   --   ∙ ∘∙-assoc _ _ _
--   --   ∙ cong (·wh (Susp∙ (typ B)) (Susp∙ (typ A)) g f ∘∙_)
--   --          (ΣPathP ((funExt (λ { north → push north north
--   --                              ; south → refl
--   --                              ; (merid a i) j
--   --                             → ((compPath-filler' (push north north)
--   --                                   (cong (SuspSmash→Join
--   --                                       ∘ fst ((-Susp (Susp∙ (typ A)
--   --                                                   ⋀∙ Susp∙ (typ B)))
--   --                                   (suspFun∙ ⋀comm→)))
--   --                                    (merid a)))
--   --                               ▷ (funExt⁻ (sym F1≡F2) a)) (~ j) i}))
--   --                 , ptLem)
--   --         ∙ sym (-Susp-∘∙ _ _ _))
--   --   ∙ sym (-Susp-∘∙ _ _ _)
--   --   ∙ cong (-Susp (Susp∙ (typ A) ⋀∙ Susp∙ (typ B)))
--   --          (sym (∘∙-assoc _ _ _)
--   --         ∙ cong₂ _∘∙_ (·wh≡·whΣ _ _ _ _) refl)
--   --   where
--   --   ptLem : Square {A = join (Susp (typ B)) (Susp (typ A))}
--   --                  (push north north ∙ sym (push north north))
--   --                  (refl ∙ sym (push north north))
--   --                  (push north north) refl
--   --   ptLem = rCancel (push north north)
--   --         ◁ (λ i j → push north north (~ j ∧ i))
--   --         ▷ lUnit (sym (push north north))

--   --   F1 F2 : Susp∙ (typ A) ⋀ Susp∙ (typ B)
--   --      →  ((Path (join (fst (Susp∙ (typ B))) (fst (Susp∙ (typ A))))
--   --                 (inl north) (inr north)))
--   --   F1 a i = join-commFun (SuspSmash→Join (merid a i))
--   --   F2 a = push north north
--   --     ∙ cong (SuspSmash→Join
--   --           ∘ fst ((-Susp (Susp∙ (typ A) ⋀∙ Susp∙ (typ B)))
--   --                         (suspFun∙ ⋀comm→)))
--   --            (merid a)

--   --   F1≡F2 : F1 ≡ F2
--   --   F1≡F2 = ⋀→Homogeneous≡ (isHomogeneousPath _ _)
--   --             λ x y →
--   --             cong-∙∙ join-commFun _ _ _
--   --           ∙ lUnit _
--   --           ∙ cong₂ _∙_ (sym (rCancel _)) refl
--   --           ∙ sym (assoc _ _ _)
--   --           ∙ cong₂ _∙_ refl
--   --               (sym (symDistr (cong SuspSmash→Join (merid (inr (y , x))))
--   --                              (cong SuspSmash→Join (sym (merid (inl tt)))))
--   --              ∙ cong sym (sym (cong-∙ SuspSmash→Join
--   --                 (merid (inr (y , x)))
--   --                 (sym (merid (inl tt)))))
--   --              ∙ cong (congS SuspSmash→Join)
--   --                 (cong sym
--   --                   (sym (cong-∙ (fst (suspFun∙ ⋀comm→))
--   --                     (merid (inr (x , y)))
--   --                     (merid (inl tt) ⁻¹)))
--   --                 ∙ rUnit _))

-- WhiteheadProdComm' : ∀ {ℓ ℓ' ℓ''} {C : Pointed ℓ''}
--    (A A' : Pointed ℓ) (eA : A ≃∙ Susp∙ (typ A')) (B B' : Pointed ℓ')

--                    (eB : B ≃∙ Susp∙ (typ B'))
--                    (f : _ →∙ C) (g : _ →∙ C)
--   → ·wh A B f g ≡ (·wh B A g f ∘∙ join-commFun∙)
-- WhiteheadProdComm' {C = C} A A' =
--   Equiv∙J (λ A _ →  (B B' : Pointed _)

--                    (eB : B ≃∙ Susp∙ (typ B'))
--                    (f : _ →∙ C) (g : _ →∙ C)
--                    → ·wh A B f g ≡ (·wh B A g f ∘∙ join-commFun∙))
--     λ B B' → Equiv∙J (λ B _ → (f : _ →∙ C) (g : _ →∙ C)
--                    → ·wh (Susp∙ (typ A')) B f g
--                    ≡ (·wh B (Susp∙ (typ A')) g f ∘∙ join-commFun∙))
--      (WhiteheadProdComm _ _)

--   -- (right derivator) version of the Jacobi identity. This
--   -- corresponds to the statement [f,[g,h]] = [[f,g],h] + [g,[f,h]]

-- -- We need some 'correction functoins' to make the theorem well-typed
-- module _ {ℓ ℓ' ℓ'' : Level} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') where
--   Jcorrection₁ : join∙ A (B ⋀∙ C) →∙ join∙ (A ⋀∙ B) C
--   fst Jcorrection₁ =
--     ≃∙map (invEquiv∙ (permute⋀Join≃∙ A B C)) .fst
--   snd Jcorrection₁ = sym (push (inl tt) (pt C))

--   Jcorrection₁⁻ : join∙ (A ⋀∙ B) C →∙ join∙ A (B ⋀∙ C)
--   Jcorrection₁⁻ = ≃∙map (permute⋀Join≃∙ A B C)

-- Jcorrection₂ : ∀ {ℓ ℓ' ℓ'' : Level} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'')
--   → join∙ A (B ⋀∙ C) →∙ join∙ B (A ⋀∙ C)
-- Jcorrection₂ A B C = Jcorrection₁⁻ B A C
--            ∘∙ ((join→ ⋀comm→ (idfun _) , refl)
--            ∘∙ Jcorrection₁ A B C)

-- module _ {ℓ ℓ' ℓ'' ℓ'''} (A : Pointed ℓ)
--          (B : Pointed ℓ') (C : Pointed ℓ'') {D : Pointed ℓ'''}
--          (f : Susp∙ (Susp (typ A)) →∙ D)
--          (g : Susp∙ (Susp (typ B)) →∙ D)
--          (h : Susp∙ (Susp (typ C)) →∙ D)
--   where
--   -- To state the theorem, we make some abbreviations
--   private
--     σΣA = σ (Susp∙ (typ A))
--     σΣB = σ (Susp∙ (typ B))
--     σΣC = σ (Susp∙ (typ C))

--     whAB  = ·wh (Susp∙ (typ A)) (Susp∙ (typ B)) {D}

--     whAC  = ·wh (Susp∙ (typ A)) (Susp∙ (typ C)) {D}
--     whBC  = ·wh (Susp∙ (typ B)) (Susp∙ (typ C)) {D}

--     whA-BC = ·wh (Susp∙ (typ A)) ((Susp∙ (typ B)) ⋀∙ (Susp∙ (typ C))) {D}
--     whAB-C = ·wh ((Susp∙ (typ A)) ⋀∙ (Susp∙ (typ B))) (Susp∙ (typ C)) {D}

--     whB-AC = ·wh (Susp∙ (typ B)) ((Susp∙ (typ A)) ⋀∙ (Susp∙ (typ C))) {D}


--     whB-CA = ·wh (Susp∙ (typ B)) ((Susp∙ (typ C)) ⋀∙ (Susp∙ (typ A))) {D}

--     ΣB*ΣC→Σ[B⋀C] = Join→SuspSmash∙ (Susp∙ (typ B)) (Susp∙ (typ C))
--     Σ[B⋀C]→ΣB*ΣC = SuspSmash→Join∙ (Susp∙ (typ B)) (Susp∙ (typ C))

--     Σ[A⋀B]→ΣA*ΣB = SuspSmash→Join∙ (Susp∙ (typ A)) (Susp∙ (typ B))
--     Σ[A⋀C]→ΣA*ΣC = SuspSmash→Join∙ (Susp∙ (typ A)) (Susp∙ (typ C))

--     whB∧C = ·wh (Susp∙ (typ B)) (Susp∙ (typ C)) {D}

--     Ω→f∙ = cong (Ω→ f .fst) (rCancel (merid north)) ∙ Ω→ f .snd
--     Ω→g∙ = cong (Ω→ g .fst) (rCancel (merid north)) ∙ Ω→ g .snd
--     Ω→h∙ = cong (Ω→ h .fst) (rCancel (merid north)) ∙ Ω→ h .snd

--   -- We need some 'correction functoins' to make the theorem well-typed
--   correction₁ = Jcorrection₁ (Susp∙ (typ A)) (Susp∙ (typ B)) (Susp∙ (typ C))

--   correction₁⁻ = Jcorrection₁⁻ (Susp∙ (typ A)) (Susp∙ (typ B)) (Susp∙ (typ C))

--   correction₂ = Jcorrection₂ (Susp∙ (typ A)) (Susp∙ (typ B)) (Susp∙ (typ C))

--   -- Main result
--   JacobiR : whA-BC f (whBC g h ∘∙ Σ[B⋀C]→ΣB*ΣC)
--         ≡ ((whAB-C (whAB f g ∘∙ Σ[A⋀B]→ΣA*ΣB) h ∘∙ correction₁)
--         +* (whB-AC g (whAC f h ∘∙ Σ[A⋀C]→ΣA*ΣC) ∘∙ correction₂))
--   JacobiR =

--     ΣPathP ((funExt (λ { (inl x) → lp x
--                        ; (inr x) → rp x
--                        ; (push a b i) j → main a b j i
--                        }))
--           , flipSquare (Iso.inv ΩSuspAdjointIso f .snd))
--     where
--     L = whA-BC f (whBC g h ∘∙ Σ[B⋀C]→ΣB*ΣC)
--     R = ((whAB-C (whAB f g ∘∙ Σ[A⋀B]→ΣA*ΣB) h ∘∙ correction₁)
--         +* (whB-AC g (whAC f h ∘∙ Σ[A⋀C]→ΣA*ΣC) ∘∙ correction₂))

--     -- The identites on point constructors.
--     lp : Susp (typ A) → Ω D .fst
--     lp = Iso.inv ΩSuspAdjointIso f .fst

--     rp : (Susp∙ (typ B) ⋀ Susp∙ (typ C)) → Ω D .fst
--     rp = rp' ∘ ⋀→Smash
--       where
--       rpl : ∀ {ℓ} {A : Type ℓ} {x : A} (p q : x ≡ x)
--         → refl ≡ q
--         → (p ∙ q ⁻¹) ∙ p ⁻¹ ∙ q ≡ refl
--       rpl p = J> cong₂ _∙_ (sym (rUnit p)) (sym (rUnit _)) ∙ rCancel p

--       rpr : ∀ {ℓ} {A : Type ℓ} {x : A} (q : x ≡ x) (p : x ≡ x)
--         → refl ≡ p
--         → (p ∙ q ⁻¹) ∙ p ⁻¹ ∙ q ≡ refl
--       rpr q = J> cong₂ _∙_ (sym (lUnit _)) (sym (lUnit _)) ∙ lCancel q

--       rp' : Smash (Susp∙ (typ B)) (Susp∙ (typ C)) → Ω D .fst
--       rp' basel = refl
--       rp' baser = refl
--       rp' (proj b c) = ((Ω→ g .fst (σΣB b) ∙ (Ω→ h .fst (σΣC c)) ⁻¹)
--                      ∙ ((Ω→ g .fst (σΣB b)) ⁻¹ ∙ Ω→ h .fst (σΣC c))) ⁻¹
--       rp' (gluel b i) =
--         sym (rpl (Ω→ g .fst (σΣB b)) (Ω→ h .fst (σΣC north))
--                  (sym (Iso.inv ΩSuspAdjointIso h .snd)) i)
--       rp' (gluer c i) =
--         sym (rpr (Ω→ h .fst (σΣC c)) (Ω→ g .fst (σΣB north))
--                  (sym (Iso.inv ΩSuspAdjointIso g .snd)) i)

--     apL apR : (a : Susp (typ A))
--             → Susp∙ (typ B) ⋀ Susp∙ (typ C) → Ω D .fst
--     apL a x = lp a ⁻¹ ∙∙ cong (fst L) (push a x) ∙∙ rp x
--     apR a x = cong (fst R) (push a x)

--     -- Some lemmas simplying the pointed functions involved
--     lem1 : whBC g h ∘∙ Σ[B⋀C]→ΣB*ΣC ≡ (fst (whBC g h ∘∙ Σ[B⋀C]→ΣB*ΣC) , refl)
--     lem1 = ΣPathP (refl , sym (rUnit _)
--                   ∙ cong₃ _∙∙_∙∙_
--                           (cong sym (Iso.inv ΩSuspAdjointIso g .snd))
--                           (cong sym (Iso.inv ΩSuspAdjointIso h .snd))
--                           refl
--                         ∙ sym (rUnit refl))

--     lem2 : whAB-C (whAB f g ∘∙ Σ[A⋀B]→ΣA*ΣB) h ∘∙ correction₁
--       ≡ ((whAB-C (whAB f g ∘∙ Σ[A⋀B]→ΣA*ΣB) h ∘∙ correction₁) .fst , refl)
--     lem2 = ΣPathP (refl
--       , sym (rUnit _)
--       ∙ cong₃ _∙∙_∙∙_ refl
--               (cong sym (Iso.inv ΩSuspAdjointIso h .snd))
--               refl
--      ∙ sym (compPath≡compPath' _ _)
--      ∙ cong sym (sym (rUnit _))
--      ∙ cong₃ _∙∙_∙∙_ refl
--                      (cong (cong (fst (whAB f g) ∘ fst Σ[A⋀B]→ΣA*ΣB))
--                            (cong sym (rCancel (merid (inl tt)))))
--                      refl
--      ∙ ∙∙lCancel _)

--     lem3 : whB-AC g (whAC f h ∘∙ Σ[A⋀C]→ΣA*ΣC) ∘∙ correction₂
--         ≡ ((whB-AC g (whAC f h ∘∙ Σ[A⋀C]→ΣA*ΣC) ∘∙ correction₂) .fst , refl)
--     lem3 = ΣPathP (refl
--       , cong₂ _∙_ (cong (cong (fst (whB-AC g (whAC f h ∘∙ Σ[A⋀C]→ΣA*ΣC)))) lem)
--                   refl
--                  ∙ sym (rUnit refl))
--       where
--       lem : snd correction₂ ≡ refl
--       lem = cong₂ _∙_ (cong (cong (fst (Jcorrection₁⁻ (Susp∙ (typ B)) (Susp∙ (typ A)) (Susp∙ (typ C)))))
--                       (sym (rUnit _))) refl
--           ∙ rCancel _


--     -- some more abbreviations
--     l : Susp (typ A) → Ω D .fst
--     m : Susp (typ B) → Ω D .fst
--     r : Susp (typ C) → Ω D .fst
--     l a = Ω→ f .fst (σΣA a)
--     m b = Ω→ g .fst (σΣB b)
--     r c = Ω→ h .fst (σΣC c)

--     -- Goal: relate 'cong (fst L) (push a (inr (b , c))))' to 'cong
--     -- (fst R) (push a (inr (b , c))))' Unfolding definitions this
--     -- gives rise to a word problem.  We could hope to automate some
--     -- parts of the proof in the future...
--     module _ (a : Susp (typ A)) (b : Susp (typ B)) (c : Susp (typ C)) where
--       leftId : (cong (fst L) (push a (inr (b , c))))
--              ≡ ((m b ⁻¹) ∙∙ r c ∙ m b ∙∙ (r c ⁻¹)) ∙ l a
--       leftId =
--         cong₂ _∙_ ((λ j i → Ω→ (lem1 j) .fst
--                                   (σ (Susp∙ (typ B) ⋀∙ Susp∙ (typ C))
--                                      (inr (b , c))) i)
--         ∙ sym (rUnit _)
--         ∙ cong (cong (fst (whBC g h)))
--                (cong-∙ (fst Σ[B⋀C]→ΣB*ΣC)
--                        (merid (inr (b , c))) (sym (merid (inl tt))))
--         ∙ cong-∙ (fst (whBC g h)) _ _
--         ∙ cong₂ _∙_ (cong-∙∙ (fst (whBC g h)) _ _ _
--                 ∙ cong₃ _∙∙_∙∙_
--                      (cong sym (cong₂ _∙_ (Iso.inv ΩSuspAdjointIso h .snd) refl
--                      ∙ sym (lUnit _)))
--                      (λ i → Ω→ h .fst (σΣC c) ∙ Ω→ g .fst (σΣB b))
--                      (cong sym (cong₂ _∙_ refl (Iso.inv ΩSuspAdjointIso g .snd)
--                              ∙ sym (rUnit _)))
--                 ∙ refl)
--              (cong₂ _∙_ (Iso.inv ΩSuspAdjointIso h .snd)
--                         (Iso.inv ΩSuspAdjointIso g .snd) ∙ sym (rUnit refl))
--         ∙ sym (rUnit ((m b ⁻¹) ∙∙ r c ∙ m b ∙∙ (r c ⁻¹))))
--         refl

--       -- more abbreviations
--       ℓA-BC =  ℓ* (Susp∙ (typ A)) ((Susp∙ (typ B)) ⋀∙ (Susp∙ (typ C)))
--       ℓAB-C =  ℓ* ((Susp∙ (typ A)) ⋀∙ (Susp∙ (typ B))) (Susp∙ (typ C))
--       ℓB-AC =  ℓ* (Susp∙ (typ B)) ((Susp∙ (typ A)) ⋀∙ (Susp∙ (typ C)))

--       correction₁-ℓ : cong (fst (correction₁)) (ℓA-BC a (inr (b , c)))
--                     ≡ (push (inl tt) north) ⁻¹
--                     ∙∙ ℓAB-C (inr (a , b)) c
--                     ∙∙ push (inl tt) north
--       correction₁-ℓ = cong-∙ (fst (correction₁)) _ _
--                    ∙ cong (sym (push (inl tt) north) ∙_)
--                           (cong-∙∙ (fst (correction₁)) _ _ _
--                           ∙ doubleCompPath≡compPath _ _ _ ∙ refl)
--                    ∙ assoc _ _ _
--                    ∙ cong₂ _∙_ (rCancel _) refl
--                    ∙ sym (lUnit _)
--                    ∙ cong₂ _∙_ (lUnit _
--                              ∙ (λ i → (λ j → push (inl tt) north (~ j ∨ ~ i))
--                                      ∙ compPath-filler' (push (inl tt) north)
--                                              (push (inr (a , b)) north ⁻¹
--                                              ∙∙ push (inr (a , b)) c
--                                              ∙∙ push (inl tt) c ⁻¹) i))
--                              ((λ i → push (inl tt) c
--                                    ∙∙ push (push (inr b) (~ i)) c ⁻¹
--                                    ∙∙ push (push (inr b) (~ i)) north)
--                              ∙ doubleCompPath≡compPath _ _ _
--                              ∙ assoc _ _ _
--                              ∙ cong₂ _∙_ (rCancel _) refl
--                              ∙ sym (lUnit _))
--                    ∙ sym (assoc _ _ _)
--                    ∙ sym (doubleCompPath≡compPath _ _ _)


--       correction₂-ℓ : cong (fst correction₂) (ℓA-BC a (inr (b , c)))
--                     ≡ ℓB-AC b (inr (a , c))
--       correction₂-ℓ =
--           cong-∙ (fst correction₂) _ _
--         ∙ cong₂ _∙_ refl
--                     (cong-∙∙ (fst correction₂) _ _ _
--                   ∙ (cong₃ _∙∙_∙∙_ (λ _ → push north (inl tt) ⁻¹)
--                   (help a b c)
--                   (cong sym (help north b c
--                             ∙ cong₂ _∙_ (cong (ℓB-AC b) (sym (push (inr c)))
--                                       ∙ ℓ*IdR _ _ b) refl
--                             ∙ sym (lUnit _)))
--                 ∙ doubleCompPath≡compPath _ _ _
--                 ∙ cong (push north (inl tt) ⁻¹ ∙_)
--                        (sym (assoc _ _ _)
--                        ∙ (cong (ℓB-AC b (inr (a , c)) ∙_) (rCancel _)
--                        ∙ sym (rUnit _)))
--                 ∙ assoc _ _ _
--                 ∙ cong₂ _∙_ (rCancel _) refl
--                 ∙ sym (lUnit _)))

--         where
--         help : (a : _) (b : _) (c : _)
--              → cong (fst correction₂) (push a (inr (b , c)))
--               ≡ ℓB-AC b (inr (a , c)) ∙ push north (inl tt)
--         help a b c =
--           cong-∙∙ ((Jcorrection₁⁻
--                     (Susp∙ (typ B)) (Susp∙ (typ A)) (Susp∙ (typ C))) .fst
--                   ∘ join→ ⋀comm→ (idfun (Susp (typ C)))) _ _ _
--           ∙ cong₃ _∙∙_∙∙_ ((λ i → push north (push (inl a) (~ i))
--                                 ∙∙ push b (push (inl a) (~ i)) ⁻¹
--                                 ∙∙ push b (inl tt))
--                         ∙ doubleCompPath≡compPath _ _ _
--                         ∙ cong₂ _∙_ refl (lCancel (push b (inl tt)))
--                         ∙ sym (rUnit _))
--                         refl (λ _ → push north (inl tt))
--           ∙ doubleCompPath≡compPath _ _ _ ∙ assoc _ _ _

--       -- more abbreviations...
--       x = l a
--       -x = x ⁻¹
--       y = m b
--       -y = y ⁻¹
--       z = r c
--       -z = z ⁻¹

--       t₁ = (y ∙ -x ∙ -y ∙ x) ∙ z ∙ -x ∙ y ∙ x ∙ -y
--       t₂ = -y ∙ -x ∙ z ∙ x ∙ -z ∙ y
--       t₃ = z ∙ -x ∙ -z ∙ x

--       t₃' = -x ∙ -z ∙ x
--       t₄ = z ∙ x ∙ -z

--       fA : Susp∙ (typ A) →∙ Ω D
--       fst fA a = ((-y ∙ z) ∙ Ω→ f .fst (σΣA a)
--                ∙ -z ∙ sym (Ω→ f .fst (σΣA a))) ∙ y
--       snd fA = cong (λ x → ((-y ∙ z) ∙ x ∙ -z ∙ x ⁻¹) ∙ y)
--                     (Iso.inv ΩSuspAdjointIso f .snd)
--              ∙ cong₂ _∙_ (cong₂ _∙_ refl (sym (lUnit _) ∙ sym (rUnit _))
--                        ∙ sym (assoc -y z -z)
--                        ∙ cong (-y ∙_) (rCancel z) ∙ sym (rUnit -y))
--                        refl
--              ∙ lCancel y

--       f-xyx f-xyx' f-zyz : Susp∙ (typ B) →∙ Ω D
--       fst f-xyx b = -x ∙ Ω→ g .fst (σΣB b) ⁻¹ ∙ x
--       snd f-xyx = cong₂ _∙_ refl
--         (cong (_∙ x) (cong sym (Iso.inv ΩSuspAdjointIso g .snd))
--           ∙ sym (lUnit x)) ∙ lCancel x
--       fst f-xyx' b = -x ∙ Ω→ g .fst (σΣB b) ∙ x
--       snd f-xyx' =
--         cong₂ _∙_ refl
--         (cong (_∙ x) (Iso.inv ΩSuspAdjointIso g .snd)
--           ∙ sym (lUnit x)) ∙ lCancel x
--       fst f-zyz b = -z ∙ Ω→ g .fst (σΣB b) ⁻¹ ∙ z
--       snd f-zyz = cong₂ _∙_ refl
--         (cong (_∙ z) (cong sym (Iso.inv ΩSuspAdjointIso g .snd))
--           ∙ sym (lUnit z))
--           ∙ lCancel z

--       f₁ f₂ fz f₃ f-yazay : Susp∙ (typ C) →∙ Ω D
--       fst f₁ z = (y ∙ -x ∙ -y ∙ x) ∙ Ω→ h .fst (σΣC z) ∙ -x ∙ y ∙ x ∙ -y
--       snd f₁ =
--         cong₂ _∙_
--           (assoc _ _ _ ∙ assoc _ _ _)
--           ((cong₂ _∙_ (Iso.inv ΩSuspAdjointIso h .snd) refl
--                      ∙ sym (lUnit _))
--           ∙ sym (symDistr _ _
--           ∙ cong₂ _∙_ refl
--              (symDistr _ _ ∙ cong₂ _∙_ refl (symDistr _ _))))
--           ∙ rCancel (((y ∙ -x) ∙ -y) ∙ x)
--       fst f₂ z = -y ∙ -x ∙ Ω→ h .fst (σΣC z) ∙ x ∙ Ω→ h .fst (σΣC z) ⁻¹ ∙ y
--       snd f₂ =
--         cong₂ _∙_ refl
--           (cong₂ _∙_ refl
--             (cong₂ _∙_ (Iso.inv ΩSuspAdjointIso h .snd)
--                        (cong₂ _∙_ refl
--                          (cong₂ _∙_ (cong sym (Iso.inv ΩSuspAdjointIso h .snd))
--                                     refl
--                        ∙ sym (lUnit _)))
--                      ∙ sym (lUnit (x ∙ y))))
--         ∙ cong₂ _∙_ refl (assoc -x x y
--                        ∙ cong₂ _∙_ (lCancel x) refl
--                        ∙ sym (lUnit y))
--                      ∙ lCancel y
--       fz = (sym , refl) ∘∙ Iso.inv ΩSuspAdjointIso h
--       fst f₃ c = -x ∙ sym (Ω→ h .fst (σΣC c)) ∙ x
--       snd f₃ =
--           cong (-x ∙_)
--            (cong (_∙ x) (cong sym (Iso.inv ΩSuspAdjointIso h .snd))
--             ∙ sym (lUnit x))
--         ∙ lCancel x
--       fst f-yazay c = (-y ∙ x) ∙ Ω→ h .fst (σΣC c) ∙ -x ∙ y
--       snd f-yazay =
--         cong₂ _∙_ (sym (symDistr -x y))
--                   (cong₂ _∙_ (Iso.inv ΩSuspAdjointIso h .snd) refl
--                            ∙ sym (lUnit (-x ∙ y)))
--                 ∙ lCancel (-x ∙ y)


--       f₄ fa : Susp∙ (typ A) →∙ Ω D
--       fst f₄ a = z ∙ Ω→ f .fst (σΣA a) ∙ -z
--       snd f₄ = cong (z ∙_) (cong (_∙ -z) (Iso.inv ΩSuspAdjointIso f .snd)
--                           ∙ sym (lUnit _)) ∙ rCancel z
--       fa = (sym , refl) ∘∙ Iso.inv ΩSuspAdjointIso f

--       rightId₁ : cong (fst R) (push a (inr (b , c)))
--              ≡ (t₂ ∙ t₁) ∙ -z ∙ t₃
--       rightId₁ =
--         cong₂ _∙_ (λ i → Ω→ (lem2 i) .fst (ℓA-BC a (inr (b , c))))
--                    (λ i → Ω→ (lem3 i) .fst (ℓA-BC a (inr (b , c))))
--         ∙ cong₂ _∙_
--           (sym (rUnit _)
--            ∙ cong (cong (fst (whAB-C (whAB f g ∘∙ Σ[A⋀B]→ΣA*ΣB) h)))
--                   correction₁-ℓ
--             ∙ cong-∙∙ (fst (whAB-C (whAB f g ∘∙ Σ[A⋀B]→ΣA*ΣB) h)) _ _ _
--             ∙ cong (λ x → x ⁻¹
--                         ∙∙ cong (fst (whAB-C (whAB f g ∘∙ Σ[A⋀B]→ΣA*ΣB) h))
--                                 (ℓAB-C (inr (a , b)) c)
--                         ∙∙ x) (cong₂ _∙_ (Iso.inv ΩSuspAdjointIso h .snd)
--                                          (Iso.inv ΩSuspAdjointIso
--                                            (whAB f g ∘∙ Σ[A⋀B]→ΣA*ΣB) .snd)
--                            ∙ sym (rUnit refl))
--                 ∙ sym (rUnit _) )
--             (sym (rUnit _)
--            ∙ cong (cong (fst (whB-AC g (whAC f h ∘∙ Σ[A⋀C]→ΣA*ΣC))))
--                              (correction₂-ℓ))
--         ∙ cong₂ _∙_ ((λ i → cong·wh-ℓ* {A = _ , inl tt} {B = _ , north}
--                              (lem4 i) h (inr (a , b)) c i)
--                     ∙ cong₃ _∙∙_∙∙_ (sym (rUnit _)
--                                     ∙ cong sym (fgid' A B f g a b)
--                                     ∙ cong₃ _∙∙_∙∙_ refl
--                                        (symDistr (m b) (l a)) refl)
--                                     (cong₂ _∙_ (λ _ → r c)
--                                       (sym (rUnit _) ∙ (fgid' A B f g a b)))
--                                     (λ _ → r c ⁻¹))
--                     ((λ i → cong·wh-ℓ* {A = _ , north} {B = _ , inl tt}
--                               g (lem5 i) b (inr (a , c)) i)
--                     ∙ cong₃ _∙∙_∙∙_ (λ _ → m b ⁻¹)
--                        (cong₂ _∙_ (sym (rUnit _) ∙ fgid' A C f h a c)
--                                   (λ _ → m b))
--                        (sym (rUnit _)
--                        ∙ cong sym (fgid' A C f h a c)
--                        ∙ cong₃ _∙∙_∙∙_ refl (symDistr (r c) (l a)) refl))
--         ∙ cong₂ _∙_ (cong₃ _∙∙_∙∙_ (doubleCompPath≡compPath _ _ _
--                                     ∙ cong₂ _∙_ refl (sym (assoc _ _ _)))
--                                    (cong (r c ∙_) (doubleCompPath≡compPath _ _ _
--                                     ∙ cong₂ _∙_ refl (sym (assoc _ _ _))))
--                                    refl
--                   ∙ doubleCompPath≡compPath _ _ _
--                 ∙ assoc _ _ _ ∙ cong (_∙ -z) λ _ → t₁)
--                   (doubleCompPath≡compPath _ _ _
--                   ∙ cong₂ _∙_ refl
--                     (cong₂ _∙_ (cong (_∙ y)
--                       (doubleCompPath≡compPath _ _ _)
--                         ∙ sym (assoc _ _ y)
--                         ∙ cong (-x ∙_) (sym (assoc _ _ y) ∙ sym (assoc _ _ _)))
--                       ((doubleCompPath≡compPath _ _ _)
--                         ∙ (cong (z ∙_) (sym (assoc -x -z x)))))
--                     ∙ assoc -y _ t₃ ∙ λ _ → t₂ ∙ t₃)
--         ∙ sym (assoc t₁ -z (t₂ ∙ t₃))
--         ∙ cong (t₁ ∙_) (assoc -z t₂ t₃
--                      ∙ cong (_∙ t₃) (funExt⁻ (cong fst (Susp·→Ωcomm C fz f₂)) c)
--                      ∙ sym (assoc t₂ -z t₃))
--         ∙ assoc t₁ t₂ _
--         ∙ cong₂ _∙_ (funExt⁻ (cong fst (Susp·→Ωcomm C f₁ f₂)) c) refl
--         where
--         fgid' : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ')
--                           (f : Susp∙ (Susp (typ A)) →∙ D)
--                           (g : Susp∙ (Susp (typ B)) →∙ D)
--                           (a : Susp (typ A)) (b : Susp (typ B))
--              → cong (fst (·wh (Susp∙ (typ A)) (Susp∙ (typ B)) f g))
--                    (cong (fst (SuspSmash→Join∙ (Susp∙ (typ A)) (Susp∙ (typ B))))
--                       (σ (_ , inl tt) (inr (a , b))))
--              ≡ (Ω→ f .fst (σ (Susp∙ (typ A)) a) ⁻¹
--              ∙∙ Ω→ g .fst (σ (Susp∙ (typ B)) b)
--               ∙ Ω→ f .fst (σ (Susp∙ (typ A)) a)
--              ∙∙ (Ω→ g .fst (σ (Susp∙ (typ B)) b) ⁻¹))
--         fgid' A B f g a b =
--           cong-∙ (fst (·wh (Susp∙ (typ A)) (Susp∙ (typ B)) f g)
--                  ∘ (fst (SuspSmash→Join∙ (Susp∙ (typ A)) (Susp∙ (typ B)))))
--                    (merid (inr (a , b))) _
--                  ∙ cong₂ _∙_ refl
--                              (cong₂ _∙_ (Iso.inv ΩSuspAdjointIso g .snd)
--                                         (Iso.inv ΩSuspAdjointIso f .snd)
--                             ∙ sym (rUnit refl))
--                            ∙ sym (rUnit _)
--              ∙ cong-∙∙ (fst (·wh (Susp∙ (typ A)) (Susp∙ (typ B)) f g)) _ _ _
--              ∙ cong₃ _∙∙_∙∙_
--                  (cong sym (cong₂ _∙_ (Iso.inv ΩSuspAdjointIso g .snd) refl
--                                       ∙ sym (lUnit _)))
--                  refl
--                  (cong sym (cong₂ _∙_ refl (Iso.inv ΩSuspAdjointIso f .snd)
--                           ∙ sym (rUnit _)))

--         lem4 : whAB f g ∘∙ Σ[A⋀B]→ΣA*ΣB
--             ≡ ((whAB f g ∘∙ Σ[A⋀B]→ΣA*ΣB) .fst , refl)
--         lem4 =
--           ΣPathP (refl , sym (rUnit _)
--                        ∙ cong sym (cong₂ _∙_ (Iso.inv ΩSuspAdjointIso g .snd)
--                                              (Iso.inv ΩSuspAdjointIso f .snd))
--                       ∙ sym (rUnit _))
--         lem5 : whAC f h ∘∙ Σ[A⋀C]→ΣA*ΣC
--             ≡ ((whAC f h ∘∙ Σ[A⋀C]→ΣA*ΣC) .fst , refl)
--         lem5 =
--           ΣPathP (refl ,  sym (rUnit _)
--                         ∙ cong sym (cong₂ _∙_ (Iso.inv ΩSuspAdjointIso h .snd)
--                                               (Iso.inv ΩSuspAdjointIso f .snd))
--                        ∙ sym (rUnit _))

--       rightId₂ : (t₂ ∙ t₁) ∙ -z ∙ t₃
--                ≡ -y ∙ (-x ∙ t₄) ∙ y ∙ t₁ ∙ t₃'
--       rightId₂ = cong₂ _∙_ (cong₂ _∙_ (cong (-y ∙_)
--                                         (cong (-x ∙_)
--                                           (assoc _ _ _ ∙ assoc _ _ _
--                                         ∙ cong₂ _∙_ (sym (assoc z x -z)) refl)))
--                                       refl)
--                        (assoc -z z _
--                       ∙ cong₂ _∙_ (lCancel z) refl ∙ sym (lUnit _))
--                ∙ sym (assoc _ _ _)
--                ∙ cong₂ _∙_ (cong (-y ∙_) (assoc _ _ _)
--                            ∙ assoc _ _ _)
--                            refl
--                ∙ sym (assoc _ _ _)
--                ∙ sym (assoc _ _ _)

--       rightId₃ : -y ∙ (-x ∙ t₄) ∙ y ∙ t₁ ∙ t₃'
--                ≡ (-y ∙ z) ∙ (x ∙ -z ∙ -x) ∙ y ∙ t₃' ∙ t₁
--       rightId₃ =
--         cong (-y ∙_)
--           (cong₂ _∙_ (funExt⁻ (cong fst (Susp·→Ωcomm A fa f₄)) a)
--                      (cong (y ∙_) (funExt⁻ (cong fst (Susp·→Ωcomm C f₁ f₃)) c)))
--         ∙ (assoc _ _ _
--          ∙ cong₂ _∙_ (cong (-y ∙_) (sym (assoc _ _ _)
--          ∙ cong (z ∙_) (sym (assoc _ _ _)))
--          ∙ assoc _ _ _) refl)
--         ∙ sym (assoc _ _ _)

--       rightId₄ : ((-y ∙ z) ∙ (x ∙ -z ∙ -x) ∙ y ∙ t₃' ∙ t₁)
--                  ∙ (y ∙ -z) ∙ (-y ∙ z)
--                ≡ (((-y ∙ z) ∙ x ∙ -z ∙ -x) ∙ y)
--                  ∙ (-x ∙ (-y ∙ x) ∙ z ∙ -x ∙ y) ∙ -z ∙ x
--       rightId₄ =
--         cong₂ _∙_ (cong (λ t → (-y ∙ z) ∙ (x ∙ -z ∙ -x) ∙ y ∙ t₃' ∙ t) t₁≡)
--                   (sym (assoc y -z _))
--         ∙ sym (assoc _ _ _)
--         ∙ cong₂ _∙_ refl (sym (assoc _ _ _)
--                        ∙ cong₂ _∙_ refl (sym (assoc _ _ _)
--                        ∙ cong₂ _∙_ refl (sym (assoc _ _ _)
--                        ∙ cong₂ _∙_ refl (assoc _ _ _
--                        ∙ cong₂ _∙_ (sym (assoc _ _ _)
--                        ∙ cong₂ _∙_ refl (sym (assoc _ _ _)
--                        ∙ cong (y ∙_) (sym (assoc _ _ _)
--                        ∙ cong (z ∙_) (sym (assoc _ _ _)
--                        ∙ cong₂ _∙_ refl (lCancel y)
--                        ∙ sym (rUnit _))))) refl))))
--         ∙ assoc _ _ _
--         ∙ assoc _ y _
--         ∙ cong₂ _∙_ refl id2
--         where
--         t₁≡ : t₁ ≡ (-x ∙ -y ∙ x) ∙ y ∙ z ∙ (-x ∙ y ∙ x) ∙ -y
--         t₁≡ = cong₂ _∙_
--           (funExt⁻ (cong fst (Susp·→Ωcomm B
--                           (Iso.inv ΩSuspAdjointIso g) f-xyx)) b)
--           (cong (z ∙_) (cong (-x ∙_)
--                          (assoc _ _ _) ∙ assoc _ _ _))
--                      ∙ sym (assoc _ _ _)

--         id2 : t₃' ∙ ((-x ∙ -y ∙ x) ∙ y ∙ z ∙ (-x ∙ y ∙ x)) ∙ (-z ∙ -y ∙ z)
--             ≡ (-x ∙ (-y ∙ x) ∙ z ∙ -x ∙ y) ∙ (-z ∙ x)
--         id2 = cong (t₃' ∙_)
--           (cong₂ _∙_ (assoc _ _ _ ∙ assoc _ _ _) refl
--           ∙ sym (assoc _ _ _)
--           ∙ cong₂ _∙_ (sym (assoc _ _ _) ∙ sym (assoc _ _ _))
--                       (funExt⁻ (cong fst (Susp·→Ωcomm B f-xyx' f-zyz)) b)
--           ∙ cong₂ _∙_ (assoc _ _ _) refl
--           ∙ assoc _ _ _
--           ∙ cong₂ _∙_ (cong₂ _∙_ refl
--                   (assoc _ _ _
--                  ∙ cong (_∙ z) (sym (symDistr y z)))
--                  ∙ assoc _ _ _
--                  ∙ cong (_∙ z) (sym (assoc _ _ _)
--                               ∙ cong₂ _∙_ refl (rCancel (y ∙ z))
--                               ∙ sym (rUnit _)))
--                  refl)
--           ∙ assoc _ _ _
--           ∙ cong₂ _∙_ (assoc _ _ _
--                       ∙ cong (_∙ z) (assoc _ -x _
--                         ∙ cong₂ _∙_ (sym (assoc _ _ _)
--                           ∙ cong (-x ∙_) (sym (assoc -z x -x)
--                             ∙ cong (-z ∙_) (rCancel x)
--                               ∙ sym (rUnit -z))) refl)) refl
--           ∙ assoc _ _ _
--           ∙ assoc _ _ _
--           ∙ cong (_∙ x) (sym (assoc _ _ _)
--                        ∙ sym (assoc _ _ _)
--                        ∙ sym (assoc _ _ _)
--                        ∙ sym (assoc -x -z _))
--           ∙ sym (assoc _ _ _)
--           ∙ cong (-x ∙_) (cong (_∙ x)
--                  (funExt⁻ (cong fst (Susp·→Ωcomm C fz f-yazay)) c)
--                  ∙ sym (assoc _ _ _))
--           ∙ assoc -x _ _
--           ∙ cong (_∙ (-z ∙ x)) refl

--       rightId₅ : ((((-y ∙ z) ∙ x ∙ -z ∙ -x) ∙ y) ∙ x)
--                   ∙ (-x ∙ (-y ∙ x) ∙ z ∙ -x ∙ y) ∙ -z ∙ x
--                ≡ (-y ∙∙ z ∙ y ∙∙ -z) ∙ x
--       rightId₅ = assoc _ _ _
--                ∙ assoc _ _ _
--                ∙ cong (_∙ x)
--                (cong (_∙ -z) (sym (assoc _ x _)
--                ∙ cong₂ _∙_ refl (assoc x -x _
--                                 ∙ cong₂ _∙_ (rCancel x) refl
--                                 ∙ sym (lUnit _)
--                                 ∙ sym (assoc _ _ _))
--                ∙ sym (assoc _ y _)
--                ∙ cong₂ _∙_ refl (assoc y -y _ ∙ cong₂ _∙_ (rCancel y) refl
--                               ∙ sym (lUnit _))
--                ∙ sym (assoc _ _ _)
--                ∙ cong₂ _∙_ refl (cong₂ _∙_ refl (assoc _ _ _ ∙ assoc _ _ _)
--                               ∙ assoc _ _ _
--                               ∙ cong (_∙ y)
--                                 (cong₂ _∙_ refl (sym (symDistr x (-z ∙ -x)
--                                               ∙ cong (_∙ -x) (symDistr -z -x)))
--                                 ∙ rCancel (x ∙ -z ∙ -x))
--                                 ∙ sym (lUnit y))
--                                 ∙ sym (assoc _ _ _))
--                ∙ sym (assoc _ _ _)
--                ∙ sym (doubleCompPath≡compPath _ _ _))

--       rightId : x ∙∙ cong (fst R) (push a (inr (b , c)))
--                   ∙∙ ((y ∙ -z) ∙ (-y ∙ z))
--               ≡ (-y ∙∙ z ∙ y ∙∙ -z) ∙ x
--       rightId = cong (x ∙∙_∙∙ (y ∙ -z) ∙ (-y ∙ z))
--                      (rightId₁ ∙ rightId₂
--                     ∙ rightId₃)
--               ∙ doubleCompPath≡compPath _ _ _
--               ∙ cong (x ∙_) (rightId₄ ∙ refl)
--               ∙ assoc _ _ _
--               ∙ cong₂ _∙_ (funExt⁻ (cong fst (Susp·→Ωcomm A
--                                      (Iso.inv ΩSuspAdjointIso f) fA)) a)
--                           refl
--               ∙ rightId₅

--       mainId :
--         Square (cong (fst L) (push a (inr (b , c))))
--                (cong (fst R) (push a (inr (b , c))))
--                (lp a) (rp (inr (b , c)))
--       mainId = (leftId ∙ sym rightId)
--             ◁ symP (doubleCompPath-filler
--                      x
--                      (cong (fst R) (push a (inr (b , c))))
--                      ((y ∙ -z) ∙ (-y ∙ z)))

--     main : (a : Susp (typ A))
--           (x : Susp∙ (typ B) ⋀ Susp∙ (typ C))
--         → Square (cong (fst L) (push a x))
--                   (cong (fst R) (push a x))
--                   (lp a) (rp x)
--     main a x =
--         doubleCompPath-filler (lp a ⁻¹) (cong (fst L) (push a x)) (rp x)
--       ▷ asFuns a x
--       where
--       asFuns : (a : Susp (typ A))
--              → (x : Susp∙ (typ B) ⋀ Susp∙ (typ C))
--              → apL a x ≡ apR a x
--       asFuns a = funExt⁻ (⋀→Homogeneous≡ (isHomogeneousPath _ _)
--          λ b c → sym (transport (PathP≡doubleCompPathʳ _ _ _ _)
--                       (symP (mainId a b c))))

--   -- -- Main result
--   -- private
--   --   [f[gh]] = ·whΣ (Susp∙ (typ A)) (_ ⋀∙ _)
--   --                 f
--   --                 (·whΣ (Susp∙ (typ B)) (Susp∙ (typ C))
--   --                   g h)

--   --   [[fg]h] = ·whΣ (_ ⋀∙ _) (Susp∙ (typ C))
--   --                 (·whΣ (Susp∙ (typ A)) (Susp∙ (typ B))
--   --                   f g) h

--   --   [g[fh]] = ·whΣ (Susp∙ (typ B)) (_ ⋀∙ _)
--   --                 g
--   --                 (·whΣ (Susp∙ (typ A)) (Susp∙ (typ C))
--   --                   f h)

--   -- JacobiΣR : [f[gh]]
--   --          ≡ ·Susp (Susp∙ (typ A) ⋀∙ (Susp∙ (typ B) ⋀∙ Susp∙ (typ C)))
--   --                  ([[fg]h] ∘∙ suspFun∙ (Iso.fun SmashAssocIso))
--   --                  ([g[fh]] ∘∙ suspFun∙ (Iso.inv SmashAssocIso
--   --                                     ∘ (⋀comm→∙ ⋀→ idfun∙ _)
--   --                                     ∘ Iso.fun SmashAssocIso))
--   -- JacobiΣR = sym (·wh≡·whΣ _ _ _ _)
--   --          ∙ cong₂ _∘∙_
--   --              ((cong (·wh (Susp∙ (typ A)) (Susp∙ (typ B) ⋀∙ Susp∙ (typ C)) f)
--   --                      (sym (·wh≡·whΣ _ _ _ _)))
--   --              ∙ JacobiR)
--   --              refl
--   --          ∙ fromSusp≅fromJoin⁻Pres+* _ _
--   --          ∙ cong₂ (·Susp (Susp∙ (typ A) ⋀∙ (Susp∙ (typ B) ⋀∙ Susp∙ (typ C))))
--   --                  (∘∙-assoc _ _ _
--   --                 ∙ (cong₂ _∘∙_ l1 l2
--   --                 ∙ sym (∘∙-assoc _ _ _))
--   --                 ∙ cong (_∘∙ suspFun∙ (fun SmashAssocIso))
--   --                   (·wh≡·whΣ (Susp∙ (typ A) ⋀∙ Susp∙ (typ B))
--   --                             (Susp∙ (typ C))
--   --                             (·whΣ (Susp∙ (typ A))
--   --                             (Susp∙ (typ B)) f g) h))
--   --                    (∘∙-assoc _ _ _
--   --                  ∙ cong₂ _∘∙_ r1 r2
--   --                  ∙ sym (∘∙-assoc _ _ _)
--   --                  ∙ cong (_∘∙ suspFun∙ compFun)
--   --                         (·wh≡·whΣ (Susp∙ _) (_ ⋀∙ _)
--   --                                   g (·whΣ (Susp∙ (typ A)) (Susp∙ (typ C)) f h)))
--   --     where
--   --     compFun = inv SmashAssocIso
--   --             ∘ (⋀comm→∙ ⋀→ idfun∙ (Susp∙ (typ C)))
--   --             ∘ fun SmashAssocIso

--   --     r1 : whB-AC g (whAC f h ∘∙ Σ[A⋀C]→ΣA*ΣC)
--   --        ≡ whB-AC g (·whΣ (Susp∙ (typ A)) (Susp∙ (typ C)) f h)
--   --     r1 = cong (whB-AC g) (·wh≡·whΣ _ _ _ _)
--   --     SJ = fst (SuspSmash→Join∙ (Susp∙ (typ B)) (Susp∙ (typ A) ⋀∙ Susp∙ (typ C)))

--   --     r2 : correction₂
--   --       ∘∙ SuspSmash→Join∙ (Susp∙ (typ A)) (Susp∙ (typ B) ⋀∙ Susp∙ (typ C))
--   --       ≡ SuspSmash→Join∙ (Susp∙ (typ B)) (Susp∙ (typ A) ⋀∙ Susp∙ (typ C))
--   --       ∘∙ suspFun∙ compFun
--   --     r2 = ΣPathP ((funExt (λ x
--   --       → cong SJ (cong (suspFun (inv SmashAssocIso) ∘
--   --                         Join→SuspSmash
--   --                        ∘ join→ ⋀comm→ (λ c → c) --
--   --                        ∘ SuspSmash→Join
--   --                        ∘ suspFun (fun SmashAssocIso))
--   --              (SuspSmash→Join→SuspSmash x ))
--   --       ∙∙ cong SJ
--   --              (cong (suspFun (inv SmashAssocIso))
--   --                (SuspFun-Join→SuspSmash≡ ⋀comm→∙ (idfun∙ (Susp∙ (typ C)))
--   --                  (SuspSmash→Join (suspFun (fun SmashAssocIso) x))))
--   --       ∙∙ (cong SJ
--   --                (funExt⁻ (sym (suspFunComp (inv SmashAssocIso) (⋀comm→∙ ⋀→ idfun∙ _)))
--   --                  (Join→SuspSmash (SuspSmash→Join (suspFun (fun SmashAssocIso) x))))
--   --        ∙∙ cong SJ (cong (suspFun (inv SmashAssocIso
--   --                                ∘ (⋀comm→∙ ⋀→ idfun∙ (Susp∙ (typ C)))))
--   --                         (SuspSmash→Join→SuspSmash (suspFun (fun SmashAssocIso) x)))
--   --        ∙∙ cong SJ (funExt⁻ (sym (suspFunComp (inv SmashAssocIso
--   --                                ∘ (⋀comm→∙ ⋀→ idfun∙ (Susp∙ (typ C))))
--   --                                (fun SmashAssocIso))) x))))
--   --          , ((cong₂ _∙_ refl (cong₂ _∙_
--   --                    (cong (congS (fst (Jcorrection₁⁻ (Susp∙ (typ B)) (Susp∙ (typ A)) (Susp∙ (typ C)))))
--   --                          (sym (rUnit (sym (push (inl tt) north))))) refl ∙ rCancel (push north (inl tt)))
--   --                  ∙ sym (rUnit _))
--   --           ◁ (flipSquare ((cong₃ _∙∙_∙∙_ refl refl (sym (rUnit _))
--   --                        ∙ ∙∙lCancel (push north (inl tt)))
--   --                       ◁ (λ j i → push north (inl tt) (~ j)))
--   --            ▷ lUnit (sym (push north (inl tt))))))

--   --     l1 : whAB-C (whAB f g ∘∙ Σ[A⋀B]→ΣA*ΣB) h
--   --       ≡ ·wh (Susp∙ (typ A) ⋀∙ Susp∙ (typ B)) (Susp∙ (typ C))
--   --             (·whΣ (Susp∙ (typ A)) (Susp∙ (typ B)) f g) h
--   --     l1 = cong₂ (·wh (Susp∙ (typ A) ⋀∙ Susp∙ (typ B)) (Susp∙ (typ C)))
--   --                (·wh≡·whΣ _ _ _ _) refl

--   --     l2 : correction₁
--   --       ∘∙ SuspSmash→Join∙ (Susp∙ (typ A)) (Susp∙ (typ B) ⋀∙ Susp∙ (typ C))
--   --       ≡ (SuspSmash→Join∙ (Susp∙ (typ A) ⋀∙ Susp∙ (typ B)) (Susp∙ (typ C))
--   --       ∘∙ suspFun∙ (fun SmashAssocIso))
--   --     l2 =
--   --       ΣPathP ((funExt (λ x
--   --       → cong (SuspSmash→Join∙ (Susp∙ (typ A) ⋀∙ Susp∙ (typ B)) (Susp∙ (typ C)) .fst)
--   --              (cong (suspFun (fun SmashAssocIso)) (SuspSmash→Join→SuspSmash x))))
--   --              , compPathL→PathP (cong₂ _∙_ refl (sym (rUnit _) ∙ rCancel _)
--   --              ∙ sym (rUnit _)
--   --              ∙ lUnit _) )

-- JacobiR' :
--   ∀ {ℓ ℓ' ℓ'' ℓ'''} {D : Pointed ℓ'''}
--      (A A' : Pointed ℓ) (eA : A ≃∙ Susp∙ (typ A'))
--      (B B' : Pointed ℓ') (eB : B ≃∙ Susp∙ (typ B'))
--      (C C' : Pointed ℓ'') (eC : C ≃∙ Susp∙ (typ C'))
--      (f : Susp∙ (typ A) →∙ D)
--      (g : Susp∙ (typ B) →∙ D)
--      (h : Susp∙ (typ C) →∙ D)
--      → ·wh A (B ⋀∙ C) f (·wh B C g h ∘∙ SuspSmash→Join∙ B C)
--       ≡ (·wh (A ⋀∙ B) C (·wh A B f g ∘∙ SuspSmash→Join∙ A B) h ∘∙ Jcorrection₁ A B C)
--       +* (·wh B (A ⋀∙ C) g (·wh A C f h ∘∙ SuspSmash→Join∙ A C) ∘∙ Jcorrection₂ A B C)
-- JacobiR' {D = D} A A' eA B B' eB C C' eC =
--   transport (λ i → (f : Susp∙ (typ (pA i)) →∙ D)
--      (g : Susp∙ (typ (pB i)) →∙ D)
--      (h : Susp∙ (typ (pC i)) →∙ D)
--      → ·wh (pA i) ((pB i) ⋀∙ (pC i)) f (·wh (pB i) (pC i) g h
--                                         ∘∙ SuspSmash→Join∙ (pB i) (pC i))
--       ≡ (·wh ((pA i) ⋀∙ (pB i)) (pC i) (·wh (pA i) (pB i) f g
--                                         ∘∙ SuspSmash→Join∙ (pA i) (pB i)) h
--         ∘∙ Jcorrection₁ (pA i) (pB i) (pC i))
--       +* (·wh (pB i) ((pA i) ⋀∙ (pC i)) g (·wh (pA i) (pC i) f h
--                                            ∘∙ SuspSmash→Join∙ (pA i) (pC i))
--        ∘∙ Jcorrection₂ (pA i) (pB i) (pC i)))
--       (JacobiR A' B' C')
--   where
--   pA = ua∙ (fst eA) (snd eA) ⁻¹
--   pB = ua∙ (fst eB) (snd eB) ⁻¹
--   pC = ua∙ (fst eC) (snd eC) ⁻¹
