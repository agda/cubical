{-# OPTIONS --safe #-}

module Cubical.HITs.CauchyReals.Experiment where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding


open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
-- open import Cubical.Data.Fin

import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos;ℤ)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad


open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationDer
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Uniform
open import Cubical.HITs.CauchyReals.PiNumber
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Summation

open import Cubical.Algebra.Ring.BigOps


open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing.Base
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.TrigonometricIdentities
open import Cubical.HITs.CauchyReals.ArcSin
open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.Relation.Binary.Base
open import Cubical.HITs.CauchyReals.Circle
open import Cubical.HITs.CauchyReals.CircleMore
open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.Group.Instances.Int

open import Cubical.Algebra.Group.ZAction

open import Cubical.HITs.SequentialColimit as Seq
open import Cubical.Data.Sequence
open import Cubical.HITs.CauchyReals.RealHomotopy

private
 variable
  ℓ : Level
  A B : Type ℓ
  


module Version1-Metric
   (A : Type ℓ)
   (distA : A → A → ℝ)
   where
   
 data Space : Type ℓ where
  pt : A → Space
  path : (p : ∀ x → x ∈ intervalℙ 0 1 → A)
           → pt (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)) ≡ pt (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))
  const≡refl : ∀ a → path (λ _ _ → a) ≡ λ _ → pt a


-- module Version1 where
--  data Space (A : Type ℓ) : Type ℓ where
--   pt : A → Space A
--   path : (p : ∀ x → x ∈ intervalℙ 0 1 → A)
--            → pt (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)) ≡ pt (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))
--   const≡refl : ∀ a → path (λ _ _ → a) ≡ λ _ → pt a


--  record ElimSpace {ℓ'} (A : Type ℓ) (T : Space A → Type ℓ') :
--    Type (ℓ-max ℓ ℓ') where
--   field
--    pt-f : ∀ x → T (pt x) 
--    path-f : ∀ p → PathP (λ i → T (path p i))
--      (pt-f (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
--      (pt-f (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))) 
--    const≡refl-f : ∀ x →
--      SquareP (λ i j → T (const≡refl x i j))
--        (path-f (λ _ _ → x))
--        refl
--        refl
--        refl

--   go : ∀ x → T x
--   go (pt x) = pt-f x
--   go (path p i) = path-f p i
--   go (const≡refl a i i₁) = const≡refl-f a i i₁

--  record ElimSpaceSet {ℓ'} (A : Type ℓ) (T : Space A → Type ℓ') :
--    Type (ℓ-max ℓ ℓ') where
--   no-eta-equality
--   field
--    pt-f : ∀ x → T (pt x) 
--    path-f : ∀ p → PathP (λ i → T (path p i))
--      (pt-f (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
--      (pt-f (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
--    isSetT : ∀ x → isSet (T x)

--   go : ∀ x → T x
--   go = ElimSpace.go w
--    where
--    w : ElimSpace A T
--    w .ElimSpace.pt-f = pt-f
--    w .ElimSpace.path-f = path-f
--    w .ElimSpace.const≡refl-f x =
--      isSet→SquareP (λ _ _ → isSetT _) _ _ _ _ 

--  record ElimSpaceProp {ℓ'} (A : Type ℓ) (T : Space A → Type ℓ') :
--    Type (ℓ-max ℓ ℓ') where
--   no-eta-equality
--   field
--    pt-f : ∀ x → T (pt x) 
--    isPropT : ∀ x → isProp (T x)

--   go : ∀ x → T x
--   go = ElimSpaceSet.go w
--    where
--    w : ElimSpaceSet A (λ z → T z)
--    w .ElimSpaceSet.pt-f = pt-f
--    w .ElimSpaceSet.path-f _ = isProp→PathP (λ _ → isPropT _) _ _ 
--    w .ElimSpaceSet.isSetT _ = isProp→isSet (isPropT _)
   
--  record ElimSpaceSet₂ {ℓ'} (A B : Type ℓ) (T : Space A → Space B → Type ℓ') :
--    Type (ℓ-max ℓ ℓ') where
--   no-eta-equality
--   field
--    pt-pt-f : ∀ a b → T (pt a) (pt b)
--    pt-path-f : ∀ a p
--      → PathP (λ i → T (pt a) (path p i))
--      (pt-pt-f a (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
--      (pt-pt-f a (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
--    path-pt-f : ∀ p b
--      → PathP (λ i → T (path p i) (pt b))
--      (pt-pt-f (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)) b)
--      (pt-pt-f (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)) b)
--    isSetT : ∀ x y → isSet (T x y)

--   go : ∀ x y → T x y
--   go = ElimSpaceSet.go w
--    where
--     w : ElimSpaceSet A (λ z → (y : Space B) → T z y)
--     w .ElimSpaceSet.pt-f x = ElimSpaceSet.go ww
--      where
--      ww : ElimSpaceSet B (λ z → T (pt x) z)
--      ww .ElimSpaceSet.pt-f = pt-pt-f x
--      ww .ElimSpaceSet.path-f = pt-path-f x
--      ww .ElimSpaceSet.isSetT _ = isSetT _ _
     
--     w .ElimSpaceSet.path-f p = funExt (ElimSpaceProp.go ww)
--      where
--      ww : ElimSpaceProp B
--            (λ z →
--               PathP (λ z₁ → T (path p z₁) z)
--               (w .ElimSpaceSet.pt-f (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)) z)
--               (w .ElimSpaceSet.pt-f (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)) z))
--      ww .ElimSpaceProp.pt-f b = path-pt-f p b
--      ww .ElimSpaceProp.isPropT x = isOfHLevelPathP' 1 (isSetT _ _) _ _
--     w .ElimSpaceSet.isSetT _ = isSetΠ λ _ → isSetT _ _

--  record ElimSpaceGroupoid₂ {ℓ'} (A B : Type ℓ) (T : Space A → Space B → Type ℓ') :
--    Type (ℓ-max ℓ ℓ') where
--   no-eta-equality
--   field
--    pt-pt-f : ∀ a b → T (pt a) (pt b)
--    pt-path-f : ∀ a p
--      → PathP (λ i → T (pt a) (path p i))
--      (pt-pt-f a (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
--      (pt-pt-f a (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
--    path-pt-f : ∀ p b
--      → PathP (λ i → T (path p i) (pt b))
--      (pt-pt-f (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)) b)
--      (pt-pt-f (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)) b)
--    path-path-f : ∀ p p' → SquareP (λ j i → T (path p i) (path p' j))
         
--          (path-pt-f p (p' 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
--          (path-pt-f p (p' 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
--          (pt-path-f (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)) p')
--          (pt-path-f (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)) p')
--    const-refl≡-Left : ∀ a (x : B) →
--       SquareP (λ i j → T (pt a) (const≡refl x i j))
--       (pt-path-f a (λ _ _ → x)) refl refl refl
--    const-refl≡-Right : ∀ a (x : B) →
--       SquareP (λ i j → T (const≡refl a i j) (pt x))
--       (path-pt-f (λ _ _ → a) x) refl refl refl
--    isGroupoidT : ∀ x y → isGroupoid (T x y)

--   go : ∀ x y → T x y
--   go = ElimSpace.go w
--    where
--     w : ElimSpace A (λ z → (y : Space B) → T z y)
--     w .ElimSpace.pt-f a = ElimSpace.go ww
--       where
--        ww : ElimSpace B (λ z → T (pt a) z)
--        ww .ElimSpace.pt-f = pt-pt-f a
--        ww .ElimSpace.path-f = pt-path-f a
--        ww .ElimSpace.const≡refl-f = const-refl≡-Left a
--     w .ElimSpace.path-f p = funExt (ElimSpaceSet.go ww)
--       where
--        ww : ElimSpaceSet B _
--        ww .ElimSpaceSet.pt-f = path-pt-f p
--        ww .ElimSpaceSet.path-f = path-path-f p 
--        ww .ElimSpaceSet.isSetT _ = isOfHLevelPathP' 2 (isGroupoidT _ _) _ _
      
--     w .ElimSpace.const≡refl-f x = congP (λ _ → funExt)
--       (funExt (ElimSpaceProp.go ww))
--      where
--      ww : ElimSpaceProp B _
--      ww .ElimSpaceProp.pt-f b = const-refl≡-Right x b
--      ww .ElimSpaceProp.isPropT _ =
--        isOfHLevelPathP' 1 (isGroupoidT _ _ _ _) _ _


--  mapSpace : (A → B) → Space A → Space B
--  mapSpace f = ElimSpace.go w
--   where
--   w : ElimSpace _ _
--   w .ElimSpace.pt-f = pt ∘ f
--   w .ElimSpace.path-f p = path (λ t t∈ → f (p t t∈))
--   w .ElimSpace.const≡refl-f a = const≡refl (f a)

--  isoSpace : Iso A B → Iso (Space A) (Space B)
--  isoSpace isoAB = w
--    where
--    open Iso isoAB

--    secMap : {f : A → B} {g : B → A} → section f g
--               → section (mapSpace f) (mapSpace g)
--    secMap s = ElimSpace.go ww
--     where
--        ww : ElimSpace _ _
--        ww .ElimSpace.pt-f x = cong pt (s _)
--        ww .ElimSpace.path-f p i j = path (λ t t∈ → s (p t t∈) j) i
--        ww .ElimSpace.const≡refl-f a i j k = const≡refl (s a k) i j
       
--    w : Iso (Space _) (Space _)
--    w .Iso.fun = mapSpace fun
--    w .Iso.inv = mapSpace inv
--    w .Iso.rightInv = secMap rightInv
--    w .Iso.leftInv = secMap leftInv


--  ℝPath : {A : Type ℓ} → A → A → Type ℓ
--  ℝPath {A = A} a₀ a₁ =
--    Σ (∀ t → t ∈ intervalℙ 0 1 → A)
--     λ p → (a₀ ≡ p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)) × (a₁ ≡ p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))

--  symℝPath : ∀ (a b : A) → ℝPath a b → ℝPath b a
--  symℝPath a b (p , pa , pb) =
--    (λ t t∈ → p (1 -ᵣ t) {!!}) ,
--     (pb ∙ {!!}) , (pa ∙ {!!} )

--  ℝPath→SpPath : ∀ {a b : A} → ℝPath a b → Path (Space A) (pt a) (pt b)
--  ℝPath→SpPath (p , p0 , p1) = cong pt p0 ∙∙ path p ∙∙ cong pt (sym p1)


--  isOfHLevelℝPath : ∀ n
--     → isOfHLevel n A
--     → ∀ (a₀ a₁ : A)
--     → isOfHLevel n (ℝPath a₀ a₁)
--  isOfHLevelℝPath n hl _ _ =
--    isOfHLevelΣ n (isOfHLevelΠ2 n λ _ _ → hl)
--     λ _ → isOfHLevel× n (isOfHLevelPath n hl _ _) (isOfHLevelPath n hl _ _)


--  module _ (A : Type ℓ) (isSetA : isSet A) where

--   opaque
--    SpℝPathPreConcat : ∀ {a b c : A} → ℝPath a b → ℝPath b c → ℝPath a c 
--    SpℝPathPreConcat (p , p0 , p1) (q , q0 , q1) =
--      pq
--       , {!!}
--       , {!!}

--     where

--     -- pqw : {!!}
--     -- pqw = {!!}


--     pq : (t : ℝ) → t ∈ intervalℙ 0 1 → A
--     pq t t∈ = stichSetFns
--       A
      
--       (rat [ 1 / 4 ])
--       (rat [ 1 / 2 ])
--       decℚ<ᵣ?
--       (λ t t<1/2 → p (clampᵣ 0 1 (t ·ᵣ 4))
--          ({!!} , {!!}))
--       (λ t 1/4<t → q (clampᵣ 0 1 ((t ·ᵣ 2) -ᵣ 1)) {!!})
--       isSetA
--       {!!} t

--    SpℝPathPreConcatInvolHom : ∀ {a b c : A} → (pab : ℝPath a b)
--      → (pbc : ℝPath b c)
--       → ℝPath (SpℝPathPreConcat (symℝPath _ _ pab)
--         (SpℝPathPreConcat pab pbc )) pbc
--    SpℝPathPreConcatInvolHom = {!!}

  
--   SpℝPathPreConcatRet : ∀ {a b c : A} → (pab : ℝPath a b) →
--      retract (mapSpace (SpℝPathPreConcat {a} {b} {c} pab))
--       (mapSpace (SpℝPathPreConcat {b} {a} {c} (symℝPath a b pab)))
--   SpℝPathPreConcatRet pab (pt x) = ℝPath→SpPath
--     (SpℝPathPreConcatInvolHom pab x)
--   SpℝPathPreConcatRet pab (path p i) j = {!!}
--   SpℝPathPreConcatRet pab (const≡refl a i i₁) = {!!}
  
--   SpℝPathPreConcatIso : ∀ {a b c : A} → ℝPath a b →
--     Iso (Space (ℝPath b c)) (Space (ℝPath a c))
--   SpℝPathPreConcatIso pab .Iso.fun =
--     mapSpace (SpℝPathPreConcat pab)
--   SpℝPathPreConcatIso pab .Iso.inv =
--     mapSpace (SpℝPathPreConcat (symℝPath _ _ pab))
--   SpℝPathPreConcatIso pab .Iso.rightInv = {!!}
--   SpℝPathPreConcatIso pab .Iso.leftInv = {!!}


--   SpℝPathPostConcatIso : ∀ {a b c : A} → ℝPath b c →
--     Iso (Space (ℝPath a b)) (Space (ℝPath a c))
--   SpℝPathPostConcatIso pbc .Iso.fun =
--     mapSpace (flip SpℝPathPreConcat pbc)
--   SpℝPathPostConcatIso pbc .Iso.inv =
--     mapSpace (flip SpℝPathPreConcat (symℝPath _ _ pbc))
--   SpℝPathPostConcatIso pbc .Iso.rightInv = {!!}

--   SpℝPathPostConcatIso  pbc .Iso.leftInv = {!!}

--   SpℝPathPreConcatEquiv : ∀ {a b c : A} → ℝPath a b →
--       (Space (ℝPath b c)) ≃ (Space (ℝPath a c))
--   SpℝPathPreConcatEquiv pab = isoToEquiv (SpℝPathPreConcatIso pab)

--   SpℝPathPostConcatEquiv : ∀ {a b c : A} → ℝPath b c →
--       (Space (ℝPath a b)) ≃ (Space (ℝPath a c))
--   SpℝPathPostConcatEquiv pbc = isoToEquiv (SpℝPathPostConcatIso pbc)



--   EncodedSpacePath₂ : Space A → Space A → Type ℓ 
--   EncodedSpacePath₂ (pt x) (pt x₁) = Space (ℝPath x x₁)
--   EncodedSpacePath₂ (pt x) (path p i) =
--     ua (SpℝPathPostConcatEquiv {a = x}
--       (p , refl , refl)) i
--   EncodedSpacePath₂ (pt x) (const≡refl a i i₁) = {!!}
--   EncodedSpacePath₂ (path p i) (pt x) =
--     ua (SpℝPathPreConcatEquiv {c = x} (p , refl , refl)) (~ i)
--   EncodedSpacePath₂ (path p i) (path p₁ i₁) = {!!}
--   EncodedSpacePath₂ (path p i) (const≡refl a i₁ i₂) = {!!}
--   EncodedSpacePath₂ (const≡refl a i i₁) (pt x) = {!!}
--   EncodedSpacePath₂ (const≡refl a i i₁) (path p i₂) = {!!}
--   EncodedSpacePath₂ (const≡refl a i i₁) (const≡refl a₁ i₂ i₃) = {!!}

  

--   DecodeSpacePath₂ : ∀ a₀ a₁ → a₀ ≡ a₁ → EncodedSpacePath₂ a₀ a₁
--   DecodeSpacePath₂ a₀ _ =
--    J (λ a₁ (p : a₀ ≡ a₁) → EncodedSpacePath₂ a₀ a₁)
--      (ElimSpace.go ww a₀)
--    where
--    ww : ElimSpace _ (λ a₀ → EncodedSpacePath₂ a₀ a₀)
--    ww .ElimSpace.pt-f a₀ = pt ((λ _ _ → a₀) , refl , refl) 
--    ww .ElimSpace.path-f p = {!ℝPath→SpPath!}
--    ww .ElimSpace.const≡refl-f = {!!}
   
--   DecodeSpacePath₂Pt : ∀ a₀ a₁ → Path (Space A) (pt a₀) (pt a₁)
--     → Space (ℝPath a₀ a₁) 
--   DecodeSpacePath₂Pt a₀ a₁ = DecodeSpacePath₂ (pt a₀) (pt a₁)
  
-- -- ElimSpaceGroupoid₂.go w
-- --    where
-- --    w : ElimSpaceGroupoid₂ _ _ (λ _ _ → hSet _)
-- --    w .ElimSpaceGroupoid₂.pt-pt-f a₀ a₁ =
-- --      Space (ℝPath a₀ a₁) , {!!}
-- --    w .ElimSpaceGroupoid₂.pt-path-f a p =
-- --      {!!}
-- --      -- {!SpℝPathPreConcatEquiv (p , refl , refl)!}
-- --    w .ElimSpaceGroupoid₂.path-pt-f p b =
-- --      TypeOfHLevel≡ 2 (sym (ua (SpℝPathPreConcatEquiv (p , refl , refl))))
-- --    w .ElimSpaceGroupoid₂.path-path-f p p' = {!!}
-- --    w .ElimSpaceGroupoid₂.const-refl≡-Left a x = {!!}
-- --    w .ElimSpaceGroupoid₂.const-refl≡-Right a x = {!!}
-- --    w .ElimSpaceGroupoid₂.isGroupoidT = {!!}

-- --  Spₙ : (A : Type ℓ) → ℕ → Type ℓ
-- --  Spₙ A zero = A
-- --  Spₙ A (suc x) = Space (Spₙ A x)



-- --  -- Spₙ-prediag2 : Space {ℓ} A → I → Space {ℓ} A 
-- --  -- Spₙ-prediag2 (pt x) _ = pt x
-- --  -- Spₙ-prediag2 (path p i) j = {!(path p j)!}
-- --  -- Spₙ-prediag2 (const≡refl a i i₁) x₁ = {!!}

 
-- --  -- Spₙ-prediag : ∀ A n → Spₙ {ℓ} A (suc (suc n)) → I → Spₙ A (suc n)
-- --  -- Spₙ-prediag A n (pt x) _ = x
-- --  -- Spₙ-prediag A zero (path p i) j =
-- --  --   let z = path (λ t t∈ → {!p t t∈!}) 
-- --  --   in {!!}
-- --  -- Spₙ-prediag A (suc n) (path p i) j =
-- --  --   let z = ((path (λ t t∈ → Spₙ-prediag A n (p t t∈) i) i))
-- --  --   in {!z!}
        
-- --  -- Spₙ-prediag A n (const≡refl a i i₁) x₁ = {!!}
 
-- --  zzz : (f : (ℝ × ℝ) → (ℝ × ℝ)) →
-- --         Square {A = Spₙ (ℝ × ℝ) 2}
-- --           (path λ jᵣ _ → pt (f (0 , jᵣ)))
-- --           (path λ jᵣ _ → pt (f (1 , jᵣ)))
-- --           (cong pt (path λ iᵣ _ → (f (iᵣ , 0))))
-- --           (cong pt (path λ iᵣ _ → (f (iᵣ , 1))))
-- --  zzz f i =
-- --    path (λ jᵣ _ → path (λ iᵣ _ → f (iᵣ , jᵣ)) i)


-- --  Spₙ-seq : (A : Type ℓ) → Sequence ℓ
-- --  Spₙ-seq A .Sequence.obj = Spₙ A
-- --  Spₙ-seq A .Sequence.map = pt
 
-- --  Sp : (A : Type ℓ) → Type ℓ
-- --  Sp A = SeqColim (Spₙ-seq A)


-- --  ℝ·ₙ : ∀  n → ℝ → Spₙ ℝ n → Spₙ ℝ n
-- --  ℝ·ₙ zero x x₁ = x ·ᵣ x₁
-- --  ℝ·ₙ (suc n) x (pt x₁) = pt (ℝ·ₙ n x x₁)
-- --  ℝ·ₙ (suc n) x (path p i) = path (λ t t∈ → ℝ·ₙ n x (p t t∈)) i
-- --  ℝ·ₙ (suc n) x (const≡refl a i i₁) =
-- --    const≡refl (ℝ·ₙ n x a) i i₁

  
-- --  _ℝ·_ : ℝ → Sp ℝ → Sp ℝ
-- --  x ℝ· incl x₁ = incl (ℝ·ₙ _ x x₁)
-- --  x ℝ· push x₁ i = push (ℝ·ₙ _ x x₁) i


-- --  opaque
-- --   inclPt : ∀ {A : Type ℓ} → (a : A) → ∀ n → Σ (Spₙ A n)
-- --     λ x → Path (Sp A) (incl {n = 0} a) (incl x) 
-- --   inclPt a zero = _ , refl
-- --   inclPt a (suc n) = _ , snd (inclPt a n) ∙ push _



-- --   -- Spₙ-corner : ∀ n → (x : Spₙ {ℓ} A n) →
-- --   --   Σ (Space A) λ x₀ → Path (Sp A) (incl {n = 1} x₀) (incl  x) 
-- --   -- Spₙ-corner zero x = _ , sym (push _)
-- --   -- Spₙ-corner (suc n) (pt x) =
-- --   --   let z , zz = Spₙ-corner n x
-- --   --     in z , zz ∙ push _
-- --   -- Spₙ-corner (suc n) (path p i) =
-- --   --   let u = path (λ t t∈ → fst (Spₙ-corner n (p t t∈))) i
-- --   --   in {!u !}
-- --   -- Spₙ-corner (suc n) (const≡refl a i i₁) = {!!}


-- --  --  ℝ·ₙ0 : ∀ n x → ℝ·ₙ n 0 x ≡ fst (inclPt 0 n) 
-- --  --  ℝ·ₙ0 zero x = 𝐑'.0LeftAnnihilates _
-- --  --  ℝ·ₙ0 (suc n) (pt x) i = pt (ℝ·ₙ0 n x i)
-- --  --  ℝ·ₙ0 (suc n) (path p j) i =
-- --  --    hcomp
-- --  --      (λ k →
-- --  --         λ { (i = i0) → path
-- --  --           (λ t t∈ → ℝ·ₙ0 n (p t t∈) (~ k)) j
-- --  --           ; (i = i1) → pt (fst (inclPt 0 n))
-- --  --           ; (j = i0) → pt ((ℝ·ₙ0 n (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)) (i ∨ ~ k)))
-- --  --           ; (j = i1) → pt ((ℝ·ₙ0 n (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)) (i ∨ ~ k)))
-- --  --         })
-- --  --      (const≡refl (fst (inclPt (rat [ pos 0 , (1+ 0) ]/) n)) i j)
-- --  --  ℝ·ₙ0 (suc n) (const≡refl a i₁ i₂) i = {!!}




-- --  -- ℝ·ₙ1 : ∀ n x → ℝ·ₙ n 1 x ≡ x 
-- --  -- ℝ·ₙ1 zero x = ·IdL _
-- --  -- ℝ·ₙ1 (suc n) (pt x) i = pt (ℝ·ₙ1 n x i)
-- --  -- ℝ·ₙ1 (suc n) (path p i₁) i = path (λ t t∈ → ℝ·ₙ1 n (p t t∈) i) i₁
-- --  -- ℝ·ₙ1 (suc n) (const≡refl a i₁ i₂) i = const≡refl (ℝ·ₙ1 n a i) i₁ i₂

-- --  -- opaque
-- --  --  incl-path : ∀ n x → Path (Sp ℝ)
-- --  --    (incl (fst (inclPt {A = ℝ} 0 n)))
-- --  --    (incl {n = n} x)

-- --  --  incl-path n x i = 
-- --  --    hcomp
-- --  --       (λ k →
-- --  --         λ { (i = i0) → push {n = n} (ℝ·ₙ0 n x k) (~ k)
-- --  --           ; (i = i1) → push {n = n} (ℝ·ₙ1 n x k) (~ k)
-- --  --         })
-- --  --         (incl {n = suc n} (
-- --  --         (path (λ t t∈ → ℝ·ₙ n t x) i)))

-- --  --  sqIsContrSpℝ : ∀ n (x : Spₙ ℝ n) →
-- --  --     Square {A = (Sp ℝ)}
-- --  --       (snd (inclPt (rat [ pos 0 , (1+ 0) ]/) n) ∙ (incl-path n x))
-- --  --       (snd (inclPt (rat [ pos 0 , (1+ 0) ]/) (suc n))
-- --  --         ∙  (incl-path (suc n) (pt x)))
-- --  --       (λ _ → incl 0)
-- --  --       (push x)

-- --  --  sqIsContrSpℝ zero x i i₁ = {!!}
-- --  --  sqIsContrSpℝ (suc n) x = {!!}
 
-- --  -- isContrSpℝ : isContr (Sp ℝ)
-- --  -- isContrSpℝ .fst = incl {n = 0} 0
-- --  -- isContrSpℝ .snd (incl {n = n} x) =
-- --  --           snd (inclPt 0 n)
-- --  --            ∙  (incl-path n x)
-- --  -- isContrSpℝ .snd (push {n} x i)  = sqIsContrSpℝ n x i


-- --  circleBase : distCircle
-- --  circleBase = Circle→distCircle (injCircle (rat [ pos 0 / 1+ 0 ]))

-- --  circleBase≡inj1 : Circle→distCircle (injCircle 1) ≡ circleBase
-- --  circleBase≡inj1 = cong Circle→distCircle (eq/ _ _ (1 , -ᵣ-rat₂ 1 0))


-- --  rotateSpₙDC : distCircle → Spₙ distCircle 1 → Spₙ distCircle 1
-- --  rotateSpₙDC a = mapSpace (ℝS¹._+ a)
-- --   -- where
-- --   -- w : ElimSpace (Spₙ distCircle 0) (λ _ → Spₙ distCircle 1)
-- --   -- w .ElimSpace.pt-f x = pt (x ℝS¹.+ a)
-- --   -- w .ElimSpace.path-f p = path (λ t t∈ → (p t t∈) ℝS¹.+ a) 
-- --   -- w .ElimSpace.const≡refl-f x = const≡refl _
 
-- --  -- rotateSpₙDCIso : ℝ → Iso {!!} {!!}
-- --  -- rotateSpₙDCIso = {!!}

-- --  opaque
-- --   arcLength : ((x : ℝ) → x ∈ intervalℙ 0 1 → distCircle) → ℝ 
-- --   arcLength = {!!}

-- --   arcLenghIsLength : ∀ p →
-- --      p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?) ℝS¹.+
-- --       Circle→distCircle (injCircle (arcLength p))
-- --       ≡ p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)
-- --   arcLenghIsLength = {!!}
  
-- --  -- SelfEncodeDC : Spₙ distCircle 1 → Σ Type λ A → A
-- --  -- SelfEncodeDC = ElimSpace.go w
-- --  --  where
-- --  --  w : ElimSpace _ _
-- --  --  w .ElimSpace.pt-f x = _ , x
-- --  --  w .ElimSpace.path-f p = ΣPathP (ua (rotationEquiv
-- --  --   (Circle→distCircle (injCircle (arcLength p)))) , ua-gluePath _
-- --  --    (arcLenghIsLength p))
-- --  --  w .ElimSpace.const≡refl-f = {!!}
 
-- --  Encodeℝ₀ : Spₙ distCircle 1 → hSet ℓ-zero
-- --  Encodeℝ₀ = ElimSpace.go w
-- --   where
-- --   w : ElimSpace distCircle (λ _ → hSet ℓ-zero)
-- --   w .ElimSpace.pt-f _ = ℝ , isSetℝ
-- --   w .ElimSpace.path-f p = TypeOfHLevel≡ 2 (ua (_+ᵣ (arcLength p) , {!!}))  
-- --   w .ElimSpace.const≡refl-f = {!!}

-- --  -- encodeℝ₀Base : ∀ x → fst (Encodeℝ₀ x)
-- --  -- encodeℝ₀Base = ElimSpaceSet.go w
-- --  --  where
-- --  --  w : ElimSpaceSet _ _
-- --  --  w .ElimSpaceSet.pt-f x = {!x!}
-- --  --  w .ElimSpaceSet.path-f = {!!}
-- --  --  w .ElimSpaceSet.isSetT = snd ∘ Encodeℝ₀

-- --  decodeDSPath : ∀ c₀ c₁ → Path (Spₙ distCircle (suc zero)) (pt c₀) (pt c₁) → ℝ
-- --  decodeDSPath c₀ c₁ p = subst (fst ∘ Encodeℝ₀) p 0 

 
-- --  opaque
-- --   encodeℝpath : ∀ (p : (x : ℝ) → x ∈ intervalℙ 0 1 → Space distCircle)
-- --         (a b : distCircle) →
-- --        pt a ≡ p (rat [ pos 0 / 1+ 0 ]) (decℚ≤ᵣ? , decℚ≤ᵣ?) →
-- --        pt b ≡ p (rat [ pos 1 / 1+ 0 ]) (decℚ≤ᵣ? , decℚ≤ᵣ?) →
-- --        {!!}
-- --   encodeℝpath = {!!}

-- --   -- encodeℝsq :
-- --   --   ∀ (p : (x : ℝ) → x ∈ intervalℙ 0 1 → Space distCircle)
-- --   --     (a : distCircle)
-- --   --     (p' : (x : ℝ) → x ∈ intervalℙ 0 1 → distCircle) →
-- --   --     (x : pt a ≡ p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)) → 
-- --   --     PathP
-- --   --     (λ i →         
-- --   --        (path p' i ≡ p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)) → ℝ ≡ ℝ)
-- --   --     (encodeℝpath p a (p' 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)) x)
-- --   --     (encodeℝpath p a (p' 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)) x)
-- --   -- encodeℝsq p a p' x = {!!}

-- --  Encodeℝ : Spₙ distCircle 2 → {!!}
-- --  Encodeℝ = {!!}

-- --  decodeDSSq : ∀ c₀ c₁ →
-- --    (p p' : Path (Spₙ distCircle (suc zero)) (pt c₀) (pt c₁))
-- --    → 
-- --    Square {A = Spₙ distCircle (suc (suc zero))}
-- --     (cong pt p)
-- --     (cong pt p')
-- --     refl
-- --     refl
-- --     → decodeDSPath _ _ p ≡ decodeDSPath _ _ p'
-- --  decodeDSSq c₀ c₁ p = {!!}

-- -- --  opaque
-- -- --   short : (c : distCircle) →
-- -- --    ((x : ℝ) → x ∈ intervalℙ 0 1 → distCircle)
-- -- --   short = {!!}

-- -- --   short0 : ∀ c → circleBase ≡ short c 0 (decℚ≤ᵣ? , decℚ≤ᵣ?) 
-- -- --   short0 = {!!}

-- -- --   short1 : ∀ c → short c 1 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ c
-- -- --   short1 = {!!}

-- -- --  opaque
-- -- --   wind : ((x : ℝ) → x ∈ intervalℙ 0 1 → distCircle) → ℤ
-- -- --   wind = {!!}

-- -- --   wind-const : ∀ c → (wind λ _ _ → c) ≡ 0 
-- -- --   wind-const = {!!}

-- -- --   wind1 : wind (λ t _ → Circle→distCircle (injCircle t)) ≡ 1
-- -- --   wind1 = {!!}
-- -- --  opaque
 
-- -- --   S¹→distCircle : S¹ → Spₙ distCircle 1
-- -- --   S¹→distCircle base = pt circleBase
-- -- --   S¹→distCircle (loop i) = 
-- -- --    ((path λ t _ →
-- -- --       Circle→distCircle (injCircle t))
-- -- --         ∙ cong {y = circleBase} pt circleBase≡inj1) i

-- -- --   Sp₁distCircle : Spₙ distCircle 1 → S¹ 
-- -- --   Sp₁distCircle (pt _) = base
-- -- --   Sp₁distCircle (path p i) = intLoop (wind p) i
-- -- --   Sp₁distCircle (const≡refl a i j) = intLoop (wind-const a i) j
 
-- -- --   S¹→distCircle∘distCircle→S¹ : ∀ x → S¹→distCircle (Sp₁distCircle x) ≡ x
-- -- --   S¹→distCircle∘distCircle→S¹ (pt x) =
-- -- --    cong pt (short0 x) ∙∙ path (short x ) ∙∙ cong pt (short1 x)
-- -- --   S¹→distCircle∘distCircle→S¹ (path p i) j =
-- -- --     hcomp
-- -- --       (λ k →
-- -- --            λ {(j = i0) → {!!}
-- -- --              ;(j = i1) → {!!}
-- -- --                -- hcomp
-- -- --                --  (λ k' →
-- -- --                --    λ { (k = i0) → {!!}
-- -- --                --      ; (k = i1) → {!!}
-- -- --                --      ; (i = i0) → {!!}
-- -- --                --      ; (i = i1) → {!!}
-- -- --                --      })
-- -- --                --  {!!}

-- -- --  --
-- -- --              })
-- -- --       {!!}
-- -- --   S¹→distCircle∘distCircle→S¹ (const≡refl a i i₁) = {!!}

-- -- --   distCircle→S¹∘S¹→distCircle : ∀ x → (Sp₁distCircle (S¹→distCircle  x)) ≡ x
-- -- --   distCircle→S¹∘S¹→distCircle base _ = base
-- -- --   distCircle→S¹∘S¹→distCircle (loop i) j =
-- -- --       hcomp (λ k →
-- -- --                   λ { (j = i1) → compPath-filler' refl loop (~ k) i
-- -- --                     ; (i = i0) → base
-- -- --                     ; (i = i1) → base
-- -- --                     })
-- -- --                 (intLoop (wind1 j) i)


-- -- --   Sp₁-pa' : (p : (x : ℝ) →
-- -- --     x ∈ intervalℙ (rat [ pos 0 / 1+ 0 ]) (rat [ pos 1 / 1+ 0 ]) →
-- -- --     Space distCircle)
-- -- --      → singl (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))
-- -- --      → singl (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))
-- -- --      → Sp₁distCircle (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))
-- -- --       ≡ Sp₁distCircle (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))
-- -- --   Sp₁-pa' p = uncurry ∘ (uncurry (flip ∘ ElimSpaceSet₂.go w  ))
-- -- --    where
-- -- --    w : ElimSpaceSet₂ distCircle distCircle
-- -- --         (λ z z₁ →
-- -- --            (y : p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ z)
-- -- --            (y₁ : p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ z₁) →
-- -- --            Sp₁distCircle (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?)) ≡
-- -- --            Sp₁distCircle (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)))
-- -- --    w .ElimSpaceSet₂.pt-pt-f x y xP yP =
-- -- --      cong Sp₁distCircle xP ∙∙
-- -- --      cong Sp₁distCircle (path {!!})
-- -- --      ∙∙ cong Sp₁distCircle (sym yP)
-- -- --    w .ElimSpaceSet₂.pt-path-f a p' i xP yP j =
-- -- --      hcomp
-- -- --        (λ k →
-- -- --          λ {    (j = i0) → Sp₁distCircle (xP (~ k))  
-- -- --                ;(j = i1) → Sp₁distCircle (yP (~ k))
-- -- --            })
-- -- --        {!!}
-- -- --      where
-- -- --      zzzw : Sp₁distCircle (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)) ≡ intLoop (wind p') i
-- -- --      zzzw = cong Sp₁distCircle yP

-- -- --      zz : Path (Space (Space distCircle))
-- -- --             (path (λ _ _ → p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)) i) (pt (path p' i))
-- -- --      zz = flipSquare (const≡refl (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))) i  ∙ cong pt yP

     

-- -- --      -- hcomp
-- -- --      --     (doubleComp-faces (λ i₁ → Sp₁distCircle (y i₁))
-- -- --      --      (λ i₁ → {!!}) j)
-- -- --      --     base
-- -- --      -- ((λ i₁ → Sp₁distCircle (y i₁)) ∙∙ (λ _ → base) ∙∙
-- -- --      --     (λ i₁ → Sp₁distCircle (y₁ (~ i₁)))) j
-- -- --    w .ElimSpaceSet₂.path-pt-f p b = {!!}
-- -- --    w .ElimSpaceSet₂.isSetT _ _ = isSetΠ2 λ _ _ → isGroupoidS¹ _ _

-- -- --   Sp₁-pa : (p : (x : ℝ) →
-- -- --     x ∈ intervalℙ (rat [ pos 0 / 1+ 0 ]) (rat [ pos 1 / 1+ 0 ]) →
-- -- --     Space distCircle)
-- -- --      → Sp₁distCircle (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))
-- -- --       ≡ Sp₁distCircle (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))
-- -- --   Sp₁-pa p = Sp₁-pa' p (_ , refl) (_ , refl)


-- -- --   Sp₁-sq : (a : Space distCircle) →
-- -- --    Square {A = S¹}
-- -- --      (Sp₁-pa (λ _ _ → a))
-- -- --      refl
-- -- --      refl
-- -- --      refl
-- -- --   Sp₁-sq = ElimSpaceProp.go w
-- -- --    where
-- -- --    w : ElimSpaceProp distCircle
-- -- --         (λ z → Square (Sp₁-pa (λ _ _ → z)) refl refl refl)
-- -- --    w .ElimSpaceProp.pt-f x = {!!} --sym (doubleCompPath-filler refl refl refl)
-- -- --    w .ElimSpaceProp.isPropT _ = isOfHLevelPathP' 2 isGroupoidS¹ _ _ _ _


  
-- -- -- --  distCircle→S¹-Elim-f : ∀ k → (x : Spₙ distCircle k) → S¹
-- -- -- --  distCircle→S¹-Elim-push : ∀ k → (x : Spₙ distCircle k) →
-- -- -- --       distCircle→S¹-Elim-f k x ≡ distCircle→S¹-Elim-f (suc k) (pt x)
  


-- -- -- --  distCircle→S¹-Elim-f = ℕ.elim (λ _ → base)
-- -- -- --    (ℕ.elim (λ _ → Sp₁distCircle)
-- -- -- --      (ℕ.elim (λ _ _ → w') w))
-- -- -- --    where
   
-- -- -- --    w' : Spₙ distCircle 2 → S¹
-- -- -- --    w' (pt x₂) = Sp₁distCircle x₂
-- -- -- --    w' (path p i) = Sp₁-pa p i
-- -- -- --    w' (const≡refl a i i₁) = Sp₁-sq a i i₁
    
-- -- -- --    w : (n : ℕ) →
-- -- -- --         (((Spₙ distCircle n → S¹) → Spₙ distCircle (suc n) → S¹) →
-- -- -- --          (Spₙ distCircle (suc n) → S¹) →
-- -- -- --          Spₙ distCircle (suc (suc n)) → S¹) →
-- -- -- --         ((Spₙ distCircle (suc n) → S¹) →
-- -- -- --          Spₙ distCircle (suc (suc n)) → S¹) →
-- -- -- --         (Spₙ distCircle (suc (suc n)) → S¹) →
-- -- -- --         Spₙ distCircle (suc (suc (suc n))) → S¹
-- -- -- --    w f0 f1 f2 f3 (pt x) = (f3 x)
-- -- -- --    w f0 f1 f2 f3 (path p i) =
-- -- -- --       let zz : Path (Spₙ distCircle 2) _ _
-- -- -- --           zz = (path (λ t t∈ → 
-- -- -- --                     S¹→distCircle
-- -- -- --                      (f3 ((p t t∈)))))
          
-- -- -- --       in (hcomp (λ k →
-- -- -- --            λ {(i = i0) → distCircle→S¹∘S¹→distCircle
-- -- -- --                  (f3
-- -- -- --                   (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))) k
-- -- -- --              ;(i = i1) → distCircle→S¹∘S¹→distCircle
-- -- -- --                  (f3
-- -- -- --                   (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))) k
-- -- -- --              })
-- -- -- --          (w' (zz i)))   
-- -- -- --    w f0 f1 f2 f3 (const≡refl (pt x) i i₁) =
-- -- -- --      {!f3 (const≡refl x i i₁)!}
-- -- -- --    w f0 f1 f2 f3 (const≡refl (path p i₂) i i₁) = {!!}
-- -- -- --    w f0 f1 f2 f3 (const≡refl (const≡refl a i₂ i₃) i i₁) = {!!}
-- -- -- --  -- distCircle→S¹-Elim-f zero x = base
-- -- -- --  -- distCircle→S¹-Elim-f (suc zero) x = Sp₁distCircle x
-- -- -- --  -- distCircle→S¹-Elim-f (suc (suc zero)) (pt x) =
-- -- -- --  --   distCircle→S¹-Elim-f (suc zero) x
-- -- -- --  -- distCircle→S¹-Elim-f (suc (suc (suc n))) (pt x) = 
-- -- -- --  --   distCircle→S¹-Elim-f (suc (suc n)) x
-- -- -- --  -- distCircle→S¹-Elim-f (suc (suc zero)) (path p i) = {!!}
-- -- -- --  -- distCircle→S¹-Elim-f (suc (suc (suc n))) (path p i) = 
   
-- -- -- --  --   let zz : Path (Spₙ distCircle 2) _ _
-- -- -- --  --       zz = (path (λ t t∈ → 
-- -- -- --  --                 S¹→distCircle
-- -- -- --  --                  (distCircle→S¹-Elim-f (suc (suc n)) ((p t t∈)))))
-- -- -- --  --       zzz : Path S¹ _ _
-- -- -- --  --       zzz = cong (distCircle→S¹-Elim-f (suc (suc zero))) zz
-- -- -- --  --       zzzz = (hcomp (λ k →
-- -- -- --  --           λ {(i = i0) → distCircle→S¹∘S¹→distCircle
-- -- -- --  --                 (distCircle→S¹-Elim-f (suc (suc n))
-- -- -- --  --                  (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))) k
-- -- -- --  --             ;(i = i1) → distCircle→S¹∘S¹→distCircle
-- -- -- --  --                 (distCircle→S¹-Elim-f (suc (suc n))
-- -- -- --  --                  (p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?))) k
-- -- -- --  --             })
-- -- -- --  --         (zzz i))
-- -- -- --  --    in {!zzzz!}
-- -- -- --  -- distCircle→S¹-Elim-f (suc (suc zero)) (const≡refl a i i₁) = {!!}
-- -- -- --  -- distCircle→S¹-Elim-f (suc (suc (suc k))) (const≡refl a i i₁) = {!!}
 

-- -- -- --  distCircle→S¹-Elim-push zero x = {!!}
-- -- -- --  distCircle→S¹-Elim-push (suc zero) x = refl
-- -- -- --  distCircle→S¹-Elim-push (suc (suc zero)) x = refl
-- -- -- --  distCircle→S¹-Elim-push (suc (suc (suc k))) x = refl

-- -- -- --  distCircle→S¹-Elim : ElimData (Spₙ-seq distCircle) (λ _ → S¹)
-- -- -- --  distCircle→S¹-Elim .ElimData.inclP {k} = distCircle→S¹-Elim-f k
-- -- -- --  distCircle→S¹-Elim .ElimData.pushP {k} = distCircle→S¹-Elim-push k

-- -- -- --  distCircle→S¹ : Sp distCircle → S¹
-- -- -- --  distCircle→S¹ = Seq.elim (Spₙ-seq distCircle) (λ _ → S¹) distCircle→S¹-Elim
-- -- -- --  -- distCircle→S¹ (incl {zero} x) = base
-- -- -- --  -- distCircle→S¹ (incl {suc zero} x) = Sp₁distCircle x
-- -- -- --  -- -- distCircle→S¹ (incl {suc zero} (path p i)) = intLoop (wind' 0 p) i
-- -- -- --  -- distCircle→S¹ (incl {suc (suc n)} (pt x)) =
-- -- -- --  --   distCircle→S¹ (incl {n = suc n} x)
-- -- -- --  -- distCircle→S¹ (incl {suc (suc n)} (path p i)) = 
 
-- -- -- --  --   let zz : Path (Spₙ distCircle 2) _ _
-- -- -- --  --       zz = (path (λ t t∈ → 
-- -- -- --  --                 S¹→distCircle
-- -- -- --  --                  (distCircle→S¹ (incl {n = suc n} (p t t∈)))))
-- -- -- --  --       zzz : Path S¹ _ _
-- -- -- --  --       zzz j = {! ()!} 
-- -- -- --  --    in ({!zzz i!})
-- -- -- --  -- distCircle→S¹ (incl {suc (suc n)} (const≡refl a i i₁)) = {!!} 
-- -- -- --  -- --  -- -- ({!!} ∙∙ intLoop (wind' n p) ∙∙ {!!}) i
-- -- -- --  -- -- distCircle→S¹ (incl {suc n} (const≡refl a i i₁)) =
-- -- -- --  -- --   {!!}
-- -- -- --  -- distCircle→S¹ (push {zero} x i) = {!!}
-- -- -- --  -- distCircle→S¹ (push {suc zero} x i) = {!!}
-- -- -- --  -- distCircle→S¹ (push {suc (suc n)} x i) = {!!}



-- -- -- -- -- --  incl-path zero (pt x) =
-- -- -- -- -- --    {!!}
-- -- -- -- -- --    -- cong incl (cong pt (sym (𝐑'.0LeftAnnihilates _))
-- -- -- -- -- --    --   ∙∙ path (λ t _ →  (t ·ᵣ x)) ∙∙ cong pt (·IdL _)) 
-- -- -- -- -- --  incl-path zero (const≡refl a i j) k = {!!}
-- -- -- -- -- --  incl-path zero (path p i) j =
-- -- -- -- -- --     hcomp
-- -- -- -- -- --       (λ k →
-- -- -- -- -- --         λ { (j = i0) → push (pt (rat [ pos 0 / 1+ 0 ])) (~ k)
-- -- -- -- -- --           ; (j = i1) → push (path p i) (~ k)
-- -- -- -- -- --           -- ; (i = i0) → push {!!} (~ k)
-- -- -- -- -- --           -- ; (i = i1) → push {!!} (~ k)
-- -- -- -- -- --         } )
-- -- -- -- -- --       {!!}
-- -- -- -- -- --  -- incl
   
-- -- -- -- -- --  --   (hcomp
-- -- -- -- -- --  --    (λ k →
-- -- -- -- -- --  --      λ { (j = i0) → const≡refl (rat 0) k i
-- -- -- -- -- --  --        ; (j = i1) → path p i
-- -- -- -- -- --  --        })
-- -- -- -- -- --  --    (hcomp
-- -- -- -- -- --  --      (λ k →
-- -- -- -- -- --  --        λ { (j = i0) → {!push ?!}
-- -- -- -- -- --  --          ; (j = i1) → {!!}
-- -- -- -- -- --  --          ; (i = i0) → {!!}
-- -- -- -- -- --  --          ; (i = i1) → {!!}
-- -- -- -- -- --  --        } )
-- -- -- -- -- --  --      {!!}))
-- -- -- -- -- --  --   -- hcomp
-- -- -- -- -- --  --   --  (λ k →
-- -- -- -- -- --  --   --    λ { (i = i0) → ?
-- -- -- -- -- --  --   --      ; (i = i1) → ?
-- -- -- -- -- --  --   --      })
-- -- -- -- -- --  --   --  {!!}
-- -- -- -- -- --  --   -- {!cong (incl {n = zero}) (cong pt (sym (𝐑'.0LeftAnnihilates (p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?))))
-- -- -- -- -- --  --   --   ∙∙ path (λ t t∈ →  (t ·ᵣ p t t∈)) ∙∙
-- -- -- -- -- --  --   --     ?) j!}
 
-- -- -- -- -- --  incl-path (suc n) x = {!!}


-- -- -- -- -- --  isContrSpℝ .fst = incl {n = 0} (pt 0)
-- -- -- -- -- --  isContrSpℝ .snd (incl {n} x) = incl-path n x
-- -- -- -- -- --  isContrSpℝ .snd (push x i) = {!!}
-- -- -- -- -- --  -- isContrSpℝ .fst = incl 0
-- -- -- -- -- --  -- isContrSpℝ .snd (incl {zero} x) = {!!}
-- -- -- -- -- --  -- isContrSpℝ .snd (incl {n = suc n} (pt x)) =
-- -- -- -- -- --  --   isContrSpℝ .snd (incl {n = n} x) ∙ {!push!}
-- -- -- -- -- --  -- isContrSpℝ .snd (incl {suc n} (path p i₁)) i = {!!}
-- -- -- -- -- --  -- isContrSpℝ .snd (push x i) = {!!}


-- -- -- -- -- -- -- module Version2 where
-- -- -- -- -- -- --  data Space {ℓ} (A : Type ℓ) : Type ℓ where
-- -- -- -- -- -- --   pt : A → Space A
-- -- -- -- -- -- --   path : (p : ∀ x → x ∈ intervalℙ 0 1 → Space A)
-- -- -- -- -- -- --            → p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)



-- -- -- -- -- -- --  Spₙ : (A : Type ℓ) → ℕ → Type ℓ
-- -- -- -- -- -- --  Spₙ A zero = A
-- -- -- -- -- -- --  Spₙ A (suc x) = Spₙ (Space A) x


-- -- -- -- -- -- --  zzz : {A : Type ℓ} (f : ℝ → ℝ → A) →
-- -- -- -- -- -- --         Square {A = Spₙ A 1}
-- -- -- -- -- -- --            (path (λ jᵣ _ → pt (f 0 jᵣ)))
-- -- -- -- -- -- --            (path (λ jᵣ _ → pt (f 1 jᵣ)))
-- -- -- -- -- -- --            (path (λ iᵣ _ → pt (f iᵣ 0)))
-- -- -- -- -- -- --            (path (λ iᵣ _ → pt (f iᵣ 1)))
          
-- -- -- -- -- -- --  zzz f i j = path
-- -- -- -- -- -- --    (λ iᵣ _ →  path (λ jᵣ _ →
-- -- -- -- -- -- --      pt ((f iᵣ jᵣ))) j) i

-- -- -- -- -- -- --  pt↑ : (A : Type ℓ) → ∀ n → Spₙ A n →  Spₙ A (suc n)
-- -- -- -- -- -- --  pt↑ A zero = pt
-- -- -- -- -- -- --  pt↑ A (suc n) x = {!pt x!}
 
-- -- -- -- -- -- --  Spₙ-seq : (A : Type ℓ) → Sequence ℓ
-- -- -- -- -- -- --  Spₙ-seq A .Sequence.obj = Spₙ A
-- -- -- -- -- -- --  Spₙ-seq A .Sequence.map {zero} = pt
-- -- -- -- -- -- --  Spₙ-seq A .Sequence.map {suc n} = {!!}
 
-- -- -- -- -- -- --  Sp : (A : Type ℓ) → Type ℓ
-- -- -- -- -- -- --  Sp A = SeqColim (Spₙ-seq A)


-- -- -- -- -- -- -- module Version3 where
-- -- -- -- -- -- --  data Space {ℓ} (A : Type ℓ) : Type ℓ where
-- -- -- -- -- -- --   pt : A → Space A
-- -- -- -- -- -- --   path : (p : ∀ x → x ∈ intervalℙ 0 1 → Space A)
-- -- -- -- -- -- --            → p 0 (decℚ≤ᵣ? , decℚ≤ᵣ?) ≡ p 1 (decℚ≤ᵣ? , decℚ≤ᵣ?)



-- -- -- -- -- -- --  Spₙ : (A : Type ℓ) → ℕ → Type ℓ
-- -- -- -- -- -- --  Spₙ A zero = Space A
-- -- -- -- -- -- --  Spₙ A (suc x) = Space (Spₙ A x)


-- -- -- -- -- -- --  zzz : {A : Type ℓ} (f : ℝ → ℝ → A) →
-- -- -- -- -- -- --         Square {A = Spₙ A 1}
-- -- -- -- -- -- --            (path (λ jᵣ _ → pt (pt (f 0 jᵣ))))
-- -- -- -- -- -- --            (path (λ jᵣ _ → pt (pt (f 1 jᵣ))))
-- -- -- -- -- -- --            (path (λ iᵣ _ → pt (pt (f iᵣ 0))))
-- -- -- -- -- -- --            (path (λ iᵣ _ → pt (pt (f iᵣ 1))))
          
-- -- -- -- -- -- --  zzz f i j = path
-- -- -- -- -- -- --    (λ iᵣ _ →  path (λ jᵣ _ →
-- -- -- -- -- -- --      pt (pt (f iᵣ jᵣ))) j) i
 
-- -- -- -- -- -- --  Spₙ-seq : (A : Type ℓ) → Sequence ℓ
-- -- -- -- -- -- --  Spₙ-seq A .Sequence.obj = Spₙ A
-- -- -- -- -- -- --  Spₙ-seq A .Sequence.map = pt
 
-- -- -- -- -- -- --  Sp : (A : Type ℓ) → Type ℓ
-- -- -- -- -- -- --  Sp A = SeqColim (Spₙ-seq A)


-- -- -- -- -- -- --  pathTo0inℝ : (x : ℝ) → {!!}
-- -- -- -- -- -- --  pathTo0inℝ = {!!}

-- -- -- -- -- -- --  incl-path : ∀ n x → Path (Sp ℝ) (incl {n = 0} (pt 0)) (incl {n = n} x) 
-- -- -- -- -- -- --  incl-path zero (pt x) = cong incl ({!!}
-- -- -- -- -- -- --    ∙∙ path (λ t _ → pt (t ·ᵣ x)) ∙∙ {!!})
-- -- -- -- -- -- --  incl-path zero (path p i) = {!incl ?!}
-- -- -- -- -- -- --    -- cong incl ({!!} ∙∙ path (λ t _ → pt ({!t ·ᵣ x!})) ∙∙ {!!})
-- -- -- -- -- -- --  incl-path (suc n) x = {!!}
 
-- -- -- -- -- -- --  isContrSpℝ : isContr (Sp ℝ)
-- -- -- -- -- -- --  isContrSpℝ .fst = incl {n = 0} (pt 0)
-- -- -- -- -- -- --  isContrSpℝ .snd (incl {n} x) = incl-path n x
-- -- -- -- -- -- --  isContrSpℝ .snd (push x i) = {!!}
-- -- -- -- -- -- --  -- isContrSpℝ .fst = incl 0
-- -- -- -- -- -- --  -- isContrSpℝ .snd (incl {zero} x) = {!!}
-- -- -- -- -- -- --  -- isContrSpℝ .snd (incl {n = suc n} (pt x)) =
-- -- -- -- -- -- --  --   isContrSpℝ .snd (incl {n = n} x) ∙ {!push!}
-- -- -- -- -- -- --  -- isContrSpℝ .snd (incl {suc n} (path p i₁)) i = {!!}
-- -- -- -- -- -- --  -- isContrSpℝ .snd (push x i) = {!!}


-- -- -- -- -- -- --  -- -- sqT : (f : ℝ → ℝ → ℝ) →
-- -- -- -- -- -- --  -- --    Square {A = Space ℝ }
-- -- -- -- -- -- --  -- --         {!!}
-- -- -- -- -- -- --  -- --         {!!}
-- -- -- -- -- -- --  -- --         {!!}
-- -- -- -- -- -- --  -- --         {!!} 
-- -- -- -- -- -- --  -- -- sqT i j = {!path (λ jᵣ _ → ?) j!}
 
-- -- -- -- -- -- --  -- -- -- zzzz : {A : Type ℓ} (f : ℝ → ℝ → ℝ → A) →
-- -- -- -- -- -- --  -- -- --        Cube {A = Sp A 2}
-- -- -- -- -- -- --  -- -- --           (λ j →
-- -- -- -- -- -- --  -- -- --             path (λ kᵣ _ →  path (λ jᵣ _ → pt (pt (pt (f 0 jᵣ kᵣ)))) j))
-- -- -- -- -- -- --  -- -- --           {!!}
-- -- -- -- -- -- --  -- -- --           -- (λ j k → path (λ jᵣ _ →
-- -- -- -- -- -- --  -- -- --           --       path (λ kᵣ _ →
-- -- -- -- -- -- --  -- -- --           --       pt (pt (pt (f 0 jᵣ kᵣ)))) k) j)
-- -- -- -- -- -- --  -- -- --           -- (λ j k → path (λ jᵣ _ →
-- -- -- -- -- -- --  -- -- --           --       path (λ kᵣ _ →
-- -- -- -- -- -- --  -- -- --           --       pt (pt (pt (f 1 jᵣ kᵣ)))) k) j)
-- -- -- -- -- -- --  -- -- --           {!!}
-- -- -- -- -- -- --  -- -- --           {!!}
-- -- -- -- -- -- --  -- -- --           {!!}
-- -- -- -- -- -- --  -- -- --           {!!}
           
          
-- -- -- -- -- -- --  -- -- -- zzzz f i j k = path
-- -- -- -- -- -- --  -- -- --   (λ kᵣ _ →  path (λ jᵣ _ →
-- -- -- -- -- -- --  -- -- --     path (λ iᵣ _ →
-- -- -- -- -- -- --  -- -- --     pt (pt (pt (f iᵣ jᵣ kᵣ)))) i) j) k


