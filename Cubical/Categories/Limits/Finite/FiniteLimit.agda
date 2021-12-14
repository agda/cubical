{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.Finite.FiniteLimit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat hiding (znots ; snotz)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.FinData
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Instances.DistLattice
open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.DistLattice.BigOps

open import Cubical.Categories.Limits.Base
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Finite.FiniteSystem

open import Cubical.Relation.Binary.Poset

private
  variable
    ℓ ℓ' ℓ'' : Level


FinDiagram : (C : Category ℓ ℓ') (n : ℕ) → Type _
FinDiagram C n = Functor (FinSysCat n) C

-- do we need this?
-- isFinLimit : {C : Category ℓ ℓ'} {n : ℕ} → FinDiagram C n → C .Category.ob → Type _
-- isFinLimit diag head = isLimit diag head

-- FinLimit : {C : Category ℓ ℓ'} {n : ℕ} → FinDiagram C n → Type _
-- FinLimit diag = Limit diag


-- In distributive lattices finite limits are joins
module _ (L' : DistLattice ℓ) where
 private
  L = fst L'
  LCat = (DistLatticeCategory L') ^op

 open DistLatticeStr (snd L')
 open Join L'
 open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L'))
 open PosetStr (IndPoset .snd) hiding (_≤_)
 open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L'))
      using (∧≤RCancel ; ∧≤LCancel)
 open Order (DistLattice→Lattice L')

 open Category LCat
 open Functor

 FinVec→FinDiagram : {n : ℕ} → FinVec L n → FinDiagram LCat n
 F-ob (FinVec→FinDiagram α) (sing i) = α i
 F-ob (FinVec→FinDiagram α) (pair i j) = α i ∧l α j
 F-hom (FinVec→FinDiagram α) {x = sing i} {y = sing j} p =
       subst (λ k → Hom[ α i , α k ]) p id
 F-hom (FinVec→FinDiagram α) {x = sing i} {y = pair j k} (inl p) =
       subst (λ l → Hom[ α i , α l ∧l α k ]) p (≤m→≤j _ _ (∧≤RCancel _ _))
 F-hom (FinVec→FinDiagram α) {x = sing i} {y = pair j k} (inr p) =
       subst (λ l → Hom[ α i , α j ∧l α l ]) p (≤m→≤j _ _ (∧≤LCancel _ _))
 F-hom (FinVec→FinDiagram α) {x = pair i j} {y = pair k l} (p , q) =
       subst2 (λ m o → Hom[ α i ∧l α j , α m ∧l α o ]) p q id
 F-id (FinVec→FinDiagram α) = is-prop-valued _ _ _ _
 F-seq (FinVec→FinDiagram α) _ _ = is-prop-valued _ _ _ _


 open NatTrans

 joinIsFinLim : {n : ℕ} (α : FinVec L n) → isLimit (FinVec→FinDiagram α) (⋁ α)
 joinIsFinLim α = islimit joinCone joinUp
  where
  joinCone : Cone (FinVec→FinDiagram α) (⋁ α)
  N-ob joinCone (sing i) = ind≤⋁ α i -- αᵢ≤⋁α
  N-ob joinCone (pair i j) = is-trans _ (α i) _ (≤m→≤j _ _ (∧≤RCancel _ _)) (ind≤⋁ α i) -- αᵢ∧αⱼ≤⋁α
  N-hom joinCone _ = is-prop-valued _ _ _ _

  joinUp : {v : ob} (ν : Cone (FinVec→FinDiagram α) v) → joinCone uniquelyFactors ν
  joinUp {v = v} ν = (f , fFactors) , uniqueness
   where
   f : LCat [ v , (⋁ α) ] -- ⋁α≤v
   f = ⋁IsMax α _ (λ i → ν .N-ob (sing i))

   fFactors : ν ≡ (f ◼ joinCone) --precomposition
   fFactors = makeNatTransPath (funExt (λ _ → is-prop-valued _ _ _ _))

   uniqueness : (y : joinCone factors ν) → (f , fFactors) ≡ y
   uniqueness _ = Σ≡Prop (λ _ → isSetNat _ _) (is-prop-valued _ _ _ _)



-- Pullbacks are (finite) limits
module _ {C : Category ℓ ℓ'} (cspan : Cospan {C = C}) where
 open Category C
 open Functor
 open Cospan ⦃...⦄
 private
  instance
   _ = cspan

 FinSys2→Cospan : Functor (FinSysCat 2) CospanCat
 F-ob FinSys2→Cospan (sing zero) = ⓪
 F-ob FinSys2→Cospan (sing (suc zero)) = ②
 F-ob FinSys2→Cospan (pair zero zero) = ⓪
 F-ob FinSys2→Cospan (pair zero (suc zero)) = ①
 F-ob FinSys2→Cospan (pair (suc zero) zero) = ①
 F-ob FinSys2→Cospan (pair (suc zero) (suc zero)) = ②

 F-hom FinSys2→Cospan {sing zero} {sing zero} _ = tt
 F-hom FinSys2→Cospan {sing zero} {sing (suc zero)} = znots
 F-hom FinSys2→Cospan {sing (suc zero)} {sing zero} = snotz
 F-hom FinSys2→Cospan {sing (suc zero)} {sing (suc zero)} _ = tt

 F-hom FinSys2→Cospan {sing zero} {pair zero zero} _ = tt
 F-hom FinSys2→Cospan {sing zero} {pair zero (suc zero)} _ = tt
 F-hom FinSys2→Cospan {sing zero} {pair (suc zero) zero} _ = tt
 F-hom FinSys2→Cospan {sing zero} {pair (suc zero) (suc zero)} (inl x) = znots x
 F-hom FinSys2→Cospan {sing zero} {pair (suc zero) (suc zero)} (inr x) = znots x

 F-hom FinSys2→Cospan {sing (suc zero)} {pair zero zero} (inl x) = snotz x
 F-hom FinSys2→Cospan {sing (suc zero)} {pair zero zero} (inr x) = snotz x
 F-hom FinSys2→Cospan {sing (suc zero)} {pair zero (suc zero)} _ = tt
 F-hom FinSys2→Cospan {sing (suc zero)} {pair (suc zero) zero} _ = tt
 F-hom FinSys2→Cospan {sing (suc zero)} {pair (suc zero) (suc zero)} _ = tt

 F-hom FinSys2→Cospan {pair _ _} {sing _} = ⊥.rec

 F-hom FinSys2→Cospan {pair zero zero} {pair zero zero} _ = tt
 F-hom FinSys2→Cospan {pair zero _} {pair (suc zero) _} (p , _) = ⊥.rec (znots p)
 F-hom FinSys2→Cospan {pair (suc zero) _} {pair zero _} (p , _) = ⊥.rec (snotz p)
 F-hom FinSys2→Cospan {pair zero (suc zero)} {pair zero (suc zero)} _ = tt
 F-hom FinSys2→Cospan {pair (suc zero) zero} {pair (suc zero) zero} _ = tt
 F-hom FinSys2→Cospan {pair _ zero} {pair _ (suc zero)} (_ , p) = ⊥.rec (znots p)
 F-hom FinSys2→Cospan {pair _ (suc zero)} {pair _ zero} (_ , p) = ⊥.rec (snotz p)
 F-hom FinSys2→Cospan {pair (suc zero) (suc zero)} {pair (suc zero) (suc zero)} _ = tt

 F-id FinSys2→Cospan {sing zero} = refl
 F-id FinSys2→Cospan {sing (suc zero)} = refl
 F-id FinSys2→Cospan {pair zero zero} = refl
 F-id FinSys2→Cospan {pair zero (suc zero)} = refl
 F-id FinSys2→Cospan {pair (suc zero) zero} = refl
 F-id FinSys2→Cospan {pair (suc zero) (suc zero)} = refl

 F-seq FinSys2→Cospan {x = x} {z = z} _ _ = isPropHomCospanCat (F-ob FinSys2→Cospan x) (F-ob FinSys2→Cospan z) _ _



 Cospan→FinDiagram : FinDiagram C 2
 Cospan→FinDiagram = funcComp (Cospan→Func cspan) FinSys2→Cospan

 -- going directly is a real pain...
 -- F-ob Cospan→FinDiagram (sing zero) = l
 -- F-ob Cospan→FinDiagram (sing (suc zero)) = r
 -- F-ob Cospan→FinDiagram (pair zero zero) = l
 -- F-ob Cospan→FinDiagram (pair zero (suc zero)) = m
 -- F-ob Cospan→FinDiagram (pair (suc zero) zero) = m
 -- F-ob Cospan→FinDiagram (pair (suc zero) (suc zero)) = r

 -- F-hom Cospan→FinDiagram {x = sing zero} {y = sing zero} _ = id
 -- F-hom Cospan→FinDiagram {x = sing zero} {y = sing (suc zero)} p = ⊥.rec (znots p)
 -- F-hom Cospan→FinDiagram {x = sing (suc zero)} {y = sing zero} p = ⊥.rec (snotz p)
 -- F-hom Cospan→FinDiagram {x = sing (suc zero)} {y = sing (suc zero)} _ = id

 -- F-hom Cospan→FinDiagram {x = sing zero} {y = pair zero zero} _ = id
 -- F-hom Cospan→FinDiagram {x = sing zero} {y = pair zero (suc zero)} _ = s₁
 -- F-hom Cospan→FinDiagram {x = sing zero} {y = pair (suc zero) zero} _ = s₁
 -- F-hom Cospan→FinDiagram {x = sing zero} {y = pair (suc zero) (suc zero)} (inl x) = ⊥.rec (znots x)
 -- F-hom Cospan→FinDiagram {x = sing zero} {y = pair (suc zero) (suc zero)} (inr x) = ⊥.rec (znots x)
 -- F-hom Cospan→FinDiagram {x = sing (suc zero)} {y = pair zero zero} (inl x) = ⊥.rec (snotz x)
 -- F-hom Cospan→FinDiagram {x = sing (suc zero)} {y = pair zero zero} (inr x) = ⊥.rec (snotz x)
 -- F-hom Cospan→FinDiagram {x = sing (suc zero)} {y = pair zero (suc zero)} _ = s₂
 -- F-hom Cospan→FinDiagram {x = sing (suc zero)} {y = pair (suc zero) zero} _ = s₂
 -- F-hom Cospan→FinDiagram {x = sing (suc zero)} {y = pair (suc zero) (suc zero)} _ = id

 -- F-hom Cospan→FinDiagram {x = pair zero zero} {y = pair zero zero} _ = id
 -- F-hom Cospan→FinDiagram {x = pair zero zero} {y = pair zero (suc zero)} (_ , q) = ⊥.rec (znots q)
 -- F-hom Cospan→FinDiagram {x = pair zero zero} {y = pair (suc zero) _} (p , _) = ⊥.rec (znots p)
 -- F-hom Cospan→FinDiagram {x = pair zero (suc zero)} {y = pair zero zero} (_ , q) = ⊥.rec (snotz q)
 -- F-hom Cospan→FinDiagram {x = pair zero (suc zero)} {y = pair zero (suc zero)} _ = id
 -- F-hom Cospan→FinDiagram {x = pair zero (suc zero)} {y = pair (suc zero) _} (p , _) = ⊥.rec (znots p)
 -- F-hom Cospan→FinDiagram {x = pair (suc zero) zero} {y = pair zero _} (p , _) = ⊥.rec (snotz p)
 -- F-hom Cospan→FinDiagram {x = pair (suc zero) zero} {y = pair (suc zero) zero} _ = id
 -- F-hom Cospan→FinDiagram {x = pair (suc zero) zero} {y = pair (suc zero) (suc zero)} (_ , q) =
 --                                                                                      ⊥.rec (znots q)
 -- F-hom Cospan→FinDiagram {x = pair (suc zero) (suc zero)} {y = pair zero _} (p , _) = ⊥.rec (snotz p)
 -- F-hom Cospan→FinDiagram {x = pair (suc zero) (suc zero)} {y = pair (suc zero) zero} (_ , q) =
 --                                                                                      ⊥.rec (snotz q)
 -- F-hom Cospan→FinDiagram {x = pair (suc zero) (suc zero)} {y = pair (suc zero) (suc zero)} _ = id

 -- F-id Cospan→FinDiagram {x = sing zero} = refl
 -- F-id Cospan→FinDiagram {x = sing (suc zero)} = refl
 -- F-id Cospan→FinDiagram {x = pair zero zero} = refl
 -- F-id Cospan→FinDiagram {x = pair zero (suc zero)} = refl
 -- F-id Cospan→FinDiagram {x = pair (suc zero) zero} = refl
 -- F-id Cospan→FinDiagram {x = pair (suc zero) (suc zero)} = refl

 -- F-seq Cospan→FinDiagram {sing zero} {sing zero} {sing zero} _ _ = sym (⋆IdL _)
 -- F-seq Cospan→FinDiagram {sing zero} {sing zero} {sing (suc zero)} _ g = ⊥.rec (znots g)
 -- F-seq Cospan→FinDiagram {sing zero} {sing zero} {pair zero zero} _ _ = sym (⋆IdL _)
 -- F-seq Cospan→FinDiagram {sing zero} {sing zero} {pair zero (suc zero)} _ _ = sym (⋆IdL _)
 -- F-seq Cospan→FinDiagram {sing zero} {sing zero} {pair (suc zero) zero} _ _ = sym (⋆IdL _)
 -- F-seq Cospan→FinDiagram {sing zero} {sing zero} {pair (suc zero) (suc zero)} _ (inl x) =
 --                                                                              ⊥.rec (znots x)
 -- F-seq Cospan→FinDiagram {sing zero} {sing zero} {pair (suc zero) (suc zero)} _ (inr x) =
 --                                                                              ⊥.rec (znots x)
 -- F-seq Cospan→FinDiagram {sing zero} {sing (suc zero)} {z} f _ = ⊥.rec (znots f)
 -- F-seq Cospan→FinDiagram {sing zero} {pair _ _} {sing _} _ g = ⊥.rec g
 -- F-seq Cospan→FinDiagram {sing zero} {pair x x₁} {pair x₂ x₃} (inl x₄) (fst₁ , snd₁) = {!!}
 -- F-seq Cospan→FinDiagram {sing zero} {pair x x₁} {pair x₂ x₃} (inr x₄) g = {!!}
 -- F-seq Cospan→FinDiagram {sing (suc zero)} {sing zero} {z} f _ = ⊥.rec (snotz f)
 -- F-seq Cospan→FinDiagram {sing (suc zero)} {sing (suc zero)} {z} f g = {!!}
 -- F-seq Cospan→FinDiagram {sing (suc zero)} {pair x x₁} {sing x₂} = {!!}
 -- F-seq Cospan→FinDiagram {sing (suc zero)} {pair x x₁} {pair x₂ x₃} = {!!}
 -- F-seq Cospan→FinDiagram {pair x x₁} {sing x₂} {z} = {!!}
 -- F-seq Cospan→FinDiagram {pair x x₁} {pair x₂ x₃} {z} = {!!}
