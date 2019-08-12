{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Graph.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
open import Cubical.Relation.Nullary

open import Cubical.Data.Sum
open import Cubical.Data.Prod

open import Cubical.Data.Graph.Base


-- The graph ω = 0 → 1 → 2 → ···

data Adj : ℕ → ℕ → Type₀ where
  adj : ∀ n → Adj n (suc n)

areAdj : ∀ m n → Dec (Adj m n)
areAdj zero zero          = no λ ()
areAdj zero (suc zero)    = yes (adj zero)
areAdj zero (suc (suc n)) = no λ ()
areAdj (suc m) zero       = no λ ()
areAdj (suc m) (suc n)    = mapDec (λ { (adj .m) → adj (suc m) })
                                   (λ { ¬a (adj .(suc m)) → ¬a (adj m) })
                                   (areAdj m n)

ωGr : Graph ℓ-zero ℓ-zero
Obj ωGr = ℕ
Hom ωGr m n with areAdj m n
... | yes _ = ⊤ -- if n ≡ (suc m)
... | no  _ = ⊥ -- otherwise

record ωDiag ℓ : Type (ℓ-suc ℓ) where
  field
    ωObj : ℕ → Type ℓ
    ωHom : ∀ n → ωObj n → ωObj (suc n)

  asDiag : Diag ℓ ωGr
  asDiag $ n = ωObj n
  _<$>_ asDiag {m} {n} f with areAdj m n
  asDiag <$> tt | yes (adj m) = ωHom m


-- Disjoint union of graphs

module _ {ℓv ℓe ℓv' ℓe'} where

  _⊎Gr_ : ∀ (G : Graph ℓv ℓe) (G' : Graph ℓv' ℓe') → Graph (ℓ-max ℓv ℓv') (ℓ-max ℓe ℓe')
  Obj (G ⊎Gr G') = Obj G ⊎ Obj G'
  Hom (G ⊎Gr G') (inl x) (inl y) = Lift {j = ℓe'} (Hom G x y)
  Hom (G ⊎Gr G') (inr x) (inr y) = Lift {j = ℓe } (Hom G' x y)
  Hom (G ⊎Gr G') _ _ = Lift ⊥

  record ⊎Diag ℓ (G : Graph ℓv ℓe) (G' : Graph ℓv' ℓe')
               : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-max ℓv ℓv') (ℓ-max ℓe ℓe'))) where
    field
      ⊎Obj : Obj G ⊎ Obj G' → Type ℓ
      ⊎Homl : ∀ {x y} → Hom G  x y → ⊎Obj (inl x) → ⊎Obj (inl y)
      ⊎Homr : ∀ {x y} → Hom G' x y → ⊎Obj (inr x) → ⊎Obj (inr y)

    asDiag : Diag ℓ (G ⊎Gr G')
    asDiag $ x = ⊎Obj x
    _<$>_ asDiag {inl x} {inl y} f = ⊎Homl (lower f)
    _<$>_ asDiag {inr x} {inr y} f = ⊎Homr (lower f)


-- Cartesian product of graphs

module _ {ℓv ℓe ℓv' ℓe'} where

  -- We need decidable equality in order to define the cartesian product
  DecGraph : ∀ ℓv ℓe → Type (ℓ-suc (ℓ-max ℓv ℓe))
  DecGraph ℓv ℓe = Σ[ G ∈ Graph ℓv ℓe ] Discrete (Obj G)

  _×Gr_ : (G : DecGraph ℓv ℓe) (G' : DecGraph ℓv' ℓe') → Graph (ℓ-max ℓv ℓv') (ℓ-max ℓe ℓe')
  Obj (G ×Gr G') = Obj (fst G) × Obj (fst G')
  Hom (G ×Gr G') (x , x') (y , y') with snd G x y | snd G' x' y'
  ... | yes _ | yes _ = Hom (fst G) x y ⊎ Hom (fst G') x' y'
  ... | yes _ | no  _ = Lift {j = ℓe } (Hom (fst G') x' y')
  ... | no  _ | yes _ = Lift {j = ℓe'} (Hom (fst G) x y)
  ... | no  _ | no  _ = Lift ⊥

  record ×Diag ℓ (G : DecGraph ℓv ℓe) (G' : DecGraph ℓv' ℓe')
               : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-max ℓv ℓv') (ℓ-max ℓe ℓe'))) where
    field
      ×Obj : Obj (fst G) × Obj (fst G') → Type ℓ
      ×Hom₁ : ∀ {x y} (f : Hom (fst G) x y) (x' : Obj (fst G'))    → ×Obj (x , x') → ×Obj (y , x')
      ×Hom₂ : ∀ (x : Obj (fst G)) {x' y'} (f : Hom (fst G') x' y') → ×Obj (x , x') → ×Obj (x , y')

    asDiag : Diag ℓ (G ×Gr G')
    asDiag $ x = ×Obj x
    _<$>_ asDiag {x , x'} {y , y'} f with snd G x y | snd G' x' y'
    _<$>_ asDiag {x , x'} {y , y'} (inl f) | yes _ | yes p' = subst _ p' (×Hom₁ f x')
    _<$>_ asDiag {x , x'} {y , y'} (inr f) | yes p | yes _  = subst _ p  (×Hom₂ x f )
    _<$>_ asDiag {x , x'} {y , y'} f | yes p | no  _  = subst _ p  (×Hom₂ x (lower f) )
    _<$>_ asDiag {x , x'} {y , y'} f | no  _ | yes p' = subst _ p' (×Hom₁ (lower f) x')

