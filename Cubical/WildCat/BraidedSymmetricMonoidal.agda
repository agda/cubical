{-
  Monoidal, braided and monoidal symmetric wild categories
-}
{-# OPTIONS --safe #-}
module Cubical.WildCat.BraidedSymmetricMonoidal where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma renaming (_×_ to _×'_)

open import Cubical.WildCat.Base
open import Cubical.WildCat.Product
open import Cubical.WildCat.Functor

private
  variable
    ℓ ℓ' : Level

open WildCat

open WildFunctor
open WildNatTrans
open WildNatIso
open wildIsIso

module _ (M : WildCat ℓ ℓ') where
  record isMonoidalWildCat : Type (ℓ-max ℓ ℓ') where
    field
      _⊗_ : WildFunctor (M × M) M
      𝟙 : ob M

      ⊗assoc : WildNatIso (M × (M × M)) M (assocₗ _⊗_) (assocᵣ _⊗_)

      ⊗lUnit : WildNatIso M M (restrFunctorₗ _⊗_ 𝟙) (idWildFunctor M)
      ⊗rUnit : WildNatIso M M (restrFunctorᵣ _⊗_ 𝟙) (idWildFunctor M)

    private
      α = N-ob (trans ⊗assoc)
      α⁻ : (c : ob M ×' ob M ×' ob M) → M [ _ , _ ]
      α⁻ c = wildIsIso.inv' (isIs ⊗assoc c)
      rId = N-ob (trans ⊗rUnit)
      lId = N-ob (trans ⊗lUnit)

    field
      -- Note: associators are on the form x ⊗ (y ⊗ z) → (x ⊗ y) ⊗ z
      triang : (a b : M .ob)
        → α (a , 𝟙 , b) ⋆⟨ M ⟩ (F-hom _⊗_ ((rId a) , id M))
          ≡ F-hom _⊗_ ((id M) , lId b)

      ⊗pentagon : (a b c d : M .ob)
        → (F-hom _⊗_ (id M , α (b , c , d)))
           ⋆⟨ M ⟩ ((α (a , (_⊗_ .F-ob (b , c)) , d))
           ⋆⟨ M ⟩ (F-hom _⊗_ (α (a , b , c) , id M)))
        ≡  (α (a , b , (F-ob _⊗_ (c , d))))
           ⋆⟨ M ⟩ (α((F-ob _⊗_ (a , b)) , c , d))

  module _ (mon : isMonoidalWildCat) where
    open isMonoidalWildCat mon
    private
      α = N-ob (trans ⊗assoc)
      α⁻ : (c : ob M ×' ob M ×' ob M) → M [ _ , _ ]
      α⁻ c = wildIsIso.inv' (isIs ⊗assoc c)

    BraidingIsoType : Type _
    BraidingIsoType = WildNatIso (M × M) M _⊗_ (comp-WildFunctor commFunctor _⊗_)

    HexagonType₁ : (B : BraidingIsoType) → Type _
    HexagonType₁ B = (x y z : M .ob) →
      F-hom _⊗_ ((id M) , N-ob (trans B) (y , z))
        ⋆⟨ M ⟩ α (x , z , y)
        ⋆⟨ M ⟩ F-hom _⊗_ (N-ob (trans B) (x , z) , (id M))
       ≡ α (x , y , z)
        ⋆⟨ M ⟩ N-ob (trans B) ((F-ob _⊗_ (x , y)) , z)
        ⋆⟨ M ⟩ α (z , x , y)

    HexagonType₂ : (B : BraidingIsoType) → Type _
    HexagonType₂ B = (x y z : M .ob) →
      F-hom _⊗_ (N-ob (trans B) (x , y) , id M)
        ⋆⟨ M ⟩ α⁻ (y , x , z)
        ⋆⟨ M ⟩ F-hom _⊗_ ((id M) , N-ob (trans B) (x , z))
       ≡ α⁻ (x , y , z)
        ⋆⟨ M ⟩ N-ob (trans B) (x , F-ob _⊗_ (y , z))
        ⋆⟨ M ⟩ α⁻ (y , z , x)

    isSymmetricBraiding : (B : BraidingIsoType)
      → Type _
    isSymmetricBraiding B = (x y : M .ob) →
      N-ob (trans B) (x , y) ⋆⟨ M ⟩ (N-ob (trans B) (y , x))
      ≡ id M

  record isBraidedWildCat : Type (ℓ-max ℓ ℓ') where
    open isMonoidalWildCat
    field
      isMonoidal : isMonoidalWildCat
      Braid : BraidingIsoType isMonoidal
      hexagons : (x y z : M .ob)
        → HexagonType₁ isMonoidal Braid
        ×' HexagonType₂ isMonoidal Braid

  record isSymmetricWildCat : Type (ℓ-max ℓ ℓ') where
    field
      isMonoidal : isMonoidalWildCat
      Braid : BraidingIsoType isMonoidal
      hexagon : HexagonType₁ isMonoidal Braid
      symBraiding : isSymmetricBraiding isMonoidal Braid

SymmetricMonoidalPrecat : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
SymmetricMonoidalPrecat ℓ ℓ' =
  Σ[ C ∈ WildCat ℓ ℓ' ] isSymmetricWildCat C
