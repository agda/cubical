{-# OPTIONS --safe #-}
module Cubical.Categories.Category.Precategory where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma renaming (_×_ to _×'_)

open import Cubical.Foundations.Pointed hiding (⋆ ; id)

private
  variable
    ℓ ℓ' : Level

-- Precategories
record Precategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  -- no-eta-equality ; NOTE: need eta equality for `opop`
  field
    ob : Type ℓ
    Hom[_,_] : ob → ob → Type ℓ'
    id   : ∀ {x} → Hom[ x , x ]
    _⋆_  : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ]) → Hom[ x , z ]
    ⋆IdL : ∀ {x y} (f : Hom[ x , y ]) → id ⋆ f ≡ f
    ⋆IdR : ∀ {x y} (f : Hom[ x , y ]) → f ⋆ id ≡ f
    ⋆Assoc : ∀ {u v w x} (f : Hom[ u , v ]) (g : Hom[ v , w ]) (h : Hom[ w , x ])
      → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)

  -- composition: alternative to diagramatic order
  _∘_ : ∀ {x y z} (g : Hom[ y , z ]) (f : Hom[ x , y ]) → Hom[ x , z ]
  g ∘ f = f ⋆ g

open Precategory

-- Helpful syntax/notation
_[_,_] : (C : Precategory ℓ ℓ') → (x y : C .ob) → Type ℓ'
_[_,_] = Hom[_,_]

-- Needed to define this in order to be able to make the subsequence syntax declaration
seq' : ∀ (C : Precategory ℓ ℓ') {x y z} (f : C [ x , y ]) (g : C [ y , z ]) → C [ x , z ]
seq' = _⋆_

infixl 15 seq'
syntax seq' C f g = f ⋆⟨ C ⟩ g

-- composition
comp' : ∀ (C : Precategory ℓ ℓ') {x y z} (g : C [ y , z ]) (f : C [ x , y ]) → C [ x , z ]
comp' = _∘_

infixr 16 comp'
syntax comp' C g f = g ∘⟨ C ⟩ f

-- Isomorphisms and paths in precategories
record PrecatIso (C : Precategory ℓ ℓ') (x y : C .ob) : Type ℓ' where
  constructor precatiso
  field
    mor : C [ x , y ]
    inv : C [ y , x ]
    sec : inv ⋆⟨ C ⟩ mor ≡ C .id
    ret : mor ⋆⟨ C ⟩ inv ≡ C .id

-- Opposite precategory
_^op : Precategory ℓ ℓ' → Precategory ℓ ℓ'
(C ^op) .ob = C .ob
(C ^op) .Hom[_,_] x y = C .Hom[_,_] y x
(C ^op) .id = C .id
(C ^op) ._⋆_ f g = C ._⋆_ g f
(C ^op) .⋆IdL = C .⋆IdR
(C ^op) .⋆IdR = C .⋆IdL
(C ^op) .⋆Assoc f g h = sym (C .⋆Assoc _ _ _)

-- Natural isomorphisms
module _ {ℓC ℓC' : Level} {C : Precategory ℓC ℓC'}
  {x y : C .ob} (f : Hom[_,_] C x y) where
  record preIsIso : Type (ℓ-max ℓC ℓC') where
    field
      inv' : Hom[_,_] C y x
      sect : _⋆_ C inv' f ≡ id C {y}
      retr : _⋆_ C f inv' ≡ id C {x}

open Precategory
open preIsIso

module _ {ℓC ℓC' ℓD ℓD' : Level} where
 -- Products
 _×_ :  (C : Precategory ℓC ℓC') (D : Precategory ℓD ℓD') → Precategory _ _
 ob (C × D) = ob C ×' ob D
 Hom[_,_] (C × D) (c , d) (c' , d') =
   Hom[_,_] C c c' ×' Hom[_,_] D d d'
 id (C × D) = id C , id D
 _⋆_ (C × D) f g = _⋆_ C (fst f) (fst g) , _⋆_ D (snd f) (snd g)
 ⋆IdL (C × D) (f , g) i = (⋆IdL C f i) , (⋆IdL D g i)
 ⋆IdR (C × D) (f , g) i = (⋆IdR C f i) , (⋆IdR D g i)
 ⋆Assoc (C × D) (f , g) (f' , g') (f'' , g'') i =
   ⋆Assoc C f f' f'' i , ⋆Assoc D g g' g'' i

 -- Functors
 record Prefunctor (C : Precategory ℓC ℓC') (D : Precategory ℓD ℓD') :
          Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
   no-eta-equality

   field
     F-ob  : C .ob → D .ob
     F-hom : {x y : C .ob} → C [ x , y ] → D [ F-ob x , F-ob y ]
     F-id  : {x : C .ob} → F-hom {y = x} (id C) ≡ id D
     F-seq : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
           → F-hom (f ⋆⟨ C ⟩ g) ≡ (F-hom f) ⋆⟨ D ⟩ (F-hom g)

 -- Natural transformation
 record PreNatTrans (C : Precategory ℓC ℓC') (D : Precategory ℓD ℓD')
          (F G : Prefunctor C D) :
          Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
   no-eta-equality

   open Prefunctor

   field
     N-ob : (x : C .ob) → D [ F .F-ob x , G .F-ob x ]
     N-hom : {x y : C .ob} (f : C [ x , y ])
       → (F .F-hom f) ⋆⟨ D ⟩ (N-ob y) ≡ (N-ob x) ⋆⟨ D ⟩ (G .F-hom f)

 -- Natural isomorphisms
 record PreNatIso (C : Precategory ℓC ℓC') (D : Precategory ℓD ℓD')
          (F G : Prefunctor C D) :
          Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
   open PreNatTrans

   field
     trans : PreNatTrans C D F G
     isIs : (c : C .ob) → preIsIso {C = D} (trans .N-ob c)

open Prefunctor
open PreNatTrans
open PreNatIso
open preIsIso


module _ {ℓC ℓC' ℓD ℓD' : Level}
  {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'}
  (F G H : Prefunctor C D) where

  compPreNatTrans : PreNatTrans _ _ F G → PreNatTrans _ _ G H → PreNatTrans _ _ F H
  N-ob (compPreNatTrans η γ) c = N-ob η c ⋆⟨ D ⟩ N-ob γ c
  N-hom (compPreNatTrans η γ) {x = x} {y = y} f =
    sym (⋆Assoc D _ _ _) ∙ cong (λ w → w ⋆⟨ D ⟩ (N-ob γ y)) (N-hom η f)
    ∙ ⋆Assoc D _ _ _
    ∙ cong  (D ⋆ N-ob η x) (N-hom γ f)
    ∙ sym (⋆Assoc D _ _ _)

  compPreNatIso : PreNatIso _ _ F G → PreNatIso _ _ G H → PreNatIso _ _ F H
  trans (compPreNatIso isη isγ) = compPreNatTrans (trans isη) (trans isγ)
  inv' (isIs (compPreNatIso isη isγ) c) = inv' (isIs isγ c) ⋆⟨ D ⟩ (inv' (isIs isη c))
  sect (isIs (compPreNatIso isη isγ) c) =
    ⋆Assoc D _ _ _
    ∙ cong (D ⋆ inv' (isIs isγ c))
       (sym (⋆Assoc D _ _ _)
       ∙ cong (λ w → w ⋆⟨ D ⟩ (N-ob (trans isγ) c)) (sect (isIs isη c))
       ∙ ⋆IdL D _)
    ∙ sect (isIs isγ c)
  retr (isIs (compPreNatIso isη isγ) c) =
    ⋆Assoc D _ _ _
    ∙ cong (D ⋆ N-ob (trans isη) c)
        (sym (⋆Assoc D _ _ _)
        ∙ cong (λ w → w ⋆⟨ D ⟩ (inv' (isIs isη c))) (retr (isIs isγ c))
        ∙ ⋆IdL D _)
    ∙ retr (isIs isη c)

module _ {ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level}
  {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} {E : Precategory ℓE ℓE'}
 where
 comp-Prefunctor : (F : Prefunctor C D) (G : Prefunctor D E)
   → Prefunctor C E
 F-ob (comp-Prefunctor F G) c = F-ob G (F-ob F c)
 F-hom (comp-Prefunctor F G) f = F-hom G (F-hom F f)
 F-id (comp-Prefunctor F G) = cong (F-hom G) (F-id F) ∙ F-id G
 F-seq (comp-Prefunctor F G) f g = cong (F-hom G) (F-seq F f g) ∙ F-seq G _ _


module _ {ℓC ℓC' : Level} {C : Precategory ℓC ℓC'}
  (F : Prefunctor (C × C) C) where
  assocₗ : Prefunctor (C × (C × C)) C
  F-ob assocₗ (x , y , z) = F-ob F (x , F-ob F (y , z))
  F-hom assocₗ {x} {y} (f , g) = F-hom F (f , F-hom F g)
  F-id assocₗ =
    cong (λ y → F-hom F (id C , y)) (F-id {C = C × C} F)
      ∙ F-id F
  F-seq assocₗ f g =
    cong (F-hom F)
         (cong (fst (f ⋆⟨ C × (C × C) ⟩ g) ,_)
           (F-seq F (snd f) (snd g)))
       ∙ F-seq F _ _

  assocᵣ : Prefunctor (C × (C × C)) C
  F-ob assocᵣ (x , y , z) = F-ob F (F-ob F (x , y) , z)
  F-hom assocᵣ (f , g) = F-hom F (F-hom F (f , (fst g)) , snd g)
  F-id assocᵣ = cong (F-hom F) (cong (_, id C) (F-id F))
              ∙ F-id F
  F-seq assocᵣ (f , f' , f'') (g , g' , g'') =
    cong (F-hom F) (cong (_, _⋆_ C f'' g'')
      (F-seq F (f , f') (g , g')))
    ∙ F-seq F _ _

-- Left and right restrictions of functors
module _ {ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level}
      {C : Precategory ℓC ℓC'}
      {D : Precategory ℓD ℓD'}
      {E : Precategory ℓE ℓE'}
      where
 restrFunctorₗ : (F : Prefunctor (C × D) E) (c : C . ob)
   → Prefunctor D E
 F-ob (restrFunctorₗ F c) d = F-ob F (c , d)
 F-hom (restrFunctorₗ F c) f = F-hom F (id C , f)
 F-id (restrFunctorₗ F c) = F-id F
 F-seq (restrFunctorₗ F c) f g =
     cong (F-hom F) (ΣPathP (sym (⋆IdR C _) , refl))
   ∙ F-seq F (id C , f) (id C , g)

 restrFunctorᵣ : (F : Prefunctor (C × D) E) (d : D . ob)
   → Prefunctor C E
 F-ob (restrFunctorᵣ F d) c = F-ob F (c , d)
 F-hom (restrFunctorᵣ F d) f = F-hom F (f , (id D))
 F-id (restrFunctorᵣ F d) = F-id F
 F-seq (restrFunctorᵣ F d) f g =
     cong (F-hom F) (ΣPathP (refl , sym (⋆IdR D _)))
   ∙ F-seq F (f , id D) (g , id D)

-- Identity functor
idPrefunctor : {ℓC ℓC' : Level}
      (C : Precategory ℓC ℓC')
   → Prefunctor C C
Prefunctor.F-ob (idPrefunctor C) c = c
Prefunctor.F-hom (idPrefunctor C) x = x
Prefunctor.F-id (idPrefunctor C) = refl
Prefunctor.F-seq (idPrefunctor C) _ _ = refl

-- Commutator
commFunctor : {ℓC ℓC' ℓD ℓD' : Level}
      {C : Precategory ℓC ℓC'}
      {D : Precategory ℓD ℓD'}
   → Prefunctor (C × D) (D × C)
Prefunctor.F-ob commFunctor (x , y) = y , x
Prefunctor.F-hom commFunctor (f , g) = g , f
Prefunctor.F-id commFunctor = refl
Prefunctor.F-seq commFunctor _ _ = refl

-- Monoidal, braided and monoidal symmetric precategories
module _ (M : Precategory ℓ ℓ') where
  record isMonoidalPrecategory : Type (ℓ-max ℓ ℓ') where
    field
      _⊗_ : Prefunctor (M × M) M
      𝟙 : ob M

      ⊗assoc : PreNatIso (M × (M × M)) M (assocₗ _⊗_) (assocᵣ _⊗_)

      ⊗lUnit : PreNatIso M M (restrFunctorₗ _⊗_ 𝟙) (idPrefunctor M)
      ⊗rUnit : PreNatIso M M (restrFunctorᵣ _⊗_ 𝟙) (idPrefunctor M)

    private
      α = N-ob (trans ⊗assoc)
      α⁻ : (c : ob M ×' ob M ×' ob M) → M [ _ , _ ]
      α⁻ c = preIsIso.inv' (isIs ⊗assoc c)
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

  module _ (mon : isMonoidalPrecategory) where
    open isMonoidalPrecategory mon
    private
      α = N-ob (trans ⊗assoc)
      α⁻ : (c : ob M ×' ob M ×' ob M) → M [ _ , _ ]
      α⁻ c = preIsIso.inv' (isIs ⊗assoc c)

    BraidingIsoType : Type _
    BraidingIsoType = PreNatIso (M × M) M _⊗_ (comp-Prefunctor commFunctor _⊗_)

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

  record isBraidedPrecategory : Type (ℓ-max ℓ ℓ') where
    open isMonoidalPrecategory
    field
      isMonoidal : isMonoidalPrecategory
      Braid : BraidingIsoType isMonoidal
      hexagons : (x y z : M .ob)
        → HexagonType₁ isMonoidal Braid
        ×' HexagonType₂ isMonoidal Braid

  record isSymmetricPrecategory : Type (ℓ-max ℓ ℓ') where
    field
      isMonoidal : isMonoidalPrecategory
      Braid : BraidingIsoType isMonoidal
      hexagon : HexagonType₁ isMonoidal Braid
      symBraiding : isSymmetricBraiding isMonoidal Braid

SymmetricMonoidalPrecat : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
SymmetricMonoidalPrecat ℓ ℓ' =
  Σ[ C ∈ Precategory ℓ ℓ' ] isSymmetricPrecategory C

-- Instances
module _ (ℓ : Level) where
  PointedCat : Precategory (ℓ-suc ℓ) ℓ
  ob PointedCat = Pointed ℓ
  Hom[_,_] PointedCat A B = A →∙ B
  Precategory.id PointedCat = idfun∙ _
  _⋆_ PointedCat f g = g ∘∙ f
  ⋆IdL PointedCat = ∘∙-idˡ
  ⋆IdR PointedCat = ∘∙-idʳ
  ⋆Assoc PointedCat f g h = sym (∘∙-assoc h g f)
