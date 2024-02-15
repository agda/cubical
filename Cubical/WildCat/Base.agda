{-
  wild categories, analogous to the formalization in Coq-HoTT

  https://github.com/HoTT/Coq-HoTT/tree/master/theories/WildCat

-}
{-# OPTIONS --safe #-}
module Cubical.WildCat.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma renaming (_×_ to _×'_)

private
  variable
    ℓ ℓ' : Level
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

record WildCat ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
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

open WildCat

-- Helpful syntax/notation
_[_,_] : (C : WildCat ℓ ℓ') → (x y : C .ob) → Type ℓ'
_[_,_] = Hom[_,_]

-- Needed to define this in order to be able to make the subsequence syntax declaration
seq' : ∀ (C : WildCat ℓ ℓ') {x y z} (f : C [ x , y ]) (g : C [ y , z ]) → C [ x , z ]
seq' = _⋆_

infixl 15 seq'
syntax seq' C f g = f ⋆⟨ C ⟩ g

-- composition
comp' : ∀ (C : WildCat ℓ ℓ') {x y z} (g : C [ y , z ]) (f : C [ x , y ]) → C [ x , z ]
comp' = _∘_

infixr 16 comp'
syntax comp' C g f = g ∘⟨ C ⟩ f

-- Isomorphisms and paths in precategories
record WildCatIso (C : WildCat ℓ ℓ') (x y : C .ob) : Type ℓ' where
  constructor precatiso
  field
    mor : C [ x , y ]
    inv : C [ y , x ]
    sec : inv ⋆⟨ C ⟩ mor ≡ C .id
    ret : mor ⋆⟨ C ⟩ inv ≡ C .id

-- Opposite wild category
_^op : WildCat ℓ ℓ' → WildCat ℓ ℓ'
(C ^op) .ob = C .ob
(C ^op) .Hom[_,_] x y = C .Hom[_,_] y x
(C ^op) .id = C .id
(C ^op) ._⋆_ f g = C ._⋆_ g f
(C ^op) .⋆IdL = C .⋆IdR
(C ^op) .⋆IdR = C .⋆IdL
(C ^op) .⋆Assoc f g h = sym (C .⋆Assoc _ _ _)

-- Natural isomorphisms
module _ {ℓC ℓC' : Level} {C : WildCat ℓC ℓC'}
  {x y : C .ob} (f : Hom[_,_] C x y) where
  record wildIsIso : Type (ℓ-max ℓC ℓC') where
    field
      inv' : Hom[_,_] C y x
      sect : _⋆_ C inv' f ≡ id C {y}
      retr : _⋆_ C f inv' ≡ id C {x}

open WildCat
open wildIsIso

_×_ :  (C : WildCat ℓC ℓC') (D : WildCat ℓD ℓD') → WildCat _ _
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
record WildFunctor (C : WildCat ℓC ℓC') (D : WildCat ℓD ℓD') :
         Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  no-eta-equality

  field
    F-ob  : C .ob → D .ob
    F-hom : {x y : C .ob} → C [ x , y ] → D [ F-ob x , F-ob y ]
    F-id  : {x : C .ob} → F-hom {y = x} (id C) ≡ id D
    F-seq : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
          → F-hom (f ⋆⟨ C ⟩ g) ≡ (F-hom f) ⋆⟨ D ⟩ (F-hom g)

-- Natural transformation
record WildNatTrans (C : WildCat ℓC ℓC') (D : WildCat ℓD ℓD')
         (F G : WildFunctor C D) :
         Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  no-eta-equality

  open WildFunctor

  field
    N-ob : (x : C .ob) → D [ F .F-ob x , G .F-ob x ]
    N-hom : {x y : C .ob} (f : C [ x , y ])
      → (F .F-hom f) ⋆⟨ D ⟩ (N-ob y) ≡ (N-ob x) ⋆⟨ D ⟩ (G .F-hom f)

-- Natural isomorphisms
record WildNatIso (C : WildCat ℓC ℓC') (D : WildCat ℓD ℓD')
         (F G : WildFunctor C D) :
         Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  open WildNatTrans

  field
    trans : WildNatTrans C D F G
    isIs : (c : C .ob) → wildIsIso {C = D} (trans .N-ob c)


open WildFunctor
open WildNatTrans
open WildNatIso
open wildIsIso

module _
  {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'}
  (F G H : WildFunctor C D) where

  compWildNatTrans : WildNatTrans _ _ F G → WildNatTrans _ _ G H → WildNatTrans _ _ F H
  N-ob (compWildNatTrans η γ) c = N-ob η c ⋆⟨ D ⟩ N-ob γ c
  N-hom (compWildNatTrans η γ) {x = x} {y = y} f =
    sym (⋆Assoc D _ _ _) ∙ cong (λ w → w ⋆⟨ D ⟩ (N-ob γ y)) (N-hom η f)
    ∙ ⋆Assoc D _ _ _
    ∙ cong  (D ⋆ N-ob η x) (N-hom γ f)
    ∙ sym (⋆Assoc D _ _ _)

  compWildNatIso : WildNatIso _ _ F G → WildNatIso _ _ G H → WildNatIso _ _ F H
  trans (compWildNatIso isη isγ) = compWildNatTrans (trans isη) (trans isγ)
  inv' (isIs (compWildNatIso isη isγ) c) = inv' (isIs isγ c) ⋆⟨ D ⟩ (inv' (isIs isη c))
  sect (isIs (compWildNatIso isη isγ) c) =
    ⋆Assoc D _ _ _
    ∙ cong (D ⋆ inv' (isIs isγ c))
       (sym (⋆Assoc D _ _ _)
       ∙ cong (λ w → w ⋆⟨ D ⟩ (N-ob (trans isγ) c)) (sect (isIs isη c))
       ∙ ⋆IdL D _)
    ∙ sect (isIs isγ c)
  retr (isIs (compWildNatIso isη isγ) c) =
    ⋆Assoc D _ _ _
    ∙ cong (D ⋆ N-ob (trans isη) c)
        (sym (⋆Assoc D _ _ _)
        ∙ cong (λ w → w ⋆⟨ D ⟩ (inv' (isIs isη c))) (retr (isIs isγ c))
        ∙ ⋆IdL D _)
    ∙ retr (isIs isη c)

module _
  {C : WildCat ℓC ℓC'} {D : WildCat ℓD ℓD'} {E : WildCat ℓE ℓE'}
 where
 comp-WildFunctor : (F : WildFunctor C D) (G : WildFunctor D E)
   → WildFunctor C E
 F-ob (comp-WildFunctor F G) c = F-ob G (F-ob F c)
 F-hom (comp-WildFunctor F G) f = F-hom G (F-hom F f)
 F-id (comp-WildFunctor F G) = cong (F-hom G) (F-id F) ∙ F-id G
 F-seq (comp-WildFunctor F G) f g = cong (F-hom G) (F-seq F f g) ∙ F-seq G _ _


module _ {C : WildCat ℓC ℓC'}
  (F : WildFunctor (C × C) C) where
  assocₗ : WildFunctor (C × (C × C)) C
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

  assocᵣ : WildFunctor (C × (C × C)) C
  F-ob assocᵣ (x , y , z) = F-ob F (F-ob F (x , y) , z)
  F-hom assocᵣ (f , g) = F-hom F (F-hom F (f , (fst g)) , snd g)
  F-id assocᵣ = cong (F-hom F) (cong (_, id C) (F-id F))
              ∙ F-id F
  F-seq assocᵣ (f , f' , f'') (g , g' , g'') =
    cong (F-hom F) (cong (_, _⋆_ C f'' g'')
      (F-seq F (f , f') (g , g')))
    ∙ F-seq F _ _

-- Left and right restrictions of functors
module _
      {C : WildCat ℓC ℓC'}
      {D : WildCat ℓD ℓD'}
      {E : WildCat ℓE ℓE'}
      where
 restrFunctorₗ : (F : WildFunctor (C × D) E) (c : C . ob)
   → WildFunctor D E
 F-ob (restrFunctorₗ F c) d = F-ob F (c , d)
 F-hom (restrFunctorₗ F c) f = F-hom F (id C , f)
 F-id (restrFunctorₗ F c) = F-id F
 F-seq (restrFunctorₗ F c) f g =
     cong (F-hom F) (ΣPathP (sym (⋆IdR C _) , refl))
   ∙ F-seq F (id C , f) (id C , g)

 restrFunctorᵣ : (F : WildFunctor (C × D) E) (d : D . ob)
   → WildFunctor C E
 F-ob (restrFunctorᵣ F d) c = F-ob F (c , d)
 F-hom (restrFunctorᵣ F d) f = F-hom F (f , (id D))
 F-id (restrFunctorᵣ F d) = F-id F
 F-seq (restrFunctorᵣ F d) f g =
     cong (F-hom F) (ΣPathP (refl , sym (⋆IdR D _)))
   ∙ F-seq F (f , id D) (g , id D)

-- Identity functor
idWildFunctor : {ℓC ℓC' : Level}
      (C : WildCat ℓC ℓC')
   → WildFunctor C C
WildFunctor.F-ob (idWildFunctor C) c = c
WildFunctor.F-hom (idWildFunctor C) x = x
WildFunctor.F-id (idWildFunctor C) = refl
WildFunctor.F-seq (idWildFunctor C) _ _ = refl

-- Commutator
commFunctor : {ℓC ℓC' ℓD ℓD' : Level}
      {C : WildCat ℓC ℓC'}
      {D : WildCat ℓD ℓD'}
   → WildFunctor (C × D) (D × C)
WildFunctor.F-ob commFunctor (x , y) = y , x
WildFunctor.F-hom commFunctor (f , g) = g , f
WildFunctor.F-id commFunctor = refl
WildFunctor.F-seq commFunctor _ _ = refl
