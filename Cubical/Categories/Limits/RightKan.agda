{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.Categories.Limits.RightKan where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Limits



module _ {ℓC ℓC' ℓM ℓM' ℓA ℓA' : Level}
         (C : Category ℓC ℓC')
         (M : Category ℓM ℓM')
         (A : Category ℓA ℓA')
         (limitA : ∀ {ℓJ ℓJ'} → Limits {ℓJ} {ℓJ'} A)
         (T : Functor M A)
         (K : Functor M C)
         where

 open Category
 open Functor
 open Cone
 open LimCone


 _↓Diag : ob C → Category _ _
 ob (x ↓Diag) = Σ[ u ∈ ob M ] C [ K .F-ob u , x ]
 Hom[_,_] (x ↓Diag) (u , f) (v , g) = Σ[ h ∈ M [ u , v ] ] K .F-hom h ⋆⟨ C ⟩ g ≡ f
 id (x ↓Diag) = id M , {!!}
 _⋆_ (x ↓Diag) = {!!}
 ⋆IdL (x ↓Diag) = {!!}
 ⋆IdR (x ↓Diag) = {!!}
 ⋆Assoc (x ↓Diag) = {!!}
 isSetHom (x ↓Diag) = {!!}

 -- need:
 i : (x : ob C) → Functor (x ↓Diag) M
 i x = {!!}
 j : {x y : ob C} (f : C [ x , y ]) → Functor (x ↓Diag) (y ↓Diag)
 j f = {!!}


 T* : (x : ob C) → Functor (x ↓Diag) A
 T* x = funcComp T (i x)

 RanOb : ob C → ob A
 RanOb x = limitA (x ↓Diag) (T* x) .lim

 -- ????
 -- RanCone : {x y : ob C} → C [ y , x ] → Cone (T* y) (RanOb x)
 -- coneOut (RanCone {x = x} f) v =
 --   limOut (limitA (x ↓Diag) (T* x)) (j f .F-ob v)
 -- coneOutCommutes (RanCone {x = x} f) = limOutCommutes (limitA (x ↓Diag) (T* x))


  -- record Cone (D : Functor J C) (c : ob C) : Type (ℓ-max (ℓ-max ℓJ ℓJ') ℓC') where
  --   constructor cone

  --   field
  --     coneOut : (v : ob J) → C [ c , F-ob D v ]
  --     coneOutCommutes : {u v : ob J} (e : J [ u , v ]) →
  --                       coneOut u ⋆⟨ C ⟩ D .F-hom e ≡ coneOut v


 Ran : Functor C A
 Ran = {!!}



 -- private
 --  -- x↓ ↪ L'
 --  inclInL' : (x : fst L) → Functor (x ↓Diag) (DLSubCat ^op)
 --  F-ob (inclInL' x) u = u .fst , u .snd .snd
 --  F-hom (inclInL' x) u≥v = u≥v
 --  F-id (inclInL' x) = refl
 --  F-seq (inclInL' x) _ _ = is-prop-valued _ _ _ _

 --  -- and y↓ ↪ x↓ for y≤x, but we don't care about functoriality
 --  ↓Incl : {x y : fst L} → y ≤ x
 --        → Σ[ u ∈ fst L ] u ∈ (y ↓)
 --        → Σ[ u ∈ fst L ] u ∈ (x ↓)
 --  ↓Incl y≤x (v , v≤y , v∈L') = (v , is-trans _ _ _ v≤y y≤x , v∈L')

 --  -- precomposition of F with the inclusion x↓ ↪ L'
 --  F* : (x : fst L) → Functor (x ↓Diag) C
 --  F* x = funcComp F (inclInL' x)

 --  -- the right Kan-extension on objects:
 --  -- laking the limit over maps F(u)→F(v) for v≤u≤x
 --  RanOb : fst L → ob C
 --  RanOb x = limitC (x ↓Diag) (F* x) .lim

 --  -- If y≤x we get a cone (i.e. commuting triangles) for v≤u≤y≤x:
 --  --
 --  -- lim { F(u)→F(v) | v≤u≤x } → F(v)
 --  --                          ↓   /
 --  --                          F(u)
 --  RanCone : {x y : fst L} → y ≤ x → Cone (F* y) (RanOb x)
 --  coneOut (RanCone {x = x} y≤x) v =
 --    limOut (limitC (x ↓Diag) (F* x)) (↓Incl y≤x v)
 --  coneOutCommutes (RanCone {x = x} y≤x) = limOutCommutes (limitC (x ↓Diag) (F* x))

 --  -- technical lemmas for proving functoriality
 --  RanConeRefl : ∀ {x} v →
 --                limOut (limitC (x ↓Diag) (F* x)) v
 --              ≡ limOut (limitC (x ↓Diag) (F* x)) (↓Incl (is-refl x) v)
 --  RanConeRefl {x = x} v =
 --    cong (λ p → limOut (limitC (x ↓Diag) (F* x)) (v .fst , p , v .snd .snd))
 --         (is-prop-valued _ _ _ _)

 --  RanConeTrans : ∀ {x y z} (y≤x : y ≤ x) (z≤y : z ≤ y) v →
 --                 limOut (limitC (x ↓Diag) (F* x)) (↓Incl y≤x (↓Incl z≤y v))
 --               ≡ limOut (limitC (x ↓Diag) (F* x)) (↓Incl (is-trans _ _ _ z≤y y≤x) v)
 --  RanConeTrans {x = x} {y = y} {z = z} y≤x z≤y v =
 --    cong (λ p → limOut (limitC (x ↓Diag) (F* x)) (v .fst , p , v .snd .snd))
 --         (is-prop-valued _ _ _ _)


 -- -- the right Kan-extension for DistLattice categories
 -- DLRan : DLPreSheaf
 -- F-ob DLRan = RanOb
 -- F-hom DLRan {y = y} y≤x = limArrow (limitC (y ↓Diag) (F* y)) _ (RanCone y≤x)
 -- F-id DLRan {x = x} =
 --  limArrowUnique (limitC (x ↓Diag) (F* x)) _ _ _ (λ v → (⋆IdL C _) ∙ RanConeRefl v)
 -- F-seq DLRan {x = x} {y = y} {z = z} y≤x z≤y =
 --  limArrowUnique (limitC (z ↓Diag) (F* z)) _ _ _ path
 --  where
 --  path : ∀ v →
 --         (F-hom DLRan y≤x) ⋆⟨ C ⟩ (F-hom DLRan z≤y) ⋆⟨ C ⟩ (limOut (limitC (z ↓Diag) (F* z)) v)
 --       ≡ coneOut (RanCone (is-trans _ _ _ z≤y y≤x)) v
 --  path v = (F-hom DLRan y≤x) ⋆⟨ C ⟩ (F-hom DLRan z≤y) ⋆⟨ C ⟩ (limOut (limitC (z ↓Diag) (F* z)) v)
 --         ≡⟨ ⋆Assoc C _ _ _ ⟩
 --           (F-hom DLRan y≤x) ⋆⟨ C ⟩ ((F-hom DLRan z≤y) ⋆⟨ C ⟩ (limOut (limitC (z ↓Diag) (F* z)) v))
 --         ≡⟨ cong (seq' C (F-hom DLRan y≤x)) (limArrowCommutes _ _ _ _) ⟩
 --           (F-hom DLRan y≤x) ⋆⟨ C ⟩ limOut (limitC (y ↓Diag) (F* y)) (↓Incl z≤y v)
 --         ≡⟨ limArrowCommutes _ _ _ _ ⟩
 --           limOut (limitC (x ↓Diag) (F* x)) (↓Incl y≤x (↓Incl z≤y v))
 --         ≡⟨ RanConeTrans y≤x z≤y v ⟩
 --           coneOut (RanCone (is-trans _ _ _ z≤y y≤x)) v ∎
