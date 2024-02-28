{-
  This file defines a wild category, which might be the free wild category over a
  directed graph (I do not know). This is intended to be used in a solver for
  wild categories.
-}
{-# OPTIONS --safe #-}

module Cubical.WildCat.Free3 where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function as Fu
open import Cubical.Foundations.Transport
import Cubical.Foundations.Isomorphism as Iso

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path renaming (Path to GPath)
import Cubical.Data.Graph.PathRefl as R

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.UnderlyingGraph

open import Cubical.Data.Sum
open import Cubical.Data.Sigma

-- open WildCat
-- open WildFunctor
-- open Graph

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' : Level

-- Free : (G : Graph ℓg ℓg') → WildCat ℓg (ℓ-max ℓg ℓg')
-- ob       (Free G)       = G .Node
-- Hom[_,_] (Free G) x y   = GPath G x y
-- id       (Free G)       = pnil
-- _⋆_      (Free G) f g   = ccat G f g
-- ⋆IdL     (Free G)       = pnil++ _
-- ⋆IdR     (Free G)       = λ _ → refl
-- ⋆Assoc   (Free G) f g h = ++assoc G f g h


module WGE (WG : WildGroupoid ℓg ℓg') (isSetHom : ∀ x y →
      isSet (WildCat.Hom[_,_] (WildGroupoid.wildCat WG) x y) ) where
 open WildGroupoid WG  
 open WildCat wildCat

 data FWG : Type (ℓ-max ℓg ℓg') where 
  [[_]] :  ob  → FWG 
  [[[_]]] : ∀ {x y} → Hom[ x , y ] → [[ x ]] ≡ [[ y ]]


 record fwgElim {ℓ'} {A : FWG → Type ℓ'} : Type (ℓ-max ℓ' (ℓ-max ℓg ℓg')) where 
  field
   [[]] : ∀ a → A [[ a ]]
   [[[]]] : ∀ {a a'} → (a= : Hom[ a , a' ]) →
                    PathP (λ i → A ([[[ a= ]]] i))
                       ([[]] a)
                       ([[]] a')
   
  f : ∀ a → A a
  f [[ x ]] = [[]] x
  f ([[[ x ]]] i) = [[[]]] x i

 record fwgElimProp {ℓ'} {A : FWG → Type ℓ'} : Type (ℓ-max ℓ' (ℓ-max ℓg ℓg')) where 
  field
   [[]] : ∀ a → A [[ a ]]
   isPropA : ∀ a → isProp (A a)
   
  f : ∀ a → A a
  f [[ x ]] = [[]] x
  f ([[[ x ]]] i) =
    isProp→PathP (λ i → isPropA ([[[ x ]]] i))
      ([[]] _) ([[]] _) i


 record fwgSetElim₂ {ℓ'} {A : FWG → FWG → Type ℓ'} : Type (ℓ-max ℓ' (ℓ-max ℓg ℓg')) where 
  field
   isSetA : ∀ a b → isSet (A a b)
   [[]][[]] : ∀ a b → A [[ a ]] [[ b ]]
   [[]][[[]]] : ∀ a {b b'} → (c : Hom[ b , b' ]) →
                    PathP (λ i → A [[ a ]] ([[[ c ]]] i))
                       ([[]][[]] a b)
                       ([[]][[]] a b')
   [[[]]][[]] : ∀ {a a'} → (c : Hom[ a , a' ]) → ∀ b →
                    PathP (λ i → A ([[[ c ]]] i) [[ b ]])
                       ([[]][[]] a b)
                       ([[]][[]] a' b)

  f : ∀ a b → A a b
  f [[ x ]] [[ x₁ ]] = [[]][[]] x x₁
  f [[ x ]] ([[[ x₁ ]]] i) = [[]][[[]]] x x₁ i
  f ([[[ x ]]] i) [[ x₁ ]] = [[[]]][[]] x x₁ i
  f ([[[ x ]]] i) ([[[ x₁ ]]] i₁) =
    isSet→SquareP (λ i i₁ → isSetA ([[[ x ]]] i) ([[[ x₁ ]]] i₁))
       ([[]][[[]]] _ x₁) ([[]][[[]]] _ x₁)
         ([[[]]][[]] x _) ([[[]]][[]] x _) i i₁


 record fwgSetElim₃ {ℓ'} {A : FWG → FWG → FWG → Type ℓ'} : Type (ℓ-max ℓ' (ℓ-max ℓg ℓg')) where 
  field
   isSetA : ∀ a b c → isSet (A a b c)
   [[]][[]][[]] : ∀ a b c → A [[ a ]] [[ b ]] [[ c ]]
   [[]][[]][[[]]] : ∀ a b {c c'} → (c= : Hom[ c , c' ]) →
                    PathP (λ i → A [[ a ]] [[ b ]] ([[[ c= ]]] i))
                       ([[]][[]][[]] a b c)
                       ([[]][[]][[]] a b c')
   [[]][[[]]][[]] : ∀ a {b b'} (b= : Hom[ b , b' ]) c →
                    PathP (λ i → A [[ a ]] ([[[ b= ]]] i) [[ c ]])
                       ([[]][[]][[]] a b c)
                       ([[]][[]][[]] a b' c)
   [[[]]][[]][[]] : ∀ {a a'} a= b c →
                    PathP (λ i → A ([[[ a= ]]] i) [[ b ]] [[ c ]])
                       ([[]][[]][[]] a b c)
                       ([[]][[]][[]] a' b c)
                       
  r₂ : fwgElim {A = λ _ → fwgSetElim₂}
  fwgSetElim₂.isSetA (fwgElim.[[]] r₂ a) _ _ = isSetA _ _ _
  fwgSetElim₂.[[]][[]] (fwgElim.[[]] r₂ a) _ _ = [[]][[]][[]] _ _ _
  fwgSetElim₂.[[]][[[]]] (fwgElim.[[]] r₂ a) _ _ = [[]][[]][[[]]] _ _ _
  fwgSetElim₂.[[[]]][[]] (fwgElim.[[]] r₂ a) _ _ = [[]][[[]]][[]] _ _ _
  fwgSetElim₂.isSetA (fwgElim.[[[]]] r₂ a= i) _ _ = isSetA _ _ _
  fwgSetElim₂.[[]][[]] (fwgElim.[[[]]] r₂ a= i) _ _ = [[[]]][[]][[]] a= _ _ i
  fwgSetElim₂.[[]][[[]]] (fwgElim.[[[]]] r₂ a= i) b c i₁ =
     isSet→SquareP
        (λ i i₁ → isSetA ([[[ a= ]]] i) [[ b ]] ([[[ c ]]] i₁))
        ([[]][[]][[[]]] _ b c)
        ([[]][[]][[[]]] _ b c)
        ([[[]]][[]][[]] a= b _)
        ([[[]]][[]][[]] a= b _)
        i i₁


  fwgSetElim₂.[[[]]][[]] (fwgElim.[[[]]] r₂ a= i) c b i₁ =
     isSet→SquareP   
       (λ i i₁ → isSetA ([[[ a= ]]] i) ([[[ c ]]] i₁) [[ b ]])
       ([[]][[[]]][[]] _ c b)
       ([[]][[[]]][[]] _ c b)
       ([[[]]][[]][[]] a= _ b)
       ([[[]]][[]][[]] a= _ b)
        i i₁

  f : ∀ a b c → A a b c
  f a = fwgSetElim₂.f (fwgElim.f r₂ a)


 fwgCode : ob → FWG → Type ℓg'
 fwgCode x [[ y ]] = Hom[ x , y ]
 fwgCode x ([[[ f ]]] i) = ua (wg⋆≃Post {x = x} f) i

 fwgPreCode : FWG → ob → Type ℓg'
 fwgPreCode [[ x ]] y = Hom[ x , y ]
 fwgPreCode ([[[ f ]]] i) y = ua (wg⋆≃Pre {x = _} {_} {y} (inv f)) i


 pre-post : ∀ {x' x y y'} (f : Hom[ x' , x ]) (g : Hom[ y , y' ]) →
                  wg⋆≃Pre f ∙ₑ wg⋆≃Post g ≡
                  wg⋆≃Post g ∙ₑ wg⋆≃Pre f
 pre-post _ _ = equivEq (funExt λ _ → ⋆Assoc _ _ _) 


 fwgCodeeL : ∀ {x y y' z} → (q : Hom[ x , y ]) (p : Hom[ y' , z ]) →
   PathP
      (λ i₁ → ua (wg⋆≃Post {x = x} {y'} {z} p) i₁ → ua (wg⋆≃Pre (inv q) ∙ₑ wg⋆≃Post p) i₁)
      ((wg⋆≃Pre (inv q) ∙ₑ wg⋆≃Pre q) .fst) (wg⋆≃Pre (inv q) .fst)
 fwgCodeeL q p i x =


   hcomp (λ j → λ { (i = i0) → ⋆Assoc q (inv q) x j
                     ; (i = i1) → inv q ⋆ x
                     })
                   (glue
                  (λ { (i = i0) → (q ⋆ inv q) ⋆ x
                     ; (i = i1) → inv q ⋆ x
                     }) (hcomp 
            (λ j → λ {(i = i0) → ⋆Assoc (inv q) (⋆InvR q (~ j) ⋆  x) p (~ j) 
               ;(i = i1) → inv q ⋆ x
               }) ((hcomp 
            (λ j → λ {(i = i0) → inv q ⋆ (⋆IdL x (~ j) ⋆ p) 
               ;(i = i1) → inv q ⋆ x
                     }) (inv q ⋆ unglue (i ∨ ~ i) x)
                 )) 
                 ))
   

 fwgCodeeR : ∀ {x y y' z} → (q : Hom[ x , y ]) (p : Hom[ y' , z ]) →
               PathP
      (λ i₁ → ua (wg⋆≃Post {x = y} p) i₁ → ua (wg⋆≃Post p ∙ₑ wg⋆≃Pre (inv q)) i₁)
      (wg⋆≃Pre q .fst)
      (idfun Hom[ y , z ])
 fwgCodeeR q p i x =
                      (glue
                  (λ { (i = i0) → q ⋆ x
                     ; (i = i1) → x
                     }) (hcomp
            (λ j → λ { (i = i0) → inv q ⋆ ⋆Assoc q x p (~ j) --⋆Assoc (inv q) (q ⋆ x) p j
                     ; (i = i1) → x
                     }) (hcomp
            (λ j → λ { (i = i0) → ⋆Assoc (inv q) q (x ⋆ p) j
                     ; (i = i1) → x
                     }) (hcomp
            (λ j → λ { (i = i0) → ⋆InvL q (~ j) ⋆ (x ⋆ p)
                     ; (i = i1) → x
                     }) (⋆IdL (unglue (i ∨ ~ i) x) i)))) )
 
 fwgCodee : FWG → FWG → Type ℓg'
 fwgCodee [[ x ]] y = fwgCode x y
 fwgCodee ([[[ q ]]] i) [[ y ]] = fwgPreCode ([[[ q ]]] i) y
 fwgCodee ([[[_]]] {x} {y} q i) ([[[_]]] {y'} {z} p j) =
   
   Glue (ua (pre-post (inv q) p i) j)
     λ { (i = i0) → ua (wg⋆≃Post {x = x} {y = y'} {z = z} p) j ,
                     equivPathP {A = λ j → ua (wg⋆≃Post p) j}
                                {B = λ j → (ua (pre-post (inv q) p i) j)}
                                {e = wg⋆≃Pre {z = y'}
                          (inv q) ∙ₑ wg⋆≃Pre {z = y'} q} {f = wg⋆≃Pre {x = y} {z = z} (inv q)}
                          (fwgCodeeL q p)
                           j
        ; (i = i1) → ua (wg⋆≃Post {x = y} {y = y'} {z = z} p) j ,
         equivPathP {A = λ j → ua (wg⋆≃Post p) j}
                     {B = λ j → ua (wg⋆≃Post p ∙ₑ wg⋆≃Pre (inv q)) j}
                     {e = compEquiv (idEquiv Hom[ y , y' ]) (wg⋆≃Pre q)}
                     {f = idEquiv _}
                     (fwgCodeeR q p) j

        ; (j = i0) → ua (wg⋆≃Pre {x = y} {z = y'} (inv q)) i ,
                    ua-unglueEquiv (wg⋆≃Pre {x = y} {z = y'} (inv q)) i
                      ∙ₑ wg⋆≃Pre q
        ; (j = i1) → ua (wg⋆≃Pre {x = y} {z = z} (inv q)) i ,
                     ua-unglueEquiv (wg⋆≃Pre {x = y} {y = x} {z = z} (inv q)) i
        } 

 isSetFwgCode : ∀ x y → isSet (fwgCode x y)
 isSetFwgCode x [[ x₁ ]] = isSetHom _ _
 isSetFwgCode x ([[[ x₁ ]]] i) =
       isProp→PathP (λ i → isPropIsSet {A = fwgCodee [[ x ]] ([[[ x₁ ]]] i)})
      (isSetHom _ _) (isSetHom _ _) i
 
 isSetFwgCodee : ∀ x y → isSet (fwgCodee x y)
 isSetFwgCodee [[ x ]] = λ { [[ x₁ ]] → isSetHom _ _
  ;   ([[[ x₁ ]]] i) → 
    isProp→PathP (λ i → isPropIsSet {A = fwgCodee [[ x ]] ([[[ x₁ ]]] i)})
      (isSetHom _ _) (isSetHom _ _) i }
 isSetFwgCodee ([[[ x ]]] i) y =
   isProp→PathP (λ i → isPropIsSet {A = fwgCodee ([[[ x ]]] i) y})
      (isSetFwgCodee ([[[ x ]]] i0) y)
      (isSetFwgCodee ([[[ x ]]] i1) y) i
 
 fwgCodeeInv : ∀ x y → fwgCodee x y → fwgCodee y x
 fwgCodeeInv = fwgSetElim₂.f w
  where
  w : fwgSetElim₂
  fwgSetElim₂.isSetA w = (λ a b → isSet→ {A = fwgCodee a b} (isSetFwgCodee b a))
  fwgSetElim₂.[[]][[]] w _ _ = inv
  fwgSetElim₂.[[]][[[]]] w x  x₂ i x₁ =
    let x₁' = ua-unglue (wg⋆≃Post x₂) i x₁
    in glue (λ { (i = i0) → inv x₁ ;
                (i = i1) → inv x₁'
                })
                (hcomp (λ j →
                (λ { (i = i0) → distInv x₁ x₂ j ;
                     (i = i1) → inv x₁'
                }) ) (inv x₁'))
  fwgSetElim₂.[[[]]][[]] w x x₂ i x₁ =
   let x' = ua-unglue (wg⋆≃Pre (inv x)) i x₁
   in glue (λ { (i = i0) → inv x₁ ;
                (i = i1) → inv x₁
                })
                 (hcomp (λ j →
                (λ { (i = i0) → (distInv (inv x) x₁ ∙ cong (inv x₁ ⋆_) (invol-inv x)) j  ;
                     (i = i1) → inv x₁
                }) ) (inv x'))
 
 idFWG : ∀ x → fwgCodee x x
 idFWG [[ x ]] = id
 idFWG ([[[_]]] {x} {y} f i) =
  glue (λ { (i = i0) → _
          ; (i = i1) → _
          }) (glue (λ { (i = i0) → _
          ; (i = i1) → _
          }) (lem i))

  where
   lem : ((inv f ⋆ (f ⋆ (inv f ⋆ id))) ⋆ f) ≡ id
   lem = (λ i → ⋆Assoc (inv f) (⋆Assoc f (inv f) id (~ i)) f i) ∙∙
            (λ i → (inv f ⋆ (⋆IdR (⋆InvR f i) i ⋆ f))) ∙
              (λ i → inv f ⋆ ⋆IdL f i) ∙∙ ⋆InvL f

 fwgCodeP : ∀ {x y} →  x ≡ y → fwgCodee x y 
 fwgCodeP {x} = J (λ y p → fwgCodee x y) (idFWG x)



 fwgCode' : ∀ {x y} →  [[ x ]] ≡ y → fwgCode x y 
 fwgCode' {x} = J (λ y p → fwgCode x y) id

 fwgCode'' : ∀ {x y} →  [[ x ]] ≡ [[ y ]] → Hom[ x , y ] 
 fwgCode'' {x} = fwgCode'


 fwgDeCode' : ∀ {x y} →  Hom[ x , y ] → [[ x ]] ≡ [[ y ]] 
 fwgDeCode' {x} = [[[_]]]

 lInv : ∀ {x y} → (f : Hom[ x , y ]) → fwgCode'' (fwgDeCode' f) ≡ f 
 lInv f i = transportRefl (⋆IdL f i) i 
 
 fromS≡ : ∀ {x y} → (f g  : Hom[ x , y ]) → fwgDeCode' f ≡ fwgDeCode' g → f ≡ g  
 fromS≡ f g p = sym (lInv f) ∙∙ cong fwgCode'' p ∙∙ lInv g


 fwgCode'M : ∀ {x y} →  x ≡ [[ y ]] → fwgCodee x [[ y ]] 
 fwgCode'M {y = y} = J (λ x _ → fwgCodee x [[ y ]])
   id Fu.∘ sym



 [a⋆b]⋆[b⁻⋆c]≡a⋆c : ∀ {x y z w} →
   (a : Hom[ x , y ]) → (b : Hom[ y , w ]) → (c : Hom[ y , z ])
   → (a ⋆ b) ⋆ (inv b ⋆ c) ≡ (a ⋆ c)
 [a⋆b]⋆[b⁻⋆c]≡a⋆c a b c =
   ⋆Assoc _ _ _ ∙ cong (a ⋆_) (sym (⋆Assoc _ _ _) ∙
     cong (_⋆ c) (⋆InvR b) ∙ ⋆IdL c)
     
 mkFwgCodee : ∀ x y → x ≡ y → fwgCodee x y
 mkFwgCodee x y = J (λ y _ → fwgCodee x y) (idFWG x)

 _fwg⋆_ : ∀ {x y z} → fwgCodee x y → fwgCodee y z → fwgCodee x z
 _fwg⋆_ {x} {y} {z} = f w x y z 
  where
  open fwgSetElim₃
  w : fwgSetElim₃ {A = λ x y z → fwgCodee x y → fwgCodee y z → fwgCodee x z}
  isSetA w x _ z = isSetΠ2 λ _ _ → isSetFwgCodee x z
  [[]][[]][[]] w _ _ _ = _⋆_
  [[]][[]][[[]]] w a b c= i f g =
    let g' = ua-unglue (wg⋆≃Post c=) i g
    in ua-glue (wg⋆≃Post c=) i
         (λ { (i = i0) → f ⋆ g })
           (inS (hcomp
                 (λ k → λ { (i = i0) → ⋆Assoc f g c= (~ k)
                          ; (i = i1) → f ⋆ g
                          }) (f ⋆ g')))
  [[]][[[]]][[]] w a b= c i f g =
    let f' = ua-unglue (wg⋆≃Post b=) i f
        g' = ua-unglue (wg⋆≃Pre (inv b=)) i g
    in hcomp (λ k → λ { (i = i0) → [a⋆b]⋆[b⁻⋆c]≡a⋆c f b= g k
                       ; (i = i1) → f ⋆ g
                          })
                          (f' ⋆ g')
  [[[]]][[]][[]] w a= b c i f g =
    let f' = ua-unglue (wg⋆≃Pre (inv a=)) i f
    in ua-glue (wg⋆≃Pre (inv a=)) i
          (λ { (i = i0) → f ⋆ g})
          (inS (hcomp
                 (λ k → λ { (i = i0) → ⋆Assoc (inv a=) f g k
                          ; (i = i1) → f ⋆ g
                          }) (f' ⋆ g)))
    
 fwg⋆Lem : ∀ {x y z} → (f : x ≡ y) (g : y ≡ z) →
   (_fwg⋆_ {x} {y} {z} (fwgCodeP {x} {y} f) (fwgCodeP {y} {z} g) ) ≡ fwgCodeP {x} {z} (f ∙ g) 
 fwg⋆Lem {x} {y} {z} =
   J (λ y f → (g : y ≡ z) →
     (_fwg⋆_ {x} {y} {z} (fwgCodeP {x} {y} f) (fwgCodeP {y} {z} g) ) ≡
      fwgCodeP {x} {z} (f ∙ g))
       (J (λ z g → (_fwg⋆_ {x} {x} {z} (fwgCodeP {x} {x} refl) (fwgCodeP {x} {z} g) ) ≡
      fwgCodeP {x} {z} (refl ∙ g))
       (fwgElimProp.f {A = λ x → (_fwg⋆_ {x} {x} {x} (fwgCodeP (λ _ → x))  (fwgCodeP {x} {x} refl)) ≡
      fwgCodeP ((λ _ → x) ∙ refl)} w x))
  where
  w : fwgElimProp
  fwgElimProp.isPropA w a = isSetFwgCodee a a _ _
  fwgElimProp.[[]] w a =
    (λ i → (transp (λ i → Hom[ a , a ]) i id ⋆
       transp (λ i → Hom[ a , a ]) i id)) ∙∙ (⋆IdR id) ∙∙
      λ i → transp (λ j → Hom[ a , a ]) (~ i)
      (transp (λ i → Hom[ a , a ]) (~ i)
       (transp (λ i → Hom[ a , a ]) (~ i) id))

 -- fwgCode''∙ : ∀ {x y z} → (p : [[ x ]] ≡ [[ y ]]) → (q : [[ y ]] ≡ [[ z ]]) →
 --    fwgCode'' (p ∙ q) ≡
 --      (fwgCode'' p ⋆ fwgCode'' q)
 -- fwgCode''∙ {x} {y} {z} p q = sym (fwg⋆Lem p q)
 --  -- fwgCode''∙0 {x} {[[ y ]]} {[[ z ]]} p q 

 fwgCode''inv0 : ∀ {x y} → (p : [[ x ]] ≡ y) →
    fwgCodeeInv [[ x ]] y (fwgCode' p) ≡
      (fwgCode'M (sym p))
 fwgCode''inv0 {x = x} = J (λ y p → fwgCodeeInv [[ x ]] y (fwgCode' p) ≡
      (fwgCode'M (sym p)))
        (cong inv (transportRefl _)
         ∙∙ id≡inv-id
         ∙∙ sym (transportRefl _))


 fwgCode''invLem :  ∀ {x y} → (p : x ≡ [[ y ]])
   → transp (λ i → fwgCodee (p i) x) i0 (idFWG x) ≡
      transp (λ i → fwgCode y (p (~ i))) i0 id
 fwgCode''invLem {x} {y} =
  J (λ x (p : [[ y ]] ≡ x) → 
     transp (λ i → fwgCodee (p (~ i)) x) i0 (idFWG x) ≡
      transp (λ i → fwgCode y (p i)) i0 id) refl Fu.∘ sym
 
 fwgCode''inv : ∀ {x y} → (p : [[ x ]] ≡ [[ y ]]) →
    inv (fwgCode'' p) ≡
      (fwgCode'' (sym p))
 fwgCode''inv p = fwgCode''inv0 p ∙ fwgCode''invLem p
 
 data GrpExpr : (x y : ob) → Type (ℓ-max ℓg ℓg') where
  idE : ∀ {x} → GrpExpr x x 
  _⋆E_ : ∀ {x y z} → GrpExpr x y → GrpExpr y z → GrpExpr x z
  invE : ∀ {x y} → GrpExpr x y → GrpExpr y x
  [[_]]E : ∀ {x y} → Hom[ x , y ] → GrpExpr x y


 GrpExpr→WG : ∀ {x y} → GrpExpr x y → Hom[ x , y ] 
 GrpExpr→WG idE = id
 GrpExpr→WG (x ⋆E x₁) = GrpExpr→WG x ⋆ GrpExpr→WG x₁
 GrpExpr→WG (invE x) = inv (GrpExpr→WG x)
 GrpExpr→WG [[ x ]]E = x
 
 GrpExpr→FWG : ∀ {x y} → GrpExpr x y → [[ x ]] ≡ [[ y ]] 
 GrpExpr→FWG idE = refl
 GrpExpr→FWG (x ⋆E x₁) = GrpExpr→FWG x ∙ GrpExpr→FWG x₁
 GrpExpr→FWG (invE x) = sym (GrpExpr→FWG x)
 GrpExpr→FWG [[ x ]]E = [[[ x ]]]


 GrpExpr→FWG≡WG : ∀ {x y} → ∀ f →  fwgCode'' {x} {y} (GrpExpr→FWG f) ≡ GrpExpr→WG f 
 GrpExpr→FWG≡WG idE = transportRefl _
 GrpExpr→FWG≡WG {x} (f ⋆E f₁) =  
     sym (fwg⋆Lem (GrpExpr→FWG f) (GrpExpr→FWG f₁)) ∙ 
      cong₂ _⋆_ (GrpExpr→FWG≡WG f) (GrpExpr→FWG≡WG f₁)   
 GrpExpr→FWG≡WG (invE f) =
       sym (fwgCode''inv ( (GrpExpr→FWG f))) ∙
         cong inv (GrpExpr→FWG≡WG f)
 GrpExpr→FWG≡WG [[ x ]]E = lInv x


-- -- -- --  -- codeIso : ∀ {x y} → Iso.Iso Hom[ x , y ] ([[ x ]] ≡ [[ y ]])  
-- -- -- --  -- Iso.Iso.fun codeIso = [[[_]]]
-- -- -- --  -- Iso.Iso.inv codeIso = fwgCode'
-- -- -- --  -- Iso.Iso.rightInv (codeIso {x = x}) = {!!}
-- -- -- --  --   --J (λ y b → [[[ transp (λ i → fwgCode x (b i)) i0 id ]]] ≡ b) {!!}
-- -- -- --  -- Iso.Iso.leftInv codeIso a = transportRefl _ ∙ ⋆IdL a

-- -- -- -- -- module _ (G : Graph ℓg ℓg') where

-- -- -- -- --  data FWG (x : G .Node) : Type (ℓ-max ℓg ℓg') where 
-- -- -- -- --   [[_]] :  ∀ {y} → G .Edge x y →  FWG x 
-- -- -- -- --   [[_↔_]] : ∀ {y z} → {!G .Edge y z!} → {!!}
  
-- -- -- -- -- FreeWG : (G : Graph ℓg ℓg') → WildGroupoid ℓg (ℓ-max ℓg ℓg')
-- -- -- -- -- ob (WildGroupoid.wildCat (FreeWG G)) = G .Node
-- -- -- -- -- Hom[ WildGroupoid.wildCat (FreeWG G) , x ] y = R.Path G x y
-- -- -- -- -- id (WildGroupoid.wildCat (FreeWG G)) = R.pnil
-- -- -- -- -- _⋆_ (WildGroupoid.wildCat (FreeWG G)) = R.ccat _
-- -- -- -- -- ⋆IdL (WildGroupoid.wildCat (FreeWG G)) = R.pnil++ _
-- -- -- -- -- ⋆IdR (WildGroupoid.wildCat (FreeWG G)) _ = refl
-- -- -- -- -- ⋆Assoc (WildGroupoid.wildCat (FreeWG G)) = R.++assoc G
-- -- -- -- -- WildGroupoid.inv (FreeWG G) = R.invPath G
-- -- -- -- -- WildGroupoid.·InvR (FreeWG G) = {!!}
-- -- -- -- -- WildGroupoid.·InvL (FreeWG G) = {!!}

-- -- -- -- -- inducedFunctor : (G : Graph ℓg ℓg') (C : WildCat ℓc ℓc')
-- -- -- -- --                → (g : GraphHom G (Cat→Graph C))
-- -- -- -- --                → WildFunctor (Free G) C
-- -- -- -- -- inducedFunctor G C g = F
-- -- -- -- --   where
-- -- -- -- --     open GraphHom
-- -- -- -- --     F : WildFunctor (Free G) C
-- -- -- -- --     F-ob  F x = g $g x
-- -- -- -- --     F-hom F f = {!comcatList (map (g <$g>_) (PathToList f))!}
-- -- -- -- --     F-id  F = {!!}
-- -- -- -- --     F-seq F = {!!}
