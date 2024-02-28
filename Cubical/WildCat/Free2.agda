{-
  This file defines a wild category, which might be the free wild category over a
  directed graph (I do not know). This is intended to be used in a solver for
  wild categories.
-}
{-# OPTIONS --safe #-}

module Cubical.WildCat.Free2 where

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
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


module _ (WG : WildGroupoid ℓg ℓg') where
 open WildGroupoid WG  
 open WildCat wildCat

 data FWG : Type (ℓ-max ℓg ℓg') where 
  [[_]] :  ob  → FWG 
  [[[_]]] : ∀ {x y} → Hom[ x , y ] → [[ x ]] ≡ [[ y ]]


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

 
 Loop≃ : ∀ {x y} → Hom[ x , y ] → Hom[ x , x ] ≃ Hom[ y , y ] 
 Loop≃ f = wg⋆≃Post f ∙ₑ wg⋆≃Pre (inv f)
 
 CodeFWG : FWG → Type ℓg'
 CodeFWG [[ x ]] = Hom[ x , x ]
 CodeFWG ([[[ f ]]] i) = ua (Loop≃ f) i

 codeFWG : ∀ {x y} → [[ x ]] ≡ y → CodeFWG y
 codeFWG p = subst CodeFWG p id

 -- decodeFWG : ∀ {y} → CodeFWG y → y ≡ y

 -- decodeFWG : ∀ {y} → CodeFWG y → y ≡ y
 -- decodeFWG {y = [[ x₁ ]]} p = [[[ p ]]]
 -- decodeFWG {y = [[[ x₁ ]]] i} p j = 
 --   hcomp (λ k → λ { (i = i0) → {!!}
 --                  ; (i = i1) → [[[ p ]]] j
 --                  ; (j = i0) → [[[ x₁ ]]] (i ∨ ~ k)
 --                  ; (j = i1) → [[[ x₁ ]]] (i ∨ ~ k)
 --                  })
 --        ([[[ ua-unglue (Loop≃ x₁) i p ]]] j)


--  fwgCodeeL : ∀ {x y y' z} → (q : Hom[ x , y ]) (p : Hom[ y' , z ]) →
--    PathP
--       (λ i₁ → ua (wg⋆≃Post {x = x} {y'} {z} p) i₁ → ua (wg⋆≃Pre (inv q) ∙ₑ wg⋆≃Post p) i₁)
--       ((wg⋆≃Pre (inv q) ∙ₑ wg⋆≃Pre q) .fst) (wg⋆≃Pre (inv q) .fst)
--  fwgCodeeL q p i x =


--    hcomp (λ j → λ { (i = i0) → ⋆Assoc q (inv q) x j
--                      ; (i = i1) → inv q ⋆ x
--                      })
--                    (glue
--                   (λ { (i = i0) → (q ⋆ inv q) ⋆ x
--                      ; (i = i1) → inv q ⋆ x
--                      }) (hcomp 
--             (λ j → λ {(i = i0) → ⋆Assoc (inv q) (⋆InvR q (~ j) ⋆  x) p (~ j) 
--                ;(i = i1) → inv q ⋆ x
--                }) ((hcomp 
--             (λ j → λ {(i = i0) → inv q ⋆ (⋆IdL x (~ j) ⋆ p) 
--                ;(i = i1) → inv q ⋆ x
--                      }) (inv q ⋆ unglue (i ∨ ~ i) x)
--                  )) 
--                  ))
   

--  fwgCodeeR : ∀ {x y y' z} → (q : Hom[ x , y ]) (p : Hom[ y' , z ]) →
--                PathP
--       (λ i₁ → ua (wg⋆≃Post {x = y} p) i₁ → ua (wg⋆≃Post p ∙ₑ wg⋆≃Pre (inv q)) i₁)
--       (wg⋆≃Pre q .fst)
--       (idfun Hom[ y , z ])
--  fwgCodeeR q p i x =
--                       (glue
--                   (λ { (i = i0) → q ⋆ x
--                      ; (i = i1) → x
--                      }) (hcomp
--             (λ j → λ { (i = i0) → inv q ⋆ ⋆Assoc q x p (~ j) --⋆Assoc (inv q) (q ⋆ x) p j
--                      ; (i = i1) → x
--                      }) (hcomp
--             (λ j → λ { (i = i0) → ⋆Assoc (inv q) q (x ⋆ p) j
--                      ; (i = i1) → x
--                      }) (hcomp
--             (λ j → λ { (i = i0) → ⋆InvL q (~ j) ⋆ (x ⋆ p)
--                      ; (i = i1) → x
--                      }) (⋆IdL (unglue (i ∨ ~ i) x) i)))) )
 
--  fwgCodee : FWG → FWG → Type ℓg'
--  fwgCodee [[ x ]] y = fwgCode x y
--  fwgCodee ([[[ q ]]] i) [[ y ]] = fwgPreCode ([[[ q ]]] i) y
--  fwgCodee ([[[_]]] {x} {y} q i) ([[[_]]] {y'} {z} p j) =
--    -- compPath→Square {p = ua ((wg⋆≃Post p))} {q = ua (Iso.isoToEquiv (wg⋆IsoPost p))}
--    --    {r = ua (Iso.isoToEquiv (wg⋆IsoPre (inv q)))} {s = ua (Iso.isoToEquiv (wg⋆IsoPre (inv q)))} 
--    --   (sym (uaCompEquiv (wg⋆≃Post p) (wg⋆≃Pre (inv q)))
--    --    ∙∙ cong ua (sym (pre-post (inv q) p))
--    --    ∙∙ uaCompEquiv (wg⋆≃Pre (inv q)) (wg⋆≃Post p)) j i
   
--    Glue (ua (pre-post (inv q) p i) j)
--      λ { (i = i0) → ua (wg⋆≃Post {x = x} {y = y'} {z = z} p) j ,
--                      equivPathP {A = λ j → ua (wg⋆≃Post p) j}
--                                 {B = λ j → (ua (pre-post (inv q) p i) j)}
--                                 {e = wg⋆≃Pre {z = y'}
--                           (inv q) ∙ₑ wg⋆≃Pre {z = y'} q} {f = wg⋆≃Pre {x = y} {z = z} (inv q)}
--                           (fwgCodeeL q p)
--                            j
--         ; (i = i1) → ua (wg⋆≃Post {x = y} {y = y'} {z = z} p) j ,
--          equivPathP {A = λ j → ua (wg⋆≃Post p) j}
--                      {B = λ j → ua (wg⋆≃Post p ∙ₑ wg⋆≃Pre (inv q)) j}
--                      {e = compEquiv (idEquiv Hom[ y , y' ]) (wg⋆≃Pre q)}
--                      {f = idEquiv _}
--                      (fwgCodeeR q p) j

--         ; (j = i0) → ua (wg⋆≃Pre {x = y} {z = y'} (inv q)) i ,
--                     ua-unglueEquiv (wg⋆≃Pre {x = y} {z = y'} (inv q)) i
--                       ∙ₑ wg⋆≃Pre q
--         ; (j = i1) → ua (wg⋆≃Pre {x = y} {z = z} (inv q)) i ,
--                      ua-unglueEquiv (wg⋆≃Pre {x = y} {y = x} {z = z} (inv q)) i
--         } 

--  -- glueCodeeSq : ∀ {x y} q {y' z} p →
--  --     Hom[ y , z ] →
--  --      SquareP
--  --        (λ i j → fwgCodee ([[[_]]] {x} {y} q i) ([[[_]]] {y'} {z} p j))
--  --         {!!}
--  --         {!!}
--  --         {!!}
--  --         {!!}
--  -- glueCodeeSq {x} {y} q {y'} {z} p f i j = {!!}
--    -- let zz = comp (λ k → hfill (λ k → compPath→Square-faces
--    --                    (ua (wg⋆≃Post p))
--    --                    (ua (wg⋆≃Post p))
--    --                    (ua (wg⋆≃Pre (inv q)))
--    --                    (ua (wg⋆≃Pre (inv q)))
--    --                    i j (~ k))
--    --                     (inS {!(sym (uaCompEquiv (wg⋆≃Post p) (wg⋆≃Pre (inv q)))
--    --    ∙∙ cong ua (sym (pre-post (inv q) p))
--    --    ∙∙ uaCompEquiv (wg⋆≃Pre (inv q)) (wg⋆≃Post p)) j i!})
--    --                  --    (inS ((sym (uaCompEquiv (wg⋆≃Post p) (wg⋆≃Pre (inv q)))
--    --                  --  ∙∙ cong ua (sym (pre-post (inv q) p))
--    --                  -- ∙∙ uaCompEquiv (wg⋆≃Pre (inv q)) (wg⋆≃Post p)) j i))
--    --              (~ k))
--    --                 (λ k →
--    --           λ { (i = i0) → {!!}
--    --             ; (i = i1) → {!!}
--    --             -- ; (j = i0) → {!!}
--    --             -- ; (j = i1) → {!!}
--    --             })
--    --        {!!}
--    -- in zz   
--     -- glue (λ { (i = i0) → glue (λ {(j = i0) → {!!} ; (j = i1) → {!!} })
--     --                      {!!}
--     --        ; (i = i1) → glue (λ {(j = i0) → {!!} ; (j = i1) → ? })
--     --                      {!!}

--     --        ; (j = i0) → glue (λ {(i = i0) → {!!} ; (i = i1) → {!!} })
--     --                      {!!}
--     --        ; (j = i1) → glue (λ {(i = i0) → {!!} ; (i = i1) → {!!}})
--     --                      {!!}
--     --        })
           
--     --        (glue ((λ { (j = i0) → {!!} ;
--     --                     (j = i1) → ?
--     --             }))
--     --         (hcomp (λ z → λ { (j = i0) → ⋆Assoc (inv q) {!!} p i
--     --              ; (j = i1) → {!!} })
--     --             (⋆Assoc (inv q) (q ⋆ (f ⋆ inv p)) p i)))

--  fwgCodeeInv : ∀ x y → fwgCodee x y → fwgCodee y x 
--  fwgCodeeInv [[ x ]] [[ x₂ ]] x₁ = inv x₁
--  fwgCodeeInv [[ x ]] ([[[ x₂ ]]] i) x₁ =
--    let x₁' = ua-unglue (wg⋆≃Post x₂) i x₁
--    in glue (λ { (i = i0) → inv x₁ ;
--                 (i = i1) → inv x₁'
--                 })
--                 (hcomp (λ j →
--                 (λ { (i = i0) → distInv x₁ x₂ j ;
--                      (i = i1) → inv x₁'
--                 }) ) (inv x₁'))
--  fwgCodeeInv ([[[ x ]]] i) [[ x₂ ]] x₁ =
--    let x' = ua-unglue (wg⋆≃Pre (inv x)) i x₁
--    in glue (λ { (i = i0) → inv x₁ ;
--                 (i = i1) → inv x₁
--                 })
--                  (hcomp (λ j →
--                 (λ { (i = i0) → (distInv (inv x) x₁ ∙ cong (inv x₁ ⋆_) (invol-inv x)) j  ;
--                      (i = i1) → inv x₁
--                 }) ) (inv x'))
  
--  fwgCodeeInv ([[[_]]] {x} {y} q i) ([[[_]]] {y'} {z} p j) v =
--    let v* = (unglue (i ∨ ~ i ∨ j ∨ ~ j) v)
--        v' : Hom[ y , z ]
--        v' = unglue (j ∨ ~ j) v*
--    in glue (λ { (i = i0) →
--               glue (λ { (j = i0) → inv v*
--                       ; (j = i1) → inv v
--                       }) {!!}
--            ; (i = i1) →
--               glue (λ { (j = i0) → inv v
--                       ; (j = i1) → inv v'
--                       }) {!!}

--            ; (j = i0) →
--               glue (λ { (i = i0) → inv v*
--                       ; (i = i1) → inv v
--                       }) {!!}
--            ; (j = i1) →
--               glue (λ { (i = i0) → inv v
--                       ; (i = i1) → inv v'
--                       }) {!!}
--            })
--          (      glue (λ { (i = i0) → p ⋆ {!!}
--                       ; (i = i1) → {!!}
--                       }) {!inv v'!} )
 
--    -- let v* = (unglue (i ∨ ~ i ∨ j ∨ ~ j) v)
--    --     v' = unglue (j ∨ ~ j) v*
--    -- in {!v!}

-- -- glue (λ { (i = i0) → {!!}
-- --         ; (i = i1) → {!!}

-- --         ; (j = i0) → {!!}
-- --         ; (j = i1) → {!!}
-- --         }) 

-- --         (glue (λ { (i = i0) → {!!}
-- --              ; (i = i1) → inv v'
-- --           }) (hcomp (λ k →
-- --                 (λ { (i = i0) → ⋆Assoc (inv p) (p ⋆ (inv v' ⋆ inv q)) q j  ;
-- --                      (i = i1) → inv v' ;
-- --                      (j = i0) → {!!} --inv (inv q ⋆ ((v*) ⋆ p));
-- --                     ; (j = i1) → {!!} --inv v*
-- --                 }) ) {!!}))
 
--  idFWG : ∀ x → fwgCodee x x
--  idFWG [[ x ]] = id
--  idFWG ([[[_]]] {x} {y} f i) =
--   glue (λ { (i = i0) → _
--           ; (i = i1) → _
--           }) (glue (λ { (i = i0) → _
--           ; (i = i1) → _
--           }) (lem i))

--   where
--    lem : ((inv f ⋆ (f ⋆ (inv f ⋆ id))) ⋆ f) ≡ id
--    lem = (λ i → ⋆Assoc (inv f) (⋆Assoc f (inv f) id (~ i)) f i) ∙∙
--             (λ i → (inv f ⋆ (⋆IdR (⋆InvR f i) i ⋆ f))) ∙
--               (λ i → inv f ⋆ ⋆IdL f i) ∙∙ ⋆InvL f
  
--  -- compFWG : ∀ {x y z} → fwgCodee x y → fwgCodee y z → fwgCodee x z
--  -- -- compFWG {x} {y} {z} = {!!}
--  -- compFWG {[[ x ]]} {[[ x₁ ]]} {[[ x₂ ]]} g h = g ⋆ h
--  -- compFWG {[[ x ]]} {[[ x₁ ]]} {[[[ x₂ ]]] i} g h = {!!}
--  --   -- ua-glue (wg⋆≃Post x₂) i (λ { (i = i0) → g ⋆ h })
--  --   --   (inS (((g ⋆ {!ua-unglue (wg⋆≃Post x₂) i h!}) ⋆ x₂))) 
--  -- compFWG {[[ x ]]} {[[[ x₁ ]]] i} {[[ x₂ ]]} g h = {!!}
--  -- compFWG {[[ x ]]} {[[[ x₁ ]]] i} {[[[ x₂ ]]] i₁} g h = {!!}
--  -- compFWG {[[[ x ]]] i} {[[ x₁ ]]} {[[ x₂ ]]} g h = {!!}
--  -- compFWG {[[[ x ]]] i} {[[ x₁ ]]} {[[[ x₂ ]]] i₁} g h = {!!}
--  -- compFWG {[[[ x ]]] i} {[[[ x₁ ]]] i₁} {[[ x₂ ]]} g h = {!!}
--  -- compFWG {[[[ x ]]] i} {[[[ x₁ ]]] i₁} {[[[ x₂ ]]] i₂} g h = {!!}

-- -- --  -- fwgCodeInv : ∀ x y z →  (f : [[ y ]] ≡  [[ x ]]) → ∀ g →
-- -- --  --      subst (fwgCode z) (sym f) g ≡
-- -- --  --      ({!subst (fwgCode ?) f ?!})
-- -- --  -- fwgCodeInv x y z f _ = {!!}


--  -- fwgCodeId : ∀ x → fwgCode x [[ x ]] 
--  -- fwgCodeId _ = id
 
--  -- fwgCodeInv : ∀ x y →  (p : [[ y ]] ≡ [[ x ]]) →
--  --      subst (fwgCode x) (sym p) (id) ≡
--  --      inv (subst (fwgCode y) p (id))
--  -- fwgCodeInv = {!!}

--  fwgCode' : ∀ {x y} →  [[ x ]] ≡ y → fwgCode x y 
--  fwgCode' {x} = J (λ y p → fwgCode x y) id

--  fwgCode'' : ∀ {x y} →  [[ x ]] ≡ [[ y ]] → Hom[ x , y ] 
--  fwgCode'' {x} = fwgCode'


--  fwgDeCode' : ∀ {x y} →  Hom[ x , y ] → [[ x ]] ≡ [[ y ]] 
--  fwgDeCode' {x} = [[[_]]]

--  lInv : ∀ {x y} → (f : Hom[ x , y ]) → fwgCode'' (fwgDeCode' f) ≡ f 
--  lInv f i = transportRefl (⋆IdL f i) i 
 
--  fromS≡ : ∀ {x y} → (f g  : Hom[ x , y ]) → fwgDeCode' f ≡ fwgDeCode' g → f ≡ g  
--  fromS≡ f g p = sym (lInv f) ∙∙ cong fwgCode'' p ∙∙ lInv g


--  fwgCode'M : ∀ {x y} →  x ≡ [[ y ]] → fwgCodee x [[ y ]] 
--  fwgCode'M {y = y} = J (λ x _ → fwgCodee x [[ y ]])
--    id Fu.∘ sym





--  mkFwgCodee : ∀ x y → x ≡ y → fwgCodee x y
--  mkFwgCodee x y = J (λ y _ → fwgCodee x y) (idFWG x)
 
--  _⋆Mid_ : ∀ {x y z} → fwgCode x y → fwgCodee y [[ z ]] → fwgCode x  [[ z ]]
--  _⋆Mid_ {x} {[[ x₁ ]]} {z} f g = f ⋆ g
--  _⋆Mid_ {x} {[[[ x₁ ]]] i} {z} f g =
--   let g' = ua-unglue (wg⋆≃Pre (inv x₁)) i g
--       f' = ua-unglue (wg⋆≃Post x₁) i f
--       -- f'⋆g' = 
--    in hcomp (λ j → λ {(i = i0) → f ⋆ ⋆IdL g j
--                      ;(i = i1) → f ⋆ g
--                      }) (hcomp (λ j → λ {(i = i0) → f ⋆ (⋆InvR x₁ j ⋆ g)
--                      ;(i = i1) → f ⋆ g
--                      }) (hcomp (λ j → λ {(i = i0) → f ⋆ ⋆Assoc x₁ (inv x₁) g (~ j)
--                      ;(i = i1) → f ⋆ g
--                      }) (hcomp (λ j → λ {(i = i0) → ⋆Assoc f x₁ (inv x₁ ⋆ g) j
--                      ;(i = i1) → f ⋆ g
--                      }) (f' ⋆ g'))))


--  _⋆Midd_ : ∀ {x y z} → fwgCode x y → fwgCodee y z → fwgCode x z
--  _⋆Midd_ {x} {y} {z = [[ x₂ ]]} = _⋆Mid_ {x = x} {y = y} {z = x₂}
--  _⋆Midd_ {y = [[ x₃ ]]} {z = [[[_]]] {y = y} x₂ i} x x₁ =
--    let x₁' = ua-unglue (wg⋆≃Post x₂) i x₁
--    in glue (λ {(i = i0) → x ⋆ x₁
--               ;(i = i1) → x ⋆ x₁'
--               }) (hcomp (λ j → λ {(i = i0) → ⋆Assoc x x₁ x₂ (~ j)
--                      ;(i = i1) → x ⋆ x₁'
--                      }) (x ⋆ x₁') )
--  _⋆Midd_ {x = x} {y = [[[ x₃ ]]] i₁} {z = [[[_]]] {y = y} x₂ i} f g =
--    {!!}
    
--  fwgCode''∙0 : ∀ {x y z} → (p : [[ x ]] ≡ y) → (q : y ≡ z) →
--     fwgCode' (p ∙ q) ≡
--       (_⋆Midd_ {y = y} {z = z} (fwgCode' p)  (mkFwgCodee _ _ q))
--  fwgCode''∙0 {x = x} {z = z} =
--    J (λ y p → (q : y ≡ z) →
--     fwgCode' (p ∙ q) ≡
--       (_⋆Midd_ {y = y} {z = z} (fwgCode' p)  (mkFwgCodee _ _ q)))
--        (J (λ z q → fwgCode' (refl ∙ q) ≡
--       (_⋆Midd_ {y = _} {z = z} (fwgCode' refl)  (mkFwgCodee _ _ q)))
--        ((λ i → transp (λ j → Hom[ x , x ]) i
--       (transp (λ i → Hom[ x , x ]) i
--        (transp (λ i → Hom[ x , x ]) i id))) ∙∙ sym (⋆IdL id) ∙∙
--         λ i → (transp (λ i → Hom[ x , x ]) (~ i) id ⋆
--        transp (λ i → Hom[ x , x ]) (~ i) id)))


--  fwgCode''∙ : ∀ {x y z} → (p : [[ x ]] ≡ [[ y ]]) → (q : [[ y ]] ≡ [[ z ]]) →
--     fwgCode'' (p ∙ q) ≡
--       (fwgCode'' p ⋆ fwgCode'' q)
--  fwgCode''∙ {x} {y} {z} p q = 
--   fwgCode''∙0 {x} {[[ y ]]} {[[ z ]]} p q 

--  fwgCode''inv0 : ∀ {x y} → (p : [[ x ]] ≡ y) →
--     fwgCodeeInv [[ x ]] y (fwgCode' p) ≡
--       (fwgCode'M (sym p))
--  fwgCode''inv0 {x = x} = J (λ y p → fwgCodeeInv [[ x ]] y (fwgCode' p) ≡
--       (fwgCode'M (sym p)))
--         (cong inv (transportRefl _)
--          ∙∙ id≡inv-id
--          ∙∙ sym (transportRefl _))


--  fwgCode''invLem :  ∀ {x y} → (p : x ≡ [[ y ]])
--    → transp (λ i → fwgCodee (p i) x) i0 (idFWG x) ≡
--       transp (λ i → fwgCode y (p (~ i))) i0 id
--  fwgCode''invLem {x} {y} =
--   J (λ x (p : [[ y ]] ≡ x) → 
--      transp (λ i → fwgCodee (p (~ i)) x) i0 (idFWG x) ≡
--       transp (λ i → fwgCode y (p i)) i0 id) refl Fu.∘ sym
 
--  fwgCode''inv : ∀ {x y} → (p : [[ x ]] ≡ [[ y ]]) →
--     inv (fwgCode'' p) ≡
--       (fwgCode'' (sym p))
--  fwgCode''inv p = fwgCode''inv0 p ∙ fwgCode''invLem p
 
--  data GrpExpr : (x y : ob) → Type (ℓ-max ℓg ℓg') where
--   idE : ∀ {x} → GrpExpr x x 
--   _⋆E_ : ∀ {x y z} → GrpExpr x y → GrpExpr y z → GrpExpr x z
--   invE : ∀ {x y} → GrpExpr x y → GrpExpr y x
--   [[_]]E : ∀ {x y} → Hom[ x , y ] → GrpExpr x y


--  GrpExpr→WG : ∀ {x y} → GrpExpr x y → Hom[ x , y ] 
--  GrpExpr→WG idE = id
--  GrpExpr→WG (x ⋆E x₁) = GrpExpr→WG x ⋆ GrpExpr→WG x₁
--  GrpExpr→WG (invE x) = inv (GrpExpr→WG x)
--  GrpExpr→WG [[ x ]]E = x
 
--  GrpExpr→FWG : ∀ {x y} → GrpExpr x y → [[ x ]] ≡ [[ y ]] 
--  GrpExpr→FWG idE = refl
--  GrpExpr→FWG (x ⋆E x₁) = GrpExpr→FWG x ∙ GrpExpr→FWG x₁
--  GrpExpr→FWG (invE x) = sym (GrpExpr→FWG x)
--  GrpExpr→FWG [[ x ]]E = [[[ x ]]]


--  GrpExpr→FWG≡WG : ∀ {x y} → ∀ f →  fwgCode'' {x} {y} (GrpExpr→FWG f) ≡ GrpExpr→WG f 
--  GrpExpr→FWG≡WG idE = transportRefl _
--  GrpExpr→FWG≡WG {x} (f ⋆E f₁) =    
--      fwgCode''∙ (GrpExpr→FWG f) (GrpExpr→FWG f₁) ∙ 
--       cong₂ _⋆_ (GrpExpr→FWG≡WG f) (GrpExpr→FWG≡WG f₁)   
--  GrpExpr→FWG≡WG (invE f) =
--        sym (fwgCode''inv ( (GrpExpr→FWG f))) ∙
--          cong inv (GrpExpr→FWG≡WG f)
--  GrpExpr→FWG≡WG [[ x ]]E = lInv x

-- -- --  module Example (x y z w : ob) (p p' : Hom[ x , y ]) (q : Hom[ y , z ])
-- -- --                   (q' : Hom[ z , y ]) (r : Hom[ w , z ]) where

-- -- --   pA pB pC : Hom[ x , w ]
-- -- --   pA = (p ⋆ (id ⋆ q)) ⋆ inv r
-- -- --   pB = ((((p ⋆ ((q ⋆ inv (inv r ⋆  r)) ⋆ inv q)) ⋆ (q ⋆ id))) ⋆ inv r) ⋆ id
-- -- --   pC = ((id ⋆ p') ⋆ ((q ⋆ inv q) ⋆ (inv p' ⋆ p))) ⋆ ((q ⋆ inv q) ⋆ (q ⋆ inv r))



-- -- --  -- codeIso : ∀ {x y} → Iso.Iso Hom[ x , y ] ([[ x ]] ≡ [[ y ]])  
-- -- --  -- Iso.Iso.fun codeIso = [[[_]]]
-- -- --  -- Iso.Iso.inv codeIso = fwgCode'
-- -- --  -- Iso.Iso.rightInv (codeIso {x = x}) = {!!}
-- -- --  --   --J (λ y b → [[[ transp (λ i → fwgCode x (b i)) i0 id ]]] ≡ b) {!!}
-- -- --  -- Iso.Iso.leftInv codeIso a = transportRefl _ ∙ ⋆IdL a

-- -- -- -- module _ (G : Graph ℓg ℓg') where

-- -- -- --  data FWG (x : G .Node) : Type (ℓ-max ℓg ℓg') where 
-- -- -- --   [[_]] :  ∀ {y} → G .Edge x y →  FWG x 
-- -- -- --   [[_↔_]] : ∀ {y z} → {!G .Edge y z!} → {!!}
  
-- -- -- -- FreeWG : (G : Graph ℓg ℓg') → WildGroupoid ℓg (ℓ-max ℓg ℓg')
-- -- -- -- ob (WildGroupoid.wildCat (FreeWG G)) = G .Node
-- -- -- -- Hom[ WildGroupoid.wildCat (FreeWG G) , x ] y = R.Path G x y
-- -- -- -- id (WildGroupoid.wildCat (FreeWG G)) = R.pnil
-- -- -- -- _⋆_ (WildGroupoid.wildCat (FreeWG G)) = R.ccat _
-- -- -- -- ⋆IdL (WildGroupoid.wildCat (FreeWG G)) = R.pnil++ _
-- -- -- -- ⋆IdR (WildGroupoid.wildCat (FreeWG G)) _ = refl
-- -- -- -- ⋆Assoc (WildGroupoid.wildCat (FreeWG G)) = R.++assoc G
-- -- -- -- WildGroupoid.inv (FreeWG G) = R.invPath G
-- -- -- -- WildGroupoid.·InvR (FreeWG G) = {!!}
-- -- -- -- WildGroupoid.·InvL (FreeWG G) = {!!}

-- -- -- -- inducedFunctor : (G : Graph ℓg ℓg') (C : WildCat ℓc ℓc')
-- -- -- --                → (g : GraphHom G (Cat→Graph C))
-- -- -- --                → WildFunctor (Free G) C
-- -- -- -- inducedFunctor G C g = F
-- -- -- --   where
-- -- -- --     open GraphHom
-- -- -- --     F : WildFunctor (Free G) C
-- -- -- --     F-ob  F x = g $g x
-- -- -- --     F-hom F f = {!comcatList (map (g <$g>_) (PathToList f))!}
-- -- -- --     F-id  F = {!!}
-- -- -- --     F-seq F = {!!}
