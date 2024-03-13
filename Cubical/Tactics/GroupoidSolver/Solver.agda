{-# OPTIONS --safe  #-}

module Cubical.Tactics.GroupoidSolver.Solver where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function as Fu
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.List as Li
open import Cubical.Data.Maybe as Mb


open import Cubical.HITs.Interval

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.GroupoidSolver.Reflection
open import Cubical.Tactics.Reflection
open import Agda.Builtin.String

-- open import Cubical.WildCat.WGE
open import Cubical.WildCat.Base


private
  variable
    ℓ ℓ' : Level

unfoldMaybe : ℕ → ∀ {ℓ} {A : Type ℓ} → (A → Maybe A) → A → List A  
unfoldMaybe zero _ _ = []
unfoldMaybe (suc x) f a =
  Mb.rec [] (λ a' → a' ∷ unfoldMaybe x f a') (f a)

data 𝑵𝒐𝒅𝒆 : Type where
 𝒐𝒑 𝒂𝒕𝒐𝒎 𝒄𝒐𝒏𝒔 𝒊𝒏𝒗 𝒊𝒏𝒗𝒐𝒍 𝒊𝒏𝒗𝑨𝒕𝒐𝒎 : 𝑵𝒐𝒅𝒆

module Nodes (ob : Type ℓ) (Hom[_,_] : ob → ob → Type ℓ') (hasInvs : Bool) where

 𝒏 : ℕ → 𝑵𝒐𝒅𝒆 → Bool
 
 𝒏 0 𝒐𝒑 = true
 𝒏 0 𝒊𝒏𝒗 = hasInvs
 
 𝒏 0 𝒄𝒐𝒏𝒔 = false
 𝒏 0 𝒂𝒕𝒐𝒎 = true
 𝒏 0 𝒊𝒏𝒗𝒐𝒍 = false
 𝒏 0 𝒊𝒏𝒗𝑨𝒕𝒐𝒎 = false

 𝒏 (suc _) 𝒊𝒏𝒗 = false
 𝒏 1 𝒐𝒑 = true
 𝒏 1 𝒄𝒐𝒏𝒔 = false
 𝒏 1 𝒂𝒕𝒐𝒎 = true
 𝒏 1 𝒊𝒏𝒗𝒐𝒍 = false
 𝒏 (suc _) 𝒊𝒏𝒗𝑨𝒕𝒐𝒎 = hasInvs

 𝒏 (suc (suc _)) 𝒐𝒑 = false
 𝒏 (suc (suc _)) 𝒄𝒐𝒏𝒔 = true
 𝒏 (suc (suc _)) 𝒊𝒏𝒗𝒐𝒍 = hasInvs
 𝒏 (suc (suc _)) 𝒂𝒕𝒐𝒎 = false


 open BinaryRelation Hom[_,_] public


 module _ (k : ℕ) where
  N : 𝑵𝒐𝒅𝒆 → Type
  N = Bool→Type Fu.∘ 𝒏 k

  data Atom : ob → ob → Type (ℓ-max ℓ ℓ') where
   a⟦_⟧  : ∀ {x y} → Hom[ x , y ] → Atom x y
   a⟦_⟧⁻ : ∀ {x y} → {invG : N 𝒊𝒏𝒗𝑨𝒕𝒐𝒎}  → Hom[ y , x ] → {Bool→Type hasInvs} → Atom x y

  Atom→𝟚×H : ∀ {x y} → Atom x y → Σ Bool λ { true → Hom[ x , y ] ; false → Hom[ y , x ] }  
  Atom→𝟚×H a⟦ x ⟧ = true , x
  Atom→𝟚×H a⟦ x ⟧⁻ = false , x
  
  data Node' : ob → ob → Type (ℓ-max ℓ ℓ') 
  data Node : ob → ob → Type (ℓ-max ℓ ℓ') where
   idN : ∀ {x} → Node x x
   atomN : ∀ {x y} → {aGuard : N 𝒂𝒕𝒐𝒎} → Atom x y → Node x y
   no : ∀ {x y} → Node' x y → Node x y

  data Node' where
   _∷N_ : ∀ {x y z} → {∷Guard : N 𝒄𝒐𝒏𝒔} → Node x y → Atom y z → Node' x z
   _⋆N_ : ∀ {x y z} → {⋆Guard : N 𝒐𝒑} → Node x y → Node y z → Node' x z
   invN : ∀ {x y} → {invGuard : N 𝒊𝒏𝒗} → Node y x →  {Bool→Type hasInvs} → Node' x y
   involN : ∀ {x y z} → {g : N 𝒊𝒏𝒗𝒐𝒍} → Node x y → Atom y z → {Bool→Type hasInvs} → Node' x y


 _a⤋_ : ∀ k → ∀ {x y} → Atom k x y → Atom (suc k) x y
 k a⤋ a⟦ x ⟧ = a⟦ x ⟧
 k a⤋ (a⟦ x ⟧⁻ {g}) = a⟦_⟧⁻ {_} {_} {_} {g} x {g}


 _N2++_ : ∀ {x y z k} → Node (suc (suc k)) x y
                      → Node (suc (suc k)) y z
                      → Node (suc (suc k)) x z
 x N2++ idN = x
 x N2++ atomN x₁ = no (x ∷N x₁)
 x N2++ no (x₁ ∷N x₂) = no ((x N2++ x₁) ∷N x₂) 
 x N2++ no (involN {g = g} x₁ x₂ {uuu}) = no (involN {g = g} (x N2++ x₁)  x₂ {uuu})


 invAtom : ∀ {x y} k {k'} → (Bool→Type hasInvs) → Atom k x y → Atom (suc k') y x
 invAtom k x a⟦ x₁ ⟧ = a⟦_⟧⁻ {_} {_} {_} {x} x₁ {x}
 invAtom k x a⟦ x₁ ⟧⁻ = a⟦ x₁ ⟧
 
 invNode : ∀ {x y k} → {hi : Bool→Type hasInvs} → Node k x y → Node k y x
 invNode' : ∀ {x y k} → {hi : Bool→Type hasInvs} → Node' k x y → Node k y x

 invNode' {k = k} {x} (_⋆N_ {⋆Guard = ⋆Guard} x₁ x₂) =
   no (_⋆N_ {⋆Guard = ⋆Guard} (invNode {hi = x} x₂)  (invNode {hi = x} x₁))
 invNode' {k = k} {x} (invN {invGuard = invGuard} x₁) = x₁
 invNode' {k = suc (suc k)} {x} (involN {g = gg} x₁ x₂ {g}) =
   no (involN {g = gg} idN (x₂) {g})  N2++ invNode {hi = x} x₁
 invNode' {k = suc (suc k)} {x} (x₁ ∷N x₂) =
   no (idN ∷N invAtom _ x x₂)  N2++ invNode {hi = x} x₁
 invNode {k = k} {x} idN = idN
 invNode {k = zero} {x} (atomN {aGuard = g} x₁) =
   no (invN {invGuard = x} (atomN {aGuard = g} x₁) {x})
 invNode {k = suc k} {x} (atomN {aGuard = g} x₁) = 
   atomN {aGuard = g} (invAtom _ x x₁)
 invNode {k = k} {x} (no x₁) = invNode' {hi = x} x₁


 invNode* : ∀ {x y k} → {hi : Bool→Type hasInvs} → Node k x y → Node k y x 
 invNode* {k = zero} {hi} f = no (invN {invGuard = hi} f {hi})
 invNode* {k = suc k} {hi} = invNode {k = suc k} {hi}
 

 len : ∀ {x y} → Node 2 x y → ℕ
 len idN = 0
 len (no (x ∷N x₁)) = suc (len x)
 len (no (involN x x₁)) = suc (suc (len x))
 
 module _ {k} (showH : {a₀ a₁ : ob} → (p : Hom[ a₀ , a₁ ]) → String) where

  showA showA' : {a₀ a₁ : ob} → Atom k a₀ a₁ → String
  showA a⟦ x ⟧ = showH x
  showA a⟦ x ⟧⁻ = "(" <> showH x <>  ")⁻¹"
  showA' a⟦ x ⟧ = "(" <> showH x <>  ")⁻¹"   
  showA' a⟦ x ⟧⁻ = showH x

  showN : {a₀ a₁ : ob} → Node k a₀ a₁ → String
  showN' : {a₀ a₁ : ob} → Node' k a₀ a₁ → String

  showN idN = "id"
  showN (atomN x) = showA x
  showN (no x) = showN' x

  showN' (x ∷N x₁) = showN x <> "⋆" <> showA x₁
  showN' (x ⋆N x₁) = "(" <> showN x <> "⋆" <> showN x₁ <> ")"
  showN' (invN x) = "(" <> showN x <>  ")⁻¹"
  showN' (involN x x₁ {v}) = showN x <>
    "⋆⟦" <> showA x₁ <> "⋆" <> showA' x₁  <> "⟧"


 _⤋'_ : ∀ k → ∀ {x y} → Node' k x y → Node (suc k) x y  

 _⤋_ : ∀ k → ∀ {x y} → Node k x y → Node (suc k) x y  
 k ⤋ idN = idN
 zero ⤋ atomN x = atomN (0 a⤋ x)
 suc zero ⤋ atomN x = no (idN ∷N (_ a⤋ x))
 k ⤋ no x = (k ⤋' x)

 suc (suc k) ⤋' (x ∷N x₁) = no ((suc (suc k) ⤋ x) ∷N (suc (suc k) a⤋ x₁))
 zero ⤋' (x ⋆N x₁) = no ((0 ⤋ x) ⋆N (0 ⤋ x₁))
 suc zero ⤋' (x ⋆N x₁) =
  (suc zero ⤋ x) N2++ (suc zero ⤋ x₁) 
 zero ⤋' invN x {hi} = invNode {hi = hi} (zero ⤋ x)

 suc (suc k) ⤋' involN {_} {_} {_} {zz} x x₁ {zzz} =
  no (involN {_} {_} {_} {_} {zz} (suc (suc k) ⤋ x) (suc (suc k) a⤋ x₁) {zzz})

 _⤋⁺_ : ∀ {k} m → ∀ {x y} → Node k x y → Node (m + k) x y  
 zero ⤋⁺ x = x
 suc m ⤋⁺ x = (m + _) ⤋ (m ⤋⁺ x)

 red[_,_] : ∀ k → ∀ {x y} → Node k x y → Node k x y  
 red[ zero , f ] = f
 red[ suc zero , f ] = f
 red[ suc (suc k) , idN ] = idN
 red[ suc (suc k) , no (x ∷N x₁) ] =
  no (red[ suc (suc k) , x ] ∷N x₁)
 red[ suc (suc k) , no (involN x x₁) ] = red[ suc (suc k) , x ]

 

 module Ev (id : isRefl')
           (_⋆_ : isTrans')
           (inv : {_ : Bool→Type hasInvs} → isSym') where 


  eva[_] : ∀ {k} → ∀ {x y} → Atom k x y → Hom[ x , y ]
  eva[ a⟦ x ⟧ ] = x
  eva[ a⟦ x ⟧⁻ {invGuard} ] = inv {invGuard} x

  ev[_] : ∀ {k} → ∀ {x y} → Node k x y → Hom[ x , y ]
  ev[_]b : ∀ {k} → ∀ {x y} → Node k x y → Bool → Hom[ x , y ]

  ev[ f ] = ev[ f ]b false 
  
 
  ev[ idN ]b _ = id
  ev[ atomN x ]b _ = eva[ x ]
  ev[ no (xs ∷N x) ]b b = ev[ xs ]b b ⋆ eva[ x ]
  ev[ no (x ⋆N x₁) ]b b = ev[ x ]b b ⋆ ev[ x₁ ]b b
  ev[ no (invN x {invGuard}) ]b b = inv {invGuard} (ev[ x ]b b)
  ev[ no (involN x x₁ {invGuard}) ]b false = (ev[ x ] ⋆ eva[ x₁ ]) ⋆
    eva[ invAtom _ {1} invGuard  x₁  ]
  ev[ no (involN x x₁) ]b true = ev[ x ]b true

  module Ev' (⋆Assoc : ∀ {u v w x}
                  (f : Hom[ u , v ])
                  (g : Hom[ v , w ])
                  (h : Hom[ w , x ])
                → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h))
             (⋆IdR : ∀ {x y} (f : Hom[ x , y ]) → f ⋆ id ≡ f)
             (⋆IdL : ∀ {x y} (f : Hom[ x , y ]) → id ⋆ f ≡ f)
             (⋆InvR : ∀ {x y hi} → (f : Hom[ x , y ]) → f ⋆ inv {hi} f ≡ id)
             (⋆InvL : ∀ {x y hi} → (f : Hom[ x , y ]) → inv {hi} f ⋆ f ≡ id)
       where

   evInv : ∀ {k} → ∀ {x y hi} → (f : Atom k x y) →
             id ≡ (eva[ f ] ⋆ eva[ invAtom k {1} hi f ])
   evInv a⟦ x ⟧ = sym (⋆InvR x)
   evInv a⟦ x ⟧⁻ = sym (⋆InvL x) 
   
   ev[_]≡ : ∀ {k} → ∀ {x y} → (f : Node k x y) → ev[ f ]b false ≡  ev[ f ]b true
   ev[ idN ]≡ = refl
   ev[ atomN x ]≡ = refl
   ev[ no (x ∷N x₁) ]≡ = cong (_⋆ eva[ x₁ ]) ev[ x ]≡
   ev[ no (x ⋆N x₁) ]≡ = cong₂ _⋆_ ev[ x ]≡ ev[ x₁ ]≡ 
   ev[ no (invN x) ]≡ = cong inv ev[ x ]≡
   ev[ no (involN x x₁) ]≡ = 
        ⋆Assoc _ _ _
     ∙∙ cong₂ _⋆_ ev[ x ]≡ (sym (evInv x₁))
     ∙∙ ⋆IdR _

   ev[_]₂≡ = ev[_]≡ {k = 2}


   evN2++b : ∀ {k} {a₀ a₁ a₂ : ob} b → (x : Node (suc (suc k)) a₀ a₁)
                                 → (x₁ : Node (suc (suc k)) a₁ a₂)
            → ev[ x ]b b ⋆ ev[ x₁ ]b b ≡ ev[ x N2++ x₁ ]b b
   evN2++b b x idN = ⋆IdR _
   evN2++b b x (no (x₁ ∷N x₂)) =
      sym (⋆Assoc _ _ _)
      ∙ cong (_⋆ eva[ x₂ ]) (evN2++b b x x₁)
   evN2++b false x (no (involN x₁ x₂)) =
     sym (⋆Assoc _ _ _)
    ∙∙ congS (_⋆ eva[ invAtom _ _ x₂ ]) (sym (⋆Assoc _ _ _))
    ∙∙ congS (λ y → ((y ⋆ eva[ x₂ ]) ⋆ eva[ invAtom _ _ x₂ ])) (evN2++b false x x₁)

   evN2++b true x (no (involN x₁ x₂)) = evN2++b true x x₁

   evN2++ : ∀ {k} {a₀ a₁ a₂ : ob}  → (x : Node (suc (suc k)) a₀ a₁)
                                 → (x₁ : Node (suc (suc k)) a₁ a₂)
            → ev[ x ] ⋆ ev[ x₁ ] ≡ ev[ x N2++ x₁ ]
   evN2++ = evN2++b false

   module Ev'' (id≡inv-id : ∀ {x hi} → id {x} ≡ inv {hi} id)
               (involInv : ∀ {x y hi hi'} → (f : Hom[ x , y ])  →
                 inv {hi} (inv {hi'} f) ≡ f)
               (distInv : ∀ {x y z hi}
                  (f : Hom[ x , y ])
                  (g : Hom[ y , z ])
                 → inv {hi} (f ⋆ g) ≡ inv {hi} g ⋆ inv {hi} f)
               where

    inv-eva : ∀ {x y} {k} {k'} a {hi} →
      inv {hi} {x} {y} (eva[_] {k} a) ≡ eva[ invAtom (k) {k'} hi a ]
    inv-eva a⟦ x ⟧ = refl
    inv-eva a⟦ x ⟧⁻ {hi} = involInv x

    invAtomInvol : ∀ {x y} k {hi hi'} → (x : Atom (suc (suc k)) x y) →
          (eva[ invAtom 2 {suc k} (hi) (invAtom (suc (suc k)) {1} hi' x) ]) ≡ (eva[ x ])
    invAtomInvol k a⟦ x ⟧ = refl
    invAtomInvol k {hi} (a⟦ x ⟧⁻ {hi'}) i = inv {isPropBool→Type hi hi' i} x


    ev[_]≡inv : ∀ {k} → ∀ {x y} {hi} b → (f : Node k x y) →
              inv {hi} (ev[ f ]b b) ≡ ev[ invNode* {hi = hi} f ]b b
    ev[_]≡inv {zero} b f = refl
    ev[_]≡inv {suc k} {hi = hi} b idN = sym (id≡inv-id {hi = hi})
    ev[_]≡inv {suc zero} {hi = hi} b (atomN x) = inv-eva x {hi}
    ev[_]≡inv {suc zero} b (no (x ⋆N x₁)) =
       distInv (ev[ x ]b b) (ev[ x₁ ]b b) ∙
         cong₂ _⋆_ (ev[_]≡inv b x₁) (ev[_]≡inv b x)
    ev[_]≡inv {suc (suc k)} {hi = hi} b (no (x ∷N x₁)) =
          distInv (ev[ x ]b b) (eva[ x₁ ])
           ∙∙ cong₂ _⋆_ (λ i → ⋆IdL (inv-eva {k' = suc k} x₁ {hi} i) (~ i))
                (ev[_]≡inv b x)
           ∙∙ evN2++b b (no (idN ∷N invAtom (suc (suc k)) hi x₁)) (invNode x)
               
    ev[_]≡inv {suc (suc k)} {hi = hi} false (no (involN x x₁ {hi'})) =
          distInv (ev[ x ] ⋆ eva[ x₁ ]) (eva[ invAtom (suc (suc k)) hi' x₁ ]) 
       ∙∙
         cong₂ _⋆_
           (inv-eva {k' = suc k} (invAtom (suc (suc k)) hi' x₁))
           (distInv ev[ x ] eva[ x₁ ]) ∙
            (λ i → ⋆Assoc (⋆IdL (invAtomInvol k {hi} {hi'} x₁ i) (~ i))
               (inv-eva {k' = 1}  x₁ {isPropBool→Type hi hi' i} i)
               (ev[_]≡inv {suc (suc k)} {hi = hi} false x i) (~ i) )
       ∙∙ evN2++b false (no (involN idN x₁)) (invNode x)

    ev[_]≡inv {suc (suc k)} true (no (involN x x₁)) = 
      ev[_]≡inv true x 
       ∙∙ sym (⋆IdL _) 
       ∙∙ evN2++b true (no (involN idN x₁)) (invNode x)


   

  data NodeCase : {a₀ a₁ : ob} → Hom[ a₀ , a₁ ] → Type (ℓ-max ℓ ℓ') where
   idCase : ∀ {x} → NodeCase (id {a = x})
   opCase : ∀ {x y z : _} → (p : Hom[ x , y ]) (q : Hom[ y , z ]) → NodeCase (p ⋆ q)
   invCase : ∀ {x y : _} → {hi : Bool→Type hasInvs}  (p : Hom[ x , y ]) → NodeCase (inv {hi} p)


module _ (WC : WildCat ℓ ℓ')  where

 open WildCat WC
 
 module WGi hasInvs (iwg : Bool→Type hasInvs → IsWildGroupoid WC) {hi : Bool→Type hasInvs} where
  open WildGroupoid (record { wildCat = WC ; isWildGroupoid = iwg hi }) public
   using (inv ; ⋆InvR; ⋆InvL; id≡inv-id; distInv; invol-inv)

 invol-inv' : ∀ hasInvs  (iwg : Bool→Type hasInvs → IsWildGroupoid WC)
            {hi hi' : Bool→Type hasInvs} {x y : WC .WildCat.ob}
      (f : Hom[ x , y ]) →
      WildGroupoid.inv
      (record { wildCat = WC ; isWildGroupoid = iwg hi })
      (WildGroupoid.inv
       (record { wildCat = WC ; isWildGroupoid = iwg hi' }) f)
      ≡ f
 invol-inv' true iwg {hi} {hi'} = WGi.invol-inv true iwg
 
 module WCTerm hasInvs (iwg : Bool→Type hasInvs → IsWildGroupoid WC) {hi : Bool→Type hasInvs} where

  open WGi hasInvs iwg 

  open Nodes ob Hom[_,_] hasInvs public
  open Ev id _⋆_ (λ {ig} → wildIsIso.inv' Fu.∘ iwg ig) public


  module WEv' = Ev' ⋆Assoc ⋆IdR ⋆IdL ⋆InvR ⋆InvL


  module WEv'' = WEv'.Ev'' (sym (id≡inv-id)) (invol-inv' hasInvs iwg) distInv 


  eva⤋ : ∀ k {a₀ a₁ : ob} → ∀ (h : Atom k a₀ a₁) → eva[ h ] ≡ eva[ k a⤋ h ]
  eva⤋ k a⟦ x ⟧ = refl
  eva⤋ k a⟦ x ⟧⁻ = refl


  invAtom⤋ : ∀ k k'  {hi} {a₀ a₁ : ob} → ∀ (h : Atom (suc (suc k)) a₀ a₁) →
                  eva[ invAtom (suc (suc k)) {k'} hi h ]
             ≡ eva[ invAtom (suc (suc (suc k))) {k'} hi (suc (suc k) a⤋ h) ]
  invAtom⤋ k k' Nodes.a⟦ x ⟧ = refl
  invAtom⤋ k k' Nodes.a⟦ x ⟧⁻ = refl


  ev⤋' : ∀ k {a₀ a₁ : ob} → ∀ (f' : Node' k a₀ a₁) → ev[ no f' ] ≡ ev[ k ⤋' f' ]
  ev⤋ :  ∀ k {a₀ a₁ : ob} → ∀ (f : Node k a₀ a₁) → ev[ f ] ≡ ev[ k ⤋ f ] 



  ev⤋ k idN = refl
  ev⤋ zero (Nodes.atomN Nodes.a⟦ x ⟧) = refl
  ev⤋ (suc zero) (Nodes.atomN Nodes.a⟦ x ⟧) = sym (⋆IdL x)
  ev⤋ (suc zero) (Nodes.atomN (Nodes.a⟦ x ⟧⁻)) = sym ((⋆IdL _))
  ev⤋ k (no x) = ev⤋' k x

  ev⤋' (suc (suc k)) (x ∷N x₁) =
    cong₂ _⋆_ (ev⤋ (suc (suc k)) x) (eva⤋ (suc (suc k)) x₁ )
  ev⤋' zero (x ⋆N x₁) = cong₂ _⋆_ (ev⤋ zero x) (ev⤋ zero x₁)
  ev⤋' (suc zero) (x ⋆N x₁) = cong₂ _⋆_ (ev⤋ 1 x) (ev⤋ 1 x₁) ∙
    WEv'.evN2++ (1 ⤋ x) (1 ⤋ x₁)
  ev⤋' zero (invN x {hi}) =
       cong inv (ev⤋ zero x) ∙ WEv''.ev[_]≡inv false (0 ⤋ x)  -- enInv1Node x hi
  ev⤋' (suc (suc k)) (Nodes.involN x x₁ {hi}) =
    cong₂ _⋆_ (λ i → (ev⤋ (suc (suc k)) x i ⋆ (eva⤋ (suc (suc k)) x₁) i))
     (invAtom⤋ k 1 {hi} x₁)

  ev⤋⁺ :  ∀ {k} m {a₀ a₁ : ob} → ∀ (f : Node k a₀ a₁) → ev[ f ] ≡ ev[ m ⤋⁺ f ] 
  ev⤋⁺ zero f = refl
  ev⤋⁺ (suc m) f = ev⤋⁺ m f ∙ ev⤋ (m + _) (m ⤋⁺ f)

  ev⤋² = ev⤋⁺ {0} 2



module WGTerm (WG : WildGroupoid ℓ ℓ') where
 open WCTerm (WildGroupoid.wildCat WG) true (λ _ → WildGroupoid.isWildGroupoid WG) public

 open WGi (WildGroupoid.wildCat WG) true (λ _ → WildGroupoid.isWildGroupoid WG) 

 open WildGroupoid WG hiding (⋆InvR ; ⋆InvL)
 open Ev' ⋆Assoc ⋆IdR ⋆IdL ⋆InvR ⋆InvL public

module _ (A : Type ℓ) where
 module Expr = Nodes Unit (λ _ _ → A)

 module DecNodes (_≟A_ : Discrete A) where

  AtomTo𝟚×A : Expr.Atom true 2 _ _ → (Bool × A)
  AtomTo𝟚×A Nodes.a⟦ x ⟧ = true , x
  AtomTo𝟚×A Nodes.a⟦ x ⟧⁻ = false , x


  mbRed : Expr.Node true 2 _ _ → Maybe (Expr.Node true 2 _ _)
  mbRed Nodes.idN = nothing
  mbRed (Nodes.no (Nodes.idN Nodes.∷N x₁)) = nothing
  mbRed (Nodes.no (x'@(Nodes.no (x Nodes.∷N x₂)) Nodes.∷N x₁)) =
     decRec (λ _ → just $ Nodes.no (Nodes.involN (Mb.rec x (idfun _) (mbRed x)) x₂) )
            (λ _ → map-Maybe (Nodes.no ∘ Nodes._∷N x₁) (mbRed x'))
      (discreteΣ 𝟚._≟_ (λ _ → _≟A_) (AtomTo𝟚×A x₂) (AtomTo𝟚×A (Expr.invAtom true 2 _ x₁)))
  mbRed (Nodes.no (Nodes.no (Nodes.involN x x₂) Nodes.∷N x₁)) = nothing
  mbRed (Nodes.no (Nodes.involN x x₁)) = nothing

  redList : Expr.Node true 2 _ _ → List (Expr.Node true 2 _ _)
  redList x = unfoldMaybe (Expr.len true x) (mbRed ∘ Expr.red[_,_] true 2) x 

redListℕ = DecNodes.redList ℕ discreteℕ

mapExpr : ∀ {A : Type ℓ} {A' : Type ℓ'} {b k}
     → (A → A')     
   → Expr.Node A b k _ _
   → Expr.Node A' b k _ _
mapExpr {A = A} {A'} {b} {k} f = w
 where
 wa : Expr.Atom A b k _ _ → Expr.Atom A' b k _ _
 wa Nodes.a⟦ x ⟧ = Nodes.a⟦ f x ⟧
 wa (Nodes.a⟦_⟧⁻ {invG = ig} x {g}) = Nodes.a⟦_⟧⁻ {invG = ig} (f x) {g}
 
 w : Expr.Node A b k _ _ → Expr.Node A' b k _ _
 w Nodes.idN = Nodes.idN
 w (Nodes.atomN {aGuard = ag} x) = Nodes.atomN {aGuard = ag}  (wa x)
 w (Nodes.no (Nodes._∷N_ {∷Guard = g} x x₁)) =
   Nodes.no (Nodes._∷N_ {∷Guard = g} (w x) (wa x₁))
 w (Nodes.no (Nodes._⋆N_ {⋆Guard = g} x x₁)) =
   Nodes.no (Nodes._⋆N_ {⋆Guard = g} (w x) (w x₁))
 w (Nodes.no (Nodes.invN {invGuard = invGuard} x {g})) =
   (Nodes.no (Nodes.invN {invGuard = invGuard} (w x) {g}))
 w (Nodes.no (Nodes.involN {g = g} x x₁ {g'})) =
   Nodes.no (Nodes.involN {g = g} (w x) (wa x₁) {g'})


mapExprQ : ∀ {A : Type ℓ} {b k}
     → (A → R.Term) → Expr.Node A b k _ _ → R.Term
mapExprQ {A = A} {b} {k} f = w
 where
 wa : Expr.Atom A b k _ _ → R.Term
 wa Nodes.a⟦ x ⟧ = R.con (quote Nodes.a⟦_⟧) (f x v∷ [])
 wa Nodes.a⟦ x ⟧⁻ = R.con (quote Nodes.a⟦_⟧⁻) (f x v∷ [])

 w : Expr.Node A b k _ _ → R.Term
 w' : Expr.Node' A b k _ _ → R.Term
 w' (x Nodes.∷N x₁) =
   R.con (quote Nodes._∷N_) (w x v∷ wa x₁ v∷ [])
 w' (x Nodes.⋆N x₁) =
   R.con (quote Nodes._⋆N_) (w x v∷ w x₁ v∷ [])
 w' (Nodes.invN x) =
   R.con (quote Nodes.invN) (w x v∷ [])
 w' (Nodes.involN x x₁) =
   R.con (quote Nodes.involN) (w x v∷ wa x₁ v∷ [])

 w Nodes.idN = R.con (quote Nodes.idN) []
 w (Nodes.atomN x) = R.con (quote Nodes.atomN) (wa x v∷ [])
 w (Nodes.no x) = R.con (quote Nodes.no) (w' x v∷ [])
 

ExprAccumM : ∀ {A : Type ℓ} {A' : Type ℓ'} {ℓs} {S : Type ℓs} {b k}
     → (S → A → R.TC (S × A')) → S         
   → Expr.Node A b k _ _
   → R.TC (S × Expr.Node A' b k _ _)
ExprAccumM {A = A} {A'} {S = S} {b} {k} f = w
 where
 open Expr

 wa : S → Expr.Atom A b k _ _ → R.TC (S × Expr.Atom A' b k _ _)
 wa s a⟦ x ⟧ = (λ (s' , x') → s' , a⟦ x' ⟧) <$> f s x
 wa s (a⟦_⟧⁻ {invG = g'} x {g}) = (λ (s' , x') → s' , (a⟦_⟧⁻  {invG = g'} x' {g})) <$> f s x 
 
 w : S → Expr.Node A b k _ _ → R.TC (S × Expr.Node A' b k _ _)
 w' : S → Expr.Node' A b k _ _ → R.TC (S × Expr.Node A' b k _ _)
 w s idN = R.returnTC (s , idN)
 w s (atomN {aGuard = ag} a) =
   (λ (s' , a') → s' , atomN {aGuard = ag} a') <$> wa s a
 w s (no x) = w' s x

 w' s (_∷N_ {∷Guard = g} x x₁) = do
  (s' , x') ← w s x
  (s' , x₁') ← wa s' x₁ 
  R.returnTC (s' , no (_∷N_ {∷Guard = g} x' x₁'))

 w' s (_⋆N_ {⋆Guard = g} x x₁) = do
  (s' , x') ← w s x
  (s' , x₁') ← w s' x₁ 
  R.returnTC (s' , no (_⋆N_ {⋆Guard = g} x' x₁'))

 w' s (invN {invGuard = g'} x {g}) =
   (λ (s' , x') → s' , (no (invN {invGuard = g'} x' {g}))) <$> w s x
 w' s (involN x x₁) = w s x


opCase' : ∀ (WG : WildGroupoid ℓ ℓ') {x y z} f g →
  WGTerm.NodeCase WG {a₀ = x} {z} _ 
opCase' WG {x} {y} {z} f g = WGTerm.opCase {WG = WG} {y = y} f g
 

invCase' : ∀ (WG : WildGroupoid ℓ ℓ') {x y} f →
  WGTerm.NodeCase WG {a₀ = y} {x} _ 
invCase' WG {x} {y} f = WGTerm.invCase {WG = WG} {x = x} {y} f

id' : (WG : WildGroupoid ℓ ℓ') → ∀ {x} → WildGroupoid.Hom[_,_] WG x x
id' WG = WildGroupoid.id WG

inv' : (WG : WildGroupoid ℓ ℓ') → ∀ {x y} → WildGroupoid.Hom[_,_] WG x y → WildGroupoid.Hom[_,_] WG y x
inv' WG = WildGroupoid.inv WG


⋆' : (WG : WildGroupoid ℓ ℓ') → ∀ {x y z} → WildGroupoid.Hom[_,_] WG x y → WildGroupoid.Hom[_,_] WG y z →  WildGroupoid.Hom[_,_] WG x z
⋆' WG = WildGroupoid._⋆_ WG


module ETerm = Expr R.Term

module _ (WGterm : R.Term) where
 module EvTerm = ETerm.Ev true
      (R.def (quote id') (WGterm v∷ []))
      (λ x y → (R.def (quote ⋆') (WGterm v∷ x v∷ y v∷ [])))
      (λ x → (R.def (quote inv') (WGterm v∷ x v∷ [])))

module Eℕ = Expr ℕ true

NodeTerm : Bool → ℕ → Type ℓ-zero
NodeTerm = λ b k → Expr.Node R.Term b k tt tt




module tryGE (tG : R.Term)  where
 
 tryG : ℕ → R.Term → R.TC (NodeTerm true 0)

 try1g : R.Term → R.TC (NodeTerm true 0)
 try1g t = do
       _ ← R.unify t (R.def (quote id') [ varg tG ])
       R.returnTC (ETerm.idN)

 tryOp : ℕ → R.Term → R.TC (NodeTerm true 0)
 tryOp zero _ = R.typeError []
 tryOp (suc k) t = do
       tm ← R.withNormalisation true $ R.checkType (R.def (quote opCase')
          (varg tG ∷ varg R.unknown ∷ [ varg R.unknown ]))
           (R.def (quote WGTerm.NodeCase) ((varg tG) ∷ [ varg t ]))
       (t1 , t2) ← h tm
       t1' ← tryG k t1
       t2' ← tryG k t2
       R.returnTC (ETerm.no (t1' ETerm.⋆N t2'))

  where

  h : R.Term → R.TC (R.Term × R.Term)
  h (R.con _ l) = match2Vargs l
  h t = R.typeError []

 tryInv : ℕ → R.Term → R.TC (NodeTerm true 0)
 tryInv zero _ = R.typeError []
 tryInv (suc k) t =  do
       tm ← R.withNormalisation true $
        (R.checkType (R.def (quote invCase')
          ((varg tG) ∷ [ varg R.unknown ])) (R.def (quote WGTerm.NodeCase)
           ((varg tG) ∷ [ varg t ])))
       R.debugPrint "tryInv" 30 ([ R.strErr "\n ---- \n" ])
       R.debugPrint "tryInv" 30 ([ R.termErr t ])
       R.debugPrint "tryInv" 30 ([ R.termErr tm ])
       t1 ← h tm
       t1' ← tryG k t1
       R.returnTC (ETerm.no (ETerm.invN t1'))

  where
  h' : List (R.Arg R.Term) → R.TC (R.Term)
  h' (harg _ ∷ xs) = h' xs
  h' (varg t1 ∷ []) = R.returnTC t1
  h' _ = do R.debugPrint "aiu" 3 ([ R.strErr "\n vvv \n" ])
            R.debugPrint "aiu" 33 ([ R.termErr t ])
            R.typeError [ R.strErr "yyy" ]

  h : R.Term → R.TC (R.Term)
  h (R.con _ l) = h' l
  h t = do R.debugPrint "aiu" 33 ([ R.strErr "\n uuu \n" ])
           R.debugPrint "aiu" 33 ([ R.termErr t ])
           R.typeError [ R.strErr "xxxx" ]


 atom : R.Term → R.TC (NodeTerm true 0)
 atom x = R.returnTC $ ETerm.atomN ETerm.a⟦ x ⟧


 tryG zero _ = R.typeError [ (R.strErr "Magic number to low") ]
 tryG (suc k) t =
   R.catchTC
    (try1g t)
    (R.catchTC (tryInv k t)
               (R.catchTC (tryOp k t) (atom t)))
  


compareTerms : R.Term → R.Term → R.TC Bool
compareTerms x x' =
 ((R.noConstraints $ R.unify x x') >> (R.returnTC true)) <|>
 (R.returnTC false)



lookupOrAppend : List R.Term → R.Term → R.TC ((List R.Term) × ℕ)
lookupOrAppend [] t = R.returnTC ([ t ] , 0)
lookupOrAppend xs@(x ∷ xs') t = do
 x≟t ← compareTerms t x
 if x≟t
  then (R.returnTC (xs , 0))
  else (do (xs'' , k) ← lookupOrAppend xs' t
           R.returnTC (x ∷ xs'' , suc k)) 


wildCatSolverTerm : Bool → R.Term → R.Term → R.TC (R.Term × List R.ErrorPart)
wildCatSolverTerm debugFlag t-g hole = do

 (t0 , t1) ← R.withNormalisation true $
  R.inferType hole >>= wait-for-type >>= (get-boundary ) >>= Mb.rec
     (R.typeError [ R.strErr "unable to get boundary" ])
     (λ x → R.returnTC x)

 (r0') ← tryGE.tryG t-g 100 t0
 (r1') ← tryGE.tryG t-g 100 t1
 (tmL , tmE0) ← ExprAccumM lookupOrAppend [] r0' 
 (tmL , tmE1) ← ExprAccumM lookupOrAppend tmL r1'  

 let pa : Eℕ.Node 0 _ _ → (R.Term × List R.ErrorPart)
     pa = λ tmE →
            let rL = redListℕ (1 Eℕ.⤋ (0 Eℕ.⤋ tmE))
                rLpaTm = foldl
                  (λ x y →
                   (R∙ x ( R.def (quote WGTerm.ev[_]₂≡)
                    (t-g v∷ (mapExprQ (lookupWithDefault (R.unknown) tmL) y) v∷ []))) )
                  Rrefl rL
            in ((R.def (quote _∙_)
                 (R.def (quote WGTerm.ev⤋²)
                   (t-g v∷ mapExprQ (lookupWithDefault (R.unknown) tmL) tmE v∷ [])
                    v∷ rLpaTm v∷ [] )) ,
                      (Li.foldr
                     (λ x → Expr.showN ℕ true mkNiceVar x ∷nl_ ) [] $ rL))

 let final = (R.def (quote _∙∙_∙∙_)
               (fst (pa tmE0)
                v∷ R.def (quote refl) []
                v∷ R.def (quote sym) (fst (pa tmE1) v∷ []) v∷ [] ))


 let info = snd (pa tmE0) ++ snd (pa tmE1) ++ (Expr.showN ℕ true mkNiceVar tmE0
            ∷nl Expr.showN ℕ true mkNiceVar tmE1
            ∷nl niceAtomList tmL)

 R.returnTC (final , info) 


-- wildCatSolverMain : Bool → R.Term → R.Term → R.TC Unit
-- wildCatSolverMain debugFlag  t-g hole = do
--   ty ← R.withNormalisation true $  R.inferType hole >>= wait-for-type
--   hole' ← R.withNormalisation true $ R.checkType hole ty
--   (solution , msg) ← groupoidSolverTerm debugFlag t-g  hole'
--   R.catchTC
--    (R.unify hole solution)
--     (R.typeError msg)


groupoidSolverTerm : Bool → R.Term → R.Term → R.TC (R.Term × List R.ErrorPart)
groupoidSolverTerm debugFlag t-g hole = do

 (t0 , t1) ← R.withNormalisation true $
  R.inferType hole >>= wait-for-type >>= (get-boundary ) >>= Mb.rec
     (R.typeError [ R.strErr "unable to get boundary" ])
     (λ x → R.returnTC x)

 (r0') ← tryGE.tryG t-g 100 t0
 (r1') ← tryGE.tryG t-g 100 t1
 (tmL , tmE0) ← ExprAccumM lookupOrAppend [] r0' 
 (tmL , tmE1) ← ExprAccumM lookupOrAppend tmL r1'  

 let pa : Eℕ.Node 0 _ _ → (R.Term × List R.ErrorPart)
     pa = λ tmE →
            let rL = redListℕ (1 Eℕ.⤋ (0 Eℕ.⤋ tmE))
                rLpaTm = foldl
                  (λ x y →
                   (R∙ x ( R.def (quote WGTerm.ev[_]₂≡)
                    (t-g v∷ (mapExprQ (lookupWithDefault (R.unknown) tmL) y) v∷ []))) )
                  Rrefl rL
            in ((R.def (quote _∙_)
                 (R.def (quote WGTerm.ev⤋²)
                   (t-g v∷ mapExprQ (lookupWithDefault (R.unknown) tmL) tmE v∷ [])
                    v∷ rLpaTm v∷ [] )) ,
                      (Li.foldr
                     (λ x → Expr.showN ℕ true mkNiceVar x ∷nl_ ) [] $ rL))

 let final = (R.def (quote _∙∙_∙∙_)
               (fst (pa tmE0)
                v∷ R.def (quote refl) []
                v∷ R.def (quote sym) (fst (pa tmE1) v∷ []) v∷ [] ))


 let info = snd (pa tmE0) ++ snd (pa tmE1) ++ (Expr.showN ℕ true mkNiceVar tmE0
            ∷nl Expr.showN ℕ true mkNiceVar tmE1
            ∷nl niceAtomList tmL)

 R.returnTC (final , info) 


groupoidSolverMain : Bool → R.Term → R.Term → R.TC Unit
groupoidSolverMain debugFlag  t-g hole = do
  ty ← R.withNormalisation true $  R.inferType hole >>= wait-for-type
  hole' ← R.withNormalisation true $ R.checkType hole ty
  (solution , msg) ← groupoidSolverTerm debugFlag t-g  hole'
  R.catchTC
   (R.unify hole solution)
    (R.typeError msg)




macro
 solveGroupoid : R.Term → R.Term → R.TC Unit
 solveGroupoid = groupoidSolverMain true




