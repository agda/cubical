{-# OPTIONS --safe  #-}

module Cubical.Tactics.WildCatSolver.Solvers where


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
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.List as Li
open import Cubical.Data.Maybe as Mb


open import Cubical.HITs.Interval

-- open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.WildCatSolver.Reflection
open import Cubical.Tactics.Reflection
open import Agda.Builtin.String

-- open import Cubical.WildCat.WGE
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.Algebra.Group

private
  variable
    ℓ ℓ' : Level

mvFlagElim : ∀ {A : Type ℓ} (mbA : Maybe A)
             → (caseMaybe {A = A} ⊥ Unit mbA) → A
mvFlagElim (just x) _ = x


record TypeWithRel ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
 no-eta-equality
 field
   Carrier : Type ℓ 
   _[_∼_] : Carrier → Carrier → Type ℓ'
   -- mbIsWildGroupoid : Maybe (∀ WS → IsWildGroupoid (toWildCat WS))


record TypeWithRelMor (T T' : TypeWithRel ℓ ℓ')
    : Type (ℓ-max ℓ ℓ') where
 open TypeWithRel
 field
   TF-ob : TypeWithRel.Carrier T → TypeWithRel.Carrier T' 
   TF-hom : ∀ {x y} → T [ x ∼ y ]
                    → T' [ TF-ob x ∼ TF-ob y ]


FreeTWRM : ∀ {ℓ} (A : Type ℓ) → TypeWithRel ℓ-zero ℓ
TypeWithRel.Carrier (FreeTWRM A) = Unit
FreeTWRM A TypeWithRel.[ x ∼ x₁ ] = A




module FuExpr' (ℓ ℓ' : Level) (InvFlag : Type)
              (𝑻 : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')))
              (𝑻→twr : 𝑻 → TypeWithRel ℓ ℓ')
              (𝑭 : 𝑻 → 𝑻 → Type (ℓ-max ℓ ℓ'))
              (𝑭-ob-map : ∀ {T T'} → 𝑭 T T'
                → TypeWithRel.Carrier (𝑻→twr T)
                   → TypeWithRel.Carrier (𝑻→twr T')   ) where
 
 module _ 𝑻 where open TypeWithRel (𝑻→twr 𝑻) public

 
 data FuExpr : (T : 𝑻) → Carrier T → Carrier T → Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  𝒂⟦_⟧ : ∀ {T x y} → T [ x ∼ y ] → FuExpr T x y
  idFE : ∀ {T x} → FuExpr T x x
  _⋆FE_ : ∀ {T x y z}
          → FuExpr T x y
          → FuExpr T y z → FuExpr T x z
  invFE : ∀ {T x y} (invF : InvFlag)
          → FuExpr T x y
          → FuExpr T y x
  ⟅_,_,_⟆FE : ∀ T {T' x y} 
            (F : 𝑭 T T')
          → FuExpr T x y
          → FuExpr T' (𝑭-ob-map F x) (𝑭-ob-map F y)


 module _ (m2str : ∀ {T x y} → T [ x ∼ y ] → String) where
  printFuExpr : ∀ {T x y} →  FuExpr T x y → String
  printFuExpr 𝒂⟦ x ⟧ = m2str x
  printFuExpr idFE = "id"
  printFuExpr (x ⋆FE x₁) =
    "(" <> printFuExpr x <> "⋆" <> printFuExpr x₁ <> ")"
  printFuExpr (invFE invF x) =
    "(" <> printFuExpr x <> ")⁻¹"
  printFuExpr ⟅ T , F , x ⟆FE =
     "⟪" <> printFuExpr x <> "⟫" 

module _ InvFlag where
 module TermExpr = FuExpr' ℓ-zero ℓ-zero InvFlag
                    (Lift R.Term) (λ _ → FreeTWRM R.Term)
                          (λ _ _ → R.Term) (λ _ _ → tt)
 open TermExpr using (𝒂⟦_⟧; idFE; _⋆FE_; invFE; ⟅_,_,_⟆FE)
               renaming (FuExpr to TE) public

module _ InvFlag where
 module ℕExpr = FuExpr' ℓ-zero ℓ-zero InvFlag
                    (Lift ℕ) (λ _ → FreeTWRM ℕ)
                          (λ _ _ → ℕ) (λ _ _ → tt)

 open ℕExpr using ()
            renaming (FuExpr to ℕE) public

module _ if ([w] [F] [a] : List R.Term) where
 lkW lkF lkA : ℕ → R.Term
 lkW = lookupWithDefault R.unknown [w]
 lkF = lookupWithDefault R.unknown [F]
 lkA = lookupWithDefault R.unknown [a]
 
 ℕExpr→TermExrp : ∀ {w} → ℕE if (lift w) _ _ → TE if (lift (lkW w)) _ _
 ℕExpr→TermExrp 𝒂⟦ x ⟧ = 𝒂⟦ lkA x ⟧
 ℕExpr→TermExrp idFE = idFE
 ℕExpr→TermExrp (x ⋆FE x₁) =
   (ℕExpr→TermExrp x ⋆FE ℕExpr→TermExrp x₁) 
 ℕExpr→TermExrp (invFE invF x) =
   invFE invF (ℕExpr→TermExrp x)
 ℕExpr→TermExrp (⟅ _ , F , x ⟆FE) = ⟅ _ , lkF F , ℕExpr→TermExrp x ⟆FE


wc→twr : WildCat ℓ ℓ' → TypeWithRel ℓ ℓ'
TypeWithRel.Carrier (wc→twr x) = WildCat.ob x
TypeWithRel._[_∼_] (wc→twr x) = WildCat.Hom[_,_] x 

mbFunctorApp : R.Term → Maybe (R.Term × R.Term)
mbFunctorApp (R.def (quote WildFunctor.F-hom) t) = matchFunctorAppArgs t
mbFunctorApp _ = nothing

record WildStr ℓ ℓ' : Type (ℓ-suc (ℓ-suc (ℓ-max ℓ ℓ'))) where
 no-eta-equality
 field
   wildStr : Type (ℓ-suc (ℓ-max ℓ ℓ'))
   toWildCat : wildStr → WildCat ℓ ℓ'
   mbIsWildGroupoid : Maybe (∀ WS → IsWildGroupoid (toWildCat WS))

 InvFlag = caseMaybe ⊥ Unit mbIsWildGroupoid

 ws→twr : wildStr → TypeWithRel ℓ ℓ'
 ws→twr = wc→twr ∘ toWildCat
 
 module _ (ws : wildStr) where
  open WildCat (toWildCat ws) renaming (Hom[_,_] to _H[_,_] ; _⋆_ to _⟨_⋆_⟩) public 
  module _ (invF : InvFlag) where
    WG = (record { wildCat = toWildCat ws
              ; isWildGroupoid = mvFlagElim mbIsWildGroupoid invF ws })
    open WildGroupoid WG public


 WildF : wildStr → wildStr → Type (ℓ-max ℓ ℓ')
 WildF ws ws' = WildFunctor (toWildCat ws) (toWildCat ws') 

 open WildFunctor


 data FuCases : (ws : wildStr) {x y : ob ws}
          → ws H[ x , y ] → Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  𝒂⟦_⟧ : ∀ {ws x y} f → FuCases ws {x} {y} f
  idFE : ∀ {ws x} → FuCases ws {x} {x} (id ws)
  _⋆FE_ : ∀ {ws x y z}
          → (f : ws H[ x , y ])
          → (g : ws H[ y , z ]) → FuCases ws {x} {z} (ws ⟨ f ⋆ g ⟩)
  invFE : ∀ {ws x y} (invF : InvFlag)
          → (f : ws H[ x , y ])
          → FuCases ws {y} {x} (inv ws invF f)
  ⟅_,_,_⟆FE : ∀ ws {ws' x y} 
            (F : WildF ws ws')
          → (f : ws H[ x , y ])
          → FuCases ws' {F-ob F x} {F-ob F y} (F-hom F f )

 module _ where
  open FuExpr' ℓ ℓ' InvFlag  wildStr ws→twr
       WildF WildFunctor.F-ob public 

 evFuExpr : {ws : wildStr} {x y : ob ws}
              → FuExpr ws x y → ws H[ x , y ] 
 evFuExpr FuExpr'.𝒂⟦ x ⟧ = x
 evFuExpr {ws} FuExpr'.idFE = id ws
 evFuExpr {ws} (x FuExpr'.⋆FE x₁) = ws ⟨ evFuExpr x ⋆ evFuExpr x₁ ⟩
 evFuExpr {ws} (FuExpr'.invFE invF x) = inv ws invF (evFuExpr x)
 evFuExpr FuExpr'.⟅ T , F , x ⟆FE = F ⟪ evFuExpr x ⟫
 
 module _ {ws : wildStr} where

  data FuAtom : ob ws → ob ws → Type (ℓ-max ℓ ℓ') where
    a[_] : ∀ {x y} → ws H[ x , y ] → FuAtom x y
    a[_,_]⁻ : ∀ {x y} → InvFlag → ws H[ y , x ] → FuAtom x y


  infixl 15 _ff∷_
  data FuFlat : ob ws → ob ws → Type (ℓ-max ℓ ℓ') where
    [ff] : ∀ {x} → FuFlat x x
    _ff∷_ : ∀ {x y z} → FuFlat x y → FuAtom y z → FuFlat x z
    _invol_∷ff_ : ∀ {x y z} →  FuFlat x y → (invF : InvFlag) →
      FuAtom y z → FuFlat x y


  invFuAtom : ∀ {x y} → InvFlag → FuAtom y x → FuAtom x y
  invFuAtom x a[ x₁ ] = a[ x , x₁ ]⁻
  invFuAtom x a[ x₁ , x₂ ]⁻ = a[ x₂ ]

  
  ff↓ : ∀ {x y} → FuFlat x y → FuFlat x y
  ff↓ [ff] = [ff]
  ff↓ (x ff∷ x₁) = ff↓ x ff∷ x₁
  ff↓ (x invol invF ∷ff x₁) = ff↓ x ff∷ x₁ ff∷ invFuAtom invF x₁
  
  ff↑ : ∀ {x y} → FuFlat x y → FuFlat x y
  ff↑ [ff] = [ff]
  ff↑ (x ff∷ x₁) = ff↑ x ff∷ x₁
  ff↑ (x invol invF ∷ff x₁) = ff↑ x


  _ff++_ : ∀ {x y z} → FuFlat x y → FuFlat y z → FuFlat x z
  x ff++ [ff] = x
  x ff++ (x₁ ff∷ x₂) = (x ff++ x₁) ff∷ x₂
  x ff++ (x₁ invol invF ∷ff x₂) = (x ff++ x₁) invol invF ∷ff x₂


  ffInv : ∀ {x y} → InvFlag → FuFlat x y → FuFlat y x
  ffInv x [ff] = [ff]
  ffInv x (x₁ ff∷ x₂) = ([ff] ff∷ (invFuAtom x x₂)) ff++ ffInv x x₁  
  ffInv x (x₁ invol invF ∷ff x₂) =
    ([ff] invol invF ∷ff x₂) ff++ ffInv x x₁

 invFuAtomExplicit : ∀ (ws : wildStr) {x y : WildCat.ob (toWildCat ws)} →
      InvFlag → FuAtom y x → FuAtom x y
 invFuAtomExplicit ws = invFuAtom {ws}

 aa⟪_,_⟫ : ∀ {ws' ws : wildStr} {x y} 
         → (F : WildF ws' ws)
         → (FuAtom x y)
         → FuAtom (F-ob F x) (F-ob F y)
 aa⟪ F , a[ x ] ⟫ = a[ F ⟪ x ⟫ ]
 aa⟪ F , a[ x , x₁ ]⁻ ⟫ = a[ x , F ⟪ x₁ ⟫ ]⁻


 ff⟪_,_⟫ : ∀ {ws' ws : wildStr} {x y} 
          → (F : WildF ws' ws)
          → (FuFlat x y)
          → FuFlat  (F-ob F x) (F-ob F y)
 ff⟪ F , [ff] ⟫ = [ff]
 ff⟪ F , x ff∷ x₁ ⟫ = ff⟪ F , x ⟫ ff∷ aa⟪ F , x₁ ⟫
 ff⟪ F , x invol invF ∷ff x₁ ⟫ = ff⟪ F , x ⟫ invol invF ∷ff aa⟪ F , x₁ ⟫


 FuExpr→FF : {ws : wildStr} {x y : ob ws}
              → FuExpr ws x y → FuFlat x y 
 FuExpr→FF 𝒂⟦ x ⟧ = [ff] ff∷ a[ x ]
 FuExpr→FF idFE = [ff]
 FuExpr→FF (x ⋆FE x₁) = (FuExpr→FF x) ff++ (FuExpr→FF x₁)
 FuExpr→FF (invFE invF x) = ffInv invF (FuExpr→FF x)
 FuExpr→FF ⟅ T , F , x ⟆FE = ff⟪ F , FuExpr→FF x ⟫

 evAtom : {ws : wildStr} {x y : ob ws}
              → FuAtom x y → ws H[ x , y ] 
 evAtom a[ x ] = x
 evAtom {ws} a[ x , x₁ ]⁻ = inv ws x x₁


 invFuAtom-involR : ∀ ws {x y} invF →
      (a : FuAtom {ws} y x) →
      (ws ⟨ evAtom a ⋆ evAtom (invFuAtom invF a) ⟩) ≡ id ws 
 invFuAtom-involR ws invF a[ x ] = ⋆InvR ws _ _
 invFuAtom-involR ws invF a[ x , x₁ ]⁻ = ⋆InvL ws _ _


 evFF : {ws : wildStr} {x y : ob ws}
              → FuFlat x y → ws H[ x , y ] 
 evFF {ws} [ff] = id ws
 evFF {ws} (x ff∷ x₁) = ws ⟨ (evFF x) ⋆ (evAtom x₁) ⟩
 evFF (x invol invF ∷ff x₁) = evFF x



 evFF≡↓ : (ws : wildStr) {x y : ob ws}
              → (f : FuFlat x y) →
               evFF (ff↓ f) ≡  evFF f
 evFF≡↓ ws [ff] = refl
 evFF≡↓ ws (f ff∷ x) = cong (ws ⟨_⋆ _ ⟩) (evFF≡↓ ws f)
 evFF≡↓ ws (f invol invF ∷ff x) =
     ⋆Assoc ws _ _ _
  ∙∙ cong₂ (ws ⟨_⋆_⟩) (evFF≡↓ ws f) (invFuAtom-involR ws invF x)
  ∙∙ ⋆IdR ws (evFF f)
 
 evFF++ : ∀ {ws x y z} → (g : FuFlat {ws} x y) → (h : FuFlat y z) →
             ws ⟨ evFF g ⋆ evFF h ⟩ ≡ (evFF (g ff++  h))  
 evFF++ {ws = ws} g [ff] = ⋆IdR ws _
 evFF++ {ws = ws} g (h ff∷ x) =  sym (⋆Assoc ws _ _ _) ∙
  cong (ws ⟨_⋆ (evAtom x) ⟩) (evFF++ g h)
 evFF++ g (h invol invF ∷ff x) = evFF++ g h

 evAinv : ∀ {ws x y} → (invF : InvFlag) →
              (g : FuAtom {ws} x y) →
               inv ws invF (evAtom g) ≡ evAtom (invFuAtom invF g)
 evAinv invF a[ x ] = refl
 evAinv {ws = ws} invF a[ x , x₁ ]⁻ with mbIsWildGroupoid | invol-inv ws 
 ... | just x₂ | ii = ii _ x₁


 aa-Func : ∀ {ws ws' x y} (F : WildFunctor (toWildCat ws) (toWildCat ws'))
      (a : FuAtom {ws} x y) →
       F-hom F (evAtom a) ≡ evAtom aa⟪ F , a ⟫
 aa-Func F a[ x ] = refl
 aa-Func {ws} {ws'} F a[ invF , x₁ ]⁻ =
  F-inv' (WG ws invF) (WG ws' invF) F x₁

 aa-Func-inv : ∀ {ws ws' x y} invF (F : WildFunctor (toWildCat ws) (toWildCat ws'))
      (a : FuAtom {ws} x y) →
         inv ws'
           invF (evAtom aa⟪ F , a ⟫) ≡ evAtom aa⟪ F , invFuAtom invF a ⟫
 aa-Func-inv invF F a[ x ] = refl
 aa-Func-inv {ws' = ws'} invF F a[ x , x₁ ]⁻ with mbIsWildGroupoid | invol-inv ws'
 ... | just x₂ | ii = ii _ _
 
 evFFinv : ∀ {ws x y} → (invF : InvFlag) →
              (g : FuFlat {ws} x y) →
               inv ws invF (evFF g) ≡ evFF (ffInv invF g)   
 evFFinv {ws} invF [ff] = id≡inv-id ws invF
 evFFinv {ws} invF (g ff∷ x) =
   distInv ws invF _ _
    ∙∙ cong₂ (ws ⟨_⋆_⟩) (evAinv invF x ∙ sym (⋆IdL ws _)) (evFFinv invF g)
         ∙∙ evFF++ _ (ffInv invF g) 
 evFFinv {ws} invF (g invol invF₁ ∷ff x) =
  evFFinv invF g ∙∙ sym (⋆IdL ws _) ∙∙ evFF++ _ (ffInv invF g)

 ff⟪⟫⋆ : ∀ {ws ws' x y z} (F : WildFunctor (toWildCat ws) (toWildCat ws'))
       → (f : FuFlat {ws} x y) → (g : FuFlat y z) →
      ws' ⟨ (evFF ff⟪ F , f ⟫) ⋆ (evFF ff⟪ F , g ⟫) ⟩
      ≡ evFF ff⟪ F , f ff++  g ⟫
 ff⟪⟫⋆ {ws' = ws'} F f [ff] = ⋆IdR ws' _
 ff⟪⟫⋆ {ws' = ws'} F f (g ff∷ x) =
  sym (⋆Assoc ws' _ _ _) ∙
   cong (ws' ⟨_⋆ (evAtom aa⟪ F , x ⟫)⟩) (ff⟪⟫⋆ F f g)
 ff⟪⟫⋆ F f (g invol invF ∷ff x) = ff⟪⟫⋆ F f g

 ff⟪⟫inv : ∀ {ws ws' x y} invF (F : WildFunctor (toWildCat ws) (toWildCat ws'))
       → (f : FuFlat {ws} x y) →
      inv ws' invF (evFF ff⟪ F , f ⟫) 
      ≡ evFF ff⟪ F , ffInv invF f ⟫
 ff⟪⟫inv {ws' = ws'} invF F [ff] = id≡inv-id ws' invF
 ff⟪⟫inv {ws' = ws'} invF F (f ff∷ x) =
   distInv ws' invF _ _
    ∙∙ cong₂ (ws' ⟨_⋆_⟩) (aa-Func-inv invF F x ∙ sym (⋆IdL ws' _)) (ff⟪⟫inv invF F f)
    ∙∙ ff⟪⟫⋆ F _ (ffInv invF f)  
 ff⟪⟫inv {ws' = ws'} invF F (f invol invF₁ ∷ff x) =
   ff⟪⟫inv invF F f
    ∙∙ sym (⋆IdL ws' _)
    ∙∙ ff⟪⟫⋆ F ([ff] invol invF₁ ∷ff x) (ffInv invF f)



 ff-Func : ∀ {ws ws' x y} (F : WildFunctor (toWildCat ws) (toWildCat ws'))
      (f : FuFlat {ws} x y) →
       F-hom F (evFF f) ≡ evFF ff⟪ F , f ⟫
 ff-Func F [ff] = F-id F
 ff-Func {ws' = ws'} F (f ff∷ x) =
  F-seq F _ _ ∙ cong₂ (ws' ⟨_⋆_⟩) (ff-Func F f) (aa-Func F x)
 ff-Func F (f invol invF ∷ff x) = ff-Func F  f
 
 evFF-Func : ∀ {ws ws'} (F : WildFunctor (toWildCat ws) (toWildCat ws')) {x y} → 
              (f : FuExpr ws x y) →
               F-hom F (evFuExpr f) ≡ evFF {ws'} ff⟪ F , FuExpr→FF f ⟫
 evFF-Func {ws' = ws'} F FuExpr'.𝒂⟦ x ⟧ = sym (⋆IdL ws' _)
 evFF-Func F FuExpr'.idFE = F-id F
 evFF-Func {ws} {ws'} F (f FuExpr'.⋆FE f₁) =
  F-seq F _ _ ∙∙ cong₂ (ws' ⟨_⋆_⟩) (evFF-Func {ws} F f) ((evFF-Func {ws} F f₁))
   ∙∙ ff⟪⟫⋆ F (FuExpr→FF f) (FuExpr→FF f₁)
 evFF-Func {ws} {ws'} F (FuExpr'.invFE invF f) =
   F-inv' (WG ws invF)
         (WG ws' invF) F (evFuExpr f)
    ∙∙ cong (inv ws' invF) (evFF-Func F f) ∙∙ ff⟪⟫inv invF F (FuExpr→FF f)
 evFF-Func F FuExpr'.⟅ T , F' , f ⟆FE =
   cong (F-hom F) (evFF-Func F' f) ∙
     ff-Func F ff⟪ F' , FuExpr→FF f ⟫
 
 evFuExpr≡evFF : (ws : wildStr) {x y : ob ws}
              → (f : FuExpr ws x y) →
                evFuExpr f ≡ evFF (FuExpr→FF f)
 evFuExpr≡evFF ws FuExpr'.𝒂⟦ x ⟧ = sym (⋆IdL ws _)
 evFuExpr≡evFF _ FuExpr'.idFE = refl
 evFuExpr≡evFF ws (f FuExpr'.⋆FE f₁) =
   cong₂ (ws ⟨_⋆_⟩) (evFuExpr≡evFF  ws f) (evFuExpr≡evFF ws f₁)
    ∙ evFF++ (FuExpr→FF f) (FuExpr→FF f₁)
 evFuExpr≡evFF ws (FuExpr'.invFE invF f) = 
  cong (inv ws invF) (evFuExpr≡evFF ws f) ∙ evFFinv invF (FuExpr→FF f) 
 evFuExpr≡evFF ws FuExpr'.⟅ T , F , f ⟆FE = evFF-Func F f

 -- evFuExpr-singl : {ws : wildStr} {x y : ob ws}
 --              → (f : FuExpr ws x y) →
 --                  Σ {!!} {!λ f' → evFuExpr f ≡ evFF (FuExpr→FF f)!}
 -- evFuExpr-singl = {!!}



 magicNumber : ℕ
 magicNumber = 100

 infixl 5 us∷_

 -- us∷_ : R.Term
 us∷_ : List (R.Arg R.Term) → List (R.Arg R.Term)
 us∷_ = R.unknown v∷_
 
 buildFromTE : ∀ {W} → TE InvFlag (lift W) _ _ → R.Term 
 buildFromTE FuExpr'.𝒂⟦ x ⟧ = R.con (quote FuExpr'.𝒂⟦_⟧) ([ varg x ])
 buildFromTE FuExpr'.idFE = R.con (quote FuExpr'.idFE) []
 buildFromTE (x FuExpr'.⋆FE x₁) =
   R.con (quote FuExpr'._⋆FE_)
    (buildFromTE x v∷ buildFromTE x₁ v∷ [])
 buildFromTE (FuExpr'.invFE invF x) =
      R.con (quote FuExpr'.invFE)
    (us∷ buildFromTE x v∷ [])
 buildFromTE FuExpr'.⟅ lift T , F , x ⟆FE =
   R.con (quote FuExpr'.⟅_,_,_⟆FE)
    (T v∷ F v∷ buildFromTE x v∷ [])
 
 module tryWCE WS (tGs : List R.Term)  where


  mb-invol : R.Term → ℕ → R.Term → R.TC (Maybe (R.Term × R.Term))
  mb-invol _ zero _ = R.typeError ("magic number too low in mb-invol" ∷ₑ [])
  mb-invol _ _ (R.con (quote [ff]) _) = R.returnTC nothing
  mb-invol W (suc n) (R.con (quote _ff∷_) tl) = match2Vargs tl >>= w
    where
    w : (R.Term × R.Term) → R.TC (Maybe (R.Term × R.Term))
    w (R.con (quote [ff]) _ , _) = R.returnTC nothing
    w (xs'@(R.con (quote _ff∷_) tl') , y) =
      match2Vargs tl' >>= λ (xs , x) →
       R.catchTC
         (R.noConstraints $ R.unify
           (R.def (quote invFuAtomExplicit) (WS v∷ W v∷ us∷ x v∷ [])) y
            >> (Mb.rec (xs , xs) (idfun _) <$> mb-invol W n xs)
            >>= λ (xs* , xs*↑) →
               R.returnTC
                (just ((R.con (quote _invol_∷ff_) (xs* v∷ us∷ x v∷ []))
                 , xs*)
                 ))
         (map-Maybe (map-both (λ xs* → R.con (quote _ff∷_)
           ((xs* v∷ y v∷ []))))
           <$> mb-invol W n xs')
    w (x , y) = R.typeError ("Imposible!! : " ∷ₑ x ∷ₑ " " ∷ₑ y ∷ₑ [])
  mb-invol _ _ x = R.typeError ("Imposible!! : " ∷ₑ x ∷ₑ [])

  mb-invol' :  R.Term → R.Term → R.TC (Maybe (R.Term × R.Term))
  mb-invol' = λ W → mb-invol W magicNumber


  redList : R.Term → ℕ → R.Term → R.TC (List R.Term)
  redList W = h
   where
   h : ℕ → R.Term →  R.TC (List R.Term)
   h zero _ = R.typeError ("magic number too low in mb-invol" ∷ₑ [])
   h (suc k) t = 
     (mb-invol' W t) >>=
       Mb.rec
         (R.returnTC [])
         λ (t' , t'↓) → do             
           p' ← h k t'↓
           -- R.typeError [ R.termErr t' ]
           R.returnTC (t' ∷ p')
     

  redList' : R.Term → R.Term → R.TC (List R.Term)
  redList' W = redList W magicNumber

  -- involPathTerm : R.Term → ℕ → R.Term → R.TC R.Term
  -- involPathTerm W (suc n) t =
  --   (mb-invol' W t) >>=
  --     Mb.rec
  --       (R.returnTC (R.def (quote refl) []))
  --       λ (t' , t'↓) → do
  --          p' ← involPathTerm W n t'↓
  --          R.returnTC $ R.def (quote _∙_)
  --            ((R.def (quote evFF≡↓) (WS v∷ W v∷ t' v∷ [])) v∷ p' v∷ [])
  -- involPathTerm _ zero _ =
  --  R.typeError ("magic number too low in mb-invol" ∷ₑ [])

  -- involPathTerm' : R.Term → R.Term → R.TC R.Term
  -- involPathTerm' W t = involPathTerm W magicNumber t 
  --   -- R.checkType pa (R.def (quote Path) {!!})
    
  checkFromTE : ∀ {W} → TE InvFlag (lift W) _ _ →
    R.TC R.Term --(Σ wildStr λ ws → Σ _ (λ x → Σ _ (FuExpr ws x))) 
  checkFromTE {W} te = do
   let te' = buildFromTE te
   R.checkType te'
      (R.def (quote FuExpr) (WS v∷ W v∷ us∷ us∷ []  ))
     -- (R.con (quote _,_)
     -- (W
     -- v∷ R.con (quote _,_)
     --   (R.unknown v∷ R.con (quote _,_)
     --   (R.unknown v∷ te' v∷ []) v∷ [])  v∷ []) )
     --   ?

  -- if = {!!}
 
  tryE : (W : R.Term) → ℕ → R.Term → R.TC (TE InvFlag (lift W) _ _)

  fromWC : R.Term → R.TC R.Term
  fromWC t = tryAllTC
    (R.typeError ("fromWC fail: " ∷ₑ t ∷ₑ []))
     tGs
     λ ws → R.unify (R.def (quote toWildCat)
           (WS v∷ ws v∷ [])) t >> R.returnTC ws

  tryOp : (W : R.Term) → ℕ → R.Term → R.TC (TE InvFlag (lift W) _ _)
  tryOp W zero _ = R.typeError []
  tryOp W (suc k) t = do
        let tm = R.con (quote FuCases._⋆FE_)
                       (R.unknown v∷ R.unknown v∷ [])
            ty = R.def (quote FuCases)
                       (WS v∷ W v∷ t v∷ [])
        tm' ← R.checkType tm ty
        (t1 , t2) ← h tm'
        t1' ← tryE W k t1
        t2' ← tryE W k t2
        R.returnTC (t1' TermExpr.⋆FE t2')
     where

      h : R.Term → R.TC (R.Term × R.Term)
      h (R.con _ l) = match2Vargs l
      h t = R.typeError []

  tryInv : (W : R.Term) → ℕ → R.Term → R.TC (TE InvFlag (lift W) _ _)
  tryInv W zero _ = R.typeError []
  tryInv W (suc k) t = do
        let tm = R.con (quote FuCases.invFE)
                       (R.unknown v∷ R.unknown v∷ [])
            ty = R.def (quote FuCases)
                       (WS v∷ W v∷ t v∷ [])
        tm' ← R.checkType tm ty
        (_ , t-x) ← h tm'
        t-x' ← tryE W k t-x
        ifQ ← R.unquoteTC R.unknown
        R.returnTC (TermExpr.invFE ifQ t-x')
     where

      h : R.Term → R.TC (R.Term × R.Term)
      h (R.con _ l) = match2Vargs l
      h t = R.typeError []


  tryFunc : (W : R.Term) → ℕ → R.Term → R.TC (TE InvFlag (lift W) _ _)
  tryFunc W zero _ = R.typeError []
  tryFunc W (suc k) t = do
        t' ← R.normalise t
        -- (R.typeError $ "tryFunc fail " ∷nl t ∷nl t' ∷nl getConTail t')
        (WC-src , F-t , x-t) ← Mb.rec
          (R.typeError $ "tryFunc fail " ∷nl t ∷nl t' ∷nl getConTail t')
          (λ (F-t , x-t) → do
            F-ty ← R.withNormalisation true $ R.inferType F-t
            (W-src , W-trg) ← h F-ty
            R.returnTC {A = R.Term × R.Term × R.Term}
              (W-src , (F-t , x-t))
            )
          (mbFunctorApp t')
        WS-src ← fromWC WC-src
        let tm = R.con (quote FuCases.⟅_,_,_⟆FE)
                       (WS-src v∷ F-t v∷ x-t  v∷ [])
            ty = R.def (quote FuCases)
                       (WS v∷ W v∷ t v∷ [])
        tm' ← R.checkType tm ty
        x-t' ← tryE WS-src k x-t
        R.returnTC (TermExpr.⟅ lift WS-src , F-t , x-t' ⟆FE)
     where

      h : R.Term → R.TC (R.Term × R.Term)
      h (R.con _ l) = match2Vargs l
      h (R.def _ l) = match2Vargs l      
      h t = R.typeError $ "match2Fail: " ∷ₑ t ∷ₑ []



  tryId : (W : R.Term) → R.Term → R.TC (TE InvFlag (lift W) _ _)
  tryId W t = do
        let tm = R.con (quote FuCases.idFE) []
            ty = R.def (quote FuCases)
                       (WS v∷ W v∷ t v∷ [])
        tm' ← R.checkType tm ty
        R.returnTC (TermExpr.idFE)

  atom : (W : R.Term) → R.Term → R.TC (TE InvFlag (lift W) _ _)
  atom _ x = R.returnTC $ TermExpr.𝒂⟦ x ⟧


  tryE W zero _ = R.typeError [ (R.strErr "Magic number to low") ]
  tryE W (suc k) t =
   R.catchTC
    (tryId W t)
    (R.catchTC (tryInv W k t)
               -- (tryOp k t)
       (R.catchTC (tryOp W k t)
         (R.catchTC (tryFunc W k t) (atom W t)))
               )



 solveW : R.Term → R.Term → R.Term → R.TC Unit
 solveW Ws Wts' hole = do
   Wts ← quotedList→ListOfTerms Wts'
   Wt ← tryAllTC
     (R.typeError $ "At least one 𝑿 must be provded!" ∷ₑ [])
     Wts R.returnTC
   hoTy ← R.withNormalisation true $
             R.inferType hole >>= wait-for-type
   (t0 , t1) ←  (get-boundary hoTy ) >>= Mb.rec
    (R.typeError [ R.strErr "unable to get boundary" ])
    (λ x → R.returnTC x)
   t0' ← tryWCE.tryE Ws Wts Wt magicNumber t0
   t1' ← tryWCE.tryE Ws Wts Wt magicNumber t1
   expr0 ← tryWCE.checkFromTE Ws Wts t0'
   expr1 ← tryWCE.checkFromTE Ws Wts t1'   
   -- R.typeError
   let msg = (TermExpr.printFuExpr InvFlag (λ _ → "●") t0' ∷nl
                TermExpr.printFuExpr InvFlag (λ _ → "●") t1' ∷ₑ [])
   invol0 ← R.normalise (R.def (quote FuExpr→FF) (Ws v∷ v[ expr0 ]))
   invol1 ← R.normalise (R.def (quote FuExpr→FF) (Ws v∷ v[ expr1 ]))


   red0 ← tryWCE.redList' Ws Wts Wt invol0
   red1 ← tryWCE.redList' Ws Wts Wt invol1

   let invPa0 = Li.map
           (λ t' → just (R.def (quote evFF≡↓) (Ws v∷ Wt v∷ t' v∷ [])))
           red0
       invPa1 = Li.map
           (λ t' → just (R.def (quote evFF≡↓) (Ws v∷ Wt v∷ t' v∷ [])))
           red1
   -- R.typeError (
   --   (join (Li.map (λ x → "\n-- " ∷ₑ [ R.termErr x ] )  red0))
   --      ++ₑ " " ∷nl " " ∷nl
   --   (join (Li.map (λ x → "\n-- " ∷ₑ [ R.termErr x ] )  red1)) ++ₑ [])

--     -- invPa0 ← tryWCE.involPathTerm' Ws Wts Wt invol0 -->>= R.normalise
--     -- invPa1 ← tryWCE.involPathTerm' Ws Wts Wt  invol1 -->>= R.normalise

--     -- -- R.typeError (invol0 ∷nl
--     -- --              invol1 ∷ₑ [])



   let finalTrm0 =
          just (R.def (quote evFuExpr≡evFF) (Ws v∷ Wt v∷ expr0 v∷ []))
          ∷ invPa0
         -- R.def (quote _∙_)
         -- ((R.def (quote evFuExpr≡evFF) (Ws v∷ Wt v∷ expr0 v∷ [])) v∷
         --  invPa0 v∷ [])
       finalTrm1 =
          just (R.def (quote evFuExpr≡evFF) (Ws v∷ Wt v∷ expr1 v∷ []))
          ∷ invPa1
         -- R.def (quote _∙_)
         -- ((R.def (quote evFuExpr≡evFF) (Ws v∷ Wt v∷ expr1 v∷ [])) v∷
         --  invPa1 v∷ [])

   let finalTrm = fromMaybe (R.def (quote refl) []) $ foldPathTerms
          (finalTrm0 ++ symPathTerms finalTrm1)
       -- --invPa0
       --   R.def (quote _∙_)
       --   (finalTrm0 v∷ --R.unknown v∷
       --    (R.def (quote sym)
       --       (finalTrm1 v∷ [])) v∷ [])

   -- msg ← R.formatErrorParts (finalTrm ∷ₑ [])

   -- R.typeError (msg ∷ₑ [])

   (R.unify finalTrm hole) -- <|> R.typeError msg


--  macro


--   testInferExpr : R.Term → R.Term → R.Term → R.Term → R.TC Unit
--   testInferExpr Ws Wts' t ho = do
--     Wts ← quotedList→ListOfTerms Wts'
--     Wt ← tryAllTC
--       (R.typeError $ "At least one 𝑿 must be provded!" ∷ₑ [])
--       Wts R.returnTC
--     expr ← tryWCE.tryE Ws Wts Wt magicNumber t -->> R.returnTC _
    
--     tryWCE.checkFromTE Ws Wts expr
--     R.typeError (TermExpr.printFuExpr InvFlag (λ _ → "●") expr  ∷ₑ [])
--     -- R.unify R.unknown ho


--   -- solveNoInvs : R.Term → R.Term → R.Term → R.TC Unit
--   -- solveNoInvs Ws Wts' hole = do
--   --   Wts ← quotedList→ListOfTerms Wts'
--   --   Wt ← tryAllTC
--   --     (R.typeError $ "At least one 𝑿 must be provded!" ∷ₑ [])
--   --     Wts R.returnTC
--   --   (t0 , t1) ← R.withNormalisation true $
--   --     R.inferType hole >>= wait-for-type >>= (get-boundary ) >>= Mb.rec
--   --    (R.typeError [ R.strErr "unable to get boundary" ])
--   --    (λ x → R.returnTC x)
--   --   t0' ← tryWCE.tryE Ws Wts Wt magicNumber t0
--   --   t1' ← tryWCE.tryE Ws Wts Wt magicNumber t1
--   --   expr0 ← tryWCE.checkFromTE Ws Wts t0'
--   --   expr1 ← tryWCE.checkFromTE Ws Wts t1'   
--   --   -- R.typeError
--   --   -- R.typeError (TermExpr.printFuExpr InvFlag (λ _ → "●") t0' ∷nl
--   --   --              TermExpr.printFuExpr InvFlag (λ _ → "●") t1' ∷ₑ [])

--   --   let finalTrm = R.def (quote _∙∙_∙∙_)
--   --         ((R.def (quote evFuExpr≡evFF) (Ws v∷ expr0 v∷ [])) v∷
--   --          (R.def (quote refl) []) v∷
--   --          (R.def (quote sym)
--   --             ((R.def (quote evFuExpr≡evFF)) (Ws v∷ expr1 v∷ []) v∷ [])) v∷ [])
--   --   R.unify finalTrm hole


--   solveW : R.Term → R.Term → R.Term → R.TC Unit
--   solveW Ws Wts' hole = do
--     Wts ← quotedList→ListOfTerms Wts'
--     Wt ← tryAllTC
--       (R.typeError $ "At least one 𝑿 must be provded!" ∷ₑ [])
--       Wts R.returnTC
--     hoTy ← R.withNormalisation true $
--               R.inferType hole >>= wait-for-type
--     (t0 , t1) ←  (get-boundary hoTy ) >>= Mb.rec
--      (R.typeError [ R.strErr "unable to get boundary" ])
--      (λ x → R.returnTC x)
--     t0' ← tryWCE.tryE Ws Wts Wt magicNumber t0
--     t1' ← tryWCE.tryE Ws Wts Wt magicNumber t1
--     expr0 ← tryWCE.checkFromTE Ws Wts t0'
--     expr1 ← tryWCE.checkFromTE Ws Wts t1'   
--     -- R.typeError
--     let msg = (TermExpr.printFuExpr InvFlag (λ _ → "●") t0' ∷nl
--                  TermExpr.printFuExpr InvFlag (λ _ → "●") t1' ∷ₑ [])
--     invol0 ← R.normalise (R.def (quote FuExpr→FF) (Ws v∷ v[ expr0 ]))
--     invol1 ← R.normalise (R.def (quote FuExpr→FF) (Ws v∷ v[ expr1 ]))


--     red0 ← tryWCE.redList' Ws Wts Wt invol0
--     red1 ← tryWCE.redList' Ws Wts Wt invol1

--     let invPa0 = Li.map
--             (λ t' → just (R.def (quote evFF≡↓) (Ws v∷ Wt v∷ t' v∷ [])))
--             red0
--         invPa1 = Li.map
--             (λ t' → just (R.def (quote evFF≡↓) (Ws v∷ Wt v∷ t' v∷ [])))
--             red1
--     -- R.typeError (
--     --   (join (Li.map (λ x → "\n-- " ∷ₑ [ R.termErr x ] )  red0))
--     --      ++ₑ " " ∷nl " " ∷nl
--     --   (join (Li.map (λ x → "\n-- " ∷ₑ [ R.termErr x ] )  red1)) ++ₑ [])

-- --     -- invPa0 ← tryWCE.involPathTerm' Ws Wts Wt invol0 -->>= R.normalise
-- --     -- invPa1 ← tryWCE.involPathTerm' Ws Wts Wt  invol1 -->>= R.normalise

-- --     -- -- R.typeError (invol0 ∷nl
-- --     -- --              invol1 ∷ₑ [])

    

--     let finalTrm0 =
--            just (R.def (quote evFuExpr≡evFF) (Ws v∷ Wt v∷ expr0 v∷ []))
--            ∷ invPa0
--           -- R.def (quote _∙_)
--           -- ((R.def (quote evFuExpr≡evFF) (Ws v∷ Wt v∷ expr0 v∷ [])) v∷
--           --  invPa0 v∷ [])
--         finalTrm1 =
--            just (R.def (quote evFuExpr≡evFF) (Ws v∷ Wt v∷ expr1 v∷ []))
--            ∷ invPa1
--           -- R.def (quote _∙_)
--           -- ((R.def (quote evFuExpr≡evFF) (Ws v∷ Wt v∷ expr1 v∷ [])) v∷
--           --  invPa1 v∷ [])

--     let finalTrm = fromMaybe (R.def (quote refl) []) $ foldPathTerms
--            (finalTrm0 ++ symPathTerms finalTrm1)
--         -- --invPa0
--         --   R.def (quote _∙_)
--         --   (finalTrm0 v∷ --R.unknown v∷
--         --    (R.def (quote sym)
--         --       (finalTrm1 v∷ [])) v∷ [])

--     -- msg ← R.formatErrorParts (finalTrm ∷ₑ [])

--     -- R.typeError (msg ∷ₑ [])

--     (R.unify finalTrm hole) -- <|> R.typeError msg



-- module _ (G : Group ℓ) where
--  open GroupStr (snd G)
--  Group→WildGroupoid : WildGroupoid ℓ-zero ℓ
--  WildCat.ob (WildGroupoid.wildCat Group→WildGroupoid) = Unit
--  WildCat.Hom[_,_] (WildGroupoid.wildCat Group→WildGroupoid) _ _ = ⟨ G ⟩
--  WildCat.id (WildGroupoid.wildCat Group→WildGroupoid) = 1g
--  WildCat._⋆_ (WildGroupoid.wildCat Group→WildGroupoid) = _·_
--  WildCat.⋆IdL (WildGroupoid.wildCat Group→WildGroupoid) = ·IdL
--  WildCat.⋆IdR (WildGroupoid.wildCat Group→WildGroupoid) = ·IdR
--  WildCat.⋆Assoc (WildGroupoid.wildCat Group→WildGroupoid) _ _ _ = sym (·Assoc _ _ _) 
--  wildIsIso.inv' (WildGroupoid.isWildGroupoid Group→WildGroupoid f) = inv f
--  wildIsIso.sect (WildGroupoid.isWildGroupoid Group→WildGroupoid f) = ·InvL f
--  wildIsIso.retr (WildGroupoid.isWildGroupoid Group→WildGroupoid f) = ·InvR f


-- GroupWS : WildStr ℓ-zero ℓ
-- GroupoidWS WildCatWS : WildStr ℓ ℓ'

-- WildStr.wildStr (GroupWS {ℓ}) = Group ℓ
-- WildStr.toWildCat (GroupWS) = WildGroupoid.wildCat ∘ Group→WildGroupoid
-- WildStr.mbIsWildGroupoid GroupWS = just (WildGroupoid.isWildGroupoid ∘ Group→WildGroupoid)

-- WildStr.wildStr (GroupoidWS {ℓ} {ℓ'}) = WildGroupoid ℓ ℓ'
-- WildStr.toWildCat GroupoidWS = WildGroupoid.wildCat
-- WildStr.mbIsWildGroupoid GroupoidWS = just WildGroupoid.isWildGroupoid



