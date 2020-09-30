{-

  Homotopy colimits of graphs

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.HITs.Colimit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Graph

{-
-- Cones under a diagram

record Cocone ℓ {ℓd ℓv ℓe} {I : Graph ℓv ℓe} (F : Diag ℓd I) (X : Type ℓ)
              : Type (ℓ-suc (ℓ-max ℓ (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc ℓd)))) where
  field
    leg : ∀ (j : Obj I) → F $ j → X
    com : ∀ {j k} (f : Hom I j k) → leg k ∘ F <$> f ≡ leg j

  postcomp : ∀ {ℓ'} {Y : Type ℓ'} → (X → Y) → Cocone ℓ' F Y
  leg (postcomp h) j = h ∘ leg j
  com (postcomp h) f = cong (h ∘_) (com f)

open Cocone public


-- Σ (Type ℓ) (Cocone ℓ F) forms a category:

module _ {ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} where

  private
    -- the "lower star" functor
    _* : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} → (X → Y) → Cocone _ F X → Cocone _ F Y
    (h *) C = postcomp C h

  CoconeMor : ∀ {ℓ ℓ'} → Σ (Type ℓ) (Cocone ℓ F) → Σ (Type ℓ') (Cocone ℓ' F) → Type _
  CoconeMor (X , C) (Y , D) = Σ[ h ∈ (X → Y) ] (h *) C ≡ D

  idCoconeMor : ∀ {ℓ} (Cp : Σ (Type ℓ) (Cocone ℓ F)) → CoconeMor Cp Cp
  idCoconeMor Cp = (λ x → x) , refl

  compCoconeMor : ∀ {ℓ ℓ' ℓ''} {C : Σ (Type ℓ) (Cocone ℓ F)} {D : Σ (Type ℓ') (Cocone ℓ' F)}
                    {E : Σ (Type ℓ'') (Cocone ℓ'' F)}
                  → CoconeMor D E → CoconeMor C D → CoconeMor C E
  compCoconeMor (g , q) (f , p) = g ∘ f , (cong (g *) p) ∙ q


-- Universal cocones are initial objects in the category Σ (Type ℓ) (Cocone ℓ F)

module _ {ℓ ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} {X : Type ℓ} where

  isUniversalAt : ∀ ℓq → Cocone ℓ F X → Type (ℓ-max ℓ (ℓ-suc (ℓ-max ℓq (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc ℓd)))))
  isUniversalAt ℓq C = ∀ (Y : Type ℓq) → isEquiv {A = (X → Y)} {B = Cocone ℓq F Y} (postcomp C)
                  -- (unfolding isEquiv, this ^ is equivalent to what one might expect:)
                  -- ∀ (Y : Type ℓ) (D : Cocone ℓ F Y) → ∃![ h ∈ (X → Y) ] (h *) C ≡ D
                  --                                  (≡ isContr (CoconeMor (X , C) (Y , D)))

  isPropIsUniversalAt : ∀ ℓq (C : Cocone ℓ F X) → isProp (isUniversalAt ℓq C)
  isPropIsUniversalAt ℓq C = isPropΠ (λ Y → isPropIsEquiv (postcomp C))

  isUniversal : Cocone ℓ F X → Typeω
  isUniversal C = ∀ ℓq → isUniversalAt ℓq C


-- Colimits are universal cocones

record isColimit {ℓ ℓd ℓv ℓe} {I : Graph ℓv ℓe} (F : Diag ℓd I) (X : Type ℓ) : Typeω where
  field
    cone : Cocone ℓ F X
    univ : isUniversal cone
open isColimit public

module _ {ℓ ℓ' ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} {X : Type ℓ} {Y : Type ℓ'} where

  postcomp⁻¹ : isColimit F X → Cocone ℓ' F Y → (X → Y)
  postcomp⁻¹ cl = invEq (_ , univ cl _ Y)

  postcomp⁻¹-inv : (cl : isColimit F X) (D : Cocone ℓ' F Y) → (postcomp (cone cl) (postcomp⁻¹ cl D)) ≡ D
  postcomp⁻¹-inv cl D = retEq (_ , univ cl _ Y) D

  postcomp⁻¹-mor : (cl : isColimit F X) (D : Cocone ℓ' F Y) → CoconeMor (X , cone cl) (Y , D)
  postcomp⁻¹-mor cl D = (postcomp⁻¹ cl D) , (postcomp⁻¹-inv cl D)

-- Colimits are unique

module _ {ℓ ℓ' ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} {X : Type ℓ} {Y : Type ℓ'} where

  uniqColimit : isColimit F X → isColimit F Y → X ≃ Y
  uniqColimit cl cl'
    = isoToEquiv (iso (fst fwd) (fst bwd)
                      (λ x i → fst (isContr→isProp (equiv-proof (univ cl' ℓ' Y) (cone cl'))
                                                   (compCoconeMor fwd bwd)
                                                   (idCoconeMor (Y , cone cl')) i) x)
                      (λ x i → fst (isContr→isProp (equiv-proof (univ cl ℓ  X) (cone cl))
                                                   (compCoconeMor bwd fwd)
                                                   (idCoconeMor (X , cone cl)) i) x))
    where fwd : CoconeMor (X , cone cl ) (Y , cone cl')
          bwd : CoconeMor (Y , cone cl') (X , cone cl )
          fwd = postcomp⁻¹-mor cl (cone cl')
          bwd = postcomp⁻¹-mor cl' (cone cl)

-- Colimits always exist

data colim {ℓd ℓe ℓv} {I : Graph ℓv ℓe} (F : Diag ℓd I) : Type (ℓ-suc (ℓ-max (ℓ-max ℓv ℓe) (ℓ-suc ℓd))) where
  colim-leg : ∀ (j : Obj I) → F $ j → colim F
  colim-com : ∀ {j k} (f : Hom I j k) → colim-leg k ∘ F <$> f ≡ colim-leg j

module _ {ℓd ℓv ℓe} {I : Graph ℓv ℓe} {F : Diag ℓd I} where

  colimCone : Cocone _ F (colim F)
  leg colimCone = colim-leg
  com colimCone = colim-com

  rec : ∀ {ℓ} {X : Type ℓ} → Cocone ℓ F X → (colim F → X)
  rec C (colim-leg j A)   = leg C j A
  rec C (colim-com f i A) = com C f i A

  colimIsColimit : isColimit F (colim F)
  cone colimIsColimit = colimCone
  univ colimIsColimit ℓq Y
    = isoToIsEquiv record { fun = postcomp colimCone
                          ; inv = rec
                          ; rightInv = λ C → refl
                          ; leftInv  = λ h → funExt (eq h) }
    where eq : ∀ h (x : colim _) → rec (postcomp colimCone h) x ≡ h x
          eq h (colim-leg j A)   = refl
          eq h (colim-com f i A) = refl

-}



---
open import Cubical.HITs.Sn
open import Cubical.HITs.S1
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Sn
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.HITs.Truncation.FromNegOne renaming (rec to trRec ; elim to trElim ; elim2 to trElim2)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.Empty

record Graph2 {ℓ ℓ'} : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  field
    Obj2 : Type ℓ
    Fam : Obj2 → Obj2 → Type ℓ' -- condition on arrows

open Graph2
record Diagram {ℓ ℓ' ℓ''} (G : Graph2 {ℓ} {ℓ'}) : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') ℓ'')) where
  no-eta-equality
  field
    Types : Obj2 G → Type ℓ''
    Funs : (x y : Obj2 G) → (Fam G x y) → Types x → Types y

open Diagram

data Colim2 {ℓ ℓ' ℓ''} (G : Graph2 {ℓ} {ℓ'}) (d : Diagram {ℓ'' = ℓ''} G) : Type (ℓ-suc (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') ℓ''))) where
 inc : (x : Obj2 G) → Types d x → Colim2 G d
 inc≡ : (x y : Obj2 G) (γ : Fam G x y) (a : Types d x) → inc y (Funs d x y γ a) ≡ inc x a

2×Graph :  ∀ {ℓ ℓ'} (G : Graph2 {ℓ} {ℓ'}) → Graph2
Obj2 (2×Graph G) = Obj2 G ⊎ Obj2 G
Fam (2×Graph G) (inl x) (inl x₁) = Fam G x x₁
Fam (2×Graph G) (inl x) (inr x₁) = Fam G x x₁
Fam (2×Graph G) (inr x) (inl x₁) = Fam G x x₁
Fam (2×Graph G) (inr x) (inr x₁) = Fam G x x₁

2×Dia : ∀ {ℓ ℓ' ℓ''} (G : Graph2 {ℓ} {ℓ'}) (d d' : Diagram {ℓ'' = ℓ''} G) → Diagram (2×Graph G)
Types (2×Dia G d d') (inl x) = Types d x
Types (2×Dia G d d') (inr x) = Types d' x
Funs (2×Dia G d d') (inl x) (inl x₁) = Funs d x x₁
Funs (2×Dia G d d') (inl x) (inr x₁) z = {!!}
Funs (2×Dia G d d') (inr x) y _ = {!!}

module _ {ℓ ℓ'} {A : ℕ → Type ℓ} {B : ℕ → Type ℓ} (F : (n : ℕ) → A n → B n) (Afam : (n : ℕ) → A n → A (suc n)) (Bfam : (n : ℕ) → B n → B (suc n)) (comm : (n : ℕ) → Bfam n ∘ F n ≡ F (suc n) ∘ Afam n) where
  theGraph : Graph2
  Obj2 theGraph = ℕ × Bool -- true = left, false = right
  Fam theGraph (n , false) (m , false) = suc n ≡ m
  Fam theGraph (n , true) (m , false) = n ≡ m
  Fam theGraph (n , false) (m , true) = ⊥
  Fam theGraph (n , true) (m , true) = suc n ≡ m

  theDiag : Diagram theGraph
  Types theDiag (n , false) = B n
  Types theDiag (n , true) = A n
  Funs theDiag (n , false) (m , false) p x = subst B p (Bfam n x)
  Funs theDiag (n , true) (m , false) p x = subst B p (F n x)
  Funs theDiag (n , true) (m , true) p x = subst A p (Afam n x)

  mainGraph : Graph2
  Obj2 mainGraph = ℕ
  Fam mainGraph n m = suc n ≡ m

  diagL : Diagram mainGraph
  Types diagL = A
  Funs diagL x y p a = subst A p (Afam x a)

  diagR : Diagram mainGraph
  Types diagR = B
  Funs diagR x y p b = subst B p (Bfam x b)

  indFun : Colim2 mainGraph diagL → Colim2 mainGraph diagR
  indFun (inc x x₁) = inc x (F x x₁)
  indFun (inc≡ x y γ a i) = helper γ i
    where
    helper : (γ : suc x ≡ y) → Path (Colim2 mainGraph diagR) (inc y (F y (subst A γ (Afam x a)))) (inc x (F x a))
    helper = J (λ y γ →  Path (Colim2 mainGraph diagR) (inc y (F y (subst A γ (Afam x a)))) (inc x (F x a)))
               ((λ i → inc (suc x) (F (suc x) (transportRefl (Afam x a) i)))
             ∙∙ (λ i → inc (suc x) (comm x (~ i) a))
             ∙∙ ((λ i → inc (suc x) (transportRefl (Bfam x (F x a)) (~ i)))
             ∙ inc≡ x (suc x) refl (F x a)))

  colim→Prop : ∀ {ℓ ℓ' ℓ'' ℓ'''} → {G : Graph2 {ℓ} {ℓ'}} {d : Diagram {ℓ'' = ℓ''} G}
             → {P : Colim2 G d → Type ℓ'''}
             → ((x : Colim2 G d) → isProp (P x))
             → ((x : Obj2 G) (y : Types d x) → P (inc x y))
             → (x : Colim2 G d) → P x
  colim→Prop {P = P} h indhyp (inc x x₁) = indhyp x x₁
  colim→Prop  {G = G} {d = d} {P = P} h indhyp (inc≡ x y γ a i) =
    isProp→PathP {B = λ i → P (inc≡ x y γ a i)} (λ i → h _) (indhyp y (Funs d x y γ a)) (indhyp x a) i

  connectedIndFun : (n : ℕ) → ((m : ℕ) → isConnectedFun n (F m)) → isConnectedFun n indFun
  connectedIndFun zero iscon = λ _ → tt* , (λ {tt* → refl})
  connectedIndFun (suc zero) iscon = 
    colim→Prop (λ _ → isPropIsContr)
               λ n b → trRec {!!} (λ fibpt → ∣ (inc n (fibpt .fst)) , (cong (inc n) (fibpt .snd)) ∣ , (λ _ → isOfHLevelTrunc {A = fiber indFun (inc n b)} 1 _ _)) (iscon n b .fst)
  connectedIndFun (suc (suc n)) iscon = {!!}

colimDiag : ∀ {ℓ ℓ' ℓ''} (G : Graph2 {ℓ} {ℓ'}) (d d' : Diagram {ℓ'' = ℓ''} G) → Diagram {!!}
Types (colimDiag G d d') x = {!!}
Funs (colimDiag G d d') = {!!}

colimIndFun : ∀ {ℓ ℓ' ℓ''} (G : Graph2 {ℓ} {ℓ'}) (d d' : Diagram {ℓ'' = ℓ''} G)
              → (x y : Obj2 G) (z : Fam G x y)
              → Colim2 {!!} {!!}
colimIndFun = {!!}
 
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence
open import Cubical.HITs.Susp

data James {ℓ} (A : Pointed ℓ) : Type ℓ where
  € : James A
  α : typ A → James A → James A
  δ : (x : James A) → x ≡ α (pt A) x 

mainlemma : ∀ {ℓ} {A : Pointed ℓ} → isConnected 2 (typ A) → Iso (James A) (Path (Susp (typ A)) north north)
mainlemma {ℓ} {A = A , a} con = {!!}
  where
  IsoJam : (x : A) → isEquiv (α {A = (A , a)} x)
  IsoJam x = trRec (isPropIsEquiv _)
                   (λ r → subst (λ x → isEquiv (α x)) r
                           (subst isEquiv (funExt δ) (idIsEquiv (James _))) )
                   (Iso.fun (PathIdTruncIso 1)
                            (isOfHLevelSuc 0 con ∣ a ∣ ∣ x ∣))

  Codes : Susp A → Type ℓ
  Codes north = James (A , a)
  Codes south = James (A , a)
  Codes (merid x i) = ua ((α x) , IsoJam x) i

  isContrTotal : isContr (Σ[ x ∈ Susp A ] Codes x)
  isContrTotal = (north , €)
                , {!!}

    where
    tihi : (y : Σ (Susp A) (λ x → Codes x)) → (north , €) ≡ y
    tihi (north , c) = {!!}
    tihi (south , c) = {!!}
    tihi (merid a i , c) = {!!}
    open import Cubical.HITs.Pushout

    αcurry : A × James (A , a) → James (A , a)
    αcurry (a , c) = α a c



    T : Type ℓ
    T = Pushout {A = A × James (A , a)} snd αcurry

    T=James : Iso (Σ (Susp A) Codes) T
    Iso.fun T=James (north , b) = inl b -- α a b
    Iso.fun T=James (south , b) = inr b
    Iso.fun T=James (merid x i , b) = hcomp (λ k → λ {(i = i0) → ((λ i → inr (transportRefl (α x b) i)) ∙∙ sym (push (x , b)) ∙∙ refl) k ; (i = i1) → transportRefl (inr b) k}) (inr ((transport (λ j → ua ((α x) , IsoJam x) (i ∨ j)) b)))
    Iso.inv T=James (inl x) = north , x
    Iso.inv T=James (inr x) = south , x
    Iso.inv T=James (push (x , jm) i) = merid x i , hcomp (λ k → λ {(i = i0) → transportRefl jm k ; (i = i1) → (transportRefl (α x jm)) k}) (transport (λ j → ua (α x , IsoJam x) (i ∧ j)) jm)
    Iso.rightInv T=James (inl x) = refl
    Iso.rightInv T=James (inr x) = refl
    Iso.rightInv T=James (push (x , jm) i) j = help! j i
      where
      test : {!!}
      test = {!!}

      help! : cong (Iso.fun T=James ∘ Iso.inv T=James) (push (x , jm)) ≡ push (x , jm)
      help! = (λ j i → hcomp (λ k →  λ { (i = i0) → doubleCompPath-filler (λ i → inr (transportRefl (α x jm) i)) (sym (push (x , jm))) refl (~ j) k
                                    ; (i = i1) → transportRefl (inr (α x jm)) (j ∨ k)
                                    ; (j = i1) → push (x , jm) (i ∨ (~ k))})
                             (hcomp (λ k → λ { (i = i0) → inr (α (transportRefl x j) (transportRefl jm j))
                                             ; (j = i0) → inr
                                                              (transport (λ j₂ → ua (α x , IsoJam x) (i ∨ j₂))
                                                               (hcomp
                                                                (λ r → λ { (i = i0) → transportRefl jm r
                                                                       ; (i = i1) → transportRefl (α x jm) r
                                                                   })
                                                                (transport (λ j₂ → ua (α x , IsoJam x) (i ∧ j₂)) jm))) -- inr (transportRefl (α x (transportRefl jm {!!})) (~ k))
                                             ; (i = i1) → transportRefl (inr (α x jm)) j -- transportRefl (inr (α x jm)) (j ∨ ~ k) -- transportRefl (inr (α x {!!})) (j ∨ (~ k))
                                             ; (j = i1) → inr (α x jm) })-- inr (α x jm)  })
                                    {!!}))

    Iso.leftInv T=James (north , b) = refl
    Iso.leftInv T=James (south , b) = refl
    Iso.leftInv T=James (merid a i , b) = {!!}

    TPathHelp : (x : James (A , a)) → Path T (inl x) (inl €)
    TPathHelp € = refl
    TPathHelp (α x x₁) = ((push (a , α x x₁) ∙∙ (λ i → inr (δ (α x x₁) (~ i))) ∙∙ sym (push (x , x₁)))) ∙ TPathHelp x₁
    TPathHelp (δ x i) j = hcomp (λ k → λ { (i = i0) → TPathHelp x (j ∧ k)
                     ; (j = i0) → inl (δ x i)
                     ; (j = i1) → TPathHelp x k})
                     (hcomp (λ k → λ { (i = i0) → inl (δ x (~ j ∧ ~ k))
                                     ; (i = i1) → (push (a , α a x) ∙∙ (λ i → inr (δ (α a x) (~ i))) ∙∙ sym (push (a , x))) j
                                     ; (j = i0) → inl (δ x (i ∨ ~ k))
                                     ; (j = i1) → inl x})
                                            {!!})

      where
      help : Path (Path T _ _)
         (push (a , α a x)
         ∙∙ (λ i → inr (δ (α a x) (~ i)))
        ∙∙ sym (push (a , x)))
        (λ i → inl (δ x (~ i)))
      help = {!!}

    TPath : (x : T) → x ≡ inl €
    TPath (inl x) = TPathHelp x
    TPath (inr x) = ((λ i → inr (δ x i)) ∙ sym (push (a , x))) ∙ TPathHelp x
    TPath (push (b , x) j) i = 
      hcomp (λ k → λ { (i = i0) → push (b , x) j
                     ; (j = i1) → {!compPath-filler ((λ i → inr (δ x i)) ∙ sym (push (a , x))) (TPathHelp x)!}
                     ; (j = i0) → TPathHelp x (i ∧ k)
                     ; (i = i1) → TPathHelp x k})
            {!!}

{-
j = i0 ⊢ TPathHelp x i
j = i1 ⊢ ((λ i₁ → inr (δ (αcurry (a , x)) i₁)) ∙∙
          (λ i₁ → push (a₁ , αcurry (a , x)) (~ i₁)) ∙∙
          ((push (a₁ , α a x) ∙∙ (λ i₁ → inr (δ (α a x) (~ i₁))) ∙∙
            (λ i₁ → push (a , x) (~ i₁)))
           ∙ TPathHelp x))
         i
i = i0 ⊢ push (a , x) j
i = i1 ⊢ inl €
-}
