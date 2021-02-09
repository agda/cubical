{-

Basic properties about Σ-types

- Action of Σ on functions ([map-fst], [map-snd])
- Characterization of equality in Σ-types using dependent paths ([ΣPath{Iso,≃,≡}PathΣ], [Σ≡Prop])
- Proof that discrete types are closed under Σ ([discreteΣ])
- Commutativity and associativity ([Σ-swap-*, Σ-assoc-*])
- Distributivity of Π over Σ ([Σ-Π-*])
- Action of Σ on isomorphisms, equivalences, and paths ([Σ-cong-fst], [Σ-cong-snd], ...)
- Characterization of equality in Σ-types using transport ([ΣPathTransport{≃,≡}PathΣ])
- Σ with a contractible base is its fiber ([Σ-contractFst, ΣUnit])

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Sigma.Properties where

open import Cubical.Data.Sigma.Base

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary
open import Cubical.Data.Unit.Base

open Iso

private
  variable
    ℓ ℓ' : Level
    A A' : Type ℓ
    B B' : (a : A) → Type ℓ
    C : (a : A) (b : B a) → Type ℓ

map-fst : {B : Type ℓ} → (f : A → A') → A × B → A' × B
map-fst f (a , b) = (f a , b)

map-snd : (∀ {a} → B a → B' a) → Σ A B → Σ A B'
map-snd f (a , b) = (a , f b)

map-× : {B : Type ℓ} {B' : Type ℓ'} → (A → A') → (B → B') → A × B → A' × B'
map-× f g (a , b) = (f a , g b)

≡-× : {A : Type ℓ} {B : Type ℓ'} {x y : A × B} → fst x ≡ fst y → snd x ≡ snd y → x ≡ y
≡-× p q i = (p i) , (q i)


-- Characterization of paths in Σ using dependent paths

-- <<<<<<< HEAD
-- ΣPathP : ∀ {x y}
--        → Σ[ p ∈ (fst x ≡ fst y) ] PathP (λ i → B (p i)) (snd x) (snd y)
--        → x ≡ y
-- ΣPathP eq i = fst eq i , snd eq i


-- ΣPathIsoPathΣ : {x y : Σ A B}
--               → Iso (Σ[ p ∈ fst x ≡ fst y ] (PathP (λ i → B (p i)) (snd x) (snd y)))
--                     (x ≡ y)
-- fun ΣPathIsoPathΣ        = ΣPathP
-- inv ΣPathIsoPathΣ eq     = (λ i → fst (eq i)) , (λ i → snd (eq i))
-- rightInv ΣPathIsoPathΣ _ = refl
-- leftInv ΣPathIsoPathΣ _  = refl

-- ΣPathPIsoPathPΣ : {A : I → Type ℓ} → {B : ∀ i → A i → Type ℓ' }
--                       → {a : Σ (A i0) (B i0)} → {b : Σ (A i1) (B i1)}
--                       → Iso (Σ[ p ∈ (PathP A (fst a) (fst b)) ]
--                                   (PathP (λ i → B i (p i)) (snd a) (snd b)))
--                             (PathP (λ i → Σ (A i) (B i)) a b)
-- ΣPathPIsoPathPΣ =
--   iso (λ x i → _ , (snd x i)) (λ x → _ , (λ i → snd (x i)))
--        (λ _ → refl) λ _ → refl

-- ΣPath≃PathΣ : {x y : Σ A B}
--             → (Σ[ p ∈ (fst x ≡ fst y) ] PathP (λ i → B (p i)) (snd x) (snd y))
--             ≃ (x ≡ y)
-- ΣPath≃PathΣ = isoToEquiv ΣPathIsoPathΣ

-- ΣPath≡PathΣ : {x y : Σ A B}
--             → (Σ[ p ∈ (fst x ≡ fst y) ] PathP (λ i → B (p i)) (snd x) (snd y))
--             ≡ (x ≡ y)
-- ΣPath≡PathΣ = ua ΣPath≃PathΣ
-- =======
module _ {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
  {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)}
  where

  ΣPathP : Σ[ p ∈ PathP A (fst x) (fst y) ] PathP (λ i → B i (p i)) (snd x) (snd y)
         → PathP (λ i → Σ (A i) (B i)) x y
  ΣPathP eq i = fst eq i , snd eq i

  PathPΣ : PathP (λ i → Σ (A i) (B i)) x y
         → Σ[ p ∈ PathP A (fst x) (fst y) ] PathP (λ i → B i (p i)) (snd x) (snd y)
  PathPΣ eq = (λ i → fst (eq i)) , (λ i → snd (eq i))

  -- allows one to write
  -- open PathPΣ somePathInΣAB renaming (fst ... )
  module PathPΣ (p : PathP (λ i → Σ (A i) (B i)) x y) where
    open Σ (PathPΣ p) public

  ΣPathIsoPathΣ : Iso (Σ[ p ∈ PathP A (fst x) (fst y) ] (PathP (λ i → B i (p i)) (snd x) (snd y)))
                      (PathP (λ i → Σ (A i) (B i)) x y)
  fun ΣPathIsoPathΣ        = ΣPathP
  inv ΣPathIsoPathΣ        = PathPΣ
  rightInv ΣPathIsoPathΣ _ = refl
  leftInv ΣPathIsoPathΣ _  = refl

  ΣPath≃PathΣ : (Σ[ p ∈ PathP A (fst x) (fst y) ] (PathP (λ i → B i (p i)) (snd x) (snd y)))
              ≃ (PathP (λ i → Σ (A i) (B i)) x y)
  ΣPath≃PathΣ = isoToEquiv ΣPathIsoPathΣ

  ΣPath≡PathΣ : (Σ[ p ∈ PathP A (fst x) (fst y) ] (PathP (λ i → B i (p i)) (snd x) (snd y)))
              ≡ (PathP (λ i → Σ (A i) (B i)) x y)
  ΣPath≡PathΣ = ua ΣPath≃PathΣ

×≡Prop : isProp A' → {u v : A × A'} → u .fst ≡ v .fst → u ≡ v
×≡Prop pB {u} {v} p i = (p i) , (pB (u .snd) (v .snd) i)

-- Characterization of dependent paths in Σ

module _ {A : I → Type ℓ} {B : (i : I) → (a : A i) → Type ℓ'}
  {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)}
  where

  ΣPathPIsoPathPΣ :
    Iso (Σ[ p ∈ PathP A (x .fst) (y .fst) ] PathP (λ i → B i (p i)) (x .snd) (y .snd))
        (PathP (λ i → Σ (A i) (B i)) x y)
  ΣPathPIsoPathPΣ .fun (p , q) i = p i , q i
  ΣPathPIsoPathPΣ .inv pq .fst i = pq i .fst
  ΣPathPIsoPathPΣ .inv pq .snd i = pq i .snd
  ΣPathPIsoPathPΣ .rightInv _ = refl
  ΣPathPIsoPathPΣ .leftInv _ = refl

  ΣPathP≃PathPΣ = isoToEquiv ΣPathPIsoPathPΣ

  ΣPathP≡PathPΣ = ua ΣPathP≃PathPΣ

-- Σ of discrete types

discreteΣ : Discrete A → ((a : A) → Discrete (B a)) → Discrete (Σ A B)
discreteΣ {B = B} Adis Bdis (a0 , b0) (a1 , b1) = discreteΣ' (Adis a0 a1)
  where
    discreteΣ' : Dec (a0 ≡ a1) → Dec ((a0 , b0) ≡ (a1 , b1))
    discreteΣ' (yes p) = J (λ a1 p → ∀ b1 → Dec ((a0 , b0) ≡ (a1 , b1))) (discreteΣ'') p b1
      where
        discreteΣ'' : (b1 : B a0) → Dec ((a0 , b0) ≡ (a0 , b1))
        discreteΣ'' b1 with Bdis a0 b0 b1
        ... | (yes q) = yes (transport ΣPath≡PathΣ (refl , q))
        ... | (no ¬q) = no (λ r → ¬q (subst (λ X → PathP (λ i → B (X i)) b0 b1) (Discrete→isSet Adis a0 a0 (cong fst r) refl) (cong snd r)))
    discreteΣ' (no ¬p) = no (λ r → ¬p (cong fst r))

Σ-swap-Iso : Iso (A × A') (A' × A)
fun Σ-swap-Iso (x , y) = (y , x)
inv Σ-swap-Iso (x , y) = (y , x)
rightInv Σ-swap-Iso _ = refl
leftInv Σ-swap-Iso _  = refl

Σ-swap-≃ : A × A' ≃ A' × A
Σ-swap-≃ = isoToEquiv Σ-swap-Iso

Σ-assoc-Iso : Iso (Σ[ (a , b) ∈ Σ A B ] C a b) (Σ[ a ∈ A ] Σ[ b ∈ B a ] C a b)
fun Σ-assoc-Iso ((x , y) , z) = (x , (y , z))
inv Σ-assoc-Iso (x , (y , z)) = ((x , y) , z)
rightInv Σ-assoc-Iso _ = refl
leftInv Σ-assoc-Iso _  = refl

Σ-assoc-≃ : (Σ[ (a , b) ∈ Σ A B ] C a b) ≃ (Σ[ a ∈ A ] Σ[ b ∈ B a ] C a b)
Σ-assoc-≃ = isoToEquiv Σ-assoc-Iso

Σ-Π-Iso : Iso ((a : A) → Σ[ b ∈ B a ] C a b) (Σ[ f ∈ ((a : A) → B a) ] ∀ a → C a (f a))
fun Σ-Π-Iso f         = (fst ∘ f , snd ∘ f)
inv Σ-Π-Iso (f , g) x = (f x , g x)
rightInv Σ-Π-Iso _    = refl
leftInv Σ-Π-Iso _     = refl

Σ-Π-≃ : ((a : A) → Σ[ b ∈ B a ] C a b) ≃ (Σ[ f ∈ ((a : A) → B a) ] ∀ a → C a (f a))
Σ-Π-≃ = isoToEquiv Σ-Π-Iso

Σ-cong-iso-fst : (isom : Iso A A') → Iso (Σ A (B ∘ fun isom)) (Σ A' B)
fun (Σ-cong-iso-fst isom) x = fun isom (x .fst) , x .snd
inv (Σ-cong-iso-fst {B = B} isom) x = inv isom (x .fst) , subst B (sym (ε (x .fst))) (x .snd)
  where
  ε = isHAEquiv.rinv (snd (iso→HAEquiv isom))
rightInv (Σ-cong-iso-fst {B = B} isom) (x , y) = ΣPathP (ε x , toPathP goal)
  where
  ε = isHAEquiv.rinv (snd (iso→HAEquiv isom))
  goal : subst B (ε x) (subst B (sym (ε x)) y) ≡ y
  goal = sym (substComposite B (sym (ε x)) (ε x) y)
      ∙∙ cong (λ x → subst B x y) (lCancel (ε x))
      ∙∙ substRefl {B = B} y
leftInv (Σ-cong-iso-fst {A = A} {B = B} isom) (x , y) = ΣPathP (leftInv isom x , toPathP goal)
  where
  ε = isHAEquiv.rinv (snd (iso→HAEquiv isom))
  γ = isHAEquiv.com (snd (iso→HAEquiv isom))

  lem : (x : A) → sym (ε (fun isom x)) ∙ cong (fun isom) (leftInv isom x) ≡ refl
  lem x = cong (λ a → sym (ε (fun isom x)) ∙ a) (γ x) ∙ lCancel (ε (fun isom x))

  goal : subst B (cong (fun isom) (leftInv isom x)) (subst B (sym (ε (fun isom x))) y) ≡ y
  goal = sym (substComposite B (sym (ε (fun isom x))) (cong (fun isom) (leftInv isom x)) y)
      ∙∙ cong (λ a → subst B a y) (lem x)
      ∙∙ substRefl {B = B} y

Σ-cong-equiv-fst : (e : A ≃ A') → Σ A (B ∘ equivFun e) ≃ Σ A' B
-- we could just do this:
-- Σ-cong-equiv-fst e = isoToEquiv (Σ-cong-iso-fst (equivToIso e))
-- but the following reduces slightly better
Σ-cong-equiv-fst {A = A} {A' = A'} {B = B} e = intro , isEqIntro
 where
  intro : Σ A (B ∘ equivFun e) → Σ A' B
  intro (a , b) = equivFun e a , b
  isEqIntro : isEquiv intro
  isEqIntro .equiv-proof x = ctr , isCtr where
    PB : ∀ {x y} → x ≡ y → B x → B y → Type _
    PB p = PathP (λ i → B (p i))

    open Σ x renaming (fst to a'; snd to b)
    open Σ (equivCtr e a') renaming (fst to ctrA; snd to α)
    ctrB : B (equivFun e ctrA)
    ctrB = subst B (sym α) b
    ctrP : PB α ctrB b
    ctrP = symP (transport-filler (λ i → B (sym α i)) b)
    ctr : fiber intro x
    ctr = (ctrA , ctrB) , ΣPathP (α , ctrP)

    isCtr : ∀ y → ctr ≡ y
    isCtr ((r , s) , p) = λ i → (a≡r i , b!≡s i) , ΣPathP (α≡ρ i , coh i) where
      open PathPΣ p renaming (fst to ρ; snd to σ)
      open PathPΣ (equivCtrPath e a' (r , ρ)) renaming (fst to a≡r; snd to α≡ρ)

      b!≡s : PB (cong (equivFun e) a≡r) ctrB s
      b!≡s i = comp (λ k → B (α≡ρ i (~ k))) (λ k → (λ
        { (i = i0) → ctrP (~ k)
        ; (i = i1) → σ (~ k)
        })) b

      coh : PathP (λ i → PB (α≡ρ i) (b!≡s i) b) ctrP σ
      coh i j = fill (λ k → B (α≡ρ i (~ k))) (λ k → (λ
        { (i = i0) → ctrP (~ k)
        ; (i = i1) → σ (~ k)
        })) (inS b) (~ j)

Σ-cong-fst : (p : A ≡ A') → Σ A (B ∘ transport p) ≡ Σ A' B
Σ-cong-fst {B = B} p i = Σ (p i) (B ∘ transp (λ j → p (i ∨ j)) i)

Σ-cong-iso-snd : ((x : A) → Iso (B x) (B' x)) → Iso (Σ A B) (Σ A B')
fun (Σ-cong-iso-snd isom) (x , y) = x , fun (isom x) y
inv (Σ-cong-iso-snd isom) (x , y') = x , inv (isom x) y'
rightInv (Σ-cong-iso-snd isom) (x , y) = ΣPathP (refl , rightInv (isom x) y)
leftInv (Σ-cong-iso-snd isom) (x , y') = ΣPathP (refl , leftInv (isom x) y')

Σ-cong-equiv-snd : (∀ a → B a ≃ B' a) → Σ A B ≃ Σ A B'
Σ-cong-equiv-snd h = isoToEquiv (Σ-cong-iso-snd (equivToIso ∘ h))

Σ-cong-snd : ((x : A) → B x ≡ B' x) → Σ A B ≡ Σ A B'
Σ-cong-snd {A = A} p i = Σ[ x ∈ A ] (p x i)

Σ-cong-iso : (isom : Iso A A')
           → ((x : A) → Iso (B x) (B' (fun isom x)))
           → Iso (Σ A B) (Σ A' B')
Σ-cong-iso isom isom' = compIso (Σ-cong-iso-snd isom') (Σ-cong-iso-fst isom)

Σ-cong-equiv : (e : A ≃ A')
             → ((x : A) → B x ≃ B' (equivFun e x))
             → Σ A B ≃ Σ A' B'
Σ-cong-equiv e e' = isoToEquiv (Σ-cong-iso (equivToIso e) (equivToIso ∘ e'))

Σ-cong' : (p : A ≡ A') → PathP (λ i → p i → Type ℓ') B B' → Σ A B ≡ Σ A' B'
Σ-cong' p p' = cong₂ (λ (A : Type _) (B : A → Type _) → Σ A B) p p'

-- Alternative version for path in Σ-types, as in the HoTT book

ΣPathTransport : (a b : Σ A B) → Type _
ΣPathTransport {B = B} a b = Σ[ p ∈ (fst a ≡ fst b) ] transport (λ i → B (p i)) (snd a) ≡ snd b

IsoΣPathTransportPathΣ : (a b : Σ A B) → Iso (ΣPathTransport a b) (a ≡ b)
IsoΣPathTransportPathΣ {B = B} a b = compIso (Σ-cong-iso-snd (λ p → invIso (equivToIso (PathP≃Path (λ i → B (p i)) _ _))))
         ΣPathIsoPathΣ

ΣPathTransport≃PathΣ : (a b : Σ A B) → ΣPathTransport a b ≃ (a ≡ b)
ΣPathTransport≃PathΣ {B = B} a b = isoToEquiv (IsoΣPathTransportPathΣ a b)

ΣPathTransport→PathΣ : (a b : Σ A B) → ΣPathTransport a b → (a ≡ b)
ΣPathTransport→PathΣ a b = Iso.fun (IsoΣPathTransportPathΣ a b)

PathΣ→ΣPathTransport : (a b : Σ A B) → (a ≡ b) → ΣPathTransport a b
PathΣ→ΣPathTransport a b = Iso.inv (IsoΣPathTransportPathΣ a b)

ΣPathTransport≡PathΣ : (a b : Σ A B) → ΣPathTransport a b ≡ (a ≡ b)
ΣPathTransport≡PathΣ a b = ua (ΣPathTransport≃PathΣ a b)

Σ-contractFst : (c : isContr A) → Σ A B ≃ B (c .fst)
Σ-contractFst {B = B} c = isoToEquiv isom
  where
  isom : Iso _ _
  isom .fun (a , b) = subst B (sym (c .snd a)) b
  isom .inv b = (c .fst , b)
  isom .rightInv b =
    cong (λ p → subst B p b) (isProp→isSet (isContr→isProp c) _ _ _ _) ∙ transportRefl _
  isom .leftInv (a , b) =
    ΣPathTransport≃PathΣ _ _ .fst (c .snd a , transportTransport⁻ (cong B (c .snd a)) _)

-- a special case of the above
ΣUnit : ∀ {ℓ} (A : Unit → Type ℓ) → Σ Unit A ≃ A tt
ΣUnit A = isoToEquiv (iso snd (λ { x → (tt , x) }) (λ _ → refl) (λ _ → refl))

Σ-contractSnd : ((a : A) → isContr (B a)) → Σ A B ≃ A
Σ-contractSnd c = isoToEquiv isom
  where
  isom : Iso _ _
  isom .fun = fst
  isom .inv a = a , c a .fst
  isom .rightInv _ = refl
  isom .leftInv (a , b) = cong (a ,_) (c a .snd b)

isEmbeddingFstΣProp : ((x : A) → isProp (B x))
                    → {u v : Σ A B}
                    → isEquiv (λ (p : u ≡ v) → cong fst p)
isEmbeddingFstΣProp {B = B} pB {u = u} {v = v} .equiv-proof x = ctr , isCtr
  where
  ctrP : u ≡ v
  ctrP = ΣPathP (x , isProp→PathP (λ _ → pB _) _ _)
  ctr  : fiber (λ (p : u ≡ v) → cong fst p) x
  ctr  = ctrP , refl

  isCtr : ∀ z → ctr ≡ z
  isCtr (z , p) = ΣPathP (ctrP≡ , cong (sym ∘ snd) fzsingl) where
    fzsingl : Path (singl x) (x , refl) (cong fst z , sym p)
    fzsingl = isContrSingl x .snd (cong fst z , sym p)
    ctrSnd : SquareP (λ i j → B (fzsingl i .fst j)) (cong snd ctrP) (cong snd z) _ _
    ctrSnd = isProp→SquareP (λ _ _ → pB _) _ _ _ _
    ctrP≡ : ctrP ≡ z
    ctrP≡ i = ΣPathP (fzsingl i .fst , ctrSnd i)

Σ≡PropEquiv : ((x : A) → isProp (B x)) → {u v : Σ A B}
            → (u .fst ≡ v .fst) ≃ (u ≡ v)
Σ≡PropEquiv pB = invEquiv (_ , isEmbeddingFstΣProp pB)

Σ≡Prop : ((x : A) → isProp (B x)) → {u v : Σ A B}
       → (p : u .fst ≡ v .fst) → u ≡ v
Σ≡Prop pB p = equivFun (Σ≡PropEquiv pB) p

≃-× : ∀ {ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''} → A ≃ C → B ≃ D → A × B ≃ C × D
≃-× eq1 eq2 =
    map-× (fst eq1) (fst eq2)
  , record
     { equiv-proof
       = λ {(c , d) → ((eq1⁻ c .fst .fst
                        , eq2⁻ d .fst .fst)
                          , ≡-× (eq1⁻ c .fst .snd)
                                (eq2⁻ d .fst .snd))
                     , λ {((a , b) , p) → ΣPathP (≡-× (cong fst (eq1⁻ c .snd (a , cong fst p)))
                                                       (cong fst (eq2⁻ d .snd (b , cong snd p)))
                                                , λ i → ≡-× (snd ((eq1⁻ c .snd (a , cong fst p)) i))
                                                             (snd ((eq2⁻ d .snd (b , cong snd p)) i)))}}}
  where
  eq1⁻ = equiv-proof (eq1 .snd)
  eq2⁻ = equiv-proof (eq2 .snd)

{- Some simple ismorphisms -}

prodIso : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
       → Iso A C
       → Iso B D
       → Iso (A × B) (C × D)
Iso.fun (prodIso iAC iBD) (a , b) = (Iso.fun iAC a) , Iso.fun iBD b
Iso.inv (prodIso iAC iBD) (c , d) = (Iso.inv iAC c) , Iso.inv iBD d
Iso.rightInv (prodIso iAC iBD) (c , d) = ΣPathP ((Iso.rightInv iAC c) , (Iso.rightInv iBD d))
Iso.leftInv (prodIso iAC iBD) (a , b) = ΣPathP ((Iso.leftInv iAC a) , (Iso.leftInv iBD b))

toProdIso : {B C : A → Type ℓ}
          → Iso ((a : A) → B a × C a) (((a : A) → B a) × ((a : A) → C a))
Iso.fun toProdIso = λ f → (λ a → fst (f a)) , (λ a → snd (f a))
Iso.inv toProdIso (f , g) = λ a → (f a) , (g a)
Iso.rightInv toProdIso (f , g) = refl
Iso.leftInv toProdIso b = funExt λ _ → refl

curryIso : Iso (((a , b) : Σ A B) → C a b) ((a : A) → (b : B a) → C a b)
Iso.fun curryIso f a b = f (a , b)
Iso.inv curryIso f a = f (fst a) (snd a)
Iso.rightInv curryIso a = refl
Iso.leftInv curryIso f = funExt λ _ → refl

curryEquiv : (((a , b) : Σ A B) → C a b) ≃ (∀ a → (b : B a) → C a b)
curryEquiv = isoToEquiv curryIso
