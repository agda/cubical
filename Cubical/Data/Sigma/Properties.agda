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
module Cubical.Data.Sigma.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma.Base
open import Cubical.Data.Unit.Base
open import Cubical.Data.Empty.Base

open import Cubical.Relation.Nullary

open import Cubical.Reflection.StrictEquiv

open Iso

private
  variable
    ℓ ℓ' ℓ'' : Level
    A A' : Type ℓ
    B B' : (a : A) → Type ℓ
    C : (a : A) (b : B a) → Type ℓ

map-fst : {B : Type ℓ} → (f : A → A') → A × B → A' × B
map-fst f (a , b) = (f a , b)

map-snd : (∀ {a} → B a → B' a) → Σ A B → Σ A B'
map-snd f (a , b) = (a , f b)

map-snd' : {f : A → A'} → (∀ {a} → B a → B' (f a)) → Σ A B → Σ A' B'
map-snd' g (_ , b) = (_ , g b)

snd'-map : {f : A → A'} → ((a , _) : Σ A B) → (B a → B' (f a)) → Σ A' B'
snd'-map (_ , b) g = (_ , g b)

map-× : {B : Type ℓ} {B' : Type ℓ'} → (A → A') → (B → B') → A × B → A' × B'
map-× f g (a , b) = (f a , g b)

≡-× : {A : Type ℓ} {B : Type ℓ'} {x y : A × B} → fst x ≡ fst y → snd x ≡ snd y → x ≡ y
≡-× p q i = (p i) , (q i)


-- Characterization of paths in Σ using dependent paths

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
  sec ΣPathIsoPathΣ _ = refl
  ret ΣPathIsoPathΣ _  = refl

  unquoteDecl ΣPath≃PathΣ = declStrictIsoToEquiv ΣPath≃PathΣ ΣPathIsoPathΣ

  ΣPath≡PathΣ : (Σ[ p ∈ PathP A (fst x) (fst y) ] (PathP (λ i → B i (p i)) (snd x) (snd y)))
              ≡ (PathP (λ i → Σ (A i) (B i)) x y)
  ΣPath≡PathΣ = ua ΣPath≃PathΣ

×≡Prop : isProp A' → {u v : A × A'} → u .fst ≡ v .fst → u ≡ v
×≡Prop pB {u} {v} p i = (p i) , (pB (u .snd) (v .snd) i)

×≡Prop' : isProp A → {u v : A × A'} → u .snd ≡ v .snd → u ≡ v
×≡Prop' pA {u} {v} p i = (pA (u .fst) (v .fst) i) , p i

-- Useful lemma to prove unique existence
uniqueExists : (a : A) (b : B a) (h : (a' : A) → isProp (B a')) (H : (a' : A) → B a' → a ≡ a') → ∃![ a ∈ A ] B a
fst (uniqueExists a b h H) = (a , b)
snd (uniqueExists a b h H) (a' , b') = ΣPathP (H a' b' , isProp→PathP (λ i → h (H a' b' i)) b b')


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
  ΣPathPIsoPathPΣ .sec _ = refl
  ΣPathPIsoPathPΣ .ret _ = refl

  unquoteDecl ΣPathP≃PathPΣ = declStrictIsoToEquiv ΣPathP≃PathPΣ ΣPathPIsoPathPΣ

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

lUnit×Iso : Iso (Unit × A) A
fun lUnit×Iso = snd
inv lUnit×Iso = tt ,_
sec lUnit×Iso _ = refl
ret lUnit×Iso _ = refl

lUnit*×Iso : Iso (Unit* {ℓ} × A) A
fun lUnit*×Iso = snd
inv lUnit*×Iso = tt* ,_
sec lUnit*×Iso _ = refl
ret lUnit*×Iso _ = refl

rUnit×Iso : Iso (A × Unit) A
fun rUnit×Iso = fst
inv rUnit×Iso = _, tt
sec rUnit×Iso _ = refl
ret rUnit×Iso _ = refl

rUnit*×Iso : Iso (A × Unit* {ℓ}) A
fun rUnit*×Iso = fst
inv rUnit*×Iso = _, tt*
sec rUnit*×Iso _ = refl
ret rUnit*×Iso _ = refl

module _ {A : Type ℓ} {A' : Type ℓ'} where
  Σ-swap-Iso : Iso (A × A') (A' × A)
  fun Σ-swap-Iso (x , y) = (y , x)
  inv Σ-swap-Iso (x , y) = (y , x)
  sec Σ-swap-Iso _ = refl
  ret Σ-swap-Iso _  = refl

  unquoteDecl Σ-swap-≃ = declStrictIsoToEquiv Σ-swap-≃ Σ-swap-Iso

module _ {A : Type ℓ} {B : A → Type ℓ'} {C : ∀ a → B a → Type ℓ''} where
  Σ-assoc-Iso : Iso (Σ[ a ∈ Σ A B ] C (fst a) (snd a)) (Σ[ a ∈ A ] Σ[ b ∈ B a ] C a b)
  fun Σ-assoc-Iso ((x , y) , z) = (x , (y , z))
  inv Σ-assoc-Iso (x , (y , z)) = ((x , y) , z)
  sec Σ-assoc-Iso _ = refl
  ret Σ-assoc-Iso _  = refl

  unquoteDecl Σ-assoc-≃ = declStrictIsoToEquiv Σ-assoc-≃ Σ-assoc-Iso

  Σ-Π-Iso : Iso ((a : A) → Σ[ b ∈ B a ] C a b) (Σ[ f ∈ ((a : A) → B a) ] ∀ a → C a (f a))
  fun Σ-Π-Iso f         = (fst ∘ f , snd ∘ f)
  inv Σ-Π-Iso (f , g) x = (f x , g x)
  sec Σ-Π-Iso _    = refl
  ret Σ-Π-Iso _     = refl

  unquoteDecl Σ-Π-≃ = declStrictIsoToEquiv Σ-Π-≃ Σ-Π-Iso

module _ {A : Type ℓ} {B : A → Type ℓ'} {B' : ∀ a → Type ℓ''} where
  Σ-assoc-swap-Iso : Iso (Σ[ a ∈ Σ A B ] B' (fst a)) (Σ[ a ∈ Σ A B' ] B (fst a))
  fun Σ-assoc-swap-Iso ((x , y) , z) = ((x , z) , y)
  inv Σ-assoc-swap-Iso ((x , z) , y) = ((x , y) , z)
  sec Σ-assoc-swap-Iso _ = refl
  ret Σ-assoc-swap-Iso _  = refl

  unquoteDecl Σ-assoc-swap-≃ = declStrictIsoToEquiv Σ-assoc-swap-≃ Σ-assoc-swap-Iso

Σ-cong-iso-fst : (isom : Iso A A') → Iso (Σ A (B ∘ fun isom)) (Σ A' B)
fun (Σ-cong-iso-fst isom) x = fun isom (x .fst) , x .snd
inv (Σ-cong-iso-fst {B = B} isom) x = inv isom (x .fst) , subst B (sym (ε (x .fst))) (x .snd)
  where
  ε = isHAEquiv.rinv (snd (iso→HAEquiv isom))
sec (Σ-cong-iso-fst {B = B} isom) (x , y) = ΣPathP (ε x , toPathP goal)
  where
  ε = isHAEquiv.rinv (snd (iso→HAEquiv isom))
  goal : subst B (ε x) (subst B (sym (ε x)) y) ≡ y
  goal = sym (substComposite B (sym (ε x)) (ε x) y)
      ∙∙ cong (λ x → subst B x y) (lCancel (ε x))
      ∙∙ substRefl {B = B} y
ret (Σ-cong-iso-fst {A = A} {B = B} isom) (x , y) = ΣPathP (ret isom x , toPathP goal)
  where
  ε = isHAEquiv.rinv (snd (iso→HAEquiv isom))
  γ = isHAEquiv.com (snd (iso→HAEquiv isom))

  lem : (x : A) → sym (ε (fun isom x)) ∙ cong (fun isom) (ret isom x) ≡ refl
  lem x = cong (λ a → sym (ε (fun isom x)) ∙ a) (γ x) ∙ lCancel (ε (fun isom x))

  goal : subst B (cong (fun isom) (ret isom x)) (subst B (sym (ε (fun isom x))) y) ≡ y
  goal = sym (substComposite B (sym (ε (fun isom x))) (cong (fun isom) (ret isom x)) y)
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
sec (Σ-cong-iso-snd isom) (x , y) = ΣPathP (refl , sec (isom x) y)
ret (Σ-cong-iso-snd isom) (x , y') = ΣPathP (refl , ret (isom x) y')

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

Σ-cong-equiv-prop :
    (e : A ≃ A')
  → ((x : A ) → isProp (B  x))
  → ((x : A') → isProp (B' x))
  → ((x : A) → B x → B' (equivFun e x))
  → ((x : A) → B' (equivFun e x) → B x)
  → Σ A B ≃ Σ A' B'
Σ-cong-equiv-prop e prop prop' prop→ prop← =
  Σ-cong-equiv e (λ x → propBiimpl→Equiv (prop x) (prop' (equivFun e x)) (prop→ x) (prop← x))

-- Alternative version for path in Σ-types, as in the HoTT book

ΣPathTransport : (a b : Σ A B) → Type _
ΣPathTransport {B = B} a b = Σ[ p ∈ (fst a ≡ fst b) ] transport (λ i → B (p i)) (snd a) ≡ snd b

IsoΣPathTransportPathΣ : (a b : Σ A B) → Iso (ΣPathTransport a b) (a ≡ b)
IsoΣPathTransportPathΣ {B = B} a b =
  compIso (Σ-cong-iso-snd (λ p → invIso (PathPIsoPath (λ i → B (p i)) _ _)))
          ΣPathIsoPathΣ

ΣPathTransport≃PathΣ : (a b : Σ A B) → ΣPathTransport a b ≃ (a ≡ b)
ΣPathTransport≃PathΣ {B = B} a b = isoToEquiv (IsoΣPathTransportPathΣ a b)

ΣPathTransport→PathΣ : (a b : Σ A B) → ΣPathTransport a b → (a ≡ b)
ΣPathTransport→PathΣ a b = Iso.fun (IsoΣPathTransportPathΣ a b)

PathΣ→ΣPathTransport : (a b : Σ A B) → (a ≡ b) → ΣPathTransport a b
PathΣ→ΣPathTransport a b = Iso.inv (IsoΣPathTransportPathΣ a b)

ΣPathTransport≡PathΣ : (a b : Σ A B) → ΣPathTransport a b ≡ (a ≡ b)
ΣPathTransport≡PathΣ a b = ua (ΣPathTransport≃PathΣ a b)

Σ-contractFstIso : (c : isContr A) → Iso (Σ A B) (B (c .fst))
fun (Σ-contractFstIso {B = B} c) p = subst B (sym (c .snd (fst p))) (snd p)
inv (Σ-contractFstIso {B = B} c) b = _ , b
sec (Σ-contractFstIso {B = B} c) b =
  cong (λ p → subst B p b) (isProp→isSet (isContr→isProp c) _ _ _ _) ∙ transportRefl _
fst (ret (Σ-contractFstIso {B = B} c) p j) = c .snd (fst p) j
snd (ret (Σ-contractFstIso {B = B} c) p j) =
  transp (λ i → B (c .snd (fst p) (~ i ∨ j))) j (snd p)

Σ-contractFst : (c : isContr A) → Σ A B ≃ B (c .fst)
Σ-contractFst {B = B} c = isoToEquiv (Σ-contractFstIso c)

-- a special case of the above
module _ (A : Unit → Type ℓ) where
  ΣUnit : Σ Unit A ≃ A tt
  unquoteDef ΣUnit = defStrictEquiv {B = A tt} ΣUnit snd (tt ,_)

Σ-contractSnd : ((a : A) → isContr (B a)) → Σ A B ≃ A
Σ-contractSnd c = isoToEquiv isom
  where
  isom : Iso _ _
  isom .fun = fst
  isom .inv a = a , c a .fst
  isom .sec _ = refl
  isom .ret (a , b) = cong (a ,_) (c a .snd b)

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

-- dependent version
ΣPathPProp : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
           → {u : Σ (A i0) (B i0)} {v : Σ (A i1) (B i1)}
           → ((a : A (i1)) → isProp (B i1 a))
           → PathP (λ i → A i) (fst u) (fst v)
           → PathP (λ i → Σ (A i) (B i)) u v
fst (ΣPathPProp {u = u} {v = v} pB p i) = p i
snd (ΣPathPProp {B = B} {u = u} {v = v} pB p i) = lem i
  where
  lem : PathP (λ i → B i (p i)) (snd u) (snd v)
  lem = toPathP (pB _ _ _)

discreteΣProp : Discrete A → ((x : A) → isProp (B x)) → Discrete (Σ A B)
discreteΣProp _≟_ isPropA _ _ =
  EquivPresDec (Σ≡PropEquiv isPropA) (_ ≟ _)

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
Iso.sec (prodIso iAC iBD) (c , d) = ΣPathP ((Iso.sec iAC c) , (Iso.sec iBD d))
Iso.ret (prodIso iAC iBD) (a , b) = ΣPathP ((Iso.ret iAC a) , (Iso.ret iBD b))

prodEquivToIso : ∀ {ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
  → (e : A ≃ C)(e' : B ≃ D)
  → prodIso (equivToIso e) (equivToIso e') ≡ equivToIso (≃-× e e')
Iso.fun (prodEquivToIso e e' i) = Iso.fun (equivToIso (≃-× e e'))
Iso.inv (prodEquivToIso e e' i) = Iso.inv (equivToIso (≃-× e e'))
Iso.sec (prodEquivToIso e e' i) = Iso.sec (equivToIso (≃-× e e'))
Iso.ret (prodEquivToIso e e' i) = Iso.ret (equivToIso (≃-× e e'))

toProdIso : {B C : A → Type ℓ}
          → Iso ((a : A) → B a × C a) (((a : A) → B a) × ((a : A) → C a))
Iso.fun toProdIso = λ f → (λ a → fst (f a)) , (λ a → snd (f a))
Iso.inv toProdIso (f , g) = λ a → (f a) , (g a)
Iso.sec toProdIso (f , g) = refl
Iso.ret toProdIso b = refl

module _ {A : Type ℓ} {B : A → Type ℓ'} {C : ∀ a → B a → Type ℓ''} where
  curryIso : Iso (((a , b) : Σ A B) → C a b) ((a : A) → (b : B a) → C a b)
  Iso.fun curryIso f a b = f (a , b)
  Iso.inv curryIso f a = f (fst a) (snd a)
  Iso.sec curryIso a = refl
  Iso.ret curryIso f = refl

  unquoteDecl curryEquiv = declStrictIsoToEquiv curryEquiv curryIso

-- Sigma type with empty base

module _ (A : ⊥ → Type ℓ) where

  open Iso

  ΣEmptyIso : Iso (Σ ⊥ A) ⊥
  fun ΣEmptyIso (* , _) = *

  ΣEmpty : Σ ⊥ A ≃ ⊥
  ΣEmpty = isoToEquiv ΣEmptyIso

module _ {ℓ : Level} (A : ⊥* {ℓ} → Type ℓ) where

  open Iso

  ΣEmpty*Iso : Iso (Σ ⊥* A) ⊥*
  fun ΣEmpty*Iso (* , _) = *

-- fiber of projection map

module _
  (A : Type ℓ)
  (B : A → Type ℓ') where

  private
    proj : Σ A B → A
    proj (a , b) = a

  module _
    (a : A) where

    open Iso

    fiberProjIso : Iso (B a) (fiber proj a)
    fiberProjIso .fun b = (a , b) , refl
    fiberProjIso .inv ((a' , b') , p) = subst B p b'
    fiberProjIso .ret b i = substRefl {B = B} b i
    fiberProjIso .sec (_ , p) i .fst .fst = p (~ i)
    fiberProjIso .sec ((_ , b') , p) i .fst .snd = subst-filler B p b' (~ i)
    fiberProjIso .sec (_ , p) i .snd j = p (~ i ∨ j)

    fiberProjEquiv : B a ≃ fiber proj a
    fiberProjEquiv = isoToEquiv fiberProjIso

separatedΣ : Separated A → ((a : A) → Separated (B a)) → Separated (Σ A B)
separatedΣ {B = B} sepA sepB (a , b) (a' , b') p = ΣPathTransport→PathΣ _ _ (pA , pB)
  where
    pA : a ≡ a'
    pA = sepA a a' (λ q → p (λ r → q (cong fst r)))

    pB : subst B pA b ≡ b'
    pB = sepB _ _ _ (λ q → p (λ r → q (cong (λ r' → subst B r' b)
                                (Separated→isSet sepA _ _ pA (cong fst r)) ∙ snd (PathΣ→ΣPathTransport _ _ r))))
