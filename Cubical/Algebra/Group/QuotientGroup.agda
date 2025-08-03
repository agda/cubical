{-

This file contains quotient groups

-}
module Cubical.Algebra.Group.QuotientGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/s_)
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.HITs.PropositionalTruncation as PT hiding (rec; elim)
open import Cubical.Relation.Binary.Base

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup

private
  variable
    ℓ : Level

module _ (G' : Group ℓ) (H' : Subgroup G') (Hnormal : isNormal H') where

  open BinaryRelation
  open isSubgroup (snd H')
  open GroupStr (snd G')
  open GroupTheory G'
  private
    G = ⟨ G' ⟩

  _~_ : G → G → Type ℓ
  x ~ y = x · inv y ∈ ⟪ H' ⟫

  isRefl~ : isRefl _~_
  isRefl~ x = subst-∈ ⟪ H' ⟫ (sym (·InvR x)) id-closed

  G/H : Type ℓ
  G/H = G /s _~_

  1/H : G/H
  1/H = [ 1g ]

  _·/H_ : G/H → G/H → G/H
  x ·/H y = setQuotBinOp isRefl~ isRefl~ _·_ rem x y
   where
   rem : (a a' b b' : G)
       → a · inv a' ∈ ⟪ H' ⟫
       → b · inv b' ∈ ⟪ H' ⟫
       → (a · b) · inv (a' · b') ∈ ⟪ H' ⟫
   rem a a' b b' haa' hbb' = subst-∈ ⟪ H' ⟫ (cong (_ ·_) (sym (invDistr _ _))) rem5
     where
     rem1 : (inv a' · a) · b · inv b' ∈ ⟪ H' ⟫
     rem1 = ·CommNormalSubgroup H' Hnormal
              (op-closed  hbb' (·CommNormalSubgroup H' Hnormal haa'))

     rem2 : ((inv a' · a) · b) · inv b' ∈ ⟪ H' ⟫
     rem2 = subst-∈ ⟪ H' ⟫ (·Assoc _ _ _) rem1

     rem3 : inv b' · (inv a' · a) · b ∈ ⟪ H' ⟫
     rem3 = ·CommNormalSubgroup H' Hnormal rem2

     rem4 : (inv b' · inv a') · (a · b) ∈ ⟪ H' ⟫
     rem4 = subst-∈ ⟪ H' ⟫ (cong (inv b' ·_) (sym (·Assoc _ _ _)) ∙ ·Assoc _ _ _) rem3

     rem5 : (a · b) · inv b' · inv a' ∈ ⟪ H' ⟫
     rem5 = ·CommNormalSubgroup H' Hnormal rem4

  inv/H : G/H → G/H
  inv/H = setQuotUnaryOp inv rem
    where
    rem : (a a' : G) → a · inv a' ∈ ⟪ H' ⟫ → inv a · inv (inv a') ∈ ⟪ H' ⟫
    rem a a' haa' = subst-∈ ⟪ H' ⟫ (cong (inv a ·_) (sym (invInv a'))) rem1
      where
      ha'a : a' · inv a ∈ ⟪ H' ⟫
      ha'a = subst-∈ ⟪ H' ⟫ (invDistr a (inv a') ∙ cong (_· inv a) (invInv a')) (inv-closed haa')

      rem1 : inv a · a' ∈ ⟪ H' ⟫
      rem1 = ·CommNormalSubgroup H' Hnormal ha'a

  ·/H-assoc : (a b c : G/H) → (a ·/H (b ·/H c)) ≡ ((a ·/H b) ·/H c)
  ·/H-assoc = elimProp3 (λ x y z → squash/ _ _) λ x y z → cong [_] (·Assoc x y z)

  ·/H-rid : (a : G/H) → (a ·/H 1/H) ≡ a
  ·/H-rid = elimProp (λ x → squash/ _ _) λ x → cong [_] (·IdR x)

  ·/H-invr : (a : G/H) → (a ·/H inv/H a) ≡ 1/H
  ·/H-invr = elimProp (λ x → squash/ _ _) λ x → cong [_] (·InvR x)

  asGroup : Group ℓ
  fst asGroup = G/H
  GroupStr.1g (snd asGroup) = [ 1g ]
  GroupStr._·_ (snd asGroup) = _·/H_
  GroupStr.inv (snd asGroup) = inv/H
  GroupStr.isGroup (snd asGroup) = isGrp
   where
   opaque
     isGrp : IsGroup [ 1g ] _·/H_ inv/H
     isGrp = GroupStr.isGroup (makeGroup-right 1/H _·/H_ inv/H squash/
                                 ·/H-assoc ·/H-rid ·/H-invr .snd)

_/_ : (G : Group ℓ) → (H : NormalSubgroup G) → Group ℓ
G / H = asGroup G (H .fst) (H .snd)

[_]/G : {G : Group ℓ} {H : NormalSubgroup G} → ⟨ G ⟩ → ⟨ G / H ⟩
[ x ]/G = [ x ]

-- Quotienting by a trivial subgroup
module _ {G' : Group ℓ} (H' : NormalSubgroup G')
         (contrH : (x y : fst G') → _~_ G' (fst H') (snd H') x y → x ≡ y) where
  private
    -- open isSubgroup (snd H')
    open GroupStr (snd G')
    open GroupTheory G'
    G = fst G'
    G/H' = fst (G' / H')

    Code : (g : G) → G/H' → hProp ℓ
    Code g =
      elim (λ _ → isSetHProp)
        (λ a → (g ≡ a) , is-set _ _)
        λ a b r → Σ≡Prop (λ _ → isPropIsProp) (cong (g ≡_) (contrH a b r))

    decode : (g : G) (x : G/H') → [ g ] ≡ x → Code g x .fst
    decode g x = J (λ x _ → Code g x .fst) refl

  trivialRel→elimPath : {g h : G} → Path G/H' [ g ] [ h ] → g ≡ h
  trivialRel→elimPath {g = g} {h = h} = decode g [ h ]

  trivialRelIso : GroupIso G' (G' / H')
  Iso.fun (fst trivialRelIso) g = [ g ]
  Iso.inv (fst trivialRelIso) =
    rec is-set (λ g → g) contrH
  Iso.rightInv (fst trivialRelIso) =
    elimProp (λ _ → squash/ _ _) λ _ → refl
  Iso.leftInv (fst trivialRelIso) _ = refl
  snd trivialRelIso =
    makeIsGroupHom λ _ _ → refl

Hom/ : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'}
  {G' : NormalSubgroup G} {H' : NormalSubgroup H}
  → (ϕ : GroupHom G H)
  → (ϕ' : (a b : _) (r : (G ~ G' .fst) (G' .snd) a b)
        → (H ~ H' .fst) (H' .snd) (fst ϕ a) (fst ϕ b))
  → GroupHom (G / G') (H / H')
fst (Hom/ ϕ ϕ') =
  elim (λ _ → squash/) (λ x → [ fst ϕ x ]) λ a b r → eq/ _ _ (ϕ' a b r)
snd (Hom/ ϕ ϕ') =
  makeIsGroupHom (elimProp2 (λ _ _ → squash/ _ _)
    λ a b → cong [_] (IsGroupHom.pres· (snd ϕ) a b))

Hom/Iso : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'}
  {G' : NormalSubgroup G} {H' : NormalSubgroup H}
  → (ϕ : GroupIso G H)
  → (ϕ' : (a b : _) (r : (G ~ G' .fst) (G' .snd) a b)
        → (H ~ H' .fst) (H' .snd) (Iso.fun (fst ϕ) a) (Iso.fun (fst ϕ) b))
     (ψ' : (a b : _) (r : (H ~ H' .fst) (H' .snd) a b)
        → (G ~ G' .fst) (G' .snd) (Iso.inv (fst ϕ) a) (Iso.inv (fst ϕ) b))
  → GroupIso (G / G') (H / H')
Iso.fun (fst (Hom/Iso {G' = G'} {H' = H'} ϕ ϕ' ψ')) =
  fst (Hom/ {G' = G'} {H' = H'} (GroupIso→GroupHom ϕ) ϕ')
Iso.inv (fst (Hom/Iso {G' = G'} {H' = H'} ϕ ϕ' ψ')) =
  fst (Hom/ {G' = H'} {H' = G'} (GroupIso→GroupHom (invGroupIso ϕ)) ψ')
Iso.rightInv (fst (Hom/Iso ϕ ϕ' ψ')) =
  elimProp (λ _ → squash/ _ _) λ a → cong [_] (Iso.rightInv (fst ϕ) a)
Iso.leftInv (fst (Hom/Iso ϕ ϕ' ψ')) =
  elimProp (λ _ → squash/ _ _) λ a → cong [_] (Iso.leftInv (fst ϕ) a)
snd (Hom/Iso {G' = G'} {H' = H'} ϕ ϕ' ψ') =
  makeIsGroupHom λ x y
    → IsGroupHom.pres· (snd (Hom/ {G' = G'} {H' = H'}
        (GroupIso→GroupHom ϕ) ϕ')) x y

Hom/ImIso : ∀ {ℓ ℓ'} {G H : Group ℓ'} (ϕ : GroupHom G H)
                     {G' H' : Group ℓ} (ψ : GroupHom G' H')
                     {ϕ' : isNormal (imSubgroup ϕ)} {ψ' : isNormal (imSubgroup ψ)}
   (eG : GroupIso G G') (eH : GroupIso H H')
   (e~ : (g : fst G)
     → fst ψ (Iso.fun (fst eG) g) ≡
        Iso.fun (fst eH) (ϕ .fst g))
  → GroupIso (H / (imSubgroup ϕ , ϕ')) (H' / (imSubgroup ψ , ψ'))
Hom/ImIso {G = G} {H} ϕ {G'} {H'} ψ {ϕ'} {ψ'} eG eH e∼ =
    (fst main)
  , makeIsGroupHom λ x y → IsGroupHom.pres· (snd main) x y
   where
   -- Faster type checking this way...
   main = Hom/Iso {G = H} {H = H'}
     {G' = (imSubgroup ϕ , ϕ')} {H' = (imSubgroup ψ , ψ')} eH
     (λ a b → PT.map (uncurry λ x p
     → (Iso.fun (fst eG) x) , e∼ x
     ∙ cong (Iso.fun (fst eH)) p
     ∙ IsGroupHom.pres· (snd eH) _ _
     ∙ cong₂ (GroupStr._·_ (snd H'))
       refl (IsGroupHom.presinv (snd eH) _)))
     λ a b → PT.map (uncurry λ x p
    → (Iso.inv (fst eG) x)
      , (sym ((cong₂ (GroupStr._·_ (snd H))
        refl (sym (IsGroupHom.presinv (snd (invGroupIso eH)) b))
        ∙ sym (IsGroupHom.pres· (snd (invGroupIso eH))
                                a (GroupStr.inv (H' .snd) b))
        ∙ cong (Iso.inv (fst eH)) (sym p)
        ∙ cong (Iso.inv (fst eH) ∘ fst ψ) (sym (Iso.rightInv (fst eG) x)))
       ∙ cong (Iso.inv (fst eH)) (e∼ (Iso.inv (fst eG) x))
       ∙ Iso.leftInv (fst eH) _)))
