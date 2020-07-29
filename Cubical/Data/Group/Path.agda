
{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Group.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Group.Base
open import Cubical.Foundations.Transport

module isGroupPath where
  isGroup≡ : {ℓ : Level} {A : Type ℓ}
    {id : A} {inv : A → A} {comp : A → A → A}
    {lUnit : (a : A) → comp id a ≡ a} {rUnit : (a : A) → comp a id ≡ a}
    {assoc : (a b c : A) →  comp (comp a b) c ≡ comp a (comp b c)}
    {lCancel : (a : A) → comp (inv a) a ≡ id} {rCancel : (a : A) → comp a (inv a) ≡ id}
    {id' : A} {inv' : A → A} {comp' : A → A → A}
    {lUnit' : (a : A) → comp' id' a ≡ a} {rUnit' : (a : A) → comp' a id' ≡ a}
    {assoc' : (a b c : A) →  comp' (comp' a b) c ≡ comp' a (comp' b c)}
    {lCancel' : (a : A) → comp' (inv' a) a ≡ id'} {rCancel' : (a : A) → comp' a (inv' a) ≡ id'}
    (p-id : id ≡ id') (p-inv : inv ≡ inv') (p-comp : comp ≡ comp')
    (p-lUnit : PathP (λ i → (a : A) → p-comp i (p-id i) a ≡ a) lUnit lUnit')
    (p-rUnit : PathP (λ i → (a : A) → p-comp i a (p-id i) ≡ a) rUnit rUnit')
    (p-assoc : PathP (λ i → (a b c : A) → p-comp i (p-comp i a b) c ≡ p-comp i a (p-comp i b c)) assoc assoc')
    (p-lCancel : PathP (λ i → (a : A) → p-comp i (p-inv i a) a ≡ p-id i) lCancel lCancel')
    (p-rCancel : PathP (λ i → (a : A) → p-comp i a (p-inv i a) ≡ p-id i) rCancel rCancel')
    → group-struct id inv comp lUnit rUnit assoc lCancel rCancel
    ≡ group-struct id' inv' comp' lUnit' rUnit' assoc' lCancel' rCancel'
  isGroup≡ p-id p-inv p-comp p-lUnit p-rUnit p-assoc p-lCancel p-rCancel i
    = group-struct (p-id i) (p-inv i) (p-comp i) (p-lUnit i) (p-rUnit i) (p-assoc i) (p-lCancel i) (p-rCancel i)

  isGroupTransport : {ℓ : Level} {A A' : Type ℓ} (setA : isSet A)
    ((group-struct id inv comp lUnit rUnit assoc lCancel rCancel) : isGroup A)
    ((group-struct id' inv' comp' lUnit' rUnit' assoc' lCancel' rCancel') : isGroup A')
    (p-A : A ≡ A')
    (p-id : transport p-A id ≡ id')
    (trcomp : (a b : A) → transport p-A (comp a b) ≡ comp' (transport p-A a) (transport p-A b))
    → transport (λ i → isGroup (p-A i)) (group-struct id inv comp lUnit rUnit assoc lCancel rCancel)
      ≡ group-struct id' inv' comp' lUnit' rUnit' assoc' lCancel' rCancel'
  isGroupTransport {ℓ} {A} {A'} setA
    (group-struct id inv _⋆_ lUnit rUnit assoc lCancel rCancel)
      (group-struct id' inv' _⋆'_ lUnit' rUnit' assoc' lCancel' rCancel')
      p-A p-id trcomp
    = isGroup≡ p-id trInv≡' trComp≡'
      (toPathP p-lUnit) (toPathP p-rUnit) (toPathP p-assoc) (toPathP p-lCancel) (toPathP p-rCancel)
      where
        -- transport in both directions along p-A
        tr : A → A'
        tr = λ (a : A) → transport p-A a
        tr- : A' → A
        tr- = λ (a : A') → transport (sym p-A) a

        -- transport laws:
        trtr-≡ : (a' : A') → tr (tr- a') ≡ a'
        trtr-≡ a' = transportTransport⁻ p-A a'

        tr-tr≡ : (a : A) → tr- (tr a) ≡ a
        tr-tr≡ a = transport⁻Transport p-A a

        trcomp' : (a' b' : A') → tr- (a' ⋆' b') ≡ (tr- a') ⋆ (tr- b')
        trcomp' a' b' =
                tr- (a' ⋆' b')
                  ≡⟨ (cong tr- ((cong (_⋆' b') (sym (trtr-≡ a'))) ∙ cong (tr (tr- a') ⋆'_) (sym (trtr-≡ b')))) ⟩
                tr- ((tr (tr- a')) ⋆' (tr (tr- b')))
                  ≡⟨ cong tr- (sym (trcomp (tr- a') (tr- b'))) ⟩
                tr- (tr (tr- a' ⋆ tr- b'))  ≡⟨ tr-tr≡ (tr- a' ⋆ tr- b') ⟩
                refl

        -- the group structures on A and A'
        G = group-struct id inv _⋆_ lUnit rUnit assoc lCancel rCancel
        G' = group-struct id' inv' _⋆'_ lUnit' rUnit' assoc' lCancel' rCancel'
        trG = transp (λ i → isGroup (p-A i)) i0 G

        -- A' is a set
        setA' : isSet A'
        setA' = transp (λ i → isSet (p-A i)) i0 setA

        -- the transported inverse
        trInv : A' → A'
        trInv a = tr (inv (tr- a))

        -- transported comp
        trComp : A' → A' → A'
        trComp a' b' = tr ((tr- a') ⋆ (tr- b'))

        trComp≡ : trComp ≡ isGroup.comp trG
        trComp≡ = refl

        trComp≡' : trComp ≡ _⋆'_
        trComp≡' = funExt λ a' → funExt
          (λ b' → (trcomp (tr- a') (tr- b')) ∙
            (cong (_⋆' (tr (tr- b'))) (trtr-≡ a')) ∙
            (cong (a' ⋆'_) (trtr-≡ b')))

        -- A' is a set so group properties are proof irrelevant
        p-lUnit =
          transp (λ i → (a' : A') → trComp≡' i (p-id i) a' ≡ a') i0 (isGroup.lUnit trG)
          ≡⟨ funExt (λ a' → (setA' (id' ⋆' a') a'
            (transp (λ i → (a' : A') → trComp≡' i (p-id i) a' ≡ a') i0 (isGroup.lUnit trG) a') (lUnit' a'))) ⟩
          lUnit' ≡⟨ refl ⟩ refl

        p-rUnit = funExt (λ a' → setA' (a' ⋆' id') a'
          (transp (λ i → (a : A') → trComp≡' i a (p-id i) ≡ a) i0 (isGroup.rUnit trG) a') (rUnit' a'))

        p-assoc = funExt (λ a' → funExt (λ b' → funExt (λ c' →
          setA' ((a' ⋆' b') ⋆' c') (a' ⋆' (b' ⋆' c'))
          (transp (λ i → (a b c : A') → trComp≡' i (trComp≡' i a b) c ≡ trComp≡' i a (trComp≡' i b c)) i0 (isGroup.assoc trG) a' b' c')
          (assoc' a' b' c'))))


        -- proof that the transported inverse is the same as inv'
        -- using uniqueness of inverses in groups
        trInv≡' : trInv ≡ inv'
        trInv≡' = funExt (λ a' →
          trInv a'
            ≡⟨ sym (rUnit' (trInv a')) ⟩
          (trInv a') ⋆' id'
            ≡⟨  cong ((trInv a') ⋆'_) (sym (rCancel' a')) ⟩
          (trInv a') ⋆' (a' ⋆' (inv' a'))
            ≡⟨ sym (assoc' (trInv a') a' (inv' a')) ⟩
          ((trInv a') ⋆' a') ⋆' (inv' a')
            ≡⟨ cong (_⋆' (inv' a'))
                    (sym (trtr-≡ ((trInv a') ⋆' a')) ∙
                      (cong tr
                            ((trcomp' (trInv a') a') ∙
                              (cong (_⋆ tr- a')
                                    (tr-tr≡ (inv (tr- a')))) ∙
                              lCancel (tr- a'))) ∙
                      p-id) ⟩
          id' ⋆' (inv' a')
            ≡⟨ lUnit' (inv' a') ⟩
          inv' a' ≡⟨ refl ⟩ refl)

        p-lCancel = funExt (λ a' → setA' ((inv' a') ⋆' a') id' (transp (λ i → (a : A') → trComp≡' i (trInv≡' i a) a ≡ p-id i) i0 (isGroup.lCancel trG) a') (lCancel' a'))
        p-rCancel = funExt (λ a' → setA' (a' ⋆' (inv' a')) id' (transp (λ i → (a : A') → trComp≡' i a (trInv≡' i a) ≡ p-id i) i0 (isGroup.rCancel trG) a') (rCancel' a'))

open isGroupPath public

Group≡ : {ℓ : Level}
  {type : Type ℓ} {setStruc : isSet type} {groupStruc : isGroup type}
  {type' : Type ℓ} {setStruc' : isSet type'} {groupStruc' : isGroup type'}
  (p-type : type ≡ type')
  (p-setStruc : PathP (λ i → isSet (p-type i)) setStruc setStruc')
  (p-groupStruc : PathP (λ i → isGroup (p-type i)) groupStruc groupStruc')
  → group type setStruc groupStruc ≡ group type' setStruc' groupStruc'
Group≡ p-type p-setStruc p-groupStruc i
  = group (p-type i) (p-setStruc i) (p-groupStruc i)


{-
module MorphPath where
  open import Cubical.Data.Sigma
  MorphTransp : {ℓ ℓ' : Level} (G G' : Group ℓ) (H H' : Group ℓ') (p-G : G ≡ G') (p-H : H ≡ H')
    (f : morph G H) (f' : morph G' H')
    (p-f : (g : Group.type G) → transp (λ i → Group.type (p-H i)) i0 (f .fst g) ≡ f' .fst (transp (λ i → Group.type (p-G i)) i0 g))
    → transp (λ i → morph (p-G i) (p-H i)) i0 f ≡ f'
  MorphTransp G G' H H' p-G p-H f f' p-f = ΣPathP ((funExt λ g → {!!} ∙ {!p-f!}) , {!!})
-}
