{-# OPTIONS --safe #-}

module Cubical.Categories.Dagger.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
import Cubical.Foundations.Isomorphism as TypeIso
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; isPropPropTrunc)

open import Cubical.Categories.Category
open import Cubical.Categories.Morphism

open import Cubical.Categories.Dagger.Base

private variable
  ℓ ℓ' : Level

module _ (CDagCat : DagCat ℓ ℓ') where
  open DagCat CDagCat renaming (cat to C)
  open areInv

  private variable
    x y z w : ob

  is†Monic is†Epic is†Iso is†PIso : Hom[ x , y ] → Type ℓ'
  is†Monic f = f ⋆ f † ≡ id
  is†Epic f = f † ⋆ f ≡ id
  is†Iso f = areInv C f (f †)
  is†PIso f = f ⋆ f † ⋆ f ≡ f

  isSelfAdjoint is†Idem : Hom[ x , x ] → Type ℓ'
  isSelfAdjoint f = f † ≡ f
  is†Idem f = isSelfAdjoint f × (f ⋆ f ≡ f)

  isPositive : Hom[ x , x ] → Type (ℓ-max ℓ ℓ')
  isPositive {x = x} f = ∃[ y ∈ ob ] Σ[ g ∈ Hom[ x , y ] ] f ≡ g ⋆ g †

  module _ (f : Hom[ x , y ]) where
    †MonicsAreSplitMon : is†Monic f → isSplitMon C f
    †MonicsAreSplitMon fmon = ∣ f † , fmon ∣₁

    †EpicsAreSplitEpi : is†Epic f → isSplitEpi C f
    †EpicsAreSplitEpi fepi = ∣ f † , fepi ∣₁

    †IsosAreIsos : is†Iso f → isIso C f
    †IsosAreIsos fiso = isiso (f †) (fiso .sec) (fiso .ret)

    †Of†MonIs†Epi : is†Monic f → is†Epic (f †)
    †Of†MonIs†Epi fmon =
      f † † ⋆ f † ≡⟨ congL _⋆_ (†-invol f) ⟩
      f ⋆ f †     ≡⟨ fmon ⟩
      id          ∎

    †Of†EpiIs†Mon : is†Epic f → is†Monic (f †)
    †Of†EpiIs†Mon fepi =
      f † ⋆ f † † ≡⟨ congR _⋆_ (†-invol f) ⟩
      f † ⋆ f     ≡⟨ fepi ⟩
      id          ∎

    †Pres†Iso : is†Iso f → is†Iso (f †)
    †Pres†Iso fiso .sec = †Of†MonIs†Epi (fiso .ret)
    †Pres†Iso fiso .ret = †Of†EpiIs†Mon (fiso .sec)

    †MonicsArePIsos : is†Monic f → is†PIso f
    †MonicsArePIsos fmon =
      f ⋆ f † ⋆ f   ≡⟨ sym (⋆Assoc f (f †) f) ⟩
      (f ⋆ f †) ⋆ f ≡⟨ congL _⋆_ fmon ⟩
      id ⋆ f        ≡⟨ ⋆IdL f ⟩
      f             ∎

    †EpicsArePIsos : is†Epic f → is†PIso f
    †EpicsArePIsos fepi =
      f ⋆ f † ⋆ f ≡⟨ congR _⋆_ fepi ⟩
      f ⋆ id      ≡⟨ ⋆IdR f ⟩
      f           ∎

    †PresPIso : is†PIso f → is†PIso (f †)
    †PresPIso fp =
      f † ⋆ f † † ⋆ f † ≡⟨ congR _⋆_ (sym (†-seq f (f †))) ⟩
      f † ⋆ (f ⋆ f †) † ≡⟨ sym (†-seq (f ⋆ (f †)) f) ⟩
      ((f ⋆ f †) ⋆ f) † ≡⟨ cong _† (⋆Assoc f (f †) f) ⟩
      (f ⋆ f † ⋆ f) †   ≡⟨ cong _† fp ⟩
      f †               ∎

  is†Unitary : CatIso C x y → Type ℓ'
  is†Unitary (f , fiso) = fiso .isIso.inv ≡ f †

  is†Unitary→is†Iso : (f : CatIso C x y) → is†Unitary f → is†Iso (f .fst)
  is†Unitary→is†Iso fiso fu = subst (areInv C (fiso .fst)) fu (CatIso→areInv fiso)

  isUnitary†Cat : Type (ℓ-max ℓ ℓ')
  isUnitary†Cat = ∀ {x y} (f : CatIso C x y) → is†Unitary f

  †CatIso : ob → ob → Type ℓ'
  †CatIso x y = Σ[ f ∈ Hom[ x , y ] ] is†Iso f

  idIs†Mon : is†Monic (id {x = x})
  idIs†Mon =
    id ⋆ id † ≡⟨ ⋆IdL (id †) ⟩
    id †      ≡⟨ †-id ⟩
    id        ∎

  seqIs†Mon : (f : Hom[ x , y ]) (g : Hom[ y , z ]) → is†Monic f → is†Monic g → is†Monic (f ⋆ g)
  seqIs†Mon f g fmon gmon =
    (f ⋆ g) ⋆ (f ⋆ g) † ≡⟨ congR _⋆_ (†-seq f g) ⟩
    (f ⋆ g) ⋆ g † ⋆ f † ≡⟨ ⋆Assoc f g ((g †) ⋆ (f †)) ⟩
    f ⋆ g ⋆ g † ⋆ f †   ≡⟨ congR _⋆_ (sym (⋆Assoc g (g †) (f †))) ⟩
    f ⋆ (g ⋆ g †) ⋆ f † ≡⟨ congR _⋆_ (congL _⋆_ gmon) ⟩
    f ⋆ id ⋆ f †        ≡⟨ congR _⋆_ (⋆IdL (f †)) ⟩
    f ⋆ f †             ≡⟨ fmon ⟩
    id                  ∎

  idIs†Epi : is†Epic (id {x = x})
  idIs†Epi =
    id † ⋆ id ≡⟨ ⋆IdR (id †) ⟩
    id †      ≡⟨ †-id ⟩
    id        ∎

  seqIs†Epi : (f : Hom[ x , y ]) (g : Hom[ y , z ]) → is†Epic f → is†Epic g → is†Epic (f ⋆ g)
  seqIs†Epi f g fepi gepi =
    (f ⋆ g) † ⋆ f ⋆ g   ≡⟨ congL _⋆_ (†-seq f g) ⟩
    (g † ⋆ f †) ⋆ f ⋆ g ≡⟨ ⋆Assoc (g †) (f †) (f ⋆ g) ⟩
    g † ⋆ f † ⋆ f ⋆ g   ≡⟨ congR _⋆_ (sym (⋆Assoc (f †) f g)) ⟩
    g † ⋆ (f † ⋆ f) ⋆ g ≡⟨ congR _⋆_ (congL _⋆_ fepi) ⟩
    g † ⋆ id ⋆ g        ≡⟨ congR _⋆_ (⋆IdL g) ⟩
    g † ⋆ g             ≡⟨ gepi ⟩
    id                  ∎

  idIs†Iso : is†Iso (id {x})
  idIs†Iso .sec = idIs†Epi
  idIs†Iso .ret = idIs†Mon

  seqIs†Iso : (f : Hom[ x , y ]) (g : Hom[ y , z ]) → is†Iso f → is†Iso g → is†Iso (f ⋆ g)
  seqIs†Iso f g fiso giso .sec = seqIs†Epi f g (fiso .sec) (giso .sec)
  seqIs†Iso f g fiso giso .ret = seqIs†Mon f g (fiso .ret) (giso .ret)

  id†Iso : †CatIso x x
  id†Iso = id , idIs†Iso

  seq†Iso : †CatIso x y → †CatIso y z → †CatIso x z
  seq†Iso (f , fiso) (g , giso) = f ⋆ g , seqIs†Iso f g fiso giso

  inv†Iso : †CatIso x y → †CatIso y x
  inv†Iso (f , fiso) = f † , †Pres†Iso f fiso

  pathTo†Iso : x ≡ y → †CatIso x y
  pathTo†Iso {x} p = subst (†CatIso x) p id†Iso

  pathTo†Iso-refl : pathTo†Iso refl ≡ id†Iso {x}
  pathTo†Iso-refl = transportRefl _

  record is†Univalent : Type (ℓ-max ℓ ℓ') where
    field
      univ : isEquiv (pathTo†Iso {x} {y})

    univEquiv : (x ≡ y) ≃ †CatIso x y
    univEquiv = pathTo†Iso , univ

    †IsoToPath : †CatIso x y → x ≡ y
    †IsoToPath = invIsEq univ

    †IsoToPath-id : †IsoToPath id†Iso ≡ refl {x = x}
    †IsoToPath-id =
      †IsoToPath id†Iso            ≡⟨ cong †IsoToPath (sym pathTo†Iso-refl) ⟩
      †IsoToPath (pathTo†Iso refl) ≡⟨ retIsEq univ refl ⟩
      refl                         ∎

  makeIs†Univalent : (†IsoToPath : ∀ {x y} → †CatIso x y → x ≡ y)
                   → (∀ {x} → †IsoToPath id†Iso ≡ refl {x = x})
                   → (∀ {x y} (f : †CatIso x y) → pathTo†Iso (†IsoToPath f) .fst ≡ f .fst)
                   → is†Univalent
  makeIs†Univalent †IsoToPath †IsoToPath-id †IsoToPath-β .is†Univalent.univ {x} {y} = TypeIso.isoToIsEquiv iso where

    iso : TypeIso.Iso (x ≡ y) (†CatIso x y)
    iso .TypeIso.Iso.fun = pathTo†Iso
    iso .TypeIso.Iso.inv = †IsoToPath
    iso .TypeIso.Iso.rightInv f = Σ≡Prop (λ _ → isPropAreInv C) (†IsoToPath-β f)
    iso .TypeIso.Iso.leftInv = J (λ y p → †IsoToPath (pathTo†Iso p) ≡ p) (
        †IsoToPath (pathTo†Iso refl) ≡⟨ cong †IsoToPath pathTo†Iso-refl ⟩
        †IsoToPath id†Iso            ≡⟨ †IsoToPath-id ⟩
        refl                         ∎
      )
