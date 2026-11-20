module Cubical.Algebra.Heap.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP

open import Cubical.Reflection.RecordEquiv

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.HITs.PropositionalTruncation

private variable
  ℓ ℓ' : Level
  X Y : Type ℓ

record IsHeap {H : Type ℓ} ([_,_,_] : H → H → H → H) : Type ℓ where
  no-eta-equality
  constructor isheap

  field
    is-set : isSet H
    assoc : ∀ a b c d e → [ a , b , [ c , d , e ] ] ≡ [ [ a , b , c ] , d , e ]
    idl : ∀ a b → [ a , a , b ] ≡ b
    idr : ∀ a b → [ a , b , b ] ≡ a
    inhab : ∥ H ∥₁

unquoteDecl IsHeapIsoΣ = declareRecordIsoΣ IsHeapIsoΣ (quote IsHeap)

record HeapStr (H : Type ℓ) : Type ℓ where
  constructor heapstr

  field
    [_,_,_] : H → H → H → H
    isHeap : IsHeap [_,_,_]

  open IsHeap isHeap public

Heap : ∀ ℓ → Type (ℓ-suc ℓ)
Heap ℓ = TypeWithStr ℓ HeapStr

record IsHeapHom {X : Type ℓ} {Y : Type ℓ'} (H : HeapStr X) (f : X → Y) (H' : HeapStr Y)
  : Type (ℓ-max ℓ ℓ') where

  constructor makeIsHeapHom

  private
    module H = HeapStr H
    module H' = HeapStr H'
  field
    pres-[] : (a b c : X) → f H.[ a , b , c ] ≡ H'.[ f a , f b , f c ]

unquoteDecl IsHeapHomIsoΣ = declareRecordIsoΣ IsHeapHomIsoΣ (quote IsHeapHom)

isPropIsHeap : {H : Type ℓ} ([_,_,_] : H → H → H → H) → isProp (IsHeap [_,_,_])
isPropIsHeap [_,_,_] = isOfHLevelRetractFromIso 1 IsHeapIsoΣ $ isPropΣ isPropIsSet λ is-set →
   isProp×3 (isPropΠ5 λ _ _ _ _ _ → is-set _ _)
            (isPropΠ2 λ _ _ → is-set _ _)
            (isPropΠ2 λ _ _ → is-set _ _)
            isPropPropTrunc

isPropIsHeapHom : (H : HeapStr X) (f : X → Y) (H' : HeapStr Y) → isProp (IsHeapHom H f H')
isPropIsHeapHom H f H' = isOfHLevelRetractFromIso 1 IsHeapHomIsoΣ $
  isPropΠ3 λ _ _ _ → H' .is-set _ _
  where open HeapStr

IsHeapEquiv : {X : Type ℓ} {Y : Type ℓ'} (H : HeapStr X) (e : X ≃ Y) (H' : HeapStr Y) → Type _
IsHeapEquiv H e H' = IsHeapHom H (e .fst) H'

HeapEquiv : (H : Heap ℓ) (H' : Heap ℓ') → Type _
HeapEquiv H H' = Σ[ e ∈ ⟨ H ⟩ ≃ ⟨ H' ⟩ ] IsHeapEquiv (str H) e (str H')

𝒮ᴰ-Heap : DUARel (𝒮-Univ ℓ) HeapStr ℓ
𝒮ᴰ-Heap = 𝒮ᴰ-Record (𝒮-Univ _) IsHeapEquiv
  (fields:
    data[ [_,_,_] ∣ autoDUARel _ _ ∣ pres-[] ]
    prop[ isHeap ∣ (λ _ _ → isPropIsHeap _) ])
  where
    open HeapStr
    open IsHeapHom

HeapPath : (H H' : Heap ℓ) → HeapEquiv H H' ≃ (H ≡ H')
HeapPath = ∫ 𝒮ᴰ-Heap .UARel.ua

uaHeap : {H H' : Heap ℓ} → HeapEquiv H H' → H ≡ H'
uaHeap = HeapPath _ _ .fst
