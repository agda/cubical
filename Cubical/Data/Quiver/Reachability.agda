module Cubical.Data.Quiver.Reachability where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Functions.Embedding

open import Cubical.Data.Empty as ⊥ hiding (elim ; rec)
open import Cubical.Data.FinData as FD
open import Cubical.Data.FinData.FinSet
import Cubical.Data.SumFin as SumFin
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum

open import Cubical.Data.Quiver.Base

import Cubical.Data.Equality as Eq

open import Cubical.HITs.PropositionalTruncation as PT hiding (elim ; rec ; map)

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

private
  variable
    ℓ ℓ' : Level
    n : ℕ

module Reachability {ℓ} {ℓ'}
  (ob : FinSet ℓ)
  (Q : QuiverOver ⟨ ob ⟩ ℓ')
  (isFinSetMor : isFinSet (Q .QuiverOver.mor ))
  where

  open QuiverOver Q

  data Walk (end : ⟨ ob ⟩) : ⟨ ob ⟩ → ℕ → Type (ℓ-max ℓ ℓ') where
    nil : Walk end end 0
    cons : ∀ n (e : mor) → Walk end (cod e) n → Walk end (dom e) (suc n)

  Walk' : (end start : ⟨ ob ⟩) → Type (ℓ-max ℓ ℓ')
  Walk' end start = Σ[ n ∈ ℕ ] Walk end start n

  trivialWalk→sameEndpoints :
    (end start : ⟨ ob ⟩) →
    Walk end start 0 →
    end ≡ start
  trivialWalk→sameEndpoints end start nil = refl

  module _
    (isFinOrdMor : isFinOrd mor) where
    isFinOrdWalk :
      ∀ (n : ℕ) →
      (end start : ⟨ ob ⟩) →
      isFinOrd (Walk end start n)
    isFinOrdWalk zero end start =
      decRec
        (λ end≡start →
           1 ,
           isoToEquiv (
             iso
               (λ _ → inl _)
               (λ { (inl tt) → subst (λ z → Walk end z zero) end≡start nil })
               (λ { (inl tt) → refl})
               λ { nil →
                 cong (λ u → subst (λ z → Walk end z zero) u nil)
                   (isFinSet→isSet (str ob) end end end≡start refl) ∙
                 substRefl {B = λ z → Walk end z zero}
                   Walk.nil }))
        (λ ¬q≡q' →
          0 ,
          uninhabEquiv
            (λ walk → ¬q≡q' (trivialWalk→sameEndpoints _ _ walk)) (λ x → x)
            )
        (isFinSet→Discrete (str ob) end start)
    isFinOrdWalk (suc n) end start =
      EquivPresIsFinOrd
        {A = Σ[ e ∈ mor ] Σ[ src≡start ∈ dom e Eq.≡ start ] Walk end (cod e) n}
        (isoToEquiv
          (iso
            (λ { (e , Eq.refl , walk) → cons n e walk })
            (λ { (cons .n e walk) → e , Eq.refl , walk })
            (λ { (cons .n e walk) → refl } )
            λ { (e , Eq.refl , walk) → refl
            }
          ))
        (isFinOrdΣ mor isFinOrdMor
          (λ e → _)
          (λ e → isFinOrdΣ (dom e Eq.≡ start)
            (decRec
              (λ src≡start →
                isContr→isFinOrd ((Eq.pathToEq src≡start) ,
                (λ { Eq.refl →
                 cong (Eq.pathToEq)
                   (isFinSet→isSet (str ob) (dom e) (dom e) src≡start refl) ∙
                Eq.eqToPath Eq.pathToEq-reflPath })))
              (λ ¬src≡start → 0 , uninhabEquiv (λ eq → ¬src≡start (Eq.eqToPath eq)) λ x → x)
              (isFinSet→Discrete (str ob) (dom e) start))
            _
            λ { Eq.refl → isFinOrdWalk n end (cod e)}))

    isFinSetWalk :
      (end start : ⟨ ob ⟩) →
      (n : ℕ) →
      isFinSet (Walk end start n)
    isFinSetWalk end start n = isFinOrd→isFinSet (isFinOrdWalk _ _ _)
    isSetWalk :
      (end start : ⟨ ob ⟩) →
      (n : ℕ) →
      isSet (Walk end start n)
    isSetWalk end start n = isFinSet→isSet (isFinSetWalk _ _ _)

  first-edge :
    {end start : ⟨ ob ⟩} →
    (walk : Walk end start (suc n)) →
    mor
  first-edge (cons _ e walk) = e

  tail :
    {end start : ⟨ ob ⟩} →
    (walk : Walk end start (suc n)) →
    Walk end (cod (first-edge walk)) n
  tail (cons _ e walk) = walk

  snocWalk :
    {start : ⟨ ob ⟩} →
    (e : mor) →
    Walk (dom e) start n →
    Walk (cod e) start (suc n)
  snocWalk e nil = cons 0 e nil
  snocWalk e (cons n e' walk) = cons (suc n) e' (snocWalk e walk)

  vertices :
    {end start : ⟨ ob ⟩} →
    Walk end start n →
    Fin (suc n) → ⟨ ob ⟩
  vertices {start = start} walk zero = start
  vertices (cons n e walk) (suc m) = vertices walk m

  hasUniqueVertices : ∀ {end start : ⟨ ob ⟩} → Walk end start n → Type ℓ
  hasUniqueVertices walk = isEmbedding (vertices walk)

  hasUniqueVertices→boundedLength :
    {end start : ⟨ ob ⟩} →
    (walk : Walk end start n) →
    hasUniqueVertices walk →
    n < card ob
  hasUniqueVertices→boundedLength walk unique =
    card↪Inequality' (_ , isFinSetFinData) ob (vertices walk) unique

  uniqueVerticesWalk : ∀ (end start : ⟨ ob ⟩) → Type (ℓ-max ℓ ℓ')
  uniqueVerticesWalk end start =
    Σ[ n ∈ ℕ ]
    Σ[ walk ∈ Walk end start n ] hasUniqueVertices walk

  tailUniqueVertices :
    {end start : ⟨ ob ⟩} →
    (walk : Walk end start (suc n)) →
    hasUniqueVertices walk →
    hasUniqueVertices (tail walk)
  tailUniqueVertices (cons _ e walk) uniq =
    isEmbedding-∘ uniq (injEmbedding isSetFin injSucFin)

  dec-hasUniqueVertices :
    ∀ {end start : ⟨ ob ⟩} → (walk : Walk end start n) →
      Dec (hasUniqueVertices walk)
  dec-hasUniqueVertices nil =
    yes (injEmbedding (isFinSet→isSet (str ob))
      (λ { {zero} {zero} → λ _ → refl }))
  dec-hasUniqueVertices (cons n e walk) =
    decRec
      (λ (k , p) → no (λ x →
        FD.znots (x zero (suc k) .equiv-proof (sym p) .fst .fst)))
      (λ ¬repeatFirst →
        decRec
          (λ uniqWalk → yes
            (λ j k →
              injEmbedding
                (isFinSet→isSet (str ob))
                (λ {
                  {zero} {zero} → λ _ → refl
                ; {zero} {suc b} →
                  λ dom≡vert →
                    ⊥.rec (¬repeatFirst (b , (sym dom≡vert)))
                ; {suc a} {zero} →
                  λ dom≡vert → ⊥.rec (¬repeatFirst (a , dom≡vert))
                ; {suc a} {suc b} → λ verts≡ →
                  decRec
                    (λ a≡b → cong suc a≡b)
                    (λ ¬a≡b →
                      ⊥.rec
                        (¬a≡b (uniqWalk a b .equiv-proof verts≡ .fst .fst)))
                    (discreteFin a b)
                })
                j
                k)
          )
          (λ ¬uniqWalk → no (λ x → ¬uniqWalk (tailUniqueVertices _ x)))
          (dec-hasUniqueVertices walk)
      )
      (DecΣ (suc n) (λ k → vertices walk k ≡ dom e)
      (λ k → isFinSet→Discrete (str ob) (vertices walk k) (dom e)))


  drop : {end start : ⟨ ob ⟩} →
    (walk : Walk end start n) →
    (k : Fin (suc n)) →
    Σ[ m ∈ ℕ ] Walk end (vertices walk k) m
  drop walk zero = _ , walk
  drop (cons n e walk) (suc k) = drop walk k

  dropPreservesUnique :
    {end start : ⟨ ob ⟩} →
    (uniqWalk : uniqueVerticesWalk end start) →
    (k : Fin (suc (uniqWalk .fst))) →
    hasUniqueVertices (drop (uniqWalk .snd .fst) k .snd)
  dropPreservesUnique uniqWalk zero = uniqWalk .snd .snd
  dropPreservesUnique (n , cons n-1 e walk , uniq) (suc k) =
    dropPreservesUnique
      (n-1 ,
      (walk , tailUniqueVertices (cons n-1 e walk) uniq)) k

  UniqueWalk : ∀ (end start : ⟨ ob ⟩) → Type _
  UniqueWalk end start =
    Σ[ n ∈ Fin (card ob) ]
    Σ[ walk ∈ Walk end start (toℕ n) ] hasUniqueVertices walk


  makeUnique :
    {end start : ⟨ ob ⟩} →
    (walk : Walk end start n) →
    uniqueVerticesWalk end start
  makeUnique nil =
    0 ,
    nil ,
    injEmbedding
      (isFinSet→isSet (str ob))
      (λ _ → isContr→isProp isContrFin1 _ _)
  makeUnique {end = end}(cons n e walk) =
    let new-vert = dom e in
    let new-edge = e in
    let n' , walk' , uniq = makeUnique walk in
    decRec
      -- There is a repeated vertex
      (λ (m , p) →
        let n'' , walk'' = drop walk' m in
        let uniq' = dropPreservesUnique (n' , (walk' , uniq)) m in
        n'' ,
        subst (λ z → Σ[ w ∈ Walk end z n'' ] hasUniqueVertices w) p (walk'' , uniq'))
      -- There is no repeated vertex
      (λ ¬ΣnewVert →
        suc n' ,
        (cons n' new-edge walk' ,
        injEmbedding
          (isFinSet→isSet (str ob))
              λ { {zero} {zero} p → refl
                ; {zero} {suc j} p → ⊥.rec (¬ΣnewVert (j , (sym p)))
                ; {suc i} {zero} p → ⊥.rec (¬ΣnewVert (i , p))
                ; {suc i} {suc j} p → congS suc $ isEmbedding→Inj uniq i j p
                }
          )
      )
      (DecΣ
        (suc n')
        (λ k → vertices walk' k ≡ new-vert)
        (λ k → isFinSet→Discrete (str ob) (vertices walk' k) new-vert))

  Walk→UniqueWalk :
    {end start : ⟨ ob ⟩} →
    (walk : Walk end start n) →
    UniqueWalk end start
  Walk→UniqueWalk {end = end}{start = start} walk =
    let m , walk' , uniq = makeUnique walk in
    let bound = hasUniqueVertices→boundedLength walk' uniq in
    let to-and-fro = sym (toFromId' (card ob) m bound) in
    fromℕ' (card ob) m bound ,
      subst
        (λ n' → Σ[ walk ∈ Walk end start n' ] hasUniqueVertices walk)
          to-and-fro (walk' , uniq)

  Reachable PathReachable : ⟨ ob ⟩ → ⟨ ob ⟩ → Type _
  Reachable end start =
    PT.∥ Σ[ n ∈ ℕ ] Walk end start n  ∥₁
  PathReachable end start =
    PT.∥ UniqueWalk end start ∥₁

  PathReachable≃Reachable :
    (end start : ⟨ ob ⟩) → PathReachable end start ≃ Reachable end start
  PathReachable≃Reachable end start =
    propBiimpl→Equiv isPropPropTrunc isPropPropTrunc
      (PT.map (λ gp → (toℕ (gp .fst)) , (gp .snd .fst)))
      (PT.map (λ (n , gw) → Walk→UniqueWalk gw))

  isFinSetHasUniqueVertices :
    {end start : ⟨ ob ⟩} →
    (gw : Walk end start n) → isFinSet (hasUniqueVertices gw)
  isFinSetHasUniqueVertices gw =
    isFinSetIsEmbedding (_ , isFinSetFinData) ob (vertices gw)

  module _
    (isFinOrdMor : isFinOrd mor)
    (end start : ⟨ ob ⟩)
    where

    isFinOrdUniqueWalk : isFinOrd (UniqueWalk end start)
    isFinOrdUniqueWalk =
      isFinOrdΣ
        (Fin (ob .snd .fst))
        ((card ob) , SumFin.FinData≃SumFin)
        (λ n → Σ-syntax (Walk end start (toℕ n)) hasUniqueVertices)
        (λ m → isFinOrdΣ
          (Walk end start (toℕ m))
          (isFinOrdWalk isFinOrdMor (toℕ m) end start)
          hasUniqueVertices
          (λ walk → DecProp→isFinOrd ((_ , isPropIsEmbedding) , dec-hasUniqueVertices walk)))
    isFinSetUniqueWalk : isFinSet (UniqueWalk end start)
    isFinSetUniqueWalk =
      isFinOrd→isFinSet isFinOrdUniqueWalk

    DecPathReachable : Dec (PathReachable end start)
    DecPathReachable = isFinSet→Dec∥∥ isFinSetUniqueWalk

    DecReachable : Dec (Reachable end start)
    DecReachable =
      EquivPresDec
        (PathReachable≃Reachable end start)
        DecPathReachable

  Reachable-is-reflexive : (u : ⟨ ob ⟩) → Reachable u u
  Reachable-is-reflexive u = ∣ 0 , nil ∣₁
