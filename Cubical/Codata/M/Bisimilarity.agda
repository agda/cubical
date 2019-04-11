{-# OPTIONS --cubical --postfix-projections #-}
module Cubical.Codata.M.Bisimilarity where

open import Cubical.Core.Everything
open import Cubical.Codata.M
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Everything
open Helpers using (J')

-- Bisimilarity as a coinductive record type.
record _≈_ {X : Type₀} {C : IxCont X} {x : X} (a b : M C x) : Type₀ where
  coinductive
  constructor _,_
  field
    head≈ : a .head ≡ b .head
    tails≈ : ∀ y → (pa : C .snd x (a .head) y) (pb : C .snd x (b .head) y)
             → (\ i → C .snd x (head≈ i) y) [ pa ≡ pb ]
             → a .tails y pa ≈ b .tails y pb

open _≈_ public



module _ {X : Type₀} {C : IxCont X} where

  -- Here we show that `a ≡ b` and `a ≈ b` are equivalent.
  --
  -- A direct construction of an isomorphism, like we do for streams,
  -- would be complicated by the type dependencies between the fields
  -- of `M C x` and even more so between the fields of the bisimilarity relation itself.
  --
  -- Instead we rely on theorem 4.7.7 of the HoTT book (fiberwise equivalences) to show that `misib` is an equivalence.

  misib : {x : X} (a b : M C x) → a ≡ b → a ≈ b
  misib a b eq .head≈ i          = eq i .head
  misib a b eq .tails≈ y pa pb q = misib (a .tails y pa) (b .tails y pb) (\ i → eq i .tails y (q i))


  -- With `a` fixed, `misib` is a fiberwise transformation between (a ≡_) and (a ≈_).
  --
  -- We show that the induced map on the total spaces is an
  -- equivalence because it is a map of contractible types.
  --
  -- The domain is the HoTT singleton type, so contractible, while the
  -- codomain is shown to be contractible by `contr-T` below.

  T : ∀ {x} → M C x → Type _
  T a = Σ (M C _) \ b → a ≈ b

  private
    lemma : ∀ {A} (B : Type₀) (P : A ≡ B) (pa : P i0) (pb : P i1) (peq : PathP (\ i → P i) pa pb)
          → PathP (\ i → PathP (\ j → P j) (transp (\ k → P (~ k ∧ i)) (~ i) (peq i)) pb)
                  peq
                  (\ j → transp (\ k → P (~ k ∨ j)) j pb)
    lemma {A} = J' _ \ pa → J' _ \ { i j → transp (\ _ → A) (~ i ∨ j) pa }



  -- We predefine `u'` so that Agda will agree that `contr-T-fst` is productive.
  private
    module Tails x a φ (u : Partial φ (T {x} a)) y (p : C .snd x (hcomp (λ i .o → u o .snd .head≈ i) (a .head)) y) where
      q = transp (\ i → C .snd x (hfill (\ i o → u o .snd .head≈ i) (inS (a .head)) (~ i)) y) i0 p
      a' = a .tails y q
      u' : Partial φ (T a')
      u' (φ = i1) = u 1=1 .fst .tails y p
                  , u 1=1 .snd .tails≈ y q p \ j → transp (\ i → C .snd x (u 1=1 .snd .head≈ (~ i ∨ j)) y) j p


  contr-T-fst : ∀ x a φ → Partial φ (T {x} a) → M C x
  contr-T-fst x a φ u .head      = hcomp (\ i o → u o .snd .head≈ i) (a .head)
  contr-T-fst x a φ u .tails y p = contr-T-fst y a' φ u'
    where
      open Tails x a φ u y p

  -- `contr-T-snd` is productive as the corecursive call appears as
  -- the main argument of transport, which is guardedness-preserving.
  {-# TERMINATING #-}
  contr-T-snd : ∀ x a φ → (u : Partial φ (T {x} a)) → a ≈ contr-T-fst x a φ u
  contr-T-snd x a φ u .head≈ i = hfill (λ { i (φ = i1) → u 1=1 .snd .head≈ i }) (inS (a .head)) i
  contr-T-snd x a φ u .tails≈ y pa pb peq =
    let r = contr-T-snd y (a .tails y pa) φ (\ { (φ = i1) → u 1=1 .fst .tails y pb , u 1=1 .snd .tails≈ y pa pb peq }) in
      transport (\ i → a .tails y pa
                ≈ contr-T-fst y (a .tails y (sym (fromPathP (\ i → peq (~ i))) i)) φ
                  (\ { (φ = i1) → u 1=1 .fst .tails y pb , u 1=1 .snd .tails≈ y
                                  ((fromPathP (\ i → peq (~ i))) (~ i)) pb
                                  \ j → lemma _ (λ h → C .snd x (u _ .snd .head≈ h) y) pa pb peq i j })) r

  contr-T : ∀ x a φ → Partial φ (T {x} a) → T a
  contr-T x a φ u .fst = contr-T-fst x a φ u
  contr-T x a φ u .snd = contr-T-snd x a φ u


  contr-T-φ-fst : ∀ x a → (u : Partial i1 (T {x} a)) → contr-T x a i1 u .fst ≡ u 1=1 .fst
  contr-T-φ-fst x a u i .head = u 1=1 .fst .head
  contr-T-φ-fst x a u i .tails y p
   = let
        q = (transp (\ i → C .snd x (hfill (\ i o → u o .snd .head≈ i) (inS (a .head)) (~ i)) y) i0 p)
      in contr-T-φ-fst y (a .tails y q)
                       (\ o → u o .fst .tails y p
                            , u o .snd .tails≈ y q p \ j → transp (\ i → C .snd x (u 1=1 .snd .head≈ (~ i ∨ j)) y) j p)
                       i

  -- `contr-T-φ-snd` is productive as the corecursive call appears as
  -- the main argument of transport, which is guardedness-preserving (even for paths of a coinductive type).
  {-# TERMINATING #-}
  contr-T-φ-snd : ∀ x a → (u : Partial i1 (T {x} a)) → (\ i → a ≈ contr-T-φ-fst x a u i) [ contr-T x a i1 u .snd ≡ u 1=1 .snd ]
  contr-T-φ-snd x a u i .head≈ = u _ .snd .head≈
  contr-T-φ-snd x a u i .tails≈ y pa pb peq = let
    eqh = u 1=1 .snd .head≈
    r = contr-T-φ-snd y (a .tails y pa) (\ o → u o .fst .tails y pb , u 1=1 .snd .tails≈ y pa pb peq)
    F : I → Type _
    F k = a .tails y pa
        ≈ contr-T-fst y
            (a .tails y (transp (λ j → C .snd x (eqh (k ∧ ~ j)) y) (~ k) (peq k)))
            i1
            (λ _ → u _ .fst .tails y pb
                 , u _ .snd .tails≈ y
                       (transp (λ j → C .snd x (eqh (k ∧ ~ j)) y) (~ k) (peq k))
                       pb
                       (λ j → lemma (C .snd x (u 1=1 .fst .head) y) (λ h → C .snd x (eqh h) y) pa pb peq k j)
             )
    u0 = contr-T-snd y (a .tails y pa) i1 (λ o → u o .fst .tails y pb , u o .snd .tails≈ y pa pb peq)
   in transport
         (λ l → PathP
           (λ z → a .tails y pa
                ≈ contr-T-φ-fst y
                   (a .tails y (transp (λ k → C .snd x (u 1=1 .snd .head≈ (~ k ∧ l)) y) (~ l) (peq l)))
                   (λ _ → u _ .fst .tails y pb
                        , u _ .snd .tails≈ y (transp (λ k → C .snd x (u _ .snd .head≈ (~ k ∧ l)) y) (~ l) (peq l)) pb
                               \ j → lemma (C .snd x (u 1=1 .fst .head) y) (λ h → C .snd x (eqh h) y) pa pb peq l j)
                   z)
           (transpFill {A = F i0} i0 (\ i → inS (F i)) u0 l)
           (u _ .snd .tails≈ y pa pb peq))
         r
         i

  contr-T-φ : ∀ x a → (u : Partial i1 (T {x} a)) → contr-T x a i1 u ≡ u 1=1
  contr-T-φ x a u i .fst = contr-T-φ-fst x a u i
  contr-T-φ x a u i .snd = contr-T-φ-snd x a u i


  contr-T' : ∀ {x} a → isContr (T {x} a)
  contr-T' a = isContrPartial→isContr (contr-T _ a) \ u → sym (contr-T-φ _ a (\ _ → u))


  bisimEquiv : ∀ {x} {a b : M C x} → isEquiv (misib a b)
  bisimEquiv = isContrToUniv _≈_ (misib _ _) contr-T'
