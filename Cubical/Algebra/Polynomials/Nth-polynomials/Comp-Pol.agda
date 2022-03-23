{-# OPTIONS --safe #-}
module Cubical.Work.Nth-polynomials.Comp-Pol where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Polynomials

open import Cubical.Work.Nth-polynomials.Base
open import Cubical.Work.Nth-polynomials.CommRing-Structure

private variable
  l l' : Level

module Compo-Pol-nm (A' : CommRing l) (n m : ℕ) where
  private
    A = fst A'
  open CommRingStr (snd A')

  module M   = PolyHIT A'
  module Mr  = Nth-Pol-CommRing A' m
  module N+M  = PolyHIT A'
  module N+Mr = Nth-Pol-CommRing A' (n +n m)
  module N∘M = PolyHIT (Mr.nth-Pol-CommRing)
  module N∘Mr  = Nth-Pol-CommRing Mr.nth-Pol-CommRing n 

-----------------------------------------------------------------------------

  N∘M→N+M : N∘M.Poly n → N+M.Poly (n +n m)
  N∘M→N+M = N∘M.Poly-Rec-Set.f n (N+M.Poly (n +n m)) N+M.trunc
           N+M.0P
           (λ v → N+M.Poly-Rec-Set.f m (N+M.Poly (n +n m)) N+M.trunc
                   N+M.0P
                   (λ v' a → N+M.base (v ++ v') a)
                   N+M._Poly+_
                   N+M.Poly+-assoc
                   N+M.Poly+-Rid
                   N+M.Poly+-comm
                   (λ v' → {!N∘M.base-neutral!})
                   (λ v' a b → N+M.base-add (v ++ v') a b))
           N+M._Poly+_
           N+M.Poly+-assoc
           N+M.Poly+-Rid
           N+M.Poly+-comm
           {!!}
           {!!}


  sep-vec : (k l : ℕ) → Vec ℕ (k +n l) → (Vec ℕ k) ×  (Vec ℕ l )
  sep-vec zero l v = [] , v
  sep-vec (suc k) l (x ∷ v) = (x ∷ fst (sep-vec k l v)) , (snd (sep-vec k l v))

  -- NM→N∘M : NM.Poly (n +n m) → N∘M.Poly n
  -- NM→N∘M = NM.Poly-Rec-Set.f (n +n m) (N∘M.Poly n) N∘M.trunc
  --          N∘M.0P
  --          (λ v a → {!!})
  --          N∘M._Poly+_
  --          N∘M.Poly+-assoc
  --          N∘M.Poly+-Rid
  --          N∘M.Poly+-comm
  --          {!!}
  --          {!!}





