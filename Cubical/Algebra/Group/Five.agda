{-# OPTIONS --safe #-}

-- This module proves the Five lemma[1] over group homomorphisms.
--
-- [1]: https://en.wikipedia.org/wiki/Five_lemma

module Cubical.Algebra.Group.Five where

open import Agda.Primitive

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Exact
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms

open BijectionIso
open IsGroupHom

private
  variable
    ℓ ℓ' : Level

module _
  {A B C D E A' B' C' D' E' : Group ℓ}
  {f : GroupHom A B} {g : GroupHom B C} {h : GroupHom C D} {j : GroupHom D E}
  {l : GroupHom A A'} {m : BijectionIso B B'} {n : GroupHom C C'} {p : BijectionIso D D'} {q : GroupHom E E'}
  {r : GroupHom A' B'} {s : GroupHom B' C'} {t : GroupHom C' D'} {u : GroupHom D' E'}
  (fg : IsExact f g) (gh : IsExact g h) (hj : IsExact h j)
  (rs : IsExact r s) (st : IsExact s t) (tu : IsExact t u)
  (lSurj : isSurjective l)
  (qInj : isInjective q)
  (sq1 : (a : fst A) → r .fst (l .fst a) ≡ m .fun .fst (f .fst a))
  (sq2 : (b : fst B) → s .fst (m .fun .fst b) ≡ n .fst (g .fst b))
  (sq3 : (c : fst C) → t .fst (n .fst c) ≡ p .fun .fst (h .fst c))
  (sq4 : (d : fst D) → u .fst (p .fun .fst d) ≡ q .fst (j .fst d))
  where
    module _ where
      nInjective : isInjective n
      nInjective c c-in-ker[n] = goal where
        goalTy = c ≡ C .snd .GroupStr.1g
        goalTyIsProp = let open GroupStr (C .snd) in is-set c 1g
        untrunc = λ (p : ∥ goalTy ∥₁) → PT.rec goalTyIsProp (λ x → x) p

        t[n[c]]≡0 : t .fst (n .fst c) ≡ D' .snd .GroupStr.1g
        t[n[c]]≡0 = cong (t .fst) c-in-ker[n] ∙ t .snd .pres1

        t[n[c]]≡p[h[c]] : t .fst (n .fst c) ≡ p .fun .fst (h .fst c)
        t[n[c]]≡p[h[c]] = sq3 c

        p[h[c]]≡0 : p .fun .fst (h .fst c) ≡ D' .snd .GroupStr.1g
        p[h[c]]≡0 = sym t[n[c]]≡p[h[c]] ∙ t[n[c]]≡0

        h[c]≡0 : h .fst c ≡ D .snd .GroupStr.1g
        h[c]≡0 = p .inj (h .fst c) p[h[c]]≡0

        c-in-ker[h] : isInKer h c
        c-in-ker[h] = h[c]≡0

        c-in-im[g] : isInIm g c
        c-in-im[g] = gh c .ker∈im c-in-ker[h]

        rest : (b : ⟨ B ⟩) → (g .fst b ≡ c) → goalTy

        goal = untrunc (PT.map (λ x → rest (fst x) (snd x)) c-in-im[g])

        rest b g[b]≡c = goal2 where

          n[g[b]]≡0 : n .fst (g .fst b) ≡ C' .snd .GroupStr.1g
          n[g[b]]≡0 = cong (n .fst) g[b]≡c ∙ c-in-ker[n]

          m[b] : ⟨ B' ⟩
          m[b] = m .fun .fst b

          s[m[b]]≡n[g[b]] : s .fst m[b] ≡ n .fst (g .fst b)
          s[m[b]]≡n[g[b]] = sq2 b

          s[m[b]]≡0 : s .fst m[b] ≡ C' .snd .GroupStr.1g
          s[m[b]]≡0 = s[m[b]]≡n[g[b]] ∙ n[g[b]]≡0

          m[b]-in-ker[s] : isInKer s m[b]
          m[b]-in-ker[s] = s[m[b]]≡0

          m[b]-in-im[r] : isInIm r m[b]
          m[b]-in-im[r] = rs m[b] .ker∈im m[b]-in-ker[s]

          rest2 : (a' : ⟨ A' ⟩) → (r .fst a' ≡ m[b]) → (a : ⟨ A ⟩) → l .fst a ≡ a' → goalTy

          goal2 =
            let inner = λ x → untrunc (PT.map (λ y → rest2 (x .fst) (x .snd) (y .fst) (y .snd)) (lSurj (x .fst))) in
            untrunc (PT.map inner m[b]-in-im[r])

          rest2 a' r[a']≡m[b] a l[a]≡a' = c≡0 where

            m[f[a]] : ⟨ B' ⟩
            m[f[a]] = m .fun .fst (f .fst a)

            r[l[a]]≡m[f[a]] : r .fst (l .fst a) ≡ m[f[a]]
            r[l[a]]≡m[f[a]] = sq1 a

            m[f[a]]≡m[b] : m[f[a]] ≡ m[b]
            m[f[a]]≡m[b] = sym r[l[a]]≡m[f[a]] ∙ cong (r .fst) l[a]≡a' ∙ r[a']≡m[b]

            f[a]≡b : f .fst a ≡ b
            f[a]≡b = isInjective→isMono (m .fun) (m .inj) m[f[a]]≡m[b]

            g[f[a]]≡c : g .fst (f .fst a) ≡ c
            g[f[a]]≡c = cong (g .fst) f[a]≡b ∙ g[b]≡c

            f[a]-in-im[f] : isInIm f (f .fst a)
            f[a]-in-im[f] = ∣ a , refl ∣₁

            f[a]-in-ker[g] : isInKer g (f .fst a)
            f[a]-in-ker[g] = fg (f .fst a) .im∈ker f[a]-in-im[f]

            g[f[a]]≡0 : g .fst (f .fst a) ≡ C .snd .GroupStr.1g
            g[f[a]]≡0 = f[a]-in-ker[g]

            c≡0 : c ≡ C .snd .GroupStr.1g
            c≡0 = sym g[f[a]]≡c ∙ g[f[a]]≡0

    module _ where
      nSurjective : isSurjective n
      nSurjective c' = goal where
        goalTy = isInIm n c'
        untrunc = λ (p : ∥ goalTy ∥₁) → PT.rec (isPropIsInIm n c') (λ x → x) p

        d' : ⟨ D' ⟩
        d' = t .fst c'

        pGroupIso = BijectionIso→GroupIso p
        pIso = pGroupIso .fst
        pInv = Iso.inv pIso

        d : ⟨ D ⟩
        d = pInv d'

        p[d]≡t[c'] : p .fun .fst d ≡ t .fst c'
        p[d]≡t[c'] = Iso.rightInv pIso d'

        u[p[d]] : ⟨ E' ⟩
        u[p[d]] = u .fst (p .fun .fst d)

        j[d] : ⟨ E ⟩
        j[d] = j .fst d

        q[j[d]] : ⟨ E' ⟩
        q[j[d]] = q .fst j[d]

        u[p[d]]≡q[j[d]] : u[p[d]] ≡ q[j[d]]
        u[p[d]]≡q[j[d]] = sq4 d

        d'-in-ker[u] : isInKer u d'
        d'-in-ker[u] = tu d' .im∈ker ∣ (c' , refl) ∣₁

        u[p[d]]≡0 : u[p[d]] ≡ E' .snd .GroupStr.1g
        u[p[d]]≡0 = cong (u .fst) p[d]≡t[c'] ∙ d'-in-ker[u]

        q[j[d]]≡0 : q[j[d]] ≡ E' .snd .GroupStr.1g
        q[j[d]]≡0 = sym u[p[d]]≡q[j[d]] ∙ u[p[d]]≡0

        j[d]≡0 : j[d] ≡ E .snd .GroupStr.1g
        j[d]≡0 = qInj j[d] q[j[d]]≡0

        d-in-ker[j] : isInKer j d
        d-in-ker[j] = j[d]≡0

        d-in-im[h] : isInIm h d
        d-in-im[h] = hj d .ker∈im d-in-ker[j]

        rest : (c : ⟨ C ⟩) → h .fst c ≡ d → goalTy

        goal = untrunc (PT.map (λ x → rest (x .fst) (x .snd)) d-in-im[h])

        rest c h[c]≡d = goal2 where
          n[c] : ⟨ C' ⟩
          n[c] = n .fst c

          t[n[c]]≡p[h[c]] : t .fst n[c] ≡ p .fun .fst (h .fst c)
          t[n[c]]≡p[h[c]] = sq3 c

          t[n[c]]≡t[c'] : t .fst n[c] ≡ t .fst c'
          t[n[c]]≡t[c'] =
            t .fst n[c]             ≡⟨ t[n[c]]≡p[h[c]] ⟩
            p .fun .fst (h .fst c)  ≡⟨ cong (p .fun .fst) h[c]≡d ⟩
            p .fun .fst d           ≡⟨ p[d]≡t[c'] ⟩
            t .fst c' ∎

          c'-n[c] : ⟨ C' ⟩
          c'-n[c] = let open GroupStr (C' .snd) in c' · (inv n[c])

          t[c'-n[c]]≡0 : t .fst c'-n[c] ≡ D' .snd .GroupStr.1g
          t[c'-n[c]]≡0 =
            let open GroupStr (C' .snd) renaming (_·_ to _·ᶜ_; inv to invᶜ; 1g to 1gᶜ) in
            let open GroupStr (D' .snd) renaming (_·_ to _·ᵈ_; inv to invᵈ; 1g to 1gᵈ) hiding (isGroup) in
            t .fst (c' ·ᶜ (invᶜ n[c]))          ≡⟨ t .snd .pres· c' (invᶜ n[c]) ⟩
            (t .fst c') ·ᵈ (t .fst (invᶜ n[c])) ≡⟨ cong ((t .fst c') ·ᵈ_) (t .snd .presinv n[c]) ⟩
            (t .fst c') ·ᵈ (invᵈ (t .fst n[c])) ≡⟨ cong (λ z → (t .fst c') ·ᵈ (invᵈ z)) t[n[c]]≡t[c'] ⟩
            (t .fst c') ·ᵈ (invᵈ (t .fst c'))   ≡⟨ cong ((t .fst c') ·ᵈ_) (sym (t .snd .presinv c')) ⟩
            (t .fst c') ·ᵈ (t .fst (invᶜ c'))   ≡⟨ sym (t .snd .pres· c' (invᶜ c')) ⟩
            t .fst (c' ·ᶜ (invᶜ c'))            ≡⟨ cong (t .fst) (IsGroup.·InvR isGroup c') ⟩
            t .fst 1gᶜ                          ≡⟨ t .snd .pres1 ⟩
            1gᵈ ∎

          [c'-n[c]]-in-ker[t] : isInKer t c'-n[c]
          [c'-n[c]]-in-ker[t] = t[c'-n[c]]≡0

          [c'-n[c]]-in-im[s] : isInIm s c'-n[c]
          [c'-n[c]]-in-im[s] = st c'-n[c] .ker∈im [c'-n[c]]-in-ker[t]

          rest2 : (b' : ⟨ B' ⟩) → s .fst b' ≡ c'-n[c] → goalTy

          goal2 = untrunc (PT.map (λ x → rest2 (x .fst) (x .snd)) [c'-n[c]]-in-im[s])

          rest2 b' s[b']≡c'-n[c] = goal3 where
            mGroupIso = BijectionIso→GroupIso m
            mIso = mGroupIso .fst
            mInv = Iso.inv mIso

            b : ⟨ B ⟩
            b = mInv b'

            m[b]≡b' : m .fun .fst b ≡ b'
            m[b]≡b' = Iso.rightInv mIso b'

            s[m[b]]≡s[b'] : s .fst (m .fun .fst b) ≡ s .fst b'
            s[m[b]]≡s[b'] = cong (s .fst) m[b]≡b'

            s[m[b]]≡c'-n[c] : s .fst (m .fun .fst b) ≡ c'-n[c]
            s[m[b]]≡c'-n[c] = s[m[b]]≡s[b'] ∙ s[b']≡c'-n[c]

            g[b] : ⟨ C ⟩
            g[b] = g .fst b

            g[b]+c : ⟨ C ⟩
            g[b]+c = C .snd .GroupStr._·_ g[b] c

            n[g[b]] : ⟨ C' ⟩
            n[g[b]] = n .fst g[b]

            n[g[b]]≡s[m[b]] : n[g[b]] ≡ s .fst (m .fun .fst b)
            n[g[b]]≡s[m[b]] = sym (sq2 b)

            n[g[b]]≡c'-n[c] : n[g[b]] ≡ c'-n[c]
            n[g[b]]≡c'-n[c] = n[g[b]]≡s[m[b]] ∙ s[m[b]]≡c'-n[c]

            n[g[b]]+n[c]≡c' : C' .snd .GroupStr._·_ n[g[b]] n[c] ≡ c'
            n[g[b]]+n[c]≡c' =
              let open GroupStr (C' .snd) in
              cong (_· n[c]) n[g[b]]≡c'-n[c] ∙ sym (·Assoc c' (inv n[c]) n[c]) ∙ cong (c' ·_) (·InvL n[c]) ∙ ·IdR c'

            n[g[b]+c]≡c' : n .fst g[b]+c ≡ c'
            n[g[b]+c]≡c' = n .snd .pres· g[b] c ∙ n[g[b]]+n[c]≡c'

            goal3 = ∣ (g[b]+c , n[g[b]+c]≡c') ∣₁

    lemma : BijectionIso C C'
    lemma = bijIso n nInjective nSurjective
