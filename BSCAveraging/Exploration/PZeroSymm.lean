import BSCAveraging.Exploration.PZero
/-! # `PZeroSymm` — exploration

None of this file is used by the three theorems of `BSCAveraging.Basic`; it is
kept as a record of the search. -/

/-! # Interior fixed points at `p = 0`: a symmetric side forces a symmetric response

`NOTES.md` §7c‴ classifies the `p = 0` alternating-maximisation fixed points.  A
side with an atom at `±1` is stationary for free (only 3 contact conditions for
3 multipliers); a side with two *interior* atoms carries one residual equation,
the bitangency condition.  This file proves the half of the classification that
is a theorem: **against a symmetric `T`, no asymmetric interior response can be
bitangent**, so a symmetric side forces a symmetric response.

Two collapses, both special to `δ = 1`.

* For a general two-atom `T = (c,−d)` the second derivative of the atom value
  loses its linear term as well — `ρ₋d − ρ₊c = (cd − dc)/(c+d) = 0` — leaving

  ```
  φ_T″(s)·(1+s·c)(1−s·d) = c·d
  ```

  so `D″` is a *quadratic* over positive denominators and `D` has at most four
  zeros with multiplicity.  A bitangency spends exactly four.

* A symmetric `T` makes the atom value **even**: `φ_(c,c)(s) = f_e(c·s)`
  (`phiSym`).  Then evaluating the certificate `D ≥ 0` at the *mirrored* points
  `−a` and `b` forces `λ₁ = 0` (`lam1_eq_zero`), so `D` is even, and `D′`
  vanishes at `0`, at `a`, and — by Rolle between the two contacts — somewhere
  in between.  Two more Rolle steps give two distinct zeros of `D″` in `(0,1)`,
  which the quadratic cannot have unless `c = 1`.

Hence `a = b` (`interior_response_symmetric`).  What is *not* covered here is a
fixed point with both sides asymmetric; the numerics in
`numerics/p0_fixed_points.py` find none.

See `NOTES.md` §7c‴. -/

open Real Set

namespace BSCAveraging

variable {l0 l1 l2 c a b : ℝ}

/-! ## The symmetric atom value and its derivatives -/

/-- Against a symmetric `T = (c,−c)` the atom value is **even**: it is `f_e(c·s)`. -/
noncomputable def phiSym (c s : ℝ) : ℝ := fe (c * s)

/-- The slack of a certificate against a symmetric `T`. -/
noncomputable def DSym (l0 l1 l2 c s : ℝ) : ℝ := l0 + l1 * s + l2 * fe s - phiSym c s

/-- Its derivative. -/
noncomputable def DSym' (l1 l2 c s : ℝ) : ℝ := l1 + l2 * artanh s - c * artanh (c * s)

/-- Its second derivative. -/
noncomputable def DSym'' (l2 c s : ℝ) : ℝ :=
  l2 * (1 / (1 - s ^ 2)) - c ^ 2 * (1 / (1 - (c * s) ^ 2))

lemma continuous_DSym : Continuous (DSym l0 l1 l2 c) := by
  have h : Continuous fun s : ℝ => fe (c * s) :=
    continuous_fe.comp (continuous_const.mul continuous_id)
  exact ((continuous_const.add (continuous_const.mul continuous_id)).add
    (continuous_const.mul continuous_fe)).sub h

lemma hasDerivAt_DSym {s : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hs0 : -1 < s) (hs1 : s < 1) :
    HasDerivAt (DSym l0 l1 l2 c) (DSym' l1 l2 c s) s := by
  have hcs0 : -1 < c * s := by nlinarith
  have hcs1 : c * s < 1 := by nlinarith
  have hfe : HasDerivAt fe (artanh s) s := by
    have h := hasDerivAt_fe_affine (p := 0) (K := 1) (x := s) (by simpa using hs0)
      (by simpa using hs1)
    simpa using h
  have hPhi : HasDerivAt (fun t : ℝ => fe (c * t)) (artanh (c * s) * c) s := by
    have h := hasDerivAt_fe_affine (p := 0) (K := c) (x := s) (by simpa using hcs0)
      (by simpa using hcs1)
    simpa using h
  have h := (((hasDerivAt_const s l0).add ((hasDerivAt_id s).const_mul l1)).add
    (hfe.const_mul l2)).sub hPhi
  have heq : 0 + l1 * 1 + l2 * artanh s - artanh (c * s) * c = DSym' l1 l2 c s := by
    simp only [DSym']; ring
  rw [heq] at h
  exact h

lemma hasDerivAt_DSym' {s : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hs0 : -1 < s) (hs1 : s < 1) :
    HasDerivAt (DSym' l1 l2 c) (DSym'' l2 c s) s := by
  have hcs0 : -1 < c * s := by nlinarith
  have hcs1 : c * s < 1 := by nlinarith
  have hart : HasDerivAt artanh (1 / (1 - s ^ 2)) s := hasDerivAt_artanh hs0 hs1
  have hlin : HasDerivAt (fun t : ℝ => c * t) c s := by
    simpa using (hasDerivAt_id s).const_mul c
  have hart2 : HasDerivAt (fun t : ℝ => artanh (c * t)) (1 / (1 - (c * s) ^ 2) * c) s :=
    (hasDerivAt_artanh hcs0 hcs1).comp s hlin
  have h := ((hasDerivAt_const s l1).add (hart.const_mul l2)).sub (hart2.const_mul c)
  have heq : 0 + l2 * (1 / (1 - s ^ 2)) - c * (1 / (1 - (c * s) ^ 2) * c)
      = DSym'' l2 c s := by
    simp only [DSym'']; ring
  rw [heq] at h
  exact h

/-! ## `λ₁ = 0`: the certificate evaluated at the mirrored points -/

/-- `f_e` is even, so the slack at `−s` differs from the slack at `s` only in the
`λ₁` term. -/
lemma DSym_neg (l0 l1 l2 c s : ℝ) :
    DSym l0 l1 l2 c (-s) = DSym l0 l1 l2 c s - 2 * (l1 * s) := by
  simp only [DSym, phiSym, fe_neg, show c * -s = -(c * s) by ring]
  ring

/-- **`λ₁ = 0`.**  The certificate at `−a` gives `λ₁ ≤ 0`, at `b` gives
`λ₁ ≥ 0`. -/
theorem lam1_eq_zero (ha0 : 0 < a) (hb0 : 0 < b)
    (hposA : 0 ≤ DSym l0 l1 l2 c (-a)) (hposB : 0 ≤ DSym l0 l1 l2 c b)
    (hA : DSym l0 l1 l2 c a = 0) (hB : DSym l0 l1 l2 c (-b) = 0) : l1 = 0 := by
  have h1 : (0 : ℝ) ≤ -(2 * (l1 * a)) := by
    rw [DSym_neg, hA] at hposA; linarith
  have h2 : DSym l0 l1 l2 c b = 2 * (l1 * b) := by
    have := DSym_neg l0 l1 l2 c b
    rw [hB] at this; linarith
  have h3 : (0 : ℝ) ≤ 2 * (l1 * b) := by rw [h2] at hposB; exact hposB
  have hle : l1 ≤ 0 := by nlinarith
  have hge : 0 ≤ l1 := by nlinarith
  linarith

/-! ## The zero count -/

/-- `D″` vanishes at two distinct positive points only if `c = 1`. -/
lemma DSym''_eq_zero_unique (hc0 : 0 < c) (hc1 : c < 1) {z w : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1) (hw0 : 0 < w) (hw1 : w < 1)
    (hz : DSym'' l2 c z = 0) (hw : DSym'' l2 c w = 0) : z = w := by
  have hz2 : (0 : ℝ) < 1 - z ^ 2 := by nlinarith
  have hw2 : (0 : ℝ) < 1 - w ^ 2 := by nlinarith
  have hcz0 : (0 : ℝ) < c * z := mul_pos hc0 hz0
  have hcw0 : (0 : ℝ) < c * w := mul_pos hc0 hw0
  have hcz1 : c * z < 1 := by nlinarith
  have hcw1 : c * w < 1 := by nlinarith
  have hcz : (0 : ℝ) < 1 - (c * z) ^ 2 := by nlinarith
  have hcw : (0 : ℝ) < 1 - (c * w) ^ 2 := by nlinarith
  -- clear denominators: `l2 (1 − c²x²) = c² (1 − x²)`
  have key : ∀ x : ℝ, 0 < 1 - x ^ 2 → 0 < 1 - (c * x) ^ 2 → DSym'' l2 c x = 0 →
      l2 * (1 - (c * x) ^ 2) = c ^ 2 * (1 - x ^ 2) := by
    intro x hx1 hx2 hx
    simp only [DSym''] at hx
    have hne : (1 : ℝ) - x ^ 2 * c ^ 2 ≠ 0 := by nlinarith
    have h : l2 * (1 / (1 - x ^ 2)) = c ^ 2 * (1 / (1 - (c * x) ^ 2)) := by linarith
    field_simp at h
    linear_combination h
  have kz := key z hz2 hcz hz
  have kw := key w hw2 hcw hw
  -- subtracting: `(z² − w²)·c²·(l2 − 1) = 0`
  have hdiff : (z ^ 2 - w ^ 2) * (c ^ 2 * (l2 - 1)) = 0 := by nlinarith [kz, kw]
  rcases mul_eq_zero.mp hdiff with h | h
  · have : z ^ 2 = w ^ 2 := by linarith
    nlinarith
  · -- `l2 = 1` forces `c = 1`
    have hl2 : l2 = 1 := by
      have hc2 : (0 : ℝ) < c ^ 2 := by positivity
      have : l2 - 1 = 0 := by
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' (ne_of_gt hc2)
        · exact h'
      linarith
    rw [hl2] at kz
    nlinarith [kz]

/-! ## The theorem -/

/-- `D′` is odd once `λ₁ = 0`. -/
lemma DSym'_neg (hc0 : 0 < c) (hc1 : c < 1) {s : ℝ} (hs0 : -1 < s) (hs1 : s < 1) :
    DSym' 0 l2 c (-s) = -DSym' 0 l2 c s := by
  have hcs0 : -1 < c * s := by nlinarith
  have hcs1 : c * s < 1 := by nlinarith
  simp only [DSym', show c * -s = -(c * s) by ring, artanh_neg_eq hs0 hs1,
    artanh_neg_eq hcs0 hcs1]
  ring

/-- The zero count: two positive contacts of an even certificate are impossible. -/
lemma no_two_positive_contacts (hc0 : 0 < c) (hc1 : c < 1) {x y : ℝ}
    (hx0 : 0 < x) (hxy : x < y) (hy1 : y < 1)
    (hDx : DSym l0 0 l2 c x = 0) (hDy : DSym l0 0 l2 c y = 0)
    (hD'x : DSym' 0 l2 c x = 0) : False := by
  have hzero : DSym' 0 l2 c 0 = 0 := by
    simp only [DSym', mul_zero, artanh_zero]; ring
  -- Rolle between the two contacts
  obtain ⟨ξ, hξmem, hξ⟩ := exists_hasDerivAt_eq_zero (f := DSym l0 0 l2 c)
    (f' := DSym' 0 l2 c) hxy continuous_DSym.continuousOn (by rw [hDx, hDy])
    (fun t ht => hasDerivAt_DSym hc0 hc1 (by linarith [ht.1]) (by linarith [ht.2]))
  -- two more Rolle steps on `D′`, whose zeros are `0 < x < ξ`
  obtain ⟨z₁, hz₁mem, hz₁⟩ := exists_hasDerivAt_eq_zero (f := DSym' 0 l2 c)
    (f' := DSym'' l2 c) hx0
    (fun t ht => ((hasDerivAt_DSym' hc0 hc1 (by linarith [ht.1])
      (by linarith [ht.2, hxy, hy1])).continuousAt).continuousWithinAt)
    (by rw [hzero, hD'x])
    (fun t ht => hasDerivAt_DSym' hc0 hc1 (by linarith [ht.1]) (by linarith [ht.2, hxy, hy1]))
  obtain ⟨z₂, hz₂mem, hz₂⟩ := exists_hasDerivAt_eq_zero (f := DSym' 0 l2 c)
    (f' := DSym'' l2 c) hξmem.1
    (fun t ht => ((hasDerivAt_DSym' hc0 hc1 (by linarith [ht.1, hx0])
      (by linarith [ht.2, hξmem.2, hy1])).continuousAt).continuousWithinAt)
    (by rw [hD'x, hξ])
    (fun t ht => hasDerivAt_DSym' hc0 hc1 (by linarith [ht.1, hx0])
      (by linarith [ht.2, hξmem.2, hy1]))
  have heq := DSym''_eq_zero_unique (l2 := l2) hc0 hc1 hz₁mem.1
    (by linarith [hz₁mem.2, hxy, hy1]) (by linarith [hz₂mem.1, hx0])
    (by linarith [hz₂mem.2, hξmem.2, hy1]) hz₁ hz₂
  linarith [hz₁mem.2, hz₂mem.1]

/-- **Against a symmetric `T`, a bitangent interior response is symmetric.**

The hypotheses are exactly the interior fixed-point data at `p = 0`: the
certificate `D ≥ 0` on the open interval, and contact — value *and* tangency —
at the two atoms `a` and `−b`. -/
theorem interior_response_symmetric (hc0 : 0 < c) (hc1 : c < 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hpos : ∀ s : ℝ, -1 < s → s < 1 → 0 ≤ DSym l0 l1 l2 c s)
    (hA : DSym l0 l1 l2 c a = 0) (hA' : DSym' l1 l2 c a = 0)
    (hB : DSym l0 l1 l2 c (-b) = 0) (hB' : DSym' l1 l2 c (-b) = 0) : a = b := by
  -- Step 1: the certificate at the mirrored points forces `λ₁ = 0`
  have hl1 : l1 = 0 :=
    lam1_eq_zero ha0 hb0 (hpos (-a) (by linarith) (by linarith))
      (hpos b (by linarith) hb1) hA hB
  subst hl1
  -- Step 2: `D` is even, so `b` is a contact as well, and `D′(b) = 0`
  have hBb : DSym l0 0 l2 c b = 0 := by
    have h := DSym_neg l0 0 l2 c b
    rw [hB] at h; linarith
  have hB'b : DSym' 0 l2 c b = 0 := by
    have h := DSym'_neg (l2 := l2) hc0 hc1 (s := b) (by linarith) hb1
    rw [hB'] at h; linarith
  -- Step 3: two distinct positive contacts are impossible
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hab
  · exact no_two_positive_contacts hc0 hc1 ha0 hab hb1 hA hBb hA'
  · exact no_two_positive_contacts hc0 hc1 hb0 hab ha1 hBb hA hB'b

end BSCAveraging
