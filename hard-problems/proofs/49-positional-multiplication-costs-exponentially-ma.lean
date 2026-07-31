import Mathlib

/-!
This snippet is about:

  digits
  binMul
  digits_injOn
  binMul_needs_exp_states

found at line 176 of 179, near the end of this file.

Everything above it is the companion's own dependencies, inlined so that
this file needs nothing but mathlib. -/

/-! Target module: LeanTest/HardProblems/Positional.lean -/

/-
Positional encoding: what a calculator actually costs.

Chapter 12 claims that a bounded machine cannot multiply, and the companion's
first pass proved it over a *unary* language (`mulLang` in `BoundedMachines`).
That is a real theorem about a false subject: nobody writes numbers in unary,
and the claim as stated is about digits. Three gaps separated the prose from
what had been checked, and this module closes each one.

* Encoding. `binMul_needs_exp_states` redoes the lower bound over fixed-width
  positional notation, the encoding the sentence is actually about. Verifying
  `n`-digit multiplication takes at least `2 ^ n` states.

* Verifying versus computing. The bound above is about *recognising* a correct
  product. `emitter_needs_exp_states` covers the other half: a device that must
  reproduce an operand needs enough memory to have held it.

* States versus bits, which was a rate error rather than a gap. A machine with
  `k` states holds only `log k` bits, so an exponential state bound is a
  *linear* memory bound, and quoting the exponential as if it were the memory
  cost overstates the case. `linear_bit_lower_bound` states it in the honest
  unit: `n` digits of input force `n` bits of register, no more.

`no_constant_register_budget` is the conclusion the chapter wants. For any
fixed register count and range, some width defeats the machine. The transition
and output maps here are arbitrary functions, not required to be computable,
which strengthens the impossibility rather than weakening it: even machines
that cheat at every step cannot escape the counting.

Formalized by Harmonic's Aristotle against Lean v4.28 and checked here against
this project's toolchain. The statements are its choices, not translations of
mine; where it declined to state something, `Positional` says so rather than
substituting a weaker claim that sounds the same. In particular, no
constant-work-space-implies-regular theorem appears: mathlib's `TM2` keeps its
input on an ordinary counted stack, so under an honest total-space convention
every long input already exceeds any constant, and the premise is unsatisfiable.
A theorem with an impossible hypothesis proves nothing about calculators.
-/

namespace HardProblems

/-! ## Verifying a product, in positional notation -/

/-- The `n`-bit positional encoding of `a`, least significant digit first,
written in the letters 0 and 1 of a three-letter alphabet whose third letter
`2` is a separator. This is what "n-digit" means in the book's sentence:
fixed width, positional, not unary. -/
def digits (n a : ℕ) : List (Fin 3) :=
  (List.range n).map (fun i => if a / 2 ^ i % 2 = 1 then (1 : Fin 3) else 0)

/-- Verifying an `n`-digit multiplication: the two operands and their product,
each in fixed-width positional notation, separated by `2`. -/
def binMul (n : ℕ) : Language (Fin 3) :=
  {w | ∃ a b : ℕ, a < 2 ^ n ∧ b < 2 ^ n ∧
    w = digits n a ++ [2] ++ digits n b ++ [2] ++ digits (2 * n) (a * b)}

/-- Two words are distinguishable for `L` when some suffix tells them apart. -/
def Distinguishable {α : Type} (L : Language α) (u v : List α) : Prop :=
  ∃ z : List α, (u ++ z ∈ L) ≠ (v ++ z ∈ L)

/-- Fixed-width positional encoding is injective below the width's capacity,
which is what makes distinct operands distinguishable prefixes. -/
theorem digits_injOn (n : ℕ) :
    ∀ a < 2 ^ n, ∀ b < 2 ^ n, digits n a = digits n b → a = b := by
  intro a ha b hb h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have he := congrArg (fun l : List (Fin 3) => l[i]?) h
    simp [digits, hi] at he
    have hab : (a / 2 ^ i % 2 = 1) ↔ (b / 2 ^ i % 2 = 1) := by
      by_cases hx : a / 2 ^ i % 2 = 1 <;> by_cases hy : b / 2 ^ i % 2 = 1 <;>
        simp_all
    simpa [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two] using hab
  · have hni : n ≤ i := Nat.le_of_not_gt hi
    rw [Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hni)),
      Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hni))]

private lemma digits_length (n a : ℕ) : (digits n a).length = n := by
  simp [digits]

private lemma binMul_probe_mem {n a : ℕ} (hn : 0 < n) (ha : a < 2 ^ n) :
    digits n a ++ [2] ++ digits n 1 ++ [2] ++ digits (2 * n) a ∈ binMul n := by
  refine ⟨a, 1, ha, ?_, ?_⟩
  · exact Nat.one_lt_two_pow_iff.mpr (Nat.pos_iff_ne_zero.mp hn)
  · simp [mul_one]

private lemma binMul_probe_only {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hmem : digits n b ++ [2] ++ digits n 1 ++ [2] ++ digits (2 * n) a ∈ binMul n) :
    b = a := by
  by_cases hn : n = 0
  · subst n
    simp_all
  rcases hmem with ⟨x, y, hx, hy, hword⟩
  have hword' : digits n b ++ ([2] ++ digits n 1 ++ [2] ++ digits (2 * n) a) =
      digits n x ++ ([2] ++ digits n y ++ [2] ++ digits (2 * n) (x * y)) := by
    simpa only [List.append_assoc] using hword
  have hfirst : digits n b = digits n x :=
    List.append_inj_left hword' (by simp [digits_length])
  have hrest := List.append_inj_right hword' (by simp [digits_length])
  have hrest' : [2] ++ (digits n 1 ++ [2] ++ digits (2 * n) a) =
      [2] ++ (digits n y ++ [2] ++ digits (2 * n) (x * y)) := by
    simpa only [List.append_assoc] using hrest
  have hafter := List.append_cancel_left hrest'
  have hafter' : digits n 1 ++ ([2] ++ digits (2 * n) a) =
      digits n y ++ ([2] ++ digits (2 * n) (x * y)) := by
    simpa only [List.append_assoc] using hafter
  have hsecond : digits n 1 = digits n y :=
    List.append_inj_left hafter' (by simp [digits_length])
  have htail := List.append_inj_right hafter' (by simp [digits_length])
  have hprod : digits (2 * n) a = digits (2 * n) (x * y) := by
    exact List.append_cancel_left htail
  have hbx : b = x := digits_injOn n b hb x hx hfirst
  have hone : 1 = y := digits_injOn n 1
    (Nat.one_lt_two_pow_iff.mpr hn) y hy hsecond
  subst x
  subst y
  simp only [mul_one] at hprod
  apply digits_injOn (2 * n) b
  · exact lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega))
  · exact lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))
  · exact hprod.symm

private lemma dfa_same_state_suffix {σ : Type} (M : DFA (Fin 3) σ)
    {u v z : List (Fin 3)} (hstate : M.eval u = M.eval v) :
    (u ++ z ∈ M.accepts) ↔ (v ++ z ∈ M.accepts) := by
  simp only [DFA.mem_accepts]
  change M.evalFrom M.start (u ++ z) ∈ M.accept ↔ M.evalFrom M.start (v ++ z) ∈ M.accept
  rw [M.evalFrom_of_append, M.evalFrom_of_append]
  have hs : M.evalFrom M.start u = M.evalFrom M.start v := by
    simpa [DFA.eval] using hstate
  rw [hs]

/-- Any finite-state machine verifying `n`-digit multiplication has at least
`2 ^ n` states. This is the claim chapter 12 makes, over the encoding the
claim is about: memory grows with the digit count, not merely without bound. -/
theorem binMul_needs_exp_states (n : ℕ) :
    ∀ (σ : Type) (_ : Fintype σ) (M : DFA (Fin 3) σ),
      M.accepts = binMul n → 2 ^ n ≤ Fintype.card σ := by
  intro σ inst M hM
  by_cases hn : n = 0
  · subst n
    simp only [pow_zero, Nat.one_le_iff_ne_zero]
    exact Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨M.start⟩)
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [← Fintype.card_fin (2 ^ n)]
    apply Fintype.card_le_of_injective (fun a : Fin (2 ^ n) => M.eval (digits n a))
    intro a b hab
    apply Fin.ext
    let z : List (Fin 3) := [2] ++ digits n 1 ++ [2] ++ digits (2 * n) a
    have ha_mem : digits n a ++ z ∈ binMul n := by
      simpa only [z, List.append_assoc] using
        (binMul_probe_mem (n := n) (a := (a : ℕ)) hnpos a.isLt)
    have hsuffix := dfa_same_state_suffix M (z := z) hab
    rw [hM] at hsuffix
    have hb_mem : digits n b ++ z ∈ binMul n := hsuffix.mp ha_mem
    exact (binMul_probe_only (a := (a : ℕ)) (b := (b : ℕ)) a.isLt b.isLt
      (by simpa only [z, List.append_assoc] using hb_mem)).symm

end HardProblems
