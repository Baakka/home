import Mathlib

/-!
This snippet is about:

  binMul_needs_n_bits
  RegisterMachine
  ComputesMultiplicationAt
  linear_bit_lower_bound
  no_constant_register_budget

found at line 379 of 380, near the end of this file.

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

/-- The same bound in the honest unit, on the verifying side: a machine whose
state fits in `s` bits cannot verify `n`-digit products unless `s` is at least
`n`. One bit per digit.

This is what makes the exponential above readable rather than impressive.
`2 ^ n` states *is* `n` bits, so the two statements say the same thing, and
quoting the state count alone invites the reader to hear an exponential cost
where the cost is linear. Mine, not Aristotle's: the job asking for it ran out
of budget, and by then it was a two-line corollary of the state bound. -/
theorem binMul_needs_n_bits (n s : ℕ) (M : DFA (Fin 3) (Fin (2 ^ s)))
    (hM : M.accepts = binMul n) : n ≤ s := by
  have h := binMul_needs_exp_states n (Fin (2 ^ s)) inferInstance M hM
  rw [Fintype.card_fin] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h

/-! ## Computing a product, not merely checking one -/

/-- A device that reads an operand into memory and must later emit the product
with 1, which is the operand itself. -/
structure Emitter (S : Type*) where
  mem : ℕ → S
  emit : S → ℕ

/-- Memory must distinguish every operand it might have to reproduce: at least
`2 ^ n` states for `n`-digit operands. Computing needs the operand held, and a
constant memory cannot hold it. -/
theorem emitter_needs_exp_states {S : Type} [Fintype S] (E : Emitter S)
    (n : ℕ) (h : ∀ a < 2 ^ n, E.emit (E.mem a) = a) :
    2 ^ n ≤ Fintype.card S := by
  let f : Fin (2 ^ n) → S := fun a => E.mem a
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have ha := h a.1 a.2
    have hb := h b.1 b.2
    exact ha.symm.trans ((congrArg E.emit hab).trans hb)
  simpa using Fintype.card_le_of_injective f hf

/-! ## The honest unit: bits of register, not count of states -/

/-- The `n` little-endian base-`base` digits of a number. -/
def fixedDigits (base n x : ℕ) [NeZero base] : List (Fin base) :=
  List.ofFn (fun i : Fin n => Fin.ofNat base ((x / base ^ (i : ℕ)) % base))

/-- Decode a little-endian positional digit block. -/
def decodeDigits (base : ℕ) (ds : List (Fin base)) : ℕ :=
  (ds.zipIdx.map fun p => (p.1 : ℕ) * base ^ p.2).sum

/-- A streaming machine with `k` finite-range registers. -/
structure RegisterMachine (base range k : ℕ) where
  init : Fin k → Fin range
  step : (Fin k → Fin range) → Fin base → (Fin k → Fin range)
  output : (Fin k → Fin range) → ℕ

namespace RegisterMachine

/-- Run a register machine over a finite input stream. -/
def run {base range k : ℕ} (M : RegisterMachine base range k) :
    List (Fin base) → (Fin k → Fin range) :=
  List.foldl M.step M.init

/-- The fixed-width input stream for multiplying `x` and `y`. -/
def multiplicationInput (base n x y : ℕ) [NeZero base] : List (Fin base) :=
  fixedDigits base n x ++ fixedDigits base n y

/-- The machine computes `n`-digit multiplication when its final-state output
is the product for every pair in the full fixed-width range `[0, base^n)`.
In particular, this quantifies over the actual transition-based execution; it
is not the mere existence of an unconstrained function on inputs. -/
def ComputesMultiplicationAt {base range k : ℕ} [NeZero base]
    (M : RegisterMachine base range k) (n : ℕ) : Prop :=
  ∀ x y, x < base ^ n → y < base ^ n →
    M.output (M.run (multiplicationInput base n x y)) = x * y

/-- Fixed-width encoding really denotes the original number in its stated
range. -/
theorem decode_fixedDigits {base n x : ℕ} [NeZero base] (hbase : 2 ≤ base)
    (hx : x < base ^ n) :
    decodeDigits base (fixedDigits base n x) = x := by
  induction n generalizing x with
  | zero => simp [decodeDigits, fixedDigits]; simp at hx; omega
  | succ n ih =>
    -- x / base < base^n since x < base^(n+1)
    have hx' : x / base < base ^ n := by
      have h := pow_succ' base n
      rw [h] at hx
      exact Nat.div_lt_of_lt_mul hx
    -- fixedDigits structure: first digit is x % base, rest is fixedDigits base n (x / base)
    have fixedDigits_succ : fixedDigits base (n + 1) x = 
        [⟨x % base, Nat.mod_lt x (by omega : 0 < base)⟩] ++ fixedDigits base n (x / base) := by
      simp [fixedDigits, List.ofFn_succ]
      constructor
      · simp [Fin.ext_iff]
      · funext i
        congr 1
        simp [Nat.div_div_eq_div_mul, pow_succ']
    rw [fixedDigits_succ]
    rw [List.singleton_append]
    -- Need: decodeDigits base (d :: ds) = d + base * decodeDigits base ds
    -- First prove a helper about zipIdx on cons
    have zipIdx_shift : ∀ (ds : List (Fin base)) (k : ℕ),
        ds.zipIdx k = ds.zipIdx.map (fun (v, i) => (v, i + k)) := by
      intro ds k
      induction ds generalizing k with
      | nil => rfl
      | cons hd tl ih =>
        have h1 : List.zipIdx (hd :: tl) k = (hd, k) :: tl.zipIdx (k + 1) := by rfl
        have h2 : List.zipIdx (hd :: tl) = (hd, 0) :: tl.zipIdx 1 := by rfl
        rw [h1, h2, ih (k + 1), ih 1]
        simp [List.map_map]
        intro a b hab
        omega
    have zipIdx_cons : ∀ (d : Fin base) (ds : List (Fin base)),
        (d :: ds).zipIdx = [(d, 0)] ++ (ds.zipIdx.map (fun (v, i) => (v, i + 1))) := by
      intro d ds
      have h : (d :: ds).zipIdx = (d, 0) :: ds.zipIdx 1 := by rfl
      rw [h, zipIdx_shift ds 1]
      rfl
    -- Now prove decodeDigits behavior on cons
    have decodeDigits_cons : ∀ (d : Fin base) (ds : List (Fin base)),
        decodeDigits base (d :: ds) = (d : ℕ) + base * decodeDigits base ds := by
      intro d ds
      simp [decodeDigits, zipIdx_cons]
      -- Goal: (List.map (fun p => p.1 * base^(p.2+1)) ds.zipIdx).sum = base * (List.map (fun p => p.1 * base^p.2) ds.zipIdx).sum
      have h : ∀ p : Fin base × ℕ, (p.1 : ℕ) * base ^ (p.2 + 1) = base * ((p.1 : ℕ) * base ^ p.2) := by
        intro p
        ring
      simp only [Function.comp_def]
      rw [show List.map (fun p => (p.1 : ℕ) * base ^ (p.2 + 1)) ds.zipIdx = 
              List.map (fun p => base * ((p.1 : ℕ) * base ^ p.2)) ds.zipIdx by
            congr 1; ext p; exact h p]
      rw [List.sum_map_mul_left]
    rw [decodeDigits_cons]
    rw [ih hx']
    simp [Nat.mod_add_div]

/-- If a machine computes multiplication at width `n`, fixing the second
operand to one makes final configurations for distinct first operands distinct. -/
theorem finalState_injective {base range k n : ℕ} [NeZero base]
    (M : RegisterMachine base range k) (hbase : 2 ≤ base) (hn : 0 < n)
    (hM : M.ComputesMultiplicationAt n) :
    Function.Injective (fun x : Fin (base ^ n) =>
      M.run (multiplicationInput base n x 1)) := by
  intro x y hxy
  have h1 : (1 : ℕ) < base ^ n := one_lt_pow₀ (by omega) (by omega)
  have hx := hM x 1 x.is_lt h1
  have hy := hM y 1 y.is_lt h1
  simp only [mul_one] at hx hy
  simp only at hxy
  rw [hxy] at hx
  exact Fin.ext (hx.symm.trans hy)

/-- The central configuration-count lower bound: a correct width-`n` machine
needs at least `base^n` different register configurations. -/
theorem state_capacity_lower_bound {base range k n : ℕ} [NeZero base]
    (M : RegisterMachine base range k) (hbase : 2 ≤ base) (hn : 0 < n)
    (hM : M.ComputesMultiplicationAt n) :
    base ^ n ≤ range ^ k := by
  have hinj := finalState_injective M hbase hn hM
  simpa using Fintype.card_le_of_injective _ hinj

/-- Quantitative binary form.  If all register configurations can be encoded
in at most `bits` bits, correctness forces at least `n` bits. -/
theorem linear_bit_lower_bound {base range k n bits : ℕ} [NeZero base]
    (M : RegisterMachine base range k) (hbase : 2 ≤ base) (hn : 0 < n)
    (hM : M.ComputesMultiplicationAt n)
    (hbits : range ^ k ≤ 2 ^ bits) :
    n ≤ bits := by
  have h1 : base ^ n ≤ range ^ k := state_capacity_lower_bound M hbase hn hM
  have h2 : base ^ n ≤ 2 ^ bits := h1.trans hbits
  have h3 : 2 ^ n ≤ base ^ n := Nat.pow_le_pow_left hbase _
  have h4 : 2 ^ n ≤ 2 ^ bits := h3.trans h2
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h4

/-- For every fixed register count and fixed range, some positive digit width
cannot be handled.  Thus no constant register budget computes multiplication
at every width. -/
theorem no_constant_register_budget (base range k : ℕ) (hbase : 2 ≤ base) :
    ∃ n > 0, ∀ M : RegisterMachine base range k,
      letI : NeZero base := ⟨by omega⟩
      ¬ M.ComputesMultiplicationAt n := by
  letI : NeZero base := ⟨by omega⟩
  have hbase1 : 1 < base := hbase
  by_cases hk : k = 0
  · exact ⟨1, by norm_num, fun M hM => by
      have hcap := state_capacity_lower_bound M hbase (by norm_num : 0 < 1) hM
      simp [hk] at hcap
      omega⟩
  · by_cases hr : range = 0
    · exact ⟨1, by norm_num, fun M hM => by
        have hcap := state_capacity_lower_bound M hbase (by norm_num : 0 < 1) hM
        simp [hr, hk] at hcap
        omega⟩
    · have hk0 : k ≠ 0 := hk
      have hpos : 0 < range ^ k := by positivity
      exact ⟨range ^ k, hpos, fun M hM => by
        have hcap := state_capacity_lower_bound M hbase hpos hM
        exact (Nat.lt_pow_self hbase1).not_ge hcap⟩

end RegisterMachine
end HardProblems
