/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.CFG
public import ProofLib.BV.ReflectROBDD

/-!
# Static `musl` AArch64 `strlen`

Symbolic execution and `subroutine_ok` contracts (`stdStrlenROSpec`, `stdStrlenSpec`) for the
22-instruction SWAR `strlen` routine over `P.hasCode addr muslStrlenWords`.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib.StdStartup

open Arm64 ProofLib

/-- Exact 22 32-bit instruction words (`88` bytes) of static `musl` 1.2.5 AArch64 `strlen`. -/
def muslStrlenWords : List (BitVec 32) := [
  0xaa0003e1#32, 0xf240083f#32, -- +0x00: mov x1, x0;       +0x04: tst x1, #0x7
  0x540000a0#32, 0x39400022#32, -- +0x08: b.eq +0x1c;       +0x0c: ldrb w2, [x1]
  0x34000202#32, 0x91000421#32, -- +0x10: cbz w2, +0x50;    +0x14: add x1, x1, #0x1
  0x17fffffb#32, 0xb207dbe4#32, -- +0x18: b +0x04;          +0x1c: mov x4, #-0x101010101010102
  0xf29fdfe4#32, 0xf9400022#32, -- +0x20: movk x4, #0xfeff; +0x24: ldr x2, [x1]
  0x8b040043#32, 0x8a220062#32, -- +0x28: add x3, x2, x4;   +0x2c: bic x2, x3, x2
  0xf201c05f#32, 0x54000061#32, -- +0x30: tst x2, #0x80..;  +0x34: b.ne +0x40
  0x91002021#32, 0x17fffffa#32, -- +0x38: add x1, x1, #0x8; +0x3c: b +0x24
  0x39400022#32, 0x34000062#32, -- +0x40: ldrb w2, [x1];    +0x44: cbz w2, +0x50
  0x91000421#32, 0x17fffffd#32, -- +0x48: add x1, x1, #0x1; +0x4c: b +0x40
  0xcb000020#32, 0xd65f03c0#32  -- +0x50: sub x0, x1, x0;   +0x54: ret
]

/-! ## Process-level state preservation -/

/-- Process-level and oracle state fields preserved identically across `strlen`. -/
def StrlenStatePreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧
  sf.sigActions = s0.sigActions ∧ sf.brk = s0.brk ∧ sf.brkStart = s0.brkStart ∧
  (∀ a, sf.mem.perm a = s0.mem.perm a) ∧ sf.oracle = s0.oracle ∧ sf.oracleIdx = s0.oracleIdx

private def StrlenCorePreserved (s0 sf : State) : Prop :=
  sf.mem = s0.mem ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧
  sf.sigActions = s0.sigActions ∧ sf.brk = s0.brk ∧ sf.brkStart = s0.brkStart ∧
  sf.oracle = s0.oracle ∧ sf.oracleIdx = s0.oracleIdx

private theorem StrlenCorePreserved.rfl (s : State) : StrlenCorePreserved s s :=
  ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩

private theorem StrlenCorePreserved.to_statePreserved {s0 sf : State}
    (h : StrlenCorePreserved s0 sf) : StrlenStatePreserved s0 sf :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   fun a => by rw [h.1], h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

@[local simp] private theorem StrlenCorePreserved_writeReg64 (s0 s : State) (r : Reg) (v : BitVec 64) :
    StrlenCorePreserved s0 (s.writeReg64 r v) ↔ StrlenCorePreserved s0 s := by
  cases r <;> simp [State.writeReg64, StrlenCorePreserved]

@[local simp] private theorem StrlenCorePreserved_writeReg32 (s0 s : State) (r : Reg) (v : BitVec 32) :
    StrlenCorePreserved s0 (s.writeReg32 r v) ↔ StrlenCorePreserved s0 s := by simp [State.writeReg32]

@[local simp] private theorem StrlenCorePreserved_setPState (s0 s : State) (p : PState) :
    StrlenCorePreserved s0 (s.setPState p) ↔ StrlenCorePreserved s0 s := Iff.rfl

@[local simp] private theorem StrlenCorePreserved_advancePC (s0 s : State) :
    StrlenCorePreserved s0 s.advancePC ↔ StrlenCorePreserved s0 s := Iff.rfl

@[local simp] private theorem StrlenCorePreserved_setPC (s0 s : State) (pc : BitVec 64) :
    StrlenCorePreserved s0 (s.setPC pc) ↔ StrlenCorePreserved s0 s := Iff.rfl

/-- Complete exit facts of `strlen` relative to entry state `s0`. -/
abbrev StrlenExit (s0 : State) (len : Nat) (sf : State) : Prop :=
  sf.readReg64 .x0 = BitVec.ofNat 64 len ∧ sf.sp = s0.sp ∧
  CalleeSavedPreserved s0 sf ∧ sf.mem = s0.mem ∧ StrlenStatePreserved s0 sf

/-! ## Read-only focus and 8-byte SWAR zero-byte equivalence -/

def strlenByte (bs pad : List (BitVec 8)) (idx : Nat) : BitVec 8 :=
  (bs ++ [0#8] ++ pad).getD idx 0#8

def strlenWord (bs pad : List (BitVec 8)) (k : Nat) : BitVec 64 :=
  pack64 (strlenByte bs pad k) (strlenByte bs pad (k + 1))
         (strlenByte bs pad (k + 2)) (strlenByte bs pad (k + 3))
         (strlenByte bs pad (k + 4)) (strlenByte bs pad (k + 5))
         (strlenByte bs pad (k + 6)) (strlenByte bs pad (k + 7))

private theorem strlen_focus8 (base : BitVec 64) (bs pad : List (BitVec 8)) (off : Nat)
    (h : off < (bs ++ [0#8] ++ pad).length) :
    (base ↦ᵣ (bs ++ [0#8] ++ pad)) =
      ((base + BitVec.ofNat 64 off) ↦₈ᵣ strlenByte bs pad off) ∗
      ((base ↦ᵣ (bs ++ [0#8] ++ pad).take off) ∗
        ((base + BitVec.ofNat 64 (off + 1)) ↦ᵣ (bs ++ [0#8] ++ pad).drop (off + 1))) := by
  have hsplit := pointsToBytesRO_split3 base (bs ++ [0#8] ++ pad) off 1 (by omega)
  rw [pointsToBytesRO_take1_eq_pointsTo8RO _ (bs ++ [0#8] ++ pad) off (by omega)] at hsplit
  exact hsplit

private theorem strlen_focus64 (base : BitVec 64) (bs pad : List (BitVec 8)) (off : Nat)
    (h : off + 8 ≤ (bs ++ [0#8] ++ pad).length) :
    (base ↦ᵣ (bs ++ [0#8] ++ pad)) =
      ((base + BitVec.ofNat 64 off) ↦₆₄ᵣ strlenWord bs pad off) ∗
      ((base ↦ᵣ (bs ++ [0#8] ++ pad).take off) ∗
        ((base + BitVec.ofNat 64 (off + 8)) ↦ᵣ (bs ++ [0#8] ++ pad).drop (off + 8))) := by
  have hsplit := pointsToBytesRO_split3 base (bs ++ [0#8] ++ pad) off 8 h
  rw [pointsToBytesRO_take8_eq_pointsTo64RO _ (bs ++ [0#8] ++ pad) off h] at hsplit
  exact hsplit

private theorem full_getD_at_len (bs pad : List (BitVec 8)) :
    strlenByte bs pad bs.length = 0#8 := by
  simp [strlenByte, List.getD]

private theorem full_getD_ne_zero_of_lt {bs : List (BitVec 8)} (pad : List (BitVec 8))
    (h0 : 0#8 ∉ bs) {i : Nat} (hi : i < bs.length) : strlenByte bs pad i ≠ 0#8 := by
  unfold strlenByte
  have h1 : i < (bs ++ [0#8]).length := by simp; omega
  simp only [List.getD, List.getElem?_append_left h1, List.getElem?_append_left hi,
    List.getElem?_eq_getElem hi, Option.getD_some]
  exact fun heq => h0 (heq ▸ List.getElem_mem hi)

private theorem le_len_succ_of_full_getD_ne_zero {bs pad : List (BitVec 8)} {k : Nat}
    (hle : k ≤ bs.length) (hnz : strlenByte bs pad k ≠ 0#8) : k + 1 ≤ bs.length := by
  rcases Nat.lt_or_eq_of_le hle with hlt | rfl
  · omega
  · exact False.elim (hnz (full_getD_at_len bs pad))

private theorem extractLsb'_swar_bic_tst_zero {x3 w : BitVec 64} (d : Nat)
    (h : (x3 &&& ~~~w) &&& 0x8080808080808080#64 = 0#64)
    (hd : d = 0 ∨ d = 8 ∨ d = 16 ∨ d = 24 ∨ d = 32 ∨ d = 40 ∨ d = 48 ∨ d = 56)
    (hz : w.extractLsb' d 8 = 0#8) :
    x3.extractLsb' d 8 &&& 0x80#8 = 0#8 := by
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> bv_slice

/-- Per-lane SWAR zero-byte exclusion for `(w + 0xfefefefefefefeff#64) &&& ~~~w &&& 0x8080...80`. -/
theorem musl_swar_no_zero_byte_at (w : BitVec 64) (d : Nat)
    (h : (w + 0xfefefefefefefeff#64) &&& ~~~w &&& 0x8080808080808080#64 = 0#64)
    (hd : d = 0 ∨ d = 8 ∨ d = 16 ∨ d = 24 ∨ d = 32 ∨ d = 40 ∨ d = 48 ∨ d = 56) :
    w.extractLsb' d 8 ≠ 0#8 := by
  intro hz
  have hbyte := extractLsb'_swar_bic_tst_zero d h hd hz
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> bv_bits

/-- Exact 8-byte SWAR zero-byte exclusion for packed 64-bit words:
    if `(w + 0xfefefefefefefeff#64) &&& ~~~w &&& 0x8080808080808080#64 = 0#64`, then all 8 bytes
    of `w = pack64 b0 b1 b2 b3 b4 b5 b6 b7` are nonzero. -/
theorem musl_swar_pack64_no_zero {b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8}
    (h : (pack64 b0 b1 b2 b3 b4 b5 b6 b7 + 0xfefefefefefefeff#64) &&&
          ~~~pack64 b0 b1 b2 b3 b4 b5 b6 b7 &&& 0x8080808080808080#64 = 0#64) :
    b0 ≠ 0#8 ∧ b1 ≠ 0#8 ∧ b2 ≠ 0#8 ∧ b3 ≠ 0#8 ∧
    b4 ≠ 0#8 ∧ b5 ≠ 0#8 ∧ b6 ≠ 0#8 ∧ b7 ≠ 0#8 := by
  have hu : unpack64 (pack64 b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] :=
    unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7
  simp only [unpack64, List.cons.injEq, and_true] at hu
  rcases hu with ⟨he0, he1, he2, he3, he4, he5, he6, he7⟩
  exact ⟨he0 ▸ musl_swar_no_zero_byte_at _ 0 h (by omega),
         he1 ▸ musl_swar_no_zero_byte_at _ 8 h (by omega),
         he2 ▸ musl_swar_no_zero_byte_at _ 16 h (by omega),
         he3 ▸ musl_swar_no_zero_byte_at _ 24 h (by omega),
         he4 ▸ musl_swar_no_zero_byte_at _ 32 h (by omega),
         he5 ▸ musl_swar_no_zero_byte_at _ 40 h (by omega),
         he6 ▸ musl_swar_no_zero_byte_at _ 48 h (by omega),
         he7 ▸ musl_swar_no_zero_byte_at _ 56 h (by omega)⟩

private theorem musl_swar_step8_le_len {bs pad : List (BitVec 8)} {k : Nat} (hk : k ≤ bs.length)
    (h : (strlenWord bs pad k + 0xfefefefefefefeff#64) &&&
          ~~~strlenWord bs pad k &&& 0x8080808080808080#64 = 0#64) :
    k + 8 ≤ bs.length := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := musl_swar_pack64_no_zero h
  have hk2 := le_len_succ_of_full_getD_ne_zero (le_len_succ_of_full_getD_ne_zero hk h0) h1
  have hk4 := le_len_succ_of_full_getD_ne_zero (le_len_succ_of_full_getD_ne_zero hk2 h2) h3
  have hk6 := le_len_succ_of_full_getD_ne_zero (le_len_succ_of_full_getD_ne_zero hk4 h4) h5
  exact le_len_succ_of_full_getD_ne_zero (le_len_succ_of_full_getD_ne_zero hk6 h6) h7

private theorem aligned_word_in_bounds {s_nat : Nat} {bs pad : List (BitVec 8)} {k : Nat}
    (halign : (s_nat + k) % 8 = 0) (hk : k ≤ bs.length)
    (hpad : 8 ≤ (s_nat + bs.length) % 8 + 1 + pad.length) :
    k + 8 ≤ (bs ++ [0#8] ++ pad).length := by
  simp only [List.length_append, List.length_singleton]; omega

private theorem mod8_eq_zero_of_and7_zero {s : BitVec 64} {k : Nat}
    (hno_wrap : s.toNat + k < 2 ^ 64)
    (hand : (s + BitVec.ofNat 64 k) &&& 7#64 = 0#64) : (s.toNat + k) % 8 = 0 := by
  have h1 : ((s + BitVec.ofNat 64 k) &&& 7#64).toNat = 0 := by rw [hand]; rfl
  rw [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
  change (s.toNat + k) &&& 7 = 0 at h1
  rwa [Nat.and_two_pow_sub_one_eq_mod _ 3] at h1

private theorem zext32_64_eq_zero_iff (a : BitVec 8) : BitVec.zeroExtend 64 a = 0#64 ↔ a = 0#8 :=
  ⟨fun h => by revert a h; bv_bits, fun h => by subst h; bv_bits⟩

private theorem add_ofNat64_step (base : BitVec 64) (k d : Nat) :
    base + BitVec.ofNat 64 k + BitVec.ofNat 64 d = base + BitVec.ofNat 64 (k + d) := by
  rw [BitVec.add_assoc]; congr 1; rw [← BitVec.ofNat_add]

private theorem add_ofNat64_one (base : BitVec 64) (k : Nat) :
    base + BitVec.ofNat 64 k + 1#64 = base + BitVec.ofNat 64 (k + 1) := add_ofNat64_step base k 1

private theorem add_ofNat64_eight (base : BitVec 64) (k : Nat) :
    base + BitVec.ofNat 64 k + 8#64 = base + BitVec.ofNat 64 (k + 8) := add_ofNat64_step base k 8

private theorem add_ofNat64_sub_self (s : BitVec 64) (n : Nat) :
    s + BitVec.ofNat 64 n - s = BitVec.ofNat 64 n := by bv_lin

/-! ## Symbolic execution over `P.hasCode addr muslStrlenWords` -/

section
arm64_proof_prelude

private theorem muslStrlen_exit_0x50 (P : Program) (addr : BitVec 64)
    (hc : P.hasCode addr muslStrlenWords) (s0 : State) (s : BitVec 64) (bs pad : List (BitVec 8))
    (st : State) (hpc_s : st.pc = addr + 0x50#64) (hrun_s : st.status = .Running)
    (hx0_s : st.readReg64 (Reg.gpr 0#5) = s)
    (hx1_s : st.readReg64 (Reg.gpr 1#5) = s + BitVec.ofNat 64 bs.length)
    (hlr_s : st.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5))
    (hsp_s : st.sp = s0.sp) (hcs_s : CalleeSavedPreserved s0 st) (hpr_s : StrlenCorePreserved s0 st) :
    SepWP P (s0.readReg64 .lr) st (s ↦ᵣ (bs ++ [0#8] ++ pad))
      (sepPost (StrlenExit s0 bs.length) (s ↦ᵣ (bs ++ [0#8] ++ pad))) := by
  wp_steps 2
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_s])
  exact ⟨⟨by simp [wp_norm, arm64_norm, add_ofNat64_sub_self], by simp [wp_norm, arm64_norm, hsp_s],
          CalleeSavedPreserved.trans hcs_s (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]),
          by simp [wp_norm, arm64_norm, hpr_s.1],
          StrlenCorePreserved.to_statePreserved (by simp [hpr_s])⟩, Entails.refl _⟩

private theorem muslStrlen_tail_loop (P : Program) (addr : BitVec 64)
    (hc : P.hasCode addr muslStrlenWords) (s0 : State) (s : BitVec 64) (bs pad : List (BitVec 8))
    (hno_zero : 0#8 ∉ bs) : ∀ (rem idx : Nat) (st : State),
      idx + rem = bs.length → st.pc = addr + 0x40#64 → st.status = .Running →
      st.readReg64 (Reg.gpr 0#5) = s → st.readReg64 (Reg.gpr 1#5) = s + BitVec.ofNat 64 idx →
      st.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) →
      st.sp = s0.sp → CalleeSavedPreserved s0 st → StrlenCorePreserved s0 st →
      SepWP P (s0.readReg64 .lr) st (s ↦ᵣ (bs ++ [0#8] ++ pad))
        (sepPost (StrlenExit s0 bs.length) (s ↦ᵣ (bs ++ [0#8] ++ pad))) := by
  intro rem; induction rem with
  | zero =>
    intro idx st hrem hpc_s hrun_s hx0_s hx1_s hlr_s hsp_s hcs_s hpr_s
    rcases (by omega : idx = bs.length) with rfl
    have hlt : bs.length < (bs ++ [0#8] ++ pad).length := by simp
    rw [strlen_focus8 s bs pad bs.length hlt]; wp_steps 2; rw [← strlen_focus8 s bs pad bs.length hlt]
    wp_if hcbz
    · exact muslStrlen_exit_0x50 P addr hc s0 s bs pad _
        (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_s])
        (by simp [wp_norm, arm64_norm, hx0_s]) (by simp [wp_norm, arm64_norm, hx1_s])
        (by simp [wp_norm, arm64_norm, hlr_s]) (by simp [wp_norm, arm64_norm, hsp_s])
        (CalleeSavedPreserved.trans hcs_s (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]))
        (by simp [hpr_s])
    · simp only [zext32_64_eq_zero_iff] at hcbz; exact False.elim (hcbz (full_getD_at_len bs pad))
  | succ rem' ih =>
    intro idx st hrem hpc_s hrun_s hx0_s hx1_s hlr_s hsp_s hcs_s hpr_s
    have hidx_lt : idx < bs.length := by omega
    have hlt : idx < (bs ++ [0#8] ++ pad).length := by simp; omega
    rw [strlen_focus8 s bs pad idx hlt]; wp_steps 2; rw [← strlen_focus8 s bs pad idx hlt]
    wp_if hcbz
    · simp only [zext32_64_eq_zero_iff] at hcbz
      exact False.elim (full_getD_ne_zero_of_lt pad hno_zero hidx_lt hcbz)
    · wp_steps 2
      exact ih (idx + 1) _ (by omega) (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (by simp [wp_norm, arm64_norm, hrun_s]) (by simp [wp_norm, arm64_norm, hx0_s])
        (by simp [wp_norm, arm64_norm, add_ofNat64_one]) (by simp [wp_norm, arm64_norm, hlr_s])
        (by simp [wp_norm, arm64_norm, hsp_s])
        (CalleeSavedPreserved.trans hcs_s (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]))
        (by simp [hpr_s])

private theorem muslStrlen_swar_loop (P : Program) (addr : BitVec 64)
    (hc : P.hasCode addr muslStrlenWords) (s0 : State) (s : BitVec 64) (bs pad : List (BitVec 8))
    (hno_zero : 0#8 ∉ bs) (hpad : 8 ≤ (s.toNat + bs.length) % 8 + 1 + pad.length) :
    ∀ (fuel k : Nat) (st : State),
      bs.length - k ≤ fuel → k ≤ bs.length → (s.toNat + k) % 8 = 0 →
      st.pc = addr + 0x24#64 → st.status = .Running → st.readReg64 (Reg.gpr 0#5) = s →
      st.readReg64 (Reg.gpr 1#5) = s + BitVec.ofNat 64 k →
      st.readReg64 (Reg.gpr 4#5) = 0xfefefefefefefeff#64 →
      st.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) →
      st.sp = s0.sp → CalleeSavedPreserved s0 st → StrlenCorePreserved s0 st →
      SepWP P (s0.readReg64 .lr) st (s ↦ᵣ (bs ++ [0#8] ++ pad))
        (sepPost (StrlenExit s0 bs.length) (s ↦ᵣ (bs ++ [0#8] ++ pad))) := by
  intro fuel; induction fuel with
  | zero =>
    intro k st hfuel hk_le halign hpc_s hrun_s hx0_s hx1_s hx4_s hlr_s hsp_s hcs_s hpr_s
    have hbounds := aligned_word_in_bounds halign hk_le hpad
    rw [strlen_focus64 s bs pad k hbounds]; wp_steps 5; rw [← strlen_focus64 s bs pad k hbounds]
    wp_if hswar
    · exact muslStrlen_tail_loop P addr hc s0 s bs pad hno_zero (bs.length - k) k _ (by omega)
        (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_s])
        (by simp [wp_norm, arm64_norm, hx0_s]) (by simp [wp_norm, arm64_norm, hx1_s])
        (by simp [wp_norm, arm64_norm, hlr_s]) (by simp [wp_norm, arm64_norm, hsp_s])
        (CalleeSavedPreserved.trans hcs_s (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]))
        (by simp [hpr_s])
    · have hk8 := musl_swar_step8_le_len hk_le hswar; omega
  | succ fuel' ih =>
    intro k st hfuel hk_le halign hpc_s hrun_s hx0_s hx1_s hx4_s hlr_s hsp_s hcs_s hpr_s
    have hbounds := aligned_word_in_bounds halign hk_le hpad
    rw [strlen_focus64 s bs pad k hbounds]; wp_steps 5; rw [← strlen_focus64 s bs pad k hbounds]
    wp_if hswar
    · exact muslStrlen_tail_loop P addr hc s0 s bs pad hno_zero (bs.length - k) k _ (by omega)
        (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_s])
        (by simp [wp_norm, arm64_norm, hx0_s]) (by simp [wp_norm, arm64_norm, hx1_s])
        (by simp [wp_norm, arm64_norm, hlr_s]) (by simp [wp_norm, arm64_norm, hsp_s])
        (CalleeSavedPreserved.trans hcs_s (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]))
        (by simp [hpr_s])
    · have hk8 := musl_swar_step8_le_len hk_le hswar
      wp_steps 2
      exact ih (k + 8) _ (by omega) hk8 (by omega)
        (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_s])
        (by simp [wp_norm, arm64_norm, hx0_s]) (by simp [wp_norm, arm64_norm, add_ofNat64_eight])
        (by simp [wp_norm, arm64_norm, hx4_s]) (by simp [wp_norm, arm64_norm, hlr_s])
        (by simp [wp_norm, arm64_norm, hsp_s])
        (CalleeSavedPreserved.trans hcs_s (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]))
        (by simp [hpr_s])

private theorem muslStrlen_setup_0x1c (P : Program) (addr : BitVec 64)
    (hc : P.hasCode addr muslStrlenWords) (s0 : State) (s : BitVec 64) (bs pad : List (BitVec 8))
    (hno_zero : 0#8 ∉ bs) (hpad : 8 ≤ (s.toNat + bs.length) % 8 + 1 + pad.length)
    (k : Nat) (st : State) (hk_le : k ≤ bs.length) (halign : (s.toNat + k) % 8 = 0)
    (hpc_s : st.pc = addr + 0x1c#64) (hrun_s : st.status = .Running)
    (hx0_s : st.readReg64 (Reg.gpr 0#5) = s)
    (hx1_s : st.readReg64 (Reg.gpr 1#5) = s + BitVec.ofNat 64 k)
    (hlr_s : st.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5))
    (hsp_s : st.sp = s0.sp) (hcs_s : CalleeSavedPreserved s0 st)
    (hpr_s : StrlenCorePreserved s0 st) :
    SepWP P (s0.readReg64 .lr) st (s ↦ᵣ (bs ++ [0#8] ++ pad))
      (sepPost (StrlenExit s0 bs.length) (s ↦ᵣ (bs ++ [0#8] ++ pad))) := by
  wp_steps 2
  exact muslStrlen_swar_loop P addr hc s0 s bs pad hno_zero hpad (bs.length - k) k _
    (by omega) hk_le halign
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_s])
    (by simp [wp_norm, arm64_norm, hx0_s]) (by simp [wp_norm, arm64_norm, hx1_s])
    (by simp (config := { decide := true }) [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hlr_s]) (by simp [wp_norm, arm64_norm, hsp_s])
    (CalleeSavedPreserved.trans hcs_s (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]))
    (by simp [hpr_s])

private theorem muslStrlen_align_loop (P : Program) (addr : BitVec 64)
    (hc : P.hasCode addr muslStrlenWords) (s0 : State) (s : BitVec 64) (bs pad : List (BitVec 8))
    (hno_zero : 0#8 ∉ bs) (hpad : 8 ≤ (s.toNat + bs.length) % 8 + 1 + pad.length)
    (hno_wrap : s.toNat + (bs.length + 1 + pad.length) < 2 ^ 64) :
    ∀ (rem idx : Nat) (st : State),
      idx + rem = bs.length → st.pc = addr + 0x04#64 → st.status = .Running →
      st.readReg64 (Reg.gpr 0#5) = s → st.readReg64 (Reg.gpr 1#5) = s + BitVec.ofNat 64 idx →
      st.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) →
      st.sp = s0.sp → CalleeSavedPreserved s0 st → StrlenCorePreserved s0 st →
      SepWP P (s0.readReg64 .lr) st (s ↦ᵣ (bs ++ [0#8] ++ pad))
        (sepPost (StrlenExit s0 bs.length) (s ↦ᵣ (bs ++ [0#8] ++ pad))) := by
  intro rem; induction rem with
  | zero =>
    intro idx st hrem hpc_s hrun_s hx0_s hx1_s hlr_s hsp_s hcs_s hpr_s
    rcases (by omega : idx = bs.length) with rfl
    wp_steps 2
    wp_if halign
    · exact muslStrlen_setup_0x1c P addr hc s0 s bs pad hno_zero hpad bs.length _
        (by omega) (mod8_eq_zero_of_and7_zero (by omega) halign)
        (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_s])
        (by simp [wp_norm, arm64_norm, hx0_s]) (by simp [wp_norm, arm64_norm, hx1_s])
        (by simp [wp_norm, arm64_norm, hlr_s]) (by simp [wp_norm, arm64_norm, hsp_s])
        (CalleeSavedPreserved.trans hcs_s (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]))
        (by simp [hpr_s])
    · have hlt : bs.length < (bs ++ [0#8] ++ pad).length := by simp
      rw [strlen_focus8 s bs pad bs.length hlt]; wp_steps 2; rw [← strlen_focus8 s bs pad bs.length hlt]
      wp_if hcbz
      · exact muslStrlen_exit_0x50 P addr hc s0 s bs pad _
          (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_s])
          (by simp [wp_norm, arm64_norm, hx0_s]) (by simp [wp_norm, arm64_norm, hx1_s])
          (by simp [wp_norm, arm64_norm, hlr_s]) (by simp [wp_norm, arm64_norm, hsp_s])
          (CalleeSavedPreserved.trans hcs_s (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]))
          (by simp [hpr_s])
      · simp only [zext32_64_eq_zero_iff] at hcbz; exact False.elim (hcbz (full_getD_at_len bs pad))
  | succ rem' ih =>
    intro idx st hrem hpc_s hrun_s hx0_s hx1_s hlr_s hsp_s hcs_s hpr_s
    have hidx_lt : idx < bs.length := by omega
    wp_steps 2
    wp_if halign
    · exact muslStrlen_setup_0x1c P addr hc s0 s bs pad hno_zero hpad idx _
        (by omega) (mod8_eq_zero_of_and7_zero (by omega) halign)
        (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_s])
        (by simp [wp_norm, arm64_norm, hx0_s]) (by simp [wp_norm, arm64_norm, hx1_s])
        (by simp [wp_norm, arm64_norm, hlr_s]) (by simp [wp_norm, arm64_norm, hsp_s])
        (CalleeSavedPreserved.trans hcs_s (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]))
        (by simp [hpr_s])
    · have hlt : idx < (bs ++ [0#8] ++ pad).length := by simp; omega
      rw [strlen_focus8 s bs pad idx hlt]; wp_steps 2; rw [← strlen_focus8 s bs pad idx hlt]
      wp_if hcbz
      · simp only [zext32_64_eq_zero_iff] at hcbz
        exact False.elim (full_getD_ne_zero_of_lt pad hno_zero hidx_lt hcbz)
      · wp_steps 2
        exact ih (idx + 1) _ (by omega)
          (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun_s])
          (by simp [wp_norm, arm64_norm, hx0_s]) (by simp [wp_norm, arm64_norm, add_ofNat64_one])
          (by simp [wp_norm, arm64_norm, hlr_s]) (by simp [wp_norm, arm64_norm, hsp_s])
          (CalleeSavedPreserved.trans hcs_s (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]))
          (by simp [hpr_s])

/-- Read-only `SepWP` proof for static `musl` 1.2.5 AArch64 `strlen` (`muslStrlenWords`). -/
theorem muslStrlen_ro_sepWP (P : Program) (addr : BitVec 64) (hc : P.hasCode addr muslStrlenWords)
    (s0 : State) (s : BitVec 64) (bs pad : List (BitVec 8))
    (hpc : s0.pc = addr) (hrun : s0.status = .Running) (hx0 : s0.readReg64 .x0 = s)
    (hno_zero : 0#8 ∉ bs) (hpad : 8 ≤ (s.toNat + bs.length) % 8 + 1 + pad.length)
    (hno_wrap : s.toNat + (bs.length + 1 + pad.length) < 2 ^ 64)
    (_haddr : addr.toNat + 88 ≤ 2 ^ 64 := by
      simp (config := { decide := true }) only [BitVec.toNat_ofNat]; try omega; try bv_arith) :
    SepWP P (s0.readReg64 .lr) s0 (s ↦ᵣ (bs ++ [0#8] ++ pad))
      (sepPost (StrlenExit s0 bs.length) (s ↦ᵣ (bs ++ [0#8] ++ pad))) := by
  wp_step
  exact muslStrlen_align_loop P addr hc s0 s bs pad hno_zero hpad hno_wrap bs.length 0 _ (by omega)
    (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simp [wp_norm, arm64_norm, hx0]) (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
    (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) (by simp [StrlenCorePreserved.rfl])

end

/-- Read-write `SepWP` proof for static `musl` 1.2.5 AArch64 `strlen` (`s ↦ₛ (bs ++ [0#8] ++ pad)`). -/
theorem muslStrlen_sepWP (P : Program) (addr : BitVec 64) (hc : P.hasCode addr muslStrlenWords)
    (s0 : State) (s : BitVec 64) (bs pad : List (BitVec 8))
    (hpc : s0.pc = addr) (hrun : s0.status = .Running) (hx0 : s0.readReg64 .x0 = s)
    (hno_zero : 0#8 ∉ bs) (hpad : 8 ≤ (s.toNat + bs.length) % 8 + 1 + pad.length)
    (hno_wrap : s.toNat + (bs.length + 1 + pad.length) < 2 ^ 64)
    (haddr : addr.toNat + 88 ≤ 2 ^ 64 := by
      simp (config := { decide := true }) only [BitVec.toNat_ofNat]; try omega; try bv_arith) :
    SepWP P (s0.readReg64 .lr) s0 (s ↦ₛ (bs ++ [0#8] ++ pad))
      (sepPost (StrlenExit s0 bs.length) (s ↦ₛ (bs ++ [0#8] ++ pad))) :=
  SepWP.of_reaches_pc fun _ hm =>
    reaches_pc_mono
      ((muslStrlen_ro_sepWP P addr hc s0 s bs pad hpc hrun hx0 hno_zero hpad hno_wrap haddr).to_reaches_pc
        (Satisfies.pointsToBytes_to_ro hm))
      (fun _ _ _ ⟨_, _, hexit, _⟩ =>
        ⟨s ↦ₛ (bs ++ [0#8] ++ pad), hexit.2.2.2.1 ▸ hm, hexit, Entails.refl _⟩)
      (fun _ _ ho => ho)

/-! ## `subroutine_ok` specifications and contracts -/

/-- Read-only `subroutine_ok` specification for `strlen(s)` over `s ↦ᵣ (bs ++ [0#8] ++ pad)`. -/
def stdStrlenROSpec : Spec (BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := fun (s, bs, pad) s0 =>
    ⌜s0.readReg64 .x0 = s ∧ 0#8 ∉ bs ∧ 8 ≤ (s.toNat + bs.length) % 8 + 1 + pad.length ∧
      s.toNat + (bs.length + 1 + pad.length) < 2 ^ 64⌝ ∗ (s ↦ᵣ (bs ++ [0#8] ++ pad))
  post := fun (s, bs, pad) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 bs.length ∧ sf.mem = s0.mem ∧
      StrlenStatePreserved s0 sf⌝ ∗ (s ↦ᵣ (bs ++ [0#8] ++ pad))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Read-write `subroutine_ok` specification for `strlen(s)` over `s ↦ₛ (bs ++ [0#8] ++ pad)`. -/
def stdStrlenSpec : Spec (BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := fun (s, bs, pad) s0 =>
    ⌜s0.readReg64 .x0 = s ∧ 0#8 ∉ bs ∧ 8 ≤ (s.toNat + bs.length) % 8 + 1 + pad.length ∧
      s.toNat + (bs.length + 1 + pad.length) < 2 ^ 64⌝ ∗ (s ↦ₛ (bs ++ [0#8] ++ pad))
  post := fun (s, bs, pad) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 bs.length ∧ sf.mem = s0.mem ∧
      StrlenStatePreserved s0 sf⌝ ∗ (s ↦ₛ (bs ++ [0#8] ++ pad))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `subroutine_ok` contract for static `musl` AArch64 `strlen` over read-only memory (`↦ᵣ`). -/
theorem muslStrlen_ro_ok (P : Program) (addr : BitVec 64) (hc : P.hasCode addr muslStrlenWords)
    (haddr : addr.toNat + 88 ≤ 2 ^ 64 := by
      simp (config := { decide := true }) only [BitVec.toNat_ofNat]; try omega; try bv_arith) :
    subroutine_ok P addr stdStrlenROSpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨s, bs, pad⟩ R s0 hpc hrun hpre _hsp
  dsimp only [stdStrlenROSpec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hno_zero, hpad, hno_wrap⟩, hmem⟩
  refine ⟨s ↦ᵣ (bs ++ [0#8] ++ pad), hmem, SepWP.mono
    (muslStrlen_ro_sepWP P addr hc s0 s bs pad hpc hrun hx0 hno_zero hpad hno_wrap haddr) ?_⟩
  intro sf P_f _ _ ⟨⟨hx0_f, hsp_f, hcs_f, hmem_f, hpres_f⟩, hent⟩
  refine ⟨fun hm => ?_, hsp_f, hcs_f⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0_f, hmem_f, hpres_f⟩, Satisfies.mono (sepConj_mono_left hent) hm⟩

end ProofLib.StdStartup
