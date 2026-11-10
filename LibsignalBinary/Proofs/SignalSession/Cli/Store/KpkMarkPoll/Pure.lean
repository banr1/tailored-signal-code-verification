/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Kits
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs

/-!
# Pure Arithmetic, Byte-Slice, and `hasChunk` Lemmas for `mark_kyber_pre_key_used::{closure#0}`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli

theorem utf8_dot_base_ke :
    utf8 ".base-ke" = [0x2e#8, 0x62#8, 0x61#8, 0x73#8, 0x65#8, 0x2d#8, 0x6b#8, 0x65#8] := by
  decide +kernel

theorem utf8_dot_base_ke_length : (utf8 ".base-ke").length = 8 := by
  rw [utf8_dot_base_ke]; rfl

theorem utf8_ys : utf8 "ys" = [0x79#8, 0x73#8] := by
  decide +kernel

theorem baseKeysName_eq_append (id : BitVec 32) :
    keyName id ++ utf8 ".base-ke" ++ [0x79#8, 0x73#8] = baseKeysName id := by
  have hsuf : utf8 ".base-ke" ++ [0x79#8, 0x73#8] = utf8 ".base-keys" := by decide +kernel
  rw [List.append_assoc, hsuf]
  rfl

theorem pointsTo16_ys_eq_bytes (a : BitVec 64) :
    (a ↦₁₆ 0x7379#16) = (a ↦ₛ [0x79#8, 0x73#8]) := by
  rw [pointsTo16_eq_pointsToBytes]
  rfl

theorem le32_length (v : BitVec 32) : (le32 v).length = 4 := rfl

theorem pointsTo32_eq_le32 (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) = (a ↦ₛ le32 v) := by
  rw [pointsTo32_eq_pointsToBytes]
  rfl

theorem publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [PublicKey.serialize]

theorem baseKeyEntry_length (signedId : BitVec 32) (baseKey : PublicKey) :
    (baseKeyEntry signedId baseKey).length = 37 := by
  simp [baseKeyEntry, le32, PublicKey.serialize]

/-- `udiv x8, w, d; msub x8, x8, d, w` computes `w.toNat % d.toNat` without overflow for all 64-bit `w`. -/
theorem udiv_msub_toNat (w d : BitVec 64) :
    (w - (w / d) * d).toNat = w.toNat % d.toNat := by
  by_cases hd0 : d.toNat = 0
  · have hd : d = 0#64 := BitVec.eq_of_toNat_eq hd0
    subst hd
    simp
  · have hq : (w / d).toNat = w.toNat / d.toNat := BitVec.toNat_udiv
    have hmul_le : (w.toNat / d.toNat) * d.toNat ≤ w.toNat := Nat.div_mul_le_self w.toNat d.toNat
    have hlt64 : w.toNat < 2 ^ 64 := w.isLt
    have hmul_nat : ((w / d) * d).toNat = (w.toNat / d.toNat) * d.toNat := by
      rw [BitVec.toNat_mul, hq, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le]
    · rw [hmul_nat, Nat.mul_comm]
      exact (Nat.mod_def w.toNat d.toNat).symm
    · rw [BitVec.le_def, hmul_nat]
      exact hmul_le

theorem udiv_msub_37_beq_zero_false {n : Nat} (hlt : n < 2 ^ 64) (hmod : n % 37 ≠ 0) :
    (BitVec.ofNat 64 n - (BitVec.ofNat 64 n / 37#64) * 37#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [udiv_msub_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  exact hmod ht

theorem udiv_msub_37_beq_zero_true {n : Nat} (hlt : n < 2 ^ 64) (hmod : n % 37 = 0) :
    (BitVec.ofNat 64 n - (BitVec.ofNat 64 n / 37#64) * 37#64 == 0#64) = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_toNat_eq
  rw [udiv_msub_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact hmod

/-- At `cmp x8, #9; b.ls` on `x8 = cap - len` (`len ≤ cap.toNat < 2 ^ 63`, `len < 2 ^ 32`),
`(cap - len).ule 9#64 = true` implies `reserveCap cap.toNat len 10 + 1 ≤ 2 ^ 63`. -/
theorem reserve_name_bound {cap : BitVec 64} {len : Nat}
    (hlen32 : len < 2 ^ 32) (hlen_le : len ≤ cap.toNat) (_hcap63 : cap.toNat < 2 ^ 63)
    (hule : (cap - BitVec.ofNat 64 len).ule 9#64 = true) :
    reserveCap cap.toNat len 10 + 1 ≤ 2 ^ 63 := by
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hlen_le
  have h9 : (9#64 : BitVec 64).toNat = 9 := rfl
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, hsub, h9] at hule
  dsimp [reserveCap]
  omega

/-- On the fast path `(cap - len).ule 9#64 = false`, `len + 10 ≤ cap.toNat`. -/
theorem fast_name_cap_ge {cap : BitVec 64} {len : Nat}
    (hlen32 : len < 2 ^ 32) (hlen_le : len ≤ cap.toNat)
    (hule : (cap - BitVec.ofNat 64 len).ule 9#64 = false) :
    len + 10 ≤ cap.toNat := by
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hlen_le
  have h9 : (9#64 : BitVec 64).toNat = 9 := rfl
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, hsub, h9] at hule
  omega

/-- At `cmp 37, (cap - len); b.hi` (`((cap - len).ult 37#64)`) with `len < 2 ^ 32`:
- if `true`, `reserveCap cap.toNat len 37 + 1 ≤ 2 ^ 63`;
- if `false`, `len + 37 ≤ cap.toNat`. -/
theorem reserve_seen_bound {cap : BitVec 64} {len : Nat}
    (hlen32 : len < 2 ^ 32) (hlen_le : len ≤ cap.toNat) (_hcap63 : cap.toNat < 2 ^ 63)
    (hult : (cap - BitVec.ofNat 64 len).ult 37#64 = true) :
    reserveCap cap.toNat len 37 + 1 ≤ 2 ^ 63 := by
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hlen_le
  have h37 : (37#64 : BitVec 64).toNat = 37 := rfl
  rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsub, h37] at hult
  dsimp [reserveCap]
  omega

theorem fast_seen_cap_ge {cap : BitVec 64} {len : Nat}
    (hlen32 : len < 2 ^ 32) (hlen_le : len ≤ cap.toNat)
    (hult : (cap - BitVec.ofNat 64 len).ult 37#64 = false) :
    len + 37 ≤ cap.toNat := by
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hlen_le
  have h37 : (37#64 : BitVec 64).toNat = 37 := rfl
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, h37] at hult
  omega

/-! ## `hasChunk` and 37-byte chunk decomposition -/

theorem hasChunk_nil {used : List (BitVec 8)} (hu : used.length = 37) :
    hasChunk [] used = false := by
  simp [hasChunk, hu]

/-- In `cmp 37#64, remBytes; csel x23, 37#64, remBytes, lo`, whenever `37 ≤ remBytes.toNat`,
the selected chunk length `x23` is always `37#64` (even at the final chunk `remBytes = 37#64`). -/
theorem csel_min_37_eq {remBytes : BitVec 64} (hge : 37 ≤ remBytes.toNat) :
    (if (37#64 : BitVec 64).ult remBytes then 37#64 else remBytes) = 37#64 := by
  by_cases h : (37#64 : BitVec 64).ult remBytes
  · simp [h]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq] at h
    have h37 : (37#64 : BitVec 64).toNat = 37 := rfl
    rw [h37] at h
    exact BitVec.eq_of_toNat_eq (by omega)

theorem cmp_37_hi_false {remBytes : BitVec 64} (hge : 37 ≤ remBytes.toNat) :
    remBytes.ult 37#64 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  have h37 : (37#64 : BitVec 64).toNat = 37 := rfl
  rw [h37]
  omega

theorem chunk_at_idx_eq {seen pre suf : List (BitVec 8)} {idx : Nat}
    (hseen : seen = pre ++ suf) (hpre : pre.length = idx * 37) :
    (seen.drop (idx * 37)).take 37 = suf.take 37 := by
  rw [hseen, ← hpre, List.drop_left]

theorem hasChunk_true_of_match {seen pre suf used : List (BitVec 8)} {idx rem : Nat}
    (hu : used.length = 37)
    (hseen : seen = pre ++ suf)
    (hpre : pre.length = idx * 37)
    (hsuf : suf.length = (rem + 1) * 37)
    (heq : suf.take 37 = used) :
    hasChunk seen used = true := by
  have htot : seen.length / used.length = idx + rem + 1 := by
    rw [hseen, List.length_append, hpre, hsuf, hu]
    omega
  unfold hasChunk
  rw [List.any_eq_true]
  refine ⟨idx, List.mem_range.mpr (by omega), ?_⟩
  rw [hu, chunk_at_idx_eq hseen hpre, heq]
  exact beq_self_eq_true used

theorem hasChunk_false_of_all_ne {seen used : List (BitVec 8)} {k : Nat}
    (hu : used.length = 37)
    (hlen : seen.length = k * 37)
    (hall : ∀ j < k, (seen.drop (j * 37)).take 37 ≠ used) :
    hasChunk seen used = false := by
  have hdiv : seen.length / used.length = k := by
    rw [hlen, hu]
    omega
  unfold hasChunk
  rw [hdiv, List.any_eq_false]
  intro j hj
  rw [List.mem_range] at hj
  rw [hu, beq_false_of_ne (hall j hj)]
  exact Bool.false_ne_true

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setPC_pre_mark (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setMem_setPC_pre_mark (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setPC_pre_mark (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setMem_setPC_pre_mark (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setPC_pre_mark (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setMem_setPC_pre_mark (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setPC_pre_mark (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setMem_setPC_pre_mark (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setPC_pre_mark (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setMem_setPC_pre_mark (s : State) (pc : BitVec 64) (m : Memory) (idx : BitVec 5) :
    ((s.setPC pc).setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setMem_pre_mark (s : State) (m : Memory) (idx : BitVec 5) :
    (s.setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setPState_pre_mark (s : State) (ps : PState) (idx : BitVec 5) :
    (s.setPState ps).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_writeReg64_pre_mark (s : State) (r : Reg) (v : BitVec 64) (idx : BitVec 5) :
    (s.writeReg64 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append64_lo_mark (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append64_hi_mark (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append32_lo_mark (hi lo : BitVec 32) :
    BitVec.extractLsb' 0 32 (hi ++ lo) = lo := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append32_hi_mark (hi lo : BitVec 32) :
    BitVec.extractLsb' 32 32 (hi ++ lo) = hi := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem zext32_trunc32_mark (u : BitVec 32) :
    (u.zeroExtend 64).truncate 32 = u := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem calleeSavedVRegs_setPC_pre_mark (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem calleeSavedVRegs_setMem_pre_mark (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem calleeSavedVRegs_setPState_pre_mark (s : State) (ps : PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem calleeSavedVRegs_writeReg64_pre_mark (s : State) (r : Reg) (v : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_setPC_pre_mark (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_setMem_pre_mark (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_setPState_pre_mark (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_writeReg64_pre_mark (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem status_setPC_pre_mark (s : State) (pc : BitVec 64) :
    (s.setPC pc).status = s.status := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem status_setMem_pre_mark (s : State) (m : Memory) :
    (s.setMem m).status = s.status := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem status_setPState_pre_mark (s : State) (ps : PState) :
    (s.setPState ps).status = s.status := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem status_writeReg64_pre_mark (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).status = s.status := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setMem_pre_mark (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setPState_pre_mark (s : State) (ps : PState) :
    (s.setPState ps).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem pc_setPC_pre_mark (s : State) (pc : BitVec 64) :
    (s.setPC pc).pc = pc := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem pc_setMem_pre_mark (s : State) (m : Memory) :
    (s.setMem m).pc = s.pc := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem pc_setPState_pre_mark (s : State) (ps : PState) :
    (s.setPState ps).pc = s.pc := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem pc_writeReg64_pre_mark (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).pc = s.pc := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setPC_pre_mark (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setMem_pre_mark (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setPState_pre_mark (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_writeReg64_pre_mark (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl

theorem bind_sepWPp_state_mark {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : let st := s; SepWPp prog ret st P Q Qp) :
    SepWPp prog ret s P Q Qp := h

theorem bind_sepWP_state_mark {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : let st := s; SepWP prog ret st P Q) :
    SepWP prog ret s P Q := h

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
