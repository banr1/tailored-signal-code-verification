/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.SepLogic.LoopTactics
public meta import ProofLib.SepLogic.LoopTactics

/-!
# Symbolic Execution for `musl` `memcpy.S`

Specification-independent `SepWP` proof (`memcpy_sepwp`, `memcpy_loop_ok`) for the 99-instruction
AArch64 `memcpy` in `musl` v1.2.5 (`src/string/aarch64/memcpy.S`, `memcpySymWords`). Overlapping
end-window stores across size classes are folded into `ByteSlice.copySet`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib

/-- The 99 32-bit instruction words of `musl`'s AArch64 `memcpy`. -/
def memcpySymWords : List (BitVec 32) := [
  0x8b020024#32, 0x8b020005#32, 0xf102005f#32, 0x540007a8#32, 0xf100805f#32, 0x540003e8#32,
  0xf100405f#32, 0x540000c3#32, 0xa9401c26#32, 0xa97f348c#32, 0xa9001c06#32, 0xa93f34ac#32,
  0xd65f03c0#32, 0x361800e2#32, 0xf9400026#32, 0xf85f8087#32, 0xf9000006#32, 0xf81f80a7#32,
  0xd65f03c0#32, 0xd503201f#32, 0x361000c2#32, 0xb9400026#32, 0xb85fc088#32, 0xb9000006#32,
  0xb81fc0a8#32, 0xd65f03c0#32, 0xb4000102#32, 0xd341fc4e#32, 0x39400026#32, 0x385ff08a#32,
  0x386e6828#32, 0x39000006#32, 0x382e6808#32, 0x381ff0aa#32, 0xd65f03c0#32, 0xd503201f#32,
  0xa9401c26#32, 0xa9412428#32, 0xa97e2c8a#32, 0xa97f348c#32, 0xf101005f#32, 0x540000e8#32,
  0xa9001c06#32, 0xa9012408#32, 0xa93e2caa#32, 0xa93f34ac#32, 0xd65f03c0#32, 0xd503201f#32,
  0xa9423c2e#32, 0xa9434430#32, 0xf101805f#32, 0x540000a9#32, 0xa97c0c82#32, 0xa97d1081#32,
  0xa93c0ca2#32, 0xa93d10a1#32, 0xa9001c06#32, 0xa9012408#32, 0xa9023c0e#32, 0xa9034410#32,
  0xa93e2caa#32, 0xa93f34ac#32, 0xd65f03c0#32, 0xd503201f#32, 0xa940342c#32, 0x92400c0e#32,
  0x927cec03#32, 0xcb0e0021#32, 0x8b0e0042#32, 0xa9411c26#32, 0xa900340c#32, 0xa9422428#32,
  0xa9432c2a#32, 0xa9c4342c#32, 0xf1024042#32, 0x54000169#32, 0xa9011c66#32, 0xa9411c26#32,
  0xa9022468#32, 0xa9422428#32, 0xa9032c6a#32, 0xa9432c2a#32, 0xa984346c#32, 0xa9c4342c#32,
  0xf1010042#32, 0x54fffee8#32, 0xa97c3c8e#32, 0xa9011c66#32, 0xa97d1c86#32, 0xa9022468#32,
  0xa97e2488#32, 0xa9032c6a#32, 0xa97f2c8a#32, 0xa904346c#32, 0xa93c3cae#32, 0xa93d1ca6#32,
  0xa93e24a8#32, 0xa93f2caa#32, 0xd65f03c0#32]

/-- Source slice of `memcpy`: read-only (`ro = true`) or shared (`ro = false`). -/
abbrev memcpySrc (ro : Bool) (src : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  bif ro then src ↦ᵣ bs else src ↦ₛ bs

@[simp, arm64_norm, wp_norm]
theorem sigActions_writeReg64' (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_writeReg32' (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_writeReg' (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).sigActions = s.sigActions := by
  cases w <;> rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_writeVReg128' (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_writeVReg64' (s : State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 idx v).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_writeVReg32' (s : State) (idx : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 idx v).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_advancePC' (s : State) : s.advancePC.sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_setPState' (s : State) (ps : PState) : (s.setPState ps).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_setMem' (s : State) (m : Memory) : (s.setMem m).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_setStatus' (s : State) (st : ExecStatus) : (s.setStatus st).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_setBrk' (s : State) (b : BitVec 64) : (s.setBrk b).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_setFs' (s : State) (f : FsState) : (s.setFs f).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_setFpsr' (s : State) (f : BitVec 32) : (s.setFpsr f).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_nextOracle' (s : State) : s.nextOracle.sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_stepExclOracle' (s : State) : s.stepExclOracle.sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_stepExclLoop' (s : State) : s.stepExclLoop.sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_appendTrace' (s : State) (evs : List TraceEvent) : (s.appendTrace evs).sigActions = s.sigActions := rfl

@[simp, arm64_norm, wp_norm]
theorem sigActions_applyWriteback' (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).sigActions = s.sigActions := by
  cases wb <;> rfl

abbrev MemcpySysPreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧
  sf.brkStart = s0.brkStart ∧ sf.oracle = s0.oracle ∧ sf.symtab = s0.symtab ∧
  sf.sigActions = s0.sigActions ∧ sf.brk = s0.brk

theorem MemcpySysPreserved.rfl (s : State) : MemcpySysPreserved s s :=
  ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩

theorem MemcpySysPreserved.trans {s0 s1 s2 : State}
    (h01 : MemcpySysPreserved s0 s1) (h12 : MemcpySysPreserved s1 s2) :
    MemcpySysPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2⟩

/-- Exit facts of `memcpy` relative to the entry state `s0`. -/
abbrev MemcpyExit (s0 : State) (dst : BitVec 64) (sf : State) : Prop :=
  sf.readReg64 .x0 = dst ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ MemcpySysPreserved s0 sf

abbrev MemcpyGoal (ro : Bool) (prog : Program) (s0 : State) (dst src : BitVec 64)
    (old bs : List (BitVec 8)) : Prop :=
  SepWP prog (s0.readReg64 .lr) s0 ((dst ↦ₛ old) ∗ memcpySrc ro src bs)
    (sepPost (MemcpyExit s0 dst) ((dst ↦ₛ bs) ∗ memcpySrc ro src bs))

/-! ## Byte-Region Lemmas for Overlapping Copies -/

theorem pack64_getD_eq_readLE (bs : List (BitVec 8)) (o o1 o2 o3 o4 o5 o6 o7 : Nat)
    (h1 : o1 = o + 1) (h2 : o2 = o + 2) (h3 : o3 = o + 3) (h4 : o4 = o + 4) (h5 : o5 = o + 5)
    (h6 : o6 = o + 6) (h7 : o7 = o + 7) :
    pack64 (bs.getD o 0#8) (bs.getD o1 0#8) (bs.getD o2 0#8) (bs.getD o3 0#8) (bs.getD o4 0#8)
      (bs.getD o5 0#8) (bs.getD o6 0#8) (bs.getD o7 0#8) = ByteSlice.readLE bs o 8 := by
  subst h1 h2 h3 h4 h5 h6 h7
  exact ByteSlice.pack64_eq_readLE_8 bs o

theorem SepWP.weaken_to_post {prog : Program} {t : BitVec 64} {s : State} {P Q : SepProp}
    {R : State → Prop} (hent : P ⊢ Q) (h : SepWP prog t s Q (sepPost R Q)) :
    SepWP prog t s P (sepPost R Q) :=
  SepWP.weaken_pre hent h

theorem SepWP.copySet_pre {prog : Program} {t : BitVec 64} {s : State} {dst : BitVec 64}
    {old src : List (BitVec 8)} {p q : Nat → Bool} {Rest : SepProp}
    {post : State → SepProp → Prop}
    (hpq : ∀ i, i < old.length → p i = q i)
    (h : SepWP prog t s ((dst ↦ₛ ByteSlice.copySet old src q) ∗ Rest) post) :
    SepWP prog t s ((dst ↦ₛ ByteSlice.copySet old src p) ∗ Rest) post := by
  rw [ByteSlice.copySet_congr hpq]; exact h

theorem write64_readLE_eq_copySet (L src : List (BitVec 8)) (off : Nat)
    (h : off + 8 ≤ L.length) :
    ByteSlice.write64 L off (ByteSlice.readLE src off 8) =
      ByteSlice.copySet L src (fun i => decide (off ≤ i) && decide (i < off + 8)) := by
  have := ByteSlice.write64_copySet_readLE L src (fun _ => false) off h
  rw [ByteSlice.copySet_false] at this
  simpa only [Bool.false_or] using this

theorem copySet_copySet (old src : List (BitVec 8)) (p q : Nat → Bool) :
    ByteSlice.copySet (ByteSlice.copySet old src p) src q =
      ByteSlice.copySet old src (fun i => p i || q i) := by
  apply ByteSlice.ext_getD (by simp)
  intro i hi
  simp only [ByteSlice.copySet_length] at hi
  simp only [ByteSlice.getD_copySet, ByteSlice.copySet_length, hi, decide_true, Bool.and_true]
  cases p i <;> cases q i <;> simp

theorem copySet_run2 (old src : List (BitVec 8)) (q : Nat → Bool) (o0 o1 : Nat)
    (h1 : o1 = o0 + 8) (h : o0 + 16 ≤ old.length) :
    ByteSlice.write64 (ByteSlice.write64 (ByteSlice.copySet old src q) o0
        (ByteSlice.readLE src o0 8)) o1 (ByteSlice.readLE src o1 8) =
      ByteSlice.copySet old src (fun i => q i || (decide (o0 ≤ i) && decide (i < o0 + 16))) := by
  subst h1
  rw [ByteSlice.write64_copySet_readLE old src q o0 (by omega),
    ByteSlice.write64_copySet_readLE old src
      (fun i => q i || (decide (o0 ≤ i) && decide (i < o0 + 8))) (o0 + 8) (by omega)]
  apply ByteSlice.copySet_congr
  intro i _
  cases q i
  · simp only [Bool.false_or]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · simp only [Bool.true_or]

theorem copySet_run2_base (old src : List (BitVec 8)) (o0 o1 : Nat)
    (h1 : o1 = o0 + 8) (h : o0 + 16 ≤ old.length) :
    ByteSlice.write64 (ByteSlice.write64 old o0 (ByteSlice.readLE src o0 8)) o1
        (ByteSlice.readLE src o1 8) =
      ByteSlice.copySet old src (fun i => decide (o0 ≤ i) && decide (i < o0 + 16)) := by
  have := copySet_run2 old src (fun _ => false) o0 o1 h1 h
  rw [ByteSlice.copySet_false] at this
  simpa only [Bool.false_or] using this

theorem write8_three_eq (old bs : List (BitVec 8)) (n : Nat)
    (hlen : old.length = n) (hslen : bs.length = n) (h1 : 1 ≤ n) (h4 : n < 4) :
    ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 old 0 (bs.getD 0 0#8)) (n / 2)
        (bs.getD (n / 2) 0#8)) (n - 1) (bs.getD (n - 1) 0#8) = bs := by
  have l1 : (ByteSlice.write8 old 0 (bs.getD 0 0#8)).length = n := by
    rw [ByteSlice.write8_length _ _ _ (by omega), hlen]
  have l2 : (ByteSlice.write8 (ByteSlice.write8 old 0 (bs.getD 0 0#8)) (n / 2)
      (bs.getD (n / 2) 0#8)).length = n := by
    rw [ByteSlice.write8_length _ _ _ (by omega), l1]
  have l3 : (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 old 0 (bs.getD 0 0#8)) (n / 2)
      (bs.getD (n / 2) 0#8)) (n - 1) (bs.getD (n - 1) 0#8)).length = n := by
    rw [ByteSlice.write8_length _ _ _ (by omega), l2]
  apply ByteSlice.ext_getD (by rw [l3, hslen])
  intro i hi
  rw [l3] at hi
  rw [ByteSlice.getD_write8 _ _ _ _ _ (by rw [l2]; omega),
    ByteSlice.getD_write8 _ _ _ _ _ (by rw [l1]; omega),
    ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
  split
  next e1 => rw [e1]
  next =>
    split
    next e2 => rw [e2]
    next =>
      split
      next e3 => rw [e3]
      next => omega

local macro "copy_collapse" : tactic =>
  `(tactic| simp (disch := first | omega | byte_region_len) only [pack64_getD_eq_readLE,
    write64_readLE_eq_copySet, copySet_copySet])

local macro "copy_runs" : tactic => `(tactic|
  wp_conv_pre => simp (disch := omega) only [pack64_getD_eq_readLE, copySet_run2,
    copySet_run2_base])

local macro "copy_entails" : tactic =>
  `(tactic| (
    try simp only [ProofLib.sepConj_assoc]
    apply ProofLib.ByteSlice.entails_of_eq
    repeat' (first
      | with_reducible rfl
      | apply ProofLib.ByteSlice.sepConj_congr_eq
      | apply ProofLib.pointsToBytes_congr_bytes
      | apply ProofLib.pointsToBytesRO_congr_bytes)
    all_goals (
      try copy_collapse
      first
      | (apply ProofLib.ByteSlice.copySet_all (by byte_region_len)
         intro i hi
         simp only [ProofLib.ByteSlice.copySet_length, Bool.or_eq_true, Bool.and_eq_true,
           decide_eq_true_eq] at hi ⊢
         omega)
      | (apply ProofLib.ByteSlice.copySet_congr
         intro i hi
         try simp only [ProofLib.ByteSlice.copySet_length] at hi
         rw [Bool.eq_iff_iff]
         simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
         omega))))

local macro "copy_done" : tactic => `(tactic| (
  apply SepWP.weaken_to_post
  · first
    | copy_entails
    | (try simp (disch := omega) only [pack64_getD_eq_readLE]
       byte_region_entails)
  · wp_done))

local macro "memcpy_ro_cases" ro:ident : tactic => `(tactic| (
  cases $ro:ident <;>
    dsimp only [MemcpyGoal, memcpySrc, MemcpyExit, MemcpySysPreserved, Bool.cond_true, Bool.cond_false]))

/-! ## Closed Arithmetic Facts -/

theorem and15_lt (x : BitVec 64) : (x &&& 15#64).toNat < 16 := by
  have h : (x &&& 15#64).ult 16#64 = true := by bv_bits
  simpa [BitVec.ult] using h

theorem andNot15_eq (x : BitVec 64) :
    x &&& 0xfffffffffffffff0#64 = x - BitVec.ofNat 64 (x &&& 15#64).toNat := by
  have h1 : x &&& 0xfffffffffffffff0#64 = x - (x &&& 15#64) := by bv_bits
  have h2 : BitVec.ofNat 64 (x &&& 15#64).toNat = x &&& 15#64 := by bv_arith
  rw [h1, h2]

theorem add_ofNat_ule (n : BitVec 64) (d K : Nat) (_hK : K < 2 ^ 64) (h : n.toNat + d ≤ K) :
    (n + BitVec.ofNat 64 d).ule (BitVec.ofNat 64 K) = true := by
  bv_arith

theorem add_ofNat_ule_false (n : BitVec 64) (d K : Nat) (_hK : K < 2 ^ 64) (hn : n.toNat ≤ 2 ^ 63)
    (hd : d < 16) (h : K < n.toNat + d) :
    (n + BitVec.ofNat 64 d).ule (BitVec.ofNat 64 K) = false := by
  bv_arith

theorem ofNat_ult_ofNat (K j : Nat) (hj : j < 2 ^ 64) (h : K < j) :
    (BitVec.ofNat 64 K).ult (BitVec.ofNat 64 j) = true := by
  bv_arith

theorem ofNat_ult_ofNat_false (K j : Nat) (hK : K < 2 ^ 64) (h : j ≤ K) :
    (BitVec.ofNat 64 K).ult (BitVec.ofNat 64 j) = false := by
  bv_arith

theorem sub_ofNat_eq (x : BitVec 64) (d q : Nat) (hq : q + d = 16) :
    x - BitVec.ofNat 64 d = x + BitVec.ofNat 64 q - 16#64 := by
  obtain rfl : d = 16 - q := by omega
  have hq16 : q ≤ 16 := by omega
  bv_omega

theorem x2_eq (n : BitVec 64) (d M r : Nat) (h : n.toNat + d - 144 = 64 * M + r)
    (_hn : n.toNat ≤ 2 ^ 63) (_hd : d < 16) (hgt : 144 < n.toNat + d) :
    n + BitVec.ofNat 64 d - 144#64 = BitVec.ofNat 64 (64 * M + r) := by
  bv_omega

theorem add_ofNat_add64 (x : BitVec 64) (p c : Nat) (c' : BitVec 64)
    (h : BitVec.ofNat 64 (c + 64) = c') :
    x + BitVec.ofNat 64 (p + 64) + BitVec.ofNat 64 c = x + BitVec.ofNat 64 p + c' := by
  subst h; bv_omega

theorem add_ofNat_add64_sub16 (x : BitVec 64) (p : Nat) :
    x + BitVec.ofNat 64 (p + 64) - 16#64 = x + BitVec.ofNat 64 p + 48#64 := by
  bv_omega

theorem ofNat_loop_count (m r : Nat) :
    BitVec.ofNat 64 (64 * m + r) = BitVec.ofNat 64 (64 * (m + 1) + r) - 64#64 := by
  bv_omega

theorem calleeSaved_trans {s0 s1 s2 : State} (h01 : CalleeSavedPreserved s0 s1)
    (h12 : CalleeSavedPreserved s1 s2) : CalleeSavedPreserved s0 s2 :=
  h01.trans h12

/-! ## The `.Lloop64` Loop (`0x130`) and Shared Tail (`0x158`) -/

set_option maxHeartbeats 400000 in
/-- Executes `.Lloop64` from `0x130` once `[0, q)` has been copied, storing 64 bytes per iteration
    before falling through to the shared `[n - 64, n)` tail at `0x158`. -/
theorem memcpy_loop_ok (ro : Bool) (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memcpySymWords)
    (st : State) (dst src n : BitVec 64) (old bs : List (BitVec 8)) (q M r : Nat)
    (hpc : st.pc = a + 304#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = dst)
    (hx1 : st.readReg64 .x1 = src + BitVec.ofNat 64 q + 48#64)
    (hx2 : st.readReg64 .x2 = BitVec.ofNat 64 (64 * M + r))
    (hx3 : st.readReg64 .x3 = dst + BitVec.ofNat 64 q - 16#64)
    (hx4 : st.readReg64 .x4 = src + n) (hx5 : st.readReg64 .x5 = dst + n)
    (hx6 : st.readReg64 .x6 = ByteSlice.readLE bs q 8)
    (hx7 : st.readReg64 .x7 = ByteSlice.readLE bs (q + 8) 8)
    (hx8 : st.readReg64 .x8 = ByteSlice.readLE bs (q + 16) 8)
    (hx9 : st.readReg64 .x9 = ByteSlice.readLE bs (q + 24) 8)
    (hx10 : st.readReg64 .x10 = ByteSlice.readLE bs (q + 32) 8)
    (hx11 : st.readReg64 .x11 = ByteSlice.readLE bs (q + 40) 8)
    (hx12 : st.readReg64 .x12 = ByteSlice.readLE bs (q + 48) 8)
    (hx13 : st.readReg64 .x13 = ByteSlice.readLE bs (q + 56) 8)
    (hlen : old.length = n.toNat) (hslen : bs.length = n.toNat)
    (hn : n.toNat = q + 64 * M + r + 128) (hq1 : 1 ≤ q) (hq16 : q ≤ 16)
    (hr1 : 1 ≤ r) (hr64 : r ≤ 64) (hn63 : n.toNat ≤ 2 ^ 63) :
    SepWP prog (st.readReg64 .lr) st
      ((dst ↦ₛ ByteSlice.copySet old bs (fun i => decide (i < 16) || decide (i < q))) ∗
        memcpySrc ro src bs)
      (sepPost (MemcpyExit st dst) ((dst ↦ₛ bs) ∗ memcpySrc ro src bs)) := by
  have hM0 : q + 64 * (M - M) = q := by rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
  wp_loop_measure frame M (fun k st' => k ≤ M ∧
      st'.readReg64 .x0 = dst ∧
      st'.readReg64 .x1 = src + BitVec.ofNat 64 (q + 64 * (M - k)) + 48#64 ∧
      st'.readReg64 .x2 = BitVec.ofNat 64 (64 * k + r) ∧
      st'.readReg64 .x3 = dst + BitVec.ofNat 64 (q + 64 * (M - k)) - 16#64 ∧
      st'.readReg64 .x4 = src + n ∧ st'.readReg64 .x5 = dst + n ∧
      st'.readReg64 .x6 = ByteSlice.readLE bs (q + 64 * (M - k)) 8 ∧
      st'.readReg64 .x7 = ByteSlice.readLE bs (q + 64 * (M - k) + 8) 8 ∧
      st'.readReg64 .x8 = ByteSlice.readLE bs (q + 64 * (M - k) + 16) 8 ∧
      st'.readReg64 .x9 = ByteSlice.readLE bs (q + 64 * (M - k) + 24) 8 ∧
      st'.readReg64 .x10 = ByteSlice.readLE bs (q + 64 * (M - k) + 32) 8 ∧
      st'.readReg64 .x11 = ByteSlice.readLE bs (q + 64 * (M - k) + 40) 8 ∧
      st'.readReg64 .x12 = ByteSlice.readLE bs (q + 64 * (M - k) + 48) 8 ∧
      st'.readReg64 .x13 = ByteSlice.readLE bs (q + 64 * (M - k) + 56) 8 ∧
      st'.fs = st.fs ∧ st'.trace = st.trace ∧ st'.tpidrEl0 = st.tpidrEl0 ∧
      st'.brkStart = st.brkStart ∧ st'.oracle = st.oracle ∧ st'.symtab = st.symtab ∧
      st'.sigActions = st.sigActions ∧ st'.brk = st.brk)
    (fun k _ => (dst ↦ₛ ByteSlice.copySet old bs
        (fun i => decide (i < 16) || decide (i < q + 64 * (M - k)))) ∗ memcpySrc ro src bs)
  case base =>
    simp only [Nat.sub_zero] at *
    generalize hp : q + 64 * M = p at *
    have hpn : p + r + 128 = n.toNat := by omega
    have hlo : (64#64).ult (BitVec.ofNat 64 r) = false :=
      ofNat_ult_ofNat_false 64 _ (by omega) (by omega)
    simp only [Nat.zero_add] at *
    clear hp hM0 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hn
    split_callee_saved
    memcpy_ro_cases ro
    all_goals (
      wp_sym_steps 10
      copy_runs
      wp_sym_steps 6
      copy_runs
      wp_sym_steps
      copy_runs
      copy_done)
  case step =>
    have hhi : (64#64).ult (BitVec.ofNat 64 (64 * (m' + 1) + r)) = true :=
      ofNat_ult_ofNat 64 _ (by omega) (by omega)
    have hm'M : m' ≤ M := by omega
    have hp' : q + 64 * (M - m') = q + 64 * (M - (m' + 1)) + 64 := by omega
    rw [hp']
    generalize hp : q + 64 * (M - (m' + 1)) = p at *
    have hpn : p + 64 * m' + r + 192 = n.toNat := by omega
    clear hp hp' hM0 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hn
    have hx1e := add_ofNat_add64 src p 48 112#64 rfl
    have hx3e := add_ofNat_add64_sub16 dst p
    have hx2s := ofNat_loop_count m' r
    right
    memcpy_ro_cases ro
    all_goals (
      wp_sym_steps 10
      copy_runs
      refine SepWP.copySet_pre (q := fun i => decide (i < 16) || decide (i < p + 64)) ?_ ?_
      · intro i _
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        omega
      · simp only [Nat.add_assoc, Nat.reduceAdd]
        rw [hx1e, hx3e, hx2s]
        wp_done)

theorem memcpy_loop_entry (ro : Bool) (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memcpySymWords)
    (s0 st : State) (dst src n : BitVec 64) (old bs : List (BitVec 8)) (q M r : Nat)
    (hlr : st.readReg64 .lr = s0.readReg64 .lr) (hsp : st.sp = s0.sp)
    (hcs : CalleeSavedPreserved s0 st) (hsys : MemcpySysPreserved s0 st)
    (hpc : st.pc = a + 304#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = dst)
    (hx1 : st.readReg64 .x1 = src + BitVec.ofNat 64 q + 48#64)
    (hx2 : st.readReg64 .x2 = BitVec.ofNat 64 (64 * M + r))
    (hx3 : st.readReg64 .x3 = dst + BitVec.ofNat 64 q - 16#64)
    (hx4 : st.readReg64 .x4 = src + n) (hx5 : st.readReg64 .x5 = dst + n)
    (hx6 : st.readReg64 .x6 = ByteSlice.readLE bs q 8)
    (hx7 : st.readReg64 .x7 = ByteSlice.readLE bs (q + 8) 8)
    (hx8 : st.readReg64 .x8 = ByteSlice.readLE bs (q + 16) 8)
    (hx9 : st.readReg64 .x9 = ByteSlice.readLE bs (q + 24) 8)
    (hx10 : st.readReg64 .x10 = ByteSlice.readLE bs (q + 32) 8)
    (hx11 : st.readReg64 .x11 = ByteSlice.readLE bs (q + 40) 8)
    (hx12 : st.readReg64 .x12 = ByteSlice.readLE bs (q + 48) 8)
    (hx13 : st.readReg64 .x13 = ByteSlice.readLE bs (q + 56) 8)
    (hlen : old.length = n.toNat) (hslen : bs.length = n.toNat)
    (hn : n.toNat = q + 64 * M + r + 128) (hq1 : 1 ≤ q) (hq16 : q ≤ 16)
    (hr1 : 1 ≤ r) (hr64 : r ≤ 64) (hn63 : n.toNat ≤ 2 ^ 63) {P : SepProp}
    (hP : P ⊢ (dst ↦ₛ ByteSlice.copySet old bs (fun i => decide (i < 16) || decide (i < q))) ∗
        memcpySrc ro src bs) :
    SepWP prog (s0.readReg64 .lr) st P
      (sepPost (MemcpyExit s0 dst) ((dst ↦ₛ bs) ∗ memcpySrc ro src bs)) := by
  rw [← hlr]
  refine SepWP.weaken_pre hP (SepWP.mono (memcpy_loop_ok ro prog a hc st dst src n old bs q M r
    hpc hrun hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hlen hslen hn hq1 hq16
    hr1 hr64 hn63) ?_)
  intro sf P_f _ _ ⟨⟨hx0f, hspf, hcsf, hsysf⟩, hent⟩
  exact ⟨⟨hx0f, hspf.trans hsp, calleeSaved_trans hcs hcsf, hsys.trans hsysf⟩, hent⟩

/-! ## Size Classes -/

theorem memcpy_0_ok (ro : Bool) (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memcpySymWords)
    (s0 : State) (dst src n : BitVec 64) (old bs : List (BitVec 8))
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : s0.readReg64 .x2 = n) (hlen : old.length = n.toNat) (hslen : bs.length = n.toNat)
    (hn0 : n.toNat = 0) :
    MemcpyGoal ro prog s0 dst src old bs := by
  obtain rfl : n = 0#64 := by bv_omega
  obtain rfl : old = [] := List.length_eq_zero_iff.mp (by rw [hlen]; rfl)
  obtain rfl : bs = [] := List.length_eq_zero_iff.mp (by rw [hslen]; rfl)
  memcpy_ro_cases ro
  all_goals (wp_sym_steps; wp_done)

theorem memcpy_1_3_ok (ro : Bool) (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memcpySymWords)
    (s0 : State) (dst src n : BitVec 64) (old bs : List (BitVec 8))
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : s0.readReg64 .x2 = n) (hlen : old.length = n.toNat) (hslen : bs.length = n.toNat)
    (hn1 : 1 ≤ n.toNat) (hn4 : n.toNat < 4) :
    MemcpyGoal ro prog s0 dst src old bs := by
  have h128 : (128#64).ult n = false := by bv_arith
  have h32 : (32#64).ult n = false := by bv_arith
  have h16 : n.ult 16#64 = true := by bv_arith
  have hb3 : n.getLsbD 3 = false := by bv_bits
  have hb2 : n.getLsbD 2 = false := by bv_bits
  have hcbz : ¬(n == 0#64) = true := by simp only [beq_iff_eq]; bv_omega
  have hhalf : n >>> 1 = BitVec.ofNat 64 (n.toNat / 2) := by bv_arith
  memcpy_ro_cases ro
  all_goals (
    wp_sym_steps
    rw [write8_three_eq old bs n.toNat hlen hslen hn1 hn4]
    wp_done)

theorem memcpy_4_7_ok (ro : Bool) (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memcpySymWords)
    (s0 : State) (dst src n : BitVec 64) (old bs : List (BitVec 8))
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : s0.readReg64 .x2 = n) (hlen : old.length = n.toNat) (hslen : bs.length = n.toNat)
    (hn4 : 4 ≤ n.toNat) (hn8 : n.toNat < 8) :
    MemcpyGoal ro prog s0 dst src old bs := by
  have h128 : (128#64).ult n = false := by bv_arith
  have h32 : (32#64).ult n = false := by bv_arith
  have h16 : n.ult 16#64 = true := by bv_arith
  have hb3 : n.getLsbD 3 = false := by bv_bits
  have hb2 : n.getLsbD 2 = true := by bv_bits
  memcpy_ro_cases ro
  all_goals (wp_sym_steps; copy_done)

theorem memcpy_8_15_ok (ro : Bool) (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memcpySymWords)
    (s0 : State) (dst src n : BitVec 64) (old bs : List (BitVec 8))
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : s0.readReg64 .x2 = n) (hlen : old.length = n.toNat) (hslen : bs.length = n.toNat)
    (hn8 : 8 ≤ n.toNat) (hn16 : n.toNat < 16) :
    MemcpyGoal ro prog s0 dst src old bs := by
  have h128 : (128#64).ult n = false := by bv_arith
  have h32 : (32#64).ult n = false := by bv_arith
  have h16 : n.ult 16#64 = true := by bv_arith
  have hb3 : n.getLsbD 3 = true := by bv_bits
  memcpy_ro_cases ro
  all_goals (wp_sym_steps; copy_done)

theorem memcpy_16_32_ok (ro : Bool) (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memcpySymWords)
    (s0 : State) (dst src n : BitVec 64) (old bs : List (BitVec 8))
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : s0.readReg64 .x2 = n) (hlen : old.length = n.toNat) (hslen : bs.length = n.toNat)
    (hn16 : 16 ≤ n.toNat) (hn32 : n.toNat ≤ 32) :
    MemcpyGoal ro prog s0 dst src old bs := by
  have h128 : (128#64).ult n = false := by bv_arith
  have h32 : (32#64).ult n = false := by bv_arith
  have h16 : n.ult 16#64 = false := by bv_arith
  memcpy_ro_cases ro
  all_goals (wp_sym_steps; copy_done)

theorem memcpy_33_64_ok (ro : Bool) (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memcpySymWords)
    (s0 : State) (dst src n : BitVec 64) (old bs : List (BitVec 8))
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : s0.readReg64 .x2 = n) (hlen : old.length = n.toNat) (hslen : bs.length = n.toNat)
    (hn33 : 33 ≤ n.toNat) (hn64 : n.toNat ≤ 64) :
    MemcpyGoal ro prog s0 dst src old bs := by
  have h128 : (128#64).ult n = false := by bv_arith
  have h32 : (32#64).ult n = true := by bv_arith
  have h64 : (64#64).ult n = false := by bv_arith
  memcpy_ro_cases ro
  all_goals (wp_sym_steps; copy_done)

theorem memcpy_65_96_ok (ro : Bool) (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memcpySymWords)
    (s0 : State) (dst src n : BitVec 64) (old bs : List (BitVec 8))
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : s0.readReg64 .x2 = n) (hlen : old.length = n.toNat) (hslen : bs.length = n.toNat)
    (hn65 : 65 ≤ n.toNat) (hn96 : n.toNat ≤ 96) :
    MemcpyGoal ro prog s0 dst src old bs := by
  have h128 : (128#64).ult n = false := by bv_arith
  have h32 : (32#64).ult n = true := by bv_arith
  have h64 : (64#64).ult n = true := by bv_arith
  have h96 : n.ule 96#64 = true := by bv_arith
  memcpy_ro_cases ro
  all_goals (wp_sym_steps; copy_done)

theorem memcpy_97_128_ok (ro : Bool) (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memcpySymWords)
    (s0 : State) (dst src n : BitVec 64) (old bs : List (BitVec 8))
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : s0.readReg64 .x2 = n) (hlen : old.length = n.toNat) (hslen : bs.length = n.toNat)
    (hn97 : 97 ≤ n.toNat) (hn128 : n.toNat ≤ 128) :
    MemcpyGoal ro prog s0 dst src old bs := by
  have h128 : (128#64).ult n = false := by bv_arith
  have h32 : (32#64).ult n = true := by bv_arith
  have h64 : (64#64).ult n = true := by bv_arith
  have h96 : n.ule 96#64 = false := by bv_arith
  memcpy_ro_cases ro
  all_goals (wp_sym_steps; copy_done)

theorem memcpy_large_ok (ro : Bool) (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memcpySymWords)
    (s0 : State) (dst src n : BitVec 64) (old bs : List (BitVec 8))
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : s0.readReg64 .x2 = n) (hlen : old.length = n.toNat) (hslen : bs.length = n.toNat)
    (hn128 : 128 < n.toNat) (hn63 : n.toNat ≤ 2 ^ 63) :
    MemcpyGoal ro prog s0 dst src old bs := by
  have h128 : (128#64).ult n = true := by bv_arith
  obtain ⟨d, hd⟩ : ∃ d, (dst &&& 15#64).toNat = d := ⟨_, rfl⟩
  have hd16 : d < 16 := hd ▸ and15_lt dst
  have hand15 : dst &&& 15#64 = BitVec.ofNat 64 d := by rw [← hd]; bv_arith
  obtain ⟨q, hq⟩ : ∃ q, q + d = 16 := ⟨16 - d, by omega⟩
  have hand16 : dst &&& 0xfffffffffffffff0#64 = dst + BitVec.ofNat 64 q - 16#64 := by
    rw [andNot15_eq, hd]; exact sub_ofNat_eq dst d q hq
  have hsrc : src - BitVec.ofNat 64 d = src + BitVec.ofNat 64 q - 16#64 :=
    sub_ofNat_eq src d q hq
  by_cases hskip : n.toNat + d ≤ 144
  · have hle : (n + BitVec.ofNat 64 d).ule 144#64 = true :=
      add_ofNat_ule n d 144 (by omega) hskip
    memcpy_ro_cases ro
    all_goals (
      wp_sym_steps 16
      clear hx1 hx2 hle h128 hand15 hand16 hsrc hd
      copy_runs
      wp_sym_steps 6
      copy_runs
      wp_sym_steps
      copy_runs
      copy_done)
  · have hgt : (n + BitVec.ofNat 64 d).ule 144#64 = false :=
      add_ofNat_ule_false n d 144 (by omega) hn63 hd16 (by omega)
    obtain ⟨M, r, hMr, hr1, hr64⟩ :
        ∃ M r, n.toNat + d - 144 = 64 * M + r ∧ 1 ≤ r ∧ r ≤ 64 :=
      ⟨(n.toNat + d - 145) / 64, (n.toNat + d - 145) % 64 + 1, by omega, by omega, by omega⟩
    have hx2e : n + BitVec.ofNat 64 d - 144#64 = BitVec.ofNat 64 (64 * M + r) :=
      x2_eq n d M r hMr hn63 hd16 (by omega)
    have hnM : n.toNat = q + 64 * M + r + 128 := by omega
    memcpy_ro_cases ro
    all_goals (
      wp_sym_steps 16
      clear hx1 hx2 hgt h128 hand15 hand16 hsrc hd hskip hMr
      copy_runs
      first
      | refine memcpy_loop_entry true prog a hc s0 _ dst src n old bs q M r ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hlen hslen hnM (by omega) (by omega) hr1 hr64 hn63 ?_
      | refine memcpy_loop_entry false prog a hc s0 _ dst src n old bs q M r ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hlen hslen hnM (by omega) (by omega) hr1 hr64 hn63 ?_
      all_goals first
        | (simp only [arm64_norm, *]; done)
        | (simp only [arm64_norm]; exact CalleeSavedPreserved.rfl _)
        | (simp only [MemcpySysPreserved, arm64_norm]; done)
        | (dsimp only [memcpySrc, Bool.cond_true, Bool.cond_false]; copy_entails)
        | skip)

/-- `SepWP` specification of `musl` AArch64 `memcpy` across all size classes (`n ≤ 2 ^ 63`). -/
theorem memcpy_sepwp (ro : Bool) (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memcpySymWords)
    (s0 : State) (dst src n : BitVec 64) (old bs : List (BitVec 8))
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : s0.readReg64 .x2 = n) (hlen : old.length = n.toNat) (hslen : bs.length = n.toNat)
    (hn63 : n.toNat ≤ 2 ^ 63) :
    MemcpyGoal ro prog s0 dst src old bs := by
  rcases Nat.lt_or_ge n.toNat 1 with h | h1
  · exact memcpy_0_ok ro prog a hc s0 dst src n old bs hpc hrun hx0 hx1 hx2 hlen hslen (by omega)
  rcases Nat.lt_or_ge n.toNat 4 with h | h4
  · exact memcpy_1_3_ok ro prog a hc s0 dst src n old bs hpc hrun hx0 hx1 hx2 hlen hslen h1 h
  rcases Nat.lt_or_ge n.toNat 8 with h | h8
  · exact memcpy_4_7_ok ro prog a hc s0 dst src n old bs hpc hrun hx0 hx1 hx2 hlen hslen h4 h
  rcases Nat.lt_or_ge n.toNat 16 with h | h16
  · exact memcpy_8_15_ok ro prog a hc s0 dst src n old bs hpc hrun hx0 hx1 hx2 hlen hslen h8 h
  rcases Nat.lt_or_ge 32 n.toNat with h32 | h
  rotate_left
  · exact memcpy_16_32_ok ro prog a hc s0 dst src n old bs hpc hrun hx0 hx1 hx2 hlen hslen h16 h
  rcases Nat.lt_or_ge 64 n.toNat with h64 | h
  rotate_left
  · exact memcpy_33_64_ok ro prog a hc s0 dst src n old bs hpc hrun hx0 hx1 hx2 hlen hslen h32 h
  rcases Nat.lt_or_ge 96 n.toNat with h96 | h
  rotate_left
  · exact memcpy_65_96_ok ro prog a hc s0 dst src n old bs hpc hrun hx0 hx1 hx2 hlen hslen h64 h
  rcases Nat.lt_or_ge 128 n.toNat with h128 | h
  rotate_left
  · exact memcpy_97_128_ok ro prog a hc s0 dst src n old bs hpc hrun hx0 hx1 hx2 hlen hslen h96 h
  exact memcpy_large_ok ro prog a hc s0 dst src n old bs hpc hrun hx0 hx1 hx2 hlen hslen h128 hn63

end VerifiedLibraries.Mallocng.Proofs
