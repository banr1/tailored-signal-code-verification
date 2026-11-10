/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropCodePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Step Combinators and Deallocation Helpers for M5 Drop Paths (Block `617`)

PC arithmetic, `InMainPlaced` pure/store step combinators, `seq_frozen_codeOk`, `step_dealloc_placed`,
and `dirVecAt` / `dirsVecAt` helpers for M5 drop blocks on Block `617`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.CodeLayout

namespace M5DropPlacedHelpers

theorem mul3_lsl4_eq_mul48 (cap : BitVec 64) :
    ((cap + (cap <<< 1#64)) <<< 4) = cap * 48#64 := by
  bv_bits

theorem mul48_toNat_of_lt (cap : BitVec 64) (hlt : cap.toNat * 48 < 2 ^ 63) :
    (cap * 48#64).toNat = cap.toNat * 48 := by
  rw [BitVec.toNat_mul]
  change (cap.toNat * 48) % 2 ^ 64 = cap.toNat * 48
  exact Nat.mod_eq_of_lt (by omega)

theorem layoutOk_u8_of_cap_ne_zero {cap : BitVec 64}
    (hnez : cap ≠ 0#64) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 := by
  have hpos : 0 < cap.toNat := by
    by_contra hle
    exact hnez (BitVec.eq_of_toNat_eq (by simpa using Nat.eq_zero_of_le_zero (Nat.not_lt.mp hle)))
  exact ⟨hpos, ⟨0, rfl⟩, by omega⟩

theorem layoutOk_dirBuf_of_cap_ne_zero {cap : BitVec 64}
    (hnez : cap ≠ 0#64) (hlt : cap.toNat * 48 < 2 ^ 63) :
    LayoutOk (cap.toNat * 48) 8 := by
  have hpos : 0 < cap.toNat := by
    by_contra hle
    exact hnez (BitVec.eq_of_toNat_eq (by simpa using Nat.eq_zero_of_le_zero (Nat.not_lt.mp hle)))
  exact ⟨by omega, ⟨3, rfl⟩, by omega⟩

theorem ofNat_sub_one_eq {n : Nat} :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem ofNat_ne_zero_of_pos_lt {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have h := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h
  omega

theorem ofNat_ne_of_ne_lt {m n : Nat} (hne : m ≠ n) (hm : m < 2 ^ 64) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 m ≠ BitVec.ofNat 64 n := by
  intro heq
  have h := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at h
  exact hne h

@[m5_st_pl ↓] theorem symtab_setPC (s : State) (p : BitVec 64) : (s.setPC p).symtab = s.symtab := by cases s; rfl
@[m5_st_pl ↓] theorem symtab_advancePC (s : State) : s.advancePC.symtab = s.symtab := by cases s; rfl
@[m5_st_pl ↓] theorem symtab_setPState (s : State) (ps : PState) : (s.setPState ps).symtab = s.symtab := by cases s; rfl
@[m5_st_pl ↓] theorem symtab_setMem (s : State) (m : Memory) : (s.setMem m).symtab = s.symtab := by cases s; rfl
@[m5_st_pl ↓] theorem symtab_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by cases s; cases r <;> rfl
@[m5_st_pl ↓] theorem symtab_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).symtab = s.symtab := by cases s; cases r <;> rfl
@[m5_st_pl ↓] theorem fs_setPC (s : State) (p : BitVec 64) : (s.setPC p).fs = s.fs := by cases s; rfl
@[m5_st_pl ↓] theorem fs_advancePC (s : State) : s.advancePC.fs = s.fs := by cases s; rfl
@[m5_st_pl ↓] theorem fs_setPState (s : State) (ps : PState) : (s.setPState ps).fs = s.fs := by cases s; rfl
@[m5_st_pl ↓] theorem fs_setMem (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
@[m5_st_pl ↓] theorem fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl
@[m5_st_pl ↓] theorem fs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := by cases s; cases r <;> rfl
@[m5_st_pl ↓] theorem trace_setPC (s : State) (p : BitVec 64) : (s.setPC p).trace = s.trace := by cases s; rfl
@[m5_st_pl ↓] theorem trace_advancePC (s : State) : s.advancePC.trace = s.trace := by cases s; rfl
@[m5_st_pl ↓] theorem trace_setPState (s : State) (ps : PState) : (s.setPState ps).trace = s.trace := by cases s; rfl
@[m5_st_pl ↓] theorem trace_setMem (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by cases s; rfl
@[m5_st_pl ↓] theorem trace_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := by cases s; cases r <;> rfl
@[m5_st_pl ↓] theorem trace_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := by cases s; cases r <;> rfl
@[m5_st_pl ↓] theorem vregs_setPC (s : State) (p : BitVec 64) : (s.setPC p).vregs = s.vregs := by cases s; rfl
@[m5_st_pl ↓] theorem vregs_advancePC (s : State) : s.advancePC.vregs = s.vregs := by cases s; rfl
@[m5_st_pl ↓] theorem vregs_setPState (s : State) (ps : PState) : (s.setPState ps).vregs = s.vregs := by cases s; rfl
@[m5_st_pl ↓] theorem vregs_setMem (s : State) (m : Memory) : (s.setMem m).vregs = s.vregs := by cases s; rfl
@[m5_st_pl ↓] theorem vregs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).vregs = s.vregs := by cases s; cases r <;> rfl
@[m5_st_pl ↓] theorem vregs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).vregs = s.vregs := by cases s; cases r <;> rfl
attribute [m5_st_pl ↓] ProofLib.reduceStateSP ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32 ProofLib.reduceStateReadReg ProofLib.reduceStateMem
  ProofLib.reduceRegFromZRBits ProofLib.reduceRegFromSPBits
  ProofLib.reduceStateWriteRegXzr

theorem readReg64_setPC_st (s : State) (p : BitVec 64) (r : Reg) :
    (s.setPC p).readReg64 r = s.readReg64 r := by cases s; rfl
theorem readReg64_advancePC_st (s : State) (r : Reg) :
    s.advancePC.readReg64 r = s.readReg64 r := by cases s; rfl
theorem readReg64_setPState_st (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases s; rfl
theorem readReg64_setMem_st (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl

theorem read_cs_x0 {r : BitVec 5} (hlo : 19 ≤ r.toNat) (hhi : r.toNat ≤ 29) (s : State) (v : BitVec 64) :
    (s.writeReg64 (.gpr 0#5) v).readReg64 (.gpr r) = s.readReg64 (.gpr r) :=
  readReg64_writeReg64_callee_saved s (.gpr 0#5) v (by decide) r hlo hhi
theorem read_cs_x1 {r : BitVec 5} (hlo : 19 ≤ r.toNat) (hhi : r.toNat ≤ 29) (s : State) (v : BitVec 64) :
    (s.writeReg64 (.gpr 1#5) v).readReg64 (.gpr r) = s.readReg64 (.gpr r) :=
  readReg64_writeReg64_callee_saved s (.gpr 1#5) v (by decide) r hlo hhi
theorem read_cs_x2 {r : BitVec 5} (hlo : 19 ≤ r.toNat) (hhi : r.toNat ≤ 29) (s : State) (v : BitVec 64) :
    (s.writeReg64 (.gpr 2#5) v).readReg64 (.gpr r) = s.readReg64 (.gpr r) :=
  readReg64_writeReg64_callee_saved s (.gpr 2#5) v (by decide) r hlo hhi
theorem read_cs_x8 {r : BitVec 5} (hlo : 19 ≤ r.toNat) (hhi : r.toNat ≤ 29) (s : State) (v : BitVec 64) :
    (s.writeReg64 (.gpr 8#5) v).readReg64 (.gpr r) = s.readReg64 (.gpr r) :=
  readReg64_writeReg64_callee_saved s (.gpr 8#5) v (by decide) r hlo hhi
theorem read_cs_x9 {r : BitVec 5} (hlo : 19 ≤ r.toNat) (hhi : r.toNat ≤ 29) (s : State) (v : BitVec 64) :
    (s.writeReg64 (.gpr 9#5) v).readReg64 (.gpr r) = s.readReg64 (.gpr r) :=
  readReg64_writeReg64_callee_saved s (.gpr 9#5) v (by decide) r hlo hhi
theorem read_cs_x30 {r : BitVec 5} (hlo : 19 ≤ r.toNat) (hhi : r.toNat ≤ 29) (s : State) (v : BitVec 64) :
    (s.writeReg64 (.gpr 30#5) v).readReg64 (.gpr r) = s.readReg64 (.gpr r) :=
  readReg64_writeReg64_callee_saved s (.gpr 30#5) v (by decide) r hlo hhi

/-- Outside-in spine peel for symbolic callee-saved GPR reads `s'.readReg64 (.gpr r) = s.readReg64 (.gpr r)`. -/
macro "m5_cs_pl " hlo:ident hhi:ident : tactic =>
  `(tactic| (
    repeat first
      | rw [M5DropPlacedHelpers.readReg64_setPC_st]
      | rw [M5DropPlacedHelpers.readReg64_advancePC_st]
      | rw [M5DropPlacedHelpers.readReg64_setPState_st]
      | rw [M5DropPlacedHelpers.readReg64_setMem_st]
      | rw [State.writeReg32]
      | rw [M5DropPlacedHelpers.read_cs_x0 $hlo $hhi]
      | rw [M5DropPlacedHelpers.read_cs_x1 $hlo $hhi]
      | rw [M5DropPlacedHelpers.read_cs_x2 $hlo $hhi]
      | rw [M5DropPlacedHelpers.read_cs_x8 $hlo $hhi]
      | rw [M5DropPlacedHelpers.read_cs_x9 $hlo $hhi]
      | rw [M5DropPlacedHelpers.read_cs_x30 $hlo $hhi]))

/-- Run a pure `SepWP` segment to `mid` and continue with `SepWPp` to `ret`. -/
theorem seq_sepWP_pl {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s P
      (fun sm Pm => sm.pc = mid → sm.status = .Running → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (mid := mid) (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial
    (SepWP.mono h fun _ _ hpcm hrunm hk _ => hk hpcm hrunm)

theorem vecHeader_to_memRegion24 (a cap ptr len : BitVec 64) :
    vecHeader a cap ptr len ⊢ memRegion a 24 := by
  unfold vecHeader
  have h0 : (a ↦₆₄ cap) ⊢ memRegion a 8 := pointsTo64_entails_memRegion a cap
  have h1 : ((a + 8#64) ↦₆₄ ptr) ⊢ memRegion (a + 8#64) 8 :=
    pointsTo64_entails_memRegion (a + 8#64) ptr
  have h2 : ((a + 16#64) ↦₆₄ len) ⊢ memRegion (a + 16#64) 8 :=
    pointsTo64_entails_memRegion (a + 16#64) len
  refine Entails.trans (sepConj_mono h0 (sepConj_mono h1 h2)) ?_
  have h12 : memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8 = memRegion (a + 8#64) 16 :=
    (ProofLib.memRegion_split' rfl (by simp only [BitVec.add_assoc, BitVec.reduceAdd]) (by decide)).symm
  have h012 : memRegion a 8 ∗ memRegion (a + 8#64) 16 = memRegion a 24 :=
    (ProofLib.memRegion_split' rfl rfl (by decide)).symm
  rw [h12, h012]
  exact Entails.refl _

theorem strRefAt_to_memRegion16_anyHeap (a : BitVec 64) (lit : List (BitVec 8)) :
    strRefAt a lit ⊢ memRegion a 16 ∗ anyHeap := by
  unfold strRefAt
  apply Entails.sepExists_elim
  intro p
  have h1 : (a ↦₆₄ p) ⊢ memRegion a 8 := pointsTo64_entails_memRegion a p
  have h2 : ((a + asm64% boxSliceLenOff) ↦₆₄ BitVec.ofNat 64 lit.length) ⊢
      memRegion (a + 8#64) 8 :=
    pointsTo64_entails_memRegion (a + 8#64) (BitVec.ofNat 64 lit.length)
  have h12 : memRegion a 8 ∗ memRegion (a + 8#64) 8 = memRegion a 16 :=
    (ProofLib.memRegion_split' (n := 8) (k := 8) (by decide) rfl (by decide)).symm
  refine Entails.trans
    (sepConj_mono h1 (sepConj_mono h2 (ProofLib.entails_anyHeap _))) ?_
  rw [← sepConj_assoc, h12]
  exact Entails.refl _

def dirVecAt (A : RustAlloc) (d : BitVec 64) (g : DirGhost) : SepProp :=
  RustHeap.vecOf A 48 8 (dirEntryAt A) d g.changed ∗ memRegion (d + 0x18#64) 16

def dirsVecAt (A : RustAlloc) (a : BitVec 64) : List DirGhost → SepProp
  | [] => emp
  | d :: ds => dirVecAt A a d ∗ dirsVecAt A (a + 0x28#64) ds

theorem dirAt_absorb (A : RustAlloc) (d : BitVec 64) (g : DirGhost) :
    dirAt A d g ∗ anyHeap ⊢ dirVecAt A d g ∗ anyHeap := by
  unfold dirAt dirVecAt
  rw [sepConj_assoc, sepConj_assoc]
  exact sepConj_mono_right (Entails.trans
    (sepConj_mono_left (strRefAt_to_memRegion16_anyHeap (d + 0x18#64) g.path))
    (by rw [sepConj_assoc]; exact sepConj_mono_right (ProofLib.entails_anyHeap _)))

theorem dirsAt_absorb (A : RustAlloc) (a : BitVec 64) (ds : List DirGhost) :
    dirsAt A a ds ∗ anyHeap ⊢ dirsVecAt A a ds ∗ anyHeap := by
  induction ds generalizing a with
  | nil =>
    simp only [dirsAt, dirsVecAt]
    exact Entails.refl _
  | cons d ds ih =>
    simp only [dirsAt, dirsVecAt]
    have h1 :
        (dirAt A a d ∗ dirsAt A (a + 0x28#64) ds) ∗ anyHeap =
          dirsAt A (a + 0x28#64) ds ∗ (dirAt A a d ∗ anyHeap) := by
      ac_rfl
    have h2 :
        (dirVecAt A a d ∗ dirsVecAt A (a + 0x28#64) ds) ∗ anyHeap =
          dirVecAt A a d ∗ (dirsVecAt A (a + 0x28#64) ds ∗ anyHeap) := by
      ac_rfl
    rw [h1, h2]
    refine Entails.trans (sepConj_mono_right (dirAt_absorb A a d)) ?_
    have h3 :
        dirsAt A (a + 0x28#64) ds ∗ (dirVecAt A a d ∗ anyHeap) =
          dirVecAt A a d ∗ (dirsAt A (a + 0x28#64) ds ∗ anyHeap) := by
      ac_rfl
    rw [h3]
    exact sepConj_mono_right (ih (a + 0x28#64))

theorem calleeSaved_read_gpr {s sm : State} (hcs : CalleeSavedPreserved s sm)
    (r : BitVec 5) (hlo : 19 ≤ r.toNat) (hhi : r.toNat ≤ 29) :
    sm.readReg64 (.gpr r) = s.readReg64 (.gpr r) := by
  have hr :
      r = 19#5 ∨ r = 20#5 ∨ r = 21#5 ∨ r = 22#5 ∨ r = 23#5 ∨ r = 24#5 ∨
      r = 25#5 ∨ r = 26#5 ∨ r = 27#5 ∨ r = 28#5 ∨ r = 29#5 := by
    have : r.toNat = 19 ∨ r.toNat = 20 ∨ r.toNat = 21 ∨ r.toNat = 22 ∨ r.toNat = 23 ∨
        r.toNat = 24 ∨ r.toNat = 25 ∨ r.toNat = 26 ∨ r.toNat = 27 ∨ r.toNat = 28 ∨
        r.toNat = 29 := by omega
    rcases this with h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq h)
    · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))
    · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq h))))))))))
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hcs.1
  · exact hcs.2.1
  · exact hcs.2.2.1
  · exact hcs.2.2.2.1
  · exact hcs.2.2.2.2.1
  · exact hcs.2.2.2.2.2.1
  · exact hcs.2.2.2.2.2.2.1
  · exact hcs.2.2.2.2.2.2.2.1
  · exact hcs.2.2.2.2.2.2.2.2.1
  · exact hcs.2.2.2.2.2.2.2.2.2.1
  · exact hcs.2.2.2.2.2.2.2.2.2.2.1

end M5DropPlacedHelpers

open M5DropPlacedHelpers

theorem mPcPlaced_add [LibsignalPlacement] (off d : Nat) :
    mPcPlaced off + BitVec.ofNat 64 d = mPcPlaced (off + d) := by
  simp only [mPcPlaced, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem mPcPlaced_add_sub [LibsignalPlacement] {off target : Nat} (hle : off ≤ target) :
    mPcPlaced off + BitVec.ofNat 64 (target - off) = mPcPlaced target := by
  rw [mPcPlaced_add, Nat.add_sub_cancel' hle]

theorem mPcPlaced_sub [LibsignalPlacement] {off d : Nat} (hle : d ≤ off) :
    mPcPlaced off + (- BitVec.ofNat 64 d) = mPcPlaced (off - d) := by
  have heq : off = (off - d) + d := by omega
  conv_lhs => rw [heq, ← mPcPlaced_add (off - d) d]
  rw [BitVec.add_assoc, BitVec.add_neg_eq_sub, BitVec.sub_self, BitVec.add_zero]

theorem mPcPlaced_bl_dealloc [LibsignalPlacement] (off : Nat) :
    mPcPlaced off + ((lsρ lsRustDeallocSymCli - (blkPl_617).base) - BitVec.ofNat 64 off) =
      lsρ lsRustDeallocSymCli := by
  change (lsmpl.base 617 + BitVec.ofNat 64 off) +
      ((lsρ lsRustDeallocSymCli - lsmpl.base 617) - BitVec.ofNat 64 off) =
    lsρ lsRustDeallocSymCli
  bv_bits

theorem codeOk_pure {CodeOk : Memory → Prop} {s s' : State}
    (hinv : CodeOk s.mem)
    (hmem : s'.mem = s.mem := by simp only [m5_st_pl]) :
    CodeOk s'.mem :=
  hmem ▸ hinv

theorem InMainPlaced.step_pure [LibsignalPlacement] {CodeOk : Memory → Prop}
    {s0 s s' : State} {k k' : Nat}
    (hs : InMainPlaced CodeOk s0 s k)
    (hpc : s'.pc = mPcPlaced k')
    (hrun : s'.status = .Running)
    (hsp : s'.sp = s.sp := by simp only [m5_st_pl])
    (hfp : s'.readReg64 .fp = s.readReg64 .fp := by simp only [m5_st_pl])
    (hmem : s'.mem = s.mem := by simp only [m5_st_pl])
    (hvregs : calleeSavedVRegs s' = calleeSavedVRegs s := by
      simp only [calleeSavedVRegs, m5_st_pl]) :
    InMainPlaced CodeOk s0 s' k' :=
  hs.mk_step hpc hrun hsp hfp (codeOk_pure hs.inv hmem) hvregs

theorem InMainPlaced.step_store [LibsignalPlacement] {CodeOk : Memory → Prop}
    {s0 s s' : State} {k k' : Nat}
    (hs : InMainPlaced CodeOk s0 s k)
    (hpc : s'.pc = mPcPlaced k')
    (hrun : s'.status = .Running)
    (hinv : CodeOk s'.mem)
    (hsp : s'.sp = s.sp := by simp only [m5_st_pl])
    (hfp : s'.readReg64 .fp = s.readReg64 .fp := by simp only [m5_st_pl])
    (hvregs : calleeSavedVRegs s' = calleeSavedVRegs s := by
      simp only [calleeSavedVRegs, m5_st_pl]) :
    InMainPlaced CodeOk s0 s' k' :=
  hs.mk_step hpc hrun hsp hfp hinv hvregs

/-- Run a `SepWP` segment to `mid`, carrying `CodeOk` across any memory stores. -/
theorem seq_frozen_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => sm.pc = mid → sm.status = .Running → CodeOk sm.mem →
        SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont hpcm hrunm (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

/-- Execute a `dealloc` call at `lsρ lsRustDeallocSymCli` inside `SepWPp`, preserving `CodeOk`,
`sm.fs = s.fs`, `sm.trace = s.trace`, and `CalleeSavedPreserved s sm`. -/
theorem step_dealloc_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks}
    {ret retPc : BitVec 64} {s : State}
    {ptr : BitVec 64} {size align sub : Nat}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A H)
    (hext : extHookStack ≤ sub) (hsub64 : sub ≤ 2 ^ 64)
    (hinv : CodeOk s.mem)
    (hpc : s.pc = lsρ lsRustDeallocSymCli) (hrun : s.status = .Running)
    (hal : s.spAligned = true) (hlr : s.readReg64 .lr = retPc)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hlay : LayoutOk size align)
    (hP : P ⊢ A.live ptr size align ∗ memRegion ptr size ∗ A.pool ∗ stackAt s.sp sub ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = retPc → sm.status = .Running → sm.sp = s.sp →
      CalleeSavedPreserved s sm → CodeOk sm.mem →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm (A.pool ∗ stackAt s.sp sub ∗ F) Q Qp oom) :
    SepWPp (mProgPlaced H) ret s P Q Qp oom := by
  let slack := memRegion (s.sp - BitVec.ofNat 64 sub) (sub - extHookStack)
  have hsplit := stackAt_split_ge s.sp hext hsub64
  refine main_call_rocl (x := (ptr, size, align)) (main_dealloc_fs_placed_ok hA)
    hinv hpc hrun hal hlr (F := slack ∗ F) ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
    simp only [sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hlay⟩
    exact Entails.of_eq (by dsimp +zetaDelta only [slack]; ac_rfl)
  · intro sm hinv' hpcm hrunm hspm hcsm
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hfsm => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm hpcm hrunm hspm hcsm hinv' hfsm htrm)
    rw [hsplit]
    exact Entails.of_eq (by dsimp +zetaDelta only [slack]; ac_rfl)

end CryptoVerification.SignalSession.Cli.MainHops
