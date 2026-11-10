/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.Layout
public import CaseStudies.Hashbrown.Proofs.Externs
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.SepLogic.WP.StepsProcessLse
public import ProofLib.SepLogic.WP.StepsSimd
public import ProofLib.SepLogic.WPFrozen
public import ProofLib.StdStartup.NonVmSteps
public import ProofLib.StdStartup.StdDetect

/-!
# Placement-Generic `memcpy`, `memset`, and Disjoint `memmove`

Placement-generic verification of static `musl` AArch64 `memcpy`, `memset`, and disjoint `memmove`
relative to `C.std.memcpyAddr`, `C.std.memsetAddr`, and `C.memmoveAddr`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Rust ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CaseStudies.Hashbrown.Proofs

/-! ## Symbolic Instruction Lists and `HbMemOpsCode` -/

/-- Instruction sequence (`99` insns, `396` bytes) for static `musl` AArch64 `memcpy` at `C.std.memcpyAddr`. -/
def hbMemcpyInstrs : List Instr := decodeWords [
  0x8b020024#32, 0x8b020005#32, 0xf102005f#32, 0x540007a8#32, 0xf100805f#32, 0x540003e8#32, 0xf100405f#32, 0x540000c3#32, 0xa9401c26#32, 0xa97f348c#32, 0xa9001c06#32,
  0xa93f34ac#32, 0xd65f03c0#32, 0x361800e2#32, 0xf9400026#32, 0xf85f8087#32, 0xf9000006#32, 0xf81f80a7#32, 0xd65f03c0#32, 0xd503201f#32, 0x361000c2#32, 0xb9400026#32,
  0xb85fc088#32, 0xb9000006#32, 0xb81fc0a8#32, 0xd65f03c0#32, 0xb4000102#32, 0xd341fc4e#32, 0x39400026#32, 0x385ff08a#32, 0x386e6828#32, 0x39000006#32, 0x382e6808#32,
  0x381ff0aa#32, 0xd65f03c0#32, 0xd503201f#32, 0xa9401c26#32, 0xa9412428#32, 0xa97e2c8a#32, 0xa97f348c#32, 0xf101005f#32, 0x540000e8#32, 0xa9001c06#32, 0xa9012408#32,
  0xa93e2caa#32, 0xa93f34ac#32, 0xd65f03c0#32, 0xd503201f#32, 0xa9423c2e#32, 0xa9434430#32, 0xf101805f#32, 0x540000a9#32, 0xa97c0c82#32, 0xa97d1081#32, 0xa93c0ca2#32,
  0xa93d10a1#32, 0xa9001c06#32, 0xa9012408#32, 0xa9023c0e#32, 0xa9034410#32, 0xa93e2caa#32, 0xa93f34ac#32, 0xd65f03c0#32, 0xd503201f#32, 0xa940342c#32, 0x92400c0e#32,
  0x927cec03#32, 0xcb0e0021#32, 0x8b0e0042#32, 0xa9411c26#32, 0xa900340c#32, 0xa9422428#32, 0xa9432c2a#32, 0xa9c4342c#32, 0xf1024042#32, 0x54000169#32, 0xa9011c66#32,
  0xa9411c26#32, 0xa9022468#32, 0xa9422428#32, 0xa9032c6a#32, 0xa9432c2a#32, 0xa984346c#32, 0xa9c4342c#32, 0xf1010042#32, 0x54fffee8#32, 0xa97c3c8e#32, 0xa9011c66#32,
  0xa97d1c86#32, 0xa9022468#32, 0xa97e2488#32, 0xa9032c6a#32, 0xa97f2c8a#32, 0xa904346c#32, 0xa93c3cae#32, 0xa93d1ca6#32, 0xa93e24a8#32, 0xa93f2caa#32, 0xd65f03c0#32]

/-- Instruction sequence (`65` insns, `260` bytes) for static `musl` AArch64 `memset` at `C.std.memsetAddr`. -/
def hbMemsetInstrs : List Instr := decodeWords [
  0x4e010c20#32, 0x8b020004#32, 0xf101805f#32, 0x540003a8#32, 0xf100405f#32, 0x54000202#32, 0x4e083c01#32, 0x361800a2#32, 0xf9000001#32, 0xf81f8081#32, 0xd65f03c0#32,
  0xd503201f#32, 0x36100082#32, 0xb9000001#32, 0xb81fc081#32, 0xd65f03c0#32, 0xb4000082#32, 0x39000001#32, 0x36080042#32, 0x781fe081#32, 0xd65f03c0#32, 0x3d800000#32,
  0x373000c2#32, 0x3c9f0080#32, 0x36280062#32, 0x3d800400#32, 0x3c9e0080#32, 0xd65f03c0#32, 0x3d800400#32, 0xad010000#32, 0xad3f0080#32, 0xd65f03c0#32, 0x12001c21#32,
  0x927cec03#32, 0x3d800000#32, 0xf102805f#32, 0x7a402820#32, 0x54000241#32, 0xd53b00e5#32, 0x924010a5#32, 0xf10010bf#32, 0x540001c1#32, 0x3d800460#32, 0xad010060#32,
  0x927ae463#32, 0xcb030082#32, 0xd1020042#32, 0xd503201f#32, 0x91010063#32, 0xd50b7423#32, 0xf1010042#32, 0x54ffffa8#32, 0xad3e0080#32, 0xad3f0080#32, 0xd65f03c0#32,
  0xcb030082#32, 0xd1004063#32, 0xd1014042#32, 0xad010060#32, 0xad820060#32, 0xf1010042#32, 0x54ffffa8#32, 0xad3e0080#32, 0xad3f0080#32, 0xd65f03c0#32]

/-- Instruction sequence (`74` insns, `296` bytes) for static `musl` AArch64 `memmove` at `C.memmoveAddr`; index `26` (`+0x68`) tail-calls `C.std.memcpyAddr`. -/
def hbMemmoveInstrs (C : HbCliLayout) : List Instr := decodeWords [
  0xaa0003e7#32, 0xaa0103e4#32, 0xeb01001f#32, 0xaa0203e3#32, 0x54000880#32, 0xcb020025#32, 0xcb0207e6#32, 0xcb0000a8#32, 0xeb06011f#32, 0x54000229#32, 0xca000021#32,
  0xeb04001f#32, 0x92400821#32, 0x54000442#32, 0xb5000321#32, 0x8b0204a2#32, 0x8b030083#32, 0xaa0003e1#32, 0xcb040040#32, 0xf2400825#32, 0x540000e0#32, 0xeb03009f#32,
  0x54000640#32, 0x38401485#32, 0x38001425#32, 0x17fffff9#32] ++ [.b (C.std.memcpyAddr - (C.memmoveAddr + 0x68#64))] ++ decodeWords [
  0xd343fc03#32, 0x927df006#32, 0x14000004#32, 0xf8656882#32, 0xf8256822#32, 0x910020a5#32, 0xeb0600bf#32, 0x54ffff81#32, 0xcb030c03#32, 0x8b050022#32, 0x8b050084#32,
  0x14000002#32, 0xaa0003e2#32, 0xd2800001#32, 0xeb01007f#32, 0x540003c0#32, 0x38616885#32, 0x38216845#32, 0x91000421#32, 0x17fffffb#32, 0xb40000c1#32, 0xb4000303#32,
  0xd1000463#32, 0x38636881#32, 0x382368e1#32, 0x17fffffc#32, 0x8b0300e1#32, 0xd1000462#32, 0xf240083f#32, 0x540000c0#32, 0xb40001e3#32, 0x38626881#32, 0xaa0203e3#32,
  0x382268e1#32, 0x17fffff8#32, 0x92400862#32, 0xaa0303e1#32, 0x14000003#32, 0xf8616880#32, 0xf82168e0#32, 0xeb02003f#32, 0xd1002021#32, 0x54ffff81#32, 0x92400863#32,
  0x17ffffe9#32, 0xaa0703e0#32, 0xd65f03c0#32]

/-- Instruction-presence bundle for `memcpy`, `memset`, and `memmove` on program `P`. -/
structure HbMemOpsCode (P : Program) (C : HbCliLayout) : Prop where
  memcpy  : hasInstrs P C.std.memcpyAddr hbMemcpyInstrs
  memset  : hasInstrs P C.std.memsetAddr hbMemsetInstrs
  memmove : hasInstrs P C.memmoveAddr (hbMemmoveInstrs C)

theorem HbMemOpsCode.withSvc {P : Program} {C : HbCliLayout} (hc : HbMemOpsCode P C) (svc : State → State) : HbMemOpsCode (P.withSvc svc) C where
  memcpy  := fun i hi => by simpa [Program.withSvc_fetch] using hc.memcpy i hi
  memset  := fun i hi => by simpa [Program.withSvc_fetch] using hc.memset i hi
  memmove := fun i hi => by simpa [Program.withSvc_fetch] using hc.memmove i hi

/-- $O(k \log N)$ boolean `WordTree` validator for `HbMemOpsCode`. -/
def checkHbMemOpsCode (C : HbCliLayout) (base : BitVec 64) (t : WordTree) : Bool :=
  let offMemcpy := (C.std.memcpyAddr - base).toNat; let offMemset := (C.std.memsetAddr - base).toNat; let offMemmove := (C.memmoveAddr - base).toNat
  decide (base + BitVec.ofNat 64 offMemcpy = C.std.memcpyAddr ∧ offMemcpy + 4 * hbMemcpyInstrs.length < 2 ^ 64 ∧
    base + BitVec.ofNat 64 offMemset = C.std.memsetAddr ∧ offMemset + 4 * hbMemsetInstrs.length < 2 ^ 64 ∧
    base + BitVec.ofNat 64 offMemmove = C.memmoveAddr ∧ offMemmove + 4 * (hbMemmoveInstrs C).length < 2 ^ 64) &&
  checkInstrsAt t offMemcpy hbMemcpyInstrs && checkInstrsAt t offMemset hbMemsetInstrs && checkInstrsAt t offMemmove (hbMemmoveInstrs C)

theorem hbMemOpsCode_of_wordTree {P : Program} {C : HbCliLayout} {t : WordTree} (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl) (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkHbMemOpsCode C P.base t = true) : HbMemOpsCode P C := by
  unfold checkHbMemOpsCode at hok; simp only [Bool.and_eq_true, decide_eq_true_eq] at hok; rcases hok with ⟨⟨⟨⟨hb1, hbd1, hb2, hbd2, hb3, hbd3⟩, hc1⟩, hc2⟩, hc3⟩
  exact ⟨hasInstrs_of_wordTree n hcode hwf hb1 hbd1 hext hovr hc1, hasInstrs_of_wordTree n hcode hwf hb2 hbd2 hext hovr hc2,
    hasInstrs_of_wordTree n hcode hwf hb3 hbd3 hext hovr hc3⟩

/-! ## State-Preservation and Byte-Slice Step Helpers -/

private def MemOpsInvariant (s0 sf : State) : Prop := sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ StdStatePreserved s0 sf
private theorem MemOpsInvariant.rfl (s : State) : MemOpsInvariant s s := ⟨Eq.refl _, CalleeSavedPreserved.rfl s, StdStatePreserved.rfl s⟩
private theorem stdStatePreserved_setPC (s0 s : State) (pc : BitVec 64) : StdStatePreserved s0 (s.setPC pc) ↔ StdStatePreserved s0 s := by cases s; rfl
private theorem sepWP_with_codeLoaded {P : Program} {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) → P.CodeLoaded s.mem → SepWP P target_pc s Pre post oom) : SepWP P target_pc s Pre post oom := by
  unfold SepWP; intro R hm hL; have hwp := h R hm hL; unfold SepWP at hwp; exact hwp R hm hL

private theorem codeLoaded_perm_of_hasInstrs {P : Program} {addr : BitVec 64} {instrs : List Instr} {m : Memory} (hL : P.CodeLoaded m) (hc : hasInstrs P addr instrs) :
    ∀ k < 4 * instrs.length, m.perm (addr + BitVec.ofNat 64 k) = some .rx := by
  rw [Program.codeLoaded_iff] at hL; rcases hL with ⟨_, _, hbytes⟩; intro k hk
  let i := k / 4; let b := k % 4; have hf := hc i (by omega); unfold Program.fetch at hf; split at hf
  · cases hf
  · simp only [Option.bind_eq_some_iff] at hf; rcases hf with ⟨w, hrw, _⟩; unfold Program.readWordOff at hrw; split at hrw
    · cases hrw
    · split at hrw
      · rename_i b0 b1 b2 b3 rest hdrop; let off := ((addr + BitVec.ofNat 64 (4 * i)) - P.base).toNat
        have hlen_drop : (P.code.drop off).length = P.code.length - off := List.length_drop; rw [hdrop] at hlen_drop; have hp := (hbytes (off + b) (by simp at hlen_drop; omega)).2.1
        have haddr_eq : P.base + BitVec.ofNat 64 (off + b) = addr + BitVec.ofNat 64 k := by
          rw [BitVec.ofNat_add, ← BitVec.add_assoc, sepBytesOff_toNat, show P.base + ((addr + BitVec.ofNat 64 (4 * i)) - P.base) = addr + BitVec.ofNat 64 (4 * i) from by bv_lin, BitVec.add_assoc, ← BitVec.ofNat_add, show 4 * i + b = k from by omega]
        rwa [← haddr_eq]
      · cases hrw
private theorem writable_len_add_code_le {P : Program} {addr dst : BitVec 64} {instrs : List Instr} {bs0 : List (BitVec 8)} {R : SepProp} {m : Memory}
    (hL : P.CodeLoaded m) (hc : hasInstrs P addr instrs) (hm : m ⊨ (dst ↦ₛ bs0) ∗ R) (hlen : bs0.length ≤ 2 ^ 64) (hcode : 4 * instrs.length ≤ 2 ^ 64) : bs0.length + 4 * instrs.length ≤ 2 ^ 64 := by
  apply Classical.byContradiction; intro hgt; have hrx := codeLoaded_perm_of_hasInstrs hL hc
  have hdisj : ∀ j < bs0.length, ∀ k < 4 * instrs.length, dst + BitVec.ofNat 64 j ≠ addr + BitVec.ofNat 64 k := by
    intro j hj k hk heq; have hw := (SepStore8.of_pointsToBytes_here (dst + BitVec.ofNat 64 j) dst bs0 j 0#8 (by omega) rfl).writable hm
    dsimp [Memory.canWrite, Memory.allPerm] at hw; rw [heq, hrx k hk] at hw; cases hw
  let d := (addr - dst).toNat; have hd_lt : d < 2 ^ 64 := BitVec.toNat_lt_twoPow_of_le (Nat.le_refl _)
  by_cases hd : d < bs0.length
  · exact hdisj d hd 0 (by omega) (by rw [show BitVec.ofNat 64 d = addr - dst from sepBytesOff_toNat _]; bv_lin)
  · refine hdisj 0 (by omega) (2 ^ 64 - d) (by omega) (BitVec.eq_of_toNat_eq ?_)
    have hd_eq : d = (addr - dst).toNat := rfl; rw [BitVec.toNat_sub] at hd_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
private theorem mapSimdLanes_dup8_eq_bcast (x : BitVec 64) (b : BitVec 8) (hb : (x.truncate 32).truncate 8 = b) :
    mapSimdLanes true 8 0#128 (fun _ => (x.zeroExtend 128) &&& 0xff#128) = ByteSlice.bcast64 b ++ ByteSlice.bcast64 b := by
  have helem : (x.zeroExtend 128) &&& 0xff#128 = b.zeroExtend 128 := by subst hb; bv_bits
  rw [mapSimdLanes_true_8]; dsimp [mapLanes, laneMask, ByteSlice.bcast64, BitVec.replicate]; simp only [helem]; bv_bits
private theorem bcast128_lo (b : BitVec 8) : (ByteSlice.bcast64 b ++ ByteSlice.bcast64 b).extractLsb' 0 64 = ByteSlice.bcast64 b := by bv_bits
private theorem bcast128_hi (b : BitVec 8) : (ByteSlice.bcast64 b ++ ByteSlice.bcast64 b).extractLsb' 64 64 = ByteSlice.bcast64 b := by bv_bits
private theorem step_dup_v0_16b_w1 {P : Program} {target_pc pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {b : BitVec 8} (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.simdInsDup true false 1#5 1#4 1#5 0#5)) (hb : (s.readReg32 .x1).truncate 8 = b)
    (hnext : SepWP P target_pc ((s.writeVReg128 0#5 (ByteSlice.bcast64 b ++ ByteSlice.bcast64 b)).setPC (pc + 4#64)) Pre post) : SepWP P target_pc s Pre post := by
  refine SepWP.step_pure hpc hrun hfetch ?_ (by cases s; rfl) hnext; dsimp [Program.evalInst, execInstWithSvc, Reg.fromZRBits]
  rw [show ((s.setPC pc).readReg64 (.gpr 1#5)) = s.readReg64 .x1 from by cases s; rfl, mapSimdLanes_dup8_eq_bcast (s.readReg64 .x1) b hb]; cases s; rfl
private theorem step_umov_x1_v0_d0 {P : Program} {target_pc pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {b : BitVec 8} (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.simdInsDup true false 8#5 7#4 0#5 1#5)) (hv0 : s.readVReg128 0#5 = ByteSlice.bcast64 b ++ ByteSlice.bcast64 b)
    (hnext : SepWP P target_pc ((s.writeReg64 .x1 (ByteSlice.bcast64 b)).setPC (pc + 4#64)) Pre post) : SepWP P target_pc s Pre post := by
  refine SepWP.step_pure hpc hrun hfetch ?_ (by cases s; rfl) hnext
  have hlane : BitVec.setWidth 64 (getSimdLane (ByteSlice.bcast64 b ++ ByteSlice.bcast64 b) 64 0) = ByteSlice.bcast64 b := by dsimp [getSimdLane]; bv_bits
  dsimp [Program.evalInst, execInstWithSvc, Reg.fromZRBits, State.writeReg]; rw [show ((s.setPC pc).readVReg128 0#5) = s.readVReg128 0#5 from by cases s; rfl, hv0, hlane]; cases s; rfl
private theorem step_str8_perm {prog : Program} {target_pc pc ea : BitVec 64} {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .B8 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hval : (s.readReg32 rt).truncate 8 = val) (hstore : SepStore8 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post) : SepWP prog target_pc s P post := by
  unfold SepWP; intro R hm; have htrunc : (s.readReg64 rt).truncate 8 = val := bitvec_truncate8_truncate32 _ ▸ hval
  let m' := s.mem.write8 ea val; have hm' := hstore.store hm; have hcan := hstore.writable hm; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; have hn := hnext m' (Memory.perm_write8 s.mem ea val); unfold SepWP at hn; exact hn R hm'
private theorem step_str16_perm {prog : Program} {target_pc pc ea : BitVec 64} {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 16}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .H16 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hval : (s.readReg64 rt).truncate 16 = val) (hstore : SepStore16 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post) : SepWP prog target_pc s P post := by
  unfold SepWP; intro R hm; let m' := s.mem.write16 ea val; have hm' := hstore.store hm; have hcan := hstore.writable hm; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .H16 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; have hn := hnext m' (Memory.perm_write16 s.mem ea val); unfold SepWP at hn; exact hn R hm'
private theorem step_str32_perm {prog : Program} {target_pc pc ea : BitVec 64} {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .W32 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hval : s.readReg32 rt = val) (hstore : SepStore32 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post) : SepWP prog target_pc s P post := by
  unfold SepWP; intro R hm; have htrunc : (s.readReg64 rt).truncate 32 = val := hval
  let m' := s.mem.write32 ea val; have hm' := hstore.store hm; have hcan := hstore.writable hm; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .W32 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; have hn := hnext m' (Memory.perm_write32 s.mem ea val); unfold SepWP at hn; exact hn R hm'
private theorem step_str64_perm {prog : Program} {target_pc pc ea val : BitVec 64} {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .X64 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hval : s.readReg64 rt = val) (hstore : SepStore64 ea val P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P' post) : SepWP prog target_pc s P post := by
  unfold SepWP; intro R hm; let m' := s.mem.write64 ea val; have hm' := hstore.store hm; have hcan := hstore.writable hm; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m' := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]; have hn := hnext m' (Memory.perm_write64 s.mem ea val); unfold SepWP at hn; exact hn R hm'
private theorem step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64} {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2) (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post) : SepWP prog target_pc s P post := by
  unfold SepWP; intro R hm; let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm; have hm2 := hstore2.store hm1; have hcan1 := hstore1.writable hm; have hcan2 := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2; apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]; have hn := hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1)); unfold SepWP at hn; exact hn R hm2
private theorem step_strSimd128_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64} {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {vt : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.strSimd .Q128 vt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hv1 : (s.readVReg128 vt).extractLsb' 0 64 = v1) (hv2 : (s.readVReg128 vt).extractLsb' 64 64 = v2) (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P2 post) : SepWP prog target_pc s P post := by
  unfold SepWP; intro R hm; let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 := hstore1.store hm; have hm2 := hstore2.store hm1; have hcan1 := hstore1.writable hm; have hcan2 := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2; have hcan16 := Memory.canWrite_16_of_8_8 hcan1 (hea2.symm ▸ hcan2); apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.strSimd .Q128 vt addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m2 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, Memory.write128, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hea2, hv1, hv2, hcan16, SimdMemSize.bytes, hpc, m1, m2]
  rw [hstep]; have hn := hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1)); unfold SepWP at hn; exact hn R hm2

private theorem step_stpSimd128_perm {prog : Program} {target_pc pc ea ea2 ea3 ea4 v1 v2 v3 v4 : BitVec 64} {s : State} {P P1 P2 P3 P4 : SepProp}
    {post : State → SepProp → Prop} {vt1 vt2 : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .Q128 vt1 vt2 addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hea3 : ea + 16#64 = ea3) (hea4 : ea3 + 8#64 = ea4) (hv1 : (s.readVReg128 vt1).extractLsb' 0 64 = v1) (hv2 : (s.readVReg128 vt1).extractLsb' 64 64 = v2)
    (hv3 : (s.readVReg128 vt2).extractLsb' 0 64 = v3) (hv4 : (s.readVReg128 vt2).extractLsb' 64 64 = v4) (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hstore3 : SepStore64 ea3 v3 P2 P3) (hstore4 : SepStore64 ea4 v4 P3 P4)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P4 post) : SepWP prog target_pc s P post := by
  unfold SepWP; intro R hm; let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2; let m3 := m2.write64 ea3 v3; let m4 := m3.write64 ea4 v4
  have hm1 := hstore1.store hm; have hm2 := hstore2.store hm1; have hm3 := hstore3.store hm2; have hm4 := hstore4.store hm3
  have hcan1 := hstore1.writable hm; have hcan2 := hstore2.writable hm1; have hcan3 := hstore3.writable hm2; have hcan4 := hstore4.writable hm3
  repeat rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2; repeat rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan3; repeat rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan4
  have hcan_lo := Memory.canWrite_16_of_8_8 hcan1 (hea2.symm ▸ hcan2); have hcan_hi := Memory.canWrite_16_of_8_8 hcan3 (hea4.symm ▸ hcan4); apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stpSimd .Q128 vt1 vt2 addr) s = ((applyWriteback s wb).setPC (pc + 4#64)).setMem m4 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, Memory.write128, applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hea2, hea3, hea4, hv1, hv2, hv3, hv4, hcan_lo, hcan_hi, SimdMemSize.bytes, hpc, m1, m2, m3, m4]
  rw [hstep]; have hp4 : m4.perm = s.mem.perm := by simp only [m1, m2, m3, m4, Memory.perm_write64]
  have hn := hnext m4 hp4; unfold SepWP at hn; exact hn R hm4
private theorem step_dcZva_perm {prog : Program} {target_pc pc v ea : BitVec 64} {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {rt : Reg}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.dcZva rt)) (hval : s.readReg64 rt = v) (hea : v &&& ~~~63#64 = ea) (hstore : SepStoreDcZva ea P P')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc ((s.setPC (pc + 4#64)).setMem m') P' post) : SepWP prog target_pc s P post := by
  rcases hstore with ⟨⟨P1, P2, P3, P4, P5, P6, P7, s1, s2, s3, s4, s5, s6, s7, s8⟩⟩; unfold SepWP; intro R hm
  let ea2 := ea + 8#64; let ea3 := ea + 16#64; let ea4 := ea3 + 8#64; let ea5 := ea3 + 16#64; let ea6 := ea5 + 8#64; let ea7 := ea5 + 16#64; let ea8 := ea7 + 8#64
  let m1 := s.mem.write64 ea 0#64; let m2 := m1.write64 ea2 0#64; let m3 := m2.write64 ea3 0#64; let m4 := m3.write64 ea4 0#64
  let m5 := m4.write64 ea5 0#64; let m6 := m5.write64 ea6 0#64; let m7 := m6.write64 ea7 0#64; let m8 := m7.write64 ea8 0#64
  have hm1 : m1 ⊨ P1 ∗ R := s1.store hm; have hm2 : m2 ⊨ P2 ∗ R := s2.store hm1
  have hm3 : m3 ⊨ P3 ∗ R := s3.store hm2; have hm4 : m4 ⊨ P4 ∗ R := s4.store hm3
  have hm5 : m5 ⊨ P5 ∗ R := s5.store hm4; have hm6 : m6 ⊨ P6 ∗ R := s6.store hm5
  have hm7 : m7 ⊨ P7 ∗ R := s7.store hm6; have hm8 : m8 ⊨ P' ∗ R := s8.store hm7
  have hp1 : m1.perm = s.mem.perm := Memory.perm_write64 _ _ _
  have hp2 : m2.perm = s.mem.perm := (Memory.perm_write64 _ _ _).trans hp1
  have hp3 : m3.perm = s.mem.perm := (Memory.perm_write64 _ _ _).trans hp2
  have hp4 : m4.perm = s.mem.perm := (Memory.perm_write64 _ _ _).trans hp3
  have hp5 : m5.perm = s.mem.perm := (Memory.perm_write64 _ _ _).trans hp4
  have hp6 : m6.perm = s.mem.perm := (Memory.perm_write64 _ _ _).trans hp5
  have hp7 : m7.perm = s.mem.perm := (Memory.perm_write64 _ _ _).trans hp6
  have hp8 : m8.perm = s.mem.perm := (Memory.perm_write64 _ _ _).trans hp7
  have hcan1 : s.mem.canWrite ea 8 = true := s1.writable hm
  have hcan2 : s.mem.canWrite ea2 8 = true := Memory.canWrite_congr hp1 _ _ ▸ s2.writable hm1
  have hcan3 : s.mem.canWrite ea3 8 = true := Memory.canWrite_congr hp2 _ _ ▸ s3.writable hm2
  have hcan4 : s.mem.canWrite ea4 8 = true := Memory.canWrite_congr hp3 _ _ ▸ s4.writable hm3
  have hcan5 : s.mem.canWrite ea5 8 = true := Memory.canWrite_congr hp4 _ _ ▸ s5.writable hm4
  have hcan6 : s.mem.canWrite ea6 8 = true := Memory.canWrite_congr hp5 _ _ ▸ s6.writable hm5
  have hcan7 : s.mem.canWrite ea7 8 = true := Memory.canWrite_congr hp6 _ _ ▸ s7.writable hm6
  have hcan8 : s.mem.canWrite ea8 8 = true := Memory.canWrite_congr hp7 _ _ ▸ s8.writable hm7
  have hcan64 := Memory.canWrite_64_of_16_16_16_16 (Memory.canWrite_16_of_8_8 hcan1 hcan2) (Memory.canWrite_16_of_8_8 hcan3 hcan4) (Memory.canWrite_16_of_8_8 hcan5 hcan6) (Memory.canWrite_16_of_8_8 hcan7 hcan8)
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.dcZva rt) s = (s.setPC (pc + 4#64)).setMem m8 := by
    change execInst (.dcZva rt) s = (s.setPC (pc + 4#64)).setMem m8; rw [execInst_dcZva, hval, hea]
    dsimp only [Memory.write128, State.advancePC, State.setPC, State.setMem, m1, m2, m3, m4, m5, m6, m7, m8, ea2, ea3, ea4, ea5, ea6, ea7, ea8]
    rw [hcan64]; simp only [Bool.not_true, Bool.false_eq_true, reduceIte]; rw [hpc]; rfl
  rw [hstep]; have hn := hnext m8 hp8; unfold SepWP at hn; exact hn R hm8
private theorem step_fill_str8 {P : Program} {target_pc pc dst ea : BitVec 64} {s : State} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs0 : List (BitVec 8)} {b : BitVec 8} {p : Nat → Bool} {off : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.str .B8 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hb : (s.readReg32 rt).truncate 8 = b) (hoff : off + 1 ≤ bs0.length) (ha : dst + BitVec.ofNat 64 off = ea)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP P target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') (dst ↦ₛ ByteSlice.fillSet bs0 b (fun i => p i || decide (i = off))) post) : SepWP P target_pc s (dst ↦ₛ ByteSlice.fillSet bs0 b p) post := by
  have hst := SepStore8.of_pointsToBytes_here ea dst (ByteSlice.fillSet bs0 b p) off b (by rw [ByteSlice.fillSet_length]; exact hoff) ha
  rw [ByteSlice.write8_fillSet bs0 b p off hoff] at hst; exact step_str8_perm hpc hrun hfetch hsp haddr hb hst hnext
private theorem step_fill_str16 {P : Program} {target_pc pc dst ea : BitVec 64} {s : State} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs0 : List (BitVec 8)} {b : BitVec 8} {p : Nat → Bool} {off : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.str .H16 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hb : (s.readReg64 rt).truncate 16 = (ByteSlice.bcast64 b).setWidth 16) (hoff : off + 2 ≤ bs0.length) (ha : dst + BitVec.ofNat 64 off = ea)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP P target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') (dst ↦ₛ ByteSlice.fillSet bs0 b (fun i => p i || (decide (off ≤ i) && decide (i < off + 2)))) post) : SepWP P target_pc s (dst ↦ₛ ByteSlice.fillSet bs0 b p) post := by
  have hst := SepStore16.of_pointsToBytes_here ea dst (ByteSlice.fillSet bs0 b p) off ((ByteSlice.bcast64 b).setWidth 16) (by rw [ByteSlice.fillSet_length]; exact hoff) ha
  have hcol := ByteSlice.writeLE_fillSet 2 bs0 b p off ((ByteSlice.bcast64 b).setWidth 16) hoff (fun j hj => ByteSlice.extractLsb'_bcast64_trunc b 16 j (by omega) (by omega))
  rw [show ByteSlice.write16 = ByteSlice.writeLE 2 from rfl, hcol] at hst; exact step_str16_perm hpc hrun hfetch hsp haddr hb hst hnext
private theorem step_fill_str32 {P : Program} {target_pc pc dst ea : BitVec 64} {s : State} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs0 : List (BitVec 8)} {b : BitVec 8} {p : Nat → Bool} {off : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.str .W32 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hb : s.readReg32 rt = (ByteSlice.bcast64 b).setWidth 32) (hoff : off + 4 ≤ bs0.length) (ha : dst + BitVec.ofNat 64 off = ea)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP P target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') (dst ↦ₛ ByteSlice.fillSet bs0 b (fun i => p i || (decide (off ≤ i) && decide (i < off + 4)))) post) : SepWP P target_pc s (dst ↦ₛ ByteSlice.fillSet bs0 b p) post := by
  have hst := SepStore32.of_pointsToBytes_here ea dst (ByteSlice.fillSet bs0 b p) off ((ByteSlice.bcast64 b).setWidth 32) (by rw [ByteSlice.fillSet_length]; exact hoff) ha
  have hcol := ByteSlice.writeLE_fillSet 4 bs0 b p off ((ByteSlice.bcast64 b).setWidth 32) hoff (fun j hj => ByteSlice.extractLsb'_bcast64_trunc b 32 j (by omega) (by omega))
  rw [show ByteSlice.write32 = ByteSlice.writeLE 4 from rfl, hcol] at hst; exact step_str32_perm hpc hrun hfetch hsp haddr hb hst hnext
private theorem step_fill_str64 {P : Program} {target_pc pc dst ea : BitVec 64} {s : State} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs0 : List (BitVec 8)} {b : BitVec 8} {p : Nat → Bool} {off : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.str .X64 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hb : s.readReg64 rt = ByteSlice.bcast64 b) (hoff : off + 8 ≤ bs0.length) (ha : dst + BitVec.ofNat 64 off = ea)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP P target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') (dst ↦ₛ ByteSlice.fillSet bs0 b (fun i => p i || (decide (off ≤ i) && decide (i < off + 8)))) post) : SepWP P target_pc s (dst ↦ₛ ByteSlice.fillSet bs0 b p) post := by
  have hst := SepStore64.of_pointsToBytes_here ea dst (ByteSlice.fillSet bs0 b p) off (ByteSlice.bcast64 b) (by rw [ByteSlice.fillSet_length]; exact hoff) ha
  rw [ByteSlice.write64_fillSet_bcast64 bs0 b p off hoff] at hst; exact step_str64_perm hpc hrun hfetch hsp haddr hb hst hnext

private theorem step_fill_strSimd128 {P : Program} {target_pc pc dst ea : BitVec 64} {s : State} {post : State → SepProp → Prop} {vt : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs0 : List (BitVec 8)} {b : BitVec 8} {p : Nat → Bool} {off : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.strSimd .Q128 vt addr)) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hv : s.readVReg128 vt = ByteSlice.bcast64 b ++ ByteSlice.bcast64 b) (hoff : off + 16 ≤ bs0.length) (ha : dst + BitVec.ofNat 64 off = ea)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP P target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') (dst ↦ₛ ByteSlice.fillSet bs0 b (fun i => p i || (decide (off ≤ i) && decide (i < off + 16)))) post) : SepWP P target_pc s (dst ↦ₛ ByteSlice.fillSet bs0 b p) post := by
  let p1 := fun i => p i || (decide (off ≤ i) && decide (i < off + 8))
  have s1 := SepStore64.of_pointsToBytes_here ea dst (ByteSlice.fillSet bs0 b p) off (ByteSlice.bcast64 b) (by byte_region_len) ha; rw [ByteSlice.write64_fillSet_bcast64 bs0 b p off (by omega)] at s1
  have s2 := SepStore64.of_pointsToBytes_here (ea + 8#64) dst (ByteSlice.fillSet bs0 b p1) (off + 8) (ByteSlice.bcast64 b) (by byte_region_len) (by rw [← ha, BitVec.ofNat_add]; bv_lin)
  rw [show ByteSlice.write64 (ByteSlice.fillSet bs0 b p1) (off + 8) (ByteSlice.bcast64 b) = ByteSlice.fillSet bs0 b (fun i => p i || (decide (off ≤ i) && decide (i < off + 16))) from by rw [ByteSlice.write64_fillSet_bcast64 bs0 b p1 (off + 8) (by omega)]; dsimp [p1]; byte_region_eq] at s2
  exact step_strSimd128_perm hpc hrun hfetch hsp haddr rfl (by rw [hv, bcast128_lo]) (by rw [hv, bcast128_hi]) s1 s2 hnext
private theorem step_fill_stpSimd128 {P : Program} {target_pc pc dst ea : BitVec 64} {s : State} {post : State → SepProp → Prop} {vt1 vt2 : BitVec 5} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs0 : List (BitVec 8)} {b : BitVec 8} {p : Nat → Bool} {off : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.stpSimd .Q128 vt1 vt2 addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hv1 : s.readVReg128 vt1 = ByteSlice.bcast64 b ++ ByteSlice.bcast64 b) (hv2 : s.readVReg128 vt2 = ByteSlice.bcast64 b ++ ByteSlice.bcast64 b) (hoff : off + 32 ≤ bs0.length) (ha : dst + BitVec.ofNat 64 off = ea)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP P target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') (dst ↦ₛ ByteSlice.fillSet bs0 b (fun i => p i || (decide (off ≤ i) && decide (i < off + 32)))) post) : SepWP P target_pc s (dst ↦ₛ ByteSlice.fillSet bs0 b p) post := by
  let p1 := fun i => p i || (decide (off ≤ i) && decide (i < off + 8)); let p2 := fun i => p1 i || (decide (off + 8 ≤ i) && decide (i < off + 16)); let p3 := fun i => p2 i || (decide (off + 16 ≤ i) && decide (i < off + 24))
  have s1 := SepStore64.of_pointsToBytes_here ea dst (ByteSlice.fillSet bs0 b p) off (ByteSlice.bcast64 b) (by byte_region_len) ha; rw [ByteSlice.write64_fillSet_bcast64 bs0 b p off (by omega)] at s1
  have s2 := SepStore64.of_pointsToBytes_here (ea + 8#64) dst (ByteSlice.fillSet bs0 b p1) (off + 8) (ByteSlice.bcast64 b) (by byte_region_len) (by rw [← ha, BitVec.ofNat_add]; bv_lin); rw [ByteSlice.write64_fillSet_bcast64 bs0 b p1 (off + 8) (by omega)] at s2
  have s3 := SepStore64.of_pointsToBytes_here (ea + 16#64) dst (ByteSlice.fillSet bs0 b p2) (off + 16) (ByteSlice.bcast64 b) (by byte_region_len) (by rw [← ha, BitVec.ofNat_add]; bv_lin); rw [ByteSlice.write64_fillSet_bcast64 bs0 b p2 (off + 16) (by omega)] at s3
  have s4 := SepStore64.of_pointsToBytes_here ((ea + 16#64) + 8#64) dst (ByteSlice.fillSet bs0 b p3) (off + 24) (ByteSlice.bcast64 b) (by byte_region_len) (by rw [← ha, BitVec.ofNat_add]; bv_lin)
  rw [show ByteSlice.write64 (ByteSlice.fillSet bs0 b p3) (off + 24) (ByteSlice.bcast64 b) = ByteSlice.fillSet bs0 b (fun i => p i || (decide (off ≤ i) && decide (i < off + 32))) from by rw [ByteSlice.write64_fillSet_bcast64 bs0 b p3 (off + 24) (by omega)]; dsimp [p1, p2, p3]; byte_region_eq] at s4
  exact step_stpSimd128_perm hpc hrun hfetch hsp haddr rfl rfl rfl (by rw [hv1, bcast128_lo]) (by rw [hv1, bcast128_hi]) (by rw [hv2, bcast128_lo]) (by rw [hv2, bcast128_hi]) s1 s2 s3 s4 hnext
private theorem step_fill_dcZva {P : Program} {target_pc pc dst v ea : BitVec 64} {s : State} {post : State → SepProp → Prop} {rt : Reg} {bs0 : List (BitVec 8)} {p : Nat → Bool} {off : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.dcZva rt)) (hval : s.readReg64 rt = v) (hea : v &&& ~~~63#64 = ea) (hoff : off + 64 ≤ bs0.length) (ha : dst + BitVec.ofNat 64 off = ea)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP P target_pc ((s.setPC (pc + 4#64)).setMem m') (dst ↦ₛ ByteSlice.fillSet bs0 0#8 (fun i => p i || (decide (off ≤ i) && decide (i < off + 64)))) post) : SepWP P target_pc s (dst ↦ₛ ByteSlice.fillSet bs0 0#8 p) post := by
  have hst := SepStoreDcZva.of_pointsToBytes_here ea dst (ByteSlice.fillSet bs0 0#8 p) off (by byte_region_len) ha
  rw [ByteSlice.fillSet_fillSet] at hst; exact step_dcZva_perm hpc hrun hfetch hval hea hst hnext
private structure IsSrcBytes (src : BitVec 64) (bs : List (BitVec 8)) (S : SepProp) : Prop where
  load8 : ∀ {a : BitVec 64} {off : Nat} {L : SepProp}, off + 1 ≤ bs.length → src + BitVec.ofNat 64 off = a → SepLoad8 a (L ∗ S) (bs.getD off 0#8)
  load32 : ∀ {a : BitVec 64} {off : Nat} {L : SepProp}, off + 4 ≤ bs.length → src + BitVec.ofNat 64 off = a → SepLoad32 a (L ∗ S) (pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8))
  load64 : ∀ {a : BitVec 64} {off : Nat} {L : SepProp}, off + 8 ≤ bs.length → src + BitVec.ofNat 64 off = a → SepLoad64 a (L ∗ S) (ByteSlice.readLE bs off 8)
private theorem isSrcBytes_rw (src : BitVec 64) (bs : List (BitVec 8)) : IsSrcBytes src bs (src ↦ₛ bs) :=
  ⟨fun h ha => SepLoad8.right (SepLoad8.of_pointsToBytes (sepConj_emp _).symm h ha), fun h ha => SepLoad32.right (SepLoad32.of_pointsToBytes (sepConj_emp _).symm h ha), fun h ha => SepLoad64.right (SepLoad64.of_pointsToBytes_readLE (sepConj_emp _).symm h ha)⟩
private theorem isSrcBytes_ro (src : BitVec 64) (bs : List (BitVec 8)) : IsSrcBytes src bs (src ↦ᵣ bs) :=
  ⟨fun h ha => SepLoad8.right (SepLoad8.of_pointsToBytesRO (sepConj_emp _).symm h ha), fun h ha => SepLoad32.right (SepLoad32.of_pointsToBytesRO (sepConj_emp _).symm h ha), fun h ha => SepLoad64.right (SepLoad64.of_pointsToBytes_readLE_RO (sepConj_emp _).symm h ha)⟩
private theorem step_copy_str8 {P : Program} {target_pc pc dst ea : BitVec 64} {s : State} {S : SepProp} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs0 bs : List (BitVec 8)} {p : Nat → Bool} {off : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.str .B8 rt addr)) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hv : (s.readReg32 rt).truncate 8 = bs.getD off 0#8) (hoff : off + 1 ≤ bs0.length) (ha : dst + BitVec.ofNat 64 off = ea)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP P target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') ((dst ↦ₛ ByteSlice.copySet bs0 bs (fun i => p i || decide (i = off))) ∗ S) post) : SepWP P target_pc s ((dst ↦ₛ ByteSlice.copySet bs0 bs p) ∗ S) post := by
  have hst := SepStore8.of_pointsToBytes_here ea dst (ByteSlice.copySet bs0 bs p) off (bs.getD off 0#8) (by byte_region_len) ha
  rw [ByteSlice.write8_copySet bs0 bs p off hoff] at hst; exact step_str8_perm hpc hrun hfetch hsp haddr hv (hst.left (R := S)) hnext
private theorem step_copy_str32 {P : Program} {target_pc pc dst ea : BitVec 64} {s : State} {S : SepProp} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs0 bs : List (BitVec 8)} {p : Nat → Bool} {off : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.str .W32 rt addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hv : s.readReg32 rt = pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)) (hoff : off + 4 ≤ bs0.length) (ha : dst + BitVec.ofNat 64 off = ea)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP P target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') ((dst ↦ₛ ByteSlice.copySet bs0 bs (fun i => p i || (decide (off ≤ i) && decide (i < off + 4)))) ∗ S) post) : SepWP P target_pc s ((dst ↦ₛ ByteSlice.copySet bs0 bs p) ∗ S) post := by
  have hst := SepStore32.of_pointsToBytes_here ea dst (ByteSlice.copySet bs0 bs p) off (pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)) (by byte_region_len) ha
  rw [ByteSlice.write32_copySet_pack32 bs0 bs p off hoff] at hst; exact step_str32_perm hpc hrun hfetch hsp haddr hv (hst.left (R := S)) hnext
private theorem step_copy_str64 {P : Program} {target_pc pc dst ea : BitVec 64} {s : State} {S : SepProp} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs0 bs : List (BitVec 8)} {p : Nat → Bool} {off : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.str .X64 rt addr)) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hv : s.readReg64 rt = ByteSlice.readLE bs off 8) (hoff : off + 8 ≤ bs0.length) (ha : dst + BitVec.ofNat 64 off = ea)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP P target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') ((dst ↦ₛ ByteSlice.copySet bs0 bs (fun i => p i || (decide (off ≤ i) && decide (i < off + 8)))) ∗ S) post) : SepWP P target_pc s ((dst ↦ₛ ByteSlice.copySet bs0 bs p) ∗ S) post := by
  have hst := SepStore64.of_pointsToBytes_here ea dst (ByteSlice.copySet bs0 bs p) off (ByteSlice.readLE bs off 8) (by byte_region_len) ha
  rw [ByteSlice.write64_copySet_readLE bs0 bs p off hoff] at hst; exact step_str64_perm hpc hrun hfetch hsp haddr hv (hst.left (R := S)) hnext
private theorem step_copy_stp64 {P : Program} {target_pc pc dst ea : BitVec 64} {s : State} {S : SepProp} {post : State → SepProp → Prop} {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs0 bs : List (BitVec 8)} {p : Nat → Bool} {off : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : P.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hv1 : s.readReg64 rt1 = ByteSlice.readLE bs off 8) (hv2 : s.readReg64 rt2 = ByteSlice.readLE bs (off + 8) 8) (hoff : off + 16 ≤ bs0.length) (ha : dst + BitVec.ofNat 64 off = ea)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP P target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') ((dst ↦ₛ ByteSlice.copySet bs0 bs (fun i => p i || (decide (off ≤ i) && decide (i < off + 16)))) ∗ S) post) : SepWP P target_pc s ((dst ↦ₛ ByteSlice.copySet bs0 bs p) ∗ S) post := by
  let p1 := fun i => p i || (decide (off ≤ i) && decide (i < off + 8))
  have s1 := SepStore64.of_pointsToBytes_here ea dst (ByteSlice.copySet bs0 bs p) off (ByteSlice.readLE bs off 8) (by byte_region_len) ha; rw [ByteSlice.write64_copySet_readLE bs0 bs p off (by omega)] at s1
  have s2 := SepStore64.of_pointsToBytes_here (ea + 8#64) dst (ByteSlice.copySet bs0 bs p1) (off + 8) (ByteSlice.readLE bs (off + 8) 8) (by byte_region_len) (by rw [← ha, BitVec.ofNat_add]; bv_lin)
  rw [show ByteSlice.write64 (ByteSlice.copySet bs0 bs p1) (off + 8) (ByteSlice.readLE bs (off + 8) 8) = ByteSlice.copySet bs0 bs (fun i => p i || (decide (off ≤ i) && decide (i < off + 16))) from by rw [ByteSlice.write64_copySet_readLE bs0 bs p1 (off + 8) (by omega)]; dsimp [p1]; byte_region_eq] at s2
  exact step_stp64_perm hpc hrun hfetch hsp haddr rfl hv1 hv2 (s1.left (R := S)) (s2.left (R := S)) hnext

/-! ## Placement-Generic `memset` -/

private theorem bcast64_truncate8 (b : BitVec 8) : ((ByteSlice.bcast64 b).truncate 32).truncate 8 = b := by dsimp [ByteSlice.bcast64, BitVec.replicate]; bv_bits
private theorem bcast64_truncate16 (b : BitVec 8) : (ByteSlice.bcast64 b).truncate 16 = (ByteSlice.bcast64 b).setWidth 16 := rfl
private theorem bcast64_truncate32 (b : BitVec 8) : (ByteSlice.bcast64 b).truncate 32 = (ByteSlice.bcast64 b).setWidth 32 := rfl
@[local arm64_norm] private theorem pc_setPC' (s : State) (p : BitVec 64) : (s.setPC p).pc = p := by cases s; rfl
@[local arm64_norm] private theorem pc_setMem' (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
@[local arm64_norm] private theorem pc_setPState' (s : State) (p : PState) : (s.setPState p).pc = s.pc := by cases s; rfl
@[local arm64_norm] private theorem pc_writeVReg128' (s : State) (r : BitVec 5) (v : BitVec 128) : (s.writeVReg128 r v).pc = s.pc := by cases s; rfl
@[local arm64_norm] private theorem status_setPC' (s : State) (p : BitVec 64) : (s.setPC p).status = s.status := by cases s; rfl
@[local arm64_norm] private theorem status_setMem' (s : State) (m : Memory) : (s.setMem m).status = s.status := by cases s; rfl
@[local arm64_norm] private theorem status_setPState' (s : State) (p : PState) : (s.setPState p).status = s.status := by cases s; rfl
@[local arm64_norm] private theorem status_writeVReg128' (s : State) (r : BitVec 5) (v : BitVec 128) : (s.writeVReg128 r v).status = s.status := by cases s; rfl
@[local arm64_norm] private theorem readReg64_writeVReg128' (s : State) (v : BitVec 5) (x : BitVec 128) (r : Reg) : (s.writeVReg128 v x).readReg64 r = s.readReg64 r := by cases s; rfl
@[local arm64_norm] private theorem readVReg128_setPC' (s : State) (p : BitVec 64) (r : BitVec 5) : (s.setPC p).readVReg128 r = s.readVReg128 r := by cases s; rfl
@[local arm64_norm] private theorem readVReg128_setMem' (s : State) (m : Memory) (r : BitVec 5) : (s.setMem m).readVReg128 r = s.readVReg128 r := by cases s; rfl
@[local arm64_norm] private theorem readVReg128_setPState' (s : State) (p : PState) (r : BitVec 5) : (s.setPState p).readVReg128 r = s.readVReg128 r := by cases s; rfl
@[local arm64_norm] private theorem readVReg128_writeReg64' (s : State) (r : Reg) (x : BitVec 64) (v : BitVec 5) : (s.writeReg64 r x).readVReg128 v = s.readVReg128 v := by cases s; rfl
@[local arm64_norm] private theorem mem_setPC' (s : State) (p : BitVec 64) : (s.setPC p).mem = s.mem := by cases s; rfl
@[local arm64_norm] private theorem mem_setPState' (s : State) (p : PState) : (s.setPState p).mem = s.mem := by cases s; rfl
@[local arm64_norm] private theorem mem_writeVReg128' (s : State) (r : BitVec 5) (v : BitVec 128) : (s.writeVReg128 r v).mem = s.mem := by cases s; rfl

private def RegInv (s0 sf : State) : Prop :=
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.sigActions = s0.sigActions ∧ sf.brk = s0.brk ∧ sf.brkStart = s0.brkStart ∧ sf.physMemAvail = s0.physMemAvail
private theorem memOpsInv_iff_regInv_perm {s0 sf : State} : MemOpsInvariant s0 sf ↔ RegInv s0 sf ∧ sf.mem.perm = s0.mem.perm := by
  dsimp [MemOpsInvariant, RegInv, StdStatePreserved]
  exact ⟨fun ⟨hsp, hcs, h1, h2, h3, h4, h5, h6, h7, hp⟩ => ⟨⟨hsp, hcs, h1, h2, h3, h4, h5, h6, h7⟩, funext hp⟩, fun ⟨⟨hsp, hcs, h1, h2, h3, h4, h5, h6, h7⟩, hp⟩ => ⟨hsp, hcs, h1, h2, h3, h4, h5, h6, h7, congrFun hp⟩⟩
@[local arm64_norm] private theorem regInv_setMem (s0 s : State) (m : Memory) : RegInv s0 (s.setMem m) ↔ RegInv s0 s := by
  dsimp [RegInv]; exact and_congr (by cases s; rfl) (and_congr (CalleeSavedPreserved_setMem s0 s m) (by cases s; rfl))
@[local arm64_norm] private theorem regInv_setPC (s0 s : State) (p : BitVec 64) : RegInv s0 (s.setPC p) ↔ RegInv s0 s := by
  dsimp [RegInv]; exact and_congr (by cases s; rfl) (and_congr (CalleeSavedPreserved_setPC s0 s p) (by cases s; rfl))
@[local arm64_norm] private theorem regInv_setPState (s0 s : State) (p : PState) : RegInv s0 (s.setPState p) ↔ RegInv s0 s := by
  dsimp [RegInv]; exact and_congr (by cases s; rfl) (and_congr (CalleeSavedPreserved_setPState s0 s p) (by cases s; rfl))
@[local arm64_norm] private theorem regInv_writeReg64 (s0 s : State) (r : Reg) (v : BitVec 64) (hr : isCalleeSavedOrSPReg r = false) : RegInv s0 (s.writeReg64 r v) ↔ RegInv s0 s := by
  dsimp [RegInv]; exact and_congr (by rw [State.sp_writeReg64_of_isCalleeSavedOrSPReg_false s r v hr]) (and_congr (CalleeSavedPreserved_writeReg64_caller s0 s r v (isCalleeSavedReg_false_of_isCalleeSavedOrSPReg_false hr)) (by cases s; cases r <;> rfl))
@[local arm64_norm] private theorem regInv_writeVReg128 (s0 s : State) (r : BitVec 5) (v : BitVec 128) (hr : isCalleeSavedVReg r = false) : RegInv s0 (s.writeVReg128 r v) ↔ RegInv s0 s := by
  dsimp [RegInv]; exact and_congr (by cases s; rfl) (and_congr (CalleeSavedPreserved_writeVReg128 s0 s r v hr) (by cases s; rfl))
private theorem perm_setMem (s : State) (m : Memory) : (s.setMem m).mem.perm = m.perm := by cases s; rfl
private theorem perm_setPC (s : State) (p : BitVec 64) : (s.setPC p).mem.perm = s.mem.perm := by cases s; rfl
private theorem perm_setPState (s : State) (p : PState) : (s.setPState p).mem.perm = s.mem.perm := by cases s; rfl
private theorem perm_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).mem.perm = s.mem.perm := by cases s; cases r <;> rfl
private theorem perm_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) : (s.writeVReg128 r v).mem.perm = s.mem.perm := by cases s; rfl
private theorem memOpsInv_setPC {s0 s : State} {pc : BitVec 64} (h : MemOpsInvariant s0 s) : MemOpsInvariant s0 (s.setPC pc) :=
  ⟨h.1, (CalleeSavedPreserved_setPC s0 s pc).mpr h.2.1, (stdStatePreserved_setPC s0 s pc).mpr h.2.2⟩
local macro "inv_close" : tactic => `(tactic| (
  have h0 := memOpsInv_iff_regInv_perm.mp ‹MemOpsInvariant _ _›; rw [memOpsInv_iff_regInv_perm]; refine ⟨?_, ?_⟩
  · simp (discharger := decide) only [regInv_setMem, regInv_setPC, regInv_setPState, regInv_writeReg64, regInv_writeVReg128, h0.1]
  · simp only [perm_setMem, perm_setPC, perm_setPState, perm_writeReg64, perm_writeVReg128, h0.2, *]))
local macro "st_pc" : tactic => `(tactic| (simp only [arm64_norm] <;> rfl))
local macro "st_run" h:ident : tactic => `(tactic| simp only [arm64_norm, $h:ident])
local macro "st_reg" h:ident : tactic => `(tactic| simpa only [arm64_norm] using $h:ident)
local macro "st_ea" h:ident : tactic => `(tactic| (simp only [evalAddrMode, arm64_norm, $h:ident]; rfl))
private theorem ofNat64_beq_zero_false {n : Nat} (h0 : n ≠ 0) (hlt : n < 2 ^ 64) : ((BitVec.ofNat 64 n == 0#64) != false) = false := by
  rw [Bool.bne_false, beq_eq_false_iff_ne]; intro heq; have ht := congrArg BitVec.toNat heq; simp [Nat.mod_eq_of_lt hlt] at ht; exact h0 ht
private theorem getLsbD_ofNat_64 (n k : Nat) (hk : k < 64 := by decide) : (BitVec.ofNat 64 n).getLsbD k = decide ((n / 2 ^ k) % 2 = 1) := by
  rw [BitVec.getLsbD_ofNat]; simp only [hk, decide_true, Bool.true_and, Nat.testBit_eq_decide_div_mod_eq]
private theorem addr_end_sub {dst xend hoff : BitVec 64} {n w : Nat} (hend : xend = dst + BitVec.ofNat 64 n) (hw : w ≤ n) (hneg : hoff + BitVec.ofNat 64 w = 0#64 := by decide) : dst + BitVec.ofNat 64 (n - w) = xend + hoff := by
  let k := n - w; have hk : n - w = k := rfl; have hn : n = k + w := by omega
  rw [hk, hend, hn, BitVec.ofNat_add, show (dst + (BitVec.ofNat 64 k + BitVec.ofNat 64 w)) + hoff = (dst + BitVec.ofNat 64 k) + (hoff + BitVec.ofNat 64 w) from by bv_lin, hneg, BitVec.add_zero]
private theorem step_tbz_taken {P : Program} {target_pc pc off : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop} {w : RegWidth} {nz : Bool} {rt : Reg} {bit : Nat} {n : Nat}
    (hf : P.fetch pc = some (.tbz w nz rt bit off)) (hpc : s.pc = pc) (hrun : s.status = .Running) (hr : s.readReg64 rt = BitVec.ofNat 64 n)
    (hbit : bit < 64) (hc : (decide ((n / 2 ^ bit) % 2 = 1) == nz) = true) (hnext : SepWP P target_pc (s.setPC (pc + off)) Q post) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; rfl) hnext; dsimp [Program.evalInst, execInstWithSvc]
  rw [show (s.setPC pc).readReg64 rt = s.readReg64 rt from by cases s; rfl, hr, getLsbD_ofNat_64 n bit hbit, hc]; cases s; rfl
private theorem step_tbz_not_taken {P : Program} {target_pc pc off : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop} {w : RegWidth} {nz : Bool} {rt : Reg} {bit : Nat} {n : Nat}
    (hf : P.fetch pc = some (.tbz w nz rt bit off)) (hpc : s.pc = pc) (hrun : s.status = .Running) (hr : s.readReg64 rt = BitVec.ofNat 64 n)
    (hbit : bit < 64) (hc : (decide ((n / 2 ^ bit) % 2 = 1) == nz) = false) (hnext : SepWP P target_pc (s.setPC (pc + 4#64)) Q post) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; rfl) hnext; dsimp [Program.evalInst, execInstWithSvc]
  rw [show (s.setPC pc).readReg64 rt = s.readReg64 rt from by cases s; rfl, hr, getLsbD_ofNat_64 n bit hbit, hc]; cases s; rfl
private theorem step_cbz_taken {P : Program} {target_pc pc off : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop} {nz : Bool} {rt : Reg} {v : BitVec 64}
    (hf : P.fetch pc = some (.cbz .W64 nz rt off)) (hpc : s.pc = pc) (hrun : s.status = .Running) (hr : s.readReg64 rt = v) (hc : ((v == 0#64) != nz) = true)
    (hnext : SepWP P target_pc (s.setPC (pc + off)) Q post) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; rfl) hnext; dsimp [Program.evalInst, execInstWithSvc]
  rw [show (s.setPC pc).readReg .W64 rt = v from by dsimp [State.readReg]; rw [show (s.setPC pc).readReg64 rt = s.readReg64 rt from by cases s; rfl, hr]]; cases s; cases nz <;> dsimp [State.setPC, State.advancePC] <;> simp_all
private theorem step_cbz_not_taken {P : Program} {target_pc pc off : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop} {nz : Bool} {rt : Reg} {v : BitVec 64}
    (hf : P.fetch pc = some (.cbz .W64 nz rt off)) (hpc : s.pc = pc) (hrun : s.status = .Running) (hr : s.readReg64 rt = v) (hc : ((v == 0#64) != nz) = false)
    (hnext : SepWP P target_pc (s.setPC (pc + 4#64)) Q post) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; rfl) hnext; dsimp [Program.evalInst, execInstWithSvc]
  rw [show (s.setPC pc).readReg .W64 rt = v from by dsimp [State.readReg]; rw [show (s.setPC pc).readReg64 rt = s.readReg64 rt from by cases s; rfl, hr]]; cases s; cases nz <;> dsimp [State.setPC, State.advancePC] <;> simp_all
private theorem finish_ret_bytes {P : Program} {pc : BitVec 64} {s0 s : State} {dst : BitVec 64} {xs ys : List (BitVec 8)}
    (hf : P.fetch pc = some (.ret (.gpr 30#5))) (hpc : s.pc = pc) (hrun : s.status = .Running) (hlr : s.readReg64 .lr = s0.readReg64 .lr) (hx0 : s.readReg64 .x0 = dst) (hinv : MemOpsInvariant s0 s) (hxs : xs = ys) :
    SepWP P (s0.readReg64 .lr) s (dst ↦ₛ xs) (fun sf Q' => Q' = (dst ↦ₛ ys) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  refine SepWP.step_pure (s' := s.setPC (s0.readReg64 .lr)) hpc hrun hf ?_ (by cases s; rfl) ?_
  · dsimp [Program.evalInst, execInstWithSvc, Reg.fromZRBits]; rw [show ((s.setPC pc).readReg64 (.gpr 30#5)) = s0.readReg64 .lr from by cases s; exact hlr]; cases s; rfl
  · exact SepWP.done (by cases s; rfl) (by cases s; exact hrun) ⟨congrArg (pointsToBytes dst) hxs, by cases s; exact hx0, memOpsInv_setPC hinv⟩
local macro "ins_off% " idx:num : term => do let offStx := Lean.Syntax.mkNumLit (toString (4 * idx.getNat)); `(BitVec.ofNat 64 $offStx)
private theorem memset_lt16 {P : Program} {entry dst : BitVec 64} {s0 s : State} {bs0 : List (BitVec 8)} {b : BitVec 8}
    (hc : hasInstrs P entry hbMemsetInstrs) (hlen : bs0.length < 16) (hpc : s.pc = entry + ins_off% 6) (hrun : s.status = .Running) (hinv : MemOpsInvariant s0 s)
    (hlr : s.readReg64 .lr = s0.readReg64 .lr) (hx0 : s.readReg64 .x0 = dst) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs0.length)
    (hx4 : s.readReg64 .x4 = dst + BitVec.ofNat 64 bs0.length) (hv0 : s.readVReg128 0#5 = ByteSlice.bcast64 b ++ ByteSlice.bcast64 b) :
    SepWP P (s0.readReg64 .lr) s (dst ↦ₛ ByteSlice.fillSet bs0 b (fun _ => false)) (fun sf Q => Q = (dst ↦ₛ List.replicate bs0.length b) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  have_instrs hc 6 15; refine step_umov_x1_v0_d0 hpc hrun hf_6 hv0 ?_
  by_cases h8 : 8 ≤ bs0.length
  · refine step_tbz_not_taken hf_7 (by st_pc) (by st_run hrun) (by st_reg hx2) (by decide) (by simp; omega) ?_
    refine step_fill_str64 (off := 0) (by st_pc) (by st_run hrun) hf_8 rfl (by st_ea hx0) (by st_pc) (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
    refine step_fill_str64 (off := bs0.length - 8) (by st_pc) (by st_run hrun) hf_9 rfl (by st_ea hx4) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m2 hm2 => ?_; dsimp only [applyWriteback]
    exact finish_ret_bytes hf_10 (by st_pc) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (by byte_region_eq)
  · refine step_tbz_taken hf_7 (by st_pc) (by st_run hrun) (by st_reg hx2) (by decide) (by simp; omega) ?_
    by_cases h4 : 4 ≤ bs0.length
    · refine step_tbz_not_taken hf_12 (by st_pc) (by st_run hrun) (by st_reg hx2) (by decide) (by simp; omega) ?_
      refine step_fill_str32 (off := 0) (by st_pc) (by st_run hrun) hf_13 rfl (by st_ea hx0) (by simp only [arm64_norm, bcast64_truncate32]) (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
      refine step_fill_str32 (off := bs0.length - 4) (by st_pc) (by st_run hrun) hf_14 rfl (by st_ea hx4) (by simp only [arm64_norm, bcast64_truncate32]) (by omega) (addr_end_sub rfl (by omega)) fun m2 hm2 => ?_; dsimp only [applyWriteback]
      exact finish_ret_bytes hf_15 (by st_pc) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (by byte_region_eq)
    · refine step_tbz_taken hf_12 (by st_pc) (by st_run hrun) (by st_reg hx2) (by decide) (by simp; omega) ?_
      by_cases h0 : bs0.length = 0
      · refine step_cbz_taken hf_16 (by st_pc) (by st_run hrun) (by st_reg hx2) (by simp [h0]) ?_; exact finish_ret_bytes hf_20 (by st_pc) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (by byte_region_eq)
      · refine step_cbz_not_taken hf_16 (by st_pc) (by st_run hrun) (by st_reg hx2) (ofNat64_beq_zero_false h0 (by omega)) ?_
        refine step_fill_str8 (off := 0) (by st_pc) (by st_run hrun) hf_17 rfl (by st_ea hx0) (by simp only [arm64_norm, bcast64_truncate8]) (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
        by_cases h2 : 2 ≤ bs0.length
        · refine step_tbz_not_taken hf_18 (by st_pc) (by st_run hrun) (by st_reg hx2) (by decide) (by simp; omega) ?_
          refine step_fill_str16 (off := bs0.length - 2) (by st_pc) (by st_run hrun) hf_19 rfl (by st_ea hx4) (by simp only [arm64_norm, bcast64_truncate16]) (by omega) (addr_end_sub rfl (by omega)) fun m2 hm2 => ?_; dsimp only [applyWriteback]
          exact finish_ret_bytes hf_20 (by st_pc) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (by byte_region_eq)
        · refine step_tbz_taken hf_18 (by st_pc) (by st_run hrun) (by st_reg hx2) (by decide) (by simp; omega) ?_; exact finish_ret_bytes hf_20 (by st_pc) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (by byte_region_eq)
private theorem memset_16_to_96 {P : Program} {entry dst : BitVec 64} {s0 s : State} {bs0 : List (BitVec 8)} {b : BitVec 8}
    (hc : hasInstrs P entry hbMemsetInstrs) (hlo : 16 ≤ bs0.length) (hhi : bs0.length ≤ 96) (hpc : s.pc = entry + ins_off% 21) (hrun : s.status = .Running) (hinv : MemOpsInvariant s0 s)
    (hlr : s.readReg64 .lr = s0.readReg64 .lr) (hx0 : s.readReg64 .x0 = dst) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs0.length)
    (hx4 : s.readReg64 .x4 = dst + BitVec.ofNat 64 bs0.length) (hv0 : s.readVReg128 0#5 = ByteSlice.bcast64 b ++ ByteSlice.bcast64 b) :
    SepWP P (s0.readReg64 .lr) s (dst ↦ₛ ByteSlice.fillSet bs0 b (fun _ => false)) (fun sf Q => Q = (dst ↦ₛ List.replicate bs0.length b) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  have_instrs hc 21 11; refine step_fill_strSimd128 (off := 0) hpc hrun hf_21 rfl (by st_ea hx0) hv0 (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
  by_cases h64 : 64 ≤ bs0.length
  · refine step_tbz_taken hf_22 (by st_pc) (by st_run hrun) (by st_reg hx2) (by decide) (by simp; omega) ?_
    refine step_fill_strSimd128 (off := 16) (by st_pc) (by st_run hrun) hf_28 rfl (by st_ea hx0) (by st_run hv0) (by omega) (by bv_lin) fun m2 hm2 => ?_; dsimp only [applyWriteback]
    refine step_fill_stpSimd128 (off := 32) (by st_pc) (by st_run hrun) hf_29 rfl (by st_ea hx0) (by st_run hv0) (by st_run hv0) (by omega) (by bv_lin) fun m3 hm3 => ?_; dsimp only [applyWriteback]
    refine step_fill_stpSimd128 (off := bs0.length - 32) (by st_pc) (by st_run hrun) hf_30 rfl (by st_ea hx4) (by st_run hv0) (by st_run hv0) (by omega) (addr_end_sub rfl (by omega)) fun m4 hm4 => ?_; dsimp only [applyWriteback]
    exact finish_ret_bytes hf_31 (by st_pc) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (by byte_region_eq)
  · refine step_tbz_not_taken hf_22 (by st_pc) (by st_run hrun) (by st_reg hx2) (by decide) (by simp; omega) ?_
    refine step_fill_strSimd128 (off := bs0.length - 16) (by st_pc) (by st_run hrun) hf_23 rfl (by st_ea hx4) (by st_run hv0) (by omega) (addr_end_sub rfl (by omega)) fun m2 hm2 => ?_; dsimp only [applyWriteback]
    by_cases h32 : 32 ≤ bs0.length
    · refine step_tbz_not_taken hf_24 (by st_pc) (by st_run hrun) (by st_reg hx2) (by decide) (by simp; omega) ?_
      refine step_fill_strSimd128 (off := 16) (by st_pc) (by st_run hrun) hf_25 rfl (by st_ea hx0) (by st_run hv0) (by omega) (by bv_lin) fun m3 hm3 => ?_; dsimp only [applyWriteback]
      refine step_fill_strSimd128 (off := bs0.length - 32) (by st_pc) (by st_run hrun) hf_26 rfl (by st_ea hx4) (by st_run hv0) (by omega) (addr_end_sub rfl (by omega)) fun m4 hm4 => ?_; dsimp only [applyWriteback]
      exact finish_ret_bytes hf_27 (by st_pc) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (by byte_region_eq)
    · refine step_tbz_taken hf_24 (by st_pc) (by st_run hrun) (by st_reg hx2) (by decide) (by simp; omega) ?_; exact finish_ret_bytes hf_27 (by st_pc) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (by byte_region_eq)
@[local arm64_norm] private theorem writeReg64_xzr' (s : State) (v : BitVec 64) : s.writeReg64 .xzr v = s := by cases s; rfl
@[local arm64_norm] private theorem readReg64_xzr' (s : State) : s.readReg64 .xzr = 0#64 := by cases s; rfl
private theorem cov_ext {p : Nat → Bool} {k : Nat} (a w k' : Nat) (hp : ∀ i < k, p i = true) (ha : a ≤ k) (hk' : k' ≤ a + w) : ∀ i < k', (p i || (decide (a ≤ i) && decide (i < a + w))) = true := by
  intro i hi; by_cases h : i < k
  · simp [hp i h]
  · simp; omega
private theorem fillSet_eq_replicate {bs0 : List (BitVec 8)} {b : BitVec 8} {p : Nat → Bool} (h : ∀ i < bs0.length, p i = true) : ByteSlice.fillSet bs0 b p = List.replicate bs0.length b :=
  ByteSlice.ext_getD (by simp) fun i hi => by rw [ByteSlice.fillSet_length] at hi; rw [ByteSlice.getD_fillSet, ByteSlice.getD_replicate', h i hi]; simp [hi]
private theorem copySet_eq_self {bs0 bs : List (BitVec 8)} {p : Nat → Bool} (hlen : bs0.length = bs.length) (h : ∀ i < bs.length, p i = true) : ByteSlice.copySet bs0 bs p = bs :=
  ByteSlice.ext_getD (by simp [hlen]) fun i hi => by rw [ByteSlice.copySet_length, hlen] at hi; rw [ByteSlice.getD_copySet, h i hi]; simp [hlen, hi]
private theorem ofNat_mod_16 (x : BitVec 64) : BitVec.ofNat 64 (x.toNat % 16) = x &&& 15#64 := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, BitVec.toNat_and]; change (x.toNat % 16) % 2 ^ 64 = x.toNat &&& (2 ^ 4 - 1); rw [Nat.and_two_pow_sub_one_eq_mod]; omega
private theorem ofNat_mod_64 (x : BitVec 64) : BitVec.ofNat 64 (x.toNat % 64) = x &&& 63#64 := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, BitVec.toNat_and]; change (x.toNat % 64) % 2 ^ 64 = x.toNat &&& (2 ^ 6 - 1); rw [Nat.and_two_pow_sub_one_eq_mod]; omega
private theorem and_not15_eq (x m : BitVec 64) (hm : m = ~~~15#64) : x &&& m = x - BitVec.ofNat 64 (x.toNat % 16) := by rw [hm, ofNat_mod_16]; bv_bits
private theorem and_not63_eq (x m1 m2 : BitVec 64) (hm1 : m1 = ~~~15#64) (hm2 : m2 = ~~~63#64) : (x &&& m1) &&& m2 = x - BitVec.ofNat 64 (x.toNat % 64) := by rw [hm1, hm2, ofNat_mod_64]; bv_bits
private theorem dcZva_align {dst : BitVec 64} {k : Nat} (hk : (dst.toNat + k) % 64 = 0) : (dst + BitVec.ofNat 64 k) &&& ~~~63#64 = dst + BitVec.ofNat 64 k := by
  have hmod : (dst + BitVec.ofNat 64 k).toNat % 64 = 0 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h0 : (dst + BitVec.ofNat 64 k) &&& 63#64 = 0#64 := by rw [← ofNat_mod_64, hmod]
  have hsub : ∀ x : BitVec 64, x &&& ~~~63#64 = x - (x &&& 63#64) := fun _ => by bv_bits
  rw [hsub, h0, BitVec.sub_zero]
private theorem step_add_reg {P : Program} {target_pc pc vx vy : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {rd rn rm : Reg} (hf : P.fetch pc = some (.addSubShift .W64 .ADD rd rn rm .LSL 0)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx : s.readReg64 rn = vx) (hy : s.readReg64 rm = vy) (hnext : SepWP P target_pc ((s.writeReg64 rd (vx + vy)).setPC (pc + 4#64)) Q post) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; cases rd <;> rfl) hnext; dsimp [Program.evalInst, execInstWithSvc, execAddSubShift, State.readReg, State.writeReg, shiftVal, shift64]
  rw [show (s.setPC pc).readReg64 rn = vx from by cases s; exact hx, show (s.setPC pc).readReg64 rm = vy from by cases s; exact hy, show vy <<< 0 = vy from by bv_bits, evalAddSub_w64_add]; cases s; rfl
private theorem step_sub_lsl {P : Program} {target_pc pc vx vy : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {rd rn rm : Reg} {sh : Nat} (hf : P.fetch pc = some (.addSubShift .W64 .SUB rd rn rm .LSL sh)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx : s.readReg64 rn = vx) (hy : s.readReg64 rm = vy) (hnext : SepWP P target_pc ((s.writeReg64 rd (vx - (vy <<< sh))).setPC (pc + 4#64)) Q post) (hsh : sh < 64 := by decide) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; cases rd <;> rfl) hnext; dsimp [Program.evalInst, execInstWithSvc, execAddSubShift, State.readReg, State.writeReg, shiftVal, shift64]
  rw [show (s.setPC pc).readReg64 rn = vx from by cases s; exact hx, show (s.setPC pc).readReg64 rm = vy from by cases s; exact hy, Nat.mod_eq_of_lt hsh, evalAddSub_w64_sub]; cases s; rfl
private theorem step_add_imm {P : Program} {target_pc pc vx : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {rd rn : Reg} {imm12 : BitVec 12} (hf : P.fetch pc = some (.addSubImm .W64 .ADD rd rn imm12 false)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx : s.readReg64 rn = vx) (hnext : SepWP P target_pc ((s.writeReg64 rd (vx + imm12.zeroExtend 64)).setPC (pc + 4#64)) Q post) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; cases rd <;> rfl) hnext; dsimp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.writeReg]
  rw [show (s.setPC pc).readReg64 rn = vx from by cases s; exact hx, evalAddSub_w64_add]; cases s; rfl
private theorem step_sub_imm {P : Program} {target_pc pc vx : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {rd rn : Reg} {imm12 : BitVec 12} (hf : P.fetch pc = some (.addSubImm .W64 .SUB rd rn imm12 false)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx : s.readReg64 rn = vx) (hnext : SepWP P target_pc ((s.writeReg64 rd (vx - imm12.zeroExtend 64)).setPC (pc + 4#64)) Q post) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; cases rd <;> rfl) hnext; dsimp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.writeReg]
  rw [show (s.setPC pc).readReg64 rn = vx from by cases s; exact hx, evalAddSub_w64_sub]; cases s; rfl
private theorem step_and64_imm {P : Program} {target_pc pc vx mask : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {rd rn : Reg} (hf : P.fetch pc = some (.logicalImm .W64 .AND rd rn mask)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx : s.readReg64 rn = vx) (hnext : SepWP P target_pc ((s.writeReg64 rd (vx &&& mask)).setPC (pc + 4#64)) Q post) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; cases rd <;> rfl) hnext; dsimp [Program.evalInst, execInstWithSvc, execLogicalImm, State.readReg, State.writeReg, evalLogical]
  rw [show (s.setPC pc).readReg64 rn = vx from by cases s; exact hx]; cases s; rfl
private theorem step_and32_byte {P : Program} {target_pc pc mask : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {rd rn : Reg} {b : BitVec 8} (hf : P.fetch pc = some (.logicalImm .W32 .AND rd rn mask)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hb : (s.readReg32 rn).truncate 8 = b) (hnext : SepWP P target_pc ((s.writeReg64 rd (b.zeroExtend 64)).setPC (pc + 4#64)) Q post) (hm : mask.truncate 32 = 255#32 := by decide) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; cases rd <;> rfl) hnext
  have hand : BitVec.setWidth 32 (BitVec.setWidth 64 (s.readReg32 rn) &&& mask) = s.readReg32 rn &&& 255#32 := by
    rw [← hm]; ext i hi; simp
  have htr : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (s.readReg32 rn) &&& mask)))) = BitVec.setWidth 64 b := by
    rw [hand]; subst hb; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
    change (((s.readReg32 rn).toNat &&& (2 ^ 8 - 1)) % 2 ^ 64 % 2 ^ 32) % 2 ^ 64 = ((s.readReg32 rn).toNat % 256) % 2 ^ 64
    rw [Nat.and_two_pow_sub_one_eq_mod]; omega
  dsimp [Program.evalInst, execInstWithSvc, execLogicalImm, State.readReg, State.writeReg, evalLogical]
  rw [show (s.setPC pc).readReg32 rn = s.readReg32 rn from by cases s; rfl, htr]; cases s; rfl
private theorem step_nop {P : Program} {target_pc pc : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    (hf : P.fetch pc = some .nop) (hpc : s.pc = pc) (hrun : s.status = .Running) (hnext : SepWP P target_pc (s.setPC (pc + 4#64)) Q post) : SepWP P target_pc s Q post :=
  SepWP.step_pure hpc hrun hf (by cases s; rfl) (by cases s; rfl) hnext
local macro "st_pclin" : tactic => `(tactic| (simp only [arm64_norm]; try bv_lin))
private theorem fillSet_false (bs0 : List (BitVec 8)) (b : BitVec 8) : ByteSlice.fillSet bs0 b (fun _ => false) = bs0 := ByteSlice.ext_getD (by simp) fun i _ => by rw [ByteSlice.getD_fillSet]; simp
private theorem cond_hi_imm {n : Nat} {imm : BitVec 12} (hn : n < 2 ^ 64) : ConditionHolds .HI (subsPState64 (BitVec.ofNat 64 n) (imm.zeroExtend 64)) = decide (imm.toNat < n) := by
  unfold subsPState64; rw [conditionHolds_hi_subs64]; have := imm.isLt; simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; omega
private theorem cond_cs_imm {n : Nat} {imm : BitVec 12} (hn : n < 2 ^ 64) : ConditionHolds .CS (subsPState64 (BitVec.ofNat 64 n) (imm.zeroExtend 64)) = decide (imm.toNat ≤ n) := by
  unfold subsPState64; rw [conditionHolds_cs_subs64]; have := imm.isLt; simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; omega
private theorem cond_ls_imm {n : Nat} {imm : BitVec 12} (hn : n < 2 ^ 64) : ConditionHolds .LS (subsPState64 (BitVec.ofNat 64 n) (imm.zeroExtend 64)) = decide (n ≤ imm.toNat) := by
  unfold subsPState64; rw [conditionHolds_ls_subs64]; have := imm.isLt; simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; omega
private theorem cond_cc_imm {n : Nat} {imm : BitVec 12} (hn : n < 2 ^ 64) : ConditionHolds .CC (subsPState64 (BitVec.ofNat 64 n) (imm.zeroExtend 64)) = decide (n < imm.toNat) := by
  unfold subsPState64; rw [conditionHolds_cc_subs64]; have := imm.isLt; simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; omega
private theorem step_subs_imm_bcond_taken {P : Program} {target_pc pc1 pc2 off vx : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop} {rd rn : Reg} {imm12 : BitVec 12} {cond : CondCode}
    (hf1 : P.fetch pc1 = some (.addSubImm .W64 .SUBS rd rn imm12 false)) (hf2 : P.fetch pc2 = some (.bCond cond off))
    (hpc : s.pc = pc1) (hrun : s.status = .Running) (hx : s.readReg64 rn = vx) (hc : ConditionHolds cond (subsPState64 vx (imm12.zeroExtend 64)) = true)
    (hnext : SepWP P target_pc (((s.writeReg64 rd (vx - imm12.zeroExtend 64)).setPState (subsPState64 vx (imm12.zeroExtend 64))).setPC (pc2 + off)) Q post) (hpc2 : pc1 + 4#64 = pc2 := by bv_lin) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure (s' := ((s.writeReg64 rd (vx - imm12.zeroExtend 64)).setPState (subsPState64 vx (imm12.zeroExtend 64))).setPC pc2) hpc hrun hf1 ?_ (by cases s; cases rd <;> rfl) ?_
  · dsimp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.writeReg]; rw [show (s.setPC pc1).readReg64 rn = vx from by cases s; exact hx, evalAddSub_w64_subs]; cases s; cases rd <;> simp [State.writeReg64, State.setPState, State.advancePC, State.setPC, hpc2]
  · refine SepWP.step_pure (by st_pc) (by st_run hrun) hf2 ?_ (by cases s; cases rd <;> rfl) hnext
    cases s; cases rd <;> simp [Program.evalInst, execInstWithSvc, State.writeReg64, State.setPState, State.setPC, hc]
private theorem step_subs_imm_bcond_not_taken {P : Program} {target_pc pc1 pc2 off vx : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop} {rd rn : Reg} {imm12 : BitVec 12} {cond : CondCode}
    (hf1 : P.fetch pc1 = some (.addSubImm .W64 .SUBS rd rn imm12 false)) (hf2 : P.fetch pc2 = some (.bCond cond off))
    (hpc : s.pc = pc1) (hrun : s.status = .Running) (hx : s.readReg64 rn = vx) (hc : ConditionHolds cond (subsPState64 vx (imm12.zeroExtend 64)) = false)
    (hnext : SepWP P target_pc (((s.writeReg64 rd (vx - imm12.zeroExtend 64)).setPState (subsPState64 vx (imm12.zeroExtend 64))).setPC (pc2 + 4#64)) Q post) (hpc2 : pc1 + 4#64 = pc2 := by bv_lin) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure (s' := ((s.writeReg64 rd (vx - imm12.zeroExtend 64)).setPState (subsPState64 vx (imm12.zeroExtend 64))).setPC pc2) hpc hrun hf1 ?_ (by cases s; cases rd <;> rfl) ?_
  · dsimp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.writeReg]; rw [show (s.setPC pc1).readReg64 rn = vx from by cases s; exact hx, evalAddSub_w64_subs]; cases s; cases rd <;> simp [State.writeReg64, State.setPState, State.advancePC, State.setPC, hpc2]
  · refine SepWP.step_pure (by st_pc) (by st_run hrun) hf2 ?_ (by cases s; cases rd <;> rfl) hnext
    cases s; cases rd <;> simp [Program.evalInst, execInstWithSvc, State.writeReg64, State.setPState, State.setPC, State.advancePC, hc]
private theorem step_memset_ccmp {P : Program} {target_pc pc1 pc2 pc3 off : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop} {n : Nat} {b : BitVec 8}
    (hf1 : P.fetch pc1 = some (.addSubImm .W64 .SUBS .xzr (.gpr 2#5) 160#12 false)) (hf2 : P.fetch pc2 = some (.condCompareImm .W32 true (.gpr 1#5) 0#5 0#4 .CS)) (hf3 : P.fetch pc3 = some (.bCond .NE off))
    (hpc : s.pc = pc1) (hrun : s.status = .Running) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 n) (hx1 : s.readReg64 .x1 = b.zeroExtend 64) (hn : n < 2 ^ 64)
    (hdcz : 160 ≤ n → b = 0#8 → ∀ ps, SepWP P target_pc ((s.setPState ps).setPC (pc3 + 4#64)) Q post)
    (hstp : ¬(160 ≤ n ∧ b = 0#8) → ∀ ps, SepWP P target_pc ((s.setPState ps).setPC (pc3 + off)) Q post) (hpc2 : pc1 + 4#64 = pc2 := by bv_lin) (hpc3 : pc2 + 4#64 = pc3 := by bv_lin) : SepWP P target_pc s Q post := by
  let ps1 := subsPState64 (BitVec.ofNat 64 n) 160#64
  refine SepWP.step_pure (s' := (s.setPState ps1).setPC pc2) hpc hrun hf1 ?_ (by cases s; rfl) ?_
  · dsimp [Program.evalInst, execInstWithSvc, execAddSubImm, State.readReg, State.writeReg]
    rw [show (s.setPC pc1).readReg64 (.gpr 2#5) = BitVec.ofNat 64 n from by cases s; exact hx2, evalAddSub_w64_subs]; cases s; simp [State.writeReg64, State.setPState, State.advancePC, State.setPC, hpc2, ps1]
  · let ps2 := if ConditionHolds .CS ps1 then ((evalAddSub .W32 .SUBS (b.zeroExtend 64) 0#64 none).2.getD ps1) else PState.ofBits4 0#4
    refine SepWP.step_ccmp_imm (by st_pc) (by st_run hrun) hf2 (s' := (s.setPState ps2).setPC pc3) ?_ ?_
    · rw [show ((s.setPState ps1).setPC pc2).readReg .W32 (.gpr 1#5) = b.zeroExtend 64 from by dsimp [State.readReg, State.readReg32]; rw [show ((s.setPState ps1).setPC pc2).readReg64 (.gpr 1#5) = b.zeroExtend 64 from by cases s; exact hx1]; bv_bits]
      cases s; simp [State.setPState, State.setPC, hpc3, ps2]
    · by_cases hc : ConditionHolds .NE ps2 = true
      · refine SepWP.step_pure (by st_pc) (by st_run hrun) hf3 (s' := (s.setPState ps2).setPC (pc3 + off)) ?_ (by cases s; rfl) ?_
        · dsimp [Program.evalInst, execInstWithSvc]; cases s; simp [State.setPState, State.setPC, hc]
        · refine hstp (fun ⟨h160, hb0⟩ => ?_) ps2
          have hcs : ConditionHolds .CS ps1 = true := by dsimp [ps1]; unfold subsPState64; rw [conditionHolds_cs_subs64]; simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; omega
          have hps2 : ps2 = (evalAddSub .W32 .SUBS (b.zeroExtend 64) 0#64 none).2.getD ps1 := by dsimp [ps2]; rw [hcs]; rfl
          rw [hps2, hb0, evalAddSub_w32_subs] at hc; dsimp only [Option.getD] at hc; unfold subsPState32 at hc; rw [conditionHolds_ne_subs32] at hc; simp at hc
      · have hcf := Bool.eq_false_iff.mpr hc
        refine SepWP.step_pure (by st_pc) (by st_run hrun) hf3 (s' := (s.setPState ps2).setPC (pc3 + 4#64)) ?_ (by cases s; rfl) ?_
        · dsimp [Program.evalInst, execInstWithSvc]; cases s; simp [State.setPState, State.setPC, State.advancePC, hcf]
        · have hcs : ConditionHolds .CS ps1 = true := by
            apply Classical.byContradiction; intro hncs; have hps2 : ps2 = PState.ofBits4 0#4 := by dsimp [ps2]; rw [Bool.eq_false_iff.mpr hncs]; rfl
            rw [hps2] at hcf; simp [ConditionHolds, PState.ofBits4] at hcf
          have h160 : 160 ≤ n := by dsimp [ps1] at hcs; unfold subsPState64 at hcs; rw [conditionHolds_cs_subs64] at hcs; simp [BitVec.ule] at hcs; omega
          have hb0 : b = 0#8 := by
            have hps2 : ps2 = (evalAddSub .W32 .SUBS (b.zeroExtend 64) 0#64 none).2.getD ps1 := by dsimp [ps2]; rw [hcs]; rfl
            rw [hps2, evalAddSub_w32_subs] at hcf; dsimp only [Option.getD] at hcf; unfold subsPState32 at hcf; rw [conditionHolds_ne_subs32, show (b.zeroExtend 64).truncate 32 = b.zeroExtend 32 from by bv_bits] at hcf
            simp at hcf; simpa [show (BitVec.setWidth 64 b).truncate 8 = b from by bv_bits] using congrArg (BitVec.truncate 8) hcf
          exact hdcz h160 hb0 ps2

private theorem ofNat64_sub {a b : Nat} (hb : b ≤ a) : BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  let d := a - b; have hd : a - b = d := rfl; have ha : a = d + b := by omega
  rw [hd, ha, BitVec.ofNat_add]; bv_lin
private theorem memset_stp_loop {P : Program} {entry dst : BitVec 64} {s0 : State} {bs0 : List (BitVec 8)} {b : BitVec 8}
    (hc : hasInstrs P entry hbMemsetInstrs) (hbound : bs0.length + 260 ≤ 2 ^ 64) :
    ∀ (rem : Nat) {k : Nat} {p : Nat → Bool} (s : State), k + 64 + rem = bs0.length → 1 ≤ rem → (∀ i < k, p i = true) →
      s.pc = entry + ins_off% 58 → s.status = .Running → MemOpsInvariant s0 s → s.readReg64 .lr = s0.readReg64 .lr → s.readReg64 .x0 = dst →
      s.readReg64 .x2 = BitVec.ofNat 64 rem → s.readReg64 .x3 = dst + BitVec.ofNat 64 k - 32#64 → s.readReg64 .x4 = dst + BitVec.ofNat 64 bs0.length →
      s.readVReg128 0#5 = ByteSlice.bcast64 b ++ ByteSlice.bcast64 b →
      SepWP P (s0.readReg64 .lr) s (dst ↦ₛ ByteSlice.fillSet bs0 b p) (fun sf Q => Q = (dst ↦ₛ List.replicate bs0.length b) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  intro rem; induction rem using Nat.strongRecOn with | ind rem ih => ?_
  intro k p s hsum hrem hp hpc hrun hinv hlr hx0 hx2 hx3 hx4 hv0; have_instrs hc 58 7
  refine step_fill_stpSimd128 (off := k) hpc hrun hf_58 rfl (by st_ea hx3) hv0 hv0 (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
  refine step_fill_stpSimd128 (off := k + 32) (by st_pclin) (by st_run hrun) hf_59 rfl (by st_ea hx3) (by st_run hv0) (by st_run hv0) (by omega) (by rw [BitVec.ofNat_add]; bv_lin) fun m2 hm2 => ?_; dsimp only [applyWriteback]
  have hp2 := cov_ext (k + 32) 32 (k + 64) (cov_ext k 32 (k + 32) hp (by omega) (by omega)) (by omega) (by omega)
  by_cases h64 : 64 < rem
  · refine step_subs_imm_bcond_taken hf_60 hf_61 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm (by omega)]; simp; try omega) ?_
    exact ih (rem - 64) (by omega) _ (by omega) (by omega) hp2 (by st_pclin) (by st_run hrun) (by inv_close) (by st_reg hlr) (by st_reg hx0)
      (by simp only [arm64_norm]; exact ofNat64_sub (b := 64) (by omega)) (by simp only [arm64_norm, BitVec.ofNat_add]; bv_lin) (by st_reg hx4) (by st_run hv0)
  · refine step_subs_imm_bcond_not_taken hf_60 hf_61 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm (by omega)]; simp; try omega) ?_
    refine step_fill_stpSimd128 (off := bs0.length - 64) (by st_pclin) (by st_run hrun) hf_62 rfl (by st_ea hx4) (by st_run hv0) (by st_run hv0) (by omega) (addr_end_sub rfl (by omega)) fun m3 hm3 => ?_; dsimp only [applyWriteback]
    refine step_fill_stpSimd128 (off := bs0.length - 32) (by st_pclin) (by st_run hrun) hf_63 rfl (by st_ea hx4) (by st_run hv0) (by st_run hv0) (by omega) (addr_end_sub rfl (by omega)) fun m4 hm4 => ?_; dsimp only [applyWriteback]
    exact finish_ret_bytes hf_64 (by st_pclin) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close)
      (fillSet_eq_replicate (cov_ext (bs0.length - 32) 32 bs0.length (cov_ext (bs0.length - 64) 32 (bs0.length - 32) hp2 (by omega) (by omega)) (by omega) (by omega)))
private theorem memset_dczva_loop {P : Program} {entry dst : BitVec 64} {s0 : State} {bs0 : List (BitVec 8)}
    (hc : hasInstrs P entry hbMemsetInstrs) (hbound : bs0.length + 260 ≤ 2 ^ 64) :
    ∀ (rem : Nat) {k : Nat} {p : Nat → Bool} (s : State), k + 64 + rem = bs0.length → 1 ≤ rem → (dst.toNat + k) % 64 = 0 → (∀ i < k, p i = true) →
      s.pc = entry + ins_off% 48 → s.status = .Running → MemOpsInvariant s0 s → s.readReg64 .lr = s0.readReg64 .lr → s.readReg64 .x0 = dst →
      s.readReg64 .x2 = BitVec.ofNat 64 rem → s.readReg64 .x3 = dst + BitVec.ofNat 64 k - 64#64 → s.readReg64 .x4 = dst + BitVec.ofNat 64 bs0.length →
      s.readVReg128 0#5 = ByteSlice.bcast64 0#8 ++ ByteSlice.bcast64 0#8 →
      SepWP P (s0.readReg64 .lr) s (dst ↦ₛ ByteSlice.fillSet bs0 0#8 p) (fun sf Q => Q = (dst ↦ₛ List.replicate bs0.length 0#8) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  intro rem; induction rem using Nat.strongRecOn with | ind rem ih => ?_
  intro k p s hsum hrem haln hp hpc hrun hinv hlr hx0 hx2 hx3 hx4 hv0; have_instrs hc 48 7; refine step_add_imm hf_48 hpc hrun hx3 ?_
  refine step_fill_dcZva (off := k) (v := dst + BitVec.ofNat 64 k) (by st_pclin) (by st_run hrun) hf_49 (by st_pclin) (dcZva_align haln) (by omega) rfl fun m1 hm1 => ?_
  have hp1 := cov_ext k 64 (k + 64) hp (by omega) (by omega)
  by_cases h64 : 64 < rem
  · refine step_subs_imm_bcond_taken hf_50 hf_51 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm (by omega)]; simp; try omega) ?_
    exact ih (rem - 64) (by omega) _ (by omega) (by omega) (by omega) hp1 (by st_pclin) (by st_run hrun) (by inv_close) (by st_reg hlr) (by st_reg hx0)
      (by simp only [arm64_norm]; exact ofNat64_sub (b := 64) (by omega)) (by simp only [arm64_norm, BitVec.ofNat_add]; bv_lin) (by st_reg hx4) (by st_run hv0)
  · refine step_subs_imm_bcond_not_taken hf_50 hf_51 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm (by omega)]; simp; try omega) ?_
    refine step_fill_stpSimd128 (off := bs0.length - 64) (by st_pclin) (by st_run hrun) hf_52 rfl (by st_ea hx4) (by st_run hv0) (by st_run hv0) (by omega) (addr_end_sub rfl (by omega)) fun m2 hm2 => ?_; dsimp only [applyWriteback]
    refine step_fill_stpSimd128 (off := bs0.length - 32) (by st_pclin) (by st_run hrun) hf_53 rfl (by st_ea hx4) (by st_run hv0) (by st_run hv0) (by omega) (addr_end_sub rfl (by omega)) fun m3 hm3 => ?_; dsimp only [applyWriteback]
    exact finish_ret_bytes hf_54 (by st_pclin) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close)
      (fillSet_eq_replicate (cov_ext (bs0.length - 32) 32 bs0.length (cov_ext (bs0.length - 64) 32 (bs0.length - 32) hp1 (by omega) (by omega)) (by omega) (by omega)))
private theorem memset_gt96 {P : Program} {entry dst : BitVec 64} {s0 s : State} {bs0 : List (BitVec 8)} {b : BitVec 8}
    (hc : hasInstrs P entry hbMemsetInstrs) (hgt : 96 < bs0.length) (hbound : bs0.length + 260 ≤ 2 ^ 64) (hpc : s.pc = entry + ins_off% 32) (hrun : s.status = .Running)
    (hinv : MemOpsInvariant s0 s) (hlr : s.readReg64 .lr = s0.readReg64 .lr) (hx0 : s.readReg64 .x0 = dst) (hx1 : (s.readReg32 .x1).truncate 8 = b)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs0.length) (hx4 : s.readReg64 .x4 = dst + BitVec.ofNat 64 bs0.length) (hv0 : s.readVReg128 0#5 = ByteSlice.bcast64 b ++ ByteSlice.bcast64 b) :
    SepWP P (s0.readReg64 .lr) s (dst ↦ₛ ByteSlice.fillSet bs0 b (fun _ => false)) (fun sf Q => Q = (dst ↦ₛ List.replicate bs0.length b) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  have_instrs hc 32 26; let r16 := dst.toNat % 16; let k16 := 16 - r16; have hr16 : r16 < 16 := Nat.mod_lt _ (by omega)
  have hk16_eq : BitVec.ofNat 64 k16 = 16#64 - BitVec.ofNat 64 r16 := by rw [show k16 = 16 - r16 from rfl, ← ofNat64_sub (by omega)]
  refine step_and32_byte hf_32 hpc hrun hx1 ?_; refine step_and64_imm hf_33 (by st_pclin) (by st_run hrun) (by st_reg hx0) ?_
  refine step_fill_strSimd128 (off := 0) (by st_pclin) (by st_run hrun) hf_34 rfl (by st_ea hx0) (by st_run hv0) (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
  have hp16 := cov_ext 0 16 16 (p := fun _ => false) (k := 0) (fun _ h => absurd h (Nat.not_lt_zero _)) (by omega) (by omega)
  refine step_memset_ccmp (b := b) hf_35 hf_36 hf_37 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by st_pc) (by omega) (fun h160 hb0 ps => ?_) (fun _ ps => ?_)
  · subst hb0; let r64 := dst.toNat % 64; let k64 := 64 - r64; have hr64 : r64 < 64 := Nat.mod_lt _ (by omega); have hr16_le : r16 ≤ r64 := by dsimp [r16, r64]; omega
    have hk64_eq : BitVec.ofNat 64 k64 = 64#64 - BitVec.ofNat 64 r64 := by rw [show k64 = 64 - r64 from rfl, ← ofNat64_sub (by omega)]
    refine SepWP.step_mrs_dczid_el0 (by st_pclin) (by st_run hrun) hf_38 rfl ?_; refine step_and64_imm hf_39 (by st_pclin) (by st_run hrun) (by st_pc) ?_
    refine step_subs_imm_bcond_not_taken hf_40 hf_41 (by st_pclin) (by st_run hrun) (by st_pc) (by unfold subsPState64; rw [conditionHolds_ne_subs64]; decide) ?_
    refine step_fill_strSimd128 (off := k16) (by st_pclin) (by st_run hrun) hf_42 rfl (by simp only [evalAddrMode, arm64_norm]; rfl) (by st_run hv0) (by omega)
      (by simp (discharger := decide) only [and_not15_eq]; change dst + BitVec.ofNat 64 k16 = (dst - BitVec.ofNat 64 r16) + 16#64; rw [hk16_eq]; bv_lin) fun m2 hm2 => ?_; dsimp only [applyWriteback]
    refine step_fill_stpSimd128 (off := k16 + 16) (by st_pclin) (by st_run hrun) hf_43 rfl (by simp only [evalAddrMode, arm64_norm]; rfl) (by st_run hv0) (by st_run hv0) (by omega)
      (by simp (discharger := decide) only [and_not15_eq, BitVec.ofNat_add]; change dst + (BitVec.ofNat 64 k16 + 16#64) = (dst - BitVec.ofNat 64 r16) + 32#64; rw [hk16_eq]; bv_lin) fun m3 hm3 => ?_; dsimp only [applyWriteback]
    have hp64 := cov_ext (k16 + 16) 32 (k16 + 48) (cov_ext k16 16 (k16 + 16) hp16 (by omega) (by omega)) (by omega) (by omega)
    refine step_and64_imm hf_44 (by st_pclin) (by st_run hrun) (by st_pc) ?_; refine step_sub_lsl hf_45 (by st_pclin) (by st_run hrun) (by st_reg hx4) (by st_pc) ?_
    refine step_sub_imm hf_46 (by st_pclin) (by st_run hrun) (by st_pc) ?_; refine step_nop hf_47 (by st_pclin) (by st_run hrun) ?_
    refine memset_dczva_loop hc hbound (bs0.length - k64 - 64) _ (k := k64) (by omega) (by omega) (by dsimp [k64, r64]; omega) (fun i hi => hp64 i (by omega)) (by st_pclin) (by st_run hrun) (by inv_close) (by st_reg hlr) (by st_reg hx0) ?_ ?_ (by st_reg hx4) (by st_run hv0)
    · simp only [arm64_norm]; simp (discharger := decide) only [and_not63_eq]; rw [show (dst + BitVec.ofNat 64 bs0.length) - (dst - BitVec.ofNat 64 r64) = BitVec.ofNat 64 (bs0.length + r64) from by rw [BitVec.ofNat_add]; bv_lin]
      change BitVec.ofNat 64 (bs0.length + r64) - BitVec.ofNat 64 128 = _; rw [ofNat64_sub (by omega)]; apply congrArg (BitVec.ofNat 64); omega
    · simp only [arm64_norm]; simp (discharger := decide) only [and_not63_eq]; change dst - BitVec.ofNat 64 r64 = dst + BitVec.ofNat 64 k64 - 64#64; rw [hk64_eq]; bv_lin
  · refine step_sub_lsl hf_55 (by st_pclin) (by st_run hrun) (by st_reg hx4) (by st_pc) ?_; refine step_sub_imm hf_56 (by st_pclin) (by st_run hrun) (by st_pc) ?_; refine step_sub_imm hf_57 (by st_pclin) (by st_run hrun) (by st_pc) ?_
    refine memset_stp_loop hc hbound (bs0.length - k16 - 64) _ (k := k16) (by omega) (by omega) (fun i hi => hp16 i (by omega)) (by st_pclin) (by st_run hrun) (by inv_close) (by st_reg hlr) (by st_reg hx0) ?_ ?_ (by st_reg hx4) (by st_run hv0)
    · simp only [arm64_norm]; simp (discharger := decide) only [and_not15_eq]; rw [show (dst + BitVec.ofNat 64 bs0.length) - (dst - BitVec.ofNat 64 r16) = BitVec.ofNat 64 (bs0.length + r16) from by rw [BitVec.ofNat_add]; bv_lin]
      change BitVec.ofNat 64 (bs0.length + r16) - BitVec.ofNat 64 80 = _; rw [ofNat64_sub (by omega)]; apply congrArg (BitVec.ofNat 64); omega
    · simp only [arm64_norm]; simp (discharger := decide) only [and_not15_eq]; change (dst - BitVec.ofNat 64 r16) - 16#64 = dst + BitVec.ofNat 64 k16 - 32#64; rw [hk16_eq]; bv_lin

theorem hbMemset_ok {P : Program} {C : HbCliLayout} (hc : HbMemOpsCode P C) : subroutine_ok P C.std.memsetAddr stdMemsetSpec := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨dst, b, len⟩ R s0 hpc hrun hpre _hsp; dsimp only [stdMemsetSpec] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩; rw [memRegion_eq_exists_bytes dst len (by omega), sepExists_sepConj_left, satisfies_sepExists] at hmem
  rcases hmem with ⟨bs0, hmem⟩; rw [sepConj_assoc, satisfies_pure_sepConj] at hmem; rcases hmem with ⟨hbs0, hmem⟩; subst hbs0
  refine ⟨dst ↦ₛ ByteSlice.fillSet bs0 b (fun _ => false), by rwa [fillSet_false], ?_⟩; apply sepWP_with_codeLoaded; intro R' hm' hL
  have hbound : bs0.length + 260 ≤ 2 ^ 64 := writable_len_add_code_le hL hc.memset (by rwa [fillSet_false] at hm') (by omega) (by decide)
  refine SepWP.mono (post := fun sf Q => Q = (dst ↦ₛ List.replicate bs0.length b) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) ?_ (fun sf P_f _ _ ⟨hPf, hx0_f, hsp_f, hcs_f, hstd_f⟩ => ⟨fun hm_f => ?_, hsp_f, hcs_f⟩)
  · have_instrs hc.memset 0 6; have hinv0 := MemOpsInvariant.rfl s0
    refine step_dup_v0_16b_w1 hpc hrun hf_0 hx1 ?_; refine step_add_reg hf_1 (by st_pclin) (by st_run hrun) (by st_reg hx0) (by st_reg hx2) ?_
    by_cases h96 : 96 < bs0.length
    · refine step_subs_imm_bcond_taken hf_2 hf_3 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm hlen]; simp; try omega) ?_
      exact memset_gt96 hc.memset h96 hbound (by st_pclin) (by st_run hrun) (by inv_close) (by st_pc) (by st_reg hx0) (by simpa only [State.readReg32, arm64_norm] using hx1) (by st_reg hx2) (by st_pc) (by st_pc)
    · refine step_subs_imm_bcond_not_taken hf_2 hf_3 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm hlen]; simp; try omega) ?_
      by_cases h16 : 16 ≤ bs0.length
      · refine step_subs_imm_bcond_taken hf_4 hf_5 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_cs_imm hlen]; simp; try omega) ?_
        exact memset_16_to_96 hc.memset h16 (by omega) (by st_pclin) (by st_run hrun) (by inv_close) (by st_pc) (by st_reg hx0) (by st_reg hx2) (by st_pc) (by st_pc)
      · refine step_subs_imm_bcond_not_taken hf_4 hf_5 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_cs_imm hlen]; simp; try omega) ?_
        exact memset_lt16 hc.memset (by omega) (by st_pclin) (by st_run hrun) (by inv_close) (by st_pc) (by st_reg hx0) (by st_reg hx2) (by st_pc) (by st_pc)
  · rw [hPf] at hm_f; dsimp only [stdMemsetSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hx0_f, hstd_f⟩, hm_f⟩

/-! ## Placement-Generic `memcpy` -/

private theorem copySet_false (bs0 bs : List (BitVec 8)) : ByteSlice.copySet bs0 bs (fun _ => false) = bs0 := ByteSlice.ext_getD (by simp) fun i _ => by rw [ByteSlice.getD_copySet]; simp
@[local arm64_norm] private theorem extendVal_uxtx0 (v : BitVec 64) : extendVal .W64 v .UXTX 0 = v := by dsimp [extendVal]; bv_bits
@[local arm64_norm] private theorem readReg32_eq' (s : State) (r : Reg) : s.readReg32 r = (s.readReg64 r).truncate 32 := rfl
@[local arm64_norm] private theorem trunc8_zeroExtend64 (v : BitVec 8) : ((v.zeroExtend 64).truncate 32).truncate 8 = v := by bv_bits
@[local arm64_norm] private theorem trunc32_zeroExtend64 (v : BitVec 32) : (v.zeroExtend 64).truncate 32 = v := by bv_bits
private theorem ofNat64_lsr {n k : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n) >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)).symm
private theorem step_lsr64 {P : Program} {target_pc pc vx : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {rd rn : Reg} {sh : Nat} (hf : P.fetch pc = some (.bitfield .W64 .UBFM rd rn sh 63)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx : s.readReg64 rn = vx) (hnext : SepWP P target_pc ((s.writeReg64 rd (vx >>> sh)).setPC (pc + 4#64)) Q post) (hsh : sh < 64 := by decide) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; cases rd <;> rfl) hnext; dsimp [Program.evalInst, execInstWithSvc, execBitfield, State.readReg, State.writeReg, evalBitfield]
  rw [show (s.setPC pc).readReg64 rn = vx from by cases s; exact hx, Nat.mod_eq_of_lt hsh]; cases s; rfl
private theorem step_ldr8_src {P : Program} {target_pc pc src ea : BitVec 64} {s : State} {L S : SepProp} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs : List (BitVec 8)} {off : Nat}
    (hsrc : IsSrcBytes src bs S) (hpc : s.pc = pc) (hrun : s.status = .Running) (hf : P.fetch pc = some (.ldr .W32 .B8 false rt addr)) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hoff : off + 1 ≤ bs.length) (ha : src + BitVec.ofNat 64 off = ea)
    (hnext : SepWP P target_pc (((applyWriteback s wb).writeReg64 rt ((bs.getD off 0#8).zeroExtend 64)).setPC (pc + 4#64)) (L ∗ S) post) : SepWP P target_pc s (L ∗ S) post :=
  SepWP.step_ldr8 hpc hrun hf hsp haddr (hsrc.load8 hoff ha) (by dsimp [State.writeReg]; congr 2; bv_bits) hnext
private theorem step_ldr32_src {P : Program} {target_pc pc src ea : BitVec 64} {s : State} {L S : SepProp} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs : List (BitVec 8)} {off : Nat}
    (hsrc : IsSrcBytes src bs S) (hpc : s.pc = pc) (hrun : s.status = .Running) (hf : P.fetch pc = some (.ldr .W32 .W32 false rt addr)) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hoff : off + 4 ≤ bs.length) (ha : src + BitVec.ofNat 64 off = ea)
    (hnext : SepWP P target_pc (((applyWriteback s wb).writeReg64 rt ((pack32 (bs.getD off 0#8) (bs.getD (off + 1) 0#8) (bs.getD (off + 2) 0#8) (bs.getD (off + 3) 0#8)).zeroExtend 64)).setPC (pc + 4#64)) (L ∗ S) post) : SepWP P target_pc s (L ∗ S) post :=
  SepWP.step_ldr32 hpc hrun hf hsp haddr (hsrc.load32 hoff ha) (by dsimp [State.writeReg]; congr 2; bv_bits) hnext
private theorem step_ldr64_src {P : Program} {target_pc pc src ea : BitVec 64} {s : State} {L S : SepProp} {post : State → SepProp → Prop} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs : List (BitVec 8)} {off : Nat}
    (hsrc : IsSrcBytes src bs S) (hpc : s.pc = pc) (hrun : s.status = .Running) (hf : P.fetch pc = some (.ldr .W64 .X64 false rt addr)) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hoff : off + 8 ≤ bs.length) (ha : src + BitVec.ofNat 64 off = ea)
    (hnext : SepWP P target_pc (((applyWriteback s wb).writeReg64 rt (ByteSlice.readLE bs off 8)).setPC (pc + 4#64)) (L ∗ S) post) : SepWP P target_pc s (L ∗ S) post :=
  SepWP.step_ldr64 hpc hrun hf hsp haddr (hsrc.load64 hoff ha) rfl hnext
private theorem step_ldp64_src {P : Program} {target_pc pc src ea : BitVec 64} {s : State} {L S : SepProp} {post : State → SepProp → Prop} {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {bs : List (BitVec 8)} {off : Nat}
    (hsrc : IsSrcBytes src bs S) (hpc : s.pc = pc) (hrun : s.status = .Running) (hf : P.fetch pc = some (.ldp .W64 false rt1 rt2 addr)) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hoff : off + 16 ≤ bs.length) (ha : src + BitVec.ofNat 64 off = ea)
    (hnext : SepWP P target_pc ((((applyWriteback s wb).writeReg64 rt1 (ByteSlice.readLE bs off 8)).writeReg64 rt2 (ByteSlice.readLE bs (off + 8) 8)).setPC (pc + 4#64)) (L ∗ S) post) : SepWP P target_pc s (L ∗ S) post :=
  SepWP.step_ldp64 hpc hrun hf hsp haddr rfl (hsrc.load64 (by omega) ha) (hsrc.load64 (off := off + 8) (by omega) (by rw [← ha, BitVec.ofNat_add]; bv_lin)) rfl hnext

private theorem finish_ret_copy {P : Program} {pc : BitVec 64} {s0 s : State} {dst : BitVec 64} {S : SepProp} {xs ys : List (BitVec 8)}
    (hf : P.fetch pc = some (.ret (.gpr 30#5))) (hpc : s.pc = pc) (hrun : s.status = .Running) (hlr : s.readReg64 .lr = s0.readReg64 .lr) (hx0 : s.readReg64 .x0 = dst) (hinv : MemOpsInvariant s0 s) (hxs : xs = ys) :
    SepWP P (s0.readReg64 .lr) s ((dst ↦ₛ xs) ∗ S) (fun sf Q' => Q' = ((dst ↦ₛ ys) ∗ S) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  refine SepWP.step_pure (s' := s.setPC (s0.readReg64 .lr)) hpc hrun hf ?_ (by cases s; rfl) ?_
  · dsimp [Program.evalInst, execInstWithSvc, Reg.fromZRBits]; rw [show ((s.setPC pc).readReg64 (.gpr 30#5)) = s0.readReg64 .lr from by cases s; exact hlr]; cases s; rfl
  · exact SepWP.done (by cases s; rfl) (by cases s; exact hrun) ⟨by rw [hxs], by cases s; exact hx0, memOpsInv_setPC hinv⟩
private theorem memcpy_lt16 {P : Program} {entry dst src : BitVec 64} {s0 s : State} {S : SepProp} {bs0 bs : List (BitVec 8)}
    (hc : hasInstrs P entry hbMemcpyInstrs) (hsrc : IsSrcBytes src bs S) (hbs0 : bs0.length = bs.length) (hlen : bs.length < 16)
    (hpc : s.pc = entry + ins_off% 13) (hrun : s.status = .Running) (hinv : MemOpsInvariant s0 s) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length) (hx4 : s.readReg64 .x4 = src + BitVec.ofNat 64 bs.length) (hx5 : s.readReg64 .x5 = dst + BitVec.ofNat 64 bs.length) :
    SepWP P (s0.readReg64 .lr) s ((dst ↦ₛ ByteSlice.copySet bs0 bs (fun _ => false)) ∗ S) (fun sf Q => Q = ((dst ↦ₛ bs) ∗ S) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  have_instrs hc 13 22
  by_cases h8 : 8 ≤ bs.length
  · refine step_tbz_not_taken hf_13 hpc hrun hx2 (by decide) (by simp; omega) ?_
    refine step_ldr64_src (off := 0) hsrc (by st_pclin) (by st_run hrun) hf_14 rfl (by st_ea hx1) (by omega) (by bv_lin) ?_; dsimp only [applyWriteback]
    refine step_ldr64_src (off := bs.length - 8) hsrc (by st_pclin) (by st_run hrun) hf_15 rfl (by st_ea hx4) (by omega) (addr_end_sub rfl (by omega)) ?_; dsimp only [applyWriteback]
    refine step_copy_str64 (off := 0) (by st_pclin) (by st_run hrun) hf_16 rfl (by st_ea hx0) (by st_pc) (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
    refine step_copy_str64 (off := bs.length - 8) (by st_pclin) (by st_run hrun) hf_17 rfl (by st_ea hx5) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m2 hm2 => ?_; dsimp only [applyWriteback]
    exact finish_ret_copy hf_18 (by st_pclin) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (copySet_eq_self hbs0 (by intro i hi; simp; omega))
  · refine step_tbz_taken hf_13 hpc hrun hx2 (by decide) (by simp; omega) ?_
    by_cases h4 : 4 ≤ bs.length
    · refine step_tbz_not_taken hf_20 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by decide) (by simp; omega) ?_
      refine step_ldr32_src (off := 0) hsrc (by st_pclin) (by st_run hrun) hf_21 rfl (by st_ea hx1) (by omega) (by bv_lin) ?_; dsimp only [applyWriteback]
      refine step_ldr32_src (off := bs.length - 4) hsrc (by st_pclin) (by st_run hrun) hf_22 rfl (by st_ea hx4) (by omega) (addr_end_sub rfl (by omega)) ?_; dsimp only [applyWriteback]
      refine step_copy_str32 (off := 0) (by st_pclin) (by st_run hrun) hf_23 rfl (by st_ea hx0) (by st_pc) (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
      refine step_copy_str32 (off := bs.length - 4) (by st_pclin) (by st_run hrun) hf_24 rfl (by st_ea hx5) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m2 hm2 => ?_; dsimp only [applyWriteback]
      exact finish_ret_copy hf_25 (by st_pclin) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (copySet_eq_self hbs0 (by intro i hi; simp; omega))
    · refine step_tbz_taken hf_20 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by decide) (by simp; omega) ?_
      by_cases h0 : bs.length = 0
      · refine step_cbz_taken hf_26 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by simp [h0]) ?_; exact finish_ret_copy hf_34 (by st_pclin) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (copySet_eq_self hbs0 (by intro i hi; omega))
      · refine step_cbz_not_taken hf_26 (by st_pclin) (by st_run hrun) (by st_reg hx2) (ofNat64_beq_zero_false h0 (by omega)) ?_; refine step_lsr64 hf_27 (by st_pclin) (by st_run hrun) (by st_reg hx2) ?_
        refine step_ldr8_src (off := 0) hsrc (by st_pclin) (by st_run hrun) hf_28 rfl (by st_ea hx1) (by omega) (by bv_lin) ?_; dsimp only [applyWriteback]
        refine step_ldr8_src (off := bs.length - 1) hsrc (by st_pclin) (by st_run hrun) hf_29 rfl (by st_ea hx4) (by omega) (addr_end_sub rfl (by omega)) ?_; dsimp only [applyWriteback]
        refine step_ldr8_src (off := bs.length / 2) hsrc (by st_pclin) (by st_run hrun) hf_30 rfl (by simp only [evalAddrMode, arm64_norm, hx1]; rfl) (by omega) (by rw [ofNat64_lsr (k := 1) (by omega)]) ?_; dsimp only [applyWriteback]
        refine step_copy_str8 (off := 0) (by st_pclin) (by st_run hrun) hf_31 rfl (by st_ea hx0) (by st_pc) (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
        refine step_copy_str8 (off := bs.length / 2) (by st_pclin) (by st_run hrun) hf_32 rfl (by simp only [evalAddrMode, arm64_norm, hx0]; rfl) (by st_pc) (by omega) (by rw [ofNat64_lsr (k := 1) (by omega)]) fun m2 hm2 => ?_; dsimp only [applyWriteback]
        refine step_copy_str8 (off := bs.length - 1) (by st_pclin) (by st_run hrun) hf_33 rfl (by st_ea hx5) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m3 hm3 => ?_; dsimp only [applyWriteback]
        exact finish_ret_copy hf_34 (by st_pclin) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (copySet_eq_self hbs0 (by intro i hi; simp; omega))
private theorem memcpy_16_to_32 {P : Program} {entry dst src : BitVec 64} {s0 s : State} {S : SepProp} {bs0 bs : List (BitVec 8)}
    (hc : hasInstrs P entry hbMemcpyInstrs) (hsrc : IsSrcBytes src bs S) (hbs0 : bs0.length = bs.length) (hlo : 16 ≤ bs.length) (hhi : bs.length ≤ 32)
    (hpc : s.pc = entry + ins_off% 8) (hrun : s.status = .Running) (hinv : MemOpsInvariant s0 s) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src) (hx4 : s.readReg64 .x4 = src + BitVec.ofNat 64 bs.length) (hx5 : s.readReg64 .x5 = dst + BitVec.ofNat 64 bs.length) :
    SepWP P (s0.readReg64 .lr) s ((dst ↦ₛ ByteSlice.copySet bs0 bs (fun _ => false)) ∗ S) (fun sf Q => Q = ((dst ↦ₛ bs) ∗ S) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  have_instrs hc 8 5; refine step_ldp64_src (off := 0) hsrc hpc hrun hf_8 rfl (by st_ea hx1) (by omega) (by bv_lin) ?_; dsimp only [applyWriteback]
  refine step_ldp64_src (off := bs.length - 16) hsrc (by st_pclin) (by st_run hrun) hf_9 rfl (by st_ea hx4) (by omega) (addr_end_sub rfl (by omega)) ?_; dsimp only [applyWriteback]
  refine step_copy_stp64 (off := 0) (by st_pclin) (by st_run hrun) hf_10 rfl (by st_ea hx0) (by st_pc) (by st_pc) (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
  refine step_copy_stp64 (off := bs.length - 16) (by st_pclin) (by st_run hrun) hf_11 rfl (by st_ea hx5) (by st_pc) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m2 hm2 => ?_; dsimp only [applyWriteback]
  exact finish_ret_copy hf_12 (by st_pclin) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (copySet_eq_self hbs0 (by intro i hi; simp; omega))
private theorem memcpy_33_to_128 {P : Program} {entry dst src : BitVec 64} {s0 s : State} {S : SepProp} {bs0 bs : List (BitVec 8)}
    (hc : hasInstrs P entry hbMemcpyInstrs) (hsrc : IsSrcBytes src bs S) (hbs0 : bs0.length = bs.length) (hlo : 32 < bs.length) (hhi : bs.length ≤ 128)
    (hpc : s.pc = entry + ins_off% 36) (hrun : s.status = .Running) (hinv : MemOpsInvariant s0 s) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length) (hx4 : s.readReg64 .x4 = src + BitVec.ofNat 64 bs.length) (hx5 : s.readReg64 .x5 = dst + BitVec.ofNat 64 bs.length) :
    SepWP P (s0.readReg64 .lr) s ((dst ↦ₛ ByteSlice.copySet bs0 bs (fun _ => false)) ∗ S) (fun sf Q => Q = ((dst ↦ₛ bs) ∗ S) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  have_instrs hc 36 27; refine step_ldp64_src (off := 0) hsrc hpc hrun hf_36 rfl (by st_ea hx1) (by omega) (by bv_lin) ?_; dsimp only [applyWriteback]
  refine step_ldp64_src (off := 16) hsrc (by st_pclin) (by st_run hrun) hf_37 rfl (by st_ea hx1) (by omega) (by bv_lin) ?_; dsimp only [applyWriteback]
  refine step_ldp64_src (off := bs.length - 32) hsrc (by st_pclin) (by st_run hrun) hf_38 rfl (by st_ea hx4) (by omega) (addr_end_sub rfl (by omega)) ?_; dsimp only [applyWriteback]
  refine step_ldp64_src (off := bs.length - 16) hsrc (by st_pclin) (by st_run hrun) hf_39 rfl (by st_ea hx4) (by omega) (addr_end_sub rfl (by omega)) ?_; dsimp only [applyWriteback]
  by_cases h64 : 64 < bs.length
  · refine step_subs_imm_bcond_taken hf_40 hf_41 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm (by omega)]; simp; try omega) ?_
    refine step_ldp64_src (off := 32) hsrc (by st_pclin) (by st_run hrun) hf_48 rfl (by st_ea hx1) (by omega) (by bv_lin) ?_; dsimp only [applyWriteback]
    refine step_ldp64_src (off := 48) hsrc (by st_pclin) (by st_run hrun) hf_49 rfl (by st_ea hx1) (by omega) (by bv_lin) ?_; dsimp only [applyWriteback]
    by_cases h96 : bs.length ≤ 96
    · refine step_subs_imm_bcond_taken hf_50 hf_51 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_ls_imm (by omega)]; simp; try omega) ?_
      refine step_copy_stp64 (off := 0) (by st_pclin) (by st_run hrun) hf_56 rfl (by st_ea hx0) (by st_pc) (by st_pc) (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
      refine step_copy_stp64 (off := 16) (by st_pclin) (by st_run hrun) hf_57 rfl (by st_ea hx0) (by st_pc) (by st_pc) (by omega) (by bv_lin) fun m2 hm2 => ?_; dsimp only [applyWriteback]
      refine step_copy_stp64 (off := 32) (by st_pclin) (by st_run hrun) hf_58 rfl (by st_ea hx0) (by st_pc) (by st_pc) (by omega) (by bv_lin) fun m3 hm3 => ?_; dsimp only [applyWriteback]
      refine step_copy_stp64 (off := 48) (by st_pclin) (by st_run hrun) hf_59 rfl (by st_ea hx0) (by st_pc) (by st_pc) (by omega) (by bv_lin) fun m4 hm4 => ?_; dsimp only [applyWriteback]
      refine step_copy_stp64 (off := bs.length - 32) (by st_pclin) (by st_run hrun) hf_60 rfl (by st_ea hx5) (by st_pc) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m5 hm5 => ?_; dsimp only [applyWriteback]
      refine step_copy_stp64 (off := bs.length - 16) (by st_pclin) (by st_run hrun) hf_61 rfl (by st_ea hx5) (by st_pc) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m6 hm6 => ?_; dsimp only [applyWriteback]
      exact finish_ret_copy hf_62 (by st_pclin) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (copySet_eq_self hbs0 (by intro i hi; simp; omega))
    · refine step_subs_imm_bcond_not_taken hf_50 hf_51 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_ls_imm (by omega)]; simp; try omega) ?_
      refine step_ldp64_src (off := bs.length - 64) hsrc (by st_pclin) (by st_run hrun) hf_52 rfl (by st_ea hx4) (by omega) (addr_end_sub rfl (by omega)) ?_; dsimp only [applyWriteback]
      refine step_ldp64_src (off := bs.length - 48) hsrc (by st_pclin) (by st_run hrun) hf_53 rfl (by st_ea hx4) (by omega) (addr_end_sub rfl (by omega)) ?_; dsimp only [applyWriteback]
      refine step_copy_stp64 (off := bs.length - 64) (by st_pclin) (by st_run hrun) hf_54 rfl (by st_ea hx5) (by st_pc) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m1 hm1 => ?_; dsimp only [applyWriteback]
      refine step_copy_stp64 (off := bs.length - 48) (by st_pclin) (by st_run hrun) hf_55 rfl (by st_ea hx5) (by st_pc) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m2 hm2 => ?_; dsimp only [applyWriteback]
      refine step_copy_stp64 (off := 0) (by st_pclin) (by st_run hrun) hf_56 rfl (by st_ea hx0) (by st_pc) (by st_pc) (by omega) (by bv_lin) fun m3 hm3 => ?_; dsimp only [applyWriteback]
      refine step_copy_stp64 (off := 16) (by st_pclin) (by st_run hrun) hf_57 rfl (by st_ea hx0) (by st_pc) (by st_pc) (by omega) (by bv_lin) fun m4 hm4 => ?_; dsimp only [applyWriteback]
      refine step_copy_stp64 (off := 32) (by st_pclin) (by st_run hrun) hf_58 rfl (by st_ea hx0) (by st_pc) (by st_pc) (by omega) (by bv_lin) fun m5 hm5 => ?_; dsimp only [applyWriteback]
      refine step_copy_stp64 (off := 48) (by st_pclin) (by st_run hrun) hf_59 rfl (by st_ea hx0) (by st_pc) (by st_pc) (by omega) (by bv_lin) fun m6 hm6 => ?_; dsimp only [applyWriteback]
      refine step_copy_stp64 (off := bs.length - 32) (by st_pclin) (by st_run hrun) hf_60 rfl (by st_ea hx5) (by st_pc) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m7 hm7 => ?_; dsimp only [applyWriteback]
      refine step_copy_stp64 (off := bs.length - 16) (by st_pclin) (by st_run hrun) hf_61 rfl (by st_ea hx5) (by st_pc) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m8 hm8 => ?_; dsimp only [applyWriteback]
      exact finish_ret_copy hf_62 (by st_pclin) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (copySet_eq_self hbs0 (by intro i hi; simp; omega))
  · refine step_subs_imm_bcond_not_taken hf_40 hf_41 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm (by omega)]; simp; try omega) ?_
    refine step_copy_stp64 (off := 0) (by st_pclin) (by st_run hrun) hf_42 rfl (by st_ea hx0) (by st_pc) (by st_pc) (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
    refine step_copy_stp64 (off := 16) (by st_pclin) (by st_run hrun) hf_43 rfl (by st_ea hx0) (by st_pc) (by st_pc) (by omega) (by bv_lin) fun m2 hm2 => ?_; dsimp only [applyWriteback]
    refine step_copy_stp64 (off := bs.length - 32) (by st_pclin) (by st_run hrun) hf_44 rfl (by st_ea hx5) (by st_pc) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m3 hm3 => ?_; dsimp only [applyWriteback]
    refine step_copy_stp64 (off := bs.length - 16) (by st_pclin) (by st_run hrun) hf_45 rfl (by st_ea hx5) (by st_pc) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m4 hm4 => ?_; dsimp only [applyWriteback]
    exact finish_ret_copy hf_46 (by st_pclin) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (copySet_eq_self hbs0 (by intro i hi; simp; omega))

private def Regs8 (bs : List (BitVec 8)) (k : Nat) (s : State) : Prop :=
  s.readReg64 .x6 = ByteSlice.readLE bs k 8 ∧ s.readReg64 .x7 = ByteSlice.readLE bs (k + 8) 8 ∧ s.readReg64 .x8 = ByteSlice.readLE bs (k + 16) 8 ∧ s.readReg64 .x9 = ByteSlice.readLE bs (k + 24) 8 ∧
  s.readReg64 .x10 = ByteSlice.readLE bs (k + 32) 8 ∧ s.readReg64 .x11 = ByteSlice.readLE bs (k + 40) 8 ∧ s.readReg64 .x12 = ByteSlice.readLE bs (k + 48) 8 ∧ s.readReg64 .x13 = ByteSlice.readLE bs (k + 56) 8
private theorem cov_ext16x4 {p : Nat → Bool} {k : Nat} (a k' : Nat) (hp : ∀ i < k, p i = true) (ha : a ≤ k) (hk' : k' ≤ a + 64) :
    ∀ i < k', ((((p i || (decide (a ≤ i) && decide (i < a + 16))) || (decide (a + 16 ≤ i) && decide (i < a + 16 + 16))) || (decide (a + 32 ≤ i) && decide (i < a + 32 + 16))) || (decide (a + 48 ≤ i) && decide (i < a + 48 + 16))) = true := by
  intro i hi; by_cases h : i < k
  · simp [hp i h]
  · simp; omega
private theorem memcpy_tail {P : Program} {entry dst src : BitVec 64} {s0 s : State} {S : SepProp} {bs0 bs : List (BitVec 8)} {k : Nat} {p : Nat → Bool}
    (hc : hasInstrs P entry hbMemcpyInstrs) (hsrc : IsSrcBytes src bs S) (hbs0 : bs0.length = bs.length) (hk1 : k + 64 ≤ bs.length) (hk2 : bs.length ≤ k + 128)
    (hp : ∀ i < k, p i = true) (hpc : s.pc = entry + ins_off% 86) (hrun : s.status = .Running) (hinv : MemOpsInvariant s0 s) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hx0 : s.readReg64 .x0 = dst) (hx3 : s.readReg64 .x3 = dst + BitVec.ofNat 64 k - 16#64) (hx4 : s.readReg64 .x4 = src + BitVec.ofNat 64 bs.length) (hx5 : s.readReg64 .x5 = dst + BitVec.ofNat 64 bs.length) (hr : Regs8 bs k s) :
    SepWP P (s0.readReg64 .lr) s ((dst ↦ₛ ByteSlice.copySet bs0 bs p) ∗ S) (fun sf Q => Q = ((dst ↦ₛ bs) ∗ S) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  rcases hr with ⟨hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13⟩; have_instrs hc 86 13
  refine step_ldp64_src (off := bs.length - 64) hsrc hpc hrun hf_86 rfl (by st_ea hx4) (by omega) (addr_end_sub rfl (by omega)) ?_; dsimp only [applyWriteback]
  refine step_copy_stp64 (off := k) (by st_pclin) (by st_run hrun) hf_87 rfl (by st_ea hx3) (by st_reg hx6) (by st_reg hx7) (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
  refine step_ldp64_src (off := bs.length - 48) hsrc (by st_pclin) (by st_run hrun) hf_88 rfl (by st_ea hx4) (by omega) (addr_end_sub rfl (by omega)) ?_; dsimp only [applyWriteback]
  refine step_copy_stp64 (off := k + 16) (by st_pclin) (by st_run hrun) hf_89 rfl (by st_ea hx3) (by st_reg hx8) (by st_reg hx9) (by omega) (by rw [BitVec.ofNat_add]; bv_lin) fun m2 hm2 => ?_; dsimp only [applyWriteback]
  refine step_ldp64_src (off := bs.length - 32) hsrc (by st_pclin) (by st_run hrun) hf_90 rfl (by st_ea hx4) (by omega) (addr_end_sub rfl (by omega)) ?_; dsimp only [applyWriteback]
  refine step_copy_stp64 (off := k + 32) (by st_pclin) (by st_run hrun) hf_91 rfl (by st_ea hx3) (by st_reg hx10) (by st_reg hx11) (by omega) (by rw [BitVec.ofNat_add]; bv_lin) fun m3 hm3 => ?_; dsimp only [applyWriteback]
  refine step_ldp64_src (off := bs.length - 16) hsrc (by st_pclin) (by st_run hrun) hf_92 rfl (by st_ea hx4) (by omega) (addr_end_sub rfl (by omega)) ?_; dsimp only [applyWriteback]
  refine step_copy_stp64 (off := k + 48) (by st_pclin) (by st_run hrun) hf_93 rfl (by st_ea hx3) (by st_reg hx12) (by st_reg hx13) (by omega) (by rw [BitVec.ofNat_add]; bv_lin) fun m4 hm4 => ?_; dsimp only [applyWriteback]
  have hp1 := cov_ext16x4 k (k + 64) hp (by omega) (by omega)
  refine step_copy_stp64 (off := bs.length - 64) (by st_pclin) (by st_run hrun) hf_94 rfl (by st_ea hx5) (by st_pc) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m5 hm5 => ?_; dsimp only [applyWriteback]
  refine step_copy_stp64 (off := bs.length - 48) (by st_pclin) (by st_run hrun) hf_95 rfl (by st_ea hx5) (by st_pc) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m6 hm6 => ?_; dsimp only [applyWriteback]
  refine step_copy_stp64 (off := bs.length - 32) (by st_pclin) (by st_run hrun) hf_96 rfl (by st_ea hx5) (by st_pc) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m7 hm7 => ?_; dsimp only [applyWriteback]
  refine step_copy_stp64 (off := bs.length - 16) (by st_pclin) (by st_run hrun) hf_97 rfl (by st_ea hx5) (by st_pc) (by st_pc) (by omega) (addr_end_sub rfl (by omega)) fun m8 hm8 => ?_; dsimp only [applyWriteback]
  exact finish_ret_copy hf_98 (by st_pclin) (by st_run hrun) (by st_reg hlr) (by st_reg hx0) (by inv_close) (copySet_eq_self hbs0 (by
    intro i hi; by_cases h : i < k + 64
    · simp [hp1 i h]
    · simp; omega))
private theorem memcpy_loop {P : Program} {entry dst src : BitVec 64} {s0 : State} {S : SepProp} {bs0 bs : List (BitVec 8)}
    (hc : hasInstrs P entry hbMemcpyInstrs) (hsrc : IsSrcBytes src bs S) (hbs0 : bs0.length = bs.length) (hbound : bs.length + 396 ≤ 2 ^ 64) :
    ∀ (rem : Nat) {k : Nat} {p : Nat → Bool} (s : State), k + 128 + rem = bs.length → 1 ≤ rem → (∀ i < k, p i = true) →
      s.pc = entry + ins_off% 76 → s.status = .Running → MemOpsInvariant s0 s → s.readReg64 .lr = s0.readReg64 .lr → s.readReg64 .x0 = dst →
      s.readReg64 .x1 = src + BitVec.ofNat 64 (k + 48) → s.readReg64 .x2 = BitVec.ofNat 64 rem → s.readReg64 .x3 = dst + BitVec.ofNat 64 k - 16#64 →
      s.readReg64 .x4 = src + BitVec.ofNat 64 bs.length → s.readReg64 .x5 = dst + BitVec.ofNat 64 bs.length → Regs8 bs k s →
      SepWP P (s0.readReg64 .lr) s ((dst ↦ₛ ByteSlice.copySet bs0 bs p) ∗ S) (fun sf Q => Q = ((dst ↦ₛ bs) ∗ S) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  intro rem; induction rem using Nat.strongRecOn with | ind rem ih => ?_
  intro k p s hsum hrem hp hpc hrun hinv hlr hx0 hx1 hx2 hx3 hx4 hx5 hr; rcases hr with ⟨hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13⟩; have_instrs hc 76 10
  refine step_copy_stp64 (off := k) hpc hrun hf_76 rfl (by st_ea hx3) hx6 hx7 (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
  refine step_ldp64_src (off := k + 64) hsrc (by st_pclin) (by st_run hrun) hf_77 rfl (by st_ea hx1) (by omega) (by rw [BitVec.ofNat_add, BitVec.ofNat_add]; bv_lin) ?_; dsimp only [applyWriteback]
  refine step_copy_stp64 (off := k + 16) (by st_pclin) (by st_run hrun) hf_78 rfl (by st_ea hx3) (by st_reg hx8) (by st_reg hx9) (by omega) (by rw [BitVec.ofNat_add]; bv_lin) fun m2 hm2 => ?_; dsimp only [applyWriteback]
  refine step_ldp64_src (off := k + 80) hsrc (by st_pclin) (by st_run hrun) hf_79 rfl (by st_ea hx1) (by omega) (by rw [BitVec.ofNat_add, BitVec.ofNat_add]; bv_lin) ?_; dsimp only [applyWriteback]
  refine step_copy_stp64 (off := k + 32) (by st_pclin) (by st_run hrun) hf_80 rfl (by st_ea hx3) (by st_reg hx10) (by st_reg hx11) (by omega) (by rw [BitVec.ofNat_add]; bv_lin) fun m3 hm3 => ?_; dsimp only [applyWriteback]
  refine step_ldp64_src (off := k + 96) hsrc (by st_pclin) (by st_run hrun) hf_81 rfl (by st_ea hx1) (by omega) (by rw [BitVec.ofNat_add, BitVec.ofNat_add]; bv_lin) ?_; dsimp only [applyWriteback]
  refine step_copy_stp64 (off := k + 48) (by st_pclin) (by st_run hrun) hf_82 rfl (by st_ea hx3) (by st_reg hx12) (by st_reg hx13) (by omega) (by rw [BitVec.ofNat_add]; bv_lin) fun m4 hm4 => ?_; dsimp only [applyWriteback]
  refine step_ldp64_src (off := k + 112) hsrc (by st_pclin) (by st_run hrun) hf_83 rfl (by st_ea hx1) (by omega) (by rw [BitVec.ofNat_add, BitVec.ofNat_add]; bv_lin) ?_; dsimp only [applyWriteback]
  have hp' := cov_ext16x4 k (k + 64) hp (by omega) (by omega)
  by_cases h64 : 64 < rem
  · refine step_subs_imm_bcond_taken hf_84 hf_85 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm (by omega)]; simp; try omega) ?_
    exact ih (rem - 64) (by omega) _ (k := k + 64) (by omega) (by omega) hp' (by st_pclin) (by st_run hrun) (by inv_close) (by st_reg hlr) (by st_reg hx0)
      (by simp only [arm64_norm, BitVec.ofNat_add]; bv_lin) (by simp only [arm64_norm]; exact ofNat64_sub (b := 64) (by omega)) (by simp only [arm64_norm, BitVec.ofNat_add]; bv_lin) (by st_reg hx4) (by st_reg hx5)
      ⟨by st_pc, by st_pc, by st_pc, by st_pc, by st_pc, by st_pc, by st_pc, by st_pc⟩
  · refine step_subs_imm_bcond_not_taken hf_84 hf_85 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm (by omega)]; simp; try omega) ?_
    exact memcpy_tail hc hsrc hbs0 (k := k + 64) (by omega) (by omega) hp' (by st_pclin) (by st_run hrun) (by inv_close) (by st_reg hlr) (by st_reg hx0)
      (by simp only [arm64_norm, BitVec.ofNat_add]; bv_lin) (by st_reg hx4) (by st_reg hx5) ⟨by st_pc, by st_pc, by st_pc, by st_pc, by st_pc, by st_pc, by st_pc, by st_pc⟩
private theorem memcpy_gt128 {P : Program} {entry dst src : BitVec 64} {s0 s : State} {S : SepProp} {bs0 bs : List (BitVec 8)}
    (hc : hasInstrs P entry hbMemcpyInstrs) (hsrc : IsSrcBytes src bs S) (hbs0 : bs0.length = bs.length) (hgt : 128 < bs.length) (hbound : bs.length + 396 ≤ 2 ^ 64)
    (hpc : s.pc = entry + ins_off% 64) (hrun : s.status = .Running) (hinv : MemOpsInvariant s0 s) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length) (hx4 : s.readReg64 .x4 = src + BitVec.ofNat 64 bs.length) (hx5 : s.readReg64 .x5 = dst + BitVec.ofNat 64 bs.length) :
    SepWP P (s0.readReg64 .lr) s ((dst ↦ₛ ByteSlice.copySet bs0 bs (fun _ => false)) ∗ S) (fun sf Q => Q = ((dst ↦ₛ bs) ∗ S) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  have_instrs hc 64 12; let r16 := dst.toNat % 16; let d := 16 - r16; have hr16 : r16 < 16 := Nat.mod_lt _ (by omega)
  have hd_eq : BitVec.ofNat 64 d = 16#64 - BitVec.ofNat 64 r16 := by rw [show d = 16 - r16 from rfl, ← ofNat64_sub (by omega)]
  refine step_ldp64_src (off := 0) hsrc hpc hrun hf_64 rfl (by st_ea hx1) (by omega) (by bv_lin) ?_; dsimp only [applyWriteback]
  refine step_and64_imm hf_65 (by st_pclin) (by st_run hrun) (by st_reg hx0) ?_; refine step_and64_imm hf_66 (by st_pclin) (by st_run hrun) (by st_reg hx0) ?_
  refine step_sub_lsl hf_67 (by st_pclin) (by st_run hrun) (by st_reg hx1) (by st_pc) ?_; refine step_add_reg hf_68 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by st_pc) ?_
  have hsrc_sub : src - (dst &&& 15#64) = src - BitVec.ofNat 64 r16 := by rw [← ofNat_mod_16 dst]
  have hx2_add : BitVec.ofNat 64 bs.length + (dst &&& 15#64) = BitVec.ofNat 64 (bs.length + r16) := by rw [← ofNat_mod_16 dst, BitVec.ofNat_add]
  refine step_ldp64_src (off := d) hsrc (by st_pclin) (by st_run hrun) hf_69 rfl (by simp only [evalAddrMode, arm64_norm]; rfl) (by omega) (by rw [hsrc_sub, hd_eq]; bv_lin) ?_; dsimp only [applyWriteback]
  refine step_copy_stp64 (off := 0) (by st_pclin) (by st_run hrun) hf_70 rfl (by st_ea hx0) (by st_pc) (by st_pc) (by omega) (by bv_lin) fun m1 hm1 => ?_; dsimp only [applyWriteback]
  have hpd : ∀ i < d, (false || (decide (0 ≤ i) && decide (i < 16))) = true := by intro i hi; simp; omega
  refine step_ldp64_src (off := d + 16) hsrc (by st_pclin) (by st_run hrun) hf_71 rfl (by simp only [evalAddrMode, arm64_norm]; rfl) (by omega) (by rw [hsrc_sub, BitVec.ofNat_add, hd_eq]; bv_lin) ?_; dsimp only [applyWriteback]
  refine step_ldp64_src (off := d + 32) hsrc (by st_pclin) (by st_run hrun) hf_72 rfl (by simp only [evalAddrMode, arm64_norm]; rfl) (by omega) (by rw [hsrc_sub, BitVec.ofNat_add, hd_eq]; bv_lin) ?_; dsimp only [applyWriteback]
  refine step_ldp64_src (off := d + 48) hsrc (by st_pclin) (by st_run hrun) hf_73 rfl (by simp only [evalAddrMode, arm64_norm]; rfl) (by omega) (by rw [hsrc_sub, BitVec.ofNat_add, hd_eq]; bv_lin) ?_; dsimp only [applyWriteback]
  by_cases hle : bs.length + r16 ≤ 144
  · refine step_subs_imm_bcond_taken (vx := BitVec.ofNat 64 (bs.length + r16)) hf_74 hf_75 (by st_pclin) (by st_run hrun) (by simp only [arm64_norm, hx2_add]) (by rw [cond_ls_imm (by omega)]; simp; try omega) ?_
    exact memcpy_tail hc hsrc hbs0 (k := d) (by omega) (by omega) hpd (by st_pclin) (by st_run hrun) (by inv_close) (by st_reg hlr) (by st_reg hx0)
      (by simp only [arm64_norm]; simp (discharger := decide) only [and_not15_eq]; change dst - BitVec.ofNat 64 r16 = dst + BitVec.ofNat 64 d - 16#64; rw [hd_eq]; bv_lin)
      (by st_reg hx4) (by st_reg hx5) ⟨by st_pc, by st_pc, by st_pc, by st_pc, by st_pc, by st_pc, by st_pc, by st_pc⟩
  · refine step_subs_imm_bcond_not_taken (vx := BitVec.ofNat 64 (bs.length + r16)) hf_74 hf_75 (by st_pclin) (by st_run hrun) (by simp only [arm64_norm, hx2_add]) (by rw [cond_ls_imm (by omega)]; simp; try omega) ?_
    exact memcpy_loop hc hsrc hbs0 hbound (bs.length + r16 - 144) _ (k := d) (by omega) (by omega) hpd (by st_pclin) (by st_run hrun) (by inv_close)
      (by st_reg hlr) (by st_reg hx0) (by simp only [arm64_norm, hsrc_sub, BitVec.ofNat_add, hd_eq]; bv_lin) (by simp only [arm64_norm]; exact ofNat64_sub (b := 144) (by omega))
      (by simp only [arm64_norm]; simp (discharger := decide) only [and_not15_eq]; change dst - BitVec.ofNat 64 r16 = dst + BitVec.ofNat 64 d - 16#64; rw [hd_eq]; bv_lin)
      (by st_reg hx4) (by st_reg hx5) ⟨by st_pc, by st_pc, by st_pc, by st_pc, by st_pc, by st_pc, by st_pc, by st_pc⟩

private theorem memcpy_gen_ok {P : Program} {entry dst src : BitVec 64} {s0 : State} {S : SepProp} {bs0 bs : List (BitVec 8)}
    (hc : hasInstrs P entry hbMemcpyInstrs) (hsrc : IsSrcBytes src bs S) (hbs0 : bs0.length = bs.length) (hlen : bs.length < 2 ^ 64)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running) (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src) (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length) :
    SepWP P (s0.readReg64 .lr) s0 ((dst ↦ₛ ByteSlice.copySet bs0 bs (fun _ => false)) ∗ S) (fun sf Q => Q = ((dst ↦ₛ bs) ∗ S) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  apply sepWP_with_codeLoaded; intro R' hm' hL
  have hbound : bs.length + 396 ≤ 2 ^ 64 := by rw [copySet_false, sepConj_assoc] at hm'; rw [← hbs0]; exact writable_len_add_code_le hL hc hm' (by omega) (by decide)
  have_instrs hc 0 8; have hinv0 := MemOpsInvariant.rfl s0
  refine step_add_reg hf_0 hpc hrun hx1 hx2 ?_; refine step_add_reg hf_1 (by st_pclin) (by st_run hrun) (by st_reg hx0) (by st_reg hx2) ?_
  by_cases h128 : 128 < bs.length
  · refine step_subs_imm_bcond_taken hf_2 hf_3 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm hlen]; simp; try omega) ?_
    exact memcpy_gt128 hc hsrc hbs0 h128 hbound (by st_pclin) (by st_run hrun) (by inv_close) (by st_pc) (by st_reg hx0) (by st_reg hx1) (by st_reg hx2) (by st_pc) (by st_pc)
  · refine step_subs_imm_bcond_not_taken hf_2 hf_3 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm hlen]; simp; try omega) ?_
    by_cases h32 : 32 < bs.length
    · refine step_subs_imm_bcond_taken hf_4 hf_5 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm hlen]; simp; try omega) ?_
      exact memcpy_33_to_128 hc hsrc hbs0 h32 (by omega) (by st_pclin) (by st_run hrun) (by inv_close) (by st_pc) (by st_reg hx0) (by st_reg hx1) (by st_reg hx2) (by st_pc) (by st_pc)
    · refine step_subs_imm_bcond_not_taken hf_4 hf_5 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_hi_imm hlen]; simp; try omega) ?_
      by_cases h16 : bs.length < 16
      · refine step_subs_imm_bcond_taken hf_6 hf_7 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_cc_imm hlen]; simp; try omega) ?_
        exact memcpy_lt16 hc hsrc hbs0 h16 (by st_pclin) (by st_run hrun) (by inv_close) (by st_pc) (by st_reg hx0) (by st_reg hx1) (by st_reg hx2) (by st_pc) (by st_pc)
      · refine step_subs_imm_bcond_not_taken hf_6 hf_7 (by st_pclin) (by st_run hrun) (by st_reg hx2) (by rw [cond_cc_imm hlen]; simp; try omega) ?_
        exact memcpy_16_to_32 hc hsrc hbs0 (by omega) (by omega) (by st_pclin) (by st_run hrun) (by inv_close) (by st_pc) (by st_reg hx0) (by st_reg hx1) (by st_pc) (by st_pc)

theorem hbMemcpy_ok {P : Program} {C : HbCliLayout} (hc : HbMemOpsCode P C) : subroutine_ok P C.std.memcpyAddr stdMemcpySpec := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre _hsp; dsimp only [stdMemcpySpec] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩; rw [memRegion_eq_exists_bytes dst bs.length (by omega), sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hmem
  rcases hmem with ⟨bs0, hmem⟩; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hmem; rcases hmem with ⟨hbs0, hmem⟩
  refine ⟨(dst ↦ₛ ByteSlice.copySet bs0 bs (fun _ => false)) ∗ (src ↦ₛ bs), by rwa [copySet_false, sepConj_assoc], ?_⟩
  refine SepWP.mono (memcpy_gen_ok hc.memcpy (isSrcBytes_rw src bs) hbs0 hlen hpc hrun hx0 hx1 hx2) (fun sf P_f _ _ ⟨hPf, hx0_f, hsp_f, hcs_f, hstd_f⟩ => ⟨fun hm_f => ?_, hsp_f, hcs_f⟩)
  rw [hPf] at hm_f; dsimp only [stdMemcpySpec]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hx0_f, hstd_f⟩, hm_f⟩

theorem hbMemcpy_ro_ok {P : Program} {C : HbCliLayout} (hc : HbMemOpsCode P C) : subroutine_ok P C.std.memcpyAddr stdMemcpyROSpec := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre _hsp; dsimp only [stdMemcpyROSpec] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩; rw [memRegion_eq_exists_bytes dst bs.length (by omega), sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hmem
  rcases hmem with ⟨bs0, hmem⟩; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hmem; rcases hmem with ⟨hbs0, hmem⟩
  refine ⟨(dst ↦ₛ ByteSlice.copySet bs0 bs (fun _ => false)) ∗ (src ↦ᵣ bs), by rwa [copySet_false, sepConj_assoc], ?_⟩
  refine SepWP.mono (memcpy_gen_ok hc.memcpy (isSrcBytes_ro src bs) hbs0 hlen hpc hrun hx0 hx1 hx2) (fun sf P_f _ _ ⟨hPf, hx0_f, hsp_f, hcs_f, hstd_f⟩ => ⟨fun hm_f => ?_, hsp_f, hcs_f⟩)
  rw [hPf] at hm_f; dsimp only [stdMemcpyROSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hx0_f, hstd_f⟩, hm_f⟩

theorem hbStdMemOps {P : Program} {C : HbCliLayout} (hc : HbMemOpsCode P C) : StdMemOps P C.std.memcpyAddr C.std.memsetAddr := ⟨hbMemset_ok hc, hbMemcpy_ok hc, hbMemcpy_ro_ok hc⟩
theorem hbStdMemOps_nonVm {P : Program} {C : HbCliLayout} (hc : HbMemOpsCode P C) : StdMemOps (P.withSvc nonVmSvc) C.std.memcpyAddr C.std.memsetAddr := hbStdMemOps (hc.withSvc nonVmSvc)

/-! ## Disjoint `memmove` and `withCodeInv` Lifts -/

private theorem memOpsInv_trans {s0 s1 s2 : State} (h1 : MemOpsInvariant s0 s1) (h2 : MemOpsInvariant s1 s2) : MemOpsInvariant s0 s2 := by
  rcases h1 with ⟨sp1, cs1, f1, t1, tp1, sa1, b1, bs1, pm1, p1⟩; rcases h2 with ⟨sp2, cs2, f2, t2, tp2, sa2, b2, bs2, pm2, p2⟩
  exact ⟨sp2.trans sp1, cs1.trans cs2, f2.trans f1, t2.trans t1, tp2.trans tp1, sa2.trans sa1, b2.trans b1, bs2.trans bs1, pm2.trans pm1, fun a => (p2 a).trans (p1 a)⟩
@[local arm64_norm] private theorem pstate_setPC' (s : State) (p : BitVec 64) : (s.setPC p).pstate = s.pstate := by cases s; rfl
@[local arm64_norm] private theorem pstate_setPState' (s : State) (p : PState) : (s.setPState p).pstate = p := by cases s; rfl
@[local arm64_norm] private theorem pstate_writeReg64' (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).pstate = s.pstate := by cases s; cases r <;> rfl
@[local arm64_norm] private theorem bv64_add_zero (v : BitVec 64) : v + 0#64 = v := BitVec.add_zero v
@[local arm64_norm] private theorem bv64_sub_zero (v : BitVec 64) : v - 0#64 = v := BitVec.sub_zero v
@[local arm64_norm] private theorem bv64_sub_self (v : BitVec 64) : v - v = 0#64 := BitVec.sub_self v
@[local arm64_norm] private theorem bv64_zero_shl (n : Nat) : (0#64 : BitVec 64) <<< n = 0#64 := BitVec.zero_shiftLeft n
@[local arm64_norm] private theorem bv64_zero_shr (n : Nat) : (0#64 : BitVec 64) >>> n = 0#64 := BitVec.zero_ushiftRight
@[local arm64_norm] private theorem bv64_zero_and (m : BitVec 64) : 0#64 &&& m = 0#64 := BitVec.zero_and
private theorem step_b {P : Program} {target_pc pc off : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    (hf : P.fetch pc = some (.b off)) (hpc : s.pc = pc) (hrun : s.status = .Running) (hnext : SepWP P target_pc (s.setPC (pc + off)) Q post) : SepWP P target_pc s Q post :=
  SepWP.step_pure hpc hrun hf (by cases s; rfl) (by cases s; rfl) hnext
private theorem step_bcond_taken {P : Program} {target_pc pc off : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {cond : CondCode} {ps : PState} (hf : P.fetch pc = some (.bCond cond off)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hps : s.pstate = ps) (hc : ConditionHolds cond ps = true) (hnext : SepWP P target_pc (s.setPC (pc + off)) Q post) : SepWP P target_pc s Q post :=
  SepWP.step_pure hpc hrun hf (by dsimp [Program.evalInst, execInstWithSvc]; rw [show (s.setPC pc).pstate = ps from by cases s; exact hps, hc]; cases s; rfl) (by cases s; rfl) hnext
private theorem step_bcond_not_taken {P : Program} {target_pc pc off : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {cond : CondCode} {ps : PState} (hf : P.fetch pc = some (.bCond cond off)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hps : s.pstate = ps) (hc : ConditionHolds cond ps = false) (hnext : SepWP P target_pc (s.setPC (pc + 4#64)) Q post) : SepWP P target_pc s Q post :=
  SepWP.step_pure hpc hrun hf (by dsimp [Program.evalInst, execInstWithSvc]; rw [show (s.setPC pc).pstate = ps from by cases s; exact hps, hc]; cases s; rfl) (by cases s; rfl) hnext
private theorem step_orr_reg {P : Program} {target_pc pc vm : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {rd rm : Reg} (hf : P.fetch pc = some (.logicalShift .W64 .ORR rd .xzr rm .LSL 0)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hm : s.readReg64 rm = vm) (hnext : SepWP P target_pc ((s.writeReg64 rd vm).setPC (pc + 4#64)) Q post) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; cases rd <;> rfl) hnext; dsimp [Program.evalInst, execInstWithSvc, execLogicalShift, State.readReg, State.writeReg, shiftVal, shift64, evalLogical]
  rw [show (s.setPC pc).readReg64 .xzr = 0#64 from by cases s; rfl, show (s.setPC pc).readReg64 rm = vm from by cases s; exact hm, show (0#64 ||| (vm <<< 0)) = vm from by bv_bits]; cases s; rfl
private theorem step_eor_reg {P : Program} {target_pc pc vx vy : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {rd rn rm : Reg} (hf : P.fetch pc = some (.logicalShift .W64 .EOR rd rn rm .LSL 0)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx : s.readReg64 rn = vx) (hy : s.readReg64 rm = vy) (hnext : SepWP P target_pc ((s.writeReg64 rd (vx ^^^ vy)).setPC (pc + 4#64)) Q post) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; cases rd <;> rfl) hnext; dsimp [Program.evalInst, execInstWithSvc, execLogicalShift, State.readReg, State.writeReg, shiftVal, shift64, evalLogical]
  rw [show (s.setPC pc).readReg64 rn = vx from by cases s; exact hx, show (s.setPC pc).readReg64 rm = vy from by cases s; exact hy, show (vx ^^^ (vy <<< 0)) = vx ^^^ vy from by bv_bits]; cases s; rfl

private theorem step_movz0 {P : Program} {target_pc pc : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {rd : Reg} (hf : P.fetch pc = some (.moveWide .W64 .MOVZ rd 0#16 0)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hnext : SepWP P target_pc ((s.writeReg64 rd 0#64).setPC (pc + 4#64)) Q post) : SepWP P target_pc s Q post :=
  SepWP.step_pure hpc hrun hf (by cases s; rfl) (by cases s; cases rd <;> rfl) hnext
private theorem step_add_lsl {P : Program} {target_pc pc vx vy : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {rd rn rm : Reg} {sh : Nat} (hf : P.fetch pc = some (.addSubShift .W64 .ADD rd rn rm .LSL sh)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx : s.readReg64 rn = vx) (hy : s.readReg64 rm = vy) (hnext : SepWP P target_pc ((s.writeReg64 rd (vx + (vy <<< sh))).setPC (pc + 4#64)) Q post) (hsh : sh < 64 := by decide) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; cases rd <;> rfl) hnext; dsimp [Program.evalInst, execInstWithSvc, execAddSubShift, State.readReg, State.writeReg, shiftVal, shift64]
  rw [show (s.setPC pc).readReg64 rn = vx from by cases s; exact hx, show (s.setPC pc).readReg64 rm = vy from by cases s; exact hy, Nat.mod_eq_of_lt hsh, evalAddSub_w64_add]; cases s; rfl
private theorem step_subs_reg {P : Program} {target_pc pc vx vy : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {rn rm : Reg} (hf : P.fetch pc = some (.addSubShift .W64 .SUBS .xzr rn rm .LSL 0)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx : s.readReg64 rn = vx) (hy : s.readReg64 rm = vy) (hnext : SepWP P target_pc ((s.setPState (subsPState64 vx vy)).setPC (pc + 4#64)) Q post) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; rfl) hnext; dsimp [Program.evalInst, execInstWithSvc, execAddSubShift, State.readReg, State.writeReg, shiftVal, shift64]
  rw [show (s.setPC pc).readReg64 rn = vx from by cases s; exact hx, show (s.setPC pc).readReg64 rm = vy from by cases s; exact hy, show vy <<< (0 % 64) = vy from by bv_bits, evalAddSub_w64_subs]; cases s; rfl
private def andsPState64 (v mask : BitVec 64) : PState := { n := (v &&& mask).msb, z := (v &&& mask) == 0#64, c := false, v := false }
private theorem step_ands_imm {P : Program} {target_pc pc vx mask : BitVec 64} {s : State} {Q : SepProp} {post : State → SepProp → Prop}
    {rd rn : Reg} (hf : P.fetch pc = some (.logicalImm .W64 .ANDS rd rn mask)) (hpc : s.pc = pc) (hrun : s.status = .Running) (hx : s.readReg64 rn = vx)
    (hnext : SepWP P target_pc (((s.writeReg64 rd (vx &&& mask)).setPState (andsPState64 vx mask)).setPC (pc + 4#64)) Q post) : SepWP P target_pc s Q post := by
  refine SepWP.step_pure hpc hrun hf ?_ (by cases s; cases rd <;> rfl) hnext; dsimp [Program.evalInst, execInstWithSvc, execLogicalImm, State.readReg, State.writeReg, evalLogical, andsPState64]
  rw [show (s.setPC pc).readReg64 rn = vx from by cases s; exact hx]; cases s; cases rd <;> rfl
private theorem finish_ret_x7 {P : Program} {pc1 pc2 dst : BitVec 64} {s0 s : State} {Q : SepProp}
    (hf72 : P.fetch pc1 = some (.logicalShift .W64 .ORR (.gpr 0#5) .xzr (.gpr 7#5) .LSL 0)) (hf73 : P.fetch pc2 = some (.ret (.gpr 30#5)))
    (hpc : s.pc = pc1) (hrun : s.status = .Running) (hlr : s.readReg64 .lr = s0.readReg64 .lr) (hx7 : s.readReg64 .x7 = dst) (hinv : MemOpsInvariant s0 s) (hpc2 : pc1 + 4#64 = pc2 := by bv_lin) :
    SepWP P (s0.readReg64 .lr) s Q (fun sf Q' => Q' = Q ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  refine step_orr_reg hf72 hpc hrun hx7 ?_; refine SepWP.step_pure (s' := (s.writeReg64 (.gpr 0#5) dst).setPC (s0.readReg64 .lr)) (by rw [pc_setPC', hpc2]) (by st_run hrun) hf73 ?_ (by cases s; rfl) ?_
  · dsimp [Program.evalInst, execInstWithSvc, Reg.fromZRBits]; rw [show ((((s.writeReg64 (.gpr 0#5) dst).setPC (pc1 + 4#64)).setPC pc2).readReg64 (.gpr 30#5)) = s0.readReg64 .lr from by cases s; exact hlr]; cases s; rfl
  · exact SepWP.done (by cases s; rfl) (by st_run hrun) ⟨rfl, by st_pc, by inv_close⟩
private theorem tail_to_memcpy {P : Program} {C : HbCliLayout} {dst src : BitVec 64} {s0 s : State} {bs0 bs : List (BitVec 8)}
    (hc : HbMemOpsCode P C) (hbs0 : bs0.length = bs.length) (hlen : bs.length < 2 ^ 64) (hf26 : P.fetch (C.memmoveAddr + 104#64) = some (.b (C.std.memcpyAddr - (C.memmoveAddr + 104#64))))
    (hpc : s.pc = C.memmoveAddr + 104#64) (hrun : s.status = .Running) (hinv : MemOpsInvariant s0 s) (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length) :
    SepWP P (s0.readReg64 .lr) s ((dst ↦ₛ ByteSlice.copySet bs0 bs (fun _ => false)) ∗ (src ↦ₛ bs)) (fun sf Q => Q = ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  refine step_b hf26 hpc hrun ?_; have hlr' : (s.setPC ((C.memmoveAddr + 104#64) + (C.std.memcpyAddr - (C.memmoveAddr + 104#64)))).readReg64 .lr = s0.readReg64 .lr := by st_reg hlr
  rw [← hlr']; refine SepWP.mono (memcpy_gen_ok hc.memcpy (isSrcBytes_rw src bs) hbs0 hlen (by st_pclin) (by st_run hrun) (by st_reg hx0) (by st_reg hx1) (by st_reg hx2)) ?_
  exact fun sf Q _ _ ⟨hQ, hx0f, hinvf⟩ => ⟨hQ, hx0f, memOpsInv_trans (memOpsInv_setPC hinv) hinvf⟩
@[local arm64_norm] private theorem bv64_shl_zero (v : BitVec 64) : v <<< 0 = v := by bv_bits
private theorem memmove_zero_len {P : Program} {C : HbCliLayout} {dst src : BitVec 64} {s0 : State}
    (hc : HbMemOpsCode P C) (hpc : s0.pc = C.memmoveAddr) (hrun : s0.status = .Running) (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src) (hx2 : s0.readReg64 .x2 = 0#64) :
    SepWP P (s0.readReg64 .lr) s0 ((dst ↦ₛ ([] : List (BitVec 8))) ∗ (src ↦ₛ ([] : List (BitVec 8)))) (fun sf Q => Q = ((dst ↦ₛ []) ∗ (src ↦ₛ [])) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
  have_instrs hc.memmove 0 27; have_instrs hc.memmove 72 2; have hinv0 := MemOpsInvariant.rfl s0
  have eq0 : ConditionHolds .EQ (subsPState64 0#64 0#64) = true := by unfold subsPState64; rw [conditionHolds_eq_subs64]; rfl
  have ne0 : ConditionHolds .NE (subsPState64 0#64 0#64) = false := by unfold subsPState64; rw [conditionHolds_ne_subs64]; rfl
  refine step_orr_reg hf_0 hpc hrun hx0 ?_; refine step_orr_reg hf_1 (by st_pclin) (by st_run hrun) (by st_reg hx1) ?_
  refine step_subs_reg hf_2 (by st_pclin) (by st_run hrun) (by st_reg hx0) (by st_reg hx1) ?_; refine step_orr_reg hf_3 (by st_pclin) (by st_run hrun) (by st_reg hx2) ?_
  by_cases heq0 : ConditionHolds .EQ (subsPState64 dst src) = true
  · refine step_bcond_taken hf_4 (by st_pclin) (by st_run hrun) (by st_pc) heq0 ?_; exact finish_ret_x7 hf_72 hf_73 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) (by inv_close)
  · refine step_bcond_not_taken hf_4 (by st_pclin) (by st_run hrun) (by st_pc) (Bool.eq_false_iff.mpr heq0) ?_; refine step_sub_lsl hf_5 (by st_pclin) (by st_run hrun) (by st_reg hx1) (by st_reg hx2) ?_
    refine step_sub_lsl hf_6 (by st_pclin) (by st_run hrun) (by st_pc) (by st_reg hx2) ?_; refine step_sub_lsl hf_7 (by st_pclin) (by st_run hrun) (by st_pc) (by st_reg hx0) ?_
    refine step_subs_reg (vx := src - dst) (vy := 0#64) hf_8 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) ?_
    by_cases hls : ConditionHolds .LS (subsPState64 (src - dst) 0#64) = true
    · refine step_bcond_taken hf_9 (by st_pclin) (by st_run hrun) (by st_pc) hls ?_; rw [← copySet_false ([] : List (BitVec 8)) []]
      exact tail_to_memcpy hc rfl (by decide) hf_26 (by st_pclin) (by st_run hrun) (by inv_close) (by st_pc) (by st_reg hx0) (by st_reg hx1) (by st_reg hx2)
    · refine step_bcond_not_taken hf_9 (by st_pclin) (by st_run hrun) (by st_pc) (Bool.eq_false_iff.mpr hls) ?_; refine step_eor_reg hf_10 (by st_pclin) (by st_run hrun) (by st_reg hx1) (by st_reg hx0) ?_
      refine step_subs_reg (vx := dst) (vy := src) hf_11 (by st_pclin) (by st_run hrun) (by st_reg hx0) (by st_pc) ?_; refine step_and64_imm hf_12 (by st_pclin) (by st_run hrun) (by st_pc) ?_
      let v1 := (src ^^^ dst) &&& 7#64
      by_cases hcs : ConditionHolds .CS (subsPState64 dst src) = true
      · have_instrs hc.memmove 47 25; refine step_bcond_taken hf_13 (by st_pclin) (by st_run hrun) (by st_pc) hcs ?_
        by_cases hv1 : (v1 == 0#64) = true
        · refine step_cbz_taken (v := v1) hf_47 (by st_pclin) (by st_run hrun) (by st_pc) (by simp [hv1]) ?_; refine step_add_lsl hf_53 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) ?_
          refine step_sub_imm hf_54 (by st_pclin) (by st_run hrun) (by st_pc) ?_; refine step_ands_imm (vx := dst) hf_55 (by st_pclin) (by st_run hrun) (by st_pc) ?_
          by_cases hd7 : ConditionHolds .EQ (andsPState64 dst 7#64) = true
          · refine step_bcond_taken hf_56 (by st_pclin) (by st_run hrun) (by st_pc) hd7 ?_; refine step_and64_imm hf_62 (by st_pclin) (by st_run hrun) (by st_pc) ?_
            refine step_orr_reg hf_63 (by st_pclin) (by st_run hrun) (by st_pc) ?_; refine step_b hf_64 (by st_pclin) (by st_run hrun) ?_
            refine step_subs_reg (vx := 0#64) (vy := 0#64) hf_67 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) ?_; refine step_sub_imm hf_68 (by st_pclin) (by st_run hrun) (by st_pc) ?_
            refine step_bcond_not_taken hf_69 (by st_pclin) (by st_run hrun) (by st_pc) ne0 ?_; refine step_and64_imm hf_70 (by st_pclin) (by st_run hrun) (by st_pc) ?_; refine step_b hf_71 (by st_pclin) (by st_run hrun) ?_
            refine step_cbz_taken (v := 0#64) hf_48 (by st_pclin) (by st_run hrun) (by st_pc) rfl ?_; exact finish_ret_x7 hf_72 hf_73 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) (by inv_close)
          · refine step_bcond_not_taken hf_56 (by st_pclin) (by st_run hrun) (by st_pc) (Bool.eq_false_iff.mpr hd7) ?_; refine step_cbz_taken (v := 0#64) hf_57 (by st_pclin) (by st_run hrun) (by st_pc) rfl ?_
            exact finish_ret_x7 hf_72 hf_73 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) (by inv_close)
        · refine step_cbz_not_taken (v := v1) hf_47 (by st_pclin) (by st_run hrun) (by st_pc) (by simp [Bool.eq_false_iff.mpr hv1]) ?_; refine step_cbz_taken (v := 0#64) hf_48 (by st_pclin) (by st_run hrun) (by st_pc) rfl ?_
          exact finish_ret_x7 hf_72 hf_73 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) (by inv_close)
      · have_instrs hc.memmove 27 16; refine step_bcond_not_taken hf_13 (by st_pclin) (by st_run hrun) (by st_pc) (Bool.eq_false_iff.mpr hcs) ?_
        by_cases hv1 : (v1 == 0#64) = true
        · refine step_cbz_not_taken (v := v1) hf_14 (by st_pclin) (by st_run hrun) (by st_pc) (by simp [hv1]) ?_; refine step_add_lsl hf_15 (by st_pclin) (by st_run hrun) (by st_pc) (by st_reg hx2) ?_
          refine step_add_lsl hf_16 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) ?_; refine step_orr_reg hf_17 (by st_pclin) (by st_run hrun) (by st_reg hx0) ?_
          refine step_sub_lsl (vx := src) (vy := src) hf_18 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) ?_; refine step_ands_imm (vx := dst) hf_19 (by st_pclin) (by st_run hrun) (by st_pc) ?_
          by_cases hd7 : dst &&& 7#64 = 0#64
          · refine step_bcond_taken hf_20 (by st_pclin) (by st_run hrun) (by st_pc) (by simp [ConditionHolds, andsPState64, hd7]) ?_; refine step_lsr64 (vx := 0#64) hf_27 (by st_pclin) (by st_run hrun) (by st_pc) ?_
            refine step_and64_imm (vx := 0#64) hf_28 (by st_pclin) (by st_run hrun) (by st_pc) ?_; refine step_b hf_29 (by st_pclin) (by st_run hrun) ?_
            refine step_subs_reg (vx := 0#64) (vy := 0#64) hf_33 (by st_pclin) (by st_run hrun) (by simp only [arm64_norm, hd7]) (by st_pc) ?_; refine step_bcond_not_taken hf_34 (by st_pclin) (by st_run hrun) (by st_pc) ne0 ?_
            refine step_sub_lsl (vx := 0#64) (vy := 0#64) hf_35 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) ?_; refine step_add_lsl hf_36 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) ?_
            refine step_add_lsl hf_37 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) ?_; refine step_b hf_38 (by st_pclin) (by st_run hrun) ?_; refine step_movz0 hf_40 (by st_pclin) (by st_run hrun) ?_
            refine step_subs_reg (vx := 0#64) (vy := 0#64) hf_41 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) ?_; refine step_bcond_taken hf_42 (by st_pclin) (by st_run hrun) (by st_pc) eq0 ?_
            exact finish_ret_x7 hf_72 hf_73 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) (by inv_close)
          · refine step_bcond_not_taken hf_20 (by st_pclin) (by st_run hrun) (by st_pc) (by simp [ConditionHolds, andsPState64, hd7]) ?_; refine step_subs_reg (vx := src) (vy := src) hf_21 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) ?_
            refine step_bcond_taken hf_22 (by st_pclin) (by st_run hrun) (by st_pc) (by unfold subsPState64; rw [conditionHolds_eq_subs64]; simp) ?_
            exact finish_ret_x7 hf_72 hf_73 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) (by inv_close)
        · refine step_cbz_taken (v := v1) hf_14 (by st_pclin) (by st_run hrun) (by st_pc) (by simp [Bool.eq_false_iff.mpr hv1]) ?_; refine step_orr_reg hf_39 (by st_pclin) (by st_run hrun) (by st_reg hx0) ?_; refine step_movz0 hf_40 (by st_pclin) (by st_run hrun) ?_
          refine step_subs_reg (vx := 0#64) (vy := 0#64) hf_41 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) ?_; refine step_bcond_taken hf_42 (by st_pclin) (by st_run hrun) (by st_pc) eq0 ?_
          exact finish_ret_x7 hf_72 hf_73 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) (by inv_close)
private theorem disjoint_sub_bounds {dst src : BitVec 64} {n : Nat} (hdisj : DisjointRegions dst n src n) (hpos : 0 < n) : n ≤ (src - dst).toNat ∧ (src - dst).toNat + n ≤ 2 ^ 64 := by
  rcases hdisj with ⟨h1, h2⟩; let u := src - dst; change n ≤ u.toNat at h1; refine ⟨h1, ?_⟩
  change u.toNat + n ≤ 2 ^ 64; rw [show dst - src = 0#64 - u from by dsimp [u]; bv_lin, BitVec.toNat_sub, BitVec.toNat_ofNat] at h2; have hu := BitVec.isLt u; omega
private theorem memmove_ls_cond {dst src : BitVec 64} {n : Nat} (hpos : 0 < n) (hd1 : n ≤ (src - dst).toNat) (hd2 : (src - dst).toNat + n ≤ 2 ^ 64) :
    ConditionHolds .LS (subsPState64 ((src - BitVec.ofNat 64 n) - dst) (0#64 - (BitVec.ofNat 64 n <<< 1))) = true := by
  let u := src - dst; change n ≤ u.toNat at hd1; change u.toNat + n ≤ 2 ^ 64 at hd2
  have hsh : (BitVec.ofNat 64 n <<< 1) = BitVec.ofNat 64 (2 * n) := by rw [show (BitVec.ofNat 64 n <<< 1) = BitVec.ofNat 64 n + BitVec.ofNat 64 n from by bv_bits, ← BitVec.ofNat_add, show n + n = 2 * n from by omega]
  rw [show (src - BitVec.ofNat 64 n) - dst = u - BitVec.ofNat 64 n from by dsimp [u]; bv_lin, hsh]
  unfold subsPState64; rw [conditionHolds_ls_subs64]; simp only [BitVec.ule, decide_eq_true_eq, BitVec.toNat_sub, BitVec.toNat_ofNat]; have hu := BitVec.isLt u; omega

theorem hbMemmove_disjoint_ok {P : Program} {C : HbCliLayout} (hc : HbMemOpsCode P C) : subroutine_ok P C.memmoveAddr stdMemcpySpec := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre _hsp
  dsimp only [stdMemcpySpec] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  cases bs with
  | nil =>
    dsimp only [List.length] at hmem hx2 hlen; rw [memRegion_zero, pointsToBytes_nil] at hmem; refine ⟨(dst ↦ₛ []) ∗ (src ↦ₛ []), by simpa [pointsToBytes_nil] using hmem, ?_⟩
    refine SepWP.mono (memmove_zero_len hc hpc hrun hx0 hx1 hx2) (fun sf P_f _ _ ⟨hPf, hx0_f, hsp_f, hcs_f, hstd_f⟩ => ⟨fun hm_f => ?_, hsp_f, hcs_f⟩)
    rw [hPf] at hm_f; dsimp only [stdMemcpySpec]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hx0_f, hstd_f⟩, hm_f⟩
  | cons b0 bs' =>
    let bs := b0 :: bs'; have hpos : 0 < bs.length := by simp [bs]
    have hdisj := IsBlock.disjoint (IsBlock.memRegion dst bs.length) (IsBlock.pointsToBytes src bs) hpos hpos (by rwa [← sepConj_assoc]); rcases disjoint_sub_bounds hdisj hpos with ⟨hd1, hd2⟩
    rw [memRegion_eq_exists_bytes dst bs.length (by omega), sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hmem
    rcases hmem with ⟨bs0, hmem⟩; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hmem; rcases hmem with ⟨hbs0, hmem⟩
    refine ⟨(dst ↦ₛ ByteSlice.copySet bs0 bs (fun _ => false)) ∗ (src ↦ₛ bs), by rwa [copySet_false, sepConj_assoc], ?_⟩
    have hwp : SepWP P (s0.readReg64 .lr) s0 ((dst ↦ₛ ByteSlice.copySet bs0 bs (fun _ => false)) ∗ (src ↦ₛ bs)) (fun sf Q => Q = ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∧ sf.readReg64 .x0 = dst ∧ MemOpsInvariant s0 sf) := by
      have_instrs hc.memmove 0 10; have_instrs hc.memmove 26 1; have hinv0 := MemOpsInvariant.rfl s0
      refine step_orr_reg hf_0 hpc hrun hx0 ?_; refine step_orr_reg hf_1 (by st_pclin) (by st_run hrun) (by st_reg hx1) ?_; refine step_subs_reg hf_2 (by st_pclin) (by st_run hrun) (by st_reg hx0) (by st_reg hx1) ?_
      refine step_orr_reg hf_3 (by st_pclin) (by st_run hrun) (by st_reg hx2) ?_; refine step_bcond_not_taken hf_4 (by st_pclin) (by st_run hrun) (by st_pc) (by unfold subsPState64; rw [conditionHolds_eq_subs64, beq_eq_false_iff_ne]; intro h; subst h; simp at hd1) ?_
      refine step_sub_lsl hf_5 (by st_pclin) (by st_run hrun) (by st_reg hx1) (by st_reg hx2) ?_; refine step_sub_lsl hf_6 (by st_pclin) (by st_run hrun) (by st_pc) (by st_reg hx2) ?_; refine step_sub_lsl hf_7 (by st_pclin) (by st_run hrun) (by st_pc) (by st_reg hx0) ?_
      refine step_subs_reg (vx := (src - BitVec.ofNat 64 bs.length) - dst) (vy := 0#64 - (BitVec.ofNat 64 bs.length <<< 1)) hf_8 (by st_pclin) (by st_run hrun) (by st_pc) (by st_pc) ?_
      refine step_bcond_taken hf_9 (by st_pclin) (by st_run hrun) (by st_pc) (memmove_ls_cond hpos hd1 hd2) ?_
      exact tail_to_memcpy hc hbs0 hlen hf_26 (by st_pclin) (by st_run hrun) (by inv_close) (by st_pc) (by st_reg hx0) (by st_reg hx1) (by st_reg hx2)
    refine SepWP.mono hwp (fun sf P_f _ _ ⟨hPf, hx0_f, hsp_f, hcs_f, hstd_f⟩ => ⟨fun hm_f => ?_, hsp_f, hcs_f⟩)
    rw [hPf] at hm_f; dsimp only [stdMemcpySpec]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hx0_f, hstd_f⟩, hm_f⟩

private theorem lift_withCodeInv {α : Type} {P Q : Program} {entry : BitVec 64} {A : HbAlloc} {spec : Spec α}
    (hcall : subroutine_ok Q entry spec) (hext : ∀ pc, Q.externAt? pc = P.externAt? pc) (hsvc : Q.svc = P.svc) (hcode : ∀ m, A.CodeInv m → Q.CodeLoaded m)
    (hpan : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R')) (hex : ∀ x code R' s0 sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R')) :
    subroutine_ok P entry (withCodeInv A spec) := by
  apply subroutine_ok_of_sepWP_init; intro x R s0 hpc hrun hpre hsp; dsimp only [withCodeInv] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hinv, hpre_in⟩
  refine ⟨spec.pre x s0, hpre_in, SepWP.call_subroutine_frame_other (ret_pc := s0.readReg64 .lr) hcall hext hsvc (hcode s0.mem hinv) hpc hrun hsp rfl (F := emp)
    (fun R' hm => by rwa [emp_sepConj]) (fun R' sf hp => hpan x R' s0 sf hp) (fun R' c sf he => hex x c R' s0 sf he) (fun sf hpcf hrunf hspf hcsf _ => by rw [sepConj_emp]; exact SepWP.done hpcf hrunf ⟨id, hspf, hcsf⟩)⟩

theorem hbMemset_withCodeInv_ok {P Q : Program} {C : HbCliLayout} {A : HbAlloc} (hc : HbMemOpsCode Q C)
    (hext : ∀ pc, Q.externAt? pc = P.externAt? pc) (hsvc : Q.svc = P.svc) (hcode : ∀ m, A.CodeInv m → Q.CodeLoaded m) :
    subroutine_ok P C.std.memsetAddr (withCodeInv A stdMemsetSpec) :=
  lift_withCodeInv (hbMemset_ok hc) hext hsvc hcode (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)

theorem hbMemmove_withCodeInv_ok {P Q : Program} {C : HbCliLayout} {A : HbAlloc} (hc : HbMemOpsCode Q C)
    (hext : ∀ pc, Q.externAt? pc = P.externAt? pc) (hsvc : Q.svc = P.svc) (hcode : ∀ m, A.CodeInv m → Q.CodeLoaded m) :
    subroutine_ok P C.memmoveAddr (withCodeInv A stdMemcpySpec) :=
  lift_withCodeInv (hbMemmove_disjoint_ok hc) hext hsvc hcode (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)

end CaseStudies.Hashbrown.Proofs.StdCli
