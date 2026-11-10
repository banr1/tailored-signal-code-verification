/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.RecClone
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.RoundLemmas
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.Decodes -- shake: keep

/-!
# Shared Helpers for the `InMemSessionStore` Future-Closure Leaves
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.SipHashBin
open CryptoVerification.E2E.InMem.HashbrownBin

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Unaligned 8-Byte Control-Group Load and `table4SingleAt` Bucket Splitting (`stride = 400`) -/

theorem probePos_3_eq_ofNat (hash : BitVec 64) :
    hash &&& 3#64 = BitVec.ofNat 64 (probePos hash 3#64).toNat := by
  simp [probePos]

theorem pack64_eq_packGroupWord (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    pack64 b0 b1 b2 b3 b4 b5 b6 b7 = packGroupWord b0 b1 b2 b3 b4 b5 b6 b7 :=
  SipHashBin.pack64_eq_or_shifts b0 b1 b2 b3 b4 b5 b6 b7

theorem getD_default_of_lt {α : Type} (xs : List α) (i : Nat) (d1 d2 : α)
    (hi : i < xs.length) :
    xs.getD i d1 = xs.getD i d2 := by
  simp [List.getD, List.getElem?_eq_getElem hi]

theorem loadGroupAt_eq_pack64 (cbs : List (BitVec 8)) (pos : Nat)
    (h : pos + 8 ≤ cbs.length) :
    loadGroupAt cbs pos =
      pack64 (cbs.getD pos 0#8) (cbs.getD (pos + 1) 0#8)
        (cbs.getD (pos + 2) 0#8) (cbs.getD (pos + 3) 0#8)
        (cbs.getD (pos + 4) 0#8) (cbs.getD (pos + 5) 0#8)
        (cbs.getD (pos + 6) 0#8) (cbs.getD (pos + 7) 0#8) := by
  rw [pack64_eq_packGroupWord]
  unfold loadGroupAt
  rw [Nat.add_zero,
      getD_default_of_lt cbs pos emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 1) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 2) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 3) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 4) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 5) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 6) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 7) emptyTag 0#8 (by omega)]

/-- Split a 12-byte control array `ctrl ↦ₛ cbs` at any offset `pos < 4` so an unaligned 8-byte
`ldr d, [ctrl, pos]` sees `((ctrl + BitVec.ofNat 64 pos) ↦₆₄ loadGroupAt cbs pos)`. -/
theorem pointsToBytes_ctrl12_split_at (ctrl : BitVec 64) (cbs : List (BitVec 8))
    (hlen : cbs.length = 12) (pos : Nat) (hpos : pos < 4) :
    (ctrl ↦ₛ cbs) =
      ((ctrl + BitVec.ofNat 64 pos) ↦₆₄ loadGroupAt cbs pos) ∗
      (ctrl ↦ₛ cbs.take pos) ∗
      ((ctrl + BitVec.ofNat 64 (pos + 8)) ↦ₛ cbs.drop (pos + 8)) := by
  have h1 : pos ≤ cbs.length := by omega
  have h2 : 8 ≤ (cbs.drop pos).length := by simp [List.length_drop, hlen]; omega
  have h3 : pos + 8 ≤ cbs.length := by omega
  rw [pointsToBytes_take_drop ctrl pos cbs h1,
      pointsToBytes_take_drop (ctrl + BitVec.ofNat 64 pos) 8 (cbs.drop pos) h2,
      List.drop_drop,
      pointsToBytes_take8_eq_pointsTo64 (ctrl + BitVec.ofNat 64 pos) cbs pos h3,
      ← loadGroupAt_eq_pack64 cbs pos h3,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  ac_rfl

/-- 400-byte (`0x190`) bucket address arithmetic in `load_session::{closure#0}` and
`store_session::{closure#0}`, equating `ctrl - 400 * (k + 1)` to `bucketAddr ctrl 400 k`. -/
theorem sub_mul400_eq_bucketAddr (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    let idx := BitVec.ofNat 64 k
    let x9 := (idx <<< 4) + ((idx <<< 4) <<< 3)
    let x8 := x9 + (idx <<< 8) + 0x190#64
    ctrl - x8 = bucketAddr ctrl 400 k := by
  unfold bucketAddr
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> bv_omega

def singleBucketRestAt (stride : Nat) (ctrl : BitVec 64) (k : Nat) : SepProp :=
  arrayAt
    (fun i a => if i = k then emp else memRegion a stride) stride
    (ctrl - BitVec.ofNat 64 (4 * stride)) [3, 2, 1, 0]

private theorem sub1600_add400 (ctrl : BitVec 64) :
    ctrl - 1600#64 + 400#64 = ctrl - 1200#64 := by bv_omega

private theorem sub1200_add400 (ctrl : BitVec 64) :
    ctrl - 1200#64 + 400#64 = ctrl - 800#64 := by bv_omega

private theorem sub800_add400 (ctrl : BitVec 64) :
    ctrl - 800#64 + 400#64 = ctrl - 400#64 := by bv_omega

theorem arrayAt_single_split_400 (ctrl : BitVec 64) (k : Nat) (hk : k < 4)
    (entryAt : BitVec 64 → SepProp) :
    arrayAt
      (fun i a => if i ∈ [k] then entryAt a else memRegion a 400) 400
      (ctrl - BitVec.ofNat 64 (4 * 400)) (List.range 4).reverse =
    entryAt (bucketAddr ctrl 400 k) ∗ singleBucketRestAt 400 ctrl k := by
  change arrayAt
      (fun i a => if i ∈ [k] then entryAt a else memRegion a 400) 400
      (ctrl - 1600#64) [3, 2, 1, 0] =
    entryAt (bucketAddr ctrl 400 k) ∗ singleBucketRestAt 400 ctrl k
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [singleBucketRestAt, bucketAddr, arrayAt, List.mem_singleton,
      Nat.reduceAdd, Nat.reduceMul,
      sub1600_add400, sub1200_add400, sub800_add400, ite_true]
    ac_rfl

theorem arrayAt_empty_split_400 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    arrayAt
      (fun i a => if i ∈ ([] : List Nat) then ⌜False⌝ else memRegion a 400) 400
      (ctrl - BitVec.ofNat 64 (4 * 400)) (List.range 4).reverse =
    memRegion (bucketAddr ctrl 400 k) 400 ∗ singleBucketRestAt 400 ctrl k := by
  have hfun :
      (fun (i : Nat) (a : BitVec 64) => if i ∈ ([] : List Nat) then ⌜False⌝ else memRegion a 400) =
      (fun i a => if i ∈ [k] then memRegion a 400 else memRegion a 400) := by
    funext i a; simp
  rw [hfun]
  exact arrayAt_single_split_400 ctrl k hk (fun a => memRegion a 400)

/-! ## 64-Bit SIMD (`D64`) Load/Store Step Rules -/

theorem step_ldrSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .D64 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P v)
    (hexec : ((applyWriteback s wb).writeVReg128 vt (v.zeroExtend 128)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldrSimd .D64 vt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read64 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 8 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : execInst (.ldrSimd .D64 vt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, Memory.readSimdSized, applyWriteback,
      Arm64.State.advancePC, Arm64.State.setPC, hsp, haddr, hread, hcan,
      SimdMemSize.bytes, hpc]
  rw [Program.evalInst_of_isSvc0Instr_false _ _ _ rfl, hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

theorem step_ldpSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .D64 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hexec : (((applyWriteback s wb).writeVReg128 vt1 (v1.zeroExtend 128)).writeVReg128 vt2 (v2.zeroExtend 128)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldpSimd .D64 vt1 vt2 addr) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read64 ea = v1 := hload1.load hm
  have hread2 : s.mem.read64 ea2 = v2 := hload2.load hm
  have hcan1 : s.mem.canRead ea 8 = true := hload1.readable hm
  have hcan2 : s.mem.canRead ea2 8 = true := hload2.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : execInst (.ldpSimd .D64 vt1 vt2 addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, Memory.readSimdSized, applyWriteback,
      Arm64.State.advancePC, Arm64.State.setPC, hsp, haddr, hea2,
      hread1, hread2, hcan1, hcan2, SimdMemSize.bytes, hpc]
  rw [Program.evalInst_of_isSvc0Instr_false _ _ _ rfl, hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

theorem step_stpSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P P1 P2 : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .D64 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hv1 : (s.readVReg128 vt1).setWidth 64 = v1)
    (hv2 : (s.readVReg128 vt2).setWidth 64 = v2)
    (hstore1 : SepStore64 ea v1 P P1)
    (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P2 post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stpSimd .D64 vt1 vt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : execInst (.stpSimd .D64 vt1 vt2 addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, Memory.writeSimdSized, applyWriteback,
      Arm64.State.advancePC, Arm64.State.setPC, Arm64.State.setMem, Arm64.State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, SimdMemSize.bytes, hpc, m1, m2]
  rw [Program.evalInst_of_isSvc0Instr_false _ _ _ rfl, hstep]
  exact hnext m2 R hm2

theorem step_stpSimd64_sp {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P P1 P2 : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {off ea ea2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .D64 vt1 vt2 (.Offset .sp off)))
    (hsp : checkRegSPAligned s .sp = true)
    (hea : s.sp + off = ea)
    (hea2 : ea + 8#64 = ea2)
    (hstore1 : SepStore64 ea ((s.readVReg128 vt1).setWidth 64) P P1)
    (hstore2 : SepStore64 ea2 ((s.readVReg128 vt2).setWidth 64) P1 P2)
    (hnext : ∀ m' : Memory, SepWP prog target_pc ((s.setPC (pc + 4#64)).setMem m') P2 post) :
    SepWP prog target_pc s P post :=
  step_stpSimd64 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, AddrMode.baseReg, hsp])
    (by simp [evalAddrMode, Arm64.State.readReg64, hea])
    hea2 rfl rfl hstore1 hstore2 rfl hnext

theorem step_ldpSimd64_sp {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {off ea ea2 v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .D64 vt1 vt2 (.Offset .sp off)))
    (hsp : checkRegSPAligned s .sp = true)
    (hea : s.sp + off = ea)
    (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hnext : SepWP prog target_pc
      (((s.writeVReg128 vt1 (v1.zeroExtend 128)).writeVReg128 vt2 (v2.zeroExtend 128)).setPC (pc + 4#64))
      P post) :
    SepWP prog target_pc s P post :=
  step_ldpSimd64 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, AddrMode.baseReg, hsp])
    (by simp [evalAddrMode, Arm64.State.readReg64, hea])
    hea2 hload1 hload2 rfl hnext

theorem step_stpSimd64_sp_pre {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P P1 P2 : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {off ea ea2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .D64 vt1 vt2 (.PreIndex .sp off)))
    (hsp : checkRegSPAligned s .sp = true)
    (hea : s.sp + off = ea)
    (hea2 : ea + 8#64 = ea2)
    (hstore1 : SepStore64 ea ((s.readVReg128 vt1).setWidth 64) P P1)
    (hstore2 : SepStore64 ea2 ((s.readVReg128 vt2).setWidth 64) P1 P2)
    (hnext : ∀ m' : Memory, SepWP prog target_pc (((s.writeReg64 .sp ea).setPC (pc + 4#64)).setMem m') P2 post) :
    SepWP prog target_pc s P post :=
  step_stpSimd64 (wb := some (.sp, ea)) hpc hrun hfetch
    (by simp [checkAddrSPAligned, AddrMode.baseReg, hsp])
    (by simp [evalAddrMode, Arm64.State.readReg64, hea])
    hea2 rfl rfl hstore1 hstore2 rfl hnext

theorem step_ldpSimd64_sp_post {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {off ea ea2 sp' v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .D64 vt1 vt2 (.PostIndex .sp off)))
    (hsp : checkRegSPAligned s .sp = true)
    (hea : s.sp = ea)
    (hea2 : ea + 8#64 = ea2)
    (hsp' : ea + off = sp')
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hnext : SepWP prog target_pc
      ((((s.writeReg64 .sp sp').writeVReg128 vt1 (v1.zeroExtend 128)).writeVReg128 vt2 (v2.zeroExtend 128)).setPC (pc + 4#64))
      P post) :
    SepWP prog target_pc s P post :=
  step_ldpSimd64 (wb := some (.sp, sp')) hpc hrun hfetch
    (by simp [checkAddrSPAligned, AddrMode.baseReg, hsp])
    (by simp [evalAddrMode, Arm64.State.readReg64, hea, hsp'])
    hea2 hload1 hload2 rfl hnext

theorem step_ldrSimd64_reg {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt rn rm : BitVec 5} {ea v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .D64 vt (.RegOffset (.gpr rn) (.gpr rm) .UXTX 0)))
    (hea : s.readReg64 (.gpr rn) + s.readReg64 (.gpr rm) = ea)
    (hload : SepLoad64 ea P v)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 vt (v.zeroExtend 128)).setPC (pc + 4#64))
      P post) :
    SepWP prog target_pc s P post :=
  step_ldrSimd64 (wb := none) hpc hrun hfetch rfl
    (by simp [evalAddrMode, extendVal, hea])
    hload rfl hnext

/-! ## Table and `ProtocolAddress` Unfolding Helpers -/

theorem table4SingleAt_eq (A : RustAlloc) (stride : Nat) (mp k0 k1 : BitVec 64)
    (k : Nat) (peerName : List (BitVec 8)) (peerDev : BitVec 8)
    (entryAt : BitVec 64 → SepProp) :
    table4SingleAt A stride mp k0 k1 k peerName peerDev entryAt =
      ⌜k < 4⌝ ∗
      ∃∗ ctrl : BitVec 64,
        ⌜ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
          4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
          ([k].length = 4 → 2#64 = 0#64) ∧
          CtrlMirrorInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∧
          FullBucketsInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) [k]⌝ ∗
        (mp ↦₆₄ ctrl) ∗
        ((mp + 8#64) ↦₆₄ 3#64) ∗
        ((mp + 16#64) ↦₆₄ 2#64) ∗
        ((mp + 24#64) ↦₆₄ 1#64) ∗
        ((mp + 32#64) ↦₆₄ k0) ∗
        ((mp + 40#64) ↦₆₄ k1) ∗
        A.live (ctrl - BitVec.ofNat 64 (4 * stride)) (tableAllocSize 4 stride) 8 ∗
        (ctrl ↦ₛ singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∗
        arrayAt
          (fun i a => if i ∈ [k] then entryAt a else memRegion a stride) stride
          (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse := by
  have hadd : mp + 32#64 + 8#64 = mp + 40#64 := by bv_omega
  dsimp only [table4SingleAt, table4At]
  simp only [hadd]
  rfl

def addrRestAt (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64) : SepProp :=
  ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
  (addr ↦₆₄ g.name.cap) ∗
  A.live g.name.ptr g.name.cap.toNat 1 ∗
  memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
    (g.name.cap.toNat - g.name.bytes.length) ∗
  memRegion (addr + 25#64) 7

theorem protocolAddressAt_eq_of_len36 (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64)
    (hlen36 : g.name.bytes.length = 36) :
    protocolAddressAt A g addr =
      ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
      ((addr + 16#64) ↦₆₄ 36#64) ∗
      ((addr + 24#64) ↦₈ g.device) ∗
      (g.name.ptr ↦ₛ g.name.bytes) ∗
      addrRestAt A g addr := by
  have hvec :
      vecGhostAt A g.name addr =
        ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        (addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
        ((addr + 16#64) ↦₆₄ 36#64) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length) := by
    unfold vecGhostAt vecU8At vecHeader
    have h1 :
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) ⊢
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
          (addr + 16#64) ↦₆₄ 36#64 ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) := by
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      simp only [hne, ↓reduceIte, hlen36] at hlen ⊢
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      have hcomm :
          (((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
              ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 36)) ∗
            (A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
              memRegion (g.name.ptr + BitVec.ofNat 64 36)
                (g.name.cap.toNat - 36))) =
          ((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
            ((addr + 16#64) ↦₆₄ 36#64) ∗
            (g.name.ptr ↦ₛ g.name.bytes) ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 36)
              (g.name.cap.toNat - 36)) := by ac_rfl
      rw [hcomm]; exact Entails.refl _
    have h2 :
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
          (addr + 16#64) ↦₆₄ 36#64 ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) ⊢
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) := by
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      rw [sepConj_pure_left_comm]
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      simp only [hne, ↓reduceIte, hlen36]
      have hcomm :
          ((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
            ((addr + 16#64) ↦₆₄ 36#64) ∗
            (g.name.ptr ↦ₛ g.name.bytes) ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 36)
              (g.name.cap.toNat - 36)) =
          (((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
              ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 36)) ∗
            (A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
              memRegion (g.name.ptr + BitVec.ofNat 64 36)
                (g.name.cap.toNat - 36))) := by ac_rfl
      rw [hcomm]; exact Entails.refl _
    exact ProofLib.sepProp_eq_of_entails h1 h2
  unfold protocolAddressAt addrRestAt
  rw [hvec]
  ac_rfl

/-! ## `MSUB` 400-Byte Bucket Offset Lemmas -/

theorem msub400_sub_eq_bucketAddr_add (ctrl : BitVec 64) (k : Nat) (hk : k < 4)
    (subOff addOff : Nat) (hsum : subOff + addOff = 400) :
    ctrl - BitVec.ofNat 64 k * 400#64 - BitVec.ofNat 64 subOff =
      bucketAddr ctrl 400 k + BitVec.ofNat 64 addOff := by
  unfold bucketAddr
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> bv_omega

theorem msub400_sub400_eq_bucketAddr (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl - BitVec.ofNat 64 k * 400#64 - 400#64 = bucketAddr ctrl 400 k := by
  simpa using msub400_sub_eq_bucketAddr_add ctrl k hk 400 0 rfl

theorem msub400_sub392_eq_bucketAddr_add8 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl - BitVec.ofNat 64 k * 400#64 - 392#64 = bucketAddr ctrl 400 k + 8#64 :=
  msub400_sub_eq_bucketAddr_add ctrl k hk 392 8 rfl

theorem msub400_sub384_eq_bucketAddr_add16 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl - BitVec.ofNat 64 k * 400#64 - 384#64 = bucketAddr ctrl 400 k + 16#64 :=
  msub400_sub_eq_bucketAddr_add ctrl k hk 384 16 rfl

theorem msub400_sub376_eq_bucketAddr_add24 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl - BitVec.ofNat 64 k * 400#64 - 376#64 = bucketAddr ctrl 400 k + 24#64 :=
  msub400_sub_eq_bucketAddr_add ctrl k hk 376 24 rfl

theorem msub400_sub368_eq_bucketAddr_add32 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl - BitVec.ofNat 64 k * 400#64 - 368#64 = bucketAddr ctrl 400 k + 32#64 :=
  msub400_sub_eq_bucketAddr_add ctrl k hk 368 32 rfl

theorem msub400_sub360_eq_bucketAddr_add40 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl - BitVec.ofNat 64 k * 400#64 - 360#64 = bucketAddr ctrl 400 k + 40#64 :=
  msub400_sub_eq_bucketAddr_add ctrl k hk 360 40 rfl

theorem msub400_sub352_eq_bucketAddr_add48 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl - BitVec.ofNat 64 k * 400#64 - 352#64 = bucketAddr ctrl 400 k + 48#64 :=
  msub400_sub_eq_bucketAddr_add ctrl k hk 352 48 rfl

theorem msub400_sub344_eq_bucketAddr_add56 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl - BitVec.ofNat 64 k * 400#64 - 344#64 = bucketAddr ctrl 400 k + 56#64 :=
  msub400_sub_eq_bucketAddr_add ctrl k hk 344 56 rfl

/-! ## `sessionRecordAt` Unpacking and Byte-Slice Bridges -/

theorem sessionRecordAt_some_eq (A : RustAlloc) (r : BitVec 64)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) :
    sessionRecordAt A r ⟨0#64, 8#64, some G⟩ ⟨some ss⟩ =
      (r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ 8#64) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
      sessionStateReprAt A (r + 24#64) G ss := by
  dsimp only [sessionRecordAt]
  rw [vecAt_empty_prev_eq_vecHeader]
  unfold vecHeader
  ac_rfl

theorem sessionRecordAt_some_any_prev_eq (A : RustAlloc) (r prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) :
    sessionRecordAt A r ⟨prevCap, prevPtr, some G⟩ ⟨some ss⟩ =
      (r ↦₆₄ prevCap) ∗ ((r + 8#64) ↦₆₄ prevPtr) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
      vecBuf A 24 8 (fun (_ : Unit) _ => emp) prevCap prevPtr [] ∗
      sessionStateReprAt A (r + 24#64) G ss := by
  dsimp only [sessionRecordAt, vecAt, vecHeader]
  ac_rfl

theorem sessionRecord_tail360_eq_bytes (a cap : BitVec 64) (bs336 : List (BitVec 8)) :
    (((a + 8#64) ↦₆₄ 8#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ cap) ∗ ((a + 32#64) ↦ₛ bs336)) =
    ((a + 8#64) ↦ₛ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 cap ++ bs336)) := by
  have h1 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have h2 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  have h3 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes]
  change (((a + 8#64) ↦₆₄ 8#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ cap) ∗ ((a + 32#64) ↦ₛ bs336)) =
    ((a + 8#64) ↦₆₄ 8#64) ∗
    (((a + 8#64 + 8#64) ↦₆₄ 0#64) ∗
      (((a + 8#64 + 8#64 + 8#64) ↦₆₄ cap) ∗
        ((a + 8#64 + 8#64 + 8#64 + 8#64) ↦ₛ bs336)))
  rw [h1, h2, h3]

theorem sessionRecord_full368_eq_bytes (a cap : BitVec 64) (bs336 : List (BitVec 8)) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 8#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ cap) ∗ ((a + 32#64) ↦ₛ bs336)) =
    (a ↦ₛ (unpack64 0#64 ++ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 cap ++ bs336))) := by
  have h :
      ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 8#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
        ((a + 24#64) ↦₆₄ cap) ∗ ((a + 32#64) ↦ₛ bs336)) =
      ((a ↦₆₄ 0#64) ∗ (((a + 8#64) ↦₆₄ 8#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
        ((a + 24#64) ↦₆₄ cap) ∗ ((a + 32#64) ↦ₛ bs336))) := by ac_rfl
  rw [h, sessionRecord_tail360_eq_bytes, pointsTo64_eq_pointsToBytes a 0#64]
  exact (pointsToBytes_append a (unpack64 0#64) _).symm

theorem cap_lt_not_noneCap {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro heq
  have h1 : (cap + 1#64).toNat = 0 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

end CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
