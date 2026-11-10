/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.HashMapIdInsert
import all Init.Data.Range.Basic
public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Decodes
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.ReserveRehash
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Skeleton
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<HashMap<ProtocolAddress, IdentityKey>>::insert` (`0x14ee0`) Proofs

Proves `hashMapIdInsertEmpty_ok` (inserting into `emptyTableAt` via `reserve_rehash`) and
`hashMapIdInsertSingleHit_ok` (in-place value replacement on `table4SingleAt`).
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.SipHashBin
open ReserveRehash
open HashMapIdInsert

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setPC_pre (s : Arm64.State) (pc : BitVec 64) (r : BitVec 5) :
    (s.setPC pc).readVReg128 r = s.readVReg128 r := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) (r : BitVec 5) :
    ((s.setPC pc).setMem m).readVReg128 r = s.readVReg128 r := by cases s; rfl

namespace HashMapIdInsertProof

theorem step_stpSimd64_sp_at (next_pc ea ea2 : BitVec 64) {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P P1 P2 : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {off : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .D64 vt1 vt2 (.Offset .sp off)))
    (hsp : checkRegSPAligned s .sp = true)
    (hnext_pc : pc + 4#64 = next_pc)
    (hea : s.sp + off = ea)
    (hea2 : ea + 8#64 = ea2)
    (hstore1 : SepStore64 ea ((s.readVReg128 vt1).setWidth 64) P P1)
    (hstore2 : SepStore64 ea2 ((s.readVReg128 vt2).setWidth 64) P1 P2)
    (hnext : ∀ m' : Memory, SepWP prog target_pc ((s.setMem m').setPC next_pc) P2 post) :
    SepWP prog target_pc s P post := by
  refine step_stpSimd64_sp hpc hrun hfetch hsp hea hea2 hstore1 hstore2 fun m' => ?_
  have heq : (s.setPC (pc + 4#64)).setMem m' = (s.setMem m').setPC next_pc := by
    subst hnext_pc; cases s; rfl
  rw [heq]
  exact hnext m'

theorem step_ldrSimd64_uxtx0 (next_pc ea : BitVec 64) {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt rn rm : BitVec 5} {v : BitVec 64}
    (_hrn : rn ≠ 31#5)
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .D64 vt (.RegOffset (.gpr rn) (.gpr rm) .UXTX 0)))
    (hnext_pc : pc + 4#64 = next_pc)
    (hea : s.readReg64 (.gpr rn) + s.readReg64 (.gpr rm) = ea)
    (hload : SepLoad64 ea P v)
    (hnext : SepWP prog target_pc ((s.writeVReg128 vt (v.zeroExtend 128)).setPC next_pc) P post) :
    SepWP prog target_pc s P post :=
  step_ldrSimd64 (wb := none) hpc hrun hfetch
    rfl
    (by simp only [evalAddrMode, extendVal, BitVec.shiftLeft_zero, hea])
    hload (by subst hnext_pc; rfl) hnext

theorem step_ldpSimd64_sp_at (next_pc ea ea2 : BitVec 64) {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {off v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .D64 vt1 vt2 (.Offset .sp off)))
    (hsp : checkRegSPAligned s .sp = true)
    (hnext_pc : pc + 4#64 = next_pc)
    (hea : s.sp + off = ea)
    (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hnext : SepWP prog target_pc
      (((s.writeVReg128 vt1 (v1.zeroExtend 128)).writeVReg128 vt2 (v2.zeroExtend 128)).setPC next_pc)
      P post) :
    SepWP prog target_pc s P post :=
  step_ldpSimd64_sp' hpc hrun hfetch hsp hea hea2 hload1 hload2 (by subst hnext_pc; rfl) hnext

theorem stackAt_16704_eq_hashOne (sp : BitVec 64) :
    stackAt sp 16704 = memRegion (sp - 16704#64) 16592 ∗ stackAt sp hashOneAddrStack :=
  stackAt_split_bottom sp hashOneAddrStack 16592 (by decide)

theorem stackAt_16704_eq_reserveRehash (sp : BitVec 64) :
    stackAt sp 16704 = memRegion (sp - 16704#64) 12288 ∗ stackAt sp reserveRehashStack :=
  stackAt_split_bottom sp reserveRehashStack 12288 (by decide)

theorem stackAt_16704_eq_extHook (sp : BitVec 64) :
    stackAt sp 16704 = memRegion (sp - 16704#64) 320 ∗ stackAt sp extHookStack :=
  stackAt_split_bottom sp extHookStack 320 (by decide)

theorem stackAt_hashMapIdInsert_eq_allocHook (sp : BitVec 64) :
    stackAt sp hashMapIdInsertStack =
      memRegion (sp - 16928#64) 12832 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 12832 (by decide)

theorem elim_reserve_post (A : RustAlloc) {prog : Program} {ret : BitVec 64}
    {x : ReserveRehashEmptyGhost} {s sf1 : Arm64.State} {F : SepProp}
    {Q Qp : Arm64.State → SepProp → Prop}
    (h : ∀ (ctrl : BitVec 64),
      sf1.readReg64 .x0 = 0xffffffffffffffff#64 →
      sf1.trace = s.trace →
      ctrl ≠ 0#64 → ctrl.toNat % 8 = 0 →
      4 * identityBucketStride ≤ ctrl.toNat → ctrl.toNat + 12 < 2 ^ 64 →
      SepWPp prog ret sf1
        ((x.mp ↦₆₄ ctrl) ∗
         ((x.mp + 8#64) ↦₆₄ 3#64) ∗
         ((x.mp + 16#64) ↦₆₄ 3#64) ∗
         ((x.mp + 24#64) ↦₆₄ 0#64) ∗
         ((x.mp + 32#64) ↦₆₄ x.k0) ∗
         ((x.mp + 40#64) ↦₆₄ x.k1) ∗
         A.live (ctrl - BitVec.ofNat 64 (4 * identityBucketStride))
           (tableAllocSize 4 identityBucketStride) (asm% hashbrownTableAlign) ∗
         (ctrl ↦ₛ emptyCtrl4) ∗
         arrayAt (fun _ a => memRegion a identityBucketStride) identityBucketStride
           (ctrl - BitVec.ofNat 64 (4 * identityBucketStride)) (List.range 4).reverse ∗
         A.pool ∗ stackAt s.sp reserveRehashStack ∗ F) Q Qp) :
    SepWPp prog ret sf1 ((reserveRehashIdentityEmptySpec A).post x s sf1 ∗ F) Q Qp := by
  dsimp only [reserveRehashIdentityEmptySpec, reserveRehashEmptySpec, table4EmptyAt, table4At]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, htr⟩ => ?_
  refine SepWPp.exists_elim fun ctrl => ?_
  refine SepWPp.pure_elim fun ⟨hc0, hc8, hcle, hclt, _, _, _⟩ => ?_
  have h40 : x.mp + asm64% tableHasherOff + 8#64 = x.mp + 40#64 := by bv_omega
  have harr :
      arrayAt (fun i a => if i ∈ ([] : List Nat) then memRegion a identityBucketStride else memRegion a identityBucketStride)
        identityBucketStride (ctrl - BitVec.ofNat 64 (4 * identityBucketStride)) (List.range 4).reverse =
      arrayAt (fun _ a => memRegion a identityBucketStride)
        identityBucketStride (ctrl - BitVec.ofNat 64 (4 * identityBucketStride)) (List.range 4).reverse := by
    simp
  rw [h40, harr]
  exact h ctrl hx0 htr hc0 hc8 hcle hclt

theorem fold_for_reserveRehash (base mp k0 k1 sp : BitVec 64) :
    (mp ↦₆₄ (base + bv% (ls_bytes% "ffffffffffffffff67726f75705f6964"))) ∗
    ((mp + 8#64) ↦₆₄ 0#64) ∗
    ((mp + 16#64) ↦₆₄ 0#64) ∗
    ((mp + 24#64) ↦₆₄ 0#64) ∗
    ((mp + 32#64) ↦₆₄ k0) ∗
    ((mp + 40#64) ↦₆₄ k1) ∗
    memRegion (sp - 16928#64) 16592 ∗
    stackAt (sp - 224#64) hashOneAddrStack ⊢
    emptyTableAt base mp k0 k1 ∗
    memRegion (sp - 16928#64) 12288 ∗
    stackAt (sp - 224#64) reserveRehashStack := by
  unfold emptyTableAt
  have h40 : mp + asm64% tableHasherOff + 8#64 = mp + 40#64 := by bv_omega
  have h1 := stackAt_16704_eq_hashOne (sp - 224#64)
  have h2 := stackAt_16704_eq_reserveRehash (sp - 224#64)
  have ha : sp - 224#64 - 16704#64 = sp - 16928#64 := by bv_omega
  rw [ha] at h1 h2
  have hstk : memRegion (sp - 16928#64) 16592 ∗ stackAt (sp - 224#64) hashOneAddrStack =
      memRegion (sp - 16928#64) 12288 ∗ stackAt (sp - 224#64) reserveRehashStack :=
    h1.symm.trans h2
  change (mp ↦₆₄ (base + bv% (ls_bytes% "ffffffffffffffff67726f75705f6964"))) ∗
    ((mp + 8#64) ↦₆₄ 0#64) ∗
    ((mp + 16#64) ↦₆₄ 0#64) ∗
    ((mp + 24#64) ↦₆₄ 0#64) ∗
    ((mp + 32#64) ↦₆₄ k0) ∗
    ((mp + 40#64) ↦₆₄ k1) ∗
    (memRegion (sp - 16928#64) 16592 ∗ stackAt (sp - 224#64) hashOneAddrStack) ⊢ _
  rw [h40, hstk]
  exact Entails.of_eq (by ac_rfl)

theorem reserveRehashStack_entails_stack16704 (sp : BitVec 64) :
    memRegion (sp - 16928#64) 12288 ∗ stackAt (sp - 224#64) reserveRehashStack ⊢
    stackAt (sp - 224#64) 16704 := by
  have h2 := stackAt_16704_eq_reserveRehash (sp - 224#64)
  have ha : sp - 224#64 - 16704#64 = sp - 16928#64 := by bv_omega
  rw [ha] at h2
  exact Entails.of_eq h2.symm

theorem ctrl_split64_eq_split8 (ctrl : BitVec 64) (pos : Nat) (hpos : pos < 4) :
    ((ctrl + BitVec.ofNat 64 pos) ↦₆₄ loadGroupAt emptyCtrl4 pos) ∗
    (ctrl ↦ₛ emptyCtrl4.take pos) ∗
    ((ctrl + BitVec.ofNat 64 (pos + 8)) ↦ₛ emptyCtrl4.drop (pos + 8)) =
    ((ctrl + BitVec.ofNat 64 pos) ↦₈ 0xff#8) ∗
    ((ctrl + BitVec.ofNat 64 pos + 8#64) ↦₈ 0xff#8) ∗
    ctrl12RestAt ctrl pos := by
  rw [← pointsToBytes_ctrl12_split_at ctrl emptyCtrl4 rfl pos hpos,
      pointsToBytes_emptyCtrl4_split ctrl pos hpos]

theorem sepWP_addr_dev_to_64 (a : BitVec 64) (dev : BitVec 8)
    {prog : Program} {pc : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop}
    (hf : P = (((a + 24#64) ↦₈ dev) ∗ memRegion (a + 25#64) 7) ∗ F)
    (h : ∀ w : BitVec 64, w.truncate 8 = dev →
      SepWP prog pc s (((a + 24#64) ↦₆₄ w) ∗ F) post) :
    SepWP prog pc s P post := by
  refine SepWP.fold (Entails.of_eq (pointsTo8_memRegion7_eq_pointsTo64 a dev)) hf ?_
  rw [sepExists_sepConj_left]
  refine sepWP_exists_elim fun w => ?_
  rw [sepConj_assoc]
  exact sepWP_pure_left_elim (h w)

theorem sepWP_bucket64_cells (bkt : BitVec 64)
    {prog : Program} {pc : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop}
    (hf : P = memRegion bkt 64 ∗ F)
    (h : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 64,
      SepWP prog pc s
        ((bkt ↦₆₄ b0) ∗ ((bkt + 8#64) ↦₆₄ b1) ∗ ((bkt + 16#64) ↦₆₄ b2) ∗ ((bkt + 24#64) ↦₆₄ b3) ∗
          ((bkt + 32#64) ↦₆₄ b4) ∗ ((bkt + 40#64) ↦₆₄ b5) ∗ ((bkt + 48#64) ↦₆₄ b6) ∗ ((bkt + 56#64) ↦₆₄ b7) ∗ F)
        post) :
    SepWP prog pc s P post := by
  have hm64 : memRegion bkt 64 =
      (∃∗ b0 : BitVec 64, ∃∗ b1 : BitVec 64, ∃∗ b2 : BitVec 64, ∃∗ b3 : BitVec 64,
       ∃∗ b4 : BitVec 64, ∃∗ b5 : BitVec 64, ∃∗ b6 : BitVec 64, ∃∗ b7 : BitVec 64,
        (bkt ↦₆₄ b0) ∗ ((bkt + 8#64) ↦₆₄ b1) ∗ ((bkt + 16#64) ↦₆₄ b2) ∗ ((bkt + 24#64) ↦₆₄ b3) ∗
        ((bkt + 32#64) ↦₆₄ b4) ∗ ((bkt + 40#64) ↦₆₄ b5) ∗ ((bkt + 48#64) ↦₆₄ b6) ∗ ((bkt + 56#64) ↦₆₄ b7)) := by
    change memRegion bkt (8 * 8) = _
    rw [memRegion_cells bkt 8 (by decide)]
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_right, sepConj_emp]
  refine SepWP.fold (Entails.of_eq hm64) hf ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine sepWP_exists_elim fun b0 => sepWP_exists_elim fun b1 =>
    sepWP_exists_elim fun b2 => sepWP_exists_elim fun b3 =>
    sepWP_exists_elim fun b4 => sepWP_exists_elim fun b5 =>
    sepWP_exists_elim fun b6 => sepWP_exists_elim fun b7 => ?_
  exact h b0 b1 b2 b3 b4 b5 b6 b7

theorem sepWP_sret33_for_none (sret : BitVec 64)
    {prog : Program} {pc : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop}
    (hf : P = memRegion sret 33 ∗ F)
    (h : ∀ b0 : BitVec 8,
      SepWP prog pc s (((sret ↦₈ b0) ∗ memRegion (sret + 1#64) 32) ∗ F) post) :
    SepWP prog pc s P post := by
  refine SepWP.fold (Entails.of_eq (memRegion_33_split_for_none sret)) hf ?_
  simp only [sepConj_assoc, sepExists_sepConj_left]
  refine sepWP_exists_elim fun b0 => ?_
  simp only [← sepConj_assoc]
  exact h b0

theorem arrayAt_empty4_split_at' (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    arrayAt (fun _ a => memRegion a identityBucketStride) identityBucketStride
      (ctrl - 256#64) (List.range 4).reverse =
      memRegion (bucketAddr ctrl 64 k) 64 ∗ buckets4OtherAt ctrl k :=
  arrayAt_empty4_split_at ctrl k hk

theorem umaxv_allOnes :
    Id.run (Bind.bind
      (forIn [0:8] 0#128 fun i __s =>
        if BitVec.ult __s (18446744073709551615#128 >>> (i * 8) &&& 255#128) = true then
          pure (ForInStep.yield (18446744073709551615#128 >>> (i * 8) &&& 255#128))
        else pure (ForInStep.yield __s))
      (fun __s => pure __s)) = 255#128 := by
  decide +kernel

theorem reverse_clz_allOnes :
    (bv% (2 ^ 64 - 1) : BitVec 64).reverse.clz = 0#64 := by
  decide +kernel

theorem and_three_idem (x : BitVec 64) :
    (x &&& 3#64) &&& 3#64 = x &&& 3#64 := by
  rw [BitVec.and_assoc, BitVec.and_self]

theorem fold_table4SingleAt_of_empty' (A : RustAlloc) (mp k0 k1 ctrl : BitVec 64)
    (g : AddrGhost) (hlen36 : g.name.bytes.length = 36)
    (keyBytes : List (BitVec 8)) (hkey : keyBytes.length = 32)
    (hc0 : ctrl ≠ 0#64) (hc8 : ctrl.toNat % 8 = 0)
    (hcle : 4 * identityBucketStride ≤ ctrl.toNat) (hclt : ctrl.toNat + 12 < 2 ^ 64) :
    (mp ↦₆₄ ctrl) ∗
    ((mp + 8#64) ↦₆₄ 3#64) ∗
    ((mp + 16#64) ↦₆₄ 2#64) ∗
    ((mp + 24#64) ↦₆₄ 1#64) ∗
    ((mp + 32#64) ↦₆₄ k0) ∗
    ((mp + 40#64) ↦₆₄ k1) ∗
    A.live (ctrl - 256#64) (tableAllocSize 4 identityBucketStride) 8 ∗
    ((ctrl + (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64)) ↦₈
      BitVec.zeroExtend 8 (hashAddrBv k0 k1 g.name.bytes g.device >>> 57)) ∗
    ((ctrl + (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64) + 8#64) ↦₈
      BitVec.zeroExtend 8 (hashAddrBv k0 k1 g.name.bytes g.device >>> 57)) ∗
    ctrl12RestAt ctrl (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat ∗
    (bucketAddr ctrl 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat ↦₆₄ g.name.cap) ∗
    ((bucketAddr ctrl 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat + 8#64) ↦₆₄ g.name.ptr) ∗
    ((bucketAddr ctrl 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat + 16#64) ↦₆₄ 36#64) ∗
    ((bucketAddr ctrl 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat + 24#64) ↦₈ g.device) ∗
    memRegion (bucketAddr ctrl 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat + 25#64) 7 ∗
    addrHeapAt A g ∗
    ((bucketAddr ctrl 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat + 32#64) ↦₆₄ loadGroupAt keyBytes 0) ∗
    ((bucketAddr ctrl 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat + 40#64) ↦₆₄ loadGroupAt keyBytes 8) ∗
    ((bucketAddr ctrl 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat + 48#64) ↦₆₄ loadGroupAt keyBytes 16) ∗
    ((bucketAddr ctrl 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat + 56#64) ↦₆₄ loadGroupAt keyBytes 24) ∗
    buckets4OtherAt ctrl (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat ⊢
    table4SingleAt A identityBucketStride mp k0 k1
      (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat
      g.name.bytes g.device (identityBucketEntryAt A g keyBytes) := by
  have hpos : (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat < 4 :=
    probePos_3_toNat_lt (hashAddrBv k0 k1 g.name.bytes g.device)
  have hpos_bv : BitVec.ofNat 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat =
      hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64 := by
    simp
  have h256 : BitVec.ofNat 64 (4 * identityBucketStride) = 256#64 := rfl
  have halign : (asm% hashbrownTableAlign) = 8 := rfl
  have htag : h2Tag (hashAddrBv k0 k1 g.name.bytes g.device) =
      BitVec.zeroExtend 8 (hashAddrBv k0 k1 g.name.bytes g.device >>> 57) :=
    (truncate8_shr57_eq_h2Tag (hashAddrBv k0 k1 g.name.bytes g.device)).symm
  have hmain := fold_table4SingleAt_of_empty A mp k0 k1 ctrl
    (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat hpos
    g hlen36 keyBytes hkey hc0 hc8 hcle hclt
  dsimp only at hmain
  rw [h256, halign, htag, hpos_bv] at hmain
  exact hmain

theorem sepWP_unpack_stackAt_hashMapIdInsert (sp : BitVec 64)
    {prog : Program} {pc : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop}
    (hf : P = stackAt sp hashMapIdInsertStack ∗ F)
    (h : ∀ (s0 s1 s2 s3 s4 s5 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : BitVec 64),
      SepWP prog pc s
        (stackAt (sp - 224#64) 16704 ∗
          ((sp - 224#64) ↦₆₄ s0) ∗ ((sp - 216#64) ↦₆₄ s1) ∗
          ((sp - 208#64) ↦₆₄ s2) ∗ ((sp - 200#64) ↦₆₄ s3) ∗
          ((sp - 192#64) ↦₆₄ s4) ∗ ((sp - 184#64) ↦₆₄ s5) ∗
          memRegion (sp - 176#64) 64 ∗
          ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗
          ((sp - 96#64) ↦₆₄ v2) ∗ ((sp - 88#64) ↦₆₄ v3) ∗
          ((sp - 80#64) ↦₆₄ v4) ∗ ((sp - 72#64) ↦₆₄ v5) ∗
          ((sp - 64#64) ↦₆₄ v6) ∗ ((sp - 56#64) ↦₆₄ v7) ∗
          ((sp - 48#64) ↦₆₄ v8) ∗ ((sp - 40#64) ↦₆₄ v9) ∗
          ((sp - 32#64) ↦₆₄ v10) ∗ ((sp - 24#64) ↦₆₄ v11) ∗
          ((sp - 16#64) ↦₆₄ v12) ∗ ((sp - 8#64) ↦₆₄ v13) ∗ F)
        post) :
    SepWP prog pc s P post := by
  have hstack : stackAt sp hashMapIdInsertStack =
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
       ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
       ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64,
        stackAt (sp - 224#64) 16704 ∗
        ((sp - 224#64) ↦₆₄ s0) ∗ ((sp - 216#64) ↦₆₄ s1) ∗
        ((sp - 208#64) ↦₆₄ s2) ∗ ((sp - 200#64) ↦₆₄ s3) ∗
        ((sp - 192#64) ↦₆₄ s4) ∗ ((sp - 184#64) ↦₆₄ s5) ∗
        memRegion (sp - 176#64) 64 ∗
        ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗
        ((sp - 96#64) ↦₆₄ v2) ∗ ((sp - 88#64) ↦₆₄ v3) ∗
        ((sp - 80#64) ↦₆₄ v4) ∗ ((sp - 72#64) ↦₆₄ v5) ∗
        ((sp - 64#64) ↦₆₄ v6) ∗ ((sp - 56#64) ↦₆₄ v7) ∗
        ((sp - 48#64) ↦₆₄ v8) ∗ ((sp - 40#64) ↦₆₄ v9) ∗
        ((sp - 32#64) ↦₆₄ v10) ∗ ((sp - 24#64) ↦₆₄ v11) ∗
        ((sp - 16#64) ↦₆₄ v12) ∗ ((sp - 8#64) ↦₆₄ v13)) := by
    rw [stackAt_hashMapIdInsert sp]
    simp only [sepExists_sepConj_left]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.fold (Entails.of_eq hstack) hf ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine sepWP_exists_elim fun s0 => sepWP_exists_elim fun s1 =>
    sepWP_exists_elim fun s2 => sepWP_exists_elim fun s3 =>
    sepWP_exists_elim fun s4 => sepWP_exists_elim fun s5 =>
    sepWP_exists_elim fun v0 => sepWP_exists_elim fun v1 =>
    sepWP_exists_elim fun v2 => sepWP_exists_elim fun v3 =>
    sepWP_exists_elim fun v4 => sepWP_exists_elim fun v5 =>
    sepWP_exists_elim fun v6 => sepWP_exists_elim fun v7 =>
    sepWP_exists_elim fun v8 => sepWP_exists_elim fun v9 =>
    sepWP_exists_elim fun v10 => sepWP_exists_elim fun v11 =>
    sepWP_exists_elim fun v12 => sepWP_exists_elim fun v13 => ?_
  exact h s0 s1 s2 s3 s4 s5 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13

theorem sepWP_extract_pure {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q F : SepProp} {post : Arm64.State → SepProp → Prop}
    (heq : Q = ⌜P⌝ ∗ F)
    (h : P → SepWP prog pc s F post) :
    SepWP prog pc s Q post := by
  rw [heq]
  exact sepWP_pure_left_elim h

theorem sepWP_sret33_for_some (sret : BitVec 64)
    {prog : Program} {pc : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop}
    (hf : P = memRegion sret 33 ∗ F)
    (h : ∀ (b0 : BitVec 8) (u0 u1 u2 u3 : BitVec 64),
      SepWP prog pc s
        ((sret ↦₈ b0) ∗ ((sret + 1#64) ↦₆₄ u0) ∗ ((sret + 9#64) ↦₆₄ u1) ∗
          ((sret + 17#64) ↦₆₄ u2) ∗ ((sret + 25#64) ↦₆₄ u3) ∗ F) post) :
    SepWP prog pc s P post := by
  have hm33 : memRegion sret 33 =
      (∃∗ b0 : BitVec 8, ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        (sret ↦₈ b0) ∗ ((sret + 1#64) ↦₆₄ u0) ∗ ((sret + 9#64) ↦₆₄ u1) ∗
        ((sret + 17#64) ↦₆₄ u2) ∗ ((sret + 25#64) ↦₆₄ u3)) := by
    rw [memRegion_split sret 1 32 (by decide), memRegion_one,
        memRegion_split (sret + 1#64) 8 24 (by decide),
        memRegion_split (sret + 1#64 + 8#64) 8 16 (by decide),
        memRegion_split (sret + 1#64 + 8#64 + 8#64) 8 8 (by decide),
        memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left]
    simp only [sepExists_sepConj_right]
  refine SepWP.fold (Entails.of_eq hm33) hf ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine sepWP_exists_elim fun b0 => sepWP_exists_elim fun u0 =>
    sepWP_exists_elim fun u1 => sepWP_exists_elim fun u2 =>
    sepWP_exists_elim fun u3 => ?_
  exact h b0 u0 u1 u2 u3

def addrHeapRestAt (A : RustAlloc) (g : AddrGhost) : SepProp :=
  ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
  A.live g.name.ptr g.name.cap.toNat 1 ∗
  memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
    (g.name.cap.toNat - g.name.bytes.length)

theorem addrHeapAt_eq_bytes_rest (A : RustAlloc) (g : AddrGhost) :
    addrHeapAt A g = (g.name.ptr ↦ₛ g.name.bytes) ∗ addrHeapRestAt A g := by
  unfold addrHeapAt addrHeapRestAt
  ac_rfl

theorem hashOneStack_to_extHookStack (sp : BitVec 64) :
    memRegion (sp - 16928#64) 16592 ∗ stackAt (sp - 224#64) hashOneAddrStack ⊢
    memRegion (sp - 16928#64) 320 ∗ stackAt (sp - 224#64) extHookStack := by
  have h1 := stackAt_16704_eq_hashOne (sp - 224#64)
  have h2 := stackAt_16704_eq_extHook (sp - 224#64)
  have ha : sp - 224#64 - 16704#64 = sp - 16928#64 := by bv_omega
  rw [ha] at h1 h2
  exact Entails.of_eq (h1.symm.trans h2)

theorem extHookStack_to_stack16704 (sp : BitVec 64) :
    memRegion (sp - 16928#64) 320 ∗ stackAt (sp - 224#64) extHookStack ⊢
    stackAt (sp - 224#64) 16704 := by
  have h2 := stackAt_16704_eq_extHook (sp - 224#64)
  have ha : sp - 224#64 - 16704#64 = sp - 16928#64 := by bv_omega
  rw [ha] at h2
  exact Entails.of_eq h2.symm

theorem allocHookStack_to_hashMapIdInsertStack (sp : BitVec 64) :
    memRegion (sp - 16928#64) 12832 ∗ stackAt sp allocHookStack ⊢
    stackAt sp hashMapIdInsertStack :=
  Entails.of_eq (stackAt_hashMapIdInsert_eq_allocHook sp).symm

theorem bytes_and_tail_entails_memRegion (ptr cap : BitVec 64) (bs : List (BitVec 8))
    (hlen36 : bs.length = 36) (hle : 36 ≤ cap.toNat) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + 36#64) (cap.toNat - 36) ⊢
    memRegion ptr cap.toNat := by
  have h1 := pointsToBytes_entails_memRegion ptr bs
  rw [hlen36] at h1
  have h2 := memRegion_split ptr 36 (cap.toNat - 36) (by have := cap.isLt; omega)
  rw [show 36 + (cap.toNat - 36) = cap.toNat by omega,
      show BitVec.ofNat 64 36 = 36#64 from rfl] at h2
  rw [h2]
  exact sepConj_mono_left h1

theorem cap_ne_zero_of_le36 (cap : BitVec 64) (h : 36 ≤ cap.toNat) :
    cap ≠ 0#64 := by
  intro h0
  rw [h0] at h
  contradiction

theorem sepWP_unpack_addrHeapAt (A : RustAlloc) (g : AddrGhost)
    (hlen36 : g.name.bytes.length = 36)
    {prog : Program} {pc : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop}
    (hf : P = addrHeapAt A g ∗ F)
    (h : (36 ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0) →
      SepWP prog pc s
        ((g.name.ptr ↦ₛ g.name.bytes) ∗
          A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + 36#64) (g.name.cap.toNat - 36) ∗ F) post) :
    SepWP prog pc s P post := by
  have heq : addrHeapAt A g =
      ⌜36 ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
      (g.name.ptr ↦ₛ g.name.bytes) ∗
      A.live g.name.ptr g.name.cap.toNat 1 ∗
      memRegion (g.name.ptr + 36#64) (g.name.cap.toNat - 36) := by
    unfold addrHeapAt
    rw [hlen36]
  refine SepWP.fold (Entails.of_eq heq) hf ?_
  simp only [sepConj_assoc]
  exact sepWP_pure_left_elim h

theorem sepWP_unpack_table4SingleAt_id (A : RustAlloc) (mp k0 k1 : BitVec 64)
    (k : Nat) (hk : k < 4)
    (oldG : AddrGhost) (hlen36 : oldG.name.bytes.length = 36)
    (oldKeyBytes : List (BitVec 8)) (hkey : oldKeyBytes.length = 32)
    {prog : Program} {pc : BitVec 64} {s : Arm64.State} {P F : SepProp}
    {post : Arm64.State → SepProp → Prop}
    (hf : P = table4SingleAt A identityBucketStride mp k0 k1 k
      oldG.name.bytes oldG.device (identityBucketEntryAt A oldG oldKeyBytes) ∗ F)
    (h : ∀ ctrl : BitVec 64,
      ctrl ≠ 0#64 → ctrl.toNat % 8 = 0 →
      4 * identityBucketStride ≤ ctrl.toNat → ctrl.toNat + 12 < 2 ^ 64 →
      let hash := hashAddrBv k0 k1 oldG.name.bytes oldG.device
      let pos := (hash &&& 3#64).toNat
      let cbs := singleCtrl4 k (h2Tag hash)
      let bkt := bucketAddr ctrl 64 k
      SepWP prog pc s
        ((mp ↦₆₄ ctrl) ∗
         ((mp + 8#64) ↦₆₄ 3#64) ∗
         ((mp + 16#64) ↦₆₄ 2#64) ∗
         ((mp + 24#64) ↦₆₄ 1#64) ∗
         ((mp + 32#64) ↦₆₄ k0) ∗
         ((mp + 40#64) ↦₆₄ k1) ∗
         A.live (ctrl - BitVec.ofNat 64 (4 * identityBucketStride))
           (tableAllocSize 4 identityBucketStride) (asm% hashbrownTableAlign) ∗
         ((ctrl + BitVec.ofNat 64 pos) ↦₆₄ loadGroupAt cbs pos) ∗
         (ctrl ↦ₛ cbs.take pos) ∗
         ((ctrl + BitVec.ofNat 64 (pos + 8)) ↦ₛ cbs.drop (pos + 8)) ∗
         (bkt ↦₆₄ oldG.name.cap) ∗
         ((bkt + 8#64) ↦₆₄ oldG.name.ptr) ∗
         ((bkt + 16#64) ↦₆₄ 36#64) ∗
         ((bkt + 24#64) ↦₈ oldG.device) ∗
         memRegion (bkt + 25#64) 7 ∗
         (oldG.name.ptr ↦ₛ oldG.name.bytes) ∗
         addrHeapRestAt A oldG ∗
         ((bkt + 32#64) ↦₆₄ loadGroupAt oldKeyBytes 0) ∗
         ((bkt + 40#64) ↦₆₄ loadGroupAt oldKeyBytes 8) ∗
         ((bkt + 48#64) ↦₆₄ loadGroupAt oldKeyBytes 16) ∗
         ((bkt + 56#64) ↦₆₄ loadGroupAt oldKeyBytes 24) ∗
         buckets4OtherAt ctrl k ∗ F) post) :
    SepWP prog pc s P post := by
  have hpos : (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat < 4 :=
    probePos_3_toNat_lt (hashAddrBv k0 k1 oldG.name.bytes oldG.device)
  have h40 : mp + asm64% tableHasherOff + 8#64 = mp + 40#64 := by bv_omega
  have hcbs_len : (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 oldG.name.bytes oldG.device))).length = 12 := by
    simp [singleCtrl4, mkCtrl4]
  have htab :
      table4SingleAt A identityBucketStride mp k0 k1 k
        oldG.name.bytes oldG.device (identityBucketEntryAt A oldG oldKeyBytes) =
      ∃∗ ctrl : BitVec 64,
        ⌜ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
          4 * identityBucketStride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
          ([k].length = 4 → 2#64 = 0#64) ∧
          CtrlMirrorInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 oldG.name.bytes oldG.device))) ∧
          FullBucketsInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 oldG.name.bytes oldG.device))) [k]⌝ ∗
        (mp ↦₆₄ ctrl) ∗
        ((mp + 8#64) ↦₆₄ 3#64) ∗
        ((mp + 16#64) ↦₆₄ 2#64) ∗
        ((mp + 24#64) ↦₆₄ 1#64) ∗
        ((mp + 32#64) ↦₆₄ k0) ∗
        ((mp + 40#64) ↦₆₄ k1) ∗
        A.live (ctrl - BitVec.ofNat 64 (4 * identityBucketStride))
          (tableAllocSize 4 identityBucketStride) (asm% hashbrownTableAlign) ∗
        ((ctrl + BitVec.ofNat 64 (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat) ↦₆₄
          loadGroupAt (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 oldG.name.bytes oldG.device)))
            (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat) ∗
        (ctrl ↦ₛ (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 oldG.name.bytes oldG.device))).take
          (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat) ∗
        ((ctrl + BitVec.ofNat 64 ((hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat + 8)) ↦ₛ
          (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 oldG.name.bytes oldG.device))).drop
            ((hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat + 8)) ∗
        (bucketAddr ctrl 64 k ↦₆₄ oldG.name.cap) ∗
        ((bucketAddr ctrl 64 k + 8#64) ↦₆₄ oldG.name.ptr) ∗
        ((bucketAddr ctrl 64 k + 16#64) ↦₆₄ 36#64) ∗
        ((bucketAddr ctrl 64 k + 24#64) ↦₈ oldG.device) ∗
        memRegion (bucketAddr ctrl 64 k + 25#64) 7 ∗
        (oldG.name.ptr ↦ₛ oldG.name.bytes) ∗
        addrHeapRestAt A oldG ∗
        ((bucketAddr ctrl 64 k + 32#64) ↦₆₄ loadGroupAt oldKeyBytes 0) ∗
        ((bucketAddr ctrl 64 k + 40#64) ↦₆₄ loadGroupAt oldKeyBytes 8) ∗
        ((bucketAddr ctrl 64 k + 48#64) ↦₆₄ loadGroupAt oldKeyBytes 16) ∗
        ((bucketAddr ctrl 64 k + 56#64) ↦₆₄ loadGroupAt oldKeyBytes 24) ∗
        buckets4OtherAt ctrl k := by
    unfold table4SingleAt table4At
    rw [pure_sepConj_of_true hk]
    congr 1; funext ctrl
    rw [h40,
        pointsToBytes_ctrl12_split_at ctrl
          (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 oldG.name.bytes oldG.device))) hcbs_len
          (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat hpos,
        arrayAt_single4_split_at ctrl k hk (identityBucketEntryAt A oldG oldKeyBytes),
        identityBucketEntryAt_eq_of_len36_32 A oldG hlen36 oldKeyBytes hkey (bucketAddr ctrl 64 k),
        addrHeapAt_eq_bytes_rest A oldG]
    ac_rfl
  refine SepWP.fold (Entails.of_eq htab) hf ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine sepWP_exists_elim fun ctrl => ?_
  refine sepWP_pure_left_elim fun ⟨hc0, hc8, hcle, hclt, _, _, _⟩ => ?_
  exact h ctrl hc0 hc8 hcle hclt

end HashMapIdInsertProof

open HashMapIdInsertProof

#arm64_check_no_rfl_state_lemmas

set_option maxHeartbeats 800000 in
theorem hashMapIdInsertEmpty_ok' (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName)
      (hashMapIdInsertEmptySpec A) := by
  simp only [hashMapIdInsertEmptySpec, emptyTableAt]
  have hfn : libsignalSessionCode.fnOff hashMapIdInsertName = num% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert") := hashMapIdInsert_fnOff
  have hHash : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName + bv% (2 ^ 64 + (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>") - (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert")))
      (hashOneAddr36Spec A) := by
    have h := inImage_ok_back hashMapIdInsert_fnOff hashOneAddr_fnOff (d := num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 608)) (by decide)
      (hashOneAddr36_ok b ext A)
    have hsub : (RebasedProg b ext).fnAddr hashMapIdInsertName + bv% (2 ^ 64 + (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>") - (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert")) =
        (RebasedProg b ext).fnAddr hashMapIdInsertName - bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 608) := by
      rw [BitVec.sub_eq_add_neg]; rfl
    rwa [hsub]
  have hRes : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName + bv% (2 ^ 64 + (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>") - (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert")))
      (reserveRehashIdentityEmptySpec A) := by
    have h := inImage_ok_back hashMapIdInsert_fnOff reserveRehashId_fnOff (d := 83652) (by decide)
      (reserveRehashIdentityEmpty_ok b ext A hHooks)
    have hsub : (RebasedProg b ext).fnAddr hashMapIdInsertName + bv% (2 ^ 64 + (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>") - (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert")) =
        (RebasedProg b ext).fnAddr hashMapIdInsertName - 83652#64 := by
      rw [BitVec.sub_eq_add_neg]; rfl
    rwa [hsub]
  have hf_14ee4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := ext) (k := 4) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" + 4))
  have hf_14f4c := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := ext) (k := 108) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" + 108))
  have hf_150e4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := ext) (k := 516) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" + 516))
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert")) 592
  dsimp only [RebasedProg] at hHash hRes hf_14ee4 hf_14f4c hf_150e4 ⊢
  clear hfn hHooks
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr hashMapIdInsertName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  replace hf_14ee4 : id _ := hf_14ee4
  replace hf_14f4c : id _ := hf_14f4c
  replace hf_150e4 : id _ := hf_150e4
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨sret, base, mp, kPtr, vPtr, k0, k1, g, keyBytes⟩ := x
  dsimp only at *
  apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<hashbrown::raw::RawTable<(libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey)>>::reserve_rehash::<hashbrown::map::make_hasher<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey, std::hash::random::RandomState>::{closure#0}>") - (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert")))
  refine sepWP_unpack_stackAt_hashMapIdInsert s0.sp (by sep_focus)
    fun v_stk_14 v_stk_15 v_stk_16 v_stk_17 v_stk_18 v_stk_19
        v_stk_0 v_stk_1 v_stk_2 v_stk_3 v_stk_4 v_stk_5 v_stk_6
        v_stk_7 v_stk_8 v_stk_9 v_stk_10 v_stk_11 v_stk_12 v_stk_13 => ?_
  wp_step
  refine step_stpSimd64_sp_at (entry + bv% (8)) (s0.sp - 112#64) (s0.sp - 104#64)
    (by wp_norm_goal) (by wp_norm_lhs) hf_14ee4
    (by simp only [checkRegSPAligned, wp_norm, arm64_norm, *])
    (by bv_omega) (by wp_norm_lhs) (by bv_omega)
    (by wp_sep_access_fast) (by wp_sep_access_fast) fun m1 => ?_
  wp_simp_pre only [bv_sub_add_lit, stackAt_16704_eq_hashOne]
  wp_steps
  wp_apply
  wp_steps
  refine SepWP.fold (fold_for_reserveRehash base mp k0 k1 s0.sp) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (ret_pc := entry + bv% (552))
    (x := ⟨base, mp, mp + 32#64, k0, k1⟩)
    (T := emptyTableAt base mp k0 k1 ∗ A.pool ∗ stackAt (s0.sp - 224#64) reserveRehashStack)
    hRes
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal)
    (by dsimp only [reserveRehashIdentityEmptySpec, reserveRehashEmptySpec]; congr 3; simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by sep_focus)
    (fun _ _ _ _ he => allowPanic_not_exited he)
    (fun sf _ hm => allowPanic_frame (trace_eq_of_eq (by simp only [wp_norm, arm64_norm, *])) hm)
    ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp1 hcs1
  rcases hcs1 with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  refine elim_reserve_post A fun ctrl hx0_1 htr hc0 hc8 hcle hclt => ?_
  dsimp only at *
  simp only [wp_norm, arm64_norm, *] at htr
  apply SepWPp.of_sepWP_ret
  wp_simp_pre only [bv_sub_add_lit, wp_norm, arm64_norm, hsp_sf]
  refine SepWP.fold (reserveRehashStack_entails_stack16704 s0.sp) (by sep_focus) ?_
  have hpos : (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat < 4 :=
    probePos_3_toNat_lt (hashAddrBv k0 k1 g.name.bytes g.device)
  have hpos_bv :
      BitVec.ofNat 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat =
        hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64 := by
    simp
  wp_conv_pre =>
    rw [protocolAddressAt_eq_of_len36 A g kPtr h_5,
        pointsToBytes_ctrl12_split_at ctrl emptyCtrl4 rfl
          (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat hpos]
  wp_steps
  refine step_ldrSimd64_uxtx0
    (entry + bv% (112))
    (ctrl + BitVec.ofNat 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat)
    (by decide) (by wp_norm_goal) (by wp_norm_lhs) hf_14f4c (by bv_omega)
    (by rw [hpos_bv]; wp_norm_lhs)
    (by wp_sep_access_fast) ?_
  have hmask0 : rawMatchTagMask
      (loadGroupAt emptyCtrl4 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat)
      (hashAddrBv k0 k1 g.name.bytes g.device) = 0#64 := by
    rw [loadGroupAt_emptyCtrl4_eq _ hpos]
    exact rawMatchTagMask_allOnes _
  unfold rawMatchTagMask at hmask0
  wp_step
  wp_step
  wp_step
  wp_step
  clear hmask0
  have hgrp := loadGroupAt_emptyCtrl4_eq (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat hpos
  have humax := umaxv_allOnes
  have hclz := reverse_clz_allOnes
  have hand3 := and_three_idem (hashAddrBv k0 k1 g.name.bytes g.device)
  have hmir := mirror_offset_eq_self (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat hpos
  have hbkt := ctrl_sub_lsl6_eq_bucketAddr_add_64 ctrl (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat hpos
  rw [hpos_bv] at hmir hbkt
  wp_conv_pre =>
    rw [ctrl_split64_eq_split8 ctrl (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat hpos,
        arrayAt_empty4_split_at' ctrl (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat hpos,
        pointsToBytes_32_eq_cells vPtr keyBytes h,
        hpos_bv]
  refine sepWP_addr_dev_to_64 kPtr g.device (by sep_focus) fun w hw => ?_
  refine sepWP_bucket64_cells
    (bucketAddr ctrl 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat)
    (by sep_focus) fun b0 b1 b2 b3 b4 b5 b6 b7 => ?_
  refine sepWP_sret33_for_none sret (by sep_focus) fun sret_b0 => ?_
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (pointsToBytes_32_eq_cells vPtr keyBytes h).symm)
    (by sep_focus) ?_
  refine SepWP.fold
    (pointsTo64_entails_pointsTo8_memRegion7
      (bucketAddr ctrl 64 (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64).toNat)
      w g.device hw)
    (by sep_focus) ?_
  refine SepWP.fold
    (fold_table4SingleAt_of_empty' A mp k0 k1 ctrl g h_5 keyBytes h hc0 hc8 hcle hclt)
    (by sep_focus) ?_
  refine SepWP.fold
    (memRegion_32_of_cells kPtr g.name.cap g.name.ptr 36#64 w)
    (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (show (sret ↦₈ 0#8) ∗ memRegion (sret + 1#64) 32 = optIdentityKeyAt sret none from rfl))
    (by sep_focus) ?_
  refine SepWP.fold
    (fold_stackAt_hashMapIdInsert s0.sp
      (hashAddrBv k0 k1 g.name.bytes g.device &&& 3#64)
      v_stk_15 v_stk_16 v_stk_17 v_stk_18 v_stk_19
      (BitVec.setWidth 64 (s0.readVReg128 9#5))
      (BitVec.setWidth 64 (s0.readVReg128 8#5))
      (s0.readReg64 (Reg.gpr 29#5))
      (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 28#5))
      (s0.readReg64 (Reg.gpr 27#5))
      (s0.readReg64 (Reg.gpr 26#5))
      (s0.readReg64 (Reg.gpr 25#5))
      (s0.readReg64 (Reg.gpr 24#5))
      (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5))
      (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5))
      (s0.readReg64 (Reg.gpr 19#5)))
    (by sep_focus) ?_
  have hv8 : BitVec.setWidth 64 (s0.readVReg128 8#5) = (calleeSavedVRegs s0).1 := rfl
  have hv9 : BitVec.setWidth 64 (s0.readVReg128 9#5) = (calleeSavedVRegs s0).2.1 := rfl
  wp_done

theorem fold_table4SingleAt_of_hit' (A : RustAlloc) (mp k0 k1 ctrl : BitVec 64)
    (k : Nat) (hk : k < 4)
    (oldG : AddrGhost) (hlen36 : oldG.name.bytes.length = 36)
    (newKeyBytes : List (BitVec 8)) (hkey : newKeyBytes.length = 32)
    (hc0 : ctrl ≠ 0#64) (hc8 : ctrl.toNat % 8 = 0)
    (hcle : 4 * identityBucketStride ≤ ctrl.toNat) (hclt : ctrl.toNat + 12 < 2 ^ 64) :
    (mp ↦₆₄ ctrl) ∗
    ((mp + 8#64) ↦₆₄ 3#64) ∗
    ((mp + 16#64) ↦₆₄ 2#64) ∗
    ((mp + 24#64) ↦₆₄ 1#64) ∗
    ((mp + 32#64) ↦₆₄ k0) ∗
    ((mp + 40#64) ↦₆₄ k1) ∗
    A.live (ctrl - 256#64) (tableAllocSize 4 identityBucketStride) 8 ∗
    ((ctrl + (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64)) ↦₆₄
      loadGroupAt (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 oldG.name.bytes oldG.device)))
        (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat) ∗
    (ctrl ↦ₛ
      List.take (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat
        (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 oldG.name.bytes oldG.device)))) ∗
    ((ctrl + ((hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64) + 8#64)) ↦ₛ
      List.drop ((hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat + 8)
        (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 oldG.name.bytes oldG.device)))) ∗
    (bucketAddr ctrl 64 k ↦₆₄ oldG.name.cap) ∗
    ((bucketAddr ctrl 64 k + 8#64) ↦₆₄ oldG.name.ptr) ∗
    ((bucketAddr ctrl 64 k + 16#64) ↦₆₄ 36#64) ∗
    ((bucketAddr ctrl 64 k + 24#64) ↦₈ oldG.device) ∗
    memRegion (bucketAddr ctrl 64 k + 25#64) 7 ∗
    addrHeapAt A oldG ∗
    ((bucketAddr ctrl 64 k + 32#64) ↦₆₄ loadGroupAt newKeyBytes 0) ∗
    ((bucketAddr ctrl 64 k + 40#64) ↦₆₄ loadGroupAt newKeyBytes 8) ∗
    ((bucketAddr ctrl 64 k + 48#64) ↦₆₄ loadGroupAt newKeyBytes 16) ∗
    ((bucketAddr ctrl 64 k + 56#64) ↦₆₄ loadGroupAt newKeyBytes 24) ∗
    buckets4OtherAt ctrl k ⊢
    table4SingleAt A identityBucketStride mp k0 k1 k
      oldG.name.bytes oldG.device (identityBucketEntryAt A oldG newKeyBytes) := by
  have hpos : (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat < 4 :=
    probePos_3_toNat_lt (hashAddrBv k0 k1 oldG.name.bytes oldG.device)
  have hpos_bv : BitVec.ofNat 64 (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat =
      hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64 := by
    simp
  have hpos8_bv : BitVec.ofNat 64 ((hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat + 8) =
      (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64) + 8#64 := by
    rw [BitVec.ofNat_add, hpos_bv]
  have hmain := fold_table4SingleAt_of_hit A mp k0 k1 ctrl k
    (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat hk hpos
    oldG hlen36 newKeyBytes hkey hc0 hc8 hcle hclt
  dsimp only at hmain
  rw [hpos8_bv, hpos_bv] at hmain
  exact hmain

set_option maxHeartbeats 800000 in
theorem hashMapIdInsertSingleHit_ok' (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName)
      (hashMapIdInsertSingleHitSpec A) := by
  simp only [hashMapIdInsertSingleHitSpec]
  have hfn : libsignalSessionCode.fnOff hashMapIdInsertName = num% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert") := hashMapIdInsert_fnOff
  have hHash : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName + bv% (2 ^ 64 + (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>") - (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert")))
      (hashOneAddr36Spec A) := by
    have h := inImage_ok_back hashMapIdInsert_fnOff hashOneAddr_fnOff (d := num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 608)) (by decide)
      (hashOneAddr36_ok b ext A)
    have hsub : (RebasedProg b ext).fnAddr hashMapIdInsertName + bv% (2 ^ 64 + (ls_off% "<std::hash::random::RandomState as core::hash::BuildHasher>::hash_one::<&libsignal_core::address::ProtocolAddress>") - (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert")) =
        (RebasedProg b ext).fnAddr hashMapIdInsertName - bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 608) := by
      rw [BitVec.sub_eq_add_neg]; rfl
    rwa [hsub]
  have hBcmp : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName + bv% (ls_off% "bcmp" - ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert"))
      e2eBcmpSpec :=
    hashbrown_bcmp_ok_at hHooks hashMapIdInsert_fnOff (by decide)
  have hDealloc : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr hashMapIdInsertName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert"))
      (rustDeallocSpec A) :=
    hashbrown_dealloc_ok_at hHooks hashMapIdInsert_fnOff (by decide)
  have hf_14ee4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := ext) (k := 4) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" + 4))
  have hf_14f4c := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := ext) (k := 108) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" + 108))
  have hf_15074 := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := b) (H := ext) (k := 404) hfn (by decide) (ls_decode% libsignalSessionBin (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert" + 404))
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<std::collections::hash::map::HashMap<libsignal_core::address::ProtocolAddress, libsignal_protocol::identity_key::IdentityKey>>::insert")) 592
  dsimp only [RebasedProg] at hHash hBcmp hDealloc hf_14ee4 hf_14f4c hf_15074 ⊢
  clear hfn hHooks
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr hashMapIdInsertName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  replace hf_14ee4 : id _ := hf_14ee4
  replace hf_14f4c : id _ := hf_14f4c
  replace hf_15074 : id _ := hf_15074
  examples_hide_fetches
  wp_init x s0
  obtain ⟨sret, mp, kPtr, vPtr, k0, k1, k, oldG, newG, oldKeyBytes, newKeyBytes⟩ := x
  dsimp only at *
  have hnew36 : newG.name.bytes.length = 36 := by
    rwa [‹newG.name.bytes = oldG.name.bytes›]
  have hpos : (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat < 4 :=
    probePos_3_toNat_lt (hashAddrBv k0 k1 oldG.name.bytes oldG.device)
  have hpos_bv :
      BitVec.ofNat 64 (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat =
        hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64 := by
    simp
  refine sepWP_unpack_stackAt_hashMapIdInsert s0.sp (by sep_focus)
    fun v_stk_14 v_stk_15 v_stk_16 v_stk_17 v_stk_18 v_stk_19
        v_stk_0 v_stk_1 v_stk_2 v_stk_3 v_stk_4 v_stk_5 v_stk_6
        v_stk_7 v_stk_8 v_stk_9 v_stk_10 v_stk_11 v_stk_12 v_stk_13 => ?_
  refine sepWP_unpack_table4SingleAt_id A mp k0 k1 k (by assumption)
    oldG (by assumption) oldKeyBytes (by assumption) (by sep_focus)
    fun ctrl hc0 hc8 hcle hclt => ?_
  dsimp only
  refine sepWP_sret33_for_some sret (by sep_focus)
    fun sret_b0 sret_u0 sret_u1 sret_u2 sret_u3 => ?_
  wp_conv_pre =>
    rw [pointsToBytes_32_eq_cells vPtr newKeyBytes (by assumption)]
  wp_step
  refine step_stpSimd64_sp_at (entry + bv% (8)) (s0.sp - 112#64) (s0.sp - 104#64)
    (by wp_norm_goal) (by wp_norm_lhs) hf_14ee4
    (by simp only [checkRegSPAligned, wp_norm, arm64_norm, *])
    (by bv_omega) (by wp_norm_lhs) (by bv_omega)
    (by wp_sep_access_fast) (by wp_sep_access_fast) fun m1 => ?_
  wp_simp_pre only [bv_sub_add_lit, stackAt_16704_eq_hashOne]
  wp_steps
  wp_apply
  rw [h_7, h_8] at h_20
  wp_conv_pre =>
    rw [protocolAddressAt_eq_of_len36 A newG kPtr hnew36]
  refine sepWP_unpack_addrHeapAt A newG hnew36 (by sep_focus)
    fun ⟨hnew_cap_ge, hnew_cap_lt, hnew_ptr⟩ => ?_
  -- Stop at the `ldr d9` at entry+108: past it, the `b.eq` needs `hmask_same` below.
  wp_steps 11
  refine step_ldrSimd64_uxtx0
    (entry + bv% (112))
    (ctrl + (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64))
    (by decide) (by wp_norm_goal) (by wp_norm_lhs) hf_14f4c (by bv_omega)
    (by wp_norm_lhs)
    (by wp_sep_access_fast) ?_
  have hmask_same := rawMatchTagMask_singleCtrl4_same k
    (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat (by assumption) hpos
    (hashAddrBv k0 k1 oldG.name.bytes oldG.device)
  have hmask_ne := laneBit_laneOfBucket4_ne_zero k
    (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat (by assumption) hpos
  have hmask_beq :
      (laneBit (laneOfBucket4 (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat k) == 0#64) = false :=
    beq_false_of_ne hmask_ne
  unfold rawMatchTagMask at hmask_same
  wp_step
  wp_step
  wp_step
  wp_step
  clear hmask_same
  have hprobe := eval_probeBucket_singleCtrl4 k
    (hashAddrBv k0 k1 oldG.name.bytes oldG.device &&& 3#64).toNat (by assumption) hpos
  rw [hpos_bv] at hprobe
  have hbkt := ctrl_sub_lsl6_eq_bucketAddr_add_64 ctrl k (by assumption)
  wp_steps
  wp_conv_pre =>
    rw [‹newG.name.bytes = oldG.name.bytes›, ‹newG.device = oldG.device›]
  refine SepWP.fold (hashOneStack_to_extHookStack s0.sp) (by sep_focus) ?_
  wp_apply
  wp_conv_pre => rw [hsp_sf]
  refine SepWP.fold (extHookStack_to_stack16704 s0.sp) (by sep_focus) ?_
  have hbcmp : BitVec.setWidth 32 (sf_1.readReg64 (Reg.gpr 0#5)) = 0#32 := h_31.mpr trivial
  have hbcmp_zext : BitVec.zeroExtend 64 (BitVec.setWidth 32 (sf_1.readReg64 (Reg.gpr 0#5))) = 0#64 := by
    rw [hbcmp]; rfl
  have hcap_beq : (newG.name.cap == 0#64) = false :=
    beq_false_of_ne (cap_ne_zero_of_le36 newG.name.cap hnew_cap_ge)
  wp_steps
  refine SepWP.fold
    (fold_stackAt_hashMapIdInsert s0.sp
      v_stk_14 0#64 ctrl 3#64 0#64
      (hashAddrBv k0 k1 oldG.name.bytes oldG.device >>> 57)
      (BitVec.setWidth 64 (s0.readVReg128 9#5))
      (BitVec.setWidth 64 (s0.readVReg128 8#5))
      (s0.readReg64 (Reg.gpr 29#5))
      (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 28#5))
      (s0.readReg64 (Reg.gpr 27#5))
      (s0.readReg64 (Reg.gpr 26#5))
      (s0.readReg64 (Reg.gpr 25#5))
      (s0.readReg64 (Reg.gpr 24#5))
      (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5))
      (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5))
      (s0.readReg64 (Reg.gpr 19#5)))
    (by sep_focus) ?_
  wp_conv_pre =>
    rw [stackAt_hashMapIdInsert_eq_allocHook s0.sp]
  refine SepWP.fold
    (bytes_and_tail_entails_memRegion newG.name.ptr newG.name.cap oldG.name.bytes (by assumption) hnew_cap_ge)
    (by sep_focus) ?_
  wp_apply
  refine SepWP.fold (allocHookStack_to_hashMapIdInsertStack s0.sp) (by sep_focus) ?_
  refine SepWP.fold
    (memRegion_32_of_addr_cells kPtr newG.name.cap newG.name.ptr 36#64 oldG.device)
    (by sep_focus) ?_
  refine SepWP.fold
    (fold_optIdentityKeyAt_some sret oldKeyBytes (by assumption))
    (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (pointsToBytes_32_eq_cells vPtr newKeyBytes h).symm)
    (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (addrHeapAt_eq_bytes_rest A oldG).symm)
    (by sep_focus) ?_
  refine SepWP.fold
    (fold_table4SingleAt_of_hit' A mp k0 k1 ctrl k (by assumption)
      oldG (by assumption) newKeyBytes h hc0 hc8 hcle hclt)
    (by sep_focus) ?_
  have hv8 : BitVec.setWidth 64 (s0.readVReg128 8#5) = (calleeSavedVRegs s0).1 := rfl
  have hv9 : BitVec.setWidth 64 (s0.readVReg128 9#5) = (calleeSavedVRegs s0).2.1 := rfl
  wp_done

end CryptoVerification.E2E.InMem.HashbrownBin
