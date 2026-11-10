/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyAdd
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `KeyHistory::add` Proofs for `<spqr::chain::Chain>::recv_key` (Block `366`)

Threads `RustCliAllocBudget M`, `A.pool lim st`, `AllocCallPreserved`, and exact
`doReserveStep` / `keyHistoryAddStep` capacity and allocator-event transitions across the
relocatable `[LibsignalPlacement]` `KeyHistory::add` sub-phases (`+496`, `+520`, `+408` to `+448`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyAddBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification (LibsignalPlacement lsmpl lsρ blkPC_366 blkPl_366)
open CryptoVerification.LibsignalSpqrV1 (Bytes Chain HkdfFn KeyHistory)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall doReserveStack reserveCap)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainEpochGhost ChainRecvKeyGhost SepWPp.mono_pre VecPin
  add_check4_props add_check32_props advance_hdr_props
  chainOuterRecvAt exists_cells4_of_length_32
  nextKeyInternalStackX pointsTo32_cells4_entails_memRegion_36_sp120
  recvKeyFrameRestAt reserveCap_props
  stackAt_nextKeyInternalX_doReserve_split vecDequePhysIdx
  vecU8At_pack_append_key32 vecU8At_pack_append_u32_be
  vecU8At_pack_raw vecU8At_unpack_for_key32 vecU8At_unpack_for_u32
)
open CryptoVerification.SpqrV1.ChainProofs.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.SpqrV1.ChainProofs.ChainAddEpochFacts (vecU8At_unpack vecU8Rest)
open CryptoVerification.SpqrV1.ChainProofs.ChainNewFacts (SepWPp.pure_left_focus)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (
  LsCallInv SepWP.pure_left_focus SepWPp.call_allowPanic_lsCallInv_mid
  SepWPp.of_sepWP_lsCallInv toBEBytes_4_length withLsCallInv
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget fitsEvents_append
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (allocCallPreserved_trans)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetBudget (
  RecvKeyPlacedStateInv recvKeyPanic recvKeyPost
)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (
  chainRecvKeySpecX doReserveStep keyHistoryAddStep
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents doReserveSpec fitsEnv_doReserve_iff
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

/-! ## `withAllocCallPreserved` and `doReserveStep` / `keyHistoryAddStep` Bridges -/

/-- Strengthen an allocating `Spec α` with `AllocCallPreserved s0 sf` so `AllocCallPreserved`
transports across `do_reserve_and_handle` calls. -/
def withAllocCallPreserved {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    post := fun x s0 sf => ⌜AllocCallPreserved s0 sf⌝ ∗ spec.post x s0 sf }

theorem doReserveStep_of_le {cap len additional : Nat} (hle : len + additional ≤ cap) :
    doReserveStep cap len additional = (cap, []) := by
  simp [doReserveStep, hle]

theorem doReserveStep_of_not_le (arg : DoReserveCall)
    (hneed : ¬ (arg.bs.length + arg.additional ≤ arg.cap.toNat)) :
    doReserveStep arg.cap.toNat arg.bs.length arg.additional =
      (reserveCap arg.cap.toNat arg.bs.length arg.additional, doReserveEvents arg) := by
  unfold doReserveStep doReserveEvents
  simp only [hneed, ↓reduceIte]
  by_cases hcap : arg.cap = 0#64
  · rw [hcap]; rfl
  · have hcap_nat : arg.cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    simp only [hcap, hcap_nat, ↓reduceIte]

/-! ## Budget-Threaded `call_doReserve_lsCallInv` -/

theorem call_doReserve_lsCallInv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {prog : Program} {entry target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCallInv lsmpl (withAllocCallPreserved (doReserveSpec M A lim))))
    (arg : DoReserveCall) (st_cur : M.σ) (ret_pc : BitVec 64)
    (x : ChainRecvKeyGhost) (st0 : M.σ) (s0 s : State)
    {P F R : SepProp} {post : State → SepProp → Prop}
    (hF : LsCallInv lsmpl s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = arg.v)
    (hx1 : (s.readReg64 .x1).toNat = arg.bs.length)
    (hx2 : (s.readReg64 .x2).toNat = arg.additional)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hbound : reserveCap arg.cap.toNat arg.bs.length arg.additional + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim st_cur (doReserveEvents arg))
    (hpre : P ⊢ vecU8At A.repAlloc arg.v arg.cap arg.ptr arg.bs ∗
      A.pool lim st_cur s ∗ stackAt s.sp doReserveStack ∗ F)
    (hnext : ∀ (sf : State) (p' : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → LsCallInv lsmpl sf.mem →
      AllocCallPreserved s sf → sf.trace = s0.trace →
      SepWPp prog target_pc sf
        (vecU8At A.repAlloc arg.v
          (BitVec.ofNat 64 (reserveCap arg.cap.toNat arg.bs.length arg.additional)) p' arg.bs ∗
          A.pool lim (M.stepEvents (doReserveEvents arg) st_cur) sf ∗
          stackAt sf.sp doReserveStack ∗ F)
        post (recvKeyPanic M A lim hkdf x st0 s0 R)) :
    SepWPp prog target_pc s P post (recvKeyPanic M A lim hkdf x st0 s0 R) := by
  have hfits_env : FitsEnv M lim st_cur (DoReserveEnv arg) :=
    (fitsEnv_doReserve_iff arg).mpr hfits
  refine SepWPp.call_allowPanic_lsCallInv_mid (x := (arg, st_cur)) (F := F) (R := R)
    (Qpan := (chainRecvKeySpecX M A lim hkdf).onPanic (x, st0) s0)
    hcall hF hpc hrun hsp_align hlr
    (fun R' hm0 => by
      have hm := Satisfies.mono (sepConj_mono_left hpre) hm0
      dsimp only [withAllocCallPreserved, doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfits_env⟩,
        by simpa only [sepConj_assoc] using hm⟩)
    (fun _ => Entails.pure_left False.elim)
    ⟨fun _ _ => rfl, fun _ => rfl⟩
    (fun sm hpcm hrunm hspm hcsm hF_m => by
      dsimp only [withAllocCallPreserved, doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun hacp_m => ?_
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htrm => ?_
      simp only [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun p' => ?_
      rw [← hspm]; simp only [sepConj_assoc]
      exact hnext sm p' hpcm hrunm hspm hcsm hF_m hacp_m (htrm.trans htr))

/-! ## Budget-Threaded `KeyHistory::add` Sub-Phases (`+408..+448`, `+520..+448`, `+496..+448`) -/

set_option maxHeartbeats 800000 in
theorem recvKey_write_key_from_408_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (st0 st_cur : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (cap1 ptr1 : BitVec 64)
    (prev : KeyHistory) (next1 key : Bytes) (ctr1 : BitVec 32)
    (hgt1 : ctr1.toNat < x.index.toNat)
    (hkey_len : key.length = 32)
    (hadd36 : prev.data.length + 36 ≤ cap1.toNat)
    (hcap1 : cap1.toNat < 2 ^ 63) (hptr1 : ptr1 ≠ 0)
    (h_cont : ∀ (s' : State),
      RecvKeyPlacedStateInv lsmpl s0 s' →
      s'.pc = (blkPl_366).base + 448#64 →
      (s'.readReg64 (.gpr 8#5)).setWidth 32 = ctr1 →
      s'.readReg64 (.gpr 19#5) = x.out →
      (s'.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
      s'.readReg64 (.gpr 21#5) =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64 →
      s'.readReg64 (.gpr 22#5) =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
      (s'.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault →
      s'.readReg64 (.gpr 24#5) = s0.sp - 120#64 →
      let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
      let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
      let prev' := prev.add (ctr1, key) x.self.params
      SepWPp ((blkPC_366).rebase (blkPl_366).base H)
        (s0.readReg64 (.gpr 30#5)) s'
        (memRegion x.out 32 ∗
          chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
          ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
          ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
          ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
          (gce.recv.next.ptr ↦ₛ next1) ∗
          vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr next1.length ∗
          ((epPtr + 0x50#64) ↦₆₄ cap1) ∗
          ((epPtr + 0x58#64) ↦₆₄ ptr1) ∗
          ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 prev'.data.length) ∗
          (ptr1 ↦ₛ prev'.data) ∗
          vecU8Rest A.repAlloc cap1 ptr1 prev'.data.length ∗
          ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
          memRegion (epPtr + 0x6c#64) 4 ∗
          stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
          memRegion (s0.sp - 120#64) 36 ∗
          recvKeyFrameRestAt s0 c3 ∗
          A.pool lim st_cur s')
        (recvKeyPost M A lim hkdf x st0 s0)
        (recvKeyPanic M A lim hkdf x st0 s0 R))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 408#64)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (prev.data.length + 4))
    (hx9 : s.readReg64 (.gpr 9#5) = ptr1)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hw23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault)
    (hx24 : s.readReg64 (.gpr 24#5) = s0.sp - 120#64) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
        ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
        (gce.recv.next.ptr ↦ₛ next1) ∗
        vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr next1.length ∗
        vecU8At A.repAlloc (epPtr + 0x50#64) cap1 ptr1 (prev.data ++ toBEBytes 4 ctr1) ∗
        ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        ((s0.sp - 120#64) ↦₃₂ ctr1) ∗
        ((s0.sp - 116#64) ↦ₛ key) ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool lim st_cur s)
      (recvKeyPost M A lim hkdf x st0 s0)
      (recvKeyPanic M A lim hkdf x st0 s0 R) := by
  intro s_idx epPtr
  dsimp only [s_idx, epPtr]; clear s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  wp_norm_hyp hvregs
  have ⟨_, hovf1, hbeq0, hbne0, _, _, _⟩ := advance_hdr_props hgt1
  have hlen_be4 : (prev.data ++ toBEBytes 4 ctr1).length = prev.data.length + 4 := by
    rw [List.length_append, toBEBytes_4_length]
  have hadd32 : (prev.data ++ toBEBytes 4 ctr1).length + 32 ≤ cap1.toNat := by omega
  have hadd_bv : BitVec.ofNat 64 (prev.data.length + 4) + 32#64 = BitVec.ofNat 64 (prev.data.length + 36) := by
    bv_omega
  let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
  have hunpack := vecU8At_unpack_for_key32 A.repAlloc (epPtr + 0x50#64) cap1 ptr1 (prev.data ++ toBEBytes 4 ctr1) hadd32
  have ha58 : epPtr + 0x50#64 + 8#64 = epPtr + 0x58#64 := by bv_kernel
  have ha60 : epPtr + 0x50#64 + 16#64 = epPtr + 0x60#64 := by bv_kernel
  rw [ha58, ha60, hlen_be4] at hunpack
  refine SepWPp.fold hunpack (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro u0; apply SepWPp.exists_elim; intro u1
  apply SepWPp.exists_elim; intro u2; apply SepWPp.exists_elim; intro u3
  obtain ⟨k0, k1, k2, k3, hkey_pack⟩ := exists_cells4_of_length_32 hkey_len
  have hkey_sp : ((s0.sp - 116#64) ↦ₛ key) =
      ((s0.sp - 116#64) ↦₆₄ k0) ∗ ((s0.sp - 108#64) ↦₆₄ k1) ∗
      ((s0.sp - 100#64) ↦₆₄ k2) ∗ ((s0.sp - 92#64) ↦₆₄ k3) := by
    have h := hkey_pack (s0.sp - 116#64)
    rw [show s0.sp - 116#64 + 8#64 = s0.sp - 108#64 by bv_kernel,
        show s0.sp - 116#64 + 16#64 = s0.sp - 100#64 by bv_kernel,
        show s0.sp - 116#64 + 24#64 = s0.sp - 92#64 by bv_kernel] at h
    exact h
  refine SepWPp.fold (Entails.of_eq hkey_sp) (by sep_focus) ?_
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx8; wp_norm_hyp hx9; wp_norm_hyp hx19; wp_norm_hyp hw20
  wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hw23; wp_norm_hyp hx24; wp_norm_hyp htrace
  wp_norm_hyp hovf1; wp_norm_hyp hbeq0; wp_norm_hyp hbne0; wp_norm_hyp hadd_bv
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 448#64) hF ?_
  wp_steps_sync_pool ((blkPl_366).base + 448#64)
  refine SepWP.fold (pointsTo32_cells4_entails_memRegion_36_sp120 s0.sp ctr1 k0 k1 k2 k3) (by sep_focus) ?_
  have hpack := vecU8At_pack_append_key32 A.repAlloc (epPtr + 0x50#64) cap1 ptr1
    (prev.data ++ toBEBytes 4 ctr1) key k0 k1 k2 k3 hkey_len hkey_pack hadd32 hcap1 hptr1
  rw [ha58, ha60, hlen_be4, show prev.data.length + 4 + 32 = prev.data.length + 36 by omega] at hpack
  refine SepWP.fold hpack (by sep_focus) ?_
  have hunpack_end := vecU8At_unpack A.repAlloc (epPtr + 0x50#64) cap1 ptr1 ((prev.data ++ toBEBytes 4 ctr1) ++ key)
  rw [ha58, ha60] at hunpack_end
  refine SepWP.fold hunpack_end (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) fun _ => ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF'
  have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
    ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
     by rw [← hx26]; wp_norm_goal,
     by rw [← hx27]; wp_norm_goal,
     by rw [← hx28]; wp_norm_goal,
     htrace, by wp_norm_goal,
     allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
  refine SepWPp.mono_pre _ ?_
    (h_cont _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
      (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
  change _ ⊢
    memRegion x.out 32 ∗
      chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
      ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
      ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
      ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
      (gce.recv.next.ptr ↦ₛ next1) ∗
      vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr next1.length ∗
      ((epPtr + 0x50#64) ↦₆₄ cap1) ∗
      ((epPtr + 0x58#64) ↦₆₄ ptr1) ∗
      ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 ((prev.data ++ toBEBytes 4 ctr1) ++ key).length) ∗
      (ptr1 ↦ₛ ((prev.data ++ toBEBytes 4 ctr1) ++ key)) ∗
      vecU8Rest A.repAlloc cap1 ptr1 ((prev.data ++ toBEBytes 4 ctr1) ++ key).length ∗
      ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
      memRegion (epPtr + 0x6c#64) 4 ∗
      stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
      memRegion (s0.sp - 120#64) 36 ∗
      recvKeyFrameRestAt s0 c3 ∗
      A.pool lim st_cur _
  sep_frame

set_option maxHeartbeats 1200000 in
theorem recvKey_add_from_520_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {H : String → Option (State → State)}
    (hdoRes : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (withAllocCallPreserved (doReserveSpec M A lim))))
    (x : ChainRecvKeyGhost) (st0 st1 : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (cap1 ptr1 : BitVec 64)
    (prev : KeyHistory) (next1 key : Bytes) (ctr1 : BitVec 32)
    (hgt1 : ctr1.toNat < x.index.toNat)
    (hkey_len : key.length = 32)
    (hp_fit : prev.data.length + 128 < 2 ^ 62)
    (hadd4 : prev.data.length + 4 ≤ cap1.toNat)
    (hcap1 : cap1.toNat < 2 ^ 63) (hptr1 : ptr1 ≠ 0)
    (hfits1 : FitsEvents M lim st1 (doReserveStep cap1.toNat (prev.data.length + 4) 32).2)
    (h_cont : ∀ (cap2 ptr2 : BitVec 64),
      cap2.toNat = (doReserveStep cap1.toNat (prev.data.length + 4) 32).1 →
      (prev.add (ctr1, key) x.self.params).data.length ≤ cap2.toNat →
      cap2.toNat < 2 ^ 63 → ptr2 ≠ 0 →
      ∀ (s' : State),
        RecvKeyPlacedStateInv lsmpl s0 s' →
        s'.pc = (blkPl_366).base + 448#64 →
        (s'.readReg64 (.gpr 8#5)).setWidth 32 = ctr1 →
        s'.readReg64 (.gpr 19#5) = x.out →
        (s'.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s'.readReg64 (.gpr 21#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64 →
        s'.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        (s'.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault →
        s'.readReg64 (.gpr 24#5) = s0.sp - 120#64 →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        let prev' := prev.add (ctr1, key) x.self.params
        SepWPp ((blkPC_366).rebase (blkPl_366).base H)
          (s0.readReg64 (.gpr 30#5)) s'
          (memRegion x.out 32 ∗
            chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
            ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
            ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
            ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
            (gce.recv.next.ptr ↦ₛ next1) ∗
            vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr next1.length ∗
            ((epPtr + 0x50#64) ↦₆₄ cap2) ∗
            ((epPtr + 0x58#64) ↦₆₄ ptr2) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 prev'.data.length) ∗
            (ptr2 ↦ₛ prev'.data) ∗
            vecU8Rest A.repAlloc cap2 ptr2 prev'.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool lim (M.stepEvents (doReserveStep cap1.toNat (prev.data.length + 4) 32).2 st1) s')
          (recvKeyPost M A lim hkdf x st0 s0)
          (recvKeyPanic M A lim hkdf x st0 s0 R))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 520#64)
    (hx1 : s.readReg64 (.gpr 1#5) = BitVec.ofNat 64 prev.data.length)
    (hx10 : s.readReg64 (.gpr 10#5) = cap1)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hw23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault)
    (hx24 : s.readReg64 (.gpr 24#5) = s0.sp - 120#64)
    (hw25 : (s.readReg64 (.gpr 25#5)).setWidth 32 = ctr1) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
        ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
        (gce.recv.next.ptr ↦ₛ next1) ∗
        vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr next1.length ∗
        vecU8At A.repAlloc (epPtr + 0x50#64) cap1 ptr1 prev.data ∗
        ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        ((s0.sp - 120#64) ↦₃₂ ctr1) ∗
        ((s0.sp - 116#64) ↦ₛ key) ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool lim st1 s)
      (recvKeyPost M A lim hkdf x st0 s0)
      (recvKeyPanic M A lim hkdf x st0 s0 R) := by
  intro s_idx epPtr
  have h_w408 := @recvKey_write_key_from_408_placed _ M A lim hkdf H x st0
  dsimp only [s_idx, epPtr]; clear s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  wp_norm_hyp hvregs
  have ⟨hadd4_bv, hlen4_toNat, hult31, hule31⟩ := add_check32_props hadd4 hcap1
  let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
  have hunpack := vecU8At_unpack_for_u32 A.repAlloc (epPtr + 0x50#64) cap1 ptr1 prev.data hadd4
  have ha58 : epPtr + 0x50#64 + 8#64 = epPtr + 0x58#64 := by bv_kernel
  have ha60 : epPtr + 0x50#64 + 16#64 = epPtr + 0x60#64 := by bv_kernel
  rw [ha58, ha60] at hunpack
  refine SepWPp.fold hunpack (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro w0
  have hpack4 := vecU8At_pack_append_u32_be A.repAlloc (epPtr + 0x50#64) cap1 ptr1 prev.data ctr1 hadd4 hcap1 hptr1
  rw [ha58, ha60] at hpack4
  have hadd_len : (prev.add (ctr1, key) x.self.params).data.length = prev.data.length + 36 := by
    simp only [KeyHistory.add, List.length_append, toBEBytes_4_length, hkey_len]
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx1; wp_norm_hyp hx10; wp_norm_hyp hx19; wp_norm_hyp hw20
  wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hw23; wp_norm_hyp hx24; wp_norm_hyp hw25; wp_norm_hyp htrace
  wp_norm_hyp hadd4_bv; wp_norm_hyp hult31; wp_norm_hyp hule31
  by_cases hhi : prev.data.length + 36 ≤ cap1.toNat
  · have hhi_t : decide (prev.data.length + 36 ≤ cap1.toNat) = true := decide_eq_true hhi
    wp_norm_hyp hhi_t
    have hstep_eq : doReserveStep cap1.toNat (prev.data.length + 4) 32 = (cap1.toNat, []) :=
      doReserveStep_of_le (by omega)
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 408#64) hF ?_
    wp_steps_sync_pool ((blkPl_366).base + 408#64)
    refine SepWP.fold hpack4 (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by rw [← hx26]; wp_norm_goal,
       by rw [← hx27]; wp_norm_goal,
       by rw [← hx28]; wp_norm_goal,
       htrace, by wp_norm_goal,
       allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
    have hcap_out : cap1.toNat = (doReserveStep cap1.toNat (prev.data.length + 4) 32).1 := by
      rw [hstep_eq]
    have hle_out : (prev.add (ctr1, key) x.self.params).data.length ≤ cap1.toNat := by omega
    have hst_eq : M.stepEvents (doReserveStep cap1.toNat (prev.data.length + 4) 32).2 st1 = st1 := by
      rw [hstep_eq, AllocCostModel.stepEvents_nil]
    refine SepWPp.mono_pre _ ?_
      (h_w408 st1 s0 c3 epochIndex hi_ep gce cap1 ptr1 prev next1 key ctr1 hgt1 hkey_len hhi hcap1 hptr1
        (fun s' hinv_s' hpc_s' hx8_s' hx19_s' hw20_s' hx21_s' hx22_s' hw23_s' hx24_s' => by
          rw [← hst_eq]
          exact h_cont cap1 ptr1 hcap_out hle_out hcap1 hptr1 s' hinv_s' hpc_s' hx8_s' hx19_s'
            hw20_s' hx21_s' hx22_s' hw23_s' hx24_s')
        _ hinv'
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame
  · have hhi_f : decide (prev.data.length + 36 ≤ cap1.toNat) = false := decide_eq_false hhi
    wp_norm_hyp hhi_f
    have hlen_be4 : (prev.data ++ toBEBytes 4 ctr1).length = prev.data.length + 4 := by
      rw [List.length_append, toBEBytes_4_length]
    have hneed32 : ¬ ((prev.data ++ toBEBytes 4 ctr1).length + 32 ≤ cap1.toNat) := by omega
    have ⟨hres_bound, hnew_ge, hnew_lt⟩ :=
      reserveCap_props (cap := cap1.toNat) (len := (prev.data ++ toBEBytes 4 ctr1).length) (additional := 32)
        (by omega) (by decide) hneed32
    let arg32 : DoReserveCall := ⟨epPtr + 0x50#64, cap1, ptr1, prev.data ++ toBEBytes 4 ctr1, 32⟩
    have hstep_eq :
        doReserveStep cap1.toNat (prev.data.length + 4) 32 =
          (reserveCap cap1.toNat (prev.data ++ toBEBytes 4 ctr1).length 32, doReserveEvents arg32) := by
      rw [← hlen_be4]
      exact doReserveStep_of_not_le arg32 hneed32
    have hfits_arg32 : FitsEvents M lim st1 (doReserveEvents arg32) := by
      simpa only [hstep_eq] using hfits1
    refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 320) hF ?_
    wp_steps_sync_pool (lsmpl.base 320)
    refine SepWP.fold hpack4 (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_doReserve_split (s0.sp - 128#64))) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF1
    refine call_doReserve_lsCallInv hdoRes arg32 st1 ((blkPl_366).base + 576#64) x st0 s0 _ hF1
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [State.spAligned, arm64_norm, hsp] at hsp0_align ⊢; revert hsp0_align; bv_kernel)
      (by wp_norm_goal)
      (by simp only [arm64_norm, htrace])
      (by dsimp [arg32, epPtr]; wp_norm_goal)
      (by dsimp [arg32]; rw [hlen_be4, ← hlen4_toNat]; wp_norm_goal)
      (by dsimp [arg32]; wp_norm_goal)
      (by wp_norm_goal) (by wp_norm_goal) hres_bound hfits_arg32
      (by simp only [arm64_norm, hsp]; sep_frame) ?_
    intro sf p' hpc_sf hrun_sf hsp_sf hcs_sf hF_sf hacp_sf htr_sf
    have hacp_0_sf : AllocCallPreserved s0 sf := by
      refine allocCallPreserved_trans ?_ hacp_sf
      refine allocCallPreserved_trans hacp ?_
      unfold AllocCallPreserved; wp_norm_goal
    simp only [arm64_norm, hsp] at hsp_sf
    have hsp_sf_align : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf] at hsp0_align ⊢; revert hsp0_align; bv_kernel
    rcases hcs_sf with ⟨hx19_sf, hx20_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf, hx25_sf, hx26_sf, hx27_sf, hx28_sf, _, hvregs_sf⟩
    simp only [arm64_norm] at hx19_sf hx20_sf hx21_sf hx22_sf hx23_sf hx24_sf hx25_sf hx26_sf hx27_sf hx28_sf hvregs_sf
    let cap2 := BitVec.ofNat 64 (reserveCap cap1.toNat (prev.data ++ toBEBytes 4 ctr1).length 32)
    have hadd36' : prev.data.length + 36 ≤ cap2.toNat := by dsimp [cap2]; omega
    have hcap2 : cap2.toNat < 2 ^ 63 := hnew_lt
    have hcap2_eq : cap2.toNat = (doReserveStep cap1.toNat (prev.data.length + 4) 32).1 := by
      dsimp [cap2]
      rw [hstep_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hunpack2 := vecU8At_unpack A.repAlloc (epPtr + 0x50#64) cap2 p' (prev.data ++ toBEBytes 4 ctr1)
    rw [ha58, ha60] at hunpack2
    refine SepWPp.fold hunpack2 (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, _, hp'_ne⟩
    have hpack2 := vecU8At_pack_raw A.repAlloc (epPtr + 0x50#64) cap2 p' (prev.data ++ toBEBytes 4 ctr1)
      (by omega) hcap2 hp'_ne
    rw [ha58, ha60] at hpack2
    wp_norm_hyp hpc_sf; wp_norm_hyp hrun_sf; wp_norm_hyp hsp_sf_align; wp_norm_hyp hsp_sf
    wp_norm_hyp hx22_sf; wp_norm_hyp hlen_be4
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 408#64) hF_sf ?_
    wp_steps_sync_pool ((blkPl_366).base + 408#64)
    refine SepWP.fold hpack2 (by sep_focus) ?_
    have hstack_back :
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 nextKeyInternalStackX) 12352 ∗
          stackAt sf.sp doReserveStack =
          stackAt (s0.sp - 128#64) nextKeyInternalStackX := by
      rw [hsp_sf, ← stackAt_nextKeyInternalX_doReserve_split (s0.sp - 128#64)]
    refine SepWP.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF2
    have hinv2 : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF2, by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by rw [← hx26, ← hx26_sf]; wp_norm_goal,
       by rw [← hx27, ← hx27_sf]; wp_norm_goal,
       by rw [← hx28, ← hx28_sf]; wp_norm_goal,
       htr_sf,
       by rw [← hvregs, ← hvregs_sf]; wp_norm_goal,
       allocCallPreserved_trans hacp_0_sf (by unfold AllocCallPreserved; wp_norm_goal)⟩
    have hle_out : (prev.add (ctr1, key) x.self.params).data.length ≤ cap2.toNat := by omega
    have hst_eq :
        M.stepEvents (doReserveStep cap1.toNat (prev.data.length + 4) 32).2 st1 =
          M.stepEvents (doReserveEvents arg32) st1 := by
      rw [hstep_eq]
    refine SepWPp.mono_pre _ ?_
      (h_w408 (M.stepEvents (doReserveEvents arg32) st1) s0 c3 epochIndex hi_ep gce cap2 p'
        prev next1 key ctr1 hgt1 hkey_len hadd36' hcap2 hp'_ne
        (fun s' hinv_s' hpc_s' hx8_s' hx19_s' hw20_s' hx21_s' hx22_s' hw23_s' hx24_s' => by
          rw [← hst_eq]
          exact h_cont cap2 p' hcap2_eq hle_out hcap2 hp'_ne s' hinv_s' hpc_s' hx8_s' hx19_s'
            hw20_s' hx21_s' hx22_s' hw23_s' hx24_s')
        _ hinv2
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by rw [← hx19, ← hx19_sf]; wp_norm_goal)
        (by rw [← hw20, ← hx20_sf]; wp_norm_goal)
        (by rw [← hx21, ← hx21_sf]; wp_norm_goal)
        (by wp_norm_goal)
        (by rw [← hw23, ← hx23_sf]; wp_norm_goal)
        (by rw [← hx24, ← hx24_sf]; wp_norm_goal))
    sep_frame

set_option maxHeartbeats 1200000 in
theorem recvKey_add_from_496_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {H : String → Option (State → State)}
    (hdoRes : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (withAllocCallPreserved (doReserveSpec M A lim))))
    (x : ChainRecvKeyGhost) (st0 st_add : M.σ) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (prevPin : VecPin)
    (prev : KeyHistory) (next1 key : Bytes) (ctr1 : BitVec 32)
    (hgt1 : ctr1.toNat < x.index.toNat)
    (hkey_len : key.length = 32)
    (hp_fit : prev.data.length + 128 < 2 ^ 62)
    (hp_le : prev.data.length ≤ prevPin.cap.toNat)
    (hp_cap : prevPin.cap.toNat < 2 ^ 63) (hp_ptr : prevPin.ptr ≠ 0)
    (hfits_add : FitsEvents M lim st_add (keyHistoryAddStep prevPin.cap.toNat prev.data.length).2)
    (h_cont : ∀ (cap2 ptr2 : BitVec 64),
      cap2.toNat = (keyHistoryAddStep prevPin.cap.toNat prev.data.length).1 →
      (prev.add (ctr1, key) x.self.params).data.length ≤ cap2.toNat →
      cap2.toNat < 2 ^ 63 → ptr2 ≠ 0 →
      ∀ (s' : State),
        RecvKeyPlacedStateInv lsmpl s0 s' →
        s'.pc = (blkPl_366).base + 448#64 →
        (s'.readReg64 (.gpr 8#5)).setWidth 32 = ctr1 →
        s'.readReg64 (.gpr 19#5) = x.out →
        (s'.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s'.readReg64 (.gpr 21#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64 →
        s'.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        (s'.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault →
        s'.readReg64 (.gpr 24#5) = s0.sp - 120#64 →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        let prev' := prev.add (ctr1, key) x.self.params
        SepWPp ((blkPC_366).rebase (blkPl_366).base H)
          (s0.readReg64 (.gpr 30#5)) s'
          (memRegion x.out 32 ∗
            chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
            ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
            ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
            ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
            (gce.recv.next.ptr ↦ₛ next1) ∗
            vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr next1.length ∗
            ((epPtr + 0x50#64) ↦₆₄ cap2) ∗
            ((epPtr + 0x58#64) ↦₆₄ ptr2) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 prev'.data.length) ∗
            (ptr2 ↦ₛ prev'.data) ∗
            vecU8Rest A.repAlloc cap2 ptr2 prev'.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool lim (M.stepEvents (keyHistoryAddStep prevPin.cap.toNat prev.data.length).2 st_add) s')
          (recvKeyPost M A lim hkdf x st0 s0)
          (recvKeyPanic M A lim hkdf x st0 s0 R))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 496#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hw23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault)
    (hx24 : s.readReg64 (.gpr 24#5) = s0.sp - 120#64) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A.repAlloc x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
        ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
        (gce.recv.next.ptr ↦ₛ next1) ∗
        vecU8Rest A.repAlloc gce.recv.next.cap gce.recv.next.ptr next1.length ∗
        ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 prev.data.length) ∗
        (prevPin.ptr ↦ₛ prev.data) ∗
        vecU8Rest A.repAlloc prevPin.cap prevPin.ptr prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        ((s0.sp - 120#64) ↦₃₂ ctr1) ∗
        ((s0.sp - 116#64) ↦ₛ key) ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool lim st_add s)
      (recvKeyPost M A lim hkdf x st0 s0)
      (recvKeyPanic M A lim hkdf x st0 s0 R) := by
  intro s_idx epPtr
  have h_add520 := @recvKey_add_from_520_placed _ M A lim hkdf H hdoRes x st0
  dsimp only [s_idx, epPtr]; clear s_idx epPtr
  have hfits_pair :
      FitsEvents M lim st_add
        ((doReserveStep prevPin.cap.toNat prev.data.length 4).2 ++
          (doReserveStep (doReserveStep prevPin.cap.toNat prev.data.length 4).1
            (prev.data.length + 4) 32).2) := by
    simpa only [keyHistoryAddStep] using hfits_add
  obtain ⟨hfits_step1, hfits_step2⟩ := (fitsEvents_append M lim _ _ st_add).mp hfits_pair
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs, hacp⟩
  wp_norm_hyp hvregs
  have ⟨hlen_toNat, hule3, hult3⟩ := add_check4_props hp_le hp_cap
  let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
  have ha58 : epPtr + 0x50#64 + 8#64 = epPtr + 0x58#64 := by bv_kernel
  have ha60 : epPtr + 0x50#64 + 16#64 = epPtr + 0x60#64 := by bv_kernel
  have hpack0 := vecU8At_pack_raw A.repAlloc (epPtr + 0x50#64) prevPin.cap prevPin.ptr prev.data hp_le hp_cap hp_ptr
  rw [ha58, ha60] at hpack0
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx19; wp_norm_hyp hw20; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hw23; wp_norm_hyp hx24; wp_norm_hyp htrace
  wp_norm_hyp hule3; wp_norm_hyp hult3
  by_cases hadd4 : prev.data.length + 4 ≤ prevPin.cap.toNat
  · have hadd4_t : decide (prev.data.length + 4 ≤ prevPin.cap.toNat) = true := decide_eq_true hadd4
    wp_norm_hyp hadd4_t
    have hstep1_eq : doReserveStep prevPin.cap.toNat prev.data.length 4 = (prevPin.cap.toNat, []) :=
      doReserveStep_of_le hadd4
    have hfits_step2' : FitsEvents M lim st_add (doReserveStep prevPin.cap.toNat (prev.data.length + 4) 32).2 := by
      simpa only [hstep1_eq, AllocCostModel.stepEvents_nil] using hfits_step2
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 520#64) hF ?_
    wp_steps_sync_pool ((blkPl_366).base + 520#64)
    refine SepWP.fold hpack0 (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by rw [← hx26]; wp_norm_goal,
       by rw [← hx27]; wp_norm_goal,
       by rw [← hx28]; wp_norm_goal,
       htrace, by wp_norm_goal,
       allocCallPreserved_trans hacp (by unfold AllocCallPreserved; wp_norm_goal)⟩
    have hkh_fst :
        (keyHistoryAddStep prevPin.cap.toNat prev.data.length).1 =
          (doReserveStep prevPin.cap.toNat (prev.data.length + 4) 32).1 := by
      simp [keyHistoryAddStep, hstep1_eq]
    have hkh_snd :
        (keyHistoryAddStep prevPin.cap.toNat prev.data.length).2 =
          (doReserveStep prevPin.cap.toNat (prev.data.length + 4) 32).2 := by
      simp [keyHistoryAddStep, hstep1_eq]
    refine SepWPp.mono_pre _ ?_
      (h_add520 st_add s0 c3 epochIndex hi_ep gce prevPin.cap prevPin.ptr prev next1 key ctr1
        hgt1 hkey_len hp_fit hadd4 hp_cap hp_ptr hfits_step2'
        (fun cap2 ptr2 hcap2 hle2 hlt2 hp2 s' hinv_s' hpc_s' hx8_s' hx19_s' hw20_s' hx21_s' hx22_s' hw23_s' hx24_s' => by
          rw [← hkh_snd]
          exact h_cont cap2 ptr2 (hcap2.trans hkh_fst.symm) hle2 hlt2 hp2 s' hinv_s' hpc_s' hx8_s'
            hx19_s' hw20_s' hx21_s' hx22_s' hw23_s' hx24_s')
        _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame
  · have hadd4_f : decide (prev.data.length + 4 ≤ prevPin.cap.toNat) = false := decide_eq_false hadd4
    wp_norm_hyp hadd4_f
    have ⟨hres_bound, hnew_ge, hnew_lt⟩ :=
      reserveCap_props (cap := prevPin.cap.toNat) (len := prev.data.length) (additional := 4)
        (by omega) (by decide) hadd4
    let arg4 : DoReserveCall := ⟨epPtr + 0x50#64, prevPin.cap, prevPin.ptr, prev.data, 4⟩
    have hstep1_eq :
        doReserveStep prevPin.cap.toNat prev.data.length 4 =
          (reserveCap prevPin.cap.toNat prev.data.length 4, doReserveEvents arg4) :=
      doReserveStep_of_not_le arg4 hadd4
    have hfits_arg4 : FitsEvents M lim st_add (doReserveEvents arg4) := by
      simpa only [hstep1_eq] using hfits_step1
    refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 320) hF ?_
    wp_steps_sync_pool (lsmpl.base 320)
    refine SepWP.fold hpack0 (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_doReserve_split (s0.sp - 128#64))) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF1
    refine call_doReserve_lsCallInv hdoRes arg4 st_add ((blkPl_366).base + 604#64) x st0 s0 _ hF1
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [State.spAligned, arm64_norm, hsp] at hsp0_align ⊢; revert hsp0_align; bv_kernel)
      (by wp_norm_goal)
      (by simp only [arm64_norm, htrace])
      (by dsimp [arg4, epPtr]; wp_norm_goal)
      (by dsimp [arg4]; rw [← hlen_toNat]; wp_norm_goal)
      (by dsimp [arg4]; wp_norm_goal)
      (by wp_norm_goal) (by wp_norm_goal) hres_bound hfits_arg4
      (by simp only [arm64_norm, hsp]; sep_frame) ?_
    intro sf p' hpc_sf hrun_sf hsp_sf hcs_sf hF_sf hacp_sf htr_sf
    have hacp_0_sf : AllocCallPreserved s0 sf := by
      refine allocCallPreserved_trans ?_ hacp_sf
      refine allocCallPreserved_trans hacp ?_
      unfold AllocCallPreserved; wp_norm_goal
    simp only [arm64_norm, hsp] at hsp_sf
    have hsp_sf_align : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf] at hsp0_align ⊢; revert hsp0_align; bv_kernel
    rcases hcs_sf with ⟨hx19_sf, hx20_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf, hx25_sf, hx26_sf, hx27_sf, hx28_sf, _, hvregs_sf⟩
    simp only [arm64_norm] at hx19_sf hx20_sf hx21_sf hx22_sf hx23_sf hx24_sf hx25_sf hx26_sf hx27_sf hx28_sf hvregs_sf
    let cap1 := BitVec.ofNat 64 (reserveCap prevPin.cap.toNat prev.data.length 4)
    have hadd4' : prev.data.length + 4 ≤ cap1.toNat := hnew_ge
    have hcap1 : cap1.toNat < 2 ^ 63 := hnew_lt
    have hcap1_toNat : cap1.toNat = reserveCap prevPin.cap.toNat prev.data.length 4 := by
      dsimp [cap1]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hunpack1 := vecU8At_unpack A.repAlloc (epPtr + 0x50#64) cap1 p' prev.data
    rw [ha58, ha60] at hunpack1
    refine SepWPp.fold hunpack1 (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, _, hp'_ne⟩
    have hpack1 := vecU8At_pack_raw A.repAlloc (epPtr + 0x50#64) cap1 p' prev.data
      (by omega) hcap1 hp'_ne
    rw [ha58, ha60] at hpack1
    wp_norm_hyp hpc_sf; wp_norm_hyp hrun_sf; wp_norm_hyp hsp_sf_align; wp_norm_hyp hsp_sf; wp_norm_hyp hx22_sf
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 520#64) hF_sf ?_
    wp_steps_sync_pool ((blkPl_366).base + 520#64)
    refine SepWP.fold hpack1 (by sep_focus) ?_
    have hstack_back :
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 nextKeyInternalStackX) 12352 ∗
          stackAt sf.sp doReserveStack =
          stackAt (s0.sp - 128#64) nextKeyInternalStackX := by
      rw [hsp_sf, ← stackAt_nextKeyInternalX_doReserve_split (s0.sp - 128#64)]
    refine SepWP.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF2
    have hinv2 : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF2, by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by rw [← hx26, ← hx26_sf]; wp_norm_goal,
       by rw [← hx27, ← hx27_sf]; wp_norm_goal,
       by rw [← hx28, ← hx28_sf]; wp_norm_goal,
       htr_sf,
       by rw [← hvregs, ← hvregs_sf]; wp_norm_goal,
       allocCallPreserved_trans hacp_0_sf (by unfold AllocCallPreserved; wp_norm_goal)⟩
    have hfits_step2' :
        FitsEvents M lim (M.stepEvents (doReserveEvents arg4) st_add)
          (doReserveStep cap1.toNat (prev.data.length + 4) 32).2 := by
      simpa only [hstep1_eq, hcap1_toNat] using hfits_step2
    have hkh_fst :
        (keyHistoryAddStep prevPin.cap.toNat prev.data.length).1 =
          (doReserveStep cap1.toNat (prev.data.length + 4) 32).1 := by
      simp [keyHistoryAddStep, hstep1_eq, hcap1_toNat]
    have hkh_st :
        M.stepEvents (keyHistoryAddStep prevPin.cap.toNat prev.data.length).2 st_add =
          M.stepEvents (doReserveStep cap1.toNat (prev.data.length + 4) 32).2
            (M.stepEvents (doReserveEvents arg4) st_add) := by
      simp [keyHistoryAddStep, hstep1_eq, hcap1_toNat, AllocCostModel.stepEvents_append]
    refine SepWPp.mono_pre _ ?_
      (h_add520 (M.stepEvents (doReserveEvents arg4) st_add) s0 c3 epochIndex hi_ep gce cap1 p'
        prev next1 key ctr1 hgt1 hkey_len hp_fit hadd4' hcap1 hp'_ne hfits_step2'
        (fun cap2 ptr2 hcap2 hle2 hlt2 hp2 s' hinv_s' hpc_s' hx8_s' hx19_s' hw20_s' hx21_s' hx22_s' hw23_s' hx24_s' => by
          rw [← hkh_st]
          exact h_cont cap2 ptr2 (hcap2.trans hkh_fst.symm) hle2 hlt2 hp2 s' hinv_s' hpc_s' hx8_s'
            hx19_s' hw20_s' hx21_s' hx22_s' hw23_s' hx24_s')
        _ hinv2 (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by rw [← hx19, ← hx19_sf]; wp_norm_goal)
        (by rw [← hw20, ← hx20_sf]; wp_norm_goal)
        (by rw [← hx21, ← hx21_sf]; wp_norm_goal)
        (by wp_norm_goal)
        (by rw [← hw23, ← hx23_sf]; wp_norm_goal)
        (by rw [← hx24, ← hx24_sf]; wp_norm_goal)
        (by simp only [arm64_norm, hx25_sf]))
    sep_frame

end LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyAddBudget
