/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsV1StatePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge2Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge2
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodePlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerDispatchPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `spqr::send` Phase 3d–3e Bridge (`+4000 -> +6216`)

Threads `RustCliAllocBudget` and `VmPreserved` through the `[LibsignalPlacement]` Phase 3d–3e
composition (`<Message>::serialize`, `States` relocation, `<States>::into_pb`, `PqRatchetState`
assembly, and `PqRatchetState::encode_to_vec`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge2PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded libsignalSessionCode lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded sessionMemcpyRegionSpec withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (ChainPB Message PqRatchetState States V1State VersionNegotiationPB spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
  (Relocatable relocatedHeap relocatedHeap_recompose)
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStatePBGhost StepInv VRegsAt optChainCap optVersionNegCap
   optVersionNegotiationPBAt_eq_exists_pinned pqRatchetStatePBEncodedLen
   pqRatchetStatePBPinnedAt)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation (noneCap)
open CryptoVerification.SpqrV1.Top.MessageSerialize
  (MessageSerializeGhost messageAt messageSerializeStackX)
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced
open CryptoVerification.Cli.SpqrV1.ProtoRepr
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   SeqEnv VmPreserved rustAllocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget (etvMemcpyRegionSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (StepInvVm sepWPp_call_cs_noPanic sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs StatesIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (statesIntoPbPlacedSpecX statesIntoPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (MessageSerializeEnv messageSerializeSpecX messageSerializeSpecXOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodePlacedBudget
  (step_copy_pq_state_none_3185c_placed step_copy_pq_state_some_3185c_placed
   step_post_memcpy_to_into_pb_3184c_placed
   step_post_message_serialize_to_memcpy_31810_placed
   step_pre_message_serialize_317fc_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerHeaderPlacedBudget
  (spqrSend_etvMemcpy_ok_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesInnerDispatchPlacedBudget
  (step_send_encode_from_vn_len_self_contained_placed)

variable [LibsignalPlacement]

/-! ## 1. `VmPreserved`-Strengthened `memcpy` Relocation Helpers (`+4020..+4096`) -/

private theorem call_memcpy_bytes_bridge2 {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry etvMemcpyRegionSpec)
    (dst src : BitVec 64) {bs : List (BitVec 8)} {n : Nat} (hlen : bs.length = n)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (src ↦ₛ bs)) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      VmPreserved s sf → VRegsAt s sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      SepWP prog target_pc sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [etvMemcpyRegionSpec, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun hvm => SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (htr.trans htrace) hvm
      ⟨hcs_sf.2.2.2.2.2.2.2.2.2.2.2⟩
      hcs_sf.1 hcs_sf.2.1 hcs_sf.2.2.1 hcs_sf.2.2.2.1 hcs_sf.2.2.2.2.1
      hcs_sf.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.1
      hcs_sf.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.1

private theorem call_memcpy_relocate_bridge2 {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry etvMemcpyRegionSpec)
    (dst src : BitVec 64) {n : Nat} {F : BitVec 64 → SepProp}
    (hrel : Relocatable n F)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      VmPreserved s sf → VRegsAt s sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (hrel src))) ?_
  wp_pull_exists; rename_i bs
  wp_focus_pure; intro hlen
  refine call_memcpy_bytes_bridge2 hcall dst src hlen hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2
    (Frame := relocatedHeap F bs ∗ Frame) (by sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hvm_sf hv_sf hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28
  have hrecomp := relocatedHeap_recompose F bs dst
  have hsrc : (src ↦ₛ bs) ⊢ memRegion src n := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion src bs
  refine SepWP.weaken_pre ?_
    (hnext sf hpc_sf hrun_sf hsp_sf htr_sf hvm_sf hv_sf hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28)
  refine Entails.trans (Entails.of_eq (show
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (relocatedHeap F bs ∗ Frame) =
    (((dst ↦ₛ bs) ∗ relocatedHeap F bs) ∗ (src ↦ₛ bs)) ∗ Frame by sep_ac_rfl)) ?_
  exact sepConj_mono_left (sepConj_mono hrecomp hsrc)

/-! ## 2. `PqRatchetState` Copy & Assembly (`+4096 -> +4288 / +4364`) -/

/-- Combines `spqrSendPlacedEntry + 4096#64 -> spqrSendPlacedEntry + (if vn.isSome then 4288#64 else 4364#64)`
    with unpacking and reassembling `pqRatchetStatePBPinnedAt A g (s.sp + 4704#64)`,
    preserving `VmPreserved s sf` and `VRegsAt s sf`. -/
theorem step_copy_and_assemble_pq_state_3185c_placed {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (s : State) (v_20 : BitVec 64)
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F))
    (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4096#64)
    (hrun : s.status = .Running)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    let pq' : PqRatchetState :=
      { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + (if vn.isSome then 4288#64 else 4364#64)) s
      (((s.sp + 0x20#64) ↦₆₄ v_20) ∗
        optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
        optChainPBRegSlotAt A (s.sp + 0xd90#64) (s.readReg64 .x25) ch ∗
        optProtoInnerStateAt A (s.sp + 0x590#64) st1.into_pb.innerState ∗
        memRegion (s.sp + 0x1260#64) 352 ∗ Frame)
      (fun sf Q => VmPreserved s sf ∧ VRegsAt s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        ∃ g : PqRatchetStatePBGhost,
          sf.readReg64 .x25 = optChainCap g.chain pq'.chain ∧
          sf.readReg64 .x26 = optVersionNegCap g.vn pq'.versionNegotiation ∧
          (sf.readReg64 .x25 + 1#64 == 0#64) = !pq'.chain.isSome ∧
          (Q ⊢ ((s.sp + 0x20#64) ↦₆₄ s.readReg64 .x20) ∗
            pqRatchetStatePBPinnedAt A g (s.sp + 4704#64) pq' ∗
            memRegion (s.sp + 0x30#64) 48 ∗
            memRegion (s.sp + 0xd90#64) 72 ∗
            memRegion (s.sp + 0x590#64) 224 ∗ Frame)) := by
  intro pq'
  obtain ⟨is, his⟩ := states_into_pb_innerState_isSome st1
  rw [his, optVersionNegotiationPBAt_eq_exists_pinned A (s.sp + 0x30#64) vn]
  wp_pull_exists; rename_i g_vn
  refine SepWP.focus_weaken
    (optVersionNegotiationPBPinnedAt_entails_vnWords6 A g_vn (s.sp + 0x30#64) vn) (by sep_focus) ?_
  wp_pull_exists; rename_i w1 w2 w3 w4 w5
  refine SepWP.focus_weaken
    (optChainPBRegSlotAt_entails_chainWords9 A (s.sp + 0xd90#64) (s.readReg64 .x25) ch)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g_ch c1 c2 c3 c4 c5 c6 c7 c8 c9
  refine SepWP.focus_weaken
    (optChainWordsHeap_x25_eq A g_ch (s.readReg64 .x25) ch c1 c2 c3 c4 c5 c6 c7 c8 c9)
    (by sep_focus) ?_
  wp_focus_pure; rintro ⟨hx25_cap, hx25_some⟩
  refine SepWP.focus_weaken
    (optProtoInnerStateAt_some_entails_outWords28 A (s.sp + 0x590#64) is) (by sep_focus) ?_
  wp_pull_exists
  rename_i i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
    i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216
  have h4704 : s.sp + 0x1260#64 = s.sp + 4704#64 := rfl
  have h4752 : s.sp + 0x1290#64 = (s.sp + 4704#64) + 48#64 := by bv_omega
  have h4760 : s.sp + 0x1298#64 = ((s.sp + 4704#64) + 48#64) + 8#64 := by bv_omega
  have h4832 : s.sp + 0x12e0#64 = (s.sp + 4704#64) + 128#64 := by bv_omega
  cases vn with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    have hvn_none : vnWords6At (s.sp + 0x30#64) (optVersionNegCap g_vn none) w1 w2 w3 w4 w5 =
        vnWords6At (s.sp + 0x30#64) noneCap w1 w2 w3 w4 w5 := rfl
    have hvn_none' : vnWords6At (s.sp + 4704#64) noneCap w1 w2 w3 w4 w5 =
        vnWords6At (s.sp + 4704#64) (optVersionNegCap g_vn none) w1 w2 w3 w4 w5 := rfl
    rw [hvn_none]
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.seq (LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodePlacedBudget.step_copy_pq_state_none_3185c_placed s v_20 w1 w2 w3 w4 w5
        c1 c2 c3 c4 c5 c6 c7 c8 c9
        i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
        i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216
        (optVersionNegWordsHeap A g_vn none w1 w2 w3 w4 w5 ∗
          optChainWordsHeap A g_ch (s.readReg64 .x25) ch c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
          protoInnerWordsHeap A is
            i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
            i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 ∗ Frame)
        hpc hrun hx26 hsp_align) ?_)
    intro sf Qf hpcf _
    rintro ⟨hvmf, hvf, hrunf, htrf, hspf, hx26f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx27f, hx28f, hQf⟩
    refine SepWP.weaken_pre hQf ?_
    rw [h4704, h4752, h4760, h4832, hvn_none']
    have hvn_pack := vnWords6_entails_optVersionNegotiationPBPinnedAt A g_vn (s.sp + 4704#64) none w1 w2 w3 w4 w5
    have hch_pack := chainWords9_entails_optChainPBPinnedAt A g_ch ((s.sp + 4704#64) + 48#64) (s.readReg64 .x25) ch
      c1 c2 c3 c4 c5 c6 c7 c8 c9
    have hin_pack := outWords28_entails_v1StatePBPinnedAt A ((s.sp + 4704#64) + 128#64) st1.into_pb is his
      i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
      i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216
    refine SepWP.focus_weaken hvn_pack (by sep_focus) ?_
    refine SepWP.focus_weaken hch_pack (by sep_focus) ?_
    refine SepWP.focus_weaken hin_pack (by sep_focus) ?_
    wp_pull_exists; rename_i g_v1
    refine ProofLib.SepWP.done hpcf hrunf
      ⟨hvmf, hvf, hrunf, htrf, hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx27f, hx28f,
        ⟨g_vn, g_ch.toProtoRepr, g_v1⟩, hx25f.trans hx25_cap, hx26f, by rw [hx25f]; exact hx25_some, ?_⟩
    unfold pqRatchetStatePBPinnedAt
    dsimp only [pq']
    exact Entails.of_eq (by sep_ac_rfl)
  | some v =>
    simp only [Option.isSome_some, ↓reduceIte]
    refine SepWP.focus_weaken
      (optVersionNegWordsHeap_some_cap_ne A g_vn v w1 w2 w3 w4 w5) (by sep_focus) ?_
    wp_focus_pure; intro hw0_ne
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.seq (LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodePlacedBudget.step_copy_pq_state_some_3185c_placed s v_20
        (optVersionNegCap g_vn (some v)) w1 w2 w3 w4 w5
        c1 c2 c3 c4 c5 c6 c7 c8 c9
        i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
        i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216
        (optVersionNegWordsHeap A g_vn (some v) w1 w2 w3 w4 w5 ∗
          optChainWordsHeap A g_ch (s.readReg64 .x25) ch c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
          protoInnerWordsHeap A is
            i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
            i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 ∗ Frame)
        hpc hrun hx26 hw0_ne hsp_align) ?_)
    intro sf Qf hpcf _
    rintro ⟨hvmf, hvf, hrunf, htrf, hspf, hx26f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx27f, hx28f, hQf⟩
    refine SepWP.weaken_pre hQf ?_
    rw [h4704, h4752, h4760, h4832]
    have hvn_pack := vnWords6_entails_optVersionNegotiationPBPinnedAt A g_vn (s.sp + 4704#64) (some v) w1 w2 w3 w4 w5
    have hch_pack := chainWords9_entails_optChainPBPinnedAt A g_ch ((s.sp + 4704#64) + 48#64) (s.readReg64 .x25) ch
      c1 c2 c3 c4 c5 c6 c7 c8 c9
    have hin_pack := outWords28_entails_v1StatePBPinnedAt A ((s.sp + 4704#64) + 128#64) st1.into_pb is his
      i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
      i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216
    refine SepWP.focus_weaken hvn_pack (by sep_focus) ?_
    refine SepWP.focus_weaken hch_pack (by sep_focus) ?_
    refine SepWP.focus_weaken hin_pack (by sep_focus) ?_
    wp_pull_exists; rename_i g_v1
    refine ProofLib.SepWP.done hpcf hrunf
      ⟨hvmf, hvf, hrunf, htrf, hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx27f, hx28f,
        ⟨g_vn, g_ch.toProtoRepr, g_v1⟩, hx25f.trans hx25_cap, hx26f, by rw [hx25f]; exact hx25_some, ?_⟩
    unfold pqRatchetStatePBPinnedAt
    dsimp only [pq']
    exact Entails.of_eq (by sep_ac_rfl)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup

/-! ## 3. Outcome-Polymorphic `SepWPp` Combinators & `+4020 -> lsmpl.base 334` Step -/

/-- Outcome-polymorphic (`Q`, `Qp`, `oom`) `SepWPp` step combinator preserving
    `LibsignalCodeRoLoaded lsmpl` and `StepInvVm`. -/
theorem sepWPp_of_sepWP_lscro_b2 {prog : Program} {ret mid : BitVec 64}
    {s : State} (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ProofLib.SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧ VRegsAt s sm ∧
        (LibsignalCodeRoLoaded lsmpl sm.mem → StepInvVm s sm → SepWPp prog ret sm Pm Q Qp oom))) :
    SepWPp prog ret s P Q Qp oom :=
  sepWPp_of_sepWP_cs_vm (SepWP.mono h fun _ _ _ _ ⟨hvm, hv, hnext⟩ =>
    ⟨hvm, hv, fun hstep => hnext ⟨hstep.libsignalCodeLoaded hinv.1, hstep.libsignalRoLoaded hinv.2⟩ hstep⟩)

/-- Outcome-polymorphic (`Q`, `Qp`, `oom`) `SepWPp` call rule for a budget-threaded
    `withLsCodeRoLoaded lsmpl` callee (`onExit = onPanic = onOom = ⌜False⌝`) whose stack fits in
    `spqrSendCalleeStack`, unpacking an existential `evs : List AllocEvent` from `spec.post`. -/
theorem sepWPp_call_lscro_calleeStack_evs_b2 {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α}
    {s : State} (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : List AllocEvent → State → SepProp} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    {φ_pre : Prop} {φ_post : List AllocEvent → State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n) ⊢ spec.pre x s)
    (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hspec_post : ∀ sf, spec.post x s sf ⊢
      ∃∗ evs : List AllocEvent, ⌜φ_post evs sf⌝ ∗ T_post evs sf ∗ stackAt s.sp n)
    (hnext : ∀ (evs : List AllocEvent) (sf : State),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post evs sf → LibsignalCodeRoLoaded lsmpl sf.mem → StepInv s sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post evs sf) ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  let F_ext := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  refine sepWPp_call_cs_noPanic (x := x) (F := F_ext) hcall hpc hrun hsp_al hlr ?_ ?_ ?_ ?_ ?_
  · intro R hm
    change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ (F_ext ∗ R)
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    refine Satisfies.mono (sepConj_mono_left hspec_pre) ?_
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hφ, ?_⟩
    rw [hP, stackAt_spqrSendCallee_split_b2 sp n hle] at hm
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; sep_ac_rfl)) hm
  · intro sf code R _ hm
    change sf.mem ⊨ spec.onExit x code s sf ∗ R at hm
    rw [hexit_eq code sf] at hm
    exact not_satisfies_false_sepConj hm
  · intro sf R _ hm
    change sf.mem ⊨ spec.onPanic x s sf ∗ R at hm
    rw [hpan_eq sf] at hm
    exact not_satisfies_false_sepConj hm
  · intro sf R _ hm
    change sf.mem ⊨ spec.onOom x s sf ∗ R at hm
    rw [hoom_eq sf] at hm
    exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hstep
    change SepWPp prog ret sm (spec.post x s sm ∗ F_ext) Q Qp oom
    refine SepWPp.weaken_pre (sepConj_mono_left (hspec_post sm)) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun evs => ?_
    rw [hsp]
    refine SepWPp.weaken_pre (Entails.of_eq (show
      (⌜φ_post evs sm⌝ ∗ T_post evs sm ∗ stackAt sp n) ∗ F_ext =
      ⌜φ_post evs sm⌝ ∗ ((stackAt sp spqrSendCalleeStack ∗ T_post evs sm) ∗ F) by
        rw [stackAt_spqrSendCallee_split_b2 sp n hle]; dsimp only [F_ext]; sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun hφ_post => ?_
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
    exact hnext evs sm hpcm hrunm (hspm.trans hsp) hφ_post
      ⟨hstep.libsignalCodeLoaded hinv.1, hstep.libsignalRoLoaded hinv.2⟩ hstep
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs

/-- Outcome-polymorphic (`Q`, `Qp`, `oom`) introduction of the three Bridge 2 `.rodata` jump tables
    (`v1StateJumpTableBytes`, `spqrSendEncodeJumpTableBytes`, `CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt`) from
    `LibsignalRoLoaded lsmpl s.mem`. -/
theorem sepWPp_intro_rodata_bridge2_placed
    {prog : Program} {ret : BitVec 64} {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog ret s
      (((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
       ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
       CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ P) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hm3 := CryptoVerification.Cli.SpqrV1.ProtoRepr.v1StateJumpTableBytes_lsro_cli_intro hro
    (CryptoVerification.Cli.SpqrV1.Top.Send.lsro_spqrSendEncodeJumpTableBytes_intro hro
      (CryptoVerification.SpqrV1.States.IntoPb.lsro_statesIntoPbJumpTablePlacedAt hro hm))
  exact h R (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm3) hL

/-- `spqrSendPlacedEntry + 4020#64 -> lsmpl.base 334`: checks `msg.serialize idx = 1#8 :: tail`,
    relocates `chunkedStatesAt` via `memcpy`, and sets up `<States>::into_pb` (`lsmpl.base 334`,
    return `spqrSendPlacedEntry + 4096#64`), preserving `VmPreserved s sf` and `VRegsAt s sf`. -/
theorem step_post_message_serialize_to_into_pb_31810_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) (s : State) (tail : List (BitVec 8))
    (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4020#64)
    (hrun : s.status = .Running) (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (lsmpl.base 334) s
      (vecU8 A.repAlloc (s.sp + 0xff0#64) (1#8 :: tail) ∗ memRegion (s.sp + 0x1260#64) 928 ∗
        chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ Frame)
      (fun sf Q => VmPreserved s sf ∧ VRegsAt s sf ∧
        sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x1260#64 ∧ sf.readReg64 .x8 = s.sp + 0x590#64 ∧
        sf.readReg64 .x30 = spqrSendPlacedEntry + 4096#64 ∧
        sf.readReg64 .x24 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Q ⊢ chunkedStatesAt A.repAlloc (s.sp + 0x1260#64) st1 ∗ memRegion (s.sp + 0x190#64) 928 ∗
          vecU8 A.repAlloc (s.sp + 0xff0#64) (1#8 :: tail) ∗ Frame)) := by
  have hmcpy := spqrSend_etvMemcpy_ok_placed hA
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.seq (step_post_message_serialize_to_memcpy_31810_placed (A := A) s tail
      (chunkedStatesAt A.repAlloc (s.sp + 0x190#64) st1 ∗ Frame) hpc hrun hx26 hsp_align) ?_)
  intro s1 Q1 hpc1 _ ⟨hvm1, hv1, hrun1, htr1, hsp1, hx0_1, hx1_1, hx2_1, hlr1, hx24_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hQ1⟩
  refine SepWP.weaken_pre hQ1 ?_
  refine call_memcpy_relocate_bridge2 hmcpy (s.sp + 0x1260#64) (s.sp + 0x190#64)
    (CryptoVerification.SpqrV1.Top.Send.Relocatable.of_chunkedStatesAt A.repAlloc st1)
    hpc1 hrun1 hsp1 hsp_align hlr1 htr1 hx0_1 hx1_1
    (by rw [hx2_1]; rfl) (Frame := vecU8 A.repAlloc (s.sp + 0xff0#64) (1#8 :: tail) ∗ Frame)
    (by sep_ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hvm2 hv2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2]
  refine SepWP.mono (LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodePlacedBudget.step_post_memcpy_to_into_pb_3184c_placed s2 _ hpc2 hrun2 hsp2_align) ?_
  intro sf Qf _ _ ⟨hvmf, hvf, hrunf, htrf, hspf, hx0f, hx8f, hlrf,
    hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hQf⟩
  rw [hsp2] at hspf hx0f hx8f; rw [hQf]
  exact ⟨hvm1.trans (hvm2.trans hvmf), ⟨hvf.eq.trans (hv2.eq.trans hv1.eq)⟩,
    hrunf, htrf.trans htr2, hspf, hx0f, hx8f, hlrf,
    hx24f.trans (hx24_2.trans hx24_1), hx19f.trans (hx19_2.trans hx19_1),
    hx20f.trans (hx20_2.trans hx20_1), hx21f.trans (hx21_2.trans hx21_1),
    hx22f.trans (hx22_2.trans hx22_1), hx23f.trans (hx23_2.trans hx23_1),
    hx25f.trans (hx25_2.trans hx25_1), hx26f.trans (hx26_2.trans hx26_1),
    hx27f.trans (hx27_2.trans hx27_1), hx28f.trans (hx28_2.trans hx28_1),
    Entails.of_eq (by sep_ac_rfl)⟩

/-! ## 4. Bridge 2 Allocation Envelopes & Full Phase 3d–3e Composition (`+4000 -> +6216`) -/

/-- Envelope-parametric allocation envelope across Phase 3d–3e Bridge 2 (`+4000 -> +6216`):
    `<Message>::serialize`, `<States>::into_pb`, and `PqRatchetState::encode_to_vec`'s single
    `rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1` buffer allocation. -/
def SendBridge2EnvOfEnv {F : ShaCompress}
    (MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop)
    (IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop)
    (sp : BitVec 64) (idx : BitVec 32)
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    List AllocEvent → Prop :=
  let pq' : PqRatchetState :=
    { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }
  SeqEnv
    (MsgSerEnv { msgA := sp + 0x1d70#64, index := idx, ret := sp + 0xff0#64, msg := msg })
    (SeqEnv
      (IntoPbEnv { out := sp + 0x590#64, stA := sp + 0x1260#64, st := st1 })
      (fun evs => evs = rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1))

/-- Default allocation envelope across Phase 3d–3e Bridge 2 (`+4000 -> +6216`),
    instantiating `MessageSerializeEnv (P := spqrPolyApi)` and `StatesIntoPbEnv`. -/
def SendBridge2Env {F : ShaCompress}
    (idx : BitVec 32) (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    List AllocEvent → Prop :=
  let pq' : PqRatchetState :=
    { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }
  SeqEnv
    (MessageSerializeEnv (P := spqrPolyApi)
      { msgA := 0#64, index := idx, ret := 0#64, msg := msg })
    (SeqEnv
      (StatesIntoPbEnv { out := 0#64, stA := 0#64, st := st1 })
      (fun evs => evs = rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1))

omit [LibsignalPlacement] in
theorem sendBridge2Env_eq_ofEnv {F : ShaCompress}
    (sp : BitVec 64) (idx : BitVec 32)
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    SendBridge2Env idx vn ch st1 msg =
      SendBridge2EnvOfEnv (MessageSerializeEnv (P := spqrPolyApi)) StatesIntoPbEnv sp idx vn ch st1 msg :=
  rfl

omit [LibsignalPlacement] in
theorem sendBridge2EnvOfEnv_intro {F : ShaCompress}
    {MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {sp : BitVec 64} {idx : BitVec 32}
    {vn : Option VersionNegotiationPB} {ch : Option ChainPB}
    {st1 : States spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    {evs₁ evs₂ : List AllocEvent}
    (hmser : MsgSerEnv { msgA := sp + 0x1d70#64, index := idx, ret := sp + 0xff0#64, msg := msg } evs₁)
    (hinto : IntoPbEnv { out := sp + 0x590#64, stA := sp + 0x1260#64, st := st1 } evs₂) :
    SendBridge2EnvOfEnv MsgSerEnv IntoPbEnv sp idx vn ch st1 msg
      (evs₁ ++ (evs₂ ++ rustAllocEvents
        (pqRatchetStatePBEncodedLen { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }) 1)) :=
  SeqEnv.append hmser (SeqEnv.append hinto rfl)

omit [LibsignalPlacement] in
theorem sendBridge2Env_nonempty {F : ShaCompress}
    (idx : BitVec 32) (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    SendBridge2Env idx vn ch st1 msg
      (([] : List AllocEvent) ++
        ([] ++ rustAllocEvents
          (pqRatchetStatePBEncodedLen { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }) 1)) :=
  SeqEnv.append ⟨Nat.zero_le _, fun _ h => nomatch h⟩
    (SeqEnv.append ⟨Nat.zero_le _, fun _ h => nomatch h⟩ rfl)

omit [LibsignalPlacement] in
/-- Slice `FitsEnv` for `SendBridge2EnvOfEnv` out of a right-nested `SeqEnv` continuation
    (matching `SpqrSendPartsTightGenEnv`'s `SeqEnv Emsg (SeqEnv Esinto (SeqEnv Epq E_tail))`). -/
theorem fitsEnv_sendBridge2EnvOfEnv_of_seq_tail
    {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ} {F : ShaCompress}
    {MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {E_tail : List AllocEvent → Prop}
    {sp : BitVec 64} {idx : BitVec 32}
    {vn : Option VersionNegotiationPB} {ch : Option ChainPB}
    {st1 : States spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    (h : FitsEnv M lim st0
      (SeqEnv
        (MsgSerEnv { msgA := sp + 0x1d70#64, index := idx, ret := sp + 0xff0#64, msg := msg })
        (SeqEnv
          (IntoPbEnv { out := sp + 0x590#64, stA := sp + 0x1260#64, st := st1 })
          (SeqEnv
            (fun evs => evs = rustAllocEvents
              (pqRatchetStatePBEncodedLen
                { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }) 1)
            E_tail)))) :
    FitsEnv M lim st0 (SendBridge2EnvOfEnv MsgSerEnv IntoPbEnv sp idx vn ch st1 msg) := by
  refine h.mono fun evs hevs => ?_
  rcases hevs with h1 | ⟨e1, e23, rfl, h1, h2 | ⟨e2, e3, rfl, h2, h3⟩⟩
  · exact Or.inl h1
  · exact Or.inr ⟨e1, e23, rfl, h1, Or.inl h2⟩
  · exact Or.inr ⟨e1, e2 ++ e3, rfl, h1, Or.inr ⟨e2, e3, rfl, h2, Or.inl h3⟩⟩

/-- Envelope-parametric full Phase 3d–3e bridge
    (`spqrSendPlacedEntry + 4000#64 -> spqrSendPlacedEntry + 6216#64`), exposing the individual
    per-phase event lists `evs₁`, `evs₂`, and
    `evs₃ := rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1` for direct right-associated
    `SeqEnv` composition with Phase 4 finish. -/
theorem step_send_bridge2_317fc_ofEnv_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (st0 : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    {MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hmser' : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecXOfEnv spqrPolyApi M A lim MsgSerEnv)))
    (hinto' : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F IntoPbEnv)))
    {s0 s : State} (hinv0_lscro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (sp v_20_old v0 v_sp10 v_sp18 : BitVec 64) (idx : BitVec 32)
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hlen : pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) } < 2 ^ 63)
    (hFit : FitsEnv M lim st0 (SendBridge2EnvOfEnv MsgSerEnv IntoPbEnv sp idx vn ch st1 msg))
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P Frame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 4000#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx24 : s.readReg32 .x24 = idx) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = sp + 4192#64) (hinv0 : StepInv s0 s)
    (hP : P = (messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ memRegion (sp + 0xff0#64) 24 ∗
      chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗ memRegion (sp + 0x1260#64) 928 ∗
      memRegion (sp + 0x590#64) 224 ∗
      ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
      optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) vn ∗
      optChainPBRegSlotAt A.repAlloc (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      A.pool lim st0 s ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sm : State) (evs₁ evs₂ : List AllocEvent)
      (g : PqRatchetStatePBGhost) (w0 : BitVec 64),
      let pq' : PqRatchetState :=
        { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }
      let evs₃ : List AllocEvent := rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1
      MsgSerEnv { msgA := sp + 0x1d70#64, index := idx, ret := sp + 0xff0#64, msg := msg } evs₁ →
      IntoPbEnv { out := sp + 0x590#64, stA := sp + 0x1260#64, st := st1 } evs₂ →
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = optChainCap g.chain pq'.chain →
      (sm.readReg64 .x25 + 1#64 == 0#64) = !pq'.chain.isSome →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      StepInv s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) pq' ∗
          vecU8 A.repAlloc (sp + 1424#64) (PqRatchetState.encodeRaw pq') ∗
          vecU8 A.repAlloc (sp + 4080#64) (msg.serialize idx) ∗
          ((sp + 32#64) ↦₆₄ s.readReg64 .x20) ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain pq'.chain) ∗
          ((sp + 24#64) ↦₆₄ s.readReg64 .x22) ∗
          memRegion (sp + 0x30#64) 48 ∗ memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗
          memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1d70#64) 48 ∗
          ((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents (evs₁ ++ (evs₂ ++ evs₃)) st0) sm ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  let roV1 : SepProp := (lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes
  let roSend : SepProp := (lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes
  let roInto : SepProp := CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt
  let x_mser : MessageSerializeGhost spqrPolyApi :=
    { msgA := sp + 0x1d70#64, index := idx, ret := sp + 0xff0#64, msg := msg }
  let x_into : StatesIntoPbGhost F :=
    { out := sp + 0x590#64, stA := sp + 0x1260#64, st := st1 }
  let pq' : PqRatchetState :=
    { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }
  have hsp_align : (sp &&& 15#64 == 0#64) = true := beq_iff_eq.mpr halign
  have hinv : LibsignalCodeRoLoaded lsmpl s.mem :=
    ⟨hinv0.libsignalCodeLoaded hinv0_lscro.1, hinv0.libsignalRoLoaded hinv0_lscro.2⟩
  subst hP
  refine sepWPp_intro_rodata_bridge2_placed hinv.2 ?_
  refine sepWPp_of_sepWP_lscro_b2 hinv
    (SepWP.mono (LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesEncodePlacedBudget.step_pre_message_serialize_317fc_placed s _
      hpc hrun (by rw [hsp]; exact hsp_align)) ?_)
  intro s1 Q1 hpc1 _ ⟨hvm1, hv1, hrun1, htr1, hsp1, hx0_1, hx1_1, hx8_1, hlr1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hQ1⟩
  refine ⟨hvm1, hv1, fun hinv1 hstep1 => ?_⟩
  rw [hQ1, ← A.pool_of_vmPreserved hstep1.2]; rw [hsp] at hsp1 hx0_1 hx8_1
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  have hinv0_1 : StepInv s0 s1 := hinv0.trans hstep1.1
  have hFit1 : FitsEnv M lim st0 (MsgSerEnv x_mser) := hFit.seq_left
  refine sepWPp_call_lscro_calleeStack_evs_b2 sp messageSerializeStackX (by decide) hmser' hinv1
    hpc1 hrun1 hsp1 hsp_align hlr1
    (x := (x_mser, st0))
    (φ_pre := s1.readReg64 .x0 = sp + 0x1d70#64 ∧
      (s1.readReg64 .x1).setWidth 32 = idx ∧ s1.readReg64 .x8 = sp + 0xff0#64 ∧
      FitsEnv M lim st0 (MsgSerEnv x_mser))
    (φ_post := fun evs₁ sf => sf.trace = s1.trace ∧ MsgSerEnv x_mser evs₁)
    (T_pre := messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ memRegion (sp + 0xff0#64) 24 ∗
      A.pool lim st0 s1)
    (T_post := fun evs₁ sf => messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗
      vecU8 A.repAlloc (sp + 0xff0#64) (msg.serialize idx) ∗
      A.pool lim (M.stepEvents evs₁ st0) sf)
    (F := (roV1 ∗ roSend ∗ roInto ∗
      chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗ memRegion (sp + 0x1260#64) 928 ∗
      memRegion (sp + 0x590#64) 224 ∗ ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
      optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) vn ∗
      optChainPBRegSlotAt A.repAlloc (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18)) ∗ Frame)
    (by
      dsimp only [SeamSpecsPlacedBudget.messageSerializeSpecXOfEnv, x_mser]
      exact Entails.of_eq (by sep_ac_rfl))
    ⟨hx0_1, by change s1.readReg32 .x1 = idx; rw [hx1_1, hx24], hx8_1, hFit1⟩
    (by dsimp only [roV1, roSend, roInto]; sep_ac_rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun sf => by
      dsimp only [SeamSpecsPlacedBudget.messageSerializeSpecXOfEnv, x_mser]
      exact Entails.sepExists_elim fun evs₁ =>
        Entails.sepExists_right evs₁ (Entails.of_eq (by sep_ac_rfl))) ?_
  intro evs₁ s2 hpc2 hrun2 hsp2 ⟨htr2, hmser1⟩ hinv2 hstep2
    hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 _
  have htr2' : s2.trace = s0.trace := htr2.trans htr1'
  have hinv0_2 : StepInv s0 s2 := hinv0_1.trans hstep2
  have hFit12 := hFit.seq_right hmser1
  obtain ⟨tail, hser⟩ := message_serialize_eq_cons msg idx
  refine SepWPp.weaken_pre
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (messageAt_entails_memRegion_48 (sp + 0x1d70#64) msg)))) ?_
  rw [hser]
  refine sepWPp_of_sepWP_lscro_b2 hinv2
    (SepWP.weaken_pre (Entails.of_eq (by rw [← hsp2]; sep_ac_rfl))
      (SepWP.mono (step_post_message_serialize_to_into_pb_31810_placed hA s2 tail st1
        (roV1 ∗ roSend ∗ roInto ∗
          memRegion (sp + 0x1d70#64) 48 ∗ memRegion (sp + 0x590#64) 224 ∗
          ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
          optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) vn ∗
          optChainPBRegSlotAt A.repAlloc (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
          (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
          A.pool lim (M.stepEvents evs₁ st0) s2 ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
        hpc2 hrun2 (by rw [hx26_2, hx26_1, hx26, hsp2])
        (by rw [hsp2]; exact hsp_align)) ?_))
  intro s3 Q3 hpc3 _ ⟨hvm3, hv3, hrun3, htr3, hsp3, hx0_3, hx8_3, hlr3, hx24_3,
    hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx26_3, hx27_3, hx28_3, hQ3⟩
  refine ⟨hvm3, hv3, fun hinv3 hstep3 => ?_⟩
  refine SepWPp.weaken_pre hQ3 ?_
  rw [hsp2] at hsp3 hx0_3 hx8_3 hx24_3 ⊢
  rw [← hser, ← A.pool_of_vmPreserved hstep3.2]
  have htr3' : s3.trace = s0.trace := htr3.trans htr2'
  have hinv0_3 : StepInv s0 s3 := hinv0_2.trans hstep3.1
  have hFit2 : FitsEnv M lim (M.stepEvents evs₁ st0) (IntoPbEnv x_into) := hFit12.seq_left
  refine sepWPp_call_lscro_calleeStack_evs_b2 sp statesIntoPbStackX (by decide) hinto' hinv3
    hpc3 hrun3 hsp3 hsp_align hlr3
    (x := (x_into, M.stepEvents evs₁ st0))
    (φ_pre := s3.readReg64 .x8 = sp + 0x590#64 ∧ s3.readReg64 .x0 = sp + 0x1260#64 ∧
      FitsEnv M lim (M.stepEvents evs₁ st0) (IntoPbEnv x_into))
    (φ_post := fun evs₂ sf => sf.trace = s3.trace ∧ IntoPbEnv x_into evs₂)
    (T_pre := memRegion (sp + 0x590#64) optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc (sp + 0x1260#64) st1 ∗
      roInto ∗ A.pool lim (M.stepEvents evs₁ st0) s3)
    (T_post := fun evs₂ sf => optProtoInnerStateAt A.repAlloc (sp + 0x590#64) st1.into_pb.innerState ∗
      memRegion (sp + 0x1260#64) chunkedStatesSize ∗
      roInto ∗ A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st0)) sf)
    (F := (roV1 ∗ roSend ∗
      memRegion (sp + 0x190#64) 928 ∗ vecU8 A.repAlloc (sp + 0xff0#64) (msg.serialize idx) ∗
      memRegion (sp + 0x1d70#64) 48 ∗ ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
      optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) vn ∗
      optChainPBRegSlotAt A.repAlloc (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18)) ∗ Frame)
    (by
      dsimp only [statesIntoPbPlacedSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.statesIntoPbPlacedSpecXOfEnv,
        CryptoVerification.SpqrV1.Top.InitInner.statesIntoPbJumpTablePlacedAt,
        CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt, roInto, x_into]
      exact Entails.of_eq (by sep_ac_rfl))
    ⟨hx8_3, hx0_3, hFit2⟩
    (by dsimp only [optProtoInnerStateSize]; sep_ac_rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun sf => by
      dsimp only [statesIntoPbPlacedSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.statesIntoPbPlacedSpecXOfEnv,
        CryptoVerification.SpqrV1.Top.InitInner.statesIntoPbJumpTablePlacedAt,
        CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt, roInto, x_into]
      exact Entails.sepExists_elim fun evs₂ => Entails.sepExists_right evs₂ (Entails.of_eq (by sep_ac_rfl))) ?_
  intro evs₂ s4 hpc4 hrun4 hsp4 ⟨htr4, hinto2⟩ hinv4 hstep4
    hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 _
  have htr4' : s4.trace = s0.trace := htr4.trans htr3'
  have hinv0_4 : StepInv s0 s4 := hinv0_3.trans hstep4
  have hx25_s4 : s4.readReg64 .x25 = s.readReg64 .x25 :=
    hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_1))
  have hx26_s4 : s4.readReg64 .x26 = s4.sp + 0x1260#64 := by
    rw [hsp4, hx26_4, hx26_3, hx26_2, hx26_1, hx26]
  have hFit3 : FitsEvents M lim (M.stepEvents evs₂ (M.stepEvents evs₁ st0))
      (rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1) :=
    (hFit12.seq_right hinto2) _ rfl
  dsimp only [chunkedStatesSize]
  rw [memRegion_928_split_352_576 sp]
  refine sepWPp_of_sepWP_lscro_b2 hinv4
    (SepWP.weaken_pre (Entails.of_eq (by rw [← hsp4, ← hx25_s4]; sep_ac_rfl))
      (SepWP.mono (step_copy_and_assemble_pq_state_3185c_placed s4 v_20_old vn ch st1
        (roV1 ∗ roSend ∗ roInto ∗
          memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x190#64) 928 ∗
          vecU8 A.repAlloc (sp + 0xff0#64) (msg.serialize idx) ∗ memRegion (sp + 0x1d70#64) 48 ∗
          (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
          A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st0)) s4 ∗
          stackAt sp spqrSendCalleeStack ∗ Frame)
        hpc4 hrun4 hx26_s4 (by rw [hsp4]; exact hsp_align)) ?_))
  intro s5 Q5 hpc5 _ ⟨hvm5, hv5, hrun5, htr5, hsp5,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx27_5, hx28_5,
    g, hx25_cap, hx26_cap, hx25_some, hQ5⟩
  refine ⟨hvm5, hv5, fun hinv5 hstep5 => ?_⟩
  refine SepWPp.weaken_pre hQ5 ?_
  rw [hsp4] at hsp5 ⊢
  rw [← A.pool_of_vmPreserved hstep5.2]
  have htr5' : s5.trace = s0.trace := htr5.trans htr4'
  have hinv0_5 : StepInv s0 s5 := hinv0_4.trans hstep5.1
  have hx19_s5 : s5.readReg64 .x19 = s.readReg64 .x19 :=
    hx19_5.trans (hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_1)))
  have hx20_s4 : s4.readReg64 .x20 = s.readReg64 .x20 :=
    hx20_4.trans (hx20_3.trans (hx20_2.trans hx20_1))
  have hx21_s5 : s5.readReg64 .x21 = s.readReg64 .x21 :=
    hx21_5.trans (hx21_4.trans (hx21_3.trans (hx21_2.trans hx21_1)))
  have hx22_s5 : s5.readReg64 .x22 = s.readReg64 .x22 :=
    hx22_5.trans (hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_1)))
  have hx23_s5 : s5.readReg64 .x23 = s.readReg64 .x23 :=
    hx23_5.trans (hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_1)))
  have hx24_s5 : s5.readReg64 .x24 = sp + 4704#64 := hx24_5.trans (hx24_4.trans hx24_3)
  have hx27_s5 : s5.readReg64 .x27 = s.readReg64 .x27 :=
    hx27_5.trans (hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_1)))
  have hx28_s5 : s5.readReg64 .x28 = sp + 4192#64 :=
    hx28_5.trans (hx28_4.trans (hx28_3.trans (hx28_2.trans (hx28_1.trans hx28))))
  rw [hx20_s4]
  have h590_split : memRegion (sp + 0x590#64) 224 ⊢
      (∃∗ v_590 : BitVec 64, ∃∗ v_598 : BitVec 64, ∃∗ v_5a0 : BitVec 64,
        ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗
      memRegion (sp + 1448#64) 200 := by
    rw [memRegion_224_split_24_200 sp]
    exact sepConj_mono_left (memRegion_24_words3_1424 sp)
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left h590_split))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v_590 => SepWPp.exists_elim fun v_598 => SepWPp.exists_elim fun v_5a0 => ?_
  refine step_send_encode_from_vn_len_self_contained_placed
    (st0 := M.stepEvents evs₂ (M.stepEvents evs₁ st0)) hA hinv0_lscro.1 sp (s.readReg64 .x22)
    v0 v_sp10 v_sp18 v_590 v_598 v_5a0 g pq'
    (pqRatchetStatePBEncodedLen_some_v1_pos vn ch st1.into_pb) hlen hFit3 halign
    hpc5 hrun5 hsp5 htr5' hx22_s5 hx24_s5 hx25_cap hx26_cap hx28_s5 hinv0_5
    (F := ((sp + 0x20#64) ↦₆₄ s.readReg64 .x20) ∗ memRegion (sp + 0x30#64) 48 ∗
      memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 1448#64) 200 ∗
      roInto ∗ memRegion (sp + 5056#64) 576 ∗
      memRegion (sp + 0x190#64) 928 ∗ vecU8 A.repAlloc (sp + 0xff0#64) (msg.serialize idx) ∗
      memRegion (sp + 0x1d70#64) 48 ∗ Frame)
    (by dsimp only [roV1, roSend]; sep_ac_rfl) ?_
  intro sm ptr w0 hpcm hrunm hspm htrm hx19m hx21m hx23m hx25m hx27m hx28m _ hinv0_m
  have hinv_m : LibsignalCodeRoLoaded lsmpl sm.mem :=
    ⟨hinv0_m.libsignalCodeLoaded hinv0_lscro.1, hinv0_m.libsignalRoLoaded hinv0_lscro.2⟩
  have hx25_some_m : (sm.readReg64 .x25 + 1#64 == 0#64) = !pq'.chain.isSome := by
    rw [hx25m, ← hx25_cap]; exact hx25_some
  have hstep_evs : M.stepEvents (rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1)
      (M.stepEvents evs₂ (M.stepEvents evs₁ st0)) =
      M.stepEvents (evs₁ ++ (evs₂ ++ rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1)) st0 := by
    rw [M.stepEvents_append, M.stepEvents_append]
  rw [hstep_evs]
  refine SepWPp.weaken_pre ?_
    (hnext sm evs₁ evs₂ g w0 hmser1 hinto2 hpcm hrunm hspm htrm
      (hx19m.trans hx19_s5) (hx21m.trans hx21_s5) (hx23m.trans hx23_s5)
      hx25m hx25_some_m (hx27m.trans hx27_s5) hx28m hinv0_m hinv_m)
  have hvec := vecU8At_entails_vecU8 A.repAlloc (sp + 1424#64)
    (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen pq'))
    ptr (PqRatchetState.encodeRaw pq')
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left hvec))))) ?_
  change _ ⊢ ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) pq' ∗
    vecU8 A.repAlloc (sp + 1424#64) (PqRatchetState.encodeRaw pq') ∗
    vecU8 A.repAlloc (sp + 0xff0#64) (msg.serialize idx) ∗
    ((sp + 0x20#64) ↦₆₄ s.readReg64 .x20) ∗ (sp ↦₆₄ w0) ∗
    ((sp + 16#64) ↦₆₄ optChainCap g.chain pq'.chain) ∗
    ((sp + 24#64) ↦₆₄ s.readReg64 .x22) ∗
    memRegion (sp + 0x30#64) 48 ∗ memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗
    memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1d70#64) 48 ∗
    ((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
    ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
    CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
    A.pool lim (M.stepEvents (evs₁ ++ (evs₂ ++ rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1)) st0) sm ∗
    stackAt sp spqrSendCalleeStack) ∗ Frame)
  dsimp only [roInto]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Single-`evs` envelope-parametric Phase 3d–3e bridge
    (`spqrSendPlacedEntry + 4000#64 -> spqrSendPlacedEntry + 6216#64`), packaging the combined
    allocation event list under `SendBridge2EnvOfEnv`. -/
theorem step_send_bridge2_317fc_single_ofEnv_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (st0 : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    {MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hmser' : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecXOfEnv spqrPolyApi M A lim MsgSerEnv)))
    (hinto' : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F IntoPbEnv)))
    {s0 s : State} (hinv0_lscro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (sp v_20_old v0 v_sp10 v_sp18 : BitVec 64) (idx : BitVec 32)
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hlen : pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) } < 2 ^ 63)
    (hFit : FitsEnv M lim st0 (SendBridge2EnvOfEnv MsgSerEnv IntoPbEnv sp idx vn ch st1 msg))
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P Frame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 4000#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx24 : s.readReg32 .x24 = idx) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = sp + 4192#64) (hinv0 : StepInv s0 s)
    (hP : P = (messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ memRegion (sp + 0xff0#64) 24 ∗
      chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗ memRegion (sp + 0x1260#64) 928 ∗
      memRegion (sp + 0x590#64) 224 ∗
      ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
      optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) vn ∗
      optChainPBRegSlotAt A.repAlloc (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      A.pool lim st0 s ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sm : State) (evs : List AllocEvent)
      (g : PqRatchetStatePBGhost) (w0 : BitVec 64),
      let pq' : PqRatchetState :=
        { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }
      SendBridge2EnvOfEnv MsgSerEnv IntoPbEnv sp idx vn ch st1 msg evs →
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = optChainCap g.chain pq'.chain →
      (sm.readReg64 .x25 + 1#64 == 0#64) = !pq'.chain.isSome →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      StepInv s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) pq' ∗
          vecU8 A.repAlloc (sp + 1424#64) (PqRatchetState.encodeRaw pq') ∗
          vecU8 A.repAlloc (sp + 4080#64) (msg.serialize idx) ∗
          ((sp + 32#64) ↦₆₄ s.readReg64 .x20) ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain pq'.chain) ∗
          ((sp + 24#64) ↦₆₄ s.readReg64 .x22) ∗
          memRegion (sp + 0x30#64) 48 ∗ memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗
          memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1d70#64) 48 ∗
          ((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st0) sm ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom :=
  step_send_bridge2_317fc_ofEnv_placed st0 hA hmser' hinto' hinv0_lscro
    sp v_20_old v0 v_sp10 v_sp18 idx vn ch st1 msg hlen hFit halign
    hpc hrun hsp htr hx24 hx26 hx28 hinv0 hP
    fun sm evs₁ evs₂ g w0 hmser1 hinto2 =>
      hnext sm
        (evs₁ ++ (evs₂ ++ rustAllocEvents
          (pqRatchetStatePBEncodedLen { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }) 1))
        g w0 (sendBridge2EnvOfEnv_intro hmser1 hinto2)

/-- Default full Phase 3d–3e bridge
    (`spqrSendPlacedEntry + 4000#64 -> spqrSendPlacedEntry + 6216#64`) against
    `messageSerializeSpecX`, `statesIntoPbPlacedSpecX`, and `SendBridge2Env`. -/
theorem step_send_bridge2_317fc_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (st0 : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hmser' : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi M A lim)))
    (hinto' : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX M A lim F)))
    {s0 s : State} (hinv0_lscro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (sp v_20_old v0 v_sp10 v_sp18 : BitVec 64) (idx : BitVec 32)
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hlen : pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) } < 2 ^ 63)
    (hFit : FitsEnv M lim st0 (SendBridge2Env idx vn ch st1 msg))
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P Frame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 4000#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx24 : s.readReg32 .x24 = idx) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = sp + 4192#64) (hinv0 : StepInv s0 s)
    (hP : P = (messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ memRegion (sp + 0xff0#64) 24 ∗
      chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗ memRegion (sp + 0x1260#64) 928 ∗
      memRegion (sp + 0x590#64) 224 ∗
      ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
      optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) vn ∗
      optChainPBRegSlotAt A.repAlloc (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      A.pool lim st0 s ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sm : State) (evs : List AllocEvent)
      (g : PqRatchetStatePBGhost) (w0 : BitVec 64),
      let pq' : PqRatchetState :=
        { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }
      SendBridge2Env idx vn ch st1 msg evs →
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = optChainCap g.chain pq'.chain →
      (sm.readReg64 .x25 + 1#64 == 0#64) = !pq'.chain.isSome →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      StepInv s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) pq' ∗
          vecU8 A.repAlloc (sp + 1424#64) (PqRatchetState.encodeRaw pq') ∗
          vecU8 A.repAlloc (sp + 4080#64) (msg.serialize idx) ∗
          ((sp + 32#64) ↦₆₄ s.readReg64 .x20) ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain pq'.chain) ∗
          ((sp + 24#64) ↦₆₄ s.readReg64 .x22) ∗
          memRegion (sp + 0x30#64) 48 ∗ memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗
          memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1d70#64) 48 ∗
          ((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st0) sm ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom :=
  step_send_bridge2_317fc_single_ofEnv_placed st0 hA hmser' hinto' hinv0_lscro
    sp v_20_old v0 v_sp10 v_sp18 idx vn ch st1 msg hlen hFit halign
    hpc hrun hsp htr hx24 hx26 hx28 hinv0 hP hnext

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge2PlacedBudget