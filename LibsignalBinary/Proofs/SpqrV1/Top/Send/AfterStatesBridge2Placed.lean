/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.EncodedLenCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainStep
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncodePlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerDispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializePlaced -- shake: keep

/-!
# Relocatable `spqr::send`: `Message::serialize` through `PqRatchetState` Encoding (`+4000 -> +6216`)

Relocatable composition of `<Message>::serialize`, `States` relocation, `<States>::into_pb`,
`PqRatchetState` stack assembly, and inlined `PqRatchetState` encoding (`+4000 -> +6216`) in
`spqr::send::<HookRng>` (Block `124`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top.Send.Placed

variable [LibsignalPlacement]

/-! ## 1. Relocation and Decomposition Helpers for `+4000..+4364` -/

/-- Framed `memcpy` call rule for an explicit byte slice `src ↦ₛ bs`. -/
private theorem call_memcpy_bytes_bridge2 {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    (dst src : BitVec 64) {bs : List (BitVec 8)} {n : Nat} (hlen : bs.length = n)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (src ↦ₛ bs)) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      VRegsAt s sf →
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
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [sessionMemcpyRegionSpec]; rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (htr.trans htrace)
      ⟨hcs_sf.2.2.2.2.2.2.2.2.2.2.2⟩
      hcs_sf.1 hcs_sf.2.1 hcs_sf.2.2.1 hcs_sf.2.2.2.1 hcs_sf.2.2.2.2.1
      hcs_sf.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.1
      hcs_sf.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.1

/-- Framed `memcpy` call rule for any `States.Leaves.Relocatable n F` predicate family. -/
private theorem call_memcpy_relocate_bridge2 {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    (dst src : BitVec 64) {n : Nat} {F : BitVec 64 → SepProp}
    (hrel : States.Leaves.Relocatable n F)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      VRegsAt s sf →
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
    (Frame := States.Leaves.relocatedHeap F bs ∗ Frame) (by ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hv_sf hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28
  have hrecomp := States.Leaves.relocatedHeap_recompose F bs dst
  have hsrc : (src ↦ₛ bs) ⊢ memRegion src n := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion src bs
  refine SepWP.weaken_pre ?_
    (hnext sf hpc_sf hrun_sf hsp_sf htr_sf hv_sf hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28)
  refine Entails.trans (Entails.of_eq (show
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (States.Leaves.relocatedHeap F bs ∗ Frame) =
    (((dst ↦ₛ bs) ∗ States.Leaves.relocatedHeap F bs) ∗ (src ↦ₛ bs)) ∗ Frame by ac_rfl)) ?_
  exact sepConj_mono_left (sepConj_mono hrecomp hsrc)

/-! ## 2. `PqRatchetState` Copy & Assembly (`+4096 -> +4288 / +4364`) -/

/-- Combines `spqrSendPlacedEntry + 4096#64 -> spqrSendPlacedEntry + (if vn.isSome then 4288#64
    else 4364#64)` (`step_copy_pq_state_some_3185c_placed` /
    `step_copy_pq_state_none_3185c_placed`) with unpacking and reassembling
    `pqRatchetStatePBPinnedAt A g (s.sp + 4704#64)`. -/
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
        ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
        optChainPBRegSlotAt A (s.sp + 0xd90#64) (s.readReg64 .x25) ch ∗
        Drop.optProtoInnerStateAt A (s.sp + 0x590#64) st1.into_pb.innerState ∗
        memRegion (s.sp + 0x1260#64) 352 ∗ Frame)
      (fun sf Q => VRegsAt s sf ∧
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
        ∃ g : Prost.EncodeToVec.PqRatchetStatePBGhost,
          sf.readReg64 .x25 = Prost.EncodeToVec.optChainCap g.chain pq'.chain ∧
          sf.readReg64 .x26 = Prost.EncodeToVec.optVersionNegCap g.vn pq'.versionNegotiation ∧
          (sf.readReg64 .x25 + 1#64 == 0#64) = !pq'.chain.isSome ∧
          (Q ⊢ ((s.sp + 0x20#64) ↦₆₄ s.readReg64 .x20) ∗
            Prost.EncodeToVec.pqRatchetStatePBPinnedAt A g (s.sp + 4704#64) pq' ∗
            memRegion (s.sp + 0x30#64) 48 ∗
            memRegion (s.sp + 0xd90#64) 72 ∗
            memRegion (s.sp + 0x590#64) 224 ∗ Frame)) := by
  intro pq'
  obtain ⟨is, his⟩ := states_into_pb_innerState_isSome st1
  rw [his, Prost.EncodeToVec.optVersionNegotiationPBAt_eq_exists_pinned A (s.sp + 0x30#64) vn]
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
    have hvn_none : vnWords6At (s.sp + 0x30#64) (Prost.EncodeToVec.optVersionNegCap g_vn none) w1 w2 w3 w4 w5 =
        vnWords6At (s.sp + 0x30#64) noneCap w1 w2 w3 w4 w5 := rfl
    have hvn_none' : vnWords6At (s.sp + 4704#64) noneCap w1 w2 w3 w4 w5 =
        vnWords6At (s.sp + 4704#64) (Prost.EncodeToVec.optVersionNegCap g_vn none) w1 w2 w3 w4 w5 := rfl
    rw [hvn_none]
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.seq (step_copy_pq_state_none_3185c_placed s v_20 w1 w2 w3 w4 w5
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
    rintro ⟨hvf, hrunf, htrf, hspf, hx26f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx27f, hx28f, hQf⟩
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
    refine Prost.EncodeToVec.SepWP.done hpcf hrunf
      ⟨hrunf, htrf, hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx27f, hx28f,
        ⟨g_vn, g_ch.toProtoRepr, g_v1⟩, hx25f.trans hx25_cap, hx26f, by rw [hx25f]; exact hx25_some, ?_⟩
    unfold Prost.EncodeToVec.pqRatchetStatePBPinnedAt
    dsimp only [pq']
    exact Entails.of_eq (by ac_rfl)
  | some v =>
    simp only [Option.isSome_some, ↓reduceIte]
    refine SepWP.focus_weaken
      (optVersionNegWordsHeap_some_cap_ne A g_vn v w1 w2 w3 w4 w5) (by sep_focus) ?_
    wp_focus_pure; intro hw0_ne
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.seq (step_copy_pq_state_some_3185c_placed s v_20
        (Prost.EncodeToVec.optVersionNegCap g_vn (some v)) w1 w2 w3 w4 w5
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
    rintro ⟨hvf, hrunf, htrf, hspf, hx26f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx27f, hx28f, hQf⟩
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
    refine Prost.EncodeToVec.SepWP.done hpcf hrunf
      ⟨hrunf, htrf, hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx27f, hx28f,
        ⟨g_vn, g_ch.toProtoRepr, g_v1⟩, hx25f.trans hx25_cap, hx26f, by rw [hx25f]; exact hx25_some, ?_⟩
    unfold Prost.EncodeToVec.pqRatchetStatePBPinnedAt
    dsimp only [pq']
    exact Entails.of_eq (by ac_rfl)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## 3. Bridge 2 Composition (`+4000 -> +6216`) -/

/-- `SepWPp` step combinator preserving `LibsignalCodeRoLoaded lsmpl` and `StepInv`. -/
theorem sepWPp_of_sepWP_lscro_b2 {prog : Program} {ret mid : BitVec 64}
    {s : State} (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ProofLib.SepWP prog mid s P (fun sm Pm =>
      VRegsAt s sm ∧ (LibsignalCodeRoLoaded lsmpl sm.mem → StepInv s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hv, hnext⟩ | hoom⟩ := h.elim hm hL
  · have hinv' : LibsignalCodeRoLoaded lsmpl sm.mem := hinv.of_keepsFrozen hsteps.keepsFrozen
    have hstep : StepInv s sm := ⟨fun _ hF => hsteps.frozenLoaded hF, hsteps.symtab_eq, hv.eq⟩
    obtain ⟨sf, hsteps', hout⟩ := hnext hinv' hstep R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

/-- `SepWPp` call rule for a `withLsCodeRoLoaded lsmpl` callee whose stack fits in
    `spqrSendCalleeStack`. -/
theorem sepWPp_call_lscro_calleeStack_b2 {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α}
    {s0 s : State} (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : State → SepProp}
    {Q : State → SepProp → Prop} {Fr F : SepProp}
    {φ_pre : Prop} {φ_post : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n))
    (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (hspec_post : ∀ sf, spec.post x s sf = (⌜φ_post sf⌝ ∗ T_post sf ∗ stackAt s.sp n))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post sf → LibsignalCodeRoLoaded lsmpl sf.mem → StepInv s sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post sf) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ Fr)) := by
  let F_ext := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  have h_step : SepWPp prog ret_pc s P
      (fun sm Pm => Pm = ((withLsCodeRoLoaded lsmpl spec).post x s sm ∗ F_ext) ∧
        sm.sp = s.sp ∧ CalleeSavedPreserved s sm)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ Fr)) :=
    ProofLib.SepWPp.call_wpp (x := x) (F := F_ext) hcall hpc hrun hsp_al hlr
      (fun R' hm => by
        change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ (F_ext ∗ R')
        rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hinv, ?_⟩
        rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
        rw [hP, stackAt_spqrSendCallee_split_b2 sp n hle] at hm
        exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; ac_rfl)) hm)
      (fun sm code R' _ hpost => by
        change sm.mem ⊨ spec.onExit x code s sm ∗ R' at hpost; rw [hexit_eq code sm] at hpost
        exact Prost.EncodeToVec.allowPanic_not_exited hpost)
      (fun sm _ _ hmFr => by
        change sm.mem ⊨ (spec.onPanic x s sm ∗ F_ext) ∗ Fr at hmFr; rw [hpan_eq sm] at hmFr
        have h1 : (((⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F_ext) ∗ Fr) ⊢
            ⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ ((anyHeap ∗ F_ext) ∗ Fr) :=
          Entails.of_eq (by ac_rfl)
        have hm' := Satisfies.mono h1 hmFr
        rw [satisfies_pure_sepConj] at hm'
        rcases hm' with ⟨⟨hal, htr_sub⟩, hm_rest⟩
        have hal0 : allocFailedIn s0 sm := by unfold allocFailedIn at hal ⊢; rwa [← htr]
        have htr0 : s0.trace <+: sm.trace := by rwa [← htr]
        exact Satisfies.mono
          (sepConj_mono_left (Entails.pure_right ⟨hal0, htr0⟩ (entails_anyHeap _))) hm_rest)
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨rfl, hspm, hcsm⟩)
      (fun sm R' _ hpost => by
        change sm.mem ⊨ spec.onOom x s sm ∗ (F_ext ∗ R') at hpost; rw [hoom_eq sm] at hpost
        exact (Prost.EncodeToVec.allowPanic_not_exited hpost).elim)
  intro R' hm hL
  rcases h_step R' hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, rfl, hspm, hcsm⟩ | hpan | hoom⟩
  · change sm.mem ⊨ (spec.post x s sm ∗ F_ext) ∗ R' at hpost
    rw [sepConj_assoc, hspec_post sm, hsp] at hpost
    have hpost' : sm.mem ⊨ ⌜φ_post sm⌝ ∗ (((stackAt sp spqrSendCalleeStack ∗ T_post sm) ∗ F) ∗ R') := by
      rw [stackAt_spqrSendCallee_split_b2 sp n hle]
      exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨hφ_post, hpost_mem⟩
    rw [hsp] at hspm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
    have hinv' : LibsignalCodeRoLoaded lsmpl sm.mem := hinv.of_keepsFrozen hsteps.keepsFrozen
    have hstep : StepInv s sm := ⟨fun _ hF => hsteps.frozenLoaded hF, hsteps.symtab_eq, hvregs⟩
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hspm hφ_post hinv' hstep
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs R' hpost_mem (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem lsro_spqrSendEncodeJumpTableBytes_intro {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ P := by
  have h := lsro_spqrSendJumpTablesPlacedAt hro hP
  have h1 : s.mem ⊨ spqrSendStatesJumpTablePlacedAt ∗ (spqrSendDropJumpTablePlacedAt ∗
      (((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗ P)) := by
    change s.mem ⊨ spqrSendStatesJumpTablePlacedAt ∗ spqrSendEncodeJumpTablePlacedAt ∗
      spqrSendDropJumpTablePlacedAt ∗ P at h
    unfold spqrSendEncodeJumpTablePlacedAt at h
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h
  exact Satisfies.of_sep_right (Satisfies.of_sep_right h1)

/-- Introduce the three `.rodata` jump tables (`v1StateJumpTableBytes`,
    `spqrSendEncodeJumpTableBytes`, `statesIntoPbJumpTablePlacedAt`) into the `SepWPp`
    precondition from `LibsignalRoLoaded lsmpl s.mem`. -/
theorem sepWPp_intro_rodata_bridge2_placed
    {prog : Program} {ret : BitVec 64} {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s
      (((lsρ v1StateJtSymLocal1) ↦ᵣ ProtoRepr.v1StateJumpTableBytes) ∗
       ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
       statesIntoPbJumpTablePlacedAt ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm3 := v1StateJumpTableBytes_lsro_local1_intro hro
    (lsro_spqrSendEncodeJumpTableBytes_intro hro (lsro_statesIntoPbJumpTablePlacedAt hro hm))
  exact h R (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm3) hL

/-- `spqrSendPlacedEntry + 4020#64 -> lsmpl.base 334`: checks `msg.serialize idx = 1#8 :: tail`,
    relocates `chunkedStatesAt` via `memcpy`, and sets up `<States>::into_pb` (`lsmpl.base 334`,
    return `spqrSendPlacedEntry + 4096#64`). -/
theorem step_post_message_serialize_to_into_pb_31810_placed {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) (s : State) (tail : List (BitVec 8))
    (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 4020#64)
    (hrun : s.status = .Running) (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (spqrSendPlacedProg ext)
      (lsmpl.base 334) s
      (vecU8 A (s.sp + 0xff0#64) (1#8 :: tail) ∗ memRegion (s.sp + 0x1260#64) 928 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ Frame)
      (fun sf Q => VRegsAt s sf ∧
        sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x1260#64 ∧ sf.readReg64 .x8 = s.sp + 0x590#64 ∧
        sf.readReg64 .x30 = spqrSendPlacedEntry + 4096#64 ∧
        sf.readReg64 .x24 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Q ⊢ chunkedStatesAt A (s.sp + 0x1260#64) st1 ∗ memRegion (s.sp + 0x190#64) 928 ∗
          vecU8 A (s.sp + 0xff0#64) (1#8 :: tail) ∗ Frame)) := by
  have hmcpy := spqrSend_etvMemcpy_ok_placed hA
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWP.seq (step_post_message_serialize_to_memcpy_31810_placed s tail
      (chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ Frame) hpc hrun hx26 hsp_align) ?_)
  intro s1 Q1 hpc1 _ ⟨hv1, hrun1, htr1, hsp1, hx0_1, hx1_1, hx2_1, hlr1, hx24_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hQ1⟩
  refine SepWP.weaken_pre hQ1 ?_
  refine call_memcpy_relocate_bridge2 hmcpy (s.sp + 0x1260#64) (s.sp + 0x190#64)
    (Relocatable.of_chunkedStatesAt A st1) hpc1 hrun1 hsp1 hsp_align hlr1 htr1 hx0_1 hx1_1
    (by rw [hx2_1]; rfl) (Frame := vecU8 A (s.sp + 0xff0#64) (1#8 :: tail) ∗ Frame) (by ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hv2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2]
  refine SepWP.mono (step_post_memcpy_to_into_pb_3184c_placed s2 _ hpc2 hrun2 hsp2_align) ?_
  intro sf Qf _ _ ⟨hvf, hrunf, htrf, hspf, hx0f, hx8f, hlrf,
    hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hQf⟩
  rw [hsp2] at hspf hx0f hx8f; rw [hQf]
  exact ⟨⟨hvf.eq.trans (hv2.eq.trans hv1.eq)⟩, hrunf, htrf.trans htr2, hspf, hx0f, hx8f, hlrf,
    hx24f.trans (hx24_2.trans hx24_1), hx19f.trans (hx19_2.trans hx19_1),
    hx20f.trans (hx20_2.trans hx20_1), hx21f.trans (hx21_2.trans hx21_1),
    hx22f.trans (hx22_2.trans hx22_1), hx23f.trans (hx23_2.trans hx23_1),
    hx25f.trans (hx25_2.trans hx25_1), hx26f.trans (hx26_2.trans hx26_1),
    hx27f.trans (hx27_2.trans hx27_1), hx28f.trans (hx28_2.trans hx28_1), Entails.of_eq (by ac_rfl)⟩

/-- Full Phase 3d–3e bridge (`spqrSendPlacedEntry + 4000#64 -> spqrSendPlacedEntry + 6216#64`). -/
theorem step_send_bridge2_317fc_placed
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext)
    (hmser' : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi A)))
    (hinto' : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX A F)))
    {s0 s : State} (hinv0_lscro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (sp v_20_old v0 v_sp10 v_sp18 : BitVec 64) (idx : BitVec 32)
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hlen : Prost.EncodeToVec.pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) } < 2 ^ 63)
    (halign : sp &&& 15#64 = 0#64) {Fr : SepProp} {ret : BitVec 64} {P Frame : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 4000#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx24 : s.readReg32 .x24 = idx) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = sp + 4192#64) (hinv0 : StepInv s0 s)
    (hP : P = (messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ memRegion (sp + 0xff0#64) 24 ∗
      chunkedStatesAt A (sp + 0x190#64) st1 ∗ memRegion (sp + 0x1260#64) 928 ∗ memRegion (sp + 0x590#64) 224 ∗
      ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
      CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) vn ∗
      optChainPBRegSlotAt A (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sm : State) (g : PqRatchetStatePBGhost) (w0 : BitVec 64),
      let pq' : PqRatchetState := { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }
      sm.pc = spqrSendPlacedEntry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = Prost.EncodeToVec.optChainCap g.chain pq'.chain →
      (sm.readReg64 .x25 + 1#64 == 0#64) = !pq'.chain.isSome →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      StepInv s0 sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((Prost.EncodeToVec.pqRatchetStatePBPinnedAt A g (sp + 4704#64) pq' ∗
          vecU8 A (sp + 1424#64) (PqRatchetState.encodeRaw pq') ∗
          vecU8 A (sp + 4080#64) (msg.serialize idx) ∗
          ((sp + 32#64) ↦₆₄ s.readReg64 .x20) ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ Prost.EncodeToVec.optChainCap g.chain pq'.chain) ∗
          ((sp + 24#64) ↦₆₄ s.readReg64 .x22) ∗
          memRegion (sp + 0x30#64) 48 ∗ memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗
          memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1d70#64) 48 ∗
          ((lsρ v1StateJtSymLocal1) ↦ᵣ ProtoRepr.v1StateJumpTableBytes) ∗
          ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ Fr))) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ Fr)) := by
  let roV1 : SepProp := (lsρ v1StateJtSymLocal1) ↦ᵣ ProtoRepr.v1StateJumpTableBytes
  let roSend : SepProp := (lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes
  have hsp_align : (sp &&& 15#64 == 0#64) = true := beq_iff_eq.mpr halign
  have hinv : LibsignalCodeRoLoaded lsmpl s.mem :=
    ⟨hinv0.libsignalCodeLoaded hinv0_lscro.1, hinv0.libsignalRoLoaded hinv0_lscro.2⟩
  subst hP
  refine sepWPp_intro_rodata_bridge2_placed hinv.2 ?_
  refine sepWPp_of_sepWP_lscro_b2 hinv
    (SepWP.mono (step_pre_message_serialize_317fc_placed s _
      hpc hrun (by rw [hsp]; exact hsp_align)) ?_)
  intro s1 Q1 hpc1 _ ⟨hv1, hrun1, htr1, hsp1, hx0_1, hx1_1, hx8_1, hlr1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hQ1⟩
  refine ⟨hv1, fun hinv1 hstep1 => ?_⟩
  rw [hQ1]; rw [hsp] at hsp1 hx0_1 hx8_1
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  have hinv0_1 : StepInv s0 s1 := hinv0.trans hstep1
  refine sepWPp_call_lscro_calleeStack_b2 sp messageSerializeStackX (by decide) hmser' hinv1
    hpc1 hrun1 hsp1 hsp_align htr1' hlr1
    (x := ({ msgA := sp + 0x1d70#64, index := idx, ret := sp + 0xff0#64, msg := msg } : MessageSerializeGhost spqrPolyApi))
    (φ_pre := s1.readReg64 .x0 = sp + 0x1d70#64 ∧
      (s1.readReg64 .x1).setWidth 32 = idx ∧ s1.readReg64 .x8 = sp + 0xff0#64)
    (φ_post := fun sf => sf.trace = s1.trace)
    (T_pre := messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ memRegion (sp + 0xff0#64) 24 ∗ A.pool)
    (T_post := fun _ => messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗
      vecU8 A (sp + 0xff0#64) (msg.serialize idx) ∗ A.pool)
    (F := (roV1 ∗ roSend ∗ statesIntoPbJumpTablePlacedAt ∗
      chunkedStatesAt A (sp + 0x190#64) st1 ∗ memRegion (sp + 0x1260#64) 928 ∗ memRegion (sp + 0x590#64) 224 ∗
      ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
      CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) vn ∗
      optChainPBRegSlotAt A (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18)) ∗ Frame)
    (by dsimp only [messageSerializeSpecX]; ac_rfl)
    ⟨hx0_1, by change s1.readReg32 .x1 = idx; rw [hx1_1, hx24], hx8_1⟩
    (by dsimp only [roV1, roSend]; ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => by dsimp only [messageSerializeSpecX]; ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hinv2 hstep2
    hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 _
  have htr2' : s2.trace = s0.trace := htr2.trans htr1'
  have hinv0_2 : StepInv s0 s2 := hinv0_1.trans hstep2
  obtain ⟨tail, hser⟩ := message_serialize_eq_cons msg idx
  refine SepWPp.weaken_pre
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (messageAt_entails_memRegion_48 (sp + 0x1d70#64) msg)))) ?_
  rw [hser]
  refine sepWPp_of_sepWP_lscro_b2 hinv2
    (SepWP.weaken_pre (Entails.of_eq (by rw [← hsp2]; ac_rfl))
      (SepWP.mono (step_post_message_serialize_to_into_pb_31810_placed hA s2 tail st1
        (roV1 ∗ roSend ∗ statesIntoPbJumpTablePlacedAt ∗
          memRegion (sp + 0x1d70#64) 48 ∗ memRegion (sp + 0x590#64) 224 ∗ ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
          CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) vn ∗
          optChainPBRegSlotAt A (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
          (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
        hpc2 hrun2 (by rw [hx26_2, hx26_1, hx26, hsp2])
        (by rw [hsp2]; exact hsp_align)) ?_))
  intro s3 Q3 hpc3 _ ⟨hv3, hrun3, htr3, hsp3, hx0_3, hx8_3, hlr3, hx24_3,
    hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx26_3, hx27_3, hx28_3, hQ3⟩
  refine ⟨hv3, fun hinv3 hstep3 => ?_⟩
  refine SepWPp.weaken_pre hQ3 ?_
  rw [hsp2] at hsp3 hx0_3 hx8_3 hx24_3 ⊢; rw [← hser]
  have htr3' : s3.trace = s0.trace := htr3.trans htr2'
  have hinv0_3 : StepInv s0 s3 := hinv0_2.trans hstep3
  refine sepWPp_call_lscro_calleeStack_b2 sp statesIntoPbStackX (by decide) hinto' hinv3
    hpc3 hrun3 hsp3 hsp_align htr3' hlr3
    (x := ({ out := sp + 0x590#64, stA := sp + 0x1260#64, st := st1 } : StatesIntoPbGhost F))
    (φ_pre := s3.readReg64 .x8 = sp + 0x590#64 ∧ s3.readReg64 .x0 = sp + 0x1260#64)
    (φ_post := fun sf => sf.trace = s3.trace)
    (T_pre := memRegion (sp + 0x590#64) optProtoInnerStateSize ∗
      chunkedStatesAt A (sp + 0x1260#64) st1 ∗ A.pool)
    (T_post := fun _ => Drop.optProtoInnerStateAt A (sp + 0x590#64) st1.into_pb.innerState ∗
      memRegion (sp + 0x1260#64) chunkedStatesSize ∗ A.pool)
    (F := (roV1 ∗ roSend ∗ statesIntoPbJumpTablePlacedAt ∗
      memRegion (sp + 0x190#64) 928 ∗ vecU8 A (sp + 0xff0#64) (msg.serialize idx) ∗
      memRegion (sp + 0x1d70#64) 48 ∗ ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
      CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) vn ∗
      optChainPBRegSlotAt A (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18)) ∗ Frame)
    (by dsimp only [statesIntoPbPlacedSpecX, optProtoInnerStateSize]; ac_rfl)
    ⟨hx8_3, hx0_3⟩ (by dsimp only [optProtoInnerStateSize]; ac_rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => by dsimp only [statesIntoPbPlacedSpecX, chunkedStatesSize]; ac_rfl) ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hinv4 hstep4
    hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 _
  have htr4' : s4.trace = s0.trace := htr4.trans htr3'
  have hinv0_4 : StepInv s0 s4 := hinv0_3.trans hstep4
  have hx25_s4 : s4.readReg64 .x25 = s.readReg64 .x25 :=
    hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_1))
  have hx26_s4 : s4.readReg64 .x26 = s4.sp + 0x1260#64 := by
    rw [hsp4, hx26_4, hx26_3, hx26_2, hx26_1, hx26]
  refine SepWPp.weaken_pre
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (by dsimp only [chunkedStatesSize]; exact Entails.of_eq (memRegion_928_split_352_576 sp)))))) ?_
  refine sepWPp_of_sepWP_lscro_b2 hinv4
    (SepWP.weaken_pre (Entails.of_eq (by rw [← hsp4, ← hx25_s4]; ac_rfl))
      (SepWP.mono (step_copy_and_assemble_pq_state_3185c_placed s4 v_20_old vn ch st1
        (roV1 ∗ roSend ∗ statesIntoPbJumpTablePlacedAt ∗
          memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x190#64) 928 ∗
          vecU8 A (sp + 0xff0#64) (msg.serialize idx) ∗ memRegion (sp + 0x1d70#64) 48 ∗
          (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
        hpc4 hrun4 hx26_s4 (by rw [hsp4]; exact hsp_align)) ?_))
  intro s5 Q5 hpc5 _ ⟨hv5, hrun5, htr5, hsp5,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx27_5, hx28_5,
    g, hx25_cap, hx26_cap, hx25_some, hQ5⟩
  refine ⟨hv5, fun hinv5 hstep5 => ?_⟩
  refine SepWPp.weaken_pre hQ5 ?_; rw [hsp4] at hsp5 ⊢
  have htr5' : s5.trace = s0.trace := htr5.trans htr4'
  have hinv0_5 : StepInv s0 s5 := hinv0_4.trans hstep5
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
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h590_split))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v_590 => SepWPp.exists_elim fun v_598 => SepWPp.exists_elim fun v_5a0 => ?_
  refine step_send_encode_from_vn_len_self_contained_placed hA hinv0_lscro.1 sp (s.readReg64 .x22)
    v0 v_sp10 v_sp18 v_590 v_598 v_5a0 g
    { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }
    (pqRatchetStatePBEncodedLen_some_v1_pos vn ch st1.into_pb) hlen halign
    hpc5 hrun5 hsp5 htr5' hx22_s5 hx24_s5 hx25_cap hx26_cap hx28_s5 hinv0_5
    (F := ((sp + 0x20#64) ↦₆₄ s.readReg64 .x20) ∗ memRegion (sp + 0x30#64) 48 ∗
      memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 1448#64) 200 ∗
      statesIntoPbJumpTablePlacedAt ∗ memRegion (sp + 5056#64) 576 ∗
      memRegion (sp + 0x190#64) 928 ∗ vecU8 A (sp + 0xff0#64) (msg.serialize idx) ∗
      memRegion (sp + 0x1d70#64) 48 ∗ Frame)
    (by dsimp only [roV1, roSend]; ac_rfl) ?_
  intro sm ptr w0 hpcm hrunm hspm htrm hx19m hx21m hx23m hx25m hx27m hx28m hfpm hinv0_m
  have hinv_m : LibsignalCodeRoLoaded lsmpl sm.mem :=
    ⟨hinv0_m.libsignalCodeLoaded hinv0_lscro.1, hinv0_m.libsignalRoLoaded hinv0_lscro.2⟩
  have hx25_some_m : (sm.readReg64 .x25 + 1#64 == 0#64) =
      !({ versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) } : PqRatchetState).chain.isSome := by
    rw [hx25m, ← hx25_cap]; exact hx25_some
  refine SepWPp.weaken_pre ?_
    (hnext sm g w0 hpcm hrunm hspm htrm
      (hx19m.trans hx19_s5) (hx21m.trans hx21_s5) (hx23m.trans hx23_s5)
      hx25m hx25_some_m (hx27m.trans hx27_s5) hx28m hinv0_m hinv_m)
  have hvec := vecU8At_entails_vecU8 A (sp + 1424#64)
    (BitVec.ofNat 64 (Prost.EncodeToVec.pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }))
    ptr (PqRatchetState.encodeRaw { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) })
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hvec))))) ?_
  change _ ⊢ ((Prost.EncodeToVec.pqRatchetStatePBPinnedAt A g (sp + 4704#64)
      { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) } ∗
    vecU8 A (sp + 1424#64) (PqRatchetState.encodeRaw
      { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }) ∗
    vecU8 A (sp + 0xff0#64) (msg.serialize idx) ∗
    ((sp + 0x20#64) ↦₆₄ s.readReg64 .x20) ∗ (sp ↦₆₄ w0) ∗
    ((sp + 16#64) ↦₆₄ Prost.EncodeToVec.optChainCap g.chain ch) ∗ ((sp + 24#64) ↦₆₄ s.readReg64 .x22) ∗
    memRegion (sp + 0x30#64) 48 ∗ memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗
    memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1d70#64) 48 ∗
    ((lsρ v1StateJtSymLocal1) ↦ᵣ ProtoRepr.v1StateJumpTableBytes) ∗
    ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
    statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
  exact Entails.of_eq (by dsimp only [roV1, roSend]; ac_rfl)

end CryptoVerification.SpqrV1.Top.Send
