/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightDefs
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProofClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
import LibsignalBinary.Proofs.SpqrV1.Drop.DropCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightTags1To4PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightTags5To8PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightTags9To11PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateCodeSym
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym

/-!
# Guarded-Tight `[LibsignalPlacement]` Verification for `V1State::merge` (Block `298`)

Assembles the `RustCliAllocBudget`-threaded guarded-tight contract for `V1State::merge` across
`pb.innerState = none` and all 11 `Chunked.*` tag arms (`Blocks 300..310`).

On canonical `tlb_lenPrefixed (V1State.encodeRaw pb) rest` input merged into `x.msg` with
`x.msg.innerState = none`, Block `298` adds zero non-free allocator operations or bytes beyond the
single `ChunkedK::merge` call (`dropOptProtoInnerState` on `none` emits `FreeOnlyEvs`). Under
`ValidV1PtsAt 640 pb` (≤ 16 slices per polynomial coder), the peak arm `ct1Sampled` (tag 8) uses
at most `80` non-free ops (`cumSmall ≤ 783,120` B, `maxReq ≤ 2,560` B), `headerSent` (tag 3) uses
at most `76` ops, and the remaining 9 arms use at most `45` ops.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement libsignalSessionLib ls_blockPlacement_base lsmpl lsρ
   withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (MlKem PqRatchetState V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchet
  (keys_ls_subroutine_ok_of_block_cro subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (ValidV1PtsAt)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_ChunkedCt1AcknowledgedMergePlacedTightOk tlb_ChunkedCt1AcknowledgedMergePlacedTightOkOf
   tlb_ChunkedCt1ReceivedMergePlacedTightOk tlb_ChunkedCt1ReceivedMergePlacedTightOkOf
   tlb_ChunkedCt1SampledMergePlacedTightOk tlb_ChunkedCt1SampledMergePlacedTightOkOf
   tlb_ChunkedCt2SampledMergePlacedTightOk tlb_ChunkedCt2SampledMergePlacedTightOkOf
   tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOk
   tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOkOf
   tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOk
   tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOkOf
   tlb_ChunkedHeaderReceivedMergePlacedTightOk tlb_ChunkedHeaderReceivedMergePlacedTightOkOf
   tlb_ChunkedHeaderSentMergePlacedTightOk tlb_ChunkedHeaderSentMergePlacedTightOkOf
   tlb_ChunkedKeysSampledMergePlacedTightOk tlb_ChunkedKeysSampledMergePlacedTightOkOf
   tlb_ChunkedKeysUnsampledMergePlacedTightOk tlb_ChunkedKeysUnsampledMergePlacedTightOkOf
   tlb_ChunkedNoHeaderReceivedMergePlacedTightOk tlb_ChunkedNoHeaderReceivedMergePlacedTightOkOf
   tlb_V1StateMergeBlk325TightOkOf tlb_V1StateMergeGuardedEnvOf
   tlb_V1StateMergePlacedTightOk tlb_V1StateMergePlacedTightOkOf)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_decode_props)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget
  (dropProtoChunkedCt1ReceivedSpec dropProtoChunkedEkSentCt1ReceivedSpec
   dropProtoChunkedHeaderReceivedSpec dropProtoChunkedHeaderSentSpec
   dropProtoChunkedNoHeaderReceivedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (dropProtoUnchunkedCt1SentEkReceivedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (chunkedCt1AcknowledgedMergeSpec chunkedCt1ReceivedMergeSpec chunkedCt1SampledMergeSpec
   chunkedEkSentCt1ReceivedMergeSpec decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (chunkedCt2SampledMergeSpec chunkedEkReceivedCt1SampledMergeSpec chunkedHeaderReceivedMergeSpec
   chunkedHeaderSentMergeSpec chunkedKeysSampledMergeSpec chunkedKeysUnsampledMergeSpec
   chunkedNoHeaderReceivedMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (v1StateMergePlacedSpec v1StateMergePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightDefs
  (e2mDomSpec e2m_ls_subroutine_ok_cl_of_block_ext e2m_ls_subroutine_ok_cro_of_block_ext
   e2m_ls_subroutine_ok_of_block_ext e2m_ok_exit_216_placed e2m_prologue_to_216_placed
   e2m_subroutine_ok_of_dom_and_fallback)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightTags1To4PlacedBudget
  (e2m_tag1_canonical_tight_placed e2m_tag2_canonical_tight_placed
   e2m_tag3_canonical_tight_placed e2m_tag4_canonical_tight_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightTags5To8PlacedBudget
  (e2m_tag5_canonical_tight_placed e2m_tag6_canonical_tight_placed
   e2m_tag7_canonical_tight_placed e2m_tag8_canonical_tight_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightTags9To11PlacedBudget
  (e2m_tag9_canonical_tight_placed e2m_tag10_canonical_tight_placed
   e2m_tag11_canonical_tight_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProofClPlacedBudget (v1State_merge_cl)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-! ## 1. Canonical Input Guard & `TopStateTight` Implication Bridge -/

/-- Decoded `V1State` tight payload predicate implied by `TopStateTight`. -/
def E2mTightV1Pb (pb : V1State) : Prop :=
  ValidV1PtsAt 640 pb ∧ rawV1State pb ≤ 46880

/-- Guard implication lemma from `LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.TopStateTight`
to `E2mTightV1Pb` on the decoded `PqRatchetState`'s `v1` payload. -/
theorem e2m_topStateTight_imp_tightV1Pb {F : ShaCompress} {K : MlKem} {stBytes : List (BitVec 8)}
    (hTop : TopStateTight F K stBytes)
    {pq : PqRatchetState} (hdec : spqrDecodeState stBytes = .ok pq)
    {pb : V1State} (hv1 : pq.inner = some (.v1 pb)) :
    E2mTightV1Pb pb := by
  obtain ⟨-, -, hv1_props, -⟩ := topStateTight_decode_props hTop hdec
  obtain ⟨hraw, hpts⟩ := hv1_props pb hv1
  exact ⟨hpts, hraw⟩

/-- `maxOps`-parametric (`SpqrTightEvs maxOps cumCap maxReq`) `FreeOnlyEvs`-append closure helper:
`Block 298`'s `dropOptProtoInnerState` (`Block 267`) on `none` adds `(0, 0, 0)` to any
`SpqrTightEvs maxOps cumCap maxReq` trace. -/
theorem e2m_spqrTightEvs_append_freeOnly {maxOps cumCap maxReq : Nat}
    {evs evs_d : List AllocEvent}
    (h : SpqrTightEvs maxOps cumCap maxReq evs) (hf : FreeOnlyEvs evs_d) :
    SpqrTightEvs maxOps cumCap maxReq (evs ++ evs_d) :=
  (h.append (SpqrTightEvs.of_freeOnly hf)).mono (by omega) (by omega) (by omega)

/-! ## 2. Canonical `tlb_` Seam Producers for `Block 298` (`SpqrTightLeafBridges`) -/

/-- `maxOps`-parametric guarded-tight contract for `V1State::merge` (Block `298`), combining
`hFallback` on `¬ tlb_V1StateMergeDom` with `hVarint` (Block `291`), `hDropInner` (Block `267`),
and the 11 `Chunked.*` arm contracts (`Blocks 300..310`). -/
theorem e2m_v1State_merge_placed_tight_ok_of_fallback [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxOps csOps c2Ops hsOps crOps ksOps kuOps hrOps caOps nhOps esOps ekOps : Nat}
    {ext : String → Option (State → State)}
    (hCsLe : csOps ≤ maxOps) (hC2Le : c2Ops ≤ maxOps) (hHsLe : hsOps ≤ maxOps)
    (hCrLe : crOps ≤ maxOps) (hKsLe : ksOps ≤ maxOps) (hKuLe : kuOps ≤ maxOps)
    (hHrLe : hrOps ≤ maxOps) (hCaLe : caOps ≤ maxOps) (hNhLe : nhOps ≤ maxOps)
    (hEsLe : esOps ≤ maxOps) (hEkLe : ekOps ≤ maxOps)
    (hFallback : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hDropInner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hCs300 : tlb_ChunkedCt1SampledMergePlacedTightOkOf A lim csOps ext)
    (hC2301 : tlb_ChunkedCt2SampledMergePlacedTightOkOf A lim c2Ops ext)
    (hHs302 : tlb_ChunkedHeaderSentMergePlacedTightOkOf A lim hsOps ext)
    (hCr303 : tlb_ChunkedCt1ReceivedMergePlacedTightOkOf A lim crOps ext)
    (hKs304 : tlb_ChunkedKeysSampledMergePlacedTightOkOf A lim ksOps ext)
    (hKu305 : tlb_ChunkedKeysUnsampledMergePlacedTightOkOf A lim kuOps ext)
    (hHr306 : tlb_ChunkedHeaderReceivedMergePlacedTightOkOf A lim hrOps ext)
    (hCa307 : tlb_ChunkedCt1AcknowledgedMergePlacedTightOkOf A lim caOps ext)
    (hNh308 : tlb_ChunkedNoHeaderReceivedMergePlacedTightOkOf A lim nhOps ext)
    (hEs309 : tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOkOf A lim esOps ext)
    (hEk310 : tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOkOf A lim ekOps ext) :
    tlb_V1StateMergePlacedTightOkOf A lim maxOps ext := by
  have hVarintCall :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (e2m_ls_subroutine_ok_of_block_ext
        (callerProg := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
        (IsLsBlockProg.externs_eq
          (prog := (CryptoVerification.blkPC_291).rebase (CryptoVerification.blkPl_291).base
            (fun _ => none)))
        hVarint)
  have hDropInnerCall :=
    e2m_ls_subroutine_ok_cl_of_block_ext
      (callerProg := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (IsLsBlockProg.externs_eq
        (prog := (CryptoVerification.blkPC_267).rebase (CryptoVerification.blkPl_267).base
          (fun _ => none)))
      hDropInner
  have hCsCall :=
    e2m_ls_subroutine_ok_cro_of_block_ext
      (callerProg := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (IsLsBlockProg.externs_eq
        (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_300).rebase
          (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_300).base (fun _ => none)))
      hCs300
  have hC2Call :=
    e2m_ls_subroutine_ok_cro_of_block_ext
      (callerProg := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (IsLsBlockProg.externs_eq
        (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_301).rebase
          (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_301).base (fun _ => none)))
      hC2301
  have hHsCall :=
    e2m_ls_subroutine_ok_cro_of_block_ext
      (callerProg := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (IsLsBlockProg.externs_eq
        (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_302).rebase
          (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_302).base (fun _ => none)))
      hHs302
  have hCrCall :=
    e2m_ls_subroutine_ok_cro_of_block_ext
      (callerProg := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (IsLsBlockProg.externs_eq
        (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_303).rebase
          (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_303).base (fun _ => none)))
      hCr303
  have hKsCall :=
    e2m_ls_subroutine_ok_cro_of_block_ext
      (callerProg := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (IsLsBlockProg.externs_eq
        (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_304).rebase
          (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_304).base (fun _ => none)))
      hKs304
  have hKuCall :=
    e2m_ls_subroutine_ok_cro_of_block_ext
      (callerProg := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (IsLsBlockProg.externs_eq
        (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_305).rebase
          (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_305).base (fun _ => none)))
      hKu305
  have hHrCall :=
    e2m_ls_subroutine_ok_cro_of_block_ext
      (callerProg := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (IsLsBlockProg.externs_eq
        (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_306).rebase
          (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_306).base (fun _ => none)))
      hHr306
  have hCaCall :=
    e2m_ls_subroutine_ok_cro_of_block_ext
      (callerProg := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (IsLsBlockProg.externs_eq
        (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_307).rebase
          (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_307).base (fun _ => none)))
      hCa307
  have hNhCall :=
    e2m_ls_subroutine_ok_cro_of_block_ext
      (callerProg := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (IsLsBlockProg.externs_eq
        (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_308).rebase
          (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_308).base (fun _ => none)))
      hNh308
  have hEsCall :=
    e2m_ls_subroutine_ok_cro_of_block_ext
      (callerProg := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (IsLsBlockProg.externs_eq
        (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_309).rebase
          (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_309).base (fun _ => none)))
      hEs309
  have hEkCall :=
    e2m_ls_subroutine_ok_cro_of_block_ext
      (callerProg := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (IsLsBlockProg.externs_eq
        (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPC_310).rebase
          (CryptoVerification.SpqrV1.Prost.MessageMerge.Part2.blkPl_310).base (fun _ => none)))
      hEk310
  have hDomOk : subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (blkPl_298).base (withLsCodeRoLoaded lsmpl (e2mDomSpec A lim maxOps)) := by
    refine e2m_prologue_to_216_placed hVarintCall ?_
    intro x st0 R s0 s pb rest hDom hFit0 hValid _hbs_eq hbs_lt56 hraw_lt63 _hraw_lt64
      hrest0_lt hrest0_le hrest0_suf hrest_le_bs hrest_suf_bs hsome_top hsp_align
      hpc hrun hsp htr hregs hinv
    rcases pb with ⟨_ | is⟩
    · exact e2m_ok_exit_216_placed (evs := []) hDom hsome_top
        ((SpqrTightEvs.of_freeOnly FreeOnlyEvs.nil).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _))
        (Nat.lt_of_le_of_lt hrest_le_bs hbs_lt56)
        hsp_align hrest_le_bs hrest_suf_bs hpc hrun hsp htr hregs
    · cases is with
      | keysUnsampled ku =>
        exact e2m_tag1_canonical_tight_placed hVarintCall hKuCall hDropInnerCall hKuLe
          ku rest hDom hFit0 (hValid _ rfl) hbs_lt56 hraw_lt63 hrest0_lt hrest0_le hrest0_suf
          hrest_le_bs hrest_suf_bs hsome_top hsp_align hpc hrun hsp htr hregs hinv
      | keysSampled ks =>
        exact e2m_tag2_canonical_tight_placed hVarintCall hKsCall hDropInnerCall hKsLe
          ks rest hDom hFit0 (hValid _ rfl) hbs_lt56 hraw_lt63 hrest0_lt hrest0_le hrest0_suf
          hrest_le_bs hrest_suf_bs hsome_top hsp_align hpc hrun hsp htr hregs hinv
      | headerSent hs =>
        exact e2m_tag3_canonical_tight_placed hVarintCall hHsCall hDropInnerCall hHsLe
          hs rest hDom hFit0 (hValid _ rfl) hbs_lt56 hraw_lt63 hrest0_lt hrest0_le hrest0_suf
          hrest_le_bs hrest_suf_bs hsome_top hsp_align hpc hrun hsp htr hregs hinv
      | ct1Received cr =>
        exact e2m_tag4_canonical_tight_placed hVarintCall hCrCall hDropInnerCall hCrLe
          cr rest hDom hFit0 (hValid _ rfl) hbs_lt56 hraw_lt63 hrest0_lt hrest0_le hrest0_suf
          hrest_le_bs hrest_suf_bs hsome_top hsp_align hpc hrun hsp htr hregs hinv
      | ekSentCt1Received es =>
        exact e2m_tag5_canonical_tight_placed hVarintCall hEsCall hDropInnerCall hEsLe
          es rest hDom hFit0 (hValid _ rfl) hbs_lt56 hraw_lt63 hrest0_lt hrest0_le hrest0_suf
          hrest_le_bs hrest_suf_bs hsome_top hsp_align hpc hrun hsp htr hregs hinv
      | noHeaderReceived nh =>
        exact e2m_tag6_canonical_tight_placed hVarintCall hNhCall hDropInnerCall hNhLe
          nh rest hDom hFit0 (hValid _ rfl) hbs_lt56 hraw_lt63 hrest0_lt hrest0_le hrest0_suf
          hrest_le_bs hrest_suf_bs hsome_top hsp_align hpc hrun hsp htr hregs hinv
      | headerReceived hr =>
        exact e2m_tag7_canonical_tight_placed hVarintCall hHrCall hDropInnerCall hHrLe
          hr rest hDom hFit0 (hValid _ rfl) hbs_lt56 hraw_lt63 hrest0_lt hrest0_le hrest0_suf
          hrest_le_bs hrest_suf_bs hsome_top hsp_align hpc hrun hsp htr hregs hinv
      | ct1Sampled cs =>
        exact e2m_tag8_canonical_tight_placed hVarintCall hCsCall hDropInnerCall hCsLe
          cs rest hDom hFit0 (hValid _ rfl) hbs_lt56 hraw_lt63 hrest0_lt hrest0_le hrest0_suf
          hrest_le_bs hrest_suf_bs hsome_top hsp_align hpc hrun hsp htr hregs hinv
      | ekReceivedCt1Sampled ek =>
        exact e2m_tag9_canonical_tight_placed hVarintCall hEkCall hDropInnerCall hEkLe
          ek rest hDom hFit0 (hValid _ rfl) hbs_lt56 hraw_lt63 hrest0_lt hrest0_le hrest0_suf
          hrest_le_bs hrest_suf_bs hsome_top hsp_align hpc hrun hsp htr hregs hinv
      | ct1Acknowledged ca =>
        exact e2m_tag10_canonical_tight_placed hVarintCall hCaCall hDropInnerCall hCaLe
          ca rest hDom hFit0 (hValid _ rfl) hbs_lt56 hraw_lt63 hrest0_lt hrest0_le hrest0_suf
          hrest_le_bs hrest_suf_bs hsome_top hsp_align hpc hrun hsp htr hregs hinv
      | ct2Sampled c2 =>
        exact e2m_tag11_canonical_tight_placed hVarintCall hC2Call hDropInnerCall hC2Le
          c2 rest hDom hFit0 (hValid _ rfl) hbs_lt56 hraw_lt63 hrest0_lt hrest0_le hrest0_suf
          hrest_le_bs hrest_suf_bs hsome_top hsp_align hpc hrun hsp htr hregs hinv
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 298)] at hDomOk
  exact e2m_subroutine_ok_of_dom_and_fallback hDomOk hFallback

/-- Self-contained `maxOps`-parametric guarded-tight contract for `V1State::merge` (Block `298`),
instantiating the `¬ tlb_V1StateMergeDom` fallback via `v1State_merge_cl`. -/
theorem e2m_v1State_merge_placed_tight_ok_of [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxOps csOps c2Ops hsOps crOps ksOps kuOps hrOps caOps nhOps esOps ekOps : Nat}
    {ext : String → Option (State → State)}
    (hCsLe : csOps ≤ maxOps) (hC2Le : c2Ops ≤ maxOps) (hHsLe : hsOps ≤ maxOps)
    (hCrLe : crOps ≤ maxOps) (hKsLe : ksOps ≤ maxOps) (hKuLe : kuOps ≤ maxOps)
    (hHrLe : hrOps ≤ maxOps) (hCaLe : caOps ≤ maxOps) (hNhLe : nhOps ≤ maxOps)
    (hEsLe : esOps ≤ maxOps) (hEkLe : ekOps ≤ maxOps)
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hDropInner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDropCr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hDropHs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDropEs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 285 (Rust.withPanics ext))
      (lsmpl.base 285) (withLsCodeLoaded lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)))
    (hDropNh : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 284 (Rust.withPanics ext))
      (lsmpl.base 284) (withLsCodeLoaded lsmpl (dropProtoChunkedNoHeaderReceivedSpec M A lim)))
    (hDropHr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 283 (Rust.withPanics ext))
      (lsmpl.base 283) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderReceivedSpec M A lim)))
    (hDropUc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 286 (Rust.withPanics ext))
      (lsmpl.base 286) (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    (hDropEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 271 (Rust.withPanics ext))
      (lsmpl.base 271) (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (hKuLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hKsLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hHsLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hCrLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hEsLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hNhLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hHrLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hCsLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hEkLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim)))
    (hCaLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hC2Loose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hCs300 : tlb_ChunkedCt1SampledMergePlacedTightOkOf A lim csOps ext)
    (hC2301 : tlb_ChunkedCt2SampledMergePlacedTightOkOf A lim c2Ops ext)
    (hHs302 : tlb_ChunkedHeaderSentMergePlacedTightOkOf A lim hsOps ext)
    (hCr303 : tlb_ChunkedCt1ReceivedMergePlacedTightOkOf A lim crOps ext)
    (hKs304 : tlb_ChunkedKeysSampledMergePlacedTightOkOf A lim ksOps ext)
    (hKu305 : tlb_ChunkedKeysUnsampledMergePlacedTightOkOf A lim kuOps ext)
    (hHr306 : tlb_ChunkedHeaderReceivedMergePlacedTightOkOf A lim hrOps ext)
    (hCa307 : tlb_ChunkedCt1AcknowledgedMergePlacedTightOkOf A lim caOps ext)
    (hNh308 : tlb_ChunkedNoHeaderReceivedMergePlacedTightOkOf A lim nhOps ext)
    (hEs309 : tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOkOf A lim esOps ext)
    (hEk310 : tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOkOf A lim ekOps ext) :
    tlb_V1StateMergePlacedTightOkOf A lim maxOps ext :=
  e2m_v1State_merge_placed_tight_ok_of_fallback
    hCsLe hC2Le hHsLe hCrLe hKsLe hKuLe hHrLe hCaLe hNhLe hEsLe hEkLe
    (v1State_merge_cl hDealloc hFrom hPush hVarint hSkip
      hDropInner hDropCr hDropHs hDropEs hDropNh hDropHr hDropUc hDropEnc
      hKuLoose hKsLoose hHsLoose hCrLoose hEsLoose hNhLoose hHrLoose hCsLoose hEkLoose hCaLoose hC2Loose)
    hVarint hDropInner
    hCs300 hC2301 hHs302 hCr303 hKs304 hKu305 hHr306 hCa307 hNh308 hEs309 hEk310

/-- Default `80`-op specialization (`tlb_V1StateMergePlacedTightOk`) from `hFallback` + default
per-arm tight contracts. -/
theorem e2m_v1State_merge_placed_tight_ok_of_fallback_default [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hFallback : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
      (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hDropInner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hCs300 : tlb_ChunkedCt1SampledMergePlacedTightOk A lim ext)
    (hC2301 : tlb_ChunkedCt2SampledMergePlacedTightOk A lim ext)
    (hHs302 : tlb_ChunkedHeaderSentMergePlacedTightOk A lim ext)
    (hCr303 : tlb_ChunkedCt1ReceivedMergePlacedTightOk A lim ext)
    (hKs304 : tlb_ChunkedKeysSampledMergePlacedTightOk A lim ext)
    (hKu305 : tlb_ChunkedKeysUnsampledMergePlacedTightOk A lim ext)
    (hHr306 : tlb_ChunkedHeaderReceivedMergePlacedTightOk A lim ext)
    (hCa307 : tlb_ChunkedCt1AcknowledgedMergePlacedTightOk A lim ext)
    (hNh308 : tlb_ChunkedNoHeaderReceivedMergePlacedTightOk A lim ext)
    (hEs309 : tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOk A lim ext)
    (hEk310 : tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOk A lim ext) :
    tlb_V1StateMergePlacedTightOk A lim ext :=
  e2m_v1State_merge_placed_tight_ok_of_fallback
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hFallback hVarint hDropInner
    hCs300 hC2301 hHs302 hCr303 hKs304 hKu305 hHr306 hCa307 hNh308 hEs309 hEk310

/-- Self-contained default `80`-op own-block producer (`tlb_V1StateMergePlacedTightOk`). -/
theorem e2m_v1State_merge_placed_tight_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hDropInner : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext))
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)))
    (hDropCr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext))
      (lsmpl.base 282) (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec M A lim)))
    (hDropHs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext))
      (lsmpl.base 281) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec M A lim)))
    (hDropEs : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 285 (Rust.withPanics ext))
      (lsmpl.base 285) (withLsCodeLoaded lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec M A lim)))
    (hDropNh : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 284 (Rust.withPanics ext))
      (lsmpl.base 284) (withLsCodeLoaded lsmpl (dropProtoChunkedNoHeaderReceivedSpec M A lim)))
    (hDropHr : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 283 (Rust.withPanics ext))
      (lsmpl.base 283) (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderReceivedSpec M A lim)))
    (hDropUc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 286 (Rust.withPanics ext))
      (lsmpl.base 286) (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)))
    (hDropEnc : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 271 (Rust.withPanics ext))
      (lsmpl.base 271) (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (hKuLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)))
    (hKsLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)))
    (hHsLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
      (lsmpl.base 302) (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)))
    (hCrLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
      (lsmpl.base 303) (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)))
    (hEsLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
      (lsmpl.base 309) (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hNhLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
      (lsmpl.base 308) (withLsCodeRoLoaded lsmpl (chunkedNoHeaderReceivedMergeSpec A lim)))
    (hHrLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)))
    (hCsLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)))
    (hEkLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
      (lsmpl.base 310) (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A lim)))
    (hCaLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)))
    (hC2Loose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
      (lsmpl.base 301) (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)))
    (hCs300 : tlb_ChunkedCt1SampledMergePlacedTightOk A lim ext)
    (hC2301 : tlb_ChunkedCt2SampledMergePlacedTightOk A lim ext)
    (hHs302 : tlb_ChunkedHeaderSentMergePlacedTightOk A lim ext)
    (hCr303 : tlb_ChunkedCt1ReceivedMergePlacedTightOk A lim ext)
    (hKs304 : tlb_ChunkedKeysSampledMergePlacedTightOk A lim ext)
    (hKu305 : tlb_ChunkedKeysUnsampledMergePlacedTightOk A lim ext)
    (hHr306 : tlb_ChunkedHeaderReceivedMergePlacedTightOk A lim ext)
    (hCa307 : tlb_ChunkedCt1AcknowledgedMergePlacedTightOk A lim ext)
    (hNh308 : tlb_ChunkedNoHeaderReceivedMergePlacedTightOk A lim ext)
    (hEs309 : tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOk A lim ext)
    (hEk310 : tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOk A lim ext) :
    tlb_V1StateMergePlacedTightOk A lim ext :=
  e2m_v1State_merge_placed_tight_ok_of
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hDealloc hFrom hPush hVarint hSkip
    hDropInner hDropCr hDropHs hDropEs hDropNh hDropHr hDropUc hDropEnc
    hKuLoose hKsLoose hHsLoose hCrLoose hEsLoose hNhLoose hHrLoose hCsLoose hEkLoose hCaLoose hC2Loose
    hCs300 hC2301 hHs302 hCr303 hKs304 hKu305 hHr306 hCa307 hNh308 hEs309 hEk310

/-- Lifts `tlb_V1StateMergePlacedTightOkOf` from `libsignalSessionLib.blockProgram` (Block `298`)
onto caller `blkPC_325` (`tlb_decodeState_placed_ok_of_v1Merge`). -/
theorem e2m_v1State_merge_blk325_tight_ok_of [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxOps : Nat}
    {ext : String → Option (State → State)}
    (h298 : tlb_V1StateMergePlacedTightOkOf A lim maxOps ext) :
    tlb_V1StateMergeBlk325TightOkOf A lim maxOps ext :=
  @keys_ls_subroutine_ok_of_block_cro _ _
    ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
    325 298 (Rust.withPanics ext) inferInstance
    ⟨rfl, IsLsBlockProg.externs_eq
      (prog := (blkPC_298).rebase (blkPl_298).base (fun _ => none))⟩
    (lsmpl.base 298)
    (v1StateMergePlacedSpecOfEnv A lim
      (tlb_V1StateMergeGuardedEnvOf maxOps) (tlb_V1StateMergeGuardedEnvOf maxOps))
    h298 _ _ _ _ (by decide) (by decide) (by decide)

/-- Default `80`-op `blk325` lift. -/
theorem e2m_v1State_merge_blk325_tight_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h298 : tlb_V1StateMergePlacedTightOk A lim ext) :
    tlb_V1StateMergeBlk325TightOkOf A lim 80 ext :=
  e2m_v1State_merge_blk325_tight_ok_of h298

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightPlacedBudget
