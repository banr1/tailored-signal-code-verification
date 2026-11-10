/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetA
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetB
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetC
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB309PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB310PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyMergeTightPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateAuthCountedR
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym

/-!
# Block-298 `V1State::merge` CLI Contract for `decode_state`

**Checked by Lean.**

Instantiates `tlb_V1StateMergeBlk325TightOkOf A lim 80` on CLI extern tables for reuse
across `encrypt` (`W1`) and `decryptSignal` (`W2`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.V1MergeBlk325Cli

open Arm64 (State subroutine_ok)
open Arm64.Obj (MultiPlacement)
open Arm64.Rust (withPanics)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement libsignalSessionLib
   lsProg_261 lsProg_263 lsProg_290 lsProg_291 lsmpl)
open CryptoVerification.RecordCodecs.Placed (lsProg_257)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SpqrV1.Prost.MessageMerge (instIsLsBlockProg_296 instIsLsBlockProg_297)
open CryptoVerification.SpqrV1.Top.Recv (ls_subroutine_ok_cro_of_cl ls_subroutine_ok_cro_of_cro)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthMergePlacedTightOk tlb_PolyDecoderMergePlacedTightOk tlb_PolyEncoderMergePlacedTightOk
   tlb_UcCt1SentMergePlacedTightOk tlb_UcEkSentCt1ReceivedMergePlacedTightOk
   tlb_V1StateMergeBlk325TightOkOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
  (cliV1StateMerge_closed_cl)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
  (cliBytes_290_cl cliDrop_267_cl cliFrom_261_cl cliPushMerge_257_cl cliSkip_263_cl
   cliVarint_291_cl)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget
  (cliAuthMergeBase_blockProgram_cro cliBytesExact_290_cro cliGrowOneVecU8_at_block
   cliPolyDecoderMerge_296_cro cliPolyEncoderMerge_297_cro cliUnchunkedCt1SentMerge_312_cro
   cliUnchunkedEkSentCt1ReceivedMerge_311_cro)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetA
  (e2ka_chunkedCt1ReceivedMerge_placed_tight_ok_of e2ka_chunkedCt1SampledMerge_placed_tight_ok
   e2ka_chunkedCt2SampledMerge_placed_tight_ok_of e2ka_chunkedHeaderSentMerge_placed_tight_ok_of
   e2ka_ucCt1SentMerge_placed_tight_ok_of e2ka_ucEkSentCt1ReceivedMerge_placed_tight_ok_of)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetB
  (e2kb_chunkedCt1Acknowledged_merge_placed_tight_ok e2kb_chunkedHeaderReceived_merge_placed_tight_ok
   e2kb_chunkedKeysSampled_merge_placed_tight_ok e2kb_chunkedKeysUnsampled_merge_placed_tight_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetC
  (e2kc_chunkedNoHeaderReceived_merge_tight_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB309PlacedBudget
  (e2b309_chunkedEkSentCt1Received_merge_tight_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB310PlacedBudget
  (e2b310_chunkedEkReceivedCt1Sampled_merge_tight_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyMergeTightPlacedBudget
  (e2p_tlb_polyDecoderMerge_placed_ok_tight e2p_tlb_polyEncoderMerge_placed_ok_tight)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightPlacedBudget
  (e2m_v1State_merge_blk325_tight_ok e2m_v1State_merge_placed_tight_ok_of_fallback_default)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateAuthCountedR
  (e2ar_authMerge_own_cl_placed_ok_tight)

/-- Instantiates `tlb_V1StateMergeBlk325TightOkOf A lim 80 ext` for any extern table agreeing with `cliGhostExterns` outside `"libsignal_session_rng_fill"`. -/
theorem v1StateMergeBlk325_cli_of_hExt [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (hA : CliGhostAllocHooks M A lim gh) :
    tlb_V1StateMergeBlk325TightOkOf A lim 80 ext := by
  let _ : IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 261 (withPanics ext))
      261 (withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_261 (withPanics ext))
      261 (withPanics ext)).externs_eq⟩
  let _ : IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 257 (withPanics ext))
      257 (withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_257 (withPanics ext))
      257 (withPanics ext)).externs_eq⟩
  let _ : IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 291 (withPanics ext))
      291 (withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_291 (withPanics ext))
      291 (withPanics ext)).externs_eq⟩
  let _ : IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 263 (withPanics ext))
      263 (withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_263 (withPanics ext))
      263 (withPanics ext)).externs_eq⟩
  let _ : IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 290 (withPanics ext))
      290 (withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_290 (withPanics ext))
      290 (withPanics ext)).externs_eq⟩
  let _ : IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 296 (withPanics ext))
      296 (withPanics ext) :=
    ⟨rfl, (instIsLsBlockProg_296 (withPanics ext)).externs_eq⟩
  let _ : IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl 297 (withPanics ext))
      297 (withPanics ext) :=
    ⟨rfl, (instIsLsBlockProg_297 (withPanics ext)).externs_eq⟩
  have hFrom := cliFrom_261_cl mmpl gh W hA (ext := ext) hExt
  have hPush := cliPushMerge_257_cl mmpl gh W hA (ext := ext) hExt
  have hVarint := cliVarint_291_cl mmpl gh W hA (ext := ext) hExt
  have hSkip := cliSkip_263_cl mmpl gh W hA (ext := ext) hExt
  have hBytesPoly := cliBytes_290_cl mmpl gh W hA (ext := ext) hExt
  have hBytesSigned := cliBytesExact_290_cro mmpl gh W hA (ext := ext) hExt
  have hDropInner := cliDrop_267_cl mmpl gh W hA (ext := ext) hExt
  have hAuthBase := cliAuthMergeBase_blockProgram_cro mmpl gh W hA (ext := ext) hExt
  have hPolyDecBase := cliPolyDecoderMerge_296_cro mmpl gh W hA (ext := ext) hExt
  have hPolyEncBase := cliPolyEncoderMerge_297_cro mmpl gh W hA (ext := ext) hExt
  have hUc311Base := cliUnchunkedEkSentCt1ReceivedMerge_311_cro mmpl gh W hA (ext := ext) hExt
  have hUc312Base := cliUnchunkedCt1SentMerge_312_cro mmpl gh W hA (ext := ext) hExt
  have hFallback := cliV1StateMerge_closed_cl mmpl gh W hA (ext := ext) hExt
  have hAuthTight : tlb_AuthMergePlacedTightOk A lim ext :=
    e2ar_authMerge_own_cl_placed_ok_tight hFrom hPush hVarint hSkip hBytesPoly
  have hGrow296 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (withPanics ext))
      (lsmpl.base 621) _ :=
    cliGrowOneVecU8_at_block
      (callerProg := libsignalSessionLib.blockProgram lsmpl 296 (withPanics ext))
      (i := 296) (bi := 623) mmpl gh W hA (ext := ext) hExt
  have hGrow297 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (withPanics ext))
      (lsmpl.base 621) _ :=
    cliGrowOneVecU8_at_block
      (callerProg := libsignalSessionLib.blockProgram lsmpl 297 (withPanics ext))
      (i := 297) (bi := 623) mmpl gh W hA (ext := ext) hExt
  have hPolyDecTight : tlb_PolyDecoderMergePlacedTightOk A lim ext :=
    e2p_tlb_polyDecoderMerge_placed_ok_tight (ext := ext)
      (ls_subroutine_ok_cro_of_cl (i := 296) (j := 261) hFrom (by decide) (by decide) (by decide))
      (ls_subroutine_ok_cro_of_cl (i := 296) (j := 257) hPush (by decide) (by decide) (by decide))
      (ls_subroutine_ok_cro_of_cl (i := 296) (j := 291) hVarint (by decide) (by decide) (by decide))
      (ls_subroutine_ok_cro_of_cl (i := 296) (j := 263) hSkip (by decide) (by decide) (by decide))
      (ls_subroutine_ok_cro_of_cro (i := 296) (j := 290) hBytesPoly (by decide) (by decide) (by decide))
      hGrow296
  have hPolyEncTight : tlb_PolyEncoderMergePlacedTightOk A lim ext :=
    e2p_tlb_polyEncoderMerge_placed_ok_tight (ext := ext)
      (ls_subroutine_ok_cro_of_cl (i := 297) (j := 261) hFrom (by decide) (by decide) (by decide))
      (ls_subroutine_ok_cro_of_cl (i := 297) (j := 257) hPush (by decide) (by decide) (by decide))
      (ls_subroutine_ok_cro_of_cl (i := 297) (j := 291) hVarint (by decide) (by decide) (by decide))
      (ls_subroutine_ok_cro_of_cl (i := 297) (j := 263) hSkip (by decide) (by decide) (by decide))
      (ls_subroutine_ok_cro_of_cro (i := 297) (j := 290) hBytesPoly (by decide) (by decide) (by decide))
      hGrow297
  have hUc311Tight : tlb_UcEkSentCt1ReceivedMergePlacedTightOk A lim ext :=
    e2ka_ucEkSentCt1ReceivedMerge_placed_tight_ok_of (Nat.le_refl 8)
      hFrom hPush hVarint hSkip hBytesSigned hAuthBase hAuthTight
  have hUc312Tight : tlb_UcCt1SentMergePlacedTightOk A lim ext :=
    e2ka_ucCt1SentMerge_placed_tight_ok_of (Nat.le_refl 10)
      hFrom hPush hVarint hSkip hBytesSigned hAuthBase hAuthTight
  have hCs300 := e2ka_chunkedCt1SampledMerge_placed_tight_ok
    hFrom hPush hVarint hSkip hUc312Base hPolyEncBase hPolyDecBase
    hUc312Tight hPolyEncTight hPolyDecTight
  have hC2301 := e2ka_chunkedCt2SampledMerge_placed_tight_ok_of (Nat.le_refl 39)
    hFrom hPush hVarint hSkip hAuthBase hPolyEncBase hAuthTight hPolyEncTight
  have hHs302 := e2ka_chunkedHeaderSentMerge_placed_tight_ok_of (Nat.le_refl 76)
    hFrom hPush hVarint hSkip hBytesSigned hAuthBase hPolyEncBase hPolyDecBase
    hAuthTight hPolyEncTight hPolyDecTight
  have hCr303 := e2ka_chunkedCt1ReceivedMerge_placed_tight_ok_of (Nat.le_refl 43)
    hFrom hPush hVarint hSkip hUc311Base hPolyEncBase hUc311Tight hPolyEncTight
  have hKs304 := e2kb_chunkedKeysSampled_merge_placed_tight_ok A lim
    hFrom hPush hVarint hSkip hBytesPoly hAuthBase hPolyEncBase hAuthTight hPolyEncTight
  have hKu305 := e2kb_chunkedKeysUnsampled_merge_placed_tight_ok A lim
    hFrom hPush hVarint hSkip hAuthBase hAuthTight
  have hHr306 := e2kb_chunkedHeaderReceived_merge_placed_tight_ok A lim
    hFrom hPush hVarint hSkip hBytesPoly hAuthBase hPolyDecBase hAuthTight hPolyDecTight
  have hCa307 := e2kb_chunkedCt1Acknowledged_merge_placed_tight_ok A lim
    hFrom hPush hVarint hSkip hUc312Base hPolyDecBase hUc312Tight hPolyDecTight
  have hNh308 := e2kc_chunkedNoHeaderReceived_merge_tight_placed_ok
    hFrom hPush hVarint hSkip hAuthBase hPolyDecBase hAuthTight hPolyDecTight
  have hEs309 := e2b309_chunkedEkSentCt1Received_merge_tight_placed_ok
    hFrom hPush hVarint hSkip hUc311Base hPolyDecBase hUc311Tight hPolyDecTight
  have hEk310 := e2b310_chunkedEkReceivedCt1Sampled_merge_tight_placed_ok
    hFrom hPush hVarint hSkip hBytesPoly hAuthBase hPolyEncBase hAuthTight hPolyEncTight
  exact e2m_v1State_merge_blk325_tight_ok
    (e2m_v1State_merge_placed_tight_ok_of_fallback_default
      hFallback hVarint hDropInner
      hCs300 hC2301 hHs302 hCr303 hKs304 hKu305 hHr306 hCa307 hNh308 hEs309 hEk310)

/-- Specializes `v1StateMergeBlk325_cli_of_hExt` to `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem v1StateMergeBlk325_cli [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    tlb_V1StateMergeBlk325TightOkOf A lim 80
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  v1StateMergeBlk325_cli_of_hExt mmpl gh W (fun _ _ => rfl) hA

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.V1MergeBlk325Cli
