/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatExt
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExt
import LibsignalBinary.Proofs.SpqrV1.Auth.UpdateExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofXExt
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.ProofExt
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofExt
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkExt
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMessageBridgeExt
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkExt
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProofExt
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochExt
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkExt
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedSendCt2Ext
import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopExt
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Ct1ReceivedExt
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Proof
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.RecvCt1AckExt

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed `<States>::recv` Assembly

Assembles `StatesRecvContractsAx` from the 13 contract-backed leaf proofs under `CliExternsOk`
and `AgreeOnCliHooks`, discharging `StatesRecvOkXExt` for `<States>::recv`.
-/

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ContractsAxExt

open Arm64 ProofLib ProofLib.ObjectLoad
open CryptoVerification (libsignalSessionCode libsignalSessionImage)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.RustHeap
  (RustAlloc allocHookStack rustAllocSpec)
open CryptoVerification.LibsignalTripleRatchet
  (AllocContractsX tripleRatchetProgAtExt withStack
   allocName shimName memcpyName noAllocShimSpec)
open CryptoVerification.LibsignalSpqrV1
  (libcruxHmacName libcruxHmacSpec
   mlkemDecapsName mlkemDecapsSpec mlkemEncaps2Name mlkemEncaps2Spec
   mlkemValidatePkName mlkemValidatePkSpec)
open CryptoVerification.SignalSession (CliExternsOk cliExternsWith)
open CryptoVerification.SignalSession.Cli.Slots
  (AgreeOnCliHooks allocContractsX_of_externsOk_on
   hookSat_map
   hookOk_sessionMemset_of_cliExt hookOk_libcMemset_of_session
   hookOk_sessionMemsetRegion_of_session hookOk_memsetRegion_of_libc)
open CryptoVerification.SpqrV1.Alloc
  (AllocContracts4K sessionMemcpyROSpec4K libcMemcpyRO_of_sessionMemcpyRO4K
   sessionMemcpyRegionROSpecWithStack
   hookSat_session2Memcpy4K_of_externsOk_on hookSat_sessionMemcpyRO4K_of_externsOk_on
   sliceConcat2_ok_of_externsOk_on sliceConcat3_ok_of_externsOk_on
   do_reserve_7_ok_ext_x_4k)
open CryptoVerification.SpqrV1.Auth
  (allocZeroedWithStackOkX_of_hook authUpdate_ok_of_externsOk_on)
open CryptoVerification.SpqrV1.Kdf (SpqrKdfHooksExt)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof (hkdf_to_slice_spqr_ok_of_hooks_ext)
open CryptoVerification.SpqrV1.Drop (DeallocOkExt)
open CryptoVerification.SpqrV1.Poly.AddChunk (AddChunkOkX add_chunk_ok_x_4k)
open CryptoVerification.SpqrV1.Poly.DecodedMessage
  (polyDecoderDecodedMessage_ok_4k polyDecoderDecodedMessage_ok_inImage_4k)
open CryptoVerification.SpqrV1.Poly.EncodeBytes (encode_bytes_ok_ext_4k encode_bytes_ok_x_4k)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
  (PolyDecodedMessageOkX polyDecodedMessageOkX_of_decodedMessage
   recv_ct2_chunk_ok_ext ct1_received_recv_ct2_chunk_ok_ax
   ek_received_ct1_sampled_recv_ct1_ack_ok_ax)
open CryptoVerification.SpqrV1.States.Recv
  (StatesRecvContractsExt StatesRecvContractsAx StatesRecvOkXExt
   states_recv_ok_x_ext_ax_full)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkExt
  (keys_sampled_recv_ct1_chunk_ok_ax)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMessageBridgeExt
  (poly_decoder_decoded_message_ok_inImage poly_decoder_decoded_message_ok_ax
   header_sent_recv_ct1_chunk_ok_ax)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProofExt
  (noHeaderReceived_recv_hdr_chunk_ok_ax)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEkExt
  (unchunked_ct1_sent_recv_ek_ok_inImage unchunked_ct1_sent_recv_ek_ok_ax)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedSendCt2Ext
  (unchunked_ct1_sent_ek_received_send_ct2_ok_inImage_of_hooks
   unchunked_ct1_sent_ek_received_send_ct2_ok_ax_of_hooks)
open CryptoVerification.SpqrV1.States.Leaves
  (send_ct2_encoder_ok_inImage send_ct2_encoder_ok_ax)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkExt
  (ct1_acknowledged_recv_ek_chunk_ok_ax)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochExt
  (ct2_sampled_recv_next_epoch_ok_ax)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## `SpqrV1.Alloc.AllocContracts4K` & `DeallocOkExt` from `CliExternsOk` -/

private theorem stub_raw_of_hookSat_local {α : Type} (b : BitVec 64)
    {ext : String → Option (State → State)} {fnName hname : String} {spec : Spec α}
    (hlt : libsignalSessionCode.fnOff fnName < 2 ^ 64)
    (hhook : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff?
      (libsignalSessionCode.fnOff fnName) = H hname)
    (hnp : Rust.isPanicSymbol hname = false)
    (hsat : HookSat ext hname spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr fnName) spec := by
  have h := hook_ok_at (P := libsignalSessionCode) (b := b) (hooks := ext)
    (name := fnName) (hname := hname) (stub := libsignalSessionCode.fnOff fnName) (k := 0)
    rfl (Nat.add_zero _) hlt hhook hnp hsat
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h

private theorem sessionMemcpyRO4K_of_withStack {prog : Program} {addr : BitVec 64}
    {stk : Nat} (hlo : allocHookStack ≤ stk) (hhi : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog addr (sessionMemcpyRegionROSpecWithStack allocHookStack)) :
    subroutine_ok prog addr (withStack sessionMemcpyROSpec4K stk) := by
  apply subroutine_ok_outcome_intro
  intro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have h1 := stackAt_split_bottom s0.sp allocHookStack (stk - allocHookStack) (by omega)
    rwa [Nat.add_sub_of_le hlo] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗ R
  have hpre' : s0.mem ⊨ (sessionMemcpyRegionROSpecWithStack allocHookStack).pre (dst, src, bs) s0 ∗ R' := by
    dsimp only [withStack, sessionMemcpyROSpec4K, sessionMemcpyRegionROSpecWithStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h.mono_outcome (dst, src, bs) R' s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · left
    refine ⟨hret, hcs, ?_⟩
    dsimp only [withStack, sessionMemcpyROSpec4K, sessionMemcpyRegionROSpecWithStack, R'] at hpost ⊢
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · dsimp only [sessionMemcpyRegionROSpecWithStack] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [sessionMemcpyRegionROSpecWithStack] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [sessionMemcpyRegionROSpecWithStack] at ho
    rw [satisfies_pure_sepConj] at ho; exact False.elim ho.1

theorem allocContracts4K_of_externsOk_on {P : PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') (b : BitVec 64) :
    AllocContracts4K b A ext' :=
  let hM4 := CryptoVerification.Cli.LibsignalSpqrV1.M4.AllocContracts4K.of_externsOk_on hOk hAg b
  { alloc := hM4.alloc
    dealloc := hM4.dealloc
    realloc := hM4.realloc
    shim := hM4.shim
    memcpy := hM4.memcpy
    session_memcpy := hM4.session_memcpy
    memcpy_ro := fun stk hlo hhi => libcMemcpyRO_of_sessionMemcpyRO4K
      (sessionMemcpyRO4K_of_withStack hlo hhi
        (stub_raw_of_hookSat_local b (by simp only [arm64_norm])
          (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memcpyName])
          (hookSat_sessionMemcpyRO4K_of_externsOk_on hOk hAg)))
    session_memcpy_region_ro := fun stk hlo hhi =>
      sessionMemcpyRO4K_of_withStack hlo hhi
        (stub_raw_of_hookSat_local b (by simp only [arm64_norm])
          (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memcpyName])
          (hookSat_sessionMemcpyRO4K_of_externsOk_on hOk hAg))
    memcpy_region := hM4.memcpy_region
    session_memcpy_region := hM4.session_memcpy_region
    memmove := hM4.memmove
    session_memmove := hM4.session_memmove
    memset := hM4.memset
    session_memset := hM4.session_memset
    memset_region := fun stk hlo hhi => stub_raw_of_hookSat_local b (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
      (hookSat_map (hAg.hookSat (by decide) hOk.memset) fun _ hh =>
        hookOk_memsetRegion_of_libc
          (hookOk_libcMemset_of_session (hookOk_sessionMemset_of_cliExt hh hlo hhi)))
    session_memset_region := fun stk hlo hhi => stub_raw_of_hookSat_local b (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
      (hookSat_map (hAg.hookSat (by decide) hOk.memset) fun _ hh =>
        hookOk_sessionMemsetRegion_of_session (hookOk_sessionMemset_of_cliExt hh hlo hhi)) }

theorem deallocOkExt_of_allocContracts4K {b : BitVec 64} {A : RustAlloc}
    {ext' : String → Option (State → State)} (hA : AllocContracts4K b A ext') :
    DeallocOkExt b A ext' :=
  hA.dealloc

/-! ## `StatesRecvContractsAx` & `<States>::recv` Top-Level Assembly -/

theorem statesRecvContractsAx_of_externsOk_on
    {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext')
    (himg : Obj.Loads libsignalSessionImage img) :
    StatesRecvContractsAx img A P.C.F P.Q.K ext' := by
  have hAx : AllocContractsX img A ext' := allocContractsX_of_externsOk_on hOk hAg img
  have hA4k : AllocContracts4K img.base A ext' := allocContracts4K_of_externsOk_on hOk hAg img.base
  have hdealloc : DeallocOkExt img.base A ext' := deallocOkExt_of_allocContracts4K hA4k
  have hAddChunk : AddChunkOkX img A ext' := add_chunk_ok_x_4k (img := img) hA4k
  have hshim : HookSat ext' shimName noAllocShimSpec := hAg.hookSat (by decide) hOk.shim
  have halloc : HookSat ext' allocName (rustAllocSpec A) := hAg.hookSat (by decide) hOk.alloc.alloc
  have hmc4k := hookSat_session2Memcpy4K_of_externsOk_on hOk hAg
  have hRO4k := hookSat_sessionMemcpyRO4K_of_externsOk_on hOk hAg
  have hhmac : HookSat ext' libcruxHmacName (libcruxHmacSpec P.C.F A) :=
    hAg.hookSat (by decide) hOk.spqr.hmac
  have hdecaps : HookSat ext' mlkemDecapsName (mlkemDecapsSpec P.Q.K) :=
    hAg.hookSat (by decide) hOk.spqr.decaps
  have hencaps2 : HookSat ext' mlkemEncaps2Name (mlkemEncaps2Spec P.Q.K) :=
    hAg.hookSat (by decide) hOk.spqr.encaps2
  have hvalPk : HookSat ext' mlkemValidatePkName (mlkemValidatePkSpec P.Q.K) :=
    hAg.hookSat (by decide) hOk.spqr.validatePk
  have hdecRaw := polyDecoderDecodedMessage_ok_inImage_4k (img := img) hA4k
  have hdecInImg := poly_decoder_decoded_message_ok_inImage hdecRaw
  have hdecOkX : PolyDecodedMessageOkX img A ext' :=
    polyDecodedMessageOkX_of_decodedMessage (img := img) (polyDecoderDecodedMessage_ok_4k hA4k)
  have hencBytesX := encode_bytes_ok_x_4k (img := img) hA4k
  have hencBytesExt := encode_bytes_ok_ext_4k hA4k
  have hconcat2 := sliceConcat2_ok_of_externsOk_on hOk hAg img
  have hconcat3 := sliceConcat3_ok_of_externsOk_on hOk hAg img
  have hhkdf := hkdf_to_slice_spqr_ok_of_hooks_ext img himg
    (SpqrKdfHooksExt.of_hookSat img P.C ext'
      (hAg.hookSat (by decide) hOk.compress256)
      (hAg.hookSat (by decide) hOk.memcpy)
      (hAg.hookSat (by decide) hOk.memcpyRO)
      (hAg.hookSat (by decide) hOk.memset))
  have hupdate := authUpdate_ok_of_externsOk_on hOk hAg img himg
  have hallocZeroed := allocZeroedWithStackOkX_of_hook (img := img) (hAg.hookSat (by decide) hOk.allocZeroed)
  have hres7 := do_reserve_7_ok_ext_x_4k (img := img) hA4k
  have hrecvEkInImg := unchunked_ct1_sent_recv_ek_ok_inImage (img := img) (F := P.C.F) hdealloc hvalPk
  have hsendCt2InImg := unchunked_ct1_sent_ek_received_send_ct2_ok_inImage_of_hooks
    (img := img) (F := P.C.F) (K := P.Q.K) hA4k hshim halloc hmc4k hRO4k hencaps2 hhmac
  have hsendCt2EncInImg := send_ct2_encoder_ok_inImage (img := img) hA4k hencBytesExt
  exact {
    keysSampledRecvCt1Chunk_ok :=
      keys_sampled_recv_ct1_chunk_ok_ax hAx hdealloc hAddChunk hencBytesX
    headerSentRecvCt1Chunk_ok :=
      header_sent_recv_ct1_chunk_ok_ax hAx hdealloc hAddChunk hdecInImg
    ct1ReceivedRecvCt2Chunk_ok :=
      ct1_received_recv_ct2_chunk_ok_ax hAx hdealloc hAddChunk
    ekSentCt1ReceivedRecvCt2Chunk_ok :=
      recv_ct2_chunk_ok_ext himg hAx hdealloc hallocZeroed hAddChunk hdecOkX
        hdecaps hconcat2 hconcat3 hhkdf hupdate hres7 hhmac
    noHeaderReceivedRecvHdrChunk_ok :=
      noHeaderReceived_recv_hdr_chunk_ok_ax himg hAx hdealloc hAddChunk hdecOkX hconcat3 hhmac
    polyAddChunk_ok := hAddChunk
    polyDecodedMessage_ok := poly_decoder_decoded_message_ok_ax hdecRaw
    unchunkedCt1SentRecvEk_ok :=
      unchunked_ct1_sent_recv_ek_ok_ax (img := img) hdealloc hvalPk
    unchunkedCt1SentEkReceivedSendCt2_ok :=
      unchunked_ct1_sent_ek_received_send_ct2_ok_ax_of_hooks
        (img := img) hA4k hshim halloc hmc4k hRO4k hencaps2 hhmac
    sendCt2Encoder_ok :=
      send_ct2_encoder_ok_ax (img := img) hA4k hencBytesExt
    ekReceivedCt1SampledRecvCt1Ack_ok :=
      ek_received_ct1_sampled_recv_ct1_ack_ok_ax hdealloc hsendCt2InImg hsendCt2EncInImg
    ct1AcknowledgedRecvEkChunk_ok :=
      ct1_acknowledged_recv_ek_chunk_ok_ax hAx hdealloc hAddChunk hdecInImg
        hrecvEkInImg hsendCt2InImg hsendCt2EncInImg
    ct2SampledRecvNextEpoch_ok :=
      ct2_sampled_recv_next_epoch_ok_ax (img := img) hdealloc
  }

theorem statesRecv_ok_x_of_contractsExt
    {img : Obj.Image} {A : RustAlloc} {F : CryptoGames.LibsignalSession.ShaCompress}
    {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext)
    (hC : StatesRecvContractsExt img A F K ext) :
    StatesRecvOkXExt img A F K ext :=
  states_recv_ok_x_ext_ax_full hAx hdealloc hC.toAx

/-- `<States>::recv` satisfies `StatesRecvOkXExt` on any `ext'` agreeing with `ext` on
`cliHookNames` under `CliExternsOk P A ext` and `Obj.Loads libsignalSessionImage img`. -/
theorem statesRecv_ok_x_of_externsOk_on
    {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext')
    (himg : Obj.Loads libsignalSessionImage img) :
    StatesRecvOkXExt img A P.C.F P.Q.K ext' :=
  states_recv_ok_x_ext_ax_full
    (allocContractsX_of_externsOk_on hOk hAg img)
    (deallocOkExt_of_allocContracts4K (allocContracts4K_of_externsOk_on hOk hAg img.base))
    (statesRecvContractsAx_of_externsOk_on hOk hAg himg)

/-- Direct CLI instantiation of `<States>::recv` on `cliExternsWith ext`: matches the
`hStatesRecv` parameter of `MainInstW2W4Ext.spqrRecvContractsAll_of_leaves` and
`SpqrRecvCliExt`. -/
theorem statesRecv_ok_x_cli_ext
    {img : Obj.Image} (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    StatesRecvOkXExt img A P.C.F P.Q.K (cliExternsWith ext) :=
  statesRecv_ok_x_of_externsOk_on hOk (AgreeOnCliHooks.cliExternsWith ext) himg

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ContractsAxExt

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SpqrV1.States.Recv
export LibsignalBinary.Proofs.SpqrV1.States.Recv.ContractsAxExt (
  allocContracts4K_of_externsOk_on
  deallocOkExt_of_allocContracts4K
  statesRecvContractsAx_of_externsOk_on
  statesRecv_ok_x_of_contractsExt
  statesRecv_ok_x_of_externsOk_on
  statesRecv_ok_x_cli_ext
)
end CryptoVerification.SpqrV1.States.Recv
-- AUTO-BRIDGE END
