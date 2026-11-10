/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled2PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled3Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled3
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `.keysUnsampled` Arm (Part 3: `+2588..+3068` & Full Arm, Block `427`)

Threads `RustCliAllocBudget` through `PolyEncoder` chunking, `mac` / `hdr` deallocation,
and the complete `.keysUnsampled` arm (`+372 -> +3068`) in Block `427`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled3PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsLogFilterAddr lsmpl lsρ)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrCoinsAfterPlaced spqrCoinsAtPlaced
   spqrMlkemFromSeedSym spqrMlkemPk1Sym spqrMlkemPk2Sym)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes Chunk MlKem PolyEncoder
   mlkemFromSeedSpec mlkemPk1Spec mlkemPk2Spec spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (KeysSampled KeysUnsampled)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack vecU8Buf)
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm
  (readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Auth (AuthenticatorGhost authenticatorPinAt)
open CryptoVerification.SpqrV1.Drop (chunkedKeysSampledAt chunkedStatesAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt chunkSize polyEncoderAt polyEncoderSize resultPolyEncoderAt)
open CryptoVerification.SpqrV1.Poly.ComputeAt (spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Poly.EncodeBytes
  (EncodeBytesGhost bytesAt encodeBytesResult encodeBytesStackX)
open CryptoVerification.SpqrV1.Poly.NextChunk (PolyNextChunkGhost polyNextChunkStack)
open CryptoVerification.SpqrV1.States.Leaves (Relocatable polyEncoderAt_split_tag)
open CryptoVerification.SpqrV1.Top.Send
  (authHeapBufs authInlineWordsAt authInlineWordsAt_352_entails_memRegion_400
   authenticatorAt_entails_exists_inline_heap chunkAt_5208_4192_1360_eq
   chunkAt_and_470_entails_memRegion_504 chunkAt_entails_memRegion chunkAt_extract_words
   chunkedStatesAt_keysUnsampled_unfold chunkedStatesTail920At
   chunkedStatesTail920At_keysSampled_eq ekSentInlineWordsAt ekSentInlineWordsAt_entails_memRegion
   fold_chunkedKeysSampledAt hdr_mac_len_96 keysUnsampled_src_entails_memRegion_928
   macHdrUnchecked_length memRegion_104_eq_words13 memRegion_38_eq_chunk_slot
   memRegion_4704_2400_split_nextChunk memRegion_504_expose_chunk_slot
   pointsToBytes_and_tail_entails_memRegion send_hdr_chunk_ok_elim spqrSendCalleeStack
   spqrSendKeySlotAt spqrSendPayloadSlotAt stackAt_spqrSendCallee_from_allocHook
   stackAt_spqrSendCallee_to_allocHook sub_drop_64_len take_64_len words3_7104_entails_memRegion)
open CryptoVerification.SpqrV1.Top.Send.Relocatable (of_chunkedKeysSampledAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget SeqEnv VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced CoinsFillPlacedOkX EncodeBytesPlacedOkX PolyNextChunkPlacedOkX
   spqrLogLevelZeroPlacedAt spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget
  (KeysUnsampledAllocEnv keysUnsampledAllocEvents
   step_keysUnsampled_372_to_512_placed step_keysUnsampled_512_to_684_sepWP_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled2PlacedBudget
  (KeysUnsampledMacReserveEnv keysUnsampledMacReserveEvents
   step_keysUnsampled_684_to_2588_sepWP_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
  (AuthMacHdrPinnedPlacedOkX DoReserve2PlacedOkX)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget.KeysUnsampledHelpers
  (SpqrSendJoinStatePlaced call_lscro_calleeStack_evs_sepWP call_lscro_calleeStack_sepWP
   finish_sepWP_lscro_plain of_sepWP_lscro_plain spqrSend_dealloc_ok_placed
   spqrSend_session_memcpy_region_ok_placed)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv encodeBytesAllocEvents encodeBytesSpecX encodeBytesSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
  (PolyNextChunkEnv polyNextChunkEnv_nonempty polyNextChunkPlacedSpec polyNextChunkPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
  (call_memcpy_relocate_cs_budget call_rustDealloc_budget)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

variable [LibsignalPlacement]

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

run_cmd Lean.Elab.Command.liftCoreM do
  for nm in [
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  ] do
    Lean.Attribute.erase nm `arm64_norm

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. Allocator Event Sequences & Envelopes (`+2588 -> +3068` and Full `.keysUnsampled` Arm) -/

/-- Address-independent `PolyNextChunkGhost` witness for `PolyNextChunkEnv` (which depends only
    on `.enc`). -/
def polyNextChunkGhostOf (enc enc' : PolyEncoder) (chunk : Chunk) : PolyNextChunkGhost :=
  { outA := 0, encA := 0, enc := enc, enc' := enc', chunk := chunk }

theorem polyNextChunkEnv_eq_ghostOf (x : PolyNextChunkGhost) :
    PolyNextChunkEnv x = PolyNextChunkEnv (polyNextChunkGhostOf x.enc x.enc' x.chunk) :=
  rfl

/-- Exact deallocation event list emitted by `.keysUnsampled` tail (`+2776..+2836`):
    `__rust_dealloc(mac_ptr, macCap, 1)` followed by `__rust_dealloc(hdr_ptr', 128, 1)`. -/
def keysUnsampledDeallocEvents (macCap : Nat) : List AllocEvent :=
  rustDeallocEvents macCap 1 ++ rustDeallocEvents 128 1

private theorem freeOnlyEvs_rustDealloc (n al : Nat) :
    FreeOnlyEvs (rustDeallocEvents n al) := by
  intro ev hmem
  unfold rustDeallocEvents at hmem
  simp only [List.mem_singleton] at hmem
  exact ⟨_, _, hmem⟩

theorem keysUnsampledDeallocEvents_freeOnly (macCap : Nat) :
    FreeOnlyEvs (keysUnsampledDeallocEvents macCap) := by
  intro ev hmem
  rcases List.mem_append.mp hmem with h | h
  · exact freeOnlyEvs_rustDealloc macCap 1 ev h
  · exact freeOnlyEvs_rustDealloc 128 1 ev h

/-- Allocator event envelope of `.keysUnsampled` sub-step 2 (`+2588 -> +3068`):
    `PolyEncoder::encode_bytes` on the 96-byte `hdr ++ mac` buffer, followed by
    `PolyEncoder::next_chunk`, followed by `FreeOnlyEvs` (`mac_ptr` and `hdr_ptr'`). -/
def KeysUnsampledTailEnv (sending_hdr out_hdr : PolyEncoder) (chunk : Chunk) :
    List AllocEvent → Prop :=
  SeqEnv (EncodeBytesEnv 96)
    (SeqEnv (PolyNextChunkEnv (polyNextChunkGhostOf sending_hdr out_hdr chunk)) FreeOnlyEvs)

theorem keysUnsampledTailEnv_nonempty (sending_hdr out_hdr : PolyEncoder) (chunk : Chunk) :
    ∃ evs, KeysUnsampledTailEnv sending_hdr out_hdr chunk evs :=
  ⟨encodeBytesAllocEvents 96, SeqEnv.inl rfl⟩

theorem keysUnsampledTailEnv_of_nextChunk {sending_hdr out_hdr : PolyEncoder} {chunk : Chunk}
    {evs_nc : List AllocEvent} (macCap : Nat)
    (hnc_evs : PolyNextChunkEnv (polyNextChunkGhostOf sending_hdr out_hdr chunk) evs_nc) :
    KeysUnsampledTailEnv sending_hdr out_hdr chunk
      (encodeBytesAllocEvents 96 ++ (evs_nc ++ keysUnsampledDeallocEvents macCap)) :=
  SeqEnv.append rfl (SeqEnv.append hnc_evs (keysUnsampledDeallocEvents_freeOnly macCap))

/-- Seed vector extracted from `tape` when `64 ≤ tape.length` (0-filled fallback otherwise). -/
def keysUnsampledSeed (tape : Bytes) : List.Vector (BitVec 8) 64 :=
  if h : 64 ≤ tape.length then ⟨tape.take 64, take_64_len h⟩
  else List.Vector.replicate 64 0#8

/-- Deterministic 64-byte ML-KEM header slice derived from `tape`. -/
def keysUnsampledHdr (K : MlKem) (tape : Bytes) : Bytes :=
  (K.fromSeed (keysUnsampledSeed tape)).1.toList

/-- Deterministic 32-byte HMAC tag over `keysUnsampledHdr K tape`. -/
def keysUnsampledMac (F : ShaCompress) (K : MlKem) (auth : Authenticator)
    (epoch : BitVec 64) (tape : Bytes) : Bytes :=
  auth.macHdrUnchecked F epoch (keysUnsampledHdr K tape)

/-- Full allocator event envelope of the inlined `States::send` `.keysUnsampled` arm (`372..3068`):
    sequences `KeysUnsampledAllocEnv` (`+512..+684`), `KeysUnsampledMacReserveEnv` (`+684..+2588`),
    and `KeysUnsampledTailEnv` (`+2588..+3068`) when `encodeBytesResult` succeeds (`evs = []` on the
    unreachable error arm). -/
def KeysUnsampledArmEnv (F : ShaCompress) (K : MlKem)
    (st : KeysUnsampled (spqrAuthApi F))
    (out_hdr : PolyEncoder) (chunk : Chunk) (tape : Bytes)
    (evs : List AllocEvent) : Prop :=
  match encodeBytesResult (keysUnsampledHdr K tape ++
      keysUnsampledMac F K st.uc.auth st.uc.epoch tape) with
  | .ok sending_hdr =>
    SeqEnv KeysUnsampledAllocEnv
      (SeqEnv (KeysUnsampledMacReserveEnv st.uc.auth (keysUnsampledHdr K tape))
        (KeysUnsampledTailEnv sending_hdr out_hdr chunk)) evs
  | .error _ => evs = []

theorem keysUnsampledArmEnv_nonempty (F : ShaCompress) (K : MlKem)
    (st : KeysUnsampled (spqrAuthApi F))
    (out_hdr : PolyEncoder) (chunk : Chunk) (tape : Bytes) :
    ∃ evs, KeysUnsampledArmEnv F K st out_hdr chunk tape evs := by
  unfold KeysUnsampledArmEnv
  split
  · exact ⟨keysUnsampledAllocEvents, SeqEnv.inl rfl⟩
  · exact ⟨[], rfl⟩

/-! ## 2. Private Call Wrappers with Explicit Pool-State Transport -/

private theorem call_encodeBytes_lscro
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret_pc tgt : BitVec 64}
    (henc_at : subroutine_ok prog (lsmpl.base 417)
      (withLsCodeRoLoaded lsmpl (encodeBytesSpecX A lim)))
    (sp out msgA : BitVec 64) (msg : Bytes) (sending_hdr : PolyEncoder) (st : M.σ)
    (hlen : msg.length < 2 ^ 64)
    (hfit : FitsEnv M lim st (EncodeBytesEnv msg.length))
    (henc_res : encodeBytesResult msg = .ok sending_hdr)
    {s0 s_pool s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 417) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx8 : s.readReg64 .x8 = out)
    (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 msg.length)
    (hpool : A.pool lim st s_pool = A.pool lim st s)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗
      memRegion out polyEncoderSize ∗ (msgA ↦ₛ msg) ∗ A.pool lim st s_pool) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP prog tgt sf
        ((stackAt sp spqrSendCalleeStack ∗
          polyEncoderAt A.repAlloc out sending_hdr ∗
          (msgA ↦ₛ msg) ∗
          A.pool lim (M.stepEvents (encodeBytesAllocEvents msg.length) st) sf) ∗ F) Q) :
    SepWP prog tgt s P Q := by
  let x : EncodeBytesGhost := { out := out, msgRO := false, msgA := msgA, msg := msg }
  rw [hpool] at hP
  refine call_lscro_calleeStack_sepWP (x := (x, st)) sp encodeBytesStackX (by decide)
    (T_pre := memRegion out polyEncoderSize ∗ (msgA ↦ₛ msg) ∗ A.pool lim st s)
    (T_post := fun sf => polyEncoderAt A.repAlloc out sending_hdr ∗ (msgA ↦ₛ msg) ∗
      (∃∗ evs : List AllocEvent, ⌜EncodeBytesEnv msg.length evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf))
    (F := F)
    (φ_pre := s.readReg64 .x8 = out ∧ s.readReg64 .x0 = msgA ∧
      s.readReg64 .x1 = BitVec.ofNat 64 msg.length ∧
      msg.length < 2 ^ 64 ∧ FitsEnv M lim st (EncodeBytesEnv msg.length))
    (φ_post := fun sf => sf.trace = s.trace)
    henc_at hcrl hpc hrun hsp hsp_align hlr
    (by dsimp only [encodeBytesSpecX, encodeBytesSpecXOfEnv, bytesAt, x]
        simp only [Bool.false_eq_true, ↓reduceIte]
        sep_ac_rfl)
    ⟨hx8, hx0, hx1, hlen, hfit⟩
    hP
    (fun _ _ => rfl)
    (fun _ => Entails.refl _)
    (by intro sf
        dsimp only [encodeBytesSpecX, encodeBytesSpecXOfEnv, bytesAt, x]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [henc_res, resultPolyEncoderAt]
        sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hcrl_sf
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro evs
  have hpull :
      ((stackAt sp spqrSendCalleeStack ∗
        (polyEncoderAt A.repAlloc out sending_hdr ∗ (msgA ↦ₛ msg) ∗
         (⌜EncodeBytesEnv msg.length evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf))) ∗ F) =
      ⌜EncodeBytesEnv msg.length evs⌝ ∗
        ((stackAt sp spqrSendCalleeStack ∗
          polyEncoderAt A.repAlloc out sending_hdr ∗
          (msgA ↦ₛ msg) ∗
          A.pool lim (M.stepEvents evs st) sf) ∗ F) := by sep_ac_rfl
  rw [hpull]
  refine SepWP.pure_elim fun hevs => ?_
  unfold EncodeBytesEnv at hevs
  subst hevs
  exact hnext sf hpc_sf hrun_sf hsp_sf (htr_sf.trans htr) hcrl_sf
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs

private theorem call_polyNextChunk_lscro
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret_pc tgt : BitVec 64}
    (hnc_at : subroutine_ok prog (lsmpl.base 416)
      (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec M A lim)))
    (sp outA encA : BitVec 64) (enc enc' : PolyEncoder) (chunk : Chunk) (st : M.σ)
    (hnc : enc.nextChunk = .ok (enc', chunk))
    (hfit : FitsEnv M lim st (PolyNextChunkEnv (polyNextChunkGhostOf enc enc' chunk)))
    {s0 s_pool s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 416) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx8 : s.readReg64 .x8 = outA)
    (hx0 : s.readReg64 .x0 = encA)
    (hpool : A.pool lim st s_pool = A.pool lim st s)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗
      memRegion outA chunkSize ∗ polyEncoderAt A.repAlloc encA enc ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st s_pool) ∗ F)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      PolyNextChunkEnv (polyNextChunkGhostOf enc enc' chunk) evs →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP prog tgt sf
        ((stackAt sp spqrSendCalleeStack ∗
          polyEncoderAt A.repAlloc encA enc' ∗
          chunkAt outA chunk ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf) ∗ F) Q) :
    SepWP prog tgt s P Q := by
  let x : PolyNextChunkGhost := { outA := outA, encA := encA, enc := enc, enc' := enc', chunk := chunk }
  rw [hpool] at hP
  refine call_lscro_calleeStack_evs_sepWP (x := (x, st)) sp polyNextChunkStack (by decide)
    (T_pre := memRegion outA chunkSize ∗ polyEncoderAt A.repAlloc encA enc ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st s)
    (T_post := fun evs sf => polyEncoderAt A.repAlloc encA enc' ∗ chunkAt outA chunk ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf)
    (F := F)
    (φ_pre := s.readReg64 .x8 = outA ∧ s.readReg64 .x0 = encA ∧
      enc.nextChunk = .ok (enc', chunk) ∧ FitsEnv M lim st (PolyNextChunkEnv x))
    (φ_post := fun evs sf => PolyNextChunkEnv x evs ∧ sf.trace = s.trace)
    hnc_at hcrl hpc hrun hsp hsp_align hlr
    (by dsimp only [polyNextChunkPlacedSpec, polyNextChunkPlacedSpecOfEnv, x]; sep_ac_rfl)
    ⟨hx8, hx0, hnc, hfit⟩
    hP
    (fun _ _ => rfl)
    (fun _ => Entails.refl _)
    (by intro sf
        dsimp only [polyNextChunkPlacedSpec, polyNextChunkPlacedSpecOfEnv, x]
        apply congrArg SepProp.sepExists; funext evs
        sep_ac_rfl) ?_
  intro sf evs hpc_sf hrun_sf hsp_sf ⟨hevs, htr_sf⟩ hcrl_sf
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs
  exact hnext sf evs hevs hpc_sf hrun_sf hsp_sf (htr_sf.trans htr) hcrl_sf
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs

private theorem call_memcpy_relocate_pool
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionBudgetSpec)
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64) (st : M.σ)
    {s0 s_pool s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hpool : A.pool lim st s_pool = A.pool lim st s)
    (hsplit : P = (memRegion dst n ∗ F src ∗ A.pool lim st s_pool) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n ∗ A.pool lim st sf) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hpool] at hsplit
  refine call_memcpy_relocate_cs_budget hcall hrel dst src st
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hsplit ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf
  rcases hcs_sf with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
  exact hnext sf hpc_sf hrun_sf hsp_sf htr_sf
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs

private theorem call_dealloc_pool
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim))
    (p : BitVec 64) (size align : Nat) (st : M.σ)
    {s0 s_pool s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hpool : A.pool lim st s_pool = A.pool lim st s)
    (hsplit : P = (A.pool lim st s_pool ∗ A.live p size align ∗
      memRegion p size ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP prog target_pc sf
        ((A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗
          stackAt sp_call allocHookStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP prog target_pc s P post := by
  rw [hpool] at hsplit
  refine call_rustDealloc_budget hcall p size align st
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hsplit ?_ hlr_ls
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf
  rcases hcs_sf with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, _, hvregs⟩
  exact hnext sf hpc_sf hrun_sf hsp_sf htr_sf
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs

private theorem seq_vm_plain {prog : Program} {mid tgt : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP prog tgt sm P_mid post) :
    SepWP prog tgt s P post :=
  SepWP.seq h1 fun sm _ hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem seq_vm_framed {prog : Program} {mid tgt : BitVec 64} {s : State}
    {P P₀ P₀' F : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hsplit : P = P₀ ∗ F)
    (h1 : SepWP prog mid s P₀ (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P₀') ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP prog tgt sm (P₀' ∗ F) post) :
    SepWP prog tgt s P post := by
  rw [hsplit]
  have hf : SepWP prog mid s (P₀ ∗ F)
      (fun sm Pm => (Pm ⊢ P₀' ∗ F) ∧ (VmPreserved s sm ∧ Q sm)) := by
    unfold SepWP at h1 ⊢
    intro R hm
    rw [sepConj_assoc] at hm
    refine reaches_pc_mono (h1 (F ∗ R) hm) ?_ (fun _ _ ho => Satisfies.drop_mid ho)
    intro sm _ _ ⟨Pm, hmf, hvm, hent, hQ⟩
    exact ⟨Pm ∗ F, by rw [sepConj_assoc]; exact hmf, sepConj_mono_left hent, hvm, hQ⟩
  exact SepWP.seq hf fun sm _ hpc hrun ⟨hent, hvm, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

/-! ## 3. Budget-Threaded Relocatable Sub-Step 2 (`+2588 -> +3068`) -/

set_option maxHeartbeats 1600000 in
/-- Non-panicking `SepWP` form of relocatable `.keysUnsampled` sub-step 2
    (`spqrSendPlacedEntry + 2588#64 -> spqrSendPlacedEntry + 3068#64`). -/
theorem step_keysUnsampled_2588_to_3068_sepWP_placed {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {K : MlKem} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (henc_call : EncodeBytesPlacedOkX A lim ext)
    (hnc_call : PolyNextChunkPlacedOkX M A lim ext)
    (sp epoch hdr_ptr' ek_ptr dk_ptr mac_cap mac_ptr : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (seed : List.Vector (BitVec 8) 64)
    (mac : Bytes)
    (sending_hdr : PolyEncoder)
    (outSt : KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hmac_len : mac.length = 32)
    (henc_res : encodeBytesResult ((K.fromSeed seed).1.toList ++ mac) = .ok sending_hdr)
    (hnc : sending_hdr.nextChunk = .ok (outSt.sending_hdr, chunk))
    (huc : outSt.uc = { epoch := epoch, auth := auth,
                        ek := (K.fromSeed seed).2.1.toList, dk := (K.fromSeed seed).2.2.toList })
    (_hhdr_ne : hdr_ptr' ≠ 0)
    (_hmac_ne : mac_ptr ≠ 0)
    (hmac_cap_b : (mac_cap == 0#64) = false)
    (hmac_cap_ge : 32 ≤ mac_cap.toNat)
    (_hmac_cap_lt : mac_cap.toNat < 2 ^ 63)
    (st : M.σ)
    (hfit : FitsEnv M lim st (KeysUnsampledTailEnv sending_hdr outSt.sending_hdr chunk))
    {tgt : BitVec 64} {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 2588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = mac_cap)
    (hx21 : s.readReg64 .x21 = mac_ptr)
    (hx22 : s.readReg64 .x22 = epoch)
    (hx23 : s.readReg64 .x23 = hdr_ptr')
    (hx24 : s.readReg64 .x24 = 64#64)
    (hx25 : s.readReg64 .x25 = 32#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 7136#64) auth ∗
      memRegion (sp + 7184#64) 352 ∗
      memRegion (sp + 7536#64) 400 ∗
      memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 1360#64) 38 ∗
      memRegion (sp + 1424#64) 504 ∗
      ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
      authHeapBufs A.repAlloc g auth ∗
      ((sp + 7104#64) ↦₆₄ 128#64) ∗
      ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗
      ((sp + 7120#64) ↦₆₄ 64#64) ∗
      A.live hdr_ptr' 128 1 ∗
      (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
      memRegion (hdr_ptr' + 96#64) 32 ∗
      A.live mac_ptr mac_cap.toNat 1 ∗
      (mac_ptr ↦ₛ mac) ∗
      memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
      vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
      vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗
      A.pool lim st s ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs_tail : List AllocEvent),
      KeysUnsampledTailEnv sending_hdr outSt.sending_hdr chunk evs_tail →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = spqrSendPlacedEntry + 3068#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = 3#64 →
      sf.readReg64 .x21 = noneCap →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x24 = 1#64 →
      sf.readReg64 .x25 = sp + 1360#64 →
      sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (spqrSendPlacedProg ext) tgt sf
        ((chunkedKeysSampledAt A.repAlloc (sp + 1424#64) outSt ∗
          chunkAt (sp + 1360#64) chunk ∗
          memRegion (sp + 1394#64) 4 ∗
          memRegion (sp + 3552#64) 504 ∗
          memRegion (sp + 4080#64) 104 ∗
          memRegion (sp + 4192#64) 504 ∗
          memRegion (sp + 4704#64) 2400 ∗
          memRegion (sp + 7104#64) 24 ∗
          memRegion (sp + 7136#64) 400 ∗
          memRegion (sp + 7536#64) 400 ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗
          A.pool lim (M.stepEvents evs_tail st) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  have henc_at : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 417)
      (withLsCodeRoLoaded lsmpl (encodeBytesSpecX A lim)) := henc_call
  have hnc_at : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 416)
      (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec M A lim)) := hnc_call
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hdealloc := spqrSend_dealloc_ok_placed hA
  have h96 : ((K.fromSeed seed).1.toList ++ mac).length = 96 := hdr_mac_len_96 K seed hmac_len
  have hek_len : (K.fromSeed seed).2.1.toList.length = 1152 := List.Vector.toList_length _
  have hdk_len : (K.fromSeed seed).2.2.toList.length = 2400 := List.Vector.toList_length _
  have hfit_enc : FitsEnv M lim st (EncodeBytesEnv ((K.fromSeed seed).1.toList ++ mac).length) := by
    rw [h96]; exact hfit.seq_left
  let st1 : M.σ := M.stepEvents (encodeBytesAllocEvents ((K.fromSeed seed).1.toList ++ mac).length) st
  have hfit_nc : FitsEnv M lim st1
      (PolyNextChunkEnv (polyNextChunkGhostOf sending_hdr outSt.sending_hdr chunk)) := by
    dsimp only [st1]
    rw [h96]
    exact (hfit.seq_right (rfl : EncodeBytesEnv 96 (encodeBytesAllocEvents 96))).seq_left
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat]
    at hpc henc_at hnc_at hmemcpy hdealloc hnext ⊢
  subst hP
  simp only [Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26]
    at hx20 hx21 hx22 hx23 hx24 hx25 hx26
  apply of_sepWP_lscro_plain (mid := lsmpl.base 417) hinv
  have hfold_7136 := authInlineWordsAt_352_entails_memRegion_400 g (sp + 7136#64) auth
  rw [show (sp + 7136#64) + 48#64 = sp + 7184#64 by rw [BitVec.add_assoc]; rfl] at hfold_7136
  refine SepWP.fold hfold_7136 (by sep_focus) ?_
  clear hfold_7136
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro hinv_1
  refine call_encodeBytes_lscro henc_at sp (sp + 7136#64) hdr_ptr'
    ((K.fromSeed seed).1.toList ++ mac) sending_hdr st
    (by rw [h96]; decide) hfit_enc henc_res
    (s0 := s0) (s_pool := s)
    (F := memRegion (sp + 7536#64) 400 ∗ memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1424#64) 504 ∗
      ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
      authHeapBufs A.repAlloc g auth ∗
      ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
      A.live hdr_ptr' 128 1 ∗ memRegion (hdr_ptr' + 96#64) 32 ∗
      A.live mac_ptr mac_cap.toNat 1 ∗ (mac_ptr ↦ₛ mac) ∗
      memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
      vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
      vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗ Frame)
    hinv_1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
    hsp_align (by simp only [wp_norm, arm64_norm, *])
    (ret_pc := (blkPl_427).base + 2608#64) (by simp only [Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [Reg.x8, wp_norm, arm64_norm, *])
    (by simp only [Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [h96, Reg.x1, BitVec.ofNat_eq_ofNat, wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm])
    (by dsimp only [polyEncoderSize]; sep_ac_rfl) ?_
  intro sm1 hpc_sm1 hrun_sm1 hsp_sm1 htr_sm1 hinv_sm1
    hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 _ _ hx26_sm1 _ hx28_sm1 hvregs_sm1
  simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x26, Reg.x28,
    wp_norm, arm64_norm, *] at hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx26_sm1 hx28_sm1 hvregs_sm1
  apply of_sepWP_lscro_plain (mid := lsmpl.base 416) hinv_sm1
  have h2640 : ∀ s_m : State,
      s_m.pc = lsρ "memcpy" → s_m.status = .Running → s_m.sp = sp → s_m.trace = s0.trace →
      s_m.readReg64 Reg.lr = (blkPl_427).base + 2644#64 →
      s_m.readReg64 Reg.x0 = sp + 7536#64 → s_m.readReg64 Reg.x1 = sp + 7136#64 →
      (s_m.readReg64 Reg.x2).toNat = 400 →
      s_m.readReg64 .x19 = s.readReg64 .x19 → s_m.readReg64 .x20 = mac_cap →
      s_m.readReg64 .x21 = mac_ptr → s_m.readReg64 .x22 = epoch →
      s_m.readReg64 .x23 = hdr_ptr' → s_m.readReg64 .x26 = sp + 4704#64 →
      s_m.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs s_m = calleeSavedVRegs s →
      A.pool lim st1 sm1 = A.pool lim st1 s_m →
      SepWP ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext)) (lsmpl.base 416) s_m
        ((stackAt sp spqrSendCalleeStack ∗
          polyEncoderAt A.repAlloc (sp + 7136#64) sending_hdr ∗
          (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
          A.pool lim st1 sm1) ∗
         (memRegion (sp + 7536#64) 400 ∗ memRegion (sp + 3552#64) 504 ∗
          memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 4704#64) 2400 ∗
          memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1424#64) 504 ∗
          ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
          authHeapBufs A.repAlloc g auth ∗
          ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
          A.live hdr_ptr' 128 1 ∗ memRegion (hdr_ptr' + 96#64) 32 ∗
          A.live mac_ptr mac_cap.toNat 1 ∗ (mac_ptr ↦ₛ mac) ∗
          memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
          vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
          vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗ Frame))
        (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem →
          SepWP ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext)) tgt sm Pm post) := by
    intro s_m hpcm hrunm hspm htrm hlrm hx0m hx1m hx2m hx19m hx20m hx21m hx22m hx23m hx26m hx28m hvregsm hpoolm
    refine call_memcpy_relocate_pool hmemcpy (Relocatable.of_polyEncoderAt A.repAlloc sending_hdr)
      (sp + 7536#64) (sp + 7136#64) st1 (s0 := s0) (s_pool := sm1) (sp_call := sp)
      (Frame := stackAt sp spqrSendCalleeStack ∗
        (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
        memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 4192#64) 504 ∗
        memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 1360#64) 38 ∗
        memRegion (sp + 1424#64) 504 ∗
        ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
        authHeapBufs A.repAlloc g auth ∗
        ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
        A.live hdr_ptr' 128 1 ∗ memRegion (hdr_ptr' + 96#64) 32 ∗
        A.live mac_ptr mac_cap.toNat 1 ∗ (mac_ptr ↦ₛ mac) ∗
        memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
        vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
        vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗ Frame)
      hpcm hrunm hspm hsp_align hlrm htrm hx0m hx1m hx2m hpoolm
      (by sep_ac_rfl) ?_
    intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 htr_sf1 hx19_sf1 hx20_sf1 hx21_sf1 hx22_sf1 hx23_sf1 _ _ hx26_sf1 _ hx28_sf1 hvregs_sf1
    simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x26, Reg.x28,
      wp_norm, arm64_norm, *] at hx19_sf1 hx20_sf1 hx21_sf1 hx22_sf1 hx23_sf1 hx26_sf1 hx28_sf1 hvregs_sf1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro hinv_2
    rw [memRegion_4704_2400_split_nextChunk sp]
    refine call_polyNextChunk_lscro hnc_at sp (sp + 5208#64) (sp + 7536#64)
      sending_hdr outSt.sending_hdr chunk st1 hnc hfit_nc
      (s0 := s0) (s_pool := sf1)
      (F := memRegion (sp + 7136#64) 400 ∗
        (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
        memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 4192#64) 504 ∗
        memRegion (sp + 4704#64) 504 ∗ memRegion (sp + 5242#64) 1862 ∗
        memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1424#64) 504 ∗
        ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
        authHeapBufs A.repAlloc g auth ∗
        ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
        A.live hdr_ptr' 128 1 ∗ memRegion (hdr_ptr' + 96#64) 32 ∗
        A.live mac_ptr mac_cap.toNat 1 ∗ (mac_ptr ↦ₛ mac) ∗
        memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
        vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
        vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
        spqrLogLevelZeroPlacedAt ∗ Frame)
      hinv_2
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
      hsp_align (by simp only [wp_norm, arm64_norm, *])
      (ret_pc := (blkPl_427).base + 2672#64) (by simp only [Reg.lr, wp_norm, arm64_norm, *])
      (by simp only [Reg.x8, wp_norm, arm64_norm, *])
      (by simp only [Reg.x0, wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm])
      (by dsimp only [polyEncoderSize, chunkSize]; sep_ac_rfl) ?_
    intro sm2 evs_nc hnc_evs hpc_sm2 hrun_sm2 hsp_sm2 htr_sm2 hinv_sm2
      hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 _ hx26_sm2 _ hx28_sm2 hvregs_sm2
    simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x26, Reg.x28,
      wp_norm, arm64_norm, *] at hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx26_sm2 hx28_sm2 hvregs_sm2
    let st2 : M.σ := M.stepEvents evs_nc st1
    apply of_sepWP_lscro_plain (mid := (blkPl_427).base + 3068#64) hinv_sm2
    rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 400) (k := 104) (b' := sp + 4592#64)
      rfl (by rw [BitVec.add_assoc]; rfl) (by decide)]
    wp_steps
    refine call_memcpy_relocate_pool hmemcpy (Relocatable.of_polyEncoderAt A.repAlloc outSt.sending_hdr)
      (sp + 4192#64) (sp + 7536#64) st2 (s0 := s0) (s_pool := sm2) (sp_call := sp)
      (Frame := stackAt sp spqrSendCalleeStack ∗
        chunkAt (sp + 5208#64) chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 7136#64) 400 ∗
        (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
        memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 4592#64) 104 ∗
        memRegion (sp + 4704#64) 504 ∗ memRegion (sp + 5242#64) 1862 ∗
        memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1424#64) 504 ∗
        ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
        authHeapBufs A.repAlloc g auth ∗
        ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
        A.live hdr_ptr' 128 1 ∗ memRegion (hdr_ptr' + 96#64) 32 ∗
        A.live mac_ptr mac_cap.toNat 1 ∗ (mac_ptr ↦ₛ mac) ∗
        memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
        vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
        vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
        spqrLogLevelZeroPlacedAt ∗ Frame)
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
      hsp_align (ret_pc := (blkPl_427).base + 2696#64) (by simp only [Reg.lr, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by sep_ac_rfl) ?_
    intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 htr_sf2 hx19_sf2 hx20_sf2 hx21_sf2 hx22_sf2 hx23_sf2 hx24_sf2 _ hx26_sf2 _ hx28_sf2 hvregs_sf2
    simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x26, Reg.x28,
      wp_norm, arm64_norm, *] at hx19_sf2 hx20_sf2 hx21_sf2 hx22_sf2 hx23_sf2 hx24_sf2 hx26_sf2 hx28_sf2 hvregs_sf2
    have hfold_ks :
        polyEncoderAt A.repAlloc (sp + 4192#64) outSt.sending_hdr ∗
        (((sp + 4592#64) ↦₆₄ g.rootKey.cap) ∗ ((sp + 4600#64) ↦₆₄ g.rootKey.ptr) ∗
         ((sp + 4608#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((sp + 4616#64) ↦₆₄ g.macKey.cap) ∗ ((sp + 4624#64) ↦₆₄ g.macKey.ptr) ∗
         ((sp + 4632#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
         ((sp + 4640#64) ↦₆₄ 1152#64) ∗ ((sp + 4648#64) ↦₆₄ ek_ptr) ∗ ((sp + 4656#64) ↦₆₄ 1152#64) ∗
         ((sp + 4664#64) ↦₆₄ 2400#64) ∗ ((sp + 4672#64) ↦₆₄ dk_ptr) ∗ ((sp + 4680#64) ↦₆₄ 2400#64) ∗
         ((sp + 4688#64) ↦₆₄ epoch)) ∗
        authHeapBufs A.repAlloc g auth ∗
        vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
        vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
        (((sp + 4080#64) ↦₆₄ g.rootKey.cap) ∗ ((sp + 4088#64) ↦₆₄ g.rootKey.ptr) ∗
         ((sp + 4096#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((sp + 4104#64) ↦₆₄ g.macKey.cap) ∗ ((sp + 4112#64) ↦₆₄ g.macKey.ptr) ∗
         ((sp + 4120#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
         ((sp + 4128#64) ↦₆₄ 1152#64) ∗ ((sp + 4136#64) ↦₆₄ ek_ptr) ∗ ((sp + 4144#64) ↦₆₄ 1152#64) ∗
         ((sp + 4152#64) ↦₆₄ 2400#64) ∗ ((sp + 4160#64) ↦₆₄ dk_ptr) ∗ ((sp + 4168#64) ↦₆₄ 2400#64) ∗
         ((sp + 4176#64) ↦₆₄ epoch)) ⊢
        chunkedKeysSampledAt A.repAlloc (sp + 4192#64) outSt ∗
        memRegion (sp + 4080#64) 104 := by
      have h1 := fold_chunkedKeysSampledAt (A := A.repAlloc) (sp + 4192#64) g outSt auth epoch
        (K.fromSeed seed).2.1.toList (K.fromSeed seed).2.2.toList ek_ptr dk_ptr huc
        (by rw [hek_len]) (by rw [hdk_len])
      have h2 := ekSentInlineWordsAt_entails_memRegion (sp + 4080#64) g auth
        1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch
      dsimp only [ekSentInlineWordsAt, authInlineWordsAt] at h1 h2
      simp only [BitVec.add_assoc, arm64_norm] at h1 h2
      exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 h2)
    refine seq_vm_plain (mid := lsρ "memcpy")
      (P_mid :=
        (memRegion (sp + 4704#64) 504 ∗
         chunkedKeysSampledAt A.repAlloc (sp + 4192#64) outSt ∗
         A.pool lim st2 sf2) ∗
        (memRegion (sp + 4080#64) 104 ∗ stackAt sp spqrSendCalleeStack ∗
         memRegion (sp + 7536#64) 400 ∗ chunkAt (sp + 5208#64) chunk ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
         memRegion (sp + 7136#64) 400 ∗
         (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
         memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 5242#64) 1862 ∗
         memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1424#64) 504 ∗
         ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
         A.live hdr_ptr' 128 1 ∗ memRegion (hdr_ptr' + 96#64) 32 ∗
         A.live mac_ptr mac_cap.toNat 1 ∗ (mac_ptr ↦ₛ mac) ∗
         memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
         spqrLogLevelZeroPlacedAt ∗ Frame))
      (Q := fun sm3 =>
        sm3.sp = sp ∧
        sm3.readReg64 Reg.lr = (blkPl_427).base + 2776#64 ∧
        sm3.trace = s0.trace ∧
        sm3.readReg64 .x0 = sp + 4704#64 ∧
        sm3.readReg64 .x1 = sp + 4192#64 ∧
        (sm3.readReg64 .x2).toNat = 504 ∧
        sm3.readReg64 .x19 = s.readReg64 .x19 ∧
        sm3.readReg64 .x20 = mac_cap ∧
        sm3.readReg64 .x21 = mac_ptr ∧
        sm3.readReg64 .x22 = epoch ∧
        sm3.readReg64 .x23 = hdr_ptr' ∧
        sm3.readReg64 .x24 = sp + 5208#64 ∧
        sm3.readReg64 .x26 = sp + 4704#64 ∧
        sm3.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sm3 = calleeSavedVRegs s) (by
      by_vm_steps (
        rw [memRegion_104_eq_words13 (sp + 4592#64)]
        wp_conv_pre =>
          dsimp only [ekSentInlineWordsAt, authInlineWordsAt]
          simp only [BitVec.add_assoc, arm64_norm, sepExists_sepConj_left, sepExists_sepConj_right]
        iterate 13 (apply SepWP.exists_elim; intro _)
        wp_steps
        refine SepWP.fold hfold_ks (by sep_focus) ?_
        refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm, *],
           Entails.of_eq (by sep_ac_rfl),
           ⟨by simp only [State.sp, arm64_norm, *],
            by simp only [Reg.lr, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *],
            by simp only [Reg.x0, arm64_norm, *],
            by simp only [Reg.x1, arm64_norm, *],
            by simp only [Reg.x2, arm64_norm],
            by simp only [Reg.x19, wp_norm, arm64_norm, *],
            by simp only [Reg.x20, wp_norm, arm64_norm, *],
            by simp only [Reg.x21, wp_norm, arm64_norm, *],
            by simp only [Reg.x22, wp_norm, arm64_norm, *],
            by simp only [Reg.x23, wp_norm, arm64_norm, *],
            by simp only [Reg.x24, wp_norm, arm64_norm, *],
            by simp only [Reg.x26, wp_norm, arm64_norm, *],
            by simp only [Reg.x28, wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *]⟩⟩)) ?_
    clear hfold_ks
    rintro sm3 hpc_sm3 hrun_sm3 hvm_sm3
      ⟨hsp_sm3, hlr_sm3, htr_sm3, hx0_sm3, hx1_sm3, hx2_sm3,
       hx19_sm3, hx20_sm3, hx21_sm3, hx22_sm3, hx23_sm3, hx24_sm3, hx26_sm3, hx28_sm3, hvregs_sm3⟩
    refine call_memcpy_relocate_pool hmemcpy (of_chunkedKeysSampledAt A.repAlloc outSt)
      (sp + 4704#64) (sp + 4192#64) st2 (s0 := s0) (s_pool := sf2) (sp_call := sp)
      (Frame := memRegion (sp + 4080#64) 104 ∗ stackAt sp spqrSendCalleeStack ∗
        memRegion (sp + 7536#64) 400 ∗ chunkAt (sp + 5208#64) chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 7136#64) 400 ∗
        (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
        memRegion (sp + 3552#64) 504 ∗ memRegion (sp + 5242#64) 1862 ∗
        memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1424#64) 504 ∗
        ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
        A.live hdr_ptr' 128 1 ∗ memRegion (hdr_ptr' + 96#64) 32 ∗
        A.live mac_ptr mac_cap.toNat 1 ∗ (mac_ptr ↦ₛ mac) ∗
        memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
        spqrLogLevelZeroPlacedAt ∗ Frame)
      hpc_sm3 hrun_sm3 hsp_sm3 hsp_align (ret_pc := (blkPl_427).base + 2776#64) hlr_sm3
      htr_sm3 hx0_sm3 hx1_sm3 hx2_sm3
      (A.pool_of_vmPreserved hvm_sm3).symm
      rfl ?_
    intro sf3 hpc_sf3 hrun_sf3 hsp_sf3 htr_sf3 hx19_sf3 hx20_sf3 hx21_sf3 hx22_sf3 hx23_sf3 hx24_sf3 _ hx26_sf3 _ hx28_sf3 hvregs_sf3
    simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x26, Reg.x28,
      wp_norm, arm64_norm, *] at hx19_sf3 hx20_sf3 hx21_sf3 hx22_sf3 hx23_sf3 hx24_sf3 hx26_sf3 hx28_sf3 hvregs_sf3
    have hmac_mem := pointsToBytes_and_tail_entails_memRegion mac_ptr mac 32 mac_cap.toNat
      hmac_len hmac_cap_ge (by omega)
    have hhdr_mem := pointsToBytes_and_tail_entails_memRegion hdr_ptr'
      ((K.fromSeed seed).1.toList ++ mac) 96 128 h96 (by decide) (by decide)
    refine SepWP.fold hmac_mem (by sep_focus) ?_
    refine SepWP.fold hhdr_mem (by sep_focus) ?_
    refine SepWP.fold (stackAt_spqrSendCallee_to_allocHook sp) (by sep_focus) ?_
    wp_steps
    refine call_dealloc_pool hdealloc mac_ptr mac_cap.toNat 1 st2
      (s0 := s0) (s_pool := sf3) (sp_call := sp)
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
      hsp_align rfl (by simp only [wp_norm, arm64_norm, *])
      (by simp only [Reg.x0, wp_norm, arm64_norm, *])
      (by simp only [Reg.x1, wp_norm, arm64_norm, *])
      (by simp only [Reg.x2, wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm])
      (by sep_ac_rfl) ?_
    intro sd1 hpc_sd1 hrun_sd1 hsp_sd1 htr_sd1 hx19_sd1 _ _ hx22_sd1 hx23_sd1 hx24_sd1 _ hx26_sd1 _ hx28_sd1 hvregs_sd1
    simp only [Reg.lr, Reg.x19, Reg.x22, Reg.x23, Reg.x24, Reg.x26, Reg.x28,
      wp_norm, arm64_norm, *] at hpc_sd1 hx19_sd1 hx22_sd1 hx23_sd1 hx24_sd1 hx26_sd1 hx28_sd1 hvregs_sd1
    wp_steps
    let st3 : M.σ := M.stepEvents (rustDeallocEvents mac_cap.toNat 1) st2
    refine call_dealloc_pool hdealloc hdr_ptr' 128 1 st3
      (s0 := s0) (s_pool := sd1) (sp_call := sp)
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
      hsp_align rfl (by simp only [wp_norm, arm64_norm, *])
      (by simp only [Reg.x0, wp_norm, arm64_norm, *])
      (by simp only [Reg.x1, wp_norm, arm64_norm, *])
      (by simp only [Reg.x2, wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm])
      (by sep_ac_rfl) ?_
    intro sd2 hpc_sd2 hrun_sd2 hsp_sd2 htr_sd2 hx19_sd2 _ _ hx22_sd2 _ hx24_sd2 _ hx26_sd2 _ hx28_sd2 hvregs_sd2
    simp only [Reg.lr, Reg.x19, Reg.x22, Reg.x24, Reg.x26, Reg.x28,
      wp_norm, arm64_norm, *] at hpc_sd2 hx19_sd2 hx22_sd2 hx24_sd2 hx26_sd2 hx28_sd2 hvregs_sd2
    let st4 : M.σ := M.stepEvents (rustDeallocEvents 128 1) st3
    refine SepWP.fold (stackAt_spqrSendCallee_from_allocHook sp) (by sep_focus) ?_
    wp_steps
    refine call_memcpy_relocate_pool hmemcpy (of_chunkedKeysSampledAt A.repAlloc outSt)
      (sp + 3552#64) (sp + 4704#64) st4 (s0 := s0) (s_pool := sd2) (sp_call := sp)
      (Frame := stackAt sp spqrSendCalleeStack ∗
        memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 4080#64) 104 ∗
        memRegion (sp + 7536#64) 400 ∗ chunkAt (sp + 5208#64) chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 5242#64) 1862 ∗
        memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1424#64) 504 ∗
        ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
        spqrLogLevelZeroPlacedAt ∗ Frame)
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
      hsp_align (ret_pc := (blkPl_427).base + 2840#64) (by simp only [Reg.lr, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by sep_ac_rfl) ?_
    intro sf4 hpc_sf4 hrun_sf4 hsp_sf4 htr_sf4 hx19_sf4 _ _ hx22_sf4 _ hx24_sf4 hx25_sf4 hx26_sf4 _ hx28_sf4 hvregs_sf4
    simp only [Reg.x19, Reg.x22, Reg.x24, Reg.x25, Reg.x26, Reg.x28,
      wp_norm, arm64_norm, *] at hx19_sf4 hx22_sf4 hx24_sf4 hx25_sf4 hx26_sf4 hx28_sf4 hvregs_sf4
    obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
    obtain ⟨hchunk_5208, hchunk_4192, hchunk_1360⟩ := chunkAt_5208_4192_1360_eq sp chunk cw0 cw1 cw2 cw3 hchunk
    have h1360_slot : memRegion (sp + 1360#64) 38 =
        (∃∗ d0 : BitVec 64, (sp + 1360#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 1368#64) ↦₆₄ d1) ∗
        (∃∗ d2 : BitVec 64, (sp + 1376#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (sp + 1384#64) ↦₆₄ d3) ∗
        (∃∗ d4 : BitVec 16, (sp + 1392#64) ↦₁₆ d4) ∗ memRegion (sp + 1394#64) 4 :=
      memRegion_38_eq_chunk_slot sp
    have hfold_chunks :
        (((sp + 1360#64) ↦₆₄ cw0) ∗ ((sp + 1368#64) ↦₆₄ cw1) ∗ ((sp + 1376#64) ↦₆₄ cw2) ∗
         ((sp + 1384#64) ↦₆₄ cw3) ∗ ((sp + 1392#64) ↦₁₆ chunk.index)) ∗
        ((((sp + 4192#64) ↦₆₄ cw0) ∗ ((sp + 4200#64) ↦₆₄ cw1) ∗ ((sp + 4208#64) ↦₆₄ cw2) ∗
          ((sp + 4216#64) ↦₆₄ cw3) ∗ ((sp + 4224#64) ↦₁₆ chunk.index)) ∗
         memRegion (sp + 4226#64) 470) ∗
        (memRegion (sp + 4704#64) 504 ∗
         (((sp + 5208#64) ↦₆₄ cw0) ∗ ((sp + 5216#64) ↦₆₄ cw1) ∗ ((sp + 5224#64) ↦₆₄ cw2) ∗
          ((sp + 5232#64) ↦₆₄ cw3) ∗ ((sp + 5240#64) ↦₁₆ chunk.index)) ∗
         memRegion (sp + 5242#64) 1862) ∗
        (((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗ ((sp + 7120#64) ↦₆₄ 64#64)) ⊢
        chunkAt (sp + 1360#64) chunk ∗
        memRegion (sp + 4192#64) 504 ∗
        memRegion (sp + 4704#64) 2400 ∗
        memRegion (sp + 7104#64) 24 := by
      rw [← hchunk_1360, ← hchunk_4192, ← hchunk_5208, memRegion_4704_2400_split_nextChunk sp]
      have h4192 := chunkAt_and_470_entails_memRegion_504 sp chunk
      have h5208 := chunkAt_entails_memRegion (sp + 5208#64) chunk
      have h7104 := words3_7104_entails_memRegion sp 128#64 hdr_ptr' 64#64
      exact sepConj_mono (Entails.refl _)
        (sepConj_mono h4192
          (sepConj_mono (sepConj_mono (Entails.refl _) (sepConj_mono h5208 (Entails.refl _))) h7104))
    rw [hchunk_5208, memRegion_504_expose_chunk_slot sp, h1360_slot]
    wp_conv_pre =>
      dsimp only [spqrLogLevelZeroPlacedAt, lsLogFilterAddr]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    iterate 5 (apply SepWP.exists_elim; intro _)
    apply SepWP.exists_elim; intro (d4192_4 : BitVec 16)
    iterate 4 (apply SepWP.exists_elim; intro _)
    refine seq_vm_framed (mid := (blkPl_427).base + 2852#64)
      (P₀ :=
        (((sp + 5208#64) ↦₆₄ cw0) ∗ ((sp + 5216#64) ↦₆₄ cw1) ∗ ((sp + 5224#64) ↦₆₄ cw2) ∗
         ((sp + 5232#64) ↦₆₄ cw3) ∗ ((sp + 5240#64) ↦₁₆ chunk.index)) ∗
        ((sp + 4224#64) ↦₁₆ d4192_4))
      (P₀' :=
        (((sp + 5208#64) ↦₆₄ cw0) ∗ ((sp + 5216#64) ↦₆₄ cw1) ∗ ((sp + 5224#64) ↦₆₄ cw2) ∗
         ((sp + 5232#64) ↦₆₄ cw3) ∗ ((sp + 5240#64) ↦₁₆ chunk.index)) ∗
        ((sp + 4224#64) ↦₁₆ chunk.index))
      (Q := fun sm4a =>
        sm4a.sp = sp ∧
        sm4a.trace = s0.trace ∧
        sm4a.readVReg128 0#5 = cw1 ++ cw0 ∧
        sm4a.readVReg128 1#5 = cw3 ++ cw2 ∧
        sm4a.readReg64 .x19 = s.readReg64 .x19 ∧
        sm4a.readReg64 .x22 = epoch ∧
        sm4a.readReg64 .x24 = sp + 5208#64 ∧
        sm4a.readReg64 .x25 = sp + 1360#64 ∧
        sm4a.readReg64 .x26 = sp + 4704#64 ∧
        sm4a.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sm4a = calleeSavedVRegs s)
      (by sep_focus)
      (by
        by_vm_steps (
          wp_steps
          refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm, *],
             Entails.of_eq (by sep_ac_rfl),
             ⟨by simp only [State.sp, arm64_norm, *],
              by simp only [wp_norm, arm64_norm, *],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp only [Reg.x19, wp_norm, arm64_norm, *],
              by simp only [Reg.x22, wp_norm, arm64_norm, *],
              by simp only [Reg.x24, wp_norm, arm64_norm, *],
              by simp only [Reg.x25, wp_norm, arm64_norm, *],
              by simp only [Reg.x26, wp_norm, arm64_norm, *],
              by simp only [Reg.x28, wp_norm, arm64_norm, *],
              by simp only [wp_norm, arm64_norm, *]⟩⟩)) ?_
    rintro sm4a hpc_sm4a hrun_sm4a hvm_sm4a
      ⟨hsp_sm4a, htr_sm4a, hq0_sm4a, hq1_sm4a,
       hx19_sm4a, hx22_sm4a, hx24_sm4a, hx25_sm4a, hx26_sm4a, hx28_sm4a, hvregs_sm4a⟩
    simp only [Reg.x19, Reg.x22, Reg.x24, Reg.x25, Reg.x26, Reg.x28]
      at hx19_sm4a hx22_sm4a hx24_sm4a hx25_sm4a hx26_sm4a hx28_sm4a
    apply CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced.blkPC_427_pairStep_0xb24
      inferInstance (blkPl_427).base _ rfl hpc_sm4a hrun_sm4a
    refine seq_vm_plain (mid := lsρ "memcpy")
      (P_mid :=
        (memRegion (sp + 1424#64) 504 ∗
         chunkedKeysSampledAt A.repAlloc (sp + 3552#64) outSt ∗
         A.pool lim st4 sf4) ∗
        (chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 4192#64) 504 ∗
         memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7104#64) 24 ∗
         memRegion (sp + 1394#64) 4 ∗ stackAt sp spqrSendCalleeStack ∗
         memRegion (sp + 4080#64) 104 ∗ memRegion (sp + 7536#64) 400 ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
         memRegion (sp + 7136#64) 400 ∗
         spqrLogLevelZeroPlacedAt ∗ Frame))
      (Q := fun sm4 =>
        sm4.sp = sp ∧
        sm4.readReg64 Reg.lr = (blkPl_427).base + 3056#64 ∧
        sm4.trace = s0.trace ∧
        sm4.readReg64 .x0 = sp + 1424#64 ∧
        sm4.readReg64 .x1 = sp + 3552#64 ∧
        (sm4.readReg64 .x2).toNat = 504 ∧
        sm4.readReg64 .x19 = s.readReg64 .x19 ∧
        sm4.readReg64 .x22 = epoch ∧
        sm4.readReg64 .x25 = sp + 1360#64 ∧
        sm4.readReg64 .x26 = sp + 4704#64 ∧
        sm4.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs sm4 = calleeSavedVRegs s) (by
      by_vm_steps (
        wp_steps
        wp_conv_pre =>
          simp only [hq0_sm4a, hq1_sm4a,
            BitVec.extractLsb'_0_64_eq_truncate, bv128_truncate_append,
            CryptoVerification.SpqrV1.States.Leaves.extractLsb'_64_64_append,
            wp_norm, arm64_norm]
        refine SepWP.fold hfold_chunks (by sep_focus) ?_
        refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm, *],
           Entails.of_eq (by dsimp only [spqrLogLevelZeroPlacedAt, lsLogFilterAddr]; sep_ac_rfl),
           ⟨by simp only [State.sp, arm64_norm, *],
            by simp only [Reg.lr, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *],
            by simp only [Reg.x0, arm64_norm, *],
            by simp only [Reg.x1, arm64_norm, *],
            by simp only [Reg.x2, arm64_norm],
            by simp only [Reg.x19, wp_norm, arm64_norm, *],
            by simp only [Reg.x22, wp_norm, arm64_norm, *],
            by simp only [Reg.x25, wp_norm, arm64_norm, *],
            by simp only [Reg.x26, wp_norm, arm64_norm, *],
            by simp only [Reg.x28, wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *]⟩⟩)) ?_
    clear hfold_chunks
    rintro sm4 hpc_sm4 hrun_sm4 hvm_sm4
      ⟨hsp_sm4, hlr_sm4, htr_sm4, hx0_sm4, hx1_sm4, hx2_sm4,
       hx19_sm4, hx22_sm4, hx25_sm4, hx26_sm4, hx28_sm4, hvregs_sm4⟩
    have hpool_sm4 : A.pool lim st4 sf4 = A.pool lim st4 sm4 := by
      rw [(A.pool_of_vmPreserved hvm_sm4a).symm, A.pool_of_vmPreserved hvm_sm4]
      simp only [wp_norm, arm64_norm]
    refine call_memcpy_relocate_pool hmemcpy (of_chunkedKeysSampledAt A.repAlloc outSt)
      (sp + 1424#64) (sp + 3552#64) st4 (s0 := s0) (s_pool := sf4) (sp_call := sp)
      (Frame := chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 4192#64) 504 ∗
        memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7104#64) 24 ∗
        memRegion (sp + 1394#64) 4 ∗ stackAt sp spqrSendCalleeStack ∗
        memRegion (sp + 4080#64) 104 ∗ memRegion (sp + 7536#64) 400 ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 7136#64) 400 ∗
        spqrLogLevelZeroPlacedAt ∗ Frame)
      hpc_sm4 hrun_sm4 hsp_sm4 hsp_align (ret_pc := (blkPl_427).base + 3056#64) hlr_sm4
      htr_sm4 hx0_sm4 hx1_sm4 hx2_sm4
      hpool_sm4
      rfl ?_
    intro sf5 hpc_sf5 hrun_sf5 hsp_sf5 htr_sf5 hx19_sf5 _ _ hx22_sf5 _ _ hx25_sf5 hx26_sf5 _ hx28_sf5 hvregs_sf5
    simp only [Reg.x19, Reg.x22, Reg.x25, Reg.x26, Reg.x28,
      wp_norm, arm64_norm, *] at hx19_sf5 hx22_sf5 hx25_sf5 hx26_sf5 hx28_sf5 hvregs_sf5
    wp_steps
    let evs_tail : List AllocEvent :=
      encodeBytesAllocEvents 96 ++ (evs_nc ++ keysUnsampledDeallocEvents mac_cap.toNat)
    have hevs_tail : KeysUnsampledTailEnv sending_hdr outSt.sending_hdr chunk evs_tail :=
      keysUnsampledTailEnv_of_nextChunk mac_cap.toNat hnc_evs
    have hst4_eq : st4 = M.stepEvents evs_tail st := by
      dsimp only [st4, st3, st2, st1, evs_tail, keysUnsampledDeallocEvents]
      rw [h96, M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
    refine finish_sepWP_lscro_plain (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (fun hinv_f => hnext _ evs_tail hevs_tail hinv_f
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *])
        (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x21, arm64_norm, noneCap, *])
        (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x24, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *])
        (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x28, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])) ?_
    rw [hst4_eq]
    simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
      RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
      RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg,
      RustCliAllocBudget.pool_writeVReg128, RustCliAllocBudget.pool_writeVReg64,
      RustCliAllocBudget.pool_writeVReg32, RustCliAllocBudget.pool_setMem_writeBytes,
      RustCliAllocBudget.pool_setMem_write8, RustCliAllocBudget.pool_setMem_write16,
      RustCliAllocBudget.pool_setMem_write32, RustCliAllocBudget.pool_setMem_write64,
      applyWriteback]
    exact Entails.of_eq (by sep_ac_rfl)
  obtain ⟨tag, htag01, encRest, henc_split⟩ :=
    polyEncoderAt_split_tag A.repAlloc (sp + 7136#64) sending_hdr
  rcases htag01 with rfl | rfl
  · wp_conv_pre => rw [henc_split]
    wp_steps
    wp_conv_pre => rw [← henc_split]
    exact h2640 _ (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
      (by simp only [Reg.x19, arm64_norm, *]) (by simp only [Reg.x20, arm64_norm, *])
      (by simp only [Reg.x21, arm64_norm, *]) (by simp only [Reg.x22, arm64_norm, *])
      (by simp only [Reg.x23, arm64_norm, *]) (by simp only [Reg.x26, arm64_norm, *])
      (by simp only [Reg.x28, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm])
  · wp_conv_pre => rw [henc_split]
    wp_steps
    wp_conv_pre => rw [← henc_split]
    exact h2640 _ (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
      (by simp only [Reg.x19, arm64_norm, *]) (by simp only [Reg.x20, arm64_norm, *])
      (by simp only [Reg.x21, arm64_norm, *]) (by simp only [Reg.x22, arm64_norm, *])
      (by simp only [Reg.x23, arm64_norm, *]) (by simp only [Reg.x26, arm64_norm, *])
      (by simp only [Reg.x28, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm])

/-- `SepWPp` wrapper of `step_keysUnsampled_2588_to_3068_sepWP_placed` (polymorphic in `Qp`). -/
theorem step_keysUnsampled_2588_to_3068_placed {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {K : MlKem} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (henc_call : EncodeBytesPlacedOkX A lim ext)
    (hnc_call : PolyNextChunkPlacedOkX M A lim ext)
    (sp epoch hdr_ptr' ek_ptr dk_ptr mac_cap mac_ptr : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (seed : List.Vector (BitVec 8) 64)
    (mac : Bytes)
    (sending_hdr : PolyEncoder)
    (outSt : KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hmac_len : mac.length = 32)
    (henc_res : encodeBytesResult ((K.fromSeed seed).1.toList ++ mac) = .ok sending_hdr)
    (hnc : sending_hdr.nextChunk = .ok (outSt.sending_hdr, chunk))
    (huc : outSt.uc = { epoch := epoch, auth := auth,
                        ek := (K.fromSeed seed).2.1.toList, dk := (K.fromSeed seed).2.2.toList })
    (hhdr_ne : hdr_ptr' ≠ 0)
    (hmac_ne : mac_ptr ≠ 0)
    (hmac_cap_b : (mac_cap == 0#64) = false)
    (hmac_cap_ge : 32 ≤ mac_cap.toNat)
    (hmac_cap_lt : mac_cap.toNat < 2 ^ 63)
    (st : M.σ)
    (hfit : FitsEnv M lim st (KeysUnsampledTailEnv sending_hdr outSt.sending_hdr chunk))
    {ret : BitVec 64} {s0 s : State} {P Frame : SepProp}
    {post Qp : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 2588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = mac_cap)
    (hx21 : s.readReg64 .x21 = mac_ptr)
    (hx22 : s.readReg64 .x22 = epoch)
    (hx23 : s.readReg64 .x23 = hdr_ptr')
    (hx24 : s.readReg64 .x24 = 64#64)
    (hx25 : s.readReg64 .x25 = 32#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 7136#64) auth ∗
      memRegion (sp + 7184#64) 352 ∗
      memRegion (sp + 7536#64) 400 ∗
      memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 1360#64) 38 ∗
      memRegion (sp + 1424#64) 504 ∗
      ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
      authHeapBufs A.repAlloc g auth ∗
      ((sp + 7104#64) ↦₆₄ 128#64) ∗
      ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗
      ((sp + 7120#64) ↦₆₄ 64#64) ∗
      A.live hdr_ptr' 128 1 ∗
      (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
      memRegion (hdr_ptr' + 96#64) 32 ∗
      A.live mac_ptr mac_cap.toNat 1 ∗
      (mac_ptr ↦ₛ mac) ∗
      memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
      vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
      vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗
      A.pool lim st s ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs_tail : List AllocEvent),
      KeysUnsampledTailEnv sending_hdr outSt.sending_hdr chunk evs_tail →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = spqrSendPlacedEntry + 3068#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = 3#64 →
      sf.readReg64 .x21 = noneCap →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x24 = 1#64 →
      sf.readReg64 .x25 = sp + 1360#64 →
      sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((chunkedKeysSampledAt A.repAlloc (sp + 1424#64) outSt ∗
          chunkAt (sp + 1360#64) chunk ∗
          memRegion (sp + 1394#64) 4 ∗
          memRegion (sp + 3552#64) 504 ∗
          memRegion (sp + 4080#64) 104 ∗
          memRegion (sp + 4192#64) 504 ∗
          memRegion (sp + 4704#64) 2400 ∗
          memRegion (sp + 7104#64) 24 ∗
          memRegion (sp + 7136#64) 400 ∗
          memRegion (sp + 7536#64) 400 ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗
          A.pool lim (M.stepEvents evs_tail st) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P post Qp := by
  refine SepWPp.seq_frozen (mid := spqrSendPlacedEntry + 3068#64)
    (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  exact step_keysUnsampled_2588_to_3068_sepWP_placed hA henc_call hnc_call
    sp epoch hdr_ptr' ek_ptr dk_ptr mac_cap mac_ptr g auth seed mac
    sending_hdr outSt chunk hmac_len henc_res hnc huc
    hhdr_ne hmac_ne hmac_cap_b hmac_cap_ge hmac_cap_lt st hfit
    hinv hsp_align hpc hrun hsp hx20 hx21 hx22 hx23 hx24 hx25 hx26 htrace hP
    fun sf evs_tail hevs hinv_f hpc_f hrun_f hsp_f
      hx19_f hx20_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f htr_f hvregs_f =>
      SepWP.done hpc_f hrun_f fun _ =>
        hnext sf evs_tail hevs hinv_f hpc_f hrun_f hsp_f
          hx19_f hx20_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f htr_f hvregs_f

/-! ## 4. Budget-Threaded `+372 -> +512` Wrapper & Complete `.keysUnsampled` Arm (`+372 -> +3068`) -/

/-- Budget-threaded sibling of `StatesSendKeysUnsampled3Placed.step_keysUnsampled_372_to_512_at_placed`
    specializing `StatesSendKeysUnsampled1PlacedBudget.step_keysUnsampled_372_to_512_placed` to
    `tgt := spqrSendPlacedEntry + 512#64`. -/
theorem step_keysUnsampled_372_to_512_at_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {K : MlKem} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym
      (withVmPreserved (mlkemFromSeedSpec K)))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec))
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch sp cur : BitVec 64)
    (tape : List (BitVec 8)) (h64 : 64 ≤ tape.length)
    (seed : List.Vector (BitVec 8) 64) (hseed_val : seed.toList = tape.take 64)
    (d4056 : BitVec 64) (st : M.σ)
    {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64) (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗ authHeapBufs A.repAlloc g auth ∗
      ((sp + 2440#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400 ∗
      spqrCoinsAtPlaced ctl cur tape ∗ A.pool lim st s ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State,
      LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = spqrSendPlacedEntry + 512#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x21 = sp + 7008#64 →
      sf.readReg64 .x22 = epoch → sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 2384#64 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x28 = s.readReg64 .x28 → sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 512#64) sf
        ((authenticatorPinAt A.repAlloc g (sp + 7136#64) auth ∗ memRegion (sp + 7184#64) 352 ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗ ((sp + 2440#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗ memRegion (sp + 4192#64) 504 ∗
          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗ memRegion (sp + 7536#64) 400 ∗
          spqrCoinsAfterPlaced ctl cur tape 64 ∗ A.pool lim st sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 512#64) s P post :=
  step_keysUnsampled_372_to_512_placed hcoinsFill hseed hpk1
    g auth epoch sp cur tape h64 seed hseed_val d4056 st
    hcrl hsp_align hpc hrun hsp hx24 htrace hP hnext

set_option maxHeartbeats 800000 in
/-- Non-panicking `SepWP` form of the complete relocatable inlined `.keysUnsampled` arm
    (`spqrSendPlacedEntry + 372#64 -> spqrSendPlacedEntry + 3068#64`). -/
theorem step_send_arm_keysUnsampled_sepWP_placed {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym
      (withVmPreserved (mlkemFromSeedSpec K)))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec))
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec))
    (hmac_call : AuthMacHdrPinnedPlacedOkX F M A lim ext)
    (hres_call : DoReserve2PlacedOkX M A lim ext)
    (henc_call : EncodeBytesPlacedOkX A lim ext)
    (hnc_call : PolyNextChunkPlacedOkX M A lim ext)
    (hpk1_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList)
    (hpk2_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (st : KeysUnsampled (spqrAuthApi F))
    (outSt : KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hsend : st.send_hdr_chunk K spqrPolyApi tape = .ok (outSt, chunk, tape'))
    (st0 : M.σ)
    (hfit : FitsEnv M lim st0 (KeysUnsampledArmEnv F K st outSt.sending_hdr chunk tape))
    {tgt : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗
      spqrCoinsAtPlaced ctl cur tape ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.keysUnsampled st) ∗
      memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4056#64) 8 ∗
      memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗
      memRegion (sp + 7136#64) 400 ∗
      memRegion (sp + 7536#64) 400) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      KeysUnsampledArmEnv F K st outSt.sending_hdr chunk tape evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .hdr chunk } (.keysSampled outSt) →
      SepWP (spqrSendPlacedProg ext) tgt sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗
          spqrCoinsAfterPlaced ctl cur tape (tape.length - tape'.length) ∗
          memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.hdr chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.keysSampled outSt) ∗
          memRegion (sp + 3552#64) 504 ∗
          memRegion (sp + 4056#64) 8 ∗
          memRegion (sp + 4080#64) 104 ∗
          memRegion (sp + 4192#64) 504 ∗
          memRegion (sp + 4704#64) 2400 ∗
          memRegion (sp + 7104#64) 24 ∗
          memRegion (sp + 7136#64) 400 ∗
          memRegion (sp + 7536#64) 400) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  obtain ⟨h64, sending_hdr, hmac, henc_res, hnc, huc, rfl⟩ :=
    send_hdr_chunk_ok_elim K st hsend
  clear hsend
  let seed : List.Vector (BitVec 8) 64 := ⟨tape.take 64, take_64_len h64⟩
  have hseed_eq : keysUnsampledSeed tape = seed := by
    unfold keysUnsampledSeed
    simp only [h64, ↓reduceDIte]
    rfl
  have hhdr_eq : keysUnsampledHdr K tape = (K.fromSeed seed).1.toList := by
    unfold keysUnsampledHdr; rw [hseed_eq]
  generalize hmac_def : st.uc.auth.macHdrUnchecked F st.uc.epoch (K.fromSeed seed).1.toList = mac
    at hmac henc_res
  have hmac_eq : keysUnsampledMac F K st.uc.auth st.uc.epoch tape = mac := by
    unfold keysUnsampledMac; rw [hhdr_eq, hmac_def]
  have hmac_len : mac.length = 32 := by
    rw [← hmac_def]; exact macHdrUnchecked_length F st.uc.auth st.uc.epoch _
  clear hmac_def
  have harm_eq :
      KeysUnsampledArmEnv F K st outSt.sending_hdr chunk tape =
      SeqEnv KeysUnsampledAllocEnv
        (SeqEnv (KeysUnsampledMacReserveEnv st.uc.auth (K.fromSeed seed).1.toList)
          (KeysUnsampledTailEnv sending_hdr outSt.sending_hdr chunk)) := by
    funext evs
    unfold KeysUnsampledArmEnv
    rw [hhdr_eq, hmac_eq, henc_res]
  rw [harm_eq] at hfit
  have hfit1 : FitsEnv M lim st0 KeysUnsampledAllocEnv := hfit.seq_left
  let st1 : M.σ := M.stepEvents keysUnsampledAllocEvents st0
  have hfit_rest1 := hfit.seq_right (rfl : KeysUnsampledAllocEnv keysUnsampledAllocEvents)
  have hfit2 : FitsEnv M lim st1 (KeysUnsampledMacReserveEnv st.uc.auth (K.fromSeed seed).1.toList) :=
    hfit_rest1.seq_left
  let st2 : M.σ :=
    M.stepEvents (keysUnsampledMacReserveEvents st.uc.auth (K.fromSeed seed).1.toList) st1
  have hfit3 : FitsEnv M lim st2 (KeysUnsampledTailEnv sending_hdr outSt.sending_hdr chunk) :=
    hfit_rest1.seq_right
      (rfl : KeysUnsampledMacReserveEnv st.uc.auth (K.fromSeed seed).1.toList
        (keysUnsampledMacReserveEvents st.uc.auth (K.fromSeed seed).1.toList))
  subst hP
  rw [chunkedStatesAt_keysUnsampled_unfold A.repAlloc (sp + 0x950#64) st,
      show (sp + 0x950#64 : BitVec 64) = sp + 2384#64 from rfl,
      show (sp + 2384#64) + 8#64 = sp + 2392#64 by rw [BitVec.add_assoc]; rfl,
      show (sp + 2384#64) + 56#64 = sp + 2440#64 by rw [BitVec.add_assoc]; rfl,
      show (sp + 2384#64) + 64#64 = sp + 2448#64 by rw [BitVec.add_assoc]; rfl,
      show (sp + 0x550#64 : BitVec 64) = sp + 1360#64 from rfl,
      ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 504) (k := 416)
        (b' := sp + 1928#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      show (sp + 0x590#64 : BitVec 64) = sp + 1424#64 from rfl,
      ProofLib.memRegion_eight (sp + 4056#64)]
  refine SepWP.fold
    (authenticatorAt_entails_exists_inline_heap A.repAlloc (sp + 2392#64) st.uc.auth)
    (by sep_focus) ?_
  rw [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro g
  wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro d4056
  refine step_keysUnsampled_372_to_512_placed hcoinsFill hseed hpk1 g st.uc.auth st.uc.epoch
    sp cur tape h64 seed rfl d4056 st0
    (Frame := tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗ ((sp + 2384#64) ↦₆₄ 2#64) ∗
      memRegion (sp + 2448#64) 864 ∗ memRegion (sp + 1360#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 1424#64) 504 ∗
      memRegion (sp + 1928#64) 416 ∗ memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4080#64) 104 ∗ memRegion (sp + 7104#64) 24 ∗ Frame)
    hinv hsp_align hpc hrun hsp hx24 htr (by sep_ac_rfl) ?_
  intro s1 hinv1 hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 _ hx24_1 hx26_1 hx28_1 htr1 hvregs_1
  refine step_keysUnsampled_512_to_684_sepWP_placed hA hpk2 sp st.uc.epoch seed
    (hpk1_slice seed) (hpk2_slice seed) st0 hfit1
    (Frame := authenticatorPinAt A.repAlloc g (sp + 7136#64) st.uc.auth ∗
      memRegion (sp + 7184#64) 352 ∗ authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
      ((sp + 2440#64) ↦₆₄ st.uc.epoch) ∗ ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
      memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 7536#64) 400 ∗
      spqrCoinsAfterPlaced ctl cur tape 64 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗ ((sp + 2384#64) ↦₆₄ 2#64) ∗
      memRegion (sp + 2448#64) 864 ∗ memRegion (sp + 1360#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 1424#64) 504 ∗
      memRegion (sp + 1928#64) 416 ∗ memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4080#64) 104 ∗ memRegion (sp + 7104#64) 24 ∗ Frame)
    hinv1 hsp_align hpc1 hrun1 hsp1 hx21_1 hx22_1 htr1
    (by sep_ac_rfl) ?_
  intro s2 hdr_ptr ek_ptr dk_ptr hinv2 hhdr_ne _ hpc2 hrun2 hsp2
    hx0_2 hx1_2 hx2_2 hx3_2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2
    hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 htr2 hvregs_2
  refine step_keysUnsampled_684_to_2588_sepWP_placed hA hmac_call hres_call
    sp st.uc.epoch hdr_ptr ek_ptr dk_ptr g st.uc.auth seed mac hmac hhdr_ne st1 hfit2
    (Frame := memRegion (sp + 7184#64) 352 ∗
      ((sp + 2440#64) ↦₆₄ st.uc.epoch) ∗
      memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 7536#64) 400 ∗
      spqrCoinsAfterPlaced ctl cur tape 64 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗ ((sp + 2384#64) ↦₆₄ 2#64) ∗
      memRegion (sp + 2448#64) 864 ∗ memRegion (sp + 1360#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 1424#64) 504 ∗
      memRegion (sp + 1928#64) 416 ∗ memRegion (sp + 3552#64) 504 ∗ Frame)
    hinv2 hsp_align hpc2 hrun2 hsp2
    hx0_2 hx1_2 hx2_2 hx3_2 hx8_2 hx20_2 hx21_2 hx22_2 hx23_2
    (by rw [hx24_2, hx24_1]) hx25_2 (by rw [hx26_2, hx26_1, hx26]) hx27_2 htr2
    (by sep_ac_rfl) ?_
  intro s3 hdr_ptr' mac_cap mac_ptr hinv3 hhdr'_ne hmac_ne hmac_cap_b hmac_cap_ge hmac_cap_lt
    hpc3 hrun3 hsp3 _ hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx28_3 htr3 hvregs_3
  refine step_keysUnsampled_2588_to_3068_sepWP_placed hA henc_call hnc_call
    sp st.uc.epoch hdr_ptr' ek_ptr dk_ptr mac_cap mac_ptr g st.uc.auth seed mac
    sending_hdr outSt chunk hmac_len henc_res hnc huc
    hhdr'_ne hmac_ne hmac_cap_b hmac_cap_ge hmac_cap_lt st2 hfit3
    (Frame := authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
      ((sp + 2440#64) ↦₆₄ st.uc.epoch) ∗
      ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
      spqrCoinsAfterPlaced ctl cur tape 64 ∗
      ((sp + 2384#64) ↦₆₄ 2#64) ∗
      memRegion (sp + 2448#64) 864 ∗
      memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 1928#64) 416 ∗ Frame)
    hinv3 hsp_align hpc3 hrun3 hsp3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 htr3
    (by sep_ac_rfl) ?_
  intro sf evs_tail hevs_tail hinv_f hpc_f hrun_f hsp_f
    hx19_f hx20_f hx21_f hx22_f hx24_f hx25_f hx26_f hx28_f htr_f hvregs_f
  let evs : List AllocEvent :=
    keysUnsampledAllocEvents ++
      (keysUnsampledMacReserveEvents st.uc.auth (K.fromSeed seed).1.toList ++ evs_tail)
  have hevs : KeysUnsampledArmEnv F K st outSt.sending_hdr chunk tape evs := by
    rw [harm_eq]
    exact SeqEnv.append rfl (SeqEnv.append rfl hevs_tail)
  have hst_eq : M.stepEvents evs_tail st2 = M.stepEvents evs st0 := by
    dsimp only [st2, st1, evs]
    rw [M.stepEvents_append, M.stepEvents_append]
  have htape_sub : tape.length - (tape.drop 64).length = 64 := sub_drop_64_len h64
  refine SepWP.weaken_pre ?_
    (hnext sf evs hevs hinv_f ⟨hpc_f, hrun_f, hsp_f, htr_f,
      by rw [hx19_f, hx19_3, hx19_2, hx19_1, hx19],
      by rw [hx20_f]; rfl,
      hx22_f, hx25_f, hx26_f,
      by rw [hx28_f, hx28_3, hx28_2, hx28_1, hx28],
      by rw [hvregs_f, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩)
  rw [hst_eq, htape_sub, hx24_f, hx21_f,
      chunkedStatesTail920At_keysSampled_eq A.repAlloc (sp + 0x590#64) outSt,
      show (sp + 0x590#64 : BitVec 64) = sp + 1424#64 from rfl,
      show (sp + 1424#64) + 504#64 = sp + 1928#64 by rw [BitVec.add_assoc]; rfl]
  have hsrc := keysUnsampled_src_entails_memRegion_928 sp st.uc.epoch g st.uc.auth
  have h4056 : ((sp + 4056#64) ↦₆₄ st.uc.epoch) ⊢ memRegion (sp + 4056#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (sp + 4056#64) st.uc.epoch
  have hpay : chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 1394#64) 4 ⊢
      spqrSendPayloadSlotAt sp ((1#64 : BitVec 64).setWidth 8) (.hdr chunk) := by
    dsimp only [spqrSendPayloadSlotAt]
    rw [show (sp + 0x550#64 : BitVec 64) = sp + 1360#64 from rfl,
        show (sp + 0x572#64 : BitVec 64) = sp + 1394#64 from rfl]
    exact Entails.pure_right rfl (Entails.refl _)
  have hkey : memRegion (sp + 0x580#64) 16 ⊢
      spqrSendKeySlotAt A.repAlloc sp noneCap (sf.readReg64 .x27) none := by
    dsimp only [spqrSendKeySlotAt]
    exact Entails.pure_right rfl (Entails.refl _)
  have hrearr_lhs :
      (chunkedKeysSampledAt A.repAlloc (sp + 1424#64) outSt ∗
       chunkAt (sp + 1360#64) chunk ∗
       memRegion (sp + 1394#64) 4 ∗
       memRegion (sp + 3552#64) 504 ∗
       memRegion (sp + 4080#64) 104 ∗
       memRegion (sp + 4192#64) 504 ∗
       memRegion (sp + 4704#64) 2400 ∗
       memRegion (sp + 7104#64) 24 ∗
       memRegion (sp + 7136#64) 400 ∗
       memRegion (sp + 7536#64) 400 ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       spqrLogLevelZeroPlacedAt ∗
       A.pool lim (M.stepEvents evs st0) sf ∗
       stackAt sp spqrSendCalleeStack) ∗
      (authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
       ((sp + 2440#64) ↦₆₄ st.uc.epoch) ∗
       ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
       spqrCoinsAfterPlaced ctl cur tape 64 ∗
       ((sp + 2384#64) ↦₆₄ 2#64) ∗
       memRegion (sp + 2448#64) 864 ∗
       memRegion (sp + 0x580#64) 16 ∗
       memRegion (sp + 1928#64) 416 ∗
       Frame) =
      (((sp + 2384#64) ↦₆₄ 2#64) ∗
       authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
       ((sp + 2440#64) ↦₆₄ st.uc.epoch) ∗
       memRegion (sp + 2448#64) 864) ∗
      ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
      (chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 1394#64) 4) ∗
      memRegion (sp + 0x580#64) 16 ∗
      (stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       spqrLogLevelZeroPlacedAt ∗
       spqrCoinsAfterPlaced ctl cur tape 64 ∗
       (chunkedKeysSampledAt A.repAlloc (sp + 1424#64) outSt ∗ memRegion (sp + 1928#64) 416) ∗
       memRegion (sp + 3552#64) 504 ∗
       memRegion (sp + 4080#64) 104 ∗
       memRegion (sp + 4192#64) 504 ∗
       memRegion (sp + 4704#64) 2400 ∗
       memRegion (sp + 7104#64) 24 ∗
       memRegion (sp + 7136#64) 400 ∗
       memRegion (sp + 7536#64) 400 ∗ Frame) := by sep_ac_rfl
  rw [hrearr_lhs]
  refine Entails.trans
    (sepConj_mono hsrc
      (sepConj_mono h4056
        (sepConj_mono hpay
          (sepConj_mono hkey (Entails.refl _)))))
    (Entails.of_eq (by sep_ac_rfl))

/-- Complete budget-threaded relocatable inlined `.keysUnsampled` arm (`372..3068`, `SepWPp`,
    polymorphic in `Qp`). -/
theorem step_send_arm_keysUnsampled_placed {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym
      (withVmPreserved (mlkemFromSeedSpec K)))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec))
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec))
    (hmac_call : AuthMacHdrPinnedPlacedOkX F M A lim ext)
    (hres_call : DoReserve2PlacedOkX M A lim ext)
    (henc_call : EncodeBytesPlacedOkX A lim ext)
    (hnc_call : PolyNextChunkPlacedOkX M A lim ext)
    (hpk1_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList)
    (hpk2_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (st : KeysUnsampled (spqrAuthApi F))
    (outSt : KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hsend : st.send_hdr_chunk K spqrPolyApi tape = .ok (outSt, chunk, tape'))
    (st0 : M.σ)
    (hfit : FitsEnv M lim st0 (KeysUnsampledArmEnv F K st outSt.sending_hdr chunk tape))
    {ret : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      stackAt sp spqrSendCalleeStack ∗ A.pool lim st0 s ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗
      spqrCoinsAtPlaced ctl cur tape ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.keysUnsampled st) ∗
      memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 3552#64) 504 ∗
      memRegion (sp + 4056#64) 8 ∗
      memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗
      memRegion (sp + 7136#64) 400 ∗
      memRegion (sp + 7536#64) 400) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      KeysUnsampledArmEnv F K st outSt.sending_hdr chunk tape evs →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SpqrSendJoinStatePlaced sp ext s0 sf
        { epoch := st.uc.epoch, payload := .hdr chunk } (.keysSampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st0) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗
          spqrCoinsAfterPlaced ctl cur tape (tape.length - tape'.length) ∗
          memRegion (sp + 0x950#64) 928 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.hdr chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) none ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.keysSampled outSt) ∗
          memRegion (sp + 3552#64) 504 ∗
          memRegion (sp + 4056#64) 8 ∗
          memRegion (sp + 4080#64) 104 ∗
          memRegion (sp + 4192#64) 504 ∗
          memRegion (sp + 4704#64) 2400 ∗
          memRegion (sp + 7104#64) 24 ∗
          memRegion (sp + 7136#64) 400 ∗
          memRegion (sp + 7536#64) 400) ∗ Frame) post Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P post Qp := by
  refine SepWPp.seq_frozen (mid := spqrSendPlacedEntry + 3068#64)
    (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  exact step_send_arm_keysUnsampled_sepWP_placed A lim ext
    hA hcoinsFill hseed hpk1 hpk2 hmac_call hres_call henc_call hnc_call
    hpk1_slice hpk2_slice sp cur tape tape' st outSt chunk hsend st0 hfit
    hinv hpc hrun hsp hsp_align htr hx19 hx24 hx26 hx28 hvregs hP
    fun sf evs hevs hinv_f hjoin =>
      SepWP.done hjoin.pc hjoin.run fun _ => hnext sf evs hevs hinv_f hjoin

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled3PlacedBudget
