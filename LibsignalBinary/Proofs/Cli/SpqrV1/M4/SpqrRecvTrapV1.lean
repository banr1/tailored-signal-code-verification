/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SpqrV1.M4.Decrypt
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.ShardFill.TryDecryptStateRatchetCoins
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Recv.Contracts
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DeriveKeys
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.PqRecv
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrow
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKey
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofX
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Proof
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Acknowledged
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceived
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSent
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceived
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1Sent
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProof
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Top
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMessageBridge
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1Chunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Ct1Received
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.RecvCt1Ack
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProof
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEk
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Top
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Contracts
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Final
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Proof
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Proof
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.Entry

/-!
# Trap-at-RNG SPQR V1 `recv` and Widened `S5 + S6` Seam for CLI Ratchet

Establishes `stage2ContractsWeak_trap`, `decode_state_ok_trap`, `states_recv_ok_x_trap`,
`spqr_recv_ok_trap`, `spqrRecvOkWT_of_v1_trap`, and the widened `S5 + S6` seam
`pqRecvDerive_okWT_trap` on `trTrapProgAt` / `trTrapExterns`.
-/

@[expose] public section

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalSpqrV1.M4
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.Recv
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.CodeLayout

/-! ## 1. Hook-table lemmas for `trTrapExterns C abs` -/

theorem sessionExterns_le_trTrap (C : Crypto) (abs : String → Option (State → State)) :
    ∀ n f,
      Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics (trTrapExterns C abs) n = some f := by
  intro n f h
  by_cases hr : n = rngFillName
  · subst hr
    by_cases hp : Rust.isPanicSymbol rngFillName = true
    · simp [Rust.withPanics, hp] at h ⊢
      exact h
    · simp only [Rust.withPanics, hp, Bool.false_eq_true, ↓reduceIte] at h
      have hn : ¬(rngFillName = "__rustc::__rust_alloc" ∨ rngFillName = "__rustc::__rust_dealloc" ∨
          rngFillName = "__rustc::__rust_realloc") := by decide
      rw [ConsumeMessageKeyTransfer.sessionExterns_not_alloc (a2 := fun _ => none) hn] at h
      simp [CryptoVerification.LibsignalSession.sessionExterns, rngFillName] at h
  · rw [withPanics_trTrap_eq_kit C 0#64 abs hr]
    exact ConsumeMessageKeyTransfer.sessionExterns_le C 0#64 abs n f h

theorem hkdfHooks_trTrapExterns (C : Crypto) (abs : String → Option (State → State)) :
    HkdfHooks C.F (trTrapExterns C abs) :=
  HkdfHooks.of_mono (ext1 := CryptoVerification.LibsignalSession.sessionExterns C.F abs)
    (sessionExterns_le_trTrap C abs)

theorem blackBox_trTrapExterns (C : Crypto) (abs : String → Option (State → State)) :
    Rust.withPanics (trTrapExterns C abs) "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook := by
  rw [withPanics_trTrap_eq_kit C 0#64 abs (by decide)]
  exact ConsumeMessageKeyTransfer.tripleRatchetProgAt_blackBox C 0#64 abs

theorem hookSat_memcpy_ro_trTrapExterns (C : Crypto) (abs : String → Option (State → State)) :
    HookSat (trTrapExterns C abs) memcpyName sessionMemcpyRegionROSpec := by
  rcases hookSat_memcpy_ro_tripleRatchetExterns C 0#64 abs with ⟨fn, hfn, hok⟩
  exact ⟨fn, (trTrapExterns_eq_tripleRatchetExterns C 0#64 abs (by decide)).trans hfn, hok⟩

theorem hookSat_allocZeroed_trTrapExterns {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hZero : HookSat abs allocZeroedName (rustAllocZeroedSpec A)) :
    HookSat (trTrapExterns C abs) allocZeroedName (rustAllocZeroedSpec A) :=
  hookSat_trTrapExterns (by decide) (by decide) hZero

theorem spqrHooks_trTrapExterns {C : Crypto} {A : RustAlloc} {K : MlKem}
    {abs : String → Option (State → State)}
    (hSH : SpqrHooks C A K abs) :
    SpqrHooks C A K (trTrapExterns C abs) where
  fromSeed := hookSat_trTrapExterns (by decide) (by decide) hSH.fromSeed
  pk1 := hookSat_trTrapExterns (by decide) (by decide) hSH.pk1
  pk2 := hookSat_trTrapExterns (by decide) (by decide) hSH.pk2
  encaps1 := hookSat_trTrapExterns (by decide) (by decide) hSH.encaps1
  encaps2 := hookSat_trTrapExterns (by decide) (by decide) hSH.encaps2
  decaps := hookSat_trTrapExterns (by decide) (by decide) hSH.decaps
  validatePk := hookSat_trTrapExterns (by decide) (by decide) hSH.validatePk
  hmac := hookSat_trTrapExterns (by decide) (by decide) hSH.hmac

/-! ## 2. `spqrRecvEmptyAny_ok_trap` and `Stage2ContractsWeak` on `trTrapExterns` -/

private def emptySpqrModel : SpqrModel where
  send := fun _ _ => some ([], none, [])
  draws := fun _ _ => 0
  recv := fun _ msg => CryptoVerification.LibsignalSpqr.spqrRecvEmpty msg
  recvPanics := fun _ _ => false
  sendPanics := fun _ _ => false

private theorem emptySpqrModel_recvEmptyOk : emptySpqrModel.RecvEmptyOk where
  recv := fun _ => rfl
  noPanic := fun _ => nofun

private theorem memcpy_recv_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr spqrRecvName + bv% (ls_off% "memcpy" - ls_off% "spqr::recv"))
      InImage.SpqrRecvEmpty.memcpyRecvPcsSpec := by
  refine hook_ok_at_raw (hname := "memcpy")
    (stub := CryptoVerification.libsignalSessionCode.fnOff "memcpy")
    (ls_lemma% fnOff "spqr::recv") (by fnoff_eq) (by fnoff_eq)
      (by fnoff_eq) ?_
  refine ⟨hookMemcpy, ?_, InImage.SpqrRecvEmpty.hookMemcpy_recv_pcs_ok⟩
  rw [withPanics_trTrap_eq_kit C 0#64 abs (by decide)]
  have hp : Rust.isPanicSymbol "memcpy" = false := by simp [Rust.isPanicSymbol]
  simp only [Rust.withPanics, hp, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem spqrRecvEmpty_res_shape (msg : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqr.spqrRecvEmpty msg = .ok ([], none) ∨
      (msg ≠ [] ∧ ∃ sd, CryptoVerification.LibsignalSpqr.spqrRecvEmpty msg = .error sd) := by
  unfold CryptoVerification.LibsignalSpqr.spqrRecvEmpty
  cases hok : CryptoVerification.LibsignalSpqr.msgPreambleOk msg with
  | true => exact Or.inl rfl
  | false =>
    refine Or.inr ⟨?_, false, rfl⟩
    intro hnil
    subst hnil
    simp [CryptoVerification.LibsignalSpqr.msgPreambleOk,
      CryptoVerification.LibsignalSpqr.msgPreamble?] at hok

theorem spqrRecvEmptyAny_ok_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr spqrRecvName)
      ((spqrRecvEmptyAnySpec A).inImage img) := by
  have hbase := InImage.SpqrRecvEmpty.spqrRecvEmpty_base_F0
    img.base (Rust.withPanics (trTrapExterns C abs)) A emptySpqrModel img emp
    emptySpqrModel_recvEmptyOk
    (InImage.SpqrRecvEmpty.memcpyRecvPcsSpecS_inImage_of img
      (memcpy_recv_ok_at_trap img.base C abs))
  apply subroutine_ok.of_codeLoaded
  intro ⟨st, msg, ret⟩ R s0 hpc hrun hpre hal _
  have hpre0 : s0.mem ⊨
      (InImage.SpqrRecvEmpty.spqrRecvEmptyCodeSpec0 A emptySpqrModel img emp).pre
        (st, msg, ret) s0 ∗ R := by
    dsimp only [spqrRecvEmptyAnySpec, InImage.SpqrRecvEmpty.spqrRecvEmptyCodeSpec0,
      InImage.SpqrRecvEmpty.spqrRecvCodeSpec0, Spec.inImage] at hpre ⊢
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨himg0, ⟨hx0, hx1, hx8, hst⟩, hmem⟩
    exact ⟨hst, himg0, ⟨hx0, hx1, hx8⟩, hmem⟩
  exact subroutine_ok.mono_outcome hbase (st, msg, ret) R s0 hpc hrun hpre0 hal fun sf hout => by
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpanic⟩ | hex | hoom
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [InImage.SpqrRecvEmpty.spqrRecvEmptyCodeSpec0,
        InImage.SpqrRecvEmpty.spqrRecvCodeSpec0, spqrRecvEmptyAnySpec, Spec.inImage,
        emptySpqrModel] at hpost ⊢
      rw [emp_sepConj] at hpost
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))
      refine Entails.sepExists_right (CryptoVerification.LibsignalSpqr.spqrRecvEmpty msg.bytes) ?_
      exact Entails.pure_right (spqrRecvEmpty_res_shape msg.bytes) (Entails.refl _)
    · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
      dsimp only [InImage.SpqrRecvEmpty.spqrRecvEmptyCodeSpec0,
        InImage.SpqrRecvEmpty.spqrRecvCodeSpec0, spqrRecvEmptyAnySpec, Spec.inImage,
        emptySpqrModel] at hpanic ⊢
      simp only [Bool.false_eq_true, or_false] at hpanic
      exact hpanic
    · exact Or.inr (Or.inr (Or.inl hex))
    · exact Or.inr (Or.inr (Or.inr hoom))

private theorem blackBoxU8_of_blackBox_std3 {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr blackBoxSpec) :
    subroutine_ok P addr blackBoxU8Spec := by
  apply subroutine_ok.of_codeLoaded
  intro v R s0 hpc hrun hpre hal _
  exact subroutine_ok.mono_outcome h v R s0 hpc hrun hpre hal fun sf hout => by
    rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simp only [blackBoxSpec, blackBoxU8Spec, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨⟨hx0, htr⟩, hR⟩
      refine ⟨⟨?_, htr⟩, hR⟩
      rw [hx0]
      exact BitVec.setWidth_setWidth_of_le (v.setWidth 8) (by decide : 8 ≤ 64)
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)

theorem stage2ContractsWeak_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hHooks : TripleRatchetHooks C A S abs) :
    Stage2ContractsWeak img C A (trTrapExterns C abs) :=
  let hC := Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A S abs hHooks
  { toAllocContractsX := AllocContractsX.of_AllocContracts hC.toAllocContracts
    black_box := subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_withStack_of_subroutine_ok (blackBoxU8_of_blackBox_std3 hC.black_box) extHookStack)
    compress256 := subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_withStack_of_subroutine_ok hC.compress256 extHookStack)
    dh := subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_withStack_of_subroutine_ok hC.dh extHookStack)
    pub_from_secret := subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_withStack_of_subroutine_ok hC.pub_from_secret extHookStack)
    static_drop := subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_withStack_of_subroutine_ok hC.static_drop extHookStack)
    shared_drop := subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_withStack_of_subroutine_ok hC.shared_drop extHookStack)
    uuid_try_parse := subroutine_ok_inImage_of_subroutine_ok img
      (uuidTryParseAnyWithStack_of_code hC.uuid_try_parse)
    decode_varint_slow := subroutine_ok_inImage_of_subroutine_ok img
      (decodeVarintSlowWithStack_of_decodeVarintSlow hC.decode_varint_slow)
    aes_enc := subroutine_ok_inImage_of_subroutine_ok img hC.aes_enc
    aes_dec := subroutine_ok_inImage_of_subroutine_ok img (aesDecWeak_of_aesDec hC.aes_dec)
    spqr_recv := spqrRecvEmptyAny_ok_trap img C A abs
    format_inner := subroutine_ok_inImage_of_subroutine_ok img hC.format_inner
    fmt_write := subroutine_ok_inImage_of_subroutine_ok img hC.fmt_write
    decode_error_from := subroutine_ok_inImage_of_subroutine_ok img
      (decodeErrorFromWithStack_of_decodeErrorFrom hC.decode_error_from)
    decode_error_push := subroutine_ok_inImage_of_subroutine_ok img
      (decodeErrorPushExtern_of_decodeErrorPush (decodeErrorPushWithStack_of_decodeErrorPush hC.decode_error_push)) }

/-! ## 3. `DecodeStateOkX` on `Stage2Contracts_trap` -/

theorem decodeVarint2_ok_of_stage2_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hTrap : Stage2Contracts_trap b C A uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.SpqrV1.Varint.decodeVarint2Name)
      (CryptoVerification.SpqrV1.Varint.decodeVarint2Spec A) := by
  refine CryptoVerification.SpqrV1.Varint.decodeVarint2_ok_of_contracts ?_ ?_
  · rw [CryptoVerification.SpqrV1.Varint.decodeVarint2_add_from_eq_fnAddr]
    exact hTrap.decode_error_from
  · rw [Prost.fnAddr_offset_eq_H
      (name := CryptoVerification.SpqrV1.Varint.decodeVarint2Name)
      (callee := varintSlowName)]
    exact Prost.decodeVarintSlow_ok_of_session2 hTrap.decode_varint_slow

theorem skipField3_ok_of_stage2_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hTrap : Stage2Contracts_trap b C A uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.SpqrV1.Varint.skipField3Name)
      (CryptoVerification.SpqrV1.Varint.skipField3Spec A) := by
  refine CryptoVerification.SpqrV1.Varint.skipField3_ok_of_contracts ?_
    (decodeVarint2_ok_of_stage2_trap hTrap)
  rw [CryptoVerification.SpqrV1.Varint.skipField3_add_from_eq_fnAddr]
  exact hTrap.decode_error_from

theorem chainParamsMerge_ok_of_stage2_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hTrap : Stage2Contracts_trap b C A uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.SpqrV1.Top.DecodeState.chainParamsMergeName)
      (CryptoVerification.SpqrV1.Top.DecodeState.chainParamsMergeSpec A) := by
  have hok : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeName)
      (CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeSpec A) := by
    refine chainParamsMerge_ok_of_contracts ?_ ?_ ?_ ?_
    · rw [Prost.fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeName) (callee := decodeErrorFromName)]
      exact hTrap.decode_error_from
    · rw [Prost.fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeName) (callee := decodeErrorPushName)]
      exact hTrap.decode_error_push
    · rw [Prost.fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeName) (callee := CryptoVerification.SpqrV1.Varint.decodeVarint2Name)]
      exact decodeVarint2_ok_of_stage2_trap hTrap
    · rw [Prost.fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.chainParamsMergeName) (callee := CryptoVerification.SpqrV1.Varint.skipField3Name)]
      exact skipField3_ok_of_stage2_trap hTrap
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre halign _
  let x' : CryptoVerification.SpqrV1.Prost.MessageMerge.ChainParamsMergeGhost :=
    ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
  exact subroutine_ok.mono_outcome hok x' R s0 hpc hrun hpre halign fun _ hout => hout

theorem epochDirectionMerge_ok_of_stage2_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hTrap : Stage2Contracts_trap img.base C A uuidTryParse S ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.SpqrV1.Top.DecodeState.epochDirectionMergeName)
      ((CryptoVerification.SpqrV1.Top.DecodeState.epochDirectionMergeSpec A).inImage img) := by
  have hok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeName)
      ((CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeSpec A).inImage img) := by
    refine epochDirectionMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_
    · rw [Prost.fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeName) (callee := decodeErrorFromName)]
      exact hTrap.decode_error_from
    · rw [Prost.fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeName) (callee := decodeErrorPushName)]
      exact hTrap.decode_error_push
    · rw [Prost.fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeName) (callee := CryptoVerification.SpqrV1.Varint.decodeVarint2Name)]
      exact decodeVarint2_ok_of_stage2_trap hTrap
    · rw [Prost.fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeName) (callee := CryptoVerification.SpqrV1.Varint.skipField3Name)]
      exact skipField3_ok_of_stage2_trap hTrap
    · rw [Prost.fnAddr_offset_eq_H (name := CryptoVerification.SpqrV1.Prost.MessageMerge.epochDirectionMergeName) (callee := bytesMerge3Name)]
      exact hBytes
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre halign _
  let x' : CryptoVerification.SpqrV1.Prost.MessageMerge.EpochDirectionMergeGhost :=
    ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
  exact subroutine_ok.mono_outcome hok x' R s0 hpc hrun hpre halign fun _ hout => hout

theorem polyEncoderMerge_ok_of_stage2_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hTrap : Stage2Contracts_trap img.base C A uuidTryParse S ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img))
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name)
      (growOneVecU8Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyEncoderMergeName)
      ((polyEncoderMergeSpec A).inImage img) := by
  refine polyEncoderMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Prost.fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := decodeErrorFromName)]
    exact hTrap.decode_error_from
  · rw [Prost.fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := decodeErrorPushName)]
    exact hTrap.decode_error_push
  · rw [Prost.fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := CryptoVerification.SpqrV1.Varint.decodeVarint2Name)]
    exact decodeVarint2_ok_of_stage2_trap hTrap
  · rw [Prost.fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := CryptoVerification.SpqrV1.Varint.skipField3Name)]
    exact skipField3_ok_of_stage2_trap hTrap
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyEncoderMergeName +
        bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]"
          "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name := by
      dsimp only [tripleRatchetProgAtExt]
      rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        show CryptoVerification.libsignalSessionCode.fnOff polyEncoderMergeName = num% (ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>") by fnoff_eq,
        show CryptoVerification.libsignalSessionCode.fnOff bytesMerge3Name = num% (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]") by fnoff_eq]
      bv_omega
    rw [h_off]; exact hBytes
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyEncoderMergeName +
        bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" -
          ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name := by
      dsimp only [tripleRatchetProgAtExt]
      rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        show CryptoVerification.libsignalSessionCode.fnOff polyEncoderMergeName = num% (ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>") by fnoff_eq,
        show CryptoVerification.libsignalSessionCode.fnOff growOneVecU8Name = num% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one") by fnoff_eq]
      bv_omega
    rw [h_off]; exact hGrow

theorem polyDecoderMerge_ok_of_stage2_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hTrap : Stage2Contracts_trap img.base C A uuidTryParse S ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img))
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name)
      (growOneVecU8Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName)
      ((polyDecoderMergeSpec A).inImage img) := by
  refine polyDecoderMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Prost.fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := decodeErrorFromName)]
    exact hTrap.decode_error_from
  · rw [Prost.fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := decodeErrorPushName)]
    exact hTrap.decode_error_push
  · rw [Prost.fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := CryptoVerification.SpqrV1.Varint.decodeVarint2Name)]
    exact decodeVarint2_ok_of_stage2_trap hTrap
  · rw [Prost.fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := CryptoVerification.SpqrV1.Varint.skipField3Name)]
    exact skipField3_ok_of_stage2_trap hTrap
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName +
        bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]"
          "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name := by
      dsimp only [tripleRatchetProgAtExt]
      rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        show CryptoVerification.libsignalSessionCode.fnOff polyDecoderMergeName = num% (ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") by fnoff_eq,
        show CryptoVerification.libsignalSessionCode.fnOff bytesMerge3Name = num% (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]") by fnoff_eq]
      bv_omega
    rw [h_off]; exact hBytes
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName +
        bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" -
          ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name := by
      dsimp only [tripleRatchetProgAtExt]
      rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        show CryptoVerification.libsignalSessionCode.fnOff polyDecoderMergeName = num% (ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") by fnoff_eq,
        show CryptoVerification.libsignalSessionCode.fnOff growOneVecU8Name = num% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one") by fnoff_eq]
      bv_omega
    rw [h_off]; exact hGrow

theorem v1StateMerge_ok_of_stage2_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hTrap : Stage2Contracts_trap img.base C A uuidTryParse S ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img))
    (hGrowVecU8 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name)
      (growOneVecU8Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr v1StateMergeName)
      ((v1StateMergeSpec A img.base).inImage img) := by
  have hFrom := hTrap.decode_error_from
  have hPush := hTrap.decode_error_push
  have hVarint := decodeVarint2_ok_of_stage2_trap hTrap
  have hSkip := skipField3_ok_of_stage2_trap hTrap
  have hAuth : AuthMergeOkX img A ext :=
    auth_merge_ok_ext hFrom hPush hVarint hSkip hBytes
  have hAuthFn := auth_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hBytes
  have hUcEk := unchunkedEkSentCt1ReceivedMerge_ok_of_fnAddr hFrom hPush hVarint hSkip hBytes hAuthFn
  have hUcCt1 := unchunkedCt1SentMerge_ok_of_fnAddr hFrom hPush hVarint hSkip hBytes hAuthFn
  have hPolyEnc := polyEncoderMerge_ok_of_stage2_trap hTrap hBytes hGrowVecU8
  have hPolyDec := polyDecoderMerge_ok_of_stage2_trap hTrap hBytes hGrowVecU8
  exact v1State_merge_ok_of_fnAddr
    hFrom hPush hVarint hSkip hTrap.toAllocContracts.dealloc
    (drop_opt_proto_inner_state_ok_ext hTrap.toAllocContracts.dealloc)
    (drop_proto_chunked_ct1_received_ok_ext hTrap.toAllocContracts.dealloc)
    (drop_proto_chunked_header_sent_ok_ext hTrap.toAllocContracts.dealloc)
    (drop_proto_chunked_ek_sent_ct1_received_ok_ext hTrap.toAllocContracts.dealloc)
    (drop_proto_chunked_no_header_received_ok_ext hTrap.toAllocContracts.dealloc)
    (drop_proto_chunked_header_received_ok_ext hTrap.toAllocContracts.dealloc)
    (drop_proto_unchunked_ct1_sent_ek_received_ok_ext hTrap.toAllocContracts.dealloc)
    (drop_glue_proto_poly_encoder_ok_ext hTrap.toAllocContracts.dealloc)
    (chunked_keys_unsampled_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth)
    (chunked_keys_sampled_merge_ok_ext_x hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc)
    (chunked_header_sent_merge_ok_ext_x hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc hPolyDec)
    (chunkedCt1Received_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcEk hPolyEnc)
    (chunkedEkSentCt1Received_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcEk hPolyDec)
    (chunked_no_header_received_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth hPolyDec)
    (chunked_header_received_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth hBytes hPolyDec)
    (chunkedCt1Sampled_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcCt1 hPolyEnc hPolyDec)
    (chunked_ek_received_ct1_sampled_merge_ok_ext_x hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc)
    (chunkedCt1Acknowledged_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcCt1 hPolyDec)
    (chunked_ct2_sampled_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth hPolyEnc)

theorem decode_state_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTrap : Stage2Contracts_trap img.base C A uuidTryParse S ext) :
    DecodeStateOkX canonicalV1InnerHeap img A ext := by
  have hb := ProofLib.base_aligned_of_loads himg
  let hAlloc := hTrap.toAllocContracts
  have hBC : BytesMerge3Contracts img A ext :=
    { loads := himg
      alloc := hAlloc
      decode_error_from := hTrap.decode_error_from
      decode_varint2 := subroutine_ok_inImage_of_subroutine_ok img (decodeVarint2_ok_of_stage2_trap hTrap)
      bytes_from_vec := bytesFromVecOk_ext himg rfl
      reserve7 := do_reserve_7_ok_ext hAlloc
      vtable_slot := bytesVtableSlotLoaded
      vtable_drop := fun p v => bytesVtableDropOk_ext p v v.length hAlloc himg rfl }
  have hBytes := hBC.ok_ext
  have hGrow := growOneVecU8_ok_ext img.base A ext hAlloc
  exact decodeState_ok
    { b_page_aligned := hb
      of_drop_inner := of_drop_inner_canonical A
      of_cap_inner := of_cap_inner_ok A
      alloc := hAlloc
      decodeErrorFrom := hTrap.decode_error_from
      decodeErrorPush := hTrap.decode_error_push
      decodeVarint2 := decodeVarint2_ok_of_stage2_trap hTrap
      skipField3 := skipField3_ok_of_stage2_trap hTrap
      chainParamsMerge := chainParamsMerge_ok_of_stage2_trap hTrap
      growOneChainEpoch := CryptoVerification.SpqrV1.Alloc.grow_one_chain_epoch_full_ok_ext hAlloc
      dropOptProtoInnerState := dropOptProtoInnerState_canonical_ok hb hAlloc.dealloc
      dropProtoPqRatchetState := dropProtoPqRatchetState_canonical_ok hb hAlloc.dealloc
      bytesMerge3 := hBytes
      epochDirectionMerge := epochDirectionMerge_ok_of_stage2_trap hTrap hBytes
      v1StateMerge := v1StateMerge_ok_of_stage2_trap hTrap hBytes hGrow }

/-! ## 4. `StatesRecvOkX`, `SpqrRecvContracts`, `spqr_recv_ok_trap`, and `spqrRecvOkWT_of_v1_trap` -/

theorem statesRecvContracts_of_hooks_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {K : MlKem}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSH : SpqrHooks C A K abs) :
    StatesRecvContracts img A C.F K (trTrapExterns C abs) := by
  let ext := trTrapExterns C abs
  have : HkdfHooks C.F ext := hkdfHooks_trTrapExterns C abs
  have hTrap : Stage2Contracts_trap img.base C A uuidTryParse (spqrV1 C.F K) ext :=
    Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A (spqrV1 C.F K) abs hTH
  have hA : AllocContracts img.base A ext := hTrap.toAllocContracts
  have hAx : AllocContractsX img A ext := AllocContractsX.of_AllocContracts hA
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName) sessionMemcpyRegionSpec := by
    have h0 := hA.session_memcpy_region_ok_at memcpyName 0 (Nat.add_zero _)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h0
  have hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec :=
    hookSat_memcpy_ro_trTrapExterns C abs
  have hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A) :=
    hookSat_allocZeroed_trTrapExterns hTH.allocZeroed
  have hSH' : SpqrHooks C A K ext := spqrHooks_trTrapExterns hSH
  have hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith C.F) ext :=
    hkdf_to_slice_spqr_ok_ext img C himg (sessionExterns_le_trTrap C abs)
  have hconcat2 : SliceConcat2OkX img A ext := slice_concat_2_ok_x hA hRO
  have hconcat3 : SliceConcat3OkX img A ext := slice_concat_3_ok_x hA hRO
  have hadd : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addChunkName) (addChunkSpec A) :=
    add_chunk_ok_ext hA
  have haddX : AddChunkOkX img A ext := add_chunk_ok_x hA
  have hencBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeBytesName) (encodeBytesSpec A) :=
    encode_bytes_ok_ext hA
  have hdecMsg : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A img.base) :=
    polyDecoderDecodedMessage_ok_ext hA
  have hdecMsgX : PolyDecodedMessageOkX img A ext := polyDecodedMessageOkX_of_alloc hA
  have hvalPk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr mlkemValidatePkName) (mlkemValidatePkSpec K) :=
    mlkemValidatePk_ok_of_hookSat hSH'.validatePk
  have hrecvEk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      (unchunkedCt1SentRecvEkSpec A C.F K) :=
    unchunked_ct1_sent_recv_ek_ok_ext hA.dealloc hvalPk
  have hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A C.F K img.base) :=
    unchunked_ct1_sent_ek_received_send_ct2_ok_ext hA hRO hSH'.encaps2 hSH'.hmac
  have hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName) (sendCt2EncoderSpec A) :=
    send_ct2_encoder_ok_ext hA hencBytes
  exact
    { keysSampledRecvCt1Chunk_ok :=
        keys_sampled_recv_ct1_chunk_ok_ext hA.dealloc hmemcpy hadd hencBytes
      headerSentRecvCt1Chunk_ok :=
        header_sent_recv_ct1_chunk_ok_alloc hA
      ct1ReceivedRecvCt2Chunk_ok :=
        ct1_received_recv_ct2_chunk_ok_ext hA.dealloc hmemcpy hadd
      ekSentCt1ReceivedRecvCt2Chunk_ok :=
        recv_ct2_chunk_ok_x_of_decodedMessage himg hA hAx
          (allocZeroedWithStackOkX_of_hook hZero)
          hSH'.decaps hconcat2 hconcat3
          hhkdf (authUpdate_ok_of_hook_x himg hconcat2 hhkdf hAx hZero)
          (do_reserve_7_ok_ext_x hA) hSH'.hmac
      noHeaderReceivedRecvHdrChunk_ok :=
        noHeaderReceived_recv_hdr_chunk_okX himg hAx hA.dealloc haddX hdecMsgX
          hconcat3 hSH'.hmac
      polyAddChunk_ok := haddX
      polyDecodedMessage_ok := hdecMsg
      unchunkedCt1SentRecvEk_ok := hrecvEk
      unchunkedCt1SentEkReceivedSendCt2_ok := hsendCt2
      sendCt2Encoder_ok := hsendCt2Enc
      ekReceivedCt1SampledRecvCt1Ack_ok :=
        ek_received_ct1_sampled_recv_ct1_ack_ok_ext hA.dealloc hsendCt2 hsendCt2Enc
      ct1AcknowledgedRecvEkChunk_ok :=
        ct1_acknowledged_recv_ek_chunk_ok_ext hA.dealloc hmemcpy hadd hdecMsg
          hrecvEk hsendCt2 hsendCt2Enc
      ct2SampledRecvNextEpoch_ok :=
        ct2_sampled_recv_next_epoch_ok_ext (drop_glue_poly16_ok_ext hA.dealloc) }

theorem states_recv_ok_x_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {K : MlKem}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSH : SpqrHooks C A K abs) :
    StatesRecvOkX img A C.F K (trTrapExterns C abs) :=
  states_recv_ok_x
    (Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A (spqrV1 C.F K) abs hTH).toAllocContracts
    (statesRecvContracts_of_hooks_trap himg hTH hSH)

theorem spqrRecvContracts_of_hooks_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {K : MlKem}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSH : SpqrHooks C A K abs) :
    SpqrRecvContracts canonicalV1InnerHeap img A C.F K (trTrapExterns C abs) := by
  let ext := trTrapExterns C abs
  have : HkdfHooks C.F ext := hkdfHooks_trTrapExterns C abs
  have hTrap : Stage2Contracts_trap img.base C A uuidTryParse (spqrV1 C.F K) ext :=
    Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A (spqrV1 C.F K) abs hTH
  have hA : AllocContracts img.base A ext := hTrap.toAllocContracts
  have hAX : AllocContractsX img A ext := AllocContractsX.of_AllocContracts hA
  have hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith C.F) ext :=
    hkdf_to_slice_spqr_ok_ext img C himg (sessionExterns_le_trTrap C abs)
  have hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec :=
    hookSat_memcpy_ro_trTrapExterns C abs
  have hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A) :=
    hookSat_allocZeroed_trTrapExterns hTH.allocZeroed
  exact CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecvContracts_of_okX himg hA
    (decode_state_ok_trap himg hTrap)
    (auth_new_ok_x himg hhkdf hA hRO hZero)
    (chainNew_ok_ext_x himg hhkdf (vec_deque_grow_ok_x hA) hAX)
    (chainAddEpoch_ok_ext_x himg hhkdf (vec_deque_grow_ok_x hA) hAX)
    (chainRecvKey_ok_alloc_x himg (slice_concat_2_ok_x hA hRO) hhkdf hA)
    (CryptoVerification.SpqrV1.Top.MessageDeserialize.messageDeserialize_spqrPolyApi_ok_of_contracts_x
      img A ext hA hTrap.format_inner)
    (states_from_pb_ok_x hA)
    (states_recv_ok_x_trap himg hTH hSH)

theorem spqr_recv_ok_trap
    (C : Crypto) (A : RustAlloc) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSpqr : SpqrHooks C A K abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr spqrRecvName)
      (spqrRecvSpecExactKeyBounded A (spqrV1Recv C.F K) img) :=
  spqrRecv_ok_ext_of_contracts (spqrRecvContracts_of_hooks_trap himg hHooks hSpqr)

def SpqrRecvOkWT_ext (img : Obj.Image) (A : RustAlloc)
    (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName) (spqrRecvSpecWT A S img)

def SpqrRecvOkWT_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr spqrRecvName) (spqrRecvSpecWT A S img)

private theorem recvResultAtX_entails_recvResultAtW (F : ShaCompress) (K : MlKem)
    (A : RustAlloc) (ret : BitVec 64) (st msg : List (BitVec 8)) :
    recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st msg) ⊢
      recvResultAtW A ret ((spqrV1 F K).recv st msg) := by
  have hshape := spqrV1Recv_key_shape F K st msg
  rw [spqrV1Recv_eq] at hshape ⊢
  rw [spqrV1_eq]
  dsimp only [toSpqrRecvModel, toSpqrModel] at hshape ⊢
  cases hrecv : recv (spqrDeps F K) (spqrHkdfWith F) st msg with
  | error e =>
    cases e <;> exact Entails.refl _
  | ok r =>
    dsimp only
    cases hkey : r.key with
    | none =>
      exact sepConj_mono_right (Entails.sepExists_right true (Entails.refl _))
    | some k =>
      rcases hshape r.state k (by simp only [hrecv, hkey]) with rfl | hlen
      · exact sepConj_mono_right (Entails.sepExists_right false (Entails.refl _))
      · have hne : (some k : MessageKey) ≠ some [] := by
          intro h
          injection h with hk
          subst hk
          contradiction
        rw [recvKeyToSalt?_of_ne hne]
        dsimp only [messageKeyToSalt?]
        rw [dite_eq_left hlen]
        exact Entails.refl _

theorem spqrRecvOkWT_of_spqrRecvXT_ext (C : Crypto) (A : RustAlloc) (K : MlKem)
    (ext : String → Option (State → State)) (img : Obj.Image)
    (h1 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      (spqrRecvSpecExactKeyBounded A (spqrV1Recv C.F K) img)) :
    SpqrRecvOkWT_ext img A (spqrV1 C.F K) ext := by
  apply subroutine_ok.of_codeLoaded
  intro ⟨st, msg, ret⟩ R s0 hpc hrun hpre hsp _
  exact subroutine_ok.mono_outcome h1 ⟨st, msg, ret⟩ R s0 hpc hrun hpre hsp fun sf hout => by
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpanic⟩ | ⟨code, hex, hexit⟩ | ⟨hoom, hoom_mem⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (recvResultAtX_entails_recvResultAtW C.F K A ret st.bytes msg.bytes))))))) hpost
    · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
      dsimp only [spqrRecvSpecExactKeyBounded, spqrRecvSpecWT, spqrRecvSpecExactKey, spqrRecvSpecW, Spec.inImage] at hpanic ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpanic ⊢
      rcases hpanic with ⟨⟨hp, htr⟩, hany⟩
      refine ⟨⟨?_, htr⟩, hany⟩
      rcases hp with ha | hr
      · exact Or.inl ha
      · exact Or.inr (toSpqrModel_recvPanics_of_toSpqrRecvModel (spqrDeps C.F K)
          (spqrHkdfWith C.F) st.bytes msg.bytes hr)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hexit⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hoom, hoom_mem⟩))

theorem spqrRecvOkWT_of_v1_trap (C : Crypto) (A : RustAlloc) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSpqr : SpqrHooks C A K abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    SpqrRecvOkWT_trap img C A (spqrV1 C.F K) abs :=
  spqrRecvOkWT_of_spqrRecvXT_ext C A K (trTrapExterns C abs) img
    (spqr_recv_ok_trap C A K abs img hHooks hSpqr himg)

/-! ## 5. `generateKeys_okW_trap` and S5 + S6 Seam `pqRecvDerive_okWT_trap` -/

def GenerateKeysOkW_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr generateKeysName)
    ((generateKeysSpecW C.F A).inImage img)

private theorem optKeyAtW_eq_optKeyRecvAt_trap (A : RustAlloc) (a : BitVec 64) (k : Salt) :
    optKeyAtW A a k = spqrRecvKeyAt A a k := by
  cases k <;> rfl

theorem generateKeys_okW_trap (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    GenerateKeysOkW_trap img C A abs := by
  have : HkdfHooks C.F (trTrapExterns C abs) := hkdfHooks_trTrapExterns C abs
  have hAlloc : AllocContracts img.base A (trTrapExterns C abs) :=
    AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hH.alloc
  have h_eq : generateKeysSpecW C.F A = generateKeysSpec C.F A := by
    unfold generateKeysSpecW generateKeysSpec
    simp only [optKeyAtW_eq_optKeyRecvAt_trap]
  unfold GenerateKeysOkW_trap
  rw [h_eq]
  exact Keys.generateKeys_ok_ext himg
    (extract_ok_ext img C (trTrapExterns C abs)
      (ConsumeMessageKeyTransfer.new_from_slice_ok_ext img C.F himg
        (sessionExterns_le_trTrap C abs)))
    (expand_multi_info_ok_ext img.base C (trTrapExterns C abs))
    hAlloc

def PqRecvDeriveSpecWT_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  SpqrRecvOkWT_trap img C A S abs →
  GenerateKeysOkW_trap img C A abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      x.st.pqRatchetState.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      mkg.seed.length = 32 →
      tr.pqrState = x.st.pqRatchetState →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG tr st1 mkg draws (TokenInit img ∗ R) s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws
              (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e draws (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

private theorem pqr_len_lt_trap {A : RustAlloc} {g : SignalMessageGhost} {a : BitVec 64}
    {m : SignalMessage} {Q : SepProp} {mem : Memory}
    (h : mem ⊨ KeyDerive.signalMessageRestAt A g a m ∗ Q) :
    m.pqRatchet.length < 2 ^ 40 := by
  unfold KeyDerive.signalMessageRestAt at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1.2.2.2.1

private theorem pqr_len_lt_of_pre_trap {P F R : SepProp} {A : RustAlloc}
    {g : SignalMessageGhost} {a : BitVec 64} {m : SignalMessage} {mem : Memory}
    (h : mem ⊨ P ∗ ((KeyDerive.signalMessageRestAt A g a m ∗ F) ∗ R)) :
    m.pqRatchet.length < 2 ^ 40 := by
  have h' : mem ⊨ KeyDerive.signalMessageRestAt A g a m ∗ (F ∗ R ∗ P) := by
    have heq : P ∗ ((KeyDerive.signalMessageRestAt A g a m ∗ F) ∗ R) =
        KeyDerive.signalMessageRestAt A g a m ∗ (F ∗ R ∗ P) := by ac_rfl
    exact heq ▸ h
  exact pqr_len_lt_trap h'

private theorem spqrRecvStack_le_trap {sp0 sp : BitVec 64}
    (hstack : rootStack ≤ sp0.toNat) (hsp : sp0 - 1504#64 = sp) :
    spqrRecvStack ≤ sp.toNat := by
  subst hsp
  have h1 : rootStack = 262144 := rfl
  have h2 : spqrRecvStack = 131072 := rfl
  rw [BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_ofNat]
    omega
  · rw [BitVec.le_def]
    simp only [BitVec.toNat_ofNat]
    omega

private abbrev optKeyRestW_trap := KeyDerive.optKeyRest

private theorem optKeyAtW_split_trap (A : RustAlloc) (a : BitVec 64) (pqrKey : Salt) :
    optKeyAtW A a pqrKey ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        optKeyRestW_trap A w0 w1 w2 pqrKey ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) := by
  rw [optKeyAtW_eq_optKeyRecvAt_trap]
  exact KeyDerive.optKeyAt_split A a pqrKey

private theorem optKeyAtW_fold_trap (A : RustAlloc) (a w0 w1 w2 : BitVec 64) (pqrKey : Salt) :
    optKeyRestW_trap A w0 w1 w2 pqrKey ∗
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢
      optKeyAtW A a pqrKey := by
  rw [optKeyAtW_eq_optKeyRecvAt_trap]
  exact KeyDerive.optKeyAt_fold A a w0 w1 w2 pqrKey

private def DeriveKeysStateW_trap (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDeriveKeysPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 32 = 1#32 ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x500#64 ∧
  ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
    s.readReg64 .x8 = newPqrCap ∧
    msgW.setWidth 8 = CryptoVerification.LibsignalSessionRepr.msgTypeByte x.msgType ∧
    mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      vecU8At A (sp + 0x500#64) newPqrCap newPqrPtr newPqrState ∗
      optKeyAtW A (sp + 0x518#64) pqrKey ∗
      memRegion x.ret 48 ∗
      memRegion sp 0x10 ∗
      ((sp + 0x10#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 0x18#64) 4 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₆₄ seedCap) ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x310 ∗
      ((sp + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 0x458#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 0x45c#64) 0xa4 ∗
      memRegion (sp + 0x530#64) 0x50 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive in
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56 in
attribute [local irreducible] Program.fetch Program.externAt? in
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc in
attribute [local wp_norm] BitVec.add_assoc in
set_option maxHeartbeats 600000 in
private theorem s6_ok_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hloads : Obj.Loads libsignalSessionImage img)
    (hgen : GenerateKeysOkW_trap img C A abs)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hseed_len : mkg.seed.length = 32)
    (h6 : DeriveKeysStateW_trap A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s) :
    reaches_pc (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC img) s
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1
        (mkg.generateKeys C.F pqrKey) newPqrState draws R s0) := by
  let ext := trTrapExterns C abs
  change reaches_pc (tripleRatchetProgAtExt img.base ext)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC img) s _
  rcases h6 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25, hx27, hx28,
    seedCap, seedPtr, newPqrCap, newPqrPtr, msgW, hx8, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfrozen, hsym, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  have hentry := entryOf_eq_tripleRatchetProgAtExt (ext := ext) hloads
    CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
  change CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img =
    (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName at hentry
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDeriveKeysPC at hpc
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState
  refine reaches_pc_midMeta hfrozen hsym ?_
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC tryDecryptMidMetaCore
  rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl] at hpc
  rw [show (0x63c#64 : BitVec 64) = 1596#64 by rfl]
  rw [hentry] at hpc ⊢
  unfold GenerateKeysOkW_trap generateKeysSpecW at hgen
  change subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr generateKeysName) _ at hgen
  rw [fnAddr_callee_of_fnOff
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys")
    (k := num% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") -
      (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
    (by decide)] at hgen
  have hentry_eq :=
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq
      img.base ext).symm
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  decrypt_fetches_at_ext_cli hentry_eq 1500 96
  clear hentry_eq
  examples_hide_fetches
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29 ⊢
  clear hsp29_eq
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap at hmem ⊢
  generalize s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx27 hx28 hx29 hmem ⊢
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  refine reaches_pc_of_sepWP_frozen hmem hfrozen hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") -
      (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")))
    (RegMid := fun sm =>
      newPqrState.length ≤ newPqrCap.toNat ∧ newPqrCap.toNat < 2 ^ 63 ∧ newPqrPtr ≠ 0 ∧
      sm.readReg64 .x0 = sp + 400#64 ∧
      sm.readReg64 .x1 = sp + 864#64 ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = entry + 1596#64 ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 976#64 ∧
      sm.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid :=
      mkgAt A (sp + 400#64) mkg ∗
      optKeyAtW A (sp + 864#64) pqrKey ∗
      memRegion (sp + 1280#64) 84 ∗
      A.pool ∗ stackAt sp tryDecryptSubStack ∗
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG tr ∗
      (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
        (newPqrPtr ↦ₛ newPqrState) ∗
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 8 ∗
      ((sp + 8#64) ↦₆₄ newPqrCap) ∗
      memRegion (sp + 16#64) 12 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ newPqrPtr) ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 80 ∗
      memRegion (sp + 440#64) 424 ∗
      memRegion (sp + 888#64) 216 ∗
      memRegion (sp + 1104#64) 176 ∗
      memRegion (sp + 1364#64) 44 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      logOff img ∗
      tryDecryptSavedRegs s0.sp s0)
    ?_ ?_
  · wp_conv_pre =>
      simp only [sepConj_assoc]
      unfold vecU8At vecHeader
      rw [memRegion_split sp 8 8 (by decide),
        mr_cut_add sp 320 80 704 (by decide),
        mr_cut_add sp 400 8 696 (by decide),
        mr_cut_add sp 408 8 688 (by decide),
        mr_cut_add sp 416 8 680 (by decide),
        mr_cut_add sp 424 8 672 (by decide),
        mr_cut_add sp 432 8 664 (by decide),
        mr_cut_add sp 440 8 656 (by decide),
        mr_cut_add sp 448 8 648 (by decide),
        mr_cut_add sp 456 8 640 (by decide),
        mr_cut_add sp 464 8 632 (by decide),
        mr_cut_add sp 472 8 624 (by decide),
        mr_cut_add sp 480 8 616 (by decide),
        mr_cut_add sp 488 376 240 (by decide),
        mr_cut_add sp 864 8 232 (by decide),
        mr_cut_add sp 872 8 224 (by decide),
        mr_cut_add sp 880 8 216 (by decide),
        mr_cut_add sp 1116 4 160 (by decide),
        mr_cut_add sp 1120 8 152 (by decide),
        mr_cut_add sp 1128 8 144 (by decide),
        mr_cut_add sp 1136 8 136 (by decide),
        mr_cut_add sp 1144 8 128 (by decide),
        mr_cut_add sp 1152 8 120 (by decide),
        mr_cut_add sp 1160 8 112 (by decide)]
      simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        ProofLib.memRegion_eight (sp + 8#64),
        ProofLib.memRegion_eight (sp + 400#64),
        ProofLib.memRegion_eight (sp + 408#64),
        ProofLib.memRegion_eight (sp + 416#64),
        ProofLib.memRegion_eight (sp + 424#64),
        ProofLib.memRegion_eight (sp + 432#64),
        ProofLib.memRegion_eight (sp + 440#64),
        ProofLib.memRegion_eight (sp + 448#64),
        ProofLib.memRegion_eight (sp + 456#64),
        ProofLib.memRegion_eight (sp + 464#64),
        ProofLib.memRegion_eight (sp + 472#64),
        ProofLib.memRegion_eight (sp + 480#64),
        ProofLib.memRegion_eight (sp + 864#64),
        ProofLib.memRegion_eight (sp + 872#64),
        ProofLib.memRegion_eight (sp + 880#64),
        memRegion_four (sp + 1116#64),
        ProofLib.memRegion_eight (sp + 1120#64),
        ProofLib.memRegion_eight (sp + 1128#64),
        ProofLib.memRegion_eight (sp + 1136#64),
        ProofLib.memRegion_eight (sp + 1144#64),
        ProofLib.memRegion_eight (sp + 1152#64),
        ProofLib.memRegion_eight (sp + 1160#64),
        KeyDerive.pointsTo64_split32 (sp + 400#64)]
    refine SepWP.focus_weaken (optKeyAtW_split_trap A (sp + 1304#64) pqrKey) (by sep_focus) ?_
    wp_pull_exists
    wp_focus_pure
    rintro ⟨hnp1, hnp2, hnp3⟩
    refine SepWP.focus_rw (pointsTo32_merge64 (sp + 1112#64) mkg.counter _) (by sep_focus) ?_
    wp_steps
    rw [show ((sp + 424#64) ↦₆₄ 32#64) = ((sp + 424#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) by
      rw [hseed_len]]
    refine SepWP.focus_weaken (optKeyAtW_fold_trap A (sp + 864#64) _ _ _ pqrKey) (by sep_focus) ?_
    refine SepWP.focus_weaken (mkgAt_fold A (sp + 400#64) seedCap seedPtr _ _ mkg hseed) (by sep_focus) ?_
    have hm16 : memRegion (sp + 16#64) 12 = memRegion (sp + 16#64) 8 ∗ memRegion (sp + 24#64) 4 := by
      simpa using mr_cut_add sp 16 8 4 (by decide)
    have hm440 : memRegion (sp + 440#64) 424 =
        memRegion (sp + 440#64) 8 ∗ (memRegion (sp + 448#64) 8 ∗ (memRegion (sp + 456#64) 8 ∗
        (memRegion (sp + 464#64) 8 ∗ (memRegion (sp + 472#64) 8 ∗ (memRegion (sp + 480#64) 8 ∗
        memRegion (sp + 488#64) 376))))) := by
      rw [mr_cut_add sp 440 8 416 (by decide),
        mr_cut_add sp 448 8 408 (by decide),
        mr_cut_add sp 456 8 400 (by decide),
        mr_cut_add sp 464 8 392 (by decide),
        mr_cut_add sp 472 8 384 (by decide),
        mr_cut_add sp 480 8 376 (by decide)]
    have hm1104 : memRegion (sp + 1104#64) 176 =
        memRegion (sp + 1104#64) 8 ∗ (memRegion (sp + 1112#64) 8 ∗ (memRegion (sp + 1120#64) 8 ∗
        (memRegion (sp + 1128#64) 8 ∗ (memRegion (sp + 1136#64) 8 ∗ (memRegion (sp + 1144#64) 8 ∗
        (memRegion (sp + 1152#64) 8 ∗ (memRegion (sp + 1160#64) 8 ∗ memRegion (sp + 1168#64) 112))))))) := by
      rw [mr_cut_add sp 1104 8 168 (by decide),
        mr_cut_add sp 1112 8 160 (by decide),
        mr_cut_add sp 1120 8 152 (by decide),
        mr_cut_add sp 1128 8 144 (by decide),
        mr_cut_add sp 1136 8 136 (by decide),
        mr_cut_add sp 1144 8 128 (by decide),
        mr_cut_add sp 1152 8 120 (by decide),
        mr_cut_add sp 1160 8 112 (by decide)]
    have hm1280 : memRegion (sp + 1280#64) 84 =
        memRegion (sp + 1280#64) 8 ∗ (memRegion (sp + 1288#64) 8 ∗ (memRegion (sp + 1296#64) 8 ∗
        (memRegion (sp + 1304#64) 8 ∗ (memRegion (sp + 1312#64) 8 ∗ (memRegion (sp + 1320#64) 8 ∗
        memRegion (sp + 1328#64) 36))))) := by
      rw [mr_cut_add sp 1280 8 76 (by decide),
        mr_cut_add sp 1288 8 68 (by decide),
        mr_cut_add sp 1296 8 60 (by decide),
        mr_cut_add sp 1304 8 52 (by decide),
        mr_cut_add sp 1312 8 44 (by decide),
        mr_cut_add sp 1320 8 36 (by decide)]
    have hm1328 : memRegion (sp + 1328#64) 80 =
        memRegion (sp + 1328#64) 36 ∗ memRegion (sp + 1364#64) 44 := by
      simpa using mr_cut_add sp 1328 36 44 (by decide)
    rw [hm16, hm440, hm1104, hm1280, hm1328]
    wp_done
  · intro sm hpcm hrunm hfm hsymm hReg
    rcases hReg with ⟨hnp1, hnp2, hnp3, hx0m, hx1m, hx8m, hlrm,
      hx19m, hx20m, hx21m, hx22m, hx23m, hx24m, hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    rw [stackAt_sub sp tryDecryptSubStack generateKeysStack]
    wp_call hgen { genA := sp + 400#64, g := mkg, pqrKeyA := sp + 864#64, pqrKey := pqrKey, ret := sp + 1280#64 }
    have hm320 : memRegion (sp + 320#64) 960 =
        memRegion (sp + 320#64) 80 ∗ (memRegion (sp + 400#64) 40 ∗
        (memRegion (sp + 440#64) 424 ∗ (memRegion (sp + 864#64) 24 ∗
        (memRegion (sp + 888#64) 216 ∗ memRegion (sp + 1104#64) 176)))) := by
      rw [mr_cut_add sp 320 80 880 (by decide),
        mr_cut_add sp 400 40 840 (by decide),
        mr_cut_add sp 440 424 416 (by decide),
        mr_cut_add sp 864 24 392 (by decide),
        mr_cut_add sp 888 216 176 (by decide)]
    rw [hm320]
    wp_done

private theorem pre_spqrRecvSpecWT_trap {A : RustAlloc} {S : SpqrModel} {img : Obj.Image}
    {stArg msgArg : VecArg} {ret : BitVec 64} {sm : State} {F R : SepProp}
    (h1 : stArg.bytes.length < 2 ^ 32)
    (h2 : msgArg.bytes.length < 2 ^ 40)
    (h3 : spqrRecvStack ≤ sm.sp.toNat)
    (h : sm.mem ⊨ (spqrRecvSpecW A S img).pre (stArg, msgArg, ret) sm ∗ (F ∗ (TokenInit img ∗ R))) :
    sm.mem ⊨ (spqrRecvSpecWT A S img).pre (stArg, msgArg, ret) sm ∗ (F ∗ R) := by
  dsimp only [spqrRecvSpecWT]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨h1, h2, h3⟩, ?_⟩
  have heq : (TokenInit img ∗ (spqrRecvSpecW A S img).pre (stArg, msgArg, ret) sm) ∗ F ∗ R =
      (spqrRecvSpecW A S img).pre (stArg, msgArg, ret) sm ∗ (F ∗ (TokenInit img ∗ R)) := by ac_rfl
  exact heq ▸ h

private theorem post_spqrRecvSpecWT_trap {A : RustAlloc} {S : SpqrModel} {img : Obj.Image}
    {x : VecArg × VecArg × BitVec 64} {sm sf1 : State} {F R : SepProp}
    (h : sf1.mem ⊨ ((spqrRecvSpecWT A S img).post x sm sf1 ∗ F) ∗ R) :
    sf1.mem ⊨ ((spqrRecvSpecW A S img).post x sm sf1 ∗ F) ∗ (TokenInit img ∗ R) := by
  dsimp only [spqrRecvSpecWT] at h
  have heq : ((TokenInit img ∗ (spqrRecvSpecW A S img).post x sm sf1) ∗ F) ∗ R =
      ((spqrRecvSpecW A S img).post x sm sf1 ∗ F) ∗ (TokenInit img ∗ R) := by ac_rfl
  exact heq ▸ h

private theorem tryDecryptFnSpec_onPanic_iff_trap (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 s' : State) :
    (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 s' =
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec
    CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec Spec.inImage
  cases hp : S.recvPanics x.st.pqRatchetState x.msg.pqRatchet with
  | true => simp only [hp, true_or, or_true]
  | false =>
    simp only [CryptoVerification.LibsignalTripleRatchet.Decrypt.Model.modelFn_fst_eq_panic_iff C decFn S x hp]

private theorem onPanic_absorb_trap {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {F R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 sf ∗ (F ∗ R)) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  rw [tryDecryptFnSpec_onPanic_iff_trap] at h
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hp, hmem⟩
  refine ⟨hp, ?_⟩
  rw [← sepConj_assoc] at hmem
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem

private theorem attach_left_trap {prog : Program} {s : State} {A B : State → Prop} {c : Prop}
    (hc : c) (h : ∃ s', Steps prog s s' ∧ (A s' ∨ B s')) :
    ∃ s', Steps prog s s' ∧ ((A s' ∧ c) ∨ B s') := by
  obtain ⟨s', hs, h | h⟩ := h
  · exact ⟨s', hs, Or.inl ⟨h, hc⟩⟩
  · exact ⟨s', hs, Or.inr h⟩

open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive in
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56 in
attribute [local irreducible] Program.fetch Program.externAt? in
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc in
attribute [local wp_norm] BitVec.add_assoc in
set_option maxHeartbeats 600000 in
private theorem s5_ok_r_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hloads : Obj.Loads libsignalSessionImage img)
    (hWeak : Stage2ContractsWeak img C A ext)
    (hrecvOk : SpqrRecvOkWT_ext img A S ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hstack : rootStack ≤ s0.sp.toNat)
    (hpqr_eq : tr.pqrState = x.st.pqRatchetState)
    (h5 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG tr st1 mkg draws (TokenInit img ∗ R) s0 s)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        (DeriveKeysStateW_trap A ctl img x trG tr st1 mkg newPqrState pqrKey draws
            (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧
            s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e draws (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧
            s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R) := by
  rcases h5 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25,
    seedCap, seedPtr, msgW, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hfrozen, hsym, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  have hentry := entryOf_eq_tripleRatchetProgAtExt (ext := ext) hloads
    CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
  change CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img =
    (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName at hentry
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segPqRecvPC at hpc
  rw [show (0x5b8#64 : BitVec 64) = 1464#64 by rfl] at hpc
  rw [hentry] at hpc
  have hentry_eq :=
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq
      img.base ext).symm
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  have hrecv_call : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entry + bv% ((2^64 + ls_off% "spqr::recv" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
      (spqrRecvSpecWT A S img) := by
    rw [← hentry_eq, ← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.fnAddr_tryDecrypt_ext_eq]
    rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.tryDecrypt_add_spqrRecv_eq_fnAddr]
    exact sub_ok_at_of_fnAddr hrecvOk spqrRecvName 0 (Nat.add_zero _)
  clear hrecvOk
  have hfmt_call :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.formatInner_ok_at_entry_ext_x
      hWeak hentry_eq
  have hdealloc_call :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.dealloc_ok_at_entry_ext_x
      hWeak.toAllocContractsX hentry_eq
  decrypt_fetches_at_ext_cli hentry_eq 1464 36
  examples_hide_fetches
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  clear hsp29_eq
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx29 hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  generalize hR'_def : (TokenInit img ∗ R) = R' at hmem
  simp only [← sepConj_assoc] at hmem
  refine steps_of_sepWP hmem hL hfrozen hsym
    (mid := entry + bv% ((2^64 + ls_off% "spqr::recv" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64))
    (RegMid := fun sm =>
      sm.readReg64 .x0 = sp + 232#64 ∧
      sm.readReg64 .x1 = x.msgA ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = entry + 1488#64 ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 1280#64 ∧
      (sm.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 16 ∗
      ((sp + 16#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 24#64) 4 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ seedCap) ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 784 ∗
      ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 1116#64) 164 ∗
      memRegion (sp + 1280#64) 48 ∗
      memRegion (sp + 1328#64) 80 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      logOff img ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool)
    ?_ ?_
  · wp_steps
    have hm1116 : memRegion (sp + 1116#64) 292 =
        memRegion (sp + 1116#64) 164 ∗ (memRegion (sp + 1280#64) 48 ∗ memRegion (sp + 1328#64) 80) := by
      rw [mr_cut_add sp 1116 164 128 (by decide), mr_cut_add sp 1280 48 80 (by decide)]
    rw [hm1116]
    wp_done
  · intro sm hpcm hrunm hfm hsymm hLm hReg hmm
    subst hR'_def
    rcases hReg with ⟨hx0m, hx1m, hx8m, hlrm, hx19m, hx20m, hx21m, hx22m, hx23m, hw24m,
      hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    let stArg : VecArg := ⟨sp + 232#64, trG.pq.cap, trG.pq.ptr, tr.pqrState⟩
    let msgArg : VecArg := ⟨x.msgA, x.msgG.pqCap, x.msgG.pqPtr, x.msg.pqRatchet⟩
    have hpre_call0 : sm.mem ⊨ (spqrRecvSpecW A S img).pre (stArg, msgArg, sp + 1280#64) sm ∗
        ((signalMessageRestAt A x.msgG x.msgA x.msg ∗
          trRestAt A sp trG tr ∗
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
            (seedPtr ↦ₛ mkg.seed) ∗
            memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
          memRegion x.ret 48 ∗
          memRegion sp 16 ∗
          ((sp + 16#64) ↦₆₄ seedPtr) ∗
          memRegion (sp + 24#64) 4 ∗
          ((sp + 28#64) ↦₃₂ msgW) ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗
          ((sp + 40#64) ↦₆₄ seedCap) ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 784 ∗
          ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
          memRegion (sp + 1116#64) 164 ∗
          memRegion (sp + 1328#64) 80 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
          memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - spqrRecvStack) ∗
          tryDecryptSavedRegs s0.sp s0) ∗ (TokenInit img ∗ R)) := by
      dsimp only [spqrRecvSpecW, Spec.inImage, VecArg.at, stArg, msgArg]
      rw [hspm]
      rw [trAt_split_pq, signalMessageAt_split_pq,
        stackAt_sub sp tryDecryptSubStack spqrRecvStack] at hmm
      rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hfm, hsymm⟩, ⟨hx0m, hx1m, hx8m⟩, ?_⟩
      simp only [sepConj_assoc] at hmm ⊢
      arm64_sep_close
    have hpq_lt : msgArg.bytes.length < 2 ^ 40 := pqr_len_lt_of_pre_trap hpre_call0
    have hst_lt : stArg.bytes.length < 2 ^ 32 := by
      show tr.pqrState.length < 2 ^ 32
      rw [hpqr_eq]
      exact hQ
    have hsp_lt : spqrRecvStack ≤ sm.sp.toNat := by
      rw [hspm]
      exact spqrRecvStack_le_trap hstack hsp_def
    have hpre_callWT := pre_spqrRecvSpecWT_trap hst_lt hpq_lt hsp_lt hpre_call0
    clear hpre_call0
    cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
    | ok pair =>
      clear hentry_eq
      rcases pair with ⟨newPqrState, pqrKey⟩
      refine steps_call hrecv_call (x := (stArg, msgArg, sp + 1280#64))
        hpcm hrunm hsp_alm hlrm hfm hsymm hLm hpre_callWT
        (fun sf hpan hpost => ⟨hpan,
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.onPanic_of_spqrRecv
            (st := stArg) (msg := msgArg) (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hff1 hsymf1 hLf1 hpost1
      have hpost1W := post_spqrRecvSpecWT_trap hpost1
      clear hpost1
      dsimp only [spqrRecvSpecW, Spec.inImage, VecArg.at, stArg, msgArg] at hpost1W
      rw [hspm] at hspf1 hpost1W
      have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1W
      rcases hpost1W with ⟨⟨htrace1, hnpR⟩, hpost1W⟩
      have hnp5 : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnpR
      clear hnpR
      rw [htracem] at htrace1
      rw [hrecv] at hpost1W
      dsimp only [recvResultAtW] at hpost1W
      unfold vecU8 at hpost1W
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1W
      rcases hpost1W with ⟨newPqrCap, newPqrPtr, hpost1W⟩
      have hpost1' : sf1.mem ⊨
          vecU8At A (sp + 1280#64) newPqrCap newPqrPtr newPqrState ∗
          (optKeyAtW A (sp + 1304#64) pqrKey ∗
           trAt A (sp + 56#64) trG tr ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗
           sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 16 ∗
           ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 4 ∗
           ((sp + 28#64) ↦₃₂ msgW) ∗
           ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗
           ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 784 ∗
           ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
           ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
           memRegion (sp + 1116#64) 164 ∗
           memRegion (sp + 1328#64) 80 ∗
           protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗
           CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ (TokenInit img ∗ R) := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 24#64 = sp + 1304#64 by rw [BitVec.add_assoc]; rfl] at hpost1W
        simp only [sepConj_assoc] at hpost1W ⊢
        arm64_sep_close
      unfold vecU8At vecHeader at hpost1'
      simp only [sepConj_assoc] at hpost1'
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1'
      rcases hpost1' with ⟨⟨hnp1, hnp2, hnp3⟩, hpost1'⟩
      have hcap_not_m1 : (newPqrCap + 1#64 == 0#64) = false := cap_add_one_ne_zero hnp2
      refine attach_left_trap hnp5 ?_
      generalize hR'_def : (TokenInit img ∗ R) = R' at hpost1' ⊢
      simp only [← sepConj_assoc] at hpost1'
      unfold DeriveKeysStateW_trap
      refine steps_done_of_sepWP_midMeta (s0 := s0)
        (Rest := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64 ∧
          sf.readReg64 .x21 = x.ss ∧
          sf.readReg64 .x22 = x.msgA ∧
          sf.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64 ∧
          (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
          sf.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64 ∧
          sf.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64 ∧
          sf.readReg64 .x28 = (s0.sp - 1504#64) + 0x500#64 ∧
          ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
            sf.readReg64 .x8 = newPqrCap ∧
            msgW.setWidth 8 = CryptoVerification.LibsignalSessionRepr.msgTypeByte x.msgType ∧
            mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
            (sf.mem ⊨
              sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
              (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                (seedPtr ↦ₛ mkg.seed) ∗
                memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
              vecU8At A ((s0.sp - 1504#64) + 0x500#64) newPqrCap newPqrPtr newPqrState ∗
              optKeyAtW A ((s0.sp - 1504#64) + 0x518#64) pqrKey ∗
              memRegion x.ret 48 ∗
              memRegion (s0.sp - 1504#64) 0x10 ∗
              (((s0.sp - 1504#64) + 0x10#64) ↦₆₄ seedPtr) ∗
              memRegion ((s0.sp - 1504#64) + 0x18#64) 4 ∗
              (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
              (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
              (((s0.sp - 1504#64) + 0x28#64) ↦₆₄ seedCap) ∗
              (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
              memRegion ((s0.sp - 1504#64) + 0x140#64) 0x310 ∗
              (((s0.sp - 1504#64) + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
              (((s0.sp - 1504#64) + 0x458#64) ↦₃₂ mkg.counter) ∗
              memRegion ((s0.sp - 1504#64) + 0x45c#64) 0xa4 ∗
              memRegion ((s0.sp - 1504#64) + 0x530#64) 0x50 ∗
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R'))
        hpost1' hLf1 hff1 hsymf1 ?_
      unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDeriveKeysPC
        tryDecryptMidMetaCore CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap
      rw [hentry, show (0x5dc#64 : BitVec 64) = 1500#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]
      clear hsp29_eq
      rw [hsp_def]
      dsimp only [vecU8At, vecHeader]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done
    | error sd =>
      refine steps_call hrecv_call (x := (stArg, msgArg, sp + 1280#64))
        hpcm hrunm hsp_alm hlrm hfm hsymm hLm hpre_callWT
        (fun sf hpan hpost => ⟨hpan,
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.onPanic_of_spqrRecv
            (st := stArg) (msg := msgArg) (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hff1 hsymf1 hLf1 hpost1
      have hpost1W := post_spqrRecvSpecWT_trap hpost1
      clear hpost1
      dsimp only [spqrRecvSpecW, Spec.inImage, VecArg.at, stArg, msgArg] at hpost1W
      rw [hspm] at hspf1 hpost1W
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost1W
      rcases hpost1W with ⟨⟨htrace1, hnpR⟩, hpost1W⟩
      have hnp5 : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnpR
      clear hnpR
      rw [htracem] at htrace1
      rw [hrecv] at hpost1W
      dsimp only [recvResultAtW, errTag] at hpost1W
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1W
      rcases hpost1W with ⟨d, hpost1W⟩
      simp only [sepConj_assoc] at hpost1W
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1W
      rcases hpost1W with ⟨hd_iff, hpost1W⟩
      have hpost1' : sf1.mem ⊨
          (((sp + 1288#64) ↦₈ d) ∗
           memRegion (sp + 1289#64) 7 ∗
           ((sp + 1280#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
           memRegion (sp + 1296#64) 32 ∗
           trAt A (sp + 56#64) trG tr ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗
           sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗
           memRegion sp 16 ∗
           ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 4 ∗
           ((sp + 28#64) ↦₃₂ msgW) ∗
           ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗
           ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 784 ∗
           ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
           ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
           memRegion (sp + 1116#64) 164 ∗
           memRegion (sp + 1328#64) 80 ∗
           protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗
           CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
           logOff img ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ (TokenInit img ∗ R) := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 8#64 = sp + 1288#64 by rw [BitVec.add_assoc]; rfl,
          show (sp + 1280#64) + 9#64 = sp + 1289#64 by rw [BitVec.add_assoc]; rfl,
          mr_cut sp 1289 7 32 39 1296#64] at hpost1W
        simp only [sepConj_assoc] at hpost1W ⊢
        arm64_sep_close
      rw [show sp + 1289#64 = (sp + 1288#64) + 1#64 by rw [BitVec.add_assoc]; rfl] at hpost1'
      cases sd with
      | true =>
        have hd0 : d = 0#8 := hd_iff.mpr rfl
        subst hd0
        obtain ⟨s', hsteps', herr | ⟨hpan, hq⟩⟩ :=
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.pqRecv_recv_err_true_x
            img C (fun ct k iv => aesCbcDecrypt C.D (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) ct)
            A ctl S ext hloads x trG tr st1 mkg draws
            (TokenInit img ∗ R) s0
            hsp0_al' hseed1 hseed2 hentry hentry_eq hfmt_call hdealloc_call hsp_def
            sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
            htrace1 hvregs_1 hff1 hsymf1 hLf1 hpost1'
        · exact ⟨s', hsteps', Or.inl ⟨herr, hnp5⟩⟩
        · exact ⟨s', hsteps', Or.inr ⟨hpan, onPanic_absorb_trap hq⟩⟩
      | false =>
        have hd_ne : d ≠ 0#8 := fun h => Bool.noConfusion (hd_iff.mp h)
        obtain ⟨s', hsteps', herr | ⟨hpan, hq⟩⟩ :=
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees.pqRecv_recv_err_false_x
            img C (fun ct k iv => aesCbcDecrypt C.D (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) ct)
            A ctl S ext x trG tr st1 mkg draws
            (TokenInit img ∗ R) s0
            hmsgW hsp0_al' hseed1 hseed2 hentry hentry_eq hfmt_call hdealloc_call hsp_def hd_ne
            sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
            htrace1 hvregs_1 hff1 hsymf1 hLf1 hpost1'
        · exact ⟨s', hsteps', Or.inl ⟨herr, hnp5⟩⟩
        · exact ⟨s', hsteps', Or.inr ⟨hpan, onPanic_absorb_trap hq⟩⟩

private theorem s5_ok_r_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hloads : Obj.Loads libsignalSessionImage img)
    (hHooks : TripleRatchetHooks C A S abs)
    (hrecvOk : SpqrRecvOkWT_trap img C A S abs)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hstack : rootStack ≤ s0.sp.toNat)
    (hpqr_eq : tr.pqrState = x.st.pqRatchetState)
    (h5 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG tr st1 mkg draws (TokenInit img ∗ R) s0 s)
    (hL : (trTrapProgAt img.base C abs).CodeLoaded s.mem) :
    ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        (DeriveKeysStateW_trap A ctl img x trG tr st1 mkg newPqrState pqrKey draws
            (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧
            s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e draws (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧
            s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R) :=
  s5_ok_r_ext img C A ctl S (trTrapExterns C abs) hloads
    (stage2ContractsWeak_trap img C A S abs hHooks) hrecvOk
    x trG tr st1 mkg draws R s0 s hQ hstack hpqr_eq h5 hL

def PqRecvDeriveSpecWT_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsWeak img C A ext →
  SpqrRecvOkWT_ext img A S ext →
  GenerateKeysOkX img C A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      x.st.pqRatchetState.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      mkg.seed.length = 32 →
      tr.pqrState = x.st.pqRatchetState →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG tr st1 mkg draws (TokenInit img ∗ R) s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws
              (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e draws (TokenInit img ∗ R) s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

private theorem s6_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State))
    (hloads : Obj.Loads libsignalSessionImage img)
    (hgen : GenerateKeysOkX img C A ext)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State)
    (hseed_len : mkg.seed.length = 32)
    (h6 : DeriveKeysStateW_trap A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s) :
    reaches_pc (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC img) s
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1
        (mkg.generateKeys C.F pqrKey) newPqrState draws R s0) := by
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.deriveKeys_ok_x
    img C A ctl ext hloads hgen x trG tr st1 mkg newPqrState pqrKey draws R s0 s hseed_len ?_
  simpa only [DeriveKeysStateW_trap,
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysState,
    optKeyAtW_eq_optKeyRecvAt_trap] using h6

theorem pqRecvDerive_okWT_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel) (ext : String → Option (State → State)) :
    PqRecvDeriveSpecWT_ext img C A ctl uuidTryParse S ext := by
  intro hloads hWeak hrecvOk hgen x trG tr st1 mkg draws R s0 s hQ hstack hseed_len hpqr_eq h5 hL
  obtain ⟨s6, hsteps6, hs6⟩ :=
    s5_ok_r_ext img C A ctl S ext hloads hWeak hrecvOk x trG tr st1 mkg draws R s0 s
      hQ hstack hpqr_eq h5 hL
  cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
  | error sd =>
    rw [hrecv] at hs6
    exact ⟨s6, hsteps6, hs6⟩
  | ok pair =>
    rcases pair with ⟨newPqrState, pqrKey⟩
    rw [hrecv] at hs6
    rcases hs6 with hs6_state | hpan
    · have hL6 := hsteps6.codeLoaded hL
      obtain ⟨hs6_state, hnp⟩ := hs6_state
      rcases s6_ok_ext img C A ctl ext hloads hgen x trG tr st1 mkg newPqrState pqrKey draws
          (TokenInit img ∗ R) s0 s6 hseed_len hs6_state hL6 with
        ⟨s7, hsteps7, ⟨_, _, hs7_state⟩ | ⟨_, hfalse⟩⟩
      swap; · exact hfalse.elim
      exact ⟨s7, hsteps6.trans hsteps7, Or.inl ⟨hs7_state, hnp⟩⟩
    · exact ⟨s6, hsteps6, Or.inr hpan⟩

theorem pqRecvDerive_okWT_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel) (abs : String → Option (State → State)) :
    PqRecvDeriveSpecWT_trap img C A ctl uuidTryParse S abs := by
  intro hloads hHooks hrecvOk hgen x trG tr st1 mkg draws R s0 s hQ hstack hseed_len hpqr_eq h5 hL
  obtain ⟨s6, hsteps6, hs6⟩ :=
    s5_ok_r_trap img C A ctl S abs hloads hHooks hrecvOk x trG tr st1 mkg draws R s0 s
      hQ hstack hpqr_eq h5 hL
  cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
  | error sd =>
    rw [hrecv] at hs6
    exact ⟨s6, hsteps6, hs6⟩
  | ok pair =>
    rcases pair with ⟨newPqrState, pqrKey⟩
    rw [hrecv] at hs6
    rcases hs6 with hs6_state | hpan
    · have hL6 := hsteps6.codeLoaded hL
      obtain ⟨hs6_state, hnp⟩ := hs6_state
      rcases s6_ok_trap img C A ctl abs hloads hgen x trG tr st1 mkg newPqrState pqrKey draws
          (TokenInit img ∗ R) s0 s6 hseed_len hs6_state hL6 with
        ⟨s7, hsteps7, ⟨_, _, hs7_state⟩ | ⟨_, hfalse⟩⟩
      swap; · exact hfalse.elim
      exact ⟨s7, hsteps6.trans hsteps7, Or.inl ⟨hs7_state, hnp⟩⟩
    · exact ⟨s6, hsteps6, Or.inr hpan⟩

end CryptoVerification.Cli.LibsignalSpqrV1.M4
