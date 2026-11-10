/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# `<NoHeaderReceived>::recv_hdr_chunk`: Definitions and Specifications

**Checked by Lean.** Decode tree, ghost state, stack-frame layout, relocation combinators, and
AArch64 separation-logic specification for `<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk`
(`0x61254`, `325` instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-- Symbol name of `<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk`
    (`0x61254`, 325 instructions). -/
abbrev noHeaderReceivedRecvHdrChunkName : String :=
  "<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk"

@[simp, arm64_norm] theorem noHeaderReceivedRecvHdrChunk_fnOff :
    libsignalSessionCode.fnOff noHeaderReceivedRecvHdrChunkName = 0x5be5c :=
  libsignalSessionCode_fnOff_0x5be5c

gen_decodes libsignalSessionCode_tree recvHdrChunkBin [0x5be5c → 0x5c370]

/-- Own stack frame of `recv_hdr_chunk`: `0x60 + 0x610 = 0x670 = 1648` bytes. -/
abbrev noHeaderReceivedRecvHdrChunkFrameBytes : Nat := 1648

/-- Total stack budget of `recv_hdr_chunk` (`1648 + polyDecodedMessageStackX = 2320 + extHookStack`). -/
abbrev noHeaderReceivedRecvHdrChunkStackX : Nat :=
  noHeaderReceivedRecvHdrChunkFrameBytes + polyDecodedMessageStackX

/-- Byte size of `Chunked.SendCt.NoHeaderReceived` (`456` bytes = `0x1c8`, align `8`). -/
abbrev chunkedNoHeaderReceivedSize : Nat := 456

/-- Byte size of `Chunked.SendCt.HeaderReceived` / `Result<NoHeaderReceivedRecvChunk, Error>`
    (`480` bytes = `0x1e0`, align `8`). -/
abbrev chunkedHeaderReceivedSize : Nat := 480

/-- Representation of `NoHeaderReceivedRecvChunk` at `a` (`480` bytes = `0x1e0`, align `8`):
    - `.stillReceiving s`: discriminant `noneCap` (`-1`) at `+0`, `chunkedNoHeaderReceivedAt A (a + 8) s`
      (`456`B at `+8..+464`), and `16`B trailing padding at `+464..+480`.
    - `.done s`: niche-encoded at `+0` via `s.uc.auth.rootKey.cap ≠ noneCap ∧ ≠ none2Cap`;
      layout is `chunkedHeaderReceivedAt A a s` (`480`B). -/
def noHeaderReceivedRecvChunkAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64) :
    Chunked.SendCt.NoHeaderReceivedRecvChunk spqrPolyApi (spqrAuthApi F) → SepProp
  | .stillReceiving s =>
      ⌜PolyDecoderStrictSorted s.receiving_hdr⌝ ∗
        (a ↦₆₄ noneCap) ∗
        chunkedNoHeaderReceivedAt A (a + 8#64) s ∗
        memRegion (a + 464#64) 16
  | .done s =>
      ⌜PolyDecoderStrictSorted s.receiving_ek⌝ ∗
        chunkedHeaderReceivedAt A a s

/-- Representation of `Result<NoHeaderReceivedRecvChunk, Error>` at `a` (`480` bytes = `0x1e0`, align `8`):
    - `.ok res`: `noHeaderReceivedRecvChunkAt A a res`
    - `.error (.err e)`: discriminant `none2Cap` (`-2`) at `+0`, `spqrErrorByte e` at `+8`, and `471`B trailing
      padding at `+9..+480`.
    - `.error (.panic _)`: unreachable in normal return `post` (`False`). -/
def noHeaderReceivedRecvChunkResultAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64) :
    StatesResult (Chunked.SendCt.NoHeaderReceivedRecvChunk spqrPolyApi (spqrAuthApi F)) → SepProp
  | .ok res =>
      noHeaderReceivedRecvChunkAt A a res
  | .error (.err e) =>
      (a ↦₆₄ none2Cap) ∗
        ((a + 8#64) ↦₈ spqrErrorByte e) ∗
        memRegion (a + 9#64) 471
  | .error (.panic _) =>
      ⌜False⌝

/-- Ghost arguments of `<NoHeaderReceived>::recv_hdr_chunk` (`0x61254`). -/
structure NoHeaderReceivedRecvHdrChunkGhost (F : ShaCompress) where
  /-- Sret pointer (`x0`, 480-byte `Result<NoHeaderReceivedRecvChunk, Error>`). -/
  outA : BitVec 64
  /-- Pointer to consumed `self : Chunked.SendCt.NoHeaderReceived` (`x1`, 456 bytes). -/
  selfA : BitVec 64
  /-- Logical input state at `selfA`. -/
  self : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)
  /-- Epoch argument (`x2`). -/
  epoch : Epoch
  /-- Pointer to `chunk : &Chunk` (`x3`, 34 bytes). -/
  chunkA : BitVec 64
  /-- Logical chunk at `chunkA`. -/
  chunk : Chunk

/-- Specification of `<spqr::v1::chunked::send_ct::NoHeaderReceived>::recv_hdr_chunk`
    (`src/v1/chunked/send_ct.rs:82–110`, image offset `0x61254`, 325 instructions):
    - Consumes `chunkedNoHeaderReceivedAt A x.selfA x.self` (leaving `memRegion x.selfA 456`)
      and preserves `chunkAt x.chunkA x.chunk`.
    - When `x.self.recv_hdr_chunk x.epoch x.chunk` returns `.ok res` or `.error (.err e)`,
      writes `noHeaderReceivedRecvChunkResultAt A x.outA (x.self.recv_hdr_chunk x.epoch x.chunk)`.
    - When `x.self.recv_hdr_chunk x.epoch x.chunk` returns `.error (.panic _)` (or on OOM),
      panics via `onPanic`. -/
def noHeaderReceivedRecvHdrChunkSpec (F : ShaCompress) (A : RustAlloc) (b : BitVec 64) :
    Spec (NoHeaderReceivedRecvHdrChunkGhost F) where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.self.receiving_hdr⌝ ∗
      memRegion x.outA chunkedHeaderReceivedSize ∗
      chunkedNoHeaderReceivedAt A x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗
      stackAt s.sp noHeaderReceivedRecvHdrChunkStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      noHeaderReceivedRecvChunkResultAt A x.outA (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
      memRegion x.selfA chunkedNoHeaderReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗
      stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX
  onPanic := fun x s0 sf =>
    ⌜((x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true ∨
        allocFailedIn s0 sf) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `<NoHeaderReceived>::recv_hdr_chunk` (`0x61254`) meets
    `(noHeaderReceivedRecvHdrChunkSpec F A img.base).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def NoHeaderReceivedRecvHdrChunkOkX (img : Obj.Image) (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr noHeaderReceivedRecvHdrChunkName)
    ((noHeaderReceivedRecvHdrChunkSpec F A img.base).inImage img)

/-- `.rodata` slice at `0x837f8` (`33` bytes): `Authenticator.hdrLabel`
    (`"Signal_PQCKA_V1_MLKEM768:ekheader"`). -/
theorem rodata_hdrLabel {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ekheader")) ↦ᵣ Authenticator.hdrLabel) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_str% "Signal_PQCKA_V1_MLKEM768:ekheader")) (n := 33) (bs := Authenticator.hdrLabel)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-- Concrete value of `PolyDecoder.new 1152` (`ENCAPSULATION_KEY_SIZE = 1152`, `ptsNeeded = 576`). -/
def polyDecoderNew1152 : PolyDecoder :=
  { pts := List.replicate NUM_POLYS SortedSetPt.new
    ptsNeeded := 576
    isComplete := false }

@[simp]
theorem polyDecoder_new_1152 :
    PolyDecoder.new 1152 = .ok (.ok polyDecoderNew1152) := by
  decide

theorem polyDecoderStrictSorted_new1152 : PolyDecoderStrictSorted polyDecoderNew1152 := by
  intro s hs
  rw [polyDecoderNew1152, List.mem_replicate] at hs
  rcases hs with ⟨_, rfl⟩
  exact List.Pairwise.nil

/-! ## Stack Frame & Representation Helpers -/

/-- Portion of the stack frame only touched in the `Some(hdrFull)` branch:
    - `[fsp + 0x200 .. fsp + 0x390)` (`400`B): `receivingEk : PolyDecoder`
    - `[fsp + 0x390 .. fsp + 0x3e0)` (`80`B): `Result<HeaderReceived, Error>` scratch
    - `[fsp + 0x5a8 .. fsp + 0x610)` (`104`B): `[x29 - 0x68 .. x29)` (`epoch` copy, `concat` sret,
      `[&[u8]; 3]` / `hmac` sret, `ep.to_be_bytes()`, and `16`B unused padding). -/
def hdrSomeBranchFrameAt (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x200#64) 400 ∗
    memRegion (fsp + 0x390#64) 80 ∗
    memRegion (fsp + 0x5a8#64) 8 ∗
    memRegion (fsp + 0x5b0#64) 24 ∗
    memRegion (fsp + 0x5c8#64) 48 ∗
    memRegion (fsp + 0x5f8#64) 8 ∗
    memRegion (fsp + 0x600#64) 16

/-- Active stack frame of `recv_hdr_chunk` at `fsp = sp - 1648#64` (`[fsp .. fsp + 0x610)` = `1552` bytes):
    - `[fsp + 0x00 .. fsp + 0x58)` (`88`B = `11` cells): 4 spill cells + `self.uc` (`56`B)
    - `[fsp + 0x58 .. fsp + 0x1e8)` (`400`B): `receivingHdr : PolyDecoder`
    - `[fsp + 0x1e8 .. fsp + 0x200)` (`24`B): `decoded_message` sret (`Option<Vec<u8>>`)
    - `[fsp + 0x3e0 .. fsp + 0x5a8)` (`456`B): `.stillReceiving` staging buffer
    - `hdrSomeBranchFrameAt fsp` (`584`B). -/
def hdrActiveFrameRegionsAt (fsp : BitVec 64) : SepProp :=
  cells fsp 11 ∗
    memRegion (fsp + 0x58#64) 400 ∗
    memRegion (fsp + 0x1e8#64) 24 ∗
    memRegion (fsp + 0x3e0#64) 456 ∗
    hdrSomeBranchFrameAt fsp

theorem memRegion_1552_eq_hdrActiveFrameRegionsAt (fsp : BitVec 64) :
    memRegion fsp 1552 = hdrActiveFrameRegionsAt fsp := by
  unfold hdrActiveFrameRegionsAt hdrSomeBranchFrameAt
  rw [ProofLib.memRegion_split' (b := fsp) (n := 88) (k := 1464)
        (b' := fsp + 0x58#64) rfl rfl (by decide),
      ProofLib.memRegion_cells fsp 11 (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x58#64) (n := 400) (k := 1064)
        (b' := fsp + 0x1e8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1e8#64) (n := 24) (k := 1040)
        (b' := fsp + 0x200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x200#64) (n := 400) (k := 640)
        (b' := fsp + 0x390#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x390#64) (n := 80) (k := 560)
        (b' := fsp + 0x3e0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x3e0#64) (n := 456) (k := 104)
        (b' := fsp + 0x5a8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x5a8#64) (n := 8) (k := 96)
        (b' := fsp + 0x5b0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x5b0#64) (n := 24) (k := 72)
        (b' := fsp + 0x5c8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x5c8#64) (n := 48) (k := 24)
        (b' := fsp + 0x5f8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x5f8#64) (n := 8) (k := 16)
        (b' := fsp + 0x600#64) rfl (by bv_omega) (by decide)]
  ac_rfl

theorem stackAt_recvHdrChunk_split (sp : BitVec 64) :
    stackAt sp noHeaderReceivedRecvHdrChunkStackX =
      stackAt (sp - 1648#64) polyDecodedMessageStackX ∗
        hdrActiveFrameRegionsAt (sp - 1648#64) ∗
        cells (sp - 96#64) 12 := by
  change memRegion (sp - BitVec.ofNat 64 18704) 18704 =
    memRegion ((sp - 1648#64) - BitVec.ofNat 64 17056) 17056 ∗ _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 18704) (n := 17056) (k := 1648)
        (b' := sp - 1648#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1648#64) (n := 1552) (k := 96)
        (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      memRegion_1552_eq_hdrActiveFrameRegionsAt (sp - 1648#64),
      ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
  have hsub : (sp - 1648#64) - BitVec.ofNat 64 17056 = sp - BitVec.ofNat 64 18704 := by bv_kernel
  rw [hsub]

theorem rejoin_stack_recvHdrChunk (s0 : State) :
    stackAt (s0.sp - 1648#64) polyDecodedMessageStackX ∗
      hdrActiveFrameRegionsAt (s0.sp - 1648#64) ∗
      savedRegsAt s0 ⊢
    stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX := by
  rw [stackAt_recvHdrChunk_split s0.sp]
  exact sepConj_mono_right (sepConj_mono_right (savedRegsAt_entails_cells12 s0))

/-! ## `SplitBytes` Combinators for `NoHeaderReceived` -/

def unchunkedNoHeaderReceivedSplit (A : RustAlloc) {F : ShaCompress}
    (uc : Unchunked.SendCt.NoHeaderReceived (spqrAuthApi F)) :
    SplitBytes 56 (fun a => unchunkedNoHeaderReceivedAt A a uc) :=
  (SplitBytes.authenticatorSplit A uc.auth).seq (SplitBytes.pointsTo64 uc.epoch) (by decide)

noncomputable def chunkedNoHeaderReceivedSplit (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    SplitBytes 456 (fun a => chunkedNoHeaderReceivedAt A a st) :=
  (unchunkedNoHeaderReceivedSplit A st.uc).seq (SplitBytes.polyDecoderSplit A st.receiving_hdr) (by decide)

/-! ## Pure Model Unfolding Lemmas for `recv_hdr_chunk` -/

theorem recv_hdr_chunk_eq_do {F : ShaCompress}
    (self : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) :
    self.recv_hdr_chunk epoch chunk =
      if epoch != self.uc.epoch then
        .error (.panic (.chunkedEpochMismatch "v1/chunked/send_ct.rs:87" epoch self.uc.epoch))
      else (do
        let receivingHdr ← StatesResult.ofPanic
          ((PolyDecoder.addChunk self.receiving_hdr chunk).mapError PolyPanic.toSpqrPanic)
        let decoded? ← StatesResult.ofPanic (receivingHdr.decodedMessage.mapError PolyPanic.toSpqrPanic)
        match decoded? with
        | some hdrFull =>
          if hdrFull.length < 64 then
            .error (.panic (.decodedSliceBounds "v1/chunked/send_ct.rs:96" hdrFull.length 64))
          else
            let mac := hdrFull.drop 64
            let hdr := hdrFull.take 64
            let uc' ← (do
              if epoch != self.uc.epoch then
                .error (.panic (.unchunkedRecvHeaderEpochMismatch epoch self.uc.epoch))
              else
                let verifyRes ← StatesResult.ofPanic
                  (Authenticator.verifyHdrError F self.uc.auth self.uc.epoch hdr mac)
                match verifyRes with
                | .error _ => .error (.err .macVerifyFailed)
                | .ok () => .ok { epoch := self.uc.epoch, auth := self.uc.auth, hdr := hdr })
            .ok (.done { uc := uc', receiving_ek := polyDecoderNew1152 })
        | none =>
          .ok (.stillReceiving { uc := self.uc, receiving_hdr := receivingHdr })) :=
  rfl

theorem recv_hdr_chunk_isPanic_of_epoch_ne {F : ShaCompress}
    (self : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (hne : epoch ≠ self.uc.epoch) :
    (self.recv_hdr_chunk epoch chunk).isPanic = true := by
  refine (congrArg StatesResult.isPanic (recv_hdr_chunk_eq_do self epoch chunk)).trans ?_
  have hbeq : (epoch != self.uc.epoch) = true := by
    rw [bne_iff_ne]; exact hne
  simp [hbeq, StatesResult.isPanic, StatesError.isPanic]

theorem recv_hdr_chunk_eq_stillReceiving {F : ShaCompress}
    (self : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingHdr : PolyDecoder)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_hdr chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok none) :
    self.recv_hdr_chunk epoch chunk =
      .ok (.stillReceiving { uc := self.uc, receiving_hdr := receivingHdr }) := by
  refine (recv_hdr_chunk_eq_do self epoch chunk).trans ?_
  subst hepoch
  simp [hadd, hdec, Except.mapError, Bind.bind, Except.bind, StatesResult.ofPanic]

theorem recv_hdr_chunk_isPanic_of_lt_64 {F : ShaCompress}
    (self : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_hdr chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hlt : hdrFull.length < 64) :
    (self.recv_hdr_chunk epoch chunk).isPanic = true := by
  refine (congrArg StatesResult.isPanic (recv_hdr_chunk_eq_do self epoch chunk)).trans ?_
  subst hepoch
  simp [hadd, hdec, hlt, Except.mapError, Bind.bind, Except.bind,
    StatesResult.ofPanic, StatesResult.isPanic, StatesError.isPanic]

theorem recv_hdr_chunk_after_decode {F : ShaCompress}
    (self : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_hdr chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge : ¬ hdrFull.length < 64) :
    let hdr := hdrFull.take 64
    let mac := hdrFull.drop 64
    self.recv_hdr_chunk epoch chunk =
      match self.uc.auth.verifyHdrError F self.uc.epoch hdr mac with
      | .error p => .error (.panic (.spqr p))
      | .ok (.error _) => .error (.err .macVerifyFailed)
      | .ok (.ok ()) =>
        .ok (.done { uc := { epoch := self.uc.epoch, auth := self.uc.auth, hdr := hdr },
                     receiving_ek := polyDecoderNew1152 }) := by
  intro hdr mac
  refine (recv_hdr_chunk_eq_do self epoch chunk).trans ?_
  subst hepoch
  dsimp only [hdr, mac]
  simp only [hadd, hdec, hge,
    Except.mapError, StatesResult.ofPanic, Bind.bind, Except.bind, Pure.pure, Except.pure,
    ToStatesPanic.toStatesPanic, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  cases Authenticator.verifyHdrError F self.uc.auth self.uc.epoch (hdrFull.take 64) (hdrFull.drop 64) with
  | error p => rfl
  | ok v =>
    cases v with
    | error e => rfl
    | ok u => cases u; rfl

theorem verifyHdrError_of_mac_gt_32 (F : ShaCompress) (auth : Authenticator) (ep : Epoch)
    (hdr mac : Bytes)
    (hk : auth.macKey.length < 2 ^ 32)
    (hd : (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr).length < 2 ^ 32)
    (hm : ¬ mac.length ≤ 32) :
    auth.verifyHdrError F ep hdr mac = .error .compareBounds := by
  simp [Authenticator.verifyHdrError, Authenticator.verifyHdr,
    Authenticator.macHdr_of_lt F auth ep hdr hk hd, LibsignalSpqrV1.compare, hm,
    Bind.bind, Except.bind, Except.map]

theorem verifyHdrError_of_mac_le_32 (F : ShaCompress) (auth : Authenticator) (ep : Epoch)
    (hdr mac : Bytes)
    (hk : auth.macKey.length < 2 ^ 32)
    (hd : (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr).length < 2 ^ 32)
    (hm : mac.length ≤ 32) :
    auth.verifyHdrError F ep hdr mac =
      if compare_prefix mac (auth.macHdrUnchecked F ep hdr) != 0#8 then
        .ok (.error .macVerifyFailed)
      else
        .ok (.ok ()) := by
  unfold Authenticator.verifyHdrError
  rw [Authenticator.verifyHdr_eq_ok_prefix F auth ep hdr mac hk hd hm]
  unfold Authenticator.verifyHdr_prefix
  by_cases hc : compare_prefix mac (auth.macHdrUnchecked F ep hdr) != 0#8 <;>
    simp [hc, Except.map, Except.mapError, AuthError.toError]

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
