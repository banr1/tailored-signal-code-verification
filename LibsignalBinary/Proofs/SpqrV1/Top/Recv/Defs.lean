/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpers
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpers
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.Specs
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep

/-!
# `spqr::recv`: Stack Frame Layout, `.rodata` Bundle, and Callee Contracts

**Checked by Lean.** Read-only `.rodata` bundle (`spqrRecvRoAt`), callee contract bundle
(`SpqrRecvContracts`), 4992-byte stack frame layout, and `statesRecvPreInv` representation bridges
for `spqr::recv` (`0x5462c`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. Read-Only `.rodata` Bundle and Callee Contract Bundle (`SpqrRecvContracts`) -/

/-- Read-only `.rodata` + `MAX_LOG_LEVEL_FILTER` + `TOKEN` bundle used across `spqr::recv` (`0x5462c`)
    and its callees (`spqr::decode_state`, `States::from_pb`, `States::recv`, `States::into_pb`,
    and `drop_glue::<PqRatchetState>`):
    - `Prost.MessageMerge.v1StateJumpTablesAt b` (used by `spqr::decode_state`),
    - `statesFromPbJumpTableAt b` (used by `States::from_pb`),
    - `statesRecvRoAt b` (includes `statesRecvJumpTableAt b`, `unchunkedSendCt2RoAt b` with
    `(b + 0xaa080#64) ↦₆₄ 0#64` for `logOff`, `tokenInitAt b`, and `reduceTableAt b`),
    - `statesIntoPbJumpTableAt b` (used by `States::into_pb`),
    - `dropOptProtoInnerStateJumpTableAt b` (used by `drop_glue::<PqRatchetState>`). -/
def spqrRecvRoAt (b : BitVec 64) : SepProp :=
  Prost.MessageMerge.v1StateJumpTablesAt b ∗
  statesFromPbJumpTableAt b ∗
  statesRecvRoAt b ∗
  statesIntoPbJumpTableAt b

/-- Bundle of callee `subroutine_ok` contracts and image/allocator hypotheses for `spqr::recv`
    (`0x5462c..0x55208`, 759 instructions). All drop-glue callees (`0x4c060`, `0x4c0d4`,
    `0x4c3a0`, `0x4c460`, `0x4c5d8`, `0x4cfa8`) are already unconditionally proved in
    `LibsignalBinary.Proofs.SpqrV1.Drop.*` from `hA.dealloc`. -/
structure SpqrRecvContracts (H_inner : V1InnerHeapPred) (img : Obj.Image) (A : RustAlloc)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  base_aligned : img.base &&& 0xfff#64 = 0#64
  himg : Obj.Loads libsignalSessionImage img
  hA : AllocContracts img.base A ext
  decodeState_ok : DecodeStateOkX H_inner img A ext
  initInner_ok : InitInnerOkX img A F ext
  chainFrom_ok : ChainFromOkX img (spqrHkdfWith F) A ext
  chainFromPb_ok : ChainFromPbOkX img A ext
  chainNew_ok : ChainNewOkX img (spqrHkdfWith F) A ext
  chainAddEpoch_ok : ChainAddEpochOkX img (spqrHkdfWith F) A ext
  chainRecvKey_ok : ChainRecvKeyOkX img (spqrHkdfWith F) A ext
  chainIntoPb_ok : ChainIntoPbOkX img A ext
  messageDeserialize_ok : MessageDeserializeOkX spqrPolyApi img A ext
  statesFromPb_ok : StatesFromPbOkX img A F ext
  statesRecv_ok : StatesRecvOkX img A F K ext
  statesIntoPb_ok : StatesIntoPbOkX img A F ext
  encodeToVec_ok : PqRatchetStateEncodeToVecOkX img A ext
  /-- Representation equivalence between `DecodeState.optProtoInnerStateAt H_inner A a opt` and
      `Drop.optProtoInnerStateAt A a opt` (used by `States::from_pb`, `States::into_pb`,
      `spqr::init_inner`, and `drop_glue`; discharged by
      `optProtoInnerStateAt_canonical_eq_drop` when `H_inner = canonicalV1InnerHeap`). -/
  h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt

/-!
## 2. Stack Frame Layout (`0x1380 = 4992` bytes)

Stack slots of `spqr::recv` (`fsp = s0.sp - 4992#64`, `x29 = s0.sp - 96#64 = fsp + 0x1320#64`):
* `fsp + 0x000 .. fsp + 0x160` (`352`B): `pre_pb : PqRatchetState` (`spqr::decode_state` output).
* `fsp + 0x160 .. fsp + 0x2c0` (`352`B): `state_pb : PqRatchetState` (active state on V1 path).
* `fsp + 0x2c0 .. fsp + 0x318` (`88`B): `Chain` slot 1 (V0 chain-ratchet path).
* `fsp + 0x318 .. fsp + 0x370` (`88`B): `Chain` slot 2 (`init_inner` / `chain_from` path).
* `fsp + 0x370 .. fsp + 0x3d0` (`96`B): `scka_msg : Message` (`48`B at `+0x370`) and scratch (`+0x3a0..+0x3d0`).
* `fsp + 0x3d0 .. fsp + 0x770` (`928`B): `st1 : States` (`V1Recv.state` moved from `States::recv`).
* `fsp + 0x770 .. fsp + 0x790` (`32`B): scratch (`q0, x8`).
* `fsp + 0x790 .. fsp + 0xb50` (`960`B): shared sret buffer (`decode_state`, `Chain::from_pb`,
  `Chain::recv_key`, `init_inner`, `Message::deserialize`, `States::recv`, `chain_from`,
  `EpochSecret`, and `PqRatchetState` for `encode_to_vec` / `drop_glue`).
* `fsp + 0xb50 .. fsp + 0xef8` (`936`B): shared sret buffer (`chain_from`, `States::from_pb`,
  `States::into_pb`, `encode_to_vec` `Vec<u8>` sret, `Chain::new`).
* `fsp + 0xef8 .. fsp + 0x1298` (`928`B): `st0 : States` (`States::from_pb` output moved for `States::recv`).
* `fsp + 0x1298 .. fsp + 0x12f0` (`x29 - 0x88 .. x29 - 0x30`, `88`B): `chain : Chain` on V1 path.
* `fsp + 0x12f0 .. fsp + 0x1320` (`x29 - 0x30 .. x29`, `48`B): scratch.
* `fsp + 0x1320 .. fsp + 0x1380` (`s0.sp - 96 .. s0.sp`, `96`B): saved registers `x29..x19`.
-/

/-- Own stack frame of `spqr::recv` (`0x5462c`): `0x60 + 0x1000 + 0x320 = 0x1380 = 4992` bytes
    (`s0.sp - 4992#64`). -/
abbrev spqrRecvOwnFrame : Nat := 0x1380

/-- Remaining callee stack budget below `s0.sp - 4992#64`: `131072 - 4992 = 126080` bytes. -/
abbrev spqrRecvCalleeStackX : Nat := 126080

theorem spqrRecvStack_eq : spqrRecvStack = spqrRecvCalleeStackX + spqrRecvOwnFrame := by decide

/-- Saved callee-saved registers at `[sp + 0x1320 .. sp + 0x1380)` (`sp = s0.sp - 0x1380`, `12`
    words = `96` bytes). -/
def spqrRecvSavedRegs (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp + 0x1320#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp + 0x1328#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp + 0x1330#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp + 0x1338#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp + 0x1340#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp + 0x1348#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp + 0x1350#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp + 0x1358#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp + 0x1360#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp + 0x1368#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp + 0x1370#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp + 0x1378#64) ↦₆₄ s0.readReg64 .x19)

theorem spqrRecvSavedRegs_entails_memRegion (sp : BitVec 64) (s0 : State) :
    spqrRecvSavedRegs sp s0 ⊢ memRegion (sp + 0x1320#64) 96 := by
  unfold spqrRecvSavedRegs
  have hcell (off : BitVec 64) (v : BitVec 64) :
      ((sp + off) ↦₆₄ v) ⊢ memRegion (sp + off) 8 :=
    ProofLib.pointsTo64_entails_memRegion (sp + off) v
  rw [ProofLib.memRegion_split (sp + 0x1320#64) 8 88 (by decide),
      ProofLib.memRegion_split (sp + 0x1320#64 + 8#64) 8 80 (by decide),
      ProofLib.memRegion_split (sp + 0x1320#64 + 8#64 + 8#64) 8 72 (by decide),
      ProofLib.memRegion_split (sp + 0x1320#64 + 8#64 + 8#64 + 8#64) 8 64 (by decide),
      ProofLib.memRegion_split (sp + 0x1320#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 56 (by decide),
      ProofLib.memRegion_split (sp + 0x1320#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
      ProofLib.memRegion_split (sp + 0x1320#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
      ProofLib.memRegion_split (sp + 0x1320#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
      ProofLib.memRegion_split (sp + 0x1320#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
      ProofLib.memRegion_split (sp + 0x1320#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
      ProofLib.memRegion_split (sp + 0x1320#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _)
    (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _)
    (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _)
    (sepConj_mono (hcell _ _) (sepConj_mono (hcell _ _) (hcell _ _)))))))))))

theorem stackAt_spqrRecv_eq_callee_and_frame (sp0 : BitVec 64) :
    stackAt sp0 spqrRecvStack =
      stackAt (sp0 - 0x1380#64) spqrRecvCalleeStackX ∗
      memRegion (sp0 - 0x1380#64) 0x1320 ∗
      memRegion (sp0 - 0x1380#64 + 0x1320#64) 96 := by
  simp only [stackAt]
  have h1 := ProofLib.memRegion_split (sp0 - BitVec.ofNat 64 spqrRecvStack)
    spqrRecvCalleeStackX 4992 (by decide)
  have h1' : spqrRecvCalleeStackX + 4992 = spqrRecvStack := rfl
  rw [h1'] at h1
  have h2 := ProofLib.memRegion_split (sp0 - 0x1380#64) 0x1320 96 (by decide)
  have h2' : 0x1320 + 96 = (4992 : Nat) := rfl
  rw [h2'] at h2
  have ha : (sp0 - 0x1380#64) - BitVec.ofNat 64 spqrRecvCalleeStackX =
      sp0 - BitVec.ofNat 64 spqrRecvStack := by
    change (sp0 - 4992#64) - 126080#64 = sp0 - 131072#64
    bv_omega
  have hb : (sp0 - BitVec.ofNat 64 spqrRecvStack) + BitVec.ofNat 64 spqrRecvCalleeStackX =
      sp0 - 0x1380#64 := by
    change (sp0 - 131072#64) + 126080#64 = sp0 - 4992#64
    bv_omega
  rw [h1, hb, ← ha, h2]

theorem stack_restore_spqrRecv (sp0 : BitVec 64) (s0 : State) :
    stackAt (sp0 - 0x1380#64) spqrRecvCalleeStackX ∗
      memRegion (sp0 - 0x1380#64) 0x1320 ∗
      spqrRecvSavedRegs (sp0 - 0x1380#64) s0 ⊢
      stackAt sp0 spqrRecvStack := by
  rw [stackAt_spqrRecv_eq_callee_and_frame sp0]
  exact sepConj_mono_right (sepConj_mono_right (spqrRecvSavedRegs_entails_memRegion (sp0 - 0x1380#64) s0))

private theorem sepExists_const {α : Sort _} [Inhabited α] (P : SepProp) :
    (∃∗ _ : α, P) = P :=
  ProofLib.Entails.antisymm
    (Entails.sepExists_elim fun _ => Entails.refl P)
    (Entails.sepExists_right default (Entails.refl P))

private theorem sepExists_proj {α β : Type} (π : α → β) (ι : β → α)
    (hπ : ∀ b, π (ι b) = b) (F : β → SepProp) :
    (∃∗ g : α, F (π g)) = ∃∗ b : β, F b :=
  ProofLib.Entails.antisymm
    (Entails.sepExists_elim fun g => Entails.sepExists_right (π g) (Entails.refl (F (π g))))
    (Entails.sepExists_elim fun b =>
      Entails.sepExists_right (ι b) (by rw [hπ b]; exact Entails.refl (F b)))

private theorem sepExists_prod {β₁ β₂ : Type} (F : β₁ × β₂ → SepProp) :
    (∃∗ p : β₁ × β₂, F p) = ∃∗ b₁ : β₁, ∃∗ b₂ : β₂, F (b₁, b₂) :=
  ProofLib.Entails.antisymm
    (Entails.sepExists_elim fun ⟨b₁, b₂⟩ =>
      Entails.sepExists_right b₁ (Entails.sepExists_right b₂ (Entails.refl (F (b₁, b₂)))))
    (Entails.sepExists_elim fun b₁ =>
      Entails.sepExists_elim fun b₂ =>
        Entails.sepExists_right (b₁, b₂) (Entails.refl (F (b₁, b₂))))

private theorem optKeysUnsampledPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.KeysUnsampled) :
    optKeysUnsampledPBAt A a opt =
      ∃∗ g : Unchunked2PBGhost, optKeysUnsampledPBPinnedAt A g a opt := by
  cases opt with
  | none => exact (sepExists_const _).symm
  | some u => exact unchunked2At_eq_exists_pinned A a u.epoch u.auth

private theorem optNoHeaderReceivedPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.NoHeaderReceived) :
    optNoHeaderReceivedPBAt A a opt =
      ∃∗ g : Unchunked2PBGhost, optNoHeaderReceivedPBPinnedAt A g a opt := by
  cases opt with
  | none => exact (sepExists_const _).symm
  | some u => exact unchunked2At_eq_exists_pinned A a u.epoch u.auth

private theorem optCt2SentPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.Ct2Sent) :
    optCt2SentPBAt A a opt =
      ∃∗ g : Unchunked2PBGhost, optCt2SentPBPinnedAt A g a opt := by
  cases opt with
  | none => exact (sepExists_const _).symm
  | some u => exact unchunked2At_eq_exists_pinned A a u.epoch u.auth

private theorem optHeaderReceivedPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderReceived) :
    optHeaderReceivedPBAt A a opt =
      ∃∗ g : Unchunked3PBGhost, optHeaderReceivedPBPinnedAt A g a opt := by
  cases opt with
  | none => exact (sepExists_const _).symm
  | some u => exact unchunked3At_eq_exists_pinned A a u.epoch u.auth u.hdr

private theorem optHeaderSentPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderSent) :
    optHeaderSentPBAt A a opt =
      ∃∗ g : Unchunked4PBGhost, optHeaderSentPBPinnedAt A g a opt := by
  cases opt with
  | none => exact (sepExists_const _).symm
  | some u => exact unchunked4At_eq_exists_pinned A a u.epoch u.auth u.ek u.dk

private theorem optEkSentCt1ReceivedPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.EkSentCt1Received) :
    optEkSentCt1ReceivedPBAt A a opt =
      ∃∗ g : Unchunked4PBGhost, optEkSentCt1ReceivedPBPinnedAt A g a opt := by
  cases opt with
  | none => exact (sepExists_const _).symm
  | some u => exact unchunked4At_eq_exists_pinned A a u.epoch u.auth u.dk u.ct1

private theorem optCt1SentEkReceivedPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.Ct1SentEkReceived) :
    optCt1SentEkReceivedPBAt A a opt =
      ∃∗ g : Unchunked5PBGhost, optCt1SentEkReceivedPBPinnedAt A g a opt := by
  cases opt with
  | none => exact (sepExists_const _).symm
  | some u => exact unchunked5At_eq_exists_pinned A a u.epoch u.auth u.es u.ek u.ct1

theorem v1StatePBAt_eq_optProtoInnerStateAt (A : RustAlloc) (a : BitVec 64) (m : V1State) :
    v1StatePBAt A a m = Drop.optProtoInnerStateAt A a m.innerState := by
  unfold v1StatePBAt v1StatePBPinnedAt Drop.optProtoInnerStateAt
  cases m.innerState with
  | none =>
    exact sepExists_const _
  | some is =>
    cases is with
    | keysUnsampled v =>
      unfold v1StateInnerPBPinnedAt Drop.protoInnerStateAt; dsimp only
      rw [← chunkedKeysUnsampledPBAt_eq_proto]
      unfold chunkedKeysUnsampledPBAt
      rw [sepExists_proj (fun g : V1StatePBGhost => g.a.gKeysUnsampled)
            (fun x => ⟨{ (default : V1StatePBGhostA) with gKeysUnsampled := x }, default⟩) (fun _ => rfl)
            (fun x => (a ↦₆₄ 0x8000000000000000#64) ∗
              optKeysUnsampledPBPinnedAt A x (a + 8#64) v.uc ∗ memRegion (a + 64#64) 160),
          ← sepExists_sepConj_right, ← sepExists_sepConj_left,
          ← optKeysUnsampledPBAt_eq_exists_pinned]
    | keysSampled v =>
      unfold v1StateInnerPBPinnedAt Drop.protoInnerStateAt; dsimp only
      rw [← chunkedKeysSampledPBAt_eq_proto]
      unfold chunkedKeysSampledPBAt
      have haddr : a + 8#64 + 104#64 = a + 112#64 := by bv_omega
      rw [haddr,
          sepExists_proj (fun g : V1StatePBGhost => g.a.gKeysSampled)
            (fun x => ⟨{ (default : V1StatePBGhostA) with gKeysSampled := x }, default⟩) (fun _ => rfl)
            (fun x => (a ↦₆₄ 0x8000000000000001#64) ∗
              optHeaderSentPBPinnedAt A x.1 (a + 8#64) v.uc ∗
              optPolynomialEncoderPBPinnedAt A x.2 (a + 112#64) v.sendingHdr ∗
              memRegion (a + 168#64) 56),
          sepExists_prod]
      simp only [← sepExists_sepConj_right, ← sepExists_sepConj_left,
        ← optHeaderSentPBAt_eq_exists_pinned, ← optPolynomialEncoderPBAt_eq_exists_pinned,
        sepConj_assoc]
    | headerSent v =>
      unfold v1StateInnerPBPinnedAt Drop.protoInnerStateAt; dsimp only
      rw [← chunkedHeaderSentPBAt_eq_proto]
      rw [sepExists_proj (fun g : V1StatePBGhost => g.a.gHeaderSent)
            (fun x => ⟨{ (default : V1StatePBGhostA) with gHeaderSent := x }, default⟩) (fun _ => rfl)
            (fun x => (a ↦₆₄ 0x8000000000000002#64) ∗
              chunkedHeaderSentPBPinnedAt A x (a + 8#64) v ∗ memRegion (a + 184#64) 40),
          ← sepExists_sepConj_right, ← sepExists_sepConj_left,
          ← chunkedHeaderSentPBAt_eq_exists_pinned]
    | ct1Received v =>
      unfold v1StateInnerPBPinnedAt Drop.protoInnerStateAt; dsimp only
      rw [← chunkedCt1ReceivedPBAt_eq_proto]
      unfold chunkedCt1ReceivedPBAt
      have haddr : a + 8#64 + 104#64 = a + 112#64 := by bv_omega
      rw [haddr,
          sepExists_proj (fun g : V1StatePBGhost => g.a.gCt1Received)
            (fun x => ⟨{ (default : V1StatePBGhostA) with gCt1Received := x }, default⟩) (fun _ => rfl)
            (fun x => (a ↦₆₄ 0x8000000000000003#64) ∗
              optEkSentCt1ReceivedPBPinnedAt A x.1 (a + 8#64) v.uc ∗
              optPolynomialEncoderPBPinnedAt A x.2 (a + 112#64) v.sendingEk ∗
              memRegion (a + 168#64) 56),
          sepExists_prod]
      simp only [← sepExists_sepConj_right, ← sepExists_sepConj_left,
        ← optEkSentCt1ReceivedPBAt_eq_exists_pinned, ← optPolynomialEncoderPBAt_eq_exists_pinned,
        sepConj_assoc]
    | ekSentCt1Received v =>
      unfold v1StateInnerPBPinnedAt Drop.protoInnerStateAt; dsimp only
      rw [← chunkedEkSentCt1ReceivedPBAt_eq_proto]
      unfold chunkedEkSentCt1ReceivedPBAt
      have haddr : a + 8#64 + 104#64 = a + 112#64 := by bv_omega
      rw [haddr,
          sepExists_proj (fun g : V1StatePBGhost => g.a.gEkSentCt1Received)
            (fun x => ⟨{ (default : V1StatePBGhostA) with gEkSentCt1Received := x }, default⟩) (fun _ => rfl)
            (fun x => (a ↦₆₄ 0x8000000000000004#64) ∗
              optEkSentCt1ReceivedPBPinnedAt A x.1 (a + 8#64) v.uc ∗
              optPolynomialDecoderPBPinnedAt A x.2 (a + 112#64) v.receivingCt2 ∗
              memRegion (a + 152#64) 72),
          sepExists_prod]
      simp only [← sepExists_sepConj_right, ← sepExists_sepConj_left,
        ← optEkSentCt1ReceivedPBAt_eq_exists_pinned, ← optPolynomialDecoderPBAt_eq_exists_pinned,
        sepConj_assoc]
    | noHeaderReceived v =>
      unfold v1StateInnerPBPinnedAt Drop.protoInnerStateAt; dsimp only
      rw [← chunkedNoHeaderReceivedPBAt_eq_proto]
      unfold chunkedNoHeaderReceivedPBAt
      have haddr : a + 8#64 + 40#64 = a + 48#64 := by bv_omega
      rw [haddr,
          sepExists_proj (fun g : V1StatePBGhost => g.a.gNoHeaderReceived)
            (fun x => ⟨{ (default : V1StatePBGhostA) with gNoHeaderReceived := x }, default⟩) (fun _ => rfl)
            (fun x => (a ↦₆₄ 0x8000000000000005#64) ∗
              optPolynomialDecoderPBPinnedAt A x.1 (a + 8#64) v.receivingHdr ∗
              optNoHeaderReceivedPBPinnedAt A x.2 (a + 48#64) v.uc ∗
              memRegion (a + 104#64) 120),
          sepExists_prod]
      simp only [← sepExists_sepConj_right, ← sepExists_sepConj_left,
        ← optPolynomialDecoderPBAt_eq_exists_pinned, ← optNoHeaderReceivedPBAt_eq_exists_pinned,
        sepConj_assoc]
    | headerReceived v =>
      unfold v1StateInnerPBPinnedAt Drop.protoInnerStateAt; dsimp only
      rw [← chunkedHeaderReceivedPBAt_eq_proto]
      unfold chunkedHeaderReceivedPBAt
      have haddr : a + 8#64 + 80#64 = a + 88#64 := by bv_omega
      rw [haddr,
          sepExists_proj (fun g : V1StatePBGhost => g.b.gHeaderReceived)
            (fun x => ⟨default, { (default : V1StatePBGhostB) with gHeaderReceived := x }⟩) (fun _ => rfl)
            (fun x => (a ↦₆₄ 0x8000000000000006#64) ∗
              optHeaderReceivedPBPinnedAt A x.1 (a + 8#64) v.uc ∗
              optPolynomialDecoderPBPinnedAt A x.2 (a + 88#64) v.receivingEk ∗
              memRegion (a + 128#64) 96),
          sepExists_prod]
      simp only [← sepExists_sepConj_right, ← sepExists_sepConj_left,
        ← optHeaderReceivedPBAt_eq_exists_pinned, ← optPolynomialDecoderPBAt_eq_exists_pinned,
        sepConj_assoc]
    | ct1Sampled v =>
      unfold v1StateInnerPBPinnedAt Drop.protoInnerStateAt; dsimp only
      rw [← chunkedCt1SampledPBAt_eq_proto]
      rw [sepExists_proj (fun g : V1StatePBGhost => g.b.gCt1Sampled)
            (fun x => ⟨default, { (default : V1StatePBGhostB) with gCt1Sampled := x }⟩) (fun _ => rfl)
            (fun x => chunkedCt1SampledPBPinnedAt A x a v),
          ← chunkedCt1SampledPBAt_eq_exists_pinned]
    | ekReceivedCt1Sampled v =>
      unfold v1StateInnerPBPinnedAt Drop.protoInnerStateAt; dsimp only
      rw [← chunkedEkReceivedCt1SampledPBAt_eq_proto]
      unfold chunkedEkReceivedCt1SampledPBAt
      have haddr : a + 8#64 + 128#64 = a + 136#64 := by bv_omega
      rw [haddr,
          sepExists_proj (fun g : V1StatePBGhost => g.b.gEkReceivedCt1Sampled)
            (fun x => ⟨default, { (default : V1StatePBGhostB) with gEkReceivedCt1Sampled := x }⟩) (fun _ => rfl)
            (fun x => (a ↦₆₄ 0x8000000000000008#64) ∗
              optCt1SentEkReceivedPBPinnedAt A x.1 (a + 8#64) v.uc ∗
              optPolynomialEncoderPBPinnedAt A x.2 (a + 136#64) v.sendingCt1 ∗
              memRegion (a + 192#64) 32),
          sepExists_prod]
      simp only [← sepExists_sepConj_right, ← sepExists_sepConj_left,
        ← optCt1SentEkReceivedPBAt_eq_exists_pinned, ← optPolynomialEncoderPBAt_eq_exists_pinned,
        sepConj_assoc]
    | ct1Acknowledged v =>
      unfold v1StateInnerPBPinnedAt Drop.protoInnerStateAt; dsimp only
      rw [← chunkedCt1AcknowledgedPBAt_eq_proto]
      unfold chunkedCt1AcknowledgedPBAt
      have haddr : a + 8#64 + 128#64 = a + 136#64 := by bv_omega
      rw [haddr,
          sepExists_proj (fun g : V1StatePBGhost => g.b.gCt1Acknowledged)
            (fun x => ⟨default, { (default : V1StatePBGhostB) with gCt1Acknowledged := x }⟩) (fun _ => rfl)
            (fun x => (a ↦₆₄ 0x8000000000000009#64) ∗
              optCt1SentPBPinnedAt A x.1 (a + 8#64) v.uc ∗
              optPolynomialDecoderPBPinnedAt A x.2 (a + 136#64) v.receivingEk ∗
              memRegion (a + 176#64) 48),
          sepExists_prod]
      simp only [← sepExists_sepConj_right, ← sepExists_sepConj_left,
        ← optCt1SentPBAt_eq_exists_pinned, ← optPolynomialDecoderPBAt_eq_exists_pinned,
        sepConj_assoc]
    | ct2Sampled v =>
      unfold v1StateInnerPBPinnedAt Drop.protoInnerStateAt; dsimp only
      rw [← chunkedCt2SampledPBAt_eq_proto]
      unfold chunkedCt2SampledPBAt
      have haddr : a + 8#64 + 56#64 = a + 64#64 := by bv_omega
      rw [haddr,
          sepExists_proj (fun g : V1StatePBGhost => g.b.gCt2Sampled)
            (fun x => ⟨default, { (default : V1StatePBGhostB) with gCt2Sampled := x }⟩) (fun _ => rfl)
            (fun x => (a ↦₆₄ 0x800000000000000a#64) ∗
              optPolynomialEncoderPBPinnedAt A x.1 (a + 8#64) v.sendingCt2 ∗
              optCt2SentPBPinnedAt A x.2 (a + 64#64) v.uc ∗
              memRegion (a + 120#64) 104),
          sepExists_prod]
      simp only [← sepExists_sepConj_right, ← sepExists_sepConj_left,
        ← optPolynomialEncoderPBAt_eq_exists_pinned, ← optCt2SentPBAt_eq_exists_pinned,
        sepConj_assoc]

theorem protoPqRatchetStateAt_eq_pqRatchetStatePBAt (A : RustAlloc) (a : BitVec 64)
    (st : PqRatchetState) :
    Drop.protoPqRatchetStateAt A a st = Prost.EncodeToVec.pqRatchetStatePBAt A a st := by
  unfold Drop.protoPqRatchetStateAt Prost.EncodeToVec.pqRatchetStatePBAt
  congr 2
  cases st.inner with
  | none => rfl
  | some inn =>
    cases inn with
    | v1 v1 =>
      unfold Drop.optProtoPqRatchetInnerAt Prost.EncodeToVec.optPqRatchetInnerPBAt
      exact (v1StatePBAt_eq_optProtoInnerStateAt A (a + 128#64) v1).symm

/-! ## 3. `v1StatePtsBound` and `statesRecvPreInv` from `spqrDecodeState` -/

theorem sortedSetPtStrictSorted_withCapacity (cap : Nat) :
    Poly.AddChunk.SortedSetPtStrictSorted (SortedSetPt.withCapacity cap) :=
  List.Pairwise.nil

theorem sortedSetPtStrictSorted_push {s : SortedSetPt} (pt : Pt)
    (hsort : Poly.AddChunk.SortedSetPtStrictSorted s) :
    Poly.AddChunk.SortedSetPtStrictSorted (s.push pt).1 := by
  have ⟨heq, hsort'⟩ := Poly.AddChunk.bsearchPush_eq_push s pt hsort
  exact heq ▸ hsort'

theorem sortedSetPtStrictSorted_pushChunksExact4Total :
    ∀ (pts : List (BitVec 8)) (v : SortedSetPt),
      Poly.AddChunk.SortedSetPtStrictSorted v →
      Poly.AddChunk.SortedSetPtStrictSorted (pushChunksExact4Total pts v)
  | [], _v, hv => hv
  | [_], _v, hv => hv
  | [_, _], _v, hv => hv
  | [_, _, _], _v, hv => hv
  | b0 :: b1 :: b2 :: b3 :: rest, v, hv =>
    sortedSetPtStrictSorted_pushChunksExact4Total rest
      (v.push { x := GF16.new (u16FromBeBytes b0 b1), y := GF16.new (u16FromBeBytes b2 b3) }).1
      (sortedSetPtStrictSorted_push _ hv)

theorem sortedSetPtStrictSorted_of_decodeDecoderPbPtsTotal :
    ∀ {bss : List (List (BitVec 8))} {outPts : List SortedSetPt},
      decodeDecoderPbPtsTotal bss = .ok outPts →
      ∀ s ∈ outPts, Poly.AddChunk.SortedSetPtStrictSorted s
  | [], _, h, s, hs => by
    cases h
    cases hs
  | pts :: rest, outPts, h, s, hs => by
    unfold decodeDecoderPbPtsTotal at h
    split at h
    · contradiction
    · dsimp only at h
      cases hrest : decodeDecoderPbPtsTotal rest with
      | error _ => rw [hrest] at h; contradiction
      | ok tail =>
        rw [hrest] at h
        cases h
        rcases List.mem_cons.mp hs with rfl | hmem
        · exact sortedSetPtStrictSorted_pushChunksExact4Total pts
            (SortedSetPt.withCapacity (pts.length / 4))
            (sortedSetPtStrictSorted_withCapacity _)
        · exact sortedSetPtStrictSorted_of_decodeDecoderPbPtsTotal hrest s hmem

theorem polyDecoderStrictSorted_of_decoderFromPbStateDecode
    {opt : Option PolynomialDecoder} {dec : PolyDecoder}
    (h : decoderFromPbStateDecode spqrPolyApi opt = .ok dec) :
    Poly.AddChunk.PolyDecoderStrictSorted dec := by
  cases opt with
  | none => contradiction
  | some pb =>
    rw [decoderFromPbStateDecode_some] at h
    cases hres : decoderFromPbResult (pbToProtoPolyDecoder pb) with
    | error _ => rw [hres] at h; contradiction
    | ok dec' =>
      rw [hres] at h
      cases h
      unfold decoderFromPbResult at hres
      split at hres
      · contradiction
      · cases hpts : decodeDecoderPbPtsTotal (pbToProtoPolyDecoder pb).pts with
        | error _ => rw [hpts] at hres; contradiction
        | ok outPts =>
          rw [hpts] at hres
          cases hres
          exact sortedSetPtStrictSorted_of_decodeDecoderPbPtsTotal hpts

@[simp] private theorem except_bind_ok_iff {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β} :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m <;> simp [Bind.bind, Except.bind]

@[simp] private theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

@[simp] private theorem decoderFromPbStateDecode_none :
    decoderFromPbStateDecode spqrPolyApi none = .error (.err .stateDecode) := rfl

theorem statesDecoderStrictSorted_of_statesFromPb {F : ShaCompress}
    {pb : V1State} {st : States spqrPolyApi (spqrAuthApi F)}
    (h : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st) :
    statesDecoderStrictSorted st := by
  unfold States.from_pb at h
  cases hinner : pb.innerState with
  | none => rw [hinner] at h; contradiction
  | some inner =>
    rw [hinner] at h
    cases inner with
    | keysUnsampled s | keysSampled s | ct1Received s
    | headerReceived s | ekReceivedCt1Sampled s | ct2Sampled s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      have hinj := Except.ok.inj h; subst hinj; trivial
    | headerSent s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      rcases s with ⟨uc, sendingEk, receivingCt1⟩
      unfold Chunked.SendEk.HeaderSent.from_pb at hv
      cases receivingCt1 with
      | none =>
        cases uc <;>
          simp +zetaHave only [except_bind_ok_iff, except_error_bind, decoderFromPbStateDecode_none,
            Pure.pure, Except.pure, reduceCtorEq, false_and, and_false, exists_false] at hv
      | some d =>
        cases uc with
        | none =>
          dsimp +zetaHave only at hv
          split at hv <;> contradiction
        | some u =>
          dsimp +zetaHave only at hv
          split at hv
          · contradiction
          · simp only [except_bind_ok_iff, Pure.pure, Except.pure, Except.ok.injEq] at hv
            rcases hv with ⟨_, _, _, _, _, _, _, _, dec, hdec, rfl⟩
            exact polyDecoderStrictSorted_of_decoderFromPbStateDecode hdec
    | ekSentCt1Received s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      rcases s with ⟨uc, receivingCt2⟩
      unfold Chunked.SendEk.EkSentCt1Received.from_pb at hv
      cases receivingCt2 with
      | none =>
        cases uc <;>
          simp +zetaHave only [except_bind_ok_iff, except_error_bind, decoderFromPbStateDecode_none,
            Pure.pure, Except.pure, reduceCtorEq, false_and, and_false, exists_false] at hv
      | some d =>
        cases uc with
        | none =>
          dsimp +zetaHave only at hv
          split at hv <;> contradiction
        | some u =>
          dsimp +zetaHave only at hv
          split at hv
          · contradiction
          · simp only [except_bind_ok_iff, Pure.pure, Except.pure, Except.ok.injEq] at hv
            rcases hv with ⟨_, _, _, _, _, _, dec, hdec, rfl⟩
            exact polyDecoderStrictSorted_of_decoderFromPbStateDecode hdec
    | noHeaderReceived s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      rcases s with ⟨uc, receivingHdr⟩
      unfold Chunked.SendCt.NoHeaderReceived.from_pb at hv
      cases receivingHdr with
      | none =>
        cases uc <;>
          simp +zetaHave only [except_bind_ok_iff, except_error_bind, decoderFromPbStateDecode_none,
            Pure.pure, Except.pure, reduceCtorEq, false_and, and_false, exists_false] at hv
      | some d =>
        cases uc with
        | none =>
          dsimp +zetaHave only at hv
          split at hv <;> contradiction
        | some u =>
          dsimp +zetaHave only at hv
          split at hv
          · contradiction
          · simp only [except_bind_ok_iff, Pure.pure, Except.pure, Except.ok.injEq] at hv
            rcases hv with ⟨_, _, _, _, _, _, dec, hdec, rfl⟩
            exact polyDecoderStrictSorted_of_decoderFromPbStateDecode hdec
    | ct1Sampled s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      rcases s with ⟨uc, sendingCt1, receivingEk⟩
      unfold Chunked.SendCt.Ct1Sampled.from_pb at hv
      cases receivingEk with
      | none =>
        cases uc <;>
          simp +zetaHave only [except_bind_ok_iff, except_error_bind, decoderFromPbStateDecode_none,
            Pure.pure, Except.pure, reduceCtorEq, false_and, and_false, exists_false] at hv
      | some d =>
        cases uc with
        | none =>
          dsimp +zetaHave only at hv
          split at hv <;> contradiction
        | some u =>
          dsimp +zetaHave only at hv
          split at hv
          · contradiction
          · simp only [except_bind_ok_iff, Pure.pure, Except.pure, Except.ok.injEq] at hv
            rcases hv with ⟨_, _, _, _, _, _, _, _, dec, hdec, rfl⟩
            exact polyDecoderStrictSorted_of_decoderFromPbStateDecode hdec
    | ct1Acknowledged s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      rcases s with ⟨uc, receivingEk⟩
      unfold Chunked.SendCt.Ct1Acknowledged.from_pb at hv
      cases receivingEk with
      | none =>
        cases uc <;>
          simp +zetaHave only [except_bind_ok_iff, except_error_bind, decoderFromPbStateDecode_none,
            Pure.pure, Except.pure, reduceCtorEq, false_and, and_false, exists_false] at hv
      | some d =>
        cases uc with
        | none =>
          dsimp +zetaHave only at hv
          split at hv <;> contradiction
        | some u =>
          dsimp +zetaHave only at hv
          split at hv
          · contradiction
          · simp only [except_bind_ok_iff, Pure.pure, Except.pure, Except.ok.injEq] at hv
            rcases hv with ⟨_, _, _, _, _, _, dec, hdec, rfl⟩
            exact polyDecoderStrictSorted_of_decoderFromPbStateDecode hdec

theorem rawV1State_le_of_spqrDecodeState {F : ShaCompress} {K : MlKem}
    {stateBytes : Bytes} {st : PqRatchetState} {pb : V1State}
    (hdec : Proto.spqrDecodeState stateBytes = .ok st)
    (hinner : st.inner = some (.v1 pb)) :
    rawV1State pb ≤ 201 * stateBytes.length := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hraw := decodeState_spqrDeps_raw_le hd
  rw [pbToPqRatchetState_pqRatchetStateToPb] at hraw
  unfold rawPqState at hraw
  rw [hinner] at hraw
  simp only [optRaw_some, rawPqInner] at hraw
  omega

theorem ekSentCt1Received_rootKey_le_rawV1State {F : ShaCompress}
    (s : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    s.uc.auth.rootKey.length ≤ rawV1State (States.ekSentCt1Received s).into_pb := by
  unfold States.into_pb Chunked.SendEk.EkSentCt1Received.into_pb
    Unchunked.SendEk.EkSentCt1Received.into_pb spqrAuthApi Authenticator.intoPb
    rawV1State rawInnerState rawChEkSentCt1Received rawUcEkSentCt1Received rawAuth optRaw
  dsimp only
  omega

def rawInnerUc : V1State.InnerState → Nat
  | .ct1Sampled s => optRaw rawUcCt1Sent s.uc
  | .ekReceivedCt1Sampled s => optRaw rawUcCt1SentEkReceived s.uc
  | .ct1Acknowledged s => optRaw rawUcCt1Sent s.uc
  | _ => 0

def rawV1Uc (pb : V1State) : Nat :=
  optRaw rawInnerUc pb.innerState

def rawPqInnerUc : PqRatchetState.Inner → Nat
  | .v1 pb => rawV1Uc pb

def rawPqUc (st : PqRatchetState) : Nat :=
  optRaw rawPqInnerUc st.inner

@[simp, reducible] private def unOkUc {S : Type} (s : S) : Except Proto.DecodeErr (S × Bytes) → S
  | .ok (s', _) => s'
  | .error _ => s

private theorem branch_ite_uc {S : Type} {R : Prop} {c : Bool} [Decidable (c = true)]
    {a b : Except Proto.DecodeErr (S × Bytes)} {x : S × Bytes}
    (h : (if c then a else b) = .ok x)
    (ha : a = .ok x → R) (hb : b = .ok x → R) : R := by
  split at h
  · exact ha h
  · exact hb h

private theorem bind_pair_ok_uc {S α : Type} {e : Except Proto.DecodeErr (α × Bytes)}
    {k : α × Bytes → Except Proto.DecodeErr (S × Bytes)} {s s' : S} {rest' : Bytes}
    (h : Bind.bind e k = .ok (s', rest'))
    (hk : ∀ v bs', k (v, bs') = .ok (unOkUc s (k (v, bs')), bs')) :
    ∃ v, e = .ok (v, rest') ∧ s' = unOkUc s (k (v, rest')) := by
  rcases he : e with err | ⟨v, bs'⟩
  · simp [he, Bind.bind, Except.bind] at h
  · simp only [he, Bind.bind, Except.bind] at h
    rw [hk v bs'] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨v, rfl, rfl⟩

private theorem branch_skip_uc {S : Type} {rawS : S → Nat} {K : Nat} {s s' : S}
    {wt : Proto.WireType} {tag : BitVec 32} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.skipField wt tag rest depth) (fun bs' => Except.ok (s, bs')) = .ok (s', rest')) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + K * (rest.length - rest'.length + 1) := by
  rcases he : Proto.skipField wt tag rest depth with err | bs'
  · simp [he, Bind.bind, Except.bind] at h
  · simp only [he, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨skipField_length_le he, Nat.le_add_right _ _⟩

private theorem branch_optMessage_uc {S Sub : Type} [Inhabited Sub]
    {mergeSub : Sub → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (Sub × Bytes)}
    {rawSub : Sub → Nat} {Ksub : Nat}
    {rawS : S → Nat} {K : Nat}
    {s s' : S} {old : Option Sub}
    {k : Option Sub × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.mergeOptMessage mergeSub wt old rest depth) k = .ok (s', rest'))
    (hb : MergeFieldBound mergeSub rawSub Ksub) (hdef : rawSub default = 0) (hK : Ksub ≤ K)
    (hg : ∀ v, optRaw rawSub old + rawS (unOkUc s (k (v, rest'))) ≤ rawS s + optRaw rawSub v)
    (hk : ∀ v bs', k (v, bs') = .ok (unOkUc s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + K * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok_uc h hk
  obtain ⟨hle, hv⟩ := mergeOptMessage_raw_le hb hdef he
  refine ⟨hle, ?_⟩
  have hgv := hg v
  have hmul : Ksub * (rest.length - rest'.length) ≤ K * (rest.length - rest'.length + 1) :=
    Nat.le_trans (Nat.mul_le_mul_right _ hK) (Nat.mul_le_mul_left K (by omega))
  omega

private theorem branch_oneofMessage_uc {S Sub : Type}
    {mergeSub : Sub → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (Sub × Bytes)}
    {rawSub : Sub → Nat} {Ksub : Nat}
    {rawS : S → Nat} {K : Nat}
    {s s' : S} {prev : Sub}
    {k : Sub × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.mergeMessage mergeSub wt prev rest depth) k = .ok (s', rest'))
    (hb : MergeFieldBound mergeSub rawSub Ksub) (hK : Ksub ≤ K)
    (hprev : rawSub prev ≤ rawS s) (hg : ∀ v, rawS (unOkUc s (k (v, rest'))) = rawSub v)
    (hk : ∀ v bs', k (v, bs') = .ok (unOkUc s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + K * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok_uc h hk
  obtain ⟨hle, hv⟩ := mergeMessage_raw_le hb he
  refine ⟨hle, ?_⟩
  rw [hg]
  have hmul : Ksub * (rest.length - rest'.length) ≤ K * (rest.length - rest'.length + 1) :=
    Nat.le_trans (Nat.mul_le_mul_right _ hK) (Nat.mul_le_mul_left K (by omega))
  omega

private theorem mergeFieldBound_zero_of {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes)}
    {rawM : M → Nat} {K : Nat} (hb : MergeFieldBound mergeField rawM K) :
    MergeFieldBound mergeField (fun _ => 0) 0 :=
  fun m tag wt rest depth m' rest' h => ⟨(hb m tag wt rest depth m' rest' h).1, Nat.zero_le _⟩

private theorem mergeFieldBound_chCt1SampledUc :
    MergeFieldBound V1State.Chunked.Ct1Sampled.mergeField (fun s => optRaw rawUcCt1Sent s.uc) 1 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.Ct1Sampled.mergeField at h
  exact branch_ite_uc h
    (fun h => branch_optMessage_uc (s := s) (rawS := fun s => optRaw rawUcCt1Sent s.uc)
      h mergeFieldBound_ucCt1Sent rfl (by omega) (fun v => by simp))
    (fun h => branch_ite_uc h
      (fun h => branch_optMessage_uc (s := s) (rawS := fun s => optRaw rawUcCt1Sent s.uc)
        h (mergeFieldBound_zero_of mergeFieldBound_polyEnc) rfl (by omega)
        (fun v => by cases s.sendingCt1 <;> cases v <;> simp [optRaw]))
      (fun h => branch_ite_uc h
        (fun h => branch_optMessage_uc (s := s) (rawS := fun s => optRaw rawUcCt1Sent s.uc)
          h (mergeFieldBound_zero_of mergeFieldBound_polyDec) rfl (by omega)
          (fun v => by cases s.receivingEk <;> cases v <;> simp [optRaw]))
        (branch_skip_uc (s := s) (rawS := fun s => optRaw rawUcCt1Sent s.uc) (K := 1))))

private theorem mergeFieldBound_chEkReceivedCt1SampledUc :
    MergeFieldBound V1State.Chunked.EkReceivedCt1Sampled.mergeField
      (fun s => optRaw rawUcCt1SentEkReceived s.uc) 1 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.EkReceivedCt1Sampled.mergeField at h
  exact branch_ite_uc h
    (fun h => branch_optMessage_uc (s := s) (rawS := fun s => optRaw rawUcCt1SentEkReceived s.uc)
      h mergeFieldBound_ucCt1SentEkReceived rfl (by omega) (fun v => by simp))
    (fun h => branch_ite_uc h
      (fun h => branch_optMessage_uc (s := s) (rawS := fun s => optRaw rawUcCt1SentEkReceived s.uc)
        h (mergeFieldBound_zero_of mergeFieldBound_polyEnc) rfl (by omega)
        (fun v => by cases s.sendingCt1 <;> cases v <;> simp [optRaw]))
      (branch_skip_uc (s := s) (rawS := fun s => optRaw rawUcCt1SentEkReceived s.uc) (K := 1)))

private theorem mergeFieldBound_chCt1AcknowledgedUc :
    MergeFieldBound V1State.Chunked.Ct1Acknowledged.mergeField (fun s => optRaw rawUcCt1Sent s.uc) 1 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.Ct1Acknowledged.mergeField at h
  exact branch_ite_uc h
    (fun h => branch_optMessage_uc (s := s) (rawS := fun s => optRaw rawUcCt1Sent s.uc)
      h mergeFieldBound_ucCt1Sent rfl (by omega) (fun v => by simp))
    (fun h => branch_ite_uc h
      (fun h => branch_optMessage_uc (s := s) (rawS := fun s => optRaw rawUcCt1Sent s.uc)
        h (mergeFieldBound_zero_of mergeFieldBound_polyDec) rfl (by omega)
        (fun v => by cases s.receivingEk <;> cases v <;> simp [optRaw]))
      (branch_skip_uc (s := s) (rawS := fun s => optRaw rawUcCt1Sent s.uc) (K := 1)))

private theorem mergeFieldBound_innerStateUc :
    MergeFieldBound V1State.InnerState.merge (optRaw rawInnerUc) 1 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.InnerState.merge at h
  exact branch_ite_uc h (fun h => branch_oneofMessage_uc h (mergeFieldBound_zero_of mergeFieldBound_chKeysUnsampled) (by omega) (Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite_uc h (fun h => branch_oneofMessage_uc h (mergeFieldBound_zero_of mergeFieldBound_chKeysSampled) (by omega) (Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite_uc h (fun h => branch_oneofMessage_uc h (mergeFieldBound_zero_of mergeFieldBound_chHeaderSent) (by omega) (Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite_uc h (fun h => branch_oneofMessage_uc h (mergeFieldBound_zero_of mergeFieldBound_chCt1Received) (by omega) (Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite_uc h (fun h => branch_oneofMessage_uc h (mergeFieldBound_zero_of mergeFieldBound_chEkSentCt1Received) (by omega) (Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite_uc h (fun h => branch_oneofMessage_uc h (mergeFieldBound_zero_of mergeFieldBound_chNoHeaderReceived) (by omega) (Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite_uc h (fun h => branch_oneofMessage_uc h (mergeFieldBound_zero_of mergeFieldBound_chHeaderReceived) (by omega) (Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite_uc h (fun h => branch_oneofMessage_uc h mergeFieldBound_chCt1SampledUc (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite_uc h (fun h => branch_oneofMessage_uc h mergeFieldBound_chEkReceivedCt1SampledUc (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite_uc h (fun h => branch_oneofMessage_uc h mergeFieldBound_chCt1AcknowledgedUc (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite_uc h (fun h => branch_oneofMessage_uc h (mergeFieldBound_zero_of mergeFieldBound_chCt2Sampled) (by omega) (Nat.zero_le _) (fun _ => rfl))
      branch_skip_uc))))))))))

private theorem mergeFieldBound_v1StateUc : MergeFieldBound V1State.mergeField rawV1Uc 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.mergeField at h
  refine branch_ite_uc h (fun h => ?_) branch_skip_uc
  obtain ⟨is', he, rfl⟩ := bind_pair_ok_uc (s := s) h (fun _ _ => rfl)
  exact mergeFieldBound_innerStateUc s.innerState tag wt rest depth is' rest' he

private theorem mergeFieldBound_pqInnerUc :
    MergeFieldBound PqRatchetState.Inner.merge (optRaw rawPqInnerUc) 1 := by
  intro s tag wt rest depth s' rest' h
  unfold PqRatchetState.Inner.merge at h
  exact branch_ite_uc h
    (fun h => branch_oneofMessage_uc h mergeFieldBound_v1StateUc (by omega)
      (by cases s with | none => rfl | some is => cases is; exact Nat.le_refl _) (fun _ => rfl))
    branch_skip_uc

private theorem mergeFieldBound_pqStateUc : MergeFieldBound PqRatchetState.mergeField rawPqUc 1 := by
  intro s tag wt rest depth s' rest' h
  unfold PqRatchetState.mergeField at h
  refine branch_ite_uc h
    (fun h => branch_optMessage_uc (s := s) (rawS := rawPqUc)
      h (mergeFieldBound_zero_of mergeFieldBound_vn) rfl (by omega)
      (fun v => by cases s.versionNegotiation <;> cases v <;> simp [rawPqUc, optRaw]))
    (fun h => branch_ite_uc h
      (fun h => branch_optMessage_uc (s := s) (rawS := rawPqUc)
        h (mergeFieldBound_zero_of mergeFieldBound_chain) rfl (by omega)
        (fun v => by cases s.chain <;> cases v <;> simp [rawPqUc, optRaw]))
      (fun h => branch_ite_uc h (fun h => ?_) branch_skip_uc))
  obtain ⟨v, he, rfl⟩ := bind_pair_ok_uc (s := s) h (fun _ _ => rfl)
  exact mergeFieldBound_pqInnerUc s.inner tag wt rest depth v rest' he

theorem rawV1Uc_le_of_spqrDecodeState
    {stateBytes : Bytes} {st : PqRatchetState} {pb : V1State}
    (hdec : Proto.spqrDecodeState stateBytes = .ok st)
    (hinner : st.inner = some (.v1 pb)) :
    rawV1Uc pb ≤ stateBytes.length := by
  have hpq : rawPqUc st ≤ stateBytes.length := by
    unfold Proto.spqrDecodeState at hdec
    split at hdec
    · simp only [Except.ok.injEq] at hdec; subst hdec; simp [rawPqUc, optRaw]
    · rcases hd : PqRatchetState.decode stateBytes with e | st'
      · simp [hd] at hdec
      · simp only [hd, Except.ok.injEq] at hdec; subst hdec
        have hraw := mergeFieldsLoop_raw_le mergeFieldBound_pqStateUc stateBytes.length default
          stateBytes Proto.RECURSION_LIMIT st' hd
        have hdef : rawPqUc default = 0 := rfl
        omega
  unfold rawPqUc at hpq
  rw [hinner] at hpq
  simpa [optRaw_some, rawPqInnerUc] using hpq

theorem ucHeaderSent_from_pb_ek_len {F : ShaCompress} {pb : V1State.Unchunked.HeaderSent}
    {s : Unchunked.SendEk.HeaderSent (spqrAuthApi F)}
    (h : Unchunked.SendEk.HeaderSent.from_pb (spqrAuthApi F) pb = .ok s) :
    s.ek.length = 1152 := by
  unfold Unchunked.SendEk.HeaderSent.from_pb at h
  split at h <;> [rename_i hcond; contradiction]
  cases hauth : pb.auth <;> rw [hauth] at h
  · contradiction
  · have hinj := Except.ok.inj h; subst hinj
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hcond).2

theorem ucCt1Sent_from_pb_lengths {F : ShaCompress} {pb : V1State.Unchunked.Ct1Sent}
    {s : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    (h : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) pb = .ok s) :
    s.es.length = 2080 ∧ s.ct1.length = 960 := by
  unfold Unchunked.SendCt.Ct1Sent.from_pb at h
  split at h <;> [rename_i hcond; contradiction]
  cases hauth : pb.auth <;> rw [hauth] at h
  · contradiction
  · have hinj := Except.ok.inj h; subst hinj
    have h12 := (Bool.and_eq_true_iff.mp hcond).1
    have h3 := (Bool.and_eq_true_iff.mp hcond).2
    exact ⟨beq_iff_eq.mp (Bool.and_eq_true_iff.mp h12).2, beq_iff_eq.mp h3⟩

theorem ucCt1SentEkReceived_from_pb_lengths {F : ShaCompress}
    {pb : V1State.Unchunked.Ct1SentEkReceived}
    {s : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)}
    (h : Unchunked.SendCt.Ct1SentEkReceived.from_pb (spqrAuthApi F) pb = .ok s) :
    s.es.length = 2080 ∧ s.ek.length = 1152 ∧ s.ct1.length = 960 := by
  unfold Unchunked.SendCt.Ct1SentEkReceived.from_pb at h
  split at h <;> [rename_i hcond; contradiction]
  cases hauth : pb.auth <;> rw [hauth] at h
  · contradiction
  · have hinj := Except.ok.inj h; subst hinj
    have h12 := (Bool.and_eq_true_iff.mp hcond).1
    have h3 := (Bool.and_eq_true_iff.mp hcond).2
    exact ⟨beq_iff_eq.mp (Bool.and_eq_true_iff.mp h12).1,
           beq_iff_eq.mp h3,
           beq_iff_eq.mp (Bool.and_eq_true_iff.mp h12).2⟩

theorem ucCt1Sent_macKey_le_rawUcCt1Sent {F : ShaCompress}
    (s : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    s.auth.macKey.length ≤ rawUcCt1Sent s.into_pb := by
  unfold Unchunked.SendCt.Ct1Sent.into_pb spqrAuthApi Authenticator.intoPb
    rawUcCt1Sent rawAuth optRaw
  dsimp only
  omega

theorem ucCt1SentEkReceived_macKey_le_rawUcCt1SentEkReceived {F : ShaCompress}
    (s : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) :
    s.auth.macKey.length ≤ rawUcCt1SentEkReceived s.into_pb := by
  unfold Unchunked.SendCt.Ct1SentEkReceived.into_pb spqrAuthApi Authenticator.intoPb
    rawUcCt1SentEkReceived rawAuth optRaw
  dsimp only
  omega

private theorem chCt1Sampled_from_pb_uc {F : ShaCompress}
    {pb : V1State.Chunked.Ct1Sampled}
    {s : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)}
    (h : Chunked.SendCt.Ct1Sampled.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok s) :
    ∃ u, pb.uc = some u ∧ Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok s.uc := by
  unfold Chunked.SendCt.Ct1Sampled.from_pb at h
  cases hrek : pb.receivingEk with
  | none =>
    simp only [hrek] at h
    cases huc : pb.uc with
    | none => simp [huc, Bind.bind, Except.bind] at h
    | some u =>
      simp only [huc] at h
      rcases except_bind_eq_ok h with ⟨_, _, h0⟩
      rcases except_bind_eq_ok h0 with ⟨u', hu', h1⟩
      have hu_eq := Except.ok.inj hu'; subst hu_eq
      rcases except_bind_eq_ok h1 with ⟨uc, huc', h2⟩
      rcases except_bind_eq_ok h2 with ⟨enc, _, h3⟩
      rcases except_bind_eq_ok h3 with ⟨dec, _, h4⟩
      have hinj := Except.ok.inj h4; subst hinj
      exact ⟨u, rfl, huc'⟩
  | some d =>
    by_cases hpts : (d.ptsNeeded.toNat != ENCAPSULATION_KEY_SIZE / 2) = true
    · simp [hrek, hpts, Bind.bind, Except.bind] at h
    · simp only [hrek, hpts, ↓reduceIte] at h
      cases huc : pb.uc with
      | none => simp [huc, Bind.bind, Except.bind] at h
      | some u =>
        simp only [huc] at h
        rcases except_bind_eq_ok h with ⟨_, _, h0⟩
        rcases except_bind_eq_ok h0 with ⟨u', hu', h1⟩
        have hu_eq := Except.ok.inj hu'; subst hu_eq
        rcases except_bind_eq_ok h1 with ⟨uc, huc', h2⟩
        rcases except_bind_eq_ok h2 with ⟨enc, _, h3⟩
        rcases except_bind_eq_ok h3 with ⟨dec, _, h4⟩
        have hinj := Except.ok.inj h4; subst hinj
        exact ⟨u, rfl, huc'⟩

private theorem chCt1Acknowledged_from_pb_uc {F : ShaCompress}
    {pb : V1State.Chunked.Ct1Acknowledged}
    {s : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)}
    (h : Chunked.SendCt.Ct1Acknowledged.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok s) :
    ∃ u, pb.uc = some u ∧ Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u = .ok s.uc := by
  unfold Chunked.SendCt.Ct1Acknowledged.from_pb at h
  cases hrek : pb.receivingEk with
  | none =>
    simp only [hrek] at h
    cases huc : pb.uc with
    | none => simp [huc, Bind.bind, Except.bind] at h
    | some u =>
      simp only [huc] at h
      rcases except_bind_eq_ok h with ⟨_, _, h0⟩
      rcases except_bind_eq_ok h0 with ⟨u', hu', h1⟩
      have hu_eq := Except.ok.inj hu'; subst hu_eq
      rcases except_bind_eq_ok h1 with ⟨uc, huc', h2⟩
      rcases except_bind_eq_ok h2 with ⟨dec, _, h3⟩
      have hinj := Except.ok.inj h3; subst hinj
      exact ⟨u, rfl, huc'⟩
  | some d =>
    by_cases hpts : (d.ptsNeeded.toNat != ENCAPSULATION_KEY_SIZE / 2) = true
    · simp [hrek, hpts, Bind.bind, Except.bind] at h
    · simp only [hrek, hpts, ↓reduceIte] at h
      cases huc : pb.uc with
      | none => simp [huc, Bind.bind, Except.bind] at h
      | some u =>
        simp only [huc] at h
        rcases except_bind_eq_ok h with ⟨_, _, h0⟩
        rcases except_bind_eq_ok h0 with ⟨u', hu', h1⟩
        have hu_eq := Except.ok.inj hu'; subst hu_eq
        rcases except_bind_eq_ok h1 with ⟨uc, huc', h2⟩
        rcases except_bind_eq_ok h2 with ⟨dec, _, h3⟩
        have hinj := Except.ok.inj h3; subst hinj
        exact ⟨u, rfl, huc'⟩

/-- `spqrDecodeState` and `States.from_pb` establish `statesRecvPreInv`. -/
theorem statesRecvPreInv_of_spqrDecodeState {F : ShaCompress} {K : MlKem}
    {stateBytes : Bytes} {st : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    (hlen : stateBytes.length < 2 ^ 32)
    (hdec : Proto.spqrDecodeState stateBytes = .ok st)
    (hinner : st.inner = some (.v1 pb))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0) :
    statesRecvPreInv st0 := by
  have hsort := statesDecoderStrictSorted_of_statesFromPb hfrom
  have hraw_from := (States.from_pb_raw_le hfrom).1
  have hraw_dec := rawV1State_le_of_spqrDecodeState (F := F) (K := K) hdec hinner
  have hraw_uc := rawV1Uc_le_of_spqrDecodeState hdec hinner
  unfold States.from_pb at hfrom
  cases hpb : pb.innerState with
  | none => rw [hpb] at hfrom; contradiction
  | some is =>
    rw [hpb] at hfrom
    cases is with
    | keysUnsampled s_pb =>
      dsimp only [Functor.map, Except.map] at hfrom
      split at hfrom <;> [contradiction; rename_i s hv]
      have hinj := Except.ok.inj hfrom; subst hinj; trivial
    | keysSampled s_pb =>
      dsimp only [Functor.map, Except.map] at hfrom
      split at hfrom <;> [contradiction; rename_i s hv]
      have hinj := Except.ok.inj hfrom; subst hinj
      unfold Chunked.SendEk.KeysSampled.from_pb at hv
      cases huc : s_pb.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩
        rcases except_bind_eq_ok hv2 with ⟨enc, _, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        exact ucHeaderSent_from_pb_ek_len huc'
    | headerSent s_pb =>
      dsimp only [Functor.map, Except.map] at hfrom
      split at hfrom <;> [contradiction; rename_i s hv]
      have hinj := Except.ok.inj hfrom; subst hinj; exact hsort
    | ct1Received s_pb =>
      dsimp only [Functor.map, Except.map] at hfrom
      split at hfrom <;> [contradiction; rename_i s hv]
      have hinj := Except.ok.inj hfrom; subst hinj; trivial
    | ekSentCt1Received s_pb =>
      dsimp only [Functor.map, Except.map] at hfrom
      split at hfrom <;> [contradiction; rename_i s hv]
      have hinj := Except.ok.inj hfrom; subst hinj
      refine ⟨hsort, ?_⟩
      have hrk := ekSentCt1Received_rootKey_le_rawV1State s
      omega
    | noHeaderReceived s_pb =>
      dsimp only [Functor.map, Except.map] at hfrom
      split at hfrom <;> [contradiction; rename_i s hv]
      have hinj := Except.ok.inj hfrom; subst hinj; exact hsort
    | headerReceived s_pb =>
      dsimp only [Functor.map, Except.map] at hfrom
      split at hfrom <;> [contradiction; rename_i s hv]
      have hinj := Except.ok.inj hfrom; subst hinj; trivial
    | ct1Sampled s_pb =>
      dsimp only [Functor.map, Except.map] at hfrom
      split at hfrom <;> [contradiction; rename_i s hv]
      have hinj := Except.ok.inj hfrom; subst hinj
      obtain ⟨u, huc, huc'⟩ := chCt1Sampled_from_pb_uc hv
      obtain ⟨hes, hct1⟩ := ucCt1Sent_from_pb_lengths huc'
      have hraw1 := ucCt1Sent_from_pb_raw_eq huc'
      have hmac := ucCt1Sent_macKey_le_rawUcCt1Sent s.uc
      have huc_pb : rawV1Uc pb = rawUcCt1Sent u := by
        simp [rawV1Uc, hpb, rawInnerUc, huc, optRaw_some]
      exact ⟨hsort, hes, hct1, by omega⟩
    | ekReceivedCt1Sampled s_pb =>
      dsimp only [Functor.map, Except.map] at hfrom
      split at hfrom <;> [contradiction; rename_i s hv]
      have hinj := Except.ok.inj hfrom; subst hinj
      unfold Chunked.SendCt.EkReceivedCt1Sampled.from_pb at hv
      cases huc : s_pb.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩
        rcases except_bind_eq_ok hv2 with ⟨enc, _, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        obtain ⟨hes, hek, hct1⟩ := ucCt1SentEkReceived_from_pb_lengths huc'
        have hraw1 := ucCt1SentEkReceived_from_pb_raw_eq huc'
        have hmac := ucCt1SentEkReceived_macKey_le_rawUcCt1SentEkReceived uc
        have huc_pb : rawV1Uc pb = rawUcCt1SentEkReceived u := by
          simp [rawV1Uc, hpb, rawInnerUc, huc, optRaw_some]
        dsimp only [statesRecvPreInv]
        exact ⟨hes, hek, hct1, by omega⟩
    | ct1Acknowledged s_pb =>
      dsimp only [Functor.map, Except.map] at hfrom
      split at hfrom <;> [contradiction; rename_i s hv]
      have hinj := Except.ok.inj hfrom; subst hinj
      obtain ⟨u, huc, huc'⟩ := chCt1Acknowledged_from_pb_uc hv
      obtain ⟨hes, hct1⟩ := ucCt1Sent_from_pb_lengths huc'
      have hraw1 := ucCt1Sent_from_pb_raw_eq huc'
      have hmac := ucCt1Sent_macKey_le_rawUcCt1Sent s.uc
      have huc_pb : rawV1Uc pb = rawUcCt1Sent u := by
        simp [rawV1Uc, hpb, rawInnerUc, huc, optRaw_some]
      exact ⟨hsort, hes, hct1, by omega⟩
    | ct2Sampled s_pb =>
      dsimp only [Functor.map, Except.map] at hfrom
      split at hfrom <;> [contradiction; rename_i s hv]
      have hinj := Except.ok.inj hfrom; subst hinj; trivial

end CryptoVerification.SpqrV1.Top.Recv
