/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonical
public import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import LibsignalBinary.Proofs.RoDataReloc
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionVtables

/-!
# Stage 1 Normalization, Model, Control-Flow, and Vtable Helpers

Provides state/`BitVec` normalization lemmas (`Stage1Norm`), pure `bundleEOf?` and `initDef` model
lemmas, `InInitiate` call/panic combinators, and `.rodata` vtable slot introduction lemmas for
Stage 1 of `signal_session_handshake::initiate`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad
open CryptoGames CryptoGames.LibsignalSession
set_option maxRecDepth 2000000
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## State and `BitVec` normalization lemmas -/

namespace Stage1Norm

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem sp_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases s; cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).symtab = s.symtab := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).symtab = s.symtab := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).symtab = s.symtab := by cases s; cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).symtab = s.symtab := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).trace = s.trace := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).trace = s.trace := by cases s; cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) (r : Reg) :
    (s.writeVReg128 idx v).readReg64 r = s.readReg64 r := by
  cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) (r : Reg) :
    (s.writeVReg128 idx v).readReg32 r = s.readReg32 r := by
  cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128)
    (w : RegWidth) (r : Reg) :
    (s.writeVReg128 idx v).readReg w r = s.readReg w r := by
  cases s; cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setPC_pre (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (idx : BitVec 5) :
    ((s.setPC pc).setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setMem_pre (s : State) (m : Memory) (idx : BitVec 5) :
    (s.setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setPState_pre (s : State) (ps : PState) (idx : BitVec 5) :
    (s.setPState ps).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) (idx : BitVec 5) :
    (s.writeReg64 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) (idx : BitVec 5) :
    (s.writeReg32 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64)
    (idx : BitVec 5) :
    (s.writeReg w r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append_lo (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append_hi (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_pack32_0 (a b c d : BitVec 8) :
    BitVec.extractLsb' 0 8 (a ++ b ++ c ++ d) = d := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_pack32_8 (a b c d : BitVec 8) :
    BitVec.extractLsb' 8 8 (a ++ b ++ c ++ d) = c := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_pack32_16 (a b c d : BitVec 8) :
    BitVec.extractLsb' 16 8 (a ++ b ++ c ++ d) = b := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_pack32_24 (a b c d : BitVec 8) :
    BitVec.extractLsb' 24 8 (a ++ b ++ c ++ d) = a := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_pack32_0_16 (a b c d : BitVec 8) :
    BitVec.extractLsb' 0 16 (a ++ b ++ c ++ d) = c ++ d := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_pack32_16_16 (a b c d : BitVec 8) :
    BitVec.extractLsb' 16 16 (a ++ b ++ c ++ d) = a ++ b := by
  bv_bits

end Stage1Norm

/-! ## Pure model lemmas (`bundleEOf?`, `initDef`, `signaturesVerify`) -/

def mkBundleE (b : BundleV)
    (h1 : b.spkSig.length = 64) (h2 : b.kpkSig.length = 64) (h3 : b.kpk.length = 1568) :
    PreKeyBundleFields :=
  { regId := b.regId
    opk := b.opk.map fun (i, k) => (i, k.bytes)
    spkId := b.spkId
    spkPub := b.spk.bytes
    spkSig := ⟨b.spkSig, h1⟩
    kpkId := b.kpkId
    kpkPub := ⟨b.kpk, h3⟩
    kpkSig := ⟨b.kpkSig, h2⟩
    idPub := b.idKey.publicKey.bytes }

theorem bundleEOf_eq_some_mkBundleE (b : BundleV)
    (h1 : b.spkSig.length = 64) (h2 : b.kpkSig.length = 64) (h3 : b.kpk.length = 1568) :
    bundleEOf? b = some (mkBundleE b h1 h2 h3) := by
  unfold bundleEOf? mkBundleE
  simp only [h1, h2, h3, ↓reduceDIte]

theorem initDef_eq_some_none_of_trust_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (F : FsFiles) (peer me : AddrVal) (b : BundleV) (coins : List (BitVec 8))
    (herr : StoresGhost.opened.identity.trusted cliIo.rd F peer b.idKey = .error ()) :
    initDef X W F peer me b coins = some none := by
  unfold initDef
  dsimp only
  cases bundleEOf? b with
  | none => rfl
  | some be => rw [herr]

theorem initDef_eq_some_none_of_trust_false (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (F : FsFiles) (peer me : AddrVal) (b : BundleV) (coins : List (BitVec 8))
    (hf : StoresGhost.opened.identity.trusted cliIo.rd F peer b.idKey = .ok false) :
    initDef X W F peer me b coins = some none := by
  unfold initDef
  dsimp only
  cases bundleEOf? b with
  | none => rfl
  | some be => rw [hf]

theorem initDef_eq_some_none_of_sigsOk_false (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (F : FsFiles) (peer me : AddrVal) (b : BundleV) (be : PreKeyBundleFields) (coins : List (BitVec 8))
    (hbe : bundleEOf? b = some be)
    (hsigs : PreKeyBundleFields.signaturesVerify X W be = false) :
    initDef X W F peer me b coins = some none := by
  unfold initDef
  dsimp only
  rw [hbe]
  cases StoresGhost.opened.identity.trusted cliIo.rd F peer b.idKey with
  | error _ => rfl
  | ok tb =>
    cases tb with
    | false => rfl
    | true =>
      cases StoresGhost.opened.identity.keyPair cliIo.rd F with
      | error _ => rfl
      | ok kp =>
        cases StoresGhost.opened.identity.regId cliIo.rd F with
        | error _ => rfl
        | ok reg =>
          dsimp only
          have hnone :
              initiateState X W (initParty peer) { idPriv := kp.privateKey.bytes, regId := reg } be
                (padCoins coins) = none := by
            unfold initiateState SignalPqxdh.Model.initiateKeys PreKeyBundleFields.signaturesVerify at *
            simp only [initiateInput] at hsigs ⊢
            rw [Bool.and_eq_false_iff] at hsigs
            rcases hsigs with h1 | h2
            · simp [h1]
            · simp [h2]
          rw [hnone]

theorem sigsOk_false_of_spk_false (X : UnreachedPqxdhPrimitives) (W : PEParams) (be : PreKeyBundleFields)
    (hspk : (modelPrims X W).sigVerify (vecU8 be.idPub)
      (SignalPqxdh.encodeEC (vecU8 be.spkPub)) (vecU8 be.spkSig) = false) :
    be.signaturesVerify X W = false := by
  unfold PreKeyBundleFields.signaturesVerify
  dsimp only [initiateInput]
  rw [hspk, Bool.false_and]

theorem sigsOk_false_of_kpk_false (X : UnreachedPqxdhPrimitives) (W : PEParams) (be : PreKeyBundleFields)
    (hkpk : (modelPrims X W).sigVerify (vecU8 be.idPub)
      (SignalPqxdh.encodeKEM (vecU8 be.kpkPub)) (vecU8 be.kpkSig) = false) :
    be.signaturesVerify X W = false := by
  unfold PreKeyBundleFields.signaturesVerify
  dsimp only [initiateInput]
  rw [hkpk, Bool.and_false]

theorem bytesToBv8_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) :
    Pqxdh.Shared.bytesToBv8 (vecU8 v) = v.toList :=
  CryptoVerification.E2E.Pqxdh.ResponderCore.bytesToBv8_vecU8 v

theorem spkSerialize_eq_encodeEC (b : BundleV) (h1 : b.spkSig.length = 64)
    (h2 : b.kpkSig.length = 64) (h3 : b.kpk.length = 1568) :
    b.spk.serialize =
      Pqxdh.Shared.bytesToBv8 (SignalPqxdh.encodeEC (vecU8 (mkBundleE b h1 h2 h3).spkPub)) := by
  have hv := bytesToBv8_vecU8 b.spk.bytes
  show (5#8 :: b.spk.bytes.toList) =
    5#8 :: Pqxdh.Shared.bytesToBv8 (vecU8 b.spk.bytes)
  rw [hv]

theorem kpkSerialize_eq_encodeKEM (b : BundleV) (h1 : b.spkSig.length = 64)
    (h2 : b.kpkSig.length = 64) (h3 : b.kpk.length = 1568) :
    (8#8 :: b.kpk) =
      Pqxdh.Shared.bytesToBv8 (SignalPqxdh.encodeKEM (vecU8 (mkBundleE b h1 h2 h3).kpkPub)) := by
  have hv := bytesToBv8_vecU8 (⟨b.kpk, h3⟩ : List.Vector (BitVec 8) 1568)
  show (8#8 :: b.kpk) =
    8#8 :: Pqxdh.Shared.bytesToBv8 (vecU8 (⟨b.kpk, h3⟩ : List.Vector (BitVec 8) 1568))
  exact congrArg (8#8 :: ·) hv.symm

/-! ## Control invariant, panic postcondition, and `withFsInv` call combinator -/

theorem atInitEntry_toExt {img : Obj.Image} {W : CliHooks} {x : InitGhost} {s0 : State}
    (h : AtInitEntry img W x s0) :
    AtInitEntryExt img (cliHookExterns W) x s0 :=
  ⟨h.pc, h.run, h.inv, h.spAligned, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7, h.x8, h.files⟩

theorem inInitiate_toExt {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiate img W s0 s k) :
    InInitiateExt img (cliHookExterns W) s0 s k :=
  ⟨h.pc, h.run, h.sp, h.fp, h.x19, h.files0, h.inv, h.vregs, h.spAligned⟩

theorem inInitiate_ofExt {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiateExt img (cliHookExterns W) s0 s k) :
    InInitiate img W s0 s k :=
  ⟨h.pc, h.run, h.sp, h.fp, h.x19, h.files0, h.inv, h.vregs, h.spAligned⟩

theorem atStage2_ofExt {img : Obj.Image} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {x : InitGhost}
    {be : PreKeyBundleFields} {s0 s : State}
    (h : AtStage2Ext img ⟨W.C, W.Q⟩ (cliHookExterns W) X x be s0 s) :
    AtStage2 img W X x be s0 s :=
  ⟨inInitiate_ofExt h.ctrl, h.trace, h.files, h.x8, h.bundleEq, h.trustedOk, h.signaturesVerify,
    h.x22, h.x23, h.x25, h.x26, h.x27⟩

theorem initStoreCallees_toExt {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {B : RunBudgets} {stk : Nat}
    (h : InitStoreCallees img A W B stk) :
    InitStoreCalleesExt img A (cliExternsWith (cliHookExterns W)) B stk :=
  { futDrop := h.futDrop
    idTrustShim := h.idTrustShim
    idTrustPoll := h.idTrustPoll
    sessLoadShim := h.sessLoadShim
    sessLoadPoll := h.sessLoadPoll
    idKeyPairShim := h.idKeyPairShim
    idKeyPairPoll := h.idKeyPairPoll
    idRegIdShim := h.idRegIdShim
    idRegIdPoll := h.idRegIdPoll
    idSaveShim := h.idSaveShim
    idSavePoll := h.idSavePoll
    sessStoreShim := h.sessStoreShim
    sessStorePoll := h.sessStorePoll }

theorem inInitiateExt_spAligned_cur {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat}
    (h : InInitiateExt img ext s0 s k) : s.spAligned = true := by
  have hal := h.spAligned
  simp only [State.spAligned, beq_iff_eq] at hal ⊢
  rw [h.sp, show cliInitiateFrame = 7408 from rfl]
  have hmod0 : s0.sp.toNat % 16 = 0 := by
    have ht := congrArg BitVec.toNat hal
    rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (0#64).toNat = 0 from rfl] at ht
    exact ht
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, show (0#64).toNat = 0 from rfl, BitVec.toNat_sub,
    show (7408#64).toNat = 7408 from rfl]
  have hlt : s0.sp.toNat < 2 ^ 64 := s0.sp.isLt
  omega

theorem InInitiate.spAligned_cur {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiate img W s0 s k) : s.spAligned = true :=
  inInitiateExt_spAligned_cur (inInitiate_toExt h)

theorem inInitiateExt_of_call {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s sm : State} {k k' : Nat} (h : InInitiateExt img ext s0 s k)
    (hpc : sm.pc = initPcExt img ext k')
    (hrun : sm.status = .Running)
    (hsp : sm.sp = s.sp)
    (hcs : CalleeSavedPreserved s sm)
    (hinv : ImgCallInv img sm)
    (hfs : sm.fs.files = s0.fs.files) :
    InInitiateExt img ext s0 sm k' where
  pc := hpc
  run := hrun
  sp := hsp.trans h.sp
  fp := hcs.2.2.2.2.2.2.2.2.2.2.1.trans h.fp
  x19 := hcs.1.trans h.x19
  files0 := hfs
  inv := hinv
  vregs := hcs.2.2.2.2.2.2.2.2.2.2.2.trans h.vregs
  spAligned := h.spAligned

theorem InInitiate.of_call {img : Obj.Image} {W : CliHooks} {s0 s sm : State}
    {k k' : Nat} (h : InInitiate img W s0 s k)
    (hpc : sm.pc = initPc img W k')
    (hrun : sm.status = .Running)
    (hsp : sm.sp = s.sp)
    (hcs : CalleeSavedPreserved s sm)
    (hinv : ImgCallInv img sm)
    (hfs : sm.fs.files = s0.fs.files) :
    InInitiate img W s0 sm k' :=
  inInitiate_ofExt (inInitiateExt_of_call (inInitiate_toExt h) hpc hrun hsp hcs hinv hfs)

theorem initCall_ext {α : Type} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State} {callee_pc ret_pc : BitVec 64}
    {spec : Spec α} {gx : α} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hcall : subroutine_ok (initProgExt img ext) callee_pc spec)
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hal : s.spAligned = true)
    (hinv : ImgCallInv img s)
    (htr : s.trace = s0.trace)
    (hfs : s.fs.files = s0.fs.files)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : P ⊢ spec.pre gx s ∗ F)
    (hpan : ∀ sf, spec.onPanic gx s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      ImgCallInv img sm →
      (sm.trace = s0.trace → sm.fs.files = s0.fs.files) →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm (spec.post gx s sm ∗ F) Q Qp (initOom s0))
    (hexit : ∀ code sf, spec.onExit gx code s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom gx s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  have hfsInv0 : FsInv s0.fs.files s0.trace s := by
    rw [← hfs, ← htr]
    exact withFsInv_entry s
  have hcallFs := subroutine_ok_withFsInv hh.fs hcall s0.fs.files s0.trace
  refine SepWPp.call_wpp_frozen hcallFs (x := gx) (F := F) hinv.1 hinv.2 hpc hrun hal hlr
    (fun R hm => ?_)
    (fun sm code R _ hpost => ?_)
    (fun sm _ _ => ?_)
    (fun sm hpcm hrunm hspm hcsm hfzm hsymm => ?_)
    (hoom := fun sm R _ hpost => ?_)
  · refine withFsInv_pre_intro hfsInv0 ?_
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hpre) hm
  · change sm.mem ⊨ (⌜FsInv s0.fs.files s0.trace sm⌝ ∗ spec.onExit gx code s sm) ∗ R at hpost
    rw [hexit, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact not_satisfies_false_sepConj hpost.2
  · refine hpanic sm _ ?_
    dsimp only [withFsInv, initSlotSpec, Spec.inImage]
    rw [sepConj_assoc]
    apply Entails.pure_left
    intro _
    refine Entails.trans (sepConj_mono_left (hpan sm)) ?_
    rw [sepConj_assoc]
    apply Entails.pure_left
    rintro ⟨hA, _⟩
    have hA0 : allocFailedIn s0 sm := by
      unfold allocFailedIn at hA ⊢
      rwa [htr] at hA
    exact Entails.pure_right (Or.inr hA0) (entails_anyHeap _)
  · dsimp only [withFsInv]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hfsInvm => ?_
    have hfsm : sm.trace = s0.trace → sm.fs.files = s0.fs.files := fun htm =>
      hfsInvm.files_eq (evs := []) (by simp [htm]) NoFsEv.nil
    exact hnext sm hpcm hrunm hspm hcsm ⟨hfzm, hsymm⟩ hfsm
  · change sm.mem ⊨ (⌜FsInv s0.fs.files s0.trace sm⌝ ∗ spec.onOom gx s sm) ∗ (F ∗ R) at hpost
    rw [hoom, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact (not_satisfies_false_sepConj hpost.2).elim

theorem initCall {α : Type} {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State} {callee_pc ret_pc : BitVec 64}
    {spec : Spec α} {gx : α} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hcall : subroutine_ok (initProg img W) callee_pc spec)
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hal : s.spAligned = true)
    (hinv : ImgCallInv img s)
    (htr : s.trace = s0.trace)
    (hfs : s.fs.files = s0.fs.files)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : P ⊢ spec.pre gx s ∗ F)
    (hpan : ∀ sf, spec.onPanic gx s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      ImgCallInv img sm →
      (sm.trace = s0.trace → sm.fs.files = s0.fs.files) →
      SepWPp (initProg img W) (s0.readReg64 .lr) sm (spec.post gx s sm ∗ F) Q Qp (initOom s0))
    (hexit : ∀ code sf, spec.onExit gx code s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom gx s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) :=
  initCall_ext (ext := cliHookExterns W) hh.toExt hpanic hcall hpc hrun hal hinv htr hfs hlr
    hpre hpan hnext hexit hoom

theorem false_entails (P : SepProp) : (⌜False⌝ : SepProp) ⊢ P := by
  rw [← sepConj_emp (⌜False⌝ : SepProp)]
  exact Entails.pure_left False.elim

theorem false_sepConj_entails (R Q : SepProp) : ((⌜False⌝ : SepProp) ∗ R) ⊢ Q := by
  rw [pure_false_sepConj]
  exact false_entails Q

theorem pure_sepConj_elim {φ : Prop} {R Q : SepProp} (h : φ → (R ⊢ Q)) :
    (⌜φ⌝ ∗ R) ⊢ Q := by
  by_cases hφ : φ
  · rw [pure_sepConj_of_true hφ]
    exact h hφ
  · rw [show φ = False from propext ⟨fun h0 => hφ h0, False.elim⟩]
    exact false_sepConj_entails R Q

theorem pure_sepConj_intro {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q := by
  rw [pure_sepConj_of_true hφ]
  exact h

theorem initCallInImage_ext {α : Type} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State} {callee_pc ret_pc : BitVec 64}
    {inner : Spec α} {gx : α} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hcall : subroutine_ok (initProgExt img ext) callee_pc (inner.inImage img))
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hal : s.spAligned = true)
    (hinv : ImgCallInv img s)
    (htr : s.trace = s0.trace)
    (hfs : s.fs.files = s0.fs.files)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : P ⊢ inner.pre gx s ∗ F)
    (hpan : ∀ sf, inner.onPanic gx s sf ⊢
      ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap := by intros; exact false_entails _)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      ImgCallInv img sm →
      (sm.trace = s0.trace → sm.fs.files = s0.fs.files) →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm (inner.post gx s sm ∗ F) Q Qp (initOom s0))
    (hexit : ∀ code sf, inner.onExit gx code s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, inner.onOom gx s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) :=
  initCall_ext hh hpanic hcall hpc hrun hal hinv htr hfs hlr
    (Entails.trans hpre (sepConj_mono_left (pure_sepConj_intro hinv (Entails.refl _))))
    hpan hnext hexit hoom

theorem initCallInImage {α : Type} {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State} {callee_pc ret_pc : BitVec 64}
    {inner : Spec α} {gx : α} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hcall : subroutine_ok (initProg img W) callee_pc (inner.inImage img))
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hal : s.spAligned = true)
    (hinv : ImgCallInv img s)
    (htr : s.trace = s0.trace)
    (hfs : s.fs.files = s0.fs.files)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : P ⊢ inner.pre gx s ∗ F)
    (hpan : ∀ sf, inner.onPanic gx s sf ⊢
      ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap := by intros; exact false_entails _)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      ImgCallInv img sm →
      (sm.trace = s0.trace → sm.fs.files = s0.fs.files) →
      SepWPp (initProg img W) (s0.readReg64 .lr) sm (inner.post gx s sm ∗ F) Q Qp (initOom s0))
    (hexit : ∀ code sf, inner.onExit gx code s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, inner.onOom gx s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) :=
  initCall hh hpanic hcall hpc hrun hal hinv htr hfs hlr
    (Entails.trans hpre (sepConj_mono_left (pure_sepConj_intro hinv (Entails.refl _))))
    hpan hnext hexit hoom

theorem sepWPp_step_inImage {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm => ImgCallInv img sm → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ := hnext (hinv.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_ret_of_sepWP {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog ret s P Q oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, hok | hoom⟩
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_mono_pre {prog : Program} {ret : BitVec 64}
    {s : State} {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

theorem sepWPp_exists_elim {α : Type} {prog : Program} {ret : BitVec 64}
    {s : State} {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ a, SepWPp prog ret s (P a) Q Qp oom) :
    SepWPp prog ret s (∃∗ a, P a) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hma⟩ := hm
  exact h a R hma hL

theorem sepWPp_pure_elim {φ : Prop} {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp oom :=
  SepWPp.pure_left h

theorem idTrust_always_ok {W : PEParams} {F : FsFiles} {peer me : AddrVal}
    {idKey : IdentityKey} {gr : Except Unit (List (BitVec 8))}
    {p : Except Unit (Option IdentityKey)}
    (hinitOk : InitOk₀ W F peer me)
    (hgr : gr = StoresGhost.opened.identity.peers.get cliIo.rd F peer.name)
    (hp : IdPeerAns gr p) :
    ∃ tb : Bool,
      idTrustOf p idKey = .ok tb ∧
      StoresGhost.opened.identity.trusted cliIo.rd F peer idKey = .ok tb := by
  obtain ⟨bs, hget, _⟩ := hinitOk.idGet
  have htr := IdGhost.trusted_of_peerAns (k := idKey) (hgr ▸ hp)
  rw [hget] at hgr
  subst hgr
  cases bs with
  | nil =>
    cases hp
    exact ⟨true, rfl, htr⟩
  | cons b rest =>
    obtain ⟨k, rfl, _⟩ := hp
    exact ⟨decide (k = idKey), rfl, htr⟩

/-! ## Read-only vtable slot introduction lemmas -/

theorem sepWPp_with_rodata {prog : Program} {tgt : BitVec 64} {s : State}
    {cell P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hro : ∀ R, (s.mem ⊨ R) → (s.mem ⊨ cell ∗ R))
    (hnext : SepWPp prog tgt s (cell ∗ P) Q Qp oom) :
    SepWPp prog tgt s P Q Qp oom := by
  intro R hm hL
  exact hnext R (by rw [sepConj_assoc]; exact hro (P ∗ R) hm) hL

theorem rodata_idVt_trustSlot_ext {img : Obj.Image} {ext : String → Option (State → State)}
    {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((idVt img + 48#64) ↦₆₄ᵣ (initProgExt img ext).fnAddr idTrustShimName) ∗ R) := by
  intro R hR
  have hfn : (initProgExt img ext).fnAddr idTrustShimName = img.base + KitInst.cliIdTrustShimOff := by
    simp only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase, idTrustShim_fnOff,
      KitInst.cliIdTrustShimOff]
  have hid : idVt img = img.base + KitInst.cliIdVtOff := rfl
  rw [hfn, hid]
  dsimp only [KitInst.cliIdVtOff, KitInst.cliIdTrustShimOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x28) + 48#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") + 8) by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") + 8))
    (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hR

theorem rodata_idVt_trustSlot {img : Obj.Image} {W : CliHooks} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((idVt img + 48#64) ↦₆₄ᵣ (initProg img W).fnAddr idTrustShimName) ∗ R) :=
  rodata_idVt_trustSlot_ext (ext := cliHookExterns W) himg hF

theorem rodata_idTrustFut_drop_ext {img : Obj.Image} {ext : String → Option (State → State)}
    {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((img.base + idTrustFutVtOff) ↦₆₄ᵣ
        (initProgExt img ext).fnAddr KitInst.cliIdFutDropName) ∗ R) := by
  intro R hR
  have hfn : (initProgExt img ext).fnAddr KitInst.cliIdFutDropName =
      img.base + KitInst.cliIdFutDropOff := by
    simp only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      KitInst.cliIdFutDrop_fnOff, KitInst.cliIdFutDropOff]
  rw [hfn, KitInst.cliIdTrustFutVtOff_eq]
  dsimp only [KitInst.cliIdTrustFutVtOff, KitInst.cliIdFutDropOff]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 0x18))
    (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hR

theorem rodata_idTrustFut_drop {img : Obj.Image} {W : CliHooks} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((img.base + idTrustFutVtOff) ↦₆₄ᵣ
        (initProg img W).fnAddr KitInst.cliIdFutDropName) ∗ R) :=
  rodata_idTrustFut_drop_ext (ext := cliHookExterns W) himg hF

theorem rodata_idTrustFut_size {img : Obj.Image} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((img.base + idTrustFutVtOff) + 8#64) ↦₆₄ᵣ 32#64) ∗ R) := by
  intro R hR
  rw [KitInst.cliIdTrustFutVtOff_eq]
  dsimp only [KitInst.cliIdTrustFutVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 0x18) + 8#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 16) by bv_omega]
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 16))
    (n := 8) (bs := unpack64 32#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) KitInst.rodata_cliIdTrustFutSize_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hR

theorem rodata_idTrustFut_align {img : Obj.Image} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((img.base + idTrustFutVtOff) + 16#64) ↦₆₄ᵣ 8#64) ∗ R) := by
  intro R hR
  rw [KitInst.cliIdTrustFutVtOff_eq]
  dsimp only [KitInst.cliIdTrustFutVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 0x18) + 16#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 8) by bv_omega]
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 8))
    (n := 8) (bs := unpack64 8#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) KitInst.rodata_cliIdTrustFutAlign_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hR

theorem rodata_idTrustFut_poll_ext {img : Obj.Image} {ext : String → Option (State → State)}
    {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((img.base + idTrustFutVtOff) + 24#64) ↦₆₄ᵣ
        (initProgExt img ext).fnAddr idTrustPollName) ∗ R) := by
  intro R hR
  have hfn : (initProgExt img ext).fnAddr idTrustPollName = img.base + KitInst.cliIdTrustPollOff := by
    simp only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase, idTrustPoll_fnOff,
      KitInst.cliIdTrustPollOff]
  rw [hfn, KitInst.cliIdTrustFutVtOff_eq]
  dsimp only [KitInst.cliIdTrustFutVtOff, KitInst.cliIdTrustPollOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") - 0x18) + 24#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}")) by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}")) )
    (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hR

theorem rodata_idTrustFut_poll {img : Obj.Image} {W : CliHooks} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((img.base + idTrustFutVtOff) + 24#64) ↦₆₄ᵣ
        (initProg img W).fnAddr idTrustPollName) ∗ R) :=
  rodata_idTrustFut_poll_ext (ext := cliHookExterns W) himg hF

theorem rodata_sessVt_loadSlot_ext {img : Obj.Image} {ext : String → Option (State → State)}
    {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((sessVt img + 24#64) ↦₆₄ᵣ (initProgExt img ext).fnAddr sessLoadShimName) ∗ R) := by
  intro R hR
  have hfn : (initProgExt img ext).fnAddr sessLoadShimName = img.base + KitInst.cliSessLoadShimOff := by
    simp only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase, sessLoadShim_fnOff,
      KitInst.cliSessLoadShimOff]
  have hsess : sessVt img = img.base + KitInst.cliSessVtOff := rfl
  rw [hfn, hsess]
  dsimp only [KitInst.cliSessVtOff, KitInst.cliSessLoadShimOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session") - 24) + 24#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session")) by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session")))
    (target := num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hR

theorem rodata_sessVt_loadSlot {img : Obj.Image} {W : CliHooks} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((sessVt img + 24#64) ↦₆₄ᵣ (initProg img W).fnAddr sessLoadShimName) ∗ R) :=
  rodata_sessVt_loadSlot_ext (ext := cliHookExterns W) himg hF

theorem rodata_sessLoadFut_drop_ext {img : Obj.Image} {ext : String → Option (State → State)}
    {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((img.base + sessLoadFutVtOff) ↦₆₄ᵣ
        (initProgExt img ext).fnAddr KitInst.cliIdFutDropName) ∗ R) := by
  intro R hR
  have hfn : (initProgExt img ext).fnAddr KitInst.cliIdFutDropName =
      img.base + KitInst.cliIdFutDropOff := by
    simp only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      KitInst.cliIdFutDrop_fnOff, KitInst.cliIdFutDropOff]
  rw [hfn, KitInst.cliSessLoadFutVtOff_eq]
  dsimp only [KitInst.cliSessLoadFutVtOff, KitInst.cliIdFutDropOff]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 24))
    (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hR

theorem rodata_sessLoadFut_drop {img : Obj.Image} {W : CliHooks} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((img.base + sessLoadFutVtOff) ↦₆₄ᵣ
        (initProg img W).fnAddr KitInst.cliIdFutDropName) ∗ R) :=
  rodata_sessLoadFut_drop_ext (ext := cliHookExterns W) himg hF

theorem rodata_sessLoadFut_size {img : Obj.Image} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((img.base + sessLoadFutVtOff) + 8#64) ↦₆₄ᵣ 24#64) ∗ R) := by
  intro R hR
  rw [KitInst.cliSessLoadFutVtOff_eq]
  dsimp only [KitInst.cliSessLoadFutVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 24) + 8#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 16) by bv_omega]
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 16))
    (n := 8) (bs := unpack64 24#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) KitInst.rodata_cliSessLoadFutSize_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hR

theorem rodata_sessLoadFut_align {img : Obj.Image} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((img.base + sessLoadFutVtOff) + 16#64) ↦₆₄ᵣ 8#64) ∗ R) := by
  intro R hR
  rw [KitInst.cliSessLoadFutVtOff_eq]
  dsimp only [KitInst.cliSessLoadFutVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 24) + 16#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 8) by bv_omega]
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 8))
    (n := 8) (bs := unpack64 8#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) KitInst.rodata_cliSessLoadFutAlign_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hR

theorem rodata_sessLoadFut_poll_ext {img : Obj.Image} {ext : String → Option (State → State)}
    {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((img.base + sessLoadFutVtOff) + 24#64) ↦₆₄ᵣ
        (initProgExt img ext).fnAddr sessLoadPollName) ∗ R) := by
  intro R hR
  have hfn : (initProgExt img ext).fnAddr sessLoadPollName = img.base + KitInst.cliSessLoadPollOff := by
    simp only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase, sessLoadPoll_fnOff,
      KitInst.cliSessLoadPollOff]
  rw [hfn, KitInst.cliSessLoadFutVtOff_eq]
  dsimp only [KitInst.cliSessLoadFutVtOff, KitInst.cliSessLoadPollOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 24) + 24#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")) by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")))
    (target := num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hR

theorem rodata_sessLoadFut_poll {img : Obj.Image} {W : CliHooks} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((img.base + sessLoadFutVtOff) + 24#64) ↦₆₄ᵣ
        (initProg img W).fnAddr sessLoadPollName) ∗ R) :=
  rodata_sessLoadFut_poll_ext (ext := cliHookExterns W) himg hF

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
