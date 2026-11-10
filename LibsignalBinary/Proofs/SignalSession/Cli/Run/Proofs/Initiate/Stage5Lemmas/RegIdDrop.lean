/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCalls
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTail
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.Epilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.Vtables
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Fetch

/-!
# Stage 5 Registration-ID Future Drop and Branch

Unpacks `idRegIdOutAt` into 6 sret words, drops and frees the 16-byte registration-ID future box
(`+0x14e4..+0x1630`), and branches at `+0x1634` (`cmn x26, #0x2`) between `stage5_err_cleanup_ok`
and `stage5_accept_ok`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

set_option linter.unusedSimpArgs false
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm, -wp_norm] fsp_stage5_eqs
attribute [-arm64_norm]
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

@[local arm64_norm, local wp_norm]
private theorem fsp_compound_offs (fsp : BitVec 64) :
    fsp + 0xe0#64 + 8#64 = fsp + 0xe8#64 ∧ fsp + 0xf0#64 + 8#64 = fsp + 0xf8#64 ∧
    fsp + 0xf8#64 + 8#64 = fsp + 0x100#64 ∧ fsp + 0x100#64 + 8#64 = fsp + 0x108#64 ∧
    fsp + 0x80#64 + 168#64 = fsp + 0x128#64 ∧ fsp + 0x80#64 + 192#64 = fsp + 0x140#64 ∧
    fsp + 0x80#64 + 536#64 = fsp + 0x298#64 ∧ fsp + 0x460#64 + 0x154#64 = fsp + 0x5b4#64 ∧
    fsp + 4096#64 + 1536#64 = fsp + 0x1600#64 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
   by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

/-- Pure/spatial branch characterization of unpacked `idRegIdOutAt` words `rw0..rw5`. -/
def regAnsBranchProp (A : RustAlloc) (retPtr : BitVec 64)
    (ans : Except Unit (BitVec 32)) (rw0 rw1 rw2 rw3 rw4 rw5 : BitVec 64) (SpeH : SepProp) : Prop :=
  match ans with
  | .ok reg => rw0 = 0xFFFFFFFFFFFFFFFE#64 ∧ rw1.setWidth 32 = reg ∧ SpeH = emp
  | .error () =>
    rw0 + 2#64 ≠ 0#64 ∧ ∃ k : RunDrop.SpeOwned,
      ((retPtr ↦₆₄ rw0) ∗ ((retPtr + 0x08#64) ↦₆₄ rw1) ∗ ((retPtr + 0x10#64) ↦₆₄ rw2) ∗
       ((retPtr + 0x18#64) ↦₆₄ rw3) ∗ ((retPtr + 0x20#64) ↦₆₄ rw4) ∗
       ((retPtr + 0x28#64) ↦₆₄ rw5) ∗ SpeH) ⊢ RunDrop.speOwnedAt A retPtr k

theorem unpack_idRegIdOutAt (A : RustAlloc) (fsp retPtr : BitVec 64)
    (ans : Except Unit (BitVec 32)) (R3 : SepProp) (m3 : Memory)
    (hm3 : m3 ⊨ idRegIdOutAt A (fsp + 0x1600#64) ans ∗ R3) :
    ∃ (rw0 rw1 rw2 rw3 rw4 rw5 : BitVec 64) (SpeH : SepProp),
      rw0 + 3#64 ≠ 0#64 ∧
      (m3 ⊨ ((fsp + 0x1600#64) ↦₆₄ rw0) ∗ (((fsp + 0x1600#64) + 0x08#64) ↦₆₄ rw1) ∗
            (((fsp + 0x1600#64) + 0x10#64) ↦₆₄ rw2) ∗ (((fsp + 0x1600#64) + 0x18#64) ↦₆₄ rw3) ∗
            (((fsp + 0x1600#64) + 0x20#64) ↦₆₄ rw4) ∗ (((fsp + 0x1600#64) + 0x28#64) ↦₆₄ rw5) ∗
            (SpeH ∗ R3)) ∧
      regAnsBranchProp A retPtr ans rw0 rw1 rw2 rw3 rw4 rw5 SpeH := by
  cases ans with
  | ok reg =>
    dsimp only [idRegIdOutAt, regAnsBranchProp] at hm3 ⊢
    have hm4 : m3 ⊨ (((fsp + 0x1600#64) + 0x08#64) ↦₃₂ reg ∗
        memRegion ((fsp + 0x1600#64) + 0x0c#64) 36) ∗
        (((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ R3) :=
      sat_eq (by ac_rfl) hm3
    have hm5 := Satisfies.mono (sepConj_mono_left (u32_tail36_words5 (fsp + 0x1600#64) reg)) hm4
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm5
    obtain ⟨rw1, rw2, rw3, rw4, rw5, hm5⟩ := hm5
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm5
    obtain ⟨hrw1, hm5⟩ := hm5
    refine ⟨0xFFFFFFFFFFFFFFFE#64, rw1, rw2, rw3, rw4, rw5, emp, by decide, ?_, rfl, hrw1, rfl⟩
    exact sat_eq (by ac_rfl) hm5
  | error u =>
    cases u
    dsimp only [idRegIdOutAt, regAnsBranchProp] at hm3 ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm3
    obtain ⟨k, hm3⟩ := hm3
    obtain ⟨rw0, rw1, rw2, rw3, rw4, rw5, SpeH, hne3, hne2, hmK, hfoldK⟩ :=
      speOwnedAt_words6 A (fsp + 0x1600#64) retPtr k R3 m3 hm3
    exact ⟨rw0, rw1, rw2, rw3, rw4, rw5, SpeH, hne3, hmK, hne2, k, hfoldK⟩

/-- Generic `extP`-parameterized control-state invariant for Stage 5. -/
structure S5InInitiate (img : Obj.Image) (extP : String → Option (State → State))
    (s0 s : State) (k : Nat) : Prop where
  pc : s.pc = (tripleRatchetProgAtExt img.base extP).fnAddr cliInitiateName + BitVec.ofNat 64 k
  run : s.status = .Running
  sp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame
  fp : s.readReg64 .fp = s0.sp - 0x60#64
  x19 : s.readReg64 (.gpr 19#5) = s0.readReg64 .x8
  files0 : s.fs.files = s0.fs.files
  inv : ImgCallInv img s
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  spAligned : s0.spAligned = true

/-- Generic `extP`-parameterized Cut 4 (`BB143`, offset `0x1484`) state predicate unifying
`AtStage5` and `AtStage5Ext`. -/
structure S5AtStage5 (img : Obj.Image) (P : PEParams)
    (extP : String → Option (State → State)) (X : UnreachedPqxdhPrimitives) (x : InitGhost)
    (be : PreKeyBundleFields) (kp : IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
    (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
    (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (s0 s : State) : Prop where
  ctrl : S5InInitiate img extP s0 s 0x1484
  trace : s.trace = s0.trace
  files : s.fs.files = x.F
  x8 : s0.readReg64 .x8 = x.ret
  bundleEq : bundleEOf? x.bundle = some be
  trustedOk : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true
  kpOk : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp
  ekPairEq :
    let ekKP := keyPairOf P.C ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
    ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList
  opkIdEq : ∀ p, x.bundle.opk = some p → opkId = p.1
  keysOk : SignalPqxdh.Model.initiateKeys (modelPrims X P)
    (initiateInput P ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)) = some (dk, hdr)
  initSessOk : initializeInitiatorSession P.C (pqxdhSpqrSession P)
    ⟨(keyPairOf P.C kp.privateKey.bytes).publicKey⟩ ⟨⟨be.idPub⟩⟩ ⟨be.spkPub⟩
    (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
    (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
    (HKDF.bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32)) = .ok ss
  pqLen : ss.pqRatchetState.length ≤ 1208
  canonPre :
    sg.localIk.bytes = ss.localIdentity.serialize ∧
    (match ss.remoteIdentity with
     | none => sg.remoteIk.bytes = []
     | some ik => sg.remoteIk.bytes = ik.serialize) ∧
    sg.alice.bytes = (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize ∧
    sg.pending = none ∧
    (∃ kg, sg.kyber = some kg ∧ kg.vec.bytes = 0x08#8 :: ofU8 hdr.kemCt) ∧
    (∃ scg sc, sg.sender = some scg ∧ ss.senderChain = some sc ∧
      scg.srk.bytes = sc.ratchetKey.publicKey.serialize ∧
      scg.priv.bytes = sc.ratchetKey.privateKey.bytes.toList) ∧
    ∀ gc ∈ sg.chains.zip ss.receiverChains,
      gc.1.srk.bytes = gc.2.senderRatchetKey.serialize ∧ gc.1.priv.bytes = []
  pqspkNonNull : pqspkPtr ≠ 0#64
  x20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64

theorem S5AtStage5.of_atStage5 {img : Obj.Image} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {x : InitGhost}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32} {s0 s : State}
    (h : AtStage5 img W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s) :
    S5AtStage5 img ⟨W.C, W.Q⟩ (cliExterns W) X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s :=
  ⟨⟨h.ctrl.pc, h.ctrl.run, h.ctrl.sp, h.ctrl.fp, h.ctrl.x19, h.ctrl.files0,
    h.ctrl.inv, h.ctrl.vregs, h.ctrl.spAligned⟩,
   h.trace, h.files, h.x8, h.bundleEq, h.trustedOk, h.kpOk, h.ekPairEq, h.opkIdEq,
   h.keysOk, h.initSessOk, h.pqLen, h.canonPre, h.pqspkNonNull, h.x20⟩

theorem S5AtStage5.of_atStage5Ext {img : Obj.Image} {P : PEParams}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {x : InitGhost}
    {be : PreKeyBundleFields} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32} {s0 s : State}
    (h : AtStage5Ext img P ext X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s) :
    S5AtStage5 img P (cliExternsWith ext) X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s :=
  ⟨⟨h.ctrl.pc, h.ctrl.run, h.ctrl.sp, h.ctrl.fp, h.ctrl.x19, h.ctrl.files0,
    h.ctrl.inv, h.ctrl.vregs, h.ctrl.spAligned⟩,
   h.trace, h.files, h.x8, h.bundleEq, h.trustedOk, h.kpOk, h.ekPairEq, h.opkIdEq,
   h.keysOk, h.initSessOk, h.pqLen, h.canonPre, h.pqspkNonNull, h.x20⟩

/-- Ext-parameterized Steps 5 & 6 (`+0x14e4 .. +0x1630`) on a minimal 12-atom spatial frame: loads
`rw0..rw5` into `x26, x27, x25, x28, x24, x21`, drops and deallocates the 16-byte registration-id
future box, and folds the 6 sret words back into `memRegion (fsp + 0x1600#64) 48`. -/
theorem stage5_reg_drop_dealloc_ok_ext {img : Obj.Image} {A : RustAlloc}
    {extP : String → Option (State → State)} {B : RunBudgets}
    {fsp storesPtr futPtr rw0 rw1 rw2 rw3 rw4 rw5 : BitVec 64}
    {Frame56 : SepProp} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img) (hExt : Stage5ExternDeps img A extP)
    (hStore : InitStoreCalleesExt img A extP B stk)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hrw0_ne3 : rw0 + 3#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base extP).fnAddr cliInitiateName + offAfterRegPoll)
    (_hrun : s.status = .Running) (hsp : s.sp = fsp) (hal : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (hinv : ImgCallInv img s)
    (htr : s.trace = s0.trace)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hnext : ∀ (RoExtra : SepProp) (sm6 : State),
      sm6.pc = (tripleRatchetProgAtExt img.base extP).fnAddr cliInitiateName + offRegDeallocDone →
      sm6.status = .Running → sm6.sp = fsp →
      calleeSavedVRegs sm6 = calleeSavedVRegs s0 → ImgCallInv img sm6 →
      sm6.trace = s0.trace → sm6.fs.files = s.fs.files →
      sm6.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm6.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sm6.readReg64 (.gpr 21#5) = rw5 →
      sm6.readReg64 (.gpr 24#5) = rw4 →
      sm6.readReg64 (.gpr 25#5) = rw2 →
      sm6.readReg64 (.gpr 26#5) = rw0 →
      sm6.readReg64 (.gpr 27#5) = rw1 →
      sm6.readReg64 (.gpr 28#5) = rw3 →
      SepWPp (tripleRatchetProgAtExt img.base extP) (s0.readReg64 .lr) sm6
        (((fsp + 0x5c8#64) ↦₆₄ futPtr) ∗
          ((fsp + 0x5d0#64) ↦₆₄ (img.base + idRegIdFutVtOff)) ∗
          memRegion (fsp + 0x1600#64) 48 ∗ A.pool ∗
          stackAt fsp (stk - cliInitiateFrame) ∗ Frame56 ∗ RoExtra) Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base extP) (s0.readReg64 .lr) s
      (((fsp + 0x5c8#64) ↦₆₄ futPtr) ∗
        ((fsp + 0x5d0#64) ↦₆₄ (img.base + idRegIdFutVtOff)) ∗
        ((fsp + 0x1600#64) ↦₆₄ rw0) ∗ (((fsp + 0x1600#64) + 0x08#64) ↦₆₄ rw1) ∗
        (((fsp + 0x1600#64) + 0x10#64) ↦₆₄ rw2) ∗ (((fsp + 0x1600#64) + 0x18#64) ↦₆₄ rw3) ∗
        (((fsp + 0x1600#64) + 0x20#64) ↦₆₄ rw4) ∗ (((fsp + 0x1600#64) + 0x28#64) ↦₆₄ rw5) ∗
        idOwnFutBoxAt futPtr storesPtr 1#8 ∗ A.live futPtr 16 8 ∗ A.pool ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Frame56) Q Qp := by
  have hfn := cliInitiate_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode stage5EpilogueBin img.base
    (Rust.withPanics extP) hfn
    (num% (ls_off% "libsignal_cli_handshake::initiate")) 5348 12
  code_fetches_from CryptoVerification.libsignalSessionCode stage5MidBin img.base
    (Rust.withPanics extP) hfn
    (num% (ls_off% "libsignal_cli_handshake::initiate")) 5620 64
  clear hfn
  dsimp only [tripleRatchetProgAtExt] at hpc
  generalize_entry h_entry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics extP)).fnAddr cliInitiateName =
      entry
  examples_hide_fetches
  have hDealloc : subroutine_ok (tripleRatchetProgAtExt img.base extP)
      (entry + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
    @Eq.subst (BitVec 64)
      (fun e => subroutine_ok (tripleRatchetProgAtExt img.base extP)
        (e + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
        ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
      _ entry h_entry hExt.dealloc_at
  clear h_entry
  have hfutDropNe : img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff KitInst.cliIdFutDropName) ≠ 0#64 :=
    futDrop_ne_zero himg
  have hsretOffs := sret_word_offs fsp
  conv =>
    arg 4
    rw [hsretOffs.1, hsretOffs.2.1, hsretOffs.2.2.1, hsretOffs.2.2.2.1, hsretOffs.2.2.2.2,
        show fsp + 0x5c8#64 = fsp + 1480#64 by bv_omega,
        show fsp + 0x5d0#64 = fsp + 1488#64 by bv_omega]
    simp only [sepConj_assoc]
  apply s5_with_rodata (idRegIdFut_drop_rodata himg hinv.1)
  generalize hdrop : img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff KitInst.cliIdFutDropName) = dropAddr
  have hdropNe : dropAddr ≠ 0#64 := hdrop ▸ hfutDropNe
  s5_have_eq hpRegStep5 :
      (((img.base + idRegIdFutVtOff) ↦₆₄ᵣ dropAddr) ∗ ((fsp + 0x1600#64) ↦₆₄ rw0) ∗
        ((fsp + 5640#64) ↦₆₄ rw1) ∗ ((fsp + 5648#64) ↦₆₄ rw2) ∗ ((fsp + 5656#64) ↦₆₄ rw3) ∗
        ((fsp + 5664#64) ↦₆₄ rw4) ∗ ((fsp + 5672#64) ↦₆₄ rw5) ∗
        ((fsp + 1488#64) ↦₆₄ (img.base + idRegIdFutVtOff)) ∗
        ((fsp + 1480#64) ↦₆₄ futPtr)) ∗ ?remRegStep5 := by s5_ac_rfl
  apply sepWPp_step_to_frozen_mem_framed hinv hpRegStep5 (mid := dropAddr)
  · s5_clear_callees
    dsimp only [tripleRatchetProgAtExt, offAfterRegPoll] at hpc ⊢
    wp_steps
    simp (config := { failIfUnchanged := false }) only [beq_eq_false_iff_ne.mpr hrw0_ne3,
      Bool.false_eq_true, ↓reduceIte]
    try wp_steps
    simp (config := { failIfUnchanged := false }) only [beq_eq_false_iff_ne.mpr hdropNe,
      Bool.false_eq_true, ↓reduceIte]
    try wp_steps
    s5_step_done
  intro _ hF5 hsym5; subst hdrop
  conv => arg 4; simp only [sepConj_assoc]
  refine s5_call_futDrop_ext (ret_pc := entry + offRegDealloc)
    hExt hStore fsp _
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal)
    (by dsimp only [offRegDealloc]; wp_norm_goal)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) ⟨hF5, hsym5⟩
    hpan (Entails.refl _) ?_
  intro sm5 hpc5 _hrun5 hsp5 hal5 hcs5 hinv5 htr5 hfs5
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hvregs] at hcs5
  rcases hcs5 with ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, _, hvregs_5⟩
  apply s5_with_rodata (idRegIdFut_size_rodata himg hinv5.1)
  apply s5_with_rodata (idRegIdFut_align_rodata himg hinv5.1)
  apply sepWPp_step_to_frozen_mem hinv5
    (mid := entry +
      bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
  · s5_clear_callees
    dsimp only [tripleRatchetProgAtExt, offRegDealloc] at hpc5 ⊢
    wp_steps
    s5_step_done
  intro _ hF6 hsym6
  have hboxMem := idOwnFutBoxAt_entails_memRegion16 futPtr storesPtr 1#8
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)]
    simp only [sepConj_assoc]
  refine s5_call_dealloc_ext (ret_pc := entry + offRegDeallocDone)
    hExt hDealloc fsp futPtr 16 8 ?eF6
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp5])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal5)
    (by dsimp only [offRegDeallocDone]; wp_norm_goal)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr5]) ⟨hF6, hsym6⟩
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx23_5])
    (by wp_norm_goal) (by wp_norm_goal) layoutOk_16_8
    hpan ?ePre6 ?_
  case ePre6 =>
    inImageKitClearInvHyps
    s5_have_eq hpull :
        idOwnFutBoxAt futPtr storesPtr 1#8 ∗ ?restRegBox := by
      conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp5]
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpull)
      (Entails.trans (sepConj_mono_left hboxMem) ?_)
    s5_close_frame
  intro sm6 hpc6 hrun6 hsp6 _hal6 hcs6 hinv6 htr6 hfs6
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_5, hx20_5, hx21_5, hx24_5, hx25_5,
    hx26_5, hx27_5, hx28_5, hvregs_5] at hcs6
  rcases hcs6 with ⟨hx19_6, hx20_6, hx21_6, _, _, hx24_6, hx25_6, hx26_6, hx27_6, hx28_6, _, hvregs_6⟩
  s5_rw_pre (s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)).symm
  have hw48 := words6_entails_memRegion48 (fsp + 0x1600#64) rw0 rw1 rw2 rw3 rw4 rw5
  have hsretSymm := sret_word_offs_symm fsp
  s5_have_eq hpW48 :
      (((fsp + 0x1600#64) ↦₆₄ rw0) ∗ (((fsp + 0x1600#64) + 0x08#64) ↦₆₄ rw1) ∗
        (((fsp + 0x1600#64) + 0x10#64) ↦₆₄ rw2) ∗ (((fsp + 0x1600#64) + 0x18#64) ↦₆₄ rw3) ∗
        (((fsp + 0x1600#64) + 0x20#64) ↦₆₄ rw4) ∗ (((fsp + 0x1600#64) + 0x28#64) ↦₆₄ rw5)) ∗
      ?remAfterReg48 := by
    conv =>
      lhs
      rw [hsretSymm.1, hsretSymm.2.1, hsretSymm.2.2.1, hsretSymm.2.2.2.1, hsretSymm.2.2.2.2]
    s5_ac_rfl
  refine sepWPp_conseq (Entails.trans (Entails.of_eq hpW48) (sepConj_mono_left hw48)) ?_
  refine sepWPp_conseq ?_
    (hnext ?roExtra sm6 hpc6 hrun6 hsp6 hvregs_6 hinv6 htr6 (hfs6.trans hfs5)
      hx19_6 hx20_6 hx21_6 hx24_6 hx25_6 hx26_6 hx27_6 hx28_6)
  inImageKitClearInvHyps
  conv =>
    lhs
    rw [show fsp + 1480#64 = fsp + 0x5c8#64 by bv_omega,
        show fsp + 1488#64 = fsp + 0x5d0#64 by bv_omega]
  exact Entails.of_eq (by s5_ac_rfl)

theorem stage5_reg_drop_dealloc_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {B : RunBudgets}
    {fsp storesPtr futPtr rw0 rw1 rw2 rw3 rw4 rw5 : BitVec 64}
    {Frame56 : SepProp} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooks img A (cliExterns W))
    (hStore : InitStoreCallees img A W B stk)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hrw0_ne3 : rw0 + 3#64 ≠ 0#64)
    (hpc : s.pc = (initProg img W).fnAddr cliInitiateName + offAfterRegPoll)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hal : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (hinv : ImgCallInv img s)
    (htr : s.trace = s0.trace)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hnext : ∀ (RoExtra : SepProp) (sm6 : State),
      sm6.pc = (initProg img W).fnAddr cliInitiateName + offRegDeallocDone →
      sm6.status = .Running → sm6.sp = fsp →
      calleeSavedVRegs sm6 = calleeSavedVRegs s0 → ImgCallInv img sm6 →
      sm6.trace = s0.trace → sm6.fs.files = s.fs.files →
      sm6.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm6.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sm6.readReg64 (.gpr 21#5) = rw5 →
      sm6.readReg64 (.gpr 24#5) = rw4 →
      sm6.readReg64 (.gpr 25#5) = rw2 →
      sm6.readReg64 (.gpr 26#5) = rw0 →
      sm6.readReg64 (.gpr 27#5) = rw1 →
      sm6.readReg64 (.gpr 28#5) = rw3 →
      SepWPp (initProg img W) (s0.readReg64 .lr) sm6
        (((fsp + 0x5c8#64) ↦₆₄ futPtr) ∗
          ((fsp + 0x5d0#64) ↦₆₄ (img.base + idRegIdFutVtOff)) ∗
          memRegion (fsp + 0x1600#64) 48 ∗ A.pool ∗
          stackAt fsp (stk - cliInitiateFrame) ∗ Frame56 ∗ RoExtra) Q Qp) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (((fsp + 0x5c8#64) ↦₆₄ futPtr) ∗
        ((fsp + 0x5d0#64) ↦₆₄ (img.base + idRegIdFutVtOff)) ∗
        ((fsp + 0x1600#64) ↦₆₄ rw0) ∗ (((fsp + 0x1600#64) + 0x08#64) ↦₆₄ rw1) ∗
        (((fsp + 0x1600#64) + 0x10#64) ↦₆₄ rw2) ∗ (((fsp + 0x1600#64) + 0x18#64) ↦₆₄ rw3) ∗
        (((fsp + 0x1600#64) + 0x20#64) ↦₆₄ rw4) ∗ (((fsp + 0x1600#64) + 0x28#64) ↦₆₄ rw5) ∗
        idOwnFutBoxAt futPtr storesPtr 1#8 ∗ A.live futPtr 16 8 ∗ A.pool ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Frame56) Q Qp :=
  stage5_reg_drop_dealloc_ok_ext himg (stage5ExternDeps_of_runHooks hh)
    (initStoreCallees_to_ext hStore) hstk hstk64 hrw0_ne3 hpc hrun hsp hal hvregs hinv htr hpan hnext

/-- Ext-parameterized Step 7 (`+0x1634 .. +0x1638`): branches on `ans` (`cmn x26, #0x2; b.ne +0x1858`)
to `stage5_err_cleanup_ok_ext` or `stage5_accept_ok_ext`. -/
theorem stage5_branch_after_reg_ok_ext {img : Obj.Image} {A : RustAlloc}
    {P : PEParams} {extP : String → Option (State → State)}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr dataPtr futPtr rw0 rw1 rw2 rw3 rw4 rw5 : BitVec 64}
    {opkId padVal w1_kyb : BitVec 32} {ans : Except Unit (BitVec 32)}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))} {kg : TailVecGhost}
    {BRest SpeH Extra : SepProp} {stk : Nat} {s0 s5 sm6 : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img) (hExt : Stage5ExternDeps img A extP)
    (hStore : InitStoreCalleesExt img A extP B stk) (hCal : Stage5CalleesExt img A extP)
    (hS : S.initiate = initDef X P) (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs5 : S5AtStage5 img P extP X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (halice : sg.alice.bytes = (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize)
    (hkgBytes : kg.vec.bytes = 0x08#8 :: ofU8 hdr.kemCt)
    (hkemLen : (0x08#8 :: ofU8 hdr.kemCt).length = 1569)
    (hkyberKey : kyberKey (u8Vec 1568 hdr.kemCt) = 0x08#8 :: ofU8 hdr.kemCt)
    (hekLen : ekASk.length = 32 ∧ ekAPk.length = 32) (hkpkLen : x.bundle.kpk.length = 1568)
    (hfoldBundle :
      ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ⊢
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr)
    (hansReg' : ans = StoresGhost.opened.identity.regId cliIo.rd x.F)
    (hrw0_ne3 : rw0 + 3#64 ≠ 0#64)
    (hansBranch : regAnsBranchProp A x.ret ans rw0 rw1 rw2 rw3 rw4 rw5 SpeH)
    (hpc6 : sm6.pc = (tripleRatchetProgAtExt img.base extP).fnAddr cliInitiateName + offRegDeallocDone)
    (_hrun6 : sm6.status = .Running)
    (hsp6 : sm6.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hvregs_6 : calleeSavedVRegs sm6 = calleeSavedVRegs s0) (hinv6 : ImgCallInv img sm6)
    (htr6 : sm6.trace = s0.trace) (hfs0 : s0.fs.files = x.F) (hfs6' : sm6.fs.files = x.F)
    (hx19_6 : sm6.readReg64 (.gpr 19#5) = x.ret)
    (hx20_6 : sm6.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64)
    (hx21_6 : sm6.readReg64 (.gpr 21#5) = rw5)
    (hx24_6 : sm6.readReg64 (.gpr 24#5) = rw4)
    (hx25_6 : sm6.readReg64 (.gpr 25#5) = rw2)
    (hx26_6 : sm6.readReg64 (.gpr 26#5) = rw0)
    (hx27_6 : sm6.readReg64 (.gpr 27#5) = rw1)
    (hx28_6 : sm6.readReg64 (.gpr 28#5) = rw3)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
    let pg : TailVecGhost :=
      { vec := ⟨33#64, dataPtr, (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize⟩
        tail := unpack32 opkFlag ++ unpack32 opkId ++ unpack64 0#64 ++
                  unpack32 x.bundle.spkId ++ unpack32 padVal }
    let kg' : TailVecGhost := { vec := kg.vec, tail := unpack32 x.bundle.kpkId ++ unpack32 w1_kyb }
    let sg₁ : SessionGhost := { sg with pending := some pg, kyber := some kg' }
    SepWPp (tripleRatchetProgAtExt img.base extP) (s0.readReg64 .lr) sm6
      (storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ∗
        coinsCursorAt img x.coinsP x.coins 192 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ logOff img ∗ A.pool ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗ initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        sessionStateAt A (fsp + 0x460#64) sg₁ ss.setUnacknowledgedPreKeyMessage ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
        stage5ScratchAt fsp (fsp + 0x460#64) futPtr (img.base + idRegIdFutVtOff) ∗
        SpeH ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Extra) Q Qp := by
  intro fsp opkFlag pg kg' sg₁
  have hfn := cliInitiate_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode stage5MidBin img.base
    (Rust.withPanics extP) hfn
    (num% (ls_off% "libsignal_cli_handshake::initiate")) 5684 8
  clear hfn
  dsimp only [tripleRatchetProgAtExt] at hpc6
  generalize_entry h_entry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics extP)).fnAddr cliInitiateName =
      entry
  examples_hide_fetches
  have h_entry_box : ∃ _ : Unit, (tripleRatchetProgAtExt img.base extP).fnAddr cliInitiateName = entry :=
    ⟨(), h_entry⟩
  clear h_entry
  cases ans with
  | error u =>
    cases u
    dsimp only [regAnsBranchProp] at hansBranch
    obtain ⟨hrw0_ne2, k, hfoldK⟩ := hansBranch
    have hx26_ne2 : sm6.readReg64 (.gpr 26#5) + 2#64 ≠ 0#64 := by
      rw [hx26_6]; exact hrw0_ne2
    have hrw0_neFD : rw0 ≠ 0xFFFFFFFFFFFFFFFD#64 := by
      intro h; exact hrw0_ne3 (by subst h; decide)
    apply sepWPp_step_to_frozen_mem hinv6 (mid := entry + offErrEntry)
    · s5_clear_callees
      dsimp only [tripleRatchetProgAtExt, offRegDeallocDone, offErrEntry] at hpc6 ⊢
      wp_steps
      simp (config := { failIfUnchanged := false }) only [beq_eq_false_iff_ne.mpr hx26_ne2,
        Bool.false_eq_true, ↓reduceIte]
      try wp_steps
      s5_step_done
    intro _ hF7 hsym7
    have hansErr : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none := by
      rw [hS]
      exact initDef_eq_some_none_of_regId_err hs5.bundleEq hs5.trustedOk hs5.kpOk hansReg'.symm
    have hscrMerge := scratch_merge fsp (fsp + 0x460#64) futPtr (img.base + idRegIdFutVtOff)
    obtain ⟨_, h_init_entry⟩ := h_entry_box
    refine sepWPp_conseq ?_
      (stage5_err_cleanup_ok_ext (B := B) (kp := kp) (pqspkPtr := pqspkPtr) (opkId := opkId) (k := k) (sg' := sg₁)
        (ss' := ss.setUnacknowledgedPreKeyMessage) (SpeHeap := SpeH) (Extra := ?extraErr)
        hExt hCal hstk hstk64 hekLen hkpkLen hansErr
        (Eq.trans (by dsimp only [offErrEntry]; wp_norm_goal : _ = entry + offErrEntry)
          (congrArg (· + offErrEntry) h_init_entry.symm))
        (by wp_norm_lhs)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp6])
        hs5.ctrl.spAligned
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hvregs_6])
        ⟨hF7, hsym7⟩
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr6])
        hfs0 hfs6'
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_6])
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx20_6])
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx26_6]; exact hrw0_neFD)
        (by
          simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx26_6, hx27_6,
            hx25_6, hx28_6, hx24_6, hx21_6]
          exact hfoldK)
        hpost hpan)
    inImageKitClearInvHyps
    s5_have_eq hpB :
        (((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗
          ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
          ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest) ∗ ?remErrB := by
      conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero]
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpB) (Entails.trans (sepConj_mono_left hfoldBundle) ?_)
    s5_have_eq hpS :
        stage5ScratchAt fsp (fsp + 0x460#64) futPtr (img.base + idRegIdFutVtOff) ∗ ?remErrS := by
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpS) (Entails.trans (sepConj_mono_left hscrMerge) ?_)
    simp (config := { failIfUnchanged := false }) only [emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by s5_ac_rfl)
  | ok reg =>
    dsimp only [regAnsBranchProp] at hansBranch
    obtain ⟨rfl, hrw1, rfl⟩ := hansBranch
    apply sepWPp_step_to_frozen_mem hinv6 (mid := entry + offSave)
    · s5_clear_callees
      dsimp only [tripleRatchetProgAtExt, offRegDeallocDone, offSave] at hpc6 ⊢
      wp_steps
      simp (config := { failIfUnchanged := false }) only [hx26_6,
        show (0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 2#64 = 0#64 by decide,
        beq_self_eq_true, ↓reduceIte]
      try wp_steps
      s5_step_done
    intro _ hF7 hsym7
    obtain ⟨_, h_init_entry⟩ := h_entry_box
    refine sepWPp_conseq ?_
      (stage5_accept_ok_ext (pqspkPtr := pqspkPtr) (dataPtr := dataPtr) (opkId := opkId) (padVal := padVal) (w1_kyb := w1_kyb)
        (w5c8 := futPtr) (w5d0 := img.base + idRegIdFutVtOff) (Extra := ?extraAcc)
        himg hExt hStore hCal hS hinitOk hstk hstk64
        hs5.bundleEq hs5.trustedOk hs5.kpOk hansReg'.symm hs5.opkIdEq
        hs5.keysOk hs5.initSessOk hs5.pqLen halice hkgBytes hkemLen hkyberKey
        hekLen hkpkLen hfoldBundle
        (Eq.trans (by dsimp only [offSave]; wp_norm_goal : _ = entry + offSave)
          (congrArg (· + offSave) h_init_entry.symm))
        (by wp_norm_lhs)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp6])
        hs5.ctrl.spAligned
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hvregs_6])
        ⟨hF7, hsym7⟩
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr6])
        hfs0 hfs6'
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_6])
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx20_6])
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx27_6, hrw1])
        hpost hpan)
    inImageKitClearInvHyps
    dsimp only [storesAt]
    conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero]
    simp (config := { failIfUnchanged := false }) only [emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by s5_ac_rfl)

theorem stage5_branch_after_reg_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr dataPtr futPtr rw0 rw1 rw2 rw3 rw4 rw5 : BitVec 64}
    {opkId padVal w1_kyb : BitVec 32} {ans : Except Unit (BitVec 32)}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))} {kg : TailVecGhost}
    {BRest SpeH Extra : SepProp} {stk : Nat} {s0 s5 sm6 : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img) (hh : RunHooks img A (cliExterns W))
    (hStore : InitStoreCallees img A W B stk) (hLocal : InitLocalCallees img A W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩) (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs5 : AtStage5 img W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (halice : sg.alice.bytes = (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize)
    (hkgBytes : kg.vec.bytes = 0x08#8 :: ofU8 hdr.kemCt)
    (hkemLen : (0x08#8 :: ofU8 hdr.kemCt).length = 1569)
    (hkyberKey : kyberKey (u8Vec 1568 hdr.kemCt) = 0x08#8 :: ofU8 hdr.kemCt)
    (hekLen : ekASk.length = 32 ∧ ekAPk.length = 32) (hkpkLen : x.bundle.kpk.length = 1568)
    (hfoldBundle :
      ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ⊢
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr)
    (hansReg' : ans = StoresGhost.opened.identity.regId cliIo.rd x.F)
    (hrw0_ne3 : rw0 + 3#64 ≠ 0#64)
    (hansBranch : regAnsBranchProp A x.ret ans rw0 rw1 rw2 rw3 rw4 rw5 SpeH)
    (hpc6 : sm6.pc = (initProg img W).fnAddr cliInitiateName + offRegDeallocDone)
    (hrun6 : sm6.status = .Running)
    (hsp6 : sm6.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hvregs_6 : calleeSavedVRegs sm6 = calleeSavedVRegs s0) (hinv6 : ImgCallInv img sm6)
    (htr6 : sm6.trace = s0.trace) (hfs0 : s0.fs.files = x.F) (hfs6' : sm6.fs.files = x.F)
    (hx19_6 : sm6.readReg64 (.gpr 19#5) = x.ret)
    (hx20_6 : sm6.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64)
    (hx21_6 : sm6.readReg64 (.gpr 21#5) = rw5)
    (hx24_6 : sm6.readReg64 (.gpr 24#5) = rw4)
    (hx25_6 : sm6.readReg64 (.gpr 25#5) = rw2)
    (hx26_6 : sm6.readReg64 (.gpr 26#5) = rw0)
    (hx27_6 : sm6.readReg64 (.gpr 27#5) = rw1)
    (hx28_6 : sm6.readReg64 (.gpr 28#5) = rw3)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
    let pg : TailVecGhost :=
      { vec := ⟨33#64, dataPtr, (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize⟩
        tail := unpack32 opkFlag ++ unpack32 opkId ++ unpack64 0#64 ++
                  unpack32 x.bundle.spkId ++ unpack32 padVal }
    let kg' : TailVecGhost := { vec := kg.vec, tail := unpack32 x.bundle.kpkId ++ unpack32 w1_kyb }
    let sg₁ : SessionGhost := { sg with pending := some pg, kyber := some kg' }
    SepWPp (initProg img W) (s0.readReg64 .lr) sm6
      (storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ∗
        coinsCursorAt img x.coinsP x.coins 192 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ logOff img ∗ A.pool ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗ initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        sessionStateAt A (fsp + 0x460#64) sg₁ ss.setUnacknowledgedPreKeyMessage ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
        stage5ScratchAt fsp (fsp + 0x460#64) futPtr (img.base + idRegIdFutVtOff) ∗
        SpeH ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Extra) Q Qp :=
  stage5_branch_after_reg_ok_ext himg (stage5ExternDeps_of_runHooks hh)
    (initStoreCallees_to_ext hStore) (Stage5CalleesExt.of_initLocalCallees hLocal)
    hS hinitOk hstk hstk64 (S5AtStage5.of_atStage5 hs5)
    halice hkgBytes hkemLen hkyberKey hekLen hkpkLen hfoldBundle
    hansReg' hrw0_ne3 hansBranch hpc6 hrun6 hsp6 hvregs_6 hinv6 htr6 hfs0 hfs6'
    hx19_6 hx20_6 hx21_6 hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 hpost hpan

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
