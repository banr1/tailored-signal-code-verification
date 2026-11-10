/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3c
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3b
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0Sym
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Root
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegFront.S0A
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.Callees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SameAccount
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegBackS7
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegBackS8
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegBackS9
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegDhMain
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.Common
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.ErrTailProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.S0A
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.S1Proof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.S2B
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegMidS4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegMidS5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegMidS6
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.DecryptPqTrapBridge
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.Seams
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Model
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.Common
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Responder Closure Stage P3 Full Assembly (`+0x1778 → +0x34dc` / `x30`)

Proves `stageP3_v4_full_ok`, unified `stageP3_ok` across all `msgVer`, and
`stageP3_initSession_ok` from `initializeRecipientSession` output.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

namespace P3P4

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

open CryptoVerification.LibsignalTripleRatchet.RawByteMove

open CryptoVerification.LibsignalTripleRatchet.Record

open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps

open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts

open CryptoVerification.LibsignalTripleRatchet.ChainClone3

open CryptoVerification.LibsignalSession

open CryptoVerification.E2E.Pqxdh.WireEntries

open CryptoVerification.E2E.Pqxdh.ResponderStore

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section TryDecryptPqDistinct

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

open CryptoVerification.LibsignalTripleRatchet.DecryptPq.Model

open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA

def _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpecP (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  { CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpec C A ctl uuidParse S img with
    pre := fun x s => ⌜x.st.pqRatchetState = [] ∧ s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧
        s.readReg64 .x2 = x.remA ∧ s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧
        (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧ (x.st.remoteIdentity ≠ some
        x.st.localIdentity ∨ DistinctSid uuidParse x.loc.name.bytes x.rem.name.bytes) ∧ SeedsLen32
        x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗ sessionStateAt A x.ss
        x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool }

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_remote_some_wp_pq_distinct {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (x : TryDecryptGhost) (remIk : IdentityKey) (s : State)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec
    8) (w3 : BitVec 64) (b31 : BitVec 8) (u400 : BitVec 64) (u408 : BitVec 8) (dw0 : BitVec 32) (db4
    db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 : BitVec 8)
    (dw3 : BitVec 64) (db31 : BitVec 8) (h_pc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 384#64) (h_run : s.status = .Running) (h_sp_align : s.spAligned =
    true) (hx8 : s.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13) (hx9 : s.readReg64 .x9 =
    pack64 b14 b15 b16 b17 b18 b19 b20 b21) (hx10 : s.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s.readReg64 .x11 = 1#64) (hx20 : s.readReg64 .x20 = s.sp + 320#64) (hx25 : s.readReg64
    .x25 = x.locA) (hx29 : s.readReg64 .x29 = s.sp + 1408#64) (hrem_eq : ∀ a : BitVec 64, (a ↦ₛ
    remIk.publicKey.bytes.toList) = remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
    b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk ∨ DistinctSid uuidTryParse x.loc.name.bytes
    x.rem.name.bytes) :
    let entry := (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    SepWP
      (tripleRatchetProgAt b C ctl abs) (entry + 472#64) s
      (((s.sp + 48#64) ↦₆₄ x.remA) ∗ ((s.sp + 400#64) ↦₆₄ u400) ∗ ((s.sp + 408#64) ↦₈ u408) ∗ ((s.sp
       + 352#64) ↦₆₄ w3) ∗ ((s.sp + 360#64) ↦₈ b31) ∗ ((s.sp + 976#64) ↦₃₂ w0) ∗ ((s.sp + 980#64) ↦₈
       b4) ∗ ((s.sp + 981#64) ↦₈ b5) ∗ remoteGroupD (s.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10
       db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 dw3 db31 ∗ ((s.sp + 1280#64) ↦ₛ
       x.st.localIdentity.publicKey.bytes.toList) ∗ protocolAddressAt A x.loc x.locA ∗
       protocolAddressAt A x.rem x.remA ∗ stackAt s.sp isSameAccountDistinctStack)
      (fun sf P_f =>
        sf.sp = s.sp ∧ sf.spAligned = true ∧ (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧ (sf.readReg64 .x1).setWidth 32 =
        0#32 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.sp + 320#64 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64
        .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = x.locA
        ∧ sf.readReg64 .x29 = s.sp + 1408#64 ∧ (P_f ⊢ ((s.sp + 48#64) ↦₆₄ x.remA) ∗ ((s.sp + 400#64)
        ↦₈ b6) ∗ ((s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗ ((s.sp + 352#64) ↦₆₄
        w3) ∗ ((s.sp + 360#64) ↦₈ b31) ∗ ((s.sp + 976#64) ↦₃₂ w0) ∗ ((s.sp + 980#64) ↦₈ b4) ∗ ((s.sp
        + 981#64) ↦₈ b5) ∗ ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗ ((s.sp + 1280#64) ↦ₛ
        x.st.localIdentity.publicKey.bytes.toList) ∗ protocolAddressAt A x.loc x.locA ∗
        protocolAddressAt A x.rem x.remA ∗ stackAt s.sp isSameAccountDistinctStack)) := by
  dsimp only
  have hT := trapsOnly_trTrap_kit b C ctl abs
  rw [← hT.fnAddr] at h_pc ⊢
  exact SepWP_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_remote_some_wp_pq_distinct_trap
      x remIk s w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      w3 b31 u400 u408 dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19
      db20 db21 db22 dw3 db31 h_pc h_run h_sp_align hx8 hx9 hx10 hx11 hx20 hx25 hx29 hrem_eq hdiff)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_step5_some_reaches_pq_distinct {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec
  64}
    {abs : String → Option (State → State)} (x : TryDecryptGhost) (remIk : IdentityKey) (F :
    SepProp) (s0 s4 : State) (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18
    b19 b20 b21 b22 : BitVec 8) (w3 : BitVec 64) (b31 : BitVec 8) (h_pc : s4.pc =
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 384#64) (h_run : s4.status =
    .Running) (h_sp : s4.sp = s0.sp - 1504#64) (h_sp_align : s4.spAligned = true) (htr : s4.trace =
    s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0) (hx8 : s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13) (hx9 : s4.readReg64 .x9
    = pack64 b14 b15 b16 b17 b18 b19 b20 b21) (hx10 : s4.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s4.readReg64 .x11 = 1#64) (hx19 : s4.readReg64 .x19 = x.ret) (hx20 : s4.readReg64 .x20 =
    (s0.sp - 1504#64) + 320#64) (hx21 : s4.readReg64 .x21 = x.ss) (hx22 : s4.readReg64 .x22 =
    x.msgA) (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64) (hx24 : (s4.readReg64
    .x24).setWidth 8 = msgTypeByte x.msgType) (hx25 : s4.readReg64 .x25 = x.locA) (hx29 :
    s4.readReg64 .x29 = s0.sp - 96#64) (hrem_eq : ∀ a : BitVec 64, (a ↦ₛ
    remIk.publicKey.bytes.toList) = remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
    b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk ∨ DistinctSid uuidTryParse x.loc.name.bytes
    x.rem.name.bytes) (hm : s4.mem ⊨
      ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗ memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗ ((s0.sp -
      1504#64 + 352#64) ↦₆₄ w3) ∗ ((s0.sp - 1504#64 + 360#64) ↦₈ b31) ∗ ((s0.sp - 1504#64 + 976#64)
      ↦₃₂ w0) ∗ ((s0.sp - 1504#64 + 980#64) ↦₈ b4) ∗ ((s0.sp - 1504#64 + 981#64) ↦₈ b5) ∗ memRegion
      ((s0.sp - 1504#64) + 56#64) 296 ∗ memRegion ((s0.sp - 1504#64) + 361#64) 39 ∗ memRegion
      ((s0.sp - 1504#64) + 434#64) 542 ∗ memRegion ((s0.sp - 1504#64) + 982#64) 298 ∗ ((s0.sp -
      1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗ memRegion ((s0.sp -
      1504#64) + 1312#64) 96 ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let entry := (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAt b C ctl abs) (entry + 472#64) s4
      (fun s5 =>
        s5.sp = sp ∧ s5.spAligned = true ∧ (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧ (s5.readReg64 .x1).setWidth 32 =
        0#32 ∧ s5.readReg64 .x19 = x.ret ∧ s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 =
        x.ss ∧ s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧ (s5.readReg64
        .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧ s5.readReg64 .x29 =
        s0.sp - 96#64 ∧ (s5.mem ⊨
          ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 1352 ∗ protocolAddressAt A x.loc x.locA
          ∗ protocolAddressAt A x.rem x.remA ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only
  have hT := trapsOnly_trTrap_kit b C ctl abs
  rw [← hT.fnAddr] at h_pc ⊢
  exact Arm64.reaches_pc.of_trapsOnly hT
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_step5_some_reaches_pq_distinct_trap
      x remIk F s0 s4 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
      w3 b31 h_pc h_run h_sp h_sp_align htr hx8 hx9 hx10 hx11 hx19 hx20 hx21 hx22 hx23 hx24 hx25
      hx29 hrem_eq hdiff hm)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_step45_reaches_pq_distinct {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec
  64}
    {abs : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img) (x :
    TryDecryptGhost) (F : SepProp) (s0 s3 : State) (h_pc : s3.pc = (tripleRatchetProgAt img.base C
    ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 160#64) (h_run : s3.status = .Running) (h_sp : s3.sp
    = s0.sp - 1504#64) (h_sp_align : s3.spAligned = true) (htr : s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0) (hx19 :
    s3.readReg64 .x19 = x.ret) (hx20 : s3.readReg64 .x20 = (s0.sp - 1504#64) + 320#64) (hx21 :
    s3.readReg64 .x21 = x.ss) (hx22 : s3.readReg64 .x22 = x.msgA) (hx23 : s3.readReg64 .x23 = (s0.sp
    - 1504#64) + 1280#64) (hx24 : (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType) (hx25 :
    s3.readReg64 .x25 = x.locA) (hx29 : s3.readReg64 .x29 = s0.sp - 96#64) (hnot_self :
    x.st.remoteIdentity ≠ some x.st.localIdentity ∨ DistinctSid uuidTryParse x.loc.name.bytes
    x.rem.name.bytes)
    (hm : s3.mem ⊨
      remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗ memRegion ((s0.sp -
      1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗ ((s0.sp - 1504#64 +
      1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗ memRegion ((s0.sp - 1504#64) +
      1312#64) 96 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗ logOff img ∗ protocolAddressAt A x.loc
      x.locA ∗ protocolAddressAt A x.rem x.remA ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F)
      :
    let entry := (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    let sp := s0.sp - 1504#64
    reaches_pc (tripleRatchetProgAt img.base C ctl abs) (entry + 472#64)
      s3
      (fun s5 =>
        s5.sp = sp ∧ s5.spAligned = true ∧ (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧ (s5.readReg64 .x1).setWidth 32 =
        0#32 ∧ s5.readReg64 .x19 = x.ret ∧ s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 =
        x.ss ∧ s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧ (s5.readReg64
        .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧ s5.readReg64 .x29 =
        s0.sp - 96#64 ∧ (s5.mem ⊨
          ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 1352 ∗ logOff img ∗ protocolAddressAt A
          x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗ stackAt sp tryDecryptSubStack ∗ F)) :=
          by
  dsimp only
  have hT := trapsOnly_trTrap_kit img.base C ctl abs
  rw [← hT.fnAddr] at h_pc ⊢
  exact Arm64.reaches_pc.of_trapsOnly hT
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_step45_reaches_pq_distinct_trap
      himg x F s0 s3 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29
      hnot_self hm)

private def _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptSpecPqP (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse :
  UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidParse S img with
    pre := fun x s =>
      ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗ ⌜x.st.pqRatchetState = [] ∧ s.readReg64 .x0 =
      x.ret ∧ s.readReg64 .x1 = x.ss ∧ s.readReg64 .x2 = x.remA ∧ s.readReg64 .x3 = x.locA ∧
      s.readReg64 .x4 = x.msgA ∧ (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
      (x.st.remoteIdentity ≠ some x.st.localIdentity ∨ DistinctSid uuidParse x.loc.name.bytes
      x.rem.name.bytes) ∧ SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤
      s.sp.toNat⌝ ∗ sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗ memRegion x.ret 48
      ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗
      A.pool }

private theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tapeAfter_zero_sa (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    CryptoVerification.SignalSession.Coins.coinsAt ctl cur rest ⊢ CryptoVerification.SignalSession.Coins.coinsAfter ctl cur rest 0 := by
  unfold CryptoVerification.SignalSession.Coins.coinsAt CryptoVerification.SignalSession.Coins.tapeAt2 CryptoVerification.SignalSession.Coins.coinsAfter CryptoVerification.SignalSession.Coins.tapeAfter2
  have hcur : cur + BitVec.ofNat 64 0 = cur := by bv_omega
  have hlen : rest.length - 0 = rest.length := Nat.sub_zero _
  rw [hcur, hlen]
  exact Entails.pure_left (fun _ => Entails.refl _)

private theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_ok_pq_P_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage
    img) (hlocal : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.LocalIdentityKeyOk_trap img C A abs)
    (hremote : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.RemoteIdentityKeyOk_trap img C A abs)
    (x : TryDecryptGhost) (R : SepProp) (s0 : State) (h_pc : s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img)
    (h_run : s0.status = .Running) (h_sp_align : s0.spAligned = true) (hpre : s0.mem ⊨
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptSpecPqP C A ctl uuidTryParse S img).pre x s0 ∗ R) : reaches_pc (trTrapProgAt
    img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC img) s0
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1State A ctl img x R s0) := by
  dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptSpecPqP] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrozen0, hsym0⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hx1, hx2, hx3, hx4, hx5, hnot_self, _, _, _⟩, hm0⟩
  unfold sessionStateAt at hm0
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm0
  rcases hm0 with ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, hm0⟩
  have hm_s1 : s0.mem ⊨
      stackAt s0.sp rootStack ∗ vecGhostAt A x.G.localIk x.ss ∗ logOff img ∗ (vecGhostAt A
      x.G.remoteIk (x.ss + 0x18#64) ∗ vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr
      (keyToBytes32 x.st.rootKey) ∗ vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap
      x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗ vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A
         (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗ optSenderChainAt A (x.ss +
         0x90#64) x.G.sender x.st.senderChain ∗ optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
         optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗ ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion)
         ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗ ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
         memRegion x.ret 48 ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R) := by
    convert hm0 using 1; sep_ac_rfl
  have hcall_inv : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab := ⟨hfrozen0, hsym0⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr_trap (C := C) (abs := abs) himg
  have h_pc' : s0.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName :=
    h_pc.trans hentry
  have h_segS1 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC img = (trTrapProgAt img.base C abs).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 472#64 := by
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC
    rw [hentry]
  rw [h_segS1]
  refine SegA.reaches_pc_seq_callInv hcall_inv
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step1_reaches_trap hlocal x _ s0 h_pc' h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc hm_s1)
    ?_
  intro s1 hpc1 hrun1 ⟨hsp1, halign1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
    hx29_1, hm1⟩ hinv1
  have hm_s2 : s1.mem ⊨
      localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗ memRegion ((s0.sp -
      1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗ (vecGhostAt A x.G.localIk
      x.ss ∗ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion (s0.sp - 1504#64) 48 ∗ ((s0.sp -
      1504#64 + 48#64) ↦₆₄ x.remA) ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗ (vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr
      (keyToBytes32 x.st.rootKey) ∗ vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap
      x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗ vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A
          (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗ optSenderChainAt A (x.ss +
          0x90#64) x.G.sender x.st.senderChain ∗ optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
          optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗ ((x.ss + 0x148#64) ↦₃₂
          x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗ ((x.ss + 0x150#64)
          ↦ₛ x.G.regIds) ∗ logOff img ∗ memRegion x.ret 48 ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base
          x.cur x.rest ∗ A.pool ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  refine SegA.reaches_pc_seq_callInv hinv1
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step2_reaches_trap x _ s0 s1 hpc1 hrun1 hsp1 halign1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1
    hx24_1 hx25_1 hx29_1 hm_s2) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2,
    hx24_2, hx25_2, hx29_2, hm2⟩ hinv2
  have hm_s3 : s2.mem ⊨
      vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      logOff img ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ (memRegion ((s0.sp - 1504#64) +
      56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗ ((s0.sp - 1504#64 + 1280#64) ↦ₛ
      x.st.localIdentity.publicKey.bytes.toList) ∗ memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      vecGhostAt A x.G.localIk x.ss ∗ memRegion (s0.sp - 1504#64) 48 ∗ ((s0.sp - 1504#64 + 48#64)
      ↦₆₄ x.remA) ∗ tryDecryptSavedRegs s0.sp s0 ∗ (vecU8At A (x.ss + 0x30#64) x.G.root.cap
      x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗ vecAt A 104 8 (chainAt A) (x.ss + 0x48#64)
      x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗ vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A
          (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗ optSenderChainAt A (x.ss +
          0x90#64) x.G.sender x.st.senderChain ∗ optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
          optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗ ((x.ss + 0x148#64) ↦₃₂
          x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗ ((x.ss + 0x150#64)
          ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt
          A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool
          ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  refine SegA.reaches_pc_seq_callInv hinv2
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step3_reaches_trap hremote x _ s0 s2 hpc2 hrun2 hsp2 halign2 htr2 hx0_2 hx8_2 hx19_2 hx20_2
    hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx29_2 hdeser_rem hm_s3) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3,
    hx29_3, hm3⟩ hinv3
  have hm_s45 : s3.mem ⊨
      remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗ memRegion ((s0.sp -
      1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗ ((s0.sp - 1504#64 +
      1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗ memRegion ((s0.sp - 1504#64) +
      1312#64) 96 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗ logOff img ∗ protocolAddressAt A x.loc
      x.locA ∗ protocolAddressAt A x.rem x.remA ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (vecGhostAt A x.G.localIk x.ss ∗ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion (s0.sp
      - 1504#64) 48 ∗ tryDecryptSavedRegs s0.sp s0 ∗ vecU8At A (x.ss + 0x30#64) x.G.root.cap
      x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗ vecAt A 104 8 (chainAt A) (x.ss + 0x48#64)
      x.G.chainsCap x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗ vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A
         (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗ optSenderChainAt A (x.ss +
         0x90#64) x.G.sender x.st.senderChain ∗ optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
         optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗ ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion)
         ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗ ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
         memRegion x.ret 48 ∗ signalMessageAt A x.msgG x.msgA x.msg ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
         A.pool ∗ R) := by
    convert hm3 using 1; sep_ac_rfl
  refine reaches_pc_mono
    (SegA.reaches_pc_callInv hinv3
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_step45_reaches_pq_distinct_trap himg x _ s0 s3 hpc3 hrun3 hsp3 halign3 htr3 hx19_3 hx20_3
      hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx29_3 hnot_self hm_s45)) ?_
  intro s5 hpc5 hrun5 ⟨⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5,
    hx25_5, hx29_5, hm5⟩, hfrozen5, hsym5⟩
  rw [← h_segS1] at hpc5
  refine ⟨hpc5, ⟨hrun5, hsp5, h_sp_align, halign5, hx29_5, htr5.1, hfrozen5, hsym5, htr5.2⟩, hx19_5, hx20_5,
    hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx1_5, ?_⟩
  unfold sessionStateAt CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, ?_⟩
  have hm5_tape : s5.mem ⊨
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ (((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗ memRegion (s0.sp - 1504#64
      + 56#64) 1352 ∗ logOff img ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ vecGhostAt A
      x.G.localIk x.ss ∗ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion (s0.sp - 1504#64) 48
      ∗ tryDecryptSavedRegs s0.sp s0 ∗ vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr
      (keyToBytes32 x.st.rootKey) ∗ vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap
      x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗ vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A
         (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗ optSenderChainAt A (x.ss +
         0x90#64) x.G.sender x.st.senderChain ∗ optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
         optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗ ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion)
         ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗ ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
         memRegion x.ret 48 ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗ A.pool ∗ R) := by
    convert hm5 using 1; sep_ac_rfl
  have hm5_after := Arm64.Satisfies.mono (sepConj_mono_left (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tapeAfter_zero_sa img.base x.cur x.rest))
    hm5_tape
  convert hm5_after using 1; sep_ac_rfl

private theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_ok_pq_P {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage
    img) (hlocal : LocalIdentityKeyOk img C A ctl abs) (hremote : RemoteIdentityKeyOk img C A ctl
    abs) (x : TryDecryptGhost) (R : SepProp) (s0 : State) (h_pc : s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img)
    (h_run : s0.status = .Running) (h_sp_align : s0.spAligned = true) (hpre : s0.mem ⊨
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptSpecPqP C A ctl uuidTryParse S img).pre x s0 ∗ R) : reaches_pc (tripleRatchetProgAt
    img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC img) s0
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1State A ctl img x R s0) := by
  dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptSpecPqP] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrozen0, hsym0⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hx1, hx2, hx3, hx4, hx5, hnot_self, _, _, _⟩, hm0⟩
  unfold sessionStateAt at hm0
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm0
  rcases hm0 with ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, hm0⟩
  have hm_s1 : s0.mem ⊨
      stackAt s0.sp rootStack ∗ vecGhostAt A x.G.localIk x.ss ∗ logOff img ∗ (vecGhostAt A
      x.G.remoteIk (x.ss + 0x18#64) ∗ vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr
      (keyToBytes32 x.st.rootKey) ∗ vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap
      x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗ vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A
         (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗ optSenderChainAt A (x.ss +
         0x90#64) x.G.sender x.st.senderChain ∗ optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
         optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗ ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion)
         ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗ ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
         memRegion x.ret 48 ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool ∗ R) := by
    convert hm0 using 1; sep_ac_rfl
  have hcall_inv : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab := ⟨hfrozen0, hsym0⟩
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.tryDecryptEntry_eq_fnAddr (C := C) (ctl := ctl) (abs := abs) himg
  have h_pc' : s0.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName :=
    h_pc.trans hentry
  have h_segS1 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC img = (tripleRatchetProgAt img.base C ctl abs).fnAddr
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 472#64 := by
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC
    rw [hentry]
  rw [h_segS1]
  refine SegA.reaches_pc_seq_callInv hcall_inv
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step1_reaches hlocal x _ s0 h_pc' h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc hm_s1)
    ?_
  intro s1 hpc1 hrun1 ⟨hsp1, halign1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
    hx29_1, hm1⟩ hinv1
  have hm_s2 : s1.mem ⊨
      localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗ memRegion ((s0.sp -
      1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗ (vecGhostAt A x.G.localIk
      x.ss ∗ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion (s0.sp - 1504#64) 48 ∗ ((s0.sp -
      1504#64 + 48#64) ↦₆₄ x.remA) ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗ (vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr
      (keyToBytes32 x.st.rootKey) ∗ vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap
      x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗ vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A
          (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗ optSenderChainAt A (x.ss +
          0x90#64) x.G.sender x.st.senderChain ∗ optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
          optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗ ((x.ss + 0x148#64) ↦₃₂
          x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗ ((x.ss + 0x150#64)
          ↦ₛ x.G.regIds) ∗ logOff img ∗ memRegion x.ret 48 ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base
          x.cur x.rest ∗ A.pool ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  refine SegA.reaches_pc_seq_callInv hinv1
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step2_reaches x _ s0 s1 hpc1 hrun1 hsp1 halign1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1
    hx24_1 hx25_1 hx29_1 hm_s2) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2,
    hx24_2, hx25_2, hx29_2, hm2⟩ hinv2
  have hm_s3 : s2.mem ⊨
      vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      logOff img ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ (memRegion ((s0.sp - 1504#64) +
      56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗ ((s0.sp - 1504#64 + 1280#64) ↦ₛ
      x.st.localIdentity.publicKey.bytes.toList) ∗ memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      vecGhostAt A x.G.localIk x.ss ∗ memRegion (s0.sp - 1504#64) 48 ∗ ((s0.sp - 1504#64 + 48#64)
      ↦₆₄ x.remA) ∗ tryDecryptSavedRegs s0.sp s0 ∗ (vecU8At A (x.ss + 0x30#64) x.G.root.cap
      x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗ vecAt A 104 8 (chainAt A) (x.ss + 0x48#64)
      x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗ vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A
          (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗ optSenderChainAt A (x.ss +
          0x90#64) x.G.sender x.st.senderChain ∗ optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
          optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗ ((x.ss + 0x148#64) ↦₃₂
          x.st.sessionVersion) ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗ ((x.ss + 0x150#64)
          ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt
          A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ A.pool
          ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  refine SegA.reaches_pc_seq_callInv hinv2
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s0_step3_reaches hremote x _ s0 s2 hpc2 hrun2 hsp2 halign2 htr2 hx0_2 hx8_2 hx19_2 hx20_2
    hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx29_2 hdeser_rem hm_s3) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3,
    hx29_3, hm3⟩ hinv3
  have hm_s45 : s3.mem ⊨
      remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗ memRegion ((s0.sp -
      1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗ ((s0.sp - 1504#64 +
      1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗ memRegion ((s0.sp - 1504#64) +
      1312#64) 96 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗ logOff img ∗ protocolAddressAt A x.loc
      x.locA ∗ protocolAddressAt A x.rem x.remA ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
      (vecGhostAt A x.G.localIk x.ss ∗ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion (s0.sp
      - 1504#64) 48 ∗ tryDecryptSavedRegs s0.sp s0 ∗ vecU8At A (x.ss + 0x30#64) x.G.root.cap
      x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗ vecAt A 104 8 (chainAt A) (x.ss + 0x48#64)
      x.G.chainsCap x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗ vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A
         (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗ optSenderChainAt A (x.ss +
         0x90#64) x.G.sender x.st.senderChain ∗ optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
         optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗ ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion)
         ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗ ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
         memRegion x.ret 48 ∗ signalMessageAt A x.msgG x.msgA x.msg ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
         A.pool ∗ R) := by
    convert hm3 using 1; sep_ac_rfl
  refine reaches_pc_mono
    (SegA.reaches_pc_callInv hinv3
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_step45_reaches_pq_distinct himg x _ s0 s3 hpc3 hrun3 hsp3 halign3 htr3 hx19_3 hx20_3
      hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx29_3 hnot_self hm_s45)) ?_
  intro s5 hpc5 hrun5 ⟨⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5,
    hx25_5, hx29_5, hm5⟩, hfrozen5, hsym5⟩
  rw [← h_segS1] at hpc5
  refine ⟨hpc5, ⟨hrun5, hsp5, h_sp_align, halign5, hx29_5, htr5.1, hfrozen5, hsym5, htr5.2⟩, hx19_5, hx20_5,
    hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx1_5, ?_⟩
  unfold sessionStateAt CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, ?_⟩
  have hm5_tape : s5.mem ⊨
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ (((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗ memRegion (s0.sp - 1504#64
      + 56#64) 1352 ∗ logOff img ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ vecGhostAt A
      x.G.localIk x.ss ∗ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion (s0.sp - 1504#64) 48
      ∗ tryDecryptSavedRegs s0.sp s0 ∗ vecU8At A (x.ss + 0x30#64) x.G.root.cap x.G.root.ptr
      (keyToBytes32 x.st.rootKey) ∗ vecAt A 104 8 (chainAt A) (x.ss + 0x48#64) x.G.chainsCap
      x.G.chainsPtr
         (x.G.chains.zip x.st.receiverChains) ∗ vecGhostAt A x.G.alice (x.ss + 0x60#64) ∗ vecU8At A
         (x.ss + 0x78#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗ optSenderChainAt A (x.ss +
         0x90#64) x.G.sender x.st.senderChain ∗ optTailVecAt A 48 (x.ss + 0xf8#64) x.G.pending ∗
         optTailVecAt A 32 (x.ss + 0x128#64) x.G.kyber ∗ ((x.ss + 0x148#64) ↦₃₂ x.st.sessionVersion)
         ∗ ((x.ss + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗ ((x.ss + 0x150#64) ↦ₛ x.G.regIds) ∗
         memRegion x.ret 48 ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗ A.pool ∗ R) := by
    convert hm5 using 1; sep_ac_rfl
  have hm5_after := Arm64.Satisfies.mono (sepConj_mono_left (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tapeAfter_zero_sa img.base x.cur x.rest))
    hm5_tape
  convert hm5_after using 1; sep_ac_rfl

private theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.seedsLen32_of_pre_pq_P {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost} {R : SepProp} {s0 : State} (hpre :
    s0.mem ⊨ (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptSpecPqP C A ctl uuidTryParse S img).pre x s0 ∗ R) : x.st.pqRatchetState = []
    ∧ SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat := by
  simp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptSpecPqP] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact ⟨hpre.1.1, hpre.1.2.2.2.2.2.2.2.2⟩

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptPq_ok_P_trap {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} {img : Obj.Image} (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) : subroutine_ok (trTrapProgAt img.base C abs) (img.base + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      ((CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpecP C A ctl uuidTryParse S img).inImage img) := by
  have hrecv := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.DecryptPqTrapBridge.spqrRecvOkQ_empty_pq_trap hH hempty himg
  have hcallees := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.tryDecryptPqCallees_trap C A S abs img hH himg
  have hs1 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_trap (img := img) (C := C) (A := A) (ctl := ctl) (S := S) (abs := abs)
  have hs2 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s2_ok_trap (img := img) (C := C) (A := A) (ctl := ctl) (abs := abs)
  have hs3 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.s3_ok_trap img C A ctl S abs
  have hs4 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s4_ok_trap img C A ctl S abs
  have hs5 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s5_ok_trap (Q := (· = [])) img C A ctl S abs
  have hs6 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegC.s6_ok_trap img C A ctl abs
  have hs7 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s7_ok_trap img C A ctl S abs
  have hs8 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s8_ok_trap img C A ctl S abs
  have hs9 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.s9_ok_trap img C A ctl S abs
  have herr := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.errTail_ok_trap (img := img) (C := C) (A := A) (ctl := ctl) (S := S) (abs
    := abs)
  have hentry : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img = img.base + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.entryOf_tryDecryptPq_eq
    himg C ctl abs
  rw [← hentry]
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  refine reaches_outcome.mono_outcome
    (spec₁ := CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img)
    (x := x) (R₁ := R) ?_ (fun _ hout => hout)
  obtain ⟨hpq, hseeds, hchains, hstk⟩ := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.seedsLen32_of_pre_pq_P (ctl := ctl) hpre
  obtain ⟨s1, hsteps1, ⟨_, _, hs1_state⟩ | ⟨_, ⟨⟩⟩⟩ := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.s0_ok_pq_P_trap himg hcallees.localIk hcallees.remoteIk x R s0
    hpc hrun hsp hpre hL
  refine LibsignalSession.reaches_outcome_steps hsteps1 ?_
  have hL1 := hsteps1.codeLoaded hL
  have hs1_step := hs1 himg hcallees.trFrom x R s0 s1 hs1_state hL1
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk trRes st1 =>
    rw [htr] at hs1_step
    cases trRes with
    | error e => exact hs1_step
    | ok tr0 =>
      rcases hs1_step with ⟨s2, hsteps2, trG2, hs2_state⟩
      refine LibsignalSession.reaches_outcome_steps hsteps2 ?_
      have hL2 := hsteps2.codeLoaded hL1
      have hs2_step := hs2 himg hcallees.findReceiverChainKey x trG2 tr0 st1 R s0 s2 hs2_state hL2
      cases hf : tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error e =>
        rw [hf] at hs2_step
        obtain ⟨s2', hsteps2', ⟨_, _, herr_st⟩ | ⟨_, ⟨⟩⟩⟩ := hs2_step hL2
        have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
            (coinsOf x.rest)) tr0.ratchet = (.error e, tr0.ratchet) :=
            ensureReceiverChain_of_find_error hf
        have hmodel := model_of_ensureReceiverChain_error (S := S) htr herc
        have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
        have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
        have hne : e ≠ .panic := by
          have he := findReceiverChainKey_error_eq hf
          subst he; decide
        have hdraws : decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 :=
          decryptDraws_of_find_error x.rest htr hf
        rw [← hdraws] at herr_st
        exact LibsignalSession.reaches_outcome_steps hsteps2'
          (herr himg hH hcallees.dropChain x trG2 tr0 st1 e R s0 s2' hne hm1 hm2 herr_st)
      | ok optCk =>
        cases optCk with
        | some ck =>
          rw [hf] at hs2_step
          obtain ⟨s4, hsteps4, ⟨_, _, hs4_state⟩ | ⟨_, ⟨⟩⟩⟩ := hs2_step hL2
          refine LibsignalSession.reaches_outcome_steps hsteps4 ?_
          have hL4 := hsteps4.codeLoaded hL2
          have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet = (.ok ck, tr0.ratchet) :=
              ensureReceiverChain_of_find_some hf
          have hdraws : 0 = decryptDraws C x.st x.msg.senderRatchetKey x.rest :=
            (decryptDraws_of_find_some x.rest htr hf).symm
          exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.DecryptPqTrapBridge.reaches_outcome_of_s4_trap himg hH hrecv hcallees hs4 hs5 hs6 hs7 hs8 hs9 herr
            hseeds hpq htr herc hdraws hs4_state hL4
        | none =>
          rw [hf] at hs2_step
          obtain ⟨s3, hsteps3, ⟨_, _, hs3_state⟩ | ⟨_, ⟨⟩⟩⟩ := hs2_step hL2
          refine LibsignalSession.reaches_outcome_steps hsteps3 ?_
          have hL3 := hsteps3.codeLoaded hL2
          have htr_chains : tr0.ratchet.receiverChains.length < 2 ^ 32 := by
            rw [(fromSessionState_ok_inv htr).2.1]; exact hchains
          have hs3_step := hs3 himg hH hcallees.createChain hcallees.derivePk
            hcallees.pkSer hcallees.chainKeyToPb hcallees.growOne hcallees.dropChain
            x trG2 tr0 st1 R s0 s3 htr hf htr_chains hstk hs3_state hL3
          dsimp only at hs3_step
          cases hdh : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf
            x.rest)) tr0.ratchet with
          | mk dhRes r1 =>
            rw [hdh] at hs3_step
            cases dhRes with
            | error e =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.error e, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              have hmodel := model_of_ensureReceiverChain_error (S := S) htr herc
              have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : e ≠ .panic := dhRatchetStep_error_ne_panic hdh
              rcases hs3_step with ⟨s3', hsteps3', ⟨trG3, r1', herr_st⟩ | ⟨hpan, hq⟩⟩
              · exact LibsignalSession.reaches_outcome_steps hsteps3'
                  (herr himg hH hcallees.dropChain x trG3 { tr0 with ratchet := r1' } st1 e
                    R s0 s3' hne hm1 hm2 herr_st)
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic hsteps3' hpan hq
            | ok ck =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.ok ck, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              rcases hs3_step with ⟨s4, hsteps4, ⟨trG4, hs4_state⟩ | ⟨hpan, hq⟩⟩
              · refine LibsignalSession.reaches_outcome_steps hsteps4 ?_
                have hL4 := hsteps4.codeLoaded hL3
                exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.DecryptPqTrapBridge.reaches_outcome_of_s4_trap himg hH hrecv hcallees hs4 hs5 hs6 hs7 hs8 hs9 herr
                  hseeds hpq htr herc rfl hs4_state hL4
              · exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.reaches_outcome_of_panic hsteps4 hpan hq

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptPq_ok_P {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} {img : Obj.Image} (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) : subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      ((CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpecP C A ctl uuidTryParse S img).inImage img) :=
  subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptPq_ok_P_trap hH hempty himg)

end TryDecryptPqDistinct

attribute [local irreducible] Program.fnOff

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_ok_P_trap {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18
    c0 remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v24 v28 v2c f248 f24c prevCounter : BitVec 32) (locIdBytes remIdBytes rootKeyBytes
    aliceBaseBytes rest : List (BitVec 8)) (sg' : SenderChainGhost) (sc : SenderChain) (st :
    SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc : AddrGhost) (msgG :
    SignalMessageGhost) (msg : SignalMessage) (hnew1 : newLocIdPtr ≠ 0#64) (hnew2 : newRemIdPtr ≠
    0#64) (hnew3 : newRootKeyPtr ≠ 0#64) (hnew4 : newAliceBasePtr ≠ 0#64) (hloc_len :
    locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33) (halice_len : aliceBaseBytes.length
    = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok st.localIdentity.publicKey) (hrem_eq
    : st.remoteIdentity = some remIk) (hrem_deser : PublicKey.deserialize remIdBytes = .ok
    remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some st.localIdentity ∨ DistinctSid
    uuidTryParse loc.name.bytes rem.name.bytes) (hroot_eq : rootKeyBytes = keyToBytes32 st.rootKey)
    (hrc : st.receiverChains = []) (hpq : st.pqRatchetState = []) (hsc : st.senderChain = some sc)
    (hpend : st.pendingPreKey = false) (hver : st.sessionVersion = 4#32) (hprev : st.previousCounter
    = prevCounter) (hsc_inl : OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1
    sq2 sq3 sq4 sq5)) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc : s.pc =
    (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) (hrun :
    s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤
    s.sp.toNat) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64
    .x21 = 1#64) (hx22 : s.readReg64 .x22 = 0xffffffffffffffff#64) (hx23 : s.readReg64 .x23 =
    newAliceBasePtr) (hx24 : s.readReg64 .x24 = 33#64) (hx25 : s.readReg64 .x25 = 8#64) (hx26 :
    s.readReg64 .x26 = 0#64) (hx28 : s.readReg64 .x28 = 32#64) : SepWPp (trTrapProgAt
    img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s
      (memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
      ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp
      + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
      0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0)
      ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
      0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr)
      ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
      whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp +
      0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄
      sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄
      sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄
      sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄
      sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄
      sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
      sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64) ∗ A.live newLocIdPtr 33
      1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗
      A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live newAliceBasePtr 33 1 ∗
      (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗ optSenderChainHeap A (some sg') (some sc) ∗
      protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A
      msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗
      stackAt s.sp rootStack ∗ A.pool)
      (fun s2 P_f => ∃ G' : SessionGhost, (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
          st).1 ≠ .error .panic ∧ (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr
          newAliceBasePtr
            locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt (pqxdhTryDecryptModel C S
            uuidTryParse rem loc msg rest st).1.toBool G' ∧ (P_f ⊢ sessionStateAt A (s.sp +
            0xa90#64) G'
              (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt A (s.sp +
              0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
              protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
              signalMessageAt A msgG whisperMsgPtr msg ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base cur rest (decryptDraws C st
              msg.senderRatchetKey rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ ((s.sp +
              0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp +
              0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp +
              0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp + 0x38#64) ↦₆₄
              0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0) ∗
              ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
              0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄
              newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
              ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64)
              ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp
              + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64)
              ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄
              sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp +
              0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
              ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb'
              0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
              sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧ s2.sp = s.sp
              ∧ s2.trace = s0.trace ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab ∧ s2.readReg64
              .x19 = coroPtr ∧ s2.readReg64 .x24 = s.sp + 0x370#64 ∧ s2.readReg64 .x27 = s.readReg64
              .x27 ∧ s2.readReg64 .x29 = s.readReg64 .x29)
      (TryDecryptPanicProp C S uuidTryParse rem loc st msg rest s0) := by
  refine SepWPp.weaken_pre (sepConj_mono_left (memRegion_344_entails_spA90SlotsAt s.sp)) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun dv => ?_
  dsimp only [spA90SlotsAt]
  refine SepWPp.bind_sepWP_frame hF hsym
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.p3_seg6_v4_wp_trap img.base C abs s coroPtr 33#64 newLocIdPtr 33#64 newRemIdPtr
    newRootKeyPtr
      v08 v10 v18 0xffffffffffffffff#64 0#64 c0 (sq0.extractLsb' 0 64) (sq0.extractLsb' 64 64)
      (sq1.extractLsb' 0 64) (sq1.extractLsb' 64 64) (sq2.extractLsb' 0 64) (sq2.extractLsb' 64 64)
      (sq3.extractLsb' 0 64) (sq3.extractLsb' 64 64) (sq4.extractLsb' 0 64) (sq4.extractLsb' 64 64)
      (sq5.extractLsb' 0 64) (sq5.extractLsb' 64 64) remAddrPtr locAddrPtr whisperMsgPtr dv.w_ca0
      dv.w_ca8 dv.w_cb0 dv.w_cb8 dv.w_cc0 dv.w_cc8 dv.w_cd0 dv.w_cd8 dv.w_ce0 dv.w_ce8 dv.w_cf0
      dv.w_cf8 dv.w_d00 dv.w_d08 dv.w_d10 dv.w_d18 dv.w_d20 dv.w_d28 dv.w_d30 (dv.q0.extractLsb' 0
      64) (dv.q0.extractLsb' 64 64) (dv.q1.extractLsb' 0 64) (dv.q1.extractLsb' 64 64)
      (dv.q2.extractLsb' 0 64) (dv.q2.extractLsb' 64 64) (dv.q3.extractLsb' 0 64) (dv.q3.extractLsb'
      64 64) (dv.q4.extractLsb' 0 64) (dv.q4.extractLsb' 64 64) (dv.q5.extractLsb' 0 64)
      (dv.q5.extractLsb' 64 64) dv.w_d98 dv.w_da0 dv.w_da8 dv.w_db8 dv.w_dc8 dv.w_dd0 dv.w_dd8 v24
      v28 v2c f248 f24c prevCounter dv.w_db0 dv.w_db4 dv.w_dc0 dv.w_de0 dv.w_de8 dv.w_dec dv.w_df0
      dv.w_df4 hpc hrun hsp_align hx19)
    (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1,
      hx19_1, hx24_1, hx27_1, hx29_1, hlr1⟩ => ?_
  have htr10 : s1.trace = s0.trace := htr1.trans htr
  have hsp_alm1 : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  rw [hx21, hx22, hx23, hx24, hx25, hx26, hx28]
  have hfold := clonedSlots_sp_a90_entails_sessionStateAt (A := A)
    s.sp newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr c0 sq0 sq1 sq2 sq3 sq4 sq5 locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes sg' sc prevCounter f248 f24c v18 0xffffffffffffffff#64
    v10 v08 0xffffffffffffffff#64 v2c ((s.readReg64 .x20).truncate 32) v28 v24 st remIk hnew1 hnew2
    hnew3 hnew4 hloc_len hrem_len halice_len hloc_deser hrem_eq hrem_deser hroot_eq hrc hpq hsc
    hpend hver hprev hsc_inl
  refine SepWPp.weaken_pre
    (Entails.trans
      (Q := (((s.sp + 0xa90#64) ↦₆₄ 33#64) ∗ ((s.sp + 0xa98#64) ↦₆₄ newLocIdPtr) ∗ ((s.sp +
      0xaa0#64) ↦₆₄ 33#64) ∗
             ((s.sp + 0xaa8#64) ↦₆₄ 33#64) ∗ ((s.sp + 0xab0#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp +
             0xab8#64) ↦₆₄ 33#64) ∗ ((s.sp + 0xac0#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xac8#64) ↦₆₄
             newRootKeyPtr) ∗ ((s.sp + 0xad0#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xad8#64) ↦₆₄ 0#64) ∗ ((s.sp
             + 0xae0#64) ↦₆₄ 8#64) ∗ ((s.sp + 0xae8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0xaf0#64) ↦₆₄ 33#64) ∗
             ((s.sp + 0xaf8#64) ↦₆₄ newAliceBasePtr) ∗ ((s.sp + 0xb00#64) ↦₆₄ 33#64) ∗ ((s.sp +
             0xb08#64) ↦₆₄ 0#64) ∗ ((s.sp + 0xb10#64) ↦₆₄ 1#64) ∗ ((s.sp + 0xb18#64) ↦₆₄ 0#64) ∗
             ((s.sp + 0xb20#64) ↦₆₄ c0) ∗ ((s.sp + 0xb28#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp +
             0xb30#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0xb38#64) ↦₆₄ sq1.extractLsb' 0 64) ∗
             ((s.sp + 0xb40#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0xb48#64) ↦₆₄ sq2.extractLsb'
             0 64) ∗ ((s.sp + 0xb50#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0xb58#64) ↦₆₄
             sq3.extractLsb' 0 64) ∗ ((s.sp + 0xb60#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp +
             0xb68#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 0xb70#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
             ((s.sp + 0xb78#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp + 0xb80#64) ↦₆₄ sq5.extractLsb'
             64 64) ∗ ((s.sp + 0xb88#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0xb90#64) ↦₆₄ v18) ∗
             ((s.sp + 0xb98#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0xba0#64) ↦₃₂ v2c) ∗ ((s.sp +
             0xba4#64) ↦₃₂ (s.readReg64 .x20).truncate 32) ∗ ((s.sp + 0xba8#64) ↦₆₄ v10) ∗ ((s.sp +
             0xbb0#64) ↦₃₂ v28) ∗ memRegion (s.sp + 0xbb4#64) 4 ∗ ((s.sp + 0xbb8#64) ↦₆₄
             0xffffffffffffffff#64) ∗ ((s.sp + 0xbc0#64) ↦₆₄ v08) ∗ ((s.sp + 0xbc8#64) ↦₆₄
             0xffffffffffffffff#64) ∗ ((s.sp + 0xbd0#64) ↦₃₂ v24) ∗ memRegion (s.sp + 0xbd4#64) 4 ∗
             ((s.sp + 0xbd8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xbdc#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0xbe0#64)
             ↦₃₂ f248) ∗ ((s.sp + 0xbe4#64) ↦₃₂ f24c) ∗ A.live newLocIdPtr 33 1 ∗ (newLocIdPtr ↦ₛ
             locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗ A.live
             newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live newAliceBasePtr 33 1 ∗
             (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗ optSenderChainHeap A (some sg') (some sc)) ∗
             (protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
             signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base
             cur rest ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗
             ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗
             ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗
             ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp + 0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp +
             0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
             ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp +
             0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32)
             ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp +
             0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr)
             ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp +
             0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗
             ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb'
             0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄
             sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp +
             0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
             ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb'
             64 64)))
      (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hfold)) ?_
  have hseeds : SeedsLen32 st := by
    intro c hc; rw [hrc] at hc; cases hc
  have hrc_len : st.receiverChains.length < 2 ^ 32 := by simp [hrc]
  have hsp_root1 : rootStack ≤ s1.sp.toNat := by rw [hsp1]; exact hsp_root
  have hx5_byte : (s1.readReg64 .x5).setWidth 8 = msgTypeByte .preKey := by
    rw [hx5_1]; rfl
  refine SepWPp.call_inImage_frame hF1 hsym1 (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptPq_ok_P_trap (ctl := 0#64) hH hempty himg)
    (x := mkClonedTryDecryptGhost s.sp newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
      locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c st remAddrPtr rem locAddrPtr loc
      whisperMsgPtr msgG msg cur rest)
    hpc1 hrun1 hsp_alm1 hlr1
    rfl ⟨hpq, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_byte, hnot_self, hseeds, hrc_len, hsp_root1⟩
    (by dsimp only [mkClonedTryDecryptGhost]; rw [hsp1]; sep_focus) (fun _ _ => rfl) ?_ ?_
  · intro sf _ R hm
    dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpecP, CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpec, mkClonedTryDecryptGhost,
      TryDecryptGhost.model] at hm
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
    rcases hm with ⟨⟨hpan_or, hpref⟩, hm⟩
    have htr_pref : s0.trace <+: sf.trace := htr10 ▸ hpref
    have hpan_or0 :
        (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 = .error .panic ∨ S.recvPanics
        st.pqRatchetState msg.pqRatchet ∨ allocFailedIn s0 sf := by
      rcases hpan_or with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (by unfold allocFailedIn at h3 ⊢; rwa [← htr10]))
    rw [← sepConj_assoc] at hm
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpan_or0, htr_pref⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm⟩
  · intro s2 hpc2 hrun2 hsp2 _ hcs2 hF2 hsym2
    dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpecP, CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.tryDecryptRawSpec, mkClonedTryDecryptGhost,
      TryDecryptGhost.model]
    rw [hsp1, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hnpan, htr2⟩ => ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    refine SepWPp.exists_elim fun G' => ?_
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hdec => ?_
    refine SepWPp.done hpc2 hrun2 ?_
    refine ⟨G', hnpan, hdec, Entails.of_eq (by ac_rfl),
      hsp2.trans hsp1, htr2.trans htr10, hF2, hsym2, (hcs2.1).trans hx19_1, (hcs2.2.2.2.2.2.1).trans
      hx24_1, (hcs2.2.2.2.2.2.2.2.2.1).trans hx27_1, (hcs2.2.2.2.2.2.2.2.2.2.2.1).trans hx29_1⟩

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_ok_P {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (ctl : BitVec 64) (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18
    c0 remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v24 v28 v2c f248 f24c prevCounter : BitVec 32) (locIdBytes remIdBytes rootKeyBytes
    aliceBaseBytes rest : List (BitVec 8)) (sg' : SenderChainGhost) (sc : SenderChain) (st :
    SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc : AddrGhost) (msgG :
    SignalMessageGhost) (msg : SignalMessage) (hnew1 : newLocIdPtr ≠ 0#64) (hnew2 : newRemIdPtr ≠
    0#64) (hnew3 : newRootKeyPtr ≠ 0#64) (hnew4 : newAliceBasePtr ≠ 0#64) (hloc_len :
    locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33) (halice_len : aliceBaseBytes.length
    = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok st.localIdentity.publicKey) (hrem_eq
    : st.remoteIdentity = some remIk) (hrem_deser : PublicKey.deserialize remIdBytes = .ok
    remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some st.localIdentity ∨ DistinctSid
    uuidTryParse loc.name.bytes rem.name.bytes) (hroot_eq : rootKeyBytes = keyToBytes32 st.rootKey)
    (hrc : st.receiverChains = []) (hpq : st.pqRatchetState = []) (hsc : st.senderChain = some sc)
    (hpend : st.pendingPreKey = false) (hver : st.sessionVersion = 4#32) (hprev : st.previousCounter
    = prevCounter) (hsc_inl : OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1
    sq2 sq3 sq4 sq5)) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc : s.pc =
    (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) (hrun :
    s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤
    s.sp.toNat) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64
    .x21 = 1#64) (hx22 : s.readReg64 .x22 = 0xffffffffffffffff#64) (hx23 : s.readReg64 .x23 =
    newAliceBasePtr) (hx24 : s.readReg64 .x24 = 33#64) (hx25 : s.readReg64 .x25 = 8#64) (hx26 :
    s.readReg64 .x26 = 0#64) (hx28 : s.readReg64 .x28 = 32#64) : SepWPp (tripleRatchetProgAt
    img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s
      (memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
      ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp
      + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
      0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0)
      ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
      0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr)
      ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
      whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp +
      0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄
      sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄
      sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄
      sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄
      sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄
      sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
      sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64) ∗ A.live newLocIdPtr 33
      1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗
      A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live newAliceBasePtr 33 1 ∗
      (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗ optSenderChainHeap A (some sg') (some sc) ∗
      protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A
      msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗
      stackAt s.sp rootStack ∗ A.pool)
      (fun s2 P_f => ∃ G' : SessionGhost, (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
          st).1 ≠ .error .panic ∧ (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr
          newAliceBasePtr
            locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt (pqxdhTryDecryptModel C S
            uuidTryParse rem loc msg rest st).1.toBool G' ∧ (P_f ⊢ sessionStateAt A (s.sp +
            0xa90#64) G'
              (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt A (s.sp +
              0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
              protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
              signalMessageAt A msgG whisperMsgPtr msg ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base cur rest (decryptDraws C st
              msg.senderRatchetKey rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ ((s.sp +
              0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp +
              0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp +
              0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp + 0x38#64) ↦₆₄
              0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0) ∗
              ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
              0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄
              newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
              ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64)
              ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp
              + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64)
              ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄
              sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp +
              0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
              ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb'
              0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
              sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧ s2.sp = s.sp
              ∧ s2.trace = s0.trace ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab ∧ s2.readReg64
              .x19 = coroPtr ∧ s2.readReg64 .x24 = s.sp + 0x370#64 ∧ s2.readReg64 .x27 = s.readReg64
              .x27 ∧ s2.readReg64 .x29 = s.readReg64 .x29)
      (TryDecryptPanicProp C S uuidTryParse rem loc st msg rest s0) := by
  have hT := trapsOnly_trTrap_kit img.base C ctl abs
  rw [← hT.fnAddr] at hpc ⊢
  exact SepWPp.of_trapsOnly hT
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_ok_P_trap img C S
      abs hH hempty himg s0 s coroPtr newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10
      v18 c0 remAddrPtr locAddrPtr whisperMsgPtr cur sq0 sq1 sq2 sq3 sq4 sq5 v24 v28 v2c f248 f24c
      prevCounter locIdBytes remIdBytes rootKeyBytes aliceBaseBytes rest sg' sc st remIk rem loc msgG
      msg hnew1 hnew2 hnew3 hnew4 hloc_len hrem_len halice_len hloc_deser hrem_eq hrem_deser
      hnot_self hroot_eq hrc hpq hsc hpend hver hprev hsc_inl hF hsym hpc hrun hsp_align hsp_root
      htr hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx28)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_nopanic_ok_P_trap {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18
    c0 remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v24 v28 v2c f248 f24c prevCounter : BitVec 32) (locIdBytes remIdBytes rootKeyBytes
    aliceBaseBytes rest : List (BitVec 8)) (sg' : SenderChainGhost) (sc : SenderChain) (st :
    SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc : AddrGhost) (msgG :
    SignalMessageGhost) (msg : SignalMessage) (hnpan1 : (pqxdhTryDecryptModel C S uuidTryParse rem
    loc msg rest st).1 ≠ .error .panic) (hnpan2 : ¬ S.recvPanics st.pqRatchetState msg.pqRatchet)
    (hnew1 : newLocIdPtr ≠ 0#64) (hnew2 : newRemIdPtr ≠ 0#64) (hnew3 : newRootKeyPtr ≠ 0#64) (hnew4
    : newAliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length =
    33) (halice_len : aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes =
    .ok st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) (hroot_eq :
    rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState
    = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false) (hver :
    st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hsc_inl :
    OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5)) (hF :
    img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc : s.pc = (trTrapProgAt img.base C
    abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) (hrun : s.status = .Running) (hsp_align :
    (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = 1#64) (hx22 : s.readReg64 .x22 =
    0xffffffffffffffff#64) (hx23 : s.readReg64 .x23 = newAliceBasePtr) (hx24 : s.readReg64 .x24 =
    33#64) (hx25 : s.readReg64 .x25 = 8#64) (hx26 : s.readReg64 .x26 = 0#64) (hx28 : s.readReg64
    .x28 = 32#64) : SepWPp (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s
      (memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
      ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp
      + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
      0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0)
      ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
      0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr)
      ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
      whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp +
      0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄
      sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄
      sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄
      sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄
      sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄
      sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
      sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64) ∗ A.live newLocIdPtr 33
      1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗
      A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live newAliceBasePtr 33 1 ∗
      (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗ optSenderChainHeap A (some sg') (some sc) ∗
      protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A
      msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗
      stackAt s.sp rootStack ∗ A.pool)
      (fun s2 P_f => ∃ G' : SessionGhost, (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
          st).1 ≠ .error .panic ∧ (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr
          newAliceBasePtr
            locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt (pqxdhTryDecryptModel C S
            uuidTryParse rem loc msg rest st).1.toBool G' ∧ (P_f ⊢ sessionStateAt A (s.sp +
            0xa90#64) G'
              (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt A (s.sp +
              0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
              protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
              signalMessageAt A msgG whisperMsgPtr msg ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base cur rest (decryptDraws C st
              msg.senderRatchetKey rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ ((s.sp +
              0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp +
              0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp +
              0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp + 0x38#64) ↦₆₄
              0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0) ∗
              ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
              0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄
              newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
              ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64)
              ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp
              + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64)
              ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄
              sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp +
              0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
              ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb'
              0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
              sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧ s2.sp = s.sp
              ∧ s2.trace = s0.trace ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab ∧ s2.readReg64
              .x19 = coroPtr ∧ s2.readReg64 .x24 = s.sp + 0x370#64 ∧ s2.readReg64 .x27 = s.readReg64
              .x27 ∧ s2.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := SepWPp.mono_panic (fun _ _ => tryDecryptPanicProp_imp_panicOomProp hnpan1
      hnpan2)
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_ok_P_trap img C S abs hH hempty himg s0 s coroPtr
      newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18 c0 remAddrPtr locAddrPtr
      whisperMsgPtr cur sq0 sq1 sq2 sq3 sq4 sq5 v24 v28 v2c f248 f24c prevCounter locIdBytes
      remIdBytes rootKeyBytes aliceBaseBytes rest sg' sc st remIk rem loc msgG msg hnew1 hnew2 hnew3
      hnew4 hloc_len hrem_len halice_len hloc_deser hrem_eq hrem_deser hnot_self hroot_eq hrc hpq
      hsc hpend hver hprev hsc_inl hF hsym hpc hrun hsp_align hsp_root htr hx19 hx21 hx22 hx23 hx24
      hx25 hx26 hx28)

/-- Specialisation of `stageP3_tryDecrypt_v4_ok` to `PanicOomProp s0` when the pure model does not
panic and `S.recvPanics` is false. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_nopanic_ok_P {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (ctl : BitVec 64) (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18
    c0 remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v24 v28 v2c f248 f24c prevCounter : BitVec 32) (locIdBytes remIdBytes rootKeyBytes
    aliceBaseBytes rest : List (BitVec 8)) (sg' : SenderChainGhost) (sc : SenderChain) (st :
    SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc : AddrGhost) (msgG :
    SignalMessageGhost) (msg : SignalMessage) (hnpan1 : (pqxdhTryDecryptModel C S uuidTryParse rem
    loc msg rest st).1 ≠ .error .panic) (hnpan2 : ¬ S.recvPanics st.pqRatchetState msg.pqRatchet)
    (hnew1 : newLocIdPtr ≠ 0#64) (hnew2 : newRemIdPtr ≠ 0#64) (hnew3 : newRootKeyPtr ≠ 0#64) (hnew4
    : newAliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length =
    33) (halice_len : aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes =
    .ok st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) (hroot_eq :
    rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState
    = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false) (hver :
    st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hsc_inl :
    OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5)) (hF :
    img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc : s.pc = (tripleRatchetProgAt img.base C
    ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1bac#64) (hrun : s.status = .Running) (hsp_align :
    (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = 1#64) (hx22 : s.readReg64 .x22 =
    0xffffffffffffffff#64) (hx23 : s.readReg64 .x23 = newAliceBasePtr) (hx24 : s.readReg64 .x24 =
    33#64) (hx25 : s.readReg64 .x25 = 8#64) (hx26 : s.readReg64 .x26 = 0#64) (hx28 : s.readReg64
    .x28 = 32#64) : SepWPp (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s
      (memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
      ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp
      + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
      0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0)
      ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
      0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr)
      ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
      whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp +
      0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄
      sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄
      sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄
      sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄
      sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄
      sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
      sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64) ∗ A.live newLocIdPtr 33
      1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗ (newRemIdPtr ↦ₛ remIdBytes) ∗
      A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live newAliceBasePtr 33 1 ∗
      (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗ optSenderChainHeap A (some sg') (some sc) ∗
      protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A
      msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗
      stackAt s.sp rootStack ∗ A.pool)
      (fun s2 P_f => ∃ G' : SessionGhost, (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
          st).1 ≠ .error .panic ∧ (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr
          newAliceBasePtr
            locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt (pqxdhTryDecryptModel C S
            uuidTryParse rem loc msg rest st).1.toBool G' ∧ (P_f ⊢ sessionStateAt A (s.sp +
            0xa90#64) G'
              (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt A (s.sp +
              0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
              protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
              signalMessageAt A msgG whisperMsgPtr msg ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base cur rest (decryptDraws C st
              msg.senderRatchetKey rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ ((s.sp +
              0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp +
              0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp +
              0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp + 0x38#64) ↦₆₄
              0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0) ∗
              ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp +
              0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄
              newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
              ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xd0#64)
              ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp
              + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64)
              ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄
              sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp +
              0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
              ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb'
              0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄
              sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧ s2.sp = s.sp
              ∧ s2.trace = s0.trace ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab ∧ s2.readReg64
              .x19 = coroPtr ∧ s2.readReg64 .x24 = s.sp + 0x370#64 ∧ s2.readReg64 .x27 = s.readReg64
              .x27 ∧ s2.readReg64 .x29 = s.readReg64 .x29)
      (PanicOomProp s0) := SepWPp.mono_panic (fun _ _ => tryDecryptPanicProp_imp_panicOomProp hnpan1
      hnpan2)
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_ok_P img C ctl S abs hH hempty himg s0 s coroPtr
      newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18 c0 remAddrPtr locAddrPtr
      whisperMsgPtr cur sq0 sq1 sq2 sq3 sq4 sq5 v24 v28 v2c f248 f24c prevCounter locIdBytes
      remIdBytes rootKeyBytes aliceBaseBytes rest sg' sc st remIk rem loc msgG msg hnew1 hnew2 hnew3
      hnew4 hloc_len hrem_len halice_len hloc_deser hrem_eq hrem_deser hnot_self hroot_eq hrc hpq
      hsc hpend hver hprev hsc_inl hF hsym hpc hrun hsp_align hsp_root htr hx19 hx21 hx22 hx23 hx24
      hx25 hx26 hx28)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_and_tryDecrypt_v4_ok_P_trap {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr v08 v10 v18
    remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938
    u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64) (v24 v28 v2c prevCounter f248
    f24c u_30 u_34 u_5c u_7c : BitVec 32) (sg : SenderChainGhost) (sc : SenderChain) (locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes rest : List (BitVec 8)) (st : SessionState (List (BitVec
    8))) (remIk : IdentityKey) (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg :
    SignalMessage) (hloc_nz : locIdPtr ≠ 0#64) (hrem_nz : remIdPtr ≠ 0#64) (hroot_nz : rootKeyPtr ≠
    0#64) (halice_nz : aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length = 33) (hrem_len :
    remIdBytes.length = 33) (hroot_len : rootKeyBytes.length = 32) (halice_len :
    aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) (hroot_eq :
    rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState
    = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false) (hver :
    st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hnpan1 :
    (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic) (hnpan2 : ¬
    S.recvPanics st.pqRatchetState msg.pqRatchet) (hF : img.FrozenLoaded s) (hsym : s.symtab =
    img.symtab) (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64
    == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace) (hx19 :
    s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) : SepWPp
    (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s
      (stageP3ClonePre A s.sp coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
        u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
        u978 u980 u988 prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc locIdBytes remIdBytes
        rootKeyBytes aliceBaseBytes ∗ bobCoroRestAt A coroPtr locIdPtr remIdPtr rootKeyPtr
        aliceBasePtr ∗ memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp +
        0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp +
        0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp
        + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x3a0#64) ↦₆₄
        remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A rem remAddrPtr ∗
        protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion
        (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗ memRegion (s.sp - BitVec.ofNat 64
        rootStack) (rootStack - chainCloneStack))
      (fun s2 P_f => ∃ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
          (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
          SessionGhost), newLocIdPtr ≠ 0#64 ∧ newRemIdPtr ≠ 0#64 ∧ newRootKeyPtr ≠ 0#64 ∧
          newAliceBasePtr ≠ 0#64 ∧ sg'.srk.bytes = sg.srk.bytes ∧ sg'.priv.bytes = sg.priv.bytes ∧
          OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) ∧
          (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic ∧
          (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
            locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt (pqxdhTryDecryptModel C S
            uuidTryParse rem loc msg rest st).1.toBool G' ∧ (P_f ⊢ sessionStateAt A (s.sp +
            0xa90#64) G' (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt
            A (s.sp + 0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
            sessionStateAt A (coroPtr + 0xf8#64) (mkClonedGhost locIdPtr remIdPtr rootKeyPtr
            aliceBasePtr
                locIdBytes remIdBytes aliceBaseBytes sg f248 f24c) st ∗ protocolAddressAt A rem
                remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG
                whisperMsgPtr msg ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey
                rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ memRegion (s.sp + 0x3e0#64)
                104 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄
                v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64)
                ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
                0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp +
                0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂
                prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗
                ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x98#64)
                ↦₆₄ 32#64) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
                whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp +
                0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp +
                0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64)
                ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄
                sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp +
                0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64)
                ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄
                sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp +
                0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧ s2.sp = s.sp ∧ s2.trace = s0.trace ∧
                img.FrozenLoaded s2 ∧ s2.symtab = img.symtab ∧ s2.readReg64 .x19 = coroPtr ∧
                s2.readReg64 .x24 = s.sp + 0x370#64 ∧ s2.readReg64 .x27 = ctxPtr ∧ s2.readReg64 .x29
                = s.readReg64 .x29)
      (PanicOomProp s0) := by
  dsimp only [stageP3ClonePre]
  refine SepWPp.bind_oom_frame
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_ok_trap img img.base C abs hH.alloc s0 s coroPtr
      locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0
      u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 prevCounter f248 f24c u_30 u_34
      u_5c u_7c sg sc locIdBytes remIdBytes rootKeyBytes aliceBaseBytes hloc_len hrem_len hroot_len
      halice_len hF hsym hpc hrun hsp_align htr hx19 hx27)
    (by sep_focus)
    fun s1 P_f1 hpc1 hrun1 ⟨newLocIdPtr, newRemIdPtr, newRootKeyPtr, newAliceBasePtr, sg', c0, sq0,
      sq1, sq2, sq3, sq4, sq5, hnew1, hnew2, hnew3, hnew4, hsrk', hpriv', hsc_inl, hent1, hsp1,
      htr1, hF1, hsym1, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1,
      hx29_1⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hent1) ?_
  refine SepWPp.weaken_frame
    (bobCoroRest_fold_sessionStateAt coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr
      locIdBytes remIdBytes rootKeyBytes aliceBaseBytes sg sc prevCounter f248 f24c st remIk hloc_nz
      hrem_nz hroot_nz halice_nz hloc_len hrem_len halice_len hloc_deser hrem_eq hrem_deser hroot_eq
      hrc hpq hsc hpend hver hprev)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stackAt_root_eq_chainClone s.sp).symm) (by sep_focus) ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
  have hsp1_root : rootStack ≤ s1.sp.toNat := by rw [hsp1]; exact hsp_root
  have hdec := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_tryDecrypt_v4_nopanic_ok_P_trap img C S abs hH hempty himg s0 s1 coroPtr
    newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr v08 v10 v18 c0 remAddrPtr locAddrPtr
    whisperMsgPtr cur sq0 sq1 sq2 sq3 sq4 sq5 v24 v28 v2c f248 f24c prevCounter locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes rest sg' sc st remIk rem loc msgG msg hnpan1 hnpan2 hnew1
    hnew2 hnew3 hnew4 hloc_len hrem_len halice_len hloc_deser hrem_eq hrem_deser hnot_self hroot_eq
    hrc hpq hsc hpend hver hprev hsc_inl hF1 hsym1 hpc1 hrun1 hsp1_align hsp1_root htr1 hx19_1
    hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1
  rw [hsp1] at hdec
  refine SepWPp.bind_oom_frame hdec (by sep_focus)
    fun s2 P_f2 hpc2 hrun2 ⟨G', hnpan, hdec_rel, hent2, hsp2, htr2, hF2, hsym2, hx19_2, hx24_2,
    hx27_2, hx29_2⟩ => ?_
  refine SepWPp.done hpc2 hrun2 ⟨newLocIdPtr, newRemIdPtr, newRootKeyPtr, newAliceBasePtr, sg', c0,
    sq0, sq1, sq2, sq3, sq4, sq5, G', hnew1, hnew2, hnew3, hnew4, hsrk', hpriv', hsc_inl, hnpan,
    hdec_rel, ?_, hsp2, htr2, hF2, hsym2, hx19_2, hx24_2, hx27_2.trans hx27_1, hx29_2.trans hx29_1⟩
  exact Entails.trans (sepConj_mono_left hent2) (Entails.of_eq (by ac_rfl))

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_and_tryDecrypt_v4_ok_P {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (ctl : BitVec 64) (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr v08 v10 v18
    remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938
    u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64) (v24 v28 v2c prevCounter f248
    f24c u_30 u_34 u_5c u_7c : BitVec 32) (sg : SenderChainGhost) (sc : SenderChain) (locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes rest : List (BitVec 8)) (st : SessionState (List (BitVec
    8))) (remIk : IdentityKey) (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg :
    SignalMessage) (hloc_nz : locIdPtr ≠ 0#64) (hrem_nz : remIdPtr ≠ 0#64) (hroot_nz : rootKeyPtr ≠
    0#64) (halice_nz : aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length = 33) (hrem_len :
    remIdBytes.length = 33) (hroot_len : rootKeyBytes.length = 32) (halice_len :
    aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) (hroot_eq :
    rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState
    = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false) (hver :
    st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hnpan1 :
    (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic) (hnpan2 : ¬
    S.recvPanics st.pqRatchetState msg.pqRatchet) (hF : img.FrozenLoaded s) (hsym : s.symtab =
    img.symtab) (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64
    == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace) (hx19 :
    s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) : SepWPp
    (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64) s
      (stageP3ClonePre A s.sp coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
        u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
        u978 u980 u988 prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc locIdBytes remIdBytes
        rootKeyBytes aliceBaseBytes ∗ bobCoroRestAt A coroPtr locIdPtr remIdPtr rootKeyPtr
        aliceBasePtr ∗ memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp +
        0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp +
        0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp
        + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x3a0#64) ↦₆₄
        remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A rem remAddrPtr ∗
        protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion
        (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗ memRegion (s.sp - BitVec.ofNat 64
        rootStack) (rootStack - chainCloneStack))
      (fun s2 P_f => ∃ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
          (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
          SessionGhost), newLocIdPtr ≠ 0#64 ∧ newRemIdPtr ≠ 0#64 ∧ newRootKeyPtr ≠ 0#64 ∧
          newAliceBasePtr ≠ 0#64 ∧ sg'.srk.bytes = sg.srk.bytes ∧ sg'.priv.bytes = sg.priv.bytes ∧
          OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) ∧
          (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic ∧
          (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
            locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt (pqxdhTryDecryptModel C S
            uuidTryParse rem loc msg rest st).1.toBool G' ∧ (P_f ⊢ sessionStateAt A (s.sp +
            0xa90#64) G' (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt
            A (s.sp + 0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
            sessionStateAt A (coroPtr + 0xf8#64) (mkClonedGhost locIdPtr remIdPtr rootKeyPtr
            aliceBasePtr
                locIdBytes remIdBytes aliceBaseBytes sg f248 f24c) st ∗ protocolAddressAt A rem
                remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG
                whisperMsgPtr msg ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey
                rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ memRegion (s.sp + 0x3e0#64)
                104 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄
                v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64)
                ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp +
                0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp +
                0x48#64) ↦₆₄ c0) ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂
                prevCounter) ∗ ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗
                ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗ ((s.sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x98#64)
                ↦₆₄ 32#64) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
                whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp +
                0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp +
                0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗ ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64)
                ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗ ((s.sp + 0x950#64) ↦₆₄
                sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗ ((s.sp +
                0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64)
                ∗ ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄
                sq4.extractLsb' 64 64) ∗ ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp +
                0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∧ s2.sp = s.sp ∧ s2.trace = s0.trace ∧
                img.FrozenLoaded s2 ∧ s2.symtab = img.symtab ∧ s2.readReg64 .x19 = coroPtr ∧
                s2.readReg64 .x24 = s.sp + 0x370#64 ∧ s2.readReg64 .x27 = ctxPtr ∧ s2.readReg64 .x29
                = s.readReg64 .x29)
      (PanicOomProp s0) := by
  have hT := trapsOnly_trTrap_kit img.base C ctl abs
  rw [← hT.fnAddr] at hpc ⊢
  exact SepWPp.of_trapsOnly hT
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_and_tryDecrypt_v4_ok_P_trap
      img C S abs hH hempty himg s0 s coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr v08
      v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0
      u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 v24 v28 v2c prevCounter f248 f24c
      u_30 u_34 u_5c u_7c sg sc locIdBytes remIdBytes rootKeyBytes aliceBaseBytes rest st remIk rem
      loc msgG msg hloc_nz hrem_nz hroot_nz halice_nz hloc_len hrem_len hroot_len halice_len
      hloc_deser hrem_eq hrem_deser hnot_self hroot_eq hrc hpq hsc hpend hver hprev hnpan1 hnpan2 hF
      hsym hpc hrun hsp_align hsp_root htr hx19 hx27)

/-! ## 1. Spatial Bridging Helpers (`+0x1cd8` and `+0x34dc`) -/

/-- Frame preserved across `stageP3_sub5_dispatch_ok` after `stageP3_tryDecrypt_v4_nopanic_ok`. -/
def _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame (A : RustAlloc) (ctl : BitVec 64) (C : Crypto) (sp : BitVec 64)
    (coroPtr v08 v10 v18 c0 newRootKeyPtr newRemIdPtr newLocIdPtr ctxPtr
     remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (sq3 sq4 sq5 : BitVec 128) (v24 v28 v2c f248 f24c prevCounter : BitVec 32) (rest : List (BitVec
    8)) (st : SessionState (List (BitVec 8))) (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg
    : SignalMessage) : SepProp :=
  ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
  protocolAddressAt A rem remAddrPtr ∗
  protocolAddressAt A loc locAddrPtr ∗
  signalMessageAt A msgG whisperMsgPtr msg ∗
  CryptoVerification.SignalSession.Coins.coinsAfter ctl cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
  ((sp + 0x8#64) ↦₆₄ v08) ∗ ((sp + 0x10#64) ↦₆₄ v10) ∗ ((sp + 0x18#64) ↦₆₄ v18) ∗
  ((sp + 0x24#64) ↦₃₂ v24) ∗ ((sp + 0x28#64) ↦₃₂ v28) ∗ ((sp + 0x2c#64) ↦₃₂ v2c) ∗
  ((sp + 0x30#64) ↦₃₂ f248) ∗ ((sp + 0x34#64) ↦₃₂ f24c) ∗
  ((sp + 0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((sp + 0x40#64) ↦₆₄ 0#64) ∗
  ((sp + 0x48#64) ↦₆₄ c0) ∗ ((sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
  ((sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
  ((sp + 0x68#64) ↦₆₄ 33#64) ∗ ((sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
  ((sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((sp + 0x98#64) ↦₆₄ 32#64) ∗
  ((sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
  ((sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
  ((sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
  ((sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
  ((sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)

set_option linter.unusedVariables false in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.postTryDecrypt_entails_dispatchPre (A : RustAlloc) (img : Obj.Image) (C : Crypto)
    (ctl : BitVec 64) (S : SpqrModel) (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr
     v08 v10 v18 c0 newRootKeyPtr newRemIdPtr newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
     cur : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (v24 v28 v2c f248 f24c prevCounter : BitVec 32) (b_2c0 :
    BitVec 8) (rest : List (BitVec 8)) (G' recG : SessionGhost) (st : SessionState (List (BitVec
    8))) (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) : (sessionStateAt A
    (s.sp + 0xa90#64) G' (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt
    A (s.sp + 0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
    sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ protocolAddressAt A rem remAddrPtr ∗
    protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base
    cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗
    A.pool ∗ memRegion (s.sp + 0x3e0#64) 104 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄
    v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗
    ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp
    + 0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0)
    ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64)
    ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗ ((s.sp +
    0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x98#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp +
    0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
    ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
    ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
    ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
    ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
    ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
    ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
    ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∗
    stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0 ⊢ stageP3DispatchPre A
    img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
      (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 b_2c0 G' recG
      (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 st ∗ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame
      A img.base C s.sp coroPtr v08 v10 v18 c0 newRootKeyPtr newRemIdPtr
      newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248 f24c
      prevCounter rest st rem loc msgG msg := by
  unfold stageP3Sub5ExtraPre stageP3DispatchPre CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame
  rw [logOff_eq_5b810 img, stackAt_root_eq_growOneSpe s.sp, ← sp3e0_104_240_eq_344 s.sp]
  have h930 := sp930_6words_entails_memRegion48 s.sp
    (sq0.extractLsb' 0 64) (sq0.extractLsb' 64 64) (sq1.extractLsb' 0 64) (sq1.extractLsb' 64 64)
    (sq2.extractLsb' 0 64) (sq2.extractLsb' 64 64)
  exact entails_replace_sub h930 (by sep_focus) (eq_of_sep_emp (by sep_focus))

/-! ## 2. Stage P3 Version-4 Complete Proof (`stageP3_v4_full_ok`) -/

set_option maxHeartbeats 1200000 in
private theorem stageP3_v4_full_ok_ext_trap_aux {A : RustAlloc} {P : Program} (img : Obj.Image) (C : Crypto)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hTraps : ProofLib.Variant.TrapsOnly (trTrapProgAt img.base C abs) P)
    (hH : TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
     outPtr initErrsPtr prevStatesPtr v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40
     u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
     : BitVec 64)
    (v24 v28 v2c prevCounter f248 f24c u_30 u_34 u_5c u_7c : BitVec 32) (b_2c0 : BitVec 8) (sg :
    SenderChainGhost) (sc : SenderChain) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes rest :
    List (BitVec 8)) (st : SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc :
    AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64) (hloc_nz : locIdPtr ≠ 0#64) (hrem_nz : remIdPtr ≠ 0#64)
    (hroot_nz : rootKeyPtr ≠ 0#64) (halice_nz : aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length =
    33) (hrem_len : remIdBytes.length = 33) (hroot_len : rootKeyBytes.length = 32) (halice_len :
    aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) (hroot_eq :
    rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState
    = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false) (hver :
    st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hnpan1 :
    (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic) (hnpan2 : ¬
    S.recvPanics st.pqRatchetState msg.pqRatchet) (hF : img.FrozenLoaded s) (hsym : s.symtab =
    img.symtab) (hpc : s.pc = P.fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64
    == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace) (hx19 :
    s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) (hOk : ∀ (newLocIdPtr
    newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64) (s' : State) (P_s' : SepProp),
      newLocIdPtr ≠ 0#64 → newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 → newAliceBasePtr ≠ 0#64 →
      sg'.srk.bytes = sg.srk.bytes → sg'.priv.bytes = sg.priv.bytes → OptSenderChainInline (some
      sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) → (mkClonedGhost newLocIdPtr
      newRemIdPtr newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt true G' → (pqxdhTryDecryptModel C
        S uuidTryParse rem loc msg rest st).1 = .ok pt → pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^
        63 → ptPtr ≠ 0#64 → s'.pc = P.fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 → s'.status = .Running → s'.sp = s.sp → s'.trace =
        s0.trace → s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 → s'.readReg64
        .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr → s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 → img.FrozenLoaded s' → s'.symtab = img.symtab →
        (P_s' ⊢ stageP3DispatchOkMid A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
          ptCap ptPtr pt b_2c0 G' (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18 c0 newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248
          f24c prevCounter rest st rem loc msgG msg) → SepWPp P (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp), newLocIdPtr ≠ 0#64 →
      newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 → newAliceBasePtr ≠ 0#64 → sg'.srk.bytes =
      sg.srk.bytes → sg'.priv.bytes = sg.priv.bytes → OptSenderChainInline (some sg') (some sc)
      (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) → (mkClonedGhost newLocIdPtr newRemIdPtr
      newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt false G' → (pqxdhTryDecryptModel
        C S uuidTryParse rem loc msg rest st).1 = .error e → e ≠ .panic → (P_f ⊢ ((s.sp + 0x88#64)
        ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗ stageP3ErrPost A img.base s0 s
        coroPtr outPtr prevStatesPtr e ∗ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18
        c0 newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248
          f24c prevCounter rest st rem loc msgG msg) → sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace
          → ClosureCalleeSaved s0 sf → img.FrozenLoaded sf → sf.symtab = img.symtab → Q sf P_f) :
    SepWPp P (s0.readReg64 .x30) s
      ((stageP3ClonePre A s.sp coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
          u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
          u978 u980 u988 prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc locIdBytes remIdBytes
          rootKeyBytes aliceBaseBytes ∗ bobCoroRestAt A coroPtr locIdPtr remIdPtr rootKeyPtr
          aliceBasePtr ∗ memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp +
          0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp +
          0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
          ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x3a0#64)
          ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A rem remAddrPtr ∗
          protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion
          (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗ memRegion (s.sp - BitVec.ofNat
          64 rootStack) (rootStack - chainCloneStack)) ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr
          initErrsPtr prevStatesPtr b_2c0) Q
      (PanicOomProp s0) := by
  have hpc_trap : s.pc = (trTrapProgAt img.base C abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64 := by
    rw [hTraps.fnAddr]; exact hpc
  have hprefix := SepWPp.of_trapsOnly hTraps
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_and_tryDecrypt_v4_ok_P_trap
      img C S abs hH hempty himg
      s0 s coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr v08 v10 v18 remAddrPtr locAddrPtr
      whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958
      u960 u968 u970 u978 u980 u988 v24 v28 v2c prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc
      locIdBytes remIdBytes rootKeyBytes aliceBaseBytes rest st remIk rem loc msgG msg hloc_nz hrem_nz
      hroot_nz halice_nz hloc_len hrem_len hroot_len halice_len hloc_deser hrem_eq hrem_deser
      hnot_self hroot_eq hrc hpq hsc hpend hver hprev hnpan1 hnpan2 hF hsym hpc_trap hrun hsp_align
      hsp_root htr hx19 hx27)
  rw [hTraps.fnAddr] at hprefix
  refine SepWPp.bind_oom_frame hprefix rfl
    fun s2 P_f2 hpc2 hrun2 ⟨newLocIdPtr, newRemIdPtr, newRootKeyPtr, newAliceBasePtr, sg', c0, sq0,
      sq1, sq2, sq3, sq4, sq5, G', hnew1, hnew2, hnew3, hnew4, hsrk', hpriv', hsc_inl, hnpan,
      hdec_rel, hent2, hsp2, htr2, hF2, hsym2, hx19_2, hx24_2, hx27_2, _⟩ => ?_
  have hpre_ent :
      P_f2 ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0 ⊢
      stageP3DispatchPre A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
        (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 b_2c0 G' (mkClonedGhost
        locIdPtr remIdPtr rootKeyPtr aliceBasePtr locIdBytes remIdBytes aliceBaseBytes sg f248 f24c)
        (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 st ∗
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18 c0 newRootKeyPtr newRemIdPtr
        newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248 f24c
        prevCounter rest st rem loc msgG msg := by
    refine Entails.trans (sepConj_mono_left hent2) ?_
    exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.postTryDecrypt_entails_dispatchPre A img C 0#64 S s0 s
      coroPtr outPtr initErrsPtr prevStatesPtr v08 v10 v18 c0 newRootKeyPtr newRemIdPtr newLocIdPtr
      ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq0 sq1 sq2 sq3 sq4 sq5 v24 v28 v2c f248 f24c
      prevCounter b_2c0 rest G' (mkClonedGhost locIdPtr remIdPtr rootKeyPtr aliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg f248 f24c) st rem loc msgG msg
  refine SepWPp.weaken_pre hpre_ent ?_
  have hpc2_trap : s2.pc = (trTrapProgAt img.base C abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1cd8#64 := by
    rw [hTraps.fnAddr]; exact hpc2
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hsp2]
  unfold stageP3DispatchPre
  rcases hres : (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 with e | pt
  · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
    have hdec_false :
        (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
          locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt false G' := by
      simpa [hres, Except.toBool] using hdec_rel
    have herr := SepWPp.of_trapsOnly hTraps
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_err_ok_trap img img.base C abs himg rfl hH.alloc
        s0 s2 coroPtr outPtr initErrsPtr prevStatesPtr hinit_ne e he_npan b_2c0 G' (mkClonedGhost
        locIdPtr remIdPtr rootKeyPtr aliceBasePtr
          locIdBytes remIdBytes aliceBaseBytes sg f248 f24c) (pqxdhTryDecryptModel C S uuidTryParse
          rem loc msg rest st).2 st
        hF2 hsym2 hpc2_trap hrun2 hsp2_align htr2 hx19_2 hx24_2')
    unfold stageP3ErrPre at herr
    rw [hsp2] at herr
    refine SepWPp.ret_sepWPp_frame herr (by sep_focus)
      fun sf _ _ ⟨hspf, htrf, hcc, hFf, hsymf⟩ => ?_
    refine hErr newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
      sg' c0 sq0 sq1 sq2 sq3 sq4 sq5 G' e sf _ hnew1 hnew2 hnew3 hnew4 hsrk' hpriv' hsc_inl
      hdec_false hres he_npan ?_ hspf htrf hcc hFf hsymf
    unfold stageP3ErrPost
    rw [hsp2]
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
  · have hb_align : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
    have hdec_true :
        (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
          locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt true G' := by
      simpa [hres, Except.toBool] using hdec_rel
    have hstack_set :
        stackAt s.sp growOneSpeStack = memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp
          setSessionStateStack :=
      stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
    rw [hstack_set]
    have hok := SepWPp.of_trapsOnly hTraps
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_sub5_decResult_ok_trap img img.base C abs hH.alloc
        s0 s2 coroPtr outPtr pt G' (mkClonedGhost locIdPtr remIdPtr rootKeyPtr aliceBasePtr
          locIdBytes remIdBytes aliceBaseBytes sg f248 f24c)
        (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 st hb_align hF2 hsym2 hpc2_trap hrun2
        hsp2_align htr2 hx19_2)
    rw [hTraps.fnAddr, hsp2] at hok
    refine SepWPp.bind_sepWPp_frame_raw hok (by sep_focus)
      fun s' P_m hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs', hsp', htr', hF', hsym',
        hx19', hx24', hx25', hx26', hx27', hx28', _⟩ => ?_
    refine hOk newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
      sg' c0 sq0 sq1 sq2 sq3 sq4 sq5 G' pt ptCap ptPtr s' _ hnew1 hnew2 hnew3 hnew4 hsrk' hpriv'
      hsc_inl hdec_true hres hpt_le hpt_lt hpt_ne hpc' hrun' hsp' htr' hx19' (hx24'.trans hx24_2)
      hx25' hx26' (hx27'.trans hx27_2) hx28' hF' hsym' ?_
    unfold stageP3DispatchOkMid
    rw [hstack_set]
    exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (eq_of_sep_emp (by sep_focus)))

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_v4_full_ok_trap {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
     outPtr initErrsPtr prevStatesPtr v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40
     u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
     : BitVec 64)
    (v24 v28 v2c prevCounter f248 f24c u_30 u_34 u_5c u_7c : BitVec 32) (b_2c0 : BitVec 8) (sg :
    SenderChainGhost) (sc : SenderChain) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes rest :
    List (BitVec 8)) (st : SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc :
    AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64) (hloc_nz : locIdPtr ≠ 0#64) (hrem_nz : remIdPtr ≠ 0#64)
    (hroot_nz : rootKeyPtr ≠ 0#64) (halice_nz : aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length =
    33) (hrem_len : remIdBytes.length = 33) (hroot_len : rootKeyBytes.length = 32) (halice_len :
    aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) (hroot_eq :
    rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState
    = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false) (hver :
    st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hnpan1 :
    (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic) (hnpan2 : ¬
    S.recvPanics st.pqRatchetState msg.pqRatchet) (hF : img.FrozenLoaded s) (hsym : s.symtab =
    img.symtab) (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64
    == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace) (hx19 :
    s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) (hOk : ∀ (newLocIdPtr
    newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64) (s' : State) (P_s' : SepProp),
      newLocIdPtr ≠ 0#64 → newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 → newAliceBasePtr ≠ 0#64 →
      sg'.srk.bytes = sg.srk.bytes → sg'.priv.bytes = sg.priv.bytes → OptSenderChainInline (some
      sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) → (mkClonedGhost newLocIdPtr
      newRemIdPtr newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt true G' → (pqxdhTryDecryptModel C
        S uuidTryParse rem loc msg rest st).1 = .ok pt → pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^
        63 → ptPtr ≠ 0#64 → s'.pc = (trTrapProgAt img.base C abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 → s'.status = .Running → s'.sp = s.sp → s'.trace =
        s0.trace → s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 → s'.readReg64
        .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr → s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 → img.FrozenLoaded s' → s'.symtab = img.symtab →
        (P_s' ⊢ stageP3DispatchOkMid A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
          ptCap ptPtr pt b_2c0 G' (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18 c0 newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248
          f24c prevCounter rest st rem loc msgG msg) → SepWPp (trTrapProgAt img.base C abs)
          (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp), newLocIdPtr ≠ 0#64 →
      newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 → newAliceBasePtr ≠ 0#64 → sg'.srk.bytes =
      sg.srk.bytes → sg'.priv.bytes = sg.priv.bytes → OptSenderChainInline (some sg') (some sc)
      (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) → (mkClonedGhost newLocIdPtr newRemIdPtr
      newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt false G' → (pqxdhTryDecryptModel
        C S uuidTryParse rem loc msg rest st).1 = .error e → e ≠ .panic → (P_f ⊢ ((s.sp + 0x88#64)
        ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗ stageP3ErrPost A img.base s0 s
        coroPtr outPtr prevStatesPtr e ∗ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18
        c0 newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248
          f24c prevCounter rest st rem loc msgG msg) → sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace
          → ClosureCalleeSaved s0 sf → img.FrozenLoaded sf → sf.symtab = img.symtab → Q sf P_f) :
    SepWPp (trTrapProgAt img.base C abs) (s0.readReg64 .x30) s
      ((stageP3ClonePre A s.sp coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
          u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
          u978 u980 u988 prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc locIdBytes remIdBytes
          rootKeyBytes aliceBaseBytes ∗ bobCoroRestAt A coroPtr locIdPtr remIdPtr rootKeyPtr
          aliceBasePtr ∗ memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp +
          0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp +
          0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
          ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x3a0#64)
          ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A rem remAddrPtr ∗
          protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion
          (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗ memRegion (s.sp - BitVec.ofNat
          64 rootStack) (rootStack - chainCloneStack)) ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr
          initErrsPtr prevStatesPtr b_2c0) Q
      (PanicOomProp s0) := by
  exact stageP3_v4_full_ok_ext_trap_aux img C S abs (ProofLib.Variant.TrapsOnly.refl _) hH hempty himg
    s0 s coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr outPtr initErrsPtr prevStatesPtr
    v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 v24 v28 v2c prevCounter f248 f24c
    u_30 u_34 u_5c u_7c b_2c0 sg sc locIdBytes remIdBytes rootKeyBytes aliceBaseBytes rest st remIk
    rem loc msgG msg Q hinit_ne hloc_nz hrem_nz hroot_nz halice_nz hloc_len hrem_len hroot_len
    halice_len hloc_deser hrem_eq hrem_deser hnot_self hroot_eq hrc hpq hsc hpend hver hprev hnpan1
    hnpan2 hF hsym hpc hrun hsp_align hsp_root htr hx19 hx27 hOk hErr

set_option maxHeartbeats 6400000 in
/-- Stage P3 Version-4 Full Assembly (`stageP3_v4_full_ok`, `+0x1778#64 -> +0x34dc#64` / `x30`): Composes `stageP3_clone_and_tryDecrypt_v4_ok` (`+0x1778#64 -> +0x1cd8#64`) with
`stageP3_sub5_decResult_ok` (`+0x1cd8#64 -> +0x34dc#64` on `Ok`) and `stageP3_sub5_err_ok`
(`+0x1cd8#64 -> s0.readReg64 .x30` on `Err`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_v4_full_ok {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (ctl : BitVec 64) (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
     outPtr initErrsPtr prevStatesPtr v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40
     u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
     : BitVec 64)
    (v24 v28 v2c prevCounter f248 f24c u_30 u_34 u_5c u_7c : BitVec 32) (b_2c0 : BitVec 8) (sg :
    SenderChainGhost) (sc : SenderChain) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes rest :
    List (BitVec 8)) (st : SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc :
    AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64) (hloc_nz : locIdPtr ≠ 0#64) (hrem_nz : remIdPtr ≠ 0#64)
    (hroot_nz : rootKeyPtr ≠ 0#64) (halice_nz : aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length =
    33) (hrem_len : remIdBytes.length = 33) (hroot_len : rootKeyBytes.length = 32) (halice_len :
    aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) (hroot_eq :
    rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState
    = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false) (hver :
    st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hnpan1 :
    (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic) (hnpan2 : ¬
    S.recvPanics st.pqRatchetState msg.pqRatchet) (hF : img.FrozenLoaded s) (hsym : s.symtab =
    img.symtab) (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64
    == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace) (hx19 :
    s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) (hOk : ∀ (newLocIdPtr
    newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64) (s' : State) (P_s' : SepProp),
      newLocIdPtr ≠ 0#64 → newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 → newAliceBasePtr ≠ 0#64 →
      sg'.srk.bytes = sg.srk.bytes → sg'.priv.bytes = sg.priv.bytes → OptSenderChainInline (some
      sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) → (mkClonedGhost newLocIdPtr
      newRemIdPtr newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt true G' → (pqxdhTryDecryptModel C
        S uuidTryParse rem loc msg rest st).1 = .ok pt → pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^
        63 → ptPtr ≠ 0#64 → s'.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 → s'.status = .Running → s'.sp = s.sp → s'.trace =
        s0.trace → s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 → s'.readReg64
        .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr → s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 → img.FrozenLoaded s' → s'.symtab = img.symtab →
        (P_s' ⊢ stageP3DispatchOkMid A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
          ptCap ptPtr pt b_2c0 G' (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18 c0 newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248
          f24c prevCounter rest st rem loc msgG msg) → SepWPp (tripleRatchetProgAt img.base C ctl
          abs) (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp), newLocIdPtr ≠ 0#64 →
      newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 → newAliceBasePtr ≠ 0#64 → sg'.srk.bytes =
      sg.srk.bytes → sg'.priv.bytes = sg.priv.bytes → OptSenderChainInline (some sg') (some sc)
      (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) → (mkClonedGhost newLocIdPtr newRemIdPtr
      newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt false G' → (pqxdhTryDecryptModel
        C S uuidTryParse rem loc msg rest st).1 = .error e → e ≠ .panic → (P_f ⊢ ((s.sp + 0x88#64)
        ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗ stageP3ErrPost A img.base s0 s
        coroPtr outPtr prevStatesPtr e ∗ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18
        c0 newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248
          f24c prevCounter rest st rem loc msgG msg) → sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace
          → ClosureCalleeSaved s0 sf → img.FrozenLoaded sf → sf.symtab = img.symtab → Q sf P_f) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .x30) s
      ((stageP3ClonePre A s.sp coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
          u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
          u978 u980 u988 prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc locIdBytes remIdBytes
          rootKeyBytes aliceBaseBytes ∗ bobCoroRestAt A coroPtr locIdPtr remIdPtr rootKeyPtr
          aliceBasePtr ∗ memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp +
          0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp +
          0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
          ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x3a0#64)
          ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A rem remAddrPtr ∗
          protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion
          (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗ memRegion (s.sp - BitVec.ofNat
          64 rootStack) (rootStack - chainCloneStack)) ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr
          initErrsPtr prevStatesPtr b_2c0) Q
      (PanicOomProp s0) := by
  exact stageP3_v4_full_ok_ext_trap_aux img C S abs (trapsOnly_trTrap_kit img.base C ctl abs) hH hempty himg
    s0 s coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr outPtr initErrsPtr prevStatesPtr
    v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 v24 v28 v2c prevCounter f248 f24c
    u_30 u_34 u_5c u_7c b_2c0 sg sc locIdBytes remIdBytes rootKeyBytes aliceBaseBytes rest st remIk
    rem loc msgG msg Q hinit_ne hloc_nz hrem_nz hroot_nz halice_nz hloc_len hrem_len hroot_len
    halice_len hloc_deser hrem_eq hrem_deser hnot_self hroot_eq hrc hpq hsc hpend hver hprev hnpan1
    hnpan2 hF hsym hpc hrun hsp_align hsp_root htr hx19 hx27 hOk hErr

/-! ## 3. Unified `stageP3_ok` Across All `msgVer` -/

set_option maxHeartbeats 1200000 in
private theorem stageP3_ok_ext_trap_aux {A : RustAlloc} {P : Program} (img : Obj.Image) (C : Crypto)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hTraps : ProofLib.Variant.TrapsOnly (trTrapProgAt img.base C abs) P)
    (hH : TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
     outPtr initErrsPtr prevStatesPtr v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40
     u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
     : BitVec 64)
    (msgVer v24 v28 v2c prevCounter f248 f24c u_30 u_34 u_5c u_7c : BitVec 32) (b_2c0 : BitVec 8)
    (sg : SenderChainGhost) (sc : SenderChain) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes
    rest : List (BitVec 8)) (st : SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc :
    AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64) (hloc_nz : locIdPtr ≠ 0#64) (hrem_nz : remIdPtr ≠ 0#64)
    (hroot_nz : rootKeyPtr ≠ 0#64) (halice_nz : aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length =
    33) (hrem_len : remIdBytes.length = 33) (hroot_len : rootKeyBytes.length = 32) (halice_len :
    aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) (hroot_eq :
    rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState
    = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false) (hver :
    st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hnpan1 : msgVer = 4#32 →
    (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic) (hnpan2 : msgVer
    = 4#32 → ¬ S.recvPanics st.pqRatchetState msg.pqRatchet) (hF : img.FrozenLoaded s) (hsym :
    s.symtab = img.symtab) (hpc : s.pc = P.fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64
    == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace) (hx19 :
    s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) (hOk : ∀ (newLocIdPtr
    newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64) (s' : State) (P_s' : SepProp),
      msgVer = 4#32 → newLocIdPtr ≠ 0#64 → newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 →
      newAliceBasePtr ≠ 0#64 → sg'.srk.bytes = sg.srk.bytes → sg'.priv.bytes = sg.priv.bytes →
      OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) →
      (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt true G' → (pqxdhTryDecryptModel C
        S uuidTryParse rem loc msg rest st).1 = .ok pt → pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^
        63 → ptPtr ≠ 0#64 → s'.pc = P.fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 → s'.status = .Running → s'.sp = s.sp → s'.trace =
        s0.trace → s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 → s'.readReg64
        .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr → s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 → img.FrozenLoaded s' → s'.symtab = img.symtab →
        (P_s' ⊢ stageP3DispatchOkMid A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
          ptCap ptPtr pt b_2c0 G' (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18 c0 newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248
          f24c prevCounter rest st rem loc msgG msg) → SepWPp P (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp), msgVer = 4#32 →
      newLocIdPtr ≠ 0#64 → newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 → newAliceBasePtr ≠ 0#64 →
      sg'.srk.bytes = sg.srk.bytes → sg'.priv.bytes = sg.priv.bytes → OptSenderChainInline (some
      sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) → (mkClonedGhost newLocIdPtr
      newRemIdPtr newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt false G' → (pqxdhTryDecryptModel
        C S uuidTryParse rem loc msg rest st).1 = .error e → e ≠ .panic → (P_f ⊢ ((s.sp + 0x88#64)
        ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗ stageP3ErrPost A img.base s0 s
        coroPtr outPtr prevStatesPtr e ∗ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18
        c0 newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248
          f24c prevCounter rest st rem loc msgG msg) → sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace
          → ClosureCalleeSaved s0 sf → img.FrozenLoaded sf → sf.symtab = img.symtab → Q sf P_f)
    (hVerNe : ∀ (sf : State) (P_f : SepProp), msgVer ≠ 4#32 → (P_f ⊢ (outPtr ↦₆₄
      0x8000000000000018#64) ∗ memRegion (outPtr + 8#64) 40 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr +
      0x2c0#64) ↦₈ 1#8) ∗ logOff img ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ stackAt s.sp
      growOneSpeStack ∗ A.pool ∗ anyHeap) → sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf → img.FrozenLoaded sf → sf.symtab = img.symtab → Q sf P_f) :
    SepWPp P (s0.readReg64 .x30) s
      ((stageP3ClonePre A s.sp coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
          u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
          u978 u980 u988 prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc locIdBytes remIdBytes
          rootKeyBytes aliceBaseBytes ∗ bobCoroRestAt A coroPtr locIdPtr remIdPtr rootKeyPtr
          aliceBasePtr ∗ memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp +
          0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp +
          0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
          ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64)
          ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A rem remAddrPtr ∗
          protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion
          (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗ memRegion (s.sp - BitVec.ofNat
          64 rootStack) (rootStack - chainCloneStack)) ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr
          initErrsPtr prevStatesPtr b_2c0) Q
      (PanicOomProp s0) := by
  by_cases hmv : msgVer = 4#32
  · subst hmv
    exact stageP3_v4_full_ok_ext_trap_aux img C S abs hTraps hH hempty himg
      s0 s coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr outPtr initErrsPtr prevStatesPtr
      v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98
      u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 v24 v28 v2c prevCounter f248
      f24c u_30 u_34 u_5c u_7c b_2c0 sg sc locIdBytes remIdBytes rootKeyBytes aliceBaseBytes rest st
      remIk rem loc msgG msg Q hinit_ne hloc_nz hrem_nz hroot_nz halice_nz hloc_len hrem_len
      hroot_len halice_len hloc_deser hrem_eq hrem_deser hnot_self hroot_eq hrc hpq hsc hpend hver
      hprev (hnpan1 rfl) (hnpan2 rfl) hF hsym hpc hrun hsp_align hsp_root htr hx19 hx27 (fun
      newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
           sg' c0 sq0 sq1 sq2 sq3 sq4 sq5 G' pt ptCap ptPtr s' P_s' =>
        hOk newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
          sg' c0 sq0 sq1 sq2 sq3 sq4 sq5 G' pt ptCap ptPtr s' P_s' rfl)
      (fun newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
           sg' c0 sq0 sq1 sq2 sq3 sq4 sq5 G' e sf P_f =>
        hErr newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr sg' c0 sq0 sq1 sq2 sq3 sq4 sq5 G'
        e sf P_f rfl)
  · unfold stageP3Sub5ExtraPre
    refine SepWPp.weaken_frame
      (Entails.of_eq (stackAt_root_chainClone_eq_growOneSpe s.sp))
      (by dsimp only [stageP3ClonePre]; sep_focus) ?_
    have hpc_trap : s.pc = (trTrapProgAt img.base C abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64 := by
      rw [hTraps.fnAddr]; exact hpc
    have hver_ne := SepWPp.of_trapsOnly hTraps
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_clone_and_ver_ne_ok_trap img C abs hH.alloc himg
        s0 s coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr v08 v10 v18 outPtr initErrsPtr
        prevStatesPtr u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960
        u968 u970 u978 u980 u988 msgVer v24 v28 v2c prevCounter f248 f24c u_30 u_34 u_5c u_7c b_2c0 sg
        sc locIdBytes remIdBytes rootKeyBytes aliceBaseBytes st remIk hmv hinit_ne hloc_nz hrem_nz
        hroot_nz halice_nz hloc_len hrem_len hroot_len halice_len hloc_deser hrem_eq hrem_deser
        hroot_eq hrc hpq hsc hpend hver hprev hF hsym hpc_trap hrun hsp_align htr hx19 hx27)
    refine SepWPp.bind_oom_frame hver_ne (by dsimp only [stageP3ClonePre]; sep_focus)
      fun sf P_ff hpcf hrunf ⟨hentf, hspf, htrf, hcsf, hFf, hsymf⟩ => ?_
    refine SepWPp.done hpcf hrunf (hVerNe sf _ hmv ?_ hspf htrf hcsf hFf hsymf)
    refine Entails.trans (sepConj_mono_left hentf) ?_
    simp only [sepConj_assoc]
    repeat apply sepConj_mono_right
    exact entails_anyHeap _

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_ok_trap {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
     outPtr initErrsPtr prevStatesPtr v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40
     u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
     : BitVec 64)
    (msgVer v24 v28 v2c prevCounter f248 f24c u_30 u_34 u_5c u_7c : BitVec 32) (b_2c0 : BitVec 8)
    (sg : SenderChainGhost) (sc : SenderChain) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes
    rest : List (BitVec 8)) (st : SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc :
    AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64) (hloc_nz : locIdPtr ≠ 0#64) (hrem_nz : remIdPtr ≠ 0#64)
    (hroot_nz : rootKeyPtr ≠ 0#64) (halice_nz : aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length =
    33) (hrem_len : remIdBytes.length = 33) (hroot_len : rootKeyBytes.length = 32) (halice_len :
    aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) (hroot_eq :
    rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState
    = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false) (hver :
    st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hnpan1 : msgVer = 4#32 →
    (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic) (hnpan2 : msgVer
    = 4#32 → ¬ S.recvPanics st.pqRatchetState msg.pqRatchet) (hF : img.FrozenLoaded s) (hsym :
    s.symtab = img.symtab) (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64
    == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace) (hx19 :
    s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) (hOk : ∀ (newLocIdPtr
    newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64) (s' : State) (P_s' : SepProp),
      msgVer = 4#32 → newLocIdPtr ≠ 0#64 → newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 →
      newAliceBasePtr ≠ 0#64 → sg'.srk.bytes = sg.srk.bytes → sg'.priv.bytes = sg.priv.bytes →
      OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) →
      (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt true G' → (pqxdhTryDecryptModel C
        S uuidTryParse rem loc msg rest st).1 = .ok pt → pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^
        63 → ptPtr ≠ 0#64 → s'.pc = (trTrapProgAt img.base C abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 → s'.status = .Running → s'.sp = s.sp → s'.trace =
        s0.trace → s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 → s'.readReg64
        .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr → s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 → img.FrozenLoaded s' → s'.symtab = img.symtab →
        (P_s' ⊢ stageP3DispatchOkMid A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
          ptCap ptPtr pt b_2c0 G' (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18 c0 newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248
          f24c prevCounter rest st rem loc msgG msg) → SepWPp (trTrapProgAt img.base C abs)
          (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp), msgVer = 4#32 →
      newLocIdPtr ≠ 0#64 → newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 → newAliceBasePtr ≠ 0#64 →
      sg'.srk.bytes = sg.srk.bytes → sg'.priv.bytes = sg.priv.bytes → OptSenderChainInline (some
      sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) → (mkClonedGhost newLocIdPtr
      newRemIdPtr newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt false G' → (pqxdhTryDecryptModel
        C S uuidTryParse rem loc msg rest st).1 = .error e → e ≠ .panic → (P_f ⊢ ((s.sp + 0x88#64)
        ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗ stageP3ErrPost A img.base s0 s
        coroPtr outPtr prevStatesPtr e ∗ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18
        c0 newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248
          f24c prevCounter rest st rem loc msgG msg) → sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace
          → ClosureCalleeSaved s0 sf → img.FrozenLoaded sf → sf.symtab = img.symtab → Q sf P_f)
    (hVerNe : ∀ (sf : State) (P_f : SepProp), msgVer ≠ 4#32 → (P_f ⊢ (outPtr ↦₆₄
      0x8000000000000018#64) ∗ memRegion (outPtr + 8#64) 40 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr +
      0x2c0#64) ↦₈ 1#8) ∗ logOff img ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ stackAt s.sp
      growOneSpeStack ∗ A.pool ∗ anyHeap) → sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf → img.FrozenLoaded sf → sf.symtab = img.symtab → Q sf P_f) :
    SepWPp (trTrapProgAt img.base C abs) (s0.readReg64 .x30) s
      ((stageP3ClonePre A s.sp coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
          u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
          u978 u980 u988 prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc locIdBytes remIdBytes
          rootKeyBytes aliceBaseBytes ∗ bobCoroRestAt A coroPtr locIdPtr remIdPtr rootKeyPtr
          aliceBasePtr ∗ memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp +
          0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp +
          0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
          ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64)
          ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A rem remAddrPtr ∗
          protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion
          (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗ memRegion (s.sp - BitVec.ofNat
          64 rootStack) (rootStack - chainCloneStack)) ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr
          initErrsPtr prevStatesPtr b_2c0) Q
      (PanicOomProp s0) := by
  exact stageP3_ok_ext_trap_aux img C S abs (ProofLib.Variant.TrapsOnly.refl _) hH hempty himg
    s0 s coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr outPtr initErrsPtr prevStatesPtr
    v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 msgVer v24 v28 v2c prevCounter f248
    f24c u_30 u_34 u_5c u_7c b_2c0 sg sc locIdBytes remIdBytes rootKeyBytes aliceBaseBytes rest st
    remIk rem loc msgG msg Q hinit_ne hloc_nz hrem_nz hroot_nz halice_nz hloc_len hrem_len hroot_len
    halice_len hloc_deser hrem_eq hrem_deser hnot_self hroot_eq hrc hpq hsc hpend hver hprev hnpan1
    hnpan2 hF hsym hpc hrun hsp_align hsp_root htr hx19 hx27 hOk hErr hVerNe

set_option maxHeartbeats 6400000 in
/-- Unified Stage P3 Theorem (`stageP3_ok`, `+0x1778#64 -> +0x34dc#64` / `x30`): Dispatches by `msgVer = 4#32`:
- When `msgVer = 4#32`: executes `stageP3_v4_full_ok` (`stageP3_clone_and_tryDecrypt_v4_ok` +
  `stageP3_sub5_decResult_ok` / `stageP3_sub5_err_ok`).
- When `msgVer ≠ 4#32`: executes `stageP3_clone_and_ver_ne_ok` (`+0x1778#64 -> s0.readReg64 .x30`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_ok {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (ctl : BitVec 64) (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
     outPtr initErrsPtr prevStatesPtr v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40
     u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
     : BitVec 64)
    (msgVer v24 v28 v2c prevCounter f248 f24c u_30 u_34 u_5c u_7c : BitVec 32) (b_2c0 : BitVec 8)
    (sg : SenderChainGhost) (sc : SenderChain) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes
    rest : List (BitVec 8)) (st : SessionState (List (BitVec 8))) (remIk : IdentityKey) (rem loc :
    AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64) (hloc_nz : locIdPtr ≠ 0#64) (hrem_nz : remIdPtr ≠ 0#64)
    (hroot_nz : rootKeyPtr ≠ 0#64) (halice_nz : aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length =
    33) (hrem_len : remIdBytes.length = 33) (hroot_len : rootKeyBytes.length = 32) (halice_len :
    aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hnot_self : st.remoteIdentity ≠ some
    st.localIdentity ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) (hroot_eq :
    rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState
    = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false) (hver :
    st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hnpan1 : msgVer = 4#32 →
    (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ≠ .error .panic) (hnpan2 : msgVer
    = 4#32 → ¬ S.recvPanics st.pqRatchetState msg.pqRatchet) (hF : img.FrozenLoaded s) (hsym :
    s.symtab = img.symtab) (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64
    == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace = s0.trace) (hx19 :
    s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) (hOk : ∀ (newLocIdPtr
    newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64) (s' : State) (P_s' : SepProp),
      msgVer = 4#32 → newLocIdPtr ≠ 0#64 → newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 →
      newAliceBasePtr ≠ 0#64 → sg'.srk.bytes = sg.srk.bytes → sg'.priv.bytes = sg.priv.bytes →
      OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) →
      (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt true G' → (pqxdhTryDecryptModel C
        S uuidTryParse rem loc msg rest st).1 = .ok pt → pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^
        63 → ptPtr ≠ 0#64 → s'.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 → s'.status = .Running → s'.sp = s.sp → s'.trace =
        s0.trace → s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 → s'.readReg64
        .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr → s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 → img.FrozenLoaded s' → s'.symtab = img.symtab →
        (P_s' ⊢ stageP3DispatchOkMid A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
          ptCap ptPtr pt b_2c0 G' (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18 c0 newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248
          f24c prevCounter rest st rem loc msgG msg) → SepWPp (tripleRatchetProgAt img.base C ctl
          abs) (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp), msgVer = 4#32 →
      newLocIdPtr ≠ 0#64 → newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 → newAliceBasePtr ≠ 0#64 →
      sg'.srk.bytes = sg.srk.bytes → sg'.priv.bytes = sg.priv.bytes → OptSenderChainInline (some
      sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5) → (mkClonedGhost newLocIdPtr
      newRemIdPtr newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c).AfterTryDecrypt false G' → (pqxdhTryDecryptModel
        C S uuidTryParse rem loc msg rest st).1 = .error e → e ≠ .panic → (P_f ⊢ ((s.sp + 0x88#64)
        ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗ stageP3ErrPost A img.base s0 s
        coroPtr outPtr prevStatesPtr e ∗ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18
        c0 newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248
          f24c prevCounter rest st rem loc msgG msg) → sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace
          → ClosureCalleeSaved s0 sf → img.FrozenLoaded sf → sf.symtab = img.symtab → Q sf P_f)
    (hVerNe : ∀ (sf : State) (P_f : SepProp), msgVer ≠ 4#32 → (P_f ⊢ (outPtr ↦₆₄
      0x8000000000000018#64) ∗ memRegion (outPtr + 8#64) 40 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr +
      0x2c0#64) ↦₈ 1#8) ∗ logOff img ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ stackAt s.sp
      growOneSpeStack ∗ A.pool ∗ anyHeap) → sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf → img.FrozenLoaded sf → sf.symtab = img.symtab → Q sf P_f) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .x30) s
      ((stageP3ClonePre A s.sp coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
          u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970
          u978 u980 u988 prevCounter f248 f24c u_30 u_34 u_5c u_7c sg sc locIdBytes remIdBytes
          rootKeyBytes aliceBaseBytes ∗ bobCoroRestAt A coroPtr locIdPtr remIdPtr rootKeyPtr
          aliceBasePtr ∗ memRegion (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp +
          0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp +
          0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
          ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64)
          ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A rem remAddrPtr ∗
          protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion
          (s.sp + 0x270#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗ memRegion (s.sp - BitVec.ofNat
          64 rootStack) (rootStack - chainCloneStack)) ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr
          initErrsPtr prevStatesPtr b_2c0) Q
      (PanicOomProp s0) := by
  exact stageP3_ok_ext_trap_aux img C S abs (trapsOnly_trTrap_kit img.base C ctl abs) hH hempty himg
    s0 s coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr outPtr initErrsPtr prevStatesPtr
    v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 msgVer v24 v28 v2c prevCounter f248
    f24c u_30 u_34 u_5c u_7c b_2c0 sg sc locIdBytes remIdBytes rootKeyBytes aliceBaseBytes rest st
    remIk rem loc msgG msg Q hinit_ne hloc_nz hrem_nz hroot_nz halice_nz hloc_len hrem_len hroot_len
    halice_len hloc_deser hrem_eq hrem_deser hnot_self hroot_eq hrc hpq hsc hpend hver hprev hnpan1
    hnpan2 hF hsym hpc hrun hsp_align hsp_root htr hx19 hx27 hOk hErr hVerNe

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_initSession_ok_trap {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr
     baseKeyBoxPtr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr ctxPtr outPtr initErrsPtr
     prevStatesPtr v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68
     u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (msgVer v24 v28 v2c pad_f4 remoteRegId localRegId u_30 u_34 u_5c u_7c : BitVec 32) (c0 c1 c2 c3
    c4 d0 d1 d2 : BitVec 64) (b_2c0 : BitVec 8) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes
    spkPubBytes spkPrivBytes chainKeyBytes rest : List (BitVec 8)) (ourIdentity theirIdentity :
    IdentityKey) (sendingKeyPair : KeyPair) (rootKey chainKey pqrKey : BitVec 256) (rem loc :
    AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64) (hloc_nz : localIkBoxPtr ≠ 0#64) (hrem_nz : remoteIkBoxPtr ≠
    0#64) (hroot_nz : rootKeyBoxPtr ≠ 0#64) (halice_nz : baseKeyBoxPtr ≠ 0#64) (hrat_pub :
    ratchetPubBoxPtr ≠ 0#64) (hrat_priv : ratchetPrivBoxPtr ≠ 0#64) (hck_ptr : chainKeyBoxPtr ≠
    0#64) (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33) (hroot_len :
    rootKeyBytes.length = 32) (halice_len : aliceBaseBytes.length = 33) (hspk_pub_len :
    spkPubBytes.length = 33) (hspk_priv_len : spkPrivBytes.length = 32) (hloc_deser :
    PublicKey.deserialize locIdBytes = .ok ourIdentity.publicKey) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok theirIdentity.publicKey) (hspk_deser :
    PublicKey.deserialize spkPubBytes = .ok sendingKeyPair.publicKey) (hspk_priv_eq : spkPrivBytes =
    sendingKeyPair.privateKey.bytes.toList) (hspk_clamp : Ratchet.clampScalar
    sendingKeyPair.privateKey.bytes = sendingKeyPair.privateKey.bytes) (hroot_eq : rootKeyBytes =
    keyToBytes32 rootKey) (hck_eq : chainKeyBytes = keyToBytes32 chainKey) (hnot_self : some
    theirIdentity ≠ some ourIdentity ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)
    (hnpan1 : msgVer = 4#32 → (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
        (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair rootKey
        chainKey pqrKey)).1 ≠ .error .panic)
    (hnpan2 : msgVer = 4#32 → ¬ S.recvPanics
        (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair rootKey
        chainKey pqrKey).pqRatchetState msg.pqRatchet)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc : s.pc = (trTrapProgAt
    img.base C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace
    = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) (hOk
    : ∀ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64) (s' : State) (P_s' : SepProp),
      msgVer = 4#32 → newLocIdPtr ≠ 0#64 → newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 →
      newAliceBasePtr ≠ 0#64 → sg'.srk.bytes = spkPubBytes → sg'.priv.bytes = spkPrivBytes →
      OptSenderChainInline (some sg') (some ⟨sendingKeyPair, ⟨chainKey, 0#32⟩⟩) (bytes104OfW6Q c0'
      sq0 sq1 sq2 sq3 sq4 sq5) → (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr
      newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' remoteRegId localRegId).AfterTryDecrypt true G' →
        (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
        (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair rootKey
        chainKey pqrKey)).1 = .ok pt → pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64
        → s'.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        0x34dc#64 → s'.status = .Running → s'.sp = s.sp → s'.trace = s0.trace → s'.readReg64 .x19 =
        coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 → s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr → s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 =
        0xfffffffffffffffe#64 → img.FrozenLoaded s' → s'.symtab = img.symtab → (P_s' ⊢
        stageP3DispatchOkMid A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr pt
        b_2c0 G'
          (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
            (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair rootKey
            chainKey pqrKey)).2 ∗ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18 c0'
            newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c
          remoteRegId localRegId 0#32 rest (initializeRecipientSession spqrOffB ourIdentity
          theirIdentity sendingKeyPair rootKey chainKey pqrKey) rem loc msgG msg) → SepWPp
          (trTrapProgAt img.base C abs) (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp), msgVer = 4#32 →
      newLocIdPtr ≠ 0#64 → newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 → newAliceBasePtr ≠ 0#64 →
      sg'.srk.bytes = spkPubBytes → sg'.priv.bytes = spkPrivBytes → OptSenderChainInline (some sg')
      (some ⟨sendingKeyPair, ⟨chainKey, 0#32⟩⟩) (bytes104OfW6Q c0' sq0 sq1 sq2 sq3 sq4 sq5) →
      (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' remoteRegId localRegId).AfterTryDecrypt false G' →
        (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
        (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair rootKey
        chainKey pqrKey)).1 = .error e → e ≠ .panic → (P_f ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr +
        0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗ stageP3ErrPost A img.base s0 s coroPtr outPtr
        prevStatesPtr e ∗ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18 c0'
        newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c
          remoteRegId localRegId 0#32 rest (initializeRecipientSession spqrOffB ourIdentity
          theirIdentity sendingKeyPair rootKey chainKey pqrKey) rem loc msgG msg) → sf.sp = s.sp +
          0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf → img.FrozenLoaded sf →
          sf.symtab = img.symtab → Q sf P_f)
    (hVerNe : ∀ (sf : State) (P_f : SepProp), msgVer ≠ 4#32 → (P_f ⊢ (outPtr ↦₆₄
      0x8000000000000018#64) ∗ memRegion (outPtr + 8#64) 40 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr +
      0x2c0#64) ↦₈ 1#8) ∗ logOff img ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ stackAt s.sp
      growOneSpeStack ∗ A.pool ∗ anyHeap) → sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf → img.FrozenLoaded sf → sf.symtab = img.symtab → Q sf P_f) :
    SepWPp (trTrapProgAt img.base C abs) (s0.readReg64 .x30) s
      ((stageP3InitSessionPre A s.sp coroPtr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr
          baseKeyBoxPtr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr ctxPtr u_38 u_40 u_48 u_50
          u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
          pad_f4 remoteRegId localRegId u_30 u_34 u_5c u_7c c0 c1 c2 c3 c4 d0 d1 d2 locIdBytes
          remIdBytes rootKeyBytes aliceBaseBytes spkPubBytes spkPrivBytes chainKeyBytes ∗ memRegion
          (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp +
          0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp +
          0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
          whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc
          locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
          CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗ memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack
          - chainCloneStack)) ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr
          b_2c0) Q
      (PanicOomProp s0) := by
  have hent := stageP3InitSessionPre_entails_clonePre (A := A)
    s.sp coroPtr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr ratchetPubBoxPtr
    ratchetPrivBoxPtr chainKeyBoxPtr ctxPtr u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938
    u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 pad_f4 remoteRegId localRegId u_30 u_34 u_5c
    u_7c c0 c1 c2 c3 c4 d0 d1 d2 locIdBytes remIdBytes rootKeyBytes aliceBaseBytes spkPubBytes
    spkPrivBytes chainKeyBytes ⟨sendingKeyPair, ⟨chainKey, 0#32⟩⟩ hrat_pub hrat_priv hck_ptr
    hspk_pub_len hspk_priv_len hspk_deser hspk_priv_eq hspk_clamp hck_eq rfl
  refine SepWPp.weaken_pre (sepConj_mono_left (Entails.trans (sepConj_mono_left hent) (Entails.of_eq
    (by rw [sepConj_assoc]) ))) ?_
  exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_ok_trap img C S abs hH hempty himg s0 s coroPtr
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr ctxPtr outPtr initErrsPtr prevStatesPtr
    v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 msgVer v24 v28 v2c 0#32 remoteRegId
    localRegId u_30 u_34 u_5c u_7c b_2c0 (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr
    chainKeyBoxPtr spkPubBytes spkPrivBytes) ⟨sendingKeyPair, ⟨chainKey, 0#32⟩⟩ locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes rest (initializeRecipientSession spqrOffB ourIdentity
    theirIdentity sendingKeyPair rootKey chainKey pqrKey) theirIdentity rem loc msgG msg Q hinit_ne
    hloc_nz hrem_nz hroot_nz halice_nz hloc_len hrem_len hroot_len halice_len hloc_deser rfl
    hrem_deser hnot_self hroot_eq rfl rfl rfl rfl rfl rfl hnpan1 hnpan2 hF hsym hpc hrun hsp_align
    hsp_root htr hx19 hx27 hOk hErr hVerNe

/-- Stage P3 Entry for `initializeRecipientSession` (`stageP3_initSession_ok`): Unpacks `bobSession344WithRegIdsBv8` and the 7 heap boxes from `stageP2_ok` and discharges
all `initializeRecipientSession` data hypotheses into `stageP3_ok`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_initSession_ok {A : RustAlloc} (img : Obj.Image) (C : Crypto)
    (ctl : BitVec 64) (S : SpqrModel) (abs : String → Option (State → State)) (hH :
    TripleRatchetHooks C A S abs) (hempty : S.RecvEmptyOk) (himg : Obj.Loads libsignalSessionImage
    img) (s0 s : State) (coroPtr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr
     baseKeyBoxPtr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr ctxPtr outPtr initErrsPtr
     prevStatesPtr v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68
     u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (msgVer v24 v28 v2c pad_f4 remoteRegId localRegId u_30 u_34 u_5c u_7c : BitVec 32) (c0 c1 c2 c3
    c4 d0 d1 d2 : BitVec 64) (b_2c0 : BitVec 8) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes
    spkPubBytes spkPrivBytes chainKeyBytes rest : List (BitVec 8)) (ourIdentity theirIdentity :
    IdentityKey) (sendingKeyPair : KeyPair) (rootKey chainKey pqrKey : BitVec 256) (rem loc :
    AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64) (hloc_nz : localIkBoxPtr ≠ 0#64) (hrem_nz : remoteIkBoxPtr ≠
    0#64) (hroot_nz : rootKeyBoxPtr ≠ 0#64) (halice_nz : baseKeyBoxPtr ≠ 0#64) (hrat_pub :
    ratchetPubBoxPtr ≠ 0#64) (hrat_priv : ratchetPrivBoxPtr ≠ 0#64) (hck_ptr : chainKeyBoxPtr ≠
    0#64) (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33) (hroot_len :
    rootKeyBytes.length = 32) (halice_len : aliceBaseBytes.length = 33) (hspk_pub_len :
    spkPubBytes.length = 33) (hspk_priv_len : spkPrivBytes.length = 32) (hloc_deser :
    PublicKey.deserialize locIdBytes = .ok ourIdentity.publicKey) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok theirIdentity.publicKey) (hspk_deser :
    PublicKey.deserialize spkPubBytes = .ok sendingKeyPair.publicKey) (hspk_priv_eq : spkPrivBytes =
    sendingKeyPair.privateKey.bytes.toList) (hspk_clamp : Ratchet.clampScalar
    sendingKeyPair.privateKey.bytes = sendingKeyPair.privateKey.bytes) (hroot_eq : rootKeyBytes =
    keyToBytes32 rootKey) (hck_eq : chainKeyBytes = keyToBytes32 chainKey) (hnot_self : some
    theirIdentity ≠ some ourIdentity ∨ DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)
    (hnpan1 : msgVer = 4#32 → (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
        (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair rootKey
        chainKey pqrKey)).1 ≠ .error .panic)
    (hnpan2 : msgVer = 4#32 → ¬ S.recvPanics
        (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair rootKey
        chainKey pqrKey).pqRatchetState msg.pqRatchet)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hpc : s.pc = (tripleRatchetProgAt
    img.base C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat) (htr : s.trace
    = s0.trace) (hx19 : s.readReg64 .x19 = coroPtr) (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) (hOk
    : ∀ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64) (s' : State) (P_s' : SepProp),
      msgVer = 4#32 → newLocIdPtr ≠ 0#64 → newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 →
      newAliceBasePtr ≠ 0#64 → sg'.srk.bytes = spkPubBytes → sg'.priv.bytes = spkPrivBytes →
      OptSenderChainInline (some sg') (some ⟨sendingKeyPair, ⟨chainKey, 0#32⟩⟩) (bytes104OfW6Q c0'
      sq0 sq1 sq2 sq3 sq4 sq5) → (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr
      newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' remoteRegId localRegId).AfterTryDecrypt true G' →
        (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
        (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair rootKey
        chainKey pqrKey)).1 = .ok pt → pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64
        → s'.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        0x34dc#64 → s'.status = .Running → s'.sp = s.sp → s'.trace = s0.trace → s'.readReg64 .x19 =
        coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 → s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr → s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 =
        0xfffffffffffffffe#64 → img.FrozenLoaded s' → s'.symtab = img.symtab → (P_s' ⊢
        stageP3DispatchOkMid A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr pt
        b_2c0 G'
          (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
            (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair rootKey
            chainKey pqrKey)).2 ∗ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18 c0'
            newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c
          remoteRegId localRegId 0#32 rest (initializeRecipientSession spqrOffB ourIdentity
          theirIdentity sendingKeyPair rootKey chainKey pqrKey) rem loc msgG msg) → SepWPp
          (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .x30) s' P_s' Q (PanicOomProp s0))
    (hErr : ∀ (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64)
      (sg' : SenderChainGhost) (c0' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (G' :
      SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp), msgVer = 4#32 →
      newLocIdPtr ≠ 0#64 → newRemIdPtr ≠ 0#64 → newRootKeyPtr ≠ 0#64 → newAliceBasePtr ≠ 0#64 →
      sg'.srk.bytes = spkPubBytes → sg'.priv.bytes = spkPrivBytes → OptSenderChainInline (some sg')
      (some ⟨sendingKeyPair, ⟨chainKey, 0#32⟩⟩) (bytes104OfW6Q c0' sq0 sq1 sq2 sq3 sq4 sq5) →
      (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' remoteRegId localRegId).AfterTryDecrypt false G' →
        (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest
        (initializeRecipientSession spqrOffB ourIdentity theirIdentity sendingKeyPair rootKey
        chainKey pqrKey)).1 = .error e → e ≠ .panic → (P_f ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr +
        0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗ stageP3ErrPost A img.base s0 s coroPtr outPtr
        prevStatesPtr e ∗ CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3PostTryDecryptFrame A img.base C s.sp coroPtr v08 v10 v18 c0'
        newRootKeyPtr newRemIdPtr
          newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c
          remoteRegId localRegId 0#32 rest (initializeRecipientSession spqrOffB ourIdentity
          theirIdentity sendingKeyPair rootKey chainKey pqrKey) rem loc msgG msg) → sf.sp = s.sp +
          0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf → img.FrozenLoaded sf →
          sf.symtab = img.symtab → Q sf P_f)
    (hVerNe : ∀ (sf : State) (P_f : SepProp), msgVer ≠ 4#32 → (P_f ⊢ (outPtr ↦₆₄
      0x8000000000000018#64) ∗ memRegion (outPtr + 8#64) 40 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr +
      0x2c0#64) ↦₈ 1#8) ∗ logOff img ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ stackAt s.sp
      growOneSpeStack ∗ A.pool ∗ anyHeap) → sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf → img.FrozenLoaded sf → sf.symtab = img.symtab → Q sf P_f) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .x30) s
      ((stageP3InitSessionPre A s.sp coroPtr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr
          baseKeyBoxPtr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr ctxPtr u_38 u_40 u_48 u_50
          u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988
          pad_f4 remoteRegId localRegId u_30 u_34 u_5c u_7c c0 c1 c2 c3 c4 d0 d1 d2 locIdBytes
          remIdBytes rootKeyBytes aliceBaseBytes spkPubBytes spkPrivBytes chainKeyBytes ∗ memRegion
          (s.sp + 0xa90#64) 344 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp +
          0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp +
          0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄
          whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc
          locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
          CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗ logOff img ∗ memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack
          - chainCloneStack)) ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr
          b_2c0) Q
      (PanicOomProp s0) := by
  have hent := stageP3InitSessionPre_entails_clonePre (A := A)
    s.sp coroPtr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr ratchetPubBoxPtr
    ratchetPrivBoxPtr chainKeyBoxPtr ctxPtr u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938
    u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 pad_f4 remoteRegId localRegId u_30 u_34 u_5c
    u_7c c0 c1 c2 c3 c4 d0 d1 d2 locIdBytes remIdBytes rootKeyBytes aliceBaseBytes spkPubBytes
    spkPrivBytes chainKeyBytes ⟨sendingKeyPair, ⟨chainKey, 0#32⟩⟩ hrat_pub hrat_priv hck_ptr
    hspk_pub_len hspk_priv_len hspk_deser hspk_priv_eq hspk_clamp hck_eq rfl
  refine SepWPp.weaken_pre (sepConj_mono_left (Entails.trans (sepConj_mono_left hent) (Entails.of_eq
    (by rw [sepConj_assoc]) ))) ?_
  exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.stageP3_ok img C ctl S abs hH hempty himg s0 s coroPtr
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr ctxPtr outPtr initErrsPtr prevStatesPtr
    v08 v10 v18 remAddrPtr locAddrPtr whisperMsgPtr cur u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0
    u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 msgVer v24 v28 v2c 0#32 remoteRegId
    localRegId u_30 u_34 u_5c u_7c b_2c0 (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr
    chainKeyBoxPtr spkPubBytes spkPrivBytes) ⟨sendingKeyPair, ⟨chainKey, 0#32⟩⟩ locIdBytes
    remIdBytes rootKeyBytes aliceBaseBytes rest (initializeRecipientSession spqrOffB ourIdentity
    theirIdentity sendingKeyPair rootKey chainKey pqrKey) theirIdentity rem loc msgG msg Q hinit_ne
    hloc_nz hrem_nz hroot_nz halice_nz hloc_len hrem_len hroot_len halice_len hloc_deser rfl
    hrem_deser hnot_self hroot_eq rfl rfl rfl rfl rfl rfl hnpan1 hnpan2 hF hsym hpc hrun hsp_align
    hsp_root htr hx19 hx27 hOk hErr hVerNe

end P3P4

end CryptoVerification.E2E.Pqxdh.ResponderClosure
