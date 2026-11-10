/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitE
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4Aux

/-!
# Stage P2 Substages 1–4 Unified Composition

Composes `stageP2_sub1_to_3_kits` with `stageP2_sub4_some_kits` (discharging Arm 3) and
`stageP2_sub4_none_kits`, reaching `+0x36ac` with a unified OPK keypair representation at
`coroPtr + 0x4b0..0x4f1`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_memRegion8_to_bytes7_1 (p : BitVec 64) :
    memRegion p 8 ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8,
      ∃∗ b4 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8,
        bytes7At p b0 b1 b2 b3 b4 b5 b6 ∗ memRegion (p + 7#64) 1 := by
  rw [ProofLib.memRegion_split p 7 1 (by decide)]
  refine Entails.trans (sepConj_mono_left (p2_memRegion7_to_bytes7At p)) ?_
  sep_norm
  exact Entails.refl _

theorem p2_bytes7_1_to_memRegion8 (p : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    bytes7At p b0 b1 b2 b3 b4 b5 b6 ∗ memRegion (p + 7#64) 1 ⊢ memRegion p 8 := by
  refine Entails.trans (sepConj_mono_left (p2_bytes7At_to_memRegion7 p b0 b1 b2 b3 b4 b5 b6)) ?_
  rw [← ProofLib.memRegion_split p 7 1 (by decide)]
  exact Entails.refl _

theorem p2_ac0_join_16_1 (sp : BitVec 64) :
    memRegion (sp + 0xac0#64) 16 ∗ memRegion (sp + 0xad0#64) 1 = memRegion (sp + 0xac0#64) 17 :=
  (ProofLib.memRegion_split' (b := sp + 0xac0#64) (n := 16) (k := 1)
    (b' := sp + 0xad0#64) rfl (by bv_omega) (by decide)).symm

theorem p2_memRegion64_to_keyPair64UnalignedAt (a : BitVec 64) :
    memRegion a 64 ⊢
      ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
      ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8, ∃∗ c63 : BitVec 8,
      ∃∗ cw0 : BitVec 64, ∃∗ cw1 : BitVec 64, ∃∗ cw2 : BitVec 64, ∃∗ cw3 : BitVec 64,
      ∃∗ cw4 : BitVec 64, ∃∗ cw5 : BitVec 64, ∃∗ cw6 : BitVec 64,
        keyPair64UnalignedAt a c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 :=
  memRegion64_entails_exists_keyPair64UnalignedAt_std3 a

theorem p2_pair64_4f8_to_cells2 (coroPtr u0 u1 : BitVec 64) :
    ((coroPtr + 0x4f8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x500#64) ↦₆₄ u1) ⊢
      cells (coroPtr + 0x4f8#64) 2 := by
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (pointsTo64_entails_memRegion _ _)) ?_
  rw [← ProofLib.memRegion_split' (b := coroPtr + 0x4f8#64) (n := 8) (k := 8)
        (b' := coroPtr + 0x500#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (coroPtr + 0x4f8#64) 2 (by decide)]
  exact Entails.refl _

/-- `Option<PreKeyId>` tag word at `msgPtr + 0x78` (`1#32` when `some _`, `0#32` when `none`). -/
def opkOptTag32 : Option (BitVec 32) → BitVec 32
  | some _ => 1#32
  | none => 0#32

/-- `Option` tag byte at `coroPtr + 0x4b0` (`1#8` when `some _`, `0#8` when `none`). -/
def opkOptTag8 : Option (BitVec 32) → BitVec 8
  | some _ => 1#8
  | none => 0#8

/-- Optional OPK lookup witness (`PreKeyRecord` when `some opkId`, `Unit` when `none`). -/
def OpkOkWitness : Option (BitVec 32) → Type
  | some _ => PreKeyRecord
  | none => Unit

def opkOkRel {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b)
    (stPk : pkKit.PkState) : (opkId? : Option (BitVec 32)) → OpkOkWitness opkId? → Prop
  | some id, r => pkKit.getRel stPk id (.ok r) ∧ pkKit.RecOk r
  | none, () => True

def opkOkUpdate {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b)
    (stPk : pkKit.PkState) : (opkId? : Option (BitVec 32)) → OpkOkWitness opkId? → pkKit.PkState
  | some id, r => pkKit.getUpdate stPk id (.ok r)
  | none, () => stPk

def opkOkEvs {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b) :
    (opkId? : Option (BitVec 32)) → OpkOkWitness opkId? → List TraceEvent
  | some id, r => pkKit.getEvs id (.ok r)
  | none, () => []

def opkOkKeyBytes : (opkId? : Option (BitVec 32)) → OpkOkWitness opkId? →
    List (BitVec 8) → List (BitVec 8) → Prop
  | some _, r, pkB, skB =>
      ∃ rawPriv : List (BitVec 8), rawPriv.length = 32 ∧
        r.preKey.publicKey = 5#8 :: pkB ∧ r.preKey.privateKey = rawPriv ∧
        skB = clampBv8List rawPriv
  | none, (), _, _ => True

set_option maxHeartbeats 1200000 in
/-- Kit-generic Stage P2 Substages 1–4 (`+0x0868 -> +0x36ac` or error exit to `s0.readReg64 .x30`):
Composes `stageP2_sub1_to_3_kits_ext` with `stageP2_sub4_some_kits_ext` (Arm 3 via
`p2_arm3_err_hooks_ok`) and `stageP2_sub4_none_kits`, unifying both OPK branches at `+0x36ac`
under `StageP2ClosureHooks` and `StageP2PureCallees4K`. -/
theorem stageP2_sub1_to_4_kits_ext {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : StageP2ClosureHooks A img.base ext) (hPure : StageP2PureCallees4K P A F img ext)
    (ikit : IdentityStoreSpec A img.base) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesOk img ikit skit)
    (hskitOk : IdentitySelfStoreKitOkI img ikit skit ext)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (hspkVt : SignedPreKeyVtablesOk img spkKit) (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hkpkVt : KyberPreKeyVtablesOk img kpkKit) (hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
    (pkKit : PreKeyStoreSpec A img.base)
    (hpkVt : PreKeyVtablesOk img pkKit) (hpkOk : PreKeyStoreKitOkImgE img pkKit ext)
    (stk : Nat) (hstk_p2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
     v_b0 u_90 u_a8 u_b8 u_d0 u_488 : BitVec 64)
    (baseKey : PublicKey) (signedPreKeyId kyberPreKeyId opkIdWord : BitVec 32)
    (opkId? : Option (BitVec 32))
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState)
    (b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64) (hkyber_nz : kyberCtCap ≠ 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) (tripleRatchetProgAtExt img.base ext) s)
    (hid_spk : spkKit.idOk signedPreKeyId)
    (hspk_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) →
      spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
        spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hkpk_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hopk_word : ∀ id : BitVec 32, opkId? = some id → opkIdWord = id)
    (hid_pk : ∀ id : BitVec 32, opkId? = some id → pkKit.getIdOk id)
    (hpk_wf : ∀ (id : BitVec 32) (r : PreKeyRecord), opkId? = some id →
      pkKit.getRel stPk id (.ok r) → pkKit.RecOk r →
      ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
        opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
        r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running) (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr) (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kpkKit.kpk_vt) (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr) (hx13 : s.readReg64 .x13 = pkKit.pk_vt)
    (hx14 : s.readReg64 .x14 = localAddrPtr) (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = ikit.id_vt) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr) (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt)
    (hErrSpk : ∀ (e : spkKit.GetErr) (spkFutPtr : BitVec 64) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt spkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
        kpkKit.storeAt kyberStorePtr stKpk ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
        ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
        cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
        processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
        ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
        memRegion (coroPtr + 0x4b1#64) 64 ∗
        ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
        ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
        ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
        ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
        ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
        ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
        ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
        ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
        memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame) →
      Q sf P_f)
    (hErrKpk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
      (e : kpkKit.GetErr) (kyberFutPtr : BitVec 64) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt kpkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
        ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
        ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
        cells (coroPtr + 0x3d8#64) 4 ∗
        processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
        ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
        memRegion (coroPtr + 0x4b1#64) 64 ∗
        ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
        ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
        ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
        ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
        ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
        ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
        ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
        ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
        memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame) →
      Q sf P_f)
    (hErrPk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
      (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
      (opkId : BitVec 32) (e : pkKit.GetErr) (pkBuf skBuf opkFutPtr v90 : BitVec 64)
      (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkId? = some opkId → pkKit.getRel stPk opkId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ pkKit.getEvs opkId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt pkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
        memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
        ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
        ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
        ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
        ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
        processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
        ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
        memRegion (coroPtr + 0x4b1#64) 64 ∗
        ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
        ((coroPtr + 0x500#64) ↦₆₄ (img.base + pkKit.getFutVtOff)) ∗
        ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
        ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
        ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
        ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
        ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ pkKit.getErr.w4 e) ∗
        ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ pkKit.getErr.w2 e) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ pkKit.getErr.w3 e) ∗
        memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame) →
      Q sf P_f)
    (hOk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
      (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
      (wOpk : OpkOkWitness opkId?) (opkPkBytes opkSkBytes : List (BitVec 8))
      (pkBuf skBuf idKpFutPtr v90 v_a8' v_b8' v_d0' : BitVec 64) (s4 : State),
      Steps (tripleRatchetProgAtExt img.base ext) s s4 →
      FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
        (stageP2Quiet spkKit kpkKit pkKit skit) (tripleRatchetProgAtExt img.base ext) s4 →
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk opkId? wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes opkId? wOpk opkPkBytes opkSkBytes →
      pkBuf ≠ 0#64 → skBuf ≠ 0#64 → idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
      s4.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x36ac#64 →
      s4.status = .Running → s4.sp = sp →
      s4.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit opkId? wOpk →
      s4.readReg64 .x0 = idKpFutPtr → s4.readReg64 .x1 = img.base + skit.kpFutVtOff →
      s4.readReg64 .x19 = coroPtr → s4.readReg64 .x21 = v_b0 →
      s4.readReg64 .x23 = coroPtr + 0x4f2#64 → s4.readReg64 .x24 = sp + 0x370#64 →
      s4.readReg64 .x25 = sp + 0x210#64 → s4.readReg64 .x26 = coroPtr + 0x398#64 →
      s4.readReg64 .x27 = ctxPtr → s4.readReg64 .x28 = sp + 0xa90#64 →
      s4.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      img.FrozenLoaded s4 → s4.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s4
        (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
         kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
         pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk opkId? wOpk) ∗
         A.live idKpFutPtr skit.kpBoxSize 8 ∗ skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
         (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
         (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
         ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
         memRegion (coroPtr + 0x100#64) 336 ∗ cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
         ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
           idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkOptTag8 opkId?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
         cells (coroPtr + 0x4f8#64) 2 ∗
         ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
         ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
         ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8') ∗
         ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8') ∗
         ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
         memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
         memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
         cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 65 ∗
         decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
         memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (spkKit.storeAt spkStorePtr stSpk ∗
       kpkKit.storeAt kyberStorePtr stKpk ∗
       pkKit.storeAt preKeyStorePtr stPk ∗
       ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       memRegion (coroPtr + 0x100#64) 336 ∗ cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
       cells (coroPtr + 0x3f8#64) 6 ∗ cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       memRegion (coroPtr + 0x4b1#64) 64 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       cells (coroPtr + 0x4f8#64) 2 ∗
       ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 65 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame)
      Q Qp := by
  refine p2_sepWPp_frame_eq
    (stageP2_sub1_to_3_kits_ext (P := P) (A := A) (F := F) img ext himg hH hPure
      skit spkKit hspkVt hspkOk kpkKit hkpkVt hkpkOk pkKit stk hstk_p2 hstk_lt
      s0 s _ Q hpan
      sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
      v_b0 u_90 u_a8 u_b8 u_d0
      baseKey signedPreKeyId kyberPreKeyId stSpk stKpk
      b_2c0 b_390 b_4f1 b_4f2
      hb hkyber_nz hF hsym hfs hid_spk hspk_wf hid_kpk hkpk_wf
      hpc hrun hsp_eq hsp_align htr hvregs
      hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 ?_ ?_ ?_)
    (by (conv => rhs; simp only [← sepConj_assoc]); sep_focus)
  · intro e spkFutPtr sf P_f hrel hpcf hrunf htrf hspf hcsf hvregsf hinvf hent
    exact hErrSpk e spkFutPtr sf P_f hrel hpcf hrunf htrf hspf hcsf hvregsf hinvf
      (Entails.trans hent (Entails.of_eq (eq_of_sep_emp (by sep_focus))))
  · intro spkRec spkPubBytes spkPrivBytes e kyberFutPtr sf P_f
      hrel_spk hrec_spk hpub_len hpriv_len hpub_eq hpriv_eq hrel_kpk
      hpcf hrunf htrf hspf hcsf hvregsf hinvf hent
    exact hErrKpk spkRec spkPubBytes spkPrivBytes e kyberFutPtr sf P_f
      hrel_spk hrec_spk hpub_len hpriv_len hpub_eq hpriv_eq hrel_kpk
      hpcf hrunf htrf hspf hcsf hvregsf hinvf
      (Entails.trans hent (Entails.of_eq (eq_of_sep_emp (by sep_focus))))
  · intro spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
      pkBuf skBuf kyberFutPtr v90_3 privCap_3 privPtr_3 s3
      hst03 hfs3 hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
      hrel_kpk hrec_kpk hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
      hpkBuf_nz hskBuf_nz hpc3 hrun3 hsp3 htr3
      hx19_3 hx21_3 _ hx23_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
      hvregs3 hF3 hsym3
    have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := hsp3 ▸ hsp_align
    have htr03 : s0.trace <+: s3.trace := by
      rw [htr3]; exact (htr.trans (List.prefix_append _ _)).trans (List.prefix_append _ _)
    refine SepWPp.weaken_frame
      (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt))
      (by sep_focus) ?_
    rw [p2_logOff_eq img]
    cases opkId? with
    | none =>
      dsimp only [opkOptTag32]
      refine p2_sepWPp_frame_eq
        (p2_cut_qpan hpan (stageP2_sub4_none_kits img ext ikit skit hskitVt hskitOk
          stk (Nat.le_trans (p2_kpShim_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2) hstk_lt
          ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x36ac#64)
          s0 s3 _
          (fun sm Pm => SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sm Pm Q Qp)
          coroPtr msgPtr ctxPtr idStorePtr (msgPtr + 0x90#64) v_b0 u_488 opkIdWord b_4b0
          hb hF3 hsym3 hpc3 hrun3 hsp3_align htr03 hvregs3 hx19_3 hx21_3 ?_))
        (by rw [hsp3]; (conv => rhs; simp only [← sepConj_assoc]); sep_focus)
      intro idKpFutPtr s4 hst34 hpc4 hrun4 hsp4 htr4_3 hx0_4 hx1_4 hidKp_nz hidKp_al
        hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
        hvregs4 hF4 hsym4
      refine SepWPp.done hpc4 hrun4 ?_
      try rw [hsp3] at hsp4
      try rw [hsp3] at hx23_4
      try rw [hsp3] at hx24_4
      try rw [hsp3] at hx28_4
      try rw [hsp3]
      have hst04 : Steps (tripleRatchetProgAtExt img.base ext) s s4 := hst03.trans hst34
      have hfs4 := hfs3.of_steps hst34 (evs := []) (by rw [htr4_3, List.append_nil])
        (fun _ => NoFsEv.nil)
      rw [← p2_logOff_eq img]
      refine SepWPp.weaken_frame
        (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
        (by sep_focus) ?_
      refine SepWPp.weaken_frame
        (p2_pair64_4f8_to_cells2 coroPtr kyberFutPtr (img.base + kpkKit.getFutVtOff))
        (by sep_focus) ?_
      refine SepWPp.weaken_frame
        (Entails.of_eq (p2_memRegion_3e0_split_88_280 sp).symm) (by sep_focus) ?_
      refine SepWPp.weaken_frame
        (p2_memRegion64_to_bytes32_pair (coroPtr + 0x4b1#64)) (by sep_focus) ?_
      sep_norm
      refine SepWPp.exists_elim fun opkPkBytes => SepWPp.exists_elim fun opkSkBytes =>
        SepWPp.pure_elim fun ⟨hopkPk_len, hopkSk_len⟩ => ?_
      have hok := hOk spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        (() : OpkOkWitness none) opkPkBytes opkSkBytes
        pkBuf skBuf idKpFutPtr v90_3 3169#64 privCap_3 privPtr_3 s4
        hst04 hfs4 hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
        hrel_kpk hrec_kpk hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
        True.intro hopkPk_len hopkSk_len True.intro
        hpkBuf_nz hskBuf_nz hidKp_nz hidKp_al hpc4 hrun4 hsp4
        (by dsimp only [opkOkEvs]; rw [htr4_3, htr3, List.append_nil])
        hx0_4 hx1_4 hx19_4 hx21_4
        (hx23_4.trans hx23_3) hx24_4 (hx25_4.trans hx25_3) (hx26_4.trans hx26_3)
        hx27_4 (hx28_4.trans hx28_3) (hx29_4.trans hx29_3)
        hvregs4 hF4 hsym4
      dsimp only [opkOkUpdate, opkOptTag8, opkOptTag32] at hok
      exact p2_sepWPp_weaken_eq hok (by sep_focus)
    | some opkId =>
      have hopk_eq : opkIdWord = opkId := hopk_word opkId rfl
      dsimp only [opkOptTag32]
      rw [hopk_eq]
      refine p2_intro_pk_vt hpkVt hF3 ?_
      let Drop_pk : SepProp :=
        ((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (img.base + pkKit.getShimOff)) ∗
        ((img.base + pkKit.getFutVtOff) ↦₆₄ᵣ (img.base + pkKit.getFutDropOff)) ∗
        ((img.base + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
        ((img.base + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + pkKit.getPollOff))
      refine SepWPp.weaken_frame (p2_memRegion8_to_bytes7_1 (sp + 0x3b0#64)) (by sep_focus) ?_
      sep_norm
      refine SepWPp.exists_elim fun s0_b => SepWPp.exists_elim fun s1_b =>
        SepWPp.exists_elim fun s2_b => SepWPp.exists_elim fun s3_b =>
        SepWPp.exists_elim fun s4_b => SepWPp.exists_elim fun s5_b =>
        SepWPp.exists_elim fun s6_b => ?_
      refine SepWPp.weaken_frame (Entails.of_eq (p2_cells8_930_split_56_8 sp)) (by sep_focus) ?_
      refine SepWPp.weaken_frame (p2_memRegion64_to_keyPair64UnalignedAt (coroPtr + 0x4b1#64))
        (by sep_focus) ?_
      sep_norm
      refine SepWPp.exists_elim fun c0_i => SepWPp.exists_elim fun c1_i =>
        SepWPp.exists_elim fun c2_i => SepWPp.exists_elim fun c3_i =>
        SepWPp.exists_elim fun c4_i => SepWPp.exists_elim fun c5_i =>
        SepWPp.exists_elim fun c6_i => SepWPp.exists_elim fun c63_i =>
        SepWPp.exists_elim fun cw0_i => SepWPp.exists_elim fun cw1_i =>
        SepWPp.exists_elim fun cw2_i => SepWPp.exists_elim fun cw3_i =>
        SepWPp.exists_elim fun cw4_i => SepWPp.exists_elim fun cw5_i =>
        SepWPp.exists_elim fun cw6_i => ?_
      refine p2_sepWPp_frame_eq
        (stageP2_sub4_some_kits_ext (P := P) (A := A) (F := F) img ext hH hPure
          pkKit hpkOk ikit skit hskitVt hskitOk
          stk (Nat.le_trans (p2_pure_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2)
          (Nat.le_trans (p2_pkShim_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2)
          (Nat.le_trans (p2_pkPoll_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2)
          (Nat.le_trans (p2_kpShim_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2) hstk_lt
          (s0.readReg64 .x30) s0 s3 _ Q hpan
          coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr (msgPtr + 0x90#64)
          (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 3169#64 privCap_3 privPtr_3
          u_488 kyberFutPtr (img.base + kpkKit.getFutVtOff)
          opkId stPk b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
          c0_i c1_i c2_i c3_i c4_i c5_i c6_i c63_i cw0_i cw1_i cw2_i cw3_i cw4_i cw5_i cw6_i
          hb hF3 hsym3 (fun sm hst htrm => p2_envOk_pk hfs3 hst htrm)
          (hid_pk opkId rfl) (fun r hrel hrec => hpk_wf opkId r rfl hrel hrec)
          hpc3 hrun3 hsp3_align htr03 hvregs3 hx19_3 hx21_3 hx23_3 hx26_3 (hsp3.symm ▸ hx28_3)
          ?_ ?_)
        (by rw [hsp3]; (conv => rhs; simp only [← sepConj_assoc]); sep_focus)
      · -- Arm 3: pkKit .error e at +0x09c4
        intro opkFutPtr e s4 _ hrel_pk hpc4 hrun4 hsp4 htr4_3
          hx19_4 hx21_4 hx23_4 hx25_4 hx26_4 hx27_4 hx28_4 _
          hvregs4 hF4 hsym4
        try rw [hsp3] at hsp4
        try rw [hsp3] at hx28_4
        try rw [hsp3]
        have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := hsp4 ▸ hsp_align
        have hstk_alloc : allocHookStack ≤ stk :=
          Nat.le_trans (p2_allocHookStack_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2
        have hstk_alloc_split := p2_stackAt_split_of_le sp stk allocHookStack hstk_alloc hstk_lt
        rw [← p2_logOff_eq img, ← hopk_eq]
        have h3b0_err :
            bytes7At (sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
              memRegion (sp + 0x3b7#64) 1 ⊢ memRegion (sp + 0x3b0#64) 8 := by
          have ha : (sp + 0x3b0#64) + 7#64 = sp + 0x3b7#64 := by bv_omega
          simpa only [ha] using
            p2_bytes7_1_to_memRegion8 (sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b
        refine SepWPp.weaken_frame
          (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_errArm (A := A) coroPtr)) (by sep_focus) ?_
        refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc_split) (by sep_focus) ?_
        refine SepWPp.weaken_frame
          (p2_pointsToBytes_entails_memRegion pkBuf kyberPubBytes 1568 hkyber_pub_len)
          (by sep_focus) ?_
        refine SepWPp.weaken_frame
          (p2_pointsToBytes_entails_memRegion skBuf kyberPrivBytes 3168 hkyber_priv_len)
          (by sep_focus) ?_
        refine SepWPp.weaken_frame h3b0_err (by sep_focus) ?_
        refine SepWPp.weaken_frame
          (Entails.of_eq (p2_memRegion_3e0_split_88_280 sp).symm) (by sep_focus) ?_
        refine SepWPp.weaken_frame
          (Entails.of_eq (p2_cells8_930_split_56_8 sp).symm) (by sep_focus) ?_
        refine SepWPp.weaken_frame
          (p2_keyPair64UnalignedAt_to_memRegion (coroPtr + 0x4b1#64)
            c0_i c1_i c2_i c3_i c4_i c5_i c6_i c63_i cw0_i cw1_i cw2_i cw3_i cw4_i cw5_i cw6_i)
          (by sep_focus) ?_
        refine SepWPp.weaken_frame
          (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
          (by sep_focus) ?_
        have harm3 := p2_arm3_err_hooks_ok (Qp := fun _ _ => False) hH hpkOk s0 s4
          sp coroPtr outPtr 0#64 8#64 preKeyStorePtr opkFutPtr pkBuf skBuf ctxPtr
          v_b0 (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) 3169#64 v_b0 privCap_3 ctxPtr privPtr_3
          opkId b_2c0 b_390 b_4f2 e hb (by decide) ⟨hF4, hsym4⟩ hsp4
          hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx23_4 (hx25_4.trans hx25_3) hx26_4 hx27_4 hx28_4
          hvregs4
        refine p2_finish_err_arm_drop (Drop := Drop_pk) harm3 (by sep_focus) ?_
          (fun sf P_f _ hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hinvf⟩ =>
            hErrPk spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
              opkId e pkBuf skBuf opkFutPtr v90_3 sf P_f
              hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
              hrel_kpk hrec_kpk hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
              rfl hrel_pk hpcf hrunf (by rw [htrf, htr4_3, htr3])
              hspf hcsf hvregsf hinvf hent)
        dsimp only [Drop_pk, opkOptTag32]
        rw [hstk_alloc_split, ← p2_ac0_join_16_1 sp]
        exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
      · -- Substage 4 .ok -> hOk at +0x36ac
        intro opkRec opkPubBytes opkPrivBytes opkFutPtr idKpFutPtr privCap_4 privPtr_4
          b0_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b63_4 c0_4 c1_4 c2_4 c3_4 c4_4 c5_4 c6_4
          w0_4 w1_4 w2_4 w3_4 w4_4 w5_4 w6_4 u0_o u1_o u2_o u3_o u4_o u5_o u6_o u7_o
          s4 hst34 hrel_pk hrec_pk hopk_pub_len hopk_priv_len hopk_pub_eq hopk_priv_eq
          hopk_pub_w hopk_priv_w hopk_lo hopk_hi
          hpc4 hrun4 hsp4 htr4_3 hx0_4 hx1_4 hidKp_nz hidKp_al
          hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
          hvregs4 hF4 hsym4
        try rw [hsp3] at hsp4
        try rw [hsp3] at hx24_4
        try rw [hsp3] at hx28_4
        try rw [hsp3]
        have hst04 : Steps (tripleRatchetProgAtExt img.base ext) s s4 := hst03.trans hst34
        have hfs4 := p2_fsAt_step_pk opkId (.ok opkRec) hfs3 hst34 htr4_3
        rw [← p2_logOff_eq img, ← hopk_eq]
        refine SepWPp.weaken_frame
          (Entails.of_eq (p2_keyPair64UnalignedAt_eq_bytes32_pair (coroPtr + 0x4b1#64)
            opkPubBytes opkPrivBytes
            b0_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b63_4 c0_4 c1_4 c2_4 c3_4 c4_4 c5_4 c6_4
            w0_4 w1_4 w2_4 w3_4 w4_4 w5_4 w6_4 u0_o u1_o u2_o u3_o u4_o u5_o u6_o u7_o
            hopk_pub_w hopk_priv_w hopk_lo hopk_hi))
          (by sep_focus) ?_
        sep_norm
        have h3b0_ok :
            bytes7At (sp + 0x3b0#64) b0_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 ∗
              memRegion (sp + 0x3b7#64) 1 ⊢ memRegion (sp + 0x3b0#64) 8 := by
          have ha : (sp + 0x3b0#64) + 7#64 = sp + 0x3b7#64 := by bv_omega
          simpa only [ha] using
            p2_bytes7_1_to_memRegion8 (sp + 0x3b0#64) b0_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4
        refine SepWPp.weaken_frame h3b0_ok (by sep_focus) ?_
        refine SepWPp.weaken_frame
          (Entails.of_eq (p2_memRegion_3e0_split_88_280 sp).symm) (by sep_focus) ?_
        refine SepWPp.weaken_frame
          (Entails.of_eq (p2_cells8_930_split_56_8 sp).symm) (by sep_focus) ?_
        refine SepWPp.weaken_frame
          (p2_pair64_4f8_to_cells2 coroPtr opkFutPtr (img.base + pkKit.getFutVtOff))
          (by sep_focus) ?_
        refine SepWPp.weaken_frame
          (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
          (by sep_focus) ?_
        refine p2_drop_frame_mid (Drop := Drop_pk) (by dsimp only [Drop_pk]; sep_focus) ?_
        have hok := hOk spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
          (opkRec : OpkOkWitness (some opkId)) opkPubBytes (clampBv8List opkPrivBytes)
          pkBuf skBuf idKpFutPtr v90_3 32#64 privCap_4 privPtr_4 s4
          hst04 hfs4 hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
          hrel_kpk hrec_kpk hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
          ⟨hrel_pk, hrec_pk⟩ hopk_pub_len (clampBv8List_length hopk_priv_len)
          ⟨opkPrivBytes, hopk_priv_len, hopk_pub_eq, hopk_priv_eq, rfl⟩
          hpkBuf_nz hskBuf_nz hidKp_nz hidKp_al hpc4 hrun4 hsp4
          (by dsimp only [opkOkEvs]; rw [htr4_3, htr3])
          hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4
          (hx25_4.trans hx25_3) hx26_4 hx27_4 hx28_4 (hx29_4.trans hx29_3)
          hvregs4 hF4 hsym4
        dsimp only [opkOkUpdate, opkOptTag8, opkOptTag32] at hok
        exact p2_sepWPp_weaken_eq hok (by sep_focus)

abbrev stageP2_sub1_to_4_kits_4k := @stageP2_sub1_to_4_kits_ext

/-- Kit-generic Stage P2 Substages 1–4 (`+0x0868 -> +0x36ac` or error exit to `s0.readReg64 .x30`). -/
theorem stageP2_sub1_to_4_kits {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext) (hPure : StageP2PureCallees P A F img ext) :
    ∀ (ikit : IdentityStoreSpec A img.base) (skit : IdentitySelfStoreSpec ikit)
      (_hskitVt : IdentitySelfVtablesOk img ikit skit)
      (_hskitOk : IdentitySelfStoreKitOkI img ikit skit ext)
      (spkKit : SignedPreKeyStoreSpec A img.base)
      (_hspkVt : SignedPreKeyVtablesOk img spkKit) (_hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
      (kpkKit : KyberPreKeyStoreSpec A img.base)
      (_hkpkVt : KyberPreKeyVtablesOk img kpkKit) (_hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
      (pkKit : PreKeyStoreSpec A img.base)
      (_hpkVt : PreKeyVtablesOk img pkKit) (_hpkOk : PreKeyStoreKitOkImgE img pkKit ext)
      (stk : Nat) (_hstk_p2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk) (_hstk_lt : stk ≤ 2 ^ 64)
      (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
      {Qp : State → SepProp → Prop} (_hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
      (sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
       idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
       v_b0 u_90 u_a8 u_b8 u_d0 u_488 : BitVec 64)
      (baseKey : PublicKey) (signedPreKeyId kyberPreKeyId opkIdWord : BitVec 32)
      (opkId? : Option (BitVec 32))
      (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState)
      (b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
      (_hb : img.base &&& 0xfff#64 = 0#64) (_hkyber_nz : kyberCtCap ≠ 0#64)
      (_hF : img.FrozenLoaded s) (_hsym : s.symtab = img.symtab)
      (_hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
        (stageP2Quiet spkKit kpkKit pkKit skit) (tripleRatchetProgAtExt img.base ext) s)
      (_hid_spk : spkKit.idOk signedPreKeyId)
      (_hspk_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) →
        spkKit.RecOk r →
        ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
          spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
          r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
      (_hid_kpk : kpkKit.getIdOk kyberPreKeyId)
      (_hkpk_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
        kpkKit.RecOk r →
        ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
          kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
          r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
          r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
      (_hopk_word : ∀ id : BitVec 32, opkId? = some id → opkIdWord = id)
      (_hid_pk : ∀ id : BitVec 32, opkId? = some id → pkKit.getIdOk id)
      (_hpk_wf : ∀ (id : BitVec 32) (r : PreKeyRecord), opkId? = some id →
        pkKit.getRel stPk id (.ok r) → pkKit.RecOk r →
        ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
          opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
          r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes)
      (_hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64)
      (_hrun : s.status = .Running) (_hsp_eq : s.sp = sp)
      (_hsp_align : (sp &&& 15#64 == 0#64) = true)
      (_htr : s0.trace <+: s.trace) (_hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
      (_hx8 : s.readReg64 .x8 = kyberStorePtr) (_hx9 : s.readReg64 .x9 = msgPtr)
      (_hx10 : s.readReg64 .x10 = kpkKit.kpk_vt) (_hx11 : s.readReg64 .x11 = preKeyStorePtr)
      (_hx12 : s.readReg64 .x12 = remoteAddrPtr) (_hx13 : s.readReg64 .x13 = pkKit.pk_vt)
      (_hx14 : s.readReg64 .x14 = localAddrPtr) (_hx15 : s.readReg64 .x15 = idStorePtr)
      (_hx16 : s.readReg64 .x16 = ikit.id_vt) (_hx19 : s.readReg64 .x19 = coroPtr)
      (_hx22 : s.readReg64 .x22 = spkStorePtr) (_hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
      (_hx24 : s.readReg64 .x24 = spkKit.spk_vt)
      (_hErrSpk : ∀ (e : spkKit.GetErr) (spkFutPtr : BitVec 64) (sf : State) (P_f : SepProp),
        spkKit.getRel stSpk signedPreKeyId (.error e) →
        sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) →
        sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
        (P_f ⊢
          speErrAt spkKit.getErr outPtr e ∗
          spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
          kpkKit.storeAt kyberStorePtr stKpk ∗
          pkKit.storeAt preKeyStorePtr stPk ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
          ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
          memRegion (coroPtr + 0x4b1#64) 64 ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
          ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
          ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
          ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
          ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
          memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
          memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
          cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame) →
        Q sf P_f)
      (_hErrKpk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (e : kpkKit.GetErr) (kyberFutPtr : BitVec 64) (sf : State) (P_f : SepProp),
        spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
        spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
        spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
        spkRec.signedPreKey.privateKey = spkPrivBytes →
        kpkKit.getRel stKpk kyberPreKeyId (.error e) →
        sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
          kpkKit.getEvs kyberPreKeyId (.error e) →
        sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
        (P_f ⊢
          speErrAt kpkKit.getErr outPtr e ∗
          spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
          kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
          pkKit.storeAt preKeyStorePtr stPk ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
          ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
          cells (coroPtr + 0x3d8#64) 4 ∗
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
          ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
          memRegion (coroPtr + 0x4b1#64) 64 ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
          ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
          ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
          ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
          ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
          memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
          memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
          cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame) →
        Q sf P_f)
      (_hErrPk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (opkId : BitVec 32) (e : pkKit.GetErr) (pkBuf skBuf opkFutPtr v90 : BitVec 64)
        (sf : State) (P_f : SepProp),
        spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
        spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
        spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
        spkRec.signedPreKey.privateKey = spkPrivBytes →
        kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
        kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
        kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
        kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
        opkId? = some opkId → pkKit.getRel stPk opkId (.error e) →
        sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
          kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ pkKit.getEvs opkId (.error e) →
        sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
        (P_f ⊢
          speErrAt pkKit.getErr outPtr e ∗
          spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
          kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
          pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
          ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
          ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
          memRegion (coroPtr + 0x4b1#64) 64 ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + pkKit.getFutVtOff)) ∗
          ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
          ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
          ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ pkKit.getErr.w4 e) ∗
          ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ pkKit.getErr.w2 e) ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ pkKit.getErr.w3 e) ∗
          memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
          memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
          cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame) →
        Q sf P_f)
      (_hOk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness opkId?) (opkPkBytes opkSkBytes : List (BitVec 8))
        (pkBuf skBuf idKpFutPtr v90 v_a8' v_b8' v_d0' : BitVec 64) (s4 : State),
        Steps (tripleRatchetProgAtExt img.base ext) s s4 →
        FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
          (stageP2Quiet spkKit kpkKit pkKit skit) (tripleRatchetProgAtExt img.base ext) s4 →
        spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
        spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
        spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
        spkRec.signedPreKey.privateKey = spkPrivBytes →
        kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
        kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
        kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
        kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
        opkOkRel pkKit stPk opkId? wOpk →
        opkPkBytes.length = 32 → opkSkBytes.length = 32 →
        opkOkKeyBytes opkId? wOpk opkPkBytes opkSkBytes →
        pkBuf ≠ 0#64 → skBuf ≠ 0#64 → idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
        s4.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x36ac#64 →
        s4.status = .Running → s4.sp = sp →
        s4.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
          kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit opkId? wOpk →
        s4.readReg64 .x0 = idKpFutPtr → s4.readReg64 .x1 = img.base + skit.kpFutVtOff →
        s4.readReg64 .x19 = coroPtr → s4.readReg64 .x21 = v_b0 →
        s4.readReg64 .x23 = coroPtr + 0x4f2#64 → s4.readReg64 .x24 = sp + 0x370#64 →
        s4.readReg64 .x25 = sp + 0x210#64 → s4.readReg64 .x26 = coroPtr + 0x398#64 →
        s4.readReg64 .x27 = ctxPtr → s4.readReg64 .x28 = sp + 0xa90#64 →
        s4.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs s4 = calleeSavedVRegs s0 →
        img.FrozenLoaded s4 → s4.symtab = img.symtab →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s4
          (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
           kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
           pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk opkId? wOpk) ∗
           A.live idKpFutPtr skit.kpBoxSize 8 ∗ skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
           (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
           (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
           ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
           memRegion (coroPtr + 0x100#64) 336 ∗ cells (coroPtr + 0x250#64) 6 ∗
           ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
           ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
           ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
           ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
           ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
           processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
             idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
           ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
           ((coroPtr + 0x4b0#64) ↦₈ opkOptTag8 opkId?) ∗
           ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
           ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
           cells (coroPtr + 0x4f8#64) 2 ∗
           ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
           ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
           ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
           ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
           ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
           ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8') ∗
           ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8') ∗
           ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
           ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
           memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
           memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
           cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 65 ∗
           decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
           memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame)
          Q Qp),
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (spkKit.storeAt spkStorePtr stSpk ∗
         kpkKit.storeAt kyberStorePtr stKpk ∗
         pkKit.storeAt preKeyStorePtr stPk ∗
         ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
         memRegion (coroPtr + 0x100#64) 336 ∗ cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
         cells (coroPtr + 0x3f8#64) 6 ∗ cells (coroPtr + 0x468#64) 4 ∗
         ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗ ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
         memRegion (coroPtr + 0x4b1#64) 64 ∗
         ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
         cells (coroPtr + 0x4f8#64) 2 ∗
         ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 opkId?) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
         ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
         ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
         memRegion (sp + 0x3b0#64) 8 ∗ memRegion (sp + 0x3e0#64) 368 ∗
         cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 65 ∗
         decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
         memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame)
        Q Qp :=
  stageP2_sub1_to_4_kits_ext img ext himg
    (StageP2ClosureHooks.of_allocContracts hA) hPure.to_4K

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
