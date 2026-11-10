/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB6
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub6Aux

/-!
# Stage P2 Substage P2.6 at SPQR V1

Proves kit-parameterized Substage P2.6 (`+0x125c → +0x1778` on `Ok`, or `+0x09f4` Arm 6 on
`get_local_registration_id` error) for any 280-byte session middle `mid` (`mid.length = 280`) on
`tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

/-! ## 1. Stack Scratch (`sp + 0x3e0..0x538`) & Kit Precondition Helpers for P2.6 -/

/-- Six 64-bit words at `sp + 0x3e0..0x410` weaken to `memRegion (sp + 0x3e0) 48` for
`kitRegIdPollSpec`. -/
theorem p2_sp3e0_words6_entails_memRegion48 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₆₄ w1) ∗
    ((sp + 0x3f0#64) ↦₆₄ w2) ∗ ((sp + 0x3f8#64) ↦₆₄ w3) ∗
    ((sp + 0x400#64) ↦₆₄ w4) ∗ ((sp + 0x408#64) ↦₆₄ w5) ⊢
      memRegion (sp + 0x3e0#64) 48 := by
  have h1 := sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3e0#64) w0)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3e8#64) w1)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3f0#64) w2)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3f8#64) w3)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x400#64) w4)
      (pointsTo64_entails_memRegion (sp + 0x408#64) w5)))))
  have hm :
      memRegion (sp + 0x3e0#64) 8 ∗ (memRegion (sp + 0x3e8#64) 8 ∗
      (memRegion (sp + 0x3f0#64) 8 ∗ (memRegion (sp + 0x3f8#64) 8 ∗
      (memRegion (sp + 0x400#64) 8 ∗ memRegion (sp + 0x408#64) 8)))) =
      memRegion (sp + 0x3e0#64) 48 := by
    rw [(ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 8) (k := 8)
          (b' := sp + 0x408#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 16)
          (b' := sp + 0x400#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 24)
          (b' := sp + 0x3f8#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 8) (k := 32)
          (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 40)
          (b' := sp + 0x3e8#64) rfl (by bv_omega) (by decide)).symm]
  exact hm ▸ h1

/-- `((sp + 0x410) ↦₆₄ w6) ∗ ((sp + 0x418) ↦ₛ ssRest)` (with `ssRest.length = 288`) weakens to
`memRegion (sp + 0x410) 296`. -/
theorem p2_sp410_word_bytes288_entails_memRegion296 (sp w6 : BitVec 64)
    (ssRest : List (BitVec 8)) (hlen : ssRest.length = 288) :
    ((sp + 0x410#64) ↦₆₄ w6) ∗ ((sp + 0x418#64) ↦ₛ ssRest) ⊢
      memRegion (sp + 0x410#64) 296 := by
  have h1 := sepConj_mono (pointsTo64_entails_memRegion (sp + 0x410#64) w6)
    (hlen ▸ ProofLib.pointsToBytes_entails_memRegion (sp + 0x418#64) ssRest)
  have hm : memRegion (sp + 0x410#64) 8 ∗ memRegion (sp + 0x418#64) 288 =
      memRegion (sp + 0x410#64) 296 :=
    (ProofLib.memRegion_split' (b := sp + 0x410#64) (n := 8) (k := 288)
      (b' := sp + 0x418#64) rfl (by bv_omega) (by decide)).symm
  exact hm ▸ h1

/-- Split the 36-byte trailing padding `memRegion (sp + 0x3ec) 36` of `regIdPollOutAt (.ok reg)`
into `(sp + 0x3ec ↦₃₂ u_3ec)` and four 64-bit words at `sp + 0x3f0..0x408` for `p2_seg6c_ext_wp`. -/
theorem p2_sp3ec_36_split_for_seg6c (sp : BitVec 64) :
    memRegion (sp + 0x3ec#64) 36 =
      ∃∗ u_3ec : BitVec 32, ∃∗ u_3f0 : BitVec 64, ∃∗ u_3f8 : BitVec 64,
      ∃∗ u_400 : BitVec 64, ∃∗ u_408 : BitVec 64,
        ((sp + 0x3ec#64) ↦₃₂ u_3ec) ∗
        ((sp + 0x3f0#64) ↦₆₄ u_3f0) ∗ ((sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
        ((sp + 0x400#64) ↦₆₄ u_400) ∗ ((sp + 0x408#64) ↦₆₄ u_408) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3ec#64) (n := 4) (k := 32)
        (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 24)
        (b' := sp + 0x3f8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 16)
        (b' := sp + 0x400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 8) (k := 8)
        (b' := sp + 0x408#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_four,
      ProofLib.memRegion_eight,
      ProofLib.memRegion_eight,
      ProofLib.memRegion_eight,
      ProofLib.memRegion_eight]
  simp only [sepConj_assoc, sepExists_sepConj_left]
  simp only [sepExists_sepConj_right, sepConj_assoc]

/-- Weaken the 48-byte `sp + 0x3e0..0x410` post-`seg6c` slot plus `memRegion (sp + 0x410) 296`
into `memRegion (sp + 0x3e0) 344`. -/
theorem p2_sp3e0_after_seg6c_entails_344 (sp w0 u_3f0 u_3f8 u_400 u_408 : BitVec 64)
    (reg u_3ec : BitVec 32) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₃₂ reg) ∗ ((sp + 0x3ec#64) ↦₃₂ u_3ec) ∗
    ((sp + 0x3f0#64) ↦₆₄ u_3f0) ∗ ((sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
    ((sp + 0x400#64) ↦₆₄ u_400) ∗ ((sp + 0x408#64) ↦₆₄ u_408) ∗
    memRegion (sp + 0x410#64) 296 ⊢ memRegion (sp + 0x3e0#64) 344 := by
  have h1 := sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3e0#64) w0)
    (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x3e8#64) reg)
    (sepConj_mono (pointsTo32_entails_memRegion (sp + 0x3ec#64) u_3ec)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3f0#64) u_3f0)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3f8#64) u_3f8)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x400#64) u_400)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x408#64) u_408)
      (Entails.refl (memRegion (sp + 0x410#64) 296))))))))
  have hm :
      memRegion (sp + 0x3e0#64) 8 ∗ (memRegion (sp + 0x3e8#64) 4 ∗
      (memRegion (sp + 0x3ec#64) 4 ∗ (memRegion (sp + 0x3f0#64) 8 ∗
      (memRegion (sp + 0x3f8#64) 8 ∗ (memRegion (sp + 0x400#64) 8 ∗
      (memRegion (sp + 0x408#64) 8 ∗ memRegion (sp + 0x410#64) 296)))))) =
      memRegion (sp + 0x3e0#64) 344 := by
    rw [(ProofLib.memRegion_split' (b := sp + 0x408#64) (n := 8) (k := 296)
          (b' := sp + 0x410#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 8) (k := 304)
          (b' := sp + 0x408#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 312)
          (b' := sp + 0x400#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 320)
          (b' := sp + 0x3f8#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3ec#64) (n := 4) (k := 328)
          (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 4) (k := 332)
          (b' := sp + 0x3ec#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 336)
          (b' := sp + 0x3e8#64) rfl (by bv_omega) (by decide)).symm]
  exact hm ▸ h1

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_regIdShim_le_sub56 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    skit.regIdShimStack ≤ stageP2Sub56Stack skit :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem p2_regIdPoll_le_sub56 {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    skit.regIdPollStack ≤ stageP2Sub56Stack skit :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)

theorem p2_regIdShim_pre_intro {A : RustAlloc} {img : Obj.Image}
    {ikit : IdentityStoreSpec A img.base} (skit : IdentitySelfStoreSpec ikit)
    {self : BitVec 64} {s : State}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = self) :
    A.pool ∗ stackAt s.sp skit.regIdShimStack ⊢
      ((kitRegIdShimSpec skit).inImage img).pre self s := by
  dsimp only [Spec.inImage, kitRegIdShimSpec]
  refine Entails.pure_right ⟨hF, hsym⟩ ?_
  refine Entails.pure_right hx0 ?_
  exact Entails.refl _

theorem p2_regIdPoll_pre_intro {A : RustAlloc} {img : Obj.Image}
    {ikit : IdentityStoreSpec A img.base} (skit : IdentitySelfStoreSpec ikit)
    {fut out self : BitVec 64} {ist0 : ikit.IdState} {s : State}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (henv : ikit.envOk s.fs.files)
    (hx0 : s.readReg64 .x0 = fut) (hx8 : s.readReg64 .x8 = out) :
    (skit.regIdBoxAt fut self 0#8 ∗ ikit.identityAt self ist0 ∗
      memRegion out 48 ∗ A.pool ∗ stackAt s.sp skit.regIdPollStack) ∗ logOff img ⊢
      (kitRegIdPollSpecI img skit).pre (fut, out, self, ist0) s := by
  dsimp only [kitRegIdPollSpecI, Spec.inImage, withLogOff, kitRegIdPollSpecE, withEnvPre,
    kitRegIdPollSpec]
  refine Entails.pure_right ⟨hF, hsym⟩ ?_
  refine sepConj_mono_left ?_
  refine Entails.pure_right henv ?_
  refine Entails.pure_right ⟨hx0, hx8⟩ ?_
  exact Entails.refl _

theorem p2_coro4f8_344_split_words7_288 (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x4f8#64) 344 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
      ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64,
        ((coroPtr + 0x4f8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x500#64) ↦₆₄ u1) ∗
        ((coroPtr + 0x508#64) ↦₆₄ u2) ∗ ((coroPtr + 0x510#64) ↦₆₄ u3) ∗
        ((coroPtr + 0x518#64) ↦₆₄ u4) ∗ ((coroPtr + 0x520#64) ↦₆₄ u5) ∗
        ((coroPtr + 0x528#64) ↦₆₄ u6) ∗ memRegion (coroPtr + 0x530#64) 288 := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x4f8#64) (n := 8) (k := 336)
        (b' := coroPtr + 0x500#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x500#64) (n := 8) (k := 328)
        (b' := coroPtr + 0x508#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x508#64) (n := 8) (k := 320)
        (b' := coroPtr + 0x510#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x510#64) (n := 8) (k := 312)
        (b' := coroPtr + 0x518#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x518#64) (n := 8) (k := 304)
        (b' := coroPtr + 0x520#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x520#64) (n := 8) (k := 296)
        (b' := coroPtr + 0x528#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x528#64) (n := 8) (k := 288)
        (b' := coroPtr + 0x530#64) rfl (by bv_omega) (by decide)]
  simp only [ProofLib.memRegion_eight, sepConj_assoc, sepExists_sepConj_left]
  simp only [sepExists_sepConj_right, sepConj_assoc]

/-! ## 2. Substage P2.6 (`+0x125c -> +0x1778` / `+0x09f4` Arm 6) -/

set_option maxHeartbeats 1200000 in
/-- Kit-Parameterized Substage P2.6 (`+0x125c -> +0x1778` / `+0x09f4` Arm 6, 4K/`Ext` `StageP2ClosureHooks`):
Copies Bob's 344-byte `SessionState` from `sp + 0x3e0` to `coroPtr + 0x4f8`, calls
`IdentityKeyStore::get_local_registration_id` shim and poll:
- `.error e`: invokes `hErr` at `+0x09f4` (Arm 6),
- `.ok localRegId`: drops/frees the future box and runs `stageP2_sub6_tail_v1_kits_ext` to `+0x1778`. -/
theorem stageP2_sub6_v1_kits_ext
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A img.base} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooks A img.base ext)
    (hskitOk : IdentitySelfStoreKitOkI img ikit skit ext)
    (hskitVt : IdentitySelfVtablesOk img ikit skit)
    (hPure : StageP2PureCallees4K P A F img ext)
    (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (stId : ikit.IdState)
    (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr outPtr
     idStorePtr kyberKpPubPtr kyberKpSecPtr ctBufPtr
     p1 p2 v_330 v_388 u_650
     u_298 u_2a0 u_80 u_88 u_90 u_a8 u_b8 u_d0
     u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (mid : List (BitVec 8)) (hmid : mid.length = 280)
    (remoteRegId opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2a8 : BitVec 32)
    (msgVerByte b_4f2 b_390 b_3ac : BitVec 8)
    (stk : Nat) (F_rest : SepProp)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hwell : WellSizedAcceptKeysInput inp)
    (hctBuf_nz : ctBufPtr ≠ 0#64)
    (hstk_sub56 : stageP2Sub56Stack skit ≤ stk)
    (hstk_lt : stk ≤ sp.toNat)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x125c#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (henv_s : ∀ s3 : State, s3.trace = s.trace →
      Steps (tripleRatchetProgAtExt img.base ext) s s3 → ikit.envOk s3.fs.files)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hOk : ∀ (localRegId : BitVec 32) (regIdFutPtr : BitVec 64) (sf : State),
      skit.regIdRel stId (.ok localRegId) →
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1778#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace ++ skit.regIdEvs (.ok localRegId) →
      sf.readReg64 .x8 = coroPtr + 0xe0#64 →
      sf.readReg64 .x9 = 8#64 →
      sf.readReg64 .x10 = msgVerByte.zeroExtend 64 →
      sf.readReg64 .x11 = coroPtr + 0xf8#64 →
      sf.readReg64 .x19 = coroPtr →
      sf.readReg64 .x20 = 0xfffffffffffffffe#64 →
      sf.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 →
      sf.readReg64 .x23 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) →
      sf.readReg64 .x24 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = v_330 →
      sf.readReg64 .x27 = sp + 0x370#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
         ((coroPtr + 0xe8#64) ↦₆₄ 8#64) ∗
         ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
         ((coroPtr + 0xf8#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++
           (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
         ((coroPtr + 0x4f8#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++
           (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
         ((sp + 0x3e0#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++
           (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
         ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
         ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ikit.identityAt idStorePtr stId ∗
         ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
         ((coroPtr + 0x790#64) ↦₆₄ (img.base + skit.regIdFutVtOff)) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
         ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
         ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
         ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x738#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         ((coroPtr + 0x740#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         opkOptFieldAt (coroPtr + 0x761#64) inp.opkBSk? ∗
         ((coroPtr + 0x781#64) ↦₈ 0#8) ∗
         ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
         ((coroPtr + 0x658#64) ↦ₛ bytesToBv8 ikBPk) ∗
         ((coroPtr + 0x678#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
         ((coroPtr + 0x6b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
         ((coroPtr + 0x6d8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         ((coroPtr + 0x6f8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
         ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
         ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
         ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
         cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x298#64) ↦₆₄ (opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32))) ∗
         ((coroPtr + 0x2a0#64) ↦₆₄ ((kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64)) ∗
         ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
         ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
         ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
         ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
         ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
         ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗
         ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
         ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
         ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
         (ctBufPtr ↦₈ 8#8) ∗
         ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
         ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
         ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
         ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((sp + 0x90#64) ↦₆₄ v_388) ∗
         ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
         ((sp + 0xa8#64) ↦₆₄ v_330) ∗
         ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗
         ((sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
         memRegion (sp + 0xbc#64) 4 ∗
         ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
         ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
         ((sp + 0x3ac#64) ↦₈ 3#8) ∗
         ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
         ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
         ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
         ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
         ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
         ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
         memRegion (sp + 0xa90#64) 288 ∗
         logOff img ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
        Q Qp)
    (hErr : ∀ (e : skit.RegIdErr) (regIdFutPtr : BitVec 64) (s4 : State),
      skit.regIdRel stId (.error e) →
      Steps (tripleRatchetProgAtExt img.base ext) s s4 →
      s4.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x9f4#64 →
      s4.status = .Running →
      s4.sp = sp →
      s4.trace = s.trace ++ skit.regIdEvs (.error e) →
      s4.readReg64 .x19 = coroPtr →
      s4.readReg64 .x21 = coroPtr + 0x390#64 →
      s4.readReg64 .x23 = coroPtr + 0x4f2#64 →
      s4.readReg64 .x25 = s.readReg64 .x25 →
      s4.readReg64 .x26 = coroPtr + 0x398#64 →
      s4.readReg64 .x27 = ctxPtr →
      s4.readReg64 .x28 = s.readReg64 .x28 →
      s4.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      img.FrozenLoaded s4 →
      s4.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s4
        (regIdPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
         memRegion (sp + 0x410#64) 296 ∗
         memRegion (sp + 0xa90#64) 288 ∗
         ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
         ((coroPtr + 0x790#64) ↦₆₄ (img.base + skit.regIdFutVtOff)) ∗
         A.live regIdFutPtr skit.regIdBoxSize 8 ∗
         skit.regIdBoxAt regIdFutPtr idStorePtr 1#8 ∗
         ikit.identityAt idStorePtr stId ∗
         ((img.base + skit.regIdFutVtOff) ↦₆₄ᵣ (img.base + skit.regIdFutDropOff)) ∗
         ((img.base + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
         ((img.base + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((coroPtr + 0x4f8#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ unpack64 0#64))) ∗
         ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
         bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
           (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
         ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
         ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗ cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗ ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
         ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗ ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
         ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗ ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗ ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
         ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗
         ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
         ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
         ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
         ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
         ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
         A.live kyberKpPubPtr 1568 1 ∗ memRegion kyberKpPubPtr 1568 ∗
         A.live kyberKpSecPtr 3168 1 ∗
         logOff img ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
         (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
       ((sp + 0x3e0#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ unpack64 0#64))) ∗
       memRegion (sp + 0xa90#64) 288 ∗
       memRegion (coroPtr + 0x4f8#64) 344 ∗
       ((coroPtr + 0x650#64) ↦₆₄ u_650) ∗
       memRegion (coroPtr + 0x788#64) 16 ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
       ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
       ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
       ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
       ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
       ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
       A.live kyberKpPubPtr 1568 1 ∗ memRegion kyberKpPubPtr 1568 ∗
       A.live kyberKpSecPtr 3168 1 ∗
       logOff img ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
      Q Qp := by
  subst hsp_eq
  have hstk_le64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt s.sp.isLt)
  have hrest_len : (mid ++ unpack64 0#64).length = 288 := by simp [hmid, unpack64]
  refine p2_ro_intro_sub6 (hskitVt.regIdSlot hF) ?_
  refine p2_ro_intro_sub6 (hskitVt.regIdFutDrop hF) ?_
  refine p2_ro_intro_sub6 (hskitVt.regIdFutSize hF) ?_
  refine p2_ro_intro_sub6 (hskitVt.regIdFutAlign hF) ?_
  refine p2_ro_intro_sub6 (hskitVt.regIdFutPoll hF) ?_
  have hsp3e0_split :
      ((s.sp + 0x3e0#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ unpack64 0#64))) =
      ((s.sp + 0x3e0#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x3e8#64) ↦₆₄ p1) ∗
      ((s.sp + 0x3f0#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x3f8#64) ↦₆₄ 33#64) ∗
      ((s.sp + 0x400#64) ↦₆₄ p2) ∗ ((s.sp + 0x408#64) ↦₆₄ 33#64) ∗
      ((s.sp + 0x410#64) ↦₆₄ 32#64) ∗ ((s.sp + 0x418#64) ↦ₛ (mid ++ unpack64 0#64)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      p2_sub6_bobSession344_split_56_288 (s.sp + 0x3e0#64) p1 p2 mid
  refine SepWPp.weaken_frame (Entails.of_eq hsp3e0_split) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_coro4f8_344_split_words7_288 coroPtr))
    (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_4f8 => SepWPp.exists_elim fun u_500 =>
    SepWPp.exists_elim fun u_508 => SepWPp.exists_elim fun u_510 =>
    SepWPp.exists_elim fun u_518 => SepWPp.exists_elim fun u_520 =>
    SepWPp.exists_elim fun u_528 => ?_
  have hc788 : memRegion (coroPtr + 0x788#64) 16 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64,
        ((coroPtr + 0x788#64) ↦₆₄ u0) ∗ ((coroPtr + 0x790#64) ↦₆₄ u1) := by
    rw [ProofLib.memRegion_split' (b := coroPtr + 0x788#64) (n := 8) (k := 8)
          (b' := coroPtr + 0x790#64) rfl (by bv_omega) (by decide)]
    simp only [ProofLib.memRegion_eight, sepConj_assoc, sepExists_sepConj_left]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc788) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_788 => SepWPp.exists_elim fun u_790 => ?_
  have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
    (Nat.le_trans (p2_alloc_le_sub56_sub6 skit) hstk_sub56) hstk_le64
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hstep1 := p2_seg6a_hooks_wp img.base ext hH s coroPtr idStorePtr ikit.id_vt
    (img.base + skit.regIdShimOff)
    33#64 p1 33#64 33#64 p2 33#64 32#64
    u_4f8 u_500 u_508 u_510 u_518 u_520 u_528 u_650
    (mid ++ unpack64 0#64)
    (by decide) hrest_len hpc hrun hsp_align hx19
  refine p2_bind_sepWP_steps_frame_qpan hF hsym hstep1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, _, _, _, _, _, hx25_1, _, _, hx28_1, hx29_1,
    hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_shim := p2_stackAt_split_of_le s.sp stk skit.regIdShimStack
    (Nat.le_trans (p2_regIdShim_le_sub56 skit) hstk_sub56) hstk_le64
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim) (by sep_focus) ?_
  sep_norm
  refine p2_call_oom_steps_frame_qpan (x := idStorePtr)
    hpan hF1 hsym1 (htr1 ▸ htr) hskitOk.regIdShim hpc1 hrun1 hsp1_al hx30_1
    (hsp1 ▸ p2_regIdShim_pre_intro skit hF1 hsym1 hx0_1)
    (by sep_focus) (fun _ => Entails.refl _)
    (hnext := fun s2 hst12 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  dsimp only [Spec.inImage, kitRegIdShimSpec]
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, _, hx25_cs2, _, _, hx28_cs2, hx29_cs2, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_2, _, _, htr2_1⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim.symm) (by sep_focus) ?_
  set regIdFutPtr : BitVec 64 := s2.readReg64 .x0
  have hstep3 := p2_seg6b_ext_wp img.base ext s2 coroPtr ctxPtr regIdFutPtr
    (img.base + skit.regIdFutVtOff) (img.base + skit.regIdPollOff)
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) (coroPtr + 0x390#64) u_788 u_790
    hpc2 hrun2 hsp2_align rfl hx1_2 (hx19_cs2.trans hx19_1)
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_steps_frame_qpan hF2 hsym2 hstep3 (by sep_focus)
    fun s3 hst23 hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx0_3, _, hx8_3, hx19_3, hx21_3, hx23_3, hx25_3, hx26_3,
    hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have htr3 : s3.trace = s.trace := by rw [htr3_2, htr2_1, htr1]
  have hst03 : Steps (tripleRatchetProgAtExt img.base ext) s s3 :=
    hst01.trans (hst12.trans hst23)
  refine SepWPp.weaken_frame
    (p2_sp3e0_words6_entails_memRegion48 s.sp 33#64 p1 33#64 33#64 p2 33#64) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_sp410_word_bytes288_entails_memRegion296 s.sp 32#64 (mid ++ unpack64 0#64) hrest_len)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (hrest_len ▸ ProofLib.pointsToBytes_entails_memRegion (s.sp + 0xa90#64) (mid ++ unpack64 0#64))
    (by sep_focus) ?_
  have hstk_poll := p2_stackAt_split_of_le s.sp stk skit.regIdPollStack
    (Nat.le_trans (p2_regIdPoll_le_sub56 skit) hstk_sub56) hstk_le64
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll) (by sep_focus) ?_
  sep_norm
  refine p2_call_oom_steps_frame_qpan
    (x := (regIdFutPtr, s.sp + 0x3e0#64, idStorePtr, stId))
    hpan hF3 hsym3 (htr3 ▸ htr) hskitOk.regIdPoll hpc3 hrun3 hsp3_al hx30_3
    (hsp3 ▸ p2_regIdPoll_pre_intro skit hF3 hsym3 (henv_s s3 htr3 hst03) hx0_3 hx8_3)
    (by sep_focus) (fun _ => Entails.refl _)
    (hnext := fun s4 hst34 hpc4 hrun4 hsp4_3 _ hcs4 hF4 hsym4 => ?_)
  dsimp only [kitRegIdPollSpecI, Spec.inImage, withLogOff, kitRegIdPollSpecE, withEnvPre,
    kitRegIdPollSpec]
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, hx23_cs4, _, hx25_cs4, hx26_cs4, hx27_cs4,
    hx28_cs4, hx29_cs4, hvregs4_3⟩
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  rw [hsp3]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.pure_elim fun ⟨hrel, htr4_3⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll.symm) (by sep_focus) ?_
  have hst04 : Steps (tripleRatchetProgAtExt img.base ext) s s4 := hst03.trans hst34
  have htr4 : s4.trace = s.trace ++ skit.regIdEvs ans := by rw [htr4_3, htr3]
  have hvregs4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := by
    rw [hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = coroPtr + 0x390#64 := hx21_cs4.trans hx21_3
  have hx23_4 : s4.readReg64 .x23 = coroPtr + 0x4f2#64 := hx23_cs4.trans hx23_3
  have hx25_4 : s4.readReg64 .x25 = s.readReg64 .x25 := by
    rw [hx25_cs4, hx25_3, hx25_cs2, hx25_1]
  have hx26_4 : s4.readReg64 .x26 = coroPtr + 0x398#64 := hx26_cs4.trans hx26_3
  have hx27_4 : s4.readReg64 .x27 = ctxPtr := hx27_cs4.trans hx27_3
  have hx28_4 : s4.readReg64 .x28 = s.readReg64 .x28 := by
    rw [hx28_cs4, hx28_3, hx28_cs2, hx28_1]
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := by
    rw [hx29_cs4, hx29_3, hx29_cs2, hx29_1]
  cases ans with
  | error e =>
    have hc4f8_fold :
        ((coroPtr + 0x4f8#64) ↦₆₄ 33#64) ∗ ((coroPtr + 0x500#64) ↦₆₄ p1) ∗
        ((coroPtr + 0x508#64) ↦₆₄ 33#64) ∗ ((coroPtr + 0x510#64) ↦₆₄ 33#64) ∗
        ((coroPtr + 0x518#64) ↦₆₄ p2) ∗ ((coroPtr + 0x520#64) ↦₆₄ 33#64) ∗
        ((coroPtr + 0x528#64) ↦₆₄ 32#64) ∗ ((coroPtr + 0x530#64) ↦ₛ (mid ++ unpack64 0#64)) =
        ((coroPtr + 0x4f8#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ unpack64 0#64))) := by
      symm
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        p2_sub6_bobSession344_split_56_288 (coroPtr + 0x4f8#64) p1 p2 mid
    refine SepWPp.weaken_frame (Entails.of_eq hc4f8_fold) (by sep_focus) ?_
    refine p2_drop_frame_sub6
      (Drop := ((ikit.id_vt + 0x20#64) ↦₆₄ᵣ (img.base + skit.regIdShimOff)) ∗
        ((img.base + skit.regIdFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + skit.regIdPollOff)))
      (by sep_focus) ?_
    have herr := hErr e regIdFutPtr s4 hrel hst04 hpc4 hrun4 hsp4 htr4
      hx19_4 hx21_4 hx23_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs4 hF4 hsym4
    exact p2_sepWPp_weaken_eq herr (by sep_focus)
  | ok localRegId =>
    dsimp only [regIdPollOutAt]
    have hsp3e8 : (s.sp + 0x3e0#64) + 8#64 = s.sp + 0x3e8#64 := by bv_omega
    have hsp3ec : (s.sp + 0x3e0#64) + 0xc#64 = s.sp + 0x3ec#64 := by bv_omega
    rw [hsp3e8, hsp3ec]
    refine SepWPp.weaken_frame (Entails.of_eq (p2_sp3ec_36_split_for_seg6c s.sp))
      (by sep_focus) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u_3ec => SepWPp.exists_elim fun u_3f0 =>
      SepWPp.exists_elim fun u_3f8 => SepWPp.exists_elim fun u_400 =>
      SepWPp.exists_elim fun u_408 => ?_
    have hstep5 := p2_seg6c_ext_wp img.base ext s4 coroPtr regIdFutPtr
      (img.base + skit.regIdFutVtOff) (img.base + skit.regIdFutDropOff)
      (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) (coroPtr + 0x390#64)
      u_88 (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) u_a8 (coroPtr + 0x390#64) u_b8 u_d0
      u_3f0 u_3f8 u_400 u_408 localRegId u_3ec
      (skit.regIdFutDrop_ne_zero hb) hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx23_4 hx26_4
    have hvt0 : (img.base + skit.regIdFutVtOff) + 0x0#64 = img.base + skit.regIdFutVtOff :=
      BitVec.add_zero _
    rw [hsp4, hvt0] at hstep5
    refine p2_bind_sepWP_steps_frame_qpan hF4 hsym4 hstep5 (by sep_focus)
      fun s5 hst45 hpc5 hrun5 hF5 hsym5 hregs5 => ?_
    rcases hregs5 with ⟨hsp5, htr5_4, _, hx19_5, hx21_5, _, hx23_5, hx24_5, hx25_5, _, _,
      hx28_5, hx29_5, hx30_5, hvregs5_4⟩
    have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
    refine SepWPp.weaken_frame
      (p2_sp3e0_after_seg6c_entails_344 s.sp 0xfffffffffffffffe#64 u_3f0 u_3f8 u_400 u_408
        localRegId u_3ec)
      (by sep_focus) ?_
    refine p2_call_nopanic_steps_frame (x := ()) (T := emp)
      hF5 hsym5 hskitOk.regIdFutDrop hpc5 hrun5 hsp5_al hx30_5
      (by simp [LibsignalPublicApi.StoreSession.futDropSpec]) True.intro (by sep_focus)
      (hnext := fun s6 hst56 hpc6 hrun6 hsp6_5 _ hcs6 hF6 hsym6 => ?_)
    dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
    refine SepWPp.pure_elim fun htr6_5 => ?_
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, _, hx23_cs6, hx24_cs6, hx25_cs6, _, _,
      hx28_cs6, hx29_cs6, hvregs6_5⟩
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    refine SepWPp.weaken_frame (skit.regIdBoxAt_memRegion regIdFutPtr idStorePtr 1#8)
      (by sep_focus) ?_
    refine p2_drop_frame_sub6
      (Drop := ((ikit.id_vt + 0x20#64) ↦₆₄ᵣ (img.base + skit.regIdShimOff)) ∗
        ((img.base + skit.regIdFutVtOff) ↦₆₄ᵣ (img.base + skit.regIdFutDropOff)) ∗
        ((img.base + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
        ((img.base + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + skit.regIdFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + skit.regIdPollOff)))
      (by sep_focus) ?_
    have hst06 : Steps (tripleRatchetProgAtExt img.base ext) s s6 :=
      hst04.trans (hst45.trans hst56)
    have htr6 : s6.trace = s.trace ++ skit.regIdEvs (.ok localRegId) := by
      rw [htr6_5, htr5_4, htr4]
    have hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0 := by
      rw [hvregs6_5, hvregs5_4, hvregs4]
    have hx25_6 : s6.readReg64 .x25 = s.readReg64 .x25 := by rw [hx25_cs6, hx25_5, hx25_4]
    have hx28_6 : s6.readReg64 .x28 = s.readReg64 .x28 := by rw [hx28_cs6, hx28_5, hx28_4]
    have hx29_6 : s6.readReg64 .x29 = s.readReg64 .x29 := by rw [hx29_cs6, hx29_5, hx29_4]
    have htail := stageP2_sub6_tail_v1_kits_ext img ext skit hH hskitVt hPure
      inp ikBPk spkBPk s0 s6
      ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1778#64)
      (fun sm Pm => SepWPp (tripleRatchetProgAtExt img.base ext) ret sm Pm Q Qp)
      s.sp coroPtr msgPtr remoteAddrPtr localAddrPtr outPtr
      regIdFutPtr kyberKpPubPtr kyberKpSecPtr ctBufPtr
      p1 p2 v_330 v_388
      u_298 u_2a0 u_80 u_90 u_400 u_3f0 u_3f8
      u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
      mid hmid localRegId remoteRegId opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2a8
      msgVerByte b_4f2 b_390 b_3ac stk
      (((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
       ((coroPtr + 0x790#64) ↦₆₄ (img.base + skit.regIdFutVtOff)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0xa90#64) 288 ∗
       logOff img ∗ F_rest)
      hwell hctBuf_nz hstk_sub56 hstk_lt hF6 hsym6 hpc6 hrun6 hsp6 hsp_align hvregs6
      (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
      (hx24_cs6.trans hx24_5)
      (fun sf hst6f hpcf hrunf hspf htrf hx8f hx9f hx10f hx11f hx19f hx20f hx22f hx23f hx24f
        hx25f hx26f hx27f hx28f hx29f hvregsf hFf hsymf => by
        refine SepWPp.done hpcf hrunf ?_
        have hok := hOk localRegId regIdFutPtr sf hrel (hst06.trans hst6f)
          hpcf hrunf hspf (htrf.trans htr6) hx8f hx9f hx10f hx11f hx19f hx20f hx22f hx23f hx24f
          (hx25f.trans hx25_6) hx26f hx27f (hx28f.trans hx28_6) (hx29f.trans hx29_6)
          hvregsf hFf hsymf
        exact p2_sepWPp_weaken_eq hok (by sep_focus))
    exact p2_sepWPp_weaken_eq (p2_cut_qpan hpan htail) (by sep_focus)

abbrev stageP2_sub6_v1_kits_4k := @stageP2_sub6_v1_kits_ext

/-- Kit-Parameterized Substage P2.6 (`+0x125c -> +0x1778` / `+0x09f4` Arm 6, 0-stack `AllocContracts`). -/
theorem stageP2_sub6_v1_kits
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A img.base} (skit : IdentitySelfStoreSpec ikit)
    (hA : AllocContracts img.base A ext)
    (hskitOk : IdentitySelfStoreKitOkI img ikit skit ext)
    (hskitVt : IdentitySelfVtablesOk img ikit skit)
    (hPure : StageP2PureCallees P A F img ext) :
    ∀ (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
      (stId : ikit.IdState)
      (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
      {Qp : State → SepProp → Prop} (_hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
      (sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr outPtr
       idStorePtr kyberKpPubPtr kyberKpSecPtr ctBufPtr
       p1 p2 v_330 v_388 u_650
       u_298 u_2a0 u_80 u_88 u_90 u_a8 u_b8 u_d0
       u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
      (mid : List (BitVec 8)), mid.length = 280 →
      ∀ (remoteRegId opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2a8 : BitVec 32)
        (msgVerByte b_4f2 b_390 b_3ac : BitVec 8)
        (stk : Nat) (F_rest : SepProp),
      img.base &&& 0xfff#64 = 0#64 →
      WellSizedAcceptKeysInput inp →
      ctBufPtr ≠ 0#64 →
      stageP2Sub56Stack skit ≤ stk →
      stk ≤ sp.toNat →
      img.FrozenLoaded s → s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x125c#64 →
      s.status = .Running →
      s.sp = sp →
      (sp &&& 15#64 == 0#64) = true →
      s0.trace <+: s.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ s3 : State, s3.trace = s.trace →
        Steps (tripleRatchetProgAtExt img.base ext) s s3 → ikit.envOk s3.fs.files) →
      s.readReg64 .x19 = coroPtr →
      (∀ (localRegId : BitVec 32) (regIdFutPtr : BitVec 64) (sf : State),
        skit.regIdRel stId (.ok localRegId) →
        Steps (tripleRatchetProgAtExt img.base ext) s sf →
        sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1778#64 →
        sf.status = .Running →
        sf.sp = sp →
        sf.trace = s.trace ++ skit.regIdEvs (.ok localRegId) →
        sf.readReg64 .x8 = coroPtr + 0xe0#64 →
        sf.readReg64 .x9 = 8#64 →
        sf.readReg64 .x10 = msgVerByte.zeroExtend 64 →
        sf.readReg64 .x11 = coroPtr + 0xf8#64 →
        sf.readReg64 .x19 = coroPtr →
        sf.readReg64 .x20 = 0xfffffffffffffffe#64 →
        sf.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 →
        sf.readReg64 .x23 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) →
        sf.readReg64 .x24 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) →
        sf.readReg64 .x25 = s.readReg64 .x25 →
        sf.readReg64 .x26 = v_330 →
        sf.readReg64 .x27 = sp + 0x370#64 →
        sf.readReg64 .x28 = s.readReg64 .x28 →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
          (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
           ((coroPtr + 0xe8#64) ↦₆₄ 8#64) ∗
           ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
           ((coroPtr + 0xf8#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++
             (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
           ((coroPtr + 0x4f8#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++
             (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
           ((sp + 0x3e0#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++
             (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
           ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
           ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
           ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
           ikit.identityAt idStorePtr stId ∗
           ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
           ((coroPtr + 0x790#64) ↦₆₄ (img.base + skit.regIdFutVtOff)) ∗
           ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
           ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
           ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
           ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
           ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
           ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
           ((coroPtr + 0x738#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
           ((coroPtr + 0x740#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
           opkOptFieldAt (coroPtr + 0x761#64) inp.opkBSk? ∗
           ((coroPtr + 0x781#64) ↦₈ 0#8) ∗
           ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
           ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
           ((coroPtr + 0x658#64) ↦ₛ bytesToBv8 ikBPk) ∗
           ((coroPtr + 0x678#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
           ((coroPtr + 0x6b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
           ((coroPtr + 0x6d8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
           ((coroPtr + 0x6f8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
           ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
           ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
           ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
           ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
           ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
           cells (coroPtr + 0x250#64) 6 ∗
           ((coroPtr + 0x298#64) ↦₆₄ (opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32))) ∗
           ((coroPtr + 0x2a0#64) ↦₆₄ ((kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64)) ∗
           ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
           ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
           ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
           ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
           ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
           ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
           ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
           ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗
           ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
           ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
           ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
           ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
           (ctBufPtr ↦₈ 8#8) ∗
           ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
           ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
           ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
           ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
           ((sp + 0x90#64) ↦₆₄ v_388) ∗
           ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
           ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
           ((sp + 0xa8#64) ↦₆₄ v_330) ∗
           ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗
           ((sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
           memRegion (sp + 0xbc#64) 4 ∗
           ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
           ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
           ((sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
           ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
           ((sp + 0x3ac#64) ↦₈ 3#8) ∗
           ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
           ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
           ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
           ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
           ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
           ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
           memRegion (sp + 0xa90#64) 288 ∗
           logOff img ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
          Q Qp) →
      (∀ (e : skit.RegIdErr) (regIdFutPtr : BitVec 64) (s4 : State),
        skit.regIdRel stId (.error e) →
        Steps (tripleRatchetProgAtExt img.base ext) s s4 →
        s4.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x9f4#64 →
        s4.status = .Running →
        s4.sp = sp →
        s4.trace = s.trace ++ skit.regIdEvs (.error e) →
        s4.readReg64 .x19 = coroPtr →
        s4.readReg64 .x21 = coroPtr + 0x390#64 →
        s4.readReg64 .x23 = coroPtr + 0x4f2#64 →
        s4.readReg64 .x25 = s.readReg64 .x25 →
        s4.readReg64 .x26 = coroPtr + 0x398#64 →
        s4.readReg64 .x27 = ctxPtr →
        s4.readReg64 .x28 = s.readReg64 .x28 →
        s4.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs s4 = calleeSavedVRegs s0 →
        img.FrozenLoaded s4 →
        s4.symtab = img.symtab →
        SepWPp (tripleRatchetProgAtExt img.base ext) ret s4
          (regIdPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
           memRegion (sp + 0x410#64) 296 ∗
           memRegion (sp + 0xa90#64) 288 ∗
           ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
           ((coroPtr + 0x790#64) ↦₆₄ (img.base + skit.regIdFutVtOff)) ∗
           A.live regIdFutPtr skit.regIdBoxSize 8 ∗
           skit.regIdBoxAt regIdFutPtr idStorePtr 1#8 ∗
           ikit.identityAt idStorePtr stId ∗
           ((img.base + skit.regIdFutVtOff) ↦₆₄ᵣ (img.base + skit.regIdFutDropOff)) ∗
           ((img.base + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
           ((img.base + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
           ((coroPtr + 0x4f8#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ unpack64 0#64))) ∗
           ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
           bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
             (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
           ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
           ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
           ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
           ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
           ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
           ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
           ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗ cells (coroPtr + 0x250#64) 6 ∗
           ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗ ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
           ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗ ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
           ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
           ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗ ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
           ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
           ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗ ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
           ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗
           ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
           ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
           ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
           ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
           ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
           ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
           ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
           ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
           ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
           A.live kyberKpPubPtr 1568 1 ∗ memRegion kyberKpPubPtr 1568 ∗
           A.live kyberKpSecPtr 3168 1 ∗
           logOff img ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
          Q Qp) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s
        (bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
           (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
         ((sp + 0x3e0#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ unpack64 0#64))) ∗
         memRegion (sp + 0xa90#64) 288 ∗
         memRegion (coroPtr + 0x4f8#64) 344 ∗
         ((coroPtr + 0x650#64) ↦₆₄ u_650) ∗
         memRegion (coroPtr + 0x788#64) 16 ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
         ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ikit.identityAt idStorePtr stId ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
         ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
         ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
         ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
         ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
         memRegion (coroPtr + 0x100#64) 336 ∗
         ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
         ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
         cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
         ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
         ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
         ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
         ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
         ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
         ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
         ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
         ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗
         ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
         ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
         ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
         ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
         ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
         A.live kyberKpPubPtr 1568 1 ∗ memRegion kyberKpPubPtr 1568 ∗
         A.live kyberKpSecPtr 3168 1 ∗
         logOff img ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
        Q Qp :=
  stageP2_sub6_v1_kits_ext img ext skit (StageP2ClosureHooks.of_allocContracts hA)
    hskitOk hskitVt hPure.to_4K

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
