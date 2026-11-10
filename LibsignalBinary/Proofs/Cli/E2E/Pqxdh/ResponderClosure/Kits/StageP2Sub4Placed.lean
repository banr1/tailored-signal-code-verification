/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1

/-!
# Relocatable Stage P2 Substage P2.4 (`Some` Branch)

Proves placed CPS Substage P2.4-Some (`+0x0d5c → +0x36ac` for `opkId? = some opkId`, or `+0x09c4`
Arm 3) on Block `518` (`stageP1ProgPlaced ext`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Shared
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore hiding sessionRecordEmptyHeaderAt
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

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

set_option maxHeartbeats 1200000 in
/-- Placed Kit-generic Substage P2.4-Some (`+0x0d5c -> +0x36ac` or `+0x09c4` Arm 3) in CPS form:
calls `pkKit.getShim`, polls `pkKit.getPoll` (delegating `.error e` at `+0x09c4` to `hErr`), and on
`.ok r` drops the OPK future and delegates `+0x0e40 -> +0x36ac` to `stageP2_sub4_some_tail_kits_placed`. -/
theorem stageP2_sub4_some_kits_ext_placed [LibsignalPlacement]
    {A : RustAlloc}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext) (hPure : StageP2BaseCalleesPlaced4K A ext)
    (pkKit : PreKeyStoreSpec A 0#64) (hpkOk : PreKeyStoreKitPlacedOk pkKit ext)
    (ikit : IdentityStoreSpec A 0#64) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_pk_shim : pkKit.getShimStack ≤ stk) (hstk_pk_poll : pkKit.getPollStack ≤ stk)
    (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
     v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 : BitVec 64)
    (opkId : BitVec 32) (stPk : pkKit.PkState)
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (henv : ∀ s3 : State, Steps (stageP1ProgPlaced ext) s s3 →
      s3.trace = s.trace → pkKit.envOk s3.fs.files)
    (hid_pk : pkKit.getIdOk opkId)
    (hrec_wf : ∀ r : PreKeyRecord, pkKit.getRel stPk opkId (.ok r) → pkKit.RecOk r →
      ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
        opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
        r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes)
    (hpc : s.pc = stageP1EntryPlaced + 0xd5c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = ctSlicePtr)
    (hx23 : s.readReg64 .x23 = v_a0) (hx26 : s.readReg64 .x26 = v_98)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64)
    (hErr : ∀ (opkFutPtr : BitVec 64) (e : pkKit.GetErr) (s4 : State),
      Steps (stageP1ProgPlaced ext) s s4 →
      pkKit.getRel stPk opkId (.error e) →
      s4.pc = stageP1EntryPlaced + 0x9c4#64 →
      s4.status = .Running → s4.sp = s.sp →
      s4.trace = s.trace ++ pkKit.getEvs opkId (.error e) →
      s4.readReg64 .x19 = coroPtr → s4.readReg64 .x21 = v_b0 →
      s4.readReg64 .x23 = v_a0 → s4.readReg64 .x25 = s.readReg64 .x25 →
      s4.readReg64 .x26 = v_98 → s4.readReg64 .x27 = ctxPtr →
      s4.readReg64 .x28 = s.sp + 0xa90#64 → s4.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s4.mem →
      SepWPp (stageP1ProgPlaced ext) ret s4
        (preKeyGetPollOutAt pkKit (s.sp + 0xa90#64) (.error e) ∗
         memRegion (s.sp + 0xac8#64) 8 ∗ memRegion (s.sp + 0xad0#64) 1 ∗
         pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
         pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
         A.live opkFutPtr pkKit.getBoxSize 8 ∗
         ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
         ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (s.sp + 0x270#64) 9 ∗
         bytes7At (s.sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
         memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0x930#64) 56 ∗
         ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
         ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
         keyPair64UnalignedAt (coroPtr + 0x4b1#64) c0_init c1_init c2_init c3_init
           c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
           cw6_init c63_init ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
         ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         ((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getShimOff)) ∗
         ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
         ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
         ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getPollOff)) ∗
         A.pool ∗ stackAt s.sp stk ∗ Frame)
        Q Qp)
    (hOk : ∀ (r : PreKeyRecord) (opkPubBytes opkPrivBytes : List (BitVec 8))
      (opkFutPtr idKpFutPtr privCap privPtr : BitVec 64)
      (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
      (w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp : BitVec 64)
      (sf : State),
      Steps (stageP1ProgPlaced ext) s sf →
      pkKit.getRel stPk opkId (.ok r) → pkKit.RecOk r →
      opkPubBytes.length = 32 → opkPrivBytes.length = 32 →
      r.preKey.publicKey = 5#8 :: opkPubBytes → r.preKey.privateKey = opkPrivBytes →
      (∀ a : BitVec 64, (a ↦ₛ opkPubBytes) =
        (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
          ((a + 24#64) ↦₆₄ u3_kp)) →
      (∀ a : BitVec 64, (a ↦ₛ clampBv8List opkPrivBytes) =
        (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
          ((a + 24#64) ↦₆₄ u7_kp)) →
      (∀ a : BitVec 64,
        bytes7At a b0 b1 b2 b3 b4 b5 b6 ∗
        ((a + 7#64) ↦₆₄ w0) ∗ ((a + 15#64) ↦₆₄ w1) ∗ ((a + 23#64) ↦₆₄ w2) ∗ ((a + 31#64) ↦₆₄ w3) =
          (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
            ((a + 24#64) ↦₆₄ u3_kp) ∗ bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6) →
      (∀ a : BitVec 64,
        bytes7At a c0 c1 c2 c3 c4 c5 c6 ∗
        ((a + 7#64) ↦₆₄ w4) ∗ ((a + 15#64) ↦₆₄ w5) ∗ ((a + 23#64) ↦₆₄ w6) ∗ ((a + 31#64) ↦₈ b63) =
          (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
            ((a + 24#64) ↦₆₄ u7_kp)) →
      sf.pc = stageP1EntryPlaced + 0x36ac#64 →
      sf.status = .Running → sf.sp = s.sp →
      sf.trace = s.trace ++ pkKit.getEvs opkId (.ok r) →
      sf.readReg64 .x0 = idKpFutPtr → sf.readReg64 .x1 = 0#64 + skit.kpFutVtOff →
      idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = v_b0 →
      sf.readReg64 .x23 = v_a0 → sf.readReg64 .x24 = s.sp + 0x370#64 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = s.sp + 0xa90#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.ok r)) ∗
         A.live idKpFutPtr skit.kpBoxSize 8 ∗
         skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
         ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
         ((s.sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (s.sp + 0x270#64) 9 ∗
         bytes7At (s.sp + 0x3b0#64) b0 b1 b2 b3 b4 b5 b6 ∗
         memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0x930#64) 56 ∗
         memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
         ((coroPtr + 0x4b0#64) ↦₈ 1#8) ∗
         keyPair64UnalignedAt (coroPtr + 0x4b1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
         ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         ((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getShimOff)) ∗
         ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
         ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
         ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getPollOff)) ∗
         A.pool ∗ stackAt s.sp stk ∗ Frame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s
      (((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (s.sp + 0x270#64) 9 ∗
       bytes7At (s.sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
       memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0x930#64) 56 ∗
       memRegion (s.sp + 0xa90#64) 65 ∗
       ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       keyPair64UnalignedAt (coroPtr + 0x4b1#64) c0_init c1_init c2_init c3_init
         c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
         cw6_init c63_init ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       ((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getShimOff)) ∗
       ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
       ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getPollOff)) ∗
       pkKit.storeAt preKeyStorePtr stPk ∗ A.pool ∗ stackAt s.sp stk ∗ Frame)
      Q Qp := by
  have hstep1 := p2_seg4a_ext_placed_wp ext s coroPtr msgPtr ctxPtr
    preKeyStorePtr pkKit.pk_vt (0#64 + pkKit.getShimOff) ctSlicePtr u_488 opkId
    hpc hrun hsp_align hx19 hx21
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, _, hx23_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hx1_1_32 : s1.readReg32 .x1 = opkId := by
    change (s1.readReg64 .x1).setWidth 32 = opkId
    rw [hx1_1, p2_zext64_trunc32_id]
  have hstk_shim := p2_stackAt_split_of_le s.sp stk pkKit.getShimStack hstk_pk_shim hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim) (by sep_focus) ?_
  sep_norm
  refine p2_call_oom_rocl_steps_frame_qpan
    (x := ({ self := preKeyStorePtr, id := opkId } : PreKeyShimCall))
    hpan hCode1 (htr1 ▸ htr) (hpkOk.getShim (by decide)) hpc1 hrun1 hsp1_al hx30_1
    (hsp1 ▸ p2_pkGetShim_pre_intro_placed hx0_1 hx1_1_32)
    (by sep_focus) (fun _ => Entails.refl _)
    (hnext := fun s2 hst12 hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [kitPreKeyGetShimSpec]
  rcases hcs2 with ⟨hcs2_19, _, _, _, hcs2_23, _, hcs2_25, hcs2_26, hcs2_27, hcs2_28,
    hcs2_29, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_2, _, _, htr2_1⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim.symm) (by sep_focus) ?_
  let opkFutPtr := s2.readReg64 .x0
  have hstep3 := p2_seg4b_ext_placed_wp ext s2 coroPtr ctxPtr opkFutPtr
    (0#64 + pkKit.getFutVtOff) (0#64 + pkKit.getPollOff) v_b0 u_4f8 u_500
    hpc2 hrun2 hsp2_align rfl hx1_2 (hcs2_19.trans hx19_1) (hcs2_27.trans hx27_1)
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_qp_frame_placed hCode2 hstep3 (by sep_focus)
    fun s3 hst23 hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, _, hx8_3, hx19_3, hx21_3, hx23_3, hx25_3, hx26_3,
    hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
  have hsp3 : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have htr3_s : s3.trace = s.trace := by rw [htr3_2, htr2_1, htr1]
  have hstk_poll := p2_stackAt_split_of_le s.sp stk pkKit.getPollStack hstk_pk_poll hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_65_pkPoll_split_eq (s.sp + 0xa90#64)))
    (by sep_focus) ?_
  rw [show (s.sp + 0xa90#64) + 0x38#64 = s.sp + 0xac8#64 by bv_omega,
      show (s.sp + 0xa90#64) + 0x40#64 = s.sp + 0xad0#64 by bv_omega]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_ac8 => ?_
  sep_norm
  refine p2_call_oom_rocl_steps_frame_qpan
    (x := (({ fut := opkFutPtr, self := preKeyStorePtr, out := s.sp + 0xa90#64,
              id := opkId } : PreKeyPollCall), stPk))
    hpan hCode3 (htr3_s ▸ htr) (hpkOk.getPoll (by decide)) hpc3 hrun3 hsp3_al hx30_3
    (hsp3 ▸ p2_pkGetPoll_pre_intro_placed
      (henv s3 (hst01.trans (hst12.trans hst23)) htr3_s) hx0_3 hx8_3 hid_pk)
    (by sep_focus) (fun _ => Entails.refl _)
    (hnext := fun s4 hst34 hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
  dsimp only [kitPreKeyGetPollSpecE, withEnvPre, kitPreKeyGetPollSpec]
  rcases hcs4 with ⟨hcs4_19, _, hcs4_21, _, hcs4_23, _, hcs4_25, hcs4_26, hcs4_27, hcs4_28,
    hcs4_29, hvregs4_3⟩
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  rw [hsp3]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.pure_elim fun ⟨hrel, htr4_3⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll.symm) (by sep_focus) ?_
  have htr4 : s4.trace = s.trace ++ pkKit.getEvs opkId ans := by rw [htr4_3, htr3_s]
  have hst04 := hst01.trans (hst12.trans (hst23.trans hst34))

  cases ans with
  | error e =>
    refine SepWPp.weaken_frame (pointsTo64_entails_memRegion (s.sp + 0xac8#64) u_ac8)
      (by sep_focus) ?_
    have herr := hErr opkFutPtr e s4 hst04 hrel hpc4 hrun4 hsp4 htr4
      (hcs4_19.trans hx19_3) (hcs4_21.trans hx21_3)
      (by rw [hcs4_23, hx23_3, hcs2_23, hx23_1, hx23])
      (by rw [hcs4_25, hx25_3, hcs2_25, hx25_1])
      (by rw [hcs4_26, hx26_3, hcs2_26, hx26_1, hx26])
      (hcs4_27.trans hx27_3)
      (by rw [hcs4_28, hx28_3, hcs2_28, hx28_1, hx28])
      (by rw [hcs4_29, hx29_3, hcs2_29, hx29_1])
      (by rw [hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]) hCode4
    exact p2_sepWPp_weaken_eq herr (by sep_focus)
  | ok r =>
    dsimp only [preKeyGetPollOutAt]
    simp only [sepConj_assoc]
    refine p2_sepWPp_pure_elim_frame (pkKit.RecOk r) (by sep_focus) fun hrec_ok => ?_
    obtain ⟨opkPubBytes, opkPrivBytes, hpub_len, hpriv_len, hpub_eq, hpriv_eq⟩ :=
      hrec_wf r hrel hrec_ok
    rw [show s.sp + 0xac8#64 = (s.sp + 0xa90#64) + 0x38#64 by bv_omega]
    refine SepWPp.weaken_frame (p2_preKeyRecordAt_unpack A (s.sp + 0xa90#64) u_ac8 r)
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun pubCap => SepWPp.exists_elim fun pubPtr =>
      SepWPp.exists_elim fun privCap => SepWPp.exists_elim fun privPtr =>
      SepWPp.exists_elim fun pad32 => ?_
    have hpub_bv : BitVec.ofNat 64 r.preKey.publicKey.length = 33#64 := by
      rw [hpub_eq]; simp [hpub_len]
    have hpriv_bv : BitVec.ofNat 64 r.preKey.privateKey.length = 32#64 := by
      rw [hpriv_eq, hpriv_len]
    rw [hpub_bv, hpriv_bv, hpub_eq, hpriv_eq]
    refine SepWPp.weaken_frame (p2_vecU8Buf_nonempty A pubCap pubPtr (5#8 :: opkPubBytes) (by simp))
      (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpub_le, hpub_lt, hpub_nz, hpub_ne2, hpub_ne1⟩ => ?_
    have hpub_ne3 : pubCap ≠ 0xfffffffffffffffd#64 := p2_cap_ne_neg3_of_lt hpub_lt
    have hstep5 := p2_seg4c_gen_placed_wp ext s4 coroPtr ctxPtr opkFutPtr
      (0#64 + pkKit.getFutVtOff) (0#64 + pkKit.getFutDropOff)
      pubCap pubPtr privCap privPtr (pad32 ++ r.preKey.id) u_ac8
      v_98 v_a0 v_b0 v_98 v_a0 u_a8 v_b0 u_b8 ctxPtr u_d0
      hpub_ne2 hpub_ne3 (pkKit.getFutDrop_ne_zero rfl) hpc4 hrun4 hsp4_align
      (hcs4_19.trans hx19_3) (hcs4_21.trans hx21_3)
      (by rw [hcs4_23, hx23_3, hcs2_23, hx23_1, hx23])
      (by rw [hcs4_26, hx26_3, hcs2_26, hx26_1, hx26])
      (hcs4_27.trans hx27_3)
    have hvt0 : (0#64 + pkKit.getFutVtOff) + 0x0#64 = 0#64 + pkKit.getFutVtOff :=
      BitVec.add_zero _
    rw [hsp4, hvt0] at hstep5
    refine p2_bind_sepWP_qp_frame_placed hCode4 hstep5 (by sep_focus)
      fun s5 hst45 hpc5 hrun5 hCode5 hregs5 => ?_
    rcases hregs5 with ⟨hsp5, htr5_4, _, hx19_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5,
      hx27_5, hx28_5, hx29_5, hx30_5, hvregs5_4⟩
    have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
    refine p2_call_nopanic_rocl_steps_frame_placed (x := ()) (T := emp)
      hCode5 (hpkOk.getFutDrop (by decide)) hpc5 hrun5 hsp5_al hx30_5
      (by dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]; exact (pure_true_sepConj emp).symm)
      True.intro (by sep_focus)
      (hnext := fun s6 hst56 hpc6 hrun6 hsp6_5 _ hcs6 hCode6 => ?_)
    dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
    refine SepWPp.pure_elim fun htr6_5 => ?_
    rcases hcs6 with ⟨hcs6_19, _, hcs6_21, hcs6_22, hcs6_23, hcs6_24, hcs6_25, hcs6_26, hcs6_27,
      hcs6_28, hcs6_29, hvregs6_5⟩
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    have htr6 : s6.trace = s.trace ++ pkKit.getEvs opkId (.ok r) := by
      rw [htr6_5, htr5_4, htr4]
    have hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0 := by
      rw [hvregs6_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
    let TailFrame : SepProp :=
      pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.ok r)) ∗
      ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
      ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
      ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
      ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
      ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getShimOff)) ∗
      ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
      ((0#64 + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getPollOff)) ∗
      Frame
    have htail := stageP2_sub4_some_tail_kits_ext_placed ext hH hPure pkKit ikit skit
      hskitVt hskitOk stk hstk_pure hstk_kp_shim hstk_lt
      (stageP1EntryPlaced + 0x36ac#64) s0 s6 s.sp TailFrame
      (fun sm Pm => SepWPp (stageP1ProgPlaced ext) ret sm Pm Q Qp)
      coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr opkFutPtr
      pubCap pubPtr privCap privPtr (pad32 ++ r.preKey.id) u_ac8 v_98 v_a0 v_b0
      opkId opkPubBytes opkPrivBytes
      b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
      c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
      cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
      hpub_len hpriv_len hpub_le hpub_nz hpub_ne1
      hCode6 hpc6 hrun6 hsp6 hsp_align (htr.trans ⟨_, htr6.symm⟩) hvregs6
      (hcs6_19.trans hx19_5) (hcs6_21.trans hx21_5) (hcs6_22.trans hx22_5)
      (hcs6_23.trans hx23_5) (hcs6_24.trans hx24_5) (hcs6_26.trans hx26_5)
      (hcs6_27.trans hx27_5)
      (by rw [hcs6_28, hx28_5, hcs4_28, hx28_3, hcs2_28, hx28_1, hx28])
      (fun idKpFutPtr b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6
           w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp sf
           hst6f hpk_words hsk_words hkp_lo hkp_hi
           hpcf hrunf hspf htrf_6 hx0_f hx1_f hx0_nz hx0_al
           hx19_f hx21_f hx23_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f
           hvregsf hCodef => by
        have hok := hOk r opkPubBytes opkPrivBytes opkFutPtr idKpFutPtr privCap privPtr
          b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6
          w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp sf
          (hst04.trans (hst45.trans (hst56.trans hst6f))) hrel hrec_ok
          hpub_len hpriv_len hpub_eq hpriv_eq hpk_words hsk_words hkp_lo hkp_hi
          hpcf hrunf hspf (htrf_6.trans htr6) hx0_f hx1_f hx0_nz hx0_al
          hx19_f hx21_f hx23_f hx24_f
          (by rw [hx25_f, hcs6_25, hx25_5, hcs4_25, hx25_3, hcs2_25, hx25_1])
          hx26_f hx27_f hx28_f
          (by rw [hx29_f, hcs6_29, hx29_5, hcs4_29, hx29_3, hcs2_29, hx29_1])
          hvregsf hCodef
        refine SepWPp.done hpcf hrunf ?_
        dsimp only [TailFrame]
        exact p2_sepWPp_weaken_eq hok (by sep_focus))
    dsimp only [TailFrame] at htail
    exact p2_sepWPp_weaken_eq (p2_cut_qpan hpan htail) (by sep_focus)

abbrev stageP2_sub4_some_kits_4k_placed := @stageP2_sub4_some_kits_ext_placed
abbrev stageP2_sub4_some_kits_hooks_placed := @stageP2_sub4_some_kits_ext_placed

theorem stageP2_sub4_some_kits_placed [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext) (hPure : StageP2PureCalleesPlaced P A F ext)
    (pkKit : PreKeyStoreSpec A 0#64) (hpkOk : PreKeyStoreKitPlacedOk pkKit ext)
    (ikit : IdentityStoreSpec A 0#64) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_pk_shim : pkKit.getShimStack ≤ stk) (hstk_pk_poll : pkKit.getPollStack ≤ stk)
    (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
     v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 : BitVec 64)
    (opkId : BitVec 32) (stPk : pkKit.PkState)
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (henv : ∀ s3 : State, Steps (stageP1ProgPlaced ext) s s3 →
      s3.trace = s.trace → pkKit.envOk s3.fs.files)
    (hid_pk : pkKit.getIdOk opkId)
    (hrec_wf : ∀ r : PreKeyRecord, pkKit.getRel stPk opkId (.ok r) → pkKit.RecOk r →
      ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
        opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
        r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes)
    (hpc : s.pc = stageP1EntryPlaced + 0xd5c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = ctSlicePtr)
    (hx23 : s.readReg64 .x23 = v_a0) (hx26 : s.readReg64 .x26 = v_98)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64)
    (hErr : ∀ (opkFutPtr : BitVec 64) (e : pkKit.GetErr) (s4 : State),
      Steps (stageP1ProgPlaced ext) s s4 →
      pkKit.getRel stPk opkId (.error e) →
      s4.pc = stageP1EntryPlaced + 0x9c4#64 →
      s4.status = .Running → s4.sp = s.sp →
      s4.trace = s.trace ++ pkKit.getEvs opkId (.error e) →
      s4.readReg64 .x19 = coroPtr → s4.readReg64 .x21 = v_b0 →
      s4.readReg64 .x23 = v_a0 → s4.readReg64 .x25 = s.readReg64 .x25 →
      s4.readReg64 .x26 = v_98 → s4.readReg64 .x27 = ctxPtr →
      s4.readReg64 .x28 = s.sp + 0xa90#64 → s4.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s4.mem →
      SepWPp (stageP1ProgPlaced ext) ret s4
        (preKeyGetPollOutAt pkKit (s.sp + 0xa90#64) (.error e) ∗
         memRegion (s.sp + 0xac8#64) 8 ∗ memRegion (s.sp + 0xad0#64) 1 ∗
         pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
         pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
         A.live opkFutPtr pkKit.getBoxSize 8 ∗
         ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
         ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (s.sp + 0x270#64) 9 ∗
         bytes7At (s.sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
         memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0x930#64) 56 ∗
         ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
         ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
         keyPair64UnalignedAt (coroPtr + 0x4b1#64) c0_init c1_init c2_init c3_init
           c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
           cw6_init c63_init ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
         ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         ((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getShimOff)) ∗
         ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
         ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
         ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getPollOff)) ∗
         A.pool ∗ stackAt s.sp stk ∗ Frame)
        Q Qp)
    (hOk : ∀ (r : PreKeyRecord) (opkPubBytes opkPrivBytes : List (BitVec 8))
      (opkFutPtr idKpFutPtr privCap privPtr : BitVec 64)
      (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
      (w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp : BitVec 64)
      (sf : State),
      Steps (stageP1ProgPlaced ext) s sf →
      pkKit.getRel stPk opkId (.ok r) → pkKit.RecOk r →
      opkPubBytes.length = 32 → opkPrivBytes.length = 32 →
      r.preKey.publicKey = 5#8 :: opkPubBytes → r.preKey.privateKey = opkPrivBytes →
      (∀ a : BitVec 64, (a ↦ₛ opkPubBytes) =
        (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
          ((a + 24#64) ↦₆₄ u3_kp)) →
      (∀ a : BitVec 64, (a ↦ₛ clampBv8List opkPrivBytes) =
        (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
          ((a + 24#64) ↦₆₄ u7_kp)) →
      (∀ a : BitVec 64,
        bytes7At a b0 b1 b2 b3 b4 b5 b6 ∗
        ((a + 7#64) ↦₆₄ w0) ∗ ((a + 15#64) ↦₆₄ w1) ∗ ((a + 23#64) ↦₆₄ w2) ∗ ((a + 31#64) ↦₆₄ w3) =
          (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
            ((a + 24#64) ↦₆₄ u3_kp) ∗ bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6) →
      (∀ a : BitVec 64,
        bytes7At a c0 c1 c2 c3 c4 c5 c6 ∗
        ((a + 7#64) ↦₆₄ w4) ∗ ((a + 15#64) ↦₆₄ w5) ∗ ((a + 23#64) ↦₆₄ w6) ∗ ((a + 31#64) ↦₈ b63) =
          (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
            ((a + 24#64) ↦₆₄ u7_kp)) →
      sf.pc = stageP1EntryPlaced + 0x36ac#64 →
      sf.status = .Running → sf.sp = s.sp →
      sf.trace = s.trace ++ pkKit.getEvs opkId (.ok r) →
      sf.readReg64 .x0 = idKpFutPtr → sf.readReg64 .x1 = 0#64 + skit.kpFutVtOff →
      idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = v_b0 →
      sf.readReg64 .x23 = v_a0 → sf.readReg64 .x24 = s.sp + 0x370#64 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = s.sp + 0xa90#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.ok r)) ∗
         A.live idKpFutPtr skit.kpBoxSize 8 ∗
         skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
         ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
         ((s.sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (s.sp + 0x270#64) 9 ∗
         bytes7At (s.sp + 0x3b0#64) b0 b1 b2 b3 b4 b5 b6 ∗
         memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0x930#64) 56 ∗
         memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
         ((coroPtr + 0x4b0#64) ↦₈ 1#8) ∗
         keyPair64UnalignedAt (coroPtr + 0x4b1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
         ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         ((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getShimOff)) ∗
         ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
         ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
         ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getPollOff)) ∗
         A.pool ∗ stackAt s.sp stk ∗ Frame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s
      (((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (s.sp + 0x270#64) 9 ∗
       bytes7At (s.sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
       memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0x930#64) 56 ∗
       memRegion (s.sp + 0xa90#64) 65 ∗
       ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       keyPair64UnalignedAt (coroPtr + 0x4b1#64) c0_init c1_init c2_init c3_init
         c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
         cw6_init c63_init ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       ((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getShimOff)) ∗
       ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
       ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getPollOff)) ∗
       pkKit.storeAt preKeyStorePtr stPk ∗ A.pool ∗ stackAt s.sp stk ∗ Frame)
      Q Qp :=
  stageP2_sub4_some_kits_ext_placed ext hH hPure.to_4K.toStageP2BaseCalleesPlaced4K pkKit hpkOk ikit skit
    hskitVt hskitOk stk hstk_pure hstk_pk_shim hstk_pk_poll hstk_kp_shim hstk_lt
    ret s0 s Frame Q (Qp := Qp) hpan
    coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
    v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 opkId stPk
    b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
    cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    hCode henv hid_pk hrec_wf hpc hrun hsp_align htr hvregs
    hx19 hx21 hx23 hx26 hx28 hErr hOk

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
