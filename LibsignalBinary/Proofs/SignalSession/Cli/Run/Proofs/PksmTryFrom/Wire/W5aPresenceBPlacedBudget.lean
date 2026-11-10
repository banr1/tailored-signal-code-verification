/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresenceBPlaced
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded `[LibsignalPlacement]` Presence Segment (`+0x460 → +0x57c`)

Defines budget-threaded `BkNoneJoinFramePlaced` and `PreKeyDropSpeOk` over
`RustCliAllocBudget M`, and proves `post_seg1a_f90_to_0ac_placed_wp` (`+0x460 → +0x57c`)
on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresenceBPlacedBudget

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWP SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters hiding dropSpeSpec
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open RunProofs.Pksm
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpec)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

abbrev PresenceErrTailStatePlaced :=
  @CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.PresenceErrTailStatePlaced

abbrev presenceErrTailStatePlaced_nonvacuous :=
  @CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.presenceErrTailStatePlaced_nonvacuous

/-- Budget-threaded `[LibsignalPlacement]` Join frame at `+0x5e0` (`1504`, `m.baseKey = none`),
instantiating `PksmWire.BkNoneJoinFramePlaced` at `A.atState lim st s2`. -/
def BkNoneJoinFramePlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 s2 : State) : Prop :=
  CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.BkNoneJoinFramePlaced
    (A.atState lim st s2) s0 s2

theorem bkNoneJoinFramePlaced_iff [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 s2 : State) :
    BkNoneJoinFramePlaced M A lim st s0 s2 ↔
      s2.pc = (blkPl_111).base + 1504#64 ∧
      s2.status = .Running ∧
      ∃ (sp' sret len ptr0 w0 w1 kyberCap kyberPtr ikCap ikPtr msgCap msgPtr : BitVec 64)
        (spkTag : BitVec 32) (vb : BitVec 8) (kyAct ikAct msgAct : Bool) (R : SepProp),
        PresenceErrTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap
          (spkTag.zeroExtend 64) vb s2 ∧
        (s2.mem ⊨ deallocSlot A.repAlloc kyberCap kyberPtr kyAct ∗
          (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool lim st s2 ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ R) :=
  Iff.rfl

/-- Budget-threaded `drop_glue<SignalProtocolError>` callee contract on `preKeyPlacedProg H`. -/
def PreKeyDropSpeOk [LibsignalPlacement] (Inv : Memory → Prop) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (preKeyPlacedProg H) (lsmpl.base 5)
    (withPreKeyInv Inv (dropSpeSpec M A lim))

private theorem sepWPp_introState {prog : Program} {ret : BitVec 64} {s1 : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ s_mid, s_mid = s1 → SepWPp prog ret s_mid P Q Qp) :
    SepWPp prog ret s1 P Q Qp :=
  h s1 rfl

/-- Budget-threaded `[LibsignalPlacement]` presence segment (`+0x460 → +0x57c` /
`+1120 → +1404`) on `preKeyPlacedProg H`, threading `A.pool lim st` through `dropSpeSpec`. -/
theorem post_seg1a_f90_to_0ac_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hDropSpe : PreKeyDropSpeOk Inv M A lim H)
    {x : PreKeyTryFromArgs} {st : M.σ} {s0 s : State}
    {sp' kyberCap kyberPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64} {opkVal : BitVec 32}
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hinv : Inv s.mem)
    (htr : s.trace = s0.trace) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1404#64) s
      (memRegion (sp' + 16#64) 96 ∗ vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
        vecU8At A.repAlloc (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A.repAlloc (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
        vecU8At A.repAlloc (sp' + 384#64) msgCap msgPtr x.inner ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
        ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗ A.pool lim st s ∗
        stackAt sp' smallRootStack)
      (fun sf Pf =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        PreKeyPostState Inv s0 sp' sf ∧ kyberCap.toNat < 2 ^ 63 ∧ bkCap.toNat < 2 ^ 63 ∧
        ikCap.toNat < 2 ^ 63 ∧ msgCap.toNat < 2 ^ 63 ∧ sf.readReg64 .x29 = sp' + 512#64 ∧
        sf.readReg64 .x28 = kyberCap ∧
        sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
        sf.readReg64 .x25 = kyberPtr ∧
        sf.readReg64 .x24 = 1#64 ∧ sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = 0x44#64 ∧
        sf.readReg64 .x21 = x.ptr ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧ sf.readReg64 .x19 = x.sret ∧
        (Pf ⊢ seg1SpillsAt sp' x opkVal bkCap bkPtr msgPtr ikPtr ∗ memRegion (sp' + 312#64) 48 ∗
          memRegion (sp' + 360#64) 72 ∗
          memRegion (sp' + 432#64) 8 ∗ Wire.vecU8Buf A.repAlloc kyberCap kyberPtr x.kyberBytes ∗
          Wire.vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
          Wire.vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
          Wire.vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h27 := hregs.x27
  have h22 := hregs.x22
  have h21 := hregs.x21
  have h20 := hregs.x20
  have h19 := hregs.x19
  have hstackSpe := stackAt_sub_split sp' dropSpeStack smallRootStack (by decide) (by decide)
  rw [← sepConj_assoc (vecU8At A.repAlloc (sp' + 360#64) ikCap ikPtr x.ikBytes),
      ← sepConj_assoc (vecU8At A.repAlloc (sp' + 336#64) bkCap bkPtr x.bkBytes),
      ← sepConj_assoc (vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr x.kyberBytes)]
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (memRegion96_seg1_unpack sp') (sepConj_mono_left (post_vecU8At4_lt A.repAlloc
        (sp' + 312#64) kyberCap kyberPtr (sp' + 336#64) bkCap bkPtr
        (sp' + 360#64) ikCap ikPtr (sp' + 384#64) msgCap msgPtr
        x.kyberBytes x.bkBytes x.ikBytes x.inner))) ?_
  simp only [sepConj_assoc, sepExists_sepConj_left]
  refine Wire.SepWPp.exists_pre fun w16 => Wire.SepWPp.exists_pre fun w20 =>
    Wire.SepWPp.exists_pre fun w24 => Wire.SepWPp.exists_pre fun w28 =>
    Wire.SepWPp.exists_pre fun w32 => Wire.SepWPp.exists_pre fun w40 =>
    Wire.SepWPp.exists_pre fun w48 => Wire.SepWPp.exists_pre fun w52 =>
    Wire.SepWPp.exists_pre fun w56 => Wire.SepWPp.exists_pre fun w68 =>
    Wire.SepWPp.exists_pre fun w72 => Wire.SepWPp.exists_pre fun w80 =>
    Wire.SepWPp.exists_pre fun w88 => Wire.SepWPp.exists_pre fun w96 =>
    Wire.SepWPp.exists_pre fun w104 => ?_
  rw [← sepConj_assoc ((sp' + 16#64) ↦₃₂ w16), ← sepConj_assoc (_ ∗ ((sp' + 20#64) ↦₃₂ w20)),
      ← sepConj_assoc (_ ∗ ((sp' + 24#64) ↦₃₂ w24)), ← sepConj_assoc (_ ∗ ((sp' + 28#64) ↦₃₂ w28)),
      ← sepConj_assoc (_ ∗ ((sp' + 32#64) ↦₆₄ w32)), ← sepConj_assoc (_ ∗ ((sp' + 40#64) ↦₆₄ w40)),
      ← sepConj_assoc (_ ∗ ((sp' + 48#64) ↦₃₂ w48)), ← sepConj_assoc (_ ∗ ((sp' + 52#64) ↦₃₂ w52)),
      ← sepConj_assoc (_ ∗ ((sp' + 56#64) ↦₆₄ w56)),
      ← sepConj_assoc (_ ∗ memRegion (sp' + 64#64) 4),
      ← sepConj_assoc (_ ∗ ((sp' + 68#64) ↦₃₂ w68)), ← sepConj_assoc (_ ∗ ((sp' + 72#64) ↦₆₄ w72)),
      ← sepConj_assoc (_ ∗ ((sp' + 80#64) ↦₆₄ w80)), ← sepConj_assoc (_ ∗ ((sp' + 88#64) ↦₆₄ w88)),
      ← sepConj_assoc (_ ∗ ((sp' + 96#64) ↦₆₄ w96)), sepConj_pure_left_comm]
  refine Wire.SepWPp.pure_pre fun ⟨hky_lt, hbk_lt, hik_lt, hmsg_lt⟩ => ?_
  rw [vecU8At_eq_header_buf A.repAlloc (sp' + 312#64),
      vecU8At_eq_header_buf A.repAlloc (sp' + 336#64),
      vecU8At_eq_header_buf A.repAlloc (sp' + 360#64),
      vecU8At_eq_header_buf A.repAlloc (sp' + 384#64)]
  simp only [PreKeyTryFromArgs.kyberBytes_length, PreKeyTryFromArgs.bkBytes_length,
    PreKeyTryFromArgs.ikBytes_length]
  have hky_ne := cap_add2_ne_of_lt hky_lt
  have hbk_eq := cap_add1_eq_of_lt hbk_lt
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_pk hkf hinv (mid := lsmpl.base 5) ?_
  wp_steps_sync_pool (lsmpl.base 5)
  refine E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv1
  refine sepWPp_introState fun s1 hs1 => ?_
  rw [← hs1]
  have hsp1_eq : s1.sp = sp' := by subst hs1; tryFromPost_sp [hsp_eq]
  have hw5 :
      ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ 1569#64) ∗ ((sp' + 336#64) ↦₆₄ bkCap) ∗
        ((sp' + 344#64) ↦₆₄ bkPtr) ∗
      ((sp' + 352#64) ↦₆₄ 33#64) ⊢ memRegion (sp' + 320#64) 40 := by
    simpa [words5At, BitVec.add_assoc, BitVec.reduceAdd] using
      words5At_entails_memRegion (sp' + 320#64) kyberPtr 1569#64 bkCap bkPtr 33#64
  have hhdr80 := post_headers_entails_memRegion80 sp' ikCap ikPtr msgCap msgPtr
    (BitVec.ofNat 64 x.inner.length) x.regId (opkTag x) opkVal x.spkId x.kpkId
  dsimp only [vecHeader] at hhdr80
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hhdr80
  have hspe : speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine Wire.SepWPp.mono_pre
    (P' := (speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool lim st s1 ∗
      stackAt s1.sp dropSpeStack) ∗
      (seg1SpillsAt sp' x opkVal bkCap bkPtr msgPtr ikPtr ∗ memRegion (sp' + 360#64) 72 ∗
        memRegion (sp' + 432#64) 8 ∗
        Wire.vecU8Buf A.repAlloc kyberCap kyberPtr x.kyberBytes ∗
        Wire.vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
        Wire.vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
        memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - dropSpeStack)))
    (by
      rw [hspe, hsp1_eq, hstackSpe]
      dsimp only [seg1SpillsAt]
      refine Entails.trans (Q :=
        (((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ 1569#64) ∗ ((sp' + 336#64) ↦₆₄ bkCap) ∗
        ((sp' + 344#64) ↦₆₄ bkPtr) ∗
          ((sp' + 352#64) ↦₆₄ 33#64)) ∗ (((sp' + 360#64) ↦₆₄ ikCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
          ((sp' + 376#64) ↦₆₄ 33#64) ∗
          ((sp' + 384#64) ↦₆₄ msgCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
          ((sp' + 400#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
          ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗
          ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗ ((sp' + 432#64) ↦₃₂ 1#32) ∗
          ((sp' + 436#64) ↦₃₂ x.kpkId)) ∗
        (((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ A.pool lim st s1 ∗ stackAt sp' dropSpeStack ∗
          ((sp' + 16#64) ↦₃₂ x.kpkId) ∗ ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗
          ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗
          ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗ ((sp' + 56#64) ↦₆₄ 33#64) ∗
          memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          Wire.vecU8Buf A.repAlloc kyberCap kyberPtr x.kyberBytes ∗
          Wire.vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
          Wire.vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
          Wire.vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
          memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - dropSpeStack)))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono hw5 (sepConj_mono_left hhdr80)) ?_
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_noPanic_pk hkf
    ((⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost), st)
    hDropSpe
    (by subst hs1; simp_all [arm64_norm])
    (by subst hs1; simp_all [arm64_norm])
    (by subst hs1; tryFromPost_sp_align hsp)
    (by subst hs1; exact hinv1)
    (ret_pc := (blkPl_111).base + 1404#64) (by subst hs1; simp_all [arm64_norm])
    (T := speAt A.repAlloc [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool lim st s1 ∗
      stackAt s1.sp dropSpeStack)
    (φ := sp' + 312#64 = sp' + 312#64 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_111).base + 1404#64))
    (by subst hs1; simp_all [dropSpeSpec, arm64_norm])
    ⟨rfl, ⟨111, by decide, 1404, by decide, rfl⟩⟩ rfl
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [dropSpeSpec]
  simp only [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  rw [← sepConj_assoc (memRegion (sp' + 312#64) 48) (∃∗ evs : List AllocEvent, _),
      sepConj_comm (memRegion (sp' + 312#64) 48) (∃∗ evs : List AllocEvent, _),
      sepConj_assoc, sepExists_sepConj_left]
  refine Wire.SepWPp.exists_pre fun evs => ?_
  simp only [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun hfree => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs⟩
  refine SepWPp.of_sepWP_end_pk hkf hinv2 ?_
  refine E2E.Pqxdh.ResponderWire.SepWP.done hpc2 hrun2 ?_
  intro hinv3
  refine ⟨evs, hfree,
    ⟨by rw [hsp2, hsp1_eq], hsp2_align, hinv3, by subst hs1; simp [htr2, htr, arm64_norm]⟩,
    hky_lt, hbk_lt, hik_lt, hmsg_lt,
    by subst hs1; simp [hx29_cs, h29, arm64_norm],
    by subst hs1; simp [hx28_cs, arm64_norm],
    by subst hs1; simp [hx27_cs, h27, arm64_norm],
    by subst hs1; simp [hx26_cs, arm64_norm],
    by subst hs1; simp [hx25_cs, arm64_norm],
    by subst hs1; simp [hx24_cs, arm64_norm],
    by subst hs1; simp [hx23_cs, arm64_norm],
    by subst hs1; simp [hx22_cs, h22, arm64_norm],
    by subst hs1; simp [hx21_cs, h21, arm64_norm],
    by subst hs1; simp [hx20_cs, h20, arm64_norm],
    by subst hs1; simp [hx19_cs, h19, arm64_norm], ?_⟩
  simp only [hstackSpe, hsp1_eq, arm64_norm]
  apply entails_of_eq; ac_rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresenceBPlacedBudget
