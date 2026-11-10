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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ProloguePlaced
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded `[LibsignalPlacement]` Prologue Segments (`+0x000..+0x0b8`)

Proves `VmPreserved` and `RustCliAllocBudget M` pool-threading forms of the empty-slice,
version-dispatch, and frame-initialization prologue segments on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ProloguePlacedBudget

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire hiding
  prologue_nil_to_504_placed_wpE prologue_entry_ne_nil_placed_wpX
  prologue_28_legacyVer_placed_wpE prologue_28_unrecognizedVer_placed_wpE
  prologue_28_validVer_placed_wpX prologue_80_init_placed_wpX
open RunProofs.Pksm
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)

private abbrev SepWPp := Wire.SepWPp
abbrev noPanicQp : State → SepProp → Prop := fun _ _ => False

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

private theorem pl_spAligned_sub608_pl {s : State} (h : s.spAligned = true) :
    ((s.sp - 608#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned, beq_iff_eq] at h
  rw [beq_iff_eq]
  bv_bits

attribute [local simp, local arm64_norm, local wp_norm]
  cond_eq_subs1_false_w40 cond_eq_len1
  cond_ne_noneCap_add2 cond_eq_noneCap_add1 cond_hi_noneCap_sub1_add3

private theorem sepWPp_of_sepWP_end_anyQp_pk {prog : Program} {ret : BitVec 64}
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : Inv s.mem)
    (h : ProofLib.SepWP prog ret s P (fun sf Pf =>
      Wire.VRegsAt s sf ∧ (Inv sf.mem → Q sf Pf))) :
    Wire.SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hv, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf,
      hq (hkf hinv hsteps.keepsFrozen), hv.eq⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Terminal Block-111 non-`svc #0` segment combinator delivering `NonSyscallPreserved` and `Inv`
for arbitrary panic postcondition `Qp`. -/
theorem sepWPp_end_ls_vm [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {H : LibsignalHooks} {ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} (hinv : Inv s.mem)
    (hseg : ∀ m_strip : Memory,
      ProofLib.SepWP ((blkPC_111).rebase (blkPl_111).base (hooksException H))
        ret (s.setMem m_strip) Pre (fun sm' Pm =>
          Wire.VRegsAt (s.setMem m_strip) sm' ∧
          ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            Inv m_real → Q (sm'.setMem m_real) Pm)) :
    Wire.SepWPp (preKeyPlacedProg H) ret s Pre Q Qp := by
  refine sepWPp_of_sepWP_end_anyQp_pk hkf hinv ?_
  apply sepWP_seg_ls_vm (Q := (blkPC_111).rebase (blkPl_111).base (hooksException H))
    blkLib_eq_111 (mid := ret)
  intro m_strip
  refine ProofLib.SepWP.of_reaches_pc fun R hm hL => ?_
  rcases ProofLib.SepWP.to_reaches_pc (hseg m_strip) hm hL with
    ⟨sm', hsteps, ⟨hpcm', hrunm', Pm, hmm', hv, hnext⟩ | hoom⟩
  · exact ⟨sm', hsteps, Or.inl ⟨hpcm', hrunm', Pm, hmm', fun m_real hnsp =>
      ProofLib.SepWP.done (by simpa [arm64_norm] using hpcm') (by simpa [arm64_norm] using hrunm')
        ⟨⟨by simpa [arm64_norm] using hv.eq⟩, fun hinv_m => hnext m_real hnsp hinv_m⟩⟩⟩
  · exact ⟨sm', hsteps, Or.inr hoom⟩

/-- Frame `A.pool lim st s` around a panic-free `Wire.SepWPp` proving `VmPreserved s sf`,
producing `A.pool lim st sf` for any `Qp`. -/
theorem sepWPp_frame_pool_of_vm {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop}
    (h : Wire.SepWPp prog ret s P Q noPanicQp)
    (hq : ∀ sf Pf, Q sf Pf → VmPreserved s sf ∧
      (∀ Ppool, (Pf ∗ Ppool ⊢ Ppool) → True) ∧ Q' sf (Pf ∗ A.pool lim st sf)) :
    Wire.SepWPp prog ret s (P ∗ A.pool lim st s) Q' Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  rcases h (A.pool lim st s ∗ R) hm hL with
    ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hqf, hv⟩ | ⟨_, _, _, hp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hvm, -, hq'⟩ := hq sf Pf hqf
    rw [← A.pool_transport lim st s sf hvm, ← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf ∗ A.pool lim st sf, hmf, hq', hv⟩⟩
  · exact False.elim hp
  · exact (not_satisfies_false_sepConj hoom).elim

/-- (``x.bytes = []`, `VmPreserved` form`): `+0 .. +36 → +76 .. +92 → +1284`. -/
theorem prologue_nil_to_504_placed_wpE_vm [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {x : RunCompose.PksmGhost} {s0 : State}
    {Qp : State → SepProp → Prop}
    (_hnil : x.bytes = [])
    (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx1 : s0.readReg64 .x1 = 0#64) (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗
        memRegion x.ret 248 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) sf ∧
        VmPreserved s0 sf ∧
        (Pf ⊢ (x.ptr ↦ₛ x.bytes) ∗
          pksmErrE A [] x.ret (.ciphertextMessageTooShort 0) ∗
          preKeyCalleeSavedAt (s0.sp - 608#64) s0))
      Qp := by
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono (memRegion248_split_8_8_8 x.ret)
      (memRegion96_split_preKeyCalleeSaved (s0.sp - 608#64)))) ?_
  simp only [bv_sub_add_lit', BitVec.reduceSub,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun w19 => Wire.SepWPp.exists_pre fun w20 =>
    Wire.SepWPp.exists_pre fun w21 => Wire.SepWPp.exists_pre fun w22 =>
    Wire.SepWPp.exists_pre fun w23 => Wire.SepWPp.exists_pre fun w24 =>
    Wire.SepWPp.exists_pre fun w25 => Wire.SepWPp.exists_pre fun w26 =>
    Wire.SepWPp.exists_pre fun w27 => Wire.SepWPp.exists_pre fun w28 =>
    Wire.SepWPp.exists_pre fun w30 => Wire.SepWPp.exists_pre fun w29 =>
    Wire.SepWPp.exists_pre fun ws16 => Wire.SepWPp.exists_pre fun ws8 =>
    Wire.SepWPp.exists_pre fun ws0 => ?_
  refine sepWPp_end_ls_vm keepsFrozenInv_codeRoLoaded hcl fun m_strip => ?_
  wp_steps
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun m_real hnsp hcl1 => ?_⟩
  refine ⟨⟨by simp_all [arm64_norm], ?_, hcl1, by simp_all [arm64_norm]⟩,
    hnsp.toVmPreserved (by simp_all [arm64_norm]), ?_⟩
  · rw [State.spAligned]
    simpa [arm64_norm] using pl_spAligned_sub608_pl hsp
  · unfold preKeyCalleeSavedAt
    simp only [bv_sub_add_lit', BitVec.reduceSub, arm64_norm]
    have herr := errCells_tooShort A [] x.ret 0
    unfold errTag speWord at herr
    change (x.ret ↦₆₄ 0xffffffffffffffff#64) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775811#64) ∗
      ((x.ret + 16#64) ↦₆₄ 0#64) ∗
      memRegion (x.ret + 24#64) 224 ⊢ _ at herr
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left herr))
    apply entails_of_eq; ac_rfl

/-- (``x.bytes = []`, budget-pool form`): threads `A.pool lim st s0` to `A.pool lim st sf`. -/
theorem prologue_nil_to_504_placed_wpE [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {x : RunCompose.PksmGhost} {s0 : State}
    {Qp : State → SepProp → Prop}
    (hnil : x.bytes = [])
    (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx1 : s0.readReg64 .x1 = 0#64) (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s0
      (((x.ptr ↦ₛ x.bytes) ∗
        memRegion x.ret 248 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96) ∗ A.pool lim st s0)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) sf ∧
        (Pf ⊢ (x.ptr ↦ₛ x.bytes) ∗
          pksmErrE A.repAlloc [] x.ret (.ciphertextMessageTooShort 0) ∗
          preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗ A.pool lim st sf))
      Qp := by
  refine sepWPp_frame_pool_of_vm
    (prologue_nil_to_504_placed_wpE_vm (A := A.repAlloc) hnil hpc hrun hsp hcl hx1 hx8) ?_
  intro sf Pf ⟨hstf, hvm, hentf⟩
  refine ⟨hvm, ⟨fun _ _ => trivial, hstf, Entails.trans (sepConj_mono_left hentf) ?_⟩⟩
  apply entails_of_eq; ac_rfl

/-- Entry non-empty step (`+0 .. +36 → +40`, `VmPreserved` form). -/
theorem prologue_entry_ne_nil_placed_wpX_vm [LibsignalPlacement] {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {s0 : State}
    {Qp : State → SepProp → Prop}
    (hne : x.bytes ≠ []) (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 40#64) s0
      (memRegion (s0.sp - 608#64 + 512#64) 96)
      (fun s1 P1 =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) s1 ∧
        VmPreserved s0 s1 ∧
        s1.readReg64 .x0 = x.ptr ∧
        s1.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length ∧
        s1.readReg64 .x19 = x.ret ∧
        s1.readReg64 .x29 = s0.sp - 608#64 + 512#64 ∧
        (P1 ⊢ preKeyCalleeSavedAt (s0.sp - 608#64) s0))
      Qp := by
  have hlen_ne : BitVec.ofNat 64 x.bytes.length ≠ 0#64 :=
    ofNat64_length_ne_zero_w40 hne hlt
  have hlen_beq : (BitVec.ofNat 64 x.bytes.length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hlen_ne
  refine Wire.SepWPp.mono_pre (memRegion96_split_preKeyCalleeSaved (s0.sp - 608#64)) ?_
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  refine Wire.SepWPp.exists_pre fun w19 => Wire.SepWPp.exists_pre fun w20 =>
    Wire.SepWPp.exists_pre fun w21 => Wire.SepWPp.exists_pre fun w22 =>
    Wire.SepWPp.exists_pre fun w23 => Wire.SepWPp.exists_pre fun w24 =>
    Wire.SepWPp.exists_pre fun w25 => Wire.SepWPp.exists_pre fun w26 =>
    Wire.SepWPp.exists_pre fun w27 => Wire.SepWPp.exists_pre fun w28 =>
    Wire.SepWPp.exists_pre fun w30 => Wire.SepWPp.exists_pre fun w29 => ?_
  refine sepWPp_end_ls_vm keepsFrozenInv_codeRoLoaded hcl fun m_strip => ?_
  wp_steps
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun m_real hnsp hcl1 => ?_⟩
  refine ⟨⟨by simp_all [arm64_norm], ?_, hcl1, by simp_all [arm64_norm]⟩,
    hnsp.toVmPreserved (by simp_all [arm64_norm]),
    by simp [hx0, arm64_norm], by simp [hx1, arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], ?_⟩
  · rw [State.spAligned]
    simpa [arm64_norm] using pl_spAligned_sub608_pl hsp
  · unfold preKeyCalleeSavedAt
    simp only [bv_sub_add_lit', BitVec.reduceSub, arm64_norm]
    apply entails_of_eq; ac_rfl

/-- Entry non-empty step (`+0 .. +36 → +40`, budget-pool form). -/
theorem prologue_entry_ne_nil_placed_wpX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {x : RunCompose.PksmGhost} {s0 : State}
    {Qp : State → SepProp → Prop}
    (hne : x.bytes ≠ []) (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 40#64) s0
      (memRegion (s0.sp - 608#64 + 512#64) 96 ∗ A.pool lim st s0)
      (fun s1 P1 =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) s1 ∧
        s1.readReg64 .x0 = x.ptr ∧
        s1.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length ∧
        s1.readReg64 .x19 = x.ret ∧
        s1.readReg64 .x29 = s0.sp - 608#64 + 512#64 ∧
        (P1 ⊢ preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗ A.pool lim st s1))
      Qp := by
  refine sepWPp_frame_pool_of_vm
    (prologue_entry_ne_nil_placed_wpX_vm hne hlt hpc hrun hsp hcl hx0 hx1 hx8) ?_
  intro s1 P1 ⟨hst1, hvm, h0, h1, h19, h29, hent1⟩
  exact ⟨hvm, ⟨fun _ _ => trivial, hst1, h0, h1, h19, h29, sepConj_mono_left hent1⟩⟩

/-- (``(vb >>> 4) < 3#8`, `VmPreserved` form`): `+40 → +1284`. -/
theorem prologue_28_legacyVer_placed_wpE_vm [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {vb : BitVec 8} {body : List (BitVec 8)} {s0 s1 : State}
    {Qp : State → SepProp → Prop}
    (hcons : x.bytes = vb :: body)
    (hlt3 : (vb >>> 4) < 3#8)
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s1)
    (hpc : s1.pc = (blkPl_111).base + 40#64)
    (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = x.ptr)
    (hx19 : s1.readReg64 .x19 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s1
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) sf ∧
        VmPreserved s1 sf ∧
        (Pf ⊢ pksmErrE A [] x.ret (.legacyCiphertextVersion (vb >>> 4)) ∗ (x.ptr ↦ₛ x.bytes)))
      Qp := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcond := cond_cs_ver_of_lt3 hlt3
  have hbytes : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ body) := by
    rw [hcons, pointsToBytes_cons]
  rw [hbytes]
  refine Wire.SepWPp.mono_pre (sepConj_mono_right (memRegion248_split_8_8_1 x.ret)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun bs16 => Wire.SepWPp.exists_pre fun ws8 =>
    Wire.SepWPp.exists_pre fun ws0 => ?_
  refine sepWPp_end_ls_vm keepsFrozenInv_codeRoLoaded hcl fun m_strip => ?_
  wp_steps
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun m_real hnsp hcl2 => ?_⟩
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hcl2, by simp [htr, arm64_norm]⟩, hnsp.toVmPreserved (by simp_all [arm64_norm]), ?_⟩
  have herr := errCells_legacyVersion A [] x.ret (vb >>> 4)
  unfold errTag speWord at herr
  change (x.ret ↦₆₄ 0xffffffffffffffff#64) ∗
    ((x.ret + 8#64) ↦₆₄ 9223372036854775812#64) ∗
    ((x.ret + 16#64) ↦₈ (vb >>> 4)) ∗
    memRegion (x.ret + 17#64) 231 ⊢ _ at herr
  refine Entails.trans (Q := ((x.ret ↦₆₄ 0xffffffffffffffff#64) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775812#64) ∗
      ((x.ret + 16#64) ↦₈ (vb >>> 4)) ∗
      memRegion (x.ret + 17#64) 231) ∗
      ((x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ body)))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← hbytes]
  exact sepConj_mono_left herr

/-- (``(vb >>> 4) < 3#8`, budget-pool form`): threads `A.pool lim st s1` to `A.pool lim st sf`. -/
theorem prologue_28_legacyVer_placed_wpE [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {vb : BitVec 8} {body : List (BitVec 8)} {s0 s1 : State}
    {Qp : State → SepProp → Prop}
    (hcons : x.bytes = vb :: body)
    (hlt3 : (vb >>> 4) < 3#8)
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s1)
    (hpc : s1.pc = (blkPl_111).base + 40#64)
    (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = x.ptr)
    (hx19 : s1.readReg64 .x19 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s1
      (((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248) ∗ A.pool lim st s1)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) sf ∧
        (Pf ⊢ pksmErrE A.repAlloc [] x.ret (.legacyCiphertextVersion (vb >>> 4)) ∗
          (x.ptr ↦ₛ x.bytes) ∗ A.pool lim st sf))
      Qp := by
  refine sepWPp_frame_pool_of_vm
    (prologue_28_legacyVer_placed_wpE_vm (A := A.repAlloc) hcons hlt3 hst hpc hrun hx0 hx19) ?_
  intro sf Pf ⟨hstf, hvm, hentf⟩
  refine ⟨hvm, ⟨fun _ _ => trivial, hstf, Entails.trans (sepConj_mono_left hentf) ?_⟩⟩
  apply entails_of_eq; ac_rfl

/-- (``¬ (vb >>> 4) < 3#8` and `4#8 < (vb >>> 4)`, `VmPreserved` form`): `+40 → +1284`. -/
theorem prologue_28_unrecognizedVer_placed_wpE_vm [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {vb : BitVec 8} {body : List (BitVec 8)} {s0 s1 : State}
    {Qp : State → SepProp → Prop}
    (hcons : x.bytes = vb :: body)
    (hge3 : ¬ (vb >>> 4) < 3#8) (hgt4 : 4#8 < (vb >>> 4))
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s1)
    (hpc : s1.pc = (blkPl_111).base + 40#64)
    (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = x.ptr)
    (hx19 : s1.readReg64 .x19 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s1
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) sf ∧
        VmPreserved s1 sf ∧
        (Pf ⊢ pksmErrE A [] x.ret (.unrecognizedCiphertextVersion (vb >>> 4)) ∗ (x.ptr ↦ₛ x.bytes)))
      Qp := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcond1 := cond_cs_ver_of_ge3 hge3
  have hcond2 := cond_ls_ver_of_gt4 hgt4
  have hbytes : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ body) := by
    rw [hcons, pointsToBytes_cons]
  rw [hbytes]
  refine Wire.SepWPp.mono_pre (sepConj_mono_right (memRegion248_split_8_8_1 x.ret)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun bs16 => Wire.SepWPp.exists_pre fun ws8 =>
    Wire.SepWPp.exists_pre fun ws0 => ?_
  refine sepWPp_end_ls_vm keepsFrozenInv_codeRoLoaded hcl fun m_strip => ?_
  wp_steps
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun m_real hnsp hcl2 => ?_⟩
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hcl2, by simp [htr, arm64_norm]⟩, hnsp.toVmPreserved (by simp_all [arm64_norm]), ?_⟩
  have herr := errCells_unrecognizedVersion A [] x.ret (vb >>> 4)
  unfold errTag speWord at herr
  change (x.ret ↦₆₄ 0xffffffffffffffff#64) ∗
    ((x.ret + 8#64) ↦₆₄ 9223372036854775813#64) ∗
    ((x.ret + 16#64) ↦₈ (vb >>> 4)) ∗
    memRegion (x.ret + 17#64) 231 ⊢ _ at herr
  refine Entails.trans (Q := ((x.ret ↦₆₄ 0xffffffffffffffff#64) ∗
      ((x.ret + 8#64) ↦₆₄ 9223372036854775813#64) ∗
      ((x.ret + 16#64) ↦₈ (vb >>> 4)) ∗
      memRegion (x.ret + 17#64) 231) ∗
      ((x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ body)))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← hbytes]
  exact sepConj_mono_left herr

/-- (``¬ (vb >>> 4) < 3#8` and `4#8 < (vb >>> 4)`, budget-pool form`): threads `A.pool lim st s1` to `A.pool lim st sf`. -/
theorem prologue_28_unrecognizedVer_placed_wpE [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {vb : BitVec 8} {body : List (BitVec 8)} {s0 s1 : State}
    {Qp : State → SepProp → Prop}
    (hcons : x.bytes = vb :: body)
    (hge3 : ¬ (vb >>> 4) < 3#8) (hgt4 : 4#8 < (vb >>> 4))
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s1)
    (hpc : s1.pc = (blkPl_111).base + 40#64)
    (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = x.ptr)
    (hx19 : s1.readReg64 .x19 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s1
      (((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248) ∗ A.pool lim st s1)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) sf ∧
        (Pf ⊢ pksmErrE A.repAlloc [] x.ret (.unrecognizedCiphertextVersion (vb >>> 4)) ∗
          (x.ptr ↦ₛ x.bytes) ∗ A.pool lim st sf))
      Qp := by
  refine sepWPp_frame_pool_of_vm
    (prologue_28_unrecognizedVer_placed_wpE_vm (A := A.repAlloc) hcons hge3 hgt4 hst hpc hrun hx0 hx19) ?_
  intro sf Pf ⟨hstf, hvm, hentf⟩
  refine ⟨hvm, ⟨fun _ _ => trivial, hstf, Entails.trans (sepConj_mono_left hentf) ?_⟩⟩
  apply entails_of_eq; ac_rfl

/-- Valid version step (`+40 → +128`, `VmPreserved` form). -/
theorem prologue_28_validVer_placed_wpX_vm [LibsignalPlacement] {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {vb : BitVec 8} {s0 s1 : State}
    {Qp : State → SepProp → Prop}
    (hge3 : ¬ (vb >>> 4) < 3#8) (hle4 : ¬ 4#8 < (vb >>> 4))
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s1)
    (hpc : s1.pc = (blkPl_111).base + 40#64)
    (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = x.ptr)
    (hx1 : s1.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s1.readReg64 .x19 = x.ret)
    (hx29 : s1.readReg64 .x29 = s0.sp - 608#64 + 512#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 128#64) s1
      (x.ptr ↦₈ vb)
      (fun s2 P2 =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) s2 ∧
        VmPreserved s1 s2 ∧
        s2.readReg64 .x29 = s0.sp - 608#64 + 512#64 ∧
        s2.readReg64 .x27 = 0x8000000000000002#64 ∧
        s2.readReg64 .x22 = vb.zeroExtend 64 ∧
        s2.readReg64 .x21 = x.ptr ∧
        s2.readReg64 .x19 = x.ret ∧
        s2.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length ∧
        (P2 ⊢ x.ptr ↦₈ vb))
      Qp := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcond1 := cond_cs_ver_of_ge3 hge3
  have hcond2 := cond_ls_ver_of_le4 hle4
  refine sepWPp_end_ls_vm keepsFrozenInv_codeRoLoaded hcl fun m_strip => ?_
  wp_steps
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun m_real hnsp hcl2 => ?_⟩
  exact ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hcl2, by simp [htr, arm64_norm]⟩,
    hnsp.toVmPreserved (by simp_all [arm64_norm]),
    by simp [hx29, arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm],
    by simp [hx19, arm64_norm], by simp [hx1, arm64_norm], Entails.refl _⟩

/-- Valid version step (`+40 → +128`, budget-pool form). -/
theorem prologue_28_validVer_placed_wpX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {vb : BitVec 8} {s0 s1 : State}
    {Qp : State → SepProp → Prop}
    (hge3 : ¬ (vb >>> 4) < 3#8) (hle4 : ¬ 4#8 < (vb >>> 4))
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s1)
    (hpc : s1.pc = (blkPl_111).base + 40#64)
    (hrun : s1.status = .Running)
    (hx0 : s1.readReg64 .x0 = x.ptr)
    (hx1 : s1.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s1.readReg64 .x19 = x.ret)
    (hx29 : s1.readReg64 .x29 = s0.sp - 608#64 + 512#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 128#64) s1
      ((x.ptr ↦₈ vb) ∗ A.pool lim st s1)
      (fun s2 P2 =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) s2 ∧
        s2.readReg64 .x29 = s0.sp - 608#64 + 512#64 ∧
        s2.readReg64 .x27 = 0x8000000000000002#64 ∧
        s2.readReg64 .x22 = vb.zeroExtend 64 ∧
        s2.readReg64 .x21 = x.ptr ∧
        s2.readReg64 .x19 = x.ret ∧
        s2.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length ∧
        (P2 ⊢ (x.ptr ↦₈ vb) ∗ A.pool lim st s2))
      Qp := by
  refine sepWPp_frame_pool_of_vm
    (prologue_28_validVer_placed_wpX_vm hge3 hle4 hst hpc hrun hx0 hx1 hx19 hx29) ?_
  intro s2 P2 ⟨hst2, hvm, h29, h27, h22, h21, h19, h1, hent2⟩
  exact ⟨hvm, ⟨fun _ _ => trivial, hst2, h29, h27, h22, h21, h19, h1, sepConj_mono_left hent2⟩⟩

/-- Field-slot initialization step (`+128 → +188`, `VmPreserved` form). -/
theorem prologue_80_init_placed_wpX_vm [LibsignalPlacement] {H : LibsignalHooks}
    {sret sp' ptr len : BitVec 64} {vb : BitVec 8} {s0 s2 : State}
    {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s2)
    (hpc : s2.pc = (blkPl_111).base + 128#64)
    (hrun : s2.status = .Running)
    (hx29 : s2.readReg64 .x29 = sp' + 512#64)
    (hx27 : s2.readReg64 .x27 = 0x8000000000000002#64)
    (hx22 : s2.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s2.readReg64 .x21 = ptr)
    (hx19 : s2.readReg64 .x19 = sret)
    (hx1 : s2.readReg64 .x1 = len) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 188#64) s2
      (memRegion (sp' + 296#64) 152)
      (fun s3 P3 =>
        PostEpilogueStatePlaced s0 sp' s3 ∧
        VmPreserved s2 s3 ∧
        s3.pstate = subsPState64 len 1#64 ∧
        s3.readReg64 .x29 = sp' + 512#64 ∧
        s3.readReg64 .x27 = 0x8000000000000002#64 ∧
        s3.readReg64 .x22 = vb.zeroExtend 64 ∧
        s3.readReg64 .x21 = ptr ∧
        s3.readReg64 .x20 = len ∧
        s3.readReg64 .x19 = sret ∧
        s3.readReg64 .x8 = sp' + 296#64 ∧
        s3.readReg64 .x2 = len - 1#64 ∧
        (P3 ⊢ ((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗
          ((sp' + 304#64) ↦₆₄ (len - 1#64)) ∗
          ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
          ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
          ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
          ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
          ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
      Qp := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  refine Wire.SepWPp.mono_pre (memRegion152_init_cells sp') ?_
  refine Wire.SepWPp.exists_pre fun w440 =>
    Wire.SepWPp.exists_pre fun w432 => Wire.SepWPp.exists_pre fun w424 =>
    Wire.SepWPp.exists_pre fun w416 => Wire.SepWPp.exists_pre fun w408 =>
    Wire.SepWPp.exists_pre fun w384 => Wire.SepWPp.exists_pre fun w360 =>
    Wire.SepWPp.exists_pre fun w336 => Wire.SepWPp.exists_pre fun w312 =>
    Wire.SepWPp.exists_pre fun c1 => Wire.SepWPp.exists_pre fun c0 => ?_
  refine sepWPp_end_ls_vm keepsFrozenInv_codeRoLoaded hcl fun m_strip => ?_
  wp_steps
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun m_real hnsp hcl3 => ?_⟩
  refine ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hcl3, by simp [htr, arm64_norm]⟩,
    hnsp.toVmPreserved (by simp_all [arm64_norm]),
    by simp [arm64_norm],
    by simp [hx29, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [arm64_norm], by simp [hx19, arm64_norm],
    by simp [arm64_norm], by simp [BitVec.sub_eq_add_neg, arm64_norm], ?_⟩
  unfold noneCap
  try simp only [arm64_norm]
  apply entails_of_eq; ac_rfl

/-- Field-slot initialization step (`+128 → +188`, budget-pool form). -/
theorem prologue_80_init_placed_wpX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {sret sp' ptr len : BitVec 64} {vb : BitVec 8} {s0 s2 : State}
    {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s2)
    (hpc : s2.pc = (blkPl_111).base + 128#64)
    (hrun : s2.status = .Running)
    (hx29 : s2.readReg64 .x29 = sp' + 512#64)
    (hx27 : s2.readReg64 .x27 = 0x8000000000000002#64)
    (hx22 : s2.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s2.readReg64 .x21 = ptr)
    (hx19 : s2.readReg64 .x19 = sret)
    (hx1 : s2.readReg64 .x1 = len) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 188#64) s2
      (memRegion (sp' + 296#64) 152 ∗ A.pool lim st s2)
      (fun s3 P3 =>
        PostEpilogueStatePlaced s0 sp' s3 ∧
        s3.pstate = subsPState64 len 1#64 ∧
        s3.readReg64 .x29 = sp' + 512#64 ∧
        s3.readReg64 .x27 = 0x8000000000000002#64 ∧
        s3.readReg64 .x22 = vb.zeroExtend 64 ∧
        s3.readReg64 .x21 = ptr ∧
        s3.readReg64 .x20 = len ∧
        s3.readReg64 .x19 = sret ∧
        s3.readReg64 .x8 = sp' + 296#64 ∧
        s3.readReg64 .x2 = len - 1#64 ∧
        (P3 ⊢ ((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗
          ((sp' + 304#64) ↦₆₄ (len - 1#64)) ∗
          ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
          ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
          ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
          ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
          ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ A.pool lim st s3))
      Qp := by
  refine sepWPp_frame_pool_of_vm
    (prologue_80_init_placed_wpX_vm hst hpc hrun hx29 hx27 hx22 hx21 hx19 hx1) ?_
  intro s3 P3 ⟨hst3, hvm, hpst, h29, h27, h22, h21, h20, h19, h8, h2, hent3⟩
  refine ⟨hvm, ⟨fun _ _ => trivial, hst3, hpst, h29, h27, h22, h21, h20, h19, h8, h2,
    Entails.trans (sepConj_mono_left hent3) ?_⟩⟩
  apply entails_of_eq; ac_rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ProloguePlacedBudget
