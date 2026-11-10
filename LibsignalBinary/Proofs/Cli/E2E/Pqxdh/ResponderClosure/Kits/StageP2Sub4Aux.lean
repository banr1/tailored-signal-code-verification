/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs

/-!
# Stage P2 Substage P2.4 Helpers, `None` Branch, and Post-Drop Tail

Provides `PreKeyRecord` layout helpers and proves `stageP2_sub4_none_kits` (`opkId? = none`,
`+0x0d5c → +0x36ac`) and the post-`futDrop` tail `stageP2_sub4_some_tail_kits` (`+0x0e40 →
+0x36ac`).
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
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

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

theorem p2_pkGetShim_pre_intro {A : RustAlloc} {img : Obj.Image}
    {pkKit : PreKeyStoreSpec A img.base} {x : PreKeyShimCall} {s : State}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hx0 : s.readReg64 .x0 = x.self) (hx1 : s.readReg32 .x1 = x.id) :
    A.pool ∗ stackAt s.sp pkKit.getShimStack ⊢
      ((kitPreKeyGetShimSpec pkKit).inImage img).pre x s := by
  dsimp only [Spec.inImage, kitPreKeyGetShimSpec]
  refine Entails.pure_right ⟨hF, hsym⟩ ?_
  refine Entails.pure_right ⟨hb, hx0, hx1⟩ ?_
  exact Entails.refl _

theorem p2_pkGetPoll_pre_intro {A : RustAlloc} {img : Obj.Image}
    {pkKit : PreKeyStoreSpec A img.base}
    {x : PreKeyPollCall} {st0 : pkKit.PkState} {s : State}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (henv : pkKit.envOk s.fs.files)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hx0 : s.readReg64 .x0 = x.fut) (hx8 : s.readReg64 .x8 = x.out)
    (hid : pkKit.getIdOk x.id) :
    pkKit.getBoxAt x.fut x.self x.id 0#8 ∗ pkKit.storeAt x.self st0 ∗
      memRegion x.out 56 ∗ A.pool ∗ stackAt s.sp pkKit.getPollStack ⊢
        ((kitPreKeyGetPollSpecE pkKit).inImage img).pre (x, st0) s := by
  dsimp only [Spec.inImage, kitPreKeyGetPollSpecE, withEnvPre, kitPreKeyGetPollSpec]
  refine Entails.pure_right ⟨hF, hsym⟩ ?_
  refine Entails.pure_right henv ?_
  refine Entails.pure_right ⟨hb, hx0, hx8, hid⟩ ?_
  exact Entails.refl _

theorem p2_kpShim_pre_intro {A : RustAlloc} {img : Obj.Image}
    {ikit : IdentityStoreSpec A img.base} {skit : IdentitySelfStoreSpec ikit}
    {self : BitVec 64} {s : State}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = self) :
    A.pool ∗ stackAt s.sp skit.kpShimStack ⊢
      ((kitKpShimSpec skit).inImage img).pre self s := by
  dsimp only [Spec.inImage, kitKpShimSpec]
  refine Entails.pure_right ⟨hF, hsym⟩ ?_
  refine Entails.pure_right hx0 ?_
  exact Entails.refl _

theorem p2_memRegion_65_pkPoll_split_eq (out : BitVec 64) :
    memRegion out 65 =
      memRegion out 56 ∗ (∃∗ u_38 : BitVec 64, (out + 0x38#64) ↦₆₄ u_38) ∗
        memRegion (out + 0x40#64) 1 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 56) (k := 9) (b' := out + 0x38#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x38#64) (n := 8) (k := 1) (b' := out + 0x40#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (out + 0x38#64)]

theorem p2_preKeyRecordAt_unpack (A : RustAlloc) (out u_38 : BitVec 64)
    (r : PreKeyRecord) :
    preKeyRecordAt A out r ∗ ((out + 0x38#64) ↦₆₄ u_38) ⊢
      ∃∗ pubCap : BitVec 64, ∃∗ pubPtr : BitVec 64,
      ∃∗ privCap : BitVec 64, ∃∗ privPtr : BitVec 64,
      ∃∗ pad32 : BitVec 32,
        preKeyRecordOut64At out
          pubCap pubPtr (BitVec.ofNat 64 r.preKey.publicKey.length)
          privCap privPtr (BitVec.ofNat 64 r.preKey.privateKey.length)
          (pad32 ++ r.preKey.id) u_38 ∗
        vecU8Buf A pubCap pubPtr r.preKey.publicKey ∗
        vecU8Buf A privCap privPtr r.preKey.privateKey := by
  unfold preKeyRecordAt RustHeap.vecU8
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun privCap => Entails.sepExists_elim fun privPtr =>
    Entails.sepExists_elim fun pubCap => Entails.sepExists_elim fun pubPtr => ?_
  rw [ProofLib.memRegion_four (out + 0x34#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun pad32 => ?_
  refine Entails.sepExists_right pubCap (Entails.sepExists_right pubPtr
    (Entails.sepExists_right privCap (Entails.sepExists_right privPtr
    (Entails.sepExists_right pad32 ?_))))
  rw [LibsignalTripleRatchet.Wire.vecU8At_eq_header_buf,
      LibsignalTripleRatchet.Wire.vecU8At_eq_header_buf]
  dsimp only [vecHeader, preKeyRecordOut64At]
  have hp30 : ((out + 0x30#64) ↦₃₂ r.preKey.id) ∗ ((out + 0x34#64) ↦₃₂ pad32) =
      ((out + 0x30#64) ↦₆₄ (pad32 ++ r.preKey.id)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (out + 0x30#64) r.preKey.id pad32
  rw [hp30]
  sep_norm
  exact Entails.of_eq (by ac_rfl)

theorem p2_pkKeyPairStack_le_pure : 176 ≤ stageP2PureAndErrStack :=
  p2_kp176_le_pure

theorem p2_memRegion_56_split_7words (p : BitVec 64) :
    memRegion p 56 =
      (∃∗ r6 : BitVec 64, ∃∗ r5 : BitVec 64, ∃∗ r4 : BitVec 64,
       ∃∗ r3 : BitVec 64, ∃∗ r2 : BitVec 64, ∃∗ r1 : BitVec 64,
       ∃∗ r0 : BitVec 64,
        (p ↦₆₄ r0) ∗ ((p + 0x08#64) ↦₆₄ r1) ∗ ((p + 0x10#64) ↦₆₄ r2) ∗
        ((p + 0x18#64) ↦₆₄ r3) ∗ ((p + 0x20#64) ↦₆₄ r4) ∗
        ((p + 0x28#64) ↦₆₄ r5) ∗ ((p + 0x30#64) ↦₆₄ r6)) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 48) (b' := p + 0x08#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x08#64) (n := 8) (k := 40) (b' := p + 0x10#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x10#64) (n := 8) (k := 32) (b' := p + 0x18#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x18#64) (n := 8) (k := 24) (b' := p + 0x20#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x20#64) (n := 8) (k := 16) (b' := p + 0x28#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x28#64) (n := 8) (k := 8) (b' := p + 0x30#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight p,
      ProofLib.memRegion_eight (p + 0x08#64),
      ProofLib.memRegion_eight (p + 0x10#64),
      ProofLib.memRegion_eight (p + 0x18#64),
      ProofLib.memRegion_eight (p + 0x20#64),
      ProofLib.memRegion_eight (p + 0x28#64),
      ProofLib.memRegion_eight (p + 0x30#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem p2_memRegion_9_sp270_eq (sp : BitVec 64) :
    memRegion (sp + 0x270#64) 9 =
      (∃∗ b_278 : BitVec 8, ∃∗ u_270 : BitVec 64,
        ((sp + 0x270#64) ↦₆₄ u_270) ∗ ((sp + 0x278#64) ↦₈ b_278)) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x270#64) (n := 8) (k := 1)
        (b' := sp + 0x278#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x270#64),
      ProofLib.memRegion_one (sp + 0x278#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem p2_sp270_9_entails_memRegion (sp u_270 : BitVec 64) (b_278 : BitVec 8) :
    ((sp + 0x270#64) ↦₆₄ u_270) ∗ ((sp + 0x278#64) ↦₈ b_278) ⊢
      memRegion (sp + 0x270#64) 9 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x270#64) (n := 8) (k := 1)
        (b' := sp + 0x278#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo8_entails_memRegion _ _)

theorem p2_preKeyRecordOut64_65_entails_memRegion (out w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    preKeyRecordOut64At out w0 w1 w2 w3 w4 w5 w6 w7 ∗ memRegion (out + 0x40#64) 1 ⊢
      memRegion out 65 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 64) (k := 1)
        (b' := out + 0x40#64) rfl (by bv_omega) (by decide)]
  refine sepConj_mono_left ?_
  dsimp only [preKeyRecordOut64At]
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 56) (b' := out + 0x08#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x08#64) (n := 8) (k := 48) (b' := out + 0x10#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x10#64) (n := 8) (k := 40) (b' := out + 0x18#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x18#64) (n := 8) (k := 32) (b' := out + 0x20#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 24) (b' := out + 0x28#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x28#64) (n := 8) (k := 16) (b' := out + 0x30#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x30#64) (n := 8) (k := 8) (b' := out + 0x38#64)
        rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (pointsTo64_entails_memRegion _ _)))))))

theorem p2_ro_intro_sepWPp {prog : Program} {ret : BitVec 64} {s : State}
    {Ro P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : ∀ {Q0 : SepProp}, s.mem ⊨ Q0 → s.mem ⊨ Ro ∗ Q0)
    (h : SepWPp prog ret s (Ro ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact hro hm

theorem p2_sub4_drop_sep_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P Drop Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = Drop ∗ Rest) (h : SepWPp prog ret s Rest Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

set_option maxHeartbeats 1200000 in
/-- Kit-generic Substage P2.4-None (`+0x0d5c -> +0x36ac`, `opkId? = none`,
`[msgPtr + 0x78] = 0#32`) in CPS form: stores `ctSlicePtr` at `[coroPtr + 0x488]`, sets
`[coroPtr + 0x4b0] = 0#8`, and invokes `skit.kpShim` reaching `+0x36ac` (`hOk`). -/
theorem stageP2_sub4_none_kits {A : RustAlloc}
    (img : Obj.Image) (ext : String → Option (State → State))
    (ikit : IdentityStoreSpec A img.base) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesOk img ikit skit)
    (hskitOk : IdentitySelfStoreKitOkI img ikit skit ext)
    (stk : Nat) (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    (coroPtr msgPtr ctxPtr idStorePtr ctSlicePtr v_b0 u_488 : BitVec 64)
    (opkId : BitVec 32) (b_4b0 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xd5c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = ctSlicePtr)
    (hOk : ∀ (idKpFutPtr : BitVec 64) (sf : State),
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x36ac#64 →
      sf.status = .Running → sf.sp = s.sp → sf.trace = s.trace →
      sf.readReg64 .x0 = idKpFutPtr → sf.readReg64 .x1 = img.base + skit.kpFutVtOff →
      idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = v_b0 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.sp + 0x370#64 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (A.live idKpFutPtr skit.kpBoxSize 8 ∗
         skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
         ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
         ((coroPtr + 0x4b0#64) ↦₈ 0#8) ∗
         ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         A.pool ∗ stackAt s.sp stk ∗ Frame)
        Q (PanicOomProp s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 0#32) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       A.pool ∗ stackAt s.sp stk ∗ Frame)
      Q (PanicOomProp s0) := by
  refine p2_ro_intro_sepWPp (hskitVt.kpSlot hF) ?_
  have hstep1 := p2_seg4_none_ext_wp img.base ext s coroPtr msgPtr ctxPtr
    idStorePtr ikit.id_vt (img.base + skit.kpShimOff) ctSlicePtr v_b0 u_488 opkId b_4b0
    hb hpc hrun hsp_align hx19 hx21
  refine p2_bind_sepWP_steps_frame hF hsym hstep1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx21_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  refine p2_sub4_drop_sep_frame
    (Drop := ((ikit.id_vt + 0x18#64) ↦₆₄ᵣ (img.base + skit.kpShimOff))) (by sep_focus) ?_
  have hstk_shim := p2_stackAt_split_of_le s.sp stk skit.kpShimStack hstk_kp_shim hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim) (by sep_focus) ?_
  sep_norm
  refine p2_call_oom_steps_frame
    (x := idStorePtr)
    hF1 hsym1 (htr1 ▸ htr) hskitOk.kpShim hpc1 hrun1 hsp1_al hx30_1
    (hsp1 ▸ p2_kpShim_pre_intro hF1 hsym1 hx0_1)
    (by sep_focus) (fun _ => Entails.refl _)
    (hnext := fun sf hst1f hpcf hrunf hspf_1 _ hcsf hFf hsymf => ?_)
  dsimp only [Spec.inImage, kitKpShimSpec]
  rcases hcsf with ⟨hcsf_19, _, hcsf_21, _, hcsf_23, hcsf_24, hcsf_25, hcsf_26, hcsf_27, hcsf_28,
    hcsf_29, hvregsf_1⟩
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_f, hx0_nz, hx0_al, htrf_1⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim.symm) (by sep_focus) ?_
  have hok := hOk (sf.readReg64 .x0) sf (hst01.trans hst1f) hpcf hrunf (hspf_1.trans hsp1)
    (htrf_1.trans htr1) rfl hx1_f hx0_nz hx0_al
    (hcsf_19.trans hx19_1) (hcsf_21.trans hx21_1) (hcsf_23.trans hx23_1)
    (hcsf_24.trans hx24_1) (hcsf_25.trans hx25_1) (hcsf_26.trans hx26_1)
    (hcsf_27.trans hx27_1) (hcsf_28.trans hx28_1) (hcsf_29.trans hx29_1)
    (by rw [hvregsf_1, hvregs1, hvregs]) hFf hsymf
  exact p2_sepWPp_weaken_eq hok (by sep_focus)

abbrev stageP2_sub4_none_kits_ext := @stageP2_sub4_none_kits
abbrev stageP2_sub4_none_kits_4k := @stageP2_sub4_none_kits
abbrev stageP2_sub4_none_kits_hooks := @stageP2_sub4_none_kits

theorem p2_words7_entails_memRegion_56 (p r0 r1 r2 r3 r4 r5 r6 : BitVec 64) :
    (p ↦₆₄ r0) ∗ ((p + 0x08#64) ↦₆₄ r1) ∗ ((p + 0x10#64) ↦₆₄ r2) ∗
    ((p + 0x18#64) ↦₆₄ r3) ∗ ((p + 0x20#64) ↦₆₄ r4) ∗
    ((p + 0x28#64) ↦₆₄ r5) ∗ ((p + 0x30#64) ↦₆₄ r6) ⊢
      memRegion p 56 := by
  rw [p2_memRegion_56_split_7words p]
  exact Entails.sepExists_right r6 (Entails.sepExists_right r5
    (Entails.sepExists_right r4 (Entails.sepExists_right r3
    (Entails.sepExists_right r2 (Entails.sepExists_right r1
    (Entails.sepExists_right r0 (Entails.refl _)))))))

theorem p2_cap_ne_neg3_of_lt {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    cap ≠ 0xfffffffffffffffd#64 :=
  fun hc => by subst hc; norm_num at hlt

set_option maxHeartbeats 1200000 in
/-- Post-`futDrop` tail (`+0x0e40 -> +0x36ac`) of `stageP2_sub4_some_kits`:
deallocates `opkFutPtr`, calls `PreKeyRecord::key_pair`, stores the clamped OPK keypair at
`coroPtr + 0x4b0..0x4f0`, frees `pubPtr`/`privPtr`, and invokes `skit.kpShim`. -/
theorem stageP2_sub4_some_tail_kits_ext {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A img.base ext) (hPure : StageP2PureCallees4K P A F img ext)
    (pkKit : PreKeyStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesOk img ikit skit)
    (hskitOk : IdentitySelfStoreKitOkI img ikit skit ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (s0 s6 : State) (sp : BitVec 64)
    (TailFrame : SepProp) (Q : State → SepProp → Prop)
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr opkFutPtr
     pubCap pubPtr privCap privPtr opkIdWord u_ac8 v_98 v_a0 v_b0 : BitVec 64)
    (opkId : BitVec 32) (opkPubBytes opkPrivBytes : List (BitVec 8))
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hpub_len : opkPubBytes.length = 32) (hpriv_len : opkPrivBytes.length = 32)
    (hpub_le : (5#8 :: opkPubBytes).length ≤ pubCap.toNat)
    (hpub_nz : pubCap ≠ 0#64) (hpub_ne1 : pubCap ≠ 0xffffffffffffffff#64)
    (hF6 : img.FrozenLoaded s6) (hsym6 : s6.symtab = img.symtab)
    (hpc6 : s6.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xe40#64)
    (hrun6 : s6.status = .Running) (hsp6 : s6.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr6 : s0.trace <+: s6.trace) (hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0)
    (hx19_6 : s6.readReg64 .x19 = coroPtr) (hx21_6 : s6.readReg64 .x21 = opkFutPtr)
    (hx22_6 : s6.readReg64 .x22 = pubCap) (hx23_6 : s6.readReg64 .x23 = 33#64)
    (hx24_6 : s6.readReg64 .x24 = img.base + pkKit.getFutVtOff)
    (hx26_6 : s6.readReg64 .x26 = pubPtr) (hx27_6 : s6.readReg64 .x27 = opkIdWord)
    (hx28_6 : s6.readReg64 .x28 = sp + 0xa90#64)
    (hDone : ∀ (idKpFutPtr : BitVec 64)
      (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
      (w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp : BitVec 64)
      (sf : State),
      Steps (tripleRatchetProgAtExt img.base ext) s6 sf →
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
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x36ac#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s6.trace →
      sf.readReg64 .x0 = idKpFutPtr → sf.readReg64 .x1 = img.base + skit.kpFutVtOff →
      idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = v_b0 →
      sf.readReg64 .x23 = v_a0 → sf.readReg64 .x24 = sp + 0x370#64 →
      sf.readReg64 .x25 = s6.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = s6.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (A.live idKpFutPtr skit.kpBoxSize 8 ∗
         skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
         ((sp + 0x98#64) ↦₆₄ v_98) ∗ ((sp + 0xa0#64) ↦₆₄ v_a0) ∗
         ((sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((sp + 0xb8#64) ↦₆₄ privCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (sp + 0x270#64) 9 ∗
         bytes7At (sp + 0x3b0#64) b0 b1 b2 b3 b4 b5 b6 ∗
         memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0x930#64) 56 ∗
         memRegion (sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x4b0#64) ↦₈ 1#8) ∗
         keyPair64UnalignedAt (coroPtr + 0x4b1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((img.base + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
         ((img.base + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         A.pool ∗ stackAt sp stk ∗ TailFrame)
        Q (PanicOomProp s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s6
      (pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
       A.live opkFutPtr pkKit.getBoxSize 8 ∗
       preKeyRecordOut64At (sp + 0xa90#64) pubCap pubPtr 33#64 privCap privPtr 32#64 opkIdWord u_ac8 ∗
       memRegion (sp + 0xad0#64) 1 ∗
       A.live pubPtr pubCap.toNat 1 ∗ (pubPtr ↦ₛ (5#8 :: opkPubBytes)) ∗
       memRegion (pubPtr + BitVec.ofNat 64 (5#8 :: opkPubBytes).length)
         (pubCap.toNat - (5#8 :: opkPubBytes).length) ∗
       vecU8Buf A privCap privPtr opkPrivBytes ∗
       ((sp + 0x98#64) ↦₆₄ v_98) ∗ ((sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ privCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (sp + 0x270#64) 9 ∗
       bytes7At (sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
       memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0x930#64) 56 ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       keyPair64UnalignedAt (coroPtr + 0x4b1#64) c0_init c1_init c2_init c3_init
         c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
         cw6_init c63_init ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((img.base + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((img.base + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.pool ∗ stackAt sp stk ∗ TailFrame)
      Q (PanicOomProp s0) := by
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
  refine SepWPp.weaken_frame (p2_vecU8Buf_nonempty A privCap privPtr opkPrivBytes (by omega))
    (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hpriv_le, _, hpriv_nz, _, _⟩ => ?_
  refine SepWPp.weaken_frame (pkKit.getBoxAt_memRegion opkFutPtr preKeyStorePtr opkId 1#8)
    (by sep_focus) ?_
  rw [show sp + 0xad0#64 = (sp + 0xa90#64) + 0x40#64 by bv_omega]
  refine SepWPp.weaken_frame
    (p2_preKeyRecordOut64_65_entails_memRegion (sp + 0xa90#64)
      pubCap pubPtr 33#64 privCap privPtr 32#64 opkIdWord u_ac8)
    (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le sp stk allocHookStack
    (Nat.le_trans p2_alloc_le_pure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_56_split_7words (sp + 0x930#64)))
    (by sep_focus) ?_
  rw [show (sp + 0x930#64) + 0x08#64 = sp + 0x938#64 by bv_omega,
      show (sp + 0x930#64) + 0x10#64 = sp + 0x940#64 by bv_omega,
      show (sp + 0x930#64) + 0x18#64 = sp + 0x948#64 by bv_omega,
      show (sp + 0x930#64) + 0x20#64 = sp + 0x950#64 by bv_omega,
      show (sp + 0x930#64) + 0x28#64 = sp + 0x958#64 by bv_omega,
      show (sp + 0x930#64) + 0x30#64 = sp + 0x960#64 by bv_omega]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun r6 => SepWPp.exists_elim fun r5 =>
    SepWPp.exists_elim fun r4 => SepWPp.exists_elim fun r3 =>
    SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun r1 =>
    SepWPp.exists_elim fun r0 => ?_
  have hstep7 := p2_seg4d_hooks_wp img.base ext hH s6 coroPtr opkFutPtr
    (img.base + pkKit.getFutVtOff) pubCap pubPtr privCap privPtr opkIdWord
    r0 r1 r2 r3 r4 r5 r6 pkKit.getBoxSize
    hpc6 hrun6 hsp6_align hpub_ne1 pkKit.getBoxSize_ne_zero pkKit.getBoxSize_lt
    hx19_6 hx21_6 hx22_6 hx23_6 hx24_6 hx26_6 hx27_6
  rw [hsp6] at hstep7
  refine p2_bind_sepWP_steps_frame hF6 hsym6 hstep7 (by sep_focus)
    fun s7 hst67 hpc7 hrun7 hF7 hsym7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7, htr7_6, hx0_7, hx8_7, hx19_7, _, hx22_7, _, _, hx25_7, hx26_7, _,
    hx28_7, hx29_7, hx30_7, hvregs7_6⟩
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_kp1 := p2_stackAt_split_of_le sp stk 176
    (Nat.le_trans p2_pkKeyPairStack_le_pure hstk_pure) hstk_lt
  have hstk_kp2 := stackAt_176_keypair_eq sp
  have hmr88_split : memRegion (sp + 0x3e0#64) 88 =
      memRegion (sp + 0x3e0#64) 65 ∗ memRegion (sp + 0x421#64) 23 :=
    ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 65) (k := 23)
      (b' := sp + 0x421#64) rfl (by bv_omega) (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq hstk_kp1) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_kp2) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hmr88_split) (by sep_focus) ?_
  sep_norm
  have h938 : (sp + 0x930#64) + 8#64 = sp + 0x938#64 := by bv_omega
  have h940 : (sp + 0x930#64) + 16#64 = sp + 0x940#64 := by bv_omega
  have h948 : (sp + 0x930#64) + 24#64 = sp + 0x948#64 := by bv_omega
  have h950 : (sp + 0x930#64) + 32#64 = sp + 0x950#64 := by bv_omega
  have h958 : (sp + 0x930#64) + 40#64 = sp + 0x958#64 := by bv_omega
  have h960 : (sp + 0x930#64) + 48#64 = sp + 0x960#64 := by bv_omega
  refine p2_call_nopanic_steps_frame
    (x := (sp + 0x930#64, pubPtr, opkPubBytes, privPtr, opkPrivBytes, sp + 0x3e0#64))
    (T := (((sp + 0x930#64) + 8#64) ↦₆₄ pubPtr) ∗ (((sp + 0x930#64) + 16#64) ↦₆₄ 33#64) ∗
      (((sp + 0x930#64) + 32#64) ↦₆₄ privPtr) ∗ (((sp + 0x930#64) + 40#64) ↦₆₄ 32#64) ∗
      (pubPtr ↦ₛ (5#8 :: opkPubBytes)) ∗ (privPtr ↦ₛ opkPrivBytes) ∗
      memRegion (sp + 0x3e0#64) 65 ∗ cells (sp - 176#64) 8 ∗ cells (sp - 112#64) 14)
    hF7 hsym7 hPure.preKeyRecordKeyPair hpc7 hrun7 hsp7_al hx30_7
    (by dsimp only [preKeyRecordKeyPairOkSpec]; rw [hsp7])
    (And.intro hx0_7 (And.intro hx8_7 (And.intro hpub_len hpriv_len)))
    (by rw [h938, h940, h950, h958]; sep_focus)
    (hnext := fun s8 hst78 hpc8 hrun8 hsp8_7 _ hcs8 hF8 hsym8 => ?_)
  dsimp only [preKeyRecordKeyPairOkSpec]
  rcases hcs8 with ⟨hcs8_19, _, _, hcs8_22, _, _, hcs8_25, hcs8_26, _, hcs8_28, hcs8_29, hvregs8_7⟩
  have hsp8 : s8.sp = sp := hsp8_7.trans hsp7
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8]; exact hsp_align
  have h3e1 : (sp + 0x3e0#64) + 1#64 = sp + 0x3e1#64 := by bv_omega
  have h401 : (sp + 0x3e0#64) + 33#64 = sp + 0x401#64 := by bv_omega
  rw [hsp7, h938, h940, h950, h958, h3e1, h401]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr8_7 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_kp2.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_kp1.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_words7_entails_memRegion_56 (sp + 0x930#64)
      pubCap pubPtr 33#64 privCap privPtr 32#64 opkIdWord)
    (by rw [h938, h940, h948, h950, h958, h960]; sep_focus) ?_
  have hclamp_len : (clampBv8List opkPrivBytes).length = 32 := clampBv8List_length hpriv_len
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b63, c0, c1, c2, c3, c4, c5, c6,
    w0, w1, w2, w3, w4, w5, w6, u0_kp, u1_kp, u2_kp, u3_kp, u4_kp, u5_kp, u6_kp, u7_kp,
    hpk_words, hsk_words, hkp64_eq, hkp_lo, hkp_hi⟩ := exists_keyPair64_decomp hpub_len hclamp_len
  have h3e1_eq : ((sp + 0x3e1#64) ↦ₛ opkPubBytes) ∗ ((sp + 0x401#64) ↦ₛ clampBv8List opkPrivBytes) =
      keyPair64UnalignedAt (sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 := by
    rw [show sp + 0x401#64 = (sp + 0x3e1#64) + 32#64 by bv_omega]; exact hkp64_eq (sp + 0x3e1#64)
  refine SepWPp.weaken_frame (Entails.of_eq h3e1_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_vecU8Buf_rejoin pubPtr pubCap (5#8 :: opkPubBytes) hpub_le) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_vecU8Buf_rejoin privPtr privCap opkPrivBytes hpriv_le) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_9_sp270_eq sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b_278 => SepWPp.exists_elim fun u_270 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  refine p2_ro_intro_sepWPp (hskitVt.kpSlot hF8) ?_
  sep_norm
  have hstep9 := p2_seg4e_hooks_wp img.base ext hH s8 coroPtr msgPtr ctxPtr pubCap pubPtr privCap privPtr
    idStorePtr ikit.id_vt (img.base + skit.kpShimOff) v_98 v_a0 v_b0 u_270 opkId b0 b1 b2 b3 b4 b5 b6 b63
    s0_b s1_b s2_b s3_b s4_b s5_b s6_b c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init b_4b0 b_278
    w0 w1 w2 w3 w4 w5 w6 cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    hpc8 hrun8 hsp8_align hpub_nz hpriv_nz (hcs8_19.trans hx19_7) (hcs8_22.trans hx22_7) (hcs8_26.trans hx26_7)
  rw [hsp8] at hstep9
  refine p2_bind_sepWP_steps_frame hF8 hsym8 hstep9 (by sep_focus)
    fun s9 hst89 hpc9 hrun9 hF9 hsym9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9, htr9_8, hx0_9, hx19_9, hx21_9, hx23_9, hx24_9, hx25_9, hx26_9, hx27_9,
    hx28_9, hx29_9, hx30_9, hvregs9_8⟩
  have hsp9_al : s9.spAligned = true := by simpa only [State.spAligned, hsp9] using hsp_align
  refine p2_sub4_drop_sep_frame
    (Drop := ((ikit.id_vt + 0x18#64) ↦₆₄ᵣ (img.base + skit.kpShimOff))) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_sp270_9_entails_memRegion sp w6 b63) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq h3e1_eq.symm) (by sep_focus) ?_
  rw [← h3e1, ← h401]
  refine SepWPp.weaken_frame
    (sp_a90_65_entails_memRegion (sp + 0x3e0#64) 0#8 opkPubBytes (clampBv8List opkPrivBytes)
      hpub_len hclamp_len) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hmr88_split.symm) (by sep_focus) ?_
  have hstk_kp_shim := p2_stackAt_split_of_le sp stk skit.kpShimStack hstk_kp_shim hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_kp_shim) (by sep_focus) ?_
  sep_norm
  have htr9 : s9.trace = s6.trace := by rw [htr9_8, htr8_7, htr7_6]
  refine p2_call_oom_steps_frame (x := idStorePtr) hF9 hsym9 (htr9 ▸ htr6) hskitOk.kpShim
    hpc9 hrun9 hsp9_al hx30_9 (hsp9 ▸ p2_kpShim_pre_intro hF9 hsym9 hx0_9)
    (by sep_focus) (fun _ => Entails.refl _)
    (hnext := fun sf hst9f hpcf hrunf hspf_9 _ hcsf hFf hsymf => ?_)
  dsimp only [Spec.inImage, kitKpShimSpec]
  rcases hcsf with ⟨hcsf_19, _, hcsf_21, _, hcsf_23, hcsf_24, hcsf_25, hcsf_26, hcsf_27, hcsf_28,
    hcsf_29, hvregsf_9⟩
  rw [hsp9]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_f, hx0_nz, hx0_al, htrf_9⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_kp_shim.symm) (by sep_focus) ?_
  have hst6f := hst67.trans (hst78.trans (hst89.trans hst9f))
  have hdone := hDone (sf.readReg64 .x0) b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6
    w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp sf
    hst6f hpk_words hsk_words hkp_lo hkp_hi
    hpcf hrunf (hspf_9.trans hsp9) (htrf_9.trans htr9) rfl hx1_f hx0_nz hx0_al
    (hcsf_19.trans hx19_9) (hcsf_21.trans hx21_9) (hcsf_23.trans hx23_9) (hcsf_24.trans hx24_9)
    (by rw [hcsf_25, hx25_9, hcs8_25, hx25_7])
    (hcsf_26.trans hx26_9) (hcsf_27.trans hx27_9)
    (by rw [hcsf_28, hx28_9, hcs8_28, hx28_7, hx28_6])
    (by rw [hcsf_29, hx29_9, hcs8_29, hx29_7])
    (by rw [hvregsf_9, hvregs9_8, hvregs8_7, hvregs7_6, hvregs6]) hFf hsymf
  exact p2_sepWPp_weaken_eq hdone (by sep_focus)

abbrev stageP2_sub4_some_tail_kits_4k := @stageP2_sub4_some_tail_kits_ext
abbrev stageP2_sub4_some_tail_kits_hooks := @stageP2_sub4_some_tail_kits_ext

theorem stageP2_sub4_some_tail_kits {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext) (hPure : StageP2PureCallees P A F img ext)
    (pkKit : PreKeyStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base) (skit : IdentitySelfStoreSpec ikit)
    (hskitVt : IdentitySelfVtablesOk img ikit skit)
    (hskitOk : IdentitySelfStoreKitOkI img ikit skit ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (s0 s6 : State) (sp : BitVec 64)
    (TailFrame : SepProp) (Q : State → SepProp → Prop)
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr opkFutPtr
     pubCap pubPtr privCap privPtr opkIdWord u_ac8 v_98 v_a0 v_b0 : BitVec 64)
    (opkId : BitVec 32) (opkPubBytes opkPrivBytes : List (BitVec 8))
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hpub_len : opkPubBytes.length = 32) (hpriv_len : opkPrivBytes.length = 32)
    (hpub_le : (5#8 :: opkPubBytes).length ≤ pubCap.toNat)
    (hpub_nz : pubCap ≠ 0#64) (hpub_ne1 : pubCap ≠ 0xffffffffffffffff#64)
    (hF6 : img.FrozenLoaded s6) (hsym6 : s6.symtab = img.symtab)
    (hpc6 : s6.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xe40#64)
    (hrun6 : s6.status = .Running) (hsp6 : s6.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr6 : s0.trace <+: s6.trace) (hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0)
    (hx19_6 : s6.readReg64 .x19 = coroPtr) (hx21_6 : s6.readReg64 .x21 = opkFutPtr)
    (hx22_6 : s6.readReg64 .x22 = pubCap) (hx23_6 : s6.readReg64 .x23 = 33#64)
    (hx24_6 : s6.readReg64 .x24 = img.base + pkKit.getFutVtOff)
    (hx26_6 : s6.readReg64 .x26 = pubPtr) (hx27_6 : s6.readReg64 .x27 = opkIdWord)
    (hx28_6 : s6.readReg64 .x28 = sp + 0xa90#64)
    (hDone : ∀ (idKpFutPtr : BitVec 64)
      (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
      (w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp : BitVec 64)
      (sf : State),
      Steps (tripleRatchetProgAtExt img.base ext) s6 sf →
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
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x36ac#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s6.trace →
      sf.readReg64 .x0 = idKpFutPtr → sf.readReg64 .x1 = img.base + skit.kpFutVtOff →
      idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = v_b0 →
      sf.readReg64 .x23 = v_a0 → sf.readReg64 .x24 = sp + 0x370#64 →
      sf.readReg64 .x25 = s6.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = s6.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (A.live idKpFutPtr skit.kpBoxSize 8 ∗
         skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
         ((sp + 0x98#64) ↦₆₄ v_98) ∗ ((sp + 0xa0#64) ↦₆₄ v_a0) ∗
         ((sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((sp + 0xb8#64) ↦₆₄ privCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (sp + 0x270#64) 9 ∗
         bytes7At (sp + 0x3b0#64) b0 b1 b2 b3 b4 b5 b6 ∗
         memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0x930#64) 56 ∗
         memRegion (sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x4b0#64) ↦₈ 1#8) ∗
         keyPair64UnalignedAt (coroPtr + 0x4b1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((img.base + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
         ((img.base + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         A.pool ∗ stackAt sp stk ∗ TailFrame)
        Q (PanicOomProp s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s6
      (pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
       A.live opkFutPtr pkKit.getBoxSize 8 ∗
       preKeyRecordOut64At (sp + 0xa90#64) pubCap pubPtr 33#64 privCap privPtr 32#64 opkIdWord u_ac8 ∗
       memRegion (sp + 0xad0#64) 1 ∗
       A.live pubPtr pubCap.toNat 1 ∗ (pubPtr ↦ₛ (5#8 :: opkPubBytes)) ∗
       memRegion (pubPtr + BitVec.ofNat 64 (5#8 :: opkPubBytes).length)
         (pubCap.toNat - (5#8 :: opkPubBytes).length) ∗
       vecU8Buf A privCap privPtr opkPrivBytes ∗
       ((sp + 0x98#64) ↦₆₄ v_98) ∗ ((sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ privCap) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (sp + 0x270#64) 9 ∗
       bytes7At (sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
       memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0x930#64) 56 ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       keyPair64UnalignedAt (coroPtr + 0x4b1#64) c0_init c1_init c2_init c3_init
         c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
         cw6_init c63_init ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((img.base + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((img.base + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.pool ∗ stackAt sp stk ∗ TailFrame)
      Q (PanicOomProp s0) :=
  stageP2_sub4_some_tail_kits_ext img ext (.of_allocContracts hA) hPure.to_4K pkKit ikit skit
    hskitVt hskitOk stk hstk_pure hstk_kp_shim hstk_lt ret s0 s6 sp TailFrame Q
    coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr opkFutPtr
    pubCap pubPtr privCap privPtr opkIdWord u_ac8 v_98 v_a0 v_b0
    opkId opkPubBytes opkPrivBytes b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
    cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    hpub_len hpriv_len hpub_le hpub_nz hpub_ne1
    hF6 hsym6 hpc6 hrun6 hsp6 hsp_align htr6 hvregs6
    hx19_6 hx21_6 hx22_6 hx23_6 hx24_6 hx26_6 hx27_6 hx28_6 hDone

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
