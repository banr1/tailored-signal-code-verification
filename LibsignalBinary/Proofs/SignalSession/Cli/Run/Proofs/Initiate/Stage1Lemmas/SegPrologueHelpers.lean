/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Stage 1 Frame Combinators and Early Error Exits

Provides `SepWPp` stepping helpers, 32-byte word pack/unpack lemmas, `cliBundleBody`, prologue and
poll stack-frame split/merge lemmas, and the shared Stage 1 early `Err` exit paths
(`stage1_plain11_exit_ext_ok`, `stage1_untrusted_exit_ext_ok`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  cliInitiateFrame initLocalsSize
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero

/-- Steps a `SepWP` basic-block segment inside `SepWPp` under `ImgCallInv img s`. -/
theorem sepWPp_step_to {prog : Program} {img : Obj.Image} (mid : BitVec 64) {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P
      (fun sm Pm => ∀ sNext : State, sm = sNext →
        sNext.pc = mid → sNext.status = .Running → ImgCallInv img sNext →
        SepWPp prog ret sNext Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hnext⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext sm rfl hpc hrun (hinv.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_drop_left {prog : Program} {tgt : BitVec 64} {s : State}
    {cell P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hnext : SepWPp prog tgt s P Q Qp oom) :
    SepWPp prog tgt s (cell ∗ P) Q Qp oom := by
  intro R hm hL
  exact hnext R (Satisfies.of_sep_right (by rwa [sepConj_assoc] at hm)) hL

theorem sepWPp_exists_left {α : Type} {prog : Program} {tgt : BitVec 64} {s : State}
    {F : α → SepProp} {R : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x, SepWPp prog tgt s (F x ∗ R) Q Qp oom) :
    SepWPp prog tgt s ((∃∗ x, F x) ∗ R) Q Qp oom := by
  rw [sepExists_sepConj_left]
  exact sepWPp_exists_elim h

theorem sepWPp_exists_pos2 {α : Type} {prog : Program} {tgt : BitVec 64} {s : State}
    {A : SepProp} {F : α → SepProp} {R : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x, SepWPp prog tgt s (A ∗ F x ∗ R) Q Qp oom) :
    SepWPp prog tgt s (A ∗ (∃∗ x, F x) ∗ R) Q Qp oom := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  exact sepWPp_exists_elim h

theorem sepWPp_exists_pos3 {α : Type} {prog : Program} {tgt : BitVec 64} {s : State}
    {A B : SepProp} {F : α → SepProp} {R : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x, SepWPp prog tgt s (A ∗ B ∗ F x ∗ R) Q Qp oom) :
    SepWPp prog tgt s (A ∗ B ∗ (∃∗ x, F x) ∗ R) Q Qp oom := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  exact sepWPp_exists_elim h

theorem sepWPp_exists_pos4 {α : Type} {prog : Program} {tgt : BitVec 64} {s : State}
    {A B C : SepProp} {F : α → SepProp} {R : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x, SepWPp prog tgt s (A ∗ B ∗ C ∗ F x ∗ R) Q Qp oom) :
    SepWPp prog tgt s (A ∗ B ∗ C ∗ (∃∗ x, F x) ∗ R) Q Qp oom := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right,
    sepExists_sepConj_right]
  exact sepWPp_exists_elim h

theorem spAligned_of_sp_eq {s1 s2 : State} (h1 : s1.spAligned = true) (hsp : s2.sp = s1.sp) :
    s2.spAligned = true := by
  simpa only [State.spAligned, hsp] using h1

theorem spAligned_of_frame {s0 s : State}
    (hal0 : s0.spAligned = true)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) :
    s.spAligned = true := by
  simp only [State.spAligned, beq_iff_eq] at hal0 ⊢
  rw [hsp, show cliInitiateFrame = 7408 from rfl]
  have hmod0 : s0.sp.toNat % 16 = 0 := by
    have ht := congrArg BitVec.toNat hal0
    rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (0#64).toNat = 0 from rfl] at ht
    exact ht
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, show (0#64).toNat = 0 from rfl, BitVec.toNat_sub,
    show (7408#64).toNat = 7408 from rfl]
  have hlt : s0.sp.toNat < 2 ^ 64 := s0.sp.isLt
  omega

theorem cs_x19 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := h.1
theorem cs_x20 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) := h.2.1
theorem cs_x21 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) := h.2.2.1
theorem cs_x22 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) := h.2.2.2.1
theorem cs_x23 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := h.2.2.2.2.1
theorem cs_x24 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := h.2.2.2.2.2.1
theorem cs_x25 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) := h.2.2.2.2.2.2.1
theorem cs_x26 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) := h.2.2.2.2.2.2.2.1
theorem cs_x27 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := h.2.2.2.2.2.2.2.2.1
theorem cs_x28 {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := h.2.2.2.2.2.2.2.2.2.1
theorem cs_fp {s sm : State} (h : CalleeSavedPreserved s sm) :
    sm.readReg64 .fp = s.readReg64 .fp := h.2.2.2.2.2.2.2.2.2.2.1
theorem cs_vregs {s sm : State} (h : CalleeSavedPreserved s sm) :
    calleeSavedVRegs sm = calleeSavedVRegs s := h.2.2.2.2.2.2.2.2.2.2.2

/-- `cliIdFutDropName` is non-null in any loaded image, so `cbz x8` never skips `futDrop`. -/
theorem cliIdFutDrop_ne_zero_ext {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    ((libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr KitInst.cliIdFutDropName == 0#64) = false := by
  obtain ⟨_, _, hb, _, _, _⟩ := ProofLib.ObjectLoad.load_eq_ok himg
  rw [Program.fnAddr_rebase, KitInst.cliIdFutDrop_fnOff, beq_eq_false_iff_ne]
  intro h
  rw [show img.base = 0#64 - KitInst.cliIdFutDropOff by
    change img.base + KitInst.cliIdFutDropOff = 0#64 at h
    rw [← h, BitVec.add_sub_cancel]] at hb
  exact absurd hb (by decide)

theorem cliIdFutDrop_ne_zero {img : Obj.Image} {W : CliHooks}
    (himg : Obj.Loads libsignalSessionImage img) :
    ((libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr KitInst.cliIdFutDropName == 0#64) = false :=
  cliIdFutDrop_ne_zero_ext (ext := cliHookExterns W) himg

@[irreducible] def futDropAddr_ext (img : Obj.Image)
    (ext : String → Option (State → State)) : BitVec 64 :=
  (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr KitInst.cliIdFutDropName

theorem futDropAddr_ext_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    futDropAddr_ext img ext =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr KitInst.cliIdFutDropName := by
  unfold futDropAddr_ext; rfl

theorem futDropAddr_ext_ne_zero {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    (futDropAddr_ext img ext == 0#64) = false := by
  rw [futDropAddr_ext_eq]; exact cliIdFutDrop_ne_zero_ext (ext := ext) himg

theorem rodata_idTrustFut_drop_irr_ext {img : Obj.Image}
    {ext : String → Option (State → State)} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((img.base + idTrustFutVtOff) ↦₆₄ᵣ futDropAddr_ext img ext) ∗ R) := by
  rw [futDropAddr_ext_eq]; exact rodata_idTrustFut_drop_ext (ext := ext) himg hF

@[irreducible] def idTrustPollAddr_ext (img : Obj.Image)
    (ext : String → Option (State → State)) : BitVec 64 :=
  (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr idTrustPollName

theorem idTrustPollAddr_ext_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    idTrustPollAddr_ext img ext =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr idTrustPollName := by
  unfold idTrustPollAddr_ext; rfl

theorem rodata_idTrustFut_poll_irr_ext {img : Obj.Image}
    {ext : String → Option (State → State)} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((img.base + idTrustFutVtOff) + 24#64) ↦₆₄ᵣ idTrustPollAddr_ext img ext) ∗ R) := by
  rw [idTrustPollAddr_ext_eq]; exact rodata_idTrustFut_poll_ext (ext := ext) himg hF

theorem bytes32_eq_exists_words4 (p : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 32) :
    (p ↦ₛ bs) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ⌜bs = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3⌝ ∗
        (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) := by
  obtain ⟨w0, w1, w2, w3, hw, hsep⟩ := exists_unpack64_of_length_32 hlen
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_)))
  refine pure_sepConj_intro hw ?_
  rw [hsep p]
  sep_frame

theorem words4_to_bytes32 (q : BitVec 64) {bs : List (BitVec 8)}
    {w0 w1 w2 w3 : BitVec 64}
    (hbs : bs = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3) :
    (q ↦₆₄ w0) ∗ ((q + 8#64) ↦₆₄ w1) ∗ ((q + 16#64) ↦₆₄ w2) ∗ ((q + 24#64) ↦₆₄ w3) ⊢
      (q ↦ₛ bs) := by
  rw [hbs, List.append_assoc, List.append_assoc,
      pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack64_length, ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem memRegion_32_words (a : BitVec 64) :
    memRegion a 32 =
      ∃∗ d3 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d0 : BitVec 64,
        (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3) := by
  have split8 : ∀ p n, n ≥ 8 → n ≤ 32 →
      memRegion p n = (∃∗ w : BitVec 64, p ↦₆₄ w) ∗ memRegion (p + 8#64) (n - 8) := by
    intro p n hge _hle
    have hn : n = 8 + (n - 8) := by omega
    conv_lhs => rw [hn]
    rw [memRegion_split p 8 (n - 8) (by omega), ProofLib.memRegion_eight]
  rw [split8 a 32 (by decide) (by decide),
      split8 _ 24 (by decide) (by decide),
      split8 _ 16 (by decide) (by decide),
      ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]

theorem boxU8Buf_serialize_unpack (A : RustAlloc) (ptr : BitVec 64) (pk : PublicKey) :
    boxU8Buf A ptr pk.serialize ⊢
      ⌜ptr ≠ 0#64⌝ ∗ A.live ptr 33 1 ∗ (ptr ↦ₛ pk.serialize) := by
  unfold boxU8Buf
  have hne : pk.serialize ≠ [] := by simp [PublicKey.serialize]
  have hlen : pk.serialize.length = 33 := by simp [PublicKey.serialize]
  rw [ite_eq_right_iff.mpr fun h => absurd h hne, hlen]
  exact pure_sepConj_elim fun ⟨hp, _⟩ => pure_sepConj_intro hp (Entails.refl _)

/-- Spatial body of `cliBundleAt` at a fixed `opkId`. -/
def cliBundleBody (a : BitVec 64) (b : BundleV) (spkSigPtr kpkSigPtr kpkPtr : BitVec 64)
    (opkId : BitVec 32) : SepProp :=
  let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
  (a ↦₆₄ 64#64) ∗ ((a + 8#64) ↦₆₄ spkSigPtr) ∗ ((a + 16#64) ↦₆₄ 64#64) ∗
    (spkSigPtr ↦ₛ b.spkSig) ∗
    ((a + 24#64) ↦ₛ b.spk.bytes.toList) ∗
    ((a + 56#64) ↦₃₂ b.spkId) ∗ memRegion (a + 60#64) 4 ∗
    ((a + 64#64) ↦₆₄ 64#64) ∗ ((a + 72#64) ↦₆₄ kpkSigPtr) ∗ ((a + 80#64) ↦₆₄ 64#64) ∗
    (kpkSigPtr ↦ₛ b.kpkSig) ∗
    ((a + 88#64) ↦₆₄ kpkPtr) ∗ ((a + 96#64) ↦₆₄ 1568#64) ∗ (kpkPtr ↦ₛ b.kpk) ∗
    ((a + 104#64) ↦₃₂ b.kpkId) ∗ memRegion (a + 108#64) 4 ∗
    ((a + 112#64) ↦₃₂ opkFlag) ∗ ((a + 116#64) ↦₃₂ opkId) ∗
    ((a + 120#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗ ((a + 152#64) ↦₃₂ b.regId) ∗
    ((a + 156#64) ↦₈ opkFlag.truncate 8) ∗
    (match b.opk with
     | some (_, k) => (a + 157#64) ↦ₛ k.bytes.toList
     | none => memRegion (a + 157#64) 32) ∗
    ((a + 189#64) ↦₈ b.device) ∗ memRegion (a + 190#64) 2

theorem cliBundleAt_unpack (a : BitVec 64) (b : BundleV)
    (spkSigPtr kpkSigPtr kpkPtr : BitVec 64) :
    cliBundleAt a b spkSigPtr kpkSigPtr kpkPtr =
      ∃∗ opkId : BitVec 32,
        ⌜b.spkSig.length = 64 ∧ b.kpkSig.length = 64 ∧ b.kpk.length = 1568 ∧
          ∀ p, b.opk = some p → opkId = p.1⌝ ∗
        cliBundleBody a b spkSigPtr kpkSigPtr kpkPtr opkId := rfl

theorem cliBundleBody_pack {a : BitVec 64} {b : BundleV}
    {spkSigPtr kpkSigPtr kpkPtr : BitVec 64} {opkId : BitVec 32}
    (h1 : b.spkSig.length = 64) (h2 : b.kpkSig.length = 64) (h3 : b.kpk.length = 1568)
    (hopk : ∀ p, b.opk = some p → opkId = p.1) :
    cliBundleBody a b spkSigPtr kpkSigPtr kpkPtr opkId ⊢
      cliBundleAt a b spkSigPtr kpkSigPtr kpkPtr := by
  rw [cliBundleAt_unpack]
  exact Entails.sepExists_right opkId (pure_sepConj_intro ⟨h1, h2, h3, hopk⟩ (Entails.refl _))

/-- Splits `memRegion fsp initLocalsSize` into individual cells for the `0x0000..0x0098` prologue stores. -/
theorem prologue_locals_split (fsp : BitVec 64) :
    memRegion fsp initLocalsSize ⊢
      ∃∗ l0 : BitVec 64, ∃∗ l80 : BitVec 64, ∃∗ l88 : BitVec 32,
      ∃∗ l90 : BitVec 64, ∃∗ l98 : BitVec 64, ∃∗ la0 : BitVec 64, ∃∗ la8 : BitVec 64,
      ∃∗ lb0 : BitVec 64, ∃∗ lb8 : BitVec 64, ∃∗ lc0 : BitVec 64, ∃∗ lc8 : BitVec 64,
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64, ∃∗ a3 : BitVec 64,
      ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64, ∃∗ a6 : BitVec 64, ∃∗ a7 : BitVec 64,
      ∃∗ a8 : BitVec 32, ∃∗ a9 : BitVec 64, ∃∗ a10 : BitVec 64,
      ∃∗ flag16 : BitVec 16,
      ∃∗ wk0 : BitVec 64, ∃∗ wk1 : BitVec 64, ∃∗ wk2 : BitVec 64,
      ∃∗ probe : BitVec 64,
        (fsp ↦₆₄ l0) ∗ memRegion (fsp + 0x08#64) 0x78 ∗
        ((fsp + 0x80#64) ↦₆₄ l80) ∗ ((fsp + 0x88#64) ↦₃₂ l88) ∗ memRegion (fsp + 0x8c#64) 4 ∗
        ((fsp + 0x90#64) ↦₆₄ l90) ∗ ((fsp + 0x98#64) ↦₆₄ l98) ∗
        ((fsp + 0xa0#64) ↦₆₄ la0) ∗ ((fsp + 0xa8#64) ↦₆₄ la8) ∗
        ((fsp + 0xb0#64) ↦₆₄ lb0) ∗ ((fsp + 0xb8#64) ↦₆₄ lb8) ∗
        ((fsp + 0xc0#64) ↦₆₄ lc0) ∗ ((fsp + 0xc8#64) ↦₆₄ lc8) ∗
        ((fsp + 0xd0#64) ↦₆₄ a0) ∗ ((fsp + 0xd8#64) ↦₆₄ a1) ∗
        ((fsp + 0xe0#64) ↦₆₄ a2) ∗ ((fsp + 0xe8#64) ↦₆₄ a3) ∗
        ((fsp + 0xf0#64) ↦₆₄ a4) ∗ ((fsp + 0xf8#64) ↦₆₄ a5) ∗
        ((fsp + 0x100#64) ↦₆₄ a6) ∗ ((fsp + 0x108#64) ↦₆₄ a7) ∗
        ((fsp + 0x110#64) ↦₃₂ a8) ∗ memRegion (fsp + 0x114#64) 4 ∗
        ((fsp + 0x118#64) ↦₆₄ a9) ∗ ((fsp + 0x120#64) ↦₆₄ a10) ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₁₆ flag16) ∗
        memRegion (fsp + 0x5ba#64) 30 ∗
        ((fsp + 0x5d8#64) ↦₆₄ wk0) ∗ ((fsp + 0x5e0#64) ↦₆₄ wk1) ∗ ((fsp + 0x5e8#64) ↦₆₄ wk2) ∗
        memRegion (fsp + 0x5f0#64) (0xc90 - 0x5f0) ∗
        ((fsp + 0xc90#64) ↦₆₄ probe) ∗
        memRegion (fsp + 0xc98#64) (initLocalsSize - 0xc98) := by
  have hsz : initLocalsSize = 7312 := rfl
  have split8At : ∀ off top, 8 ≤ top - off → top - off ≤ 7312 →
      memRegion (fsp + BitVec.ofNat 64 off) (top - off) =
        (∃∗ w : BitVec 64, (fsp + BitVec.ofNat 64 off) ↦₆₄ w) ∗
          memRegion (fsp + BitVec.ofNat 64 (off + 8)) (top - (off + 8)) := by
    intro off top h1 h2
    have hn : top - off = 8 + (top - (off + 8)) := by omega
    conv_lhs => rw [hn]
    rw [memRegion_split _ 8 _ (by omega), ProofLib.memRegion_eight,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  have split4At : ∀ off top, 4 ≤ top - off → top - off ≤ 7312 →
      memRegion (fsp + BitVec.ofNat 64 off) (top - off) =
        (∃∗ w : BitVec 32, (fsp + BitVec.ofNat 64 off) ↦₃₂ w) ∗
          memRegion (fsp + BitVec.ofNat 64 (off + 4)) (top - (off + 4)) := by
    intro off top h1 h2
    have hn : top - off = 4 + (top - (off + 4)) := by omega
    conv_lhs => rw [hn]
    rw [memRegion_split _ 4 _ (by omega), ProofLib.memRegion_four,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  have splitGapAt : ∀ off k top, k ≤ top - off → top - off ≤ 7312 →
      memRegion (fsp + BitVec.ofNat 64 off) (top - off) =
        memRegion (fsp + BitVec.ofNat 64 off) k ∗
          memRegion (fsp + BitVec.ofNat 64 (off + k)) (top - (off + k)) := by
    intro off k top h1 h2
    have hn : top - off = k + (top - (off + k)) := by omega
    conv_lhs => rw [hn]
    rw [memRegion_split _ k _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  have htop3 : memRegion fsp initLocalsSize ⊢
      memRegion (fsp + BitVec.ofNat 64 0) (0x5b8 - 0) ∗
        (∃∗ flag16 : BitVec 16, (fsp + 0x5b8#64) ↦₁₆ flag16) ∗
        memRegion (fsp + BitVec.ofNat 64 0x5ba) (7312 - 0x5ba) := by
    have hs : memRegion fsp initLocalsSize =
        memRegion (fsp + BitVec.ofNat 64 0) (0x5b8 - 0) ∗
          memRegion (fsp + 0x5b8#64) 2 ∗
          memRegion (fsp + BitVec.ofNat 64 0x5ba) (7312 - 0x5ba) := by
      rw [hsz, show (7312 : Nat) = 0x5b8 + (2 + (7312 - 0x5ba)) by decide,
        memRegion_split fsp 0x5b8 _ (by decide),
        memRegion_split _ 2 _ (by decide)]
      simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
        Nat.reduceSub]
    rw [hs]
    exact sepConj_mono_right (sepConj_mono_left (memRegion_two_pointsTo16 (fsp + 0x5b8#64)))
  refine Entails.trans htop3 ?_
  rw [split8At 0 0x5b8 (by decide) (by decide),
      splitGapAt 0x08 0x78 0x5b8 (by decide) (by decide),
      split8At 0x80 0x5b8 (by decide) (by decide),
      split4At 0x88 0x5b8 (by decide) (by decide),
      splitGapAt 0x8c 4 0x5b8 (by decide) (by decide),
      split8At 0x90 0x5b8 (by decide) (by decide),
      split8At 0x98 0x5b8 (by decide) (by decide),
      split8At 0xa0 0x5b8 (by decide) (by decide),
      split8At 0xa8 0x5b8 (by decide) (by decide),
      split8At 0xb0 0x5b8 (by decide) (by decide),
      split8At 0xb8 0x5b8 (by decide) (by decide),
      split8At 0xc0 0x5b8 (by decide) (by decide),
      split8At 0xc8 0x5b8 (by decide) (by decide),
      split8At 0xd0 0x5b8 (by decide) (by decide),
      split8At 0xd8 0x5b8 (by decide) (by decide),
      split8At 0xe0 0x5b8 (by decide) (by decide),
      split8At 0xe8 0x5b8 (by decide) (by decide),
      split8At 0xf0 0x5b8 (by decide) (by decide),
      split8At 0xf8 0x5b8 (by decide) (by decide),
      split8At 0x100 0x5b8 (by decide) (by decide),
      split8At 0x108 0x5b8 (by decide) (by decide),
      split4At 0x110 0x5b8 (by decide) (by decide),
      splitGapAt 0x114 4 0x5b8 (by decide) (by decide),
      split8At 0x118 0x5b8 (by decide) (by decide),
      split8At 0x120 0x5b8 (by decide) (by decide),
      splitGapAt 0x5ba 30 7312 (by decide) (by decide),
      split8At 0x5d8 7312 (by decide) (by decide),
      split8At 0x5e0 7312 (by decide) (by decide),
      split8At 0x5e8 7312 (by decide) (by decide),
      splitGapAt 0x5f0 (0xc90 - 0x5f0) 7312 (by decide) (by decide),
      split8At 0xc90 7312 (by decide) (by decide)]
  simp only [hsz, BitVec.add_zero, Nat.reduceAdd, Nat.reduceSub,
    sepExists_sepConj_left, sepExists_sepConj_right]
  repeat' (apply Entails.sepExists_elim; intro)
  sep_frame

/-- Merges low prologue scratch cells `[fsp, fsp + 0xd0)` back into `memRegion fsp 0xd0`. -/
theorem prologue_low_d0_merge (fsp : BitVec 64)
    (l0 l80 : BitVec 64) (l88 : BitVec 32)
    (l90 l98 la0 la8 lb0 lb8 lc0 lc8 : BitVec 64) :
    (fsp ↦₆₄ l0) ∗ memRegion (fsp + 0x08#64) 0x78 ∗
      ((fsp + 0x80#64) ↦₆₄ l80) ∗ ((fsp + 0x88#64) ↦₃₂ l88) ∗ memRegion (fsp + 0x8c#64) 4 ∗
      ((fsp + 0x90#64) ↦₆₄ l90) ∗ ((fsp + 0x98#64) ↦₆₄ l98) ∗
      ((fsp + 0xa0#64) ↦₆₄ la0) ∗ ((fsp + 0xa8#64) ↦₆₄ la8) ∗
      ((fsp + 0xb0#64) ↦₆₄ lb0) ∗ ((fsp + 0xb8#64) ↦₆₄ lb8) ∗
      ((fsp + 0xc0#64) ↦₆₄ lc0) ∗ ((fsp + 0xc8#64) ↦₆₄ lc8) ⊢
      memRegion fsp 0xd0 := by
  have m64 := pointsTo64_entails_memRegion
  have m32 := pointsTo32_entails_memRegion
  refine Entails.trans (sepConj_mono (m64 _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m32 _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _) (m64 _ _))))))))))))) ?_
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x08#64) 8 120 128 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x80#64) 128 8 136 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x88#64) 136 4 140 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x8c#64) 140 4 144 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x90#64) 144 8 152 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0x98#64) 152 8 160 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0xa0#64) 160 8 168 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0xa8#64) 168 8 176 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0xb0#64) 176 8 184 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0xb8#64) 184 8 192 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge fsp (fsp + 0xc0#64) 192 8 200 (by bv_omega) (by decide) (by decide)]
  rw [memRegion_merge fsp (fsp + 0xc8#64) 200 8 208 (by bv_omega) (by decide) (by decide)]
  exact Entails.refl _

/-- Merges upper prologue scratch cells `[fsp + 0x5ba, fsp + initLocalsSize)` back into one `memRegion`. -/
theorem prologue_high_5ba_merge (fsp : BitVec 64)
    (wk0 wk1 wk2 probe : BitVec 64) :
    memRegion (fsp + 0x5ba#64) 30 ∗
      ((fsp + 0x5d8#64) ↦₆₄ wk0) ∗ ((fsp + 0x5e0#64) ↦₆₄ wk1) ∗ ((fsp + 0x5e8#64) ↦₆₄ wk2) ∗
      memRegion (fsp + 0x5f0#64) (0xc90 - 0x5f0) ∗
      ((fsp + 0xc90#64) ↦₆₄ probe) ∗
      memRegion (fsp + 0xc98#64) (initLocalsSize - 0xc98) ⊢
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
  have m64 := pointsTo64_entails_memRegion
  refine Entails.trans (sepConj_mono (Entails.refl _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (m64 _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (m64 _ _) (Entails.refl _))))))) ?_
  rw [← sepConj_assoc, memRegion_merge (fsp + 0x5ba#64) (fsp + 0x5d8#64) 30 8 38 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0x5ba#64) (fsp + 0x5e0#64) 38 8 46 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0x5ba#64) (fsp + 0x5e8#64) 46 8 54 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0x5ba#64) (fsp + 0x5f0#64) 54 1696 1750 (by bv_omega) (by decide) (by decide)]
  rw [← sepConj_assoc, memRegion_merge (fsp + 0x5ba#64) (fsp + 0xc90#64) 1750 8 1758 (by bv_omega) (by decide) (by decide)]
  rw [memRegion_merge (fsp + 0x5ba#64) (fsp + 0xc98#64) 1758 (initLocalsSize - 0xc98)
    (initLocalsSize - 0x5ba) (by bv_omega) (by decide) (by decide)]
  exact Entails.refl _

/-- Splits `[sp + 0x5ba, sp + initLocalsSize)` into future pointer/vtable slots (`+0x5c0`, `+0x5c8`) and an sret region at `sp + 0x1600`. -/
theorem poll_frame_5ba_split (sp : BitVec 64) (outSz : Nat)
    (hout : 0x1600 + outSz ≤ initLocalsSize) :
    memRegion (sp + 0x5ba#64) (initLocalsSize - 0x5ba) =
      memRegion (sp + 0x5ba#64) 6 ∗
        (∃∗ f0 : BitVec 64, (sp + 0x5c0#64) ↦₆₄ f0) ∗
        (∃∗ f1 : BitVec 64, (sp + 0x5c8#64) ↦₆₄ f1) ∗
        memRegion (sp + 0x5d0#64) (0x1600 - 0x5d0) ∗
        memRegion (sp + 0x1600#64) outSz ∗
        memRegion (sp + BitVec.ofNat 64 (0x1600 + outSz)) (initLocalsSize - (0x1600 + outSz)) := by
  have hsz : initLocalsSize = 7312 := rfl
  have h1 : initLocalsSize - 0x5ba = 6 + (initLocalsSize - 0x5c0) := by omega
  have h2 : initLocalsSize - 0x5c0 = 8 + (initLocalsSize - 0x5c8) := by omega
  have h3 : initLocalsSize - 0x5c8 = 8 + (initLocalsSize - 0x5d0) := by omega
  have h4 : initLocalsSize - 0x5d0 = (0x1600 - 0x5d0) + (initLocalsSize - 0x1600) := by omega
  have h5 : initLocalsSize - 0x1600 = outSz + (initLocalsSize - (0x1600 + outSz)) := by omega
  rw [h1, memRegion_split (sp + 0x5ba#64) 6 _ (by omega),
      h2, memRegion_split _ 8 _ (by omega), ProofLib.memRegion_eight,
      h3, memRegion_split _ 8 _ (by omega), ProofLib.memRegion_eight,
      h4, memRegion_split _ (0x1600 - 0x5d0) _ (by omega),
      h5, memRegion_split _ outSz _ (by omega)]
  simp only [Nat.reduceSub, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]

/-- Merges `[sp + 0x5ba, sp + initLocalsSize)` back after `idTrustPoll` / `sessLoadPoll`. -/
theorem poll_frame_5ba_merge (sp : BitVec 64) (f0 f1 : BitVec 64) (outSz : Nat)
    (hout : 0x1600 + outSz ≤ initLocalsSize) :
    memRegion (sp + 0x5ba#64) 6 ∗
      ((sp + 0x5c0#64) ↦₆₄ f0) ∗
      ((sp + 0x5c8#64) ↦₆₄ f1) ∗
      memRegion (sp + 0x5d0#64) (0x1600 - 0x5d0) ∗
      memRegion (sp + 0x1600#64) outSz ∗
      memRegion (sp + BitVec.ofNat 64 (0x1600 + outSz)) (initLocalsSize - (0x1600 + outSz)) ⊢
      memRegion (sp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
  rw [poll_frame_5ba_split sp outSz hout]
  sep_frame

set_option maxHeartbeats 2400000 in
/-- `SpeOwned.plain 11` (`SignatureValidationFailed`) error return from `0x0350` when `x26 = speWord 11`. -/
theorem stage1_plain11_exit_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop}
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hctrl : InInitiateExt img ext s0 s 0x0350)
    (htr : s.trace = s0.trace)
    (hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 11) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (stage2Mem A img x stk s0) Q Qp (initOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  refine sepWPp_mono_pre ?_
    (stage1_epilogue_err_ext_ok hstk hstk64 hctrl htr hx8 hans hpost
      (H_err := emp)
      (H_extra := coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img)
      (by
        rw [sepConj_emp]
        exact words_to_plain11_initResAt A x.ret
          (s.readReg64 (.gpr 26#5)) (s.readReg64 (.gpr 27#5))
          (s.readReg64 (.gpr 25#5)) (s.readReg64 (.gpr 28#5))
          (s.readReg64 (.gpr 24#5)) (s.readReg64 (.gpr 21#5)) hx26))
  unfold stage2Mem
  dsimp only [fsp]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (stage2Locals_entails_memRegion img fsp x s0)))))))))))
  sep_frame

theorem stage1_plain11_exit_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop}
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hctrl : InInitiate img W s0 s 0x0350)
    (htr : s.trace = s0.trace)
    (hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hx26 : s.readReg64 (.gpr 26#5) = speWord 11) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (stage2Mem A img x stk s0) Q Qp (initOom s0) :=
  stage1_plain11_exit_ext_ok (ext := cliHookExterns W) hstk hstk64 hx8
    (inInitiate_toExt hctrl) htr hans hpost hx26

set_option maxHeartbeats 2400000 in
/-- Untrusted-identity `Err` exit (`0x0244 → String::clone → 0x026c → 0x0350 → ret`) when `is_trusted_identity` returns `Ok(false)`. -/
theorem stage1_untrusted_exit_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hS : S.initiate = initDef X P)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hctrl : InInitiateExt img ext s0 s 0x0244)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0xfe0#64)
    (htr : s.trace = s0.trace)
    (htrustF : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey =
      .ok false)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (stage2Mem A img x stk s0) Q Qp (initOom s0) := by
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage1Bin img.base
    (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
    (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x0244 0x0040
  have hpc := hctrl.pc; have hrun := hctrl.run; have hsp := hctrl.sp
  have hfp := hctrl.fp; have hx19 := hctrl.x19; have hfs0 := hctrl.files0
  have hvregs := hctrl.vregs; have hal0 := hctrl.spAligned
  have hal := inInitiateExt_spAligned_cur hctrl
  unfold stage2Mem; dsimp only; rw [← hsp]
  have hsplit5ba :
      memRegion (s.sp + 0x5ba#64) (initLocalsSize - 0x5ba) =
        memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
          memRegion (s.sp + 0x1600#64) 24 ∗
          (∃∗ b0 : BitVec 8, (s.sp + 0x1618#64) ↦₈ b0) ∗
          memRegion (s.sp + 0x1619#64) 7 ∗
          memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620) := by
    rw [show initLocalsSize - 0x5ba = (0x1600 - 0x5ba) + (24 + (1 + (7 + (initLocalsSize - 0x1620)))) by decide,
      memRegion_split (s.sp + 0x5ba#64) (0x1600 - 0x5ba) _ (by decide),
      memRegion_split _ 24 _ (by decide),
      memRegion_split _ 1 _ (by decide), ProofLib.memRegion_one,
      memRegion_split _ 7 _ (by decide)]
    simp only [Nat.reduceSub, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hsplit5ba]
  refine sepWPp_mono_pre (P' :=
      ∃∗ b0 : BitVec 8,
        ((s.sp + 0x1618#64) ↦₈ b0) ∗
        memRegion (s.sp + 0x1619#64) 7 ∗
        memRegion (s.sp + 0x1600#64) 24 ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ A.pool ∗ initSaved s0 ∗
        memRegion s.sp 0xd0 ∗ initArgsAt img s.sp x s0 ∗
        memRegion (s.sp + 0x128#64) 0x490 ∗
        ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620) ∗
        stackAt s.sp (stk - cliInitiateFrame))
    (by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro b0
      exact Entails.sepExists_right b0 (by sep_frame)) ?_
  refine sepWPp_exists_elim fun b0 => ?_
  unfold initArgsAt
  have hent : initEntryExt img ext =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
  dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc ⊢
  try simp only [BitVec.ofNat_eq_ofNat] at hpc
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
  examples_hide_fetches
  refine sepWPp_step_to
    (fnBase + bv% (ls_rel% "libsignal_cli_handshake::initiate"
      "<alloc::string::String as core::clone::Clone>::clone"))
    hctrl.inv ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sClone hsClone hpcC hrunC hinvC
  have hspC : sClone.sp = s.sp := by rw [← hsClone]; simp [wp_norm, arm64_norm]
  have hx0C : sClone.readReg64 .x0 = x.peerA := by rw [← hsClone]; simp [wp_norm, arm64_norm]
  have hx8C : sClone.readReg64 .x8 = s.sp + 0x1600#64 := by
    rw [← hsClone]; simp [wp_norm, arm64_norm, hsp]; try bv_omega
  have hlrC : sClone.readReg64 .lr = initPcExt img ext 0x0258 := by
    rw [← hsClone]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm]; try bv_omega
  have hx20C : sClone.readReg64 (.gpr 20#5) = x.peerA := by
    rw [← hsClone]; simp [wp_norm, arm64_norm]
  have hx21C : sClone.readReg64 (.gpr 21#5) = s.sp + 0xfe0#64 := by
    rw [← hsClone]; simp [wp_norm, arm64_norm, hx21]
  have hfpC : sClone.readReg64 .fp = s.readReg64 .fp := by
    rw [← hsClone]; simp [wp_norm, arm64_norm]
  have hx19C : sClone.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := by
    rw [← hsClone]; simp [wp_norm, arm64_norm]
  have hvregsC : calleeSavedVRegs sClone = calleeSavedVRegs s0 := by
    rw [← hsClone]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregs]
  have htrC : sClone.trace = s0.trace := by rw [← hsClone]; simp [wp_norm, arm64_norm, htr]
  have hfsC : sClone.fs.files = s0.fs.files := by rw [← hsClone]; simp [wp_norm, arm64_norm, hfs0]
  have halC : sClone.spAligned = true := by simpa only [State.spAligned, hspC] using hal
  clear hsClone
  have hclone := init_stringClone_ok_at_ext (ext := ext) hh hstk hstk64
  refine sepWPp_mono_pre (P' :=
      ((stringCloneAtStkSpec A (stk - cliInitiateFrame)).pre
        (x.peerA, s.sp + 0x1600#64, x.peer.name) sClone) ∗
      (((s.sp + 0x1618#64) ↦₈ b0) ∗ memRegion (s.sp + 0x1619#64) 7 ∗
        (((x.peerA + asm64% addrDeviceOff) ↦₈ x.peer.device) ∗
          memRegion (x.peerA + asm64% (addrDeviceOff + 1))
            (asm% (protocolAddressSize - (addrDeviceOff + 1)))) ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ initSaved s0 ∗
        memRegion s.sp 0xd0 ∗ initArgsAt img s.sp x s0 ∗
        memRegion (s.sp + 0x128#64) 0x490 ∗
        ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620))) ?_ ?_
  · unfold stringCloneAtStkSpec protocolAddressAt initArgsAt
    dsimp only
    rw [hspC]
    repeat rw [sepConj_assoc]
    exact pure_sepConj_intro ⟨hx0C, hx8C⟩ (by sep_frame)
  rw [← hent] at hpcC
  refine initCallInImage_ext hh hpanic hclone hpcC hrunC halC hinvC htrC hfsC hlrC
    (Entails.refl _) (fun _ => Entails.refl _) ?_
  intro sm hpcM hrunM hspM hcsM hinvM hfsM
  unfold stringCloneAtStkSpec; dsimp only
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun htrM => ?_
  have htrM' : sm.trace = s0.trace := htrM.trans htrC
  have hfsM' : sm.fs.files = s0.fs.files := hfsM htrM'
  have hspM' : sm.sp = s.sp := hspM.trans hspC
  have hx20M : sm.readReg64 (.gpr 20#5) = x.peerA := (cs_x20 hcsM).trans hx20C
  have hx21M : sm.readReg64 (.gpr 21#5) = s.sp + 0xfe0#64 := (cs_x21 hcsM).trans hx21C
  refine sepWPp_mono_pre
    (sepConj_mono
      (sepConj_mono_right (sepConj_mono_left (vecU8_unpack_words A (s.sp + 0x1600#64) x.peer.val.name)))
      (Entails.refl _)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_elim fun cap => ?_
  refine sepWPp_exists_elim fun ptr => ?_
  have haddr1618 : (s.sp + 0xfe0#64) + 0x638#64 = s.sp + 0x1618#64 := by bv_omega
  dsimp only [initPcExt] at hpcM
  rw [hent] at hpcM
  dsimp only [initProgExt, tripleRatchetProgAtExt]
  refine sepWPp_step_to (fnBase + 0x026c#64) hinvM ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sMid hsMid hpcMid hrunMid hinvMid
  have hspMid : sMid.sp = s.sp := by rw [← hsMid]; simp [wp_norm, arm64_norm, hspM']
  have hx27Mid : sMid.readReg64 (.gpr 27#5) = cap := by rw [← hsMid]; simp [wp_norm, arm64_norm]
  have hx25Mid : sMid.readReg64 (.gpr 25#5) = ptr := by rw [← hsMid]; simp [wp_norm, arm64_norm]
  have hx28Mid : sMid.readReg64 (.gpr 28#5) = BitVec.ofNat 64 x.peer.val.name.length := by
    rw [← hsMid]; simp [wp_norm, arm64_norm]
  have hfpMid : sMid.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsMid]; simp [wp_norm, arm64_norm, cs_fp hcsM, hfpC, hfp]
  have hx19Mid : sMid.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsMid]; simp [wp_norm, arm64_norm, cs_x19 hcsM, hx19C, hx19]
  have hvregsMid : calleeSavedVRegs sMid = calleeSavedVRegs s0 := by
    rw [← hsMid]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsM, hvregsC]
  have htrMid : sMid.trace = s0.trace := by rw [← hsMid]; simp [wp_norm, arm64_norm, htrM']
  have hfsMid : sMid.fs.files = s0.fs.files := by
    rw [← hsMid]; simp [wp_norm, arm64_norm, hfsM']
  clear hsMid
  have hdev8 : BitVec.extractLsb' 0 8 (BitVec.zeroExtend 64 x.peer.device) = x.peer.device := by
    bv_bits
  have htrunc8 : BitVec.truncate 8 (BitVec.zeroExtend 64 x.peer.device) = x.peer.device := by
    bv_bits
  try rw [haddr1618]
  try rw [hdev8]
  try rw [htrunc8]
  refine sepWPp_mono_pre (P' :=
      ((∃∗ w4 : BitVec 64,
          ⌜BitVec.extractLsb' 0 8 w4 = x.peer.device⌝ ∗
          ((s.sp + 0x1618#64) ↦₆₄ w4)) ∗
        ((s.sp + 0x1600#64) ↦₆₄ cap) ∗
        ((s.sp + 0x1608#64) ↦₆₄ ptr) ∗
        ((s.sp + 0x1610#64) ↦₆₄ BitVec.ofNat 64 x.peer.val.name.length) ∗
        stage1VecBuf A cap ptr x.peer.val.name ∗
        protocolAddressAt A x.peer x.peerA ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ A.pool ∗ initSaved s0 ∗
        memRegion s.sp 0xd0 ∗ initArgsAt img s.sp x s0 ∗
        memRegion (s.sp + 0x128#64) 0x490 ∗
        ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620) ∗
        stackAt s.sp (stk - cliInitiateFrame))) ?_ ?_
  · rw [hspC]
    unfold protocolAddressAt
    have hpack4 : ((s.sp + 0x1618#64) ↦₈ x.peer.device) ∗ memRegion (s.sp + 0x1619#64) 7 ⊢
        ∃∗ w4 : BitVec 64, ⌜BitVec.extractLsb' 0 8 w4 = x.peer.device⌝ ∗ ((s.sp + 0x1618#64) ↦₆₄ w4) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        byte_and_pad7_entails_word64 (s.sp + 0x1618#64) x.peer.device
    refine Entails.trans ?_ (sepConj_mono_left hpack4)
    sep_frame
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_elim fun w4 => ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun hw4 => ?_
  refine sepWPp_step_to (fnBase + 0x0350#64) hinvMid ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sErr hsErr hpcErr hrunErr hinvErr
  have hspErr : sErr.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hspMid, hsp]
  have hfpErr : sErr.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hfpMid]
  have hx19Err : sErr.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hx19Mid]
  have hvregsErr : calleeSavedVRegs sErr = calleeSavedVRegs s0 := by
    rw [← hsErr]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsMid]
  have hfsErr : sErr.fs.files = s0.fs.files := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hfsMid]
  have htrErr : sErr.trace = s0.trace := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, htrMid]
  have hx26Err : sErr.readReg64 (.gpr 26#5) = speWord speUntrustedIdentity := by
    rw [← hsErr]; simp [wp_norm, arm64_norm]; rfl
  have hx27Err : sErr.readReg64 (.gpr 27#5) = cap := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hx27Mid]
  have hx25Err : sErr.readReg64 (.gpr 25#5) = ptr := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hx25Mid]
  have hx28Err : sErr.readReg64 (.gpr 28#5) = BitVec.ofNat 64 x.peer.val.name.length := by
    rw [← hsErr]; simp [wp_norm, arm64_norm, hx28Mid]
  have hx24Err : sErr.readReg64 (.gpr 24#5) = w4 := by
    rw [← hsErr]; simp [wp_norm, arm64_norm]
  clear hsErr
  rw [← hent] at hpcErr
  have hctrlErr : InInitiateExt img ext s0 sErr 0x0350 :=
    ⟨hpcErr, hrunErr, hspErr, hfpErr, hx19Err, hfsErr, hinvErr, hvregsErr, hal0⟩
  have hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none := by
    rw [hS]
    exact initDef_eq_some_none_of_trust_false X P x.F x.peer.val x.me.val
      x.bundle x.coins htrustF
  refine sepWPp_mono_pre ?_
    (stage1_epilogue_err_ext_ok hstk hstk64 hctrlErr htrErr hx8 hans hpost
      (H_err := stage1VecBuf A cap ptr x.peer.val.name)
      (H_extra := coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img)
      (by
        rw [hx27Err, hx25Err]
        exact words_to_untrusted_initResAt A x.ret x.peer.val
          (sErr.readReg64 (.gpr 26#5)) cap ptr
          (sErr.readReg64 (.gpr 28#5))
          (sErr.readReg64 (.gpr 24#5)) (sErr.readReg64 (.gpr 21#5))
          hx26Err hx28Err (hx24Err ▸ hw4)))
  rw [← hsp]
  have hlocMerge :
      memRegion s.sp 0xd0 ∗ initArgsAt img s.sp x s0 ∗
        memRegion (s.sp + 0x128#64) 0x490 ∗
        ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
        (memRegion (s.sp + 0x5ba#64) (0x1600 - 0x5ba) ∗
          ((s.sp + 0x1600#64) ↦₆₄ cap) ∗
          ((s.sp + 0x1608#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x1610#64) ↦₆₄ BitVec.ofNat 64 x.peer.val.name.length) ∗
          ((s.sp + 0x1618#64) ↦₆₄ w4) ∗
          memRegion (s.sp + 0x1620#64) (initLocalsSize - 0x1620)) ⊢
        memRegion s.sp initLocalsSize := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right ?_)))))
      (stage2Locals_entails_memRegion img s.sp x s0)
    have m64 := pointsTo64_entails_memRegion
    refine Entails.trans (sepConj_mono (Entails.refl _)
      (sepConj_mono (m64 _ _) (sepConj_mono (m64 _ _)
      (sepConj_mono (m64 _ _) (sepConj_mono (m64 _ _) (Entails.refl _)))))) ?_
    rw [← sepConj_assoc, memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1600#64) (0x1600 - 0x5ba) 8 (0x1608 - 0x5ba) (by bv_omega) (by decide) (by decide)]
    rw [← sepConj_assoc, memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1608#64) (0x1608 - 0x5ba) 8 (0x1610 - 0x5ba) (by bv_omega) (by decide) (by decide)]
    rw [← sepConj_assoc, memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1610#64) (0x1610 - 0x5ba) 8 (0x1618 - 0x5ba) (by bv_omega) (by decide) (by decide)]
    rw [← sepConj_assoc, memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1618#64) (0x1618 - 0x5ba) 8 (0x1620 - 0x5ba) (by bv_omega) (by decide) (by decide)]
    rw [memRegion_merge (s.sp + 0x5ba#64) (s.sp + 0x1620#64) (0x1620 - 0x5ba) (initLocalsSize - 0x1620)
      (initLocalsSize - 0x5ba) (by bv_omega) (by decide) (by decide)]
    exact Entails.refl _
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hlocMerge))))))))))
  sep_frame

theorem stage1_untrusted_exit_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hctrl : InInitiate img W s0 s 0x0244)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0xfe0#64)
    (htr : s.trace = s0.trace)
    (htrustF : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey =
      .ok false)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (stage2Mem A img x stk s0) Q Qp (initOom s0) :=
  stage1_untrusted_exit_ext_ok (P := ⟨W.C, W.Q⟩) (ext := cliHookExterns W) hh.toExt hS hstk hstk64
    hx8 (inInitiate_toExt hctrl) hx21 htr htrustF hpost hpanic

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
