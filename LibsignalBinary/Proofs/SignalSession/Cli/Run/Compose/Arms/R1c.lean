/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Hops
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Specifications.AsmConstants
import ProofLib.SepLogic.Entry

/-!
# `signal_session::run` Arm `R1c`: `initiate` Call and `init` Exit Tails

Proves `run_hop_init3_ok` (`R+0x28f0 → R+0xf8c / R+0x2c7c`) on `signal_session::run`:
from `AtInit2` (`R+0x28f0`), calls `signal_session_handshake::initiate` (`hc.initiate`), writes an
empty output `Vec` and frees the six bundle/address buffers to reach `AtJoin` (`R+0xf8c`) on
`.ok ()`, or drops the returned `SignalProtocolError`, writes `-1`, and frees the six buffers to
reach `AtReject .postDispatch` (`R+0x2c7c`) on `.error _`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunDrop

/-! ## 1. Layout-Independent Decode Tables & Symbol `fnOff`s -/

gen_decodes CryptoVerification.libsignalSessionCode_tree r1c_dec_main
  [(ls_off% "libsignal_cli::run" + 10480) → (ls_off% "libsignal_cli::run" + 10812)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r1c_dec_pjoin
  [(ls_off% "libsignal_cli::run" + 3972) → (ls_off% "libsignal_cli::run" + 3980)]

gen_decodes CryptoVerification.libsignalSessionCode_tree r1c_dec_rejtail
  [(ls_off% "libsignal_cli::run" + 11348) → (ls_off% "libsignal_cli::run" + 11388)]

section

set_option maxRecDepth 200000

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

private theorem r1c_init_fnOff :
    libsignalSessionCode.fnOff wrapInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "libsignal_cli_handshake::initiate")

/-! ## 2. `SepWPp` Call, Framing, Deallocation & Stack Helpers -/

private theorem r1c_perm {P P' Q : SepProp} (h : P' ⊢ Q) (heq : P = P') : P ⊢ Q :=
  heq ▸ h

private theorem r1c_perm_post {P Q' Q : SepProp} (h : P ⊢ Q') (heq : Q' = Q) : P ⊢ Q :=
  heq ▸ h

private theorem r1c_stackAt_split_ge (sp : BitVec 64) {k n : Nat}
    (hle : k ≤ n) (hn : n ≤ 2 ^ 64) :
    stackAt sp n = memRegion (sp - BitVec.ofNat 64 n) (n - k) ∗ stackAt sp k := by
  have h := ProofLib.stackAt_split_bottom sp k (n - k) (by omega)
  rwa [Nat.add_sub_of_le hle] at h

private theorem r1c_split_at (fsp : BitVec 64) (a m c : Nat)
    (hm : a + m ≤ c) (hc : c ≤ runLocalBytes) :
    memRegion (fsp + BitVec.ofNat 64 a) (c - a) =
      memRegion (fsp + BitVec.ofNat 64 a) m ∗
        memRegion (fsp + BitVec.ofNat 64 (a + m)) (c - (a + m)) := by
  have hlb : runLocalBytes = 0x29f0 := rfl
  have hs := ProofLib.memRegion_split (fsp + BitVec.ofNat 64 a) m (c - (a + m)) (by omega)
  have hl : m + (c - (a + m)) = c - a := by omega
  have ha : fsp + BitVec.ofNat 64 a + BitVec.ofNat 64 m = fsp + BitVec.ofNat 64 (a + m) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  simpa only [hl, ha] using hs

private theorem r1c_sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

private theorem r1c_sepWPp_exists_left {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x, P x) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x R hx hL

private theorem r1c_sepWPp_pure_left {P0 : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : P0 → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜P0⌝ ∗ P) Q Qp oom := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

private theorem r1c_call_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {callee retAddr ret : BitVec 64} {spec : Spec α} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (x : α)
    (hcall : subroutine_ok prog callee (spec.inImage img))
    (hinv : ImgCallInv img s)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = retAddr)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ runOom s0 sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sm : State,
      Steps prog s sm →
      ImgCallInv img sm →
      sm.pc = retAddr →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp (runOom s0)) :
    SepWPp prog ret s P Q Qp (runOom s0) := by
  intro R hm hL
  have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
    Satisfies.mono (sepConj_mono_left hP) hm
  have hpre : s.mem ⊨ (spec.inImage img).pre x s ∗ (F ∗ R) := by
    dsimp only [Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, by simpa only [sepConj_assoc] using hm_pre⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [Spec.inImage] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hinv.of_steps hsteps) hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [Spec.inImage] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [Spec.inImage] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

private theorem r1c_call_raw {α : Type} {prog : Program} {img : Obj.Image}
    {callee retAddr ret : BitVec 64} {spec : Spec α} {s0 s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (x : α)
    (hcall : subroutine_ok prog callee spec)
    (hinv : ImgCallInv img s)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = retAddr)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ runOom s0 sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sm : State,
      Steps prog s sm →
      ImgCallInv img sm →
      sm.pc = retAddr →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp (runOom s0)) :
    SepWPp prog ret s P Q Qp (runOom s0) := by
  intro R hm hL
  have hm_pre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm_pre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hinv.of_steps hsteps) hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

private theorem r1c_inRun_step {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s s' : State} {k k' : Nat} (h : InRun img ext s0 s k)
    (hpc : s'.pc = runPc img ext k') (hrun : s'.status = .Running)
    (hsp : s'.sp = s.sp) (hfp : s'.readReg64 .fp = s.readReg64 .fp)
    (hinv : ImgCallInv img s') (hv : calleeSavedVRegs s' = calleeSavedVRegs s) :
    InRun img ext s0 s' k' :=
  ⟨hpc, hrun, hsp.trans h.sp, hfp.trans h.fp, hinv, hv.trans h.vregs, h.spAligned⟩

private theorem r1c_hist_of_eq {i : Inputs} {s0 s s' : State}
    (htr : s'.trace = s.trace) (hfs : s'.fs.files = s.fs.files)
    (h : RunHistOk i s0 s) : RunHistOk i s0 s' :=
  ⟨hfs.trans h.1, by rw [htr]; exact h.2⟩

private theorem r1c_ownedBytes_entails_nameHeap (A : RustAlloc) (cap ptr len : BitVec 64)
    (bs : List (BitVec 8)) :
    ownedBytes A cap ptr len bs ⊢
      ⌜len = BitVec.ofNat 64 bs.length⌝ ∗
        addrNameHeap A ⟨⟨cap, ptr, bs⟩, 0#8⟩ := by
  unfold ownedBytes addrNameHeap
  apply Entails.pure_left; rintro ⟨hlen, hle, hlt, hne⟩
  exact Entails.pure_right hlen (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

private theorem r1c_nameHeap_dealloc (A : RustAlloc) (g : AddrGhost) (hcap : g.name.cap ≠ 0) :
    addrNameHeap A g ⊢
      ⌜LayoutOk g.name.cap.toNat 1⌝ ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion g.name.ptr g.name.cap.toNat := by
  unfold addrNameHeap
  simp only [hcap, ↓reduceIte]
  apply Entails.pure_left; rintro ⟨hle, hlt, _⟩
  have hpos : 0 < g.name.cap.toNat :=
    Nat.pos_of_ne_zero fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
  refine Entails.pure_right ⟨hpos, ⟨0, rfl⟩, by omega⟩ (sepConj_mono_right ?_)
  have hmerge :
      memRegion g.name.ptr g.name.bytes.length ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length) =
      memRegion g.name.ptr g.name.cap.toNat := by
    have hsum : g.name.bytes.length + (g.name.cap.toNat - g.name.bytes.length) =
        g.name.cap.toNat := Nat.add_sub_of_le hle
    simpa only [hsum] using
      (ProofLib.memRegion_split g.name.ptr g.name.bytes.length
        (g.name.cap.toNat - g.name.bytes.length) (by omega)).symm
  rw [← hmerge]
  exact sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion g.name.ptr g.name.bytes)

private theorem r1c_nameHeap_zero (A : RustAlloc) (g : AddrGhost) (hcap : g.name.cap = 0) :
    addrNameHeap A g ⊢ emp := by
  unfold addrNameHeap
  simp only [hcap, ↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

private theorem r1c_empty_vecU8 (A : RustAlloc) (a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ⊢
      vecU8 A a [] := by
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  dsimp only [vecU8At, vecHeader, List.length_nil]
  have hp : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 := by decide
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte, sepConj_emp, sepConj_assoc]
  exact r1c_perm_post (Entails.pure_right hp (Entails.refl _)) (by ac_rfl)

/-! ## 3. 6-Word `SpeOwned` Copy Infrastructure (`0x23b0 → 0x1750`) -/

private def r1c_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

private theorem r1c_wand_refl (P : SepProp) : emp ⊢ (P -∗ P) :=
  Entails.wand_intro (Entails.of_eq (emp_sepConj P))

private theorem r1c_wand_post {P Q Q' : SepProp} (h : Q ⊢ Q') :
    (P -∗ Q) ⊢ (P -∗ Q') :=
  Entails.wand_intro (Entails.trans (Entails.of_eq (sepConj_comm _ _))
    (Entails.trans (Entails.wand_elim P Q) h))

private theorem r1c_pointsTo64_pack (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (a ↦₆₄ r1c_pack64 b0 b1 b2 b3 b4 b5 b6 b7) =
      (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
        ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
        ((a + 7#64) ↦₈ b7) := by
  have a2 : a + 1#64 + 1#64 = a + 2#64 := by bv_omega
  have a3 : a + 2#64 + 1#64 = a + 3#64 := by bv_omega
  have a4 : a + 3#64 + 1#64 = a + 4#64 := by bv_omega
  have a5 : a + 4#64 + 1#64 = a + 5#64 := by bv_omega
  have a6 : a + 5#64 + 1#64 = a + 6#64 := by bv_omega
  have a7 : a + 6#64 + 1#64 = a + 7#64 := by bv_omega
  dsimp only [r1c_pack64]
  rw [← pointsToBytes8_eq_pointsTo64 a b0 b1 b2 b3 b4 b5 b6 b7]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, a2, a3, a4, a5, a6, a7]

private theorem r1c_pointsTo64_pack32x2 (a : BitVec 64) (c1 c2 : BitVec 32) :
    (a ↦₆₄ (c2 ++ c1)) = (a ↦₃₂ c1) ∗ ((a + 4#64) ↦₃₂ c2) := by
  have hlo : (c2 ++ c1).extractLsb' 0 32 = c1 := BitVec.extractLsb'_append_eq_right
  have hhi : (c2 ++ c1).extractLsb' 32 32 = c2 := BitVec.extractLsb'_append_eq_left
  rw [pointsTo64_split32 a (c2 ++ c1), hlo, hhi]

private theorem r1c_u64_to_u8pad7 (a : BitVec 64) (b0 : BitVec 8) (hi : BitVec 64)
    (hhi : hi.setWidth 8 = b0) :
    (a ↦₆₄ hi) ⊢ (a ↦₈ b0) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_eq_pointsToBytes a hi]
  dsimp only [unpack64]
  rw [pointsToBytes_cons]
  have hlow : hi.extractLsb' 0 8 = b0 := by
    rw [← BitVec.setWidth_eq_extractLsb' (by decide), hhi]
  rw [hlow]
  exact sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion (a + 1#64) _)

private theorem r1c_u8pad7_to_u64 (a : BitVec 64) (b0 : BitVec 8) :
    ((a ↦₈ b0) ∗ memRegion (a + 1#64) 7) ⊢
      ∃∗ hi : BitVec 64, ⌜hi.setWidth 8 = b0⌝ ∗ (a ↦₆₄ hi) := by
  rw [ProofLib.memRegion_split' (b := a + 1#64) (n := 1) (k := 6) (b' := a + 2#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 2#64) (n := 1) (k := 5) (b' := a + 3#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 3#64) (n := 1) (k := 4) (b' := a + 4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 4#64) (n := 1) (k := 3) (b' := a + 5#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 5#64) (n := 1) (k := 2) (b' := a + 6#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 6#64) (n := 1) (k := 1) (b' := a + 7#64) rfl (by bv_omega) (by decide)]
  simp only [Path.Helpers.memRegion_1_eq_pointsTo8, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b7
  apply Entails.sepExists_elim; intro b6
  apply Entails.sepExists_elim; intro b5
  apply Entails.sepExists_elim; intro b4
  apply Entails.sepExists_elim; intro b3
  apply Entails.sepExists_elim; intro b2
  apply Entails.sepExists_elim; intro b1
  let hi := r1c_pack64 b0 b1 b2 b3 b4 b5 b6 b7
  have hlow : hi.setWidth 8 = b0 := BitVec.setWidth_append_eq_right
  refine Entails.sepExists_right hi (Entails.pure_right hlow ?_)
  rw [r1c_pointsTo64_pack a b0 b1 b2 b3 b4 b5 b6 b7]
  exact Entails.of_eq (by ac_rfl)

private def r1c_WordShift (s d : BitVec 64) (Ps Pd : SepProp) : Prop :=
  Ps ⊢ ∃∗ w : BitVec 64, (s ↦₆₄ w) ∗ ((d ↦₆₄ w) -∗ Pd)

private theorem r1c_ws_u64 (s d w : BitVec 64) :
    r1c_WordShift s d (s ↦₆₄ w) (d ↦₆₄ w) :=
  Entails.sepExists_right w
    (Entails.trans (Entails.of_eq (sepConj_emp (s ↦₆₄ w)).symm)
      (sepConj_mono_right (r1c_wand_refl (d ↦₆₄ w))))

private theorem r1c_ws_mem8 (s d : BitVec 64) :
    r1c_WordShift s d (memRegion s 8) (memRegion d 8) := by
  unfold r1c_WordShift
  rw [ProofLib.memRegion_eight s]
  apply Entails.sepExists_elim; intro w
  exact Entails.sepExists_right w
    (Entails.trans (Entails.of_eq (sepConj_emp (s ↦₆₄ w)).symm)
      (sepConj_mono_right
        (Entails.trans (r1c_wand_refl (d ↦₆₄ w))
          (r1c_wand_post (pointsTo64_entails_memRegion d w)))))

private theorem r1c_ws_u8pad7 (s d : BitVec 64) (b0 : BitVec 8) :
    r1c_WordShift s d ((s ↦₈ b0) ∗ memRegion (s + 1#64) 7)
      ((d ↦₈ b0) ∗ memRegion (d + 1#64) 7) := by
  unfold r1c_WordShift
  refine Entails.trans (r1c_u8pad7_to_u64 s b0) ?_
  apply Entails.sepExists_elim; intro w
  apply Entails.pure_left; intro hlow
  exact Entails.sepExists_right w
    (Entails.trans (Entails.of_eq (sepConj_emp (s ↦₆₄ w)).symm)
      (sepConj_mono_right
        (Entails.trans (r1c_wand_refl (d ↦₆₄ w))
          (r1c_wand_post (r1c_u64_to_u8pad7 d b0 w hlow)))))

private theorem r1c_ws_u32x2 (s d : BitVec 64) (c1 c2 : BitVec 32) :
    r1c_WordShift s d ((s ↦₃₂ c1) ∗ ((s + 4#64) ↦₃₂ c2))
      ((d ↦₃₂ c1) ∗ ((d + 4#64) ↦₃₂ c2)) := by
  unfold r1c_WordShift
  rw [← r1c_pointsTo64_pack32x2 s c1 c2, ← r1c_pointsTo64_pack32x2 d c1 c2]
  exact r1c_ws_u64 s d (c2 ++ c1)

private theorem r1c_ex_left {α : Sort _} {P : α → SepProp} {Q R : SepProp}
    (h : ∀ x : α, P x ∗ Q ⊢ R) : (∃∗ x, P x) ∗ Q ⊢ R := by
  rw [sepExists_sepConj_left]; exact Entails.sepExists_elim h

private theorem r1c_keep {A X Rest G : SepProp} (h : (A ∗ X) ∗ Rest ⊢ G) :
    A ∗ (X ∗ Rest) ⊢ G := by
  rw [← sepConj_assoc]; exact h

private theorem r1c_peel {α : Sort _} {A : SepProp} {P : α → SepProp} {Rest G : SepProp}
    (h : ∀ x : α, A ∗ (P x ∗ Rest) ⊢ G) : A ∗ ((∃∗ x, P x) ∗ Rest) ⊢ G := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; exact Entails.sepExists_elim h

private theorem r1c_peel_end {α : Sort _} {A : SepProp} {P : α → SepProp} {G : SepProp}
    (h : ∀ x : α, A ∗ P x ⊢ G) : A ∗ (∃∗ x, P x) ⊢ G := by
  rw [sepExists_sepConj_right]; exact Entails.sepExists_elim h

private def r1c_vecHeap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

private theorem r1c_vecU8At_eq (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        r1c_vecHeap A cap ptr bs := by
  dsimp only [vecU8At, vecHeader, r1c_vecHeap]; ac_rfl

private theorem r1c_vecHeap_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    r1c_vecHeap A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ r1c_vecHeap A cap ptr bs := by
  unfold r1c_vecHeap
  apply Entails.pure_left; rintro ⟨hle, hlt, hne⟩
  exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

private structure r1c_W6 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64

private def r1c_slot6 (a : BitVec 64) (e : r1c_W6) : SepProp :=
  (a ↦₆₄ e.w0) ∗ ((a + 8#64) ↦₆₄ e.w1) ∗ ((a + 16#64) ↦₆₄ e.w2) ∗
    ((a + 24#64) ↦₆₄ e.w3) ∗ ((a + 32#64) ↦₆₄ e.w4) ∗ ((a + 40#64) ↦₆₄ e.w5)

private theorem r1c_mem48_to_slot6 (a : BitVec 64) :
    memRegion a 48 ⊢ ∃∗ e : r1c_W6, r1c_slot6 a e := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 24) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 16) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 8) (b' := a + 40#64) rfl (by bv_omega) (by decide)]
  simp only [ProofLib.memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  exact Entails.sepExists_right ⟨w0, w1, w2, w3, w4, w5⟩
    (by dsimp only [r1c_slot6]; exact Entails.of_eq (by ac_rfl))

private theorem r1c_slot6_to_mem48 (a : BitVec 64) (e : r1c_W6) :
    r1c_slot6 a e ⊢ memRegion a 48 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 24) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 16) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 8) (b' := a + 40#64) rfl (by bv_omega) (by decide)]
  dsimp only [r1c_slot6]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (pointsTo64_entails_memRegion _ _))))))

private theorem r1c_ws_combine6 {src dst : BitVec 64} (e : r1c_W6)
    (D0 D1 D2 D3 D4 D5 H : SepProp)
    (htag : e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec) :
    (((src ↦₆₄ e.w0) ∗ ((dst ↦₆₄ e.w0) -∗ D0)) ∗
      (((src + 8#64) ↦₆₄ e.w1) ∗ (((dst + 8#64) ↦₆₄ e.w1) -∗ D1)) ∗
      (((src + 16#64) ↦₆₄ e.w2) ∗ (((dst + 16#64) ↦₆₄ e.w2) -∗ D2)) ∗
      (((src + 24#64) ↦₆₄ e.w3) ∗ (((dst + 24#64) ↦₆₄ e.w3) -∗ D3)) ∗
      (((src + 32#64) ↦₆₄ e.w4) ∗ (((dst + 32#64) ↦₆₄ e.w4) -∗ D4)) ∗
      (((src + 40#64) ↦₆₄ e.w5) ∗ (((dst + 40#64) ↦₆₄ e.w5) -∗ D5)) ∗
      H) ⊢
      ∃∗ e' : r1c_W6,
        ⌜e'.w0 ≠ pendingTag ∧ e'.w0 ≠ okTagVec⌝ ∗
        r1c_slot6 src e' ∗
        (r1c_slot6 dst e' -∗ (D0 ∗ D1 ∗ D2 ∗ D3 ∗ D4 ∗ D5 ∗ H)) := by
  let W : SepProp :=
    ((dst ↦₆₄ e.w0) -∗ D0) ∗ (((dst + 8#64) ↦₆₄ e.w1) -∗ D1) ∗
      (((dst + 16#64) ↦₆₄ e.w2) -∗ D2) ∗ (((dst + 24#64) ↦₆₄ e.w3) -∗ D3) ∗
      (((dst + 32#64) ↦₆₄ e.w4) -∗ D4) ∗ (((dst + 40#64) ↦₆₄ e.w5) -∗ D5) ∗ H
  have h1 :
      (((src ↦₆₄ e.w0) ∗ ((dst ↦₆₄ e.w0) -∗ D0)) ∗
        (((src + 8#64) ↦₆₄ e.w1) ∗ (((dst + 8#64) ↦₆₄ e.w1) -∗ D1)) ∗
        (((src + 16#64) ↦₆₄ e.w2) ∗ (((dst + 16#64) ↦₆₄ e.w2) -∗ D2)) ∗
        (((src + 24#64) ↦₆₄ e.w3) ∗ (((dst + 24#64) ↦₆₄ e.w3) -∗ D3)) ∗
        (((src + 32#64) ↦₆₄ e.w4) ∗ (((dst + 32#64) ↦₆₄ e.w4) -∗ D4)) ∗
        (((src + 40#64) ↦₆₄ e.w5) ∗ (((dst + 40#64) ↦₆₄ e.w5) -∗ D5)) ∗ H) =
      r1c_slot6 src e ∗ W := by
    dsimp only [r1c_slot6, W]; ac_rfl
  have h2 :
      W ∗ r1c_slot6 dst e =
        ((dst ↦₆₄ e.w0) ∗ ((dst ↦₆₄ e.w0) -∗ D0)) ∗
          (((dst + 8#64) ↦₆₄ e.w1) ∗ (((dst + 8#64) ↦₆₄ e.w1) -∗ D1)) ∗
          (((dst + 16#64) ↦₆₄ e.w2) ∗ (((dst + 16#64) ↦₆₄ e.w2) -∗ D2)) ∗
          (((dst + 24#64) ↦₆₄ e.w3) ∗ (((dst + 24#64) ↦₆₄ e.w3) -∗ D3)) ∗
          (((dst + 32#64) ↦₆₄ e.w4) ∗ (((dst + 32#64) ↦₆₄ e.w4) -∗ D4)) ∗
          (((dst + 40#64) ↦₆₄ e.w5) ∗ (((dst + 40#64) ↦₆₄ e.w5) -∗ D5)) ∗ H := by
    dsimp only [r1c_slot6, W]; ac_rfl
  refine Entails.sepExists_right e (Entails.pure_right htag ?_)
  rw [h1]
  exact sepConj_mono_right
    (Entails.wand_intro
      (Entails.trans (Entails.of_eq h2)
        (sepConj_mono (Entails.wand_elim _ _)
          (sepConj_mono (Entails.wand_elim _ _)
            (sepConj_mono (Entails.wand_elim _ _)
              (sepConj_mono (Entails.wand_elim _ _)
                (sepConj_mono (Entails.wand_elim _ _)
                  (sepConj_mono (Entails.wand_elim _ _) (Entails.refl H)))))))))

private theorem r1c_speOwnedAt_post {src dst : BitVec 64} {P Q : SepProp}
    (hPQ : P ⊢ Q) :
    (∃∗ e : r1c_W6,
      ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r1c_slot6 src e ∗ (r1c_slot6 dst e -∗ P)) ⊢
    (∃∗ e : r1c_W6,
      ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r1c_slot6 src e ∗ (r1c_slot6 dst e -∗ Q)) :=
  Entails.sepExists_mono fun _ =>
    sepConj_mono_right (sepConj_mono_right (r1c_wand_post hPQ))

private theorem r1c_shift6 {src dst w0 : BitVec 64}
    {P1 P2 P3 P4 P5 Q1 Q2 Q3 Q4 Q5 H : SepProp}
    (htag : w0 ≠ pendingTag ∧ w0 ≠ okTagVec)
    (h1 : r1c_WordShift (src + 8#64) (dst + 8#64) P1 Q1)
    (h2 : r1c_WordShift (src + 16#64) (dst + 16#64) P2 Q2)
    (h3 : r1c_WordShift (src + 24#64) (dst + 24#64) P3 Q3)
    (h4 : r1c_WordShift (src + 32#64) (dst + 32#64) P4 Q4)
    (h5 : r1c_WordShift (src + 40#64) (dst + 40#64) P5 Q5) :
    ((src ↦₆₄ w0) ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ H) ⊢
      ∃∗ e : r1c_W6,
        ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗
        r1c_slot6 src e ∗
        (r1c_slot6 dst e -∗ ((dst ↦₆₄ w0) ∗ Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ Q5 ∗ H)) := by
  have h0 : (src ↦₆₄ w0) ⊢ (src ↦₆₄ w0) ∗ ((dst ↦₆₄ w0) -∗ (dst ↦₆₄ w0)) :=
    Entails.trans (Entails.of_eq (sepConj_emp (src ↦₆₄ w0)).symm)
      (sepConj_mono_right (r1c_wand_refl (dst ↦₆₄ w0)))
  refine Entails.trans
    (sepConj_mono h0
      (sepConj_mono h1
        (sepConj_mono h2
          (sepConj_mono h3
            (sepConj_mono h4
              (sepConj_mono h5 (Entails.refl H))))))) ?_
  apply r1c_peel; intro w1; apply r1c_keep
  apply r1c_peel; intro w2; apply r1c_keep
  apply r1c_peel; intro w3; apply r1c_keep
  apply r1c_peel; intro w4; apply r1c_keep
  apply r1c_peel; intro w5
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (r1c_ws_combine6 ⟨w0, w1, w2, w3, w4, w5⟩ (dst ↦₆₄ w0) Q1 Q2 Q3 Q4 Q5 H htag)

private theorem r1c_speWord_tags {i : Nat} (hi : i ≤ 40) :
    speWord i ≠ pendingTag ∧ speWord i ≠ okTagVec := by
  unfold speWord pendingTag okTagVec
  constructor <;> bv_omega

private theorem r1c_cap_tags {cap : BitVec 64} (hcap : cap.toNat < 2 ^ 63) :
    cap ≠ pendingTag ∧ cap ≠ okTagVec := by
  unfold pendingTag okTagVec
  constructor <;> bv_omega

private theorem r1c_plainSpeTag_le {i : Nat} (h : RunDrop.PlainSpeTag i) : i ≤ 40 := by
  unfold RunDrop.PlainSpeTag RunDrop.plainSpeTags at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> omega

private theorem r1c_strSpeTag_le {i : Nat} (h : RunDrop.StrSpeTag i) : i ≤ 40 := by
  unfold RunDrop.StrSpeTag RunDrop.strSpeTags at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Unpack any 48-byte `RunDrop.speOwnedAt A src k` into 6 words `e` with `e.w0 ∉ {-3, -2}` and
a pure-`SepProp` magic wand restoring `RunDrop.speOwnedAt A dst k` from `r1c_slot6 dst e`. -/
private theorem r1c_speOwnedAt_words6 (A : RustAlloc) (src dst : BitVec 64)
    (k : RunDrop.SpeOwned) :
    RunDrop.speOwnedAt A src k ⊢
      ∃∗ e : r1c_W6,
        ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗
        r1c_slot6 src e ∗
        (r1c_slot6 dst e -∗ RunDrop.speOwnedAt A dst k) := by
  have hw1_mem32 : ∀ (i : Nat) (P1 Q1 : SepProp), i ≤ 40 →
      r1c_WordShift (src + 8#64) (dst + 8#64) P1 Q1 →
      ((src ↦₆₄ speWord i) ∗ P1 ∗ memRegion (src + 16#64) 32) ⊢
        ∃∗ e : r1c_W6,
          ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r1c_slot6 src e ∗
          (r1c_slot6 dst e -∗ ((dst ↦₆₄ speWord i) ∗ Q1 ∗ memRegion (dst + 16#64) 32)) := by
    intro i P1 Q1 hi h1
    rw [ProofLib.memRegion_split' (b := src + 16#64) (n := 8) (k := 24) (b' := src + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := src + 24#64) (n := 8) (k := 16) (b' := src + 32#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := src + 32#64) (n := 8) (k := 8) (b' := src + 40#64) rfl (by bv_omega) (by decide)]
    refine Entails.trans
      (Entails.of_eq (by rw [← sepConj_emp (memRegion (src + 40#64) 8)]; ac_rfl))
      (Entails.trans
        (r1c_shift6 (H := emp) (r1c_speWord_tags hi) h1
          (r1c_ws_mem8 (src + 16#64) (dst + 16#64))
          (r1c_ws_mem8 (src + 24#64) (dst + 24#64))
          (r1c_ws_mem8 (src + 32#64) (dst + 32#64))
          (r1c_ws_mem8 (src + 40#64) (dst + 40#64)))
        (r1c_speOwnedAt_post ?_))
    rw [ProofLib.memRegion_split' (b := dst + 16#64) (n := 8) (k := 24) (b' := dst + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := dst + 24#64) (n := 8) (k := 16) (b' := dst + 32#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := dst + 32#64) (n := 8) (k := 8) (b' := dst + 40#64) rfl (by bv_omega) (by decide)]
    exact Entails.of_eq (by rw [sepConj_emp])
  have hplain40 : ∀ (i : Nat), i ≤ 40 →
      ((src ↦₆₄ speWord i) ∗ memRegion (src + 8#64) 40) ⊢
        ∃∗ e : r1c_W6,
          ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r1c_slot6 src e ∗
          (r1c_slot6 dst e -∗ ((dst ↦₆₄ speWord i) ∗ memRegion (dst + 8#64) 40)) := by
    intro i hi
    rw [ProofLib.memRegion_split' (b := src + 8#64) (n := 8) (k := 32) (b' := src + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := dst + 8#64) (n := 8) (k := 32) (b' := dst + 16#64) rfl (by bv_omega) (by decide)]
    exact Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans (hw1_mem32 i _ _ hi (r1c_ws_mem8 (src + 8#64) (dst + 8#64)))
        (r1c_speOwnedAt_post (Entails.of_eq (by ac_rfl))))
  have hw1_u8_mem32 : ∀ (i : Nat) (v : BitVec 8), i ≤ 40 →
      ((src ↦₆₄ speWord i) ∗ ((src + 8#64) ↦₈ v) ∗ memRegion (src + 9#64) 39) ⊢
        ∃∗ e : r1c_W6,
          ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r1c_slot6 src e ∗
          (r1c_slot6 dst e -∗
            ((dst ↦₆₄ speWord i) ∗ ((dst + 8#64) ↦₈ v) ∗ memRegion (dst + 9#64) 39)) := by
    intro i v hi
    rw [ProofLib.memRegion_split' (b := src + 9#64) (n := 7) (k := 32) (b' := src + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := dst + 9#64) (n := 7) (k := 32) (b' := dst + 16#64) rfl (by bv_omega) (by decide)]
    have hs9 : src + 8#64 + 1#64 = src + 9#64 := by bv_omega
    have hd9 : dst + 8#64 + 1#64 = dst + 9#64 := by bv_omega
    have hu8 := r1c_ws_u8pad7 (src + 8#64) (dst + 8#64) v
    rw [hs9, hd9] at hu8
    exact Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans (hw1_mem32 i _ _ hi hu8)
        (r1c_speOwnedAt_post (Entails.of_eq (by ac_rfl))))
  have hvec_at8 : ∀ (i : Nat) (bs : List (BitVec 8)) (P4 P5 Q4 Q5 H : SepProp), i ≤ 40 →
      r1c_WordShift (src + 32#64) (dst + 32#64) P4 Q4 →
      r1c_WordShift (src + 40#64) (dst + 40#64) P5 Q5 →
      ((src ↦₆₄ speWord i) ∗ vecU8 A (src + 8#64) bs ∗ P4 ∗ P5 ∗ H) ⊢
        ∃∗ e : r1c_W6,
          ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r1c_slot6 src e ∗
          (r1c_slot6 dst e -∗ ((dst ↦₆₄ speWord i) ∗ vecU8 A (dst + 8#64) bs ∗ Q4 ∗ Q5 ∗ H)) := by
    intro i bs P4 P5 Q4 Q5 H hi h4 h5
    conv => lhs; dsimp only [vecU8]
    apply r1c_peel; intro cap
    apply r1c_peel; intro ptr
    rw [r1c_vecU8At_eq]
    have hs16 : src + 8#64 + 8#64 = src + 16#64 := by bv_omega
    have hs24 : src + 8#64 + 16#64 = src + 24#64 := by bv_omega
    have hd16 : dst + 8#64 + 8#64 = dst + 16#64 := by bv_omega
    have hd24 : dst + 8#64 + 16#64 = dst + 24#64 := by bv_omega
    rw [hs16, hs24]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans
        (r1c_shift6 (H := r1c_vecHeap A cap ptr bs ∗ H) (r1c_speWord_tags hi)
          (r1c_ws_u64 (src + 8#64) (dst + 8#64) cap)
          (r1c_ws_u64 (src + 16#64) (dst + 16#64) ptr)
          (r1c_ws_u64 (src + 24#64) (dst + 24#64) (BitVec.ofNat 64 bs.length))
          h4 h5)
        (r1c_speOwnedAt_post ?_))
    rw [← hd16, ← hd24]
    have hvec :
        ((dst + 8#64) ↦₆₄ cap) ∗ ((dst + 8#64 + 8#64) ↦₆₄ ptr) ∗
          ((dst + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          r1c_vecHeap A cap ptr bs ⊢
        vecU8 A (dst + 8#64) bs :=
      Entails.sepExists_right cap
        (Entails.sepExists_right ptr (Entails.of_eq (r1c_vecU8At_eq A (dst + 8#64) cap ptr bs).symm))
    exact r1c_perm_post
      (r1c_perm
        (sepConj_mono hvec (Entails.refl ((dst ↦₆₄ speWord i) ∗ Q4 ∗ Q5 ∗ H)))
        (by ac_rfl))
      (by ac_rfl)
  cases k with
  | badKemKeyType => exact hplain40 31 (by omega)
  | badKemKeyLength => exact hplain40 33 (by omega)
  | plain i hi => exact hplain40 i (r1c_plainSpeTag_le hi)
  | withString i hi =>
    dsimp only [RunDrop.speOwnedAt]
    apply r1c_peel; intro bs
    rw [show (0x20#64 : BitVec 64) = 32#64 from rfl,
        ProofLib.memRegion_split' (b := src + 32#64) (n := 8) (k := 8) (b' := src + 40#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := dst + 32#64) (n := 8) (k := 8) (b' := dst + 40#64) rfl (by bv_omega) (by decide)]
    refine Entails.trans
      (Entails.of_eq (by rw [← sepConj_emp (memRegion (src + 40#64) 8)]; ac_rfl))
      (Entails.trans
        (hvec_at8 i bs _ _ _ _ emp (r1c_strSpeTag_le hi)
          (r1c_ws_mem8 (src + 32#64) (dst + 32#64))
          (r1c_ws_mem8 (src + 40#64) (dst + 40#64)))
        (r1c_speOwnedAt_post ?_))
    exact r1c_perm_post
      (sepConj_mono_right
        (sepConj_mono_left (Entails.sepExists_right bs (Entails.refl _))))
      (by rw [sepConj_emp])
  | untrustedIdentity addr =>
    dsimp only [RunDrop.speOwnedAt, apiErrAt, addrCloneAt]
    have hs32 : src + 8#64 + 0x18#64 = src + 32#64 := by bv_omega
    have hs33 : src + 8#64 + 0x19#64 = src + 33#64 := by bv_omega
    have hd32 : dst + 8#64 + 0x18#64 = dst + 32#64 := by bv_omega
    have hd33 : dst + 8#64 + 0x19#64 = dst + 33#64 := by bv_omega
    have hs33' : src + 32#64 + 1#64 = src + 33#64 := by bv_omega
    have hd33' : dst + 32#64 + 1#64 = dst + 33#64 := by bv_omega
    have hu8 := r1c_ws_u8pad7 (src + 32#64) (dst + 32#64) addr.device
    rw [hs33', hd33'] at hu8
    rw [hs32, hs33, hd32, hd33, show (0x28#64 : BitVec 64) = 40#64 from rfl]
    exact Entails.trans
      (Entails.of_eq (by rw [← sepConj_emp (memRegion (src + 40#64) 8)]; ac_rfl))
      (Entails.trans
        (hvec_at8 speUntrustedIdentity addr.name _ _ _ _ emp (by decide)
          hu8 (r1c_ws_mem8 (src + 40#64) (dst + 40#64)))
        (r1c_speOwnedAt_post (Entails.of_eq (by rw [sepConj_emp]; ac_rfl))))
  | sessionNotFound addr op =>
    dsimp only [RunDrop.speOwnedAt, apiErrAt, addrCloneAt, strRefAt, vecU8]
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_ex_left; intro cap
    apply r1c_ex_left; intro ptr
    rw [← sepConj_assoc, ← sepConj_assoc]
    apply r1c_peel_end; intro p
    rw [r1c_vecU8At_eq]
    have hs28 : src + 0x20#64 + asm64% boxSliceLenOff = src + 40#64 := by bv_omega
    have hd28 : dst + 0x20#64 + asm64% boxSliceLenOff = dst + 40#64 := by bv_omega
    have hs25 : src + 24#64 + 1#64 = src + 25#64 := by bv_omega
    have hd25 : dst + 24#64 + 1#64 = dst + 25#64 := by bv_omega
    have hu8 := r1c_ws_u8pad7 (src + 24#64) (dst + 24#64) addr.device
    rw [hs25, hd25] at hu8
    rw [hs28, show (0x18#64 : BitVec 64) = 24#64 from rfl,
        show (0x19#64 : BitVec 64) = 25#64 from rfl,
        show (0x20#64 : BitVec 64) = 32#64 from rfl] at *
    refine Entails.trans
      (r1c_perm
        (sepConj_mono (r1c_vecHeap_cap_lt A cap ptr addr.name)
          (Entails.refl ((src ↦₆₄ cap) ∗ ((src + 8#64) ↦₆₄ ptr) ∗
            ((src + 16#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗
            (((src + 24#64) ↦₈ addr.device) ∗ memRegion (src + 25#64) 7) ∗
            ((src + 32#64) ↦₆₄ p) ∗ ((src + 40#64) ↦₆₄ BitVec.ofNat 64 (utf8 op).length) ∗
            (p ↦ᵣ utf8 op))))
        (by ac_rfl)) ?_
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hcap_lt
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans
        (r1c_shift6 (H := r1c_vecHeap A cap ptr addr.name ∗ (p ↦ᵣ utf8 op))
          (r1c_cap_tags hcap_lt)
          (r1c_ws_u64 (src + 8#64) (dst + 8#64) ptr)
          (r1c_ws_u64 (src + 16#64) (dst + 16#64) (BitVec.ofNat 64 addr.name.length))
          hu8
          (r1c_ws_u64 (src + 32#64) (dst + 32#64) p)
          (r1c_ws_u64 (src + 40#64) (dst + 40#64) (BitVec.ofNat 64 (utf8 op).length)))
        (r1c_speOwnedAt_post ?_))
    rw [← hd28]
    have hvec :
        (dst ↦₆₄ cap) ∗ ((dst + 8#64) ↦₆₄ ptr) ∗
          ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 addr.name.length) ∗
          r1c_vecHeap A cap ptr addr.name ⊢
        ∃∗ cap', ∃∗ ptr', vecU8At A dst cap' ptr' addr.name :=
      Entails.sepExists_right cap
        (Entails.sepExists_right ptr (Entails.of_eq (r1c_vecU8At_eq A dst cap ptr addr.name).symm))
    have hstr :
        ((dst + 32#64) ↦₆₄ p) ∗
          ((dst + 32#64 + asm64% boxSliceLenOff) ↦₆₄ BitVec.ofNat 64 (utf8 op).length) ∗
          (p ↦ᵣ utf8 op) ⊢
        ∃∗ p', ((dst + 32#64) ↦₆₄ p') ∗
          ((dst + 32#64 + asm64% boxSliceLenOff) ↦₆₄ BitVec.ofNat 64 (utf8 op).length) ∗
          (p' ↦ᵣ utf8 op) :=
      Entails.sepExists_right p (Entails.refl _)
    exact r1c_perm_post
      (r1c_perm
        (sepConj_mono hvec
          (sepConj_mono (Entails.refl (((dst + 24#64) ↦₈ addr.device) ∗ memRegion (dst + 25#64) 7))
            hstr))
        (by ac_rfl))
      (by ac_rfl)
  | proto fnName err =>
    cases err with
    | panic =>
      dsimp only [RunDrop.speOwnedAt, speAt]
      rw [← sepConj_emp ⌜False⌝]
      exact Entails.pure_left False.elim
    | invalidProtobufEncoding => exact hplain40 2 (by omega)
    | noKeyTypeIdentifier => exact hplain40 7 (by omega)
    | invalidKeyAgreement => exact hplain40 10 (by omega)
    | ciphertextMessageTooShort n =>
      exact hw1_mem32 3 _ _ (by omega) (r1c_ws_u64 (src + 8#64) (dst + 8#64) (BitVec.ofNat 64 n))
    | badKeyLength n =>
      exact hw1_mem32 9 _ _ (by omega) (r1c_ws_u64 (src + 8#64) (dst + 8#64) (BitVec.ofNat 64 n))
    | legacyCiphertextVersion v => exact hw1_u8_mem32 4 v (by omega)
    | unrecognizedCiphertextVersion v => exact hw1_u8_mem32 5 v (by omega)
    | badKeyType v => exact hw1_u8_mem32 8 v (by omega)
    | duplicatedMessage c1 c2 =>
      dsimp only [RunDrop.speOwnedAt, speAt]
      have hs12 : src + 8#64 + 4#64 = src + 12#64 := by bv_omega
      have hd12 : dst + 8#64 + 4#64 = dst + 12#64 := by bv_omega
      have hu32 := r1c_ws_u32x2 (src + 8#64) (dst + 8#64) c1 c2
      rw [hs12, hd12] at hu32
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (Entails.trans (hw1_mem32 23 _ _ (by omega) hu32)
          (r1c_speOwnedAt_post (Entails.of_eq (by ac_rfl))))
    | invalidSessionStructure rsn =>
      dsimp only [RunDrop.speOwnedAt, speAt, strRefAt]
      apply r1c_peel; intro p
      have hs16 : src + 8#64 + asm64% boxSliceLenOff = src + 16#64 := by bv_omega
      have hd16 : dst + 8#64 + asm64% boxSliceLenOff = dst + 16#64 := by bv_omega
      rw [hs16, hd16,
          ProofLib.memRegion_split' (b := src + 24#64) (n := 8) (k := 16) (b' := src + 32#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := src + 32#64) (n := 8) (k := 8) (b' := src + 40#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := dst + 24#64) (n := 8) (k := 16) (b' := dst + 32#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := dst + 32#64) (n := 8) (k := 8) (b' := dst + 40#64) rfl (by bv_omega) (by decide)]
      refine Entails.trans (Entails.of_eq (by ac_rfl))
        (Entails.trans
          (r1c_shift6 (H := p ↦ᵣ invalidSessionStructureStr rsn) (r1c_speWord_tags (i := 20) (by omega))
            (r1c_ws_u64 (src + 8#64) (dst + 8#64) p)
            (r1c_ws_u64 (src + 16#64) (dst + 16#64) (BitVec.ofNat 64 (invalidSessionStructureStr rsn).length))
            (r1c_ws_mem8 (src + 24#64) (dst + 24#64))
            (r1c_ws_mem8 (src + 32#64) (dst + 32#64))
            (r1c_ws_mem8 (src + 40#64) (dst + 40#64)))
          (r1c_speOwnedAt_post ?_))
      have hstr :
          ((dst + 8#64) ↦₆₄ p) ∗ ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr rsn).length) ∗
            (p ↦ᵣ invalidSessionStructureStr rsn) ⊢
          ∃∗ p', ((dst + 8#64) ↦₆₄ p') ∗
            ((dst + 8#64 + asm64% boxSliceLenOff) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr rsn).length) ∗
            (p' ↦ᵣ invalidSessionStructureStr rsn) := by
        rw [hd16]; exact Entails.sepExists_right p (Entails.refl _)
      exact r1c_perm_post
        (r1c_perm
          (sepConj_mono hstr
            (Entails.refl ((dst ↦₆₄ speWord 20) ∗
              (memRegion (dst + 24#64) 8 ∗ memRegion (dst + 32#64) 8) ∗ memRegion (dst + 40#64) 8)))
          (by ac_rfl))
        (by ac_rfl)
    | invalidState =>
      dsimp only [RunDrop.speOwnedAt, speAt, strRefAt]
      apply r1c_peel; intro bs
      rw [← sepConj_assoc]
      apply r1c_peel_end; intro p
      have hs40 : src + 32#64 + asm64% boxSliceLenOff = src + 40#64 := by bv_omega
      have hd40 : dst + 32#64 + asm64% boxSliceLenOff = dst + 40#64 := by bv_omega
      rw [hs40]
      refine Entails.trans (Entails.of_eq (by ac_rfl))
        (Entails.trans
          (hvec_at8 1 bs _ _ _ _ (p ↦ᵣ fnName) (by omega)
            (r1c_ws_u64 (src + 32#64) (dst + 32#64) p)
            (r1c_ws_u64 (src + 40#64) (dst + 40#64) (BitVec.ofNat 64 fnName.length)))
          (r1c_speOwnedAt_post ?_))
      have hstr :
          ((dst + 32#64) ↦₆₄ p) ∗ ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 fnName.length) ∗
            (p ↦ᵣ fnName) ⊢
          ∃∗ p', ((dst + 32#64) ↦₆₄ p') ∗
            ((dst + 32#64 + asm64% boxSliceLenOff) ↦₆₄ BitVec.ofNat 64 fnName.length) ∗
            (p' ↦ᵣ fnName) := by
        rw [hd40]; exact Entails.sepExists_right p (Entails.refl _)
      exact r1c_perm_post
        (r1c_perm
          (sepConj_mono (Entails.refl (dst ↦₆₄ speWord 1))
            (sepConj_mono
              (Entails.sepExists_right bs (Entails.refl _) :
                vecU8 A (dst + 8#64) bs ⊢ ∃∗ bs', vecU8 A (dst + 8#64) bs')
              hstr))
          (by ac_rfl))
        (by ac_rfl)
    | invalidMessage mt rsn =>
      have hinval : ∀ (bs : List (BitVec 8)),
          ((src ↦₆₄ speWord 24) ∗ vecU8 A (src + 8#64) bs ∗
            ((src + 32#64) ↦₈ msgTypeByte mt) ∗ memRegion (src + 33#64) 15) ⊢
            ∃∗ e : r1c_W6,
              ⌜e.w0 ≠ pendingTag ∧ e.w0 ≠ okTagVec⌝ ∗ r1c_slot6 src e ∗
              (r1c_slot6 dst e -∗
                ((dst ↦₆₄ speWord 24) ∗ vecU8 A (dst + 8#64) bs ∗
                  ((dst + 32#64) ↦₈ msgTypeByte mt) ∗ memRegion (dst + 33#64) 15)) := by
        intro bs
        rw [ProofLib.memRegion_split' (b := src + 33#64) (n := 7) (k := 8) (b' := src + 40#64) rfl (by bv_omega) (by decide),
            ProofLib.memRegion_split' (b := dst + 33#64) (n := 7) (k := 8) (b' := dst + 40#64) rfl (by bv_omega) (by decide)]
        have hs33 : src + 32#64 + 1#64 = src + 33#64 := by bv_omega
        have hd33 : dst + 32#64 + 1#64 = dst + 33#64 := by bv_omega
        have hu8 := r1c_ws_u8pad7 (src + 32#64) (dst + 32#64) (msgTypeByte mt)
        rw [hs33, hd33] at hu8
        exact Entails.trans
          (Entails.of_eq (by rw [← sepConj_emp (memRegion (src + 40#64) 8)]; ac_rfl))
          (Entails.trans
            (hvec_at8 24 bs _ _ _ _ emp (by omega) hu8
              (r1c_ws_mem8 (src + 40#64) (dst + 40#64)))
            (r1c_speOwnedAt_post (Entails.of_eq (by rw [sepConj_emp]; ac_rfl))))
      cases rsn with
      | decryptionFailed =>
        dsimp only [RunDrop.speOwnedAt, speAt, invalidMessageStrAt]
        rw [show (src ↦₆₄ speWord 24) ∗ ⌜False⌝ ∗ ((src + 32#64) ↦₈ msgTypeByte mt) ∗
              memRegion (src + 33#64) 15 =
            ⌜False⌝ ∗ ((src ↦₆₄ speWord 24) ∗ ((src + 32#64) ↦₈ msgTypeByte mt) ∗
              memRegion (src + 33#64) 15) by ac_rfl]
        exact Entails.pure_left False.elim
      | tooFarInFuture => exact hinval tooFarInFutureStr
      | macFailed => exact hinval macFailedStr
      | pqRatchet =>
        dsimp only [RunDrop.speOwnedAt, speAt, invalidMessageStrAt]
        apply r1c_peel; intro bs
        exact Entails.trans (hinval bs)
          (r1c_speOwnedAt_post
            (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right bs (Entails.refl _)))))
      | badCiphertext =>
        dsimp only [RunDrop.speOwnedAt, speAt, invalidMessageStrAt]
        apply r1c_peel; intro bs
        exact Entails.trans (hinval bs)
          (r1c_speOwnedAt_post
            (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right bs (Entails.refl _)))))

/-! ## 4. v0.31 State Normalization, Bundle/Address Collapse & Ok Tail (`0x2908 → 0x0f8c`) -/

private theorem r1c_extractLsb_append_lo (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
private theorem r1c_extractLsb_append_hi (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
private theorem r1c_calleeSavedVRegs_q0 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]
private theorem r1c_calleeSavedVRegs_q1 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 1#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]
private theorem r1c_calleeSavedVRegs_q2 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 2#5 v) = calleeSavedVRegs s := by
  simp [calleeSavedVRegs, State.writeVReg128, VRegFile.calleeSaved, VRegFile.write, VRegFile.read]
private theorem r1c_calleeSavedVRegs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := by cases s; cases r <;> rfl
private theorem r1c_calleeSavedVRegs_setPC (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl
private theorem r1c_calleeSavedVRegs_setMem (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl
private theorem r1c_calleeSavedVRegs_setPState (s : State) (ps : PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := by cases s; rfl
private theorem r1c_readReg64_setPState (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
private theorem r1c_sp_setPState (s : State) (ps : PState) :
    (s.setPState ps).sp = s.sp := by cases s; rfl
private theorem r1c_mem_setPState (s : State) (ps : PState) :
    (s.setPState ps).mem = s.mem := by cases s; rfl
private theorem r1c_status_setPState (s : State) (ps : PState) :
    (s.setPState ps).status = s.status := by cases s; rfl
private theorem r1c_trace_setPState (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := by cases s; rfl
private theorem r1c_symtab_setPState (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by cases s; rfl
private theorem r1c_fs_setPState (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl
private theorem r1c_fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl
private theorem r1c_fs_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).fs = s.fs := by cases s; rfl
private theorem r1c_fs_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl
private theorem r1c_fs_setMem (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

ls_attribute [local simp]
  r1c_extractLsb_append_lo r1c_extractLsb_append_hi
  r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
  r1c_calleeSavedVRegs_writeReg64
  r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPState
  r1c_readReg64_setPState r1c_sp_setPState r1c_mem_setPState r1c_status_setPState
  r1c_trace_setPState r1c_symtab_setPState r1c_fs_setPState
  r1c_fs_writeReg64 r1c_fs_writeVReg128 r1c_fs_setPC r1c_fs_setMem
ls_attribute [local arm64_norm]
  r1c_extractLsb_append_lo r1c_extractLsb_append_hi
  r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
  r1c_calleeSavedVRegs_writeReg64
  r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPState
  r1c_readReg64_setPState r1c_sp_setPState r1c_mem_setPState r1c_status_setPState
  r1c_trace_setPState r1c_symtab_setPState r1c_fs_setPState
  r1c_fs_writeReg64 r1c_fs_writeVReg128 r1c_fs_setPC r1c_fs_setMem
ls_attribute [local wp_norm]
  r1c_extractLsb_append_lo r1c_extractLsb_append_hi
  r1c_calleeSavedVRegs_q0 r1c_calleeSavedVRegs_q1 r1c_calleeSavedVRegs_q2
  r1c_calleeSavedVRegs_writeReg64
  r1c_calleeSavedVRegs_setPC r1c_calleeSavedVRegs_setMem r1c_calleeSavedVRegs_setPState
  r1c_readReg64_setPState r1c_sp_setPState r1c_mem_setPState r1c_status_setPState
  r1c_trace_setPState r1c_symtab_setPState r1c_fs_setPState
  r1c_fs_writeReg64 r1c_fs_writeVReg128 r1c_fs_setPC r1c_fs_setMem

local macro "r1c_close_post" : tactic =>
  `(tactic| (repeat' apply And.intro; all_goals (simp (config := { zetaDelta := true }) only [runFsp, wp_norm, arm64_norm, *]; try bv_omega)))

private theorem r1c_spAligned {s0 s : State} (h0 : s0.spAligned = true)
    (hsp : s.sp = runFsp s0) : s.spAligned = true := by
  have h1 : ((s0.sp - 0x2a50#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x2a50#64 h0
  show (s.sp &&& 15#64 == 0#64) = true; rwa [hsp]

private theorem r1c_files_of_trace_eq {P : Program} (hP : TraceFsSound P) {s sm : State}
    (hsteps : Steps P s sm) (htr : sm.trace = s.trace) : sm.fs.files = s.fs.files :=
  hP.files_eq hsteps (by rw [htr]; simp) NoFsEv.nil

private theorem r1c_fnAddr_of_fnOff {img : Obj.Image} {ext : String → Option (State → State)}
    {name : String} {k : Nat} (h : libsignalSessionCode.fnOff name = k) :
    (mProg img ext).fnAddr name = img.base + BitVec.ofNat 64 k :=
  fnAddr_rebase_eq_add_of_fnOff h

private theorem r1c_fnAddr_rel {img : Obj.Image} {ext : String → Option (State → State)}
    {f g : String} {kf kg rel : Nat}
    (hf : libsignalSessionCode.fnOff f = kf) (hg : libsignalSessionCode.fnOff g = kg)
    (hrel : BitVec.ofNat 64 kf + BitVec.ofNat 64 rel = BitVec.ofNat 64 kg) :
    (mProg img ext).fnAddr g = (mProg img ext).fnAddr f + BitVec.ofNat 64 rel := by
  rw [r1c_fnAddr_of_fnOff hf, r1c_fnAddr_of_fnOff hg, BitVec.add_assoc, hrel]

private theorem r1c_fnAddr_rel_back {img : Obj.Image} {ext : String → Option (State → State)}
    {f g : String} {kf kg rel : Nat}
    (hf : libsignalSessionCode.fnOff f = kf) (hg : libsignalSessionCode.fnOff g = kg)
    (hrel : BitVec.ofNat 64 kg + BitVec.ofNat 64 rel = BitVec.ofNat 64 kf) :
    (mProg img ext).fnAddr g = (mProg img ext).fnAddr f - BitVec.ofNat 64 rel := by
  rw [r1c_fnAddr_of_fnOff hf, r1c_fnAddr_of_fnOff hg, ← hrel]; bv_omega

private theorem r1c_frame_seq {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P_in P P' F : SepProp} {post : State → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : ImgCallInv img s) (hP : P_in ⊢ P ∗ F)
    (h : SepWP prog mid s P (fun s1 P1 => post s1 ∧ P1 = P') (fun _ => ⌜False⌝))
    (hk : ∀ s1 : State, ImgCallInv img s1 → s1.pc = mid → s1.status = .Running → post s1 →
      SepWPp prog ret s1 (P' ∗ F) Q Qp oom) :
    SepWPp prog ret s P_in Q Qp oom := by
  intro R hm hL
  have hm0 : s.mem ⊨ P ∗ (F ∗ R) :=
    by simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  rcases h.elim hm0 hL with ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hpost1, rfl⟩ | ⟨_, hfalse⟩⟩
  · obtain ⟨sf, hsteps2, hout⟩ :=
      hk s1 (hinv.of_steps hsteps) hpc1 hrun1 hpost1 R
        (by simpa only [sepConj_assoc] using hm1) (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

private theorem r1c_addr_unpack (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a ⊢
      (((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗ memRegion (a + 16#64) 16) ∗
        addrNameHeap A g) := by
  rw [protocolAddressAt_eq_parts]
  exact r1c_perm_post
    (r1c_perm
      (sepConj_mono (addrUpperAt_entails_memRegion (a + 16#64) g)
        (Entails.refl ((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗ addrNameHeap A g)))
      (by ac_rfl))
    (by ac_rfl)

private theorem r1c_addr_to_mem32 (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a ⊢ memRegion a 32 ∗ addrNameHeap A g := by
  refine Entails.trans (r1c_addr_unpack A g a) (sepConj_mono_left ?_)
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))

private theorem r1c_cliBundleAt_unpack (a : BitVec 64) (b : BundleV)
    (spkSigPtr kpkSigPtr kpkPtr : BitVec 64) :
    cliBundleAt a b spkSigPtr kpkSigPtr kpkPtr ⊢
      memRegion a 192 ∗ memRegion spkSigPtr 64 ∗ memRegion kpkSigPtr 64 ∗
        memRegion kpkPtr 1568 := by
  dsimp only [cliBundleAt]
  apply Entails.sepExists_elim; intro opkId
  apply Entails.pure_left; rintro ⟨hspk64, hkpk64, hkpk1568, _⟩
  have hspkB : (b.spk.bytes.toList).length = 32 := by simp
  have hidB : (b.idKey.publicKey.bytes.toList).length = 32 := by simp
  have hopk32 : (match b.opk with
      | some (_, k) => (a + 157#64) ↦ₛ k.bytes.toList
      | none => memRegion (a + 157#64) 32) ⊢ memRegion (a + 157#64) 32 := by
    cases b.opk with
    | none => exact Entails.refl _
    | some pk =>
      have hpk : pk.2.bytes.toList.length = 32 := by simp
      simpa only [hpk] using ProofLib.pointsToBytes_entails_memRegion (a + 157#64) pk.2.bytes.toList
  have hm192 :
      (a ↦₆₄ 64#64) ∗ ((a + 8#64) ↦₆₄ spkSigPtr) ∗ ((a + 16#64) ↦₆₄ 64#64) ∗
        ((a + 24#64) ↦ₛ b.spk.bytes.toList) ∗ ((a + 56#64) ↦₃₂ b.spkId) ∗ memRegion (a + 60#64) 4 ∗
        ((a + 64#64) ↦₆₄ 64#64) ∗ ((a + 72#64) ↦₆₄ kpkSigPtr) ∗ ((a + 80#64) ↦₆₄ 64#64) ∗
        ((a + 88#64) ↦₆₄ kpkPtr) ∗ ((a + 96#64) ↦₆₄ 1568#64) ∗
        ((a + 104#64) ↦₃₂ b.kpkId) ∗ memRegion (a + 108#64) 4 ∗
        ((a + 112#64) ↦₃₂ (if b.opk.isSome then 1#32 else 0#32)) ∗ ((a + 116#64) ↦₃₂ opkId) ∗
        ((a + 120#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗ ((a + 152#64) ↦₃₂ b.regId) ∗
        ((a + 156#64) ↦₈ (if b.opk.isSome then 1#32 else 0#32).truncate 8) ∗
        (match b.opk with
         | some (_, k) => (a + 157#64) ↦ₛ k.bytes.toList
         | none => memRegion (a + 157#64) 32) ∗
        ((a + 189#64) ↦₈ b.device) ∗ memRegion (a + 190#64) 2 ⊢ memRegion a 192 := by
    rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 184) (b' := a + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 176) (b' := a + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 168) (b' := a + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 24#64) (n := 32) (k := 136) (b' := a + 56#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 56#64) (n := 4) (k := 132) (b' := a + 60#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 60#64) (n := 4) (k := 128) (b' := a + 64#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 64#64) (n := 8) (k := 120) (b' := a + 72#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 72#64) (n := 8) (k := 112) (b' := a + 80#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 80#64) (n := 8) (k := 104) (b' := a + 88#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 88#64) (n := 8) (k := 96) (b' := a + 96#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 96#64) (n := 8) (k := 88) (b' := a + 104#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 104#64) (n := 4) (k := 84) (b' := a + 108#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 108#64) (n := 4) (k := 80) (b' := a + 112#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 112#64) (n := 4) (k := 76) (b' := a + 116#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 116#64) (n := 4) (k := 72) (b' := a + 120#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 120#64) (n := 32) (k := 40) (b' := a + 152#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 152#64) (n := 4) (k := 36) (b' := a + 156#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 156#64) (n := 1) (k := 35) (b' := a + 157#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 157#64) (n := 32) (k := 3) (b' := a + 189#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 189#64) (n := 1) (k := 2) (b' := a + 190#64) rfl (by bv_omega) (by decide)]
    exact r1c_perm_post
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (by simpa only [hspkB] using ProofLib.pointsToBytes_entails_memRegion (a + 24#64) b.spk.bytes.toList)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono (by simpa only [hidB] using ProofLib.pointsToBytes_entails_memRegion (a + 120#64) b.idKey.publicKey.bytes.toList)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (sepConj_mono hopk32
      (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _)))))))))))))))))))))
      (by ac_rfl)
  have h1 : (spkSigPtr ↦ₛ b.spkSig) ⊢ memRegion spkSigPtr 64 := by
    simpa only [hspk64] using ProofLib.pointsToBytes_entails_memRegion spkSigPtr b.spkSig
  have h2 : (kpkSigPtr ↦ₛ b.kpkSig) ⊢ memRegion kpkSigPtr 64 := by
    simpa only [hkpk64] using ProofLib.pointsToBytes_entails_memRegion kpkSigPtr b.kpkSig
  have h3 : (kpkPtr ↦ₛ b.kpk) ⊢ memRegion kpkPtr 1568 := by
    simpa only [hkpk1568] using ProofLib.pointsToBytes_entails_memRegion kpkPtr b.kpk
  exact r1c_perm_post
    (r1c_perm
      (sepConj_mono hm192 (sepConj_mono h1 (sepConj_mono h2 h3)))
      (by ac_rfl))
    (by ac_rfl)

private theorem r1c_run_fnOff :
    libsignalSessionCode.fnOff runName = num% (ls_off% "libsignal_cli::run") :=
  ls_lemma% fnOff "libsignal_cli::run"

private theorem r1c_dealloc_fnOff :
    libsignalSessionCode.fnOff deallocName = num% (ls_off% "__rustc::__rust_dealloc") :=
  ls_stub% "__rustc::__rust_dealloc"

private theorem r1c_dropSpe_fnOff :
    libsignalSessionCode.fnOff cliDropSpeName =
      num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]"

private theorem r1c_call_dealloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {s0 s1 : State}
    {ptr : BitVec 64} {sz resStack retOff : Nat} {Rest : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hsp0 : s0.spAligned = true)
    (hinv1 : ImgCallInv img s1)
    (hpc1 : s1.pc = (mProg img ext).fnAddr runName +
      bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc"))
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = runFsp s0)
    (hlr1 : s1.readReg64 .lr = runPc img ext retOff)
    (hx0 : s1.readReg64 .x0 = ptr)
    (hx1 : (s1.readReg64 .x1).toNat = sz)
    (hx2 : s1.readReg64 .x2 = 1#64)
    (hlay : LayoutOk sz 1)
    (hnext : ∀ s2 : State,
      ImgCallInv img s2 → s2.pc = runPc img ext retOff → s2.status = .Running →
      s2.sp = runFsp s0 → CalleeSavedPreserved s1 s2 →
      s2.fs = s1.fs → s2.trace = s1.trace →
      SepWPp (mProg img ext) (s0.readReg64 .lr) s2
        (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ Rest) Q Qp (runOom s0)) :
    SepWPp (mProg img ext) (s0.readReg64 .lr) s1
      ((A.live ptr sz 1 ∗ memRegion ptr sz) ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ Rest) Q Qp (runOom s0) := by
  have hrel : (mProg img ext).fnAddr deallocName =
      (mProg img ext).fnAddr runName +
        bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc") :=
    r1c_fnAddr_rel r1c_run_fnOff r1c_dealloc_fnOff rfl
  refine r1c_call_inImage (s0 := s0)
    (F := memRegion (runFsp s0 - BitVec.ofNat 64 (resStack - runFrame))
      (resStack - runFrame - extHookStack) ∗ Rest)
    (ptr, sz, 1) hh.allocFs.dealloc hinv1 (hpc1.trans hrel.symm) hrun1
    (r1c_spAligned hsp0 hsp1) hlr1 ?_
    (hnext := fun s2 _ hinv2 hpc2 hrun2 hsp2 hcs2 => ?_)
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
    rw [hsp1, r1c_stackAt_split_ge (runFsp s0) hext_le hsub64]
    conv => rhs; rw [sepConj_assoc]
    refine Entails.pure_right ⟨hx0, hx1, by rw [hx2]; rfl, hlay⟩ ?_
    exact Entails.of_eq (by ac_rfl)
  · refine r1c_sepWPp_weaken_pre
      (P' := ⌜s2.fs = s1.fs ∧ s2.trace = s1.trace⌝ ∗
        (stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ Rest))
      (by
        dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
        rw [hsp1, r1c_stackAt_split_ge (runFsp s0) hext_le hsub64]
        simp only [← sepConj_assoc, pure_sepConj_pure]
        exact Entails.of_eq (by ac_rfl)) ?_
    apply r1c_sepWPp_pure_left; rintro ⟨hfs2, htr2⟩
    exact hnext s2 hinv2 hpc2 hrun2 (hsp2.trans hsp1) hcs2 hfs2 htr2

private def r1c_lowGaps (fsp : BitVec 64) : SepProp :=
  memRegion fsp 0x110 ∗ memRegion (fsp + 0x118#64) 8 ∗ memRegion (fsp + 0x128#64) 16 ∗
    memRegion (fsp + 0x148#64) 16 ∗ memRegion (fsp + 0x160#64) 24 ∗ memRegion (fsp + 0x180#64) 56

private def r1c_lowCells (fsp : BitVec 64) (d : Init2Data) : SepProp :=
  ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
    ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗
    r1c_lowGaps fsp

private theorem r1c_lowCells_to_mem1d0 (fsp : BitVec 64) (d : Init2Data) :
    r1c_lowCells fsp d ⊢ memRegion fsp 0x1d0 := by
  dsimp only [r1c_lowCells, r1c_lowGaps]
  rw [ProofLib.memRegion_split' (b := fsp) (n := 0x110) (k := 0xc0) (b' := fsp + 0x110#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x110#64) (n := 8) (k := 0xb8) (b' := fsp + 0x118#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x118#64) (n := 8) (k := 0xb0) (b' := fsp + 0x120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x120#64) (n := 8) (k := 0xa8) (b' := fsp + 0x128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x128#64) (n := 16) (k := 0x98) (b' := fsp + 0x138#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x138#64) (n := 8) (k := 0x90) (b' := fsp + 0x140#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x140#64) (n := 8) (k := 0x88) (b' := fsp + 0x148#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x148#64) (n := 16) (k := 0x78) (b' := fsp + 0x158#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x158#64) (n := 8) (k := 0x70) (b' := fsp + 0x160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x160#64) (n := 24) (k := 0x58) (b' := fsp + 0x178#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x178#64) (n := 8) (k := 0x50) (b' := fsp + 0x180#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x180#64) (n := 56) (k := 0x18) (b' := fsp + 0x1b8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1b8#64) (n := 8) (k := 0x10) (b' := fsp + 0x1c0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1c0#64) (n := 8) (k := 8) (b' := fsp + 0x1c8#64) rfl (by bv_omega) (by decide)]
  exact r1c_perm
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)))))))))))))))
    (by ac_rfl)

private theorem r1c_rewrite_front {A B : SepProp} (R : SepProp) {P Q : SepProp}
    (hab : A ⊢ B) (h1 : P = A ∗ R) (h2 : B ∗ R = Q) : P ⊢ Q :=
  h2 ▸ h1 ▸ sepConj_mono_left hab

private def r1c_okCore (A : RustAlloc) (g : RunCall) (g' : StoresGhost) (s0 : State) : SepProp :=
  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ anyHeap

private def r1c_lowNoDir (fsp : BitVec 64) (d : Init2Data) : SepProp :=
  ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
    ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ r1c_lowGaps fsp

private def r1c_lowNoMePtr (fsp : BitVec 64) (d : Init2Data) : SepProp :=
  ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
    ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowGaps fsp

private theorem r1c_ok_free_peer {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {g' : StoresGhost}
    {peerG : AddrGhost} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRun img ext s0 s 0x2988)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [])))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (addrNameHeap A peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp
  let mid := memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) [] ∗
    memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  let core := r1c_okCore A g g' s0
  have hrejoin_peer :
      (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗ mid ⊢
      runLocals fsp [(0x208, 24, vecU8 A (fsp + 0x208#64) [])] := by
    have hp32 :
        ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16 ⊢ memRegion (fsp + 0x2a0#64) 32 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x2a0#64) (n := 8) (k := 24) (b' := fsp + 0x2a8#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x2a8#64) (n := 8) (k := 16) (b' := fsp + 0x2b0#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
    dsimp only [runLocals, runLocalsFrom, Nat.sub_zero, mid]
    rw [show fsp + BitVec.ofNat 64 0 = fsp by bv_omega,
        show (0x208 : Nat) + 24 = 0x220 from rfl,
        r1c_split_at fsp 0x220 (0x2a0 - 0x220) runLocalBytes (by decide) (by decide),
        r1c_split_at fsp 0x2a0 32 runLocalBytes (by decide) (by decide)]
    exact r1c_rewrite_front
      (memRegion fsp 0x208 ∗ vecU8 A (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0))
      hp32 (by ac_rfl) (by ac_rfl)
  by_cases hcap : peerG.name.cap = 0#64
  · have hstep : SepWP (mProg img ext) (runPc img ext 0xf8c) s
        ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap)
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap)) (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := r1c_spAligned hs.spAligned hsp
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10632 8
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; rw [hcap, show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := (((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x2b0#64) 16) ∗
        mid ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A peerG hcap))
        (Entails.of_eq (by dsimp only [mid, core]; rw [emp_sepConj]; ac_rfl)))
      hstep fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1⟩ => ?_
    have hat : AtJoin img ext g g' [] s0 s1 :=
      { base := ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        x19 := hx19_1, x20 := hx20_1
        trace := htr1 ▸ htr
        hist := r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist
        ans := hans
        wrOk := hwr }
    refine r1c_sepWPp_weaken_pre ?_ (hjoin s1 g' [] hat)
    dsimp only [joinMem]
    exact r1c_rewrite_front (stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hrejoin_peer (by ac_rfl) (by dsimp only [core, r1c_okCore, fsp]; ac_rfl)
  · have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep : SepWP (mProg img ext)
        ((mProg img ext).fnAddr runName + bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc")) s
        (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPc img ext 0xf8c ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = peerG.name.ptr ∧ s1.readReg64 .x1 = peerG.name.cap ∧
          s1.readReg64 .x2 = 1#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr)))
        (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := r1c_spAligned hs.spAligned hsp
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10632 16
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_pjoin img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 3972 8
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; rw [show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    apply r1c_sepWPp_weaken_pre (sepConj_mono_left (r1c_nameHeap_dealloc A peerG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq
      (F := (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        memRegion (fsp + 0x2b0#64) 16 ∗ mid ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hs.inv (Entails.of_eq (by dsimp only [mid, core]; ac_rfl)) hstep
      fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        ((((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ mid ∗ core))
      (Entails.of_eq (by ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have htr_tot : s2.trace = s.trace := htr2.trans htr1
    have hat : AtJoin img ext g g' [] s0 s2 :=
      { base := ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
        x19 := hx19_2.trans hx19_1, x20 := hx20_2.trans hx20_1
        trace := htr_tot ▸ htr
        hist := r1c_hist_of_eq htr_tot (congrArg FsState.files (hfs2.trans hfs1)) hhist
        ans := hans
        wrOk := hwr }
    refine r1c_sepWPp_weaken_pre ?_ (hjoin s2 g' [] hat)
    dsimp only [joinMem]
    exact r1c_rewrite_front (stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hrejoin_peer (by ac_rfl) (by dsimp only [core, r1c_okCore, fsp]; ac_rfl)

private theorem r1c_ok_free_dir {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRun img ext s0 s 0x2974)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [])))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (addrNameHeap A dirG ∗ r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
        vecU8 A (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        addrNameHeap A d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp dirG
  let tail := vecU8 A (fsp + 0x208#64) [] ∗
    memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
    addrNameHeap A d.peerG ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  have hm208 : r1c_lowCells fsp d ∗ memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ⊢
      memRegion fsp 0x208 := by
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0x1d0) (k := 0x208 - 0x1d0)
          (b' := fsp + 0x1d0#64) rfl rfl (by decide)]
    exact sepConj_mono_left (r1c_lowCells_to_mem1d0 fsp d)
  by_cases hcap : d.dirCap = 0#64
  · have hstep : SepWP (mProg img ext) (runPc img ext 0x2988) s
        ((fsp + 0x1c0#64) ↦₆₄ d.dirCap)
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = ((fsp + 0x1c0#64) ↦₆₄ d.dirCap)) (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := r1c_spAligned hs.spAligned hsp
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10612 8
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; rw [hcap, show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowNoDir fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗ tail ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A dirG hcap))
        (Entails.of_eq (by dsimp only [r1c_lowCells, r1c_lowNoDir, tail]; rw [emp_sepConj]; ac_rfl)))
      hstep fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_free_peer (peerG := d.peerG) hh hext_le hsub64 ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        hx19_1 hx20_1 (htr1 ▸ htr) (r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist)
        (hans) hwr hjoin)
    exact r1c_rewrite_front
      (tail ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hm208
      (by dsimp only [r1c_lowCells, r1c_lowNoDir]; ac_rfl)
      (by dsimp only [tail, fsp]; ac_rfl)
  · have hbeq : (d.dirCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep : SepWP (mProg img ext)
        ((mProg img ext).fnAddr runName + bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc")) s
        (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr))
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPc img ext 0x2988 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = d.dirPtr ∧ s1.readReg64 .x1 = d.dirCap ∧
          s1.readReg64 .x2 = 1#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)))
        (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := r1c_spAligned hs.spAligned hsp
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10612 20
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; rw [show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    apply r1c_sepWPp_weaken_pre (sepConj_mono_left (r1c_nameHeap_dealloc A dirG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq
      (F := (A.live dirG.name.ptr dirG.name.cap.toNat 1 ∗
          memRegion dirG.name.ptr dirG.name.cap.toNat) ∗
        r1c_lowNoDir fsp d ∗ memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗ tail ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hs.inv (Entails.of_eq (by dsimp only [r1c_lowCells, r1c_lowNoDir, tail]; ac_rfl)) hstep
      fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live d.dirPtr d.dirCap.toNat 1 ∗ memRegion d.dirPtr d.dirCap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        ((r1c_lowCells fsp d ∗ memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0)) ∗
          tail ∗ r1c_okCore A g g' s0))
      (Entails.of_eq (by dsimp only [dirG, r1c_lowCells, r1c_lowNoDir]; ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have htr_tot : s2.trace = s.trace := htr2.trans htr1
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_free_peer (peerG := d.peerG) hh hext_le hsub64 ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
        (hx19_2.trans hx19_1) (hx20_2.trans hx20_1) (htr_tot ▸ htr)
        (r1c_hist_of_eq htr_tot (congrArg FsState.files (hfs2.trans hfs1)) hhist)
        (hans) hwr hjoin)
    exact r1c_rewrite_front
      (tail ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hm208 (by ac_rfl) (by dsimp only [tail, fsp]; ac_rfl)

private theorem r1c_ok_free_me {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRun img ext s0 s 0x2960)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [])))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
        vecU8 A (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        addrNameHeap A d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp dirG
  let restDir := addrNameHeap A dirG ∗
    memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
    vecU8 A (fsp + 0x208#64) [] ∗
    memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
    addrNameHeap A d.peerG ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  by_cases hcap : d.meG.name.cap = 0#64
  · have hstep : SepWP (mProg img ext) (runPc img ext 0x2974) s emp
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = emp) (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hx21_0 : s.readReg64 (.gpr 21#5) = 0#64 := hx21.trans hcap
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10592 4
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := addrNameHeap A dirG ∗ r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
        vecU8 A (fsp + 0x208#64) [] ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        addrNameHeap A d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hs.inv
      (sepConj_mono_left (r1c_nameHeap_zero A d.meG hcap)) hstep
      fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx20_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_free_dir (d := d) hh hext_le hsub64 ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        hx19_1 hx20_1 (htr1 ▸ htr) (r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist)
        (hans) hwr hjoin)
    exact Entails.of_eq (by dsimp only [fsp, dirG]; rw [emp_sepConj])
  · have hbeq : (d.meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hbeq21 : (s.readReg64 (.gpr 21#5) == 0#64) = false := by rw [hx21]; exact hbeq
    have hstep : SepWP (mProg img ext)
        ((mProg img ext).fnAddr runName + bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc")) s
        ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr)
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPc img ext 0x2974 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = d.meG.name.ptr ∧ s1.readReg64 .x1 = d.meG.name.cap ∧
          s1.readReg64 .x2 = 1#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res) ∧
          P1 = ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr))
        (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := r1c_spAligned hs.spAligned hsp
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10592 20
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; rw [show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    apply r1c_sepWPp_weaken_pre (sepConj_mono_left (r1c_nameHeap_dealloc A d.meG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq
      (F := (A.live d.meG.name.ptr d.meG.name.cap.toNat 1 ∗
          memRegion d.meG.name.ptr d.meG.name.cap.toNat) ∗
        r1c_lowNoMePtr fsp d ∗ restDir ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hs.inv (Entails.of_eq (by dsimp only [r1c_lowCells, r1c_lowNoMePtr, restDir]; ac_rfl)) hstep
      fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live d.meG.name.ptr d.meG.name.cap.toNat 1 ∗
          memRegion d.meG.name.ptr d.meG.name.cap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        (r1c_lowCells fsp d ∗ restDir ∗ r1c_okCore A g g' s0))
      (Entails.of_eq (by dsimp only [r1c_lowCells, r1c_lowNoMePtr]; ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have htr_tot : s2.trace = s.trace := htr2.trans htr1
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_free_dir (d := d) hh hext_le hsub64 ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
        (hx19_2.trans hx19_1) (hx20_2.trans hx20_1) (htr_tot ▸ htr)
        (r1c_hist_of_eq htr_tot (congrArg FsState.files (hfs2.trans hfs1)) hhist)
        (hans) hwr hjoin)
    exact Entails.of_eq (by dsimp only [restDir, fsp, dirG]; ac_rfl)

private theorem r1c_ok_tail {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRun img ext s0 s 0x2908)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some (some (namedWrites g'.writes, [])))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      ((A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp dirG
  let names := addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d.peerG
  let hiSlots := (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  have h1d0 :
      memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ⊢
        ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
          memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
            (((fsp + 0x208#64) ↦₆₄ v0) ∗ ((fsp + 0x210#64) ↦₆₄ v1) ∗ ((fsp + 0x218#64) ↦₆₄ v2)) ∗
            memRegion (fsp + 0x220#64) (0x2a0 - 0x220) := by
    rw [ProofLib.memRegion_split' (b := fsp + 0x1d0#64) (n := 0x208 - 0x1d0) (k := 0x2a0 - 0x208) (b' := fsp + 0x208#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x208#64) (n := 8) (k := 0x2a0 - 0x210) (b' := fsp + 0x210#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x210#64) (n := 8) (k := 0x2a0 - 0x218) (b' := fsp + 0x218#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x218#64) (n := 8) (k := 0x2a0 - 0x220) (b' := fsp + 0x220#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (fsp + 0x208#64), ProofLib.memRegion_eight (fsp + 0x210#64), ProofLib.memRegion_eight (fsp + 0x218#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v2
    apply Entails.sepExists_elim; intro v1
    apply Entails.sepExists_elim; intro v0
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2 (Entails.of_eq (by ac_rfl))))
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      ((A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        names ∗ r1c_lowCells fsp d ∗ hiSlots ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      h1d0 (by dsimp only [names, hiSlots]; ac_rfl) (by rfl))
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro v0
  apply r1c_sepWPp_exists_left; intro v1
  apply r1c_sepWPp_exists_left; intro v2
  let midVec := memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
    vecU8 A (fsp + 0x208#64) [] ∗
    memRegion (fsp + 0x220#64) (0x2a0 - 0x220)
  let lowAfter1 := ((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
    ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowGaps fsp
  have hstep1 : SepWP (mProg img ext)
      ((mProg img ext).fnAddr runName + bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc")) s
      (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x208#64) ↦₆₄ v0) ∗ ((fsp + 0x210#64) ↦₆₄ v1) ∗ ((fsp + 0x218#64) ↦₆₄ v2))
      (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
        s1.readReg64 .lr = runPc img ext 0x2930 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        s1.readReg64 .x0 = d.spkSigPtr ∧ s1.readReg64 .x1 = 64#64 ∧ s1.readReg64 .x2 = 1#64 ∧
        s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
        s1.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P1 = (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x208#64) ↦₆₄ 0#64) ∗ ((fsp + 0x210#64) ↦₆₄ 1#64) ∗ ((fsp + 0x218#64) ↦₆₄ 0#64)))
      (fun _ => ⌜False⌝) := by
    have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
    have hfp := hs.fp; have hv := hs.vregs
    have hal : s.spAligned = true := r1c_spAligned hs.spAligned hsp
    have hfn := r1c_run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10504 40
    clear hfn
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
    generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
    examples_hide_fetches; rw [show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, by ac_rfl⟩; r1c_close_post
  refine r1c_frame_seq
    (F := (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
      (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      lowAfter1 ∗ memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
      memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
      names ∗ hiSlots ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
    hs.inv (Entails.of_eq (by dsimp only [r1c_lowCells, lowAfter1]; ac_rfl)) hstep1
    fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1⟩ => ?_
  have hlay64 : LayoutOk 64 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  have hlay1568 : LayoutOk 1568 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  have hemp_vec : ((fsp + 0x208#64) ↦₆₄ 0#64) ∗ ((fsp + 0x210#64) ↦₆₄ 1#64) ∗ ((fsp + 0x218#64) ↦₆₄ 0#64) ⊢
      vecU8 A (fsp + 0x208#64) [] := by
    have h := r1c_empty_vecU8 A (fsp + 0x208#64)
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗
      ((A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        r1c_lowCells fsp d ∗ midVec ∗ names ∗ hiSlots ∗ r1c_okCore A g g' s0))
    (r1c_rewrite_front
      (((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
        (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        lowAfter1 ∗ memRegion (fsp + 0x1d0#64) (0x208 - 0x1d0) ∗
        memRegion (fsp + 0x220#64) (0x2a0 - 0x220) ∗
        names ∗ hiSlots ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hemp_vec (by ac_rfl) (by dsimp only [r1c_lowCells, lowAfter1, midVec]; ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
      hx0_1 (by rw [hx1_1]; rfl) hx2_1 hlay64
      fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, _, _, _, _, _, _, _, hfp2, hv2⟩
  let lowNoKpk := ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowGaps fsp
  have hstep2 : SepWP (mProg img ext)
      ((mProg img ext).fnAddr runName + bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc")) s2
      (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr))
      (fun s3 P3 => (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
        s3.readReg64 .lr = runPc img ext 0x2948 ∧
        calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s2.trace ∧ s3.fs = s2.fs ∧
        s3.readReg64 .x0 = d.kpkPtr ∧ s3.readReg64 .x1 = 1568#64 ∧ s3.readReg64 .x2 = 1#64 ∧
        s3.readReg64 (.gpr 19#5) = g.stores ∧ s3.readReg64 (.gpr 20#5) = g.res ∧
        s3.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P3 = (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)))
      (fun _ => ⌜False⌝) := by
    have hfp_2 := hfp2.trans hfp1; have hv_2 := hv2.trans hv1
    have hx19_2' := hx19_2.trans hx19_1; have hx20_2' := hx20_2.trans hx20_1; have hx21_2' := hx21_2.trans hx21_1
    have hal : s2.spAligned = true := r1c_spAligned hs.spAligned hsp2
    have hfn := r1c_run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10544 24
    clear hfn
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc2 ⊢
    generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
    examples_hide_fetches; rw [show fsp = s2.sp from hsp2.symm]; clear hsp2; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, rfl⟩; r1c_close_post
  refine r1c_frame_seq
    (F := (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      lowNoKpk ∗ midVec ∗ names ∗ hiSlots ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
    hinv2 (Entails.of_eq (by dsimp only [r1c_lowCells, lowNoKpk]; ac_rfl)) hstep2
    fun s3 hinv3 hpc3 hrun3 ⟨hsp3, hfp3, hlr3, hv3, htr3, hfs3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx21_3⟩ => ?_
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗
      ((A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        r1c_lowCells fsp d ∗ midVec ∗ names ∗ hiSlots ∗ r1c_okCore A g g' s0))
    (Entails.of_eq (by dsimp only [r1c_lowCells, lowNoKpk]; ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv3 hpc3 hrun3 hsp3 hlr3
      hx0_3 (by rw [hx1_3]; rfl) hx2_3 hlay1568
      fun s4 hinv4 hpc4 hrun4 hsp4 hcs4 hfs4 htr4 => ?_)
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, _, _, _, _, _, _, _, hfp4, hv4⟩
  let lowNoKpkSig := ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowGaps fsp
  have hstep3 : SepWP (mProg img ext)
      ((mProg img ext).fnAddr runName + bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc")) s4
      (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64))
      (fun s5 P5 => (s5.sp = fsp ∧ s5.readReg64 .fp = s0.sp - 0x60#64 ∧
        s5.readReg64 .lr = runPc img ext 0x2960 ∧
        calleeSavedVRegs s5 = calleeSavedVRegs s0 ∧ s5.trace = s4.trace ∧ s5.fs = s4.fs ∧
        s5.readReg64 .x0 = d.kpkSigPtr ∧ s5.readReg64 .x1 = 64#64 ∧ s5.readReg64 .x2 = 1#64 ∧
        s5.readReg64 (.gpr 19#5) = g.stores ∧ s5.readReg64 (.gpr 20#5) = g.res ∧
        s5.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P5 = (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)))
      (fun _ => ⌜False⌝) := by
    have hfp_4 := hfp4.trans hfp3; have hv_4 := hv4.trans hv3
    have hx19_4' := hx19_4.trans hx19_3; have hx20_4' := hx20_4.trans hx20_3; have hx21_4' := hx21_4.trans hx21_3
    have hal : s4.spAligned = true := r1c_spAligned hs.spAligned hsp4
    have hfn := r1c_run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10568 24
    clear hfn
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc4 ⊢
    generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
    examples_hide_fetches; rw [show fsp = s4.sp from hsp4.symm]; clear hsp4; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, rfl⟩; r1c_close_post
  refine r1c_frame_seq
    (F := (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      lowNoKpkSig ∗ midVec ∗ names ∗ hiSlots ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
    hinv4 (Entails.of_eq (by dsimp only [r1c_lowCells, lowNoKpkSig]; ac_rfl)) hstep3
    fun s5 hinv5 hpc5 hrun5 ⟨hsp5, hfp5, hlr5, hv5, htr5, hfs5, hx0_5, hx1_5, hx2_5, hx19_5, hx20_5, hx21_5⟩ => ?_
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗
      (r1c_lowCells fsp d ∗ midVec ∗ names ∗ hiSlots ∗ r1c_okCore A g g' s0))
    (Entails.of_eq (by dsimp only [r1c_lowCells, lowNoKpkSig]; ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv5 hpc5 hrun5 hsp5 hlr5
      hx0_5 (by rw [hx1_5]; rfl) hx2_5 hlay64
      fun s6 hinv6 hpc6 hrun6 hsp6 hcs6 hfs6 htr6 => ?_)
  rcases hcs6 with ⟨hx19_6, hx20_6, hx21_6, _, _, _, _, _, _, _, hfp6, hv6⟩
  have htr_tot : s6.trace = s.trace :=
    htr6.trans (htr5.trans (htr4.trans (htr3.trans (htr2.trans htr1))))
  have hfs_tot : s6.fs = s.fs :=
    hfs6.trans (hfs5.trans (hfs4.trans (hfs3.trans (hfs2.trans hfs1))))
  refine r1c_sepWPp_weaken_pre ?_
    (r1c_ok_free_me (d := d) hh hext_le hsub64 ⟨hpc6, hrun6, hsp6, hfp6.trans hfp5, hinv6, hv6.trans hv5, hs.spAligned⟩
      (hx19_6.trans hx19_5) (hx20_6.trans hx20_5) (hx21_6.trans hx21_5)
      (htr_tot ▸ htr) (r1c_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist)
      (hans) hwr hjoin)
  exact Entails.of_eq (by dsimp only [midVec, names, hiSlots, fsp, dirG]; ac_rfl)

/-! ## 5. Error Tail (`R+0x28f4 → R+0x2998 → R+0x29d0 → R+0x2c7c`) -/

private def r1c_errCore (A : RustAlloc) (g : RunCall) (g' : StoresGhost) (s0 : State) : SepProp :=
  runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
    storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ anyHeap

private theorem r1c_err_free_peer {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {g' : StoresGhost}
    {peerG : AddrGhost} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRun img ext s0 s 0x2c68)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (addrNameHeap A peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion fsp 0x2a0 ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp
  let mid := memRegion fsp 0x2a0 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  let core := r1c_errCore A g g' s0
  have hrejoin_peer :
      (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗ mid ⊢
      runLocals fsp [] := by
    have hp32 :
        ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16 ⊢ memRegion (fsp + 0x2a0#64) 32 := by
      rw [ProofLib.memRegion_split' (b := fsp + 0x2a0#64) (n := 8) (k := 24) (b' := fsp + 0x2a8#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x2a8#64) (n := 8) (k := 16) (b' := fsp + 0x2b0#64) rfl (by bv_omega) (by decide)]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
    dsimp only [runLocals, runLocalsFrom, mid]
    rw [r1c_split_at fsp 0 0x2a0 runLocalBytes (by decide) (by decide),
        r1c_split_at fsp 0x2a0 32 runLocalBytes (by decide) (by decide),
        show fsp + BitVec.ofNat 64 0 = fsp by bv_omega]
    exact r1c_rewrite_front
      (memRegion fsp 0x2a0 ∗ memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0))
      hp32 (by ac_rfl) (by ac_rfl)
  by_cases hcap : peerG.name.cap = 0#64
  · have hstep : SepWP (mProg img ext) (runPc img ext 0x2c7c) s
        ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap)
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores) ∧
          P1 = ((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap)) (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := r1c_spAligned hs.spAligned hsp
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_rejtail img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 11368 8
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; rw [hcap, show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := (((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗ memRegion (fsp + 0x2b0#64) 16) ∗
        mid ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A peerG hcap))
        (Entails.of_eq (by dsimp only [mid, core]; rw [emp_sepConj]; ac_rfl)))
      hstep fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1⟩ => ?_
    have hat : AtReject img ext g g' .postDispatch s0 s1 :=
      { base := ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        x19 := hx19_1
        preRegs := fun h => nomatch h
        trace := htr1 ▸ htr
        hist := r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist
        ans := hans }
    refine r1c_sepWPp_weaken_pre ?_ (hrej s1 g' .postDispatch hat)
    dsimp only [rejectMem]
    exact r1c_rewrite_front (stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hrejoin_peer (by ac_rfl) (by dsimp only [core, r1c_errCore, fsp]; ac_rfl)
  · have hbeq : (peerG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep : SepWP (mProg img ext)
        ((mProg img ext).fnAddr runName + bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc")) s
        (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr))
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPc img ext 0x2c7c ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = peerG.name.ptr ∧ s1.readReg64 .x1 = peerG.name.cap ∧
          s1.readReg64 .x2 = 1#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores) ∧
          P1 = (((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr)))
        (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hal : s.spAligned = true := r1c_spAligned hs.spAligned hsp
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_rejtail img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 11368 20
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; rw [show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    apply r1c_sepWPp_weaken_pre (sepConj_mono_left (r1c_nameHeap_dealloc A peerG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq
      (F := (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        memRegion (fsp + 0x2b0#64) 16 ∗ mid ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hs.inv (Entails.of_eq (by dsimp only [mid, core]; ac_rfl)) hstep
      fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live peerG.name.ptr peerG.name.cap.toNat 1 ∗
          memRegion peerG.name.ptr peerG.name.cap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        ((((fsp + 0x2a0#64) ↦₆₄ peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ mid ∗ core))
      (Entails.of_eq (by ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, _, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have htr_tot : s2.trace = s.trace := htr2.trans htr1
    have hat : AtReject img ext g g' .postDispatch s0 s2 :=
      { base := ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
        x19 := hx19_2.trans hx19_1
        preRegs := fun h => nomatch h
        trace := htr_tot ▸ htr
        hist := r1c_hist_of_eq htr_tot (congrArg FsState.files (hfs2.trans hfs1)) hhist
        ans := hans }
    refine r1c_sepWPp_weaken_pre ?_ (hrej s2 g' .postDispatch hat)
    dsimp only [rejectMem]
    exact r1c_rewrite_front (stackAt fsp (resStack - runFrame) ∗ A.pool ∗ core)
      hrejoin_peer (by ac_rfl) (by dsimp only [core, r1c_errCore, fsp]; ac_rfl)

private theorem r1c_err_free_dir {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRun img ext s0 s 0x2c54)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx22 : s.readReg64 (.gpr 22#5) = d.dirPtr)
    (hx24 : s.readReg64 (.gpr 24#5) = d.dirCap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion fsp 0x2a0 ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp dirG
  let peerRest := addrNameHeap A d.peerG ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion fsp 0x2a0 ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  by_cases hcap : d.dirCap = 0#64
  · have hstep : SepWP (mProg img ext) (runPc img ext 0x2c68) s emp
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores) ∧ P1 = emp) (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hx24_0 : s.readReg64 (.gpr 24#5) = 0#64 := hx24.trans hcap
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_rejtail img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 11348 4
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := peerRest ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A dirG hcap))
        (Entails.of_eq (by dsimp only [peerRest]; ac_rfl)))
      hstep fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_free_peer (g' := g') (peerG := d.peerG) hh hext_le hsub64 ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        hx19_1 (htr1 ▸ htr) (r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist)
        (hans) hrej)
    exact Entails.of_eq (by dsimp only [peerRest, fsp]; rw [emp_sepConj]; ac_rfl)
  · have hbeq : (d.dirCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep : SepWP (mProg img ext)
        ((mProg img ext).fnAddr runName + bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc")) s emp
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPc img ext 0x2c68 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = d.dirPtr ∧ s1.readReg64 .x1 = d.dirCap ∧
          s1.readReg64 .x2 = 1#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores) ∧ P1 = emp)
        (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_rejtail img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 11348 20
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    apply r1c_sepWPp_weaken_pre (sepConj_mono_left (r1c_nameHeap_dealloc A dirG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq
      (F := (A.live dirG.name.ptr dirG.name.cap.toNat 1 ∗
          memRegion dirG.name.ptr dirG.name.cap.toNat) ∗
        peerRest ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      hs.inv (Entails.of_eq (by dsimp only [peerRest]; rw [emp_sepConj]; ac_rfl)) hstep
      fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live d.dirPtr d.dirCap.toNat 1 ∗ memRegion d.dirPtr d.dirCap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ (peerRest ∗ r1c_errCore A g g' s0))
      (Entails.of_eq (by dsimp only [dirG]; rw [emp_sepConj]; ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, _, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have htr_tot : s2.trace = s.trace := htr2.trans htr1
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_free_peer (g' := g') (peerG := d.peerG) hh hext_le hsub64 ⟨hpc2, hrun2, hsp2, hfp2.trans hfp1, hinv2, hv2.trans hv1, hs.spAligned⟩
        (hx19_2.trans hx19_1) (htr_tot ▸ htr)
        (r1c_hist_of_eq htr_tot (congrArg FsState.files (hfs2.trans hfs1)) hhist)
        (hans) hrej)
    exact Entails.of_eq (by dsimp only [peerRest, fsp]; ac_rfl)

private theorem r1c_err_free_me {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRun img ext s0 s 0x2a20)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp dirG
  let hiRest := addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  have hm2a0 : r1c_lowCells fsp d ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ⊢
      memRegion fsp 0x2a0 := by
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0x1d0) (k := 0x2a0 - 0x1d0)
          (b' := fsp + 0x1d0#64) rfl rfl (by decide)]
    exact sepConj_mono_left (r1c_lowCells_to_mem1d0 fsp d)
  by_cases hcap : d.meG.name.cap = 0#64
  · have hstep : SepWP (mProg img ext) (runPc img ext 0x2c54) s
        (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr))
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 (.gpr 19#5) = g.stores ∧
          s1.readReg64 (.gpr 22#5) = d.dirPtr ∧ s1.readReg64 (.gpr 24#5) = d.dirCap) ∧
          P1 = (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)))
        (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hx21_0 : s.readReg64 (.gpr 21#5) = 0#64 := hx21.trans hcap
      have hal : s.spAligned = true := r1c_spAligned hs.spAligned hsp
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10784 28
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; rw [show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := r1c_lowNoDir fsp d ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        hiRest ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      hs.inv
      (Entails.trans (sepConj_mono_left (r1c_nameHeap_zero A d.meG hcap))
        (Entails.of_eq (by dsimp only [r1c_lowCells, r1c_lowNoDir, hiRest]; rw [emp_sepConj]; ac_rfl)))
      hstep fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hv1, htr1, hfs1, hx19_1, hx22_1, hx24_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_free_dir (g' := g') (d := d) hh hext_le hsub64 ⟨hpc1, hrun1, hsp1, hfp1, hinv1, hv1, hs.spAligned⟩
        hx19_1 hx22_1 hx24_1 (htr1 ▸ htr)
        (r1c_hist_of_eq htr1 (congrArg FsState.files hfs1) hhist)
        (hans) hrej)
    exact r1c_rewrite_front
      (hiRest ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      hm2a0 (by dsimp only [r1c_lowCells, r1c_lowNoDir]; ac_rfl)
      (by dsimp only [hiRest, fsp, dirG]; ac_rfl)
  · have hbeq : (d.meG.name.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hstep1 : SepWP (mProg img ext)
        ((mProg img ext).fnAddr runName + bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc")) s
        ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr)
        (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
          s1.readReg64 .lr = runPc img ext 0x2a34 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
          s1.readReg64 .x0 = d.meG.name.ptr ∧ s1.readReg64 .x1 = d.meG.name.cap ∧
          s1.readReg64 .x2 = 1#64 ∧
          s1.readReg64 (.gpr 19#5) = g.stores) ∧
          P1 = ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr))
        (fun _ => ⌜False⌝) := by
      have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
      have hfp := hs.fp; have hv := hs.vregs
      have hbeq21 : (s.readReg64 (.gpr 21#5) == 0#64) = false := by rw [hx21]; exact hbeq
      have hal : s.spAligned = true := r1c_spAligned hs.spAligned hsp
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10784 20
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; rw [show fsp = s.sp from hsp.symm]; clear hsp; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    apply r1c_sepWPp_weaken_pre (sepConj_mono_left (r1c_nameHeap_dealloc A d.meG hcap))
    rw [sepConj_assoc, sepConj_assoc]
    apply r1c_sepWPp_pure_left; intro hlay
    refine r1c_frame_seq
      (F := (A.live d.meG.name.ptr d.meG.name.cap.toNat 1 ∗
          memRegion d.meG.name.ptr d.meG.name.cap.toNat) ∗
        r1c_lowNoMePtr fsp d ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        hiRest ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      hs.inv (Entails.of_eq (by dsimp only [r1c_lowCells, r1c_lowNoMePtr, hiRest]; ac_rfl)) hstep1
      fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx1_1, hx2_1, hx19_1⟩ => ?_
    refine r1c_sepWPp_weaken_pre
      (P' := (A.live d.meG.name.ptr d.meG.name.cap.toNat 1 ∗
          memRegion d.meG.name.ptr d.meG.name.cap.toNat) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        (r1c_lowCells fsp d ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
          hiRest ∗ r1c_errCore A g g' s0))
      (Entails.of_eq (by dsimp only [r1c_lowCells, r1c_lowNoMePtr]; ac_rfl))
      (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv1 hpc1 hrun1 hsp1 hlr1
        hx0_1 (congrArg BitVec.toNat hx1_1) hx2_1 hlay
        fun s2 hinv2 hpc2 hrun2 hsp2 hcs2 hfs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, _, _, _, _, _, _, _, _, _, hfp2, hv2⟩
    have hstep2 : SepWP (mProg img ext) (runPc img ext 0x2c54) s2
        (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr))
        (fun s3 P3 => (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s2.trace ∧ s3.fs = s2.fs ∧
          s3.readReg64 (.gpr 19#5) = g.stores ∧
          s3.readReg64 (.gpr 22#5) = d.dirPtr ∧ s3.readReg64 (.gpr 24#5) = d.dirCap) ∧
          P3 = (((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr)))
        (fun _ => ⌜False⌝) := by
      have hfp_2 := hfp2.trans hfp1; have hv_2 := hv2.trans hv1; have hx19_2' := hx19_2.trans hx19_1
      have hal : s2.spAligned = true := r1c_spAligned hs.spAligned hsp2
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10804 8
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc2 ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; rw [show fsp = s2.sp from hsp2.symm]; clear hsp2; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    refine r1c_frame_seq
      (F := r1c_lowNoDir fsp d ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        hiRest ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      hinv2 (Entails.of_eq (by dsimp only [r1c_lowCells, r1c_lowNoDir]; ac_rfl)) hstep2
      fun s3 hinv3 hpc3 hrun3 ⟨hsp3, hfp3, hv3, htr3, hfs3, hx19_3, hx22_3, hx24_3⟩ => ?_
    have htr_tot : s3.trace = s.trace := htr3.trans (htr2.trans htr1)
    have hfs_tot : s3.fs = s.fs := hfs3.trans (hfs2.trans hfs1)
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_free_dir (g' := g') (d := d) hh hext_le hsub64 ⟨hpc3, hrun3, hsp3, hfp3, hinv3, hv3, hs.spAligned⟩
        hx19_3 hx22_3 hx24_3 (htr_tot ▸ htr)
        (r1c_hist_of_eq htr_tot (congrArg FsState.files hfs_tot) hhist)
        (hans) hrej)
    exact r1c_rewrite_front
      (hiRest ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
      hm2a0 (by dsimp only [r1c_lowCells, r1c_lowNoDir]; ac_rfl)
      (by dsimp only [hiRest, fsp, dirG]; ac_rfl)

private theorem r1c_err_tail {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {g : RunCall} {g' : StoresGhost}
    {d : Init2Data} {k : RunDrop.SpeOwned} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hstk32 : 32 + extHookStack ≤ resStack - runFrame)
    (hext_le : extHookStack ≤ resStack - runFrame)
    (hsub64 : resStack - runFrame ≤ 2 ^ 64)
    (hs : InRun img ext s0 s 0x28f4)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx20 : s.readReg64 (.gpr 20#5) = g.res)
    (hx21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap)
    (htr : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    let dirG : AddrGhost := ⟨⟨d.dirCap, d.dirPtr, d.dir⟩, 0#8⟩
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (RunDrop.speOwnedAt A (fsp + 0x23b0#64) k ∗
        (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
        (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d.peerG ∗
        r1c_lowCells fsp d ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      Q Qp (runOom s0) := by
  intro fsp dirG
  let heaps := (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
    (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
    (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64)
  let names := addrNameHeap A d.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d.peerG
  let lowPeer := r1c_lowCells fsp d ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16)
  have hsplit_1750 :
      memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ⊢
        ∃∗ dst0 : r1c_W6,
          r1c_slot6 (fsp + 0x1750#64) dst0 ∗
            memRegion (fsp + 0x2c0#64) (0x1750 - 0x2c0) ∗
            memRegion (fsp + 0x1780#64) (0x23b0 - 0x1780) := by
    rw [ProofLib.memRegion_split' (b := fsp + 0x2c0#64) (n := 0x1750 - 0x2c0)
          (k := 0x23b0 - 0x1750) (b' := fsp + 0x1750#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x1750#64) (n := 48)
          (k := 0x23b0 - 0x1780) (b' := fsp + 0x1780#64) rfl (by bv_omega) (by decide)]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left (r1c_mem48_to_slot6 (fsp + 0x1750#64)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    exact Entails.sepExists_mono fun _ => Entails.of_eq (by ac_rfl)
  apply r1c_sepWPp_weaken_pre
    (sepConj_mono_left (r1c_speOwnedAt_words6 A (fsp + 0x23b0#64) (fsp + 0x1750#64) k))
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro sw
  rw [sepConj_assoc, sepConj_assoc]
  apply r1c_sepWPp_pure_left; rintro ⟨hnot_pend, hnot_ok⟩
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      (r1c_slot6 (fsp + 0x23b0#64) sw ∗
        (r1c_slot6 (fsp + 0x1750#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x1750#64) k) ∗
        heaps ∗ names ∗ lowPeer ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
      hsplit_1750 (by dsimp only [heaps, names, lowPeer]; ac_rfl) (by rfl))
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro dst0
  let gaps2c0 := memRegion (fsp + 0x2c0#64) (0x1750 - 0x2c0) ∗
    memRegion (fsp + 0x1780#64) (0x23b0 - 0x1780) ∗
    memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0)
  have hcmn3 : ((sw.w0 + 3#64) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by intro h0; apply hnot_pend; unfold pendingTag; bv_omega)
  have hcmn2_eq : ((sw.w0 + 2#64) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by intro h0; apply hnot_ok; unfold okTagVec; bv_omega)
  have hcmn2_ne : ((sw.w0 + 2#64) != 0#64) = true :=
    bne_iff_ne.mpr (by intro h0; apply hnot_ok; unfold okTagVec; bv_omega)
  have hstep_copy : SepWP (mProg img ext) ((mProg img ext).fnAddr cliDropSpeName) s
      (r1c_slot6 (fsp + 0x23b0#64) sw ∗ r1c_slot6 (fsp + 0x1750#64) dst0)
      (fun s1 P1 => (s1.sp = fsp ∧ s1.readReg64 .fp = s0.sp - 0x60#64 ∧
        s1.readReg64 .lr = runPc img ext 0x29d0 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧ s1.trace = s.trace ∧ s1.fs = s.fs ∧
        s1.readReg64 .x0 = fsp + 0x1750#64 ∧
        s1.readReg64 (.gpr 19#5) = g.stores ∧ s1.readReg64 (.gpr 20#5) = g.res ∧
        s1.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P1 = (r1c_slot6 (fsp + 0x23b0#64) sw ∗ r1c_slot6 (fsp + 0x1750#64) sw))
      (fun _ => ⌜False⌝) := by
    have hpc := hs.pc; have hrun := hs.run; have hsp := hs.sp
    have hfp := hs.fp; have hv := hs.vregs
    have hal : s.spAligned = true := r1c_spAligned hs.spAligned hsp
    have hfn0 := r1c_run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 10484 20
    code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 10648 56
    clear hfn0
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
    generalize hfn :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
    examples_hide_fetches
    rw [show fsp = s.sp from hsp.symm]; clear hsp
    dsimp only [r1c_slot6]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm, ← hfn, Program.fnAddr_rebase, r1c_run_fnOff, r1c_dropSpe_fnOff, BitVec.add_assoc, BitVec.reduceAdd])
      (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, by simp only [wp_norm, arm64_norm, BitVec.add_assoc, BitVec.reduceAdd]⟩
    r1c_close_post
  refine r1c_frame_seq
    (F := (r1c_slot6 (fsp + 0x1750#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x1750#64) k) ∗
      gaps2c0 ∗ heaps ∗ names ∗ lowPeer ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
    hs.inv (Entails.of_eq (by dsimp only [gaps2c0]; ac_rfl)) hstep_copy
    fun s1 hinv1 hpc1 hrun1 ⟨hsp1, hfp1, hlr1, hv1, htr1, hfs1, hx0_1, hx19_1, hx20_1, hx21_1⟩ => ?_
  have hwand :
      r1c_slot6 (fsp + 0x1750#64) sw ∗
        (r1c_slot6 (fsp + 0x1750#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x1750#64) k) ⊢
      RunDrop.speOwnedAt A (fsp + 0x1750#64) k := Entails.wand_elim _ _
  have hwand_src :
      r1c_slot6 (fsp + 0x23b0#64) sw ∗ r1c_slot6 (fsp + 0x1750#64) sw ∗
        (r1c_slot6 (fsp + 0x1750#64) sw -∗ RunDrop.speOwnedAt A (fsp + 0x1750#64) k) ⊢
      RunDrop.speOwnedAt A (fsp + 0x1750#64) k ∗ memRegion (fsp + 0x23b0#64) 48 := by
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono hwand (r1c_slot6_to_mem48 (fsp + 0x23b0#64) sw))
  refine r1c_call_inImage (s0 := s0)
    (F := memRegion (fsp + 0x23b0#64) 48 ∗ gaps2c0 ∗ heaps ∗ names ∗ lowPeer ∗ r1c_okCore A g g' s0)
    ⟨fsp + 0x1750#64, k⟩
    (hdrop (resStack - runFrame) hstk32 hsub64)
    hinv1 hpc1 hrun1 (r1c_spAligned hs.spAligned hsp1) hlr1
    (by
      dsimp only [RunDrop.dropSpeOwnedSpec]
      rw [hsp1]
      refine Entails.trans
        (r1c_rewrite_front
          (gaps2c0 ∗ heaps ∗ names ∗ lowPeer ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0)
          hwand_src (by ac_rfl) (by rfl)) ?_
      conv => rhs; rw [sepConj_assoc]
      refine Entails.pure_right hx0_1 (Entails.of_eq (by ac_rfl)))
    (hnext := fun sm hsteps_m hinv_m hpcm hrunm hspm hcsm => ?_)
  rcases hcsm with ⟨hx19_m, hx20_m, hx21_m, _, _, _, _, _, _, _, hfp_m, hv_m⟩
  dsimp only [RunDrop.dropSpeOwnedSpec]
  rw [hsp1, sepConj_assoc]
  apply r1c_sepWPp_pure_left; intro htr_m
  have hfs_m : sm.fs.files = s1.fs.files := r1c_files_of_trace_eq hh.fs hsteps_m htr_m
  have hmerge_2c0 :
      memRegion (fsp + 0x1750#64) 48 ∗ memRegion (fsp + 0x23b0#64) 48 ∗ gaps2c0 ⊢
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) := by
    dsimp only [gaps2c0]
    rw [r1c_split_at fsp 0x2c0 (0x1750 - 0x2c0) runLocalBytes (by decide) (by decide),
        r1c_split_at fsp 0x1750 48 runLocalBytes (by decide) (by decide),
        r1c_split_at fsp 0x1780 (0x23b0 - 0x1780) runLocalBytes (by decide) (by decide),
        r1c_split_at fsp 0x23b0 48 runLocalBytes (by decide) (by decide)]
    exact Entails.of_eq (by ac_rfl)
  have hres_split :
      memRegion g.res runResSize ⊢
        ∃∗ w_res : BitVec 64, (g.res ↦₆₄ w_res) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    have heq : memRegion g.res runResSize =
        (∃∗ w_res : BitVec 64, g.res ↦₆₄ w_res) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
      rw [← ProofLib.memRegion_eight g.res]
      exact ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide)
    rw [heq]; simp only [sepExists_sepConj_left]; exact Entails.refl _
  let coreNoRes := memRegion g.call 56 ∗
    storesAt A g.stores g' ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ anyHeap
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      (A.pool ∗ stackAt fsp (resStack - runFrame) ∗ heaps ∗ names ∗ lowPeer ∗ r1c_okCore A g g' s0)
      hmerge_2c0 (by ac_rfl) (by rfl))
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      (memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) ∗
        A.pool ∗ stackAt fsp (resStack - runFrame) ∗ heaps ∗ names ∗ lowPeer ∗ coreNoRes)
      hres_split (by dsimp only [r1c_okCore, coreNoRes]; ac_rfl) (by rfl))
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro w_res
  have hsp_m : sm.sp = fsp := hspm.trans hsp1
  have hfp_m' : sm.readReg64 .fp = s0.sp - 0x60#64 := hfp_m.trans hfp1
  have hv_m' : calleeSavedVRegs sm = calleeSavedVRegs s0 := hv_m.trans hv1
  have hx19_m' : sm.readReg64 (.gpr 19#5) = g.stores := hx19_m.trans hx19_1
  have hx20_m' : sm.readReg64 (.gpr 20#5) = g.res := hx20_m.trans hx20_1
  have hx21_m' : sm.readReg64 (.gpr 21#5) = d.meG.name.cap := hx21_m.trans hx21_1
  have hlay64 : LayoutOk 64 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  have hlay1568 : LayoutOk 1568 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  let hiSlots := memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
    (((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
      memRegion (fsp + 0x2b0#64) 16) ∗
    memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0)
  let lowAfter1 := ((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
    ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowGaps fsp
  have hstep1 : SepWP (mProg img ext)
      ((mProg img ext).fnAddr runName + bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc")) sm
      ((g.res ↦₆₄ w_res) ∗ ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64))
      (fun s2 P2 => (s2.sp = fsp ∧ s2.readReg64 .fp = s0.sp - 0x60#64 ∧
        s2.readReg64 .lr = runPc img ext 0x29f0 ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧ s2.trace = sm.trace ∧ s2.fs = sm.fs ∧
        s2.readReg64 .x0 = d.spkSigPtr ∧ s2.readReg64 .x1 = 64#64 ∧ s2.readReg64 .x2 = 1#64 ∧
        s2.readReg64 (.gpr 19#5) = g.stores ∧ s2.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P2 = ((g.res ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
          ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64)))
      (fun _ => ⌜False⌝) := by
    have hal : sm.spAligned = true := r1c_spAligned hs.spAligned hsp_m
    have hfn := r1c_run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10704 32
    clear hfn
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpcm ⊢
    generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
    examples_hide_fetches; rw [show fsp = sm.sp from hsp_m.symm]; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, by ac_rfl⟩; r1c_close_post
  refine r1c_frame_seq
    (F := memRegion (g.res + 8#64) (runResSize - 8) ∗
      heaps ∗ lowAfter1 ∗ names ∗ hiSlots ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ coreNoRes)
    hinv_m (Entails.of_eq (by dsimp only [lowPeer, r1c_lowCells, lowAfter1, hiSlots]; ac_rfl)) hstep1
    fun s2 hinv2 hpc2 hrun2 ⟨hsp2, hfp2, hlr2, hv2, htr2, hfs2, hx0_2, hx1_2, hx2_2, hx19_2, hx21_2⟩ => ?_
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.spkSigPtr 64 1 ∗ memRegion d.spkSigPtr 64) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗
      ((A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
        (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        r1c_lowCells fsp d ∗ names ∗ hiSlots ∗ r1c_errCore A g g' s0))
    (Entails.of_eq (by dsimp only [heaps, r1c_lowCells, lowAfter1, r1c_errCore, runResAt, coreNoRes]; ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv2 hpc2 hrun2 hsp2 hlr2
      hx0_2 (by rw [hx1_2]; rfl) hx2_2 hlay64
      fun s3 hinv3 hpc3 hrun3 hsp3 hcs3 hfs3 htr3 => ?_)
  rcases hcs3 with ⟨hx19_3, _, hx21_3, _, _, _, _, _, _, _, hfp3, hv3⟩
  let lowNoKpk := ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowGaps fsp
  have hstep2 : SepWP (mProg img ext)
      ((mProg img ext).fnAddr runName + bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc")) s3
      (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr))
      (fun s4 P4 => (s4.sp = fsp ∧ s4.readReg64 .fp = s0.sp - 0x60#64 ∧
        s4.readReg64 .lr = runPc img ext 0x2a08 ∧
        calleeSavedVRegs s4 = calleeSavedVRegs s0 ∧ s4.trace = s3.trace ∧ s4.fs = s3.fs ∧
        s4.readReg64 .x0 = d.kpkPtr ∧ s4.readReg64 .x1 = 1568#64 ∧ s4.readReg64 .x2 = 1#64 ∧
        s4.readReg64 (.gpr 19#5) = g.stores ∧ s4.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P4 = (((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr)))
      (fun _ => ⌜False⌝) := by
    have hfp_3 := hfp3.trans hfp2; have hv_3 := hv3.trans hv2
    have hx19_3' := hx19_3.trans hx19_2; have hx21_3' := hx21_3.trans hx21_2
    have hal : s3.spAligned = true := r1c_spAligned hs.spAligned hsp3
    have hfn := r1c_run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10736 24
    clear hfn
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc3 ⊢
    generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
    examples_hide_fetches; rw [show fsp = s3.sp from hsp3.symm]; clear hsp3; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, rfl⟩; r1c_close_post
  refine r1c_frame_seq
    (F := (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      lowNoKpk ∗ names ∗ hiSlots ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
    hinv3 (Entails.of_eq (by dsimp only [r1c_lowCells, lowNoKpk]; ac_rfl)) hstep2
    fun s4 hinv4 hpc4 hrun4 ⟨hsp4, hfp4, hlr4, hv4, htr4, hfs4, hx0_4, hx1_4, hx2_4, hx19_4, hx21_4⟩ => ?_
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.kpkPtr 1568 1 ∗ memRegion d.kpkPtr 1568) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗
      ((A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
        r1c_lowCells fsp d ∗ names ∗ hiSlots ∗ r1c_errCore A g g' s0))
    (Entails.of_eq (by dsimp only [r1c_lowCells, lowNoKpk]; ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv4 hpc4 hrun4 hsp4 hlr4
      hx0_4 (by rw [hx1_4]; rfl) hx2_4 hlay1568
      fun s5 hinv5 hpc5 hrun5 hsp5 hcs5 hfs5 htr5 => ?_)
  rcases hcs5 with ⟨hx19_5, _, hx21_5, _, _, _, _, _, _, _, hfp5, hv5⟩
  let lowNoKpkSig := ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗ r1c_lowGaps fsp
  have hstep3 : SepWP (mProg img ext)
      ((mProg img ext).fnAddr runName + bv% (ls_rel% "libsignal_cli::run" "__rustc::__rust_dealloc")) s5
      (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64))
      (fun s6 P6 => (s6.sp = fsp ∧ s6.readReg64 .fp = s0.sp - 0x60#64 ∧
        s6.readReg64 .lr = runPc img ext 0x2a20 ∧
        calleeSavedVRegs s6 = calleeSavedVRegs s0 ∧ s6.trace = s5.trace ∧ s6.fs = s5.fs ∧
        s6.readReg64 .x0 = d.kpkSigPtr ∧ s6.readReg64 .x1 = 64#64 ∧ s6.readReg64 .x2 = 1#64 ∧
        s6.readReg64 (.gpr 19#5) = g.stores ∧ s6.readReg64 (.gpr 21#5) = d.meG.name.cap) ∧
        P6 = (((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x158#64) ↦₆₄ 64#64)))
      (fun _ => ⌜False⌝) := by
    have hfp_5 := hfp5.trans hfp4; have hv_5 := hv5.trans hv4
    have hx19_5' := hx19_5.trans hx19_4; have hx21_5' := hx21_5.trans hx21_4
    have hal : s5.spAligned = true := r1c_spAligned hs.spAligned hsp5
    have hfn := r1c_run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10760 24
    clear hfn
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc5 ⊢
    generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
    examples_hide_fetches; rw [show fsp = s5.sp from hsp5.symm]; clear hsp5; wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, rfl⟩; r1c_close_post
  refine r1c_frame_seq
    (F := (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      lowNoKpkSig ∗ names ∗ hiSlots ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_errCore A g g' s0)
    hinv5 (Entails.of_eq (by dsimp only [r1c_lowCells, lowNoKpkSig]; ac_rfl)) hstep3
    fun s6 hinv6 hpc6 hrun6 ⟨hsp6, hfp6, hlr6, hv6, htr6, hfs6, hx0_6, hx1_6, hx2_6, hx19_6, hx21_6⟩ => ?_
  refine r1c_sepWPp_weaken_pre
    (P' := (A.live d.kpkSigPtr 64 1 ∗ memRegion d.kpkSigPtr 64) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗
      (r1c_lowCells fsp d ∗ names ∗ hiSlots ∗ r1c_errCore A g g' s0))
    (Entails.of_eq (by dsimp only [r1c_lowCells, lowNoKpkSig]; ac_rfl))
    (r1c_call_dealloc hh hext_le hsub64 hs.spAligned hinv6 hpc6 hrun6 hsp6 hlr6
      hx0_6 (by rw [hx1_6]; rfl) hx2_6 hlay64
      fun s7 hinv7 hpc7 hrun7 hsp7 hcs7 hfs7 htr7 => ?_)
  rcases hcs7 with ⟨hx19_7, _, hx21_7, _, _, _, _, _, _, _, hfp7, hv7⟩
  have htr_tot : s7.trace = s.trace :=
    htr7.trans (htr6.trans (htr5.trans (htr4.trans (htr3.trans (htr2.trans (htr_m.trans htr1))))))
  have hfs_tot : s7.fs.files = s.fs.files := by
    have hfs7_m : s7.fs = sm.fs := hfs7.trans (hfs6.trans (hfs5.trans (hfs4.trans (hfs3.trans hfs2))))
    exact (congrArg FsState.files hfs7_m).trans (hfs_m.trans (congrArg FsState.files hfs1))
  refine r1c_sepWPp_weaken_pre ?_
    (r1c_err_free_me (g' := g') (d := d) hh hext_le hsub64 ⟨hpc7, hrun7, hsp7, hfp7.trans hfp6, hinv7, hv7.trans hv6, hs.spAligned⟩
      (hx19_7.trans hx19_6) (hx21_7.trans hx21_6)
      (htr_tot ▸ htr) (r1c_hist_of_eq htr_tot hfs_tot hhist)
      (hans) hrej)
  exact Entails.of_eq (by dsimp only [names, hiSlots, fsp, dirG]; ac_rfl)

/-! ## 6. Main Hop Theorem: `run_hop_init3_ok` (`R+0x28f0 → R+0xf8c / R+0x2c7c`) -/

private theorem r1c_init2Locals_unpack (A : RustAlloc) (fsp : BitVec 64) (d : Init2Data) :
    runLocals fsp (init2Cells A fsp d) ⊢
      (fsp ↦₃₂ 0#32) ∗
      protocolAddressAt A d.peerG (fsp + 0x2a0#64) ∗
      protocolAddressAt A d.meG (fsp + 0x320#64) ∗
      cliBundleAt (fsp + 0x4d0#64) d.bundle d.spkSigPtr d.kpkSigPtr d.kpkPtr ∗
      memRegion (fsp + 0x23b0#64) 48 ∗
      (memRegion (fsp + 4#64) (0x110 - 4) ∗
        ((fsp + 0x110#64) ↦₆₄ d.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x138#64) ↦₆₄ d.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
        ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d.kpkPtr) ∗
        ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
        ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗
        memRegion (fsp + 0x118#64) 8 ∗ memRegion (fsp + 0x128#64) 16 ∗
        memRegion (fsp + 0x148#64) 16 ∗ memRegion (fsp + 0x160#64) 24 ∗
        memRegion (fsp + 0x180#64) 56) ∗
      memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
      (memRegion (fsp + 0x2c0#64) (0x320 - 0x2c0) ∗
        memRegion (fsp + 0x340#64) (0x4d0 - 0x340) ∗
        memRegion (fsp + 0x590#64) (0x23b0 - 0x590)) ∗
      memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) := by
  dsimp only [runLocals, runLocalsFrom, init2Cells]
  simp only [Nat.reduceAdd, Nat.reduceSub, ProofLib.memRegion_zero,
    emp_sepConj, sepConj_emp, BitVec.ofNat_eq_ofNat]
  exact Entails.of_eq (by ac_rfl)

/-- Arm `R1c` hop theorem (`R+0x28f0 → R+0xf8c / R+0x2c7c`): steps
`bl signal_session_handshake::initiate`, invokes `hc.initiate` using `AtInit2.init_facts`, and
routes `.ok ()` through `r1c_ok_tail` to `AtJoin` (`R+0xf8c`) and `.error _` through `r1c_err_tail`
to `AtReject .postDispatch` (`R+0x2c7c`). -/
theorem run_hop_init3_ok_ext {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {g : RunCall} {d2 : Init2Data}
    {s0 s2 : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (hspb : resStack ≤ s0.sp.toNat)
    (he : AtRunEntry S img ext g s0)
    (hi2 : AtInit2 img ext g d2 s0 s2)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    ProofLib.SepWPp (mProg img ext) (s0.readReg64 .lr) s2
      (init2Mem A img g d2 s0 resStack) Q Qp (runOom s0) := by
  let _ := himg
  obtain ⟨hrf, hsub63, hsub64, _, _, _, _, _, _, _, _, _, _, _,
      hstk32, _, hext_le, _, _, hinit_stk, _, _⟩ := runNeed_bounds hres hres64
  have hspb_slot : resStack - runFrame ≤ s2.sp.toNat := by
    have hrf_eq : runFrame = 0x2a50 := rfl
    have hsp2 : s2.sp = s0.sp - 0x2a50#64 := hi2.base.sp
    have hle : (0x2a50#64 : BitVec 64) ≤ s0.sp := by
      rw [BitVec.le_def]; change 0x2a50 ≤ s0.sp.toNat; omega
    rw [hsp2, BitVec.toNat_sub_of_le hle, hrf_eq]
    change resStack - 0x2a50 ≤ s0.sp.toNat - 0x2a50; omega
  obtain ⟨hcoins63, hfs2, _hspk64, _hkpk64, _hkpk1568, hfilesOk, hinitOk, hga⟩ :=
    AtInit2.init_facts he hi2
  let fsp := runFsp s0
  let dirG : AddrGhost := ⟨⟨d2.dirCap, d2.dirPtr, d2.dir⟩, 0#8⟩
  have hstep_bl : SepWP (mProg img ext) ((mProg img ext).fnAddr wrapInitiateName) s2 emp
      (fun s3 P3 => (s3.sp = fsp ∧ s3.readReg64 .fp = s0.sp - 0x60#64 ∧
        s3.readReg64 .lr = runPc img ext 0x28f4 ∧
        calleeSavedVRegs s3 = calleeSavedVRegs s0 ∧ s3.trace = s2.trace ∧ s3.fs = s2.fs ∧
        s3.readReg64 .x0 = fsp + 0x2a0#64 ∧ s3.readReg64 .x1 = fsp + 0x320#64 ∧
        s3.readReg64 .x2 = g.stores + 0xf0#64 ∧ s3.readReg64 .x3 = sessVt img ∧
        s3.readReg64 .x4 = g.stores ∧ s3.readReg64 .x5 = idVt img ∧
        s3.readReg64 .x6 = fsp + 0x4d0#64 ∧ s3.readReg64 .x7 = 0#64 ∧
        s3.readReg64 .x8 = fsp + 0x23b0#64 ∧
        s3.readReg64 (.gpr 19#5) = g.stores ∧ s3.readReg64 (.gpr 20#5) = g.res ∧
        s3.readReg64 (.gpr 21#5) = d2.meG.name.cap) ∧ P3 = emp)
      (fun _ => ⌜False⌝) := by
    have hpc := hi2.base.pc; have hrun := hi2.base.run; have hsp := hi2.base.sp
    have hfp := hi2.base.fp; have hv := hi2.base.vregs
    have hx0 := hi2.x0; have hx1 := hi2.x1; have hx2 := hi2.x2; have hx3 := hi2.x3
    have hx4 := hi2.x4; have hx5 := hi2.x5; have hx6 := hi2.x6; have hx7 := hi2.x7
    have hx8 := hi2.x8; have hx19 := hi2.x19; have hx20 := hi2.x20; have hx21 := hi2.x21
    have hfn0 := r1c_run_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
      (Rust.withPanics ext) hfn0 (num% (ls_off% "libsignal_cli::run")) 10480 4
    clear hfn0
    dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
    generalize hfn :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
    examples_hide_fetches
    wp_steps
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm, ← hfn, Program.fnAddr_rebase, r1c_run_fnOff, r1c_init_fnOff])
      (by simp only [wp_norm, arm64_norm, *])
    refine ⟨?_, rfl⟩
    r1c_close_post
  refine r1c_frame_seq (F := init2Mem A img g d2 s0 resStack)
    hi2.base.inv (Entails.of_eq (emp_sepConj _).symm) hstep_bl
    fun s3 hinv3 hpc3 hrun3 ⟨hsp3, hfp3, hlr3, hv3, htr3, hfs3,
      hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx5_3, hx6_3, hx7_3, hx8_3,
      hx19_3, hx20_3, hx21_3⟩ => ?_
  rw [emp_sepConj]
  let initX : InitGhost :=
    { peer := d2.peerG
      peerA := fsp + 0x2a0#64
      me := d2.meG
      meA := fsp + 0x320#64
      stores := g.stores
      ret := fsp + 0x23b0#64
      coinsP := g.coins
      F := runFiles g.i
      coins := MainHops.coinsOf g.i
      bundleA := fsp + 0x4d0#64
      bundle := d2.bundle
      spkSigPtr := d2.spkSigPtr
      kpkSigPtr := d2.kpkSigPtr
      kpkPtr := d2.kpkPtr }
  let lowPre := memRegion (fsp + 4#64) (0x110 - 4) ∗
    ((fsp + 0x110#64) ↦₆₄ d2.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
    ((fsp + 0x138#64) ↦₆₄ d2.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
    ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d2.kpkPtr) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d2.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d2.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d2.dirPtr) ∗
    memRegion (fsp + 0x118#64) 8 ∗ memRegion (fsp + 0x128#64) 16 ∗
    memRegion (fsp + 0x148#64) 16 ∗ memRegion (fsp + 0x160#64) 24 ∗
    memRegion (fsp + 0x180#64) 56
  let hiGaps := memRegion (fsp + 0x2c0#64) (0x320 - 0x2c0) ∗
    memRegion (fsp + 0x340#64) (0x4d0 - 0x340) ∗
    memRegion (fsp + 0x590#64) (0x23b0 - 0x590)
  let initFrame := memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
    A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
    ownedBytes A d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
    lowPre ∗ memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
    hiGaps ∗ memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0)
  have htr_s3 : s0.trace <+: s3.trace := htr3 ▸ hi2.trace
  have hspb_s3 : resStack - runFrame ≤ s3.sp.toNat := by
    rw [hsp3]; dsimp only [fsp]; rwa [← hi2.base.sp]
  have hfs_s3 : s3.fs.files = runFiles g.i := (congrArg FsState.files hfs3).trans hfs2
  refine r1c_call_raw (s0 := s0) (F := initFrame) initX
    (hc.initiate (resStack - runFrame) hinit_stk hsub63)
    hinv3 hpc3 hrun3 (r1c_spAligned hi2.base.spAligned hsp3) hlr3
    (by
      dsimp only [init2Mem, slotsOf, mkSlot, initSlotSpec, Spec.inImage, slotFrame, initX]
      refine Entails.trans
        (r1c_rewrite_front
          (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
            storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
            coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
            CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗
            A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
            ownedBytes A d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
            runSaved s0 ∗ stackAt fsp (resStack - runFrame) ∗ A.pool)
          (r1c_init2Locals_unpack A fsp d2)
          (by ac_rfl) (by rfl)) ?_
      simp only [sepConj_assoc]
      apply Entails.pure_right hinv3
      apply Entails.pure_right
        ⟨hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx5_3, hx6_3, hx7_3, hx8_3,
         hfs_s3, hfilesOk, hinitOk, hspb_s3⟩
      apply Entails.pure_right hcoins63
      rw [hsp3]
      exact Entails.of_eq (by dsimp only [initFrame, lowPre, hiGaps]; ac_rfl))
    (hpanic := fun sf R' _ hp => by
      dsimp only [slotsOf, mkSlot, initSlotSpec, Spec.inImage, initX] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      rcases hp.1 with hnone | halloc
      · exact hpanic sf _ (Or.inl (by rw [hga, hnone]; rfl))
      · exact hpanic sf _ (Or.inr (allocFailedIn_of_prefix htr_s3 halloc)))
    (hoom := fun _ _ _ ho => by
      dsimp only [slotsOf, mkSlot, initSlotSpec, Spec.inImage, initX] at ho
      exact (not_satisfies_false_sepConj ho).elim)
    (hnext := fun sm _ hinv_m hpcm hrunm hspm hcsm => ?_)
  rcases hcsm with ⟨hx19_m, hx20_m, hx21_m, _, _, _, _, _, _, _, hfp_m, hv_m⟩
  dsimp only [slotsOf, mkSlot, initSlotSpec, Spec.inImage, initX]
  simp only [sepExists_sepConj_left]
  apply r1c_sepWPp_exists_left; intro g'
  apply r1c_sepWPp_exists_left; intro e
  rw [sepConj_assoc]
  apply r1c_sepWPp_pure_left; rintro ⟨hslotTr, hslotOut⟩
  rw [hsp3]
  have hsp_m : sm.sp = fsp := hspm.trans hsp3
  have hs_m : InRun img ext s0 sm 0x28f4 :=
    ⟨hpcm, hrunm, hsp_m, hfp_m.trans hfp3, hinv_m, hv_m.trans hv3, hi2.base.spAligned⟩
  have hx19_m' : sm.readReg64 (.gpr 19#5) = g.stores := hx19_m.trans hx19_3
  have hx20_m' : sm.readReg64 (.gpr 20#5) = g.res := hx20_m.trans hx20_3
  have hx21_m' : sm.readReg64 (.gpr 21#5) = d2.meG.name.cap := hx21_m.trans hx21_3
  have htr_m : s0.trace <+: sm.trace := htr_s3.trans hslotTr.1
  have hhist_m : RunHistOk g.i s0 sm :=
    ⟨hslotTr.2.1.trans hfs_s3, hslotTr.2.2.trans (htr3 ▸ hi2.stdout)⟩
  have hcollapse_post :
      protocolAddressAt A d2.peerG (fsp + 0x2a0#64) ∗
        protocolAddressAt A d2.meG (fsp + 0x320#64) ∗
        cliBundleAt (fsp + 0x4d0#64) d2.bundle d2.spkSigPtr d2.kpkSigPtr d2.kpkPtr ∗
        (fsp ↦₃₂ 0#32) ∗ logOff img ∗ anyHeap ∗ initFrame ⊢
      (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
        (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
        (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
        addrNameHeap A d2.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d2.peerG ∗
        r1c_lowCells fsp d2 ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗
        (memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗ anyHeap) := by
    have hlow : (fsp ↦₃₂ 0#32) ∗ lowPre ⊢ r1c_lowCells fsp d2 := by
      have hm110 : (fsp ↦₃₂ 0#32) ∗ memRegion (fsp + 4#64) (0x110 - 4) ⊢ memRegion fsp 0x110 := by
        rw [ProofLib.memRegion_split' (b := fsp) (n := 4) (k := 0x110 - 4)
              (b' := fsp + 4#64) rfl rfl (by decide)]
        exact sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion fsp 0#32)
      dsimp only [lowPre, r1c_lowCells, r1c_lowGaps]
      exact r1c_rewrite_front
        (((fsp + 0x110#64) ↦₆₄ d2.spkSigPtr) ∗ ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x138#64) ↦₆₄ d2.kpkSigPtr) ∗ ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
          ((fsp + 0x158#64) ↦₆₄ 64#64) ∗ ((fsp + 0x178#64) ↦₆₄ d2.kpkPtr) ∗
          ((fsp + 0x1b8#64) ↦₆₄ d2.meG.name.ptr) ∗
          ((fsp + 0x1c0#64) ↦₆₄ d2.dirCap) ∗ ((fsp + 0x1c8#64) ↦₆₄ d2.dirPtr) ∗
          memRegion (fsp + 0x118#64) 8 ∗ memRegion (fsp + 0x128#64) 16 ∗
          memRegion (fsp + 0x148#64) 16 ∗ memRegion (fsp + 0x160#64) 24 ∗
          memRegion (fsp + 0x180#64) 56)
        hm110 (by ac_rfl) (by ac_rfl)
    have hhi : memRegion (fsp + 0x320#64) 32 ∗ memRegion (fsp + 0x4d0#64) 192 ∗ hiGaps ⊢
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) := by
      dsimp only [hiGaps]
      rw [ProofLib.memRegion_split' (b := fsp + 0x2c0#64) (n := 0x320 - 0x2c0)
            (k := 0x23b0 - 0x320) (b' := fsp + 0x320#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x320#64) (n := 32)
            (k := 0x23b0 - 0x340) (b' := fsp + 0x340#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x340#64) (n := 0x4d0 - 0x340)
            (k := 0x23b0 - 0x4d0) (b' := fsp + 0x4d0#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 0x4d0#64) (n := 192)
            (k := 0x23b0 - 0x590) (b' := fsp + 0x590#64) rfl (by bv_omega) (by decide)]
      exact Entails.of_eq (by ac_rfl)
    have hdir : ownedBytes A d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ⊢
        addrNameHeap A dirG := by
      refine Entails.trans
        (r1c_ownedBytes_entails_nameHeap A d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir) ?_
      exact Entails.pure_left fun _ => Entails.refl _
    have hpeer : protocolAddressAt A d2.peerG (fsp + 0x2a0#64) ⊢
        (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A d2.peerG := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using r1c_addr_unpack A d2.peerG (fsp + 0x2a0#64)
    have hany : logOff img ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
    dsimp only [initFrame]
    refine Entails.trans
      (sepConj_mono hpeer
        (sepConj_mono (r1c_addr_to_mem32 A d2.meG (fsp + 0x320#64))
          (sepConj_mono (r1c_cliBundleAt_unpack (fsp + 0x4d0#64) d2.bundle d2.spkSigPtr d2.kpkSigPtr d2.kpkPtr)
            (Entails.refl _)))) ?_
    refine Entails.trans
      (r1c_rewrite_front
        ((((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
            memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A d2.peerG ∗
          memRegion (fsp + 0x320#64) 32 ∗ addrNameHeap A d2.meG ∗
          memRegion (fsp + 0x4d0#64) 192 ∗
          memRegion d2.spkSigPtr 64 ∗ memRegion d2.kpkSigPtr 64 ∗ memRegion d2.kpkPtr 1568 ∗
          logOff img ∗ anyHeap ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
          ownedBytes A d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
          memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
          hiGaps ∗ memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
        hlow (by ac_rfl) (by rfl)) ?_
    refine Entails.trans
      (r1c_rewrite_front
        (r1c_lowCells fsp d2 ∗
          (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
            memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A d2.peerG ∗
          addrNameHeap A d2.meG ∗
          memRegion d2.spkSigPtr 64 ∗ memRegion d2.kpkSigPtr 64 ∗ memRegion d2.kpkPtr 1568 ∗
          logOff img ∗ anyHeap ∗
          memRegion g.res runResSize ∗ memRegion g.call 56 ∗
          (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
          A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
          ownedBytes A d2.dirCap d2.dirPtr (BitVec.ofNat 64 d2.dir.length) d2.dir ∗
          memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
          memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
        hhi (by ac_rfl) (by rfl)) ?_
    exact r1c_rewrite_front
      (memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        r1c_lowCells fsp d2 ∗
        (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
          memRegion (fsp + 0x2b0#64) 16) ∗ addrNameHeap A d2.peerG ∗
        addrNameHeap A d2.meG ∗
        memRegion d2.spkSigPtr 64 ∗ memRegion d2.kpkSigPtr 64 ∗ memRegion d2.kpkPtr 1568 ∗
        memRegion g.res runResSize ∗ memRegion g.call 56 ∗
        (g.inp ↦ₛ inputOf g.i g.c) ∗ runSaved s0 ∗
        A.live d2.spkSigPtr 64 1 ∗ A.live d2.kpkSigPtr 64 1 ∗ A.live d2.kpkPtr 1568 1 ∗
        memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
      (sepConj_mono hdir hany) (by ac_rfl) (by ac_rfl)
  apply r1c_sepWPp_weaken_pre
    (r1c_rewrite_front
      (storesAt A g.stores g' ∗ initResAt A (fsp + 0x23b0#64) e ∗ A.pool ∗
        stackAt fsp (resStack - runFrame))
      hcollapse_post (by ac_rfl) (by rfl))
  cases e with
  | ok u =>
    cases u
    rcases hslotOut with ⟨_, _, hans_ok, hwr⟩
    have hans : g.a = some (some (namedWrites g'.writes, [])) := by
      rw [hga, hans_ok]; rfl
    dsimp only [initResAt]
    have hcmn3_ok : ((0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 3#64 == 0#64) = false := by decide
    have hcmn2_ne_ok : ((0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 2#64 != 0#64) = false := by decide
    have hcmn2_eq_ok : ((0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 2#64 == 0#64) = true := by decide
    have hstep_ok : SepWP (mProg img ext) (runPc img ext 0x2908) sm
        ((fsp + 0x23b0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64)
        (fun s4 P4 => (s4.sp = fsp ∧ s4.readReg64 .fp = s0.sp - 0x60#64 ∧
          calleeSavedVRegs s4 = calleeSavedVRegs s0 ∧ s4.trace = sm.trace ∧ s4.fs = sm.fs ∧
          s4.readReg64 (.gpr 19#5) = g.stores ∧ s4.readReg64 (.gpr 20#5) = g.res ∧
          s4.readReg64 (.gpr 21#5) = d2.meG.name.cap) ∧
          P4 = ((fsp + 0x23b0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64))
        (fun _ => ⌜False⌝) := by
      have hpc := hs_m.pc; have hrun := hs_m.run; have hfp := hs_m.fp; have hv := hs_m.vregs
      have hal : sm.spAligned = true := r1c_spAligned hi2.base.spAligned hsp_m
      have hfn := r1c_run_fnOff
      code_fetches_range CryptoVerification.libsignalSessionCode r1c_dec_main img.base
        (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_cli::run")) 10484 20
      clear hfn
      dsimp only [mProg, runPc, tripleRatchetProgAtExt] at hpc ⊢
      generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase at *
      examples_hide_fetches; rw [show fsp = sm.sp from hsp_m.symm]; wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine ⟨?_, rfl⟩; r1c_close_post
    let okRest := (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
      (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
      (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
      addrNameHeap A d2.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d2.peerG ∗
      r1c_lowCells fsp d2 ∗
      memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
      (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0
    refine r1c_frame_seq
      (F := memRegion (fsp + 0x23b0#64 + 8#64) 40 ∗
        memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
        memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗ okRest)
      hs_m.inv (Entails.of_eq (by dsimp only [okRest, r1c_okCore]; ac_rfl)) hstep_ok
      fun s4 hinv4 hpc4 hrun4 ⟨hsp4, hfp4, hv4, htr4, hfs4, hx19_4, hx20_4, hx21_4⟩ => ?_
    have hmerge_ok :
        ((fsp + 0x23b0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          memRegion (fsp + 0x23b0#64 + 8#64) 40 ∗
          memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
          memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ⊢
        memRegion (fsp + 0x2c0#64) (runLocalBytes - 0x2c0) := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [r1c_split_at fsp 0x2c0 (0x23b0 - 0x2c0) runLocalBytes (by decide) (by decide),
          r1c_split_at fsp 0x23b0 8 runLocalBytes (by decide) (by decide),
          r1c_split_at fsp 0x23b8 40 runLocalBytes (by decide) (by decide)]
      exact r1c_rewrite_front
        (memRegion (fsp + 0x23b8#64) 40 ∗
          memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
          memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0))
        (pointsTo64_entails_memRegion _ _) (by ac_rfl) (by ac_rfl)
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_ok_tail (d := d2) hh hext_le hsub64 ⟨hpc4, hrun4, hsp4, hfp4, hinv4, hv4, hi2.base.spAligned⟩
        hx19_4 hx20_4 hx21_4 (htr4 ▸ htr_m)
        (r1c_hist_of_eq htr4 (congrArg FsState.files hfs4) hhist_m)
        hans hwr hjoin)
    exact r1c_rewrite_front okRest hmerge_ok (by ac_rfl) (by dsimp only [okRest, fsp, dirG]; ac_rfl)
  | error err =>
    have hans : g.a = some none := by
      rw [hga, hslotOut.2.2]; rfl
    dsimp only [initResAt]
    let errRest := (A.live d2.spkSigPtr 64 1 ∗ memRegion d2.spkSigPtr 64) ∗
      (A.live d2.kpkPtr 1568 1 ∗ memRegion d2.kpkPtr 1568) ∗
      (A.live d2.kpkSigPtr 64 1 ∗ memRegion d2.kpkSigPtr 64) ∗
      addrNameHeap A d2.meG ∗ addrNameHeap A dirG ∗ addrNameHeap A d2.peerG ∗
      r1c_lowCells fsp d2 ∗
      memRegion (fsp + 0x1d0#64) (0x2a0 - 0x1d0) ∗
      (((fsp + 0x2a0#64) ↦₆₄ d2.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d2.peerG.name.ptr) ∗
        memRegion (fsp + 0x2b0#64) 16) ∗
      memRegion (fsp + 0x2c0#64) (0x23b0 - 0x2c0) ∗
      memRegion (fsp + 0x23e0#64) (runLocalBytes - 0x23e0) ∗
      stackAt fsp (resStack - runFrame) ∗ A.pool ∗ r1c_okCore A g g' s0
    apply r1c_sepWPp_weaken_pre
      (P' := (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (fsp + 0x23b0#64) k) ∗ errRest)
      (Entails.of_eq (by dsimp only [errRest, r1c_okCore]; ac_rfl))
    simp only [sepExists_sepConj_left]
    apply r1c_sepWPp_exists_left; intro k
    refine r1c_sepWPp_weaken_pre ?_
      (r1c_err_tail (g' := g') (d := d2) (k := k) hh hdrop hstk32 hext_le hsub64 hs_m hx19_m' hx20_m' hx21_m'
        htr_m hhist_m hans hrej)
    exact Entails.of_eq (by dsimp only [errRest, fsp, dirG])

theorem run_hop_init3_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {g : RunCall} {d2 : Init2Data}
    {s0 s2 : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (hspb : resStack ≤ s0.sp.toNat)
    (he : AtRunEntry S img ext g s0)
    (hi2 : AtInit2 img ext g d2 s0 s2)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectK img ext A g s0 resStack Q Qp)
    (hjoin : JoinK img ext A g s0 resStack Q Qp) :
    ProofLib.SepWPp (mProg img ext) (s0.readReg64 .lr) s2
      (init2Mem A img g d2 s0 resStack) Q Qp (runOom s0) :=
  run_hop_init3_ok_ext himg hh.toExt hc hdrop hres hres64 hspb he hi2 hpanic hrej hjoin

end

end CryptoVerification.SignalSession.Cli.RunCompose


