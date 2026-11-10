/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.PrologueB
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTail
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.OkBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# `PreKeySignalMessage::try_from`: Top-Level Entry-to-Return Assembly (`preKeyTryFrom_ok_of_postLoop`)

Defines `pksmTryFromSpec` and `PreKeyPostLoopOkW`, and composes the early-error path
(`+0x000 → +0x504 → ret`), the protobuf decode loop (`+0x000 → +0x460`), the loop-error
cleanup (`+0x460 → +0x504 → ret`), and `PreKeyPostLoopOkW` (`+0x460 → ret`) into
`preKeyTryFrom_ok_of_postLoop`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

/-! ## 1. All-Inputs Spec (`pksmTryFromSpec`) and `SepWPp` Post Combinators -/

/-- All-inputs `Spec RunCompose.PksmGhost` for `PreKeySignalMessage::try_from`, matching
`RunCompose.pksmSlotSpec A img S` when `S.pksmParse = Pksm.pksmParse` (`< 2 ^ 32`). -/
def pksmTryFromSpec (A : RustAlloc) (img : Obj.Image) : Spec RunCompose.PksmGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ptr ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret ∧
          preKeyTryFromStack ≤ s.sp.toNat⌝ ∗
        (x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ logOff img ∗
        stackAt s.sp preKeyTryFromStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          RunCompose.pksmResAt A x.ret (Pksm.pksmParse x.bytes) ∗
          (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗
          stackAt s0.sp preKeyTryFromStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Top-level `subroutine_ok` statement for `PreKeySignalMessage::try_from` on
`contractProg img.base ext` against `pksmTryFromSpec A img`. -/
def PreKeyTryFromOk (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr preKeyTryFromName)
    (pksmTryFromSpec A img)

/-- Rewrites `pksmTryFromSpec A img` to `RunCompose.pksmSlotSpec A img S` whenever `S.pksmParse`
agrees with `Pksm.pksmParse`. -/
theorem pksmSlotSpec_eq_pksmTryFromSpec (A : RustAlloc) (img : Obj.Image) (S : RunCompose.RunSem)
    (hS : ∀ b, S.pksmParse b = Pksm.pksmParse b) :
    RunCompose.pksmSlotSpec A img S = pksmTryFromSpec A img := by
  have hfun : S.pksmParse = Pksm.pksmParse := funext hS
  unfold RunCompose.pksmSlotSpec pksmTryFromSpec
  rw [hfun]

/-- Bridges `PreKeyTryFromOk` to `subroutine_ok ... (RunCompose.pksmSlotSpec A img S)`. -/
theorem pksmSlotSpec_of_preKeyTryFromOk {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunCompose.RunSem}
    (hS : ∀ b, S.pksmParse b = Pksm.pksmParse b)
    (hok : PreKeyTryFromOk img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName)
      (RunCompose.pksmSlotSpec A img S) := by
  rw [pksmSlotSpec_eq_pksmTryFromSpec A img S hS]
  exact hok

theorem SepWPp.mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp)
    (hQ : ∀ sf Pf, sf.pc = ret → sf.status = .Running → Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc, hrun, Pf, hmf, hq, hv⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, Pf, hmf, hQ sf Pf hpc hrun hq, hv⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

/-- The Err tail post (`sp`, callee-saved, trace, `pksmErrE A fn x.ret e ∗ R`) meets
`(pksmTryFromSpec A img).post` whenever `Pksm.pksmParse x.bytes = none`. -/
theorem w8b_errPost {img : Obj.Image} {A : RustAlloc} {x : RunCompose.PksmGhost} {s0 sf : State}
    {Pf R : SepProp} {fn : List (BitVec 8)} {e : SignalProtocolError}
    (hparse : Pksm.pksmParse x.bytes = none)
    (h : sf.sp = s0.sp ∧
      (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      sf.trace = s0.trace ∧
      (Pf ⊢ (pksmErrE A fn x.ret e ∗ R) ∗ (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗ A.pool ∗
        stackAt s0.sp preKeyTryFromStack)) :
    sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf) := by
  obtain ⟨hsp, hcs, htr, hent⟩ := h
  refine ⟨hsp, hcs, Entails.trans hent ?_⟩
  dsimp only [pksmTryFromSpec, Spec.inImage]
  refine Entails.trans
    (sepConj_mono_left (pksmResAt_err_of_parse A fn x.ret x.bytes e R hparse)) ?_
  rw [pure_sepConj_of_true htr]
  apply entails_of_eq; ac_rfl

/-- `w8b_errPost` specialized to heap-free error payloads (`Pf ⊢ pksmErrE A fn x.ret e ∗ ...`). -/
theorem w8b_errPost_noHeap {img : Obj.Image} {A : RustAlloc} {x : RunCompose.PksmGhost}
    {s0 sf : State} {Pf : SepProp} {fn : List (BitVec 8)} {e : SignalProtocolError}
    (hparse : Pksm.pksmParse x.bytes = none)
    (h : sf.sp = s0.sp ∧
      (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      sf.trace = s0.trace ∧
      (Pf ⊢ pksmErrE A fn x.ret e ∗ (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗ A.pool ∗
        stackAt s0.sp preKeyTryFromStack)) :
    sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf) := by
  obtain ⟨hsp, hcs, htr, hent⟩ := h
  refine ⟨hsp, hcs, Entails.trans hent ?_⟩
  dsimp only [pksmTryFromSpec, Spec.inImage]
  have herr : pksmErrE A fn x.ret e ⊢ RunCompose.pksmResAt A x.ret (Pksm.pksmParse x.bytes) := by
    simpa [sepConj_emp] using pksmResAt_err_of_parse A fn x.ret x.bytes e emp hparse
  refine Entails.trans (sepConj_mono_left herr) ?_
  rw [pure_sepConj_of_true htr]
  apply entails_of_eq; ac_rfl

/-! ## 2. Post-loop interface (`+0x460`, decode Ok) -/

/-- Post-loop `Ok` continuation `+0x460 → ret` (`1120 → ret`): from the
loop exit with `x24 = 0` and the decoded `m` of the body `b1 :: bs1` (version byte `vb` in the
accepted window), the function returns with `pksmTryFromSpec`'s post.-/
def PreKeyPostLoopOkW (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) :
    Prop :=
  ∀ (x : RunCompose.PksmGhost) (s0 s : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage),
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    Pksm.decodeProto (b1 :: bs1) = some m →
    PreKeyLoopExitState img s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr vb s →
    s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1120#64 →
    s.status = .Running →
    s.readReg64 .x24 = 0#64 →
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) s
      (wirePreKeyOf A (s0.sp - 608#64 + 312#64) m ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗
        A.pool ∗ stackAt (s0.sp - 608#64) preKeyTryFromSubStack)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf))
      (tryFromQp s0)

/-- Loop-exit glue: `preKey_valid_to_460_wpW`'s post (+ the frame kept across `+0x000 → +0x460`)
regroups into the shape both `+0x460` continuations consume. -/
theorem w8b_loopExit_regroup (A : RustAlloc) (img : Obj.Image) (x : RunCompose.PksmGhost)
    (s0 : State) (vb b1 : BitVec 8) (bs1 : List (BitVec 8)) (x24 : BitVec 64)
    (res : Option ProtoPreKeySignalMessage) (hcons : x.bytes = vb :: b1 :: bs1) :
    ((x.ptr ↦₈ vb) ∗
        preKeyLoopExitMem A (s0.sp - 608#64) (x.ptr + 1#64) (b1 :: bs1) x24 res ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0) ∗
      (memRegion x.ret 248 ∗ logOff img ∗ memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 - BitVec.ofNat 64 preKeyTryFromSubStack)
          (preKeyTryFromSubStack - Prost.skipFieldStackX 100)) ⊢
      (match res with
        | some m' => ⌜x24 = 0#64⌝ ∗ wirePreKeyOf A (s0.sp - 608#64 + 312#64) m'
        | none =>
          ⌜x24 ≠ 0#64⌝ ∗ decodeErrorAt A x24 ∗
            (∃∗ mErr, wirePreKeyOf A (s0.sp - 608#64 + 312#64) mErr)) ∗
      (memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗
        A.pool ∗ stackAt (s0.sp - 608#64) preKeyTryFromSubStack) := by
  have h440 := pointsTo64_entails_memRegion (s0.sp - 608#64 + 440#64) (s0.sp - 608#64 + 296#64)
  unfold preKeyLoopExitMem
  rw [hcons, stackAt_preKeyTryFromSubStack_skipField (s0.sp - 608#64)]
  simp only [pointsToBytes_cons]
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left h440))))
  apply entails_of_eq; ac_rfl

/-! ## 3. Entry → return -/

/-- `try_from` from `+0x000` to the return address (`s0.x30`), every input (`< 2 ^ 32`). -/
theorem preKey_entry_to_ret_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc : AllocHooksW img A ext)
    (hDropErr : Prost.DropDecodeErrorOkExtX img A ext)
    (hLoopF4 : PreKeyDecodeLoopF4OkW img A ext)
    (hPost : PreKeyPostLoopOkW img A ext)
    {x : RunCompose.PksmGhost} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (contractProg img.base ext).fnAddr preKeyTryFromName)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (contractProg img.base ext) (s0.readReg64 .x30) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ logOff img ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf))
      (tryFromQp s0) := by
  have hsplit : stackAt s0.sp preKeyTryFromStack =
      stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗ memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗ memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96 :=
    stackAt_preKeyTryFrom_split s0.sp
  rw [hsplit]
  by_cases hvalid : ∃ vb b1 bs1, x.bytes = vb :: b1 :: bs1 ∧
      ¬ (vb >>> 4) < 3#8 ∧ ¬ 4#8 < (vb >>> 4)
  · -- valid version byte, non-empty body: `+0x000 → +0x460`, then split on `Pksm.decodeProto`
    obtain ⟨vb, b1, bs1, hcons, hge3, hle4⟩ := hvalid
    rw [stackAt_preKeyTryFromSubStack_skipField (s0.sp - 608#64)]
    refine SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗
          memRegion (s0.sp - 608#64 + 296#64) 152 ∗
          memRegion (s0.sp - 608#64 + 448#64) 64 ∗
          memRegion (s0.sp - 608#64 + 512#64) 96 ∗
          A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100)) ∗
        (memRegion x.ret 248 ∗ logOff img ∗ memRegion (s0.sp - 608#64) 296 ∗
          memRegion (s0.sp - 608#64 - BitVec.ofNat 64 preKeyTryFromSubStack)
            (preKeyTryFromSubStack - Prost.skipFieldStackX 100)))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_tryFrom
      (preKey_valid_to_460_wpW hLoopF4 hcons hge3 hle4 hlt hpc hrun hsp hF hsym hx0 hx1 hx8) ?_
    intro s1 P1 hpc1 hrun1 ⟨hst1, hent1⟩
    refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
    clear hent1
    refine SepWPp.mono_pre
      (w8b_loopExit_regroup A img x s0 vb b1 bs1 (s1.readReg64 .x24)
        (Pksm.decodeProto (b1 :: bs1)) hcons) ?_
    cases hdec : Pksm.decodeProto (b1 :: bs1) with
    | none =>
      have hv_ok : 0x30#8 ≤ vb ∧ vb ≤ 0x4f#8 :=
        (pksmParse_ver_ok_iff vb).mp (not_or.mpr ⟨hge3, hle4⟩)
      have hparse : Pksm.pksmParse x.bytes = none := by
        rw [hcons]; exact pksmParse_decodeNone hv_ok hdec
      simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_pre fun mErr => ?_
      refine SepWPp.pure_pre fun hx24_ne => ?_
      refine SepWPp.mono_post
        (SepWPp.mono_pre (by apply entails_of_eq; ac_rfl)
          (preKey_loopErr_460_wpE (x := x) halloc hDropErr hst1 hpc1 hrun1 rfl hx24_ne mErr)) ?_
      intro sf Pf _ _ hq
      exact w8b_errPost hparse hq
    | some m =>
      simp only [sepConj_assoc]
      refine SepWPp.pure_pre fun hx24 => ?_
      exact hPost x s0 s1 vb b1 bs1 m hcons hge3 hle4 hlt hdec hst1 hpc1 hrun1 hx24
  · -- early Err: `+0x000 → +0x504 → ret`
    have herr : x.bytes = [] ∨ (∃ vb body, x.bytes = vb :: body ∧
        ((vb >>> 4) < 3#8 ∨ 4#8 < (vb >>> 4) ∨ body = [])) := by
      rcases hb : x.bytes with _ | ⟨vb, _ | ⟨b1, bs1⟩⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨vb, [], rfl, Or.inr (Or.inr rfl)⟩
      · refine Or.inr ⟨vb, b1 :: bs1, rfl, ?_⟩
        by_cases h3 : (vb >>> 4) < 3#8
        · exact Or.inl h3
        · by_cases h4 : 4#8 < (vb >>> 4)
          · exact Or.inr (Or.inl h4)
          · exact absurd ⟨vb, b1, bs1, hb, h3, h4⟩ hvalid
    refine SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗
          memRegion x.ret 248 ∗
          memRegion (s0.sp - 608#64) 296 ∗
          memRegion (s0.sp - 608#64 + 296#64) 152 ∗
          memRegion (s0.sp - 608#64 + 512#64) 96) ∗
        (stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
          memRegion (s0.sp - 608#64 + 448#64) 64 ∗ logOff img ∗ A.pool))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_tryFrom
      (preKey_earlyErr_to_504_wpE (A := A) herr hlt hpc hrun hsp hF hsym hx0 hx1 hx8) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hst1, hparse, e, hent1⟩
    refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
    clear hent1
    refine SepWPp.mono_post
      (SepWPp.mono_pre (by apply entails_of_eq; ac_rfl)
        (epilogue_504_wpX (A := A) (x := x) (R := pksmErrE A [] x.ret e) hst1 hpc1 hrun1)) ?_
    intro sf Pf _ _ hq
    exact w8b_errPost_noHeap hparse hq

/-! ## 4. Top-level subroutine theorem -/

/-- `PreKeyTryFromOk` (`subroutine_ok ... (pksmTryFromSpec A img)`) from the decode loop,
the post-loop Ok path, and the dealloc / `DecodeError` drop contracts (`< 2 ^ 32`). -/
theorem preKeyTryFrom_ok_of_postLoop {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc : AllocHooksW img A ext)
    (hDropErr : Prost.DropDecodeErrorOkExtX img A ext)
    (hLoopF4 : PreKeyDecodeLoopF4OkW img A ext)
    (hPost : PreKeyPostLoopOkW img A ext) :
    PreKeyTryFromOk img A ext := by
  unfold PreKeyTryFromOk
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [pksmTryFromSpec, Spec.inImage] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, ⟨hx0, hx1_nat, hlt, hx8, _hsp_ge⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ logOff img ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool) ∗ R := by
    ac_nf at hmem ⊢
  have hfull := preKey_entry_to_ret_wpX halloc hDropErr hLoopF4 hPost
    hlt hpc hrun hsp hF hsym hx0 hx1 hx8
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hvregs_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hvregs_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact Or.inr (Or.inl ⟨hpan, htr_f R hmf⟩)
  · exact (allowPanic_not_exited hoom).elim

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
