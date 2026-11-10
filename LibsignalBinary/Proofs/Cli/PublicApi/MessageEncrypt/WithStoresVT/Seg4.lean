/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEnc
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalFetch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalMem
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalOk
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg3
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalEnc
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalErr
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalFrame

/-!
# CLI MessageEncrypt `WithStoresVT` (Part 4): `h45_SegExitVT_trap` and `SegSignal` (`h45_segSignal_okVT_trap`) on `trTrapProgAt`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalSpqrV1 (TokenInit)
open CryptoVerification.Cli.LibsignalPublicApi (encryptWithStoresName)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-- Segment continuation wrapper for `withStoresEncSpecVT_trap`. -/
def h45_SegExitVT_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State))
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (next : State → Prop) : Prop :=
  (trTrapProgAt img.base C abs).CodeLoaded s.mem →
  ∃ sf, Steps (trTrapProgAt img.base C abs) s sf ∧
    (next sf ∨
      SubroutineOutcome (withStoresEncSpecVT_trap kit st0 ikit ist0 C ctl parse S encRecord)
        x R s0 sf)

theorem h45_segExitVT_of_segExit_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State}
    {next : State → Prop}
    (h : SegExit_trap kit st0 ikit ist0 C ctl parse S encRecord abs x (TokenInit img ∗ R) s0 s next) :
    h45_SegExitVT_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s next := by
  intro hL
  obtain ⟨sf, hst, hnext | hout⟩ := h hL
  · exact ⟨sf, hst, Or.inl hnext⟩
  · exact ⟨sf, hst, Or.inr (h45_subroutineOutcome_vt_of_v hout)⟩

theorem h45_segExitVT_trans_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {mid next : State → Prop}
    (h1 : h45_SegExitVT_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s mid)
    (h2 : ∀ sm, mid sm → h45_SegExitVT_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 sm next) :
    h45_SegExitVT_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s next := by
  intro hL
  obtain ⟨sm, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hst2, hnext⟩ := h2 sm hmid (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hnext⟩
  · exact ⟨sm, hst1, Or.inr hout⟩

theorem h45_segExitVT_of_false_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h : h45_SegExitVT_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s (fun _ => False)) :
    h45_SegExitVT_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s next := by
  intro hL
  obtain ⟨sf, hst, hfalse | hout⟩ := h hL
  · exact False.elim hfalse
  · exact ⟨sf, hst, Or.inr hout⟩

theorem h45_segExitVT_call_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    {α : Type} {entry : BitVec 64} {spec : Spec α} {F : SepProp}
    (hcal : subroutine_ok (trTrapProgAt img.base C abs) entry spec)
    (g : α)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hal : s.spAligned = true)
    (_hlr : s.readReg64 .x30 ≠ 0#64)
    (hpre : s.mem ⊨ spec.pre g s ∗ (F ∗ R))
    (hexit : ∀ sf code, sf.status = .Exited code → Steps (trTrapProgAt img.base C abs) s sf →
      (sf.mem ⊨ spec.onExit g code s sf ∗ (F ∗ R)) → False)
    (hpan : ∀ sf, sf.status = .Panicked → Steps (trTrapProgAt img.base C abs) s sf →
      (sf.mem ⊨ (spec.onPanic g s sf ∗ F) ∗ R) →
      (sf.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl parse S encRecord).onPanic x s0 sf ∗ R))
    (hok : ∀ sf, (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      Steps (trTrapProgAt img.base C abs) s sf →
      sf.pc = s.readReg64 .x30 → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      (sf.mem ⊨ (spec.post g s sf ∗ F) ∗ R) →
      h45_SegExitVT_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 sf next)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom g s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    h45_SegExitVT_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hout, _⟩ := hcal.no_fault_before_outcome g (F ∗ R) s hpc hrun hpre hal hL
  rcases hout with ⟨⟨hsf_pc, _, hsf_run⟩, ⟨hsf_sp, hcs⟩, hpost⟩ | ⟨hpan_st, honp⟩ | ⟨code, hex_st, honex⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost
    obtain ⟨sf', hsteps', hfin⟩ := hok sf hL hsteps hsf_pc hsf_run hsf_sp hcs hpost (hsteps.codeLoaded hL)
    exact ⟨sf', hsteps.trans hsteps', hfin⟩
  · rw [← sepConj_assoc] at honp
    exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_st, hpan sf hpan_st hsteps honp⟩))⟩
  · exact False.elim (hexit sf code hex_st hsteps honex)
  · exact False.elim (hoom sf _ _hoom_st _hoom_post)

section SegSignal

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem h45_segSignal_ack_to_enc_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State)
    (hs : Pf.SegSignal.SegSignalAckStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => Pf.SegSignal.SegSignalEncStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k
        R0 s0 s') := by
  obtain ⟨hcur, hsc, hfrom, hrem, hnone, hs_pc, ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, hx20, hx23, hx25, hx26, hx27, hx28, hpt, hrest, hloc, hnow, hstk, hm⟩ := hs
  set sp := s0.sp - 0xbe0#64 with hsp0
  change s.mem ⊨
    (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
    curScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    (memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
      memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8) ∗
    memRegion x.ret 248 ∗ encCommon A ctl img x 0 s0 ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) at hm
  unfold curScratch encSpillsAtV at hm
  have hscr : memRegion sp 0x50 =
      memRegion sp 0x38 ∗ memRegion (sp + 0x38#64) 8 ∗ memRegion (sp + 0x40#64) 8 ∗
        memRegion (sp + 0x48#64) 8 := by
    rw [segSignal_memRegion_cut sp (sp + 0x38#64) 0x50 0x38 0x18 rfl rfl (by decide),
      segSignal_memRegion_cut (sp + 0x38#64) (sp + 0x40#64) 0x18 8 0x10 (by bv_omega) rfl (by decide),
      segSignal_memRegion_cut (sp + 0x40#64) (sp + 0x48#64) 0x10 8 8 (by bv_omega) rfl (by decide)]
  have h584 : memRegion (sp + 0x584#64) 84 =
      memRegion (sp + 0x584#64) 4 ∗ memRegion (sp + 0x588#64) 8 ∗ memRegion (sp + 0x590#64) 8 ∗
        memRegion (sp + 0x598#64) 4 ∗ memRegion (sp + 0x59c#64) 8 ∗
        memRegion (sp + 0x5a4#64) 8 ∗ memRegion (sp + 0x5ac#64) 8 ∗
        memRegion (sp + 0x5b4#64) 8 ∗ memRegion (sp + 0x5bc#64) 4 ∗
        memRegion (sp + 0x5c0#64) 24 := by
    rw [show (84 : Nat) = 4 + (8 + (8 + (4 + (8 + (8 + (8 + (8 + (4 + 24)))))))) from rfl,
      show sp + 0x584#64 = sp + BitVec.ofNat 64 0x584 from rfl,
      mr_cut_add sp 0x584 4 _ (by decide),
      mr_cut_add sp (0x584 + 4) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  have h5d8 : memRegion (sp + 0x5d8#64) 0x5a8 =
      memRegion (sp + 0x5d8#64) 32 ∗ memRegion (sp + 0x5f8#64) 0x278 ∗
        memRegion (sp + 0x870#64) 8 ∗ memRegion (sp + 0x878#64) 8 ∗
        memRegion (sp + 0x880#64) 8 ∗ memRegion (sp + 0x888#64) 8 ∗
        memRegion (sp + 0x890#64) 4 ∗ memRegion (sp + 0x894#64) 0x2ec := by
    rw [show (0x5a8 : Nat) = 32 + (0x278 + (8 + (8 + (8 + (8 + (4 + 0x2ec)))))) from rfl,
      show sp + 0x5d8#64 = sp + BitVec.ofNat 64 0x5d8 from rfl,
      mr_cut_add sp 0x5d8 32 _ (by decide),
      mr_cut_add sp (0x5d8 + 32) 0x278 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  rw [hscr, h584, h5d8] at hm
  obtain ⟨u38, hm⟩ := segSignal_peel8 (sp + 0x38#64) (by sep_focus) hm
  obtain ⟨u40, hm⟩ := segSignal_peel8 (sp + 0x40#64) (by sep_focus) hm
  obtain ⟨u48, hm⟩ := segSignal_peel8 (sp + 0x48#64) (by sep_focus) hm
  obtain ⟨a0, hm⟩ := segSignal_peel4 (sp + 0x584#64) (by sep_focus) hm
  obtain ⟨a1, hm⟩ := segSignal_peel8 (sp + 0x588#64) (by sep_focus) hm
  obtain ⟨a2, hm⟩ := segSignal_peel8 (sp + 0x590#64) (by sep_focus) hm
  obtain ⟨a3, hm⟩ := segSignal_peel4 (sp + 0x598#64) (by sep_focus) hm
  obtain ⟨c0, hm⟩ := segSignal_peel8 (sp + 0x59c#64) (by sep_focus) hm
  obtain ⟨c1, hm⟩ := segSignal_peel8 (sp + 0x5a4#64) (by sep_focus) hm
  obtain ⟨c2, hm⟩ := segSignal_peel8 (sp + 0x5ac#64) (by sep_focus) hm
  obtain ⟨c3, hm⟩ := segSignal_peel8 (sp + 0x5b4#64) (by sep_focus) hm
  obtain ⟨c4, hm⟩ := segSignal_peel4 (sp + 0x5bc#64) (by sep_focus) hm
  obtain ⟨e0, hm⟩ := segSignal_peel8 (sp + 0x870#64) (by sep_focus) hm
  obtain ⟨e1, hm⟩ := segSignal_peel8 (sp + 0x878#64) (by sep_focus) hm
  obtain ⟨e2, hm⟩ := segSignal_peel8 (sp + 0x880#64) (by sep_focus) hm
  obtain ⟨e3, hm⟩ := segSignal_peel8 (sp + 0x888#64) (by sep_focus) hm
  obtain ⟨e4, hm⟩ := segSignal_peel4 (sp + 0x890#64) (by sep_focus) hm
  have hentry : encEntry img = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) hEnv.loads encryptWithStoresName
  have hs_pc' : s.pc = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 0x348#64 := by
    rw [hs_pc, hentry]
  have hm4 := segSignal_focusR' (T := ((sp + 0x38#64) ↦₆₄ u38) ∗ ((sp + 0x40#64) ↦₆₄ u40) ∗
        ((sp + 0x48#64) ↦₆₄ u48) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
        ((sp + 0x580#64) ↦₃₂ 2#32) ∗ ((sp + 0x584#64) ↦₃₂ a0) ∗ ((sp + 0x588#64) ↦₆₄ a1) ∗
        ((sp + 0x590#64) ↦₆₄ a2) ∗ ((sp + 0x598#64) ↦₃₂ a3) ∗ ((sp + 0x59c#64) ↦₆₄ c0) ∗
        ((sp + 0x5a4#64) ↦₆₄ c1) ∗ ((sp + 0x5ac#64) ↦₆₄ c2) ∗ ((sp + 0x5b4#64) ↦₆₄ c3) ∗
        ((sp + 0x5bc#64) ↦₃₂ c4) ∗
        ((sp + 0x870#64) ↦₆₄ e0) ∗ ((sp + 0x878#64) ↦₆₄ e1) ∗ ((sp + 0x880#64) ↦₆₄ e2) ∗
        ((sp + 0x888#64) ↦₆₄ e3) ∗ ((sp + 0x890#64) ↦₃₂ e4))
    (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) (by sep_focus) (by sep_focus) hm
  refine Pf.SegFrom.SegExit.of_sepWP_trap hm4 (Pf.SegSignal.segSignal_step_enc_trap hs_pc' hrun hsp hal hx23 hx25 hx27) ?_
  intro s3 Pm3 hL hsteps hs3_pc hs3_run hm5
    ⟨hs3_sp, hs3_tr, hx0, hx1, hx2, hx3, hx4, hx5, hs3_x19, hs3_x20, hs3_x25, hs3_x26, hs3_x28,
      hs3_x29, hs3_vregs, hlr, hPm3⟩
  have ⟨hfl3, hsym3⟩ := SegFrom.callInv_steps hfl hsym hsteps hL
  have hs3_al : s3.spAligned = true := SegFrom.spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  have hPost := Entails.trans hPm3
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _) (sepConj_mono
    (pointsTo32_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo32_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (pointsTo32_entails_memRegion _ _)))))))))))))))))))))
  have hm7 := Satisfies.mono (sepConj_mono_left hPost) hm5
  refine Pf.SegFrom.SegExit.next_trap ?_
  unfold Pf.SegSignal.SegSignalEncStateV
  refine ⟨hcur, hsc, hfrom, hrem, hnone, by rw [hs3_pc, hentry], by rw [hlr, hentry],
    ⟨hs3_run, hs3_sp, hal0, hs3_al, hs3_x29.trans hx29, hs3_x19.trans hx19, hfl3, hsym3,
      hs3_vregs.trans hvregs⟩,
    hs3_tr.trans htr, hx0, hx1, hx2, hx3, hx4, hx5, hs3_x20.trans hx20, hs3_x25.trans hx25,
    hs3_x26.trans hx26, hs3_x28.trans hx28, hpt, hrest, hloc, hnow, hstk, ?_⟩
  rw [← hsp0]
  have h580g : memRegion (sp + 0x580#64) 120 =
      memRegion (sp + 0x580#64) 4 ∗ memRegion (sp + 0x584#64) 4 ∗ memRegion (sp + 0x588#64) 8 ∗
        memRegion (sp + 0x590#64) 8 ∗ memRegion (sp + 0x598#64) 4 ∗
        memRegion (sp + 0x59c#64) 8 ∗ memRegion (sp + 0x5a4#64) 8 ∗
        memRegion (sp + 0x5ac#64) 8 ∗ memRegion (sp + 0x5b4#64) 8 ∗
        memRegion (sp + 0x5bc#64) 4 ∗ memRegion (sp + 0x5c0#64) 24 ∗
        memRegion (sp + 0x5d8#64) 32 := by
    rw [show (120 : Nat) = 4 + (4 + (8 + (8 + (4 + (8 + (8 + (8 + (8 + (4 + (24 + 32))))))))))
        from rfl,
      show sp + 0x580#64 = sp + BitVec.ofNat 64 0x580 from rfl,
      mr_cut_add sp 0x580 4 _ (by decide),
      mr_cut_add sp (0x580 + 4) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8 + 4) 24 _ (by decide)]
  have h5f8g : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x278 ∗ memRegion (sp + 0x870#64) 8 ∗
        memRegion (sp + 0x878#64) 8 ∗ memRegion (sp + 0x880#64) 8 ∗
        memRegion (sp + 0x888#64) 8 ∗ memRegion (sp + 0x890#64) 4 ∗
        memRegion (sp + 0x894#64) 0x2ec := by
    rw [show (0x588 : Nat) = 0x278 + (8 + (8 + (8 + (8 + (4 + 0x2ec))))) from rfl,
      show sp + 0x5f8#64 = sp + BitVec.ofNat 64 0x5f8 from rfl,
      mr_cut_add sp 0x5f8 0x278 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  unfold cmScratch encSpillsAtV
  rw [h580g, h5f8g]
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm7

private theorem h45_coinsAfter_zero_entails_coinsAt (b cur : BitVec 64) (rest : List (BitVec 8))
    (hrest : rest.length < 2 ^ 63) :
    CryptoVerification.SignalSession.Coins.coinsAfter b cur rest 0 ⊢
      CryptoVerification.SignalSession.Coins.coinsAt b cur rest := by
  unfold CryptoVerification.SignalSession.Coins.coinsAfter
    CryptoVerification.SignalSession.Coins.tapeAfter2
    CryptoVerification.SignalSession.Coins.coinsAt
    CryptoVerification.SignalSession.Coins.tapeAt2
  have hcur : cur + BitVec.ofNat 64 0 = cur := BitVec.add_zero cur
  have hlen : rest.length - 0 = rest.length := Nat.sub_zero rest.length
  rw [hcur, hlen]
  exact Entails.pure_right hrest (Entails.refl _)

private def h45_segSignalEncCallFrame {ss_vt id_vt : BitVec 64} (A : RustAlloc) (_img : Obj.Image)
    (x : WithStoresEncGhost)
    (g : RecordGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (sp : BitVec 64) (s0 : State) : SepProp :=
  sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
  cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
  memRegion x.ret 248 ∗
  protocolAddressAt A x.loc x.locA ∗ nowAt s0.sp x.now ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - rootStack) ∗
  encSavedRegs s0.sp s0

private theorem h45_segSignal_enc_pre_unpack {ss_vt id_vt : BitVec 64}
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (img : Obj.Image) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (sp : BitVec 64) (R : SepProp) (s0 s : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp : s.sp = sp)
    (h64 : 64 ≤ x.rest.length)
    (hQ : otr.pqrState.length < 2 ^ 32) (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = sp + 0x580#64) (hx1 : s.readReg64 .x1 = sp + 0x288#64)
    (hx2 : s.readReg64 .x2 = x.ptA) (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 x.ptext.length)
    (hx4 : s.readReg64 .x4 = 0#64) (hx5 : s.readReg64 .x5 = x.remA)
    (hpt : x.ptext.length < 2 ^ 32) (hrest : x.rest.length < 2 ^ 63)
    (hm : s.mem ⊨
      (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 120 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x 0 s0 ∗ (TokenInit img ∗ R)) :
    ∃ g : RecordGhost,
      s.mem ⊨ (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse S img).pre
        (segSignalEncGhost sp pqCap pqPtr otr x) s ∗
        (h45_segSignalEncCallFrame (ss_vt := ss_vt) (id_vt := id_vt) A img x g sess taken k sp s0 ∗ R) := by
  unfold takenSlots encCommon at hm
  rw [hsp0, stackAt_sub sp encSubStack rootStack] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨g, hm⟩ := hm
  refine ⟨g, ?_⟩
  have htape := h45_coinsAfter_zero_entails_coinsAt img.base x.cur x.rest hrest
  have hm_rearr : s.mem ⊨
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
      (TokenInit img ∗
        otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗
        protocolAddressAt A x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗
        logOff img ∗
        stackAt sp rootStack ∗
        A.pool ∗
        h45_segSignalEncCallFrame (ss_vt := ss_vt) (id_vt := id_vt) A img x g sess taken k sp s0 ∗ R) := by
    unfold h45_segSignalEncCallFrame
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  have hm_tape := Satisfies.mono (sepConj_mono_left htape) hm_rearr
  have hx3_nat : (s.readReg64 .x3).toNat = x.ptext.length := by
    rw [hx3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT
    CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec Spec.inImage segSignalEncGhost optAddrAt
  dsimp only
  rw [hsp, emp_sepConj]
  have hpure :
      (⌜otr.pqrState.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ : SepProp) ∗
      ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      ⌜s.readReg64 .x0 = sp + 0x580#64 ∧ s.readReg64 .x1 = sp + 0x288#64 ∧
        s.readReg64 .x2 = x.ptA ∧ (s.readReg64 .x3).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧
        s.readReg64 .x4 = (if (none : Option AddrGhost).isSome then 0#64 else 0#64) ∧
        ((none : Option AddrGhost).isSome → 0#64 ≠ 0#64) ∧
        s.readReg64 .x5 = x.remA⌝ ∗
      (CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
        (TokenInit img ∗
          otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
          (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A x.rem x.remA ∗
          memRegion (sp + 0x580#64) 120 ∗
          logOff img ∗
          stackAt sp rootStack ∗
          A.pool ∗
          h45_segSignalEncCallFrame (ss_vt := ss_vt) (id_vt := id_vt) A img x g sess taken k sp s0 ∗ R)) =
      ((⌜otr.pqrState.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗ TokenInit img ∗
        (⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
          ⌜s.readReg64 .x0 = sp + 0x580#64 ∧ s.readReg64 .x1 = sp + 0x288#64 ∧
            s.readReg64 .x2 = x.ptA ∧ (s.readReg64 .x3).toNat = x.ptext.length ∧
            x.ptext.length < 2 ^ 32 ∧
            s.readReg64 .x4 = (if (none : Option AddrGhost).isSome then 0#64 else 0#64) ∧
            ((none : Option AddrGhost).isSome → 0#64 ≠ 0#64) ∧
            s.readReg64 .x5 = x.remA⌝ ∗
          otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
          (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A x.rem x.remA ∗
          memRegion (sp + 0x580#64) 120 ∗
          CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
          logOff img ∗
          stackAt sp rootStack ∗
          A.pool)) ∗
        (h45_segSignalEncCallFrame (ss_vt := ss_vt) (id_vt := id_vt) A img x g sess taken k sp s0 ∗ R)) := by
    ac_rfl
  rw [← hpure, satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj]
  refine ⟨⟨hQ, h64⟩, ⟨hfl, hsym⟩,
    ⟨hx0, hx1, hx2, hx3_nat, hpt, hx4, (by intro h; cases h), hx5⟩, hm_tape⟩

private theorem h45_segSignal_enc_post_pack {ss_vt id_vt : BitVec 64}
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (img : Obj.Image) (x : WithStoresEncGhost) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (sp : BitVec 64) (R : SepProp) (s0 s sm : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp : s.sp = sp)
    (hpost : sm.mem ⊨
      ((CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse S img).post
        (segSignalEncGhost sp pqCap pqPtr otr x) s sm ∗
        h45_segSignalEncCallFrame (ss_vt := ss_vt) (id_vt := id_vt) A img x g sess taken k sp s0) ∗ R) :
    (segSignalRes C S x otr).1 ≠ .error .panic ∧ sm.trace = s.trace ∧
    (sm.mem ⊨
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x (S.draws otr.pqrState x.rest) s0 ∗
      (TokenInit img ∗ R)) := by
  unfold CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT
    CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec Spec.inImage at hpost
  dsimp only at hpost
  rw [segSignalEncGhost_model, hsp] at hpost
  unfold segSignalEncGhost optAddrAt at hpost
  dsimp only at hpost
  rw [emp_sepConj] at hpost
  have h1 : sm.mem ⊨ ⌜(segSignalRes C S x otr).1 ≠ .error .panic ∧ sm.trace = s.trace⌝ ∗
      (((∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (S.draws otr.pqrState x.rest) ∗
        logOff img ∗ stackAt sp rootStack ∗ A.pool ∗
        h45_segSignalEncCallFrame (ss_vt := ss_vt) (id_vt := id_vt) A img x g sess taken k sp s0) ∗
        (TokenInit img ∗ R)) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hpost
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hne, htr⟩, hmem⟩
  refine ⟨hne, htr, ?_⟩
  unfold h45_segSignalEncCallFrame at hmem
  have hmem_rearr : sm.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - rootStack) ∗
        stackAt sp rootStack) ∗
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        nowAt s0.sp x.now ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (S.draws otr.pqrState x.rest) ∗
        logOff img ∗ encSavedRegs s0.sp s0 ∗ A.pool ∗ (TokenInit img ∗ R)) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack rootStack] at hmem_rearr
  unfold encCommon
  rw [hsp0]
  exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmem_rearr

private theorem h45_q_otr {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken)) :
    otr.pqrState.length < 2 ^ 32 :=
  fromSessionState_pqrState hfrom ▸ hEnv.scopeQ r sess hsc hcur

private theorem h45_segSignal_call_sub_trap {α : Type} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (trTrapProgAt img.base C abs) entry spec) (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit xc code s sf ∗ R') → False)
    (hpanic : ∀ sf, Steps (trTrapProgAt img.base C abs) s sf → sf.status = .Panicked →
      (sf.mem ⊨ (spec.onPanic xc s sf ∗ F) ∗ R) →
      (sf.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R0))
    (hnext : ∀ sm : State, (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      Steps (trTrapProgAt img.base C abs) s sm → sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → (sm.mem ⊨ (spec.post xc s sm ∗ F) ∗ R) →
      h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom xc s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, hout, _⟩ := hcall.no_fault_before_outcome xc (F ∗ R) s hpc hrun hm hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hL hsteps hpcm hrunm hspm hcsm hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hpanic sm hsteps hpan hpost⟩))⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact (hoom sm _ _hoom_st _hoom_post).elim

private theorem h45_segSignal_enc_to_ret_pf_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R_frame : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length)
    (hs : Pf.SegSignal.SegSignalEncStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k
      (TokenInit img ∗ R_frame) s0 s) :
    h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R_frame s0 s
      (fun s' => Pf.SegSignal.SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k
        (TokenInit img ∗ R_frame) s0 s') := by
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R_frame
  rcases hs with ⟨hcur, hsc, hfrom, hrem, hnone, hs_pc, hs_lr,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, hx0, hx1, hx2, hx3, hx4, hx5, hx20, hx25, hx26, hx28,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64 with hsp0
  have hentry : encEntry img = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) hEnv.loads encryptWithStoresName
  have hs_pc' : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName := by
    rw [hs_pc, hentry, Pf.SegSignal.otrEnc_addr_eq_trap]
  have hQ : otr.pqrState.length < 2 ^ 32 := h45_q_otr hEnv hcur hsc hfrom
  have hm' : s.mem ⊨
      (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 120 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x 0 s0 ∗ (TokenInit img ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [R]; ac_rfl)) hm
  obtain ⟨g, hm_pre⟩ := h45_segSignal_enc_pre_unpack C A ctl S img x sess otr taken pqCap pqPtr k sp R
    s0 s hsp0.symm hsp h64 hQ hfl hsym hx0 hx1 hx2 hx3 hx4 hx5 hpt hrest hm'
  refine h45_segSignal_call_sub_trap hEnv.callees.otrEnc (segSignalEncGhost sp pqCap pqPtr otr x)
    hs_pc' hrun hal hs_lr hm_pre
    (fun _ code _ _ hex => by
      rw [show (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse S img).onExit
            (segSignalEncGhost sp pqCap pqPtr otr x) code s _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost =>
      Pf.SegSignal.segSignal_panic_bridge (Q := fun s => s.length < 2 ^ 32) hcur hsc hnone hfrom hrem htr hpost)
    ?_
  intro sm hL1 hsteps12 hsm_pc hsm_run hsm_sp hcsm hpost
  have ⟨hflm, hsymm⟩ := SegFrom.callInv_steps hfl hsym hsteps12 hL1
  have hsm_sp' : sm.sp = sp := hsm_sp.trans hsp
  have hsm_al : sm.spAligned = true := SegFrom.spAligned_of_sp_eq hal hsm_sp
  have hsm_x19 : sm.readReg64 .x19 = x.ret := (hcsm.1).trans hx19
  have hsm_x20 : sm.readReg64 .x20 = sp + 0x58#64 := (hcsm.2.1).trans hx20
  have hsm_x25 : sm.readReg64 .x25 = sp + 0x580#64 := (hcsm.2.2.2.2.2.2.1).trans hx25
  have hsm_x26 : sm.readReg64 .x26 = sp + 0x9d0#64 := (hcsm.2.2.2.2.2.2.2.1).trans hx26
  have hsm_x28 : sm.readReg64 .x28 = sp + 0x4a0#64 := (hcsm.2.2.2.2.2.2.2.2.2.1).trans hx28
  have hsm_x29 : sm.readReg64 .x29 = s0.sp - 0x60#64 :=
    (hcsm.2.2.2.2.2.2.2.2.2.2.1).trans hx29
  have hsm_vregs : calleeSavedVRegs sm = calleeSavedVRegs s0 :=
    (hcsm.2.2.2.2.2.2.2.2.2.2.2).trans hvregs
  obtain ⟨hne, hsm_tr, hm_ret⟩ :=
    h45_segSignal_enc_post_pack C A ctl S img x g sess otr taken pqCap pqPtr k sp R s0 s sm
      hsp0.symm hsp hpost
  have hm_ret' : sm.mem ⊨
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x (S.draws otr.pqrState x.rest) s0 ∗
      (encStoreExtra kit st0 ikit ist0 x s0 ∗ (TokenInit img ∗ R_frame)) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [R]; ac_rfl)) hm_ret
  exact h45_segExitVT_of_segExit_trap (Pf.SegFrom.SegExit.next_trap ⟨hcur, hsc, hfrom, hrem, hnone, hne, hsm_pc,
    ⟨hsm_run, hsm_sp', hal0, hsm_al, hsm_x29, hsm_x19, hflm, hsymm, hsm_vregs⟩,
    hsm_tr.trans htr, hsm_x20, hsm_x25, hsm_x26, hsm_x28,
    hpt, hrest, hloc, hnow, hstk, g, hm_ret'⟩)

private theorem h45_pqCap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
  omega

private theorem h45_segSignal_list_len3 {α : Type} (ws : List α) (h : ws.length = 3) :
    ∃ v0 v1 v2, ws = [v0, v1, v2] := by
  rcases ws with _ | ⟨v0, ws⟩; · nomatch h
  rcases ws with _ | ⟨v1, ws⟩; · nomatch h
  rcases ws with _ | ⟨v2, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨v0, v1, v2, rfl⟩
  · nomatch h

private theorem h45_signalMessageWordsAt_eq_words64At (gm : SignalMessageGhost) (sm : SignalMessage)
    (a : BitVec 64) (m7 m8 m9 m10 m11 m12 m14 : BitVec 64) :
    signalMessageWordsAt gm sm a m7 m8 m9 m10 m11 m12 m14 =
      words64At a [gm.pqCap, gm.pqPtr, BitVec.ofNat 64 sm.pqRatchet.length, gm.ctPtr,
        BitVec.ofNat 64 sm.ciphertext.length, gm.serPtr, BitVec.ofNat 64 sm.serialized.length,
        m7, m8, m9, m10, m11, m12, sm.previousCounter ++ sm.counter, m14] := by
  simp only [signalMessageWordsAt, words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

private theorem h45_signalMessageAt_relocate (A : RustAlloc) (gm : SignalMessageGhost) (src : BitVec 64)
    (sm : SignalMessage) {m : Memory} {R : SepProp}
    (hm : m ⊨ signalMessageAt A gm src sm ∗ R) :
    ∃ (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) (H : SepProp),
      gm.pqCap + 1#64 ≠ 0#64 ∧
      (m ⊨ words64At src [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        H ∗ R) ∧
      (∀ dst : BitVec 64,
        words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
          H ⊢ signalMessageAt A gm dst sm) := by
  have hm' := Satisfies.mono (sepConj_mono_left (signalMessageAt_unpack A gm src sm)) hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm'
  rcases hm' with ⟨hpq, hm'⟩
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm'
  obtain ⟨m7, m8, m9, m10, m11, m12, m14, hm'⟩ := hm'
  rw [h45_signalMessageWordsAt_eq_words64At, sepConj_assoc] at hm'
  refine ⟨gm.pqPtr, BitVec.ofNat 64 sm.pqRatchet.length, gm.ctPtr,
    BitVec.ofNat 64 sm.ciphertext.length, gm.serPtr, BitVec.ofNat 64 sm.serialized.length,
    m7, m8, m9, m10, m11, m12, sm.previousCounter ++ sm.counter, m14,
    signalMessageHeap A gm sm m7 m8 m9 m10 m11 m12 m14,
    h45_pqCap_add_one_ne_zero hpq, hm', ?_⟩
  intro dst
  rw [← h45_signalMessageWordsAt_eq_words64At]
  exact signalMessageAt_pack A gm dst sm m7 m8 m9 m10 m11 m12 m14

private def h45_segSignalOkFrame {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost)
    (g : RecordGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
    (k : IdentityKey) (draws : Nat) (sp : BitVec 64) (H : SepProp) (s0 : State) : SepProp :=
  H ∗
  sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
  memRegion (sp + 0x3f0#64) 120 ∗
  cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗
  memRegion (sp + 0x5f8#64) 0x508 ∗
  memRegion (sp + 0xb18#64) 0x68 ∗
  memRegion x.ret 248 ∗ encCommon A ctl img x draws s0

private theorem h45_segSignal_ok_unpack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (k : IdentityKey) (sm : SignalMessage) (draws : Nat) (sp : BitVec 64) (R : SepProp)
    (s0 s : State)
    (hm : s.mem ⊨
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' otr') ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (.ok sm) ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x draws s0 ∗ R) :
    ∃ (pqCap' pqPtr' : BitVec 64) (gm : SignalMessageGhost)
      (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 v0 v1 v2 : BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64) (H : SepProp),
      gm.pqCap + 1#64 ≠ 0#64 ∧
      (∀ dst : BitVec 64,
        words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
          H ⊢ signalMessageAt A gm dst sm) ∧
      (s.mem ⊨ (words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
            w12, w13, w14] ∗
          words64At (sp + 0xb00#64) [v0, v1, v2] ∗
          words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
            d14, d15]) ∗
        (h45_segSignalOkFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g sess taken otr' pqCap' pqPtr'
          k draws sp H s0 ∗ R)) := by
  unfold signalMessageResultAt at hm
  dsimp only at hm
  have hm1 : s.mem ⊨
      (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr') ∗
      (∃∗ gm : SignalMessageGhost, signalMessageAt A gm (sp + 0x580#64) sm) ∗
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗ encCommon A ctl img x draws s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨pqCap', hm1⟩ := hm1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨pqPtr', hm1⟩ := hm1
  have hm2 : s.mem ⊨
      (∃∗ gm : SignalMessageGhost, signalMessageAt A gm (sp + 0x580#64) sm) ∗
      (otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
        sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗ encCommon A ctl img x draws s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm2
  obtain ⟨gm, hm2⟩ := hm2
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, H, hpq, hm3, hpack⟩ :=
    h45_signalMessageAt_relocate A gm (sp + 0x580#64) sm hm2
  have h370 : memRegion (sp + 0x370#64) 0xf8 =
      memRegion (sp + 0x370#64) 128 ∗ memRegion (sp + 0x3f0#64) 120 :=
    segSignal_memRegion_cut (sp + 0x370#64) (sp + 0x3f0#64) 0xf8 128 120 (by bv_omega) (by decide) (by decide)
  have h5f8 : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x508 ∗
        (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68) := by
    rw [segSignal_memRegion_cut (sp + 0x5f8#64) (sp + 0xb00#64) 0x588 0x508 0x80 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0xb00#64) (sp + 0xb18#64) 0x80 24 0x68 (by bv_omega) (by decide) (by decide)]
  rw [h370, h5f8] at hm3
  have hm_d : s.mem ⊨ memRegion (sp + 0x370#64) (8 * 16) ∗
      (memRegion (sp + 0xb00#64) (8 * 3) ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        h45_segSignalOkFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g sess taken otr' pqCap' pqPtr' k
          draws sp H s0 ∗ R) := by
    unfold h45_segSignalOkFrame
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm3
  obtain ⟨ds, hds_len, hm_d⟩ := memRegion_exists_words64At 16 (sp + 0x370#64) (by decide) hm_d
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, rfl⟩ :=
    segSignal_list_len16 ds hds_len
  have hm_v : s.mem ⊨ memRegion (sp + 0xb00#64) (8 * 3) ∗
      (words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
          d14, d15] ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        h45_segSignalOkFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g sess taken otr' pqCap' pqPtr' k
          draws sp H s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm_d
  obtain ⟨vs, hvs_len, hm_v⟩ := memRegion_exists_words64At 3 (sp + 0xb00#64) (by decide) hm_v
  obtain ⟨v0, v1, v2, rfl⟩ := h45_segSignal_list_len3 vs hvs_len
  refine ⟨pqCap', pqPtr', gm, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, H,
    hpq, hpack, ?_⟩
  exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm_v

private theorem h45_segSignal_ok_pack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (sm : SignalMessage) (gm : SignalMessageGhost)
    (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64)
    (draws : Nat) (sp : BitVec 64) (H R Pm : SepProp) (s0 s1 : State)
    (hpack : ∀ dst : BitVec 64,
      words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        H ⊢ signalMessageAt A gm dst sm)
    (hPm : Pm ⊢ words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
        w12, w13, w14] ∗
      words64At (sp + 0xb00#64) [w4, w5, w6] ∗
      words64At (sp + 0x370#64) [0x8000000000000000#64, gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8,
        w9, w10, w11, w12, w13, w14])
    (hm : s1.mem ⊨ Pm ∗ (h45_segSignalOkFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g sess taken otr'
      pqCap' pqPtr' k draws sp H s0 ∗ R)) :
    s1.mem ⊨ cmSlots A sp sess taken otr' pqCap' pqPtr' k (.signalMessage sm) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x draws s0 ∗ R := by
  have hm1 := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold h45_segSignalOkFrame at hm1
  have h370_hd :
      words64At (sp + 0x370#64) [0x8000000000000000#64, gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8,
        w9, w10, w11, w12, w13, w14] =
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗
        words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
          w12, w13, w14] := rfl
  rw [h370_hd] at hm1
  have h580 :
      words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
        w14] ⊢ memRegion (sp + 0x580#64) 120 :=
    words64At_entails_memRegion
      [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14]
      (sp + 0x580#64) (by simp only [List.length_cons, List.length_nil]; decide)
  have hb00 :
      words64At (sp + 0xb00#64) [w4, w5, w6] ⊢ memRegion (sp + 0xb00#64) 24 :=
    words64At_entails_memRegion [w4, w5, w6] (sp + 0xb00#64)
      (by simp only [List.length_cons, List.length_nil]; decide)
  have hsm_ex :
      words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
        w12, w13, w14] ∗ H ⊢
      ∃∗ gm' : SignalMessageGhost, signalMessageAt A gm' ((sp + 0x370#64) + 8#64) sm :=
    Entails.trans (hpack ((sp + 0x370#64) + 8#64)) (Entails.sepExists_right gm (Entails.refl _))
  have hrec_ex :
      sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ⊢
      ∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken) :=
    Entails.sepExists_right g (Entails.refl _)
  have hm_rearr : s1.mem ⊨
      ((words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
            w12, w13, w14] ∗ H) ∗
        sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        words64At (sp + 0xb00#64) [w4, w5, w6]) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
      ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗ memRegion (sp + 0x3f0#64) 120 ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x508 ∗
      memRegion (sp + 0xb18#64) 0x68 ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x draws s0 ∗ R :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm1
  have hm_mono := Satisfies.mono
    (sepConj_mono_left (sepConj_mono hsm_ex (sepConj_mono hrec_ex (sepConj_mono h580 hb00))))
    hm_rearr
  have h46a_eq :
      memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗
        (memRegion (sp + 0x580#64) 120 ∗
          (memRegion (sp + 0x5f8#64) 0x508 ∗
            (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68))) := by
    rw [segSignal_memRegion_cut (sp + 0x46a#64) (sp + 0x580#64) 0x716 0x116 0x600 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0x580#64) (sp + 0x5f8#64) 0x600 120 0x588 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0x5f8#64) (sp + 0xb00#64) 0x588 0x508 0x80 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0xb00#64) (sp + 0xb18#64) 0x80 24 0x68 (by bv_omega) (by decide) (by decide)]
  have h3f0 : (sp + 0x370#64) + 0x80#64 = sp + 0x3f0#64 := by bv_omega
  have hm_poll : s1.mem ⊨
      (memRegion (sp + 0x46a#64) 0x116 ∗
        (memRegion (sp + 0x580#64) 120 ∗
          (memRegion (sp + 0x5f8#64) 0x508 ∗
            (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68)))) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
      ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗
      (∃∗ gm' : SignalMessageGhost, signalMessageAt A gm' ((sp + 0x370#64) + 8#64) sm) ∗
      memRegion (sp + 0x3f0#64) 120 ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x draws s0 ∗ R :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm_mono
  rw [← h46a_eq] at hm_poll
  unfold cmSlots takenSlots apiEncResultAt
  dsimp only
  rw [h3f0]
  exact Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm_poll

private theorem h45_segSignal_ok_path_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (sm : SignalMessage) (hok : (segSignalRes C S x otr).1 = .ok sm)
    (hs : Pf.SegSignal.SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => ∃ m otr' pqCap' pqPtr',
        CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap'
          pqPtr' R0 s0 s') := by
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hs with ⟨hcur, hsc, hfrom, hrem, hnone, _, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, hx20, hx25, hx26, hx28, hpt, hrest, hloc, hnow, hstk, g, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hentry : encEntry img = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) hEnv.loads encryptWithStoresName
  have hs_pc' : s.pc = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 0x3a4#64 := by
    simpa only [hentry] using hs_pc
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]
    change s0.sp - 0x60#64 = (s0.sp - 0xbe0#64) + 0xb80#64
    bv_omega
  rw [hok] at hm
  obtain ⟨pqCap', pqPtr', gm, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, H,
    hpq, hpack, hm_unp⟩ :=
    h45_segSignal_ok_unpack A ctl img x g sess taken (segSignalRes C S x otr).2 k sm
      (S.draws otr.pqrState x.rest) sp R s0 s hm
  refine Pf.SegFrom.SegExit.of_sepWP_trap hm_unp
    (Pf.SegSignal.segSignal_step_ok_trap hs_pc' hrun hsp hal hx25 hx26 hx29' hpq) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x19, hs1_x20, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hPm1⟩
  have ⟨hfl1, hsym1⟩ := SegFrom.callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := SegFrom.spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hm1_ok := h45_segSignal_ok_pack A ctl img x g sess taken (segSignalRes C S x otr).2 pqCap' pqPtr' k sm gm
    w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
    (S.draws otr.pqrState x.rest) sp H R Pm1 s0 s1 hpack hPm1 hm1
  have hstep5 : EncEncryptStep C S uuidTryParse x sess otr (.signalMessage sm) (segSignalRes C S x otr).2 := by
    unfold EncEncryptStep
    rw [hnone]
    exact ⟨sm, execOk_of_exec_ok hok, rfl⟩
  refine Pf.SegFrom.SegExit.next_trap ⟨.signalMessage sm, (segSignalRes C S x otr).2, pqCap', pqPtr',
    ⟨hcur, hsc, hfrom, hrem, hstep5⟩, ?_⟩
  refine ⟨?_, ⟨hs1_run, hs1_sp, hal0, hs1_al, hs1_x29.trans hx29, hs1_x19.trans hx19,
      hfl1, hsym1, hs1_vregs.trans hvregs⟩, hs1_tr.trans htr,
    ⟨hs1_x20.trans hx20, hs1_x25.trans hx25, hs1_x26.trans hx26, hs1_x28.trans hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm1_ok⟩
  rw [hs1_pc, cmPC, hentry]

private theorem h45_segSignal_err_path_pf_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (p : SignalProtocolError) (herr : (segSignalRes C S x otr).1 = .error p)
    (hs : Pf.SegSignal.SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let envF := h45_envF hEnv
  obtain ⟨hcur, hsc, hfrom, hrem, hnone, hnp, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩, htr, hx20, hx25, hx26, hx28,
    hpt, hrest, hloc, hnow, hstk, g, hm⟩ := hs
  set sp := s0.sp - 0xbe0#64 with hsp0
  have hp_pan : p ≠ .panic := by
    rintro rfl
    exact hnp herr
  rw [herr] at hm
  simp only [signalMessageResultAt, errResultAt, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceSub,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨pqCap', pqPtr', hm⟩ := hm
  have hst : speAt A (utf8 "encrypt") (sp + 0x588#64) p ⊢
      ∃∗ ws : List (BitVec 64), ∃∗ H : SepProp,
        ⌜SpeStaged A x.ret (.protocol p) ws H⌝ ∗ words64At (sp + 0x588#64) ws ∗ H :=
    speStaged_of_encErrAt A (sp + 0x588#64) x.ret (.protocol p) (by intro h; cases h)
  have hm1 := segSignal_apply hst (by sep_focus) hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨ws, H, hm1⟩ := hm1
  obtain ⟨hstg, hm1⟩ := segSignal_pure_front hm1
  obtain ⟨w0, w1, w2, w3, w4, w5, rfl⟩ := segSignal_list_len6 ws hstg.2.1
  have hsplit : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x508 ∗ memRegion (sp + 0xb00#64) 24 ∗
        memRegion (sp + 0xb18#64) 0x68 := by
    rw [show (0x588 : Nat) = 0x508 + (24 + 0x68) from rfl,
      show sp + 0x5f8#64 = sp + BitVec.ofNat 64 0x5f8 from rfl,
      mr_cut_add sp 0x5f8 0x508 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x508) 24 _ (by decide)]
  have hm2 := segSignal_apply (Entails.of_eq_explicit hsplit) (by sep_focus) hm1
  have hm2' : s.mem ⊨ memRegion (sp + 0xb00#64) (8 * 3) ∗ _ :=
    segSignal_apply (Entails.refl _) (by sep_focus) hm2
  obtain ⟨vs, hvs, hm3⟩ := SegFrom.memRegion_exists_words64At 3 (sp + 0xb00#64) (by decide) hm2'
  obtain ⟨v0, v1, v2, rfl⟩ := h45_segSignal_list_len3 vs hvs
  have hentry : encEntry img = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) hEnv.loads encryptWithStoresName
  have hs_pc' : s.pc = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 0x3a4#64 := by
    rw [hs_pc, hentry]
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29, hsp0]
    bv_omega
  have hm4 := segSignal_focusR (T := ((sp + 0x580#64) ↦₆₄ errTag) ∗
      words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗ words64At (sp + 0xb00#64) [v0, v1, v2])
    (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) (by sep_focus) (by sep_focus) hm3
  refine Pf.SegFrom.SegExit.of_sepWP_trap hm4 (Pf.SegSignal.segSignal_step_err_trap hs_pc' hrun hsp hal hx25 hx26 hx29') ?_
  intro s3 Pm3 hL hsteps hs3_pc hs3_run hm5
    ⟨hs3_sp, hs3_tr, hs3_x19, hs3_x20, hs3_x21, hs3_x23, hs3_x25, hs3_x26, hs3_x27, hs3_x28,
      hs3_x29, hs3_vregs, hPm3⟩
  have ⟨hfl3, hsym3⟩ := SegFrom.callInv_steps hfl hsym hsteps hL
  have hs3_al : s3.spAligned = true := SegFrom.spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  have hm6 := Satisfies.mono (sepConj_mono_left hPm3) hm5
  rw [← sepConj_assoc] at hm6
  have hm7 := segSignal_apply (segSignal_err_tail_ent A sp g sess taken k pqCap' pqPtr' (segSignalRes C S x otr).2
    w0 w1 w2 w3 w4 w5) (by sep_focus) hm6
  have hmod := segSignal_model_err (C := C) (S := S) (x := x) hcur hnone hfrom hrem
    (execOk_of_exec_error herr)
  have hdraws := (segSignal_sendState (S := S) (x := x) (c := .newOrUnchanged) hcur hnone hfrom hrem).2
  have hstf : (h45_kitF kit).storeFinal st0 (okAnswers r .newOrUnchanged)
      (x.model C S uuidTryParse (okAnswers r .newOrUnchanged)).2 = st0 := by
    rw [h45_storeFinal_kitF, hmod]; rfl
  have histf : ikit.idFinal ist0 (okAnswers r .newOrUnchanged)
      (x.model C S uuidTryParse (okAnswers r .newOrUnchanged)).2 = ist0 := by
    rw [hmod]; rfl
  rw [← h45_segExit_kitF_trap]
  refine Tails.tailSignalEncryptErr_ok_trap envF x R0 s0 s3
    (okAnswers r .newOrUnchanged) (.protocol p)
    w0 w1 w2 w3 w4 w5 H cmScratch (Or.inr rfl) g (takenRecord sess taken)
    (some (pqCap', pqPtr', (segSignalRes C S x otr).2)) ?_ hstg ?_
  · refine (h45_tailModel_kitF kit st0 ikit ist0 C S uuidTryParse encRecord x
        (okAnswers r .newOrUnchanged) (.error (.protocol p)) s0 s3).mpr ?_
    refine ⟨⟨by rw [hmod, segSignal_ofProtocol hp_pan], by rw [hmod]; exact ⟨hsc.2, trivial⟩,
      by rw [hmod]; trivial⟩, ?_⟩
    rw [hs3_tr, htr, hmod, ikit.traceOfWith_load]; rfl
  · refine ⟨?_, ⟨hs3_run, hs3_sp, hal0, hs3_al, hs3_x29.trans hx29, hs3_x19.trans hx19,
      hfl3, hsym3, hs3_vregs.trans hvregs⟩, ⟨hs3_x26.trans hx26, hs3_x28.trans hx28, hs3_x27, hs3_x21, hs3_x23⟩,
      hstk, ?_⟩
    · rw [hs3_pc, hentry]
    · rw [hdraws, hstf, histf]
      dsimp only
      rw [← hsp0]
      exact Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm7

theorem h45_segSignal_okVT_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R_frame : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length)
    (hpk : sess.pendingPreKey = none)
    (hs : KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k
      (TokenInit img ∗ R_frame) s0 s) :
    h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R_frame s0 s
      (fun s' => ∃ m otr' pqCap' pqPtr',
        CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap'
          pqPtr' (TokenInit img ∗ R_frame) s0 s') := by
  refine h45_segExitVT_trans_trap
    (h45_segExitVT_of_segExit_trap (h45_segSignal_to_ack_trap hEnv x r sess otr taken pqCap pqPtr k
      (TokenInit img ∗ R_frame) s0 s hpk hs))
    fun sm h =>
      h45_segExitVT_trans_trap
        (h45_segExitVT_of_segExit_trap (h45_segSignal_ack_to_enc_trap hEnv x r sess otr taken pqCap pqPtr k
          (TokenInit img ∗ R_frame) s0 sm h))
        fun sn h' =>
          h45_segExitVT_trans_trap
            (h45_segSignal_enc_to_ret_pf_trap hEnv x r sess otr taken pqCap pqPtr k R_frame s0 sn h64 h')
            fun sr hret => ?_
  rcases hres : (segSignalRes C S x otr).1 with p | m
  · exact h45_segExitVT_of_false_trap
      (h45_segExitVT_of_segExit_trap (h45_segSignal_err_path_pf_trap hEnv x r sess otr taken k
        (TokenInit img ∗ R_frame) s0 sr p hres hret))
  · exact h45_segExitVT_of_segExit_trap
      (h45_segSignal_ok_path_trap hEnv x r sess otr taken k (TokenInit img ∗ R_frame) s0 sr m hres hret)

end SegSignal

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
