/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
public import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Rodata
import LibsignalBinary.Proofs.Common.StringCloneFlat

/-!
# Shared Infrastructure and Frame Helpers for `segLoad_ok`

`FrozenInv` and `SegExit` bridges, `.rodata` vtable/literal lemmas, `loadPollOutAtS` decomposition,
and stack-frame splitting helpers for the `load_session` entry segment of
`session_message_encrypt_with_stores`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `FrozenInv` and `SegExit` Bridges -/

structure FrozenInv (img : Obj.Image) (s : State) : Prop where
  frozen : img.FrozenLoaded s
  symtab : s.symtab = img.symtab

theorem FrozenInv.of_steps {prog : Program} {img : Obj.Image} {s sf : State}
    (h : FrozenInv img s) (hsteps : Steps prog s sf) : FrozenInv img sf :=
  ⟨h.1.of_keepsFrozen hsteps.keepsFrozen, hsteps.symtab_eq.trans h.2⟩

theorem messageEncrypt_of_sepWP_frozen {prog : Program} {img : Obj.Image} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : FrozenInv img s)
    (h : SepWP prog mid s P
      (fun sm Pm => FrozenInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := h.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ :=
    hnext (hF.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem messageEncrypt_call_panic_then_wp_frozen {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : FrozenInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F)
        (fun sf' P_f => FrozenInv img sf' → post sf' P_f))
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun (hpre R' hm) hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hFm := hF.of_steps hsteps
    obtain ⟨sf, hsteps', ⟨hpc', hrun', P_f, hmf, hq⟩ | ⟨_, _hoom⟩⟩ :=
      (hnext sm hpcm hrunm hspm hcsm).elim hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc', hrun', P_f, hmf, hq (hFm.of_steps hsteps')⟩⟩
    · exact (not_satisfies_false_sepConj _hoom).elim
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · rw [hexit_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (hoom sm (F ∗ R') _hoom_st _hoom_post).elim

theorem messageEncrypt_call_panic_then_sepWPp_frozen {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : FrozenInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → FrozenInv img sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ Qpan sf' ∗ R)))
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun (hpre R' hm) hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hFm := hF.of_steps hsteps
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm hFm R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · rw [hexit_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (hoom sm (F ∗ R') _hoom_st _hoom_post).elim

theorem alloc_onPanic_entails {C : Crypto} {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {s0 s sf : State} {F : SepProp}
    (hpref0 : s0.trace <+: s.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf := by
  dsimp only [withStoresEncSpecV, Spec.inImage]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  have halloc0 : allocFailedIn s0 sf := by
    unfold allocFailedIn at halloc ⊢
    rcases hpref0 with ⟨t1, ht1⟩
    have hlen : s.trace.length = s0.trace.length + t1.length := by
      rw [← ht1, List.length_append]
    rw [hlen, ← List.drop_drop] at halloc
    exact List.mem_of_mem_drop halloc
  exact Entails.pure_right ⟨hpref0.trans hpref, Or.inl halloc0⟩ (entails_anyHeap _)

theorem segExit_of_sepWPp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (tripleRatchetProgAt img.base C ctl abs) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 sf Out)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R))) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hcont⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · obtain ⟨sf, hsteps', hout'⟩ := hcont hmf (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem segExit_done {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {Out : State → Prop}
    (h : Out s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s Out :=
  fun _ => ⟨s, .refl s, Or.inl h⟩

theorem segExit_of_false {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {Out : State → Prop}
    (h : SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False)) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := h hL
  exact ⟨sf, hsteps, hout.elim False.elim Or.inr⟩

/-! ## Entry and Callee Address Lemmas -/

theorem encEntry_eq_fnAddr {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    encEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName :=
  entryOf_eq_tripleRatchetProgAt env.loads encryptWithStoresName

theorem encEntry_eq_base_add {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    encEntry img = img.base + 0x3cbd8#64 := by
  rw [encEntry_eq_fnAddr env, Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x3cbd8]

theorem memcpy_ok_at_enc {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (_env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + bv% (ls_off% "memcpy" - 0x3cbd8))
      framelessMemcpySpec := by
  exact framelessMemcpy_ok_at (b := img.base) (C := C) (ctl := ctl) (abs := abs)
    (name := encryptWithStoresName) (k := num% (ls_off% "memcpy" - 0x3cbd8))
    (by simp only [libsignalSessionCode_fnOff_0x3cbd8, arm64_norm])

theorem dealloc_ok_at_enc {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x3cbd8))
      (rustDeallocSpec A) := by
  exact dealloc_ok_at_norm (b := img.base) (C := C) (ctl := ctl)
    (name := encryptWithStoresName) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x3cbd8)) env.hooks.alloc
    (by simp only [libsignalSessionCode_fnOff_0x3cbd8, arm64_norm])

theorem stringClone_ok_at_enc {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + bv% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - 0x3cbd8))
      (stringCloneSpec A) := by
  exact sub_ok_at_of_fnAddr
    (LibsignalBinary.Proofs.Common.StringCloneFlat.stringClone_tripleRatchetProgAt_ok img.base C A ctl abs env.hooks.alloc)
    encryptWithStoresName (num% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - 0x3cbd8))
    (by simp only [libsignalSessionCode_fnOff_0x3cbd8,
      LibsignalBinary.Proofs.Common.StringCloneFlat.stringCloneName_fnOff, arm64_norm])

/-! ## `.rodata` Vtable and String Literal Lemmas -/

def loadVtablesAt {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) : SepProp :=
  ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (b + kit.loadShimOff)) ∗
  ((b + kit.loadFutVtOff) ↦₆₄ᵣ (b + kit.loadFutDropOff)) ∗
  ((b + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
  ((b + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((b + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (b + kit.loadPollOff))

theorem loadVtablesAt_intro {img : Obj.Image} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} (vt : MessageDecrypt.SessionOnlyVtablesOk img kit)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ loadVtablesAt kit ∗ P := by
  unfold loadVtablesAt
  simp only [sepConj_assoc]
  exact vt.loadSlot hF (vt.loadFutDrop hF
    (vt.loadFutSize hF (vt.loadFutAlign hF
      (vt.loadFutPoll hF hP))))

private theorem rodata_0x4a6a0_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% 0x3cdb0 0x3cdb4) - num% (ls_xref% 0x2440 0x2444))).take 15 = utf8 "message_encrypt" := by
  rfl_kernel

theorem rodata_message_encrypt_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4)) ↦ᵣ utf8 "message_encrypt") ∗ P :=
  EncryptCoreFacts.of_rodata_loads_eq himg
    (secOff := num% (ls_xref% 0x3cdb0 0x3cdb4)) (secLen := 15) (dataOff := num% (ls_xref% 0x2440 0x2444))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) rodata_0x4a6a0_eq hro hP

/-! ## Model Helpers for `segLoad` Error Exits -/

/-- Default `StoreAnswers` witness for `segLoad` error exits, where only `loadSession` is consulted. -/
def answersOfLoad (ans : Except Unit (Option (SessionRecord (List (BitVec 8))))) :
    StoreAnswers (List (BitVec 8)) Unit :=
  { loadSession := ans
    isTrustedIdentity := .ok true
    saveIdentity := .ok .newOrUnchanged
    storeSession := .ok () }

@[simp]
theorem draws_answersOfLoad_err (S : SpqrModel) (x : WithStoresEncGhost) :
    x.draws S (answersOfLoad (.error ())) = 0 := rfl

@[simp]
theorem draws_answersOfLoad_none (S : SpqrModel) (x : WithStoresEncGhost) :
    x.draws S (answersOfLoad (.ok none)) = 0 := rfl

theorem draws_answersOfLoad_some_none (S : SpqrModel) (x : WithStoresEncGhost)
    (r : SessionRecord (List (BitVec 8))) (hr : r.currentSession = none) :
    x.draws S (answersOfLoad (.ok (some r))) = 0 := by
  simp [EncryptGhost.draws, EncryptGhost.sendState, loadedSession, answersOfLoad, hr]

theorem tailModel_load_err {A : RustAlloc} {b : BitVec 64} {kit : SessionStoreSpec A b}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A b} {ist0 : ikit.IdState}
    {C : Crypto} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {s0 s : State}
    (hl : kit.loadRel st0 x.rem.val (.error ()))
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.error ())) :
    TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (answersOfLoad (.error ())) (.error (.store ())) s0 s := by
  have hm : x.model C S uuidTryParse (answersOfLoad (.error ())) =
      (.error (.store ()), [.loadSession x.rem.val]) := rfl
  refine ⟨⟨congrArg Prod.fst hm, ?_⟩, ?_⟩
  · rw [congrArg Prod.snd hm]
    exact ⟨⟨hl, trivial⟩, trivial⟩
  · rw [htr, congrArg Prod.snd hm, ikit.traceOfWith_load]
    rfl

theorem tailModel_load_none {A : RustAlloc} {b : BitVec 64} {kit : SessionStoreSpec A b}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A b} {ist0 : ikit.IdState}
    {C : Crypto} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {s0 s : State}
    (hl : kit.loadRel st0 x.rem.val (.ok none))
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok none)) :
    TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (answersOfLoad (.ok none))
      (.error (.sessionNotFound x.rem.val "message_encrypt")) s0 s := by
  have hm : x.model C S uuidTryParse (answersOfLoad (.ok none)) =
      (.error (.sessionNotFound x.rem.val "message_encrypt"), [.loadSession x.rem.val]) := rfl
  refine ⟨⟨congrArg Prod.fst hm, ?_⟩, ?_⟩
  · rw [congrArg Prod.snd hm]
    exact ⟨⟨hl, trivial⟩, trivial⟩
  · rw [htr, congrArg Prod.snd hm, ikit.traceOfWith_load]
    rfl

theorem tailModel_load_some_none {A : RustAlloc} {b : BitVec 64} {kit : SessionStoreSpec A b}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A b} {ist0 : ikit.IdState}
    {C : Crypto} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))} {s0 s : State}
    (hl : kit.loadRel st0 x.rem.val (.ok (some r)))
    (hr : r.currentSession = none)
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r))) :
    TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (answersOfLoad (.ok (some r)))
      (.error (.sessionNotFound x.rem.val "message_encrypt")) s0 s := by
  have hm : x.model C S uuidTryParse (answersOfLoad (.ok (some r))) =
      (.error (.sessionNotFound x.rem.val "message_encrypt"), [.loadSession x.rem.val]) := by
    unfold EncryptGhost.model messageEncrypt Api.run storeCall answersOfLoad
    simp only [ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, pure, ExceptT.pure, StateT.pure, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, StateT.map, Functor.map, throw, throwThe, MonadExceptOf.throw, hr]
    rfl
  refine ⟨⟨congrArg Prod.fst hm, ?_⟩, ?_⟩
  · rw [congrArg Prod.snd hm]
    exact ⟨⟨hl, trivial⟩, trivial⟩
  · rw [htr, congrArg Prod.snd hm, ikit.traceOfWith_load]
    rfl

/-! ## `DevWord` and `SpeStaged` Error Helpers -/

private theorem pointsTo8_eq_pointsToBytes (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

/-- 64-bit word `w3` whose low byte is device ID `d` followed by 7 padding bytes. -/
def DevWord (d : BitVec 8) (w3 : BitVec 64) : Prop :=
  ∃ pad : List (BitVec 8), pad.length = 7 ∧ unpack64 w3 = d :: pad

theorem devWord_of_pointsTo8_memRegion7 (p : BitVec 64) (d : BitVec 8) :
    ((p ↦₈ d) ∗ memRegion (p + 1#64) 7) ⊢
      ∃∗ w3 : BitVec 64, ⌜DevWord d w3⌝ ∗ (p ↦₆₄ w3) := by
  rw [pointsTo8_eq_pointsToBytes, memRegion_eq_exists_bytes (p + 1#64) 7 (by decide),
      sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pad
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hpad
  have h1 : p + 1#64 = p + BitVec.ofNat 64 [d].length := rfl
  rw [h1, ← pointsToBytes_append]
  have hlen8 : ([d] ++ pad).length = 8 := by simp [hpad]
  obtain ⟨w3, hw3⟩ := exists_unpack64_of_length_8 hlen8
  rw [hw3, ← pointsTo64_eq_pointsToBytes]
  refine Entails.sepExists_right w3 ?_
  exact Entails.pure_right ⟨pad, hpad, hw3.symm⟩ (Entails.refl _)

theorem pointsTo64_entails_dev_of_devWord (q : BitVec 64) {d : BitVec 8} {w3 : BitVec 64}
    (h : DevWord d w3) :
    (q ↦₆₄ w3) ⊢ (q ↦₈ d) ∗ memRegion (q + 1#64) 7 := by
  rcases h with ⟨pad, hpad, hw3⟩
  rw [pointsTo64_eq_pointsToBytes, hw3]
  change (q ↦ₛ ([d] ++ pad)) ⊢ _
  rw [pointsToBytes_append]
  have h1 : q + BitVec.ofNat 64 [d].length = q + 1#64 := rfl
  rw [h1, ← pointsTo8_eq_pointsToBytes]
  apply sepConj_mono_right
  have hreg := pointsToBytes_entails_memRegion (q + 1#64) pad
  rwa [hpad] at hreg

theorem speStaged_storeErr (A : RustAlloc) (b ret w6 : BitVec 64) :
    SpeStaged A ret (.store ())
      [0x800000000000001A#64, b + bv% (ls_reloc% 0x77cc), 10#64, 1#64, b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16), w6]
      ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) := by
  refine ⟨by decide, rfl, ?_⟩
  dsimp only [words64At, encErrAt, apiErrAt, strRefAt]
  have h10 : BitVec.ofNat 64 storeHookStr.length = 10#64 := by decide +kernel
  have hword : speWord speApplicationCallback = 0x800000000000001A#64 := rfl
  have ha1 : ret + 8#64 + 8#64 + 8#64 = ret + 8#64 + 0x10#64 := by bv_arith
  have ha2 : ret + 8#64 + 0x10#64 + 8#64 = ret + 8#64 + 0x18#64 := by bv_arith
  have ha3 : ret + 8#64 + 0x18#64 + 8#64 = ret + 8#64 + 0x20#64 := by bv_arith
  have ha4 : ret + 8#64 + 0x20#64 + 8#64 = ret + 8#64 + 0x28#64 := by bv_arith
  rw [ha1, ha2, ha3, ha4, sepConj_emp, hword]
  have hpull :
      (((ret + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
        ((ret + 8#64 + 8#64) ↦₆₄ (b + bv% (ls_reloc% 0x77cc))) ∗
        ((ret + 8#64 + 0x10#64) ↦₆₄ 10#64) ∗
        ((ret + 8#64 + 0x18#64) ↦₆₄ 1#64) ∗
        ((ret + 8#64 + 0x20#64) ↦₆₄ (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
        ((ret + 8#64 + 0x28#64) ↦₆₄ w6)) ∗
        ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) =
      ((ret + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
        (((ret + 8#64 + 8#64) ↦₆₄ (b + bv% (ls_reloc% 0x77cc))) ∗
          ((ret + 8#64 + 8#64 + 8#64) ↦₆₄ 10#64) ∗
          ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)) ∗
        ((ret + 8#64 + 0x18#64) ↦₆₄ 1#64) ∗
        ((ret + 8#64 + 0x20#64) ↦₆₄ (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
        ((ret + 8#64 + 0x28#64) ↦₆₄ w6) := by
    rw [ha1]
    ac_rfl
  rw [hpull]
  refine sepConj_mono_right ?_
  refine sepConj_mono ?_ ?_
  · refine Entails.sepExists_right (b + bv% (ls_reloc% 0x77cc)) ?_
    rw [h10]
    exact Entails.of_eq (by ac_rfl)
  refine sepConj_mono (Entails.sepExists_right 1#64 (Entails.pure_right (by decide) (Entails.refl _))) ?_
  refine sepConj_mono (Entails.sepExists_right (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) (Entails.refl _)) ?_
  exact pointsTo64_entails_memRegion _ _

theorem speStaged_sessionNotFound_devWord (A : RustAlloc) (b ret cap ptr w3 : BitVec 64)
    (a : AddrVal) (hdev : DevWord a.device w3) :
    SpeStaged A ret (.sessionNotFound a "message_encrypt")
      [cap, ptr, BitVec.ofNat 64 a.name.length, w3, b + bv% (ls_xref% 0x3cdb0 0x3cdb4), 15#64]
      (vecU8Buf A cap ptr a.name ∗ ((b + bv% (ls_xref% 0x3cdb0 0x3cdb4)) ↦ᵣ utf8 "message_encrypt")) := by
  refine ⟨by nofun, rfl, ?_⟩
  dsimp only [words64At, encErrAt, apiErrAt, addrCloneAt, strRefAt]
  have h15 : BitVec.ofNat 64 (utf8 "message_encrypt").length = 15#64 := by decide +kernel
  have ha1 : ret + 8#64 + 8#64 + 8#64 = ret + 8#64 + 0x10#64 := by bv_arith
  have ha2 : ret + 8#64 + 0x10#64 + 8#64 = ret + 8#64 + 0x18#64 := by bv_arith
  have ha3 : ret + 8#64 + 0x18#64 + 8#64 = ret + 8#64 + 0x20#64 := by bv_arith
  have ha4 : ret + 8#64 + 0x20#64 + 8#64 = ret + 8#64 + 0x28#64 := by bv_arith
  rw [ha1, ha2, ha3, ha4, sepConj_emp]
  have hvec :
      (((ret + 8#64) ↦₆₄ cap) ∗ ((ret + 8#64 + 8#64) ↦₆₄ ptr) ∗
        ((ret + 8#64 + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
        vecU8Buf A cap ptr a.name) ⊢ vecU8 A (ret + 8#64) a.name := by
    unfold vecU8
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h16 : ret + 8#64 + 16#64 = ret + 8#64 + 0x10#64 := rfl
    rw [h16]
    exact Entails.of_eq (by ac_rfl)
  have hpull :
      (((ret + 8#64) ↦₆₄ cap) ∗
        ((ret + 8#64 + 8#64) ↦₆₄ ptr) ∗
        ((ret + 8#64 + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
        ((ret + 8#64 + 0x18#64) ↦₆₄ w3) ∗
        ((ret + 8#64 + 0x20#64) ↦₆₄ (b + bv% (ls_xref% 0x3cdb0 0x3cdb4))) ∗
        ((ret + 8#64 + 0x28#64) ↦₆₄ 15#64)) ∗
        (vecU8Buf A cap ptr a.name ∗ ((b + bv% (ls_xref% 0x3cdb0 0x3cdb4)) ↦ᵣ utf8 "message_encrypt")) =
      ((((ret + 8#64) ↦₆₄ cap) ∗ ((ret + 8#64 + 8#64) ↦₆₄ ptr) ∗
          ((ret + 8#64 + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
          vecU8Buf A cap ptr a.name) ∗
        ((ret + 8#64 + 0x18#64) ↦₆₄ w3)) ∗
        (((ret + 8#64 + 0x20#64) ↦₆₄ (b + bv% (ls_xref% 0x3cdb0 0x3cdb4))) ∗
          ((ret + 8#64 + 0x20#64 + 8#64) ↦₆₄ 15#64) ∗
          ((b + bv% (ls_xref% 0x3cdb0 0x3cdb4)) ↦ᵣ utf8 "message_encrypt")) := by
    rw [ha4]
    ac_rfl
  rw [hpull]
  refine sepConj_mono ?_ ?_
  · refine Entails.trans (sepConj_mono hvec (pointsTo64_entails_dev_of_devWord _ hdev)) ?_
    have h19 : ret + 8#64 + 0x18#64 + 1#64 = ret + 8#64 + 0x19#64 := by bv_arith
    rw [h19]
    exact Entails.of_eq (by ac_rfl)
  · refine Entails.sepExists_right (b + bv% (ls_xref% 0x3cdb0 0x3cdb4)) ?_
    rw [h15]
    exact Entails.of_eq (by ac_rfl)

/-! ## Decomposition of `loadPollOutAtS` -/

/-- Residual separation-logic payload after extracting the 7 header words and 312-byte tail
from `loadPollOutAtS`. -/
def LoadOutRes (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc) (b : BitVec 64)
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8)))))
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)) : SepProp :=
  match ans with
  | .error () =>
    ⌜w0 = 0xFFFFFFFFFFFFFFFE#64 ∧ w1 = 0x800000000000001A#64 ∧
      w2 = b + bv% (ls_reloc% 0x77cc) ∧ w3 = 10#64 ∧ w4 = 1#64 ∧ w5 = b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)⌝ ∗
      ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)
  | .ok none =>
    ⌜w0 = 0xFFFFFFFFFFFFFFFF#64⌝
  | .ok (some r) =>
    ∃∗ g : RecordGhost,
      ⌜Scope r ∧ g.prevCap.toNat < 2 ^ 63 ∧
        w0 = g.prevCap ∧ w1 = g.prevPtr ∧ w2 = 0#64 ∧ w3 = recordCurCap g ∧
        RecordTailInline g r w4 w5 w6 tail⌝ ∗
        recordHeap A g r

theorem words7_repack_q128 (out w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8))
    (R : SepProp) :
    (recordWords56At out w0 w1 w2 w3 w4 w5 w6 ∗ ((out + 0x38#64) ↦ₛ tail) ∗ R) =
      ((out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
        ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₁₂₈ (w5 ++ w4)) ∗
        ((out + 0x30#64) ↦₆₄ w6) ∗ ((out + 0x38#64) ↦ₛ tail) ∗ R) := by
  unfold recordWords56At
  rw [words3_repack_q128_w64 out w4 w5 w6]
  ac_rfl

theorem loadPollOutAtS_decompose (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (b out : BitVec 64)
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8))))) :
    loadPollOutAtS Scope A b out ans ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ tail : List (BitVec 8),
        ⌜w0 ≠ 0xFFFFFFFFFFFFFFFD#64 ∧ tail.length = 312⌝ ∗
        (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
        ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₁₂₈ (w5 ++ w4)) ∗
        ((out + 0x30#64) ↦₆₄ w6) ∗ ((out + 0x38#64) ↦ₛ tail) ∗
        LoadOutRes Scope A b ans w0 w1 w2 w3 w4 w5 w6 tail := by
  rcases ans with ⟨⟩ | _ | r
  · dsimp only [loadPollOutAtS, LoadOutRes]
    rw [memRegion_split (out + 0x30#64) 8 312 (by decide),
        ProofLib.memRegion_eight (out + 0x30#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [memRegion_eq_exists_bytes (out + 0x38#64) 312 (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro tail
    apply Entails.sepExists_elim; intro w6
    have hpull_err :
        (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((out + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
          ((out + 0x10#64) ↦₆₄ (b + bv% (ls_reloc% 0x77cc))) ∗
          ((out + 0x18#64) ↦₆₄ 10#64) ∗
          ((out + 0x20#64) ↦₆₄ 1#64) ∗
          ((out + 0x28#64) ↦₆₄ (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
          ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
          (((out + 0x30#64) ↦₆₄ w6) ∗ (⌜tail.length = 312⌝ ∗ ((out + 0x38#64) ↦ₛ tail))) =
        ⌜tail.length = 312⌝ ∗
          ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
            ((out + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
            ((out + 0x10#64) ↦₆₄ (b + bv% (ls_reloc% 0x77cc))) ∗
            ((out + 0x18#64) ↦₆₄ 10#64) ∗
            (((out + 0x20#64) ↦₆₄ 1#64) ∗
              ((out + 0x28#64) ↦₆₄ (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
              ((out + 0x30#64) ↦₆₄ w6)) ∗
            ((out + 0x38#64) ↦ₛ tail) ∗
            ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)) := by ac_rfl
    rw [hpull_err]
    apply Entails.pure_left; intro htail
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFE#64
      (Entails.sepExists_right 0x800000000000001A#64
      (Entails.sepExists_right (b + bv% (ls_reloc% 0x77cc))
      (Entails.sepExists_right 10#64
      (Entails.sepExists_right 1#64
      (Entails.sepExists_right (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))
      (Entails.sepExists_right w6
      (Entails.sepExists_right tail ?_)))))))
    rw [words3_repack_q128_w64 out 1#64 (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) w6]
    apply Entails.pure_right ⟨by decide, htail⟩
    have hpull_err2 :
        (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((out + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
          ((out + 0x10#64) ↦₆₄ (b + bv% (ls_reloc% 0x77cc))) ∗
          ((out + 0x18#64) ↦₆₄ 10#64) ∗
          ((out + 0x20#64) ↦₁₂₈ (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16) ++ 1#64)) ∗
          ((out + 0x30#64) ↦₆₄ w6) ∗
          ((out + 0x38#64) ↦ₛ tail) ∗
          (⌜0xFFFFFFFFFFFFFFFE#64 = 0xFFFFFFFFFFFFFFFE#64 ∧
            0x800000000000001A#64 = 0x800000000000001A#64 ∧
            b + bv% (ls_reloc% 0x77cc) = b + bv% (ls_reloc% 0x77cc) ∧ 10#64 = 10#64 ∧
            1#64 = 1#64 ∧ b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16) = b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)⌝ ∗
          ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)) =
        ⌜0xFFFFFFFFFFFFFFFE#64 = 0xFFFFFFFFFFFFFFFE#64 ∧
            0x800000000000001A#64 = 0x800000000000001A#64 ∧
            b + bv% (ls_reloc% 0x77cc) = b + bv% (ls_reloc% 0x77cc) ∧ 10#64 = 10#64 ∧
            1#64 = 1#64 ∧ b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16) = b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)⌝ ∗
          ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
            ((out + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
            ((out + 0x10#64) ↦₆₄ (b + bv% (ls_reloc% 0x77cc))) ∗
            ((out + 0x18#64) ↦₆₄ 10#64) ∗
            (((out + 0x20#64) ↦₁₂₈ (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16) ++ 1#64)) ∗
              ((out + 0x30#64) ↦₆₄ w6)) ∗
            ((out + 0x38#64) ↦ₛ tail) ∗
            ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)) := by ac_rfl
    rw [hpull_err2]
    exact Entails.pure_right ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (Entails.refl _)
  · dsimp only [loadPollOutAtS, LoadOutRes]
    have hc6 : memRegion (out + 8#64) 48 = cells (out + 8#64) 6 :=
      ProofLib.memRegion_cells (out + 8#64) 6 (by decide)
    rw [memRegion_split (out + 8#64) 48 312 (by decide), hc6]
    simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
      memRegion_eq_exists_bytes (out + 0x38#64) 312 (by decide),
      sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro tail
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2
    apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro w5
    apply Entails.sepExists_elim; intro w6
    have hpull_none :
        (out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
          (((out + 8#64) ↦₆₄ w1) ∗
            ((out + 0x10#64) ↦₆₄ w2) ∗
            ((out + 0x18#64) ↦₆₄ w3) ∗
            ((out + 0x20#64) ↦₆₄ w4) ∗
            ((out + 0x28#64) ↦₆₄ w5) ∗
            ((out + 0x30#64) ↦₆₄ w6)) ∗
          (⌜tail.length = 312⌝ ∗ ((out + 0x38#64) ↦ₛ tail)) =
        ⌜tail.length = 312⌝ ∗
          ((out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
            ((out + 8#64) ↦₆₄ w1) ∗
            ((out + 0x10#64) ↦₆₄ w2) ∗
            ((out + 0x18#64) ↦₆₄ w3) ∗
            (((out + 0x20#64) ↦₆₄ w4) ∗
              ((out + 0x28#64) ↦₆₄ w5) ∗
              ((out + 0x30#64) ↦₆₄ w6)) ∗
            ((out + 0x38#64) ↦ₛ tail)) := by ac_rfl
    rw [hpull_none]
    apply Entails.pure_left; intro htail
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFF#64
      (Entails.sepExists_right w1 (Entails.sepExists_right w2
      (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.sepExists_right w6
      (Entails.sepExists_right tail ?_)))))))
    rw [words3_repack_q128_w64 out w4 w5 w6]
    apply Entails.pure_right ⟨by decide, htail⟩
    have hpull_none2 :
        (out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
          ((out + 8#64) ↦₆₄ w1) ∗
          ((out + 0x10#64) ↦₆₄ w2) ∗
          ((out + 0x18#64) ↦₆₄ w3) ∗
          ((out + 0x20#64) ↦₁₂₈ (w5 ++ w4)) ∗
          ((out + 0x30#64) ↦₆₄ w6) ∗
          ((out + 0x38#64) ↦ₛ tail) ∗
          ⌜0xFFFFFFFFFFFFFFFF#64 = 0xFFFFFFFFFFFFFFFF#64⌝ =
        ⌜0xFFFFFFFFFFFFFFFF#64 = 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          ((out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
            ((out + 8#64) ↦₆₄ w1) ∗
            ((out + 0x10#64) ↦₆₄ w2) ∗
            ((out + 0x18#64) ↦₆₄ w3) ∗
            (((out + 0x20#64) ↦₁₂₈ (w5 ++ w4)) ∗
              ((out + 0x30#64) ↦₆₄ w6)) ∗
            ((out + 0x38#64) ↦ₛ tail)) := by ac_rfl
    rw [hpull_none2]
    exact Entails.pure_right rfl (Entails.refl _)
  · dsimp only [loadPollOutAtS, LoadOutRes]
    apply Entails.pure_left; intro hscope
    apply Entails.sepExists_elim; intro g
    rw [sessionRecordAt_eq_words56_sep_tail A out g r]
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro w5
    apply Entails.sepExists_elim; intro w6
    apply Entails.sepExists_elim; intro tail
    apply Entails.pure_left; intro htail_inl
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (recordHeap_prevCap_lt_two_pow_63 A g r))) ?_
    have hpull :
        recordWords56At out g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
          ((out + 0x38#64) ↦ₛ tail) ∗ (⌜g.prevCap.toNat < 2 ^ 63⌝ ∗ recordHeap A g r) =
        ⌜g.prevCap.toNat < 2 ^ 63⌝ ∗
          (recordWords56At out g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
            ((out + 0x38#64) ↦ₛ tail) ∗ recordHeap A g r) := by ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hcap_lt
    have hne := (ne_neg_tags_of_lt_two_pow_63 hcap_lt).2.2
    refine Entails.sepExists_right g.prevCap
      (Entails.sepExists_right g.prevPtr
      (Entails.sepExists_right 0#64
      (Entails.sepExists_right (recordCurCap g)
      (Entails.sepExists_right w4
      (Entails.sepExists_right w5
      (Entails.sepExists_right w6
      (Entails.sepExists_right tail ?_)))))))
    rw [words7_repack_q128]
    apply Entails.pure_right ⟨hne, htail_inl.1⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))))))
    refine Entails.sepExists_right g ?_
    exact Entails.pure_right ⟨hscope, hcap_lt, rfl, rfl, rfl, rfl, htail_inl⟩ (Entails.refl _)

/-! ## Stack, Frame, and `currentSession` Branch Helpers -/

theorem pointsTo16_zero_eq_pointsTo8_pair (a : BitVec 64) :
    (a ↦₁₆ 0#16) = ((a ↦₈ 0#8) ∗ ((a + 1#64) ↦₈ 0#8)) :=
  pointsTo16_split8 a 0#16

theorem encSavedRegs_fold (sp0 : BitVec 64) (s0 : State) :
    ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
      encSavedRegs sp0 s0 :=
  Entails.refl _

theorem stackAt_split_top (sp : BitVec 64) (n m : Nat) (h : n + m ≤ 2 ^ 64) :
    stackAt sp (n + m) =
      stackAt (sp - BitVec.ofNat 64 m) n ∗ memRegion (sp - BitVec.ofNat 64 m) m := by
  simp only [stackAt]
  rw [memRegion_split _ n m h]
  have e1 : sp - BitVec.ofNat 64 (n + m) = sp - BitVec.ofNat 64 m - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + m) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 m := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

theorem encSubStackV_le_two_pow_64 {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    {sp0 : BitVec 64} (hsp : withStoresEncStackV kit ikit ≤ sp0.toNat) :
    encSubStackV kit ikit ≤ 2 ^ 64 := by
  have hlt := sp0.isLt
  unfold withStoresEncStackV encFrameSize at hsp
  omega

theorem stackAt_withStoresEncStack_split {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp0 : BitVec 64) (hsp : withStoresEncStackV kit ikit ≤ sp0.toNat) :
    stackAt sp0 (withStoresEncStackV kit ikit) =
      stackAt (sp0 - 0xbe0#64) (encSubStackV kit ikit) ∗
      memRegion (sp0 - 0xbe0#64) 0xb80 ∗
      cells (sp0 - 96#64) 12 := by
  have hlt := sp0.isLt
  have hsp' : encSubStackV kit ikit + 3040 ≤ sp0.toNat := hsp
  have h1 := ProofLib.stackAt_split_cells sp0 (encSubStackV kit ikit + 0xb80) 12 (by omega)
  rw [show encSubStackV kit ikit + 0xb80 + 8 * 12 = withStoresEncStackV kit ikit by
    unfold withStoresEncStackV encFrameSize; omega] at h1
  have h2 := stackAt_split_top (sp0 - 96#64) (encSubStackV kit ikit) 0xb80 (by omega)
  rw [show (sp0 - 96#64) - BitVec.ofNat 64 0xb80 = sp0 - 0xbe0#64 by bv_omega] at h2
  rw [h1, h2, sepConj_assoc]

theorem memRegion_0xb80_split (sp : BitVec 64) :
    memRegion sp 0xb80 =
      (∃∗ v0 : BitVec 64, (sp ↦₆₄ v0)) ∗
      memRegion (sp + 8#64) 0x48 ∗
      (∃∗ v50 : BitVec 64, ((sp + 0x50#64) ↦₆₄ v50)) ∗
      (∃∗ v58 : BitVec 64, ((sp + 0x58#64) ↦₆₄ v58)) ∗
      (∃∗ v60 : BitVec 32, ((sp + 0x60#64) ↦₃₂ v60)) ∗
      memRegion (sp + 0x64#64) 4 ∗
      cells (sp + 0x68#64) 18 ∗
      (∃∗ vf8 : BitVec 32, ((sp + 0xf8#64) ↦₃₂ vf8)) ∗
      memRegion (sp + 0xfc#64) 4 ∗
      cells (sp + 0x100#64) 2 ∗
      memRegion (sp + 0x110#64) 0x358 ∗
      (∃∗ v468 : BitVec 16, ((sp + 0x468#64) ↦₁₆ v468)) ∗
      memRegion (sp + 0x46a#64) 6 ∗
      cells (sp + 0x470#64) 5 ∗
      memRegion (sp + 0x498#64) 0xe8 ∗
      memRegion (sp + 0x580#64) 368 ∗
      memRegion (sp + 0x6f0#64) 8 ∗
      memRegion (sp + 0x6f8#64) 312 ∗
      (∃∗ q830 : BitVec 128, ((sp + 0x830#64) ↦₁₂₈ q830)) ∗
      (∃∗ v840 : BitVec 64, ((sp + 0x840#64) ↦₆₄ v840)) ∗
      memRegion (sp + 0x848#64) 0x338 := by
  have hc18 : memRegion (sp + 0x68#64) 0x90 = cells (sp + 0x68#64) 18 :=
    ProofLib.memRegion_cells (sp + 0x68#64) 18 (by decide)
  have hc2 : memRegion (sp + 0x100#64) 0x10 = cells (sp + 0x100#64) 2 :=
    ProofLib.memRegion_cells (sp + 0x100#64) 2 (by decide)
  have hc5 : memRegion (sp + 0x470#64) 0x28 = cells (sp + 0x470#64) 5 :=
    ProofLib.memRegion_cells (sp + 0x470#64) 5 (by decide)
  rw [memRegion_split sp 8 0xb78 (by decide),
      memRegion_split (sp + 8#64) 0x48 0xb30 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64) 8 0xb28 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64) 8 0xb20 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64) 4 0xb1c (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64) 4 0xb18 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64) 0x90 0xa88 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64 + 0x90#64) 4 0xa84 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64 + 0x90#64 + 4#64) 4 0xa80 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64 + 0x90#64 + 4#64 + 4#64) 0x10 0xa70 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64 + 0x90#64 + 4#64 + 4#64 + 0x10#64) 0x358 0x718 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64 + 0x90#64 + 4#64 + 4#64 + 0x10#64 + 0x358#64) 2 0x716 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64 + 0x90#64 + 4#64 + 4#64 + 0x10#64 + 0x358#64 + 2#64) 6 0x710 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64 + 0x90#64 + 4#64 + 4#64 + 0x10#64 + 0x358#64 + 2#64 + 6#64) 0x28 0x6e8 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64 + 0x90#64 + 4#64 + 4#64 + 0x10#64 + 0x358#64 + 2#64 + 6#64 + 0x28#64) 0xe8 0x600 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64 + 0x90#64 + 4#64 + 4#64 + 0x10#64 + 0x358#64 + 2#64 + 6#64 + 0x28#64 + 0xe8#64) 368 0x490 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64 + 0x90#64 + 4#64 + 4#64 + 0x10#64 + 0x358#64 + 2#64 + 6#64 + 0x28#64 + 0xe8#64 + 368#64) 8 0x488 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64 + 0x90#64 + 4#64 + 4#64 + 0x10#64 + 0x358#64 + 2#64 + 6#64 + 0x28#64 + 0xe8#64 + 368#64 + 8#64) 312 0x350 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64 + 0x90#64 + 4#64 + 4#64 + 0x10#64 + 0x358#64 + 2#64 + 6#64 + 0x28#64 + 0xe8#64 + 368#64 + 8#64 + 312#64) 16 0x340 (by decide),
      memRegion_split (sp + 8#64 + 0x48#64 + 8#64 + 8#64 + 4#64 + 4#64 + 0x90#64 + 4#64 + 4#64 + 0x10#64 + 0x358#64 + 2#64 + 6#64 + 0x28#64 + 0xe8#64 + 368#64 + 8#64 + 312#64 + 16#64) 8 0x338 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight sp,
      ProofLib.memRegion_eight (sp + 0x50#64),
      ProofLib.memRegion_eight (sp + 0x58#64),
      ProofLib.memRegion_four (sp + 0x60#64),
      hc18,
      ProofLib.memRegion_four (sp + 0xf8#64),
      hc2,
      ProofLib.memRegion_two (sp + 0x468#64),
      hc5,
      memRegion_sixteen (sp + 0x830#64),
      ProofLib.memRegion_eight (sp + 0x840#64)]

theorem loadShimStack_le_encSubStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    kit.loadShimStack ≤ encSubStackV kit ikit := by
  unfold encSubStackV
  omega

theorem loadPollStack_le_encSubStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    kit.loadPollStack ≤ encSubStackV kit ikit := by
  unfold encSubStackV
  omega

theorem allocHookStack_le_encSubStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    allocHookStack ≤ encSubStackV kit ikit := by
  have h1 : allocHookStack ≤ encSubStack := by decide
  have h2 := encSubStack_le_encSubStackV kit ikit
  omega

theorem stack_encSubV_split {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (k : Nat) (hk : k ≤ encSubStackV kit ikit)
    (hsub : encSubStackV kit ikit ≤ 2 ^ 64) :
    stackAt sp (encSubStackV kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - k) ∗
        stackAt sp k := by
  have h := stackAt_split_bottom sp k (encSubStackV kit ikit - k) (by omega)
  rwa [Nat.add_sub_of_le hk] at h

theorem stack_encSub_shim {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hsub : encSubStackV kit ikit ≤ 2 ^ 64) :
    stackAt sp (encSubStackV kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
        stackAt sp kit.loadShimStack :=
  stack_encSubV_split kit ikit sp kit.loadShimStack (loadShimStack_le_encSubStackV kit ikit) hsub

theorem stack_encSub_shim_to_poll {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hsub : encSubStackV kit ikit ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
        stackAt sp kit.loadShimStack =
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
        stackAt sp kit.loadPollStack :=
  (stack_encSub_shim kit ikit sp hsub).symm.trans
    (stack_encSubV_split kit ikit sp kit.loadPollStack (loadPollStack_le_encSubStackV kit ikit) hsub)

theorem stack_encSub_clone (sp : BitVec 64) :
    stackAt sp encSubStack =
      memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - 80) ∗
        stackAt sp 80 := by
  have h := stackAt_split_bottom sp 80 (encSubStack - 80) (by decide)
  rwa [show 80 + (encSubStack - 80) = encSubStack by decide] at h

theorem stack_encSub_clone_back (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - 80) ∗
        stackAt sp 80 =
      stackAt sp encSubStack :=
  (stack_encSub_clone sp).symm

theorem curSession_none_of_recordTailInline {g : RecordGhost}
    {r : SessionRecord (List (BitVec 8))} {w4 w5 w6 : BitVec 64} {tail : List (BitVec 8)}
    (hinl : RecordTailInline g r w4 w5 w6 tail) (hr : r.currentSession = none) :
    g.cur = none ∧ recordCurCap g = 0xFFFFFFFFFFFFFFFF#64 := by
  rcases hinl with ⟨_, hcur⟩
  rw [hr] at hcur
  cases hg : g.cur with
  | none =>
    refine ⟨rfl, ?_⟩
    simp [recordCurCap, hg, noneCap]
  | some G =>
    rw [hg] at hcur
    exact False.elim hcur

theorem curSession_some_of_recordTailInline {A : RustAlloc} {g : RecordGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {w4 w5 w6 : BitVec 64} {tail : List (BitVec 8)}
    (hinl : RecordTailInline g r w4 w5 w6 tail) (hr : r.currentSession = some sess) :
    recordHeap A g r ⊢ ⌜recordCurCap g ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗ recordHeap A g r := by
  rcases hinl with ⟨_, hcur⟩
  rw [hr] at hcur
  cases hg : g.cur with
  | none =>
    rw [hg] at hcur
    exact False.elim hcur
  | some G =>
    refine Entails.trans (recordHeap_curCap_lt_two_pow_63_of_some A g r G sess hg hr) ?_
    apply Entails.pure_left; intro hlt
    exact Entails.pure_right (ne_neg_tags_of_lt_two_pow_63 hlt).1 (Entails.refl _)

theorem enc_adrp_0x4d6a0 {img : Obj.Image} {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (k : BitVec 64)
    (hk : k = 0x1d8#64 ∨ k = 0x43c#64) :
    (((libsignalSessionCode.rebase img.base H).fnAddr encryptWithStoresName + k) &&&
      0xfffffffffffff000#64) +
      (if k = 0x1d8#64
       then bv% (page% (ls_xref% 0x3cdb0 0x3cdb4) - 0x3c000)
       else bv% (page% (ls_xref% 0x3cdb0 0x3cdb4) - 0x3d000)) +
      bv% ((ls_xref% 0x3cdb0 0x3cdb4) % 4096) = img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4) := by
  have hb := ProofLib.ObjectLoad.base_aligned_of_loads himg
  rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x3cbd8, BitVec.add_assoc img.base,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rcases hk with rfl | rfl <;> simp only [↓reduceIte, BitVec.reduceEq] <;> bv_arith

/-- Prefix of `encSpillsAtV` (`sp + 0x58 .. sp + 0x108`), leaving `[sp + 0x108] = x.remA`
exposed for reload. -/
def encSpillsInit (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) : SepProp :=
  ((sp + 0x58#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0x60#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0x64#64) 4 ∗ ((sp + 0x68#64) ↦₆₄ x.ptA) ∗
  ((sp + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0x78#64) ↦₆₄ x.remA) ∗
  ((sp + 0x80#64) ↦₆₄ x.locA) ∗ ((sp + 0x88#64) ↦₆₄ x.ssA) ∗ ((sp + 0x90#64) ↦₆₄ ss_vt) ∗
  ((sp + 0x98#64) ↦₆₄ x.idA) ∗ ((sp + 0xa0#64) ↦₆₄ id_vt) ∗
  ((sp + 0xa8#64) ↦₆₄ (sp + 0xb6f#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
  ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
  ((sp + 0xc8#64) ↦₆₄ x.locA) ∗ ((sp + 0xd0#64) ↦₆₄ x.ssA) ∗ ((sp + 0xd8#64) ↦₆₄ ss_vt) ∗
  ((sp + 0xe0#64) ↦₆₄ x.idA) ∗ ((sp + 0xe8#64) ↦₆₄ id_vt) ∗
  ((sp + 0xf0#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0xf8#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0xfc#64) 4 ∗ ((sp + 0x100#64) ↦₆₄ (sp + 0xb6f#64))

theorem encSpillsInit_fold (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) :
    ((sp + 0x58#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0x60#64) ↦₃₂ x.now.tvNsec) ∗
    memRegion (sp + 0x64#64) 4 ∗ ((sp + 0x68#64) ↦₆₄ x.ptA) ∗
    ((sp + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0x78#64) ↦₆₄ x.remA) ∗
    ((sp + 0x80#64) ↦₆₄ x.locA) ∗ ((sp + 0x88#64) ↦₆₄ x.ssA) ∗ ((sp + 0x90#64) ↦₆₄ ss_vt) ∗
    ((sp + 0x98#64) ↦₆₄ x.idA) ∗ ((sp + 0xa0#64) ↦₆₄ id_vt) ∗
    ((sp + 0xa8#64) ↦₆₄ (sp + 0xb6f#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
    ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
    ((sp + 0xc8#64) ↦₆₄ x.locA) ∗ ((sp + 0xd0#64) ↦₆₄ x.ssA) ∗ ((sp + 0xd8#64) ↦₆₄ ss_vt) ∗
    ((sp + 0xe0#64) ↦₆₄ x.idA) ∗ ((sp + 0xe8#64) ↦₆₄ id_vt) ∗
    ((sp + 0xf0#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0xf8#64) ↦₃₂ x.now.tvNsec) ∗
    memRegion (sp + 0xfc#64) 4 ∗ ((sp + 0x100#64) ↦₆₄ (sp + 0xb6f#64)) ⊢
      encSpillsInit ss_vt id_vt sp x :=
  Entails.refl _

theorem encSpillsAt_fold (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) :
    encSpillsInit ss_vt id_vt sp x ∗ ((sp + 0x108#64) ↦₆₄ x.remA) ⊢
      encSpillsAtV ss_vt id_vt sp x :=
  Entails.of_eq (by unfold encSpillsAtV encSpillsInit; ac_rfl)

theorem nowAt_fold (sp0 : BitVec 64) (t : SystemTime) :
    (sp0 ↦₆₄ t.tvSec) ∗ ((sp0 + 8#64) ↦₃₂ t.tvNsec) ∗ memRegion (sp0 + 12#64) 4 ⊢
      nowAt sp0 t :=
  Entails.refl _

theorem fold_sp50 (sp v0 : BitVec 64) :
    (sp ↦₆₄ v0) ∗ memRegion (sp + 8#64) 0x48 ⊢ memRegion sp 0x50 := by
  rw [memRegion_split sp 8 0x48 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)

theorem fold_sp58 (sp v50 : BitVec 64) :
    memRegion sp 0x50 ∗ ((sp + 0x50#64) ↦₆₄ v50) ⊢ memRegion sp 0x58 := by
  rw [memRegion_split sp 0x50 8 (by decide)]
  exact sepConj_mono_right (pointsTo64_entails_memRegion _ _)

theorem fold_46a_498 (sp v0 v1 v2 v3 v4 : BitVec 64) :
    memRegion (sp + 0x46a#64) 6 ∗
    ((sp + 0x470#64) ↦₆₄ v0) ∗ ((sp + 0x478#64) ↦₆₄ v1) ∗
    ((sp + 0x480#64) ↦₆₄ v2) ∗ ((sp + 0x488#64) ↦₆₄ v3) ∗
    ((sp + 0x490#64) ↦₆₄ v4) ∗ memRegion (sp + 0x498#64) 0xe8 ⊢
      memRegion (sp + 0x46a#64) 0x116 := by
  have hc5 : memRegion (sp + 0x470#64) 0x28 = cells (sp + 0x470#64) 5 :=
    ProofLib.memRegion_cells (sp + 0x470#64) 5 (by decide)
  rw [memRegion_split (sp + 0x46a#64) 6 0x110 (by decide),
      memRegion_split (sp + 0x46a#64 + 6#64) 0x28 0xe8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hc5]
  have hpull :
      memRegion (sp + 0x46a#64) 6 ∗
        ((sp + 0x470#64) ↦₆₄ v0) ∗ ((sp + 0x478#64) ↦₆₄ v1) ∗
        ((sp + 0x480#64) ↦₆₄ v2) ∗ ((sp + 0x488#64) ↦₆₄ v3) ∗
        ((sp + 0x490#64) ↦₆₄ v4) ∗ memRegion (sp + 0x498#64) 0xe8 =
      memRegion (sp + 0x46a#64) 6 ∗
        (((sp + 0x470#64) ↦₆₄ v0) ∗ ((sp + 0x478#64) ↦₆₄ v1) ∗
          ((sp + 0x480#64) ↦₆₄ v2) ∗ ((sp + 0x488#64) ↦₆₄ v3) ∗
          ((sp + 0x490#64) ↦₆₄ v4)) ∗
        memRegion (sp + 0x498#64) 0xe8 := by ac_rfl
  rw [hpull]
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  refine sepConj_mono_right (sepConj_mono_left ?_)
  exact Entails.sepExists_right v0 (sepConj_mono_right
    (Entails.sepExists_right v1 (sepConj_mono_right
      (Entails.sepExists_right v2 (sepConj_mono_right
        (Entails.sepExists_right v3 (sepConj_mono_right
          (Entails.sepExists_right v4 (Entails.refl _)))))))))

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

