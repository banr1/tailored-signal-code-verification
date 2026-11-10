/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Decode lemmas (`0x3a4a8 .. 0x3a530`, 35 instructions) -/

gen_decodes libsignalSessionCode_tree messageDecryptLoadBin [(ls_off% "session_message_decrypt_signal") → (ls_off% "session_message_decrypt_signal" + 136)]

/-! ## 2. Frame & Stack Helpers -/

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

theorem stackAt_wsStack_split (sp0 : BitVec 64) :
    stackAt sp0 wsStack =
      stackAt (sp0 - 0xee0#64) wsCalleeStack ∗
      memRegion (sp0 - 0xee0#64) 0xe80 ∗
      cells (sp0 - 96#64) 12 := by
  have h1 := ProofLib.stackAt_split_cells sp0 (wsStack - 96) 12 (by decide)
  rw [show wsStack - 96 + 8 * 12 = wsStack by decide] at h1
  have h2 := stackAt_split_top (sp0 - 96#64) wsCalleeStack 0xe80 (by decide)
  rw [show wsCalleeStack + 0xe80 = wsStack - 96 by decide,
      show (sp0 - 96#64) - BitVec.ofNat 64 0xe80 = sp0 - 0xee0#64 by bv_omega] at h2
  rw [h1, h2, sepConj_assoc]

theorem memRegion_0xe80_split (sp : BitVec 64) :
    memRegion sp 0xe80 =
      (∃∗ v0 : BitVec 64, (sp ↦₆₄ v0)) ∗
      memRegion (sp + 8#64) 0x98 ∗
      cells (sp + 0xa0#64) 16 ∗
      memRegion (sp + 0x120#64) 0x1a8 ∗
      (∃∗ b2c8 : BitVec 8, ((sp + 0x2c8#64) ↦₈ b2c8)) ∗
      memRegion (sp + 0x2c9#64) 7 ∗
      cells (sp + 0x2d0#64) 5 ∗
      memRegion (sp + 0x2f8#64) 8 ∗
      memRegion (sp + 0x300#64) 0x1b0 ∗
      memRegion (sp + 0x4b0#64) 0x140 ∗
      memRegion (sp + 0x5f0#64) 368 ∗
      memRegion (sp + 0x760#64) 0x6a0 ∗
      memRegion (sp + 0xe00#64) 0x80 := by
  have hc16 : memRegion (sp + 0xa0#64) 0x80 = cells (sp + 0xa0#64) 16 :=
    ProofLib.memRegion_cells (sp + 0xa0#64) 16 (by decide)
  have hc5 : memRegion (sp + 0x2d0#64) 0x28 = cells (sp + 0x2d0#64) 5 :=
    ProofLib.memRegion_cells (sp + 0x2d0#64) 5 (by decide)
  rw [memRegion_split sp 8 0xe78 (by decide),
      memRegion_split (sp + 8#64) 0x98 0xde0 (by decide),
      memRegion_split (sp + 8#64 + 0x98#64) 0x80 0xd60 (by decide),
      memRegion_split (sp + 8#64 + 0x98#64 + 0x80#64) 0x1a8 0xbb8 (by decide),
      memRegion_split (sp + 8#64 + 0x98#64 + 0x80#64 + 0x1a8#64) 1 0xbb7 (by decide),
      memRegion_split (sp + 8#64 + 0x98#64 + 0x80#64 + 0x1a8#64 + 1#64) 7 0xbb0 (by decide),
      memRegion_split (sp + 8#64 + 0x98#64 + 0x80#64 + 0x1a8#64 + 1#64 + 7#64) 0x28 0xb88 (by decide),
      memRegion_split (sp + 8#64 + 0x98#64 + 0x80#64 + 0x1a8#64 + 1#64 + 7#64 + 0x28#64) 8 0xb80 (by decide),
      memRegion_split (sp + 8#64 + 0x98#64 + 0x80#64 + 0x1a8#64 + 1#64 + 7#64 + 0x28#64 + 8#64) 0x1b0 0x9d0 (by decide),
      memRegion_split (sp + 8#64 + 0x98#64 + 0x80#64 + 0x1a8#64 + 1#64 + 7#64 + 0x28#64 + 8#64 + 0x1b0#64) 0x140 0x890 (by decide),
      memRegion_split (sp + 8#64 + 0x98#64 + 0x80#64 + 0x1a8#64 + 1#64 + 7#64 + 0x28#64 + 8#64 + 0x1b0#64 + 0x140#64) 368 0x720 (by decide),
      memRegion_split (sp + 8#64 + 0x98#64 + 0x80#64 + 0x1a8#64 + 1#64 + 7#64 + 0x28#64 + 8#64 + 0x1b0#64 + 0x140#64 + 368#64) 0x6a0 0x80 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight sp, memRegion_one (sp + 0x2c8#64), hc16, hc5]

theorem fold_words8 (a v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
    ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7) ⊢
      memRegion a 0x40 := by
  have hc : memRegion a 0x40 = cells a 8 := ProofLib.memRegion_cells a 8 (by decide)
  rw [hc]
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 (sepConj_mono_right (Entails.sepExists_right v1 (sepConj_mono_right
    (Entails.sepExists_right v2 (sepConj_mono_right (Entails.sepExists_right v3 (sepConj_mono_right
      (Entails.sepExists_right v4 (sepConj_mono_right (Entails.sepExists_right v5 (sepConj_mono_right
        (Entails.sepExists_right v6 (sepConj_mono_right
          (Entails.sepExists_right v7 (Entails.refl _)))))))))))))))

theorem fold_2e0 (sp v0 v1 v2 : BitVec 64) :
    ((sp + 0x2e0#64) ↦₆₄ v0) ∗ ((sp + 0x2e8#64) ↦₆₄ v1) ∗ ((sp + 0x2f0#64) ↦₆₄ v2) ∗
      memRegion (sp + 0x2f8#64) 8 ⊢
    memRegion (sp + 0x2e0#64) 0x20 := by
  have hc : memRegion (sp + 0x2e0#64) 24 = cells (sp + 0x2e0#64) 3 :=
    ProofLib.memRegion_cells (sp + 0x2e0#64) 3 (by decide)
  rw [memRegion_split (sp + 0x2e0#64) 24 8 (by decide), hc]
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
    ← sepConj_assoc]
  refine sepConj_mono_left ?_
  rw [sepConj_assoc]
  exact Entails.sepExists_right v0 (sepConj_mono_right
    (Entails.sepExists_right v1 (sepConj_mono_right (Entails.sepExists_right v2 (Entails.refl _)))))

theorem fold_2c8 (sp : BitVec 64) (b0 : BitVec 8) :
    ((sp + 0x2c8#64) ↦₈ b0) ∗ memRegion (sp + 0x2c9#64) 7 ⊢
    memRegion (sp + 0x2c8#64) 8 := by
  rw [memRegion_split (sp + 0x2c8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)

theorem fold_sp0 (sp v0 : BitVec 64) :
    (sp ↦₆₄ v0) ∗ memRegion (sp + 8#64) 0x98 ⊢ memRegion sp 0xa0 := by
  rw [memRegion_split sp 8 0x98 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)

theorem stackAt_wsStackV_split {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp0 : BitVec 64) (hbound : wsStackV kit ikit ≤ sp0.toNat) :
    stackAt sp0 (wsStackV kit ikit) =
      stackAt (sp0 - 0xee0#64) (wsCalleeStackV kit ikit) ∗
      memRegion (sp0 - 0xee0#64) 0xe80 ∗
      cells (sp0 - 96#64) 12 := by
  have hlt := sp0.isLt
  have hle : wsCalleeStack ≤ wsCalleeStackV kit ikit := wsCalleeStack_le_V kit ikit
  have hframe : wsFrame = 0xee0 := rfl
  have hstack_eq : wsStackV kit ikit = wsCalleeStackV kit ikit + 0xee0 := rfl
  have h1 := ProofLib.stackAt_split_cells sp0 (wsStackV kit ikit - 96) 12 (by omega)
  rw [show wsStackV kit ikit - 96 + 8 * 12 = wsStackV kit ikit by omega] at h1
  have h2 := stackAt_split_top (sp0 - 96#64) (wsCalleeStackV kit ikit) 0xe80 (by omega)
  rw [show wsCalleeStackV kit ikit + 0xe80 = wsStackV kit ikit - 96 by omega,
      show (sp0 - 96#64) - BitVec.ofNat 64 0xe80 = sp0 - 0xee0#64 by bv_omega] at h2
  rw [h1, h2, sepConj_assoc]

theorem stack_wsCalleeV_shim {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hn : wsCalleeStackV kit ikit ≤ 2 ^ 64) :
    stackAt sp (wsCalleeStackV kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - kit.loadShimStack) ∗
        stackAt sp kit.loadShimStack :=
  stack_wsCalleeV_sub sp (loadShimStack_le_V kit ikit) hn

theorem stack_wsCalleeV_shim_to_poll {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hn : wsCalleeStackV kit ikit ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - kit.loadShimStack) ∗
        stackAt sp kit.loadShimStack =
      memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - kit.loadPollStack) ∗
        stackAt sp kit.loadPollStack := by
  rw [← stack_wsCalleeV_shim kit ikit sp hn]
  exact stack_wsCalleeV_sub sp (loadPollStack_le_V kit ikit) hn

theorem stack_wsCalleeV_poll_back {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hn : wsCalleeStackV kit ikit ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - kit.loadPollStack) ∗
        stackAt sp kit.loadPollStack =
      stackAt sp (wsCalleeStackV kit ikit) :=
  (stack_wsCalleeV_sub sp (loadPollStack_le_V kit ikit) hn).symm

/-! ## 3. `SepWPp` / `DecSeg` Infrastructure -/

structure FrozenInv (img : Obj.Image) (s : State) : Prop where
  frozen : img.FrozenLoaded s
  symtab : s.symtab = img.symtab

theorem FrozenInv.of_steps {prog : Program} {img : Obj.Image} {s sf : State}
    (h : FrozenInv img s) (hsteps : Steps prog s sf) : FrozenInv img sf :=
  ⟨h.1.of_keepsFrozen hsteps.keepsFrozen, hsteps.symtab_eq.trans h.2⟩

theorem messageDecrypt_of_sepWP_frozen {prog : Program} {img : Obj.Image} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : FrozenInv img s)
    (h : SepWP prog mid s P
      (fun sm Pm => FrozenInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := h.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ :=
    hnext (hF.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem messageDecrypt_call_panic_then_wp_frozen {α : Type} {prog : Program} {img : Obj.Image}
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
  refine SepWPp.call_wpp_frozen hcall hF.1 hF.2 hpc hrun hsp_align hlr hpre
    (fun _ _ _ _ hex => by rw [hexit_eq] at hex; exact not_satisfies_false_sepConj hex)
    (fun sm _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm')
    (fun sm hpcm hrunm hspm hcsm hfz hsym R' hpost hL => ?_)
    (fun sm R' hoom_st hoom_post => (hoom sm (F ∗ R') hoom_st hoom_post).elim)
  have hFm : FrozenInv img sm := ⟨hfz, hsym⟩
  obtain ⟨sf, hsteps', ⟨hpc', hrun', P_f, hmf, hq⟩ | ⟨_, _hoom⟩⟩ :=
    (hnext sm hpcm hrunm hspm hcsm).elim hpost hL
  · exact ⟨sf, hsteps', Or.inl ⟨hpc', hrun', P_f, hmf, hq (hFm.of_steps hsteps')⟩⟩
  · exact (not_satisfies_false_sepConj _hoom).elim

theorem messageDecrypt_call_panic_then_wpp_frozen {α : Type} {prog : Program} {img : Obj.Image}
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
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) :=
  SepWPp.call_wpp_frozen hcall hF.1 hF.2 hpc hrun hsp_align hlr hpre
    (fun _ _ _ _ hex => by rw [hexit_eq] at hex; exact not_satisfies_false_sepConj hex)
    (fun sm _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm')
    (fun sm hpcm hrunm hspm hcsm hfz hsym => hnext sm hpcm hrunm hspm hcsm ⟨hfz, hsym⟩)
    (fun sm R' hoom_st hoom_post => (hoom sm (F ∗ R') hoom_st hoom_post).elim)

theorem loadShim_onPanic_entailsV {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).onPanic x s0 sf := by
  dsimp only [withStoresDecSpecV, Spec.inImage]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  unfold allocFailedIn at halloc ⊢
  rw [htr] at halloc hpref
  exact Entails.pure_right ⟨hpref, Or.inl halloc⟩ (entails_anyHeap _)

theorem decSegV_of_sepWPp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (tripleRatchetProgAt img.base C ctl abs) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Out sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).onPanic x s0 sf ∗ R))) :
    DecSegV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem wsSavedRegs_fold (sp0 : BitVec 64) (s0 : State) :
    ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
      wsSavedRegs sp0 s0 :=
  Entails.refl _

set_option maxHeartbeats 1600000 in
theorem segLoadV_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegLoadSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope := by
  intro hH x R s0 hfs hpc hrun hal hpre
  dsimp only [withStoresDecSpecV, Spec.inImage] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrozen, hsym⟩, ⟨hx0, hx1, hx2, hx4, hx6, hx8, hsp_le, haddr_ss, _haddr_id⟩, hmem⟩
  simp only [← sepConj_assoc] at hmem
  simp only [wp_norm, arm64_norm] at hx0 hx1 hx2 hx4 hx6 hx8
  have hentry := entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) hH.loads
    msgDecryptName
  have hfn : libsignalSessionCode.fnOff msgDecryptName = num% (ls_off% "session_message_decrypt_signal") :=
    CryptoVerification.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  unfold wsEntryPC at hpc
  rw [hentry] at hpc
  have hshim := subroutine_ok_withStepsPost_inImage hH.kit.loadShim
  have hpoll := hH.kit.loadPoll
  have hfsAt : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet) (tripleRatchetProgAt img.base C ctl abs) s0 :=
    (hfs.fsAt (evs := []) (List.append_nil _).symm (fun _ => NoFsEv.nil)).mono (fun _ h => h.1) id
  have hF0 : FrozenInv img s0 := ⟨hfrozen, hsym⟩
  have hsp_lt := s0.sp.isLt
  have hn_v : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + 0xee0 := rfl
    omega
  have hsp_base : wsStack ≤ s0.sp.toNat := Nat.le_trans (wsStack_le_V kit ikit) hsp_le
  code_fetches CryptoVerification.libsignalSessionCode messageDecryptLoadBin img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "session_message_decrypt_signal")) 140
  apply decSegV_of_sepWPp (target := loadPolledPC img) hmem
  have hLP : (libsignalSessionCode.rebase img.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr msgDecryptName + 0x8c#64 =
      loadPolledPC img := by
    unfold loadPolledPC
    rw [hentry]
  rw [← hLP]
  dsimp only [tripleRatchetProgAt] at hpc hshim hpoll hfsAt ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr msgDecryptName = entry at *
  examples_hide_fetches
  apply messageDecrypt_of_sepWP_frozen hF0 (mid := img.base + kit.loadShimOff)
  rw [stackAt_wsStackV_split kit ikit s0.sp hsp_le, memRegion_0xe80_split (s0.sp - 0xee0#64),
    stack_wsCalleeV_shim kit ikit (s0.sp - 0xee0#64) hn_v]
  cells_unfold
  unfold decVtablesAtV decLoadVtableAtV decStoreVtableAtV decTrustVtableAtV decSaveVtableAtV
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply SepWP.exists_elim; intro _)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  apply (messageDecrypt_call_panic_then_wpp_frozen hshim (x := ⟨s0.readReg64 (Reg.gpr 3#5), x.remA⟩) hF1)
  · wp_norm_lhs
  · wp_norm_lhs
  · simp only [State.spAligned, wp_norm, arm64_norm]; exact hal
  · wp_norm_lhs
  · intro _R' _hmR'
    refine inImage_pre_intro hF1.1 hF1.2 ?_
    dsimp only [kitLoadShimSpec]
    simp only [sepConj_assoc, wp_norm, arm64_norm, hx1] at _hmR' ⊢
    arm64_sep_close
  · intro _; exact loadShim_onPanic_entailsV (by wp_norm_lhs)
  · intro _ _; rfl
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf hF2
  dsimp only [Spec.inImage, withStepsPost, kitLoadShimSpec]
  simp only [wp_norm, arm64_norm] at hpc_sf hsp_sf
  apply messageDecrypt_of_sepWP_frozen hF2 (mid := img.base + kit.loadPollOff)
  wp_simp_pre [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hbox_ne, hbox_mod, htr_sf⟩
  have henv : kit.envOk sf.fs.files :=
    (hfsAt.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
  clear hsteps_sh hfsAt
  simp only [wp_norm, arm64_norm] at hx1_sf
  apply SepWP.fold (Entails.of_eq (stack_wsCalleeV_shim_to_poll kit ikit (s0.sp - 0xee0#64) hn_v)) (by sep_focus)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF3
  apply (messageDecrypt_call_panic_then_wp_frozen hpoll
    (x := (⟨sf.readReg64 (Reg.gpr 0#5), (s0.sp - 0xee0#64) + 0x5f0#64, x.remA, x.rem⟩,
      s0.readReg64 (Reg.gpr 3#5), st0)) hF3)
  · wp_norm_lhs
  · wp_norm_lhs
  · simp only [State.spAligned, wp_norm, arm64_norm, hsp_sf]; exact hal
  · wp_norm_lhs
  · intro _R' _hmR'
    refine withEnvPre_pre_intro (by simp only [arm64_norm]; exact henv) ?_
    dsimp only [kitLoadPollSpecS]
    simp only [sepConj_assoc, wp_norm, arm64_norm, hsp_sf, haddr_ss, and_true] at _hmR' ⊢
    refine ⟨⟨hF3.1, hF3.2⟩, ?_⟩
    arm64_sep_close
  · intro _; exact loadShim_onPanic_entailsV (by simp only [wp_norm, arm64_norm]; exact htr_sf)
  · intro _ _; rfl
  intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
  dsimp only [kitLoadPollSpecSE, kitLoadPollSpecS]
  simp only [wp_norm, arm64_norm, hsp_sf] at hpc_sf1 hsp_sf1
  wp_simp_pre [wp_norm, arm64_norm, hsp_sf, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w
  apply SepWP.pure_elim; rintro ⟨hloadRel, htr_sf1⟩
  apply SepWP.fold (wsSavedRegs_fold s0.sp s0) (by sep_focus)
  apply SepWP.fold (fold_sp0 (s0.sp - 0xee0#64) 0#64) (by sep_focus)
  apply SepWP.fold (fold_words8 (s0.sp - 0xee0#64 + 0xa0#64)
    x.msgA x.remA x.locA (s0.readReg64 (Reg.gpr 3#5))
    kit.ss_vt (s0.readReg64 (Reg.gpr 5#5))
    ikit.id_vt (s0.sp - 113#64)) (by sep_focus)
  apply SepWP.fold (fold_2c8 (s0.sp - 0xee0#64) 0#8) (by sep_focus)
  apply SepWP.fold (fold_2e0 (s0.sp - 0xee0#64)
    (((entry + bv% (32)) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_reloc% (ls_reloc% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#1]")) - page% (ls_off% "<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent as prost::message::Message>::encoded_len [local#1]" + 56)))
    (((entry + bv% (32)) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_reloc% (ls_reloc% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#1]")) - page% (ls_off% "<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent as prost::message::Message>::encoded_len [local#1]" + 56))) 0#64) (by sep_focus)
  apply SepWP.fold (Entails.of_eq (stack_wsCalleeV_poll_back kit ikit (s0.sp - 0xee0#64) hn_v)) (by sep_focus)
  have hsplit_extra := wsCalleeStack_split_extra kit ikit st0 ist0 s0 hsp_le
  dsimp only [Reg.x3, Reg.x5] at hsplit_extra
  apply SepWP.fold hsplit_extra (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF4 hmf
  refine ⟨⟨w, .ok false, .ok .newOrUnchanged, .ok ()⟩, ?_⟩
  refine ⟨?_, ?_, hsp_base, ?_, hloadRel, ?_, ?_⟩
  · wp_norm_lhs
  · simp only [CalleeSavedPreserved, wp_norm, arm64_norm] at hcs_sf hcs_sf1
    refine ⟨by wp_norm_lhs,
            by simp only [wp_norm, arm64_norm, hsp_sf1],
            hal,
            by simp only [State.spAligned, wp_norm, arm64_norm, hsp_sf1]; exact hal,
            by simp only [wp_norm, arm64_norm, hcs_sf1, hcs_sf],
            by simp only [wp_norm, arm64_norm, hcs_sf1, hcs_sf],
            hF4.1, hF4.2,
            by simp only [wp_norm, arm64_norm, hcs_sf1, hcs_sf]⟩
  · simp only [CalleeSavedPreserved, wp_norm, arm64_norm] at hcs_sf1
    simpa only [Reg.x19, wp_norm, arm64_norm, hsp_sf] using hcs_sf1.1
  · simp only [wp_norm, arm64_norm] at htr_sf1 ⊢
    rw [htr_sf1, htr_sf]
  · dsimp only [LoadPolledStateV, wsFixedV, wsArgCellsV, decVtablesAtV,
      decLoadVtableAtV, decStoreVtableAtV, decTrustVtableAtV, decSaveVtableAtV,
      wsEnv, wsMsgCells, Reg.x3, Reg.x5] at hmf ⊢
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, BitVec.add_assoc] at hmf ⊢
    arm64_sep_close

theorem segLoad_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegLoadSpec img C A ctl uuidTryParse S encRecord abs :=
  segLoadV_ok

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

theorem messageDecrypt_of_sepWP_lscro [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  StoreKit.sepWPp_seq_lscro hF h

theorem messageDecrypt_call_panic_then_wp_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F)
        (fun sf' P_f => StoreKit.LibsignalCodeRoLoaded lsmpl sf'.mem → post sf' P_f))
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call_wpp (StoreKit.subroutine_ok_rocl_of_plain (pl := lsmpl) hcall)
    hpc hrun hsp_align hlr
    (fun R' hm => by
      dsimp only [StoreKit.withLsRoCl]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hF, hpre R' hm⟩)
    (fun _ _ _ _ hex => by dsimp only [StoreKit.withLsRoCl] at hex; rw [hexit_eq] at hex; exact not_satisfies_false_sepConj hex)
    (fun sm _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm')
    (fun sm hpcm hrunm hspm hcsm => ?_)
    (fun sm R' hoom_st hoom_post => (hoom sm (F ∗ R') hoom_st hoom_post).elim)
  dsimp only [StoreKit.withLsRoCl]
  refine SepWPp.congr_pre (sepConj_assoc _ _ _) (SepWPp.pure_left fun hFm R' hpost hL => ?_)
  obtain ⟨sf, hsteps', ⟨hpc', hrun', P_f, hmf, hq⟩ | ⟨_, _hoom⟩⟩ :=
    (hnext sm hpcm hrunm hspm hcsm).elim hpost hL
  · exact ⟨sf, hsteps', Or.inl ⟨hpc', hrun', P_f, hmf, hq (hFm.of_keepsFrozen hsteps'.keepsFrozen)⟩⟩
  · exact (not_satisfies_false_sepConj _hoom).elim

theorem messageDecrypt_call_panic_then_wpp_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ Qpan sf' ∗ R)))
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call_wpp (StoreKit.subroutine_ok_rocl_of_plain (pl := lsmpl) hcall)
    hpc hrun hsp_align hlr
    (fun R' hm => by
      dsimp only [StoreKit.withLsRoCl]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hF, hpre R' hm⟩)
    (fun _ _ _ _ hex => by dsimp only [StoreKit.withLsRoCl] at hex; rw [hexit_eq] at hex; exact not_satisfies_false_sepConj hex)
    (fun sm _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm')
    (fun sm hpcm hrunm hspm hcsm => ?_)
    (fun sm R' hoom_st hoom_post => (hoom sm (F ∗ R') hoom_st hoom_post).elim)
  dsimp only [StoreKit.withLsRoCl]
  exact SepWPp.congr_pre (sepConj_assoc _ _ _) (SepWPp.pure_left fun hFm => hnext sm hpcm hrunm hspm hcsm hFm)

theorem loadShim_onPanic_entailsVPlaced [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).onPanic x s0 sf := by
  dsimp only [withStoresDecPlacedSpecV, StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  unfold allocFailedIn at halloc ⊢
  rw [htr] at halloc hpref
  exact Entails.pure_right ⟨hpref, Or.inl halloc⟩ (entails_anyHeap _)

theorem decSegVPlaced_of_sepWPp [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (lsProg_197 H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Out sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).onPanic x s0 sf ∗ R))) :
    DecSegVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

set_option maxHeartbeats 1600000 in
theorem segLoadVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegLoadSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro hH x R s0 hfs hpc hrun hal hpre
  obtain ⟨hcrl0, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [withStoresDecPlacedSpecV] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx4, hx6, hx8, hsp_le, haddr_ss, _haddr_id⟩, hmem⟩
  simp only [← sepConj_assoc] at hmem
  simp only [wp_norm, arm64_norm] at hx0 hx1 hx2 hx4 hx6 hx8
  unfold wsEntryPCPlaced at hpc
  have hshim := subroutine_ok_withStepsPost
    (hH.kit.loadShim (callerProg := lsProg_197 H) (callerBlk := 197) (by decide))
  have hpoll := hH.kit.loadPoll (callerProg := lsProg_197 H) (callerBlk := 197) (by decide)
  rw [BitVec.zero_add] at hshim hpoll
  have hfsAt : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_197 H) s0 :=
    (hfs.fsAt (evs := []) (List.append_nil _).symm (fun _ => NoFsEv.nil)).mono (fun _ h => h.1) id
  have hsp_lt := s0.sp.isLt
  have hn_v : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + 0xee0 := rfl
    omega
  have hsp_base : wsStack ≤ s0.sp.toNat := Nat.le_trans (wsStack_le_V kit ikit) hsp_le
  apply decSegVPlaced_of_sepWPp (target := loadPolledPCPlaced) hmem
  unfold loadPolledPCPlaced
  dsimp only [lsProg_197] at hshim hpoll hfsAt ⊢
  apply messageDecrypt_of_sepWP_lscro hcrl0 (mid := kit.loadShimOff)
  rw [stackAt_wsStackV_split kit ikit s0.sp hsp_le, memRegion_0xe80_split (s0.sp - 0xee0#64),
    stack_wsCalleeV_shim kit ikit (s0.sp - 0xee0#64) hn_v]
  cells_unfold
  unfold decVtablesAtV decLoadVtableAtV decStoreVtableAtV decTrustVtableAtV decSaveVtableAtV
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply SepWP.exists_elim; intro _)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  apply (messageDecrypt_call_panic_then_wpp_lscro hshim (x := ⟨s0.readReg64 (Reg.gpr 3#5), x.remA⟩) hF1)
  · wp_norm_lhs
  · wp_norm_lhs
  · simp only [State.spAligned, wp_norm, arm64_norm]; exact hal
  · wp_norm_lhs
  · intro _R' _hmR'
    dsimp only [withStepsPost, Arm64.ReachesOutcome.withStepsPost, StoreKit.withLsRoCl, kitLoadShimSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hF1, ?_⟩
    simp only [sepConj_assoc, wp_norm, arm64_norm, hx1] at _hmR' ⊢
    arm64_sep_close
  · intro _; exact loadShim_onPanic_entailsVPlaced (by wp_norm_lhs)
  · intro _ _; rfl
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf hF2
  dsimp only [withStepsPost, Arm64.ReachesOutcome.withStepsPost, StoreKit.withLsRoCl, kitLoadShimSpec]
  simp only [wp_norm, arm64_norm] at hpc_sf hsp_sf
  apply messageDecrypt_of_sepWP_lscro hF2 (mid := kit.loadPollOff)
  wp_simp_pre [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hsteps_sh, _hcrl_sf, hx1_sf, hbox_ne, hbox_mod, htr_sf⟩
  have henv : kit.envOk sf.fs.files :=
    (hfsAt.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
  clear hsteps_sh hfsAt
  simp only [wp_norm, arm64_norm] at hx1_sf
  apply SepWP.fold (Entails.of_eq (stack_wsCalleeV_shim_to_poll kit ikit (s0.sp - 0xee0#64) hn_v)) (by sep_focus)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF3
  apply (messageDecrypt_call_panic_then_wp_lscro hpoll
    (x := (⟨sf.readReg64 (Reg.gpr 0#5), (s0.sp - 0xee0#64) + 0x5f0#64, x.remA, x.rem⟩,
      s0.readReg64 (Reg.gpr 3#5), st0)) hF3)
  · wp_norm_lhs
  · wp_norm_lhs
  · simp only [State.spAligned, wp_norm, arm64_norm, hsp_sf]; exact hal
  · wp_norm_lhs
  · intro _R' _hmR'
    dsimp only [StoreKit.withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hF3, ?_⟩
    refine withEnvPre_pre_intro (by simp only [arm64_norm]; exact henv) ?_
    dsimp only [StoreKit.kitLoadPollPlacedSpecS]
    simp only [sepConj_assoc, wp_norm, arm64_norm, hsp_sf, haddr_ss, and_true] at _hmR' ⊢
    arm64_sep_close
  · intro _; exact loadShim_onPanic_entailsVPlaced (by simp only [wp_norm, arm64_norm]; exact htr_sf)
  · intro _ _; rfl
  intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
  dsimp only [StoreKit.withLsRoCl, StoreKit.kitLoadPollPlacedSpecSE, StoreKit.kitLoadPollPlacedSpecS]
  simp only [wp_norm, arm64_norm, hsp_sf] at hpc_sf1 hsp_sf1
  wp_simp_pre [wp_norm, arm64_norm, hsp_sf, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w
  apply SepWP.pure_elim; rintro ⟨_hcrl_sf1, hloadRel, htr_sf1⟩
  apply SepWP.fold (wsSavedRegs_fold s0.sp s0) (by sep_focus)
  apply SepWP.fold (fold_sp0 (s0.sp - 0xee0#64) 0#64) (by sep_focus)
  apply SepWP.fold (fold_words8 (s0.sp - 0xee0#64 + 0xa0#64)
    x.msgA x.remA x.locA (s0.readReg64 (Reg.gpr 3#5))
    kit.ss_vt (s0.readReg64 (Reg.gpr 5#5))
    ikit.id_vt (s0.sp - 113#64)) (by sep_focus)
  apply SepWP.fold (fold_2c8 (s0.sp - 0xee0#64) 0#8) (by sep_focus)
  apply SepWP.fold (fold_2e0 (s0.sp - 0xee0#64) _ _ 0#64) (by sep_focus)
  apply SepWP.fold (Entails.of_eq (stack_wsCalleeV_poll_back kit ikit (s0.sp - 0xee0#64) hn_v)) (by sep_focus)
  have hsplit_extra := wsCalleeStack_split_extra_placed kit ikit st0 ist0 s0 hsp_le
  dsimp only [Reg.x3, Reg.x5] at hsplit_extra
  apply SepWP.fold hsplit_extra (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF4 hmf
  refine ⟨⟨w, .ok false, .ok .newOrUnchanged, .ok ()⟩, ?_⟩
  refine ⟨?_, ?_, hsp_base, ?_, hloadRel, ?_, ?_⟩
  · wp_norm_lhs
  · simp only [CalleeSavedPreserved, wp_norm, arm64_norm] at hcs_sf hcs_sf1
    refine ⟨by wp_norm_lhs,
            by simp only [wp_norm, arm64_norm, hsp_sf1],
            hal,
            by simp only [State.spAligned, wp_norm, arm64_norm, hsp_sf1]; exact hal,
            by simp only [wp_norm, arm64_norm, hcs_sf1, hcs_sf],
            by simp only [wp_norm, arm64_norm, hcs_sf1, hcs_sf],
            hF4,
            by simp only [wp_norm, arm64_norm, hcs_sf1, hcs_sf]⟩
  · simp only [CalleeSavedPreserved, wp_norm, arm64_norm] at hcs_sf1
    simpa only [Reg.x19, wp_norm, arm64_norm, hsp_sf] using hcs_sf1.1
  · simp only [wp_norm, arm64_norm] at htr_sf1 ⊢
    rw [htr_sf1, htr_sf]
  · dsimp only [LoadPolledStateVPlaced, wsFixedVPlaced, wsArgCellsV, decVtablesAtV,
      decLoadVtableAtV, decStoreVtableAtV, decTrustVtableAtV, decSaveVtableAtV,
      wsEnvPlaced, wsMsgCells, Reg.x3, Reg.x5] at hmf ⊢
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, BitVec.add_assoc] at hmf ⊢
    arm64_sep_close

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad
