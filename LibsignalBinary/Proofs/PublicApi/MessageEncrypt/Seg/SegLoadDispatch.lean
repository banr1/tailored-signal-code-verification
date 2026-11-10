/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadShimPoll
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadDecodes
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `segLoad` Post-Poll Error Dispatch (`+0x160..+0x180`, `+0x41c..+0x45c`)

Handles the `ans = .error ()` (store hook error) and `ans = .ok none` (`SessionNotFound`) branches
at post-poll dispatch `+0x160` of `session_message_encrypt_with_stores`, routing both to
`tailWriteErr_ok`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Frame and `.rodata` Helpers -/

theorem enc_sp_bound_of_kit {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (ikit : IdentityStoreSpec A b)
    {sp : Nat} (h : withStoresEncStackV kit ikit ≤ sp) : withStoresEncStack ≤ sp := by
  unfold withStoresEncStackV encSubStackV encSubStack withStoresEncStack encFrameSize at *
  omega

theorem satisfies_pure_left {p : Prop} {Q : SepProp} {m : Memory} (h : m ⊨ ⌜p⌝ ∗ Q) :
    p ∧ (m ⊨ Q) :=
  (satisfies_pure_sepConj p Q m).mp h

theorem satisfies_sepExists_left {α : Type _} {P : α → SepProp} {Q : SepProp} {m : Memory}
    (h : m ⊨ (∃∗ a, P a) ∗ Q) : ∃ a, m ⊨ P a ∗ Q := by
  rw [sepExists_sepConj_left] at h
  exact (satisfies_sepExists _ m).mp h

theorem loadOutRes_err_eq (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (b w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)) :
    LoadOutRes Scope A b (.error ()) w0 w1 w2 w3 w4 w5 w6 tail =
      ⌜w0 = 0xFFFFFFFFFFFFFFFE#64 ∧ w1 = 0x800000000000001A#64 ∧
        w2 = b + bv% (ls_reloc% 0x77cc) ∧ w3 = 10#64 ∧ w4 = 1#64 ∧ w5 = b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)⌝ ∗
        ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) := rfl

theorem memRegion_0x110_0x35a_fold (sp : BitVec 64) (b0 b1 : BitVec 8) :
    memRegion (sp + 0x110#64) 0x358 ∗ ((sp + 0x468#64) ↦₈ b0) ∗ ((sp + 0x469#64) ↦₈ b1) ⊢
      memRegion (sp + 0x110#64) 0x35a := by
  rw [memRegion_split (sp + 0x110#64) 0x358 2 (by decide),
      memRegion_split (sp + 0x110#64 + 0x358#64) 1 1 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo8_entails_memRegion _ _) (pointsTo8_entails_memRegion _ _))

theorem dispatchFrame_tail_entails {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (s0 : State) (v50 : BitVec 64) :
    protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
      dispatchFrame kit st0 ikit ist0 ctl x s0 v50 ⊢
    memRegion (s0.sp - 0xbe0#64) 0x58 ∗ memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗ memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x 0 s0 ∗ encStoreExtra kit st0 ikit ist0 x s0 := by
  dsimp only [dispatchFrame, encCommon]
  have hspills := encSpillsAt_fold kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x
  have h58 := fold_sp58 (s0.sp - 0xbe0#64) v50
  have h35a := memRegion_0x110_0x35a_fold (s0.sp - 0xbe0#64) 0#8 0#8
  have hperm :
      protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
        (nowAt s0.sp x.now ∗ encSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 0xbe0#64) 0x50 ∗
          ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗ encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗ memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
          ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗ memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗
          memRegion x.ret 248 ∗ tapeAfter ctl x.cur x.rest 0 ∗ logOff img ∗
          encStoreExtra kit st0 ikit ist0 x s0) =
      (memRegion (s0.sp - 0xbe0#64) 0x50 ∗ ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50)) ∗
      (memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗ ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗
        ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8)) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗ memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      (encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA)) ∗
      memRegion x.ret 248 ∗
      ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest 0 ∗ logOff img ∗
        stackAt (s0.sp - 0xbe0#64) encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗
      encStoreExtra kit st0 ikit ist0 x s0 := by ac_rfl
  rw [hperm]
  exact sepConj_mono h58 (sepConj_mono h35a (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left hspills))))

theorem memRegion_0x848_split_0x9d0 (sp : BitVec 64) :
    memRegion (sp + 0x848#64) 0x338 =
      memRegion (sp + 0x848#64) 0x188 ∗
      cells (sp + 0x9d0#64) 3 ∗
      memRegion (sp + 0x9e8#64) 0x198 := by
  have hc3 : memRegion (sp + 0x9d0#64) 24 = cells (sp + 0x9d0#64) 3 :=
    ProofLib.memRegion_cells (sp + 0x9d0#64) 3 (by decide)
  rw [memRegion_split (sp + 0x848#64) 0x188 0x1b0 (by decide),
      memRegion_split (sp + 0x848#64 + 0x188#64) 24 0x198 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hc3]

theorem pollWith_0x9d0_fold (sp w3 w4 w5 v830 v838 v840 : BitVec 64) (tail : List (BitVec 8))
    (htail : tail.length = 312) :
    (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      memRegion (sp + 0x6f0#64) 8 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ v830) ∗ ((sp + 0x838#64) ↦₆₄ v838) ∗
      ((sp + 0x840#64) ↦₆₄ v840) ∗
      memRegion (sp + 0x848#64) 0x188) ∗
    (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5)) ∗
    memRegion (sp + 0x9e8#64) 0x198 ⊢
      pollWith sp 0x9d0 [w3, w4, w5] := by
  dsimp only [pollWith, words64At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  have ht : ((sp + 0x6f8#64) ↦ₛ tail) ⊢ memRegion (sp + 0x6f8#64) 312 := by
    have h := pointsToBytes_entails_memRegion (sp + 0x6f8#64) tail
    rwa [htail] at h
  refine sepConj_mono_left ?_
  rw [memRegion_split (sp + 0x46a#64) 0x116 1104 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64) 368 736 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64) 8 728 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64 + 8#64) 312 416 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64 + 8#64 + 312#64) 8 408 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64 + 8#64 + 312#64 + 8#64) 8 400 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64 + 8#64 + 312#64 + 8#64 + 8#64) 8 392 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono ht (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))))))

/-! ## Store Error Branch (`ans = .error ()`) -/

theorem segLoad_dispatch_err_wp {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (_env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {s : State} {sp w4 w5 w6 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hps : s.pstate = addsPState64 0xFFFFFFFFFFFFFFFE#64 2#64) :
    SepWP (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x5b4#64) s
      (((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
        memRegion (sp + 0x848#64) 0x338 ∗ F)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x26 = sp + 0x9d0#64 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        P_f = (((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
          memRegion (sp + 0x848#64) 0x188 ∗
          ((sp + 0x9d0#64) ↦₆₄ w4) ∗ ((sp + 0x9d8#64) ↦₆₄ w5) ∗ ((sp + 0x9e0#64) ↦₆₄ w6) ∗
          memRegion (sp + 0x9e8#64) 0x198 ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hfn : libsignalSessionCode.fnOff encryptWithStoresName = 0x3cbd8 :=
    libsignalSessionCode_fnOff_0x3cbd8
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBin img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3cbd8 0x160 0x18
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  simp only [wp_norm, arm64_norm] at hx25 hx26
  wp_conv_pre => rw [memRegion_0x848_split_0x9d0 s.sp]
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  simp only [wp_norm, arm64_norm, hx26, hal_norm, true_and]

theorem segExit_of_sepWP_frozen {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {post : State → SepProp → Prop} {Out : State → Prop}
    (hF : FrozenInv img s) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) target s P post)
    (hcont : ∀ sf P_f, sf.pc = target → sf.status = .Running → post sf P_f →
      FrozenInv img sf → (sf.mem ⊨ P_f ∗ R) →
      SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 sf Out) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_f, hmf, hpost⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout'⟩ :=
    hcont sm P_f hpcm hrunm hpost (hF.of_steps hsteps) hmf (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem segLoad_dispatch_err {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (sp w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8))
    (hsp_eq : sp = s0.sp - 0xbe0#64)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x160#64)
    (hmeta : encMidMeta img x s0 s)
    (hsp_le : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (htail : tail.length = 312)
    (hl : kit.loadRel st0 x.rem.val (.error ()))
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.error ()))
    (hx27 : s.readReg64 .x27 = w1) (hx21 : s.readReg64 .x21 = w2) (hx23 : s.readReg64 .x23 = w3)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hps : s.pstate = addsPState64 w0 2#64)
    (hm : s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
      ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutRes Scope A img.base (.error ()) w0 w1 w2 w3 w4 w5 w6 tail ∗
      protocolAddressAt A x.rem x.remA ∗
      A.pool ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
      dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun s' => ∃ r g sess,
        CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s') := by
  subst hsp_eq
  rcases hmeta with ⟨hrun, hsp, hal0, hal, hx29, hx19, hF, hsym, hvregs⟩
  have hm_drop : s.mem ⊨
      LoadOutRes Scope A img.base (.error ()) w0 w1 w2 w3 w4 w5 w6 tail ∗
      ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        protocolAddressAt A x.rem x.remA ∗
        A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
        dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R) := by
    refine Satisfies.drop_left (P := loadVtablesAt kit) ?_
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  clear hm
  rw [loadOutRes_err_eq, sepConj_assoc] at hm_drop
  obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hm_drop'⟩ := satisfies_pure_left hm_drop
  rw [← sepConj_assoc] at hm_drop'
  have hm_tail : s.mem ⊨
      (((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
        (((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          memRegion (s0.sp - 0xbe0#64) 0x58 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
          encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          memRegion x.ret 248 ∗
          encCommon A ctl img x 0 s0 ∗
          encStoreExtra kit st0 ikit ist0 x s0)) ∗ R := by
    refine Satisfies.mono ?_ hm_drop'
    refine sepConj_mono_left ?_
    have hfr := dispatchFrame_tail_entails kit st0 ikit ist0 ctl x s0 v50
    have hperm1 :
        ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          protocolAddressAt A x.rem x.remA ∗
          A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
          dispatchFrame kit st0 ikit ist0 ctl x s0 v50) =
        (protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
          dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗
        (((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6)) := by ac_rfl
    rw [hperm1]
    refine Entails.trans (sepConj_mono_left hfr) ?_
    exact Entails.of_eq (by ac_rfl)
  have hwp := segLoad_dispatch_err_wp env
    (w4 := 1#64) (w5 := img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) (w6 := w6)
    (F := ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
      ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
      memRegion (s0.sp - 0xbe0#64) 0x58 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommon A ctl img x 0 s0 ∗
      encStoreExtra kit st0 ikit ist0 x s0)
    hpc hrun hsp hal hx25 hx26 hps
  refine segExit_of_sepWP_frozen ⟨hF, hsym⟩ hm_tail hwp ?_
  intro sf P_f hpcf hrunf hpostf hFf hm_f
  rcases hpostf with ⟨hspf, half, htrf, hx19f, hx29f, hvregsf, hx26f, hx28f, hx27f, hx21f, hx23f, rfl⟩
  refine segExit_of_false (tailWriteErr_ok env x R s0 sf (answersOfLoad (.error ())) (.store ())
    0x800000000000001A#64 (img.base + bv% (ls_reloc% 0x77cc)) 10#64 1#64 (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) w6
    ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)
    (tailModel_load_err hl (htrf.trans htr))
    (speStaged_storeErr A img.base x.ret w6)
    ⟨?_, ⟨hrunf, hspf, hal0, half, hx29f.trans hx29, hx19f.trans hx19, hFf.1, hFf.2, hvregsf.trans hvregs⟩,
      ⟨hx26f, hx28f.trans hx28, hx27f.trans hx27, hx21f.trans hx21, hx23f.trans hx23⟩,
      enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩)
  · rw [encEntry_eq_fnAddr env, hpcf]
  · dsimp only [EncTailV]
    rw [draws_answersOfLoad_err]
    change sf.mem ⊨ _ ∗ _ ∗ _ ∗ _ ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R)
    refine Satisfies.mono ?_ hm_f
    have hpoll := pollWith_0x9d0_fold (s0.sp - 0xbe0#64)
      1#64 (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) w6
      1#64 (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) w6 tail htail
    have hperm2 :
        ((((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188 ∗
          ((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
          ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ w6) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198 ∗
          (((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            memRegion (s0.sp - 0xbe0#64) 0x58 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
            encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
            memRegion x.ret 248 ∗
            encCommon A ctl img x 0 s0 ∗
            encStoreExtra kit st0 ikit ist0 x s0)) ∗ R) =
        ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188) ∗
        (((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
          ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ w6)) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198) ∗
        (memRegion (s0.sp - 0xbe0#64) 0x58 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
          ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
          encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          memRegion x.ret 248 ∗
          encCommon A ctl img x 0 s0 ∗
          (encStoreExtra kit st0 ikit ist0 x s0 ∗ R)) := by ac_rfl
    rw [hperm2]
    refine Entails.trans (sepConj_mono_left hpoll) ?_
    exact Entails.of_eq (by ac_rfl)

/-! ## Missing Record Branch (`ans = .ok none`) -/

theorem loadOutRes_none_eq (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (b w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)) :
    LoadOutRes Scope A b (.ok none) w0 w1 w2 w3 w4 w5 w6 tail =
      ⌜w0 = 0xFFFFFFFFFFFFFFFF#64⌝ := rfl

theorem stack_encSub_extHook (sp : BitVec 64) :
    stackAt sp encSubStack =
      memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        stackAt sp extHookStack := by
  have h := stackAt_split_bottom sp extHookStack (encSubStack - extHookStack) (by decide)
  rwa [show extHookStack + (encSubStack - extHookStack) = encSubStack by decide] at h

theorem stack_encSub_extHook_back (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        stackAt sp extHookStack =
      stackAt sp encSubStack :=
  (stack_encSub_extHook sp).symm

theorem memRegion_0x580_split_24 (sp : BitVec 64) :
    memRegion (sp + 0x580#64) 368 =
      memRegion (sp + 0x580#64) 24 ∗ memRegion (sp + 0x598#64) 344 := by
  rw [memRegion_split (sp + 0x580#64) 24 344 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_0x598_split (sp : BitVec 64) :
    memRegion (sp + 0x598#64) 344 =
      (∃∗ b0 : BitVec 8, (sp + 0x598#64) ↦₈ b0) ∗
      memRegion (sp + 0x599#64) 7 ∗
      (∃∗ v5a0 : BitVec 64, (sp + 0x5a0#64) ↦₆₄ v5a0) ∗
      memRegion (sp + 0x5a8#64) 328 := by
  rw [memRegion_split (sp + 0x598#64) 1 343 (by decide),
      memRegion_split (sp + 0x598#64 + 1#64) 7 336 (by decide),
      memRegion_split (sp + 0x598#64 + 1#64 + 7#64) 8 328 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_one (sp + 0x598#64), ProofLib.memRegion_eight (sp + 0x5a0#64)]

theorem memRegion_0x580_368_fold (sp w0 w1 w2 w3 w4 : BitVec 64) :
    ((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗
    ((sp + 0x590#64) ↦₆₄ w2) ∗ ((sp + 0x598#64) ↦₆₄ w3) ∗
    ((sp + 0x5a0#64) ↦₆₄ w4) ∗ memRegion (sp + 0x5a8#64) 328 ⊢
      memRegion (sp + 0x580#64) 368 := by
  rw [memRegion_split (sp + 0x580#64) 8 360 (by decide),
      memRegion_split (sp + 0x580#64 + 8#64) 8 352 (by decide),
      memRegion_split (sp + 0x580#64 + 8#64 + 8#64) 8 344 (by decide),
      memRegion_split (sp + 0x580#64 + 8#64 + 8#64 + 8#64) 8 336 (by decide),
      memRegion_split (sp + 0x580#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 328 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))))

theorem vecU8_eq_words3_sep_buf (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 0x10#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8
  apply ProofLib.sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl)))
  · apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    exact Entails.of_eq (by ac_rfl)

def dispatchFrameNo108848 {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (st0 : kit.StoreState) (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (s0 : State) (v50 : BitVec 64) : SepProp :=
  let sp := s0.sp - 0xbe0#64
  nowAt s0.sp x.now ∗
  encSavedRegs s0.sp s0 ∗
  memRegion sp 0x50 ∗
  ((sp + 0x50#64) ↦₆₄ v50) ∗
  encSpillsInit kit.ss_vt ikit.id_vt sp x ∗
  memRegion (sp + 0x110#64) 0x358 ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
  memRegion (sp + 0x6f0#64) 8 ∗
  (x.ptA ↦ₛ x.ptext) ∗
  protocolAddressAt A x.loc x.locA ∗
  memRegion x.ret 248 ∗
  tapeAfter ctl x.cur x.rest 0 ∗
  logOff img ∗
  encStoreExtra kit st0 ikit ist0 x s0

theorem dispatchFrame_eq_108_848_sep {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (s0 : State) (v50 : BitVec 64) :
    dispatchFrame kit st0 ikit ist0 ctl x s0 v50 =
      ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50 := by
  dsimp only [dispatchFrame, dispatchFrameNo108848]
  ac_rfl

theorem segLoad_dispatch_none_pre_wp {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (_env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {s : State} {sp remA : BitVec 64} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = 0xFFFFFFFFFFFFFFFF#64)
    (hps : s.pstate = addsPState64 0xFFFFFFFFFFFFFFFF#64 2#64) :
    SepWP (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + bv% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - 0x3cbd8)) s
      (((sp + 0x108#64) ↦₆₄ remA) ∗ F)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = remA ∧
        sf.readReg64 .x8 = sp + 0x580#64 ∧
        sf.readReg64 .x22 = remA ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x428#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        P_f = (((sp + 0x108#64) ↦₆₄ remA) ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hfn : libsignalSessionCode.fnOff encryptWithStoresName = 0x3cbd8 :=
    libsignalSessionCode_fnOff_0x3cbd8
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBin img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3cbd8 0x160 0x24
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBin img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3cbd8 0x41c 0x0c
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  simp only [wp_norm, arm64_norm] at hx24
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  simp only [wp_norm, arm64_norm, hal_norm, true_and]

theorem devWord_of_pointsTo8_memRegion7_1432 (sp : BitVec 64) (dev : BitVec 8) :
    ((sp + 1432#64) ↦₈ dev) ∗ memRegion (sp + 1433#64) 7 ⊢
      ∃∗ w3 : BitVec 64, ⌜DevWord dev w3⌝ ∗ ((sp + 1432#64) ↦₆₄ w3) := by
  have h := devWord_of_pointsTo8_memRegion7 (sp + 1432#64) dev
  have h1 : sp + 1432#64 + 1#64 = sp + 1433#64 := by bv_arith
  rwa [h1] at h

theorem segLoad_dispatch_none_post_wp {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {s : State} {sp remA cap ptr len : BitVec 64} {dev : BitVec 8} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = remA)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64) :
    SepWP (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x5b4#64) s
      (((remA + 0x18#64) ↦₈ dev) ∗
        ((sp + 0x580#64) ↦₆₄ cap) ∗ ((sp + 0x588#64) ↦₆₄ ptr) ∗
        ((sp + 0x590#64) ↦₆₄ len) ∗
        memRegion (sp + 0x598#64) 344 ∗
        memRegion (sp + 0x848#64) 0x338 ∗ F)
      (fun sf P_f =>
        ∃ w3 : BitVec 64, DevWord dev w3 ∧
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          sf.readReg64 .x26 = sp + 0x9d0#64 ∧
          sf.readReg64 .x28 = sp + 0x4a0#64 ∧
          sf.readReg64 .x27 = cap ∧
          sf.readReg64 .x21 = ptr ∧
          sf.readReg64 .x23 = len ∧
          P_f = (((remA + 0x18#64) ↦₈ dev) ∗
            memRegion (sp + 0x580#64) 368 ∗
            memRegion (sp + 0x848#64) 0x188 ∗
            ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ (img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4))) ∗
            ((sp + 0x9e0#64) ↦₆₄ 15#64) ∗
            memRegion (sp + 0x9e8#64) 0x198 ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hadrp := enc_adrp_0x4d6a0 (H := Rust.withPanics (tripleRatchetExterns C ctl abs))
    env.loads 0x43c#64 (Or.inr rfl)
  have hfn : libsignalSessionCode.fnOff encryptWithStoresName = 0x3cbd8 :=
    libsignalSessionCode_fnOff_0x3cbd8
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBin img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3cbd8 0x428 0x34
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  simp only [wp_norm, arm64_norm] at hx22 hx26 hx28 hadrp
  wp_conv_pre =>
    rw [memRegion_0x598_split s.sp, memRegion_0x848_split_0x9d0 s.sp]
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  repeat (apply SepWP.exists_elim; intro _)
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.fold (devWord_of_pointsTo8_memRegion7_1432 s.sp dev) (by sep_focus)
  wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro w3
  apply SepWP.pure_elim; intro hdev
  wp_steps
  apply SepWP.fold (memRegion_0x580_368_fold s.sp cap ptr len w3 _) (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨w3, hdev, ?_⟩
  simp only [wp_norm, arm64_norm, hx26, hx28, hal_norm, true_and]
  ac_rfl

theorem segLoad_dispatch_none {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (sp w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8))
    (hsp_eq : sp = s0.sp - 0xbe0#64)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x160#64)
    (hmeta : encMidMeta img x s0 s)
    (hsp_le : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (htail : tail.length = 312)
    (hl : kit.loadRel st0 x.rem.val (.ok none))
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok none))
    (hx24 : s.readReg64 .x24 = w0)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hps : s.pstate = addsPState64 w0 2#64)
    (hm : s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
      ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutRes Scope A img.base (.ok none) w0 w1 w2 w3 w4 w5 w6 tail ∗
      protocolAddressAt A x.rem x.remA ∗
      A.pool ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
      dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun s' => ∃ r g sess,
        CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s') := by
  subst hsp_eq
  rcases hmeta with ⟨hrun, hsp, hal0, hal, hx29, hx19, hF, hsym, hvregs⟩
  have hm_drop : s.mem ⊨
      LoadOutRes Scope A img.base (.ok none) w0 w1 w2 w3 w4 w5 w6 tail ∗
      ((((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
        (vecGhostAt A x.rem.name x.remA ∗
          ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          memRegion (x.remA + 0x19#64) 7 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
          A.pool ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          stackAt (s0.sp - 0xbe0#64) extHookStack ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50))) ∗ R) := by
    refine Satisfies.drop_left (P := loadVtablesAt kit) ?_
    refine Satisfies.mono ?_ hm
    rw [protocolAddressAt, memRegion_0x580_split_24 (s0.sp - 0xbe0#64),
        stack_encSub_extHook (s0.sp - 0xbe0#64), dispatchFrame_eq_108_848_sep kit st0 ikit ist0 ctl x s0 v50]
    exact Entails.of_eq (by ac_rfl)
  clear hm
  rw [loadOutRes_none_eq] at hm_drop
  obtain ⟨rfl, hm_drop'⟩ := satisfies_pure_left hm_drop
  clear hm_drop
  refine segExit_of_sepWPp
    (target := (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x5b4#64) hm_drop' ?_
  have hpre_wp := segLoad_dispatch_none_pre_wp env
    (remA := x.remA)
    (F := vecGhostAt A x.rem.name x.remA ∗
      ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
      memRegion (x.remA + 0x19#64) 7 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
      A.pool ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
      stackAt (s0.sp - 0xbe0#64) extHookStack ∗
      memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50))
    hpc hrun hsp hal hx24 hps
  refine messageEncrypt_of_sepWP_frozen ⟨hF, hsym⟩ (SepWP.mono hpre_wp ?_)
  intro sm P_m hpcm hrunm hpostm hFm
  rcases hpostm with ⟨hspm, halm, htrm, hx0m, hx8m, hx22m, hx30m, hx19m, hx29m, hvregsm, hx26m, hx28m, rfl⟩
  refine messageEncrypt_call_panic_then_wp_frozen (stringClone_ok_at_enc env)
    (x := (x.remA, s0.sp - 0xbe0#64 + 0x580#64, x.rem.name))
    (F := ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
      ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
      memRegion (x.remA + 0x19#64) 7 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50))
    hFm hpcm hrunm halm hx30m ?_ ?_ (fun _ _ => rfl) ?_
  · intro R' hm'
    dsimp only [stringCloneSpec]
    refine Satisfies.mono ?_ hm'
    rw [hspm]
    have hperm_c :
        (((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          (vecGhostAt A x.rem.name x.remA ∗
            ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
            memRegion (x.remA + 0x19#64) 7 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
            A.pool ∗
            memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
            stackAt (s0.sp - 0xbe0#64) extHookStack ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
            (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50))) ∗ R' =
        (vecGhostAt A x.rem.name x.remA ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
          A.pool ∗
          stackAt (s0.sp - 0xbe0#64) extHookStack) ∗
        ((((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          memRegion (x.remA + 0x19#64) 7 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50)) ∗ R') := by ac_rfl
    rw [hperm_c]
    apply sepConj_mono_left
    exact Entails.pure_right (And.intro hx0m hx8m) (Entails.refl _)
  · intro sf_p
    dsimp only [stringCloneSpec]
    exact alloc_onPanic_entails (by rw [htrm, htr]; exact ⟨kit.loadEvs encRecord x.rem.val (.ok none), rfl⟩)
  · intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨hcs19, _, _, hcs22, _, _, _, hcs26, _, hcs28, hcs29, hcsv1⟩
    dsimp only [stringCloneSpec]
    wp_conv_pre => rw [vecU8_eq_words3_sep_buf]
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
    apply SepWP.exists_elim; intro cap
    apply SepWP.exists_elim; intro ptr
    apply SepWP.pure_elim; intro htr1
    have hsp1' : sf1.sp = s0.sp - 0xbe0#64 := by rw [hsp1, hspm]
    have hal1 : sf1.spAligned = true := by rw [State.spAligned, hsp1, ← State.spAligned]; exact halm
    have hx22_1 : sf1.readReg64 .x22 = x.remA := by rw [hcs22, hx22m]
    have hx26_1 : sf1.readReg64 .x26 = s0.sp - 0xbe0#64 + 0x9d0#64 := by rw [hcs26, hx26m, hx26]
    have hx28_1 : sf1.readReg64 .x28 = s0.sp - 0xbe0#64 + 0x4a0#64 := by rw [hcs28, hx28m, hx28]
    have hpost_wp := segLoad_dispatch_none_post_wp env
      (s := sf1) (sp := s0.sp - 0xbe0#64) (remA := x.remA)
      (cap := cap) (ptr := ptr) (len := BitVec.ofNat 64 x.rem.name.bytes.length)
      (dev := x.rem.device)
      (F := vecGhostAt A x.rem.name x.remA ∗
        memRegion (x.remA + 0x19#64) 7 ∗
        vecU8Buf A cap ptr x.rem.name.bytes ∗
        A.pool ∗
        stackAt (s0.sp - 0xbe0#64) encSubStack ∗
        ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
        (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50))
      hpc1 hrun1 hsp1' hal1 hx22_1 hx26_1 hx28_1
    have hpre_post_eq :
        vecGhostAt A x.rem.name x.remA ∗
          ((s0.sp - 0xbe0#64 + 0x580#64) ↦₆₄ cap) ∗
          ((s0.sp - 0xbe0#64 + 1416#64) ↦₆₄ ptr) ∗
          ((s0.sp - 0xbe0#64 + 1424#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
          vecU8Buf A cap ptr x.rem.name.bytes ∗
          A.pool ∗
          stackAt sm.sp extHookStack ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          memRegion (x.remA + 0x19#64) 7 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50 =
        ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          ((s0.sp - 0xbe0#64 + 0x580#64) ↦₆₄ cap) ∗
          ((s0.sp - 0xbe0#64 + 0x588#64) ↦₆₄ ptr) ∗
          ((s0.sp - 0xbe0#64 + 0x590#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (vecGhostAt A x.rem.name x.remA ∗
            memRegion (x.remA + 0x19#64) 7 ∗
            vecU8Buf A cap ptr x.rem.name.bytes ∗
            A.pool ∗
            stackAt (s0.sp - 0xbe0#64) encSubStack ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
            (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50)) := by
      rw [hspm, ← stack_encSub_extHook_back (s0.sp - 0xbe0#64)]
      ac_rfl
    refine sepWP_conseq_pc_run hpre_post_eq hpost_wp ?_
    intro sf P_f hpcf hrunf hpostf hFf hm_f
    rcases hpostf with ⟨w3', hdev, hspf, half, htrf, hx19f, hx29f, hvregsf, hx26f, hx28f, hx27f, hx21f, hx23f, rfl⟩
    have hm_rod := rodata_message_encrypt_intro env.loads hFf.1.roData hm_f
    refine segExit_of_false (tailWriteErr_ok env x R s0 sf (answersOfLoad (.ok none))
      (.sessionNotFound x.rem.val "message_encrypt")
      cap ptr (BitVec.ofNat 64 x.rem.val.name.length) w3' (img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4)) 15#64
      (vecU8Buf A cap ptr x.rem.val.name ∗ ((img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4)) ↦ᵣ utf8 "message_encrypt"))
      (tailModel_load_none hl (by rw [htrf, htr1, htrm, htr]))
      (speStaged_sessionNotFound_devWord A img.base x.ret cap ptr w3' x.rem.val hdev)
      ⟨?_, ⟨hrunf, hspf, hal0, half,
        by rw [hx29f, hcs29, hx29m, hx29],
        by rw [hx19f, hcs19, hx19m, hx19], hFf.1, hFf.2,
        by rw [hvregsf, hcsv1, hvregsm, hvregs]⟩,
        ⟨hx26f, hx28f, hx27f, hx21f, hx23f⟩,
        enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩)
    · rw [encEntry_eq_fnAddr env, hpcf]
    · dsimp only [EncTailV]
      rw [draws_answersOfLoad_none]
      change sf.mem ⊨ _ ∗ _ ∗ _ ∗ _ ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R)
      refine Satisfies.mono ?_ hm_rod
      have hpoll := pollWith_0x9d0_fold (s0.sp - 0xbe0#64)
        w3' (img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4)) 15#64 w4 w5 w6 tail htail
      have hperm_end :
          ((img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4)) ↦ᵣ utf8 "message_encrypt") ∗
          ((((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188 ∗
            ((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ w3') ∗
            ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ (img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4))) ∗
            ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ 15#64) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198 ∗
            (vecGhostAt A x.rem.name x.remA ∗
              memRegion (x.remA + 0x19#64) 7 ∗
              vecU8Buf A cap ptr x.rem.name.bytes ∗
              A.pool ∗
              stackAt (s0.sp - 0xbe0#64) encSubStack ∗
              ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
              (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
                ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
                ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
                ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
                ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
                dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50))) ∗ R) =
          (memRegion (s0.sp - 0xbe0#64) 0x50 ∗ ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50)) ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
            ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8)) ∗
          ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
            ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188) ∗
          (((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ w3') ∗
            ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ (img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4))) ∗
            ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ 15#64)) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198) ∗
          (encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA)) ∗
          ((vecU8Buf A cap ptr x.rem.val.name ∗ ((img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4)) ↦ᵣ utf8 "message_encrypt")) ∗
            memRegion x.ret 248 ∗
            encCommon A ctl img x 0 s0 ∗
            (encStoreExtra kit st0 ikit ist0 x s0 ∗ R)) := by
        dsimp only [dispatchFrameNo108848, encCommon, protocolAddressAt, AddrGhost.val]
        ac_rfl
      rw [hperm_end]
      refine Entails.trans (sepConj_mono (fold_sp58 _ _)
        (sepConj_mono (memRegion_0x110_0x35a_fold _ _ _)
          (sepConj_mono hpoll
            (sepConj_mono_left (encSpillsAt_fold _ _ _ _))))) ?_
      exact Entails.of_eq (by ac_rfl)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
