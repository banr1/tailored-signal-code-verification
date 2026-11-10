/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.Common
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFetch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailWriteErr
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# T1 `previous_sessions` Buffer Deallocation Tail (`+0x564..+0x5b4`)

Proves `tailFreePrevSessions_ok` (and `tailFreePrevSessions_ok_trap`), freeing any backing buffer of
the empty `previous_sessions` `Vec` at `sp + 0x110` before continuing into `tailWriteErr_ok` at
`+0x5b4`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.freePrevSessions_zero_sepWP_trap
    {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {sp prevPtr : BitVec 64}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x564#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x5b4#64) s
      (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = s.readReg64 .x30 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))) := by
  subst hsp
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches_cli b (Rust.withPanics (trTrapExterns C abs)) hfn 1380 80
  generalize_entry (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.freePrevSessions_zero_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp prevPtr : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x564#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x5b4#64) s
      (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = s.readReg64 .x30 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))) := by
  subst hsp
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1380 80
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 800000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.freePrevSessions_nz_sepWP_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {s : State} {sp prevCap prevPtr : BitVec 64}
    (hA : AllocHooks A abs)
    (hcap_nz : prevCap ≠ 0#64)
    (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x564#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x5b4#64) s
      (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64) ∗
       A.pool ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24) ∗
       stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp allocHookStack)) := by
  subst hsp
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  have hdealloc := dealloc_ok_at_trap b C A abs hA CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::encrypt")) rfl
  have hmul24 := mul24_shift_toNat hcap_lt
  messageEncryptTail_fetches_cli b (Rust.withPanics (trTrapExterns C abs)) hfn 1380 80
  generalize_entry (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  refine sepWP_call_dealloc (sp := s.sp) (entry + bv% (1460)) hdealloc rfl
    (F := ((s.sp + 272#64) ↦₆₄ prevCap) ∗ ((s.sp + 280#64) ↦₆₄ prevPtr) ∗ ((s.sp + 288#64) ↦₆₄ 0#64))
    (by ac_rfl)
    rfl hmul24 rfl rfl hrun hsp_al rfl ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf
  obtain ⟨hx19_sf, _, hx21_sf, _, hx23_sf, _, hx25_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ := hcs_sf
  dsimp only [State.setPC, State.writeReg64, State.sp, State.trace] at hsp_sf htr_sf
  simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.fp, Reg.gpr.injEq,
    reduceCtorEq, BitVec.reduceEq, or_self, ite_false] at hx19_sf hx21_sf hx23_sf hx25_sf hx26_sf hx27_sf hx28_sf hx29_sf
  have hsp_al_sf : sf.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_sf]; exact hsp_al
  apply SepWP.done hpc_sf hrun_sf
  refine ⟨hsp_sf, hsp_al_sf, htr_sf, hx19_sf, hx21_sf, hx23_sf, hx25_sf, hx26_sf,
    hx27_sf, hx28_sf, hx29_sf, hvregs_sf, ?_⟩
  ac_rfl

set_option maxHeartbeats 800000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.freePrevSessions_nz_sepWP
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp prevCap prevPtr : BitVec 64}
    (hA : AllocHooks A abs)
    (hcap_nz : prevCap ≠ 0#64)
    (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x564#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x5b4#64) s
      (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64) ∗
       A.pool ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24) ∗
       stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp allocHookStack)) := by
  subst hsp
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  have hdealloc := dealloc_ok_at b C A ctl abs hA CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::encrypt")) rfl
  have hmul24 := mul24_shift_toNat hcap_lt
  messageEncryptTail_fetches_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1380 80
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  refine sepWP_call_dealloc (sp := s.sp) (entry + bv% (1460)) hdealloc rfl
    (F := ((s.sp + 272#64) ↦₆₄ prevCap) ∗ ((s.sp + 280#64) ↦₆₄ prevPtr) ∗ ((s.sp + 288#64) ↦₆₄ 0#64))
    (by ac_rfl)
    rfl hmul24 rfl rfl hrun hsp_al rfl ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf
  obtain ⟨hx19_sf, _, hx21_sf, _, hx23_sf, _, hx25_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ := hcs_sf
  dsimp only [State.setPC, State.writeReg64, State.sp, State.trace] at hsp_sf htr_sf
  simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.fp, Reg.gpr.injEq,
    reduceCtorEq, BitVec.reduceEq, or_self, ite_false] at hx19_sf hx21_sf hx23_sf hx25_sf hx26_sf hx27_sf hx28_sf hx29_sf
  have hsp_al_sf : sf.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_sf]; exact hsp_al
  apply SepWP.done hpc_sf hrun_sf
  refine ⟨hsp_sf, hsp_al_sf, htr_sf, hx19_sf, hx21_sf, hx23_sf, hx25_sf, hx26_sf,
    hx27_sf, hx28_sf, hx29_sf, hvregs_sf, ?_⟩
  ac_rfl

open CryptoVerification.LibsignalPublicApi.StoreKit

variable {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)}
  {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
  {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.tailFreePrevSessions_ok_trap (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (prevCap prevPtr : BitVec 64)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x564#64) (tailRegs w0 w1 w2)
      (fun sp => memRegion sp 0x58 ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry_trap (C := C) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (memRegion sp 0x58 ∗
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      memRegion (sp + 0x128#64) 0x158 ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  by_cases hcap : prevCap = 0#64
  · subst hcap
    rw [vecAt_prev_zero_eq A sp prevPtr] at hmem
    let F := memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R
    have hmem_re : s.mem ⊨
        ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
        ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ F) := by
      have heq :
          ((memRegion sp 0x58 ∗
            (⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
              (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))) ∗
            memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x1ea ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
           ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ F)) := by
        dsimp only [F]; ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hmem_re
    have hmem2 := hmem_re.2

    have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.freePrevSessions_zero_sepWP_trap (prevPtr := prevPtr) hpc hrun hsp_al hsp
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP_trap hmem2 hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, _, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x5b4#64 := by
      rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry_trap (C := C) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.tailWriteErr_ok_trap env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    have hmf2 : s1.mem ⊨
        (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea) ∗
        (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ F) =
          ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea) ∗
           (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F]; ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (vecHeader_prev_weaken sp 0#64 prevPtr)) hmf2
    have heq2 :
        (memRegion (sp + 0x110#64) 0x35a ∗
         (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
    rwa [← heq2]
  · rw [vecAt_prev_nz_eq A sp prevCap prevPtr hcap] at hmem
    let F := memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
      memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - allocHookStack) ∗
      encSavedRegs s0.sp s0 ∗ R
    have hmem_re :
        s.mem ⊨ ⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
          ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.pool ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
            memRegion prevPtr (prevCap.toNat * 24) ∗ stackAt sp allocHookStack) ∗ F) := by
      have heq :
          ((memRegion sp 0x58 ∗
            (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
              (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
               ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
               memRegion prevPtr (prevCap.toNat * 24))) ∗
            memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
           ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
             ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.pool ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
             memRegion prevPtr (prevCap.toNat * 24) ∗ stackAt sp allocHookStack) ∗ F)) := by
        unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon
        change ((memRegion sp 0x58 ∗
          (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
            (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
             ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
             memRegion prevPtr (prevCap.toNat * 24))) ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
          stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R) = _
        rw [stackAt_encSubStack_alloc sp]
        dsimp only [F]
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hmem_re
    rcases hmem_re with ⟨⟨_, hcap_lt, _⟩, hmem2⟩
    have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.freePrevSessions_nz_sepWP_trap (prevPtr := prevPtr) env.hooks.alloc_abs hcap hcap_lt hpc hrun hsp_al hsp
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP_trap hmem2 hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x5b4#64 := by
      rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry_trap (C := C) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.tailWriteErr_ok_trap env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hsteps1.frozenLoaded hfl, hsteps1.symtab_eq.trans hsym, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    have hmf2 : s1.mem ⊨
        (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea) ∗
        (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp allocHookStack) ∗ F) =
          ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea) ∗
           (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
        unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon
        change _ = ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea) ∗
           (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
              nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
              stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R))
        rw [stackAt_encSubStack_alloc sp]
        dsimp only [F]
        ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (vecHeader_prev_weaken sp prevCap prevPtr)) hmf2
    have heq2 :
        (memRegion (sp + 0x110#64) 0x35a ∗
         (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
    rwa [← heq2]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.tailFreePrevSessions_ok (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (prevCap prevPtr : BitVec 64)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x564#64) (tailRegs w0 w1 w2)
      (fun sp => memRegion sp 0x58 ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (memRegion sp 0x58 ∗
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      memRegion (sp + 0x128#64) 0x158 ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  by_cases hcap : prevCap = 0#64
  · subst hcap
    rw [vecAt_prev_zero_eq A sp prevPtr] at hmem
    let F := memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R
    have hmem_re : s.mem ⊨
        ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
        ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ F) := by
      have heq :
          ((memRegion sp 0x58 ∗
            (⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
              (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))) ∗
            memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x1ea ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
           ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ F)) := by
        dsimp only [F]; ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hmem_re
    have hmem2 := hmem_re.2

    have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.freePrevSessions_zero_sepWP (prevPtr := prevPtr) hpc hrun hsp_al hsp
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP hmem2 hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, _, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x5b4#64 := by
      rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.tailWriteErr_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    have hmf2 : s1.mem ⊨
        (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea) ∗
        (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ F) =
          ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea) ∗
           (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F]; ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (vecHeader_prev_weaken sp 0#64 prevPtr)) hmf2
    have heq2 :
        (memRegion (sp + 0x110#64) 0x35a ∗
         (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
    rwa [← heq2]
  · rw [vecAt_prev_nz_eq A sp prevCap prevPtr hcap] at hmem
    let F := memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
      memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - allocHookStack) ∗
      encSavedRegs s0.sp s0 ∗ R
    have hmem_re :
        s.mem ⊨ ⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
          ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.pool ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
            memRegion prevPtr (prevCap.toNat * 24) ∗ stackAt sp allocHookStack) ∗ F) := by
      have heq :
          ((memRegion sp 0x58 ∗
            (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
              (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
               ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
               memRegion prevPtr (prevCap.toNat * 24))) ∗
            memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
           ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
             ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.pool ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
             memRegion prevPtr (prevCap.toNat * 24) ∗ stackAt sp allocHookStack) ∗ F)) := by
        unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon
        change ((memRegion sp 0x58 ∗
          (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
            (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
             ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
             memRegion prevPtr (prevCap.toNat * 24))) ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
          stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R) = _
        rw [stackAt_encSubStack_alloc sp]
        dsimp only [F]
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hmem_re
    rcases hmem_re with ⟨⟨_, hcap_lt, _⟩, hmem2⟩
    have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.freePrevSessions_nz_sepWP (prevPtr := prevPtr) env.hooks.alloc hcap hcap_lt hpc hrun hsp_al hsp
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP hmem2 hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x5b4#64 := by
      rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.tailWriteErr_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hsteps1.frozenLoaded hfl, hsteps1.symtab_eq.trans hsym, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    have hmf2 : s1.mem ⊨
        (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea) ∗
        (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp allocHookStack) ∗ F) =
          ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea) ∗
           (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
        unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon
        change _ = ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea) ∗
           (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
              nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
              stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R))
        rw [stackAt_encSubStack_alloc sp]
        dsimp only [F]
        ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (vecHeader_prev_weaken sp prevCap prevPtr)) hmf2
    have heq2 :
        (memRegion (sp + 0x110#64) 0x35a ∗
         (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
    rwa [← heq2]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions
