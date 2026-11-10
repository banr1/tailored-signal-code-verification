/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFetch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResult
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem segExit_of_sepWP {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {target_pc : BitVec 64} {P R' R : SepProp}
    {post : State → SepProp → Prop} {Next : State → Prop} {s0 s : State}
    (hm : s.mem ⊨ P ∗ R')
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) target_pc s P post)
    (hnext : ∀ s1 P_f, Steps (tripleRatchetProgAt img.base C ctl abs) s s1 →
      s1.pc = target_pc → s1.status = .Running → (s1.mem ⊨ P_f ∗ R') → post s1 P_f →
      SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s1 Next) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s Next := by
  intro hL
  obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_f, hmf1, hpost1⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps2, hout⟩ :=
    hnext s1 P_f hsteps1 hpc1 hrun1 hmf1 hpost1 (hsteps1.codeLoaded hL)
  exact ⟨sf, hsteps1.trans hsteps2, hout⟩

theorem resStaged_of_speStaged {A : RustAlloc} {ret : BitVec 64} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {jws : List (BitVec 64)} {H : SepProp}
    (hst : SpeStaged A ret e [w0, w1, w2, w3, w4, w5] H) (hjws : jws.length = 24) :
    ResStaged A ret (.error e) [errTag, w0, w1, w2] (unpack64List (w3 :: w4 :: w5 :: jws)) H := by
  rcases hst with ⟨hne, _, hent⟩
  refine ⟨fun h => hne (Except.error.inj h), rfl, ?_, ?_⟩
  · simp [hjws]
  · rw [apiEncResultAt_error, ← words64At_eq_pointsToBytes (ret + 0x20#64)]
    have hsplit :
        words64At ret [errTag, w0, w1, w2] ∗
          words64At (ret + 0x20#64) (w3 :: w4 :: w5 :: jws) ∗ H =
        (ret ↦₆₄ errTag) ∗
          (words64At (ret + 8#64) [w0, w1, w2, w3, w4, w5] ∗ H) ∗
          words64At (ret + 56#64) jws := by
      simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
      ac_rfl
    rw [hsplit]
    have hj_mem : words64At (ret + 56#64) jws ⊢ memRegion (ret + 56#64) 192 := by
      have h192 : (192 : Nat) = 8 * jws.length := by omega
      rw [h192]
      exact words64At_entails_memRegion (ret + 56#64) jws (by omega)
    exact sepConj_mono_right (sepConj_mono hent hj_mem)

set_option maxHeartbeats 800000 in
theorem writeErr_sepWP {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp : BitVec 64}
    {bws dws : List (BitVec 64)} {s : State}
    (hbws : bws.length = 27) (hdws : dws.length = 27)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x5b4#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x5f8#64) s
      (words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) dws)
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.symtab = s.symtab ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = sp + 0x4a0#64 ∧
        sf.readReg64 .x22 = errTag ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) bws)) := by
  subst hsp
  have hfn := libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1460 68
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  rw [words64At_27 (s.sp + 0x9d0#64) hbws,
      words64At_27 (s.sp + 0x4a0#64) hdws]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  refine ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, hx28, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [words64At_27 (s.sp + 0x4a0#64) hbws]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

open CryptoVerification.LibsignalPublicApi.StoreKit

variable {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)}
  {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
  {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}

theorem tailWriteErr_ok (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0x5b4#64) (tailRegs w0 w1 w2)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  have hpoll : pollWith sp 0x9d0 [w3, w4, w5] =
      memRegion (sp + 0x46a#64) 0x36 ∗ memRegion (sp + 0x4a0#64) (8 * 27) ∗
        memRegion (sp + 0x578#64) 0x458 ∗ words64At (sp + 0x9d0#64) [w3, w4, w5] ∗
        memRegion (sp + 0x9e8#64) (8 * 24) ∗ memRegion (sp + 0xaa8#64) 0xd8 := by
    change memRegion (sp + 0x46a#64) 0x566 ∗ words64At (sp + 0x9d0#64) [w3, w4, w5] ∗
      memRegion (sp + 0x9e8#64) 0x198 = _
    rw [memRegion_split' (b := sp + 0x46a#64) (b' := sp + 0x4a0#64) (n := 0x36) (k := 0x530)
        (by decide) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 0x4a0#64) (b' := sp + 0x578#64) (n := 8 * 27) (k := 0x458)
        (by decide) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 0x9e8#64) (b' := sp + 0xaa8#64) (n := 8 * 24) (k := 0xd8)
        (by decide) (by bv_omega) (by decide)]
    ac_rfl
  let F := memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗ memRegion (sp + 0x46a#64) 0x36 ∗
    memRegion (sp + 0x578#64) 0x458 ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S answers) s0 ∗ R
  have hmem1 : s.mem ⊨ memRegion (sp + 0x9e8#64) (8 * 24) ∗
      (memRegion (sp + 0x4a0#64) (8 * 27) ∗ words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ F) := by
    have heq :
      ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
      (memRegion (sp + 0x9e8#64) (8 * 24) ∗
       (memRegion (sp + 0x4a0#64) (8 * 27) ∗ words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ F)) := by
      rw [hpoll]
      dsimp only [F, sp]
      ac_rfl
    rwa [← heq]
  obtain ⟨jws, hjws, hmem2⟩ :=
    memRegion_eq_exists_words64At 24 (sp + 0x9e8#64) (by decide) s.mem _ hmem1
  rw [← sepConj_assoc, sepConj_comm (words64At (sp + 0x9e8#64) jws), sepConj_assoc] at hmem2
  obtain ⟨dws, hdws, hmem3⟩ :=
    memRegion_eq_exists_words64At 27 (sp + 0x4a0#64) (by decide) s.mem _ hmem2
  let bws := w3 :: w4 :: w5 :: jws
  have hbws : bws.length = 27 := by simp [bws, hjws]
  have hbws_eq :
      words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ words64At (sp + 0x9e8#64) jws =
        words64At (sp + 0x9d0#64) bws := by
    simp only [bws, words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hmem4 : s.mem ⊨
      (words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) dws) ∗ F := by
    have heq :
      (words64At (sp + 0x4a0#64) dws ∗ words64At (sp + 0x9e8#64) jws ∗
        words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ F) =
      ((words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) dws) ∗ F) := by
      rw [← hbws_eq]; ac_rfl
    rwa [← heq]
  have hwp := writeErr_sepWP hbws hdws hpc hrun hsp_al hsp hx26 hx28
  refine segExit_of_sepWP hmem4 hwp ?_
  intro s1 P_f hsteps1 hpc1 hrun1 hmf1
    ⟨hsp1, hsp1_al, htr1, hsym1, hx29_1, hx19_1, hx28_1, hx22_1, hx27_1, hx21_1, hx23_1, hvregs1, hPf⟩
  subst hPf
  have hpc1' : s1.pc = encEntry img + 0x5f8#64 := by
    rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  have hst1 := resStaged_of_speStaged hst hjws
  refine tailWriteResult_ok env x R0 s0 s1 answers (.error e) errTag w0 w1 w2
    (unpack64List bws) H hm1 hst1 ?_
  refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
    hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
    ⟨hx28_1, hx22_1, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
    hstack_le, ?_⟩
  have hjoin_low :
      memRegion (sp + 0x110#64) 0x35a ∗ memRegion (sp + 0x46a#64) 0x36 =
        memRegion (sp + 0x110#64) 0x390 :=
    (memRegion_split' (b := sp + 0x110#64) (b' := sp + 0x46a#64) (n := 0x35a) (k := 0x36)
      (by decide) (by bv_omega) (by decide)).symm
  have hbws_mem : words64At (sp + 0x9d0#64) bws ⊢ memRegion (sp + 0x9d0#64) 0xd8 := by
    have h0xd8 : (0xd8 : Nat) = 8 * bws.length := by omega
    rw [h0xd8]
    exact words64At_entails_memRegion (sp + 0x9d0#64) bws (by omega)
  have hjoin_high :
      memRegion (sp + 0x578#64) 0x608 =
        memRegion (sp + 0x578#64) 0x458 ∗ memRegion (sp + 0x9d0#64) 0xd8 ∗
          memRegion (sp + 0xaa8#64) 0xd8 := by
    rw [memRegion_split' (b := sp + 0x578#64) (b' := sp + 0x9d0#64) (n := 0x458) (k := 0x1b0)
        (by decide) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 0x9d0#64) (b' := sp + 0xaa8#64) (n := 0xd8) (k := 0xd8)
        (by decide) (by bv_omega) (by decide)]
  have hmf2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left hbws_mem)) hmf1
  have heq :
      ((memRegion (sp + 0x9d0#64) 0xd8 ∗ words64At (sp + 0x4a0#64) bws) ∗ F) =
      ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ unpack64List bws) ∗ memRegion (sp + 0x578#64) 0x608 ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
    dsimp only [F]
    rw [← words64At_eq_pointsToBytes (sp + 0x4a0#64) bws, ← hjoin_low, hjoin_high]
    ac_rfl
  rwa [← heq]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
