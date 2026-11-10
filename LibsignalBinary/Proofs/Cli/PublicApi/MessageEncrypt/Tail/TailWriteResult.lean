/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResult
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.Common
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFetch
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# T2 Result Writer and T3 Epilogue Tail (`+0x5f8..+0x660`)

Proves `tailWriteResult_ok` (and `tailWriteResult_ok_trap`), writing the 248-byte `Result` value to
`[x19]` and executing the function epilogue to establish `withStoresEncSpecV`'s postcondition.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 800000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult.writeResult_sepWP_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {sp ret : BitVec 64}
    {w0 w1 w2 w3 : BitVec 64} {bws rws4 rws27 : List (BitVec 64)} {s0 s : State}
    (hbws : bws.length = 27) (hr4 : rws4.length = 4) (hr27 : rws27.length = 27)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x5f8#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx19 : s.readReg64 .x19 = ret)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hx22 : s.readReg64 .x22 = w0)
    (hx27 : s.readReg64 .x27 = w1)
    (hx21 : s.readReg64 .x21 = w2)
    (hx23 : s.readReg64 .x23 = w3) :
    SepWP (trTrapProgAt b C abs) (s0.readReg64 .lr) s
      (words64At (sp + 0x4a0#64) bws ∗ words64At ret rws4 ∗
        words64At (ret + 0x20#64) rws27 ∗ encSavedRegsAtSp sp s0)
      (fun sf P_f =>
        sf.sp = sp + 0xbe0#64 ∧
        sf.trace = s.trace ∧
        (sf.readReg64 .x19 = s0.readReg64 .x19 ∧
         sf.readReg64 .x20 = s0.readReg64 .x20 ∧
         sf.readReg64 .x21 = s0.readReg64 .x21 ∧
         sf.readReg64 .x22 = s0.readReg64 .x22 ∧
         sf.readReg64 .x23 = s0.readReg64 .x23 ∧
         sf.readReg64 .x24 = s0.readReg64 .x24 ∧
         sf.readReg64 .x25 = s0.readReg64 .x25 ∧
         sf.readReg64 .x26 = s0.readReg64 .x26 ∧
         sf.readReg64 .x27 = s0.readReg64 .x27 ∧
         sf.readReg64 .x28 = s0.readReg64 .x28 ∧
         sf.readReg64 .x29 = s0.readReg64 .x29 ∧
         calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        P_f = (words64At (sp + 0x4a0#64) bws ∗ words64At ret [w0, w1, w2, w3] ∗
          words64At (ret + 0x20#64) bws ∗ encSavedRegsAtSp sp s0)) := by
  subst hsp
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches_cli b (Rust.withPanics (trTrapExterns C abs)) hfn 1528 104
  generalize_entry (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  rw [words64At_27 (s.sp + 0x4a0#64) hbws,
      words64At_4 ret hr4,
      words64At_27 (ret + 0x20#64) hr27]
  unfold encSavedRegsAtSp
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  refine ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  rw [words64At_27 (ret + 0x20#64) hbws]
  simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult.writeResult_sepWP {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp ret : BitVec 64}
    {w0 w1 w2 w3 : BitVec 64} {bws rws4 rws27 : List (BitVec 64)} {s0 s : State}
    (hbws : bws.length = 27) (hr4 : rws4.length = 4) (hr27 : rws27.length = 27)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x5f8#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx19 : s.readReg64 .x19 = ret)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hx22 : s.readReg64 .x22 = w0)
    (hx27 : s.readReg64 .x27 = w1)
    (hx21 : s.readReg64 .x21 = w2)
    (hx23 : s.readReg64 .x23 = w3) :
    SepWP (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .lr) s
      (words64At (sp + 0x4a0#64) bws ∗ words64At ret rws4 ∗
        words64At (ret + 0x20#64) rws27 ∗ encSavedRegsAtSp sp s0)
      (fun sf P_f =>
        sf.sp = sp + 0xbe0#64 ∧
        sf.trace = s.trace ∧
        (sf.readReg64 .x19 = s0.readReg64 .x19 ∧
         sf.readReg64 .x20 = s0.readReg64 .x20 ∧
         sf.readReg64 .x21 = s0.readReg64 .x21 ∧
         sf.readReg64 .x22 = s0.readReg64 .x22 ∧
         sf.readReg64 .x23 = s0.readReg64 .x23 ∧
         sf.readReg64 .x24 = s0.readReg64 .x24 ∧
         sf.readReg64 .x25 = s0.readReg64 .x25 ∧
         sf.readReg64 .x26 = s0.readReg64 .x26 ∧
         sf.readReg64 .x27 = s0.readReg64 .x27 ∧
         sf.readReg64 .x28 = s0.readReg64 .x28 ∧
         sf.readReg64 .x29 = s0.readReg64 .x29 ∧
         calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        P_f = (words64At (sp + 0x4a0#64) bws ∗ words64At ret [w0, w1, w2, w3] ∗
          words64At (ret + 0x20#64) bws ∗ encSavedRegsAtSp sp s0)) := by
  subst hsp
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1528 104
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  rw [words64At_27 (s.sp + 0x4a0#64) hbws,
      words64At_4 ret hr4,
      words64At_27 (ret + 0x20#64) hr27]
  unfold encSavedRegsAtSp
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  refine ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  rw [words64At_27 (ret + 0x20#64) hbws]
  simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

open CryptoVerification.LibsignalPublicApi.StoreKit

variable {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)}
  {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
  {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult.tailWriteResult_ok_trap (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) (w0 w1 w2 w3 : BitVec 64)
    (bs : List (BitVec 8)) (H : SepProp)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers res s0 s)
    (hst : ResStaged A x.ret res [w0, w1, w2, w3] bs H)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x5f8#64)
      (fun sp s => s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x22 = w0 ∧
        s.readReg64 .x27 = w1 ∧ s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
        memRegion (sp + 0x578#64) 0x608 ∗ H)
      R s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  rcases hm with ⟨⟨hmod_res, hcallsRel, hidCallsRel⟩, htrace⟩
  rcases hst with ⟨hres_np, _, hbs_len, hres_ent⟩
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx28, hx22, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry_trap (C := C) (abs := abs) env.loads] at hpc
  obtain ⟨bws, hbws, hbs_eq⟩ := exists_unpack64List 27 (by omega : bs.length = 8 * 27)
  have hbs_words : ∀ a : BitVec 64, (a ↦ₛ bs) = words64At a bws := fun a => by
    rw [hbs_eq, ← words64At_eq_pointsToBytes]
  let sp := s0.sp - 0xbe0#64
  let stf := kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2
  let istf := ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2
  let R' := encStoreExtra kit stf ikit istf x s0 ∗ R
  change s.mem ⊨
    (memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
      memRegion (sp + 0x578#64) 0x608 ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R' at hmem
  have hret_split : memRegion x.ret 248 =
      memRegion x.ret (8 * 4) ∗ memRegion (x.ret + 0x20#64) (8 * 27) :=
    memRegion_split' (b := x.ret) (b' := x.ret + 0x20#64) (n := 8 * 4) (k := 8 * 27)
      (by decide) rfl (by decide)
  let F := memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
    memRegion (sp + 0x578#64) 0x608 ∗ H ∗ stackAt sp encSubStack ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗ A.pool
  have hmem1 : s.mem ⊨ memRegion x.ret (8 * 4) ∗ (memRegion (x.ret + 0x20#64) (8 * 27) ∗
      words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R')) := by
    have heq :
      ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
        memRegion (sp + 0x578#64) 0x608 ∗ H) ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R') =
      (memRegion x.ret (8 * 4) ∗ (memRegion (x.ret + 0x20#64) (8 * 27) ∗
      words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R'))) := by
      dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon, F, sp]
      rw [hbs_words (s0.sp - 0xbe0#64 + 0x4a0#64), hret_split, encSavedRegs_eq_atSp s0.sp s0]
      ac_rfl
    rwa [← heq]
  obtain ⟨rws4, hr4, hmem2⟩ := memRegion_eq_exists_words64At 4 x.ret (by decide) s.mem _ hmem1
  rw [← sepConj_assoc, sepConj_comm (words64At x.ret rws4), sepConj_assoc] at hmem2
  obtain ⟨rws27, hr27, hmem3⟩ :=
    memRegion_eq_exists_words64At 27 (x.ret + 0x20#64) (by decide) s.mem _ hmem2
  have hmem4 : s.mem ⊨
      (words64At (sp + 0x4a0#64) bws ∗ words64At x.ret rws4 ∗
        words64At (x.ret + 0x20#64) rws27 ∗ encSavedRegsAtSp sp s0) ∗ (F ∗ R') := by
    have heq :
      (words64At (x.ret + 0x20#64) rws27 ∗ words64At x.ret rws4 ∗
        words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R')) =
      ((words64At (sp + 0x4a0#64) bws ∗ words64At x.ret rws4 ∗
        words64At (x.ret + 0x20#64) rws27 ∗ encSavedRegsAtSp sp s0) ∗ (F ∗ R')) := by ac_rfl
    rwa [← heq]
  intro hL
  have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult.writeResult_sepWP_trap (s0 := s0) hbws hr4 hr27 hpc hrun hsp_al hsp hx19 hx28 hx22 hx27 hx21 hx23
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hspf, htracef, hcsf, rfl⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hmem4 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  rw [hvregs] at hcsf
  have hspf0 : sf.sp = s0.sp := by
    rw [hspf]; bv_omega
  refine ⟨sf, hsteps, Or.inr (Or.inl ⟨⟨hpcf, hspf0, hrunf⟩, ⟨hspf0, hcsf⟩, ?_⟩)⟩
  let PostBody :=
    kit.storeAt x.ssA stf ∗
    ikit.identityAt x.idA istf ∗
    apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 ∗
    nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
    logOff img ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ A.pool
  have hmf1 : sf.mem ⊨
      ((words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H) ∗
       (memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ bs) ∗ memRegion (sp + 0x578#64) 0x608 ∗
        encSavedRegs s0.sp s0 ∗ stackAt sp encSubStack) ∗
       (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
        logOff img ∗ A.pool)) ∗ R' := by
    have heq :
      ((words64At (sp + 0x4a0#64) bws ∗ words64At x.ret [w0, w1, w2, w3] ∗
        words64At (x.ret + 0x20#64) bws ∗ encSavedRegsAtSp sp s0) ∗ (F ∗ R')) =
      (((words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H) ∗
       (memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ bs) ∗ memRegion (sp + 0x578#64) 0x608 ∗
        encSavedRegs s0.sp s0 ∗ stackAt sp encSubStack) ∗
       (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
        logOff img ∗ A.pool)) ∗ R') := by
      dsimp only [F, sp]
      rw [← hbs_words (s0.sp - 0xbe0#64 + 0x4a0#64), ← hbs_words (x.ret + 0x20#64),
          ← encSavedRegs_eq_atSp s0.sp s0]
      ac_rfl
    rwa [← heq]
  have hstack_ent := writeResult_frame_entails_stackAtV kit.ss_vt ikit.id_vt x s0 bs hbs_len
  have hres_ent' :
      words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H ⊢
        apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 := by
    rw [hmod_res]; exact hres_ent
  have hmf2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono hres_ent' (sepConj_mono_left hstack_ent))) hmf1
  have hmf2' : sf.mem ⊨
      (encStoreExtra kit stf ikit istf x s0 ∗ stackAt s0.sp withStoresEncStack) ∗
      (apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 ∗
       nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
       logOff img ∗ A.pool) ∗ R := by
    have heq :
      ((apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 ∗
        stackAt s0.sp withStoresEncStack ∗
        (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
         logOff img ∗ A.pool)) ∗ R') =
      ((encStoreExtra kit stf ikit istf x s0 ∗ stackAt s0.sp withStoresEncStack) ∗
       (apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
        logOff img ∗ A.pool) ∗ R) := by
      dsimp only [R']; ac_rfl
    rwa [← heq]
  have hmf2'' := Satisfies.mono
    (sepConj_mono_left (withStoresEncStack_join_extra kit stf ikit istf x s0)) hmf2'
  have hmf3 : sf.mem ⊨ PostBody ∗ R := by
    have heq :
      ((kit.storeAt x.ssA stf ∗ ikit.identityAt x.idA istf ∗
        stackAt s0.sp (withStoresEncStackV kit ikit)) ∗
       (apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
        logOff img ∗ A.pool) ∗ R) = (PostBody ∗ R) := by
      dsimp only [PostBody]; ac_rfl
    rwa [← heq]
  have hpure : (x.model C S uuidTryParse answers).1 ≠ .error .panic ∧
      kit.callsRel st0 answers (x.model C S uuidTryParse answers).2 ∧
      ikit.idCallsRel ist0 answers (x.model C S uuidTryParse answers).2 ∧
      sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S uuidTryParse answers).2 :=
    ⟨hmod_res ▸ hres_np, hcallsRel, hidCallsRel, htracef.trans htrace⟩
  have hmf4 : sf.mem ⊨
      (⌜(x.model C S uuidTryParse answers).1 ≠ .error .panic ∧
        kit.callsRel st0 answers (x.model C S uuidTryParse answers).2 ∧
        ikit.idCallsRel ist0 answers (x.model C S uuidTryParse answers).2 ∧
        sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S uuidTryParse answers).2⌝ ∗
       PostBody) ∗ R := by
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, hmf3⟩
  exact Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro answers)) hmf4

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult.tailWriteResult_ok (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) (w0 w1 w2 w3 : BitVec 64)
    (bs : List (BitVec 8)) (H : SepProp)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers res s0 s)
    (hst : ResStaged A x.ret res [w0, w1, w2, w3] bs H)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x5f8#64)
      (fun sp s => s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x22 = w0 ∧
        s.readReg64 .x27 = w1 ∧ s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
        memRegion (sp + 0x578#64) 0x608 ∗ H)
      R s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  rcases hm with ⟨⟨hmod_res, hcallsRel, hidCallsRel⟩, htrace⟩
  rcases hst with ⟨hres_np, _, hbs_len, hres_ent⟩
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx28, hx22, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  obtain ⟨bws, hbws, hbs_eq⟩ := exists_unpack64List 27 (by omega : bs.length = 8 * 27)
  have hbs_words : ∀ a : BitVec 64, (a ↦ₛ bs) = words64At a bws := fun a => by
    rw [hbs_eq, ← words64At_eq_pointsToBytes]
  let sp := s0.sp - 0xbe0#64
  let stf := kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2
  let istf := ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2
  let R' := encStoreExtra kit stf ikit istf x s0 ∗ R
  change s.mem ⊨
    (memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
      memRegion (sp + 0x578#64) 0x608 ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R' at hmem
  have hret_split : memRegion x.ret 248 =
      memRegion x.ret (8 * 4) ∗ memRegion (x.ret + 0x20#64) (8 * 27) :=
    memRegion_split' (b := x.ret) (b' := x.ret + 0x20#64) (n := 8 * 4) (k := 8 * 27)
      (by decide) rfl (by decide)
  let F := memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
    memRegion (sp + 0x578#64) 0x608 ∗ H ∗ stackAt sp encSubStack ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗ A.pool
  have hmem1 : s.mem ⊨ memRegion x.ret (8 * 4) ∗ (memRegion (x.ret + 0x20#64) (8 * 27) ∗
      words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R')) := by
    have heq :
      ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
        memRegion (sp + 0x578#64) 0x608 ∗ H) ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R') =
      (memRegion x.ret (8 * 4) ∗ (memRegion (x.ret + 0x20#64) (8 * 27) ∗
      words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R'))) := by
      dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon, F, sp]
      rw [hbs_words (s0.sp - 0xbe0#64 + 0x4a0#64), hret_split, encSavedRegs_eq_atSp s0.sp s0]
      ac_rfl
    rwa [← heq]
  obtain ⟨rws4, hr4, hmem2⟩ := memRegion_eq_exists_words64At 4 x.ret (by decide) s.mem _ hmem1
  rw [← sepConj_assoc, sepConj_comm (words64At x.ret rws4), sepConj_assoc] at hmem2
  obtain ⟨rws27, hr27, hmem3⟩ :=
    memRegion_eq_exists_words64At 27 (x.ret + 0x20#64) (by decide) s.mem _ hmem2
  have hmem4 : s.mem ⊨
      (words64At (sp + 0x4a0#64) bws ∗ words64At x.ret rws4 ∗
        words64At (x.ret + 0x20#64) rws27 ∗ encSavedRegsAtSp sp s0) ∗ (F ∗ R') := by
    have heq :
      (words64At (x.ret + 0x20#64) rws27 ∗ words64At x.ret rws4 ∗
        words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R')) =
      ((words64At (sp + 0x4a0#64) bws ∗ words64At x.ret rws4 ∗
        words64At (x.ret + 0x20#64) rws27 ∗ encSavedRegsAtSp sp s0) ∗ (F ∗ R')) := by ac_rfl
    rwa [← heq]
  intro hL
  have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult.writeResult_sepWP (s0 := s0) hbws hr4 hr27 hpc hrun hsp_al hsp hx19 hx28 hx22 hx27 hx21 hx23
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hspf, htracef, hcsf, rfl⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hmem4 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  rw [hvregs] at hcsf
  have hspf0 : sf.sp = s0.sp := by
    rw [hspf]; bv_omega
  refine ⟨sf, hsteps, Or.inr (Or.inl ⟨⟨hpcf, hspf0, hrunf⟩, ⟨hspf0, hcsf⟩, ?_⟩)⟩
  let PostBody :=
    kit.storeAt x.ssA stf ∗
    ikit.identityAt x.idA istf ∗
    apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 ∗
    nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
    logOff img ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ A.pool
  have hmf1 : sf.mem ⊨
      ((words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H) ∗
       (memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ bs) ∗ memRegion (sp + 0x578#64) 0x608 ∗
        encSavedRegs s0.sp s0 ∗ stackAt sp encSubStack) ∗
       (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
        logOff img ∗ A.pool)) ∗ R' := by
    have heq :
      ((words64At (sp + 0x4a0#64) bws ∗ words64At x.ret [w0, w1, w2, w3] ∗
        words64At (x.ret + 0x20#64) bws ∗ encSavedRegsAtSp sp s0) ∗ (F ∗ R')) =
      (((words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H) ∗
       (memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ bs) ∗ memRegion (sp + 0x578#64) 0x608 ∗
        encSavedRegs s0.sp s0 ∗ stackAt sp encSubStack) ∗
       (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
        logOff img ∗ A.pool)) ∗ R') := by
      dsimp only [F, sp]
      rw [← hbs_words (s0.sp - 0xbe0#64 + 0x4a0#64), ← hbs_words (x.ret + 0x20#64),
          ← encSavedRegs_eq_atSp s0.sp s0]
      ac_rfl
    rwa [← heq]
  have hstack_ent := writeResult_frame_entails_stackAtV kit.ss_vt ikit.id_vt x s0 bs hbs_len
  have hres_ent' :
      words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H ⊢
        apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 := by
    rw [hmod_res]; exact hres_ent
  have hmf2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono hres_ent' (sepConj_mono_left hstack_ent))) hmf1
  have hmf2' : sf.mem ⊨
      (encStoreExtra kit stf ikit istf x s0 ∗ stackAt s0.sp withStoresEncStack) ∗
      (apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 ∗
       nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
       logOff img ∗ A.pool) ∗ R := by
    have heq :
      ((apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 ∗
        stackAt s0.sp withStoresEncStack ∗
        (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
         logOff img ∗ A.pool)) ∗ R') =
      ((encStoreExtra kit stf ikit istf x s0 ∗ stackAt s0.sp withStoresEncStack) ∗
       (apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
        logOff img ∗ A.pool) ∗ R) := by
      dsimp only [R']; ac_rfl
    rwa [← heq]
  have hmf2'' := Satisfies.mono
    (sepConj_mono_left (withStoresEncStack_join_extra kit stf ikit istf x s0)) hmf2'
  have hmf3 : sf.mem ⊨ PostBody ∗ R := by
    have heq :
      ((kit.storeAt x.ssA stf ∗ ikit.identityAt x.idA istf ∗
        stackAt s0.sp (withStoresEncStackV kit ikit)) ∗
       (apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
        logOff img ∗ A.pool) ∗ R) = (PostBody ∗ R) := by
      dsimp only [PostBody]; ac_rfl
    rwa [← heq]
  have hpure : (x.model C S uuidTryParse answers).1 ≠ .error .panic ∧
      kit.callsRel st0 answers (x.model C S uuidTryParse answers).2 ∧
      ikit.idCallsRel ist0 answers (x.model C S uuidTryParse answers).2 ∧
      sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S uuidTryParse answers).2 :=
    ⟨hmod_res ▸ hres_np, hcallsRel, hidCallsRel, htracef.trans htrace⟩
  have hmf4 : sf.mem ⊨
      (⌜(x.model C S uuidTryParse answers).1 ≠ .error .panic ∧
        kit.callsRel st0 answers (x.model C S uuidTryParse answers).2 ∧
        ikit.idCallsRel ist0 answers (x.model C S uuidTryParse answers).2 ∧
        sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S uuidTryParse answers).2⌝ ∗
       PostBody) ∗ R := by
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, hmf3⟩
  exact Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro answers)) hmf4

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult
