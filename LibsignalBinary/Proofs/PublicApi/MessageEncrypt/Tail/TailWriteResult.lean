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
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

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

theorem memRegion_eq_exists_words64At :
    ∀ (n : Nat) (a : BitVec 64), 8 * n ≤ 2 ^ 64 →
      (∀ m R, (m ⊨ memRegion a (8 * n) ∗ R) →
        ∃ ws : List (BitVec 64), ws.length = n ∧ (m ⊨ words64At a ws ∗ R))
  | 0, a, _, m, R, hm => by
    rw [Nat.mul_zero, ProofLib.memRegion_zero] at hm
    exact ⟨[], rfl, hm⟩
  | n + 1, a, hbound, m, R, hm => by
    have hsplit : memRegion a (8 * (n + 1)) = memRegion a 8 ∗ memRegion (a + 8#64) (8 * n) := by
      rw [show 8 * (n + 1) = 8 + 8 * n by omega]
      exact memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 8 * n) rfl rfl (by omega)
    rw [hsplit, ProofLib.memRegion_eight, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists] at hm
    obtain ⟨w, hm⟩ := hm
    rw [sepConj_comm (a ↦₆₄ w), sepConj_assoc] at hm
    obtain ⟨ws, hlen, hm⟩ :=
      memRegion_eq_exists_words64At n (a + 8#64) (by omega) m (R ∗ (a ↦₆₄ w)) hm
    refine ⟨w :: ws, by simp [hlen], ?_⟩
    rw [words64At, sepConj_assoc]
    rw [← sepConj_assoc (words64At (a + 8#64) ws), sepConj_comm _ (a ↦₆₄ w)] at hm
    exact hm

theorem words64At_drop_succ {a : BitVec 64} {i : Nat} {ws : List (BitVec 64)}
    (h : i < ws.length) :
    words64At a (ws.drop i) =
      (a ↦₆₄ ws.getD i 0#64) ∗ words64At (a + 8#64) (ws.drop (i + 1)) := by
  induction i generalizing a ws with
  | zero =>
    cases ws with
    | nil => simp at h
    | cons w ws' => rfl
  | succ i ih =>
    cases ws with
    | nil => simp at h
    | cons w ws' =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
      exact ih h

theorem words64At_drop_eq_emp {a : BitVec 64} {i : Nat} {ws : List (BitVec 64)}
    (h : ws.length ≤ i) :
    words64At a (ws.drop i) = emp := by
  rw [List.drop_eq_nil_of_le h, words64At]

theorem words64At_4 (a : BitVec 64) {ws : List (BitVec 64)} (h : ws.length = 4) :
    words64At a ws =
      (a ↦₆₄ ws.getD 0 0#64) ∗ ((a + 0x08#64) ↦₆₄ ws.getD 1 0#64) ∗
      ((a + 0x10#64) ↦₆₄ ws.getD 2 0#64) ∗ ((a + 0x18#64) ↦₆₄ ws.getD 3 0#64) := by
  conv => lhs; rw [← @List.drop_zero _ ws]
  repeat rw [words64At_drop_succ (by omega)]
  rw [words64At_drop_eq_emp (by omega)]
  simp only [sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem words64At_27 (a : BitVec 64) {ws : List (BitVec 64)} (h : ws.length = 27) :
    words64At a ws =
      (a ↦₆₄ ws.getD 0 0#64) ∗ ((a + 0x08#64) ↦₆₄ ws.getD 1 0#64) ∗
      ((a + 0x10#64) ↦₆₄ ws.getD 2 0#64) ∗ ((a + 0x18#64) ↦₆₄ ws.getD 3 0#64) ∗
      ((a + 0x20#64) ↦₆₄ ws.getD 4 0#64) ∗ ((a + 0x28#64) ↦₆₄ ws.getD 5 0#64) ∗
      ((a + 0x30#64) ↦₆₄ ws.getD 6 0#64) ∗ ((a + 0x38#64) ↦₆₄ ws.getD 7 0#64) ∗
      ((a + 0x40#64) ↦₆₄ ws.getD 8 0#64) ∗ ((a + 0x48#64) ↦₆₄ ws.getD 9 0#64) ∗
      ((a + 0x50#64) ↦₆₄ ws.getD 10 0#64) ∗ ((a + 0x58#64) ↦₆₄ ws.getD 11 0#64) ∗
      ((a + 0x60#64) ↦₆₄ ws.getD 12 0#64) ∗ ((a + 0x68#64) ↦₆₄ ws.getD 13 0#64) ∗
      ((a + 0x70#64) ↦₆₄ ws.getD 14 0#64) ∗ ((a + 0x78#64) ↦₆₄ ws.getD 15 0#64) ∗
      ((a + 0x80#64) ↦₆₄ ws.getD 16 0#64) ∗ ((a + 0x88#64) ↦₆₄ ws.getD 17 0#64) ∗
      ((a + 0x90#64) ↦₆₄ ws.getD 18 0#64) ∗ ((a + 0x98#64) ↦₆₄ ws.getD 19 0#64) ∗
      ((a + 0xa0#64) ↦₆₄ ws.getD 20 0#64) ∗ ((a + 0xa8#64) ↦₆₄ ws.getD 21 0#64) ∗
      ((a + 0xb0#64) ↦₆₄ ws.getD 22 0#64) ∗ ((a + 0xb8#64) ↦₆₄ ws.getD 23 0#64) ∗
      ((a + 0xc0#64) ↦₆₄ ws.getD 24 0#64) ∗ ((a + 0xc8#64) ↦₆₄ ws.getD 25 0#64) ∗
      ((a + 0xd0#64) ↦₆₄ ws.getD 26 0#64) := by
  conv => lhs; rw [← @List.drop_zero _ ws]
  repeat rw [words64At_drop_succ (by omega)]
  rw [words64At_drop_eq_emp (by omega)]
  simp only [sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

def encSavedRegsAtSp (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp + 0xb80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp + 0xb88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp + 0xb90#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp + 0xb98#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp + 0xba0#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp + 0xba8#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp + 0xbb0#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp + 0xbb8#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp + 0xbc0#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp + 0xbc8#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp + 0xbd0#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp + 0xbd8#64) ↦₆₄ s0.readReg64 .x19)

theorem sub_eq_atSp (sp0 d off : BitVec 64) (h : d + off = 0xbe0#64) :
    sp0 - d = (sp0 - 0xbe0#64) + off := by
  bv_omega

theorem encSavedRegs_eq_atSp (sp0 : BitVec 64) (s0 : State) :
    encSavedRegs sp0 s0 = encSavedRegsAtSp (sp0 - 0xbe0#64) s0 := by
  simp only [encSavedRegs, encSavedRegsAtSp,
    sub_eq_atSp sp0 96#64 0xb80#64 rfl, sub_eq_atSp sp0 88#64 0xb88#64 rfl,
    sub_eq_atSp sp0 80#64 0xb90#64 rfl, sub_eq_atSp sp0 72#64 0xb98#64 rfl,
    sub_eq_atSp sp0 64#64 0xba0#64 rfl, sub_eq_atSp sp0 56#64 0xba8#64 rfl,
    sub_eq_atSp sp0 48#64 0xbb0#64 rfl, sub_eq_atSp sp0 40#64 0xbb8#64 rfl,
    sub_eq_atSp sp0 32#64 0xbc0#64 rfl, sub_eq_atSp sp0 24#64 0xbc8#64 rfl,
    sub_eq_atSp sp0 16#64 0xbd0#64 rfl, sub_eq_atSp sp0 8#64 0xbd8#64 rfl]

set_option maxHeartbeats 800000 in
theorem writeResult_sepWP {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp ret : BitVec 64}
    {w0 w1 w2 w3 : BitVec 64} {bws rws4 rws27 : List (BitVec 64)} {s0 s : State}
    (hbws : bws.length = 27) (hr4 : rws4.length = 4) (hr27 : rws27.length = 27)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x5f8#64)
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
  have hfn := libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1528 104
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
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

theorem tailWriteResult_ok (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) (w0 w1 w2 w3 : BitVec 64)
    (bs : List (BitVec 8)) (H : SepProp)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers res s0 s)
    (hst : ResStaged A x.ret res [w0, w1, w2, w3] bs H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0x5f8#64)
      (fun sp s => s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x22 = w0 ∧
        s.readReg64 .x27 = w1 ∧ s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
        memRegion (sp + 0x578#64) 0x608 ∗ H)
      R s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  rcases hm with ⟨⟨hmod_res, hcallsRel, hidCallsRel⟩, htrace⟩
  rcases hst with ⟨hres_np, _, hbs_len, hres_ent⟩
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx28, hx22, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
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
    encCommon A ctl img x (x.draws S answers) s0 ∗ R' at hmem
  have hret_split : memRegion x.ret 248 =
      memRegion x.ret (8 * 4) ∗ memRegion (x.ret + 0x20#64) (8 * 27) :=
    memRegion_split' (b := x.ret) (b' := x.ret + 0x20#64) (n := 8 * 4) (k := 8 * 27)
      (by decide) rfl (by decide)
  let F := memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
    memRegion (sp + 0x578#64) 0x608 ∗ H ∗ stackAt sp encSubStack ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ logOff img ∗ A.pool
  have hmem1 : s.mem ⊨ memRegion x.ret (8 * 4) ∗ (memRegion (x.ret + 0x20#64) (8 * 27) ∗
      words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R')) := by
    have heq :
      ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
        memRegion (sp + 0x578#64) 0x608 ∗ H) ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x (x.draws S answers) s0 ∗ R') =
      (memRegion x.ret (8 * 4) ∗ (memRegion (x.ret + 0x20#64) (8 * 27) ∗
      words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R'))) := by
      dsimp only [encCommon, F, sp]
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
  have hwp := writeResult_sepWP (s0 := s0) hbws hr4 hr27 hpc hrun hsp_al hsp hx19 hx28 hx22 hx27 hx21 hx23
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
    protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
    logOff img ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ A.pool
  have hmf1 : sf.mem ⊨
      ((words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H) ∗
       (memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ bs) ∗ memRegion (sp + 0x578#64) 0x608 ∗
        encSavedRegs s0.sp s0 ∗ stackAt sp encSubStack) ∗
       (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
        logOff img ∗ A.pool)) ∗ R' := by
    have heq :
      ((words64At (sp + 0x4a0#64) bws ∗ words64At x.ret [w0, w1, w2, w3] ∗
        words64At (x.ret + 0x20#64) bws ∗ encSavedRegsAtSp sp s0) ∗ (F ∗ R')) =
      (((words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H) ∗
       (memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ bs) ∗ memRegion (sp + 0x578#64) 0x608 ∗
        encSavedRegs s0.sp s0 ∗ stackAt sp encSubStack) ∗
       (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
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
       protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
       logOff img ∗ A.pool) ∗ R := by
    have heq :
      ((apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 ∗
        stackAt s0.sp withStoresEncStack ∗
        (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
         logOff img ∗ A.pool)) ∗ R') =
      ((encStoreExtra kit stf ikit istf x s0 ∗ stackAt s0.sp withStoresEncStack) ∗
       (apiEncResultAt A x.ret (x.model C S uuidTryParse answers).1 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
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
        protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
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
