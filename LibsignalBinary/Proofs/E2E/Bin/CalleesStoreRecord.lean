/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon
public import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.Skeleton
public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.BodyDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.CanonKey
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Skeleton
import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.Bridge
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.ChainMerge
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.DeserializeLeaves
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.MergeField
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Root
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Callees
import LibsignalBinary.Proofs.E2E.Record.Serialization.Serialize
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From

@[expose] public section

namespace CryptoVerification.E2E.Bin

open Arm64 ProofLib ProofLib.ObjectLoad
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.InMem

variable {C : Crypto} {A : RustAlloc} {S : SpqrModel}

local notation "binProg" img:arg C:arg ctl:arg abs:arg =>
  (tripleRatchetProg (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Program)

abbrev StoreRecEnv (C : Crypto) (A : RustAlloc) (S : SpqrModel) (img : Obj.Image)
    (_ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img ∧ BinHooks C A S abs

abbrev inMemSavePollOff : BitVec 64 := 0x077cc#64

/-! ## Store Shim Bridges (`0x2ddc0`, `0x2f458`, `0x2f408`) -/

private theorem stackAt_sub_split0 (sp : BitVec 64) (k m : Nat) (hkm : k ≤ m)
    (hm : m ≤ 2 ^ 64) :
    stackAt sp m =
      memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  unfold stackAt
  exact memRegion_split' (b := sp - BitVec.ofNat 64 m) (b' := sp - BitVec.ofNat 64 k)
    (N := m) (n := m - k) (k := k) (by omega)
    (by
      have h1 : BitVec.ofNat 64 m = BitVec.ofNat 64 (m - k) + BitVec.ofNat 64 k := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hkm]
      rw [h1]
      bv_lin)
    (by omega)

/-! ## Store Poll-Closure Bridges (`0x077cc`, `0x08ee4`, `0x08ce4`) -/

theorem inMemSaveIdentity_closure_ok' (ctl : BitVec 64)
    (img : Obj.Image) (abs : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hHooks : HashbrownBin.HashbrownBinHooks A (Rust.withPanics (tripleRatchetExterns C ctl abs))) :
    subroutine_ok (binProg img C ctl abs)
      (img.base + inMemSavePollOff) ((HashbrownBin.saveIdentityEmptySpec A).inImage img) := by
  have hProg :
      binProg img C ctl abs =
        HashbrownBin.RebasedProg img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) := by
    rw [tripleRatchetProg_eq_tripleRatchetProgAt hLoads]
  have hAddr :
      (HashbrownBin.RebasedProg img.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
        HashbrownBin.saveIdentityClosureName = img.base + inMemSavePollOff := by
    rw [HashbrownBin.RebasedProg, Program.fnAddr_rebase, HashbrownBin.saveIdentityClosure_fnOff]
  rw [hProg, ← hAddr]
  exact LibsignalTripleRatchet.subroutine_ok_inImage img
    (HashbrownBin.saveIdentityEmpty_ok img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) A hHooks)

theorem inMemStoreSession_closure_ok' (ctl : BitVec 64)
    (img : Obj.Image) (abs : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hHooks : HashbrownBin.HashbrownBinHooks A (Rust.withPanics (tripleRatchetExterns C ctl abs))) :
    subroutine_ok (binProg img C ctl abs)
      (img.base + SessionStoreImpl.inMemStorePollOff) ((HashbrownBin.storeSessionEmptySpec A).inImage img) := by
  have hProg :
      binProg img C ctl abs =
        HashbrownBin.RebasedProg img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) := by
    rw [tripleRatchetProg_eq_tripleRatchetProgAt hLoads]
  have hAddr :
      (HashbrownBin.RebasedProg img.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
        HashbrownBin.storeSessionClosureName = img.base + SessionStoreImpl.inMemStorePollOff := by
    rw [HashbrownBin.RebasedProg, Program.fnAddr_rebase, HashbrownBin.storeSessionClosure_fnOff]
  rw [hProg, ← hAddr]
  exact LibsignalTripleRatchet.subroutine_ok_inImage img
    (HashbrownBin.storeSessionEmpty_ok img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) A hHooks)

theorem inMemLoadSession_closure_ok' (ctl : BitVec 64)
    (img : Obj.Image) (abs : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hHooks : HashbrownBin.HashbrownBinHooks A (Rust.withPanics (tripleRatchetExterns C ctl abs))) :
    subroutine_ok (binProg img C ctl abs)
      (img.base + inMemLoadPollOff) ((HashbrownBin.loadSessionSingleSpec A).inImage img) := by
  have hProg :
      binProg img C ctl abs =
        HashbrownBin.RebasedProg img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) := by
    rw [tripleRatchetProg_eq_tripleRatchetProgAt hLoads]
  have hAddr :
      (HashbrownBin.RebasedProg img.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
        HashbrownBin.loadSessionClosureName = img.base + inMemLoadPollOff := by
    rw [HashbrownBin.RebasedProg, Program.fnAddr_rebase, HashbrownBin.loadSessionClosure_fnOff]
  rw [hProg, ← hAddr]
  exact LibsignalTripleRatchet.subroutine_ok_inImage img
    (HashbrownBin.loadSessionSingle_ok img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) A hHooks)

theorem inMemLoadSession_recordSingle_ok' (ctl : BitVec 64)
    (img : Obj.Image) (abs : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hHooks : HashbrownBin.HashbrownBinHooks A (Rust.withPanics (tripleRatchetExterns C ctl abs))) :
    subroutine_ok (binProg img C ctl abs)
      (img.base + inMemLoadPollOff) ((SessionStoreImpl.loadSessionRecordSingleSpec A).inImage img) := by
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hLoads]
  exact LibsignalTripleRatchet.subroutine_ok_inImage img
    (SessionStoreImpl.loadSessionRecordSingle_ok hHooks)

theorem inMemStoreSession_recordSingleHit_ok' (ctl : BitVec 64)
    (img : Obj.Image) (abs : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hHooks : HashbrownBin.HashbrownBinHooks A (Rust.withPanics (tripleRatchetExterns C ctl abs))) :
    subroutine_ok (binProg img C ctl abs)
      (img.base + SessionStoreImpl.inMemStorePollOff) ((SessionStoreImpl.storeSessionRecordSingleHitSpec A).inImage img) := by
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hLoads]
  exact LibsignalTripleRatchet.subroutine_ok_inImage img
    (SessionStoreImpl.storeSessionRecordSingleHit_ok hHooks)

/-! ## Record Serialization and Deserialization Bridges -/

theorem sessionRecord_serialize_canon_ok' (ctl : BitVec 64)
    (img : Obj.Image) (abs : String → Option (State → State))
    (hEnv : StoreRecEnv C A S img ctl abs) :
    subroutine_ok (binProg img C ctl abs)
      (img.base + serializeOff) ((Record.Serialization.serializeCanonSpec A).inImage img) := by
  have hSer := Record.Serialization.serializeCanon_ok img.base C A ctl abs hEnv.2.alloc
  have hAddr :
      (tripleRatchetProgAt img.base C ctl abs).fnAddr Record.Serialization.serializeName = img.base + serializeOff := by
    change (tripleRatchetProgAt img.base C ctl abs).fnAddr recordSerializeName = img.base + serializeOff
    rw [tripleRatchetProgAt, Program.fnAddr_rebase, serialize_fnOff]
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hEnv.1, ← hAddr]
  exact LibsignalTripleRatchet.subroutine_ok_inImage img hSer

theorem sessionRecord_deserialize_gen_ok' (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hEnv : StoreRecEnv C Record.A0 S Record.sessionImg0 ctl abs) :
    subroutine_ok (binProg Record.sessionImg0 C ctl abs)
      (Record.sessionImg0.base + deserializeOff) Record.DeserializeGeneral.deserializeGenSpec := by
  have hDeser := Record.DeserializeGeneral.deserializeGen_ok C ctl hEnv.2.alloc
  have hAddr :
      (tripleRatchetProgAt Record.sessionImg0.base C ctl abs).fnAddr Record.recDeserializeName =
        Record.sessionImg0.base + deserializeOff := by
    rw [tripleRatchetProgAt, Program.fnAddr_rebase, deserialize_fnOff]
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hEnv.1, ← hAddr]
  exact hDeser

private theorem mem_zip_of_mem_left :
    ∀ {α β : Type} {xs : List α} {ys : List β} {x : α},
      xs.length = ys.length → x ∈ xs → ∃ y, (x, y) ∈ xs.zip ys
  | _, _, [], [], _, _, hx => by simp at hx
  | _, _, x' :: xs, y' :: ys, x, hlen, hx => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨y', List.mem_cons_self ..⟩
    · obtain ⟨y, hy⟩ := mem_zip_of_mem_left hlen hx
      exact ⟨y, List.mem_cons_of_mem _ hy⟩

theorem binCanonSession_of_canonSession {G0 G : SessionGhost} {s : Session (List (BitVec 8))}
    (h0 : BinCanonSession G0 s) (hG : Record.Serialization.CanonSession G s) :
    BinCanonSession G s := by
  rcases h0 with ⟨_, hwf, _, _, _, hrc_len, hrc_mk, _, halice, hkyber, hpq, henc⟩
  rcases hG with ⟨hlocal, hrem, hsender, hlen_eq, hzip, hpend⟩
  refine ⟨⟨hlocal, hrem, hsender, hlen_eq, hzip, hpend⟩,
    hwf, hlocal, ?_, ?_, hrc_len, hrc_mk, ?_, halice, hkyber, hpq, henc⟩
  · cases hri : s.state.remoteIdentity <;> simpa [hri] using hrem
  · revert hsender
    unfold Record.Serialization.CanonSender
    cases G.sender <;> cases s.state.senderChain <;> intro hsender
    · exact True.intro
    · exact hsender
    · exact hsender
    · exact hsender.1
  · intro cg hcg
    obtain ⟨rc, hmem⟩ := mem_zip_of_mem_left hlen_eq hcg
    have hcc := hzip (cg, rc) hmem
    have hser_len : rc.senderRatchetKey.serialize.length = 33 :=
      PublicKey.serialize_length rc.senderRatchetKey
    exact ⟨hcc.1.trans (by rfl) ▸ hser_len, hcc.2⟩

theorem canonRecord_to_serializationCanon {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (h : CanonRecord g r) :
    Record.Serialization.CanonRecord g r := by
  revert h
  unfold CanonRecord Record.Serialization.CanonRecord Record.Serialization.CanonCur
  cases g.cur <;> cases r.currentSession <;> intro h
  · exact True.intro
  · exact h
  · exact h
  · exact h.toCanonSession

private theorem stackAt_sub_split (sp : BitVec 64) (k m : Nat) (hkm : k ≤ m)
    (hm : m ≤ 2 ^ 64) :
    stackAt sp m =
      memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  unfold stackAt
  have hsplit := memRegion_split' (b := sp - BitVec.ofNat 64 m) (b' := sp - BitVec.ofNat 64 k)
    (N := m) (n := m - k) (k := k) (by omega)
    (by
      have h1 : BitVec.ofNat 64 m = BitVec.ofNat 64 (m - k) + BitVec.ofNat 64 k := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hkm]
      rw [h1]
      bv_lin)
    (by omega)
  exact hsplit

abbrev deserializeRecordStack : Nat := recordDeserializeStack
abbrev serializationRecordStack : Nat := recordSerializeStack

private theorem stackAt_recordSerialize_split (sp : BitVec 64) :
    stackAt sp recordSerializeStack =
      memRegion (sp - BitVec.ofNat 64 recordSerializeStack)
        (recordSerializeStack - Record.Serialization.serializeStack) ∗
      stackAt sp Record.Serialization.serializeStack :=
  stackAt_sub_split sp Record.Serialization.serializeStack recordSerializeStack (by decide) (by decide)

private theorem memRegion_48_split_32_16 (out : BitVec 64) :
    memRegion out 48 = memRegion out 32 ∗ memRegion (out + 32#64) 16 :=
  memRegion_split out 32 16 (by decide)

abbrev serializationRecordSpec (A : RustAlloc) : Spec RecordSerializeGhost :=
  recordSerializeSpec A

/-- Transports `Record.Serialization.serializeCanon_ok` to `recordSerializeSpec`. -/
theorem sessionRecord_serialize_ok' (ctl : BitVec 64)
    (img : Obj.Image) (abs : String → Option (State → State))
    (hEnv : StoreRecEnv C A S img ctl abs) :
    subroutine_ok (binProg img C ctl abs)
      (img.base + serializeOff) ((recordSerializeSpec A).inImage img) := by
  have hser := sessionRecord_serialize_canon_ok' ctl img abs hEnv
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' := hpre
  dsimp only [Spec.inImage, recordSerializeSpec] at hpre'
  rw [memRegion_48_split_32_16 x.out, stackAt_recordSerialize_split s0.sp,
      sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hF, hsym⟩, hpre'⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx8, hcanon, hlen⟩, hmem⟩
  have hcanon_serialize : Record.Serialization.CanonRecord x.g x.r := canonRecord_to_serializationCanon hcanon
  let x_serialize : Record.Serialization.SerializeGhost := ⟨x.self, x.out, x.g, x.r⟩
  let R_serialize : SepProp :=
    memRegion (x.out + 32#64) 16 ∗
    memRegion (s0.sp - BitVec.ofNat 64 recordSerializeStack)
      (recordSerializeStack - Record.Serialization.serializeStack) ∗ R
  have hpre_serialize : s0.mem ⊨ ((Record.Serialization.serializeCanonSpec A).inImage img).pre x_serialize s0 ∗ R_serialize := by
    dsimp only [Spec.inImage, Record.Serialization.serializeCanonSpec, x_serialize, R_serialize]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hF, hsym⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hcanon_serialize, hlen⟩, ?_⟩
    convert hmem using 1; ac_rfl
  refine hser.mono_outcome x_serialize R_serialize s0 hpc hrun hpre_serialize hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, Record.Serialization.serializeCanonSpec, x_serialize, R_serialize] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq_mem⟩
    dsimp only [Spec.inImage, recordSerializeSpec]
    rw [stackAt_recordSerialize_split s0.sp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    convert hq_mem using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, Record.Serialization.serializeCanonSpec, Record.Serialization.allocPanic,
      recordSerializeSpec, R_serialize] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfail, hq_mem⟩
    refine ⟨hfail, ?_⟩
    have hany : (anyHeap ∗ memRegion (x.out + 32#64) 16 ∗
        memRegion (s0.sp - BitVec.ofNat 64 recordSerializeStack)
          (recordSerializeStack - Record.Serialization.serializeStack)) ∗ R ⊢ anyHeap ∗ R :=
      sepConj_mono_left (entails_anyHeap _)
    refine Satisfies.mono hany ?_
    convert hq_mem using 1; ac_rfl
  · dsimp only [Spec.inImage, Record.Serialization.serializeCanonSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · dsimp only [Spec.inImage, Record.Serialization.serializeCanonSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim

private theorem vecAt_prev_zero_eq (out : BitVec 64) :
    vecAt Record.A0 24 8 (fun (_ : Unit) _ => emp) out 0#64 8#64 [] =
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) := by
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧
      (8#64 : BitVec 64) ≠ 0#64) := by decide
  unfold vecAt vecHeader vecBuf
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ite_true, sepConj_emp,
    Record.SeedLengthFacts.pure_true_sepConj hpure]

theorem deserOutRecordG_entails_binCanonSession {G0 : SessionGhost} (s : Session (List (BitVec 8)))
    (h0 : BinCanonSession G0 s) (hr : Record.DeserializeGeneral.DeserializeScope ⟨some s⟩) (out : BitVec 64) :
    Record.DeserializeGeneral.deserOutRecordG out ⟨some s⟩ ⊢
      ∃∗ G : SessionGhost, ⌜BinCanonSession G s⌝ ∗
        sessionRecordAt Record.A0 out ⟨0#64, 8#64, some G⟩ ⟨some s⟩ := by
  have hAfter := Record.DeserializeGeneral.ssgAfter_recFields ⟨some s⟩ hr s rfl
  have hRepr := Record.DeserializeGeneral.prostSSG_repr ⟨some s⟩ hr s rfl (out + 0x18#64)
  have hdef :
      Record.DeserializeGeneral.deserOutRecordG out ⟨some s⟩ =
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          Record.DeserializeGeneral.prostSSGAt Record.A0 (out + 0x18#64) (Record.DeserializeGeneral.ssgOf s) := by
    unfold Record.DeserializeGeneral.deserOutRecordG
    rw [hAfter]
    ac_rfl
  rw [hdef]
  refine Entails.trans (sepConj_mono_right hRepr) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun G => ?_
  have h1 :
      (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
        (⌜Record.Serialization.CanonSession G s⌝ ∗ Record.sessionStateReprAt Record.A0 (out + 0x18#64) G s)) =
      (⌜Record.Serialization.CanonSession G s⌝ ∗
        (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          Record.sessionStateReprAt Record.A0 (out + 0x18#64) G s)) := by
    ac_rfl
  rw [h1]
  refine Entails.pure_left fun hcanon => ?_
  refine Entails.sepExists_right G ?_
  refine Entails.pure_right (binCanonSession_of_canonSession h0 hcanon) ?_
  unfold sessionRecordAt
  dsimp only
  rw [vecAt_prev_zero_eq]
  exact Entails.refl _

private theorem stackAt_recordDeserialize_split (sp : BitVec 64) :
    stackAt sp recordDeserializeStack =
      memRegion (sp - BitVec.ofNat 64 recordDeserializeStack)
        (recordDeserializeStack - Record.recDeserializeStack) ∗
      stackAt sp Record.recDeserializeStack :=
  stackAt_sub_split sp Record.recDeserializeStack recordDeserializeStack (by decide) (by decide)

private noncomputable def deserializeExactSpec : Spec Record.DeserializeGeneral.DeserializeGenGhost where
  pre := Record.DeserializeGeneral.deserializeGenSpec.pre
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ Record.encodeRecord x.r) ∗
      Record.DeserializeGeneral.deserOutRecordG x.out x.r ∗
      stackAt s0.sp Record.recDeserializeStack
  onPanic := Record.DeserializeGeneral.deserializeGenSpec.onPanic

private theorem deserLoopG_run_exact {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hMF : Record.DeserializeGeneral.MergeFieldGenOk C ctl (fun _ => True) abs)
    {x : Record.DeserializeGeneral.DeserializeGenGhost} {R : SepProp}
    {s0 : State} (hr : Record.DeserializeGeneral.DeserializeScope x.r) :
    ∀ (m k : Nat) (s : State), k + m = (Record.DeserializeGeneral.recFields x.r).length →
      Record.DeserializeGeneral.DeserLoopG C ctl x R s0 k s →
      reaches_outcome (Record.DeserializeSeed.recordProg C ctl abs) deserializeExactSpec x R s0 s := by
  intro m
  induction m with
  | zero =>
    intro k s hk hs
    simp only [Nat.add_zero] at hk
    subst hk
    have hexit := Record.DeserializeGeneral.deserLoopExitG_ok C ctl (abs := abs) x R s0 s hr hs
    refine reaches_outcome.of_codeLoaded fun hL => ?_
    obtain ⟨sf, hst, ⟨hret, hcc, hmem⟩ | ⟨hpan, hmem⟩⟩ := hexit hL
    · exact reaches_outcome_steps hst (reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩))
    · exact reaches_outcome_steps hst (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan, hmem⟩)))
  | succ m ih =>
    intro k s hk hs
    have hlt : k < (Record.DeserializeGeneral.recFields x.r).length := by omega
    have hiter := Record.DeserializeGeneral.deserLoopIterG_ok C ctl hMF x R s0 k s hr hlt hs
    refine reaches_outcome.of_codeLoaded fun hL => ?_
    obtain ⟨s', hst, hs' | ⟨hpan, hmem⟩⟩ := hiter hL
    · exact reaches_outcome_steps hst (ih (k + 1) s' (by omega) hs')
    · exact reaches_outcome_steps hst (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan, hmem⟩)))

private theorem deserializeExact_ok (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hAlloc : AllocHooks Record.A0 abs) :
    Record.Serialization.OkAt Record.sessionImg0.base C ctl abs Record.recDeserializeName
      deserializeExactSpec := by
  have hC := Record.DeserializeSeed.deserializeCallees_ok_of_hooks C ctl hAlloc
  have hMF := Record.DeserializeGeneral.mergeFieldGen_ok C ctl hC (Record.DeserializeGeneral.chainMergeGen_ok C ctl hC)
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hal hL => ?_
  have hr : Record.DeserializeGeneral.DeserializeScope x.r := by
    have h := hpre
    simp only [deserializeExactSpec, Record.DeserializeGeneral.deserializeGenSpec, sepConj_assoc, satisfies_pure_sepConj] at h
    exact h.1.2.2.2.1
  obtain ⟨s, hst, hs | ⟨hpan, hmem⟩⟩ :=
    Record.DeserializeGeneral.deserLoopEntryG_ok C ctl hC x R s0 hpc hrun hpre hal hL
  · exact reaches_outcome_steps hst (deserLoopG_run_exact hMF hr _ 0 s (Nat.zero_add _) hs)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan, hmem⟩)))

theorem img_eq_sessionImg0 {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) (hb0 : img.base = 0#64) :
    img = Record.sessionImg0 := by
  have h1 : libsignalSessionImage.load 0#64 = .ok img := hb0 ▸ himg
  have h2 : libsignalSessionImage.load 0#64 = .ok Record.sessionImg0 :=
    Record.EntryAux.sessionImg0_base ▸ Record.loads_sessionImg0
  exact Except.ok.inj (h1.symm.trans h2)

abbrev DeserializeRecordCanonical := RecordCanonical
abbrev deserializeRecordOpenSpec (A : RustAlloc) := recordDeserializeOpenSpec A

/-- Transports `Record.DeserializeGeneral.deserializeExact_ok` to `recordDeserializeOpenSpec A`
when `img.base = 0#64` and `A = Record.A0`. -/
theorem sessionRecord_deserialize_ok' (ctl : BitVec 64)
    (img : Obj.Image) (abs : String → Option (State → State))
    (hEnv : StoreRecEnv C A S img ctl abs)
    (hb0 : img.base = 0#64) (hA0 : A = Record.A0) :
    subroutine_ok (binProg img C ctl abs)
      (img.base + deserializeOff) ((recordDeserializeOpenSpec A).inImage img) := by
  subst hA0
  have himg_eq := img_eq_sessionImg0 hEnv.1 hb0
  have hb_eq : img.base = Record.sessionImg0.base :=
    hb0.trans Record.EntryAux.sessionImg0_base.symm
  have hAddr :
      (tripleRatchetProgAt img.base C ctl abs).fnAddr Record.recDeserializeName =
        img.base + deserializeOff := by
    rw [tripleRatchetProgAt, Program.fnAddr_rebase, deserialize_fnOff]
  have hdeser : subroutine_ok (binProg img C ctl abs)
      (img.base + deserializeOff) deserializeExactSpec := by
    rw [tripleRatchetProg_eq_tripleRatchetProgAt hEnv.1, ← hAddr, hb_eq]
    exact deserializeExact_ok C ctl abs hEnv.2.alloc
  refine subroutine_ok_outcome_intro fun ⟨ptr, bs, out, sess⟩ R s0 hpc hrun hpre hal => ?_
  have hpre' := hpre
  dsimp only [Spec.inImage, recordDeserializeOpenSpec] at hpre'
  rw [stackAt_recordDeserialize_split s0.sp, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hF, hsym⟩, hpre'⟩
  have hF0 : Record.sessionImg0.FrozenLoaded s0 := himg_eq ▸ hF
  have hsym0 : s0.symtab = Record.sessionImg0.symtab := himg_eq ▸ hsym
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1_nat, hx8, hbs, hr, G0, hG0⟩, hmem⟩
  subst hbs
  have hlen_lt : (Record.encodeRecord ⟨some sess⟩).length < 2 ^ 20 :=
    Record.DeserializeGeneral.encodeRecord_length_lt hr
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (Record.encodeRecord ⟨some sess⟩).length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let x_deserialize : Record.DeserializeGeneral.DeserializeGenGhost := ⟨ptr, out, ⟨some sess⟩⟩
  let R_deserialize : SepProp :=
    Record.A0.pool ∗
    memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack)
      (recordDeserializeStack - Record.recDeserializeStack) ∗ R
  have hpre_deserialize : s0.mem ⊨ deserializeExactSpec.pre x_deserialize s0 ∗ R_deserialize := by
    dsimp only [deserializeExactSpec, Record.DeserializeGeneral.deserializeGenSpec, x_deserialize, R_deserialize]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx8, hr, hF0, hsym0⟩, ?_⟩
    convert hmem using 1; ac_rfl
  refine hdeser.mono_outcome x_deserialize R_deserialize s0 hpc hrun hpre_deserialize hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [deserializeExactSpec, x_deserialize, R_deserialize] at hq
    have hrepr := deserOutRecordG_entails_binCanonSession sess hG0 hr out
    have hq' := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrepr)))) hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq'
    rcases hq' with ⟨htr, hq_mem⟩
    dsimp only [Spec.inImage, recordDeserializeOpenSpec]
    rw [stackAt_recordDeserialize_split s0.sp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    convert hq_mem using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [deserializeExactSpec, Record.DeserializeGeneral.deserializeGenSpec, Record.Serialization.allocPanic,
      Spec.inImage, recordDeserializeOpenSpec, R_deserialize] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfail, hq_mem⟩
    refine ⟨hfail, ?_⟩
    have hany : (anyHeap ∗ Record.A0.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack)
          (recordDeserializeStack - Record.recDeserializeStack)) ∗ R ⊢ anyHeap ∗ R :=
      sepConj_mono_left (entails_anyHeap _)
    refine Satisfies.mono hany ?_
    convert hq_mem using 1; ac_rfl
  · dsimp only [deserializeExactSpec, Record.DeserializeGeneral.deserializeGenSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · dsimp only [deserializeExactSpec, Record.DeserializeGeneral.deserializeGenSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim

end CryptoVerification.E2E.Bin
