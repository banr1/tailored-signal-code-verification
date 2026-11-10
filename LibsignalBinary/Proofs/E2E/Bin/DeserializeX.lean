/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.Record
public import LibsignalBinary.Proofs.E2E.Record.L1GX.BodyDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.CanonKey
import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Callees
import LibsignalBinary.Proofs.E2E.Record.L1GX.Body
import LibsignalBinary.Proofs.E2E.Record.L1GX.Fields
import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.ProstSSGXRepr
import LibsignalBinary.Proofs.E2E.RecordX.LengthP

/-!
# `SessionRecord::deserialize` (`0x16ed4`) on PQXDH-Scope Records

**Checked by Lean.**

Transports `Record.L1GX.deserializeBodyXExact_ok` to `recordDeserializeOpenSpecP A` (`RecordCanonical`
specialized to `RecordX.DeserializeScopeP`), parameterized by the `merge_field` contract `hMF`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Bin.DeserX

open Arm64 ProofLib ProofLib.ObjectLoad
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin

/-- `Bin.RecordCanonical` specialized to the decoder scope `RecordX.DeserializeScopeP`. -/
def RecordCanonicalP (stateBytes : List (BitVec 8)) (s : Session (List (BitVec 8))) : Prop :=
  stateBytes = encodeRecord ⟨some s⟩ ∧ RecordX.DeserializeScopeP ⟨some s⟩ ∧ ∃ G, BinCanonSession G s

def recordDeserializeOpenSpecP (A : RustAlloc) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × Session (List (BitVec 8))) where
  pre := fun (ptr, bs, out, sess) st =>
    ⌜st.readReg64 .x0 = ptr ∧ (st.readReg64 .x1).toNat = bs.length ∧
      st.readReg64 .x8 = out ∧ RecordCanonicalP bs sess⌝ ∗
      (ptr ↦ₛ bs) ∗ memRegion out 0x170 ∗ A.pool ∗ stackAt st.sp recordDeserializeStack
  post := fun (ptr, bs, out, sess) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (ptr ↦ₛ bs) ∗
      (∃∗ G : SessionGhost, ⌜BinCanonSession G sess⌝ ∗
        sessionRecordAt A out ⟨0#64, 8#64, some G⟩ ⟨some sess⟩) ∗
      A.pool ∗ stackAt s0.sp recordDeserializeStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private abbrev binProgX (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Program :=
  tripleRatchetProg img C ctl abs

private theorem stackAt_sub_splitX (sp : BitVec 64) (k m : Nat) (hkm : k ≤ m)
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

private theorem stackAt_recordDeserialize_splitX (sp : BitVec 64) :
    stackAt sp recordDeserializeStack =
      memRegion (sp - BitVec.ofNat 64 recordDeserializeStack)
        (recordDeserializeStack - Record.recDeserializeStack) ∗
      stackAt sp Record.recDeserializeStack :=
  stackAt_sub_splitX sp Record.recDeserializeStack recordDeserializeStack (by decide) (by decide)

theorem img_eq_sessionImg0X {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) (hb0 : img.base = 0#64) :
    img = Record.sessionImg0 := by
  have h1 : libsignalSessionImage.load 0#64 = .ok img := hb0 ▸ himg
  have h2 : libsignalSessionImage.load 0#64 = .ok Record.sessionImg0 :=
    Record.EntryAux.sessionImg0_base ▸ Record.loads_sessionImg0
  exact Except.ok.inj (h1.symm.trans h2)

private theorem vecAt_prev_zero_eqX (out : BitVec 64) :
    vecAt Record.A0 24 8 (fun (_ : Unit) _ => emp) out 0#64 8#64 [] =
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) := by
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧
      (8#64 : BitVec 64) ≠ 0#64) := by decide
  unfold vecAt vecHeader vecBuf
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ite_true, sepConj_emp,
    Record.SeedLengthFacts.pure_true_sepConj hpure]

theorem binCanonSession_of_l2X {G0 G : SessionGhost} {s : Session (List (BitVec 8))}
    (h0 : BinCanonSession G0 s) (hG : Record.Serialization.CanonSession G s) :
    BinCanonSession G s := by
  have mem_zip_of_mem_left : ∀ {α β : Type} {xs : List α} {ys : List β} {x : α},
      xs.length = ys.length → x ∈ xs → ∃ y, (x, y) ∈ xs.zip ys := by
    intro α β xs
    induction xs with
    | nil => intro ys x _ hx; simp at hx
    | cons x' xs ih =>
      intro ys x hlen hx
      cases ys with
      | nil => simp at hlen
      | cons y' ys =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨y', List.mem_cons_self ..⟩
        · obtain ⟨y, hy⟩ := ih hlen hx
          exact ⟨y, List.mem_cons_of_mem _ hy⟩
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

theorem deserOutRecordX_entails_binCanonSession {G0 : SessionGhost}
    (s : Session (List (BitVec 8)))
    (h0 : BinCanonSession G0 s) (hr : RecordX.DeserializeScopeP ⟨some s⟩) (out : BitVec 64) :
    Record.L1GX.deserOutRecordX out ⟨some s⟩ ⊢
      ∃∗ G : SessionGhost, ⌜BinCanonSession G s⌝ ∗
        sessionRecordAt Record.A0 out ⟨0#64, 8#64, some G⟩ ⟨some s⟩ := by
  have hAfter := Record.L1GX.ssgxAfter_recFieldsX ⟨some s⟩ hr s rfl
  have hRepr := Record.L1GX.Leaf.ProstSSGXRepr.prostSSGX_repr ⟨some s⟩ hr s rfl (out + 0x18#64)
  have hdef :
      Record.L1GX.deserOutRecordX out ⟨some s⟩ =
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          Record.L1GX.prostSSGXAt Record.A0 (out + 0x18#64) (Record.L1GX.ssgxOf s) := by
    unfold Record.L1GX.deserOutRecordX
    rw [hAfter]
    ac_rfl
  rw [hdef]
  refine Entails.trans (sepConj_mono_right hRepr) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun G => ?_
  have h1 :
      (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
        (⌜Record.Serialization.CanonSession G s⌝ ∗
          Record.sessionStateReprAt Record.A0 (out + 0x18#64) G s)) =
      (⌜Record.Serialization.CanonSession G s⌝ ∗
        (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          Record.sessionStateReprAt Record.A0 (out + 0x18#64) G s)) := by
    ac_rfl
  rw [h1]
  refine Entails.pure_left fun hcanon => ?_
  refine Entails.sepExists_right G ?_
  refine Entails.pure_right (binCanonSession_of_l2X h0 hcanon) ?_
  unfold sessionRecordAt
  dsimp only
  rw [vecAt_prev_zero_eqX]
  exact Entails.refl _

/-- `SessionRecord::deserialize` against `recordDeserializeOpenSpecP A`, given `merge_field`
contract `hMF`. -/
private theorem sessionRecord_deserialize_okX (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image) (abs : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocHooks Record.A0 abs)
    (hMF : Record.DeserializeSeed.DeserializeCallees C ctl abs →
      Record.L1GX.MergeFieldXOk C ctl (fun _ => True) abs)
    (hb0 : img.base = 0#64) (hA0 : A = Record.A0) :
    subroutine_ok (binProgX img C ctl abs)
      (img.base + deserializeOff) ((recordDeserializeOpenSpecP A).inImage img) := by
  subst hA0
  have himg_eq := img_eq_sessionImg0X hLoads hb0
  have hb_eq : img.base = Record.sessionImg0.base :=
    hb0.trans Record.EntryAux.sessionImg0_base.symm
  have hAddr :
      (tripleRatchetProgAt img.base C ctl abs).fnAddr Record.recDeserializeName =
        img.base + deserializeOff := by
    rw [tripleRatchetProgAt, Program.fnAddr_rebase, deserialize_fnOff]
  have hC := Record.DeserializeSeed.deserializeCallees_ok_of_hooks C ctl hAlloc
  have hdeser : subroutine_ok (binProgX img C ctl abs)
      (img.base + deserializeOff) Record.L1GX.deserializeXExactSpec := by
    rw [binProgX, tripleRatchetProg_eq_tripleRatchetProgAt hLoads, ← hAddr, hb_eq]
    exact Record.L1GX.deserializeBodyXExact_ok C ctl hC (hMF hC)
  refine subroutine_ok_outcome_intro ?_
  intro ⟨ptr, bs, out, sess⟩ R s0 hpc hrun hpre hal
  have hpre' := hpre
  dsimp only [Spec.inImage, recordDeserializeOpenSpecP] at hpre'
  rw [stackAt_recordDeserialize_splitX s0.sp, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hF, hsym⟩, hpre'⟩
  have hF0 : Record.sessionImg0.FrozenLoaded s0 := himg_eq ▸ hF
  have hsym0 : s0.symtab = Record.sessionImg0.symtab := himg_eq ▸ hsym
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1_nat, hx8, hbs, hr, G0, hG0⟩, hmem⟩
  subst hbs
  have hlen_lt : (Record.encodeRecord ⟨some sess⟩).length < 2 ^ 21 :=
    RecordX.encodeRecord_length_lt_P hr
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (Record.encodeRecord ⟨some sess⟩).length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let x_l1 : Record.DeserializeGeneral.DeserializeGenGhost := ⟨ptr, out, ⟨some sess⟩⟩
  let R_l1 : SepProp :=
    Record.A0.pool ∗
    memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack)
      (recordDeserializeStack - Record.recDeserializeStack) ∗ R
  have hpre_l1 : s0.mem ⊨ Record.L1GX.deserializeXExactSpec.pre x_l1 s0 ∗ R_l1 := by
    dsimp only [Record.L1GX.deserializeXExactSpec, Record.L1GX.deserializeXSpec, x_l1, R_l1]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx8, hr, hF0, hsym0⟩, ?_⟩
    convert hmem using 1; ac_rfl
  refine hdeser.mono_outcome x_l1 R_l1 s0 hpc hrun hpre_l1 hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Record.L1GX.deserializeXExactSpec, Record.L1GX.deserOutRawX, x_l1, R_l1] at hq
    have hrepr := deserOutRecordX_entails_binCanonSession sess hG0 hr out
    have hq' := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrepr)))) hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq'
    rcases hq' with ⟨htr, hq_mem⟩
    dsimp only [Spec.inImage, recordDeserializeOpenSpecP]
    rw [stackAt_recordDeserialize_splitX s0.sp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    convert hq_mem using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Record.L1GX.deserializeXExactSpec, Record.L1GX.deserializeXSpec,
      Record.Serialization.allocPanic, Spec.inImage, recordDeserializeOpenSpecP, R_l1] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfail, hq_mem⟩
    refine ⟨hfail, ?_⟩
    have hany : (anyHeap ∗ Record.A0.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack)
          (recordDeserializeStack - Record.recDeserializeStack)) ∗ R ⊢ anyHeap ∗ R :=
      sepConj_mono_left (entails_anyHeap _)
    refine Satisfies.mono hany ?_
    convert hq_mem using 1; ac_rfl
  · dsimp only [Record.L1GX.deserializeXExactSpec, Record.L1GX.deserializeXSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · dsimp only [Record.L1GX.deserializeXExactSpec, Record.L1GX.deserializeXSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim

end CryptoVerification.E2E.Bin.DeserX
