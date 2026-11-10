/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefs

/-!
# `SessionRecord::serialize` (`0`-prev and `prev1`) and `Vec<Vec<u8>>::clone` Credit

Proves symbolic `(M : AllocCostModel) [HasFineReallocCredit M]` `PhaseCreditSpec` and
`DeallocCreditSpec` bounds in binary call order for:
1. `optLargeCost_le_two_mul`: `optLargeCost M req ≤ 2 * req` for all `req : Nat` when
   `8195 ≤ smallMaxReq M`.
2. `<Vec<Vec<u8>> as Clone>::clone` on `[enc]` (`vecVecClone1Events enc`) and its epilogue
   deallocation (`dropVecVecClone1Events enc`).
3. `SessionRecord::serialize` on `0`-prev (`Some` and `Option` `RecordGhost`/`SessionRecord`) and
   `prev1` (`previous_sessions = [enc]`), both with exact `sc = 63` epilogue cancellation and with
   `SeqEnv ... FreeOnlyEvs`, plus tight per-size-class `cumSmall` refinements.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit

open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (encodeRecordPrev1Mem)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel SeqEnv FreeOnlyEvs
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  segCloneEvents SegCloneEnv
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (
  ModelHyps PhaseCreditSpec DeallocCreditSpec ConcatEnv
)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (
  optLargeCost vecCloneCum vecCloneLarge
  segCloneCum segCloneLarge segCloneMaxReq
  dropClonedSessionEvents
)

/-! ## 1. Linear `optLargeCost M req ≤ 2 * req` Lemma (`8195 ≤ smallMaxReq M`) -/

/-- Whenever `8195 ≤ smallMaxReq M` (in `fineCostModel`, `smallMaxReq = 135,167`),
`optLargeCost M req ≤ 2 * req` for EVERY `req : Nat`: small requests contribute `0`, while
`sc = 63` requests satisfy `req > 8195` so `req + 8195 ≤ 2 * req`. -/
theorem optLargeCost_le_two_mul {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 8195 ≤ HasFineReallocCredit.smallMaxReq M) (req : Nat) :
    optLargeCost M req ≤ 2 * req := by
  unfold optLargeCost
  split
  · exact Nat.zero_le _
  · rename_i hnot
    have hgt : HasFineReallocCredit.smallMaxReq M < req := Nat.lt_of_not_ge hnot
    have hle := hM.largeCost_le hgt
    omega

theorem vecCloneLarge_le_two_mul {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 8195 ≤ HasFineReallocCredit.smallMaxReq M) (len : Nat) :
    vecCloneLarge M len ≤ 2 * len := by
  unfold vecCloneLarge
  split
  · exact Nat.zero_le _
  · exact optLargeCost_le_two_mul hM hsmall len

/-! ## 2. `<Vec<Vec<u8>> as Clone>::clone` on 1-Element `[enc]` & Epilogue Drop -/

/-- Deterministic allocator events of `<Vec<Vec<u8>> as Clone>::clone` on `[enc]`
(definitionally equal to `Over.VecVecDefsBudget.vecVecClone1Events enc`). -/
def vecVecClone1Events (enc : List (BitVec 8)) : List AllocEvent :=
  rustAllocEvents 24 8 ++ (if enc.length = 0 then [] else rustAllocEvents enc.length 1)

/-- Exact epilogue deallocation events of the temporary 1-element `Vec<Vec<u8>>` `[enc]` in
`CloseSerBodyBCoreG.serPrev1Tail_core_ok_g`: inner `enc` buffer (when `enc.length ≠ 0`) followed
by the `24`-byte outer `Vec` buffer. -/
def dropVecVecClone1Events (enc : List (BitVec 8)) : List AllocEvent :=
  (if enc.length = 0 then [] else rustDeallocEvents enc.length 1) ++
    rustDeallocEvents 24 8

def vecVecClone1Cum (enc : List (BitVec 8)) : Nat :=
  (2 * 24 + 9539) + vecCloneCum enc.length

def vecVecClone1Large (M : AllocCostModel) [HasFineReallocCredit M]
    (enc : List (BitVec 8)) : Nat :=
  optLargeCost M 24 + vecCloneLarge M enc.length

def vecVecClone1MaxReq (enc : List (BitVec 8)) : Nat :=
  max 24 enc.length

theorem PhaseCreditSpec.vecVecClone1 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (enc : List (BitVec 8)) :
    PhaseCreditSpec M (· = vecVecClone1Events enc)
      (vecVecClone1Cum enc)
      (vecVecClone1Large M enc)
      (vecVecClone1Large M enc)
      (vecVecClone1MaxReq enc) := by
  have h24 := SessionCloneCredit.PhaseCreditSpec.rustAlloc_optLarge hM (req := 24) (al := 8) (by decide)
  have henc : PhaseCreditSpec M
      (· = if enc.length = 0 then [] else rustAllocEvents enc.length 1)
      (vecCloneCum enc.length)
      (vecCloneLarge M enc.length)
      (vecCloneLarge M enc.length)
      enc.length := by
    unfold vecCloneCum vecCloneLarge
    exact (SessionCloneCredit.PhaseCreditSpec.condRustAlloc_optLarge hM
      (p := enc.length = 0) (req := enc.length) (al := 1) (by decide)).mono
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by split <;> omega)
  exact SessionCloneCredit.PhaseCreditSpec.append_eq_self h24 henc

theorem DeallocCreditSpec.dropVecVecClone1 (M : AllocCostModel) [HasFineReallocCredit M]
    (enc : List (BitVec 8)) :
    DeallocCreditSpec M (· = dropVecVecClone1Events enc) (vecVecClone1Large M enc) := by
  have henc : DeallocCreditSpec M
      (· = if enc.length = 0 then [] else rustDeallocEvents enc.length 1)
      (vecCloneLarge M enc.length) :=
    SessionCloneCredit.DeallocCreditSpec.condFree_optLarge M (by decide)
  have h24 := SessionCloneCredit.DeallocCreditSpec.free_optLarge M (req := 24) (al := 8) (by decide)
  unfold dropVecVecClone1Events vecVecClone1Large
  exact (SessionCloneCredit.DeallocCreditSpec.append_eq henc h24).mono (by omega)

/-! ## 3. `0`-Prev `SessionRecord::serialize` (`Some` & `Option`) -/

/-- Exact allocator event trace of `SessionRecord::serialize` on a `0`-prev `Some` session:
`SessionStructure::clone` (`segCloneEvents`) → output `Vec::with_capacity(encLen)` →
pre-reserved `encode_varint` + `encode_raw` (`[]`) → `drop_glue<SessionStructure>` (`sc = 63` cancel). -/
def serializeSomeExactEvents (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    List AllocEvent :=
  let encLen := (lenField 1 (encSessionMem G sess)).length
  segCloneEvents G sess.state ++ rustAllocEvents encLen 1 ++ dropClonedSessionEvents G sess.state

/-- `ConcatEnv` form of `0`-prev `Some` `SessionRecord::serialize` with exact `sc = 63` drop. -/
def SerializeSomeCancelEnv (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    List AllocEvent → Prop :=
  let encLen := (lenField 1 (encSessionMem G sess)).length
  ConcatEnv
    (ConcatEnv (SegCloneEnv G sess.state) (· = rustAllocEvents encLen 1))
    (· = dropClonedSessionEvents G sess.state)

/-- `SeqEnv ... FreeOnlyEvs` form of `0`-prev `Some` `SessionRecord::serialize`. -/
def SerializeSomeSeqFreeEnv (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    List AllocEvent → Prop :=
  let encLen := (lenField 1 (encSessionMem G sess)).length
  SeqEnv (SegCloneEnv G sess.state)
    (SeqEnv (· = rustAllocEvents encLen 1) FreeOnlyEvs)

def serializeSomeCum (G : SessionGhost) (sess : Session (List (BitVec 8))) : Nat :=
  let encLen := (lenField 1 (encSessionMem G sess)).length
  segCloneCum G sess.state + (2 * encLen + 9539)

def serializeSomePeak (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (sess : Session (List (BitVec 8))) : Nat :=
  let encLen := (lenField 1 (encSessionMem G sess)).length
  segCloneLarge M G sess.state + optLargeCost M encLen

def serializeSomeOutLarge (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (sess : Session (List (BitVec 8))) : Nat :=
  optLargeCost M (lenField 1 (encSessionMem G sess)).length

def serializeSomeMaxReq (G : SessionGhost) (sess : Session (List (BitVec 8))) : Nat :=
  max (segCloneMaxReq G sess.state) (lenField 1 (encSessionMem G sess)).length

/-- Exact-cancel `0`-prev `serialize` (`Some`): `Δlive = optLargeCost M encLen` (all `sc = 63`
clone buffers cancelled by `drop_glue`) and `Δpeak = segCloneLarge M G sess.state + optLargeCost M encLen`. -/
theorem PhaseCreditSpec.serializeSome_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    PhaseCreditSpec M (SerializeSomeCancelEnv G sess)
      (serializeSomeCum G sess)
      (serializeSomeOutLarge M G sess)
      (serializeSomePeak M G sess)
      (serializeSomeMaxReq G sess) := by
  let encLen := (lenField 1 (encSessionMem G sess)).length
  have hout := SessionCloneCredit.PhaseCreditSpec.rustAlloc_optLarge hM (req := encLen) (al := 1) (by decide)
  exact SessionCloneCredit.PhaseCreditSpec.segClone_body_drop_cancel hM G sess.state hout

theorem PhaseCreditSpec.serializeSome_exact {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    PhaseCreditSpec M (· = serializeSomeExactEvents G sess)
      (serializeSomeCum G sess)
      (serializeSomeOutLarge M G sess)
      (serializeSomePeak M G sess)
      (serializeSomeMaxReq G sess) := by
  refine (PhaseCreditSpec.serializeSome_cancel hM G sess).of_imp fun _ h => ?_
  subst h
  let encLen := (lenField 1 (encSessionMem G sess)).length
  exact ⟨segCloneEvents G sess.state ++ rustAllocEvents encLen 1,
    dropClonedSessionEvents G sess.state, rfl,
    ⟨segCloneEvents G sess.state, rustAllocEvents encLen 1, rfl, rfl, rfl⟩, rfl⟩

/-- `SeqEnv ... FreeOnlyEvs` variant of `0`-prev `serialize` (`Some`). -/
theorem PhaseCreditSpec.serializeSome_seqFree {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    PhaseCreditSpec M (SerializeSomeSeqFreeEnv G sess)
      (serializeSomeCum G sess)
      (serializeSomePeak M G sess)
      (serializeSomePeak M G sess)
      (serializeSomeMaxReq G sess) := by
  have hcl := SessionCloneCredit.PhaseCreditSpec.segClone hM G sess.state
  have hout := SessionCloneCredit.PhaseCreditSpec.rustAlloc_optLarge hM
    (req := (lenField 1 (encSessionMem G sess)).length) (al := 1) (by decide)
  have hfr := PhaseCreditSpec.freeOnly_of_hyps hM
  unfold SerializeSomeSeqFreeEnv serializeSomeCum serializeSomePeak serializeSomeMaxReq
  exact (hcl.seq (hout.seq hfr)).mono
    (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by omega)

/-- Full `0`-prev `RecordGhost` / `SessionRecord` exact-cancel envelope (`[]` when `none`). -/
def RecordSerializeCancelEnv (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    List AllocEvent → Prop :=
  match g.cur, r.currentSession with
  | some G, some sess => SerializeSomeCancelEnv G sess
  | _, _ => (· = [])

/-- Full `0`-prev `RecordGhost` / `SessionRecord` `SeqEnv ... FreeOnlyEvs` envelope (`[]` when `none`). -/
def RecordSerializeSeqFreeEnv (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    List AllocEvent → Prop :=
  match g.cur, r.currentSession with
  | some G, some sess => SerializeSomeSeqFreeEnv G sess
  | _, _ => (· = [])

def recordSerializeCum (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Nat :=
  match g.cur, r.currentSession with
  | some G, some sess => serializeSomeCum G sess
  | _, _ => 0

def recordSerializeOutLarge (M : AllocCostModel) [HasFineReallocCredit M]
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Nat :=
  match g.cur, r.currentSession with
  | some G, some sess => serializeSomeOutLarge M G sess
  | _, _ => 0

def recordSerializePeak (M : AllocCostModel) [HasFineReallocCredit M]
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Nat :=
  match g.cur, r.currentSession with
  | some G, some sess => serializeSomePeak M G sess
  | _, _ => 0

def recordSerializeMaxReq (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Nat :=
  match g.cur, r.currentSession with
  | some G, some sess => serializeSomeMaxReq G sess
  | _, _ => 0

theorem PhaseCreditSpec.recordSerialize_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    PhaseCreditSpec M (RecordSerializeCancelEnv g r)
      (recordSerializeCum g r)
      (recordSerializeOutLarge M g r)
      (recordSerializePeak M g r)
      (recordSerializeMaxReq g r) := by
  unfold RecordSerializeCancelEnv recordSerializeCum recordSerializeOutLarge
    recordSerializePeak recordSerializeMaxReq
  cases g.cur <;> cases r.currentSession
  · exact PhaseCreditSpec.nil M
  · exact PhaseCreditSpec.nil M
  · exact PhaseCreditSpec.nil M
  · rename_i G sess
    exact PhaseCreditSpec.serializeSome_cancel hM G sess

theorem PhaseCreditSpec.recordSerialize_seqFree {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    PhaseCreditSpec M (RecordSerializeSeqFreeEnv g r)
      (recordSerializeCum g r)
      (recordSerializePeak M g r)
      (recordSerializePeak M g r)
      (recordSerializeMaxReq g r) := by
  unfold RecordSerializeSeqFreeEnv recordSerializeCum recordSerializePeak recordSerializeMaxReq
  cases g.cur <;> cases r.currentSession
  · exact PhaseCreditSpec.nil M
  · exact PhaseCreditSpec.nil M
  · exact PhaseCreditSpec.nil M
  · rename_i G sess
    exact PhaseCreditSpec.serializeSome_seqFree hM G sess

/-! ## 4. `prev1` `SessionRecord::serialize` (`previous_sessions = [enc]`) -/

/-- Exact allocator event trace of `SessionRecord::serialize` on `prev1` in exact binary call order:
1. `SessionStructure::clone` (`segCloneEvents G sess.state`);
2. `<Vec<Vec<u8>> as Clone>::clone` on `[enc]` (`vecVecClone1Events enc`);
3. Output `Vec::with_capacity(totalLen)` (`rustAllocEvents totalLen 1`);
4. `drop_glue<SessionStructure>` (`dropClonedSessionEvents G sess.state`);
5. Epilogue deallocation of cloned `[enc]` (`dropVecVecClone1Events enc`). -/
def serializePrev1ExactEvents (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) : List AllocEvent :=
  let totalLen := (encodeRecordPrev1Mem G sess enc).length
  segCloneEvents G sess.state ++
    vecVecClone1Events enc ++
    rustAllocEvents totalLen 1 ++
    dropClonedSessionEvents G sess.state ++
    dropVecVecClone1Events enc

/-- `ConcatEnv` form of `prev1` `SessionRecord::serialize` with exact `sc = 63` drop cancellation. -/
def SerializePrev1CancelEnv (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) : List AllocEvent → Prop :=
  let totalLen := (encodeRecordPrev1Mem G sess enc).length
  ConcatEnv
    (ConcatEnv
      (ConcatEnv (SegCloneEnv G sess.state) (· = vecVecClone1Events enc))
      (· = rustAllocEvents totalLen 1))
    (ConcatEnv (· = dropClonedSessionEvents G sess.state) (· = dropVecVecClone1Events enc))

/-- `SeqEnv ... FreeOnlyEvs` form of `prev1` `SessionRecord::serialize`. -/
def SerializePrev1SeqFreeEnv (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) : List AllocEvent → Prop :=
  let totalLen := (encodeRecordPrev1Mem G sess enc).length
  SeqEnv (SegCloneEnv G sess.state)
    (SeqEnv (· = vecVecClone1Events enc)
      (SeqEnv (· = rustAllocEvents totalLen 1) FreeOnlyEvs))

def serializePrev1Cum (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) : Nat :=
  let totalLen := (encodeRecordPrev1Mem G sess enc).length
  segCloneCum G sess.state + vecVecClone1Cum enc + (2 * totalLen + 9539)

def serializePrev1OutLarge (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8)) : Nat :=
  optLargeCost M (encodeRecordPrev1Mem G sess enc).length

def serializePrev1Peak (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8)) : Nat :=
  segCloneLarge M G sess.state + vecVecClone1Large M enc +
    optLargeCost M (encodeRecordPrev1Mem G sess enc).length

def serializePrev1MaxReq (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) : Nat :=
  max (max (segCloneMaxReq G sess.state) (vecVecClone1MaxReq enc))
    (encodeRecordPrev1Mem G sess enc).length

/-- Exact-cancel `prev1` `serialize`: both temporary clones (`SessionStructure` and `Vec<Vec<u8>>`
`[enc]`) cancel in binary epilogue drop order, leaving `Δlive = optLargeCost M totalLen`. -/
theorem PhaseCreditSpec.serializePrev1_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) :
    PhaseCreditSpec M (SerializePrev1CancelEnv G sess enc)
      (serializePrev1Cum G sess enc)
      (serializePrev1OutLarge M G sess enc)
      (serializePrev1Peak M G sess enc)
      (serializePrev1MaxReq G sess enc) := by
  have hcl := SessionCloneCredit.PhaseCreditSpec.segClone hM G sess.state
  have hvv := PhaseCreditSpec.vecVecClone1 hM enc
  have hout := SessionCloneCredit.PhaseCreditSpec.rustAlloc_optLarge hM
    (req := (encodeRecordPrev1Mem G sess enc).length) (al := 1) (by decide)
  have h123 : PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (SegCloneEnv G sess.state) (· = vecVecClone1Events enc))
        (· = rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1))
      (serializePrev1Cum G sess enc)
      (serializePrev1OutLarge M G sess enc +
        (segCloneLarge M G sess.state + vecVecClone1Large M enc))
      (serializePrev1Peak M G sess enc)
      (serializePrev1MaxReq G sess enc) := by
    unfold serializePrev1Cum serializePrev1OutLarge serializePrev1Peak serializePrev1MaxReq
    exact ((hcl.concat hvv).concat hout).mono
      (by dsimp only; omega) (by omega) (by omega) (by omega)
  have hd_sess := SessionCloneCredit.DeallocCreditSpec.dropClonedSession M G sess.state
  have hd_vv := DeallocCreditSpec.dropVecVecClone1 M enc
  exact h123.concat_dealloc_cancel (hd_sess.concat hd_vv)

theorem PhaseCreditSpec.serializePrev1_exact {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) :
    PhaseCreditSpec M (· = serializePrev1ExactEvents G sess enc)
      (serializePrev1Cum G sess enc)
      (serializePrev1OutLarge M G sess enc)
      (serializePrev1Peak M G sess enc)
      (serializePrev1MaxReq G sess enc) := by
  refine (PhaseCreditSpec.serializePrev1_cancel hM G sess enc).of_imp fun _ h => ?_
  subst h
  let totalLen := (encodeRecordPrev1Mem G sess enc).length
  refine ⟨segCloneEvents G sess.state ++ vecVecClone1Events enc ++ rustAllocEvents totalLen 1,
    dropClonedSessionEvents G sess.state ++ dropVecVecClone1Events enc, ?_, ?_, ?_⟩
  · simp [serializePrev1ExactEvents, List.append_assoc]; rfl
  · exact ⟨segCloneEvents G sess.state ++ vecVecClone1Events enc,
      rustAllocEvents totalLen 1, rfl,
      ⟨segCloneEvents G sess.state, vecVecClone1Events enc, rfl, rfl, rfl⟩, rfl⟩
  · exact ⟨dropClonedSessionEvents G sess.state, dropVecVecClone1Events enc, rfl, rfl, rfl⟩

/-- `SeqEnv ... FreeOnlyEvs` variant of `prev1` `serialize`. -/
theorem PhaseCreditSpec.serializePrev1_seqFree {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) :
    PhaseCreditSpec M (SerializePrev1SeqFreeEnv G sess enc)
      (serializePrev1Cum G sess enc)
      (serializePrev1Peak M G sess enc)
      (serializePrev1Peak M G sess enc)
      (serializePrev1MaxReq G sess enc) := by
  have hcl := SessionCloneCredit.PhaseCreditSpec.segClone hM G sess.state
  have hvv := PhaseCreditSpec.vecVecClone1 hM enc
  have hout := SessionCloneCredit.PhaseCreditSpec.rustAlloc_optLarge hM
    (req := (encodeRecordPrev1Mem G sess enc).length) (al := 1) (by decide)
  have hfr := PhaseCreditSpec.freeOnly_of_hyps hM
  unfold SerializePrev1SeqFreeEnv serializePrev1Cum serializePrev1Peak serializePrev1MaxReq
  exact (hcl.seq (hvv.seq (hout.seq hfr))).mono
    (by dsimp only; omega) (by omega) (by omega) (by omega)

/-! ## 5. Tight Per-Size-Class `SessionRecord::serialize` Credit -/

section TightSerializeCredit

open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (
  rustAllocTightCum rustAllocTightCum_fine_24 rustAllocTightCum_fine_le_143484
  segCloneTightCum tryCloneSmallDelta tryCloneSmallDelta_fine_le_143484
)

/-- Tight cumulative small/metadata bound for `vecVecClone1Events enc` (`488 + tryCloneSmallDelta`
on `fineCostModel`, `≤ 143,972` B). -/
def vecVecClone1TightCum (M : AllocCostModel) [HasFineReallocCredit M]
    (enc : List (BitVec 8)) : Nat :=
  rustAllocTightCum M 24 + tryCloneSmallDelta M enc.length

/-- Tight cumulative small/metadata bound for `0`-prev `Some` `SessionRecord::serialize`. -/
def serializeSomeTightCum (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (sess : Session (List (BitVec 8))) : Nat :=
  segCloneTightCum M G sess.state +
    rustAllocTightCum M (lenField 1 (encSessionMem G sess)).length

/-- Tight cumulative small/metadata bound for `0`-prev `RecordGhost` / `SessionRecord` `serialize`. -/
def recordSerializeTightCum (M : AllocCostModel) [HasFineReallocCredit M]
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Nat :=
  match g.cur, r.currentSession with
  | some G, some sess => serializeSomeTightCum M G sess
  | _, _ => 0

/-- Tight cumulative small/metadata bound for `prev1` `SessionRecord::serialize`. -/
def serializePrev1TightCum (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) : Nat :=
  segCloneTightCum M G sess.state + vecVecClone1TightCum M enc +
    rustAllocTightCum M (encodeRecordPrev1Mem G sess enc).length

theorem PhaseCreditSpec.vecVecClone1_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (enc : List (BitVec 8)) :
    PhaseCreditSpec M (· = vecVecClone1Events enc)
      (vecVecClone1TightCum M enc)
      (vecVecClone1Large M enc)
      (vecVecClone1Large M enc)
      (vecVecClone1MaxReq enc) := by
  have h24 := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight hM (req := 24) (al := 8) (by decide)
  have henc : PhaseCreditSpec M
      (· = if enc.length = 0 then [] else rustAllocEvents enc.length 1)
      (tryCloneSmallDelta M enc.length)
      (vecCloneLarge M enc.length)
      (vecCloneLarge M enc.length)
      enc.length := by
    unfold tryCloneSmallDelta vecCloneLarge
    exact (SessionCloneCredit.PhaseCreditSpec.condRustAlloc_tight hM
      (p := enc.length = 0) (req := enc.length) (al := 1) (by decide)).mono
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by split <;> omega)
  exact SessionCloneCredit.PhaseCreditSpec.append_eq_self h24 henc

/-- Tight `0`-prev `serialize` (`Some`) with `sc = 63` cancellation, charging
`segCloneTightCum M G sess.state + rustAllocTightCum M encLen` to `cumSmall`. -/
theorem PhaseCreditSpec.serializeSome_cancel_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    PhaseCreditSpec M (SerializeSomeCancelEnv G sess)
      (serializeSomeTightCum M G sess)
      (serializeSomeOutLarge M G sess)
      (serializeSomePeak M G sess)
      (serializeSomeMaxReq G sess) := by
  have hout := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight hM
    (req := (lenField 1 (encSessionMem G sess)).length) (al := 1) (by decide)
  exact SessionCloneCredit.PhaseCreditSpec.segClone_body_drop_cancel_tight hM G sess.state hout

theorem PhaseCreditSpec.serializeSome_exact_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    PhaseCreditSpec M (· = serializeSomeExactEvents G sess)
      (serializeSomeTightCum M G sess)
      (serializeSomeOutLarge M G sess)
      (serializeSomePeak M G sess)
      (serializeSomeMaxReq G sess) := by
  refine (PhaseCreditSpec.serializeSome_cancel_tight hM G sess).of_imp fun _ h => ?_
  subst h
  let encLen := (lenField 1 (encSessionMem G sess)).length
  exact ⟨segCloneEvents G sess.state ++ rustAllocEvents encLen 1,
    dropClonedSessionEvents G sess.state, rfl,
    ⟨segCloneEvents G sess.state, rustAllocEvents encLen 1, rfl, rfl, rfl⟩, rfl⟩

theorem PhaseCreditSpec.serializeSome_seqFree_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    PhaseCreditSpec M (SerializeSomeSeqFreeEnv G sess)
      (serializeSomeTightCum M G sess)
      (serializeSomePeak M G sess)
      (serializeSomePeak M G sess)
      (serializeSomeMaxReq G sess) := by
  have hcl := SessionCloneCredit.PhaseCreditSpec.segClone_tight hM G sess.state
  have hout := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight hM
    (req := (lenField 1 (encSessionMem G sess)).length) (al := 1) (by decide)
  have hfr := PhaseCreditSpec.freeOnly_of_hyps hM
  unfold SerializeSomeSeqFreeEnv serializeSomeTightCum serializeSomePeak serializeSomeMaxReq
  exact (hcl.seq (hout.seq hfr)).mono
    (by omega) (by dsimp only; omega) (by dsimp only; omega) (by omega)

theorem PhaseCreditSpec.recordSerialize_cancel_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    PhaseCreditSpec M (RecordSerializeCancelEnv g r)
      (recordSerializeTightCum M g r)
      (recordSerializeOutLarge M g r)
      (recordSerializePeak M g r)
      (recordSerializeMaxReq g r) := by
  unfold RecordSerializeCancelEnv recordSerializeTightCum recordSerializeOutLarge
    recordSerializePeak recordSerializeMaxReq
  cases g.cur <;> cases r.currentSession
  · exact PhaseCreditSpec.nil M
  · exact PhaseCreditSpec.nil M
  · exact PhaseCreditSpec.nil M
  · rename_i G sess
    exact PhaseCreditSpec.serializeSome_cancel_tight hM G sess

theorem PhaseCreditSpec.recordSerialize_seqFree_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    PhaseCreditSpec M (RecordSerializeSeqFreeEnv g r)
      (recordSerializeTightCum M g r)
      (recordSerializePeak M g r)
      (recordSerializePeak M g r)
      (recordSerializeMaxReq g r) := by
  unfold RecordSerializeSeqFreeEnv recordSerializeTightCum recordSerializePeak recordSerializeMaxReq
  cases g.cur <;> cases r.currentSession
  · exact PhaseCreditSpec.nil M
  · exact PhaseCreditSpec.nil M
  · exact PhaseCreditSpec.nil M
  · rename_i G sess
    exact PhaseCreditSpec.serializeSome_seqFree_tight hM G sess

/-- Tight `prev1` `serialize` with `sc = 63` cancellation, charging
`serializePrev1TightCum M G sess enc` to `cumSmall` while cancelling both temporary clones. -/
theorem PhaseCreditSpec.serializePrev1_cancel_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) :
    PhaseCreditSpec M (SerializePrev1CancelEnv G sess enc)
      (serializePrev1TightCum M G sess enc)
      (serializePrev1OutLarge M G sess enc)
      (serializePrev1Peak M G sess enc)
      (serializePrev1MaxReq G sess enc) := by
  have hcl := SessionCloneCredit.PhaseCreditSpec.segClone_tight hM G sess.state
  have hvv := PhaseCreditSpec.vecVecClone1_tight hM enc
  have hout := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight hM
    (req := (encodeRecordPrev1Mem G sess enc).length) (al := 1) (by decide)
  have h123 : PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (SegCloneEnv G sess.state) (· = vecVecClone1Events enc))
        (· = rustAllocEvents (encodeRecordPrev1Mem G sess enc).length 1))
      (serializePrev1TightCum M G sess enc)
      (serializePrev1OutLarge M G sess enc +
        (segCloneLarge M G sess.state + vecVecClone1Large M enc))
      (serializePrev1Peak M G sess enc)
      (serializePrev1MaxReq G sess enc) := by
    unfold serializePrev1TightCum serializePrev1OutLarge serializePrev1Peak serializePrev1MaxReq
    exact ((hcl.concat hvv).concat hout).mono
      (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)
  have hd_sess := SessionCloneCredit.DeallocCreditSpec.dropClonedSession M G sess.state
  have hd_vv := DeallocCreditSpec.dropVecVecClone1 M enc
  exact h123.concat_dealloc_cancel (hd_sess.concat hd_vv)

theorem PhaseCreditSpec.serializePrev1_exact_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) :
    PhaseCreditSpec M (· = serializePrev1ExactEvents G sess enc)
      (serializePrev1TightCum M G sess enc)
      (serializePrev1OutLarge M G sess enc)
      (serializePrev1Peak M G sess enc)
      (serializePrev1MaxReq G sess enc) := by
  refine (PhaseCreditSpec.serializePrev1_cancel_tight hM G sess enc).of_imp fun _ h => ?_
  subst h
  let totalLen := (encodeRecordPrev1Mem G sess enc).length
  refine ⟨segCloneEvents G sess.state ++ vecVecClone1Events enc ++ rustAllocEvents totalLen 1,
    dropClonedSessionEvents G sess.state ++ dropVecVecClone1Events enc, ?_, ?_, ?_⟩
  · simp [serializePrev1ExactEvents, List.append_assoc]; rfl
  · exact ⟨segCloneEvents G sess.state ++ vecVecClone1Events enc,
      rustAllocEvents totalLen 1, rfl,
      ⟨segCloneEvents G sess.state, vecVecClone1Events enc, rfl, rfl, rfl⟩, rfl⟩
  · exact ⟨dropClonedSessionEvents G sess.state, dropVecVecClone1Events enc, rfl, rfl, rfl⟩

theorem PhaseCreditSpec.serializePrev1_seqFree_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (enc : List (BitVec 8)) :
    PhaseCreditSpec M (SerializePrev1SeqFreeEnv G sess enc)
      (serializePrev1TightCum M G sess enc)
      (serializePrev1Peak M G sess enc)
      (serializePrev1Peak M G sess enc)
      (serializePrev1MaxReq G sess enc) := by
  have hcl := SessionCloneCredit.PhaseCreditSpec.segClone_tight hM G sess.state
  have hvv := PhaseCreditSpec.vecVecClone1_tight hM enc
  have hout := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight hM
    (req := (encodeRecordPrev1Mem G sess enc).length) (al := 1) (by decide)
  have hfr := PhaseCreditSpec.freeOnly_of_hyps hM
  unfold SerializePrev1SeqFreeEnv serializePrev1TightCum serializePrev1Peak serializePrev1MaxReq
  exact (hcl.seq (hvv.seq (hout.seq hfr))).mono
    (by omega) (by omega) (by omega) (by omega)

/-! ### Concrete `fineCostModel` Cap Theorems -/

theorem vecVecClone1TightCum_fine_le (enc : List (BitVec 8)) :
    vecVecClone1TightCum fineCostModel enc ≤ 143972 := by
  unfold vecVecClone1TightCum
  have h24 : rustAllocTightCum fineCostModel 24 ≤ 488 := by
    rw [rustAllocTightCum_fine_24]
  exact Nat.le_trans (Nat.add_le_add h24 (tryCloneSmallDelta_fine_le_143484 enc.length)) (by decide)

theorem serializeSomeTightCum_fine_le_of_clone
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {c : Nat}
    (hcl : segCloneTightCum fineCostModel G sess.state ≤ c) :
    serializeSomeTightCum fineCostModel G sess ≤ c + 143484 := by
  unfold serializeSomeTightCum
  exact Nat.add_le_add hcl (rustAllocTightCum_fine_le_143484 _)

/-- When `segCloneTightCum fineCostModel G sess.state ≤ 1,500,446`,
`serializeSomeTightCum fineCostModel G sess ≤ 1,643,930`. -/
theorem serializeSomeTightCum_fine_benchmark_le
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hcl : segCloneTightCum fineCostModel G sess.state ≤ 1500446) :
    serializeSomeTightCum fineCostModel G sess ≤ 1643930 :=
  Nat.le_trans (serializeSomeTightCum_fine_le_of_clone hcl) (by decide)

theorem recordSerializeTightCum_fine_le_of_clone
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))} {c : Nat}
    (hcl : ∀ G sess, g.cur = some G → r.currentSession = some sess →
      segCloneTightCum fineCostModel G sess.state ≤ c) :
    recordSerializeTightCum fineCostModel g r ≤ c + 143484 := by
  unfold recordSerializeTightCum
  cases hg : g.cur <;> cases hr : r.currentSession
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · rename_i G sess
    exact serializeSomeTightCum_fine_le_of_clone (hcl G sess hg hr)

theorem recordSerializeTightCum_fine_benchmark_le
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hcl : ∀ G sess, g.cur = some G → r.currentSession = some sess →
      segCloneTightCum fineCostModel G sess.state ≤ 1500446) :
    recordSerializeTightCum fineCostModel g r ≤ 1643930 :=
  Nat.le_trans (recordSerializeTightCum_fine_le_of_clone hcl) (by decide)

theorem serializePrev1TightCum_fine_le_of_clone
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)} {c : Nat}
    (hcl : segCloneTightCum fineCostModel G sess.state ≤ c) :
    serializePrev1TightCum fineCostModel G sess enc ≤ c + 287456 := by
  unfold serializePrev1TightCum
  have h12 := Nat.add_le_add hcl (vecVecClone1TightCum_fine_le enc)
  have h123 := Nat.add_le_add h12
    (rustAllocTightCum_fine_le_143484 (encodeRecordPrev1Mem G sess enc).length)
  rw [Nat.add_assoc c 143972 143484, show 143972 + 143484 = 287456 by decide] at h123
  exact h123

/-- When `segCloneTightCum fineCostModel G sess.state ≤ 1,500,446`,
`serializePrev1TightCum fineCostModel G sess enc ≤ 1,787,902`. -/
theorem serializePrev1TightCum_fine_benchmark_le
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hcl : segCloneTightCum fineCostModel G sess.state ≤ 1500446) :
    serializePrev1TightCum fineCostModel G sess enc ≤ 1787902 :=
  Nat.le_trans (serializePrev1TightCum_fine_le_of_clone hcl) (by decide)

end TightSerializeCredit

end LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
