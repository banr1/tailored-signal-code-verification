/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Fields
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Composition of Inlined `SessionStructure::decode` Loop

Composes the per-step contracts of `PrevDec/LoopDefs.lean` (entry, loop head, key dispatch, four
field-arm groups, and exit entailment) into `OverPrevDecodeStmt` (`+0x1ee8 → +0x2620`) for
`message_decrypt_prekey::<Coins>::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Std Arm64 ProofLib ProofLib.ObjectLoad SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ssgqOf genFieldsQ)

/-! ## Generic `SepWPp` Sequencing and Consequence -/

/-- Sequence two `SepWPp` blocks through the intermediate pc `mid`, sharing the panic post. -/
theorem overDec_sepWPp_seq {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {Qm Q Qp : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Qm Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm →
      SepWPp prog target sm Pm Q Qp) :
    SepWPp prog target s P Q Qp := by
  intro R hm hL
  rcases h1 R hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hQ⟩ | hpan⟩
  · rcases h2 sm Pm hpcm hrunm hQ R hmm (hsteps.codeLoaded hL) with ⟨sf, hsteps', hout⟩
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan⟩

theorem overDec_sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  exact h R (Arm64.Satisfies.mono (sepConj_mono_left hent) hm) hL

theorem overDec_sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q' Qp : State → SepProp → Prop}
    (hQ : ∀ sf P_f, sf.pc = ret → sf.status = .Running → Q sf P_f → Q' sf P_f)
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQf⟩ | hpan⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hQ sf P_f hpc hrun hQf⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-! ## Key and Arm Composition -/

/-- Compose `OverDecKeyStmtExt A` and `OverDecArmStmtTRExt A P` into `OverDecFieldStmtExt A P`. -/
theorem overDecField_of_key_arm_ext {A : RustAlloc} {P : GenFieldQ → Prop}
    (hK : OverDecKeyStmtExt A) (hA : OverDecArmStmtTRExt A P) (hPA : ∀ fl, P fl → OverDecAnyField fl) :
    OverDecFieldStmtExt A P := by
  intro img ext hL hAC s0 s g v fl rest hP hok hfr hsuf hlen hregs
  refine overDec_sepWPp_seq (hK img ext hL
    (stage1XAllocContractsX_of_trAllocContractsX hAC) s0 s g v fl
    rest (hPA fl hP) hok hsuf hlen hregs) ?_
  rintro sm Pm - - ⟨hregs', hx0, hx22, hent⟩
  exact overDec_sepWPp_weaken_pre hent
    (hA img ext hL hAC s0 sm g v fl rest hP hok hfr hsuf hlen hregs' hx0 hx22)

theorem overDecField_of_key_arm {P : GenFieldQ → Prop}
    (hK : OverDecKeyStmt) (hA : OverDecArmStmtTR P) (hPA : ∀ fl, P fl → OverDecAnyField fl) :
    OverDecFieldStmt P :=
  overDecField_of_key_arm_ext hK hA hPA

/-- Combine the four field-arm groups into `OverDecArmStmtTRExt A OverDecAnyField`. -/
theorem overDecArm_any_ext {A : RustAlloc}
    (hV : OverDecArmStmtTRExt A OverDecVarintField) (hB : OverDecArmStmtTRExt A OverDecBytesField)
    (hS : OverDecArmStmtTRExt A OverDecSenderField) (hR : OverDecArmStmtTRExt A OverDecRecvField) :
    OverDecArmStmtTRExt A OverDecAnyField := by
  intro img ext hL hAC s0 s g v fl rest hP
  rcases hP with h | h | h | h
  · exact hV img ext hL hAC s0 s g v fl rest h
  · exact hB img ext hL hAC s0 s g v fl rest h
  · exact hS img ext hL hAC s0 s g v fl rest h
  · exact hR img ext hL hAC s0 s g v fl rest h

theorem overDecArm_any
    (hV : OverDecArmStmtTR OverDecVarintField) (hB : OverDecArmStmtTR OverDecBytesField)
    (hS : OverDecArmStmtTR OverDecSenderField) (hR : OverDecArmStmtTR OverDecRecvField) :
    OverDecArmStmtTR OverDecAnyField :=
  overDecArm_any_ext hV hB hS hR

/-! ## Pure Facts on Fields of `encSession sess` -/

/-- Every field's encoding is non-empty (it starts with the key varint). -/
theorem overDec_enc_ne_nil (fl : GenFieldQ) : fl.enc ≠ [] := by
  unfold GenFieldQ.enc CryptoVerification.LibsignalProtoCodec.encodeKey
  intro h
  exact CryptoVerification.LibsignalProtoCodec.encodeVarint_ne_nil _ (List.append_eq_nil_iff.mp h).1

/-- A field list's encodings: the suffix after dropping the head is a suffix of the whole. -/
theorem overDec_flatMap_cons (fl : GenFieldQ) (fs : List GenFieldQ) :
    (fl :: fs).flatMap GenFieldQ.enc = fl.enc ++ fs.flatMap GenFieldQ.enc := by
  rw [List.flatMap_cons]

/-- With no pending pre-key, no field of `genFields` is `pending`. -/
theorem overDec_genFields_noPending (s : Session (List (BitVec 8)))
    (hp : s.pendingPreKey = none) (f : GenField)
    (hf : f ∈ CryptoVerification.E2E.Record.DeserializeGeneral.genFields s) :
    ∀ k, f ≠ .pending k := by
  intro k hk
  subst hk
  unfold CryptoVerification.E2E.Record.DeserializeGeneral.genFields at hf
  rw [hp] at hf
  simp only [List.mem_append, List.mem_map] at hf
  rcases hf with ((((((h | h) | h) | h) | h) | h) | ⟨c, _, hc⟩) | h
  all_goals first
    | (split at h <;> simp at h)
    | (cases hc)
    | (simp at h)

/-- Every field of a session without pending pre-keys belongs to one of the four arm groups. -/
theorem overDec_anyField_of_mem (s : Session (List (BitVec 8)))
    (hp : s.pendingPreKey = none) (hk : s.pendingKyberPreKey = none)
    (fl : GenFieldQ) (hfl : fl ∈ genFieldsQ s) : OverDecAnyField fl := by
  unfold genFieldsQ at hfl
  simp only [List.mem_append, List.mem_map] at hfl
  rcases hfl with ⟨fx, hfx, rfl⟩ | h15
  · unfold CryptoVerification.E2E.Record.L1GX.genFieldsX at hfx
    simp only [hp, hk, List.mem_append, List.mem_map,
      CryptoVerification.E2E.Record.L1GX.pendingFieldX, List.not_mem_nil, or_false] at hfx
    rcases hfx with ((((⟨f, hf, rfl⟩ | h10) | h11) | h13) | h15)
    · have hnp := overDec_genFields_noPending _ rfl f hf
      cases f with
      | pending k => exact absurd rfl (hnp k)
      | version _ => exact Or.inl trivial
      | prevCounter _ => exact Or.inl trivial
      | lik _ => exact Or.inr (Or.inl trivial)
      | rik _ => exact Or.inr (Or.inl trivial)
      | root _ => exact Or.inr (Or.inl trivial)
      | sender _ => exact Or.inr (Or.inr (Or.inl trivial))
      | recv _ => exact Or.inr (Or.inr (Or.inr trivial))
    · split at h10 <;> simp only [List.mem_singleton, List.not_mem_nil] at h10
      subst h10; exact Or.inl trivial
    · split at h11 <;> simp only [List.mem_singleton, List.not_mem_nil] at h11
      subst h11; exact Or.inl trivial
    · split at h13 <;> simp only [List.mem_singleton, List.not_mem_nil] at h13
      subst h13; exact Or.inr (Or.inl trivial)
    · simp at h15
  · split at h15 <;> simp only [List.mem_singleton, List.not_mem_nil] at h15
    subst h15; exact Or.inr (Or.inl trivial)

/-- A version-4 session has a non-empty field list (tag 1 first). -/
theorem overDec_genFieldsQ_ne_nil (s : Session (List (BitVec 8)))
    (hv : s.state.sessionVersion = 4#32) : genFieldsQ s ≠ [] := by
  unfold genFieldsQ CryptoVerification.E2E.Record.L1GX.genFieldsX
    CryptoVerification.E2E.Record.DeserializeGeneral.genFields
  simp [hv]

/-- Inductive freshness chain for a field list starting from decoded value `v`: each field is fresh against the accumulator after prior fields. -/
inductive OverDecFreshChain : List GenFieldQ → SSGQ → Prop
  | nil (v : SSGQ) : OverDecFreshChain [] v
  | cons (fl : GenFieldQ) (fs : List GenFieldQ) (v : SSGQ) :
      fl.Fresh v → OverDecFreshChain fs (v.apply fl) → OverDecFreshChain (fl :: fs) v

theorem overDecFreshChain_cons_inv {fl : GenFieldQ} {fs : List GenFieldQ} {v : SSGQ}
    (h : OverDecFreshChain (fl :: fs) v) : fl.Fresh v ∧ OverDecFreshChain fs (v.apply fl) := by
  cases h with
  | cons _ _ _ h1 h2 => exact ⟨h1, h2⟩

/-- The indexed freshness of `ssgqAfter`-style folds gives the fresh chain. -/
theorem overDecFreshChain_of_getElem (fs : List GenFieldQ) (v : SSGQ)
    (h : ∀ k (hk : k < fs.length), (fs[k]'hk).Fresh ((fs.take k).foldl SSGQ.apply v)) :
    OverDecFreshChain fs v := by
  induction fs generalizing v with
  | nil => exact .nil v
  | cons fl fs ih =>
    refine .cons fl fs v (h 0 (Nat.zero_lt_succ _)) (ih (v.apply fl) ?_)
    intro k hk
    exact h (k + 1) (Nat.succ_lt_succ hk)

/-! ## Loop Exit Entailment -/

/-- The cursor and slice cells at the exit collapse to the scratch regions: the cursor word
`q + 0xbe8` and the cursor run `q + 0xbf0` to `memRegion (q + 0xbe8) 136`, the slice header
`{ptr, len}` at `q + 0x920` to `memRegion (q + 0x920) 16`. -/
theorem overDec_exit_cells (q c p l : BitVec 64) :
    ((q + 0xbe8#64) ↦₆₄ c) ∗ ((q + 0x920#64) ↦₆₄ p) ∗ ((q + 0x920#64 + 8#64) ↦₆₄ l) ∗
        memRegion (q + 0xbf0#64) 128 ⊢
      memRegion (q + 0xbe8#64) 136 ∗ memRegion (q + 0x920#64) 16 := by
  have h136 : memRegion (q + 0xbe8#64) 136 =
      memRegion (q + 0xbe8#64) 8 ∗ memRegion (q + 0xbf0#64) 128 :=
    memRegion_split' (n := 8) (k := 128) (by decide) (by bv_omega) (by decide)
  have h16 : memRegion (q + 0x920#64) 16 =
      memRegion (q + 0x920#64) 8 ∗ memRegion (q + 0x920#64 + 8#64) 8 :=
    memRegion_split' (n := 8) (k := 8) (by decide) rfl (by decide)
  rw [h136, h16]
  refine Entails.trans ?_ (Entails.of_eq (P := (memRegion (q + 0xbe8#64) 8 ∗
      memRegion (q + 0x920#64) 8 ∗ memRegion (q + 0x920#64 + 8#64) 8 ∗
      memRegion (q + 0xbf0#64) 128)) (by ac_rfl))
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))

theorem overDec_entails_anyHeap_right {P T : SepProp} (h : P ⊢ T) : P ⊢ T ∗ anyHeap := by
  refine Entails.trans h ?_
  refine Entails.trans (Entails.of_eq (sepConj_emp T).symm) ?_
  exact sepConj_mono_right (entails_anyHeap _)

theorem overDec_assoc_anyHeap (A B C D : SepProp) :
    (A ∗ B ∗ C ∗ D) ∗ anyHeap ⊢ A ∗ B ∗ C ∗ D ∗ anyHeap :=
  Entails.of_eq (by simp only [sepConj_assoc])

/-- At loop exit (`rest = []`), `overDecHeapExt` entails `overPrevElemAtExt A`, `overDecScratchPostExt A`, stack, and `A.pool` (using `g.enc ≠ []` to rule out `encCap = 0`). -/
theorem overDec_exit_ext {A : RustAlloc} (g : OverDecG) (v : SSGQ) (hne : g.enc ≠ []) :
    overDecHeapExt A g [] v ⊢
      overPrevElemAtExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗ overDecScratchPostExt A g.q v ∗
        stackAt g.q overDecStackX ∗ A.pool ∗ anyHeap := by
  refine Entails.trans ?_ (overDec_assoc_anyHeap _ _ _ _)
  refine overDec_entails_anyHeap_right ?_
  unfold overDecHeapExt CryptoVerification.LibsignalTripleRatchet.Prost.sliceCursorAfter
  have hcells := overDec_exit_cells g.q (g.q + 0x920#64)
    (g.encPtr + BitVec.ofNat 64 (g.enc.length - ([] : List (BitVec 8)).length))
    (BitVec.ofNat 64 ([] : List (BitVec 8)).length)
  refine Entails.trans (Entails.of_eq (Q :=
    (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗ ((g.q + 0x920#64) ↦₆₄
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - ([] : List (BitVec 8)).length))) ∗
      ((g.q + 0x920#64 + 8#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length) ∗
      memRegion (g.q + 0xbf0#64) 128) ∗
    (overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗ (g.encPtr ↦ₛ g.enc) ∗
      prostSSGQAt A (g.q + 0x930#64) v ∗
      memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
      stackAt g.q overDecStackX ∗ A.pool)) (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hcells) ?_
  unfold overPrevElemAtExt overDecScratchPostExt overPrevElemRestExt vecU8At
  split_ifs with hcap
  · refine Entails.trans (Entails.of_eq (Q := ⌜g.enc.length ≤ g.encCap.toNat ∧
        g.encCap.toNat < 2 ^ 63 ∧ g.encPtr ≠ 0⌝ ∗ _) (by sep_focus)) ?_
    refine Entails.pure_left ?_
    rintro ⟨hl, -, -⟩
    exfalso
    apply hne
    rw [hcap] at hl
    simpa using hl
  · sep_entail

theorem overDec_exit (g : OverDecG) (v : SSGQ) (hne : g.enc ≠ []) :
    overDecHeap g [] v ⊢
      overPrevElemAt g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗ overDecScratchPost g.q v ∗
        stackAt g.q overDecStackX ∗ CryptoVerification.E2E.Record.A0.pool ∗ anyHeap :=
  overDec_exit_ext g v hne

/-! ## Field Loop Induction -/

/-- Field-loop induction (`+0x216c → +0x2620`) over a non-empty suffix `fs` of fields, folding `SSGQ.apply` from `v`. -/
theorem overDec_loop_ext {A : RustAlloc} (hField : OverDecFieldStmtExt A OverDecAnyField)
    (hCons : OverDecHeadConsStmtExt A) (hNil : OverDecHeadNilStmtExt A)
    (img : Obj.Image) (ext : String → Option (State → State))
    (hL : Obj.Loads libsignalSessionImage img)
    (hAC : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext)
    (s0 : State) (g : OverDecG) (hlen : g.enc.length < 2 ^ 62) :
    ∀ (fs : List GenFieldQ) (v : SSGQ) (s : State), fs ≠ [] →
      (∀ fl ∈ fs, OverDecAnyField fl ∧ fl.Ok) → OverDecFreshChain fs v →
      fs.flatMap GenFieldQ.enc <:+ g.enc →
      OverDecRegs img ext s0 g 0x216c#64 s →
      SepWPp (contractProg img.base ext)
          ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2620#64) s
        (overDecHeapExt A g (fs.flatMap GenFieldQ.enc) v)
        (fun sf P_f => OverDecRegs img ext s0 g 0x2620#64 sf ∧
          (P_f ⊢ overDecHeapExt A g [] (fs.foldl SSGQ.apply v)))
        (PanicOomProp s0) := by
  intro fs
  induction fs with
  | nil => intro v s hne; exact absurd rfl hne
  | cons fl fs ih =>
    intro v s _ hmem hfr hsuf hregs
    have hfl := hmem fl (List.mem_cons_self ..)
    obtain ⟨hfr1, hfr2⟩ := overDecFreshChain_cons_inv hfr
    rw [overDec_flatMap_cons] at hsuf ⊢
    refine overDec_sepWPp_seq
      (hField img ext hL hAC s0 s g v fl _ hfl.1 hfl.2 hfr1 hsuf hlen hregs) ?_
    rintro sm Pm - - ⟨hregsm, hentm⟩
    refine overDec_sepWPp_weaken_pre hentm ?_
    have hsuf' : fs.flatMap GenFieldQ.enc <:+ g.enc :=
      List.IsSuffix.trans (List.suffix_append _ _) hsuf
    rcases fs with _ | ⟨fl', fs'⟩
    · exact hNil img ext hL s0 sm g (v.apply fl) hlen hregsm
    · have hne : (fl' :: fs').flatMap GenFieldQ.enc ≠ [] := by
        rw [overDec_flatMap_cons]
        intro h
        exact overDec_enc_ne_nil fl' (List.append_eq_nil_iff.mp h).1
      refine overDec_sepWPp_seq (hCons img ext hL s0 sm g (v.apply fl) _ hne hsuf' hlen hregsm) ?_
      rintro sn Pn - - ⟨hregsn, hentn⟩
      exact overDec_sepWPp_weaken_pre hentn
        (ih (v.apply fl) sn (List.cons_ne_nil _ _)
          (fun f hf => hmem f (List.mem_cons_of_mem _ hf)) hfr2 hsuf' hregsn)

theorem overDec_loop (hField : OverDecFieldStmt OverDecAnyField)
    (hCons : OverDecHeadConsStmt) (hNil : OverDecHeadNilStmt)
    (img : Obj.Image) (ext : String → Option (State → State))
    (hL : Obj.Loads libsignalSessionImage img)
    (hAC : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img
      CryptoVerification.E2E.Record.A0 ext)
    (s0 : State) (g : OverDecG) (hlen : g.enc.length < 2 ^ 62) :
    ∀ (fs : List GenFieldQ) (v : SSGQ) (s : State), fs ≠ [] →
      (∀ fl ∈ fs, OverDecAnyField fl ∧ fl.Ok) → OverDecFreshChain fs v →
      fs.flatMap GenFieldQ.enc <:+ g.enc →
      OverDecRegs img ext s0 g 0x216c#64 s →
      SepWPp (contractProg img.base ext)
          ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2620#64) s
        (overDecHeap g (fs.flatMap GenFieldQ.enc) v)
        (fun sf P_f => OverDecRegs img ext s0 g 0x2620#64 sf ∧
          (P_f ⊢ overDecHeap g [] (fs.foldl SSGQ.apply v)))
        (PanicOomProp s0) :=
  overDec_loop_ext hField hCons hNil img ext hL hAC s0 g hlen

/-! ## Pure Facts on the Archived Session -/

theorem overDec_flatMap_ne_nil (fs : List GenFieldQ) (hfs : fs ≠ []) :
    fs.flatMap GenFieldQ.enc ≠ [] := by
  rcases fs with _ | ⟨fl, fs⟩
  · exact absurd rfl hfs
  · rw [overDec_flatMap_cons]
    intro h
    exact overDec_enc_ne_nil fl (List.append_eq_nil_iff.mp h).1

/-- The archived session's encoding is shorter than `2 ^ 62`. -/
theorem overDec_encSession_length_lt (sess : Session (List (BitVec 8)))
    (hscope : Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q
      Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q ⟨some sess⟩) :
    (CryptoVerification.E2E.Record.encSession sess).length < 2 ^ 62 := by
  have h1 := Symbolic.Swarm.TRREF.B3DeserQ.encodeRecord_length_lt62_of_Q hscope
  have h3 : (CryptoVerification.E2E.Record.encSession sess).length ≤
      (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length := by
    unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
    dsimp only [Option.map_some]
    exact CryptoVerification.E2E.RecordX.lenField_length_ge' 1
      (CryptoVerification.E2E.Record.encSession sess)
  omega

/-- `recFieldsQ_fresh` restated on the field list `recFieldsQ r`, without `ssgqAfter`. -/
theorem overDec_freshChain_recFieldsQ (r : SessionRecord (List (BitVec 8)))
    (hscope : Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q
      Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q r) :
    OverDecFreshChain (Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ r) SSGQ.empty := by
  refine overDecFreshChain_of_getElem _ _ ?_
  intro k hk
  exact Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ_fresh r hscope k hk

/-- The fields of the archived session are fresh along the decode. -/
theorem overDec_freshChain_genFieldsQ (sess : Session (List (BitVec 8)))
    (hscope : Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q
      Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q ⟨some sess⟩) :
    OverDecFreshChain (genFieldsQ sess) SSGQ.empty := by
  have h := overDec_freshChain_recFieldsQ _ hscope
  rwa [Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ_of_some (s := sess) rfl] at h

/-- Decoding all the fields of the archived session gives `ssgqOf sess`. -/
theorem overDec_fold_genFieldsQ (sess : Session (List (BitVec 8)))
    (hscope : Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q
      Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q ⟨some sess⟩) :
    (genFieldsQ sess).foldl SSGQ.apply SSGQ.empty = ssgqOf sess := by
  have hrec : Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ ⟨some sess⟩ = genFieldsQ sess :=
    Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ_of_some (r := ⟨some sess⟩) (s := sess) rfl
  have h := Symbolic.Swarm.TRREF.B3DeserQ.ssgqAfter_recFieldsQ ⟨some sess⟩ hscope sess rfl
  unfold Symbolic.Swarm.TRREF.B3DeserQ.ssgqAfter at h
  rw [List.take_length, hrec] at h
  exact h

/-- The fields of the archived session are in the four groups and well-formed. -/
theorem overDec_mem_genFieldsQ (sess : Session (List (BitVec 8)))
    (hscope : Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q
      Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q ⟨some sess⟩)
    (hpp : sess.pendingPreKey = none) (hpk : sess.pendingKyberPreKey = none) :
    ∀ fl ∈ genFieldsQ sess, OverDecAnyField fl ∧ fl.Ok := by
  have hrec : Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ ⟨some sess⟩ = genFieldsQ sess :=
    Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ_of_some (r := ⟨some sess⟩) (s := sess) rfl
  have hok := Symbolic.Swarm.TRREF.B3DeserQ.recFieldsQ_ok ⟨some sess⟩ hscope
  rw [hrec] at hok
  exact fun fl hfl => ⟨overDec_anyField_of_mem sess hpp hpk fl hfl, hok fl hfl⟩

theorem overDec_encSession_eq (sess : Session (List (BitVec 8)))
    (hscope : Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q
      Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q ⟨some sess⟩) :
    CryptoVerification.E2E.Record.encSession sess = (genFieldsQ sess).flatMap GenFieldQ.enc :=
  Symbolic.Swarm.TRREF.B3DeserQ.encSession_eq_genFieldsQ ⟨some sess⟩ hscope sess rfl

/-! ## Top-Level Loop Composition -/

/-- The decode from the field body (`+0x216c`, after Entry) to the frozen post at `+0x2620`
(`A : RustAlloc`). -/
theorem overDec_after_entry_ext {A : RustAlloc} (hField : OverDecFieldStmtExt A OverDecAnyField)
    (hCons : OverDecHeadConsStmtExt A) (hNil : OverDecHeadNilStmtExt A)
    (img : Obj.Image) (ext : String → Option (State → State))
    (hL : Obj.Loads libsignalSessionImage img)
    (hAC : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext)
    (s0 sm : State) (g : OverDecG) (sess : Session (List (BitVec 8)))
    (hencfs : g.enc = (genFieldsQ sess).flatMap GenFieldQ.enc)
    (hlen : g.enc.length < 2 ^ 62) (hfsne : genFieldsQ sess ≠ [])
    (hmem : ∀ fl ∈ genFieldsQ sess, OverDecAnyField fl ∧ fl.Ok)
    (hfresh : OverDecFreshChain (genFieldsQ sess) SSGQ.empty)
    (hfold : (genFieldsQ sess).foldl SSGQ.apply SSGQ.empty = ssgqOf sess)
    (hregsm : OverDecRegs img ext s0 g 0x216c#64 sm) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2620#64) sm
      (overDecHeapExt A g g.enc SSGQ.empty)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2620#64 sf ∧
        (P_f ⊢ overDecHeapExt A g [] (ssgqOf sess)))
      (PanicOomProp s0) := by
  have hsuf : (genFieldsQ sess).flatMap GenFieldQ.enc <:+ g.enc := by
    rw [← hencfs]
  have hloop := overDec_loop_ext hField hCons hNil img ext hL hAC s0 g hlen (genFieldsQ sess)
    SSGQ.empty sm hfsne hmem hfresh hsuf hregsm
  rw [← hencfs, hfold] at hloop
  exact hloop

theorem overDec_after_entry (hField : OverDecFieldStmt OverDecAnyField)
    (hCons : OverDecHeadConsStmt) (hNil : OverDecHeadNilStmt)
    (img : Obj.Image) (ext : String → Option (State → State))
    (hL : Obj.Loads libsignalSessionImage img)
    (hAC : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img
      CryptoVerification.E2E.Record.A0 ext)
    (s0 sm : State) (g : OverDecG) (sess : Session (List (BitVec 8)))
    (hencfs : g.enc = (genFieldsQ sess).flatMap GenFieldQ.enc)
    (hlen : g.enc.length < 2 ^ 62) (hfsne : genFieldsQ sess ≠ [])
    (hmem : ∀ fl ∈ genFieldsQ sess, OverDecAnyField fl ∧ fl.Ok)
    (hfresh : OverDecFreshChain (genFieldsQ sess) SSGQ.empty)
    (hfold : (genFieldsQ sess).foldl SSGQ.apply SSGQ.empty = ssgqOf sess)
    (hregsm : OverDecRegs img ext s0 g 0x216c#64 sm) :
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2620#64) sm
      (overDecHeap g g.enc SSGQ.empty)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2620#64 sf ∧
        (P_f ⊢ overDecHeap g [] (ssgqOf sess)))
      (PanicOomProp s0) :=
  overDec_after_entry_ext hField hCons hNil img ext hL hAC s0 sm g sess hencfs hlen hfsne
    hmem hfresh hfold hregsm

/-- Compose Entry, the field loop over `genFieldsQ sess`, and loop exit into `OverPrevDecodeStmtExt A`. -/
theorem overPrevDecode_of_steps_ext {A : RustAlloc} (hEntry : OverDecEntryStmtExt A)
    (hField : OverDecFieldStmtExt A OverDecAnyField)
    (hCons : OverDecHeadConsStmtExt A) (hNil : OverDecHeadNilStmtExt A) :
    OverPrevDecodeStmtExt A := by
  intro img ext hL hAC s0 s prevCap prevPtr encCap encPtr enc sess hok hfz hsym hpc hrun
    hal htr hx21 hx24 hx25 hx27 hx29
  obtain ⟨henc, hscope, hver, hpp, hpk⟩ := hok
  have hencfs : enc = (genFieldsQ sess).flatMap GenFieldQ.enc :=
    henc.trans (overDec_encSession_eq sess hscope)
  have hfsne := overDec_genFieldsQ_ne_nil sess hver
  have hne : enc ≠ [] := hencfs ▸ overDec_flatMap_ne_nil _ hfsne
  have hlen : enc.length < 2 ^ 62 := henc ▸ overDec_encSession_length_lt sess hscope
  have hEntry' := hEntry img ext hL
    (stage1XAllocContractsX_of_trAllocContractsX hAC) s0 s
    ⟨s.sp, s.readReg64 .x19, s.readReg64 .x20, s.readReg64 .x26, prevCap, prevPtr, encCap,
      encPtr, enc, s⟩ hne hlen hfz hsym hpc hrun rfl hal htr rfl rfl rfl hx21 hx24 hx25 hx27 hx29 rfl
  refine overDec_sepWPp_seq hEntry' ?_
  rintro sm Pm - - ⟨hregsm, hentm⟩
  refine overDec_sepWPp_weaken_pre hentm ?_
  refine overDec_sepWPp_mono_post ?_ (overDec_after_entry_ext hField hCons hNil img ext hL hAC s0
    sm _ sess hencfs hlen hfsne (overDec_mem_genFieldsQ sess hscope hpp hpk)
    (overDec_freshChain_genFieldsQ sess hscope) (overDec_fold_genFieldsQ sess hscope) hregsm)
  rintro sf P_f - - ⟨⟨-, -, hsp, -, htrf, hfzf, hsymf, h19, h20, h26, h21, h24, h25, h27, -, h29, hvregsf⟩,
    hentf⟩
  exact ⟨Entails.trans hentf (overDec_exit_ext _ (ssgqOf sess) (by exact hne)), hsp, htrf, hfzf,
    hsymf, h19, h20, h21, h24, h25, h26, h27, h29, hvregsf⟩

theorem overPrevDecode_of_steps (hEntry : OverDecEntryStmt)
    (hField : OverDecFieldStmt OverDecAnyField)
    (hCons : OverDecHeadConsStmt) (hNil : OverDecHeadNilStmt) :
    OverPrevDecodeStmt :=
  overPrevDecode_of_steps_ext hEntry hField hCons hNil

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
