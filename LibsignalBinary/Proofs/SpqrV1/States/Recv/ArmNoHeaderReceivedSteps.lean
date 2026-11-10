/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledSteps
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.noHeaderReceived` Arm Steps (`0x55ca8`, `+2132`)

Jump-table dispatch (`+36 -> +2132`), pure unfolding lemmas, `57`-word (`456`B) state extraction
helpers, and instruction-level stepping lemmas for `.noHeaderReceived` (tag `7#64`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append

/-- Jump-table dispatch (`+36 -> +2132`, `0x55478 -> 0x55ca8`) specialized to `tag = 7#64` (`.noHeaderReceived`). -/
theorem states_recv_dispatch_noHeaderReceived
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (s1 : State) (fsp st_ptr : BitVec 64) (Rest : SepProp)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = st_ptr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2132#64)
      s1
      ((st_ptr ↦₆₄ 7#64) ∗ statesRecvRoAt b ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ (st_ptr ↦₆₄ 7#64) ∗ statesRecvRoAt b ∗ Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x0 = s1.readReg64 .x0 ∧
        s2.readReg64 .x1 = st_ptr ∧
        s2.readReg64 .x2 = s1.readReg64 .x2 ∧
        s2.readReg64 .x3 = s1.readReg64 .x3 ∧
        s2.readReg64 .x8 = 5#64 ∧
        s2.readReg64 .x12 = 7#64 ∧
        s2.readReg64 .x19 = s1.readReg64 .x0 ∧
        s2.readReg64 .x21 = fsp + 3856#64 ∧
        s2.readReg64 .x24 = s1.readReg64 .x2 ∧
        s2.readReg64 .x28 = fsp + 3272#64 ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧
        TraceCalleeSaved s2 s1) := by
  have h := states_recv_dispatch hb s1 fsp st_ptr 7#64 Rest
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset, statesRecvJumpIdx] at h
  exact h

/-! ## 1. Pure Model Unfolding Lemmas for `States.recv` on `.noHeaderReceived` -/

theorem states_recv_noHeaderReceived_gt {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (hgt : msg.epoch > st.uc.epoch) :
    (States.noHeaderReceived st).recv K msg =
      .error (.err (.epochOutOfRange msg.epoch)) := by
  unfold States.recv
  simp only [Chunked.SendCt.NoHeaderReceived.epoch, hgt, ↓reduceIte]

theorem states_recv_noHeaderReceived_lt {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (hlt : msg.epoch < st.uc.epoch) :
    (States.noHeaderReceived st).recv K msg =
      .ok { key := none, state := .noHeaderReceived st } := by
  have hnot_gt : ¬ (msg.epoch > st.uc.epoch) := BitVec.not_lt.mpr (BitVec.le_of_lt hlt)
  unfold States.recv
  simp only [Chunked.SendCt.NoHeaderReceived.epoch, hnot_gt, hlt, ↓reduceIte]

theorem states_recv_noHeaderReceived_eq_non_hdr {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (heq : msg.epoch = st.uc.epoch)
    (hno : ∀ c, msg.payload ≠ .hdr c) :
    (States.noHeaderReceived st).recv K msg =
      .ok { key := none, state := .noHeaderReceived st } := by
  have hnot_lt : ¬ (st.uc.epoch < st.uc.epoch) := BitVec.lt_irrefl _
  unfold States.recv
  cases hp : msg.payload <;>
    simp only [Chunked.SendCt.NoHeaderReceived.epoch, heq, hp, gt_iff_lt, hnot_lt, ↓reduceIte]
  exact False.elim (hno _ hp)

theorem states_recv_noHeaderReceived_eq_hdr {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (heq : msg.epoch = st.uc.epoch) (hp : msg.payload = .hdr chunk) :
    (States.noHeaderReceived st).recv K msg =
      match st.recv_hdr_chunk st.uc.epoch chunk with
      | .error e => .error e
      | .ok (.stillReceiving s') => .ok { key := none, state := .noHeaderReceived s' }
      | .ok (.done s') => .ok { key := none, state := .headerReceived s' } := by
  have hnot_lt : ¬ (st.uc.epoch < st.uc.epoch) := BitVec.lt_irrefl _
  unfold States.recv
  simp only [Chunked.SendCt.NoHeaderReceived.epoch, heq, hp, gt_iff_lt, hnot_lt, ↓reduceIte]
  cases st.recv_hdr_chunk st.uc.epoch chunk with
  | error e => rfl
  | ok res => cases res <;> rfl

/-! ## 2. 57-Word Extraction for `chunkedNoHeaderReceivedAt` (`456`B = `7 + 50` words) -/

def mkWords57_7_50 (g : AuthWords) (ep : BitVec 64) (p : Words5x10) : Words57 :=
  { b0 := ⟨g.v1.w0, g.v1.w1, g.v1.w2, g.v2.w0, g.v2.w1, g.v2.w2, ep,
           p.b0.w0, p.b0.w1, p.b0.w2⟩
    b1 := ⟨p.b0.w3, p.b0.w4, p.b0.w5, p.b0.w6, p.b0.w7, p.b0.w8, p.b0.w9,
           p.b1.w0, p.b1.w1, p.b1.w2⟩
    b2 := ⟨p.b1.w3, p.b1.w4, p.b1.w5, p.b1.w6, p.b1.w7, p.b1.w8, p.b1.w9,
           p.b2.w0, p.b2.w1, p.b2.w2⟩
    b3 := ⟨p.b2.w3, p.b2.w4, p.b2.w5, p.b2.w6, p.b2.w7, p.b2.w8, p.b2.w9,
           p.b3.w0, p.b3.w1, p.b3.w2⟩
    b4 := ⟨p.b3.w3, p.b3.w4, p.b3.w5, p.b3.w6, p.b3.w7, p.b3.w8, p.b3.w9,
           p.b4.w0, p.b4.w1, p.b4.w2⟩
    w50 := p.b4.w3
    w51 := p.b4.w4
    w52 := p.b4.w5
    w53 := p.b4.w6
    w54 := p.b4.w7
    w55 := p.b4.w8
    w56 := p.b4.w9 }

theorem words57List_mkWords57_7_50 (g : AuthWords) (ep : BitVec 64) (p : Words5x10) :
    ct2SentWordsList g ep ++ words5x10List p = words57List (mkWords57_7_50 g ep p) := by
  simp only [words57List, mkWords57_7_50, words5x10List, words10List,
    ct2SentWordsList, authWordsList, vecWordsList,
    List.append_assoc, List.cons_append, List.nil_append]

theorem chunkedNoHeaderReceivedAt_extract57 (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedNoHeaderReceivedAt A a st ⊢
      ∃∗ w : Words57,
        ⌜w.b0.w6 = st.uc.epoch⌝ ∗
        words57At a w ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) := by
  unfold chunkedNoHeaderReceivedAt
  rw [unchunkedNoHeaderReceivedAt_eq_ct2SentAt]
  refine Entails.trans (sepConj_mono
    (unchunkedCt2SentAt_extract A a { epoch := st.uc.epoch, auth := st.uc.auth })
    (relocatable_400_extract_words5x10 (Relocatable.of_polyDecoderAt A st.receiving_hdr) (a + 56#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro p
  let w := mkWords57_7_50 g st.uc.epoch p
  refine Entails.sepExists_right w (Entails.pure_right rfl ?_)
  rw [words57At_eq_wordsAt, ← words57List_mkWords57_7_50]
  exact wordsExtract_sepConj rfl (fun _ => rfl)

/-- 60-word (`480`-byte) state tuple (`6 × Words10`) for `Chunked.SendCt.HeaderReceived`. -/
structure Words60 where
  b0 : Words10
  b1 : Words10
  b2 : Words10
  b3 : Words10
  b4 : Words10
  b5 : Words10

def words60List (w : Words60) : List (BitVec 64) :=
  words10List w.b0 ++ words10List w.b1 ++ words10List w.b2 ++
  words10List w.b3 ++ words10List w.b4 ++ words10List w.b5

@[simp]
theorem length_words60List (w : Words60) : (words60List w).length = 60 := rfl

def words60At (a : BitVec 64) (w : Words60) : SepProp :=
  words10At a w.b0 ∗
  words10At (a + 80#64) w.b1 ∗
  words10At (a + 160#64) w.b2 ∗
  words10At (a + 240#64) w.b3 ∗
  words10At (a + 320#64) w.b4 ∗
  words10At (a + 400#64) w.b5

theorem words60At_eq_wordsAt (a : BitVec 64) (w : Words60) :
    words60At a w = wordsAt a (words60List w) := by
  unfold words60At words60List
  simp only [List.append_assoc, wordsAt_append, length_words10List,
    ← words10At_eq_wordsAt, bv_add_lit_add_lit_recv, sepConj_assoc]

theorem words60At_entails_memRegion (a : BitVec 64) (w : Words60) :
    words60At a w ⊢ memRegion a 480 := by
  rw [words60At_eq_wordsAt]
  exact wordsAt_entails_memRegion (words60List w) a 480 rfl

theorem recompose60 {F_pred : BitVec 64 → SepProp} (dst : BitVec 64) (w : Words60) :
    words60At dst w ∗ relocatedHeap F_pred (wordsBytes (words60List w)) ⊢ F_pred dst := by
  rw [words60At_eq_wordsAt, wordsAt_eq_pointsToBytes]
  exact relocatedHeap_recompose F_pred (wordsBytes (words60List w)) dst

def mkWords60_10_50 (g : ThreeVecWords) (ep : BitVec 64) (p : Words5x10) : Words60 :=
  { b0 := ⟨g.v1.w0, g.v1.w1, g.v1.w2, g.auth.v1.w0, g.auth.v1.w1, g.auth.v1.w2,
           g.auth.v2.w0, g.auth.v2.w1, g.auth.v2.w2, ep⟩
    b1 := p.b0
    b2 := p.b1
    b3 := p.b2
    b4 := p.b3
    b5 := p.b4 }

theorem words60List_mkWords60_10_50 (g : ThreeVecWords) (ep : BitVec 64) (p : Words5x10) :
    ekSentWordsList g ep ++ words5x10List p = words60List (mkWords60_10_50 g ep p) := by
  simp only [words60List, mkWords60_10_50, words5x10List, words10List,
    ekSentWordsList, ct2SentWordsList, authWordsList, vecWordsList,
    List.append_assoc, List.cons_append, List.nil_append]

theorem chunkedHeaderReceivedAt_extract60 (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedHeaderReceivedAt A a st ⊢
      ∃∗ w : Words60,
        words60At a w ∗
        relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst st) (wordsBytes (words60List w)) := by
  unfold chunkedHeaderReceivedAt
  rw [unchunkedHeaderReceivedAt_eq_ekSentAt]
  refine Entails.trans (sepConj_mono
    (unchunkedEkSentAt_extract A a { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.hdr })
    (relocatable_400_extract_words5x10 (Relocatable.of_polyDecoderAt A st.receiving_ek) (a + 80#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro p
  let w := mkWords60_10_50 g st.uc.epoch p
  refine Entails.sepExists_right w ?_
  rw [words60At_eq_wordsAt, ← words60List_mkWords60_10_50]
  exact wordsExtract_sepConj rfl (fun _ => rfl)

theorem noHeaderReceivedRecvHdrChunk_fnAddr_eq {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr noHeaderReceivedRecvHdrChunkName =
      (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 48640#64 :=
  (fnAddr_fwd_eq (d := 48640) (b := b) (X := Rust.withPanics ext)
    statesRecv_fnOff noHeaderReceivedRecvHdrChunk_fnOff (by decide)).symm

/-! ## 3. Instruction-Level Stepping Lemmas for `.noHeaderReceived` (`+2132`, `0x55ca8`)

Entry register and stack state at `+2132` (`0x55ca8`) after `states_recv_dispatch_noHeaderReceived`:
- `x8 = retPtr`, `x19 = selfA`, `x20 = msgA`
- `x29 = sp + 6704`, `x30 = retAddr`
-/

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv")

theorem selfA_noHeaderReceived_entails_memRegion (selfA : BitVec 64) (w : Words57) :
    (selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗ memRegion (selfA + 464#64) 464 ⊢
      memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split selfA 8 920 (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 456) (k := 464)
        (b' := selfA + 464#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion selfA 7#64)
    (sepConj_mono_left (words57At_entails_memRegion (selfA + 8#64) w))

theorem selfA_456_entails_memRegion (selfA : BitVec 64) :
    (selfA ↦₆₄ 7#64) ∗ memRegion (selfA + 8#64) 456 ∗ memRegion (selfA + 464#64) 464 ⊢
      memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split selfA 8 920 (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 456) (k := 464)
        (b' := selfA + 464#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion selfA 7#64)

theorem selfA_recompose_noHeaderReceived (A : RustAlloc) {F : ShaCompress}
    (selfA : BitVec 64) (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (w : Words57) :
    words57At (selfA + 8#64) w ∗
      relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w)) ⊢
      chunkedNoHeaderReceivedAt A (selfA + 8#64) st :=
  recompose57 (F_pred := fun dst => chunkedNoHeaderReceivedAt A dst st) (selfA + 8#64) w

theorem selfA_recompose_456 (A : RustAlloc) {F : ShaCompress}
    (selfA : BitVec 64) (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (w : Words57) :
    (selfA ↦₆₄ 7#64) ∗
      (words57At (selfA + 8#64) w ∗
       relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w))) ∗
      memRegion (selfA + 464#64) 464 ⊢
      (selfA ↦₆₄ 7#64) ∗
      chunkedNoHeaderReceivedAt A (selfA + 8#64) st ∗
      memRegion (selfA + 464#64) 464 :=
  sepConj_mono_right (sepConj_mono_left (selfA_recompose_noHeaderReceived A selfA st w))

theorem words63At_entails_words60At (a : BitVec 64) (w : Words60)
    (q60 : BitVec 128) (w62 : BitVec 64) :
    words63At (a + 8#64)
      { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
        q60 := q60, w62 := w62 } ⊢
      words60At (a + 8#64) w ∗ memRegion (a + 488#64) 24 := by
  have htail :
      ((a + 488#64) ↦₁₂₈ q60) ∗ ((a + 504#64) ↦₆₄ w62) ⊢
      memRegion (a + 488#64) 24 := by
    rw [ProofLib.memRegion_split' (b := a + 488#64) (n := 16) (k := 8)
          (b' := a + 504#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono
      (pointsTo128_entails_memRegion_16 (a + 488#64) q60)
      (ProofLib.pointsTo64_entails_memRegion (a + 504#64) w62)
  refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_right htail)
  dsimp only [words63At, words60At, words10At]
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]

theorem nhr_stillReceiving_out_entails_resultV1RecvAt (A : RustAlloc) {F : ShaCompress} (outA : BitVec 64)
    (outSt : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (w : Words57) (w57 w58 w59 : BitVec 64) (q60 : BitVec 128) (w62 w936 : BitVec 64) (q944 : BitVec 128) :
    (outA ↦₆₄ 7#64) ∗
      words63At (outA + 8#64)
        { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4
          b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56, w57, w58, w59⟩
          q60 := q60, w62 := w62 } ∗
      memRegion (outA + 512#64) 376 ∗
      memRegion (outA + 888#64) 40 ∗
      ((outA + 928#64) ↦₆₄ noneCap) ∗
      ((outA + 936#64) ↦₆₄ w936) ∗
      ((outA + 944#64) ↦₁₂₈ q944) ∗
      relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w)) ⊢
      resultV1RecvAt A (F := F) outA (.ok { key := none, state := .noHeaderReceived outSt }) := by
  dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt]
  rw [ProofLib.memRegion_split' (b := outA + 464#64) (n := 48) (k := 416)
        (b' := outA + 512#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 512#64) (n := 376) (k := 40)
        (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
  have h57 := words63At_entails_words57At outA w w57 w58 w59 q60 w62
  have hrec := recompose57 (F_pred := fun dst => chunkedNoHeaderReceivedAt A dst outSt) (outA + 8#64) w
  have hopt := optEpochSecretAt_none_of_parts A (outA + 928#64) w936 q944
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd] at hopt
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h57)) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ 7#64) ∗
    (words57At (outA + 8#64) w ∗
     relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w))) ∗
    (memRegion (outA + 464#64) 48 ∗ (memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40)) ∗
    (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono hrec (sepConj_mono_right hopt))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem nhr_done_out_entails_resultV1RecvAt (A : RustAlloc) {F : ShaCompress} (outA : BitVec 64)
    (outSt : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (w : Words60) (q60 : BitVec 128) (w62 w936 : BitVec 64) (q944 : BitVec 128) :
    (outA ↦₆₄ 8#64) ∗
      words63At (outA + 8#64)
        { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
          q60 := q60, w62 := w62 } ∗
      memRegion (outA + 512#64) 376 ∗
      memRegion (outA + 888#64) 40 ∗
      ((outA + 928#64) ↦₆₄ noneCap) ∗
      ((outA + 936#64) ↦₆₄ w936) ∗
      ((outA + 944#64) ↦₁₂₈ q944) ∗
      relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w)) ⊢
      resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerReceived outSt }) := by
  dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt]
  rw [ProofLib.memRegion_split' (b := outA + 488#64) (n := 24) (k := 416)
        (b' := outA + 512#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 512#64) (n := 376) (k := 40)
        (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
  have h60 := words63At_entails_words60At outA w q60 w62
  have hrec := recompose60 (F_pred := fun dst => chunkedHeaderReceivedAt A dst outSt) (outA + 8#64) w
  have hopt := optEpochSecretAt_none_of_parts A (outA + 928#64) w936 q944
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd] at hopt
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left h60)) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ 8#64) ∗
    (words60At (outA + 8#64) w ∗
     relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w))) ∗
    (memRegion (outA + 488#64) 24 ∗ (memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40)) ∗
    (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono hrec (sepConj_mono_right hopt))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_880_split_480_400 (fsp : BitVec 64) :
    memRegion (fsp + 976#64) 880 =
      memRegion (fsp + 976#64) 480 ∗ memRegion (fsp + 1456#64) 400 :=
  ProofLib.memRegion_split' (b := fsp + 976#64) (n := 480) (k := 400)
    (b' := fsp + 1456#64) rfl (by bv_omega) (by decide)

theorem words60At_400_entails_memRegion_880 (fsp : BitVec 64) (w : Words60) :
    words60At (fsp + 976#64) w ∗ memRegion (fsp + 1456#64) 400 ⊢
      memRegion (fsp + 976#64) 880 := by
  rw [memRegion_880_split_480_400 fsp]
  exact sepConj_mono_left (words60At_entails_memRegion (fsp + 976#64) w)

theorem words57At_eq_pointsToBytes (a : BitVec 64) (w : Words57) :
    words57At a w = (a ↦ₛ wordsBytes (words57List w)) := by
  rw [words57At_eq_wordsAt, wordsAt_eq_pointsToBytes]

@[simp]
theorem length_wordsBytes_words57List (w : Words57) :
    (wordsBytes (words57List w)).length = 456 := by
  rw [length_wordsBytes, length_words57List]

theorem call_memcpy_words57 {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    (dst src : BitVec 64) (w : Words57)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = 456)
    (hsplit : P = (memRegion dst 456 ∗ words57At src w) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf ((words57At dst w ∗ words57At src w) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit, words57At_eq_pointsToBytes src w]
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, wordsBytes (words57List w)))
    (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [length_wordsBytes_words57List, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · dsimp only [sessionMemcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    rw [← words57At_eq_pointsToBytes dst w, ← words57At_eq_pointsToBytes src w]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

theorem fnAddr_adrp_5901c {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr statesRecvName + 15304#64) &&&
      0xfffffffffffff000#64) + bv% (ls_xref% 0x53c24 - 0x53000) = b + bv% (ls_xref% 0x53c24) := by
  rw [Program.fnAddr_rebase, statesRecv_fnOff]
  revert hb; bv_bits

def nhrUnusedRestAt (fsp : BitVec 64) : SepProp :=
  memRegion fsp 8 ∗ memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
  memRegion (fsp + 2736#64) 16 ∗ memRegion (fsp + 3208#64) 936

theorem sendEkUnusedAt_split_nhr (fsp : BitVec 64) :
    sendEkUnusedAt fsp ⊢ memRegion (fsp + 2752#64) 456 ∗ nhrUnusedRestAt fsp := by
  unfold sendEkUnusedAt nhrUnusedRestAt
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 16) (k := 1392)
        (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 456) (k := 936)
        (b' := fsp + 3208#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_nhrUnusedRest_entails_sendEkUnusedAt (fsp : BitVec 64) :
    memRegion (fsp + 2752#64) 456 ∗ nhrUnusedRestAt fsp ⊢ sendEkUnusedAt fsp := by
  unfold sendEkUnusedAt nhrUnusedRestAt
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 16) (k := 1392)
        (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 456) (k := 936)
        (b' := fsp + 3208#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem words57At_nhrUnusedRest_entails_sendEkUnusedAt (fsp : BitVec 64) (w : Words57) :
    words57At (fsp + 2752#64) w ∗ nhrUnusedRestAt fsp ⊢ sendEkUnusedAt fsp :=
  Entails.trans
    (sepConj_mono_left (words57At_entails_memRegion (fsp + 2752#64) w))
    (memRegion_nhrUnusedRest_entails_sendEkUnusedAt fsp)

set_option maxHeartbeats 800000 in
theorem nhr_step_2132_2180
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s : State) (fsp out st_ptr msg_ptr msg_ep w62_old : BitVec 64)
    (w : Words57) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2132#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = st_ptr) (hx19 : s.readReg64 .x19 = out) (hx24 : s.readReg64 .x24 = msg_ptr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2180#64) s
      (memRegion (fsp + 2752#64) 456 ∗ words57At (st_ptr + 8#64) w ∗
       (msg_ptr ↦₆₄ msg_ep) ∗ ((fsp + 504#64) ↦₆₄ w62_old) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          words57At (fsp + 2752#64) w ∗ words57At (st_ptr + 8#64) w ∗
          (msg_ptr ↦₆₄ msg_ep) ∗ ((fsp + 504#64) ↦₆₄ w.b0.w6) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = msg_ep ∧
        sm.readReg64 .x21 = st_ptr ∧
        sm.readReg64 .x24 = msg_ptr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep w.b0.w6)) ∧
        sm.pstate.z = (ekCmpW8 (subsPState64 msg_ep w.b0.w6) == 0#32) ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx1 hx19 hx24
  have hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      sessionMemcpyRegionSpec := Leaves.sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) (b := b) (X := Rust.withPanics ext)
      statesRecv_fnOff (ls_stub% "memcpy") (by decide)).symm hmemcpy
  states_recv_fetches_range b (Rust.withPanics ext) 2132 48
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  refine call_memcpy_words57 (ret_pc := entry + 2152#64)
    hmemcpy_raw (s.sp + 2752#64) (s.readReg64 .x1 + 8#64) w
    rfl hrun rfl hfsp_align rfl rfl rfl rfl rfl (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
  have hx19_1 : sf1.readReg64 .x19 = s.readReg64 .x19 := hcs1.1
  have hx21_1 : sf1.readReg64 .x21 = s.readReg64 .x1 := hcs1.2.2.1
  have hx24_1 : sf1.readReg64 .x24 = s.readReg64 .x24 := hcs1.2.2.2.2.2.1
  have hx29_1 : sf1.readReg64 .x29 = s.readReg64 .x29 := hcs1.2.2.2.2.2.2.2.2.2.2.1
  wp_simp_pre [words57At, words10At, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [words57At, words10At, ekCmpW8, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc,
    hx19_1, hx21_1, hx24_1, hx29_1, htr1]
  wp_done

def nhrSpills8984 (s : State) (sp : SendEkSpills) : SendEkSpills :=

  { sp with
    b2 := { sp.b2 with w8 := noneCap }
    b3 := { sp.b3 with w2 := s.readReg64 .x26, w4 := s.readReg64 .x1 }
    b4 := { sp.b4 with w2 := s.readReg64 .x23 }
    b5 := { sp.b5 with w4 := s.readReg64 .x9, w5 := s.readReg64 .x6,
                       w8 := s.readReg64 .x5, w9 := s.readReg64 .x3 } }

set_option maxHeartbeats 800000 in
theorem nhr_step_8984_18996
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8984#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s
      (sendEkSpillsAt fsp sp ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ sendEkSpillsAt fsp (nhrSpills8984 s sp) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = s.readReg64 .x0 ∧ sm.readReg64 .x1 = sp.b1.w6 ∧
        sm.readReg64 .x2 = sp.b1.w0 ∧ sm.readReg64 .x3 = s.readReg64 .x27 ∧
        sm.readReg64 .x4 = s.readReg64 .x4 ∧ sm.readReg64 .x5 = sp.b2.w6 ∧
        sm.readReg64 .x6 = s.readReg64 .x7 ∧ sm.readReg64 .x7 = s.readReg64 .x20 ∧
        sm.readReg64 .x8 = sp.b2.w5 ∧ sm.readReg64 .x9 = s.readReg64 .x14 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧ sm.readReg64 .x11 = s.readReg64 .x11 ∧
        sm.readReg64 .x12 = s.readReg64 .x12 ∧ sm.readReg64 .x13 = s.readReg64 .x13 ∧
        sm.readReg64 .x14 = s.readReg64 .x17 ∧ sm.readReg64 .x15 = s.readReg64 .x15 ∧
        sm.readReg64 .x16 = s.readReg64 .x16 ∧ sm.readReg64 .x17 = s.readReg64 .x18 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = sp.b1.w7 ∧
        sm.readReg64 .x21 = sp.b2.w9 ∧ sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = sp.b1.w8 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x2 ∧
        sm.readReg64 .x27 = sp.b1.w9 ∧ sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ sm.readReg64 .x30 = s.readReg64 .x30 ∧
        TraceCalleeSaved sm s) := by
  subst hsp
  states_recv_fetches_range b (Rust.withPanics ext) 8984 80
  dsimp only [tripleRatchetProgAtExt, statesRecvName, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_simp_pre [sendEkSpillsAt, words10At, nhrSpills8984, noneCap, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [sendEkSpillsAt, words10At, nhrSpills8984, noneCap, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

def nhrSpills8664 (sp : SendEkSpills) (w : Words57) : SendEkSpills :=
  { sp with
    b1 := { sp.b1 with w6 := w.b0.w0, w8 := w.b1.w5, w9 := w.b1.w6 }
    b2 := { sp.b2 with w5 := w.b0.w1, w6 := w.b4.w8, w7 := 7#64, w9 := w.b4.w2 }
    b3 := { sp.b3 with w3 := w.b2.w1, w5 := w.b0.w7, w6 := w.b1.w3, w7 := w.b2.w5, w8 := w.b3.w0, w9 := w.b2.w8 }
    b4 := { sp.b4 with w0 := w.b2.w6, w1 := w.b1.w2, w3 := w.b1.w0, w4 := w.b2.w2,
                       w5 := w.b0.w5, w6 := w.b0.w4, w7 := w.b1.w1, w8 := w.b2.w0, w9 := w.b2.w3 }
    b5 := { sp.b5 with w0 := w.b0.w9, w1 := w.b4.w4, w2 := w.b1.w4, w3 := w.b0.w8,
                       w6 := w.b0.w3, w7 := w.b2.w4 }
    w60 := w.w56
    w61 := w.b0.w2 }

set_option maxHeartbeats 1200000 in
theorem nhr_step_8664_8984
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (w : Words57) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8664#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8984#64) s
      (words57At (fsp + 2752#64) w ∗ sendEkSpillsAt fsp sp ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words57At (fsp + 2752#64) w ∗ sendEkSpillsAt fsp (nhrSpills8664 sp w) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = w.b3.w9 ∧ sm.readReg64 .x1 = w.b2.w7 ∧
        sm.readReg64 .x2 = w.b4.w7 ∧ sm.readReg64 .x3 = w.w54 ∧
        sm.readReg64 .x4 = w.b4.w9 ∧ sm.readReg64 .x5 = w.b4.w6 ∧
        sm.readReg64 .x6 = w.w50 ∧ sm.readReg64 .x7 = w.b4.w0 ∧
        sm.readReg64 .x9 = w.b1.w7 ∧ sm.readReg64 .x10 = w.b3.w5 ∧
        sm.readReg64 .x11 = w.b3.w4 ∧ sm.readReg64 .x12 = w.b3.w3 ∧
        sm.readReg64 .x13 = w.w52 ∧ sm.readReg64 .x14 = w.b4.w3 ∧
        sm.readReg64 .x15 = w.b3.w6 ∧ sm.readReg64 .x16 = w.w55 ∧
        sm.readReg64 .x17 = w.w53 ∧ sm.readReg64 .x18 = w.b4.w5 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = w.b3.w8 ∧
        sm.readReg64 .x22 = w.w51 ∧ sm.readReg64 .x23 = w.b1.w9 ∧
        sm.readReg64 .x24 = w.b3.w1 ∧ sm.readReg64 .x25 = w.b3.w2 ∧
        sm.readReg64 .x26 = w.b1.w8 ∧ sm.readReg64 .x27 = w.b2.w9 ∧
        sm.readReg64 .x28 = w.b3.w7 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = w.b4.w1 ∧ TraceCalleeSaved sm s) := by
  subst hsp
  states_recv_fetches_range b (Rust.withPanics ext) 8664 320
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_simp_pre [words57At, sendEkSpillsAt, words10At, nhrSpills8664, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [words57At, sendEkSpillsAt, words10At, nhrSpills8664, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

theorem nhr_step_2180_lt_8664
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2180#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hz : s.pstate.z = false) (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 255#32) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8664#64) s
      Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp
  have hcond : ConditionHolds CondCode.EQ s.pstate = false := hz
  states_recv_fetches_range b (Rust.withPanics ext) 2180 12
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem nhr_step_2180_eq_8568
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2180#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hz : s.pstate.z = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8568#64) s
      Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp
  have hcond : ConditionHolds CondCode.EQ s.pstate = true := hz
  states_recv_fetches_range b (Rust.withPanics ext) 2180 4
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; wp_steps; wp_done

open CryptoVerification.SpqrV1.Top.MessageSerialize in
theorem nhr_step_8568_non_hdr_8664
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp msg_ptr : BitVec 64) (p : MessagePayload spqrPolyApi) (Frame : SepProp)
    (hno : ∀ c, p ≠ .hdr c)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8568#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx24 : s.readReg64 .x24 = msg_ptr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8664#64) s
      (messagePayloadAt spqrPolyApi msg_ptr p ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ messagePayloadAt spqrPolyApi msg_ptr p ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x24 = msg_ptr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx24
  states_recv_fetches_range b (Rust.withPanics ext) 8568 12
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  cases p with
  | hdr c => exact False.elim (hno c rfl)
  | none | ek _ | ct1 _ | ct1Ack _ | ekCt1Ack _ | ct2 _ =>
    dsimp only [messagePayloadAt, BitVec.ofNat_eq_ofNat]
    wp_simp_pre [sepConj_assoc]; wp_steps; wp_done

open CryptoVerification.SpqrV1.Top.MessageSerialize in
theorem nhr_step_8568_hdr_8612
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s : State) (fsp out st_ptr msg_ptr msg_ep : BitVec 64)
    (chunk : Chunk) (w : Words57) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8568#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = msg_ep)
    (hx21 : s.readReg64 .x21 = st_ptr) (hx24 : s.readReg64 .x24 = msg_ptr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8612#64) s
      (memRegion (fsp + 976#64) 456 ∗ words57At (st_ptr + 8#64) w ∗
       messagePayloadAt spqrPolyApi msg_ptr (.hdr chunk) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          words57At (fsp + 976#64) w ∗ words57At (st_ptr + 8#64) w ∗
          messagePayloadAt spqrPolyApi msg_ptr (.hdr chunk) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1856#64 ∧
        sm.readReg64 .x1 = fsp + 976#64 ∧
        sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x3 = msg_ptr + 10#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = msg_ep ∧
        sm.readReg64 .x21 = st_ptr ∧
        sm.readReg64 .x24 = msg_ptr ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19 hx20 hx21 hx24
  have hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      sessionMemcpyRegionSpec := Leaves.sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) (b := b) (X := Rust.withPanics ext)
      statesRecv_fnOff (ls_stub% "memcpy") (by decide)).symm hmemcpy
  states_recv_fetches_range b (Rust.withPanics ext) 8568 44
  dsimp only [tripleRatchetProgAtExt, statesRecvName, messagePayloadAt, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_simp_pre [sepConj_assoc]
  wp_steps
  refine call_memcpy_words57 (ret_pc := entry + 8596#64)
    hmemcpy_raw (s.sp + 976#64) (s.readReg64 .x21 + 8#64) w
    rfl hrun rfl hfsp_align rfl rfl rfl rfl rfl (by sep_focus) ?_
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
  have hx19_1 : sf1.readReg64 .x19 = s.readReg64 .x19 := hcs1.1
  have hx20_1 : sf1.readReg64 .x20 = s.readReg64 .x20 := hcs1.2.1
  have hx21_1 : sf1.readReg64 .x21 = s.readReg64 .x21 := hcs1.2.2.1
  have hx24_1 : sf1.readReg64 .x24 = s.readReg64 .x24 := hcs1.2.2.2.2.2.1
  have hx29_1 : sf1.readReg64 .x29 = s.readReg64 .x29 := hcs1.2.2.2.2.2.2.2.2.2.2.1
  wp_steps
  simp only [sepConj_assoc, hx19_1, hx20_1, hx21_1, hx24_1, hx29_1, htr1]
  wp_done

/-- Deallocation view of `unchunkedNoHeaderReceivedAt A a uc` (`56` bytes = `0x38`):
    two `Vec<u8>` headers (`twoVec56HeadersAt a g`) and their conditional heap allocations. -/
theorem unchunkedNoHeaderReceivedAt_entails_dealloc (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (uc : Unchunked.SendCt.NoHeaderReceived (spqrAuthApi F)) :
    unchunkedNoHeaderReceivedAt A a uc ⊢
      ∃∗ g : TwoVecGhost,
        twoVec56HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr := by
  rw [unchunkedNoHeaderReceivedAt_eq_ct2SentAt]
  exact unchunkedCt2SentAt_entails_dealloc A a { epoch := uc.epoch, auth := uc.auth }

/-- Join `memRegion (fsp + 2752) 56`, `memRegion (fsp + 2808) 384`, and `memRegion (fsp + 3192) 16`
    into `memRegion (fsp + 2752) 456`. -/
theorem chunked_nhr_456_join (fsp : BitVec 64) :
    memRegion (fsp + 2752#64) 56 ∗ memRegion (fsp + 2808#64) polyArrayBytes ∗
      memRegion (fsp + 3192#64) 16 ⊢
      memRegion (fsp + 2752#64) 456 := by
  dsimp only [polyArrayBytes]
  rw [ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 56) (k := 400) (b' := fsp + 2808#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2808#64) (n := 384) (k := 16) (b' := fsp + 3192#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem nhr_step_2180_gt_19324
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (fsp out msg_ep u0 u16 : BitVec 64) (u8 : BitVec 8)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2180#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hz : s.pstate.z = false) (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 1#32)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = msg_ep) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64) s
      ((out ↦₆₄ u0) ∗ ((out + 8#64) ↦₈ u8) ∗ ((out + 16#64) ↦₆₄ u16) ∗
       chunkedNoHeaderReceivedAt A (fsp + 2752#64) st ∗
       A.pool ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 4#8) ∗ ((out + 16#64) ↦₆₄ msg_ep) ∗
          memRegion (fsp + 2752#64) 456 ∗
          A.pool ∗ stackAt fsp dropStack32 ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  subst hsp hx19 hx20
  have hcond : ConditionHolds CondCode.EQ s.pstate = false := hz
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := Drop.sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      statesRecv_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hpt16_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18446744073709512900#64)
      (dropGlueSortedSetPt16Spec A) := by
    have hrel : (tripleRatchetProgAtExt b ext).fnAddr statesRecvName =
        (tripleRatchetProgAtExt b ext).fnAddr dropSortedSetPt16Name + BitVec.ofNat 64 38716 :=
      Program.fnAddr_rel (k := 38716) (b := b) (X := Rust.withPanics ext)
        libsignalSessionCode_fnOff_0x46920 statesRecv_fnOff (by decide)
    refine Drop.sub_ok_of_addr_eq ?_ (drop_glue_sorted_set_pt16_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [rustDeallocSpec] at hdealloc_raw
  states_recv_fetches_range b (Rust.withPanics ext) 2180 88
  dsimp only [tripleRatchetProgAtExt, statesRecvName, dropSortedSetPt16Name,
    chunkedNoHeaderReceivedAt, noneCap, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw hpt16_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  nth_rw 1 [stackAt_dropStack32_split_bottom s.sp]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_left (unchunkedNoHeaderReceivedAt_entails_dealloc A (s.sp + 2752#64) st.uc)))))) ?_
  wp_pull_exists; rename_i g
  refine DropGlueFacts.seq_clean (mid := entry + 2232#64)
    (P_mid := ((s.readReg64 .x19 ↦₆₄ 0xffffffffffffffff#64) ∗
      ((s.readReg64 .x19 + 8#64) ↦₈ 4#8) ∗
      ((s.readReg64 .x19 + 16#64) ↦₆₄ s.readReg64 .x20) ∗
      ((twoVec56HeadersAt (s.sp + 2752#64) g ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
       polyDecoderAt A ((s.sp + 2752#64) + 56#64) st.receiving_hdr) ∗
      A.pool ∗ (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ Frame))
    (Q := fun sm => sm.sp = s.sp ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s)
    ?_ ?_
  · dsimp only [twoVec56HeadersAt, vecCapPtrDealloc]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_simp_pre [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
      wp_steps
      refine DropGlueFacts.align_pre
        (by dsimp only [Reg.x19, Reg.x20]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd, beq_iff_eq]; ac_rfl) ?_
      wp_done
    · wp_simp_pre [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
      wp_steps; wp_apply
      refine DropGlueFacts.align_pre
        (by dsimp only [Reg.x19, Reg.x20]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd, beq_iff_eq]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨hsp_1, hx29_1, htrace_1⟩
    refine DropGlueFacts.seq_clean (mid := entry + 2252#64)
      (P_mid := ((s.readReg64 .x19 ↦₆₄ 0xffffffffffffffff#64) ∗
        ((s.readReg64 .x19 + 8#64) ↦₈ 4#8) ∗
        ((s.readReg64 .x19 + 16#64) ↦₆₄ s.readReg64 .x20) ∗
        (memRegion (s.sp + 2752#64) 56 ∗
         polyDecoderAt A ((s.sp + 2752#64) + 56#64) st.receiving_hdr) ∗
        A.pool ∗ stackAt s.sp dropStack32 ∗ Frame))
      (Q := fun sm => sm.sp = s.sp ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s)
      ?_ ?_
    · have hstep2 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 2252#64) s1
          ((s.readReg64 .x19 ↦₆₄ 0xffffffffffffffff#64) ∗
            ((s.readReg64 .x19 + 8#64) ↦₈ 4#8) ∗
            ((s.readReg64 .x19 + 16#64) ↦₆₄ s.readReg64 .x20) ∗
            ((twoVec56HeadersAt (s.sp + 2752#64) g ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
             polyDecoderAt A ((s.sp + 2752#64) + 56#64) st.receiving_hdr) ∗
            A.pool ∗ (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (s.readReg64 .x19 ↦₆₄ 0xffffffffffffffff#64) ∗
              ((s.readReg64 .x19 + 8#64) ↦₈ 4#8) ∗
              ((s.readReg64 .x19 + 16#64) ↦₆₄ s.readReg64 .x20) ∗
              (twoVec56HeadersAt (s.sp + 2752#64) g ∗
               polyDecoderAt A ((s.sp + 2752#64) + 56#64) st.receiving_hdr) ∗
              A.pool ∗ (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ Frame) ∧
            sm.sp = s.sp ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
        dsimp only [twoVec56HeadersAt, vecCapPtrDealloc]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_simp_pre [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
          wp_steps
          refine DropGlueFacts.align_pre
            (by dsimp only [Reg.x19, Reg.x20]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]; ac_rfl) ?_
          wp_done
        · wp_simp_pre [bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
          wp_steps; wp_apply
          refine DropGlueFacts.align_pre
            (by rw [hsp_1]; dsimp only [Reg.x19, Reg.x20]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]; ac_rfl) ?_
          wp_done
      rw [stackAt_dropStack32_split_bottom s.sp]
      exact SepWP.strengthen_entails_const
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (sepConj_mono_left (twoVec56HeadersAt_entails_memRegion_56 (s.sp + 2752#64) g))))))
        hstep2
    · intro s2 hpc2 hrun2 ⟨hsp_2, hx29_2, htrace_2⟩
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (sepConj_mono_right
            (polyDecoderAt_entails_vecs_tail A ((s.sp + 2752#64) + 56#64) st.receiving_hdr)))))) ?_
      wp_pull_exists; rename_i vecs
      have h2808 : (s.sp + 2752#64) + 56#64 = s.sp + 2808#64 := by bv_omega
      have h440 : (s.sp + 2808#64) + 384#64 = (s.sp + 2752#64) + 440#64 := by bv_omega
      rw [h2808, h440]
      wp_focus_pure; intro hvecs_len
      wp_steps
      have hstack_eq : dropStack32 = dropGluePoly16Stack := rfl
      rw [hstack_eq]
      wp_call hpt16_raw ⟨s.sp + 2808#64, vecs⟩
      wp_steps
      rw [← hstack_eq, hsp_2]
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            (s.readReg64 (Reg.gpr 19#5) ↦₆₄ 0xffffffffffffffff#64) ∗
              ((s.readReg64 (Reg.gpr 19#5) + 8#64) ↦₈ 4#8) ∗
              ((s.readReg64 (Reg.gpr 19#5) + 16#64) ↦₆₄ s.readReg64 (Reg.gpr 20#5)) ∗
              (memRegion (s.sp + 2752#64) 56 ∗
               memRegion (s.sp + 2808#64) polyArrayBytes ∗
               memRegion (s.sp + 3192#64) 16) ∗
              A.pool ∗ stackAt s.sp dropStack32 ∗ Frame by ac_rfl))
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (chunked_nhr_456_join s.sp)))))) ?_
      dsimp only [Reg.x19, Reg.x20, Reg.x29] at hx29_2 ⊢
      wp_done

theorem add_two_bne_zero_of_ne {w0 : BitVec 64} (h : w0 ≠ 0xfffffffffffffffe#64) :
    (w0 + 2#64 != 0#64) = true := by
  rw [bne_iff_ne]; bv_omega

theorem add_one_beq_zero_false_of_ne {w0 : BitVec 64} (h : w0 ≠ noneCap) :
    (w0 + 1#64 == 0#64) = false := by
  unfold noneCap at h; rw [beq_eq_false_iff_ne]; bv_omega

theorem nhr_step_8612_call
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp msg_ep msg_ptr : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8612#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1856#64) (hx1 : s.readReg64 .x1 = fsp + 976#64)
    (hx2 : s.readReg64 .x2 = msg_ep) (hx3 : s.readReg64 .x3 = msg_ptr + 10#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr noHeaderReceivedRecvHdrChunkName) s Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧ sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1856#64 ∧ sm.readReg64 .x1 = fsp + 976#64 ∧
        sm.readReg64 .x2 = msg_ep ∧ sm.readReg64 .x3 = msg_ptr + 10#64 ∧
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8616#64 ∧
        CalleeSavedPreserved s sm ∧ TraceCalleeSaved sm s) := by
  subst hsp hx2
  have hfn := noHeaderReceivedRecvHdrChunk_fnAddr_eq (b := b) (ext := ext)
  rw [hfn]
  states_recv_fetches_range b (Rust.withPanics ext) 8612 4
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem nhr_step_8616_err_19324
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out w1 w2 w3 sp_w61 o0 o1 o2 o3 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8616#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64) s
      (((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
       ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗ ((fsp + 496#64) ↦₆₄ sp_w61) ∗
       (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗ ((out + 24#64) ↦₆₄ o3) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
          ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗ ((fsp + 496#64) ↦₆₄ w3) ∗
          (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗ ((out + 24#64) ↦₆₄ w3) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  subst hsp hx19
  states_recv_fetches_range b (Rust.withPanics ext) 8616 48
  dsimp only [tripleRatchetProgAtExt, statesRecvName, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; wp_simp_pre [sepConj_assoc]; wp_steps; wp_done

def nhrSpills15296 (sp : SendEkSpills) (w : Words60) : SendEkSpills :=
  { sp with
    b0 := { sp.b0 with w1 := w.b3.w6, w2 := w.b3.w2, w4 := w.b3.w3, w5 := w.b4.w2,
                       w6 := w.b4.w1, w7 := w.b3.w9, w8 := w.b3.w5, w9 := w.b3.w4 }
    b1 := { sp.b1 with w2 := w.b4.w0, w3 := w.b3.w7, w5 := w.b3.w8, w6 := w.b0.w1 }
    b2 := { sp.b2 with w1 := w.b5.w2, w2 := w.b5.w0, w3 := w.b4.w4, w4 := w.b4.w6,
                       w5 := w.b0.w2, w6 := w.b4.w9 }
    b3 := { sp.b3 with w3 := w.b2.w2, w4 := w.b2.w8, w8 := w.b3.w1, w9 := w.b2.w9 }
    b4 := { sp.b4 with w0 := w.b2.w7, w4 := w.b2.w3, w6 := w.b0.w5, w9 := w.b2.w4 }
    b5 := { sp.b5 with w1 := w.b4.w5, w2 := w.b1.w4, w3 := w.b0.w8, w6 := w.b0.w4,
                       w7 := w.b2.w5, w9 := w.b5.w5 }
    w61 := w.b0.w3, w62 := w.b0.w7 }

set_option maxHeartbeats 1200000 in
theorem nhr_step_8616_ok_15296
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (w : Words60) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0 : w.b0.w0 ≠ 0xfffffffffffffffe#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8616#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 15296#64) s
      (words60At (fsp + 1856#64) w ∗ sendEkSpillsAt fsp sp ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words60At (fsp + 1856#64) w ∗ sendEkSpillsAt fsp (nhrSpills15296 sp w) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = w.b0.w9 ∧ sm.readReg64 .x1 = w.b2.w0 ∧
        sm.readReg64 .x2 = w.b1.w5 ∧ sm.readReg64 .x4 = w.b1.w6 ∧
        sm.readReg64 .x5 = w.b5.w3 ∧ sm.readReg64 .x6 = w.b5.w1 ∧
        sm.readReg64 .x7 = w.b2.w6 ∧ sm.readReg64 .x8 = w.b5.w5 ∧
        sm.readReg64 .x9 = w.b1.w7 ∧ sm.readReg64 .x10 = w.b1.w3 ∧
        sm.readReg64 .x11 = w.b4.w8 ∧ sm.readReg64 .x12 = w.b3.w0 ∧
        sm.readReg64 .x13 = w.b4.w3 ∧ sm.readReg64 .x14 = w.b1.w1 ∧
        sm.readReg64 .x15 = w.b1.w2 ∧ sm.readReg64 .x16 = w.b5.w7 ∧
        sm.readReg64 .x17 = w.b5.w4 ∧ sm.readReg64 .x18 = w.b1.w0 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = w.b0.w6 ∧
        sm.readReg64 .x21 = w.b4.w7 ∧ sm.readReg64 .x22 = w.b0.w0 ∧
        sm.readReg64 .x23 = w.b1.w9 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = w.b1.w8 ∧
        sm.readReg64 .x27 = w.b5.w6 ∧ sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ sm.readReg64 .x30 = w.b2.w1 ∧
        sm.pstate = addsPState64 w.b0.w0 1#64 ∧ TraceCalleeSaved sm s) := by
  subst hsp
  have hz : (w.b0.w0 + 2#64 != 0#64) = true := add_two_bne_zero_of_ne hw0
  states_recv_fetches_range b (Rust.withPanics ext) 8616 28
  states_recv_fetches_range b (Rust.withPanics ext) 14972 324
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_simp_pre [words60At, sendEkSpillsAt, words10At, nhrSpills15296, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [words60At, sendEkSpillsAt, words10At, nhrSpills15296, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

def nhrSpillsStill8984 (s : State) (sp : SendEkSpills) : SendEkSpills :=
  { sp with
    b0 := { sp.b0 with w0 := s.readReg64 .x5 }
    b1 := { sp.b1 with w8 := s.readReg64 .x4, w9 := s.readReg64 .x9 }
    b2 := { sp.b2 with w7 := 7#64, w9 := s.readReg64 .x13 }
    b3 := { sp.b3 with w5 := sp.b5.w3, w6 := sp.b5.w2, w7 := s.readReg64 .x7 }
    b4 := { sp.b4 with w1 := s.readReg64 .x10, w3 := s.readReg64 .x14, w5 := s.readReg64 .x20,
                       w7 := s.readReg64 .x15, w8 := s.readReg64 .x30 }
    b5 := { sp.b5 with w0 := s.readReg64 .x18, w2 := s.readReg64 .x2, w3 := s.readReg64 .x0 }
    w60 := s.readReg64 .x16 }

set_option maxHeartbeats 800000 in
theorem nhr_step_15296_still_8984
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 15296#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hps : s.pstate = addsPState64 noneCap 1#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8984#64) s
      (sendEkSpillsAt fsp sp ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ sendEkSpillsAt fsp (nhrSpillsStill8984 s sp) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = sp.b1.w2 ∧ sm.readReg64 .x1 = sp.b3.w4 ∧
        sm.readReg64 .x2 = s.readReg64 .x11 ∧ sm.readReg64 .x3 = sp.b5.w9 ∧
        sm.readReg64 .x4 = sp.b2.w2 ∧ sm.readReg64 .x5 = s.readReg64 .x21 ∧
        sm.readReg64 .x6 = s.readReg64 .x6 ∧ sm.readReg64 .x7 = sp.b0.w6 ∧
        sm.readReg64 .x8 = sp.b5.w2 ∧ sm.readReg64 .x9 = s.readReg64 .x26 ∧
        sm.readReg64 .x10 = sp.b0.w1 ∧ sm.readReg64 .x11 = sp.b0.w8 ∧
        sm.readReg64 .x12 = sp.b0.w9 ∧ sm.readReg64 .x13 = s.readReg64 .x5 ∧
        sm.readReg64 .x14 = sp.b2.w3 ∧ sm.readReg64 .x15 = sp.b1.w3 ∧
        sm.readReg64 .x16 = s.readReg64 .x27 ∧ sm.readReg64 .x17 = s.readReg64 .x17 ∧
        sm.readReg64 .x18 = sp.b2.w4 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp.b0.w7 ∧ sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = sp.b2.w1 ∧ sm.readReg64 .x23 = s.readReg64 .x1 ∧
        sm.readReg64 .x24 = sp.b0.w2 ∧ sm.readReg64 .x25 = sp.b0.w4 ∧
        sm.readReg64 .x26 = s.readReg64 .x23 ∧ sm.readReg64 .x27 = s.readReg64 .x12 ∧
        sm.readReg64 .x28 = sp.b1.w5 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = sp.b0.w5 ∧ TraceCalleeSaved sm s) := by
  subst hsp
  states_recv_fetches_range b (Rust.withPanics ext) 15296 4
  states_recv_fetches_range b (Rust.withPanics ext) 18464 160
  dsimp only [tripleRatchetProgAtExt, statesRecvName, noneCap, BitVec.ofNat_eq_ofNat] at hpc hps ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_simp_pre [sendEkSpillsAt, words10At, nhrSpillsStill8984, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [sendEkSpillsAt, words10At, nhrSpillsStill8984, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

def nhrSpillsDone8984 (s : State) (sp : SendEkSpills) (w58 w59 : BitVec 64) : SendEkSpills :=
  { sp with
    b0 := { sp.b0 with w0 := sp.b2.w1 }
    b1 := { sp.b1 with w0 := s.readReg64 .x16, w6 := s.readReg64 .x22, w7 := w59,
                       w8 := s.readReg64 .x2, w9 := s.readReg64 .x4 }
    b2 := { sp.b2 with w1 := s.readReg64 .x6, w2 := sp.b2.w6, w5 := sp.b1.w6,
                       w6 := s.readReg64 .x11, w7 := 8#64, w9 := sp.b0.w5 }
    b3 := { sp.b3 with w0 := w58, w3 := s.readReg64 .x30, w5 := sp.w62,
                       w6 := s.readReg64 .x10, w7 := sp.b5.w7, w8 := s.readReg64 .x12,
                       w9 := sp.b3.w4 }
    b4 := { sp.b4 with w0 := s.readReg64 .x7, w1 := s.readReg64 .x15, w2 := s.readReg64 .x1,
                       w3 := s.readReg64 .x18, w4 := sp.b3.w3, w5 := sp.b4.w6,
                       w6 := sp.b5.w6, w7 := s.readReg64 .x14, w8 := s.readReg64 .x1,
                       w9 := sp.b4.w4 }
    b5 := { sp.b5 with w0 := s.readReg64 .x0, w1 := sp.b2.w3, w4 := s.readReg64 .x9,
                       w6 := sp.w61, w7 := sp.b4.w9, w9 := s.readReg64 .x17 }
    w60 := s.readReg64 .x27, w61 := sp.b2.w5, w62 := s.readReg64 .x20 }

set_option maxHeartbeats 1200000 in
theorem nhr_step_15296_done_8984
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (s : State) (fsp w0 w58 w59 : BitVec 64) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_ne_none : w0 ≠ noneCap)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 15296#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hps : s.pstate = addsPState64 w0 1#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 8984#64) s
      (((fsp + 2320#64) ↦₆₄ w58) ∗ ((fsp + 2328#64) ↦₆₄ w59) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ sendEkSpillsAt fsp sp ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 2320#64) ↦₆₄ w58) ∗ ((fsp + 2328#64) ↦₆₄ w59) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ sendEkSpillsAt fsp (nhrSpillsDone8984 s sp w58 w59) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = sp.b0.w7 ∧ sm.readReg64 .x1 = sp.b4.w0 ∧
        sm.readReg64 .x2 = s.readReg64 .x21 ∧ sm.readReg64 .x3 = s.readReg64 .x17 ∧
        sm.readReg64 .x4 = sp.b2.w6 ∧ sm.readReg64 .x5 = sp.b2.w4 ∧
        sm.readReg64 .x6 = sp.b2.w2 ∧ sm.readReg64 .x7 = sp.b1.w2 ∧
        sm.readReg64 .x8 = 8#64 ∧ sm.readReg64 .x9 = s.readReg64 .x9 ∧
        sm.readReg64 .x10 = sp.b0.w8 ∧ sm.readReg64 .x11 = sp.b0.w9 ∧
        sm.readReg64 .x12 = sp.b0.w4 ∧ sm.readReg64 .x13 = sp.b2.w1 ∧
        sm.readReg64 .x14 = s.readReg64 .x13 ∧ sm.readReg64 .x15 = sp.b0.w1 ∧
        sm.readReg64 .x16 = sp.b5.w9 ∧ sm.readReg64 .x17 = s.readReg64 .x5 ∧
        sm.readReg64 .x18 = sp.b5.w1 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp.b1.w5 ∧ sm.readReg64 .x21 = s.readReg64 .x22 ∧
        sm.readReg64 .x22 = s.readReg64 .x6 ∧ sm.readReg64 .x23 = s.readReg64 .x23 ∧
        sm.readReg64 .x24 = sp.b3.w8 ∧ sm.readReg64 .x25 = sp.b0.w2 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧ sm.readReg64 .x27 = sp.b3.w9 ∧
        sm.readReg64 .x28 = sp.b1.w3 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = sp.b0.w6 ∧ TraceCalleeSaved sm s) := by
  subst hsp
  have hz : (w0 + 1#64 == 0#64) = false := add_one_beq_zero_false_of_ne hw0_ne_none
  have hadrp := fnAddr_adrp_5901c (b := b) (H := Rust.withPanics ext) hb
  states_recv_fetches_range b (Rust.withPanics ext) 15296 72
  states_recv_fetches_range b (Rust.withPanics ext) 18624 268
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hps hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_simp_pre [sendEkSpillsAt, words10At, nhrSpillsDone8984, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_steps
  simp only [sendEkSpillsAt, words10At, nhrSpillsDone8984, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
  wp_done

end CryptoVerification.SpqrV1.States.Recv
