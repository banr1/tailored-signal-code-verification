/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.States2
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.HeapIntro
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: V1 Ratchet Chain & Key Error Cleanup

Error-path symbolic execution and stack/heap cleanup after `spqr::chain_from` (`+2568..+2656`)
and `<Chain>::recv_key` (`+2000..+2056 -> +2632`) on the V1 ratchet path of `spqr::recv`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.DecodeState CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.ChainFrom CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.MessageDeserialize CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.ChainProofs CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592 Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-- Shared error cleanup tail at `+2632 .. +2656` (`0x55074 .. 0x5508c` -> `+1040` when `w26 =
    0`). -/
theorem step_drop_vn_2632 (b : BitVec 64) (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hdealloc : DeallocOkExt b A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 2632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 4416 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  have hdealloc_raw := spqrRecv_dealloc_ok hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 2632 28
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  cases hvn : pre_pb.versionNegotiation with
  | none =>
    dsimp only [optVersionNegotiationPBTailAt]
    wp_focus_pure; intro hw0
    subst hw0
    have hsle : (1#64).sle noneCap = false := rfl
    wp_steps 3
    refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
    refine SepWP.focus_weaken (ownFrame_join_err_2524 s0.sp) (by sep_focus) ?_
    exact step_epilogue b A M ext st msg ret s0 _ _ R post hpost
      (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0_align
      (by simp only [arm64_norm, *]) (by ac_rfl)
  | some vn =>
    refine SepWP.focus_weaken (vnTail_sub4640_some_entails_dealloc A s0.sp w0 w1 vn) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc]
    by_cases hc0 : (w0 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hw0
      wp_steps 3
      refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
      refine SepWP.focus_weaken (ownFrame_join_err_2524 s0.sp) (by sep_focus) ?_
      exact step_epilogue b A M ext st msg ret s0 _ _ R post hpost
        (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0_align
        (by simp only [arm64_norm, *]) (by ac_rfl)
    · have hslt := Drop.cap_ne_zero_slt_one_false hcap_lt hc0
      have hsle := cap_ne_zero_one_sle_true hcap_lt hc0
      have hlt_false := Drop.cap_ne_zero_lt_one_false hcap_lt hc0
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)))
        (by sep_focus) ?_
      wp_steps 6
      wp_call hdealloc_raw ⟨w1, w0.toNat, 1⟩
      have hsp_eq : stackAt s.sp allocHookStack = stackAt (s0.sp - 4992#64) allocHookStack := by rw [hsp]
      refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm)
        (by sep_focus) ?_
      wp_steps 1
      refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp w0 w1) (by sep_focus) ?_
      refine SepWP.focus_weaken (ownFrame_join_err_2524 s0.sp) (by sep_focus) ?_
      exact step_epilogue b A M ext st msg ret s0 _ _ R post hpost
        (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0_align
        (by simp only [arm64_norm, *]) (by ac_rfl)

/-! ## 2. Pure Model Error Lemmas for `chainFrom` and `recvKey` -/

theorem error_isStateDecode_eq_beq (e : Error) :
    e.isStateDecode = (e == .stateDecode) := by
  cases e <;> rfl

theorem recv_v1_after_statesRecv_eq {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes}
    {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v)
    (hep0 : (pre.epoch == 0#64) = false) :
    LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) stateBytes msgBytes = (do
      let msgKeyEpoch : Epoch := pre.epoch - 1#64
      let chain0 ← SpqrApiResult.ofError (chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation)
      let chain1 ←
        match v.key with
        | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
        | none => pure chain0
      let (chain2, msgKey) ← SpqrApiResult.ofChainResult (chain1.recvKey (spqrHkdfWith F) msgKeyEpoch pre.index)
      let newStateBytes := (spqrDeps F K).encodeState {
        inner := some ((spqrDeps F K).statesIntoPb v.state)
        versionNegotiation := none
        chain := some chain2.intoPb
      }
      let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
      .ok { state := newStateBytes, key := outKey }) := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have heq := recv_v1_ratchet_eq (spqrDeps F K) (spqrHkdfWith F) hpre hd
    (pqRatchetStateToPb_inner_some hinner) hmv hmin
  have hmd' : (spqrDeps F K).msgDeserialize pre.epoch pre.remaining = .ok sckaMsg := by
    dsimp [spqrDeps]; rw [hmsg]
  have hfrom' : (spqrDeps F K).statesFromPb pb = .ok st0 :=
    Send.spqrDeps_statesFromPb_of_ok F K hfrom
  have hrecv' : (spqrDeps F K).statesRecv st0 sckaMsg = .ok (v.key, v.state) := by
    dsimp [spqrDeps]; rw [hrecv]
  have hch_eq : (pqRatchetStateToPb pre_pb).chain = pre_pb.chain := rfl
  have hvn_eq : (pqRatchetStateToPb pre_pb).versionNegotiation = pre_pb.versionNegotiation := rfl
  rw [hmd', hfrom'] at heq
  dsimp only [Bind.bind, Except.bind] at heq
  rw [hrecv'] at heq
  dsimp only [Bind.bind, Except.bind] at heq
  rw [hep0, hch_eq, hvn_eq] at heq
  exact heq

theorem spqrV1Recv_v1_chainFrom_err (F : ShaCompress) (K : MlKem)
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)} {e : Error}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v)
    (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .error e) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .error (e == .stateDecode) ∧
      ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  have heq := recv_v1_after_statesRecv_eq hpre hdec hinner hmv hmin hmsg hst0 hrecv hep0
  rw [hcf] at heq
  rw [← error_isStateDecode_eq_beq]
  exact spqrV1Recv_recv_noPanic_of_err heq

theorem spqrV1Recv_v1_recvKey_err (F : ShaCompress) (K : MlKem)
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)} {chain0 chain1 : Chain} {e : Error}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok v)
    (hep0 : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hkey : (match v.key with
      | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
      | none => pure chain0) = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .error (.err e)) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .error (e == .stateDecode) ∧
      ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  have heq := recv_v1_after_statesRecv_eq hpre hdec hinner hmv hmin hmsg hst0 hrecv hep0
  rw [hcf] at heq
  dsimp only [SpqrApiResult.ofError, Bind.bind, Except.bind] at heq
  cases hvk : v.key with
  | none =>
    rw [hvk] at hkey heq
    dsimp only [Pure.pure, Except.pure, Bind.bind, Except.bind] at hkey heq
    injection hkey with h; subst h
    rw [hrk] at heq
    rw [← error_isStateDecode_eq_beq]
    exact spqrV1Recv_recv_noPanic_of_err heq
  | some es =>
    rw [hvk] at hkey heq
    dsimp only [Bind.bind, Except.bind] at hkey heq
    rw [hkey] at heq
    dsimp only [Bind.bind, Except.bind] at heq
    rw [hrk] at heq
    rw [← error_isStateDecode_eq_beq]
    exact spqrV1Recv_recv_noPanic_of_err heq

/-! ## 3. Drop `v.key : Option EpochSecret` at `+2600 .. +2628 -> +2632` (`step_drop_optEpochSecret_2600`) -/

private theorem exists_mem_read64_pair (a w0 w1 : BitVec 64) :
    ∃ m : Memory, m.read64 a = w0 ∧ m.read64 (a + 8#64) = w1 :=
  ⟨(Memory.empty.write64 a w0).write64 (a + 8#64) w1,
    by rw [Memory.read64_write64_base_zero_add8, Memory.read64_write64_same],
    Memory.read64_write64_same _ _ _⟩

private theorem regionHeap_disjoint_of_regionHeap {a : BitVec 64} {n : Nat}
    {m₀ m₁ : Memory} {h₂ : Heap} (hd : (regionHeap a n m₁).Disjoint h₂) :
    (regionHeap a n m₀).Disjoint h₂ := by
  unfold Heap.Disjoint at hd
  refine Heap.Disjoint.of_phys_left (ha := by simp [regionHeap]) (hf := by simp [regionHeap])
    (hm := by simp [regionHeap]) fun x => ?_
  by_cases hx : InRegion a n x
  · have h1 : (regionHeap a n m₁).phys x = some (.rw (m₁.read8 x)) := by simp [regionHeap, hx]
    rcases hd.1 x with h | h | ⟨_, h, _⟩
    · rw [h1] at h; contradiction
    · exact Or.inr (Or.inl h)
    · rw [h1] at h; cases h
  · exact Or.inl (by simp [regionHeap, hx])

private theorem regionHeap_union_unique {a : BitVec 64} {n : Nat}
    {m₀ m' : Memory} {h₂ h_rest : Heap}
    (hd₀ : (regionHeap a n m₀).Disjoint h₂)
    (hd' : (regionHeap a n m').Disjoint h_rest)
    (hu : (regionHeap a n m').union h_rest = (regionHeap a n m₀).union h₂) :
    (∀ x, InRegion a n x → m'.read8 x = m₀.read8 x) ∧ h_rest = h₂ := by
  unfold Heap.Disjoint at hd₀ hd'
  refine ⟨fun x hx => ?_, ?_⟩
  · have hphys := congrFun (congrArg Heap.phys hu) x
    simp only [Heap.union, regionHeap, hx, ↓reduceIte] at hphys
    injection hphys with hcell
    injection hcell
  · apply Heap.ext
    · funext x
      have hphys := congrFun (congrArg Heap.phys hu) x
      by_cases hx : InRegion a n x
      · have h0_some : (regionHeap a n m₀).phys x = some (.rw (m₀.read8 x)) := by simp [regionHeap, hx]
        have h'_some : (regionHeap a n m').phys x = some (.rw (m'.read8 x)) := by simp [regionHeap, hx]
        have h2_none : h₂.phys x = none := by
          rcases hd₀.1 x with h | h | ⟨_, h, _⟩
          · rw [h0_some] at h; contradiction
          · exact h
          · rw [h0_some] at h; cases h
        have hr_none : h_rest.phys x = none := by
          rcases hd'.1 x with h | h | ⟨_, h, _⟩
          · rw [h'_some] at h; contradiction
          · exact h
          · rw [h'_some] at h; cases h
        rw [hr_none, h2_none]
      · simp only [Heap.union, regionHeap, hx, ↓reduceIte] at hphys
        exact hphys
    · funext γ k
      have hauth := congrFun (congrFun (congrArg Heap.auth hu) γ) k
      simpa [Heap.union, regionHeap] using hauth
    · funext γ k
      have hfrag := congrFun (congrFun (congrArg Heap.frag hu) γ) k
      simpa [Heap.union, regionHeap] using hfrag
    · funext x
      have hm := congrFun (congrArg Heap.mapped hu) x
      simpa [Heap.union, regionHeap] using hm

theorem memRegion16_replace_pointsTo64_pair {a kw0 kw1 : BitVec 64} {R : SepProp}
    {α : Type} {Q : α → SepProp} {Ψ : α → Memory → Prop} {S : α → SepProp}
    (hQ : ∀ x, IsBlock (Q x) a 16 (Ψ x))
    (hent : ((a ↦₆₄ kw0) ∗ ((a + 8#64) ↦₆₄ kw1)) ∗ R ⊢ ∃∗ x : α, Q x ∗ S x) :
    memRegion a 16 ∗ R ⊢
      ∃∗ x : α,
        ⌜∃ m : Memory, m.read64 a = kw0 ∧ m.read64 (a + 8#64) = kw1 ∧ Ψ x m⌝ ∗
        memRegion a 16 ∗ S x := by
  have hblk0 : IsBlock ((a ↦₆₄ kw0) ∗ ((a + 8#64) ↦₆₄ kw1)) a 16
      (fun m => m.read64 a = kw0 ∧ m.read64 (a + 8#64) = kw1) :=
    (IsBlock.pointsTo64 a kw0).sepConj (IsBlock.pointsTo64 (a + 8#64) kw1) rfl (by decide)
  obtain ⟨m₀, hm₀⟩ := exists_mem_read64_pair a kw0 kw1
  simpa only [and_assoc] using IsBlock.replace_in_entails hblk0 ⟨m₀, hm₀⟩ hQ hent

theorem vecU8_entails_pair_memRegion16_dealloc (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8))
    (w3 : BitVec 64) :
    vecU8 A a bs ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      ∃∗ p : BitVec 64 × BitVec 64,
        ((a ↦₆₄ p.1) ∗ ((a + 8#64) ↦₆₄ p.2)) ∗
        (⌜p.1.toNat < 2 ^ 63⌝ ∗ memRegion (a + 16#64) 16 ∗ vecCapPtrDealloc A p.1 p.2) := by
  change (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, vecU8At A a cap ptr bs) ∗ ((a + 24#64) ↦₆₄ w3) ⊢ _
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun cap => ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun ptr => ?_
  have hdealloc := vecU8At_entails_capPtr_dealloc_lt A a cap ptr bs
  have hw3 := ProofLib.pointsTo64_entails_memRegion (a + 24#64) w3
  refine Entails.trans (sepConj_mono hdealloc hw3) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hcap_lt => ?_
  have h16 : memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 8 = memRegion (a + 16#64) 16 := by
    rw [← ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8)
          (b' := a + 24#64) rfl (by bv_omega) (by decide)]
  refine Entails.sepExists_right (cap, ptr) ?_
  dsimp only
  refine Entails.trans
    (Entails.of_eq (show
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗ vecCapPtrDealloc A cap ptr) ∗
        memRegion (a + 24#64) 8 =
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr)) ∗
        ((memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 8) ∗ vecCapPtrDealloc A cap ptr) by ac_rfl)) ?_
  refine sepConj_mono_right ?_
  rw [h16]
  exact Entails.pure_right hcap_lt (Entails.refl _)

theorem optEpochSecret_none_entails_of_hfold (A : RustAlloc) (a kw0 kw1 kw2 kw3 : BitVec 64)
    (P_key : SepProp)
    (hfold : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        States.Recv.optEpochSecretAt A dst none) :
    memRegion a 16 ∗ (((a + 16#64) ↦₆₄ kw2) ∗ ((a + 24#64) ↦₆₄ kw3) ∗ P_key) ⊢
      ⌜kw0 = noneCap⌝ ∗ memRegion a 32 := by
  have hQ : ∀ _ : Unit, IsBlock ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 8) a 16
      (fun m => m.read64 a = noneCap ∧ True) :=
    fun _ => (IsBlock.pointsTo64 a noneCap).sepConj (IsBlock.memRegion (a + 8#64) 8) rfl (by decide)
  have hent : ((a ↦₆₄ kw0) ∗ ((a + 8#64) ↦₆₄ kw1)) ∗
      (((a + 16#64) ↦₆₄ kw2) ∗ ((a + 24#64) ↦₆₄ kw3) ∗ P_key) ⊢
      ∃∗ _ : Unit, ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 8) ∗ memRegion (a + 16#64) 16 := by
    refine Entails.trans
      (Entails.of_eq (by simp only [sepConj_assoc]))
      (Entails.trans (hfold a) ?_)
    dsimp only [States.Recv.optEpochSecretAt]
    rw [show (24 : Nat) = 8 + 16 by rfl,
        memRegion_split (a + 8#64) 8 16 (by decide),
        show (a + 8#64) + 8#64 = a + 16#64 by bv_omega,
        ← sepConj_assoc]
    exact Entails.sepExists_right () (Entails.refl _)
  refine Entails.trans (memRegion16_replace_pointsTo64_pair hQ hent) ?_
  refine Entails.sepExists_elim fun _ => ?_
  refine Entails.pure_left fun ⟨m, hm0, _, hm_none, _⟩ => ?_
  refine Entails.pure_right (hm0.symm.trans hm_none) ?_
  rw [show (32 : Nat) = 16 + 16 by rfl, memRegion_split a 16 16 (by decide)]
  exact Entails.refl _

theorem optEpochSecret_some_entails_of_hfold (A : RustAlloc) (a kw0 kw1 kw2 kw3 : BitVec 64)
    (P_key : SepProp) (sec : EpochSecret)
    (hfold : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        States.Recv.optEpochSecretAt A dst (some sec)) :
    memRegion a 16 ∗ (((a + 16#64) ↦₆₄ kw2) ∗ ((a + 24#64) ↦₆₄ kw3) ∗ P_key) ⊢
      ⌜kw0.toNat < 2 ^ 63⌝ ∗ memRegion a 32 ∗ vecCapPtrDealloc A kw0 kw1 := by
  have hQ : ∀ p : BitVec 64 × BitVec 64,
      IsBlock ((a ↦₆₄ p.1) ∗ ((a + 8#64) ↦₆₄ p.2)) a 16
        (fun m => m.read64 a = p.1 ∧ m.read64 (a + 8#64) = p.2) :=
    fun p => (IsBlock.pointsTo64 a p.1).sepConj (IsBlock.pointsTo64 (a + 8#64) p.2) rfl (by decide)
  have hent : ((a ↦₆₄ kw0) ∗ ((a + 8#64) ↦₆₄ kw1)) ∗
      (((a + 16#64) ↦₆₄ kw2) ∗ ((a + 24#64) ↦₆₄ kw3) ∗ P_key) ⊢
      ∃∗ p : BitVec 64 × BitVec 64,
        ((a ↦₆₄ p.1) ∗ ((a + 8#64) ↦₆₄ p.2)) ∗
        (⌜p.1.toNat < 2 ^ 63⌝ ∗ memRegion (a + 16#64) 16 ∗ vecCapPtrDealloc A p.1 p.2) := by
    refine Entails.trans
      (Entails.of_eq (by simp only [sepConj_assoc]))
      (Entails.trans (hfold a) ?_)
    dsimp only [States.Recv.optEpochSecretAt, States.RecvCt2Chunk.epochSecretAt]
    exact vecU8_entails_pair_memRegion16_dealloc A a sec.secret sec.epoch
  refine Entails.trans (memRegion16_replace_pointsTo64_pair hQ hent) ?_
  refine Entails.sepExists_elim fun ⟨cap, ptr⟩ => ?_
  refine Entails.pure_left fun ⟨m, hm0, hm1, hmc, hmp⟩ => ?_
  have hcap : cap = kw0 := hmc.symm.trans hm0
  have hptr : ptr = kw1 := hmp.symm.trans hm1
  subst hcap hptr
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hcap_lt => ?_
  refine Entails.pure_right hcap_lt ?_
  rw [← sepConj_assoc, show (32 : Nat) = 16 + 16 by rfl, memRegion_split a 16 16 (by decide)]
  exact Entails.refl _

theorem memRegion_4416_join_464_32_3920 (sp0 : BitVec 64) :
    memRegion (sp0 - 4512#64) 464 ∗
      memRegion (sp0 - 4048#64) 32 ∗
      memRegion (sp0 - 4016#64) 3920 ⊢
    memRegion (sp0 - 4512#64) 4416 := by
  rw [show (4416 : Nat) = 464 + (32 + 3920) by decide,
      memRegion_split (sp0 - 4512#64) 464 (32 + 3920) (by decide),
      show (sp0 - 4512#64) + 464#64 = sp0 - 4048#64 by bv_omega,
      memRegion_split (sp0 - 4048#64) 32 3920 (by decide),
      show (sp0 - 4048#64) + 32#64 = sp0 - 4016#64 by bv_omega]
  exact Entails.refl _

theorem cap_add_one_ult_sub_one_false {cap : BitVec 64}
    (hcap_lt : cap.toNat < 2 ^ 63) (hc0 : ¬(cap == 0#64) = true) :
    (cap + 1#64).ult (cap - 1#64) = false := by
  have hc_ne : cap ≠ 0#64 := by rwa [beq_iff_eq] at hc0
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  bv_omega

/-- Drop `v.key : Option EpochSecret` at `+2600 .. +2628` (`0x55054 .. 0x55070 -> +2632`): sets
    `w26 = w28` (`0`), checks `sub x8, x24, #1; cmn x8, #2; b.cs +2632`, calls
    `__rust_dealloc(x25, x24, 1)` when `v.key = some sec` and `kw0 ≠ 0`, and finishes via
    `step_drop_vn_2632` (`+2632`). -/
theorem step_drop_optEpochSecret_2600 (b : BitVec 64) (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hdealloc : DeallocOkExt b A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (key : Option EpochSecret) (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        States.Recv.optEpochSecretAt A dst key)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 2600#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1)
    (hx28 : s.readReg64 .x28 = 0#64)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 464 ∗
      memRegion (s0.sp - 4048#64) 16 ∗
      (((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key) ∗
      memRegion (s0.sp - 4016#64) 3920 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  have hdealloc_raw := spqrRecv_dealloc_ok hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 2600 32
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  cases key with
  | none =>
    have hnone := optEpochSecret_none_entails_of_hfold A (s0.sp - 4048#64) kw0 kw1 kw2 kw3 P_key hfold_key
    rw [bv_sub_add_lit s0.sp 4048 16, bv_sub_add_lit s0.sp 4048 24] at hnone
    simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hnone
    refine SepWP.focus_weaken hnone (by sep_focus) ?_
    wp_focus_pure; intro hkw0
    subst hkw0
    refine SepWP.focus_weaken (memRegion_4416_join_464_32_3920 s0.sp) (by sep_focus) ?_
    wp_steps 4
    exact step_drop_vn_2632 b A M ext hdealloc st msg ret pre_pb w0 w1 s0 _ _ R post hpost hs0_align
      (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl)
  | some sec =>
    have hsome := optEpochSecret_some_entails_of_hfold A (s0.sp - 4048#64) kw0 kw1 kw2 kw3 P_key sec hfold_key
    rw [bv_sub_add_lit s0.sp 4048 16, bv_sub_add_lit s0.sp 4048 24] at hsome
    simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hsome
    refine SepWP.focus_weaken hsome (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    refine SepWP.focus_weaken (memRegion_4416_join_464_32_3920 s0.sp) (by sep_focus) ?_
    dsimp only [vecCapPtrDealloc]
    by_cases hc0 : (kw0 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hkw0 : kw0 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hkw0
      wp_steps 4
      exact step_drop_vn_2632 b A M ext hdealloc st msg ret pre_pb w0 w1 s0 _ _ R post hpost hs0_align
        (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl)
    · have hult_false := cap_add_one_ult_sub_one_false hcap_lt hc0
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)))
        (by sep_focus) ?_
      wp_steps 8
      wp_call hdealloc_raw ⟨kw1, kw0.toNat, 1⟩
      have hsp_eq : stackAt s.sp allocHookStack = stackAt (s0.sp - 4992#64) allocHookStack := by rw [hsp]
      refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm)
        (by sep_focus) ?_
      exact step_drop_vn_2632 b A M ext hdealloc st msg ret pre_pb w0 w1 s0 _ _ R post hpost hs0_align
        (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl)

/-! ## 4. Post-`chain_from` Error Cleanup at `+2568 .. +2600 -> +2632` (`step_chainFrom_err_2568`) -/

theorem memRegion_464_16_of_msg (sp0 : BitVec 64) (sckaMsg : Message spqrPolyApi) :
    memRegion (sp0 - 4512#64) 224 ∗
      memRegion (sp0 - 4288#64) 176 ∗
      MessageSerialize.messageAt spqrPolyApi (sp0 - 4112#64) sckaMsg ∗
      memRegion (sp0 - 4064#64) 32 ⊢
    memRegion (sp0 - 4512#64) 464 ∗
      memRegion (sp0 - 4048#64) 16 := by
  have hmsg := messageAt_entails_memRegion_48 (sp0 - 4112#64) sckaMsg
  rw [ProofLib.memRegion_split' (b := sp0 - 4064#64) (n := 16) (k := 16) (b' := sp0 - 4048#64) rfl (by bv_omega) (by decide),
      show (464 : Nat) = 224 + (176 + (48 + 16)) by decide,
      ProofLib.memRegion_split' (b := sp0 - 4512#64) (n := 224) (k := 240) (b' := sp0 - 4288#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4288#64) (n := 176) (k := 64) (b' := sp0 - 4112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4112#64) (n := 48) (k := 16) (b' := sp0 - 4064#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans
    (Entails.of_eq (show
      memRegion (sp0 - 4512#64) 224 ∗
        memRegion (sp0 - 4288#64) 176 ∗
        MessageSerialize.messageAt spqrPolyApi (sp0 - 4112#64) sckaMsg ∗
        (memRegion (sp0 - 4064#64) 16 ∗ memRegion (sp0 - 4048#64) 16) =
      (memRegion (sp0 - 4512#64) 224 ∗
        memRegion (sp0 - 4288#64) 176 ∗
        MessageSerialize.messageAt spqrPolyApi (sp0 - 4112#64) sckaMsg ∗
        memRegion (sp0 - 4064#64) 16) ∗
        memRegion (sp0 - 4048#64) 16 by ac_rfl)) ?_
  exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmsg)))

theorem memRegion_3920_join_chainFrom_err (sp0 err_w1 err_w2 err_w3 : BitVec 64) :
    memRegion (sp0 - 4016#64) 928 ∗
      memRegion (sp0 - 3088#64) 32 ∗
      ((sp0 - 3056#64) ↦₆₄ Top.ChainFromVersionNegotiation.noneCap) ∗
      ((sp0 - 3048#64) ↦₆₄ err_w1) ∗
      ((sp0 - 3040#64) ↦₆₄ err_w2) ∗
      ((sp0 - 3032#64) ↦₆₄ err_w3) ∗
      memRegion (sp0 - 3024#64) 56 ∗
      memRegion (sp0 - 2968#64) 872 ∗
      ((sp0 - 2096#64) ↦₆₄ err_w1) ∗
      ((sp0 - 2088#64) ↦₆₄ err_w2) ∗
      ((sp0 - 2080#64) ↦₆₄ err_w3) ∗
      memRegion (sp0 - 2072#64) 1976 ⊢
    memRegion (sp0 - 4016#64) 3920 := by
  have h32 := words4_to_memRegion_32 (sp0 - 3056#64) Top.ChainFromVersionNegotiation.noneCap err_w1 err_w2 err_w3
  rw [bv_sub_add_lit sp0 3056 8, bv_sub_add_lit sp0 3056 16, bv_sub_add_lit sp0 3056 24] at h32
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h32
  have h24 := words3_to_memRegion_24 (sp0 - 2096#64) err_w1 err_w2 err_w3
  rw [bv_sub_add_lit sp0 2096 8, bv_sub_add_lit sp0 2096 16] at h24
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h24
  rw [show (3920 : Nat) = 928 + (32 + (32 + (56 + (872 + (24 + 1976))))) by decide,
      ProofLib.memRegion_split' (b := sp0 - 4016#64) (n := 928) (k := 2992) (b' := sp0 - 3088#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 3088#64) (n := 32) (k := 2960) (b' := sp0 - 3056#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 3056#64) (n := 32) (k := 2928) (b' := sp0 - 3024#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 3024#64) (n := 56) (k := 2872) (b' := sp0 - 2968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2968#64) (n := 872) (k := 2000) (b' := sp0 - 2096#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2096#64) (n := 24) (k := 1976) (b' := sp0 - 2072#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans
    (Entails.of_eq (show
      memRegion (sp0 - 4016#64) 928 ∗
        memRegion (sp0 - 3088#64) 32 ∗
        ((sp0 - 3056#64) ↦₆₄ Top.ChainFromVersionNegotiation.noneCap) ∗
        ((sp0 - 3048#64) ↦₆₄ err_w1) ∗
        ((sp0 - 3040#64) ↦₆₄ err_w2) ∗
        ((sp0 - 3032#64) ↦₆₄ err_w3) ∗
        memRegion (sp0 - 3024#64) 56 ∗
        memRegion (sp0 - 2968#64) 872 ∗
        ((sp0 - 2096#64) ↦₆₄ err_w1) ∗
        ((sp0 - 2088#64) ↦₆₄ err_w2) ∗
        ((sp0 - 2080#64) ↦₆₄ err_w3) ∗
        memRegion (sp0 - 2072#64) 1976 =
      memRegion (sp0 - 4016#64) 928 ∗
        memRegion (sp0 - 3088#64) 32 ∗
        (((sp0 - 3056#64) ↦₆₄ Top.ChainFromVersionNegotiation.noneCap) ∗
          ((sp0 - 3048#64) ↦₆₄ err_w1) ∗
          ((sp0 - 3040#64) ↦₆₄ err_w2) ∗
          ((sp0 - 3032#64) ↦₆₄ err_w3)) ∗
        memRegion (sp0 - 3024#64) 56 ∗
        memRegion (sp0 - 2968#64) 872 ∗
        (((sp0 - 2096#64) ↦₆₄ err_w1) ∗
          ((sp0 - 2088#64) ↦₆₄ err_w2) ∗
          ((sp0 - 2080#64) ↦₆₄ err_w3)) ∗
        memRegion (sp0 - 2072#64) 1976 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono h32 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h24)))))

theorem memRegion_2872_split_chainFrom_err (sp0 : BitVec 64) :
    memRegion (sp0 - 2968#64) 2872 ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
        memRegion (sp0 - 2968#64) 872 ∗
        ((sp0 - 2096#64) ↦₆₄ d0) ∗
        ((sp0 - 2088#64) ↦₆₄ d1) ∗
        ((sp0 - 2080#64) ↦₆₄ d2) ∗
        memRegion (sp0 - 2072#64) 1976 := by
  rw [show (2872 : Nat) = 872 + (24 + 1976) by decide,
      ProofLib.memRegion_split' (b := sp0 - 2968#64) (n := 872) (k := 2000) (b' := sp0 - 2096#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2096#64) (n := 24) (k := 1976) (b' := sp0 - 2072#64) rfl (by bv_omega) (by decide),
      memRegion_24_words3 (sp0 - 2096#64),
      bv_sub_add_lit sp0 2096 8,
      bv_sub_add_lit sp0 2096 16]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro d2
  apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d0
  refine Entails.sepExists_right d0 (Entails.sepExists_right d1 (Entails.sepExists_right d2 ?_))
  exact Entails.of_eq (by ac_rfl)

theorem SepWP.drop_left {prog : Program} {target_pc : BitVec 64} {s : State} {Q P : SepProp}
    {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s P post) :
    SepWP prog target_pc s (Q ∗ P) post := by
  unfold SepWP at h ⊢
  intro R hsat
  rw [sepConj_assoc] at hsat
  exact h R (Satisfies.of_sep_right hsat)

theorem SepWP.drop_ro {prog : Program} {target_pc : BitVec 64} {s : State} (Q : SepProp) {P P' : SepProp}
    {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s P' post)
    (heq : P = Q ∗ P') :
    SepWP prog target_pc s P post := by
  subst heq
  exact SepWP.drop_left h

theorem chainErrorAt_unpack_words4 (out : BitVec 64) (err : Error) :
    Top.ChainFromVersionNegotiation.chainErrorAt out err =
      ∃∗ q0 : BitVec 128, ∃∗ w3 : BitVec 64,
        ⌜BitVec.truncate 8 q0 = Top.ChainFromVersionNegotiation.spqrErrorTag err⌝ ∗
        (out ↦₆₄ Top.ChainFromVersionNegotiation.noneCap) ∗
        ((out + 8#64) ↦₆₄ q0.extractLsb' 0 64) ∗
        ((out + 16#64) ↦₆₄ q0.extractLsb' 64 64) ∗
        ((out + 24#64) ↦₆₄ w3) ∗
        memRegion (out + 32#64) 56 := by
  unfold Top.ChainFromVersionNegotiation.chainErrorAt pointsTo128
  have h16 : out + 8#64 + 8#64 = out + 16#64 := by bv_omega
  rw [h16]
  simp only [sepConj_assoc]

theorem rodata_chunkedStatesLocal2JumpTableAt {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ Drop.chunkedStatesLocal2JumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_bytes% "0e001a000426341e5508")) (n := 10) (bs := Drop.chunkedStatesLocal2JumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem step_chainFrom_err_2568 (b : BitVec 64) (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        States.Recv.optEpochSecretAt A dst v.key)
    (e : Error) (q0_err : BitVec 128) (w3_err : BitVec 64)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode))
    (htag_q0 : BitVec.truncate 8 q0_err = Top.ChainFromVersionNegotiation.spqrErrorTag e)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 2568#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1)
    (hx28 : s.readReg64 .x28 = 0#64)
    (hP : P =
      Drop.chunkedStatesLocal2JumpTableAt b ∗
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 176 ∗
      MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗
      ((s0.sp - 4032#64) ↦₆₄ kw2) ∗
      ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
      P_key ∗
      chunkedStatesAt A (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ Top.ChainFromVersionNegotiation.noneCap) ∗
      ((s0.sp - 3048#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
      ((s0.sp - 3040#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
      ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
      memRegion (s0.sp - 3024#64) 56 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      ((s0.sp - 2096#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
      ((s0.sp - 2088#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
      ((s0.sp - 2080#64) ↦₆₄ w3_err) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  have hdrop_states := spqrRecv_dropStates_ok (F := F) hdealloc
  simp only [Drop.dropChunkedStatesLocal2Spec] at hdrop_states
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hdrop_states hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 2568 32
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r3 r2 r1 r0
  have hret_fold :
      ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((ret + 8#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
        ((ret + 16#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((ret + 24#64) ↦₆₄ w3_err) ∗
        memRegion (ret + 32#64) 16) ⊢
      recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [herr]
    exact recv_err_q0_foldX A ret (q0_err.extractLsb' 64 64) w3_err q0_err e htag_q0
  wp_steps 8
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStackPoly64 (by decide)))
    (by sep_focus) ?_
  wp_call hdrop_states ⟨s0.sp - 4016#64, v.state⟩
  have hsp_eq : stackAt s.sp dropStackPoly64 = stackAt (s0.sp - 4992#64) dropStackPoly64 := by rw [hsp]
  refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStackPoly64 (by decide)).symm)
    (by sep_focus) ?_
  refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
  refine SepWP.focus_weaken (memRegion_464_16_of_msg s0.sp sckaMsg) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (memRegion_3920_join_chainFrom_err s0.sp (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err)
    (by sep_focus) ?_
  refine SepWP.drop_ro (Drop.chunkedStatesLocal2JumpTableAt b)
    (step_drop_optEpochSecret_2600 b A (spqrV1Recv F K) ext hdealloc st msg ret pre_pb w0 w1
      v.key kw0 kw1 kw2 kw3 P_key hfold_key s0 _ _ R post hpost hs0_align
      (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) rfl)
    (by ac_rfl)

theorem step_post_chainFrom_err_1860 (b : BitVec 64) (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp)
    (hfold_key : ∀ dst : BitVec 64,
      (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
        States.Recv.optEpochSecretAt A dst v.key)
    (e : Error)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 1860#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = kw0)
    (hx25 : s.readReg64 .x25 = kw1)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = 0#64)
    (hP : P =
      Drop.chunkedStatesLocal2JumpTableAt b ∗
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 176 ∗
      MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗
      ((s0.sp - 4032#64) ↦₆₄ kw2) ∗
      ((s0.sp - 4024#64) ↦₆₄ kw3) ∗
      P_key ∗
      chunkedStatesAt A (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      Top.ChainFromVersionNegotiation.chainErrorAt (s0.sp - 3056#64) e ∗
      memRegion (s0.sp - 2968#64) 2872 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  have hnone1 : (Top.ChainFromVersionNegotiation.noneCap + 1#64 == 0#64) = true := rfl
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 1860 28
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  rw [chainErrorAt_unpack_words4 (s0.sp - 3056#64) e,
      bv_sub_add_lit s0.sp 3056 8,
      bv_sub_add_lit s0.sp 3056 16,
      bv_sub_add_lit s0.sp 3056 24,
      bv_sub_add_lit s0.sp 3056 32]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i q0_err w3_err
  wp_focus_pure; intro htag_q0
  refine SepWP.focus_weaken (memRegion_2872_split_chainFrom_err s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i d0 d1 d2
  wp_steps 7
  exact step_chainFrom_err_2568 b A F K ext hb hdealloc st msg ret pre_pb w0 w1 sckaMsg v
    kw0 kw1 kw2 kw3 P_key hfold_key e q0_err w3_err herr htag_q0 s0 _ _ R post hpost hs0_align
    (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by ac_rfl)

/-! ## 5. Post-`recv_key` Error Cleanup at `+2000 .. +2056 -> +2632` (`step_recvKey_err_2000`) -/

theorem recvKeyErrAt_entails_code_memRegion23_v1 (out : BitVec 64) (e : Error) :
    recvKeyErrAt out e ⊢
      (out ↦₆₄ 1#64) ∗
      ((out + 8#64) ↦₈ Top.ChainFromVersionNegotiation.spqrErrorTag e) ∗
      memRegion (out + 9#64) 23 := by
  unfold recvKeyErrAt; split
  · refine sepConj_mono_right (sepConj_mono_right ?_)
    rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 7) (k := 16) (b' := out + 0x10#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := out + 0x10#64) (n := 8) (k := 8) (b' := out + 0x18#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  · refine sepConj_mono_right (sepConj_mono_right ?_)
    rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 3) (k := 20) (b' := out + 0x0c#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := out + 0x0c#64) (n := 4) (k := 16) (b' := out + 0x10#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := out + 0x10#64) (n := 4) (k := 12) (b' := out + 0x14#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _)))
  · refine sepConj_mono_right (sepConj_mono_right ?_)
    rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 3) (k := 20) (b' := out + 0x0c#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := out + 0x0c#64) (n := 4) (k := 16) (b' := out + 0x10#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _))
  · refine sepConj_mono_right (sepConj_mono_right ?_)
    rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 3) (k := 20) (b' := out + 0x0c#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := out + 0x0c#64) (n := 4) (k := 16) (b' := out + 0x10#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _))
  · rw [← sepConj_emp ⌜False⌝]; exact Entails.pure_left False.elim

theorem recvKeyErrAt_sub3056_expose_words4 (sp0 : BitVec 64) (e : Error) :
    recvKeyErrAt (sp0 - 3056#64) e ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ⌜∀ r : BitVec 64,
          ((r + 8#64) ↦₆₄ w1) ⊢
            ((r + 8#64) ↦₈ Top.ChainFromVersionNegotiation.spqrErrorTag e) ∗
            memRegion (r + 9#64) 7⌝ ∗
        ((sp0 - 3056#64) ↦₆₄ 1#64) ∗
        ((sp0 - 3048#64) ↦₆₄ w1) ∗
        ((sp0 - 3040#64) ↦₆₄ w2) ∗
        ((sp0 - 3032#64) ↦₆₄ w3) := by
  refine Entails.trans (recvKeyErrAt_entails_code_memRegion23_v1 (sp0 - 3056#64) e) ?_
  refine Entails.trans
    (sepConj_mono_right (err_payload_expose (sp0 - 3056#64)
      (Top.ChainFromVersionNegotiation.spqrErrorTag e) 23 (by decide) (by decide))) ?_
  rw [bv_sub_add_lit sp0 3056 8,
      bv_sub_add_lit sp0 3056 16,
      bv_sub_add_lit sp0 3056 24,
      bv_sub_add_lit sp0 3056 32]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, memRegion_zero, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w3
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hw1
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_))
  exact Entails.pure_right hw1 (Entails.of_eq (by ac_rfl))

theorem memRegion_4416_join_recvKey_err (sp0 w1 w2 w3 : BitVec 64)
    (sckaMsg : Message spqrPolyApi) :
    memRegion (sp0 - 4512#64) 224 ∗
      memRegion (sp0 - 4288#64) 176 ∗
      MessageSerialize.messageAt spqrPolyApi (sp0 - 4112#64) sckaMsg ∗
      memRegion (sp0 - 4064#64) 48 ∗
      memRegion (sp0 - 4016#64) 928 ∗
      memRegion (sp0 - 3088#64) 32 ∗
      ((sp0 - 3056#64) ↦₆₄ 1#64) ∗
      ((sp0 - 3048#64) ↦₆₄ w1) ∗
      ((sp0 - 3040#64) ↦₆₄ w2) ∗
      ((sp0 - 3032#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 3024#64) 2792 ∗
      memRegion (sp0 - 232#64) 88 ∗
      memRegion (sp0 - 144#64) 48 ⊢
    memRegion (sp0 - 4512#64) 4416 := by
  have hmsg := messageAt_entails_memRegion_48 (sp0 - 4112#64) sckaMsg
  have h32 := words4_to_memRegion_32 (sp0 - 3056#64) 1#64 w1 w2 w3
  rw [bv_sub_add_lit sp0 3056 8, bv_sub_add_lit sp0 3056 16, bv_sub_add_lit sp0 3056 24] at h32
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h32
  rw [show (4416 : Nat) = 224 + (176 + (48 + (48 + (928 + (32 + (32 + (2792 + (88 + 48)))))))) by decide,
      ProofLib.memRegion_split' (b := sp0 - 4512#64) (n := 224) (k := 4192) (b' := sp0 - 4288#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4288#64) (n := 176) (k := 4016) (b' := sp0 - 4112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4112#64) (n := 48) (k := 3968) (b' := sp0 - 4064#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4064#64) (n := 48) (k := 3920) (b' := sp0 - 4016#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4016#64) (n := 928) (k := 2992) (b' := sp0 - 3088#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 3088#64) (n := 32) (k := 2960) (b' := sp0 - 3056#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 3056#64) (n := 32) (k := 2928) (b' := sp0 - 3024#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 3024#64) (n := 2792) (k := 136) (b' := sp0 - 232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 232#64) (n := 88) (k := 48) (b' := sp0 - 144#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans
    (Entails.of_eq (show
      memRegion (sp0 - 4512#64) 224 ∗
        memRegion (sp0 - 4288#64) 176 ∗
        MessageSerialize.messageAt spqrPolyApi (sp0 - 4112#64) sckaMsg ∗
        memRegion (sp0 - 4064#64) 48 ∗
        memRegion (sp0 - 4016#64) 928 ∗
        memRegion (sp0 - 3088#64) 32 ∗
        ((sp0 - 3056#64) ↦₆₄ 1#64) ∗
        ((sp0 - 3048#64) ↦₆₄ w1) ∗
        ((sp0 - 3040#64) ↦₆₄ w2) ∗
        ((sp0 - 3032#64) ↦₆₄ w3) ∗
        memRegion (sp0 - 3024#64) 2792 ∗
        memRegion (sp0 - 232#64) 88 ∗
        memRegion (sp0 - 144#64) 48 =
      memRegion (sp0 - 4512#64) 224 ∗
        memRegion (sp0 - 4288#64) 176 ∗
        MessageSerialize.messageAt spqrPolyApi (sp0 - 4112#64) sckaMsg ∗
        memRegion (sp0 - 4064#64) 48 ∗
        memRegion (sp0 - 4016#64) 928 ∗
        memRegion (sp0 - 3088#64) 32 ∗
        (((sp0 - 3056#64) ↦₆₄ 1#64) ∗
          ((sp0 - 3048#64) ↦₆₄ w1) ∗
          ((sp0 - 3040#64) ↦₆₄ w2) ∗
          ((sp0 - 3032#64) ↦₆₄ w3)) ∗
        memRegion (sp0 - 3024#64) 2792 ∗
        memRegion (sp0 - 232#64) 88 ∗
        memRegion (sp0 - 144#64) 48 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hmsg
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h32))))))

theorem step_recvKey_err_2028 (b : BitVec 64) (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (g1 : ChainProofs.ChainGhost) (chain1 : Chain)
    (err : Error) (w1_err w2_err w3_err : BitVec 64)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (err == .stateDecode))
    (hw1_err : ∀ r : BitVec 64,
      ((r + 8#64) ↦₆₄ w1_err) ⊢
        ((r + 8#64) ↦₈ Top.ChainFromVersionNegotiation.spqrErrorTag err) ∗
        memRegion (r + 9#64) 7)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 2028#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = w1_err)
    (hx22 : s.readReg64 .x22 = w2_err)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = w3_err)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      Drop.chunkedStatesLocal2JumpTableAt b ∗
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 176 ∗
      MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 48 ∗
      chunkedStatesAt A (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ 1#64) ∗
      ((s0.sp - 3048#64) ↦₆₄ w1_err) ∗
      ((s0.sp - 3040#64) ↦₆₄ w2_err) ∗
      ((s0.sp - 3032#64) ↦₆₄ w3_err) ∗
      memRegion (s0.sp - 3024#64) 2792 ∗
      ChainProofs.chainAt A (s0.sp - 232#64) g1 chain1 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  have hdrop_chain := spqrRecv_dropChain_ok hdealloc
  simp only [Drop.dropSpqrChainSpec] at hdrop_chain
  have hdrop_states := spqrRecv_dropStates_ok (F := F) hdealloc
  simp only [Drop.dropChunkedStatesLocal2Spec] at hdrop_states
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have hfp : s.readReg64 .fp = s0.sp - 96#64 := hx29
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hdrop_chain hdrop_states hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 2028 32
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r3 r2 r1 r0
  have hret_fold :
      ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((ret + 8#64) ↦₆₄ w1_err) ∗
        ((ret + 16#64) ↦₆₄ w2_err) ∗
        ((ret + 24#64) ↦₆₄ w3_err) ∗
        memRegion (ret + 32#64) 16) ⊢
      recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [herr]
    exact recv_err_words_foldX A ret w1_err w2_err w3_err
      (Top.ChainFromVersionNegotiation.spqrErrorTag err) (err == .stateDecode)
      (Iff.of_eq (spqrErrorTag_eq_zero_iff err)) hw1_err
  wp_steps 5
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack80 (by decide)))
    (by sep_focus) ?_
  wp_call hdrop_chain ⟨s0.sp - 232#64, g1, chain1⟩
  have hsp_eq1 : stackAt s.sp dropStack80 = stackAt (s0.sp - 4992#64) dropStack80 := by rw [hsp]
  refine SepWP.focus_weaken (Entails.of_eq hsp_eq1) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack80 (by decide)).symm)
    (by sep_focus) ?_
  wp_steps 2
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStackPoly64 (by decide)))
    (by sep_focus) ?_
  wp_call hdrop_states ⟨s0.sp - 4016#64, v.state⟩
  conv in (stackAt _ dropStackPoly64) =>
    arg 1
    simp only [hsp, *]
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStackPoly64 (by decide)).symm)
    (by sep_focus) ?_
  wp_steps 1
  refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
  refine SepWP.focus_weaken
    (memRegion_4416_join_recvKey_err s0.sp w1_err w2_err w3_err sckaMsg)
    (by sep_focus) ?_
  refine SepWP.drop_ro (Drop.chunkedStatesLocal2JumpTableAt b)
    (step_drop_vn_2632 b A (spqrV1Recv F K) ext hdealloc st msg ret pre_pb w0 w1 s0 _ _ R post hpost hs0_align
      (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) rfl)
    (by ac_rfl)

theorem step_recvKey_err_2000 (b : BitVec 64) (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (g1 : ChainProofs.ChainGhost) (chain1 : Chain)
    (err : Error)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (err == .stateDecode))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 2000#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = w0)
    (hx28 : s.readReg64 .x28 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      Drop.chunkedStatesLocal2JumpTableAt b ∗
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 80 ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 176 ∗
      MessageSerialize.messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 48 ∗
      chunkedStatesAt A (s0.sp - 4016#64) v.state ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      recvKeyErrAt (s0.sp - 3056#64) err ∗
      memRegion (s0.sp - 3024#64) 2792 ∗
      ChainProofs.chainAt A (s0.sp - 232#64) g1 chain1 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 2000 28
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  refine SepWP.focus_weaken (recvKeyErrAt_sub3056_expose_words4 s0.sp err) (by sep_focus) ?_
  wp_pull_exists; rename_i w1_err w2_err w3_err
  wp_focus_pure; intro hw1_err
  wp_steps 7
  exact step_recvKey_err_2028 b A F K ext hb hdealloc st msg ret pre_pb w0 w1 sckaMsg v
    g1 chain1 err w1_err w2_err w3_err herr hw1_err s0 _ _ R post hpost hs0_align
    (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Recv
