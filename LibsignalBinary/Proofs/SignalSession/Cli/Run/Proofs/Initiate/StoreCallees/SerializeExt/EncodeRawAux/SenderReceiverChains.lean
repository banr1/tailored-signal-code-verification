/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.BasePart2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.PrologueVersionLocalIdentity
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::encode_raw` Segment 2: Tag 6 (`sender_chain`) and Tag 7 (`receiver_chains`)
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf

def chainRest (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
    ((a + 8#64) ↦₆₄ gc.1.srk.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
    vecU8Buf A gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
    vecGhostAt A gc.1.priv (a + 24#64) ∗
    vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
      (gc.1.keys.zip gc.2.messageKeys) ∗
    optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_open_cap (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    protoChainAt A gc a = (a ↦₆₄ gc.1.srk.cap) ∗ chainRest A gc a := by
  unfold protoChainAt chainRest vecGhostAt
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader
  ac_rfl

theorem chainAt_close_cap (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64)
    (R : SepProp) :
    (a ↦₆₄ gc.1.srk.cap) ∗ chainRest A gc a ∗ R = protoChainAt A gc a ∗ R := by
  rw [chainAt_open_cap A gc a, sepConj_assoc]

theorem sepWPp_extract_chainAt_cap {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {gc : ChainGhost × ReceiverChain} {a : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfocus : P = protoChainAt A gc a ∗ F := by sep_focus)
    (h : gc.1.srk.cap.toNat < 2 ^ 63 → SepWPpX img prog ret s P Q Qp) :
    SepWPpX img prog ret s P Q Qp := by
  have hfocus' : P = vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
      (⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
        vecGhostAt A gc.1.priv (a + 24#64) ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
          (gc.1.keys.zip gc.2.messageKeys) ∗
        optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64) ∗ F) := by
    rw [hfocus]
    unfold protoChainAt vecGhostAt
    ac_rfl
  exact sepWPp_extract_vecU8At_bounds (hfocus := hfocus') (fun _ hcap _ => h hcap)

theorem cmn1_beq_zero_false {cap : BitVec 64} (hcap : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 : cap = 0xffffffffffffffff#64 := by
    calc cap = (cap + 1#64) - 1#64 := by bv_lin
      _ = 0#64 - 1#64 := by rw [heq]
      _ = 0xffffffffffffffff#64 := by rfl
  rw [h1] at hcap
  revert hcap; decide

theorem cap_beq_noneCap_false {cap : BitVec 64} (hcap : cap.toNat < 2 ^ 63) :
    (cap == 0xffffffffffffffff#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  rw [heq] at hcap
  revert hcap; decide

def vecChainsRest (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) : SepProp :=
  ⌜gcs.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    A.live ptr (cap.toNat * 104) 8 ∗
    memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104)

theorem vecAt_chains_open (A : RustAlloc) (ss cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (hne : gcs ≠ []) (hle : gcs.length ≤ cap.toNat) :
    vecAt A 104 8 (chainAt A) (ss + 72#64) cap ptr gcs =
      ((ss + 72#64) ↦₆₄ cap) ∗ ((ss + 80#64) ↦₆₄ ptr) ∗
      ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
      arrayAt (chainAt A) 104 ptr gcs ∗ vecChainsRest A cap ptr gcs := by
  have hne_cap : cap ≠ 0 := by
    intro h; subst h
    have hpos := List.length_pos_of_ne_nil hne
    change gcs.length ≤ 0 at hle
    omega
  unfold vecAt vecHeader vecBuf vecChainsRest
  simp only [hne_cap, ↓reduceIte,
    show (ss + 72#64) + 8#64 = ss + 80#64 by bv_lin,
    show (ss + 72#64) + 16#64 = ss + 88#64 by bv_lin]
  ac_rfl

theorem vecAt_chains_close (A : RustAlloc) (ss cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (hne : gcs ≠ []) (hle : gcs.length ≤ cap.toNat) (R : SepProp) :
    ((ss + 72#64) ↦₆₄ cap) ∗ ((ss + 80#64) ↦₆₄ ptr) ∗
      ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
      arrayAt (chainAt A) 104 ptr gcs ∗ vecChainsRest A cap ptr gcs ∗ R =
      vecAt A 104 8 (chainAt A) (ss + 72#64) cap ptr gcs ∗ R := by
  rw [vecAt_chains_open A ss cap ptr gcs hne hle]
  simp only [sepConj_assoc]

theorem vecAt_chains_nil (A : RustAlloc) (ss cap ptr : BitVec 64) :
    vecAt A 104 8 (chainAt A) (ss + 72#64) cap ptr [] =
      ((ss + 72#64) ↦₆₄ cap) ∗ ((ss + 80#64) ↦₆₄ ptr) ∗
      ((ss + 88#64) ↦₆₄ 0#64) ∗
      vecBuf A 104 8 (chainAt A) cap ptr [] := by
  unfold vecAt vecHeader
  simp only [List.length_nil,
    show (ss + 72#64) + 8#64 = ss + 80#64 by bv_lin,
    show (ss + 72#64) + 16#64 = ss + 88#64 by bv_lin, sepConj_assoc]

theorem sepWPp_extract_vecAt_chains_bounds {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {a cap ptr : BitVec 64} {gcs : List (ChainGhost × ReceiverChain)}
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hfocus : P = vecAt A 104 8 (chainAt A) a cap ptr gcs ∗ F := by sep_focus)
    (h : gcs.length ≤ cap.toNat → cap.toNat * 104 < 2 ^ 63 → SepWPpX img prog ret s P Q Qp) :
    SepWPpX img prog ret s P Q Qp := by
  intro hinv R hm hL
  have hfocus' : P ∗ R = ⌜gcs.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (vecHeader a cap ptr (BitVec.ofNat 64 gcs.length) ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 104) 8 ∗ arrayAt (chainAt A) 104 ptr gcs ∗
           memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104)) ∗ F ∗ R) := by
    rw [hfocus]; unfold vecAt vecBuf; ac_rfl
  have hm' := hm
  rw [hfocus', satisfies_pure_sepConj] at hm'
  exact h hm'.1.1 hm'.1.2.1 hinv R hm hL

theorem bv_len_mul_104 (n : Nat) :
    BitVec.ofNat 64 n * 104#64 = BitVec.ofNat 64 (n * 104) := by
  simp [BitVec.ofNat_mul]

theorem bv_cons_len_mul_104_sub (gc : ChainGhost × ReceiverChain)
    (rest : List (ChainGhost × ReceiverChain)) :
    BitVec.ofNat 64 ((gc :: rest).length * 104) - 104#64 =
      BitVec.ofNat 64 (rest.length * 104) := by
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul, BitVec.ofNat_add]
  bv_lin

theorem bv_mul_104_beq_zero_false {rest : List (ChainGhost × ReceiverChain)}
    (hne : rest ≠ []) (hlt : rest.length * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 (rest.length * 104) == 0#64) = false := by
  have hpos : 0 < rest.length := List.length_pos_of_ne_nil hne
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  change rest.length * 104 = 0 at h1
  omega

theorem bv_cons_len_mul_104_beq_104_false (gc : ChainGhost × ReceiverChain)
    {rest : List (ChainGhost × ReceiverChain)}
    (hne : rest ≠ []) (hlt : (gc :: rest).length * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 ((gc :: rest).length * 104) == 104#64) = false := by
  have hpos : 0 < rest.length := List.length_pos_of_ne_nil hne
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  change (gc :: rest).length * 104 = 104 at h1
  simp only [List.length_cons] at h1
  omega

theorem bv_cons_len_mul_104_bne_104_true (gc : ChainGhost × ReceiverChain)
    {rest : List (ChainGhost × ReceiverChain)}
    (hne : rest ≠ []) (hlt : (gc :: rest).length * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 ((gc :: rest).length * 104) != 104#64) = true := by
  simp only [bne, bv_cons_len_mul_104_beq_104_false gc hne hlt, Bool.not_false]

theorem ofNat64_chains_len_beq_zero_false {gcs : List (ChainGhost × ReceiverChain)}
    (hne : gcs ≠ []) (hlt : gcs.length < 2 ^ 63) :
    (BitVec.ofNat 64 gcs.length == 0#64) = false := by
  have hpos : 0 < gcs.length := List.length_pos_of_ne_nil hne
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  change gcs.length = 0 at h1
  omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local irreducible] vecRest vecU8Buf vecSrcRest vecCopyDone
attribute [local irreducible] chainRest vecChainsRest vecBuf

@[local arm64_norm]
theorem bv_add_neg80_2 (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 :=
  (BitVec.sub_eq_add_neg x 80#64).symm

set_option maxHeartbeats 400000

/-! ## 1. Tag 6 (`sender_chain`, `+0x1cc → +0x1e8`, offsets `460..488`) -/

/-- Tag 6 (`+0x1cc..+0x1e8`): encodes `sender_chain` (`optSenderChainAt` at `ss + 0x90`) via
`encode::<Chain>` with tag `6` when `Some`, or skips when `None` (`noneCap`). -/
theorem step_encraw_tag6 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEC : OkAtX img ext encodeChainName (encodeChainSpecX A))
    (ss v sp0 cap ptr : BitVec 64)
    (senderG : Option SenderChainGhost) (sender : Option SenderChain)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + (encSenderFieldMem senderG sender).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 460#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (optSenderChainAt A (ss + 0x90#64) senderG sender ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 488#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((optSenderChainAt A (ss + 0x90#64) senderG sender ∗
          vecU8At A v cap' ptr' (bs ++ encSenderFieldMem senderG sender) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallEC := @encraw_call_protoEncodeChain img A ext hEC
  encraw_fetches_range img.base (Rust.withPanics ext) 460 488
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  cases senderG with
  | none =>
    cases sender with
    | none =>
      simp only [optSenderChainAt, noneCap, sepConj_assoc]
      apply SepWPpX.of_sepWP (mid := entry + bv% (488))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hPost :
          ((ss + 144#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ memRegion (ss + 144#64 + 8#64) 96 ∗
          vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack ∗ F =
          (optSenderChainAt A (ss + 0x90#64) none none ∗
            vecU8At A v cap ptr (bs ++ encSenderFieldMem none none) ∗
            A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by
        simp only [optSenderChainAt, noneCap, encSenderFieldMem, List.append_nil, sepConj_assoc]
      rw [hPost]
      exact hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    | some sc =>
      simp only [optSenderChainAt, sepConj_assoc]
      exact SepWPpX.pure_elim fun h => False.elim h
  | some g =>
    cases sender with
    | none =>
      simp only [optSenderChainAt, sepConj_assoc]
      exact SepWPpX.pure_elim fun h => False.elim h
    | some sc =>
      rw [optSenderChainAt_some_eq_chainAt_er A (ss + 0x90#64) g sc]
      simp only [sepConj_assoc]
      refine SepWPpX.pure_elim fun hpriv => ?_
      refine sepWPp_extract_chainAt_cap (A := A) (gc := (senderGhostAsChain g, senderAsChain sc))
        (a := ss + 0x90#64) (h := fun hcap => ?_)
      have hcmn1 := cmn1_beq_zero_false hcap
      have hcmn2 := cap_beq_noneCap_false hcap
      rw [chainAt_open_cap A (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64)]
      simp only [sepConj_assoc]
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [chainAt_close_cap A (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64)]
      refine hCallEC 6 sp0 (ss + 0x90#64) v cap ptr (entry + bv% (488))
        (senderGhostAsChain g, senderAsChain sc) bs (Or.inl rfl) hlen_lt
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
        have hx19m : sm.readReg64 .x19 = v := by
          have := hcsm.1; simp only [arm64_norm, *] at this; exact this
        have hx20m : sm.readReg64 .x20 = ss := by
          have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        have hRestore :
            (protoChainAt A (senderGhostAsChain g, senderAsChain sc) (ss + 0x90#64) ∗
              vecU8At A v cap' ptr' (bs ++ lenField 6 (encChainMem (senderGhostAsChain g, senderAsChain sc))) ∗
              A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F =
            (optSenderChainAt A (ss + 0x90#64) (some g) (some sc) ∗
              vecU8At A v cap' ptr' (bs ++ encSenderFieldMem (some g) (some sc)) ∗
              A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by
          rw [optSenderChainAt_some_eq_chainAt_er A (ss + 0x90#64) g sc, eq_true hpriv,
              pure_true, emp_sepConj]
          rfl
        rw [hRestore]
        exact hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'

/-! ## 2. Tag 7 (`receiver_chains` loop, `+0x1e8 → +0x218`, offsets `488..536`) -/

theorem mul_104_cons_lt {α : Type} {x : α} {xs : List α} (h : (x :: xs).length * 104 < 2 ^ 63) :
    xs.length * 104 < 2 ^ 63 := by
  simp only [List.length_cons] at h; omega

theorem len_head_lt_of_cons {bs : List (BitVec 8)} {gc : ChainGhost × ReceiverChain}
    {rest : List (ChainGhost × ReceiverChain)}
    (h : bs.length + (((gc :: rest).map fun gc => lenField 7 (encChainMem gc)).flatten).length < 2 ^ 32) :
    bs.length + (lenField 7 (encChainMem gc)).length < 2 ^ 32 := by
  simp only [List.map_cons, List.flatten_cons, List.length_append] at h; omega

theorem len_rest_lt_of_cons {bs : List (BitVec 8)} {gc : ChainGhost × ReceiverChain}
    {rest : List (ChainGhost × ReceiverChain)}
    (h : bs.length + (((gc :: rest).map fun gc => lenField 7 (encChainMem gc)).flatten).length < 2 ^ 32) :
    (bs ++ lenField 7 (encChainMem gc)).length +
      ((rest.map fun gc => lenField 7 (encChainMem gc)).flatten).length < 2 ^ 32 := by
  simp only [List.map_cons, List.flatten_cons, List.length_append] at h ⊢; omega

/-- Inner loop of Tag 7 (`+0x1fc..+0x218`, `508..536`): encodes each `gc ∈ gcs` at `curPtr`
(stride `104`) with tag `7` into `v`. -/
theorem step_encraw_tag7_loop {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEC : OkAtX img ext encodeChainName (encodeChainSpecX A))
    (gcs : List (ChainGhost × ReceiverChain))
    (hne : gcs ≠ [])
    (ss v sp0 curPtr cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hmul_lt : gcs.length * 104 < 2 ^ 63)
    (hlen_lt : bs.length + ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = curPtr)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (gcs.length * 104))
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (arrayAt (chainAt A) 104 curPtr gcs ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 536#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((arrayAt (chainAt A) 104 curPtr gcs ∗
          vecU8At A v cap' ptr' (bs ++ (gcs.map fun gc => lenField 7 (encChainMem gc)).flatten) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  induction gcs generalizing curPtr cap ptr bs s P F with
  | nil => exact False.elim (hne rfl)
  | cons gc rest ih =>
    have hCallEC := @encraw_call_encodeChain img A ext hEC
    encraw_fetches_range img.base (Rust.withPanics ext) 508 536
    generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
    examples_hide_fetches
    rw [hP]
    simp only [arrayAt, sepConj_assoc]
    have hlen_head := len_head_lt_of_cons hlen_lt
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallEC 7 sp0 curPtr v cap ptr (entry + bv% (524)) gc bs (Or.inr rfl) hlen_head
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hcs1
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 ((gc :: rest).length * 104) := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = curPtr + 104#64 := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      cases rest with
      | nil =>
        simp only [List.length_singleton, Nat.one_mul] at hx21_1
        change s1.readReg64 .x21 = 104#64 at hx21_1
        apply SepWPpX.of_sepWP (mid := entry + bv% (536))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPpX.weaken_pre ?_ (hnext _ cap1 ptr1
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        simp only [arrayAt, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          List.append_nil, emp_sepConj, sepConj_emp, sepConj_assoc]
        exact entails_of_sep_focus (by sep_focus)
      | cons gc2 rest' =>
        have hne_rest : (gc2 :: rest') ≠ [] := List.cons_ne_nil _ _
        have hsub := bv_cons_len_mul_104_sub gc (gc2 :: rest')
        have hmul_rest := mul_104_cons_lt hmul_lt
        have hbeq0 := bv_mul_104_beq_zero_false hne_rest hmul_rest
        have hbeq104 := bv_cons_len_mul_104_beq_104_false gc hne_rest hmul_lt
        have hbne104 := bv_cons_len_mul_104_bne_104_true gc hne_rest hmul_lt
        apply SepWPpX.of_sepWP (mid := entry + bv% (508))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have hlen_rest := len_rest_lt_of_cons hlen_lt
        refine ih (F := chainAt A gc curPtr ∗ F) hne_rest (curPtr + 104#64) cap1 ptr1
          (bs ++ lenField 7 (encChainMem gc)) hmul_rest hlen_rest
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
          (by sep_focus) ?_
        intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
        refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
        simp only [arrayAt, List.map_cons, List.flatten_cons, List.append_assoc, sepConj_assoc]
        exact entails_of_sep_focus (by sep_focus)

/-- Tag 7 (`+0x1e8..+0x218`, `488..536`): encodes all receiver chains in
`vecAt A 104 8 (chainAt A) (ss + 0x48#64) cCap cPtr gcs` with tag `7` into `v`. -/
theorem step_encraw_tag7 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEC : OkAtX img ext encodeChainName (encodeChainSpecX A))
    (ss v sp0 cCap cPtr cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + ((gcs.map fun gc => lenField 7 (encChainMem gc)).flatten).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecAt A 104 8 (chainAt A) (ss + 0x48#64) cCap cPtr gcs ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 536#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecAt A 104 8 (chainAt A) (ss + 0x48#64) cCap cPtr gcs ∗
          vecU8At A v cap' ptr' (bs ++ (gcs.map fun gc => lenField 7 (encChainMem gc)).flatten) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hLoop := @step_encraw_tag7_loop img A ext hEC
  encraw_fetches_range img.base (Rust.withPanics ext) 488 508
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPp_extract_vecAt_chains_bounds (A := A) (a := ss + 0x48#64)
    (cap := cCap) (ptr := cPtr) (gcs := gcs) (h := fun hle hcap_mul => ?_)
  by_cases hgcs : gcs = []
  · subst hgcs
    rw [vecAt_chains_nil A ss cCap cPtr]
    simp only [sepConj_assoc]
    apply SepWPpX.of_sepWP (mid := entry + bv% (536))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [show
        ((ss + 72#64) ↦₆₄ cCap) ∗ ((ss + 80#64) ↦₆₄ cPtr) ∗ ((ss + 88#64) ↦₆₄ 0#64) ∗
        vecBuf A 104 8 (chainAt A) cCap cPtr [] ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
        stackAt (sp0 - 80#64) encodeRawSubStack ∗ F =
        (vecAt A 104 8 (chainAt A) (ss + 0x48#64) cCap cPtr [] ∗ vecU8At A v cap ptr bs ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F by
      rw [vecAt_chains_nil A ss cCap cPtr]; simp only [sepConj_assoc]]
    simpa only [List.map_nil, List.flatten_nil, List.append_nil] using
      hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hbeq0 := ofNat64_chains_len_beq_zero_false hgcs (by omega)
    have hmul := bv_len_mul_104 gcs.length
    rw [vecAt_chains_open A ss cCap cPtr gcs hgcs hle]
    simp only [sepConj_assoc]
    apply SepWPpX.of_sepWP (mid := entry + bv% (508))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hLoop gcs hgcs ss v sp0 cPtr cap ptr bs (by omega) hlen_lt
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
      (by sep_focus) ?_
    intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
    refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
    rw [vecAt_chains_open A ss cCap cPtr gcs hgcs hle]
    exact entails_of_sep_focus (by sep_focus)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
