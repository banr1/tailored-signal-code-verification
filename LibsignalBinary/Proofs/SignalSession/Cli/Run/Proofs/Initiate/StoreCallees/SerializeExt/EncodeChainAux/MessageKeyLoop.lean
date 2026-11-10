/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeChainAux.MessageKeyLoopBody
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `encode::<Chain, Vec<u8>>`: `message_keys` Loop (`+0x258 → +0x670`) and Epilogue
-/

set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf
  sepWPp_extract_vecU8Buf_le vecU8Buf_eq_open_one vecU8Buf_snoc_eq
open CryptoVerification.E2E.Record
open EncodeVarintNorm
open scoped BigOperators

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ### List & pointer arithmetic helpers for `message_keys` loop -/

theorem zip_map_snd_eq_encChain {α β γ : Type*} (xs : List α) (ys : List β) (f : β → γ)
    (h : xs.length = ys.length) :
    (xs.zip ys).map (fun p => f p.2) = ys.map f := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp [List.zip_cons_cons, ih ys h]

theorem zip_length_eq_right {α β : Type*} (xs : List α) (ys : List β)
    (h : xs.length = ys.length) :
    (xs.zip ys).length = ys.length := by
  simp [List.length_zip, h]

theorem mk_endPtr_step (cur : BitVec 64) (n : Nat) :
    cur + BitVec.ofNat 64 ((n + 1) * 104) =
      (cur + 104#64) + BitVec.ofNat 64 (n * 104) := by
  have h1 : BitVec.ofNat 64 ((n + 1) * 104) = 104#64 + BitVec.ofNat 64 (n * 104) := by
    rw [Nat.add_mul, Nat.one_mul, BitVec.ofNat_add]
    bv_omega
  rw [h1, ← BitVec.add_assoc]

theorem bv_add_eq_self_iff {a b : BitVec 64} :
    (a == a + b) = (b == 0#64) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor <;> intro h <;> bv_omega

theorem bv_nat_beq_zero_false {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem mk_endPtr_ne_of_pos (cur : BitVec 64) (n : Nat) (hpos : 0 < n) (hlt : n * 104 < 2 ^ 32) :
    ((cur + 104#64) == (cur + 104#64) + BitVec.ofNat 64 (n * 104)) = false := by
  rw [bv_add_eq_self_iff]
  exact bv_nat_beq_zero_false (by omega) hlt

theorem bv_madd_104 (ptr : BitVec 64) (n : Nat) :
    ptr + BitVec.ofNat 64 n * 104#64 = ptr + BitVec.ofNat 64 (n * 104) := by
  have h : BitVec.ofNat 64 n * 104#64 = BitVec.ofNat 64 (n * 104) := by
    rw [← BitVec.ofNat_mul]
  rw [h]

def vecMkRest (A : RustAlloc) (cap ptr : BitVec 64)
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) : SepProp :=
  ⌜mks.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    A.live ptr (cap.toNat * 104) 8 ∗
    memRegion (ptr + BitVec.ofNat 64 (mks.length * 104)) ((cap.toNat - mks.length) * 104)

theorem sepWPp_extract_vecBuf_mk_le {img : Obj.Image} {A : RustAlloc} {cap ptr : BitVec 64}
    {mks : List (MessageKeyGhost × MessageKeyGenerator)}
    {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = vecBuf A 104 8 (messageKeyAt A) cap ptr mks ∗ F)
    (h : mks.length ≤ cap.toNat → SepWPpX img prog ret s P Q Qp) :
    SepWPpX img prog ret s P Q Qp := by
  intro hinv R hm hL
  have hhm : s.mem ⊨ ⌜mks.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((if cap = 0 then emp
        else A.live ptr (cap.toNat * 104) 8 ∗ arrayAt (messageKeyAt A) 104 ptr mks ∗
          memRegion (ptr + BitVec.ofNat 64 (mks.length * 104)) ((cap.toNat - mks.length) * 104)) ∗
        F ∗ R) := by
    convert hm using 1
    rw [hP]
    unfold vecBuf
    ac_rfl
  rw [satisfies_pure_sepConj] at hhm
  exact h hhm.1.1 hinv R hm hL

theorem vecBuf_mk_eq_open (A : RustAlloc) (cap ptr : BitVec 64)
    (mks : List (MessageKeyGhost × MessageKeyGenerator))
    (hpos : 0 < mks.length) (hle : mks.length ≤ cap.toNat) :
    vecBuf A 104 8 (messageKeyAt A) cap ptr mks =
      arrayAt (messageKeyAt A) 104 ptr mks ∗ vecMkRest A cap ptr mks := by
  have hne : cap ≠ 0 := by
    intro h0; have : cap.toNat = 0 := by simp [h0]
    omega
  unfold vecBuf vecMkRest
  simp only [hne, ↓reduceIte]
  ac_rfl

/-- Rest of `chainAt A gc a` excluding the `Vec<MessageKey>` field at `a + 48#64`. -/
def chainMkUnusedAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
    vecGhostAt A gc.1.srk a ∗ vecGhostAt A gc.1.priv (a + 24#64) ∗
    optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_mk_cells (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    protoChainAt A gc a =
      ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
      ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length) ∗
      vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
      chainMkUnusedAt A gc a := by
  unfold protoChainAt chainMkUnusedAt vecAt vecHeader
  have h56 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have h64 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [h56, h64]
  ac_rfl

theorem sepWPp_extract_chain_mk_bounds {img : Obj.Image} {A : RustAlloc}
    {gc : ChainGhost × ReceiverChain} {a : BitVec 64}
    {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = protoChainAt A gc a ∗ F)
    (h : gc.2.messageKeys.length ≤ maxMessageKeys →
         gc.1.keys.length = gc.2.messageKeys.length →
         SepWPpX img prog ret s P Q Qp) :
    SepWPpX img prog ret s P Q Qp := by
  intro hinv R hm hL
  have hhm : s.mem ⊨
      ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
      ((vecGhostAt A gc.1.srk a ∗ vecGhostAt A gc.1.priv (a + 24#64) ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
          (gc.1.keys.zip gc.2.messageKeys) ∗
        optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) ∗ F ∗ R) := by
    convert hm using 1
    rw [hP]
    unfold protoChainAt
    ac_rfl
  rw [satisfies_pure_sepConj] at hhm
  exact h hhm.1.2.1 hhm.1.2.2 hinv R hm hL

/-! ### Loop back-edge helpers (`+668 → +1648` or `+680`, offsets `668..680`) -/

theorem step_encChain_mk_next_eq (img : Obj.Image) (ext : String → Option (State → State))
    (v cur endPtr sp0 : BitVec 64)
    (heq : ((cur + 104#64) == endPtr) = true)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 668#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 1648#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm P Q Qp) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q Qp := by
  encChain_fetches_range img.base (Rust.withPanics ext) 668 680
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  apply SepWPpX.of_sepWP (mid := entry + bv% (1648))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_mk_next_ne (img : Obj.Image) (ext : String → Option (State → State))
    (v cur endPtr sp0 : BitVec 64)
    (hne : ((cur + 104#64) == endPtr) = false)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 668#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 680#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v (cur + 104#64) endPtr →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm P Q Qp) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q Qp := by
  encChain_fetches_range img.base (Rust.withPanics ext) 668 680
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  apply SepWPpX.of_sepWP (mid := entry + bv% (680))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *]⟩

/-! ### Inductive `message_keys` Loop (`+680 → +1648`): `step_encChain_mk_loop` -/

theorem mk_len_tl_lt {α : Type} (x : α) (xs : List α)
    (h : (x :: xs).length * 104 < 2 ^ 32) :
    xs.length * 104 < 2 ^ 32 := by
  simp only [List.length_cons] at h
  omega

theorem mk_bound_head (curBs : List (BitVec 8))
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator))
    (hbound : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32) :
    curBs.length + (lenField 4 (encMessageKey gk.2)).length < 2 ^ 32 := by
  simp only [List.map_cons, List.flatten_cons, List.length_append] at hbound
  omega

theorem mk_bound_tail (curBs : List (BitVec 8))
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator))
    (hbound : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32) :
    (curBs ++ lenField 4 (encMessageKey gk.2)).length +
      ((tl.map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32 := by
  simp only [List.map_cons, List.flatten_cons, List.length_append] at hbound ⊢
  omega

theorem step_encChain_mk_loop (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hMK : OkAtX img ext msgKeyLenName (msgKeyLenSpec A))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (tl : List (MessageKeyGhost × MessageKeyGenerator))
    (v cur endPtr curCap curPtr sp0 : BitVec 64)
    (curBs : List (BitVec 8))
    (hend : endPtr = cur + BitVec.ofNat 64 ((gk :: tl).length * 104))
    (hlen_mk : (gk :: tl).length * 104 < 2 ^ 32)
    (hbound : curBs.length +
      (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 680#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      arrayAt (messageKeyAt A) 104 cur (gk :: tl) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (capOut ptrOut : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 1648#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v capOut ptrOut
          (curBs ++ ((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten) ∗
          arrayAt (messageKeyAt A) 104 cur (gk :: tl) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  induction tl generalizing gk cur curCap curPtr curBs s P F with
  | nil =>
    have hbound1 := mk_bound_head curBs gk [] hbound
    have heq_end : ((cur + 104#64) == endPtr) = true := by
      rw [hend]; simp
    refine step_encChain_mk_elem img A ext hA hMK hEV hDR
      v cur endPtr curCap curPtr sp0 gk curBs hbound1
      (x := x) (F := F) hpc hrun hsp halign htr hregs
      (by rw [hP]; simp only [arrayAt, sepConj_emp]) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hregs1
    refine step_encChain_mk_next_eq img ext v cur endPtr sp0 heq_end
      hpc1 hrun1 hsp1 htr1 hregs1 ?_
    intro sm hpcm hrunm hspm htrm
    refine sepWPp_congr_pre ?_ (hnext sm cap1 ptr1 hpcm hrunm hspm htrm)
    simp only [arrayAt, sepConj_emp, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil]
  | cons gk2 tl2 ih =>
    have hbound1 := mk_bound_head curBs gk (gk2 :: tl2) hbound
    have hlen_tl := mk_len_tl_lt gk (gk2 :: tl2) hlen_mk
    have hbound_tl := mk_bound_tail curBs gk (gk2 :: tl2) hbound
    refine step_encChain_mk_elem img A ext hA hMK hEV hDR
      v cur endPtr curCap curPtr sp0 gk curBs hbound1
      (x := x) (F := arrayAt (messageKeyAt A) 104 (cur + 104#64) (gk2 :: tl2) ∗ F)
      hpc hrun hsp halign htr hregs
      (by rw [hP]; simp only [arrayAt]; ac_rfl) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hregs1
    have hend_step : endPtr = (cur + 104#64) + BitVec.ofNat 64 ((gk2 :: tl2).length * 104) := by
      rw [hend]
      exact mk_endPtr_step cur (gk2 :: tl2).length
    have hne_end : ((cur + 104#64) == endPtr) = false := by
      rw [hend_step]
      exact mk_endPtr_ne_of_pos cur (gk2 :: tl2).length (by simp) hlen_tl
    refine step_encChain_mk_next_ne img ext v cur endPtr sp0 hne_end
      hpc1 hrun1 hsp1 htr1 hregs1 ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hregs2
    refine ih gk2 (cur + 104#64) cap1 ptr1 (curBs ++ lenField 4 (encMessageKey gk.2))
      hend_step hlen_tl hbound_tl
      (F := messageKeyAt A gk cur ∗ F)
      hpc2 hrun2 hsp2 htr2 hregs2
      (by ac_rfl) ?_
    intro sm capOut ptrOut hpcm hrunm hspm htrm
    refine sepWPp_congr_pre ?_ (hnext sm capOut ptrOut hpcm hrunm hspm htrm)
    simp only [arrayAt, List.map_cons, List.flatten_cons, List.append_assoc]
    ac_rfl

/-! ### Segment 4 (`+600 → +1648`): `step_encChain_seg4` -/

theorem step_encChain_seg4_empty (img : Obj.Image) (ext : String → Option (State → State))
    (a sp0 : BitVec 64)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 600#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((a + 64#64) ↦₆₄ 0#64) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 1648#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm (((a + 64#64) ↦₆₄ 0#64) ∗ F) Q Qp) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q Qp := by
  encChain_fetches_range img.base (Rust.withPanics ext) 600 608
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  apply SepWPpX.of_sepWP (mid := entry + bv% (1648))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_seg4_init (img : Obj.Image) (ext : String → Option (State → State))
    (v a mkPtr sp0 : BitVec 64) (n : Nat)
    (hpos : 0 < n) (hlt : n < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 600#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (((a + 56#64) ↦₆₄ mkPtr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 n)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 680#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v mkPtr (mkPtr + BitVec.ofNat 64 (n * 104)) →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((((a + 56#64) ↦₆₄ mkPtr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 n)) ∗ F) Q Qp) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q Qp := by
  encChain_fetches_range img.base (Rust.withPanics ext) 600 640
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  have hnz := bv_nat_beq_zero_false hpos hlt
  have hmadd := bv_madd_104 mkPtr n
  apply SepWPpX.of_sepWP (mid := entry + bv% (680))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *]⟩

theorem step_encChain_seg4 (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) (hA : AllocContractsX img A ext)
    (hMK : OkAtX img ext msgKeyLenName (msgKeyLenSpec A))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v a curCap curPtr sp0 : BitVec 64) (gc : ChainGhost × ReceiverChain)
    (curBs : List (BitVec 8))
    (hbound : curBs.length +
      ((gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 600#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      protoChainAt A gc a ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (capOut ptrOut : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 1648#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v capOut ptrOut
          (curBs ++ (gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten) ∗
          protoChainAt A gc a ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_chain_mk_bounds (A := A) (gc := gc) (a := a)
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hmk_max hkeys_len => ?_
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length :=
    zip_length_eq_right gc.1.keys gc.2.messageKeys hkeys_len
  have hzip_map :
      (gc.1.keys.zip gc.2.messageKeys).map (fun p => lenField 4 (encMessageKey p.2)) =
      gc.2.messageKeys.map (fun mk => lenField 4 (encMessageKey mk)) :=
    zip_map_snd_eq_encChain gc.1.keys gc.2.messageKeys (fun mk => lenField 4 (encMessageKey mk)) hkeys_len
  rw [chainAt_eq_mk_cells A gc a]
  rcases hmks : gc.1.keys.zip gc.2.messageKeys with _ | ⟨gk, tl⟩
  · have hmks_len : gc.2.messageKeys.length = 0 := by
      rw [← hzip_len, hmks]; rfl
    have hmks_nil : gc.2.messageKeys = [] := List.eq_nil_of_length_eq_zero hmks_len
    refine step_encChain_seg4_empty img ext a sp0
      (F := vecU8At A v curCap curPtr curBs ∗
        ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
        ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
        vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr [] ∗
        chainMkUnusedAt A gc a ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      hpc hrun hsp htr hx20 (by simp only [List.length_nil]; ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm
    refine sepWPp_congr_pre ?_ (hnext sm curCap curPtr hpcm hrunm hspm htrm)
    rw [chainAt_eq_mk_cells A gc a, hmks, hmks_nil]
    simp only [List.length_nil, List.map_nil, List.flatten_nil, List.append_nil]
    ac_rfl
  · rw [hmks] at hzip_len hzip_map
    have hlen_le : (gk :: tl).length ≤ 2000 := by
      have : maxMessageKeys = 2000 := rfl
      omega
    have hlen_pos : 0 < (gk :: tl).length := by simp
    have hlen_lt : (gk :: tl).length < 2 ^ 32 := by omega
    have hlen_mk : (gk :: tl).length * 104 < 2 ^ 32 := by omega
    refine sepWPp_extract_vecBuf_mk_le (A := A) (cap := gc.1.mkCap) (ptr := gc.1.mkPtr)
      (mks := gk :: tl)
      (F := vecU8At A v curCap curPtr curBs ∗
        ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
        ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (gk :: tl).length) ∗
        chainMkUnusedAt A gc a ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by ac_rfl) fun hle_cap => ?_
    rw [vecBuf_mk_eq_open A gc.1.mkCap gc.1.mkPtr (gk :: tl) hlen_pos hle_cap]
    refine step_encChain_seg4_init img ext v a gc.1.mkPtr sp0 (gk :: tl).length
      hlen_pos hlen_lt
      (F := vecU8At A v curCap curPtr curBs ∗
        ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
        arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gk :: tl) ∗
        vecMkRest A gc.1.mkCap gc.1.mkPtr (gk :: tl) ∗
        chainMkUnusedAt A gc a ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      hpc hrun hsp htr hx19 hx20 (by ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hregs1
    have hbound_mks :
        curBs.length +
          (((gk :: tl).map (fun p => lenField 4 (encMessageKey p.2))).flatten).length < 2 ^ 32 := by
      rw [hzip_map]
      exact hbound
    refine step_encChain_mk_loop img A ext hA hMK hEV hDR
      gk tl v gc.1.mkPtr (gc.1.mkPtr + BitVec.ofNat 64 ((gk :: tl).length * 104))
      curCap curPtr sp0 curBs rfl hlen_mk hbound_mks
      (x := x)
      (F := ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
        ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (gk :: tl).length) ∗
        vecMkRest A gc.1.mkCap gc.1.mkPtr (gk :: tl) ∗
        chainMkUnusedAt A gc a ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hregs1 (by ac_rfl) ?_
    intro sm capOut ptrOut hpcm hrunm hspm htrm
    refine sepWPp_congr_pre ?_ (hnext sm capOut ptrOut hpcm hrunm hspm htrm)
    rw [chainAt_eq_mk_cells A gc a, hmks,
        vecBuf_mk_eq_open A gc.1.mkCap gc.1.mkPtr (gk :: tl) hlen_pos hle_cap,
        hzip_map]
    ac_rfl

/-! ### Epilogue (`+1648 → ret`, offsets `1648..1676`): `step_encChain_epilogue` -/

theorem step_encChain_epilogue (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (capOut ptrOut : BitVec 64)
    {x : EncodeChainGhost} {R : SepProp}
    {s0 s : State} {P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 1648#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (vecU8At A x.v capOut ptrOut (x.bs ++ lenField x.tag (encChainMem x.gc)) ∗
      protoChainAt A x.gc x.a ∗
      A.pool ∗ stackAt (s0.sp - 96#64) encChainSubStack ∗
      encChainSavedRegs s0.sp s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 1648 1676
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  unfold encChainSavedRegs
  have hsp_align96 := sp_sub_96_aligned halign
  apply SepWPpX.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPpX.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine ⟨?_, by simp only [arm64_norm, *],
    ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *]⟩⟩
  intro hm
  simp only [encodeChainSpecX, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨by simp only [arm64_norm, *], ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨capOut, ptrOut, ?_⟩
  rw [stackAt_encodeChainStackX_split s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
    s0.readReg64 (Reg.gpr 28#5), s0.readReg64 (Reg.gpr 27#5),
    s0.readReg64 (Reg.gpr 26#5), s0.readReg64 (Reg.gpr 25#5),
    s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
    s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
    s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5), ?_⟩
  convert hm using 1
  ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
