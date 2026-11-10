/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Tail
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeStateEmpty.Proof -- shake: keep

/-!
# Preamble Varint Loops of Empty-State `spqr::recv`

Verifies the epoch and index LEB128 varint-decoding loops and post-loop bounds checks of
`spqr::recv` on an empty state.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty
  (mr_cut' vecU8Tail vecArg_at_nil)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Exposing a single byte in `msg.at A` -/

/-- The remainder of `msg.at A` when byte `b` at `msg.ptr + pre.length` is focused (`msg.bytes = pre ++ b :: post`). -/
def msgByteFrame (A : RustAlloc) (msg : VecArg) (pre post : List (BitVec 8)) : SepProp :=
  (msg.v ↦₆₄ msg.cap) ∗ ((msg.v + 8#64) ↦₆₄ msg.ptr) ∗
    ((msg.v + 16#64) ↦₆₄ BitVec.ofNat 64 msg.bytes.length) ∗
    ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
    A.live msg.ptr msg.cap.toNat 1 ∗
    (msg.ptr ↦ₛ pre) ∗
    ((msg.ptr + BitVec.ofNat 64 pre.length + 1#64) ↦ₛ post) ∗
    memRegion (msg.ptr + BitVec.ofNat 64 msg.bytes.length) (msg.cap.toNat - msg.bytes.length)

theorem msg_expose_byte (A : RustAlloc) (msg : VecArg) (pre post : List (BitVec 8)) (b : BitVec 8)
    (off : BitVec 64) (hsplit : msg.bytes = pre ++ b :: post)
    (hoff : off = msg.ptr + BitVec.ofNat 64 pre.length) :
    msg.at A ⊢ (off ↦₈ b) ∗ msgByteFrame A msg pre post := by
  simp only [VecArg.at, vecU8At, vecHeader, msgByteFrame, sepConj_assoc, sepConj_pure_left_comm]
  refine Entails.pure_left fun hp => Entails.pure_right hp ?_
  have hcap : msg.cap ≠ 0 := by
    intro hc
    have h0 : msg.cap.toNat = 0 := by rw [hc]; rfl
    have hpos : 0 < msg.bytes.length := by rw [hsplit]; simp
    omega
  have hpts : (msg.ptr ↦ₛ msg.bytes) =
      (msg.ptr ↦ₛ pre) ∗ (off ↦₈ b) ∗ ((off + 1#64) ↦ₛ post) := by
    rw [hsplit, pointsToBytes_append, pointsToBytes_cons, ← hoff]
  simp only [hcap, ↓reduceIte, hpts, ← hoff]
  exact Entails.of_eq (by ac_rfl)

theorem msg_unexpose_byte (A : RustAlloc) (msg : VecArg) (pre post : List (BitVec 8)) (b : BitVec 8)
    (off : BitVec 64) (hsplit : msg.bytes = pre ++ b :: post)
    (hoff : off = msg.ptr + BitVec.ofNat 64 pre.length) :
    ((off ↦₈ b) ∗ msgByteFrame A msg pre post) ⊢ msg.at A := by
  simp only [VecArg.at, vecU8At, vecHeader, msgByteFrame, sepConj_assoc, sepConj_pure_left_comm]
  refine Entails.pure_left fun hp => Entails.pure_right hp ?_
  have hcap : msg.cap ≠ 0 := by
    intro hc
    have h0 : msg.cap.toNat = 0 := by rw [hc]; rfl
    have hpos : 0 < msg.bytes.length := by rw [hsplit]; simp
    omega
  have hpts : (msg.ptr ↦ₛ msg.bytes) =
      (msg.ptr ↦ₛ pre) ∗ (off ↦₈ b) ∗ ((off + 1#64) ↦ₛ post) := by
    rw [hsplit, pointsToBytes_append, pointsToBytes_cons, ← hoff]
  simp only [hcap, ↓reduceIte, hpts, ← hoff]
  exact Entails.of_eq (by ac_rfl)

/-! ## Pure bitvector and varint lemmas -/

theorem varint_out_norm (out : BitVec 64) (b : BitVec 8) (i : Nat) (hi : i < 10) :
    (BitVec.setWidth 64 b &&& 127#64) <<< (7 * i % 64) ||| out =
      out ||| (BitVec.setWidth 64 b &&& 127#64) <<< (7 * i) := by
  have hm : 7 * i % 64 = 7 * i := Nat.mod_eq_of_lt (by omega)
  rw [hm, BitVec.or_comm]

theorem list_cons_of_length_pos {α : Type} {l : List α} (h : 0 < l.length) :
    ∃ x xs, l = x :: xs := by
  cases l with
  | nil => simp at h
  | cons x xs => exact ⟨x, xs, rfl⟩

theorem nat_le_of_bv_ule {a b : Nat} (ha : a ≤ 10) (hb : b ≤ 10)
    (h : (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = true) : a ≤ b := by
  simp [BitVec.ule, BitVec.toNat_ofNat] at h
  omega

theorem nat_lt_of_not_bv_ule {a b : Nat} (ha : a ≤ 10) (hb : b ≤ 10)
    (h : ¬(BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = true) : b < a := by
  simp [BitVec.ule, BitVec.toNat_ofNat] at h
  omega

theorem hb_ne_of_sxtb_tb (b : BitVec 8)
    (htb : (BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 b >>> 0 &&& 255#64 |||
          (if b.getLsbD 7 = true then (bv% (2 ^ 64 - 1)) else 0#64) &&& bv% (2 ^ 64 - 256)))).getLsbD 31 = true) :
    b &&& 0x80#8 ≠ 0#8 := by
  revert b htb; decide

theorem hb_eq_of_not_sxtb_tb (b : BitVec 8)
    (htb : ¬(BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 b >>> 0 &&& 255#64 |||
          (if b.getLsbD 7 = true then (bv% (2 ^ 64 - 1)) else 0#64) &&& bv% (2 ^ 64 - 256)))).getLsbD 31 = true) :
    b &&& 0x80#8 = 0#8 := by
  revert b htb; decide

theorem csel_rest1_min_10 {msg_len pre1_len rest1_len : Nat}
    (hlen : msg_len = 1 + pre1_len + rest1_len) (hlt : msg_len < 2 ^ 63) :
    (if (BitVec.ofNat 64 msg_len - BitVec.ofNat 64 (1 + pre1_len)).ult 10#64 = true then
      BitVec.ofNat 64 msg_len - BitVec.ofNat 64 (1 + pre1_len)
    else 10#64) = BitVec.ofNat 64 (min rest1_len 10) := by
  have h1 : 1 + pre1_len < 2 ^ 63 := by omega
  have h2 : rest1_len < 2 ^ 63 := by omega
  have hsub : BitVec.ofNat 64 msg_len - BitVec.ofNat 64 (1 + pre1_len) =
      BitVec.ofNat 64 rest1_len := by bv_omega
  rw [hsub]
  clear hsub
  by_cases h : rest1_len < 10
  · have hlt10 : (BitVec.ofNat 64 rest1_len).ult 10#64 = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat]; omega
    have hmin : min rest1_len 10 = rest1_len := Nat.min_eq_left (Nat.le_of_lt h)
    simp [hlt10, hmin]
  · have hlt10 : ¬((BitVec.ofNat 64 rest1_len).ult 10#64 = true) := by
      simp [BitVec.ult, BitVec.toNat_ofNat]; omega
    have hmin : min rest1_len 10 = 10 := Nat.min_eq_right (by omega)
    simp [hlt10, hmin]

theorem rest1_nil_of_ule {version : BitVec 8} {msg_bytes pre₁ rest1 : List (BitVec 8)}
    (hmsg : msg_bytes = version :: (pre₁ ++ rest1))
    (_hlt : msg_bytes.length < 2 ^ 63)
    (hls : (BitVec.ofNat 64 msg_bytes.length).ule (BitVec.ofNat 64 (1 + pre₁.length)) = true) :
    rest1 = [] := by
  have hlen : msg_bytes.length = 1 + pre₁.length + rest1.length := by
    rw [hmsg, List.length_cons, List.length_append]
    omega
  simp [BitVec.ule, BitVec.toNat_ofNat] at hls
  have h0 : rest1.length = 0 := by omega
  exact List.eq_nil_of_length_eq_zero h0

theorem rest1_cons_of_not_ule {version : BitVec 8} {msg_bytes pre₁ rest1 : List (BitVec 8)}
    (hmsg : msg_bytes = version :: (pre₁ ++ rest1))
    (_hlt : msg_bytes.length < 2 ^ 63)
    (hls : ¬(BitVec.ofNat 64 msg_bytes.length).ule (BitVec.ofNat 64 (1 + pre₁.length)) = true) :
    ∃ b₀ rest1', rest1 = b₀ :: rest1' := by
  have hlen : msg_bytes.length = 1 + pre₁.length + rest1.length := by
    rw [hmsg, List.length_cons, List.length_append]
    omega
  simp [BitVec.ule, BitVec.toNat_ofNat] at hls
  have hpos : 0 < rest1.length := by omega
  exact list_cons_of_length_pos hpos

theorem spqrVarintAux_err_of_hi {i : Nat} {out : BitVec 64} {b : BitVec 8} {rest' : List (BitVec 8)}
    (hb : b &&& 0x80#8 ≠ 0#8) (hend : i + 1 = 10 ∨ rest' = []) :
    spqrVarintAux i out (b :: rest') = none := by
  rw [spqrVarintAux]
  simp only [hb, ↓reduceIte, maxVarintBytes]
  rcases hend with h10 | rfl
  · simp [h10]
  · by_cases h10 : i + 1 = 10 <;> simp [h10, spqrVarintAux]

theorem spqrVarintAux_ok_of_lo {i : Nat} {out : BitVec 64} {b : BitVec 8} {rest' : List (BitVec 8)}
    (hb : b &&& 0x80#8 = 0#8) :
    spqrVarintAux i out (b :: rest') =
      some (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * i)), rest') := by
  rw [spqrVarintAux]
  simp [hb]

theorem spqrVarintAux_step_of_hi {i : Nat} {out : BitVec 64} {b : BitVec 8} {rest' : List (BitVec 8)}
    (hb : b &&& 0x80#8 ≠ 0#8) (hi : i + 1 < 10) :
    spqrVarintAux i out (b :: rest') =
      spqrVarintAux (i + 1) (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * i))) rest' := by
  conv => lhs; rw [spqrVarintAux]
  have hne : i + 1 ≠ maxVarintBytes := by unfold maxVarintBytes; omega
  simp [hb, hne]

theorem index_bounds_ne {msg_len pre1_len j : Nat}
    (h1 : 1 ≤ pre1_len) (hlen : pre1_len + j + 2 ≤ msg_len) (hlt : msg_len < 2 ^ 63) :
    BitVec.ofNat 64 (msg_len - 2) ≠ BitVec.ofNat 64 (pre1_len - 1 + j) := by
  bv_omega

theorem varint_end_of_ge {j : Nat} {rest1 pre2 rest' : List (BitVec 8)} {b : BitVec 8}
    (hj : j < 10) (hrest1 : rest1 = pre2 ++ b :: rest') (hpre2 : pre2.length = j)
    (hge : min rest1.length 10 ≤ j + 1) :
    j + 1 = 10 ∨ rest' = [] := by
  have hlen : rest1.length = j + 1 + rest'.length := by
    rw [hrest1, List.length_append, List.length_cons, hpre2]; omega
  by_cases h10 : j + 1 = 10
  · exact Or.inl h10
  · right
    have h0 : rest'.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero h0

theorem varint_cont_of_lt {j : Nat} {rest1 pre2 rest' : List (BitVec 8)} {b : BitVec 8}
    (hrest1 : rest1 = pre2 ++ b :: rest') (hpre2 : pre2.length = j)
    (hlt : j + 1 < min rest1.length 10) :
    j + 1 < 10 ∧ ∃ b' rest'', rest' = b' :: rest'' := by
  have hlen : rest1.length = j + 1 + rest'.length := by
    rw [hrest1, List.length_append, List.length_cons, hpre2]; omega
  refine ⟨by omega, ?_⟩
  cases rest' with
  | nil => simp [List.length_nil] at hlen; omega
  | cons b' rest'' => exact ⟨b', rest'', rfl⟩

/-! ## Post-index check (`+252 .. +272`, `0x54728 .. 0x5473c`) -/

set_option maxHeartbeats 800000 in
/-- Steps from `+252` (`0x54728: lsr x11, x21, #32`) after `spqrDecodeVarint rest1 = some (index, rest2)`
to `ret`. -/
theorem step_after_index (img : Obj.Image) (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (S : SpqrModel) (F : SepProp)
    (hmc : subroutine_ok (libsignalSessionCode.rebase base hooks)
      ((libsignalSessionCode.rebase base hooks).fnAddr spqrRecvName +
        bv% (ls_off% "memcpy" - ls_off% "spqr::recv"))
      (memcpyRecvPcsSpecS.inImage img))
    (st msg : VecArg) (ret : BitVec 64) (version : BitVec 8) (index : BitVec 64)
    (r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrRecvEmptyCodeSpec0 A S img F).post (st, msg, ret) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hst : st.bytes = [])
    (hrecv : S.recv st.bytes msg.bytes =
      if index.toNat < 2 ^ 32 then .ok ([], none) else .error false)
    (hpc : s.pc = (libsignalSessionCode.rebase base hooks).fnAddr spqrRecvName + 252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = index)
    (hx25 : s.readReg64 .x25 = version.zeroExtend 64)
    (hP : P =
      st.at A ∗ msg.at A ∗
      ((ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2) ∗
        ((ret + 24#64) ↦₆₄ r3) ∗ memRegion (ret + 32#64) 16) ∗
      F ∗ A.pool ∗
      recvStackRest s0.sp f0 f8 f16 f24 b50 b58 b60
        (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19))
    (hI : RecvImgInv img s) :
    SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post := by
  have hfn : libsignalSessionCode.fnOff spqrRecvName = num% (ls_off% "spqr::recv") :=
    (ls_lemma% fnOff "spqr::recv")
  have herr_tail := step_recv_err_tail img base hooks A S F st msg ret
    r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 s0
  have hok_tail := step_recv_ok_tail img base hooks A S F hmc st msg ret version
    r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 s0
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    base hooks hfn (num% (ls_off% "spqr::recv")) 252 24
  clear hfn
  dsimp only [spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail ⊢
  generalize_entry (libsignalSessionCode.rebase base
    hooks).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_if hhi
  · have hnlt : ¬ index.toNat < 2 ^ 32 := by bv_omega
    have herr : S.recv st.bytes msg.bytes = .error false := by
      simp only [hrecv, hnlt, ↓reduceIte]
    exact herr_tail _ P R post hpost herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hsp, arm64_norm]) hs0A (by simp [htr, arm64_norm]) (by simp [hx19, arm64_norm]) hP
  · have hlt : index.toNat < 2 ^ 32 := by bv_omega
    have hok : S.recv st.bytes msg.bytes = .ok ([], none) := by
      simp only [hrecv, hlt, ↓reduceIte]
    wp_steps
    exact hok_tail _ P R post hpost hst hok (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hsp, arm64_norm]) hs0A (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm])
      (by simp [hx19, arm64_norm]) (by simp [hx25, arm64_norm]) hP
      (RecvImgInv.congr hI (by simp [arm64_norm]) (by simp [arm64_norm]))

/-! ## Index varint loop (`+192 .. +248`, `0x546ec .. 0x54724`) -/

set_option maxHeartbeats 1600000 in
/-- Steps the index varint loop (`+192 .. +248`) from iteration `j` (`k = 10 - j` fuel) to `ret`. -/
theorem step_index_loop (img : Obj.Image) (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (S : SpqrModel) (F : SepProp)
    (hmc : subroutine_ok (libsignalSessionCode.rebase base hooks)
      ((libsignalSessionCode.rebase base hooks).fnAddr spqrRecvName +
        bv% (ls_off% "memcpy" - ls_off% "spqr::recv"))
      (memcpyRecvPcsSpecS.inImage img))
    (st msg : VecArg) (ret : BitVec 64) (version : BitVec 8)
    (pre₁ rest1 : List (BitVec 8))
    (r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrRecvEmptyCodeSpec0 A S img F).post (st, msg, ret) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hst : st.bytes = [])
    (hs0A : s0.spAligned = true)
    (hpre1 : 1 ≤ pre₁.length)
    (hlen_lt : msg.bytes.length < 2 ^ 63) :
    ∀ (k j : Nat) (out : BitVec 64) (pre₂ rest' : List (BitVec 8)) (b : BitVec 8)
      (s : State) (P : SepProp),
      10 - j ≤ k →
      j < 10 →
      msg.bytes = (version :: pre₁ ++ pre₂) ++ b :: rest' →
      rest1 = pre₂ ++ b :: rest' →
      pre₂.length = j →
      (S.recv st.bytes msg.bytes =
        match spqrVarintAux j out (b :: rest') with
        | none => .error false
        | some (index, _) => if index.toNat < 2 ^ 32 then .ok ([], none) else .error false) →
      s.pc = (libsignalSessionCode.rebase base hooks).fnAddr spqrRecvName + 192#64 →
      s.status = .Running →
      s.sp = s0.sp - 4992#64 →
      s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x0 = st.v →
      s.readReg64 .x19 = ret →
      s.readReg64 .x25 = version.zeroExtend 64 →
      s.readReg64 .x8 = msg.ptr + 1#64 →
      s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length →
      s.readReg64 .x10 = BitVec.ofNat 64 (pre₁.length + j) →
      s.readReg64 .x11 = BitVec.ofNat 64 (7 * j) →
      s.readReg64 .x12 = BitVec.ofNat 64 (pre₁.length - 1 + j) →
      s.readReg64 .x13 = BitVec.ofNat 64 (min rest1.length 10) →
      s.readReg64 .x14 = BitVec.ofNat 64 (msg.bytes.length - 2) →
      s.readReg64 .x15 = BitVec.ofNat 64 (j + 1) →
      s.readReg64 .x21 = out →
      P =
        st.at A ∗ msg.at A ∗
        ((ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2) ∗
          ((ret + 24#64) ↦₆₄ r3) ∗ memRegion (ret + 32#64) 16) ∗
        F ∗ A.pool ∗
        recvStackRest s0.sp f0 f8 f16 f24 b50 b58 b60
          (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) →
      RecvImgInv img s →
      SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post := by
  intro k
  induction k with
  | zero =>
    intro j _ _ _ _ hjk hj
    omega
  | succ k ih =>
    intro j out pre₂ rest' b s P hjk hj hsplit hrest1 hpre2 hrecv
      hpc hrun hsp htr hx0 hx19 hx25 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx21 hP hI
    have hfn : libsignalSessionCode.fnOff spqrRecvName = num% (ls_off% "spqr::recv") :=
      (ls_lemma% fnOff "spqr::recv")
    have herr_tail := step_recv_err_tail img base hooks A S F st msg ret
      r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 s0
    have hafter := step_after_index img base hooks A S F hmc st msg ret version
      (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * j)))
      r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 s0
    code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
      base hooks hfn (num% (ls_off% "spqr::recv")) 192 60
    clear hfn
    have hmsg_ge : pre₁.length + j + 2 ≤ msg.bytes.length := by
      rw [hsplit]; simp [hpre2]
    have hne_bounds := index_bounds_ne hpre1 hmsg_ge hlen_lt
    have hoff : msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j)) =
        msg.ptr + BitVec.ofNat 64 (version :: pre₁ ++ pre₂).length := by
      simp only [List.length_cons, List.length_append, hpre2]; bv_omega
    have hexp := msg_expose_byte A msg (version :: pre₁ ++ pre₂) rest' b
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j))) hsplit hoff
    have hunexp := msg_unexpose_byte A msg (version :: pre₁ ++ pre₂) rest' b
      (msg.ptr + (1#64 + BitVec.ofNat 64 (pre₁.length + j))) hsplit hoff
    clear hoff
    have hsplit_symm := hsplit.symm; clear hsplit
    have hrest1_symm := hrest1.symm; clear hrest1
    subst hP
    dsimp only [spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc herr_tail hafter ih ⊢
    generalize_entry (libsignalSessionCode.rebase base
      hooks).fnAddr "spqr::recv" = entry
    examples_hide_fetches
    wp_steps
    wp_if hbounds
    · exact False.elim (hne_bounds hbounds)
    clear hbounds
    refine SepWP.fold hexp (by sep_focus) ?_
    wp_steps
    refine SepWP.fold hunexp (by sep_focus) ?_
    wp_if hhs
    · have hge : min rest1.length 10 ≤ j + 1 :=
        nat_le_of_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      have hend := varint_end_of_ge hj hrest1_symm.symm hpre2 hge
      wp_steps
      wp_if htb
      · have hb : b &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb b htb
        have herr : S.recv st.bytes msg.bytes = .error false := by
          rw [hrecv, spqrVarintAux_err_of_hi hb hend]
        exact herr_tail _ _ R post hpost herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          (by simp [hsp, arm64_norm]) hs0A (by simp [htr, arm64_norm])
          (by simp [hx19, arm64_norm]) (by ac_rfl)
      · have hb : b &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb b htb
        have hrec_ok : S.recv st.bytes msg.bytes =
            if (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).toNat < 2 ^ 32 then .ok ([], none)
            else .error false := by
          rw [hrecv, spqrVarintAux_ok_of_lo hb]
        exact hafter _ _ R post hpost hst hrec_ok (by simp [arm64_norm])
          (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm]) hs0A
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [arm64_norm]; exact varint_out_norm out b j hj)
          (by simp [hx25, arm64_norm]) (by ac_rfl)
          (RecvImgInv.congr hI (by simp [arm64_norm]) (by simp [arm64_norm]))
    · have hlt : j + 1 < min rest1.length 10 :=
        nat_lt_of_not_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      obtain ⟨hj1, b', rest'', rfl⟩ := varint_cont_of_lt hrest1_symm.symm hpre2 hlt
      wp_steps
      wp_if htb
      · have hb : b &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb b htb
        have hrec_step : S.recv st.bytes msg.bytes =
            match spqrVarintAux (j + 1) (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) (b' :: rest'') with
            | none => .error false
            | some (index, _) => if index.toNat < 2 ^ 32 then .ok ([], none) else .error false := by
          rw [hrecv, spqrVarintAux_step_of_hi hb hj1]
        have hsplit' : msg.bytes = (version :: pre₁ ++ (pre₂ ++ [b])) ++ b' :: rest'' := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hrest1' : rest1 = (pre₂ ++ [b]) ++ b' :: rest'' := by
          rw [← hrest1_symm]; simp [List.append_assoc]
        have hpre2' : (pre₂ ++ [b]).length = j + 1 := by
          rw [List.length_append, List.length_singleton, hpre2]
        exact ih (j + 1) (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * j)))
          (pre₂ ++ [b]) rest'' b' _ _ (by omega) hj1 hsplit' hrest1' hpre2' hrec_step
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx25, arm64_norm]) (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [arm64_norm]; bv_omega)
          (by simp [arm64_norm]; bv_omega)
          (by simp [arm64_norm]; bv_omega)
          (by simp [hx13, arm64_norm]) (by simp [hx14, arm64_norm])
          (by simp [arm64_norm]; bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out b j hj)
          (by ac_rfl)
          (RecvImgInv.congr hI (by simp [arm64_norm]) (by simp [arm64_norm]))
      · have hb : b &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb b htb
        have hrec_ok : S.recv st.bytes msg.bytes =
            if (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * j))).toNat < 2 ^ 32 then .ok ([], none)
            else .error false := by
          rw [hrecv, spqrVarintAux_ok_of_lo hb]
        wp_steps
        exact hafter _ _ R post hpost hst hrec_ok (by simp [arm64_norm])
          (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm]) hs0A
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [arm64_norm]; exact varint_out_norm out b j hj)
          (by simp [hx25, arm64_norm]) (by ac_rfl)
          (RecvImgInv.congr hI (by simp [arm64_norm]) (by simp [arm64_norm]))

/-! ## Post-epoch check (`+144 .. +188`, `0x546bc .. 0x546e8`) -/

set_option maxHeartbeats 800000 in
/-- Steps from `+144` (`0x546bc: cbz x22, 0x54740`) after `spqrDecodeVarint rest0 = some (epoch, rest1)`
to `ret`. -/
theorem step_after_epoch (img : Obj.Image) (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (S : SpqrModel) (F : SepProp)
    (hmc : subroutine_ok (libsignalSessionCode.rebase base hooks)
      ((libsignalSessionCode.rebase base hooks).fnAddr spqrRecvName +
        bv% (ls_off% "memcpy" - ls_off% "spqr::recv"))
      (memcpyRecvPcsSpecS.inImage img))
    (st msg : VecArg) (ret : BitVec 64) (version : BitVec 8)
    (pre₁ rest1 : List (BitVec 8)) (epoch : BitVec 64)
    (r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrRecvEmptyCodeSpec0 A S img F).post (st, msg, ret) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hst : st.bytes = [])
    (hs0A : s0.spAligned = true)
    (hpre1 : 1 ≤ pre₁.length)
    (hlen_lt : msg.bytes.length < 2 ^ 63)
    (hmsg_eq : msg.bytes = version :: (pre₁ ++ rest1))
    (hrecv : S.recv st.bytes msg.bytes =
      if epoch == 0#64 then .error false
      else
        match spqrDecodeVarint rest1 with
        | none => .error false
        | some (index, _) => if index.toNat < 2 ^ 32 then .ok ([], none) else .error false)
    (hpc : s.pc = (libsignalSessionCode.rebase base hooks).fnAddr spqrRecvName + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx19 : s.readReg64 .x19 = ret)
    (hx25 : s.readReg64 .x25 = version.zeroExtend 64)
    (hx8 : s.readReg64 .x8 = msg.ptr + 1#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 (1 + pre₁.length))
    (hx22 : s.readReg64 .x22 = epoch)
    (hP : P =
      st.at A ∗ msg.at A ∗
      ((ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2) ∗
        ((ret + 24#64) ↦₆₄ r3) ∗ memRegion (ret + 32#64) 16) ∗
      F ∗ A.pool ∗
      recvStackRest s0.sp f0 f8 f16 f24 b50 b58 b60
        (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
        (s0.readReg64 .x20) (s0.readReg64 .x19))
    (hI : RecvImgInv img s) :
    SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post := by
  have hfn : libsignalSessionCode.fnOff spqrRecvName = num% (ls_off% "spqr::recv") :=
    (ls_lemma% fnOff "spqr::recv")
  have herr_tail := step_recv_err_tail img base hooks A S F st msg ret
    r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 s0
  have hidx_loop := step_index_loop img base hooks A S F hmc st msg ret version pre₁ rest1
    r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 s0 R post hpost hst hs0A hpre1 hlen_lt 10 0 0#64 []
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    base hooks hfn (num% (ls_off% "spqr::recv")) 144 48
  clear hfn
  have hmsg_symm := hmsg_eq.symm; clear hmsg_eq
  dsimp only [spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc herr_tail hidx_loop ⊢
  generalize_entry (libsignalSessionCode.rebase base
    hooks).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_if hepoch
  · have herr : S.recv st.bytes msg.bytes = .error false := by
      simp [hrecv, hepoch]
    exact herr_tail _ P R post hpost herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hsp, arm64_norm]) hs0A (by simp [htr, arm64_norm]) (by simp [hx19, arm64_norm]) hP
  · have hepoch_f : (epoch == 0#64) = false := beq_false_of_ne hepoch
    wp_steps
    wp_if hls
    · have hrest1_nil := rest1_nil_of_ule hmsg_symm.symm hlen_lt hls
      have herr : S.recv st.bytes msg.bytes = .error false := by
        rw [hrecv, hepoch_f, hrest1_nil]; rfl
      exact herr_tail _ P R post hpost herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hsp, arm64_norm]) hs0A (by simp [htr, arm64_norm]) (by simp [hx19, arm64_norm]) hP
    · wp_steps
      obtain ⟨b₀, rest1', hrest1_cons⟩ := rest1_cons_of_not_ule hmsg_symm.symm hlen_lt hls
      have hlen_eq : msg.bytes.length = 1 + pre₁.length + rest1.length := by
        rw [← hmsg_symm, List.length_cons, List.length_append]
        omega
      have hpre1_lt : 1 + pre₁.length < 2 ^ 63 := by omega
      have hlen_ge : 2 ≤ msg.bytes.length := by
        rw [← hmsg_symm, hrest1_cons]; simp; omega
      have hsplit0 : msg.bytes = (version :: pre₁ ++ []) ++ b₀ :: rest1' := by
        rw [← hmsg_symm, hrest1_cons]; simp
      have hrest1_0 : rest1 = [] ++ b₀ :: rest1' := hrest1_cons
      have hrecv0 : S.recv st.bytes msg.bytes =
          match spqrVarintAux 0 0#64 (b₀ :: rest1') with
          | none => .error false
          | some (index, _) => if index.toNat < 2 ^ 32 then .ok ([], none) else .error false := by
        rw [hrecv, hepoch_f, hrest1_cons]; rfl
      exact hidx_loop rest1' b₀ _ P (by omega) (by omega) hsplit0 hrest1_0 rfl hrecv0
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
        (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
        (by simp [hx25, arm64_norm]) (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
        (by simp [arm64_norm]; bv_omega)
        (by simp [arm64_norm])
        (by simp [arm64_norm]; bv_omega)
        (by simp [arm64_norm]; exact csel_rest1_min_10 hlen_eq hlen_lt)
        (by simp [arm64_norm]; bv_omega)
        (by simp [arm64_norm])
        (by simp [arm64_norm])
        hP
        (RecvImgInv.congr hI (by simp [arm64_norm]) (by simp [arm64_norm]))

/-! ## Epoch varint loop (`+96 .. +140`, `0x5468c .. 0x546b8`) -/

set_option maxHeartbeats 1600000 in
/-- Steps the epoch varint loop (`+96 .. +140`) from iteration `j` (`k = 10 - j` fuel) to `ret`. -/
theorem step_epoch_loop (img : Obj.Image) (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (S : SpqrModel) (F : SepProp)
    (hmc : subroutine_ok (libsignalSessionCode.rebase base hooks)
      ((libsignalSessionCode.rebase base hooks).fnAddr spqrRecvName +
        bv% (ls_off% "memcpy" - ls_off% "spqr::recv"))
      (memcpyRecvPcsSpecS.inImage img))
    (st msg : VecArg) (ret : BitVec 64) (version : BitVec 8)
    (rest0 : List (BitVec 8))
    (r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrRecvEmptyCodeSpec0 A S img F).post (st, msg, ret) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hst : st.bytes = [])
    (hs0A : s0.spAligned = true)
    (hlen_lt : msg.bytes.length < 2 ^ 63) :
    ∀ (k j : Nat) (out : BitVec 64) (pre₁ rest0' : List (BitVec 8)) (b : BitVec 8)
      (s : State) (P : SepProp),
      10 - j ≤ k →
      j < 10 →
      msg.bytes = (version :: pre₁) ++ b :: rest0' →
      rest0 = pre₁ ++ b :: rest0' →
      pre₁.length = j →
      (S.recv st.bytes msg.bytes =
        match spqrVarintAux j out (b :: rest0') with
        | none => .error false
        | some (epoch, rest1) =>
          if epoch == 0#64 then .error false
          else
            match spqrDecodeVarint rest1 with
            | none => .error false
            | some (index, _) => if index.toNat < 2 ^ 32 then .ok ([], none) else .error false) →
      s.pc = (libsignalSessionCode.rebase base hooks).fnAddr spqrRecvName + 96#64 →
      s.status = .Running →
      s.sp = s0.sp - 4992#64 →
      s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x0 = st.v →
      s.readReg64 .x19 = ret →
      s.readReg64 .x25 = version.zeroExtend 64 →
      s.readReg64 .x8 = msg.ptr + 1#64 →
      s.readReg64 .x9 = BitVec.ofNat 64 msg.bytes.length →
      s.readReg64 .x10 = BitVec.ofNat 64 (7 * j) →
      s.readReg64 .x11 = msg.ptr →
      s.readReg64 .x12 = BitVec.ofNat 64 (min rest0.length 10) →
      s.readReg64 .x14 = BitVec.ofNat 64 (j + 1) →
      s.readReg64 .x22 = out →
      P =
        st.at A ∗ msg.at A ∗
        ((ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2) ∗
          ((ret + 24#64) ↦₆₄ r3) ∗ memRegion (ret + 32#64) 16) ∗
        F ∗ A.pool ∗
        recvStackRest s0.sp f0 f8 f16 f24 b50 b58 b60
          (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) →
      RecvImgInv img s →
      SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post := by
  intro k
  induction k with
  | zero =>
    intro j _ _ _ _ hjk hj
    omega
  | succ k ih =>
    intro j out pre₁ rest0' b s P hjk hj hsplit hrest0 hpre1 hrecv
      hpc hrun hsp htr hx0 hx19 hx25 hx8 hx9 hx10 hx11 hx12 hx14 hx22 hP hI
    have hfn : libsignalSessionCode.fnOff spqrRecvName = num% (ls_off% "spqr::recv") :=
      (ls_lemma% fnOff "spqr::recv")
    have herr_tail := step_recv_err_tail img base hooks A S F st msg ret
      r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 s0
    have hafter := step_after_epoch img base hooks A S F hmc st msg ret version
      (pre₁ ++ [b]) rest0' (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * j)))
      r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 s0
    code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
      base hooks hfn (num% (ls_off% "spqr::recv")) 96 48
    clear hfn
    have hoff : msg.ptr + BitVec.ofNat 64 (j + 1) =
        msg.ptr + BitVec.ofNat 64 (version :: pre₁).length := by
      simp only [List.length_cons, hpre1]
    have hexp := msg_expose_byte A msg (version :: pre₁) rest0' b
      (msg.ptr + BitVec.ofNat 64 (j + 1)) hsplit hoff
    have hunexp := msg_unexpose_byte A msg (version :: pre₁) rest0' b
      (msg.ptr + BitVec.ofNat 64 (j + 1)) hsplit hoff
    clear hoff
    have hsplit_symm := hsplit.symm; clear hsplit
    have hrest0_symm := hrest0.symm; clear hrest0
    subst hP
    dsimp only [spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc herr_tail hafter ih ⊢
    generalize_entry (libsignalSessionCode.rebase base
      hooks).fnAddr "spqr::recv" = entry
    examples_hide_fetches
    refine SepWP.fold hexp (by sep_focus) ?_
    wp_steps
    refine SepWP.fold hunexp (by sep_focus) ?_
    wp_if hhs
    · have hge : min rest0.length 10 ≤ j + 1 :=
        nat_le_of_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      have hend := varint_end_of_ge hj hrest0_symm.symm hpre1 hge
      wp_steps
      wp_if htb
      · have hb : b &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb b htb
        have herr : S.recv st.bytes msg.bytes = .error false := by
          rw [hrecv, spqrVarintAux_err_of_hi hb hend]
        exact herr_tail _ _ R post hpost herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          (by simp [hsp, arm64_norm]) hs0A (by simp [htr, arm64_norm])
          (by simp [hx19, arm64_norm]) (by ac_rfl)
      · have hb : b &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb b htb
        have hrec_ok : S.recv st.bytes msg.bytes =
            if (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) == 0#64 then .error false
            else
              match spqrDecodeVarint rest0' with
              | none => .error false
              | some (index, _) => if index.toNat < 2 ^ 32 then .ok ([], none) else .error false := by
          rw [hrecv, spqrVarintAux_ok_of_lo hb]
        have hmsg_eq' : msg.bytes = version :: ((pre₁ ++ [b]) ++ rest0') := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hpre1' : 1 ≤ (pre₁ ++ [b]).length := by
          rw [List.length_append, List.length_singleton]; omega
        exact hafter _ _ R post hpost hst hs0A hpre1' hlen_lt hmsg_eq' hrec_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx25, arm64_norm]) (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [hpre1, arm64_norm]; bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out b j hj)
          (by ac_rfl)
          (RecvImgInv.congr hI (by simp [arm64_norm]) (by simp [arm64_norm]))
    · have hlt : j + 1 < min rest0.length 10 :=
        nat_lt_of_not_bv_ule (Nat.min_le_right _ _) (by omega) hhs
      obtain ⟨hj1, b', rest0'', rfl⟩ := varint_cont_of_lt hrest0_symm.symm hpre1 hlt
      wp_steps
      wp_if htb
      · have hb : b &&& 0x80#8 ≠ 0#8 := hb_ne_of_sxtb_tb b htb
        have hrec_step : S.recv st.bytes msg.bytes =
            match spqrVarintAux (j + 1) (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) (b' :: rest0'') with
            | none => .error false
            | some (epoch, rest1) =>
              if epoch == 0#64 then .error false
              else
                match spqrDecodeVarint rest1 with
                | none => .error false
                | some (index, _) => if index.toNat < 2 ^ 32 then .ok ([], none) else .error false := by
          rw [hrecv, spqrVarintAux_step_of_hi hb hj1]
        have hsplit' : msg.bytes = (version :: (pre₁ ++ [b])) ++ b' :: rest0'' := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hrest0' : rest0 = (pre₁ ++ [b]) ++ b' :: rest0'' := by
          rw [← hrest0_symm]; simp [List.append_assoc]
        have hpre1' : (pre₁ ++ [b]).length = j + 1 := by
          rw [List.length_append, List.length_singleton, hpre1]
        exact ih (j + 1) (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * j)))
          (pre₁ ++ [b]) rest0'' b' _ _ (by omega) hj1 hsplit' hrest0' hpre1' hrec_step
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx25, arm64_norm]) (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [arm64_norm]; bv_omega)
          (by simp [hx11, arm64_norm]) (by simp [hx12, arm64_norm])
          (by simp [arm64_norm]; bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out b j hj)
          (by ac_rfl)
          (RecvImgInv.congr hI (by simp [arm64_norm]) (by simp [arm64_norm]))
      · have hb : b &&& 0x80#8 = 0#8 := hb_eq_of_not_sxtb_tb b htb
        have hrec_ok : S.recv st.bytes msg.bytes =
            if (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * j))) == 0#64 then .error false
            else
              match spqrDecodeVarint (b' :: rest0'') with
              | none => .error false
              | some (index, _) => if index.toNat < 2 ^ 32 then .ok ([], none) else .error false := by
          rw [hrecv, spqrVarintAux_ok_of_lo hb]
        have hmsg_eq' : msg.bytes = version :: ((pre₁ ++ [b]) ++ b' :: rest0'') := by
          rw [← hsplit_symm]; simp [List.append_assoc]
        have hpre1' : 1 ≤ (pre₁ ++ [b]).length := by
          rw [List.length_append, List.length_singleton]; omega
        wp_steps
        exact hafter _ _ R post hpost hst hs0A hpre1' hlen_lt hmsg_eq' hrec_ok
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
          (by simp [hx25, arm64_norm]) (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm])
          (by simp [hpre1, arm64_norm]; bv_omega)
          (by simp [arm64_norm]; exact varint_out_norm out b j hj)
          (by ac_rfl)
          (RecvImgInv.congr hI (by simp [arm64_norm]) (by simp [arm64_norm]))

end CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
