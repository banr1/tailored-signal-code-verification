/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Mac.MacCodeSym
public import LibsignalBinary.Proofs.CodeLayout
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.Hmac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hmac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.Hmac.MD
import LibsignalBinary.Proofs.Hmac.OuterAux
import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.AesCbc.Bytes -- shake: keep

/-!
# Verification of `<SignalMessage>::compute_mac`

Verifies `<libsignal_protocol::protocol::SignalMessage>::compute_mac` against
`computeMacSpec` and `computeMacSpecX` on both rebased images and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState compress256Hook)
open CryptoVerification.LibsignalHmac.OuterAux
open ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet.GeneralizeEntry

set_option maxRecDepth 200000

/-! ## Hook contracts for `memset` and `sha2::sha256::compress256` -/

/-- Trace-preserving `memset` spec without a stack frame. -/
def session2MemsetSpec : Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := fun (dst, val, n) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ (s0.readReg64 .x1).truncate 8 = val ∧
      (s0.readReg64 .x2).toNat = n⌝ ∗
      memRegion dst n
  post := fun (dst, val, n) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ List.replicate n val)


/-- Trace-preserving `compress256` spec on `tripleRatchetProgAt`. -/
def session2Compress256Spec (F : ShaCompress) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (stA, st, blkA, blk, n) s0 =>
    ⌜s0.readReg64 .x0 = stA ∧ s0.readReg64 .x1 = blkA ∧
      (s0.readReg64 .x2).toNat = n ∧ blk.length = 64 * n⌝ ∗
      (stA ↦ₛ shaStateBytes st) ∗ (blkA ↦ₛ blk)
  post := fun (stA, st, blkA, blk, _n) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (stA ↦ₛ shaStateBytes ((chunks64 blk).foldl F st)) ∗ (blkA ↦ₛ blk)


/-! ## Byte, word, `ShaState`, and `hmacStateAt` representation lemmas -/

open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes

private theorem pointsTo8_eq_pointsToBytes (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

def bytesToU64LE (bs : List (BitVec 8)) : BitVec 64 :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend 64) 0

theorem unpack64_bytesToU64LE {bs : List (BitVec 8)} (h : bs.length = 8) :
    unpack64 (bytesToU64LE bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals (try simp at h)
  dsimp only [bytesToU64LE, unpack64, List.foldr]
  refine List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits, rfl⟩⟩⟩⟩⟩⟩⟩⟩

theorem pointsToBytes_8_eq_pointsTo64 (a : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ bytesToU64LE bs) := by
  rw [ProofLib.pointsTo64_eq_pointsToBytes, unpack64_bytesToU64LE h]

theorem list_eq_chunks8_of_len32 {α : Type} {bs : List α} (h : bs.length = 32) :
    bs = bs.take 8 ++ (bs.drop 8).take 8 ++ (bs.drop 16).take 8 ++ (bs.drop 24).take 8 := by
  have h1 : bs.drop 24 = (bs.drop 24).take 8 := by
    rw [List.take_of_length_le (by simp [h])]
  have h2 : bs.drop 8 = (bs.drop 8).take 8 ++ (bs.drop 16).take 8 ++ (bs.drop 24).take 8 := by
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 8)]
    rw [List.drop_drop, show 8 + 8 = 16 from rfl]
    conv_lhs => rhs; rw [← List.take_append_drop 8 (bs.drop 16)]
    rw [List.drop_drop, show 16 + 8 = 24 from rfl, ← h1, List.append_assoc]
  have h0 := (List.take_append_drop 8 bs).symm
  rw [h2] at h0
  simpa [List.append_assoc] using h0

theorem pointsToBytes_32_eq_words64 (a : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 32) :
    (a ↦ₛ bs) =
      (a ↦₆₄ bytesToU64LE (bs.take 8)) ∗
      ((a + 8#64) ↦₆₄ bytesToU64LE ((bs.drop 8).take 8)) ∗
      ((a + 16#64) ↦₆₄ bytesToU64LE ((bs.drop 16).take 8)) ∗
      ((a + 24#64) ↦₆₄ bytesToU64LE ((bs.drop 24).take 8)) := by
  conv_lhs => rw [list_eq_chunks8_of_len32 h]
  simp only [pointsToBytes_append, List.length_append, List.length_take, List.length_drop, h,
    Nat.min_eq_left (by omega : 8 ≤ 32), Nat.min_eq_left (by omega : 8 ≤ 32 - 8),
    Nat.min_eq_left (by omega : 8 ≤ 32 - 16), Nat.min_eq_left (by omega : 8 ≤ 32 - 24),
    BitVec.add_assoc, sepConj_assoc]
  rw [pointsToBytes_8_eq_pointsTo64 a (by simp [h]),
    pointsToBytes_8_eq_pointsTo64 (a + 8#64) (by simp [h]),
    pointsToBytes_8_eq_pointsTo64 (a + 16#64) (by simp [h]),
    pointsToBytes_8_eq_pointsTo64 (a + 24#64) (by simp [h])]

theorem pointsToBytes_64_eq_words64 (a : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 64) :
    (a ↦ₛ bs) =
      (a ↦₆₄ bytesToU64LE (bs.take 8)) ∗
      ((a + 8#64) ↦₆₄ bytesToU64LE ((bs.drop 8).take 8)) ∗
      ((a + 16#64) ↦₆₄ bytesToU64LE ((bs.drop 16).take 8)) ∗
      ((a + 24#64) ↦₆₄ bytesToU64LE ((bs.drop 24).take 8)) ∗
      ((a + 32#64) ↦₆₄ bytesToU64LE ((bs.drop 32).take 8)) ∗
      ((a + 40#64) ↦₆₄ bytesToU64LE ((bs.drop 40).take 8)) ∗
      ((a + 48#64) ↦₆₄ bytesToU64LE ((bs.drop 48).take 8)) ∗
      ((a + 56#64) ↦₆₄ bytesToU64LE ((bs.drop 56).take 8)) := by
  have hlo : (bs.take 32).length = 32 := by simp [h]
  have hhi : (bs.drop 32).length = 32 := by simp [h]
  conv_lhs => rw [← List.take_append_drop 32 bs]
  rw [pointsToBytes_append, hlo,
    pointsToBytes_32_eq_words64 a hlo,
    pointsToBytes_32_eq_words64 (a + 32#64) hhi]
  simp only [List.take_take, List.drop_take, List.drop_drop, BitVec.add_assoc, sepConj_assoc]
  rfl

private theorem unpack32_eq_toLEBytes_4 (w : BitVec 32) : unpack32 w = toLEBytes 4 w := rfl

theorem pointsToBytes_shaStateBytes_eq_32 (a : BitVec 64) (st : ShaState) :
    (a ↦ₛ shaStateBytes st) =
      (a ↦₃₂ st.get 0) ∗ ((a + 4#64) ↦₃₂ st.get 1) ∗
      ((a + 8#64) ↦₃₂ st.get 2) ∗ ((a + 12#64) ↦₃₂ st.get 3) ∗
      ((a + 16#64) ↦₃₂ st.get 4) ∗ ((a + 20#64) ↦₃₂ st.get 5) ∗
      ((a + 24#64) ↦₃₂ st.get 6) ∗ ((a + 28#64) ↦₃₂ st.get 7) := by
  rw [shaStateBytes_eq_append]
  simp only [pointsToBytes_append, toLEBytes_length,
    ← unpack32_eq_toLEBytes_4, ← ProofLib.pointsTo32_eq_pointsToBytes, BitVec.add_assoc, sepConj_assoc]
  rfl

def hmacBufBytes (tail pad : List (BitVec 8)) : List (BitVec 8) :=
  tail ++ pad ++ [BitVec.ofNat 8 tail.length]

theorem hmacBufBytes_length {tail pad : List (BitVec 8)}
    (ht : tail.length < 64) (hp : pad.length = 63 - tail.length) :
    (hmacBufBytes tail pad).length = 64 := by
  simp [hmacBufBytes, hp]; omega

def hmacWords64At (a : BitVec 64) (innerSt : ShaState) (nBlocks : Nat)
    (outerSt : ShaState) (tail pad : List (BitVec 8)) : SepProp :=
  let buf := hmacBufBytes tail pad
  let ib := shaStateBytes innerSt
  let ob := shaStateBytes outerSt
  (a ↦₆₄ bytesToU64LE (buf.take 8)) ∗
  ((a + 8#64) ↦₆₄ bytesToU64LE ((buf.drop 8).take 8)) ∗
  ((a + 16#64) ↦₆₄ bytesToU64LE ((buf.drop 16).take 8)) ∗
  ((a + 24#64) ↦₆₄ bytesToU64LE ((buf.drop 24).take 8)) ∗
  ((a + 32#64) ↦₆₄ bytesToU64LE ((buf.drop 32).take 8)) ∗
  ((a + 40#64) ↦₆₄ bytesToU64LE ((buf.drop 40).take 8)) ∗
  ((a + 48#64) ↦₆₄ bytesToU64LE ((buf.drop 48).take 8)) ∗
  ((a + 56#64) ↦₆₄ bytesToU64LE ((buf.drop 56).take 8)) ∗
  ((a + 64#64) ↦₆₄ bytesToU64LE (ib.take 8)) ∗
  ((a + 72#64) ↦₆₄ bytesToU64LE ((ib.drop 8).take 8)) ∗
  ((a + 80#64) ↦₆₄ bytesToU64LE ((ib.drop 16).take 8)) ∗
  ((a + 88#64) ↦₆₄ bytesToU64LE ((ib.drop 24).take 8)) ∗
  ((a + 96#64) ↦₆₄ BitVec.ofNat 64 nBlocks) ∗
  ((a + 104#64) ↦₆₄ bytesToU64LE (ob.take 8)) ∗
  ((a + 112#64) ↦₆₄ bytesToU64LE ((ob.drop 8).take 8)) ∗
  ((a + 120#64) ↦₆₄ bytesToU64LE ((ob.drop 16).take 8)) ∗
  ((a + 128#64) ↦₆₄ bytesToU64LE ((ob.drop 24).take 8)) ∗
  ((a + 136#64) ↦₆₄ 1#64)

theorem hmacWords64At_eq (a : BitVec 64) (innerSt : ShaState) (nBlocks : Nat)
    (outerSt : ShaState) {tail pad : List (BitVec 8)}
    (ht : tail.length < 64) (hp : pad.length = 63 - tail.length) :
    hmacWords64At a innerSt nBlocks outerSt tail pad =
      (a ↦ₛ tail) ∗ ((a + BitVec.ofNat 64 tail.length) ↦ₛ pad) ∗
      ((a + 0x3f#64) ↦₈ BitVec.ofNat 8 tail.length) ∗
      ((a + 0x40#64) ↦ₛ shaStateBytes innerSt) ∗
      ((a + 0x60#64) ↦₆₄ BitVec.ofNat 64 nBlocks) ∗
      ((a + 0x68#64) ↦ₛ shaStateBytes outerSt) ∗
      ((a + 0x88#64) ↦₆₄ 1#64) := by
  have hbuf : (a ↦ₛ hmacBufBytes tail pad) =
      (a ↦ₛ tail) ∗ ((a + BitVec.ofNat 64 tail.length) ↦ₛ pad) ∗
      ((a + 0x3f#64) ↦₈ BitVec.ofNat 8 tail.length) := by
    unfold hmacBufBytes
    rw [pointsToBytes_append, pointsToBytes_append, List.length_append, hp,
      show tail.length + (63 - tail.length) = 63 by omega,
      show (BitVec.ofNat 64 63 : BitVec 64) = 0x3f#64 from rfl,
      ← pointsTo8_eq_pointsToBytes, sepConj_assoc]
  have h64 := pointsToBytes_64_eq_words64 a (hmacBufBytes_length ht hp)
  have hib := pointsToBytes_32_eq_words64 (a + 0x40#64) (shaStateBytes_length innerSt)
  have hob := pointsToBytes_32_eq_words64 (a + 0x68#64) (shaStateBytes_length outerSt)
  have hrhs :
      (a ↦ₛ tail) ∗ ((a + BitVec.ofNat 64 tail.length) ↦ₛ pad) ∗
      ((a + 0x3f#64) ↦₈ BitVec.ofNat 8 tail.length) ∗
      ((a + 0x40#64) ↦ₛ shaStateBytes innerSt) ∗
      ((a + 0x60#64) ↦₆₄ BitVec.ofNat 64 nBlocks) ∗
      ((a + 0x68#64) ↦ₛ shaStateBytes outerSt) ∗
      ((a + 0x88#64) ↦₆₄ 1#64) =
      ((a ↦ₛ tail) ∗ ((a + BitVec.ofNat 64 tail.length) ↦ₛ pad) ∗
      ((a + 0x3f#64) ↦₈ BitVec.ofNat 8 tail.length)) ∗
      ((a + 0x40#64) ↦ₛ shaStateBytes innerSt) ∗
      ((a + 0x60#64) ↦₆₄ BitVec.ofNat 64 nBlocks) ∗
      ((a + 0x68#64) ↦ₛ shaStateBytes outerSt) ∗
      ((a + 0x88#64) ↦₆₄ 1#64) := by ac_rfl
  rw [hrhs, ← hbuf, h64, hib, hob]
  dsimp only [hmacWords64At]
  simp only [BitVec.add_assoc, sepConj_assoc]
  rfl

private theorem hmacStateAt_eq_words64 (a : BitVec 64) (innerSt : ShaState) (nBlocks : Nat)
    (outerSt : ShaState) (tail : List (BitVec 8)) :
    hmacStateAt a innerSt nBlocks outerSt tail =
      ∃∗ pad : List (BitVec 8),
        ⌜tail.length < 64 ∧ pad.length = 63 - tail.length⌝ ∗
        hmacWords64At a innerSt nBlocks outerSt tail pad := by
  unfold hmacStateAt
  rw [memRegion_eq_exists_bytes (a + BitVec.ofNat 64 tail.length) (63 - tail.length) (by omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun pad => ?_)
  have hlhs :
      ⌜tail.length < 64⌝ ∗ (a ↦ₛ tail) ∗
        (⌜pad.length = 63 - tail.length⌝ ∗ ((a + BitVec.ofNat 64 tail.length) ↦ₛ pad)) ∗
        ((a + 0x3f#64) ↦₈ BitVec.ofNat 8 tail.length) ∗
        ((a + 0x40#64) ↦ₛ shaStateBytes innerSt) ∗
        ((a + 0x60#64) ↦₆₄ BitVec.ofNat 64 nBlocks) ∗
        ((a + 0x68#64) ↦ₛ shaStateBytes outerSt) ∗
        ((a + 0x88#64) ↦₆₄ 1#64) =
      ⌜tail.length < 64⌝ ∗ ⌜pad.length = 63 - tail.length⌝ ∗
        ((a ↦ₛ tail) ∗ ((a + BitVec.ofNat 64 tail.length) ↦ₛ pad) ∗
          ((a + 0x3f#64) ↦₈ BitVec.ofNat 8 tail.length) ∗
          ((a + 0x40#64) ↦ₛ shaStateBytes innerSt) ∗
          ((a + 0x60#64) ↦₆₄ BitVec.ofNat 64 nBlocks) ∗
          ((a + 0x68#64) ↦ₛ shaStateBytes outerSt) ∗
          ((a + 0x88#64) ↦₆₄ 1#64)) := by ac_rfl
  rw [hlhs, pure_sepConj, pure_sepConj, pure_sepConj]
  ext h
  refine ⟨fun ⟨ht, hp, hm⟩ => ⟨⟨ht, hp⟩, ?_⟩, fun ⟨⟨ht, hp⟩, hm⟩ => ⟨ht, hp, ?_⟩⟩
  · rwa [hmacWords64At_eq a innerSt nBlocks outerSt ht hp]
  · rwa [← hmacWords64At_eq a innerSt nBlocks outerSt ht hp]

theorem hmacWords64At_entails_hmacStateAt (a : BitVec 64) (innerSt : ShaState)
    (nBlocks : Nat) (outerSt : ShaState) {tail pad : List (BitVec 8)}
    (ht : tail.length < 64) (hp : pad.length = 63 - tail.length) :
    hmacWords64At a innerSt nBlocks outerSt tail pad ⊢
      hmacStateAt a innerSt nBlocks outerSt tail := by
  rw [hmacStateAt_eq_words64]
  refine Entails.trans ?_ (Entails.sepExists_right pad (Entails.refl _))
  have htrue : (⌜tail.length < 64 ∧ pad.length = 63 - tail.length⌝ ∗
      hmacWords64At a innerSt nBlocks outerSt tail pad) =
      hmacWords64At a innerSt nBlocks outerSt tail pad := by
    simp only [pure_sepConj, ht, hp, and_self, true_and]
  rw [htrue]
  exact Entails.refl _

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") → (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac" + 1260)]

local elab "s2_ext_fetches " b:term:max ext:term:max
    hfn:term:max off:term:max len:term:max : tactic => open Lean Meta Elab Tactic in do
  let offLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat off "s2_ext_fetches "))
  let k0Lit := Syntax.mkNumLit "0"
  let lenLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat len "s2_ext_fetches "))
  let hfnId : Ident ← if hfn.raw.isIdent then pure ⟨hfn.raw⟩ else do
    let g ← getMainGoal
    let c? ← g.withContext do
      tryCatchRuntimeEx (do
        let e := (← instantiateMVars (← Term.elabTermAndSynthesize hfn none)).consumeMData
        return if e.isConst then some e.constName! else none) (fun _ => pure none)
    match c? with
    | some c => pure (mkCIdentFrom hfn c)
    | none =>
      let id := mkIdent `_hfn_layout
      evalTactic (← `(tactic| have $id := $hfn))
      pure id
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode libsignalSessionBin $b (Rust.withPanics $ext) $hfnId:ident $offLit:num $k0Lit:num $lenLit:num))

private theorem session2Memset_of_sessionMemsetRegion {prog : Program} {addr : BitVec 64}
    (h : subroutine_ok prog addr sessionMemsetRegionSpec) :
    subroutine_ok prog addr session2MemsetSpec := by
  refine subroutine_ok_outcome_intro fun ⟨dst, val, n⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ sessionMemsetRegionSpec.pre (dst, val, n) s0 ∗ R := by
    simp only [session2MemsetSpec, sessionMemsetRegionSpec, memsetRegionSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
    refine ⟨⟨hx0, ?_, hx2, by rw [← hx2]; exact Nat.le_of_lt (s0.readReg64 .x2).isLt⟩, hmem⟩
    rw [← hx1]; dsimp [State.readReg32]; bv_bits
  exact subroutine_ok.mono_outcome h (dst, val, n) R s0 hpc hrun hpre' hsp fun _ hout => hout

private theorem computeMac_fnOff : libsignalSessionCode.fnOff computeMacName = num% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") :=
  (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::compute_mac")
private theorem of_sepWP_inImage {prog : Program} (mid : BitVec 64) {ret : BitVec 64} {img : Obj.Image}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem stackAt_pk_eq_nfs (sp : BitVec 64) :
    stackAt sp publicKeySerializeStack =
      stackAt sp newFromSliceStack ∗ memRegion (sp - 4128#64) 3584 := by
  simp only [stackAt, publicKeySerializeStack, allocHookStack, newFromSliceStack]
  rw [show (4096 + 32 : Nat) = 3584 + 544 by decide,
    memRegion_split _ 3584 544 (by decide)]
  have e1 : sp - BitVec.ofNat 64 (3584 + 544) = sp - 4128#64 := by bv_arith
  have e2 : sp - 4128#64 + BitVec.ofNat 64 3584 = sp - BitVec.ofNat 64 544 := by bv_arith
  rw [e1, e2, sepConj_comm]

private theorem stackAt_pk_eq_alloc (sp : BitVec 64) :
    stackAt sp publicKeySerializeStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 4128#64) 32 := by
  simp only [stackAt, publicKeySerializeStack, allocHookStack]
  rw [show (4096 + 32 : Nat) = 32 + 4096 by decide,
    memRegion_split _ 32 4096 (by decide)]
  have e1 : sp - BitVec.ofNat 64 (32 + 4096) = sp - 4128#64 := by bv_arith
  have e2 : sp - 4128#64 + BitVec.ofNat 64 32 = sp - BitVec.ofNat 64 4096 := by bv_arith
  rw [e1, e2, sepConj_comm]

private def newFromSlicePkStackSpec (F : ShaCompress) : Spec NewFromSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.keyA ∧
      (s.readReg64 .x2).toNat = x.key.length ∧ x.key.length ≤ 64⌝ ∗
      memRegion x.ret 0x98 ∗ (x.keyA ↦ₛ x.key) ∗
      stackAt s.sp publicKeySerializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ret ↦₆₄ 0#64) ∗ hmacCoreAt F (x.ret + 8#64) x.key [] ∗
      (x.keyA ↦ₛ x.key) ∗
      stackAt s0.sp publicKeySerializeStack

private theorem newFromSlice_ok_at2_ext (img : Obj.Image) (C : Crypto)
    (ext : String → Option (State → State))
    (hnew : NewFromSliceOkExt img C ext)
    (entry : BitVec 64) (hfn : entry = (tripleRatchetProgAtExt img.base ext).fnAddr computeMacName) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      ((newFromSlicePkStackSpec C.F).inImage img) := by
  have heq : entry + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") = (tripleRatchetProgAtExt img.base ext).fnAddr newFromSliceName := by
    subst hfn
    dsimp only [tripleRatchetProgAtExt]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::compute_mac"),
      (ls_lemma% fnOff "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]")]
    bv_omega
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [heq] at hpc
  refine subroutine_ok.mono_outcome hnew x (memRegion (s0.sp - 4128#64) 3584 ∗ R) s0 hpc hrun
    (by simpa only [Spec.inImage, newFromSliceSpec, newFromSlicePkStackSpec,
      stackAt_pk_eq_nfs, sepConj_assoc] using hpre) hsp fun _ hraw => ?_
  unfold SubroutineOutcome at hraw ⊢
  simpa only [Spec.inImage, newFromSliceSpec, newFromSlicePkStackSpec,
    stackAt_pk_eq_nfs, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw


private def rustDeallocPkStackSpec (A : RustAlloc) : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (p, bs) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ (s.readReg64 .x2).toNat = 1⌝ ∗
      A.pool ∗ A.live p bs.length 1 ∗ (p ↦ₛ bs) ∗ stackAt s.sp publicKeySerializeStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp publicKeySerializeStack


private theorem dealloc_pkStack_ok_at2_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by
        fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustDeallocPkStackSpec A) := by
  have hdeel := hA.dealloc_ok_at (name := name) (k := k) hk
  refine subroutine_ok_outcome_intro fun ⟨p, bs⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (rustDeallocSpec A).pre (p, bs.length, 1) s0 ∗
      (memRegion (s0.sp - 4128#64) 32 ∗ R) := by
    simp only [rustDeallocSpec, rustDeallocPkStackSpec, stackAt_pk_eq_alloc,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    refine ⟨hpre.1, ?_⟩
    have hm : s0.mem ⊨ (p ↦ₛ bs) ∗ (A.pool ∗ A.live p bs.length 1 ∗
        stackAt s0.sp allocHookStack ∗ memRegion (s0.sp - 4128#64) 32 ∗ R) := by
      refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hpre.2
      ac_rfl
    have hm2 := Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion p bs)) hm
    refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hm2
    ac_rfl
  refine subroutine_ok.mono_outcome hdeel (p, bs.length, 1) (memRegion (s0.sp - 4128#64) 32 ∗ R) s0 hpc hrun hpre' hsp fun _ hraw => ?_
  unfold SubroutineOutcome at hraw ⊢
  simpa only [rustDeallocSpec, rustDeallocPkStackSpec,
    stackAt_pk_eq_alloc, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw


private theorem publicKeySerialize_ok_at2_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hpk : PublicKeySerializeOkExt b A ext)
    (entry : BitVec 64) (hfn : entry = (tripleRatchetProgAtExt b ext).fnAddr computeMacName) :
    subroutine_ok (tripleRatchetProgAtExt b ext) (entry + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      (publicKeySerializeSpec A) := by
  have heq : entry + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") = (tripleRatchetProgAtExt b ext).fnAddr publicKeySerializeName := by
    subst hfn
    dsimp only [tripleRatchetProgAtExt]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::compute_mac"),
      (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::serialize")]
    bv_omega
  exact heq ▸ hpk


def computeMacFramePad (sp : BitVec 64) : SepProp :=
  memRegion (sp - 200#64) 8 ∗ memRegion (sp - 128#64) 32

theorem cells_96_12_eq (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      ∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
      ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64, ∃∗ s6 : BitVec 64, ∃∗ s7 : BitVec 64,
      ∃∗ s8 : BitVec 64, ∃∗ s9 : BitVec 64, ∃∗ s10 : BitVec 64, ∃∗ s11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ s0) ∗ ((sp - 88#64) ↦₆₄ s1) ∗ ((sp - 80#64) ↦₆₄ s2) ∗ ((sp - 72#64) ↦₆₄ s3) ∗
        ((sp - 64#64) ↦₆₄ s4) ∗ ((sp - 56#64) ↦₆₄ s5) ∗ ((sp - 48#64) ↦₆₄ s6) ∗ ((sp - 40#64) ↦₆₄ s7) ∗
        ((sp - 32#64) ↦₆₄ s8) ∗ ((sp - 24#64) ↦₆₄ s9) ∗ ((sp - 16#64) ↦₆₄ s10) ∗ ((sp - 8#64) ↦₆₄ s11) := by
  cells_unfold

theorem cells_496_18_eq (sp : BitVec 64) :
    cells (sp - 496#64) 18 =
      ∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
      ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64, ∃∗ s6 : BitVec 64, ∃∗ s7 : BitVec 64,
      ∃∗ s8 : BitVec 64, ∃∗ s9 : BitVec 64, ∃∗ s10 : BitVec 64, ∃∗ s11 : BitVec 64,
      ∃∗ s12 : BitVec 64, ∃∗ s13 : BitVec 64, ∃∗ s14 : BitVec 64, ∃∗ s15 : BitVec 64,
      ∃∗ s16 : BitVec 64, ∃∗ s17 : BitVec 64,
        ((sp - 496#64) ↦₆₄ s0) ∗ ((sp - 488#64) ↦₆₄ s1) ∗ ((sp - 480#64) ↦₆₄ s2) ∗ ((sp - 472#64) ↦₆₄ s3) ∗
        ((sp - 464#64) ↦₆₄ s4) ∗ ((sp - 456#64) ↦₆₄ s5) ∗ ((sp - 448#64) ↦₆₄ s6) ∗ ((sp - 440#64) ↦₆₄ s7) ∗
        ((sp - 432#64) ↦₆₄ s8) ∗ ((sp - 424#64) ↦₆₄ s9) ∗ ((sp - 416#64) ↦₆₄ s10) ∗ ((sp - 408#64) ↦₆₄ s11) ∗
        ((sp - 400#64) ↦₆₄ s12) ∗ ((sp - 392#64) ↦₆₄ s13) ∗ ((sp - 384#64) ↦₆₄ s14) ∗ ((sp - 376#64) ↦₆₄ s15) ∗
        ((sp - 368#64) ↦₆₄ s16) ∗ ((sp - 360#64) ↦₆₄ s17) := by
  cells_unfold

theorem memRegion_192_64_eq (sp : BitVec 64) :
    memRegion (sp - 192#64) (8 * 8) =
      memRegion (sp - 192#64) 24 ∗
      memRegion (sp - 160#64) 24 ∗
      (∃∗ v, (sp - 168#64) ↦₆₄ v) ∗
      (∃∗ v, (sp - 136#64) ↦₆₄ v) := by
  rw [show (8 * 8 : Nat) = 24 + (8 + (24 + 8)) by decide,
    memRegion_split (sp - 192#64) 24 (8 + (24 + 8)) (by decide),
    memRegion_split (sp - 192#64 + 24#64) 8 (24 + 8) (by decide),
    memRegion_split (sp - 192#64 + 24#64 + 8#64) 24 8 (by decide)]
  have a1 : sp - 192#64 + 24#64 = sp - 168#64 := by bv_arith
  have a2 : sp - 168#64 + 8#64 = sp - 160#64 := by bv_arith
  have a3 : sp - 160#64 + 24#64 = sp - 136#64 := by bv_arith
  rw [a1, a2, a3,
    memRegion_cells (sp - 168#64) 1 (by decide),
    memRegion_cells (sp - 136#64) 1 (by decide)]
  simp only [cells, sepConj_emp]
  ac_rfl

theorem stackAt_computeMacAt_eq (pkStack : Nat) (hbound : pkStack + 496 < 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (pkStack + 496) =
      stackAt (sp - 496#64) pkStack ∗
      computeMacFramePad sp ∗
      cells (sp - 496#64) 18 ∗
      memRegion (sp - 352#64) 0x98 ∗
      memRegion (sp - 192#64) 24 ∗
      memRegion (sp - 160#64) 24 ∗
      (∃∗ v, (sp - 168#64) ↦₆₄ v) ∗
      (∃∗ v, (sp - 136#64) ↦₆₄ v) ∗
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
       ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64, ∃∗ s6 : BitVec 64, ∃∗ s7 : BitVec 64,
       ∃∗ s8 : BitVec 64, ∃∗ s9 : BitVec 64, ∃∗ s10 : BitVec 64, ∃∗ s11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ s0) ∗ ((sp - 88#64) ↦₆₄ s1) ∗ ((sp - 80#64) ↦₆₄ s2) ∗ ((sp - 72#64) ↦₆₄ s3) ∗
        ((sp - 64#64) ↦₆₄ s4) ∗ ((sp - 56#64) ↦₆₄ s5) ∗ ((sp - 48#64) ↦₆₄ s6) ∗ ((sp - 40#64) ↦₆₄ s7) ∗
        ((sp - 32#64) ↦₆₄ s8) ∗ ((sp - 24#64) ↦₆₄ s9) ∗ ((sp - 16#64) ↦₆₄ s10) ∗ ((sp - 8#64) ↦₆₄ s11)) := by
  unfold computeMacFramePad
  have hof : BitVec.ofNat 64 (pkStack + 496) = BitVec.ofNat 64 pkStack + 496#64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have htop : stackAt sp (pkStack + 496) =
      stackAt (sp - 496#64) pkStack ∗ memRegion (sp - 496#64) 496 := by
    simp only [stackAt]
    rw [memRegion_split _ pkStack 496 (Nat.le_of_lt hbound), hof]
    have e1 : sp - (BitVec.ofNat 64 pkStack + 496#64) =
        sp - 496#64 - BitVec.ofNat 64 pkStack := by bv_arith
    have e2 : sp - 496#64 - BitVec.ofNat 64 pkStack +
        BitVec.ofNat 64 pkStack = sp - 496#64 := by bv_arith
    rw [e1, e2]
  rw [htop]
  have hm496 : memRegion (sp - 496#64) 496 =
      memRegion (sp - 496#64) (8 * 18) ∗
      memRegion (sp - 352#64) 0x98 ∗
      memRegion (sp - 200#64) 8 ∗
      memRegion (sp - 192#64) (8 * 8) ∗
      memRegion (sp - 128#64) 32 ∗
      memRegion (sp - 96#64) (8 * 12) := by
    rw [show (496 : Nat) = 144 + (152 + (8 + (64 + (32 + 96)))) by decide,
      memRegion_split (sp - 496#64) 144 (152 + (8 + (64 + (32 + 96)))) (by decide),
      memRegion_split (sp - 496#64 + 144#64) 152 (8 + (64 + (32 + 96))) (by decide),
      memRegion_split (sp - 496#64 + 144#64 + 152#64) 8 (64 + (32 + 96)) (by decide),
      memRegion_split (sp - 496#64 + 144#64 + 152#64 + 8#64) 64 (32 + 96) (by decide),
      memRegion_split (sp - 496#64 + 144#64 + 152#64 + 8#64 + 64#64) 32 96 (by decide)]
    have a1 : sp - 496#64 + 144#64 = sp - 352#64 := by bv_arith
    have a2 : sp - 352#64 + 152#64 = sp - 200#64 := by bv_arith
    have a3 : sp - 200#64 + 8#64 = sp - 192#64 := by bv_arith
    have a4 : sp - 192#64 + 64#64 = sp - 128#64 := by bv_arith
    have a5 : sp - 128#64 + 32#64 = sp - 96#64 := by bv_arith
    rw [a1, a2, a3, a4, a5]
  rw [hm496, memRegion_cells (sp - 496#64) 18 (by decide),
    memRegion_192_64_eq sp,
    memRegion_cells (sp - 96#64) 12 (by decide),
    cells_96_12_eq sp]
  ac_rfl

theorem stackAt_computeMac_eq (sp : BitVec 64) :
    stackAt sp computeMacStack =
      stackAt (sp - 496#64) publicKeySerializeStack ∗
      computeMacFramePad sp ∗
      cells (sp - 496#64) 18 ∗
      memRegion (sp - 352#64) 0x98 ∗
      memRegion (sp - 192#64) 24 ∗
      memRegion (sp - 160#64) 24 ∗
      (∃∗ v, (sp - 168#64) ↦₆₄ v) ∗
      (∃∗ v, (sp - 136#64) ↦₆₄ v) ∗
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
       ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64, ∃∗ s6 : BitVec 64, ∃∗ s7 : BitVec 64,
       ∃∗ s8 : BitVec 64, ∃∗ s9 : BitVec 64, ∃∗ s10 : BitVec 64, ∃∗ s11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ s0) ∗ ((sp - 88#64) ↦₆₄ s1) ∗ ((sp - 80#64) ↦₆₄ s2) ∗ ((sp - 72#64) ↦₆₄ s3) ∗
        ((sp - 64#64) ↦₆₄ s4) ∗ ((sp - 56#64) ↦₆₄ s5) ∗ ((sp - 48#64) ↦₆₄ s6) ∗ ((sp - 40#64) ↦₆₄ s7) ∗
        ((sp - 32#64) ↦₆₄ s8) ∗ ((sp - 24#64) ↦₆₄ s9) ∗ ((sp - 16#64) ↦₆₄ s10) ∗ ((sp - 8#64) ↦₆₄ s11)) :=
  stackAt_computeMacAt_eq publicKeySerializeStack (by decide) sp

private theorem hmacCoreAt_nil_eq_words64 (F : ShaCompress) (a : BitVec 64) (key : List (BitVec 8)) :
    hmacCoreAt F a key [] =
      ∃∗ pad : { l : List (BitVec 8) // l.length = 63 },
        hmacWords64At a (hmacInnerInit F key) 1 (hmacOuterInit F key) [] pad.1 := by
  rw [hmacCoreAt, hmacStateAt_eq_words64]
  simp only [List.length_nil, Nat.sub_zero]
  exact ProofLib.Entails.antisymm
    (Entails.sepExists_elim fun pad =>
      Entails.pure_left fun ⟨_, hp⟩ =>
        Entails.sepExists_right ⟨pad, hp⟩ (Entails.refl _))
    (Entails.sepExists_elim fun ⟨pad, hp⟩ =>
      Entails.sepExists_right pad (Entails.pure_right ⟨by decide, hp⟩ (Entails.refl _)))

theorem pt64_cells_entails {a : BitVec 64} {n : Nat} (v : BitVec 64) {P : SepProp}
    (h : P ⊢ cells (a + 8#64) n) :
    (a ↦₆₄ v) ∗ P ⊢ cells a (n + 1) := by
  rw [cells]
  exact Entails.trans (sepConj_mono_right h) (Entails.sepExists_right v (Entails.refl _))

theorem pt64_cells_1 (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) ⊢ cells a 1 := by
  simp only [cells, sepConj_emp]
  exact Entails.sepExists_right v (Entails.refl _)

private theorem keyToBytes32_length (k : BitVec 256) :
    (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

theorem keyToBytes32_length_le_64 (k : BitVec 256) :
    (keyToBytes32 k).length ≤ 64 := by
  rw [keyToBytes32_length]; decide

theorem fold_19_words_352 (sp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : BitVec 64) :
    ((sp - 352#64) ↦₆₄ w0) ∗ ((sp - 344#64) ↦₆₄ w1) ∗ ((sp - 344#64 + 8#64) ↦₆₄ w2) ∗
    ((sp - 344#64 + 16#64) ↦₆₄ w3) ∗ ((sp - 344#64 + 24#64) ↦₆₄ w4) ∗ ((sp - 344#64 + 32#64) ↦₆₄ w5) ∗
    ((sp - 344#64 + 40#64) ↦₆₄ w6) ∗ ((sp - 344#64 + 48#64) ↦₆₄ w7) ∗ ((sp - 344#64 + 56#64) ↦₆₄ w8) ∗
    ((sp - 344#64 + 64#64) ↦₆₄ w9) ∗ ((sp - 344#64 + 72#64) ↦₆₄ w10) ∗ ((sp - 344#64 + 80#64) ↦₆₄ w11) ∗
    ((sp - 344#64 + 88#64) ↦₆₄ w12) ∗ ((sp - 344#64 + 96#64) ↦₆₄ w13) ∗ ((sp - 344#64 + 104#64) ↦₆₄ w14) ∗
    ((sp - 344#64 + 112#64) ↦₆₄ w15) ∗ ((sp - 344#64 + 120#64) ↦₆₄ w16) ∗ ((sp - 344#64 + 128#64) ↦₆₄ w17) ∗
    ((sp - 344#64 + 136#64) ↦₆₄ w18) ⊢
      memRegion (sp - 352#64) 0x98 := by
  rw [show (0x98 : Nat) = 8 * 19 by decide, memRegion_cells (sp - 352#64) 19 (by decide)]
  have h344 : sp - 352#64 + 8#64 = sp - 344#64 := by bv_arith
  refine pt64_cells_entails w0 ?_; rw [h344]
  refine pt64_cells_entails w1 ?_
  refine pt64_cells_entails w2 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w3 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w4 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w5 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w6 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w7 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w8 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w9 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w10 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w11 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w12 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w13 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w14 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w15 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w16 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w17 ?_; simp only [arm64_norm]
  exact pt64_cells_1 (sp - 344#64 + 136#64) w18

theorem fold_18_words_496 (sp : BitVec 64)
    (hS : ShaState) (hB : Nat) (oS : ShaState) (pad : List (BitVec 8))
    (hpad : pad.length = 63) :
    ((sp - 496#64) ↦₆₄ bytesToU64LE ((hmacBufBytes [] pad).take 8)) ∗
    ((sp - 488#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 8).take 8)) ∗
    ((sp - 480#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 16).take 8)) ∗
    ((sp - 472#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 24).take 8)) ∗
    ((sp - 464#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 32).take 8)) ∗
    ((sp - 456#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 40).take 8)) ∗
    ((sp - 448#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 48).take 8)) ∗
    ((sp - 440#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 56).take 8)) ∗
    ((sp - 432#64) ↦₆₄ bytesToU64LE ((shaStateBytes hS).take 8)) ∗
    ((sp - 424#64) ↦₆₄ bytesToU64LE (((shaStateBytes hS).drop 8).take 8)) ∗
    ((sp - 416#64) ↦₆₄ bytesToU64LE (((shaStateBytes hS).drop 16).take 8)) ∗
    ((sp - 408#64) ↦₆₄ bytesToU64LE (((shaStateBytes hS).drop 24).take 8)) ∗
    ((sp - 400#64) ↦₆₄ BitVec.ofNat 64 hB) ∗
    ((sp - 392#64) ↦₆₄ bytesToU64LE ((shaStateBytes oS).take 8)) ∗
    ((sp - 384#64) ↦₆₄ bytesToU64LE (((shaStateBytes oS).drop 8).take 8)) ∗
    ((sp - 376#64) ↦₆₄ bytesToU64LE (((shaStateBytes oS).drop 16).take 8)) ∗
    ((sp - 368#64) ↦₆₄ bytesToU64LE (((shaStateBytes oS).drop 24).take 8)) ∗
    ((sp - 360#64) ↦₆₄ 1#64) ⊢
      memRegion (sp - 496#64) 33 ∗
      memRegion (sp - 463#64) 30 ∗
      ((sp - 433#64) ↦₈ 0#8) ∗
      ((sp - 432#64) ↦ₛ shaStateBytes hS) ∗
      ((sp - 400#64) ↦₆₄ BitVec.ofNat 64 hB) ∗
      ((sp - 392#64) ↦ₛ shaStateBytes oS) ∗
      ((sp - 360#64) ↦₆₄ 1#64) := by
  have heq :
      ((sp - 496#64) ↦₆₄ bytesToU64LE ((hmacBufBytes [] pad).take 8)) ∗
      ((sp - 488#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 8).take 8)) ∗
      ((sp - 480#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 16).take 8)) ∗
      ((sp - 472#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 24).take 8)) ∗
      ((sp - 464#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 32).take 8)) ∗
      ((sp - 456#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 40).take 8)) ∗
      ((sp - 448#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 48).take 8)) ∗
      ((sp - 440#64) ↦₆₄ bytesToU64LE (((hmacBufBytes [] pad).drop 56).take 8)) ∗
      ((sp - 432#64) ↦₆₄ bytesToU64LE ((shaStateBytes hS).take 8)) ∗
      ((sp - 424#64) ↦₆₄ bytesToU64LE (((shaStateBytes hS).drop 8).take 8)) ∗
      ((sp - 416#64) ↦₆₄ bytesToU64LE (((shaStateBytes hS).drop 16).take 8)) ∗
      ((sp - 408#64) ↦₆₄ bytesToU64LE (((shaStateBytes hS).drop 24).take 8)) ∗
      ((sp - 400#64) ↦₆₄ BitVec.ofNat 64 hB) ∗
      ((sp - 392#64) ↦₆₄ bytesToU64LE ((shaStateBytes oS).take 8)) ∗
      ((sp - 384#64) ↦₆₄ bytesToU64LE (((shaStateBytes oS).drop 8).take 8)) ∗
      ((sp - 376#64) ↦₆₄ bytesToU64LE (((shaStateBytes oS).drop 16).take 8)) ∗
      ((sp - 368#64) ↦₆₄ bytesToU64LE (((shaStateBytes oS).drop 24).take 8)) ∗
      ((sp - 360#64) ↦₆₄ 1#64) =
      hmacWords64At (sp - 496#64) hS hB oS [] pad := by
    dsimp only [hmacWords64At]
    have a1 : sp - 496#64 + 8#64 = sp - 488#64 := by bv_arith
    have a2 : sp - 496#64 + 16#64 = sp - 480#64 := by bv_arith
    have a3 : sp - 496#64 + 24#64 = sp - 472#64 := by bv_arith
    have a4 : sp - 496#64 + 32#64 = sp - 464#64 := by bv_arith
    have a5 : sp - 496#64 + 40#64 = sp - 456#64 := by bv_arith
    have a6 : sp - 496#64 + 48#64 = sp - 448#64 := by bv_arith
    have a7 : sp - 496#64 + 56#64 = sp - 440#64 := by bv_arith
    have a8 : sp - 496#64 + 64#64 = sp - 432#64 := by bv_arith
    have a9 : sp - 496#64 + 72#64 = sp - 424#64 := by bv_arith
    have a10 : sp - 496#64 + 80#64 = sp - 416#64 := by bv_arith
    have a11 : sp - 496#64 + 88#64 = sp - 408#64 := by bv_arith
    have a12 : sp - 496#64 + 96#64 = sp - 400#64 := by bv_arith
    have a13 : sp - 496#64 + 104#64 = sp - 392#64 := by bv_arith
    have a14 : sp - 496#64 + 112#64 = sp - 384#64 := by bv_arith
    have a15 : sp - 496#64 + 120#64 = sp - 376#64 := by bv_arith
    have a16 : sp - 496#64 + 128#64 = sp - 368#64 := by bv_arith
    have a17 : sp - 496#64 + 136#64 = sp - 360#64 := by bv_arith
    rw [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17]
  rw [heq, hmacWords64At_eq (sp - 496#64) hS hB oS (by decide) (by simpa using hpad)]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.add_zero, pointsToBytes_nil,
    emp_sepConj, sepConj_assoc]
  have b1 : sp - 496#64 + 0x3f#64 = sp - 433#64 := by bv_arith
  have b2 : sp - 496#64 + 0x40#64 = sp - 432#64 := by bv_arith
  have b3 : sp - 496#64 + 0x60#64 = sp - 400#64 := by bv_arith
  have b4 : sp - 496#64 + 0x68#64 = sp - 392#64 := by bv_arith
  have b5 : sp - 496#64 + 0x88#64 = sp - 360#64 := by bv_arith
  rw [b1, b2, b3, b4, b5]
  have hm63 : memRegion (sp - 496#64) 63 =
      memRegion (sp - 496#64) 33 ∗ memRegion (sp - 463#64) 30 := by
    rw [show (63 : Nat) = 33 + 30 by decide,
      memRegion_split (sp - 496#64) 33 30 (by decide)]
    have ha : sp - 496#64 + 33#64 = sp - 463#64 := by bv_arith
    rw [ha]
  rw [← sepConj_assoc (memRegion (sp - 496#64) 33), ← hm63]
  exact sepConj_mono_left (hpad ▸ pointsToBytes_entails_memRegion (sp - 496#64) pad)

theorem allocFailedIn_of_trace_eq {s0 s sf : State} (htr : s.trace = s0.trace)
    (h : allocFailedIn s sf ∧ s.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at *
  rw [← htr]
  exact h

theorem spAligned_of_sub_496 {s : State} (sp0 : BitVec 64)
    (hsp : s.sp = sp0 - 496#64) (ha : (sp0 &&& 15#64 == 0#64) = true) :
    s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq] at ha ⊢
  bv_bits

theorem fold_pre_memcpy_31 (sp ptr2 : BitVec 64) (bs : List (BitVec 8)) (b : BitVec 8)
    (h : bs.length = 33) :
    memRegion (sp - 463#64) 30 ∗ ((sp - 433#64) ↦₈ b) ∗ (ptr2 ↦ₛ bs) ⊢
      memRegion (sp - 463#64) (bs.take 31).length ∗
      (ptr2 ↦ₛ bs.take 31) ∗ ((ptr2 + 31#64) ↦ₛ bs.drop 31) := by
  have htake : (bs.take 31).length = 31 := by simp [h]
  rw [htake]
  have hm31 : memRegion (sp - 463#64) 31 =
      memRegion (sp - 463#64) 30 ∗ memRegion (sp - 433#64) 1 := by
    rw [memRegion_split (sp - 463#64) 30 1 (by decide)]
    have ha : sp - 463#64 + 30#64 = sp - 433#64 := by bv_arith
    rw [ha]
  have hbs : (ptr2 ↦ₛ bs) = (ptr2 ↦ₛ bs.take 31) ∗ ((ptr2 + 31#64) ↦ₛ bs.drop 31) := by
    conv_lhs => rw [← List.take_append_drop 31 bs]
    rw [pointsToBytes_append, htake]
  rw [hm31, ← hbs, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_left (pointsTo8_entails_memRegion (sp - 433#64) b))

theorem fold_blk2 (sp : BitVec 64) (s1 s2 : List (BitVec 8)) (h1 : s1.length = 33) :
    ((sp - 496#64) ↦ₛ s1) ∗ ((sp - 463#64) ↦ₛ s2) ⊢
      ((sp - 496#64) ↦ₛ (s1 ++ s2)) := by
  rw [pointsToBytes_append, h1]
  have ha : sp - 496#64 + BitVec.ofNat 64 33 = sp - 463#64 := by bv_arith
  rw [ha]
  exact Entails.refl _

theorem fold_post_blk2 (sp : BitVec 64) (blk rbs : List (BitVec 8))
    (h : blk.length = 64 * 1) (hr : rbs.length = 33) :
    ((sp - 496#64) ↦ₛ blk) ⊢
      memRegion (sp - 496#64) (rbs.drop 31).length ∗
      memRegion (sp - 494#64) 61 ∗
      (∃∗ b63 : BitVec 8, (sp - 433#64) ↦₈ b63) := by
  have h64 : blk.length = 64 := by omega
  have hdrop : (rbs.drop 31).length = 2 := by simp [hr]
  rw [hdrop]
  have hm := h64 ▸ pointsToBytes_entails_memRegion (sp - 496#64) blk
  have hsplit : memRegion (sp - 496#64) 64 =
      memRegion (sp - 496#64) 2 ∗ memRegion (sp - 494#64) 61 ∗
      (∃∗ b63 : BitVec 8, (sp - 433#64) ↦₈ b63) := by
    rw [memRegion_split (sp - 496#64) 2 62 (by decide),
      memRegion_split (sp - 496#64 + 2#64) 61 1 (by decide),
      memRegion_one]
    have ha1 : sp - 496#64 + 2#64 = sp - 494#64 := by bv_arith
    have ha2 : sp - 494#64 + 61#64 = sp - 433#64 := by bv_arith
    rw [ha1, ha2]
  rwa [← hsplit]

theorem fold_rejoin_31 (ptr2 : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 33) :
    (ptr2 ↦ₛ bs.take 31) ∗ ((ptr2 + 31#64) ↦ₛ bs.drop 31) ⊢ (ptr2 ↦ₛ bs) := by
  have htake : (bs.take 31).length = 31 := by simp [h]
  conv_rhs => rw [← List.take_append_drop 31 bs]
  rw [pointsToBytes_append, htake]
  exact Entails.refl _

def mkMacEnv (sender receiver : IdentityKey) (macKey : BitVec 256)
    (message : List (BitVec 8)) : LibsignalHmac.MacEnv where
  base := 0
  sik  := 0
  rik  := 0
  key  := 0
  msg  := 0
  out  := 0
  sp0  := 0
  ret0 := 0
  vsik := ⟨sender.publicKey.serialize, by simp [PublicKey.serialize]⟩
  vrik := ⟨receiver.publicKey.serialize, by simp [PublicKey.serialize]⟩
  vkey := keyToBytes32 macKey
  vmsg := message

theorem mkMacEnv_hState_one (F : ShaCompress) (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    hmacInnerInit F (keyToBytes32 macKey) =
      (mkMacEnv sender receiver macKey message).hState F 1 := by
  have hk := keyToBytes32_length macKey
  rw [LibsignalHmac.MD.hState_one (mkMacEnv sender receiver macKey message) F hk]
  unfold hmacInnerInit hmacKeyBlock
  simp [mkMacEnv, LibsignalHmac.MacEnv.ipadKey, LibsignalHmac.MacEnv.k0, hk]

theorem mkMacEnv_oState1 (F : ShaCompress) (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    hmacOuterInit F (keyToBytes32 macKey) =
      (mkMacEnv sender receiver macKey message).oState1 F := by
  have hk := keyToBytes32_length macKey
  unfold hmacOuterInit hmacKeyBlock LibsignalHmac.MacEnv.oState1
  simp [mkMacEnv, LibsignalHmac.MacEnv.opadKey, LibsignalHmac.MacEnv.k0, hk]

theorem mkMacEnv_hState_two (F : ShaCompress) (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    (chunks64 (sender.publicKey.serialize ++ receiver.publicKey.serialize.take 31)).foldl F
      (hmacInnerInit F (keyToBytes32 macKey)) =
      (mkMacEnv sender receiver macKey message).hState F 2 := by
  have hk := keyToBytes32_length macKey
  have h64 : (sender.publicKey.serialize ++ receiver.publicKey.serialize.take 31).length = 64 := by
    simp [PublicKey.serialize]
  rw [chunks64_of_length_64 h64, List.foldl_cons, List.foldl_nil,
    mkMacEnv_hState_one F sender receiver macKey message,
    LibsignalHmac.MD.hState_two (mkMacEnv sender receiver macKey message) F hk]
  rfl

theorem fold_short_pre (sp : BitVec 64) (n : Nat) (h : n < 62) :
    memRegion (sp - 494#64) 61 ⊢
      memRegion (sp - 494#64) n ∗
      memRegion (sp - 494#64 + BitVec.ofNat 64 n) (61 - n) := by
  have hsplit : (61 : Nat) = n + (61 - n) := by omega
  conv_lhs => rw [hsplit, memRegion_split (sp - 494#64) n (61 - n) (by omega)]
  exact Entails.refl _

private theorem pure_sepConj_true {P : Prop} (h : P) (Q : SepProp) :
    ⌜P⌝ ∗ Q = Q := by
  simp only [pure_sepConj, h, true_and]

theorem pure_sepConj_true_shared_lb {P : Prop} (h : P) (Q : SepProp) :
    ⌜P⌝ ∗ Q = Q :=
  pure_sepConj_true h Q

theorem fold_short_post (F : ShaCompress) (sp : BitVec 64)
    (sender receiver : IdentityKey) (macKey : BitVec 256) (message : List (BitVec 8))
    (hshort : message.length < 62) (b63 : BitVec 8)
    (hb63 : b63 = BitVec.ofNat 8 (message.length + 2)) :
    let e := mkMacEnv sender receiver macKey message
    ((sp - 496#64) ↦ₛ receiver.publicKey.serialize.drop 31) ∗
    ((sp - 494#64) ↦ₛ message) ∗
    memRegion (sp - 494#64 + BitVec.ofNat 64 message.length) (61 - message.length) ∗
    ((sp - 433#64) ↦₈ b63) ∗
    ((sp - 432#64) ↦ₛ shaStateBytes (e.hState F 2)) ∗
    ((sp - 400#64) ↦₆₄ 2#64) ∗
    ((sp - 392#64) ↦ₛ shaStateBytes (e.oState1 F)) ∗
    ((sp - 360#64) ↦₆₄ 1#64) ⊢
    hmacStateAt (sp - 496#64) (e.hState F e.innerB) e.innerB (e.oState1 F) e.innerTail := by
  intro e
  have hk := keyToBytes32_length macKey
  obtain ⟨hb, hp, htail⟩ := LibsignalHmac.MD.short e hk (by dsimp [e, mkMacEnv]; omega)
  have htail_len : e.innerTail.length = message.length + 2 := by
    rw [htail]
    simp [e, mkMacEnv, PublicKey.serialize]
    omega
  have hlt64 : message.length + 2 < 64 := by omega
  have htail_pts :
      ((sp - 496#64) ↦ₛ e.innerTail) =
        ((sp - 496#64) ↦ₛ receiver.publicKey.serialize.drop 31) ∗
        ((sp - 494#64) ↦ₛ message) := by
    rw [htail]
    dsimp only [e, mkMacEnv, List.Vector.toList]
    rw [pointsToBytes_append]
    have hd2 : (receiver.publicKey.serialize.drop 31).length = 2 := by simp [PublicKey.serialize]
    have ha : sp - 496#64 + BitVec.ofNat 64 (receiver.publicKey.serialize.drop 31).length = sp - 494#64 := by
      rw [hd2]; bv_arith
    rw [ha]
  have ha_pad : sp - 496#64 + BitVec.ofNat 64 e.innerTail.length =
      sp - 494#64 + BitVec.ofNat 64 message.length := by
    rw [htail_len]; bv_omega
  have h_pad_len : 63 - e.innerTail.length = 61 - message.length := by omega
  have hb1 : sp - 496#64 + 0x3f#64 = sp - 433#64 := by bv_arith
  have hb2 : sp - 496#64 + 0x40#64 = sp - 432#64 := by bv_arith
  have hb3 : sp - 496#64 + 0x60#64 = sp - 400#64 := by bv_arith
  have hb4 : sp - 496#64 + 0x68#64 = sp - 392#64 := by bv_arith
  have hb5 : sp - 496#64 + 0x88#64 = sp - 360#64 := by bv_arith
  unfold hmacStateAt
  rw [hb, htail_pts, ha_pad, h_pad_len, hb1, hb2, hb3, hb4, hb5, htail_len, ← hb63,
    pure_sepConj_true hlt64]
  simp only [sepConj_assoc]
  exact Entails.refl _

private theorem bv64_ushiftRight_6 (x : BitVec 64) : x >>> 6 = x / 64#64 := by bv_bits
private theorem bv64_and_63 (x : BitVec 64) : x &&& 63#64 = x % 64#64 := by bv_bits
private theorem bv64_and_mask64 {x : BitVec 64} (h : x.ult 0x8000000000000000#64 = true) :
    x &&& 0x7fffffffffffffc0#64 = 64#64 * (x / 64#64) := by bv_bits

theorem ofNat64_div_64 {m : Nat} (hm : m < 2 ^ 64) :
    BitVec.ofNat 64 m / 64#64 = BitVec.ofNat 64 (m / 64) := by
  have hd : m / 64 < 2 ^ 64 := by omega
  have h64 : (64#64 : BitVec 64).toNat = 64 := rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, h64, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hd]

theorem ofNat64_mod_64 {m : Nat} (hm : m < 2 ^ 64) :
    BitVec.ofNat 64 m % 64#64 = BitVec.ofNat 64 (m % 64) := by
  have hd : m % 64 < 2 ^ 64 := by omega
  have h64 : (64#64 : BitVec 64).toNat = 64 := rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, h64, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hd]

theorem sub62_ushiftRight_6 {n : Nat} (hge : 62 ≤ n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n - 62#64) >>> 6 = BitVec.ofNat 64 ((n - 62) / 64) := by
  have hsub : BitVec.ofNat 64 n - 62#64 = BitVec.ofNat 64 (n - 62) := by bv_omega
  rw [hsub, bv64_ushiftRight_6, ofNat64_div_64 (by omega)]

theorem sub62_and_63 {n : Nat} (hge : 62 ≤ n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n - 62#64) &&& 63#64 = BitVec.ofNat 64 ((n - 62) % 64) := by
  have hsub : BitVec.ofNat 64 n - 62#64 = BitVec.ofNat 64 (n - 62) := by bv_omega
  rw [hsub, bv64_and_63, ofNat64_mod_64 (by omega)]

theorem sub62_and_mask64 {n : Nat} (hge : 62 ≤ n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n - 62#64) &&& 0x7fffffffffffffc0#64 =
      BitVec.ofNat 64 (64 * ((n - 62) / 64)) := by
  have hsub : BitVec.ofNat 64 n - 62#64 = BitVec.ofNat 64 (n - 62) := by bv_omega
  have hult : (BitVec.ofNat 64 (n - 62)).ult 0x8000000000000000#64 = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
    omega
  rw [hsub, bv64_and_mask64 hult, ofNat64_div_64 (by omega), ← BitVec.ofNat_mul]

theorem fold_long_pre_62 (sp msgA : BitVec 64) (message : List (BitVec 8))
    (b63 : BitVec 8) (hge : 62 ≤ message.length) :
    memRegion (sp - 494#64) 61 ∗ ((sp - 433#64) ↦₈ b63) ∗ (msgA ↦ₛ message) ⊢
      memRegion (sp - 494#64) (message.take 62).length ∗
      (msgA ↦ₛ message.take 62) ∗ ((msgA + 62#64) ↦ₛ message.drop 62) := by
  have htake : (message.take 62).length = 62 := by simp; omega
  rw [htake]
  have hm62 : memRegion (sp - 494#64) 62 =
      memRegion (sp - 494#64) 61 ∗ memRegion (sp - 433#64) 1 := by
    rw [memRegion_split (sp - 494#64) 61 1 (by decide)]
    have ha : sp - 494#64 + 61#64 = sp - 433#64 := by bv_arith
    rw [ha]
  have hmsg : (msgA ↦ₛ message) =
      (msgA ↦ₛ message.take 62) ∗ ((msgA + 62#64) ↦ₛ message.drop 62) := by
    conv_lhs => rw [← List.take_append_drop 62 message]
    rw [pointsToBytes_append, htake]
  rw [hm62, ← hmsg, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_left (pointsTo8_entails_memRegion (sp - 433#64) b63))

theorem fold_blk3 (sp : BitVec 64) (s1 s2 : List (BitVec 8)) (h1 : s1.length = 2) :
    ((sp - 496#64) ↦ₛ s1) ∗ ((sp - 494#64) ↦ₛ s2) ⊢
      ((sp - 496#64) ↦ₛ (s1 ++ s2)) := by
  rw [pointsToBytes_append, h1]
  have ha : sp - 496#64 + BitVec.ofNat 64 2 = sp - 494#64 := by bv_arith
  rw [ha]
  exact Entails.refl _

theorem mkMacEnv_hState_three (F : ShaCompress) (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) (hge : 62 ≤ message.length) :
    (chunks64 (receiver.publicKey.serialize.drop 31 ++ message.take 62)).foldl F
      ((mkMacEnv sender receiver macKey message).hState F 2) =
      ((mkMacEnv sender receiver macKey message).hState F 3) := by
  have hk := keyToBytes32_length macKey
  have h64 : (receiver.publicKey.serialize.drop 31 ++ message.take 62).length = 64 := by
    simp [PublicKey.serialize]; omega
  have hlong := (LibsignalHmac.MD.long (mkMacEnv sender receiver macKey message) F hk hge).1
  rw [chunks64_of_length_64 h64, List.foldl_cons, List.foldl_nil, hlong]
  rfl

theorem mkMacEnv_innerTail_eq (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) (hge : 62 ≤ message.length) :
    (mkMacEnv sender receiver macKey message).innerTail =
      message.drop (62 + 64 * (mkMacEnv sender receiver macKey message).nFull) :=
  (LibsignalHmac.MD.long (mkMacEnv sender receiver macKey message)
    (fun s _ => s) (keyToBytes32_length macKey) hge).2.2.2.2

theorem mkMacEnv_innerPos_eq (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) (hge : 62 ≤ message.length) :
    (mkMacEnv sender receiver macKey message).innerPos = (message.length - 62) % 64 :=
  (LibsignalHmac.MD.long (mkMacEnv sender receiver macKey message)
    (fun s _ => s) (keyToBytes32_length macKey) hge).2.2.1

theorem mkMacEnv_innerB_eq (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) (hge : 62 ≤ message.length) :
    (mkMacEnv sender receiver macKey message).innerB =
      3 + (mkMacEnv sender receiver macKey message).nFull :=
  (LibsignalHmac.MD.long (mkMacEnv sender receiver macKey message)
    (fun s _ => s) (keyToBytes32_length macKey) hge).2.1

theorem mkMacEnv_innerTail_length (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    (mkMacEnv sender receiver macKey message).innerTail.length =
      (mkMacEnv sender receiver macKey message).innerPos := by
  have hk := keyToBytes32_length macKey
  have hlen := LibsignalHmac.MD.innerMsg_length (mkMacEnv sender receiver macKey message) hk
  simp only [LibsignalHmac.MacEnv.innerTail, LibsignalHmac.MacEnv.innerB,
    LibsignalHmac.MacEnv.innerPos, List.length_drop]
  omega

theorem mkMacEnv_innerTail_length_lt (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    (mkMacEnv sender receiver macKey message).innerTail.length < 64 := by
  rw [mkMacEnv_innerTail_length]
  exact Nat.mod_lt _ (by decide)

theorem mkMacEnv_hState_full (F : ShaCompress) (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) (hge : 62 ≤ message.length) :
    (chunks64 ((message.drop 62).take
        (64 * (mkMacEnv sender receiver macKey message).nFull))).foldl F
      ((mkMacEnv sender receiver macKey message).hState F 3) =
      ((mkMacEnv sender receiver macKey message).hState F
        (mkMacEnv sender receiver macKey message).innerB) := by
  have hlong := LibsignalHmac.MD.long (mkMacEnv sender receiver macKey message)
    F (keyToBytes32_length macKey) hge
  rw [hlong.2.1, hlong.2.2.2.1]
  rfl

theorem fold_post_blk2_buf (sp : BitVec 64) (blk : List (BitVec 8))
    (h : blk.length = 64 * 1) :
    ((sp - 496#64) ↦ₛ blk) ⊢
      memRegion (sp - 496#64) 63 ∗
      (∃∗ b63 : BitVec 8, (sp - 433#64) ↦₈ b63) := by
  have h64 : blk.length = 64 := by omega
  have hm := h64 ▸ pointsToBytes_entails_memRegion (sp - 496#64) blk
  have hsplit : memRegion (sp - 496#64) 64 =
      memRegion (sp - 496#64) 63 ∗ (∃∗ b63 : BitVec 8, (sp - 433#64) ↦₈ b63) := by
    rw [memRegion_split (sp - 496#64) 63 1 (by decide), memRegion_one]
    have ha : sp - 496#64 + 63#64 = sp - 433#64 := by bv_arith
    rw [ha]
  rwa [← hsplit]

theorem fold_post_blk3 (sp msgA : BitVec 64) (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message blk3 : List (BitVec 8))
    (hblk : blk3.length = 64 * 1) (hge : 62 ≤ message.length) :
    ((sp - 496#64) ↦ₛ blk3) ∗ ((msgA + 62#64) ↦ₛ message.drop 62) ⊢
      memRegion (sp - 496#64) (mkMacEnv sender receiver macKey message).innerTail.length ∗
      memRegion
        (sp - 496#64 + BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerTail.length)
        (63 - (mkMacEnv sender receiver macKey message).innerTail.length) ∗
      (∃∗ b63 : BitVec 8, (sp - 433#64) ↦₈ b63) ∗
      ((msgA + 62#64) ↦ₛ
        (message.drop 62).take (64 * (mkMacEnv sender receiver macKey message).nFull)) ∗
      ((msgA + 62#64 + BitVec.ofNat 64 (64 * (mkMacEnv sender receiver macKey message).nFull)) ↦ₛ
        (mkMacEnv sender receiver macKey message).innerTail) := by
  have h1 := fold_post_blk2_buf sp blk3 hblk
  have hlt := mkMacEnv_innerTail_length_lt sender receiver macKey message
  have hm63 : memRegion (sp - 496#64) 63 =
      memRegion (sp - 496#64) (mkMacEnv sender receiver macKey message).innerTail.length ∗
      memRegion
        (sp - 496#64 + BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerTail.length)
        (63 - (mkMacEnv sender receiver macKey message).innerTail.length) := by
    have h63 : 63 = (mkMacEnv sender receiver macKey message).innerTail.length +
        (63 - (mkMacEnv sender receiver macKey message).innerTail.length) := by omega
    conv_lhs => rw [h63]
    exact memRegion_split (sp - 496#64)
      (mkMacEnv sender receiver macKey message).innerTail.length
      (63 - (mkMacEnv sender receiver macKey message).innerTail.length) (by omega)
  have htake_len :
      ((message.drop 62).take (64 * (mkMacEnv sender receiver macKey message).nFull)).length =
        64 * (mkMacEnv sender receiver macKey message).nFull := by
    rw [List.length_take, List.length_drop]
    exact Nat.min_eq_left (Nat.mul_div_le (message.length - 62) 64)
  have hdrop_eq :
      (message.drop 62).drop (64 * (mkMacEnv sender receiver macKey message).nFull) =
        (mkMacEnv sender receiver macKey message).innerTail := by
    rw [List.drop_drop, mkMacEnv_innerTail_eq sender receiver macKey message hge]
  have hmsg : ((msgA + 62#64) ↦ₛ message.drop 62) =
      ((msgA + 62#64) ↦ₛ
        (message.drop 62).take (64 * (mkMacEnv sender receiver macKey message).nFull)) ∗
      ((msgA + 62#64 + BitVec.ofNat 64 (64 * (mkMacEnv sender receiver macKey message).nFull)) ↦ₛ
        (mkMacEnv sender receiver macKey message).innerTail) := by
    conv_lhs =>
      rw [← List.take_append_drop (64 * (mkMacEnv sender receiver macKey message).nFull)
        (message.drop 62)]
    rw [pointsToBytes_append, htake_len, hdrop_eq]
  rw [hm63, sepConj_assoc] at h1
  rw [hmsg]
  refine Entails.trans (sepConj_mono_left h1) ?_
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem fold_rejoin_msg_long (msgA : BitVec 64) (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) (hge : 62 ≤ message.length) :
    (msgA ↦ₛ message.take 62) ∗
      ((msgA + 62#64) ↦ₛ
        (message.drop 62).take (64 * (mkMacEnv sender receiver macKey message).nFull)) ∗
      ((msgA + 62#64 + BitVec.ofNat 64 (64 * (mkMacEnv sender receiver macKey message).nFull)) ↦ₛ
        (mkMacEnv sender receiver macKey message).innerTail) ⊢
      (msgA ↦ₛ message) := by
  have htake62 : (message.take 62).length = 62 := by simp; omega
  have htake_len :
      ((message.drop 62).take (64 * (mkMacEnv sender receiver macKey message).nFull)).length =
        64 * (mkMacEnv sender receiver macKey message).nFull := by
    rw [List.length_take, List.length_drop]
    exact Nat.min_eq_left (Nat.mul_div_le (message.length - 62) 64)
  have hdrop_eq :
      (message.drop 62).drop (64 * (mkMacEnv sender receiver macKey message).nFull) =
        (mkMacEnv sender receiver macKey message).innerTail := by
    rw [List.drop_drop, mkMacEnv_innerTail_eq sender receiver macKey message hge]
  have hmsg2 : ((msgA + 62#64) ↦ₛ message.drop 62) =
      ((msgA + 62#64) ↦ₛ
        (message.drop 62).take (64 * (mkMacEnv sender receiver macKey message).nFull)) ∗
      ((msgA + 62#64 + BitVec.ofNat 64 (64 * (mkMacEnv sender receiver macKey message).nFull)) ↦ₛ
        (mkMacEnv sender receiver macKey message).innerTail) := by
    conv_lhs =>
      rw [← List.take_append_drop (64 * (mkMacEnv sender receiver macKey message).nFull)
        (message.drop 62)]
    rw [pointsToBytes_append, htake_len, hdrop_eq]
  have hmsg1 : (msgA ↦ₛ message) =
      (msgA ↦ₛ message.take 62) ∗ ((msgA + 62#64) ↦ₛ message.drop 62) := by
    conv_lhs => rw [← List.take_append_drop 62 message]
    rw [pointsToBytes_append, htake62]
  rw [hmsg1, hmsg2]
  exact Entails.refl _

theorem fold_long_post (F : ShaCompress) (sp : BitVec 64)
    (sender receiver : IdentityKey) (macKey : BitVec 256) (message : List (BitVec 8))
    (b_pos : BitVec 8) (blk_word : BitVec 64)
    (hb_pos : b_pos = BitVec.ofNat 8 (mkMacEnv sender receiver macKey message).innerTail.length)
    (hblk_word : blk_word = BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB) :
    ((sp - 496#64) ↦ₛ (mkMacEnv sender receiver macKey message).innerTail) ∗
      memRegion
        (sp - 496#64 + BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerTail.length)
        (63 - (mkMacEnv sender receiver macKey message).innerTail.length) ∗
      ((sp - 433#64) ↦₈ b_pos) ∗
      ((sp - 432#64) ↦ₛ LibsignalHmac.shaStateBytes
        ((mkMacEnv sender receiver macKey message).hState F
          (mkMacEnv sender receiver macKey message).innerB)) ∗
      ((sp - 400#64) ↦₆₄ blk_word) ∗
      ((sp - 392#64) ↦ₛ LibsignalHmac.shaStateBytes
        ((mkMacEnv sender receiver macKey message).oState1 F)) ∗
      ((sp - 360#64) ↦₆₄ 1#64) ⊢
      hmacStateAt (sp - 496#64)
        ((mkMacEnv sender receiver macKey message).hState F
          (mkMacEnv sender receiver macKey message).innerB)
        (mkMacEnv sender receiver macKey message).innerB
        ((mkMacEnv sender receiver macKey message).oState1 F)
        (mkMacEnv sender receiver macKey message).innerTail := by
  unfold hmacStateAt
  have hlt := mkMacEnv_innerTail_length_lt sender receiver macKey message
  have ha3f : sp - 496#64 + 0x3f#64 = sp - 433#64 := by bv_arith
  have ha40 : sp - 496#64 + 0x40#64 = sp - 432#64 := by bv_arith
  have ha60 : sp - 496#64 + 0x60#64 = sp - 400#64 := by bv_arith
  have ha68 : sp - 496#64 + 0x68#64 = sp - 392#64 := by bv_arith
  have ha88 : sp - 496#64 + 0x88#64 = sp - 360#64 := by bv_arith
  rw [ha3f, ha40, ha60, ha68, ha88, hb_pos, hblk_word, pure_sepConj_true hlt]
  exact Entails.refl _

def RegsSaved (s sf : State) : Prop :=
  sf.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
  sf.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
  sf.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
  sf.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
  sf.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
  sf.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
  sf.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
  sf.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
  sf.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
  sf.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
  sf.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5) ∧
  calleeSavedVRegs sf = calleeSavedVRegs s

theorem regsSaved_of_calleeSavedPreserved {s sf : State} (h : CalleeSavedPreserved s sf) :
    RegsSaved s sf :=
  h

theorem call_pk_serialize {prog : Program} {ret callee : BitVec 64}
    {A : RustAlloc} {s0 s : State} {P F R : SepProp} {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog callee (publicKeySerializeSpec A))
    (ret_pc sp_cur keyA : BitVec 64) (key : PublicKey)
    (hP : P = ((keyA ↦ₛ key.bytes.toList) ∗ A.pool ∗
      stackAt sp_cur publicKeySerializeStack) ∗ F)
    (hside : s.pc = callee ∧ s.status = .Running ∧ s.spAligned = true ∧
      s.sp = sp_cur ∧ s.readReg64 Reg.lr = ret_pc ∧ s.trace = s0.trace ∧
      s.readReg64 (Reg.gpr 0#5) = keyA)
    (hnext : ∀ (sf : State),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_cur → RegsSaved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0 → sf.readReg64 (Reg.gpr 1#5) = 33#64 →
      sf.trace = s0.trace →
      SepWPp prog ret sf
        ((keyA ↦ₛ key.bytes.toList) ∗
          A.live (sf.readReg64 (Reg.gpr 0#5)) key.serialize.length 1 ∗
          (sf.readReg64 (Reg.gpr 0#5) ↦ₛ key.serialize) ∗
          A.pool ∗ stackAt sp_cur publicKeySerializeStack ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  rcases hside with ⟨hpc, hrun, hsp, hsp_cur, hlr, htr, hφ⟩
  refine SepWPp.call_frame (x := ⟨keyA, key⟩) hcall hpc hrun hsp hlr
    (by simp only [publicKeySerializeSpec, hsp_cur, Reg.x0, sepConj_assoc]) hφ hP
    (fun sf code R' _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [publicKeySerializeSpec] at hm
      exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm)
    (fun sf hpcm hrunm hspm hcsm => ?_)
  have hne : key.serialize ≠ [] := by simp [PublicKey.serialize]
  conv =>
    arg 4
    simp only [publicKeySerializeSpec, boxU8Buf, hne, ite_false, hsp_cur, Reg.x0, Reg.x1,
      sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1, htr'⟩ => ?_
  conv =>
    arg 4
    rw [sepConj_left_comm (keyA ↦ₛ key.bytes.toList)]
  refine SepWPp.pure_elim fun ⟨hx0, _⟩ => ?_
  exact hnext sf hpcm hrunm (hspm.trans hsp_cur) (regsSaved_of_calleeSavedPreserved hcsm)
    hx0 hx1 (htr'.trans htr)

theorem fold_stk_192_64 (sp : BitVec 64) (v13 v12 : BitVec 64) :
    memRegion (sp - 192#64) 24 ∗ ((sp - 168#64) ↦₆₄ v13) ∗
      memRegion (sp - 160#64) 24 ∗ ((sp - 136#64) ↦₆₄ v12) ⊢
      memRegion (sp - 192#64) 64 := by
  have h1 : memRegion (sp - 192#64) 64 =
      memRegion (sp - 192#64) 24 ∗ memRegion (sp - 168#64) 8 ∗
      memRegion (sp - 160#64) 24 ∗ memRegion (sp - 136#64) 8 := by
    rw [memRegion_split (sp - 192#64) 24 (8 + (24 + 8)) (by decide),
      memRegion_split (sp - 192#64 + 24#64) 8 (24 + 8) (by decide),
      memRegion_split (sp - 192#64 + 24#64 + 8#64) 24 8 (by decide)]
    have a1 : sp - 192#64 + 24#64 = sp - 168#64 := by bv_arith
    have a2 : sp - 168#64 + 8#64 = sp - 160#64 := by bv_arith
    have a3 : sp - 160#64 + 24#64 = sp - 136#64 := by bv_arith
    rw [a1, a2, a3]
  rw [h1]
  exact sepConj_mono_right (sepConj_mono
    (pointsTo64_entails_memRegion (sp - 168#64) v13)
    (sepConj_mono_right (pointsTo64_entails_memRegion (sp - 136#64) v12)))

private theorem hmacStateAt_eq_words64_sub (a : BitVec 64) (innerSt : ShaState) (nBlocks : Nat)
    (outerSt : ShaState) (tail : List (BitVec 8)) (ht : tail.length < 64) :
    hmacStateAt a innerSt nBlocks outerSt tail =
      ∃∗ pad : { l : List (BitVec 8) // l.length = 63 - tail.length },
        hmacWords64At a innerSt nBlocks outerSt tail pad.1 := by
  rw [hmacStateAt_eq_words64]
  exact ProofLib.Entails.antisymm
    (Entails.sepExists_elim fun pad =>
      Entails.pure_left fun ⟨_, hp⟩ =>
        Entails.sepExists_right ⟨pad, hp⟩ (Entails.refl _))
    (Entails.sepExists_elim fun ⟨pad, hp⟩ =>
      Entails.sepExists_right pad (Entails.pure_right ⟨ht, hp⟩ (Entails.refl _)))

theorem cells_352_18_eq (sp : BitVec 64) :
    cells (sp - 352#64) 18 =
      ∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
      ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64, ∃∗ s6 : BitVec 64, ∃∗ s7 : BitVec 64,
      ∃∗ s8 : BitVec 64, ∃∗ s9 : BitVec 64, ∃∗ s10 : BitVec 64, ∃∗ s11 : BitVec 64,
      ∃∗ s12 : BitVec 64, ∃∗ s13 : BitVec 64, ∃∗ s14 : BitVec 64, ∃∗ s15 : BitVec 64,
      ∃∗ s16 : BitVec 64, ∃∗ s17 : BitVec 64,
        ((sp - 352#64) ↦₆₄ s0) ∗ ((sp - 344#64) ↦₆₄ s1) ∗ ((sp - 336#64) ↦₆₄ s2) ∗ ((sp - 328#64) ↦₆₄ s3) ∗
        ((sp - 320#64) ↦₆₄ s4) ∗ ((sp - 312#64) ↦₆₄ s5) ∗ ((sp - 304#64) ↦₆₄ s6) ∗ ((sp - 296#64) ↦₆₄ s7) ∗
        ((sp - 288#64) ↦₆₄ s8) ∗ ((sp - 280#64) ↦₆₄ s9) ∗ ((sp - 272#64) ↦₆₄ s10) ∗ ((sp - 264#64) ↦₆₄ s11) ∗
        ((sp - 256#64) ↦₆₄ s12) ∗ ((sp - 248#64) ↦₆₄ s13) ∗ ((sp - 240#64) ↦₆₄ s14) ∗ ((sp - 232#64) ↦₆₄ s15) ∗
        ((sp - 224#64) ↦₆₄ s16) ∗ ((sp - 216#64) ↦₆₄ s17) := by
  cells_unfold

theorem memRegion_352_152_eq (sp : BitVec 64) :
    memRegion (sp - 352#64) 0x98 =
      cells (sp - 352#64) 18 ∗ memRegion (sp - 208#64) 8 := by
  rw [show (0x98 : Nat) = 8 * 18 + 8 by decide,
    memRegion_split (sp - 352#64) (8 * 18) 8 (by decide),
    memRegion_cells (sp - 352#64) 18 (by decide)]
  have ha : sp - 352#64 + BitVec.ofNat 64 (8 * 18) = sp - 208#64 := by bv_arith
  rw [ha]

theorem word7_296_eq (sp : BitVec 64) {tail pad : List (BitVec 8)}
    (ht : tail.length < 64) (hp : pad.length = 63 - tail.length) :
    ((sp - 296#64) ↦₆₄ bytesToU64LE (((hmacBufBytes tail pad).drop 56).take 8)) =
      ((sp - 296#64) ↦ₛ (tail ++ pad).drop 56) ∗
      ((sp - 289#64) ↦₈ BitVec.ofNat 8 tail.length) := by
  have hlen63 : (tail ++ pad).length = 63 := by simp [hp]; omega
  have hdrop : ((hmacBufBytes tail pad).drop 56).take 8 =
      (tail ++ pad).drop 56 ++ [BitVec.ofNat 8 tail.length] := by
    unfold hmacBufBytes
    rw [List.drop_append_of_le_length (by omega),
      List.take_of_length_le (by simp [hlen63])]
  have hlen8 : (((hmacBufBytes tail pad).drop 56).take 8).length = 8 := by
    rw [hdrop]; simp [hlen63]
  rw [← pointsToBytes_8_eq_pointsTo64 (sp - 296#64) hlen8, hdrop,
    pointsToBytes_append]
  have hlen7 : ((tail ++ pad).drop 56).length = 7 := by simp [hlen63]
  have ha : sp - 296#64 + BitVec.ofNat 64 7 = sp - 289#64 := by bv_arith
  rw [hlen7, ha, ← pointsTo8_eq_pointsToBytes]

theorem zext64_ofNat8_eq {n : Nat} (hn : n < 64) :
    BitVec.zeroExtend 64 (BitVec.ofNat 8 n) = BitVec.ofNat 64 n := by
  bv_omega

private theorem bv64_xor_63 {x : BitVec 64} (h : x.ult 64#64 = true) :
    x ^^^ 63#64 = 63#64 - x := by bv_bits

theorem ofNat64_xor_63 {n : Nat} (hn : n < 64) :
    BitVec.ofNat 64 n ^^^ 63#64 = BitVec.ofNat 64 (63 - n) := by
  have hult : (BitVec.ofNat 64 n).ult 64#64 = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  rw [bv64_xor_63 hult]
  bv_omega

theorem bhi_7_false {n : Nat} (h : n ≤ 7) :
    ((!(BitVec.ofNat 64 n).ult 7#64) && !((BitVec.ofNat 64 n) == 7#64)) = false := by
  rcases Nat.lt_or_eq_of_le h with hlt | rfl
  · have h1 : (BitVec.ofNat 64 n).ult 7#64 = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    simp [h1]
  · simp

theorem fold_18_words_496_cells (sp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64) :
    ((sp - 496#64) ↦₆₄ w0) ∗ ((sp - 496#64 + 8#64) ↦₆₄ w1) ∗
    ((sp - 496#64 + 16#64) ↦₆₄ w2) ∗ ((sp - 496#64 + 24#64) ↦₆₄ w3) ∗
    ((sp - 496#64 + 32#64) ↦₆₄ w4) ∗ ((sp - 496#64 + 40#64) ↦₆₄ w5) ∗
    ((sp - 496#64 + 48#64) ↦₆₄ w6) ∗ ((sp - 496#64 + 56#64) ↦₆₄ w7) ∗
    ((sp - 496#64 + 64#64) ↦₆₄ w8) ∗ ((sp - 496#64 + 72#64) ↦₆₄ w9) ∗
    ((sp - 496#64 + 80#64) ↦₆₄ w10) ∗ ((sp - 496#64 + 88#64) ↦₆₄ w11) ∗
    ((sp - 496#64 + 96#64) ↦₆₄ w12) ∗ ((sp - 496#64 + 104#64) ↦₆₄ w13) ∗
    ((sp - 496#64 + 112#64) ↦₆₄ w14) ∗ ((sp - 496#64 + 120#64) ↦₆₄ w15) ∗
    ((sp - 496#64 + 128#64) ↦₆₄ w16) ∗ ((sp - 496#64 + 136#64) ↦₆₄ w17) ⊢
      cells (sp - 496#64) 18 := by
  refine pt64_cells_entails w0 ?_
  refine pt64_cells_entails w1 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w2 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w3 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w4 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w5 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w6 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w7 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w8 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w9 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w10 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w11 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w12 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w13 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w14 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w15 ?_; simp only [arm64_norm]
  refine pt64_cells_entails w16 ?_; simp only [arm64_norm]
  exact pt64_cells_1 (sp - 496#64 + 136#64) w17

theorem fold_post_copy_352 (sp : BitVec 64)
    (hS : ShaState) (hB : Nat) (oS : ShaState) {tail pad : List (BitVec 8)}
    (ht : tail.length < 64) (hp : pad.length = 63 - tail.length) :
    ((sp - 352#64) ↦₆₄ bytesToU64LE ((hmacBufBytes tail pad).take 8)) ∗
    ((sp - 344#64) ↦₆₄ bytesToU64LE (((hmacBufBytes tail pad).drop 8).take 8)) ∗
    ((sp - 336#64) ↦₆₄ bytesToU64LE (((hmacBufBytes tail pad).drop 16).take 8)) ∗
    ((sp - 328#64) ↦₆₄ bytesToU64LE (((hmacBufBytes tail pad).drop 24).take 8)) ∗
    ((sp - 320#64) ↦₆₄ bytesToU64LE (((hmacBufBytes tail pad).drop 32).take 8)) ∗
    ((sp - 312#64) ↦₆₄ bytesToU64LE (((hmacBufBytes tail pad).drop 40).take 8)) ∗
    ((sp - 304#64) ↦₆₄ bytesToU64LE (((hmacBufBytes tail pad).drop 48).take 8)) ∗
    ((sp - 296#64) ↦ₛ (tail ++ pad).drop 56) ∗
    ((sp - 289#64) ↦₈ BitVec.ofNat 8 tail.length) ∗
    ((sp - 288#64) ↦₆₄ bytesToU64LE ((shaStateBytes hS).take 8)) ∗
    ((sp - 280#64) ↦₆₄ bytesToU64LE (((shaStateBytes hS).drop 8).take 8)) ∗
    ((sp - 272#64) ↦₆₄ bytesToU64LE (((shaStateBytes hS).drop 16).take 8)) ∗
    ((sp - 264#64) ↦₆₄ bytesToU64LE (((shaStateBytes hS).drop 24).take 8)) ∗
    ((sp - 256#64) ↦₆₄ BitVec.ofNat 64 hB) ∗
    ((sp - 248#64) ↦₆₄ bytesToU64LE ((shaStateBytes oS).take 8)) ∗
    ((sp - 240#64) ↦₆₄ bytesToU64LE (((shaStateBytes oS).drop 8).take 8)) ∗
    ((sp - 232#64) ↦₆₄ bytesToU64LE (((shaStateBytes oS).drop 16).take 8)) ∗
    ((sp - 224#64) ↦₆₄ bytesToU64LE (((shaStateBytes oS).drop 24).take 8)) ∗
    ((sp - 216#64) ↦₆₄ 1#64) ⊢
      ((sp - 352#64) ↦ₛ tail) ∗
      (∃∗ b_pad0 : BitVec 8, (sp - 352#64 + BitVec.ofNat 64 tail.length) ↦₈ b_pad0) ∗
      memRegion (sp - 352#64 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length) ∗
      ((sp - 288#64) ↦ₛ shaStateBytes hS) ∗
      ((sp - 256#64) ↦₆₄ BitVec.ofNat 64 hB) ∗
      ((sp - 248#64) ↦ₛ shaStateBytes oS) ∗
      ((sp - 216#64) ↦₆₄ 1#64) := by
  have heq :
      ((sp - 352#64) ↦₆₄ bytesToU64LE ((hmacBufBytes tail pad).take 8)) ∗
      ((sp - 344#64) ↦₆₄ bytesToU64LE (((hmacBufBytes tail pad).drop 8).take 8)) ∗
      ((sp - 336#64) ↦₆₄ bytesToU64LE (((hmacBufBytes tail pad).drop 16).take 8)) ∗
      ((sp - 328#64) ↦₆₄ bytesToU64LE (((hmacBufBytes tail pad).drop 24).take 8)) ∗
      ((sp - 320#64) ↦₆₄ bytesToU64LE (((hmacBufBytes tail pad).drop 32).take 8)) ∗
      ((sp - 312#64) ↦₆₄ bytesToU64LE (((hmacBufBytes tail pad).drop 40).take 8)) ∗
      ((sp - 304#64) ↦₆₄ bytesToU64LE (((hmacBufBytes tail pad).drop 48).take 8)) ∗
      ((sp - 296#64) ↦ₛ (tail ++ pad).drop 56) ∗
      ((sp - 289#64) ↦₈ BitVec.ofNat 8 tail.length) ∗
      ((sp - 288#64) ↦₆₄ bytesToU64LE ((shaStateBytes hS).take 8)) ∗
      ((sp - 280#64) ↦₆₄ bytesToU64LE (((shaStateBytes hS).drop 8).take 8)) ∗
      ((sp - 272#64) ↦₆₄ bytesToU64LE (((shaStateBytes hS).drop 16).take 8)) ∗
      ((sp - 264#64) ↦₆₄ bytesToU64LE (((shaStateBytes hS).drop 24).take 8)) ∗
      ((sp - 256#64) ↦₆₄ BitVec.ofNat 64 hB) ∗
      ((sp - 248#64) ↦₆₄ bytesToU64LE ((shaStateBytes oS).take 8)) ∗
      ((sp - 240#64) ↦₆₄ bytesToU64LE (((shaStateBytes oS).drop 8).take 8)) ∗
      ((sp - 232#64) ↦₆₄ bytesToU64LE (((shaStateBytes oS).drop 16).take 8)) ∗
      ((sp - 224#64) ↦₆₄ bytesToU64LE (((shaStateBytes oS).drop 24).take 8)) ∗
      ((sp - 216#64) ↦₆₄ 1#64) =
      hmacWords64At (sp - 352#64) hS hB oS tail pad := by
    rw [← sepConj_assoc ((sp - 296#64) ↦ₛ (tail ++ pad).drop 56), ← word7_296_eq sp ht hp]
    dsimp only [hmacWords64At]
    have a1 : sp - 352#64 + 8#64 = sp - 344#64 := by bv_arith
    have a2 : sp - 352#64 + 16#64 = sp - 336#64 := by bv_arith
    have a3 : sp - 352#64 + 24#64 = sp - 328#64 := by bv_arith
    have a4 : sp - 352#64 + 32#64 = sp - 320#64 := by bv_arith
    have a5 : sp - 352#64 + 40#64 = sp - 312#64 := by bv_arith
    have a6 : sp - 352#64 + 48#64 = sp - 304#64 := by bv_arith
    have a7 : sp - 352#64 + 56#64 = sp - 296#64 := by bv_arith
    have a8 : sp - 352#64 + 64#64 = sp - 288#64 := by bv_arith
    have a9 : sp - 352#64 + 72#64 = sp - 280#64 := by bv_arith
    have a10 : sp - 352#64 + 80#64 = sp - 272#64 := by bv_arith
    have a11 : sp - 352#64 + 88#64 = sp - 264#64 := by bv_arith
    have a12 : sp - 352#64 + 96#64 = sp - 256#64 := by bv_arith
    have a13 : sp - 352#64 + 104#64 = sp - 248#64 := by bv_arith
    have a14 : sp - 352#64 + 112#64 = sp - 240#64 := by bv_arith
    have a15 : sp - 352#64 + 120#64 = sp - 232#64 := by bv_arith
    have a16 : sp - 352#64 + 128#64 = sp - 224#64 := by bv_arith
    have a17 : sp - 352#64 + 136#64 = sp - 216#64 := by bv_arith
    rw [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17]
  rw [heq, hmacWords64At_eq (sp - 352#64) hS hB oS ht hp]
  have b1 : sp - 352#64 + 0x3f#64 = sp - 289#64 := by bv_arith
  have b2 : sp - 352#64 + 0x40#64 = sp - 288#64 := by bv_arith
  have b3 : sp - 352#64 + 0x60#64 = sp - 256#64 := by bv_arith
  have b4 : sp - 352#64 + 0x68#64 = sp - 248#64 := by bv_arith
  have b5 : sp - 352#64 + 0x88#64 = sp - 216#64 := by bv_arith
  rw [b1, b2, b3, b4, b5]
  have hpad_ent :
      ((sp - 352#64 + BitVec.ofNat 64 tail.length) ↦ₛ pad) ∗
      ((sp - 289#64) ↦₈ BitVec.ofNat 8 tail.length) ⊢
      (∃∗ b_pad0 : BitVec 8, (sp - 352#64 + BitVec.ofNat 64 tail.length) ↦₈ b_pad0) ∗
      memRegion (sp - 352#64 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length) := by
    have ha_end : sp - 289#64 =
        (sp - 352#64 + BitVec.ofNat 64 tail.length) + BitVec.ofNat 64 (63 - tail.length) := by
      bv_omega
    have hm1 : ((sp - 352#64 + BitVec.ofNat 64 tail.length) ↦ₛ pad) ⊢
        memRegion (sp - 352#64 + BitVec.ofNat 64 tail.length) (63 - tail.length) := by
      rw [← hp]
      exact pointsToBytes_entails_memRegion (sp - 352#64 + BitVec.ofNat 64 tail.length) pad
    have hm2 := pointsTo8_entails_memRegion (sp - 289#64) (BitVec.ofNat 8 tail.length)
    have hsplit1 :
        memRegion (sp - 352#64 + BitVec.ofNat 64 tail.length) (63 - tail.length) ∗
        memRegion (sp - 289#64) 1 =
        memRegion (sp - 352#64 + BitVec.ofNat 64 tail.length) (64 - tail.length) := by
      rw [ha_end, ← memRegion_split (sp - 352#64 + BitVec.ofNat 64 tail.length)
        (63 - tail.length) 1 (by omega), show (63 - tail.length) + 1 = 64 - tail.length by omega]
    have hsplit2 :
        memRegion (sp - 352#64 + BitVec.ofNat 64 tail.length) (64 - tail.length) =
        (∃∗ b_pad0 : BitVec 8, (sp - 352#64 + BitVec.ofNat 64 tail.length) ↦₈ b_pad0) ∗
        memRegion (sp - 352#64 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length) := by
      rw [show 64 - tail.length = 1 + (63 - tail.length) by omega,
        memRegion_split (sp - 352#64 + BitVec.ofNat 64 tail.length) 1 (63 - tail.length) (by omega),
        memRegion_one]
    rw [← hsplit2, ← hsplit1]
    exact sepConj_mono hm1 hm2
  rw [← sepConj_assoc ((sp - 352#64 + BitVec.ofNat 64 tail.length) ↦ₛ pad),
    ← sepConj_assoc (∃∗ b_pad0 : BitVec 8, (sp - 352#64 + BitVec.ofNat 64 tail.length) ↦₈ b_pad0)]
  exact sepConj_mono_right (sepConj_mono_left hpad_ent)

theorem fold_post_memset_352 (sp : BitVec 64) (tail : List (BitVec 8)) :
    ((sp - 352#64) ↦ₛ tail) ∗
      ((sp - 352#64 + BitVec.ofNat 64 tail.length) ↦₈ 0x80#8) ∗
      ((sp - 352#64 + BitVec.ofNat 64 tail.length + 1#64) ↦ₛ
        List.replicate (63 - tail.length) 0#8) ⊢
      ((sp - 352#64) ↦ₛ (tail ++ [0x80#8] ++ List.replicate (63 - tail.length) 0#8)) := by
  rw [pointsToBytes_append, pointsToBytes_append, List.length_append, List.length_singleton,
    BitVec.ofNat_add, show (BitVec.ofNat 64 1 : BitVec 64) = 1#64 from rfl,
    ← BitVec.add_assoc, ← pointsTo8_eq_pointsToBytes, sepConj_assoc]
  exact Entails.refl _

theorem cells_192_8_eq (sp : BitVec 64) :
    memRegion (sp - 192#64) 64 =
      ∃∗ b0 : BitVec 64, ∃∗ b1 : BitVec 64, ∃∗ b2 : BitVec 64, ∃∗ b3 : BitVec 64,
      ∃∗ b4 : BitVec 64, ∃∗ b5 : BitVec 64, ∃∗ b6 : BitVec 64, ∃∗ b7 : BitVec 64,
        ((sp - 192#64) ↦₆₄ b0) ∗ ((sp - 184#64) ↦₆₄ b1) ∗ ((sp - 176#64) ↦₆₄ b2) ∗ ((sp - 168#64) ↦₆₄ b3) ∗
        ((sp - 160#64) ↦₆₄ b4) ∗ ((sp - 152#64) ↦₆₄ b5) ∗ ((sp - 144#64) ↦₆₄ b6) ∗ ((sp - 136#64) ↦₆₄ b7) := by
  rw [memRegion_cells (sp - 192#64) 8 (by decide)]
  cells_unfold

def words7At352 (sp : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ((sp - 352#64) ↦₆₄ bytesToU64LE (bs.take 8)) ∗
  ((sp - 344#64) ↦₆₄ bytesToU64LE ((bs.drop 8).take 8)) ∗
  ((sp - 336#64) ↦₆₄ bytesToU64LE ((bs.drop 16).take 8)) ∗
  ((sp - 328#64) ↦₆₄ bytesToU64LE ((bs.drop 24).take 8)) ∗
  ((sp - 320#64) ↦₆₄ bytesToU64LE ((bs.drop 32).take 8)) ∗
  ((sp - 312#64) ↦₆₄ bytesToU64LE ((bs.drop 40).take 8)) ∗
  ((sp - 304#64) ↦₆₄ bytesToU64LE ((bs.drop 48).take 8))

def words7At192 (sp : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ((sp - 192#64) ↦₆₄ bytesToU64LE (bs.take 8)) ∗
  ((sp - 184#64) ↦₆₄ bytesToU64LE ((bs.drop 8).take 8)) ∗
  ((sp - 176#64) ↦₆₄ bytesToU64LE ((bs.drop 16).take 8)) ∗
  ((sp - 168#64) ↦₆₄ bytesToU64LE ((bs.drop 24).take 8)) ∗
  ((sp - 160#64) ↦₆₄ bytesToU64LE ((bs.drop 32).take 8)) ∗
  ((sp - 152#64) ↦₆₄ bytesToU64LE ((bs.drop 40).take 8)) ∗
  ((sp - 144#64) ↦₆₄ bytesToU64LE ((bs.drop 48).take 8))

theorem list_eq_chunks8_of_len24 {α : Type} {bs : List α} (h : bs.length = 24) :
    bs = bs.take 8 ++ (bs.drop 8).take 8 ++ (bs.drop 16).take 8 := by
  have h1 : bs.drop 16 = (bs.drop 16).take 8 := by
    rw [List.take_of_length_le (by simp [h])]
  have h2 : bs.drop 8 = (bs.drop 8).take 8 ++ (bs.drop 16).take 8 := by
    conv_lhs => rw [← List.take_append_drop 8 (bs.drop 8)]
    rw [List.drop_drop, show 8 + 8 = 16 from rfl, ← h1]
  have h0 := (List.take_append_drop 8 bs).symm
  rw [h2] at h0
  simpa [List.append_assoc] using h0

theorem pointsToBytes_24_eq_words64 (a : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 24) :
    (a ↦ₛ bs) =
      (a ↦₆₄ bytesToU64LE (bs.take 8)) ∗
      ((a + 8#64) ↦₆₄ bytesToU64LE ((bs.drop 8).take 8)) ∗
      ((a + 16#64) ↦₆₄ bytesToU64LE ((bs.drop 16).take 8)) := by
  conv_lhs => rw [list_eq_chunks8_of_len24 h]
  simp only [pointsToBytes_append, List.length_append, List.length_take, List.length_drop, h,
    Nat.min_eq_left (by omega : 8 ≤ 24), Nat.min_eq_left (by omega : 8 ≤ 24 - 8),
    Nat.min_eq_left (by omega : 8 ≤ 24 - 16), BitVec.add_assoc, sepConj_assoc]
  rw [pointsToBytes_8_eq_pointsTo64 a (by simp [h]),
    pointsToBytes_8_eq_pointsTo64 (a + 8#64) (by simp [h]),
    pointsToBytes_8_eq_pointsTo64 (a + 16#64) (by simp [h])]

theorem pointsToBytes_56_eq_words64 (a : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 56) :
    (a ↦ₛ bs) =
      (a ↦₆₄ bytesToU64LE (bs.take 8)) ∗
      ((a + 8#64) ↦₆₄ bytesToU64LE ((bs.drop 8).take 8)) ∗
      ((a + 16#64) ↦₆₄ bytesToU64LE ((bs.drop 16).take 8)) ∗
      ((a + 24#64) ↦₆₄ bytesToU64LE ((bs.drop 24).take 8)) ∗
      ((a + 32#64) ↦₆₄ bytesToU64LE ((bs.drop 32).take 8)) ∗
      ((a + 40#64) ↦₆₄ bytesToU64LE ((bs.drop 40).take 8)) ∗
      ((a + 48#64) ↦₆₄ bytesToU64LE ((bs.drop 48).take 8)) := by
  have hlo : (bs.take 32).length = 32 := by simp [h]
  have hhi : (bs.drop 32).length = 24 := by simp [h]
  conv_lhs => rw [← List.take_append_drop 32 bs]
  rw [pointsToBytes_append, hlo,
    pointsToBytes_32_eq_words64 a hlo,
    pointsToBytes_24_eq_words64 (a + 32#64) hhi]
  simp only [List.take_take, List.drop_take, List.drop_drop, BitVec.add_assoc, sepConj_assoc]
  rfl

theorem pointsToBytes_56_eq_words7At352 (sp : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 56) :
    ((sp - 352#64) ↦ₛ bs) = words7At352 sp bs := by
  rw [pointsToBytes_56_eq_words64 (sp - 352#64) h]
  dsimp only [words7At352]
  have a1 : sp - 352#64 + 8#64 = sp - 344#64 := by bv_arith
  have a2 : sp - 352#64 + 16#64 = sp - 336#64 := by bv_arith
  have a3 : sp - 352#64 + 24#64 = sp - 328#64 := by bv_arith
  have a4 : sp - 352#64 + 32#64 = sp - 320#64 := by bv_arith
  have a5 : sp - 352#64 + 40#64 = sp - 312#64 := by bv_arith
  have a6 : sp - 352#64 + 48#64 = sp - 304#64 := by bv_arith
  rw [a1, a2, a3, a4, a5, a6]

theorem pointsToBytes_56_eq_words7At192 (sp : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 56) :
    ((sp - 192#64) ↦ₛ bs) = words7At192 sp bs := by
  rw [pointsToBytes_56_eq_words64 (sp - 192#64) h]
  dsimp only [words7At192]
  have a1 : sp - 192#64 + 8#64 = sp - 184#64 := by bv_arith
  have a2 : sp - 192#64 + 16#64 = sp - 176#64 := by bv_arith
  have a3 : sp - 192#64 + 24#64 = sp - 168#64 := by bv_arith
  have a4 : sp - 192#64 + 32#64 = sp - 160#64 := by bv_arith
  have a5 : sp - 192#64 + 40#64 = sp - 152#64 := by bv_arith
  have a6 : sp - 192#64 + 48#64 = sp - 144#64 := by bv_arith
  rw [a1, a2, a3, a4, a5, a6]

theorem fold_pad_lt_378 (F : ShaCompress) (sp : BitVec 64)
    (sender receiver : IdentityKey) (macKey : BitVec 256) (message : List (BitVec 8))
    (hp : (mkMacEnv sender receiver macKey message).innerPos < 56) :
    let e := mkMacEnv sender receiver macKey message
    ((sp - 352#64) ↦ₛ (e.innerTail ++ [0x80#8] ++ List.replicate (63 - e.innerPos) 0#8)) ∗
    ((sp - 288#64) ↦ₛ shaStateBytes (e.hState F e.innerB)) ⊢
    words7At352 sp ((e.innerPadded.drop (e.innerPadded.length - 64)).take 56) ∗
    (∃∗ w7 : BitVec 64, (sp - 296#64) ↦₆₄ w7) ∗
    ((sp - 288#64) ↦ₛ shaStateBytes
      ((chunks64 (e.innerPadded.take (e.innerPadded.length - 64))).foldl F sha256IV)) := by
  intro e
  have hk := keyToBytes32_length macKey
  obtain ⟨hdrop, hfold⟩ := LibsignalHmac.MD.pad_lt e F hk hp
  have htail_len : e.innerTail.length = e.innerPos :=
    mkMacEnv_innerTail_length sender receiver macKey message
  have hp' : e.innerPos < 56 := hp
  have h56_eq : (e.innerPadded.drop (e.innerPadded.length - 64)).take 56 =
      e.innerTail ++ [0x80#8] ++ List.replicate (55 - e.innerPos) 0#8 := by
    rw [hdrop, List.take_left' (by simp [htail_len]; omega)]
  have h56_len : ((e.innerPadded.drop (e.innerPadded.length - 64)).take 56).length = 56 := by
    rw [h56_eq]; simp [htail_len]; omega
  have hbuf_eq :
      e.innerTail ++ [0x80#8] ++ List.replicate (63 - e.innerPos) 0#8 =
      (e.innerPadded.drop (e.innerPadded.length - 64)).take 56 ++ List.replicate 8 0#8 := by
    rw [h56_eq, show 63 - e.innerPos = (55 - e.innerPos) + 8 by omega,
      List.replicate_add, ← List.append_assoc]
  have ha296 : sp - 352#64 + BitVec.ofNat 64 56 = sp - 296#64 := by bv_arith
  rw [hbuf_eq, pointsToBytes_append, h56_len, ha296,
    pointsToBytes_56_eq_words7At352 sp h56_len,
    pointsToBytes_8_eq_pointsTo64 (sp - 296#64) (by simp),
    hfold, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_left
    (Entails.sepExists_right (bytesToU64LE (List.replicate 8 0#8)) (Entails.refl _)))

theorem pointsToBytes_64_352_eq (sp : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 64) :
    ((sp - 352#64) ↦ₛ bs) =
      ((sp - 352#64) ↦₆₄ bytesToU64LE (bs.take 8)) ∗
      ((sp - 344#64) ↦₆₄ bytesToU64LE ((bs.drop 8).take 8)) ∗
      ((sp - 336#64) ↦₆₄ bytesToU64LE ((bs.drop 16).take 8)) ∗
      ((sp - 328#64) ↦₆₄ bytesToU64LE ((bs.drop 24).take 8)) ∗
      ((sp - 320#64) ↦₆₄ bytesToU64LE ((bs.drop 32).take 8)) ∗
      ((sp - 312#64) ↦₆₄ bytesToU64LE ((bs.drop 40).take 8)) ∗
      ((sp - 304#64) ↦₆₄ bytesToU64LE ((bs.drop 48).take 8)) ∗
      ((sp - 296#64) ↦₆₄ bytesToU64LE ((bs.drop 56).take 8)) := by
  rw [pointsToBytes_64_eq_words64 (sp - 352#64) h]
  have a1 : sp - 352#64 + 8#64 = sp - 344#64 := by bv_arith
  have a2 : sp - 352#64 + 16#64 = sp - 336#64 := by bv_arith
  have a3 : sp - 352#64 + 24#64 = sp - 328#64 := by bv_arith
  have a4 : sp - 352#64 + 32#64 = sp - 320#64 := by bv_arith
  have a5 : sp - 352#64 + 40#64 = sp - 312#64 := by bv_arith
  have a6 : sp - 352#64 + 48#64 = sp - 304#64 := by bv_arith
  have a7 : sp - 352#64 + 56#64 = sp - 296#64 := by bv_arith
  rw [a1, a2, a3, a4, a5, a6, a7]

theorem fold_8_words_192 (sp : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 64) :
    ((sp - 192#64) ↦₆₄ bytesToU64LE (bs.take 8)) ∗
    ((sp - 184#64) ↦₆₄ bytesToU64LE ((bs.drop 8).take 8)) ∗
    ((sp - 176#64) ↦₆₄ bytesToU64LE ((bs.drop 16).take 8)) ∗
    ((sp - 168#64) ↦₆₄ bytesToU64LE ((bs.drop 24).take 8)) ∗
    ((sp - 160#64) ↦₆₄ bytesToU64LE ((bs.drop 32).take 8)) ∗
    ((sp - 152#64) ↦₆₄ bytesToU64LE ((bs.drop 40).take 8)) ∗
    ((sp - 144#64) ↦₆₄ bytesToU64LE ((bs.drop 48).take 8)) ∗
    ((sp - 136#64) ↦₆₄ bytesToU64LE ((bs.drop 56).take 8)) ⊢
      ((sp - 192#64) ↦ₛ bs) := by
  rw [pointsToBytes_64_eq_words64 (sp - 192#64) h]
  have a1 : sp - 192#64 + 8#64 = sp - 184#64 := by bv_arith
  have a2 : sp - 192#64 + 16#64 = sp - 176#64 := by bv_arith
  have a3 : sp - 192#64 + 24#64 = sp - 168#64 := by bv_arith
  have a4 : sp - 192#64 + 32#64 = sp - 160#64 := by bv_arith
  have a5 : sp - 192#64 + 40#64 = sp - 152#64 := by bv_arith
  have a6 : sp - 192#64 + 48#64 = sp - 144#64 := by bv_arith
  have a7 : sp - 192#64 + 56#64 = sp - 136#64 := by bv_arith
  rw [a1, a2, a3, a4, a5, a6, a7]
  exact Entails.refl _

theorem fold_pad_ge_378 (F : ShaCompress) (sp : BitVec 64)
    (sender receiver : IdentityKey) (macKey : BitVec 256) (message : List (BitVec 8))
    (w7 : BitVec 64)
    (hp : 56 ≤ (mkMacEnv sender receiver macKey message).innerPos) :
    let e := mkMacEnv sender receiver macKey message
    let padBlk := e.innerTail ++ [0x80#8] ++ List.replicate (63 - e.innerPos) 0#8
    ((sp - 352#64) ↦₆₄ 0#64) ∗ ((sp - 344#64) ↦₆₄ 0#64) ∗
    ((sp - 336#64) ↦₆₄ 0#64) ∗ ((sp - 328#64) ↦₆₄ 0#64) ∗
    ((sp - 320#64) ↦₆₄ 0#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
    ((sp - 304#64) ↦₆₄ 0#64) ∗ ((sp - 296#64) ↦₆₄ w7) ∗
    ((sp - 192#64) ↦ₛ padBlk) ∗
    ((sp - 288#64) ↦ₛ shaStateBytes ((chunks64 padBlk).foldl F (e.hState F e.innerB))) ⊢
    words7At352 sp ((e.innerPadded.drop (e.innerPadded.length - 64)).take 56) ∗
    (∃∗ w7' : BitVec 64, (sp - 296#64) ↦₆₄ w7') ∗
    memRegion (sp - 192#64) 64 ∗
    ((sp - 288#64) ↦ₛ shaStateBytes
      ((chunks64 (e.innerPadded.take (e.innerPadded.length - 64))).foldl F sha256IV)) := by
  intro e padBlk
  have hk := keyToBytes32_length macKey
  obtain ⟨hdrop, hfold⟩ := LibsignalHmac.MD.pad_ge e F hk hp
  have htail_len : e.innerTail.length = e.innerPos :=
    mkMacEnv_innerTail_length sender receiver macKey message
  have htail_lt : e.innerPos < 64 := by
    rw [← htail_len]
    exact mkMacEnv_innerTail_length_lt sender receiver macKey message
  have hpadBlk_len : padBlk.length = 64 := by
    dsimp only [padBlk]; simp [htail_len]; omega
  have hst_eq : (chunks64 padBlk).foldl F (e.hState F e.innerB) =
      (chunks64 (e.innerPadded.take (e.innerPadded.length - 64))).foldl F sha256IV := by
    rw [chunks64_of_length_64 hpadBlk_len, List.foldl_cons, List.foldl_nil, hfold]
  have h56_eq : (e.innerPadded.drop (e.innerPadded.length - 64)).take 56 =
      List.replicate 56 0#8 := by
    rw [hdrop, List.take_left' (by simp)]
  have hw7 : words7At352 sp (List.replicate 56 0#8) =
      ((sp - 352#64) ↦₆₄ 0#64) ∗ ((sp - 344#64) ↦₆₄ 0#64) ∗
      ((sp - 336#64) ↦₆₄ 0#64) ∗ ((sp - 328#64) ↦₆₄ 0#64) ∗
      ((sp - 320#64) ↦₆₄ 0#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
      ((sp - 304#64) ↦₆₄ 0#64) := by
    dsimp only [words7At352]
    have z : bytesToU64LE (List.replicate 8 0#8) = 0#64 := by decide
    simp only [List.drop_replicate, List.take_replicate, Nat.min_eq_left (by decide : 8 ≤ 56),
      Nat.min_eq_left (by decide : 8 ≤ 56 - 8), Nat.min_eq_left (by decide : 8 ≤ 56 - 16),
      Nat.min_eq_left (by decide : 8 ≤ 56 - 24), Nat.min_eq_left (by decide : 8 ≤ 56 - 32),
      Nat.min_eq_left (by decide : 8 ≤ 56 - 40), Nat.min_eq_left (by decide : 8 ≤ 56 - 48), z]
  rw [hst_eq, h56_eq, hw7]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (Entails.sepExists_right w7 (Entails.refl _))
        (sepConj_mono_left
          (by simpa only [hpadBlk_len] using
            pointsToBytes_entails_memRegion (sp - 192#64) padBlk)))))))))

private theorem unpack64_eq_toLEBytes_8 (w : BitVec 64) : unpack64 w = toLEBytes 8 w := rfl

private theorem toBEBytes_len {w : Nat} (n : Nat) (x : BitVec w) : (toBEBytes n x).length = n := by
  simp [toBEBytes]

theorem innerHash_len (F : ShaCompress) (e : LibsignalHmac.MacEnv) :
    (e.innerHash F).length = 32 := by
  change (sha256With F e.innerMsg).length = 32
  unfold sha256With
  generalize ((chunks64 (sha256Pad e.innerMsg)).foldl F sha256IV) = st
  rcases st with ⟨l, hl⟩
  simp [List.length_flatMap, toBEBytes, hl]

theorem mkMacEnv_innerPadded_drop_eq (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    let e := mkMacEnv sender receiver macKey message
    e.innerPadded.drop (e.innerPadded.length - 64) =
      (e.innerPadded.drop (e.innerPadded.length - 64)).take 56 ++
        toBEBytes 8 (BitVec.ofNat 64 (8 * e.innerMsg.length)) ∧
    ((e.innerPadded.drop (e.innerPadded.length - 64)).take 56).length = 56 := by
  intro e
  have hk := keyToBytes32_length macKey
  have htail_len : e.innerTail.length = e.innerPos :=
    mkMacEnv_innerTail_length sender receiver macKey message
  by_cases hp : e.innerPos < 56
  · obtain ⟨hdrop, _⟩ := LibsignalHmac.MD.pad_lt e (fun s _ => s) hk hp
    have h56 : (e.innerPadded.drop (e.innerPadded.length - 64)).take 56 =
        e.innerTail ++ [0x80#8] ++ List.replicate (55 - e.innerPos) 0#8 := by
      rw [hdrop, List.take_left' (by simp [htail_len]; omega)]
    refine ⟨by rw [h56, hdrop], by rw [h56]; simp [htail_len]; omega⟩
  · have hge : 56 ≤ e.innerPos := by omega
    obtain ⟨hdrop, _⟩ := LibsignalHmac.MD.pad_ge e (fun s _ => s) hk hge
    have h56 : (e.innerPadded.drop (e.innerPadded.length - 64)).take 56 =
        List.replicate 56 0#8 := by
      rw [hdrop, List.take_left' (by simp)]
    refine ⟨by rw [h56, hdrop], by rw [h56]; simp⟩

theorem memRegion_352_64_pre_outer_eq (sp : BitVec 64) :
    memRegion (sp - 352#64) 64 =
      (∃∗ u7 : BitVec 32, ∃∗ u6 : BitVec 32, ∃∗ u5 : BitVec 32, ∃∗ u4 : BitVec 32,
       ∃∗ u3 : BitVec 32, ∃∗ u2 : BitVec 32, ∃∗ u1 : BitVec 32, ∃∗ u0 : BitVec 32,
        ((sp - 352#64) ↦₃₂ u0) ∗ ((sp - 348#64) ↦₃₂ u1) ∗
        ((sp - 344#64) ↦₃₂ u2) ∗ ((sp - 340#64) ↦₃₂ u3) ∗
        ((sp - 336#64) ↦₃₂ u4) ∗ ((sp - 332#64) ↦₃₂ u5) ∗
        ((sp - 328#64) ↦₃₂ u6) ∗ ((sp - 324#64) ↦₃₂ u7)) ∗
      (∃∗ b320 : BitVec 8, (sp - 320#64) ↦₈ b320) ∗
      (∃∗ z319 : BitVec 64, (sp - 319#64) ↦₆₄ z319) ∗
      (∃∗ z311 : BitVec 64, (sp - 311#64) ↦₆₄ z311) ∗
      memRegion (sp - 303#64) 15 := by
  have h32 : memRegion (sp - 352#64) 32 =
      ∃∗ u7 : BitVec 32, ∃∗ u6 : BitVec 32, ∃∗ u5 : BitVec 32, ∃∗ u4 : BitVec 32,
      ∃∗ u3 : BitVec 32, ∃∗ u2 : BitVec 32, ∃∗ u1 : BitVec 32, ∃∗ u0 : BitVec 32,
        ((sp - 352#64) ↦₃₂ u0) ∗ ((sp - 348#64) ↦₃₂ u1) ∗
        ((sp - 344#64) ↦₃₂ u2) ∗ ((sp - 340#64) ↦₃₂ u3) ∗
        ((sp - 336#64) ↦₃₂ u4) ∗ ((sp - 332#64) ↦₃₂ u5) ∗
        ((sp - 328#64) ↦₃₂ u6) ∗ ((sp - 324#64) ↦₃₂ u7) := by
    rw [memRegion_split (sp - 352#64) 4 28 (by decide),
      memRegion_split (sp - 352#64 + 4#64) 4 24 (by decide),
      memRegion_split (sp - 352#64 + 4#64 + 4#64) 4 20 (by decide),
      memRegion_split (sp - 352#64 + 4#64 + 4#64 + 4#64) 4 16 (by decide),
      memRegion_split (sp - 352#64 + 4#64 + 4#64 + 4#64 + 4#64) 4 12 (by decide),
      memRegion_split (sp - 352#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64) 4 8 (by decide),
      memRegion_split (sp - 352#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64) 4 4 (by decide)]
    have a1 : sp - 352#64 + 4#64 = sp - 348#64 := by bv_arith
    have a2 : sp - 348#64 + 4#64 = sp - 344#64 := by bv_arith
    have a3 : sp - 344#64 + 4#64 = sp - 340#64 := by bv_arith
    have a4 : sp - 340#64 + 4#64 = sp - 336#64 := by bv_arith
    have a5 : sp - 336#64 + 4#64 = sp - 332#64 := by bv_arith
    have a6 : sp - 332#64 + 4#64 = sp - 328#64 := by bv_arith
    have a7 : sp - 328#64 + 4#64 = sp - 324#64 := by bv_arith
    rw [a1, a2, a3, a4, a5, a6, a7,
      memRegion_four (sp - 352#64), memRegion_four (sp - 348#64),
      memRegion_four (sp - 344#64), memRegion_four (sp - 340#64),
      memRegion_four (sp - 336#64), memRegion_four (sp - 332#64),
      memRegion_four (sp - 328#64), memRegion_four (sp - 324#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  rw [memRegion_split (sp - 352#64) 32 32 (by decide),
    memRegion_split (sp - 352#64 + 32#64) 1 31 (by decide),
    memRegion_split (sp - 352#64 + 32#64 + 1#64) 8 23 (by decide),
    memRegion_split (sp - 352#64 + 32#64 + 1#64 + 8#64) 8 15 (by decide)]
  have b1 : sp - 352#64 + 32#64 = sp - 320#64 := by bv_arith
  have b2 : sp - 320#64 + 1#64 = sp - 319#64 := by bv_arith
  have b3 : sp - 319#64 + 8#64 = sp - 311#64 := by bv_arith
  have b4 : sp - 311#64 + 8#64 = sp - 303#64 := by bv_arith
  rw [b1, b2, b3, b4, h32, memRegion_one (sp - 320#64),
    memRegion_cells (sp - 319#64) 1 (by decide),
    memRegion_cells (sp - 311#64) 1 (by decide)]
  simp only [cells, sepConj_emp, sepConj_assoc]

theorem fold_pre_compress7_aux (sp : BitVec 64)
    (bs56 fullBlk : List (BitVec 8)) (msgBitLen : Nat) (x8 : BitVec 64)
    (h56_len : bs56.length = 56)
    (hdrop_eq : fullBlk = bs56 ++ toBEBytes 8 (BitVec.ofNat 64 msgBitLen))
    (hx8 : x8 = rev64 (BitVec.ofNat 64 msgBitLen)) :
    ((sp - 352#64) ↦₆₄ bytesToU64LE (bs56.take 8)) ∗
    ((sp - 344#64) ↦₆₄ bytesToU64LE ((bs56.drop 8).take 8)) ∗
    ((sp - 336#64) ↦₆₄ bytesToU64LE ((bs56.drop 16).take 8)) ∗
    ((sp - 328#64) ↦₆₄ bytesToU64LE ((bs56.drop 24).take 8)) ∗
    ((sp - 320#64) ↦₆₄ bytesToU64LE ((bs56.drop 32).take 8)) ∗
    ((sp - 312#64) ↦₆₄ bytesToU64LE ((bs56.drop 40).take 8)) ∗
    ((sp - 304#64) ↦₆₄ bytesToU64LE ((bs56.drop 48).take 8)) ∗
    ((sp - 296#64) ↦₆₄ x8) ∗
    ((sp - 192#64) ↦₆₄ bytesToU64LE (bs56.take 8)) ∗
    ((sp - 184#64) ↦₆₄ bytesToU64LE ((bs56.drop 8).take 8)) ∗
    ((sp - 176#64) ↦₆₄ bytesToU64LE ((bs56.drop 16).take 8)) ∗
    ((sp - 168#64) ↦₆₄ bytesToU64LE ((bs56.drop 24).take 8)) ∗
    ((sp - 160#64) ↦₆₄ bytesToU64LE ((bs56.drop 32).take 8)) ∗
    ((sp - 152#64) ↦₆₄ bytesToU64LE ((bs56.drop 40).take 8)) ∗
    ((sp - 144#64) ↦₆₄ bytesToU64LE ((bs56.drop 48).take 8)) ∗
    ((sp - 136#64) ↦₆₄ x8) ⊢
    memRegion (sp - 352#64) 64 ∗
    ((sp - 192#64) ↦ₛ fullBlk) := by
  have h352 :
      ((sp - 352#64) ↦₆₄ bytesToU64LE (bs56.take 8)) ∗
      ((sp - 344#64) ↦₆₄ bytesToU64LE ((bs56.drop 8).take 8)) ∗
      ((sp - 336#64) ↦₆₄ bytesToU64LE ((bs56.drop 16).take 8)) ∗
      ((sp - 328#64) ↦₆₄ bytesToU64LE ((bs56.drop 24).take 8)) ∗
      ((sp - 320#64) ↦₆₄ bytesToU64LE ((bs56.drop 32).take 8)) ∗
      ((sp - 312#64) ↦₆₄ bytesToU64LE ((bs56.drop 40).take 8)) ∗
      ((sp - 304#64) ↦₆₄ bytesToU64LE ((bs56.drop 48).take 8)) ∗
      ((sp - 296#64) ↦₆₄ x8) ⊢
      memRegion (sp - 352#64) 64 := by
    have hw8 :
        ((sp - 352#64) ↦₆₄ bytesToU64LE (bs56.take 8)) ∗
        ((sp - 344#64) ↦₆₄ bytesToU64LE ((bs56.drop 8).take 8)) ∗
        ((sp - 336#64) ↦₆₄ bytesToU64LE ((bs56.drop 16).take 8)) ∗
        ((sp - 328#64) ↦₆₄ bytesToU64LE ((bs56.drop 24).take 8)) ∗
        ((sp - 320#64) ↦₆₄ bytesToU64LE ((bs56.drop 32).take 8)) ∗
        ((sp - 312#64) ↦₆₄ bytesToU64LE ((bs56.drop 40).take 8)) ∗
        ((sp - 304#64) ↦₆₄ bytesToU64LE ((bs56.drop 48).take 8)) ∗
        ((sp - 296#64) ↦₆₄ x8) =
        words7At352 sp bs56 ∗ ((sp - 296#64) ↦₆₄ x8) := by
      dsimp only [words7At352]
      simp only [sepConj_assoc]
    have ha : sp - 352#64 + 56#64 = sp - 296#64 := by bv_arith
    have hm64 : memRegion (sp - 352#64) 64 =
        memRegion (sp - 352#64) 56 ∗ memRegion (sp - 296#64) 8 := by
      rw [memRegion_split (sp - 352#64) 56 8 (by decide), ha]
    rw [hw8, ← pointsToBytes_56_eq_words7At352 sp h56_len, hm64]
    refine sepConj_mono ?_ (pointsTo64_entails_memRegion (sp - 296#64) x8)
    simpa only [h56_len] using pointsToBytes_entails_memRegion (sp - 352#64) bs56
  have h192 :
      ((sp - 192#64) ↦₆₄ bytesToU64LE (bs56.take 8)) ∗
      ((sp - 184#64) ↦₆₄ bytesToU64LE ((bs56.drop 8).take 8)) ∗
      ((sp - 176#64) ↦₆₄ bytesToU64LE ((bs56.drop 16).take 8)) ∗
      ((sp - 168#64) ↦₆₄ bytesToU64LE ((bs56.drop 24).take 8)) ∗
      ((sp - 160#64) ↦₆₄ bytesToU64LE ((bs56.drop 32).take 8)) ∗
      ((sp - 152#64) ↦₆₄ bytesToU64LE ((bs56.drop 40).take 8)) ∗
      ((sp - 144#64) ↦₆₄ bytesToU64LE ((bs56.drop 48).take 8)) ∗
      ((sp - 136#64) ↦₆₄ x8) =
      ((sp - 192#64) ↦ₛ fullBlk) := by
    have ha : sp - 192#64 + BitVec.ofNat 64 56 = sp - 136#64 := by bv_arith
    have hx8_pts : ((sp - 136#64) ↦₆₄ x8) =
        ((sp - 136#64) ↦ₛ toBEBytes 8 (BitVec.ofNat 64 msgBitLen)) := by
      rw [hx8, ProofLib.pointsTo64_eq_pointsToBytes, unpack64_eq_toLEBytes_8,
        LibsignalHmac.OuterAux.toLEBytes_8_rev64]
    conv_rhs => rw [hdrop_eq]
    rw [pointsToBytes_append, h56_len, ha, ← hx8_pts,
      pointsToBytes_56_eq_words7At192 sp h56_len]
    dsimp only [words7At192]
    simp only [sepConj_assoc]
  have hassoc :
      ((sp - 352#64) ↦₆₄ bytesToU64LE (bs56.take 8)) ∗
      ((sp - 344#64) ↦₆₄ bytesToU64LE ((bs56.drop 8).take 8)) ∗
      ((sp - 336#64) ↦₆₄ bytesToU64LE ((bs56.drop 16).take 8)) ∗
      ((sp - 328#64) ↦₆₄ bytesToU64LE ((bs56.drop 24).take 8)) ∗
      ((sp - 320#64) ↦₆₄ bytesToU64LE ((bs56.drop 32).take 8)) ∗
      ((sp - 312#64) ↦₆₄ bytesToU64LE ((bs56.drop 40).take 8)) ∗
      ((sp - 304#64) ↦₆₄ bytesToU64LE ((bs56.drop 48).take 8)) ∗
      ((sp - 296#64) ↦₆₄ x8) ∗
      ((sp - 192#64) ↦₆₄ bytesToU64LE (bs56.take 8)) ∗
      ((sp - 184#64) ↦₆₄ bytesToU64LE ((bs56.drop 8).take 8)) ∗
      ((sp - 176#64) ↦₆₄ bytesToU64LE ((bs56.drop 16).take 8)) ∗
      ((sp - 168#64) ↦₆₄ bytesToU64LE ((bs56.drop 24).take 8)) ∗
      ((sp - 160#64) ↦₆₄ bytesToU64LE ((bs56.drop 32).take 8)) ∗
      ((sp - 152#64) ↦₆₄ bytesToU64LE ((bs56.drop 40).take 8)) ∗
      ((sp - 144#64) ↦₆₄ bytesToU64LE ((bs56.drop 48).take 8)) ∗
      ((sp - 136#64) ↦₆₄ x8) =
      (((sp - 352#64) ↦₆₄ bytesToU64LE (bs56.take 8)) ∗
       ((sp - 344#64) ↦₆₄ bytesToU64LE ((bs56.drop 8).take 8)) ∗
       ((sp - 336#64) ↦₆₄ bytesToU64LE ((bs56.drop 16).take 8)) ∗
       ((sp - 328#64) ↦₆₄ bytesToU64LE ((bs56.drop 24).take 8)) ∗
       ((sp - 320#64) ↦₆₄ bytesToU64LE ((bs56.drop 32).take 8)) ∗
       ((sp - 312#64) ↦₆₄ bytesToU64LE ((bs56.drop 40).take 8)) ∗
       ((sp - 304#64) ↦₆₄ bytesToU64LE ((bs56.drop 48).take 8)) ∗
       ((sp - 296#64) ↦₆₄ x8)) ∗
      (((sp - 192#64) ↦₆₄ bytesToU64LE (bs56.take 8)) ∗
       ((sp - 184#64) ↦₆₄ bytesToU64LE ((bs56.drop 8).take 8)) ∗
       ((sp - 176#64) ↦₆₄ bytesToU64LE ((bs56.drop 16).take 8)) ∗
       ((sp - 168#64) ↦₆₄ bytesToU64LE ((bs56.drop 24).take 8)) ∗
       ((sp - 160#64) ↦₆₄ bytesToU64LE ((bs56.drop 32).take 8)) ∗
       ((sp - 152#64) ↦₆₄ bytesToU64LE ((bs56.drop 40).take 8)) ∗
       ((sp - 144#64) ↦₆₄ bytesToU64LE ((bs56.drop 48).take 8)) ∗
       ((sp - 136#64) ↦₆₄ x8)) := by
    simp only [sepConj_assoc]
  rw [hassoc, h192]
  exact sepConj_mono_left h352

theorem fold_pre_compress7 (sp : BitVec 64)
    (sender receiver : IdentityKey) (macKey : BitVec 256) (message : List (BitVec 8))
    (x8 : BitVec 64)
    (hx8 : x8 = rev64 (BitVec.ofNat 64 (8 * (mkMacEnv sender receiver macKey message).innerMsg.length))) :
    let e := mkMacEnv sender receiver macKey message
    let bs56 := (e.innerPadded.drop (e.innerPadded.length - 64)).take 56
    ((sp - 352#64) ↦₆₄ bytesToU64LE (bs56.take 8)) ∗
    ((sp - 344#64) ↦₆₄ bytesToU64LE ((bs56.drop 8).take 8)) ∗
    ((sp - 336#64) ↦₆₄ bytesToU64LE ((bs56.drop 16).take 8)) ∗
    ((sp - 328#64) ↦₆₄ bytesToU64LE ((bs56.drop 24).take 8)) ∗
    ((sp - 320#64) ↦₆₄ bytesToU64LE ((bs56.drop 32).take 8)) ∗
    ((sp - 312#64) ↦₆₄ bytesToU64LE ((bs56.drop 40).take 8)) ∗
    ((sp - 304#64) ↦₆₄ bytesToU64LE ((bs56.drop 48).take 8)) ∗
    ((sp - 296#64) ↦₆₄ x8) ∗
    ((sp - 192#64) ↦₆₄ bytesToU64LE (bs56.take 8)) ∗
    ((sp - 184#64) ↦₆₄ bytesToU64LE ((bs56.drop 8).take 8)) ∗
    ((sp - 176#64) ↦₆₄ bytesToU64LE ((bs56.drop 16).take 8)) ∗
    ((sp - 168#64) ↦₆₄ bytesToU64LE ((bs56.drop 24).take 8)) ∗
    ((sp - 160#64) ↦₆₄ bytesToU64LE ((bs56.drop 32).take 8)) ∗
    ((sp - 152#64) ↦₆₄ bytesToU64LE ((bs56.drop 40).take 8)) ∗
    ((sp - 144#64) ↦₆₄ bytesToU64LE ((bs56.drop 48).take 8)) ∗
    ((sp - 136#64) ↦₆₄ x8) ⊢
    memRegion (sp - 352#64) 64 ∗
    ((sp - 192#64) ↦ₛ (e.innerPadded.drop (e.innerPadded.length - 64))) := by
  obtain ⟨hdrop_eq, h56_len⟩ := mkMacEnv_innerPadded_drop_eq sender receiver macKey message
  exact fold_pre_compress7_aux sp _ _ _ x8 h56_len hdrop_eq hx8

theorem pointsToBytes_shaStateBytes_288_eq (sp : BitVec 64) (st : ShaState) :
    ((sp - 288#64) ↦ₛ shaStateBytes st) =
      ((sp - 288#64) ↦₃₂ st.get 0) ∗ ((sp - 284#64) ↦₃₂ st.get 1) ∗
      ((sp - 280#64) ↦₃₂ st.get 2) ∗ ((sp - 276#64) ↦₃₂ st.get 3) ∗
      ((sp - 272#64) ↦₃₂ st.get 4) ∗ ((sp - 268#64) ↦₃₂ st.get 5) ∗
      ((sp - 264#64) ↦₃₂ st.get 6) ∗ ((sp - 260#64) ↦₃₂ st.get 7) := by
  rw [pointsToBytes_shaStateBytes_eq_32 (sp - 288#64) st]
  have a1 : sp - 288#64 + 4#64 = sp - 284#64 := by bv_arith
  have a2 : sp - 288#64 + 8#64 = sp - 280#64 := by bv_arith
  have a3 : sp - 288#64 + 12#64 = sp - 276#64 := by bv_arith
  have a4 : sp - 288#64 + 16#64 = sp - 272#64 := by bv_arith
  have a5 : sp - 288#64 + 20#64 = sp - 268#64 := by bv_arith
  have a6 : sp - 288#64 + 24#64 = sp - 264#64 := by bv_arith
  have a7 : sp - 288#64 + 28#64 = sp - 260#64 := by bv_arith
  rw [a1, a2, a3, a4, a5, a6, a7]

theorem pointsToBytes_shaStateBytes_248_eq (sp : BitVec 64) (st : ShaState) :
    ((sp - 248#64) ↦ₛ shaStateBytes st) =
      ((sp - 248#64) ↦₃₂ st.get 0) ∗ ((sp - 244#64) ↦₃₂ st.get 1) ∗
      ((sp - 240#64) ↦₃₂ st.get 2) ∗ ((sp - 236#64) ↦₃₂ st.get 3) ∗
      ((sp - 232#64) ↦₃₂ st.get 4) ∗ ((sp - 228#64) ↦₃₂ st.get 5) ∗
      ((sp - 224#64) ↦₃₂ st.get 6) ∗ ((sp - 220#64) ↦₃₂ st.get 7) := by
  rw [pointsToBytes_shaStateBytes_eq_32 (sp - 248#64) st]
  have a1 : sp - 248#64 + 4#64 = sp - 244#64 := by bv_arith
  have a2 : sp - 248#64 + 8#64 = sp - 240#64 := by bv_arith
  have a3 : sp - 248#64 + 12#64 = sp - 236#64 := by bv_arith
  have a4 : sp - 248#64 + 16#64 = sp - 232#64 := by bv_arith
  have a5 : sp - 248#64 + 20#64 = sp - 228#64 := by bv_arith
  have a6 : sp - 248#64 + 24#64 = sp - 224#64 := by bv_arith
  have a7 : sp - 248#64 + 28#64 = sp - 220#64 := by bv_arith
  rw [a1, a2, a3, a4, a5, a6, a7]

theorem pointsTo32_rev32_eq_toBEBytes (a : BitVec 64) (w : BitVec 32) :
    (a ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 w))) =
      (a ↦ₛ toBEBytes 4 w) := by
  rw [ProofLib.pointsTo32_eq_pointsToBytes, unpack32_eq_toLEBytes_4,
    LibsignalHmac.OuterAux.toLEBytes_4_rev32_64_truncate]

theorem fold_pad_320_at_1d408 (sp : BitVec 64) :
    ((sp - 320#64) ↦₈ 0x80#8) ∗ ((sp - 319#64) ↦₆₄ 0#64) ∗
    ((sp - 311#64) ↦₆₄ 0#64) ∗ memRegion (sp - 303#64) 15 ⊢
    ((sp - 320#64) ↦₆₄ 0x80#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
    (∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ((sp - 304#64) ↦₆₄ w6) ∗ ((sp - 296#64) ↦₆₄ w7)) := by
  have h17_lhs :
      ((sp - 320#64) ↦₈ 0x80#8) ∗ ((sp - 319#64) ↦₆₄ 0#64) ∗
      ((sp - 311#64) ↦₆₄ 0#64) =
      ((sp - 320#64) ↦ₛ ([0x80#8] ++ unpack64 0#64 ++ unpack64 0#64)) := by
    have a1 : sp - 320#64 + BitVec.ofNat 64 1 = sp - 319#64 := by bv_arith
    have a2 : sp - 320#64 + BitVec.ofNat 64 9 = sp - 311#64 := by bv_arith
    rw [pointsToBytes_append, pointsToBytes_append,
      show ([0x80#8] ++ unpack64 0#64).length = 9 by decide,
      show ([0x80#8] : List (BitVec 8)).length = 1 by decide,
      a1, a2, ← pointsTo8_eq_pointsToBytes, ← ProofLib.pointsTo64_eq_pointsToBytes,
      ← ProofLib.pointsTo64_eq_pointsToBytes, sepConj_assoc]
  have h17_bytes :
      [0x80#8] ++ unpack64 0#64 ++ unpack64 0#64 =
      unpack64 0x80#64 ++ unpack64 0#64 ++ [0#8] := by decide
  have h17_rhs :
      ((sp - 320#64) ↦ₛ (unpack64 0x80#64 ++ unpack64 0#64 ++ [0#8])) =
      ((sp - 320#64) ↦₆₄ 0x80#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
      ((sp - 304#64) ↦₈ 0#8) := by
    have a1 : sp - 320#64 + BitVec.ofNat 64 8 = sp - 312#64 := by bv_arith
    have a2 : sp - 320#64 + BitVec.ofNat 64 16 = sp - 304#64 := by bv_arith
    rw [pointsToBytes_append, pointsToBytes_append,
      show (unpack64 0x80#64 ++ unpack64 0#64).length = 16 by decide,
      show (unpack64 0x80#64).length = 8 by decide,
      a1, a2, ← ProofLib.pointsTo64_eq_pointsToBytes, ← ProofLib.pointsTo64_eq_pointsToBytes,
      ← pointsTo8_eq_pointsToBytes, sepConj_assoc]
  have hm16 :
      ((sp - 304#64) ↦₈ 0#8) ∗ memRegion (sp - 303#64) 15 ⊢
      ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ((sp - 304#64) ↦₆₄ w6) ∗ ((sp - 296#64) ↦₆₄ w7) := by
    have ha : sp - 304#64 + 1#64 = sp - 303#64 := by bv_arith
    have hsplit : memRegion (sp - 304#64) 16 =
        memRegion (sp - 304#64) 1 ∗ memRegion (sp - 303#64) 15 := by
      rw [memRegion_split (sp - 304#64) 1 15 (by decide), ha]
    have hcells : memRegion (sp - 304#64) 16 =
        ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
          ((sp - 304#64) ↦₆₄ w6) ∗ ((sp - 296#64) ↦₆₄ w7) := by
      rw [memRegion_cells (sp - 304#64) 2 (by decide)]
      cells_unfold
    rw [← hcells, hsplit]
    exact sepConj_mono_left (pointsTo8_entails_memRegion (sp - 304#64) 0#8)
  rw [← sepConj_assoc ((sp - 319#64) ↦₆₄ 0#64),
    ← sepConj_assoc ((sp - 320#64) ↦₈ 0x80#8),
    h17_lhs, h17_bytes, h17_rhs]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right hm16)

theorem fold_at_1d408_aux (sp : BitVec 64)
    (h_in : ShaState) (ih lastBlk : List (BitVec 8))
    (hih_eq : h_in.toList.flatMap (toBEBytes 4) = ih)
    (hih_len : ih.length = 32)
    (hdrop_len : lastBlk.length = 64) :
    ((sp - 352#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 0)))) ∗
    ((sp - 348#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 1)))) ∗
    ((sp - 344#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 2)))) ∗
    ((sp - 340#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 3)))) ∗
    ((sp - 336#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 4)))) ∗
    ((sp - 332#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 5)))) ∗
    ((sp - 328#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 6)))) ∗
    ((sp - 324#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 7)))) ∗
    ((sp - 320#64) ↦₈ 0x80#8) ∗ ((sp - 319#64) ↦₆₄ 0#64) ∗
    ((sp - 311#64) ↦₆₄ 0#64) ∗ memRegion (sp - 303#64) 15 ∗
    ((sp - 288#64) ↦₃₂ h_in.get 0) ∗ ((sp - 284#64) ↦₃₂ h_in.get 1) ∗
    ((sp - 280#64) ↦₃₂ h_in.get 2) ∗ ((sp - 276#64) ↦₃₂ h_in.get 3) ∗
    ((sp - 272#64) ↦₃₂ h_in.get 4) ∗ ((sp - 268#64) ↦₃₂ h_in.get 5) ∗
    ((sp - 264#64) ↦₃₂ h_in.get 6) ∗ ((sp - 260#64) ↦₃₂ h_in.get 7) ∗
    ((sp - 192#64) ↦ₛ lastBlk) ⊢
    ((sp - 352#64) ↦₆₄ bytesToU64LE (ih.take 8)) ∗
    ((sp - 344#64) ↦₆₄ bytesToU64LE ((ih.drop 8).take 8)) ∗
    ((sp - 336#64) ↦₆₄ bytesToU64LE ((ih.drop 16).take 8)) ∗
    ((sp - 328#64) ↦₆₄ bytesToU64LE ((ih.drop 24).take 8)) ∗
    ((sp - 320#64) ↦₆₄ 0x80#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
    (∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ((sp - 304#64) ↦₆₄ w6) ∗ ((sp - 296#64) ↦₆₄ w7)) ∗
    memRegion (sp - 288#64) 32 ∗
    memRegion (sp - 192#64) 64 := by
  have h352 :
      ((sp - 352#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 0)))) ∗
      ((sp - 348#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 1)))) ∗
      ((sp - 344#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 2)))) ∗
      ((sp - 340#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 3)))) ∗
      ((sp - 336#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 4)))) ∗
      ((sp - 332#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 5)))) ∗
      ((sp - 328#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 6)))) ∗
      ((sp - 324#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 7)))) =
      ((sp - 352#64) ↦₆₄ bytesToU64LE (ih.take 8)) ∗
      ((sp - 344#64) ↦₆₄ bytesToU64LE ((ih.drop 8).take 8)) ∗
      ((sp - 336#64) ↦₆₄ bytesToU64LE ((ih.drop 16).take 8)) ∗
      ((sp - 328#64) ↦₆₄ bytesToU64LE ((ih.drop 24).take 8)) := by
    have hbe :
        ((sp - 352#64) ↦ₛ ih) =
        ((sp - 352#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 0)))) ∗
        ((sp - 348#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 1)))) ∗
        ((sp - 344#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 2)))) ∗
        ((sp - 340#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 3)))) ∗
        ((sp - 336#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 4)))) ∗
        ((sp - 332#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 5)))) ∗
        ((sp - 328#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 6)))) ∗
        ((sp - 324#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 7)))) := by
      conv_lhs => rw [← hih_eq, LibsignalHmac.OuterAux.shaState_be_eq_append h_in]
      simp only [pointsToBytes_append, List.length_append, toBEBytes_len,
        ← pointsTo32_rev32_eq_toBEBytes, BitVec.add_assoc, sepConj_assoc]
      have a1 : sp - 352#64 + 4#64 = sp - 348#64 := by bv_arith
      have a2 : sp - 352#64 + 8#64 = sp - 344#64 := by bv_arith
      have a3 : sp - 352#64 + 12#64 = sp - 340#64 := by bv_arith
      have a4 : sp - 352#64 + 16#64 = sp - 336#64 := by bv_arith
      have a5 : sp - 352#64 + 20#64 = sp - 332#64 := by bv_arith
      have a6 : sp - 352#64 + 24#64 = sp - 328#64 := by bv_arith
      have a7 : sp - 352#64 + 28#64 = sp - 324#64 := by bv_arith
      rw [a1, a2, a3, a4, a5, a6, a7]
    rw [← hbe, pointsToBytes_32_eq_words64 (sp - 352#64) hih_len]
    have b1 : sp - 352#64 + 8#64 = sp - 344#64 := by bv_arith
    have b2 : sp - 352#64 + 16#64 = sp - 336#64 := by bv_arith
    have b3 : sp - 352#64 + 24#64 = sp - 328#64 := by bv_arith
    rw [b1, b2, b3]
  have h288 :
      ((sp - 288#64) ↦₃₂ h_in.get 0) ∗ ((sp - 284#64) ↦₃₂ h_in.get 1) ∗
      ((sp - 280#64) ↦₃₂ h_in.get 2) ∗ ((sp - 276#64) ↦₃₂ h_in.get 3) ∗
      ((sp - 272#64) ↦₃₂ h_in.get 4) ∗ ((sp - 268#64) ↦₃₂ h_in.get 5) ∗
      ((sp - 264#64) ↦₃₂ h_in.get 6) ∗ ((sp - 260#64) ↦₃₂ h_in.get 7) ⊢
      memRegion (sp - 288#64) 32 := by
    rw [← pointsToBytes_shaStateBytes_288_eq sp h_in]
    rw [← shaStateBytes_length h_in]
    exact pointsToBytes_entails_memRegion (sp - 288#64) (shaStateBytes h_in)
  have h192 :
      ((sp - 192#64) ↦ₛ lastBlk) ⊢
      memRegion (sp - 192#64) 64 := by
    simpa only [hdrop_len] using pointsToBytes_entails_memRegion (sp - 192#64) lastBlk
  have hassoc1 :
      ((sp - 352#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 0)))) ∗
      ((sp - 348#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 1)))) ∗
      ((sp - 344#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 2)))) ∗
      ((sp - 340#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 3)))) ∗
      ((sp - 336#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 4)))) ∗
      ((sp - 332#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 5)))) ∗
      ((sp - 328#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 6)))) ∗
      ((sp - 324#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 7)))) ∗
      ((sp - 320#64) ↦₈ 0x80#8) ∗ ((sp - 319#64) ↦₆₄ 0#64) ∗
      ((sp - 311#64) ↦₆₄ 0#64) ∗ memRegion (sp - 303#64) 15 ∗
      ((sp - 288#64) ↦₃₂ h_in.get 0) ∗ ((sp - 284#64) ↦₃₂ h_in.get 1) ∗
      ((sp - 280#64) ↦₃₂ h_in.get 2) ∗ ((sp - 276#64) ↦₃₂ h_in.get 3) ∗
      ((sp - 272#64) ↦₃₂ h_in.get 4) ∗ ((sp - 268#64) ↦₃₂ h_in.get 5) ∗
      ((sp - 264#64) ↦₃₂ h_in.get 6) ∗ ((sp - 260#64) ↦₃₂ h_in.get 7) ∗
      ((sp - 192#64) ↦ₛ lastBlk) =
      (((sp - 352#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 0)))) ∗
       ((sp - 348#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 1)))) ∗
       ((sp - 344#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 2)))) ∗
       ((sp - 340#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 3)))) ∗
       ((sp - 336#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 4)))) ∗
       ((sp - 332#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 5)))) ∗
       ((sp - 328#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 6)))) ∗
       ((sp - 324#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 7))))) ∗
      (((sp - 320#64) ↦₈ 0x80#8) ∗ ((sp - 319#64) ↦₆₄ 0#64) ∗
       ((sp - 311#64) ↦₆₄ 0#64) ∗ memRegion (sp - 303#64) 15) ∗
      (((sp - 288#64) ↦₃₂ h_in.get 0) ∗ ((sp - 284#64) ↦₃₂ h_in.get 1) ∗
       ((sp - 280#64) ↦₃₂ h_in.get 2) ∗ ((sp - 276#64) ↦₃₂ h_in.get 3) ∗
       ((sp - 272#64) ↦₃₂ h_in.get 4) ∗ ((sp - 268#64) ↦₃₂ h_in.get 5) ∗
       ((sp - 264#64) ↦₃₂ h_in.get 6) ∗ ((sp - 260#64) ↦₃₂ h_in.get 7)) ∗
      ((sp - 192#64) ↦ₛ lastBlk) := by
    simp only [sepConj_assoc]
  rw [hassoc1, h352]
  refine Entails.trans (sepConj_mono_right (sepConj_mono (fold_pad_320_at_1d408 sp) (sepConj_mono h288 h192))) ?_
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem fold_at_1d408 (F : ShaCompress) (sp : BitVec 64)
    (sender receiver : IdentityKey) (macKey : BitVec 256) (message : List (BitVec 8))
    (h_in : ShaState)
    (hh_in : h_in = F ((chunks64 ((mkMacEnv sender receiver macKey message).innerPadded.take
        ((mkMacEnv sender receiver macKey message).innerPadded.length - 64))).foldl F sha256IV)
      ((mkMacEnv sender receiver macKey message).innerPadded.drop
        ((mkMacEnv sender receiver macKey message).innerPadded.length - 64))) :
    let e := mkMacEnv sender receiver macKey message
    ((sp - 352#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 0)))) ∗
    ((sp - 348#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 1)))) ∗
    ((sp - 344#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 2)))) ∗
    ((sp - 340#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 3)))) ∗
    ((sp - 336#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 4)))) ∗
    ((sp - 332#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 5)))) ∗
    ((sp - 328#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 6)))) ∗
    ((sp - 324#64) ↦₃₂ BitVec.truncate 32 (rev32_64 (BitVec.zeroExtend 64 (h_in.get 7)))) ∗
    ((sp - 320#64) ↦₈ 0x80#8) ∗ ((sp - 319#64) ↦₆₄ 0#64) ∗
    ((sp - 311#64) ↦₆₄ 0#64) ∗ memRegion (sp - 303#64) 15 ∗
    ((sp - 288#64) ↦₃₂ h_in.get 0) ∗ ((sp - 284#64) ↦₃₂ h_in.get 1) ∗
    ((sp - 280#64) ↦₃₂ h_in.get 2) ∗ ((sp - 276#64) ↦₃₂ h_in.get 3) ∗
    ((sp - 272#64) ↦₃₂ h_in.get 4) ∗ ((sp - 268#64) ↦₃₂ h_in.get 5) ∗
    ((sp - 264#64) ↦₃₂ h_in.get 6) ∗ ((sp - 260#64) ↦₃₂ h_in.get 7) ∗
    ((sp - 192#64) ↦ₛ (e.innerPadded.drop (e.innerPadded.length - 64))) ⊢
    ((sp - 352#64) ↦₆₄ bytesToU64LE ((e.innerHash F).take 8)) ∗
    ((sp - 344#64) ↦₆₄ bytesToU64LE (((e.innerHash F).drop 8).take 8)) ∗
    ((sp - 336#64) ↦₆₄ bytesToU64LE (((e.innerHash F).drop 16).take 8)) ∗
    ((sp - 328#64) ↦₆₄ bytesToU64LE (((e.innerHash F).drop 24).take 8)) ∗
    ((sp - 320#64) ↦₆₄ 0x80#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
    (∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ((sp - 304#64) ↦₆₄ w6) ∗ ((sp - 296#64) ↦₆₄ w7)) ∗
    memRegion (sp - 288#64) 32 ∗
    memRegion (sp - 192#64) 64 := by
  have hk := keyToBytes32_length macKey
  have hih_eq : h_in.toList.flatMap (toBEBytes 4) =
      (mkMacEnv sender receiver macKey message).innerHash F := by
    rw [hh_in, ← LibsignalHmac.MD.innerHash_eq _ F hk]
  have hih_len : ((mkMacEnv sender receiver macKey message).innerHash F).length = 32 :=
    innerHash_len F _
  have hdrop_len : ((mkMacEnv sender receiver macKey message).innerPadded.drop
      ((mkMacEnv sender receiver macKey message).innerPadded.length - 64)).length = 64 := by
    obtain ⟨hdrop_eq, h56_len⟩ := mkMacEnv_innerPadded_drop_eq sender receiver macKey message
    rw [hdrop_eq, List.length_append, h56_len, toBEBytes_len]
  exact fold_at_1d408_aux sp h_in _ _ hih_eq hih_len hdrop_len

theorem cells_352_8_eq (sp : BitVec 64) :
    memRegion (sp - 352#64) 64 =
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
        ((sp - 352#64) ↦₆₄ c0) ∗ ((sp - 344#64) ↦₆₄ c1) ∗ ((sp - 336#64) ↦₆₄ c2) ∗ ((sp - 328#64) ↦₆₄ c3) ∗
        ((sp - 320#64) ↦₆₄ c4) ∗ ((sp - 312#64) ↦₆₄ c5) ∗ ((sp - 304#64) ↦₆₄ c6) ∗ ((sp - 296#64) ↦₆₄ c7) := by
  rw [memRegion_cells (sp - 352#64) 8 (by decide)]
  cells_unfold

theorem fold_pre_compress8_aux (sp : BitVec 64)
    (ih outerBlk : List (BitVec 8)) (x8 : BitVec 64)
    (hih_len : ih.length = 32)
    (houter_eq : outerBlk = ih ++ [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64)
    (hx8 : x8 = rev64 (256#64 ||| (1#64 <<< 9))) :
    ((sp - 352#64) ↦₆₄ bytesToU64LE (ih.take 8)) ∗
    ((sp - 344#64) ↦₆₄ bytesToU64LE ((ih.drop 8).take 8)) ∗
    ((sp - 336#64) ↦₆₄ bytesToU64LE ((ih.drop 16).take 8)) ∗
    ((sp - 328#64) ↦₆₄ bytesToU64LE ((ih.drop 24).take 8)) ∗
    ((sp - 320#64) ↦₆₄ 0x80#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
    ((sp - 304#64) ↦₆₄ 0#64) ∗ ((sp - 296#64) ↦₆₄ x8) ∗
    ((sp - 192#64) ↦₆₄ bytesToU64LE (ih.take 8)) ∗
    ((sp - 184#64) ↦₆₄ bytesToU64LE ((ih.drop 8).take 8)) ∗
    ((sp - 176#64) ↦₆₄ bytesToU64LE ((ih.drop 16).take 8)) ∗
    ((sp - 168#64) ↦₆₄ bytesToU64LE ((ih.drop 24).take 8)) ∗
    ((sp - 160#64) ↦₆₄ 0x80#64) ∗ ((sp - 152#64) ↦₆₄ 0#64) ∗
    ((sp - 144#64) ↦₆₄ 0#64) ∗ ((sp - 136#64) ↦₆₄ x8) ⊢
    memRegion (sp - 352#64) 63 ∗
    (∃∗ b_cf : BitVec 8, (sp - 289#64) ↦₈ b_cf) ∗
    ((sp - 192#64) ↦ₛ outerBlk) := by
  have h352 :
      ((sp - 352#64) ↦₆₄ bytesToU64LE (ih.take 8)) ∗
      ((sp - 344#64) ↦₆₄ bytesToU64LE ((ih.drop 8).take 8)) ∗
      ((sp - 336#64) ↦₆₄ bytesToU64LE ((ih.drop 16).take 8)) ∗
      ((sp - 328#64) ↦₆₄ bytesToU64LE ((ih.drop 24).take 8)) ∗
      ((sp - 320#64) ↦₆₄ 0x80#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
      ((sp - 304#64) ↦₆₄ 0#64) ∗ ((sp - 296#64) ↦₆₄ x8) ⊢
      memRegion (sp - 352#64) 63 ∗ (∃∗ b_cf : BitVec 8, (sp - 289#64) ↦₈ b_cf) := by
    have hm64 : memRegion (sp - 352#64) 64 =
        memRegion (sp - 352#64) 63 ∗ (∃∗ b_cf : BitVec 8, (sp - 289#64) ↦₈ b_cf) := by
      have ha : sp - 352#64 + 63#64 = sp - 289#64 := by bv_arith
      rw [memRegion_split (sp - 352#64) 63 1 (by decide), ha, memRegion_one]
    rw [← hm64, cells_352_8_eq sp]
    exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
        (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.refl _))))))))
  have h192_lo :
      ((sp - 192#64) ↦₆₄ bytesToU64LE (ih.take 8)) ∗
      ((sp - 184#64) ↦₆₄ bytesToU64LE ((ih.drop 8).take 8)) ∗
      ((sp - 176#64) ↦₆₄ bytesToU64LE ((ih.drop 16).take 8)) ∗
      ((sp - 168#64) ↦₆₄ bytesToU64LE ((ih.drop 24).take 8)) =
      ((sp - 192#64) ↦ₛ ih) := by
    rw [pointsToBytes_32_eq_words64 (sp - 192#64) hih_len]
    have a1 : sp - 192#64 + 8#64 = sp - 184#64 := by bv_arith
    have a2 : sp - 192#64 + 16#64 = sp - 176#64 := by bv_arith
    have a3 : sp - 192#64 + 24#64 = sp - 168#64 := by bv_arith
    rw [a1, a2, a3]
  have h192_hi :
      ((sp - 160#64) ↦₆₄ 0x80#64) ∗ ((sp - 152#64) ↦₆₄ 0#64) ∗
      ((sp - 144#64) ↦₆₄ 0#64) ∗ ((sp - 136#64) ↦₆₄ x8) =
      ((sp - 160#64) ↦ₛ ([0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64)) := by
    have hbytes :
        unpack64 0x80#64 ++ unpack64 0#64 ++ unpack64 0#64 ++
          unpack64 (rev64 (256#64 ||| (1#64 <<< 9))) =
        [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64 := by decide
    have b1 : sp - 160#64 + BitVec.ofNat 64 8 = sp - 152#64 := by bv_arith
    have b2 : sp - 160#64 + BitVec.ofNat 64 16 = sp - 144#64 := by bv_arith
    have b3 : sp - 160#64 + BitVec.ofNat 64 24 = sp - 136#64 := by bv_arith
    rw [hx8, ← hbytes, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      show (unpack64 0x80#64 ++ unpack64 0#64 ++ unpack64 0#64).length = 24 by decide,
      show (unpack64 0x80#64 ++ unpack64 0#64).length = 16 by decide,
      show (unpack64 0x80#64).length = 8 by decide,
      ← ProofLib.pointsTo64_eq_pointsToBytes, ← ProofLib.pointsTo64_eq_pointsToBytes,
      ← ProofLib.pointsTo64_eq_pointsToBytes, ← ProofLib.pointsTo64_eq_pointsToBytes,
      b1, b2, b3]
    simp only [sepConj_assoc]
  have h192 :
      ((sp - 192#64) ↦₆₄ bytesToU64LE (ih.take 8)) ∗
      ((sp - 184#64) ↦₆₄ bytesToU64LE ((ih.drop 8).take 8)) ∗
      ((sp - 176#64) ↦₆₄ bytesToU64LE ((ih.drop 16).take 8)) ∗
      ((sp - 168#64) ↦₆₄ bytesToU64LE ((ih.drop 24).take 8)) ∗
      ((sp - 160#64) ↦₆₄ 0x80#64) ∗ ((sp - 152#64) ↦₆₄ 0#64) ∗
      ((sp - 144#64) ↦₆₄ 0#64) ∗ ((sp - 136#64) ↦₆₄ x8) =
      ((sp - 192#64) ↦ₛ outerBlk) := by
    have ha : sp - 192#64 + BitVec.ofNat 64 32 = sp - 160#64 := by bv_arith
    conv_rhs =>
      rw [houter_eq,
        show ih ++ [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64 =
          ih ++ ([0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64) by
          simp only [List.append_assoc],
        pointsToBytes_append, hih_len, ha, ← h192_lo, ← h192_hi]
    simp only [sepConj_assoc]
  have hassoc :
      ((sp - 352#64) ↦₆₄ bytesToU64LE (ih.take 8)) ∗
      ((sp - 344#64) ↦₆₄ bytesToU64LE ((ih.drop 8).take 8)) ∗
      ((sp - 336#64) ↦₆₄ bytesToU64LE ((ih.drop 16).take 8)) ∗
      ((sp - 328#64) ↦₆₄ bytesToU64LE ((ih.drop 24).take 8)) ∗
      ((sp - 320#64) ↦₆₄ 0x80#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
      ((sp - 304#64) ↦₆₄ 0#64) ∗ ((sp - 296#64) ↦₆₄ x8) ∗
      ((sp - 192#64) ↦₆₄ bytesToU64LE (ih.take 8)) ∗
      ((sp - 184#64) ↦₆₄ bytesToU64LE ((ih.drop 8).take 8)) ∗
      ((sp - 176#64) ↦₆₄ bytesToU64LE ((ih.drop 16).take 8)) ∗
      ((sp - 168#64) ↦₆₄ bytesToU64LE ((ih.drop 24).take 8)) ∗
      ((sp - 160#64) ↦₆₄ 0x80#64) ∗ ((sp - 152#64) ↦₆₄ 0#64) ∗
      ((sp - 144#64) ↦₆₄ 0#64) ∗ ((sp - 136#64) ↦₆₄ x8) =
      (((sp - 352#64) ↦₆₄ bytesToU64LE (ih.take 8)) ∗
       ((sp - 344#64) ↦₆₄ bytesToU64LE ((ih.drop 8).take 8)) ∗
       ((sp - 336#64) ↦₆₄ bytesToU64LE ((ih.drop 16).take 8)) ∗
       ((sp - 328#64) ↦₆₄ bytesToU64LE ((ih.drop 24).take 8)) ∗
       ((sp - 320#64) ↦₆₄ 0x80#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
       ((sp - 304#64) ↦₆₄ 0#64) ∗ ((sp - 296#64) ↦₆₄ x8)) ∗
      (((sp - 192#64) ↦₆₄ bytesToU64LE (ih.take 8)) ∗
       ((sp - 184#64) ↦₆₄ bytesToU64LE ((ih.drop 8).take 8)) ∗
       ((sp - 176#64) ↦₆₄ bytesToU64LE ((ih.drop 16).take 8)) ∗
       ((sp - 168#64) ↦₆₄ bytesToU64LE ((ih.drop 24).take 8)) ∗
       ((sp - 160#64) ↦₆₄ 0x80#64) ∗ ((sp - 152#64) ↦₆₄ 0#64) ∗
       ((sp - 144#64) ↦₆₄ 0#64) ∗ ((sp - 136#64) ↦₆₄ x8)) := by
    simp only [sepConj_assoc]
  rw [hassoc, h192]
  exact Entails.trans (sepConj_mono_left h352) (by simp only [sepConj_assoc]; exact Entails.refl _)

theorem fold_pre_compress8 (F : ShaCompress) (sp : BitVec 64)
    (sender receiver : IdentityKey) (macKey : BitVec 256) (message : List (BitVec 8))
    (x8 : BitVec 64) (hx8 : x8 = rev64 (256#64 ||| (1#64 <<< 9))) :
    let e := mkMacEnv sender receiver macKey message
    ((sp - 352#64) ↦₆₄ bytesToU64LE ((e.innerHash F).take 8)) ∗
    ((sp - 344#64) ↦₆₄ bytesToU64LE (((e.innerHash F).drop 8).take 8)) ∗
    ((sp - 336#64) ↦₆₄ bytesToU64LE (((e.innerHash F).drop 16).take 8)) ∗
    ((sp - 328#64) ↦₆₄ bytesToU64LE (((e.innerHash F).drop 24).take 8)) ∗
    ((sp - 320#64) ↦₆₄ 0x80#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
    ((sp - 304#64) ↦₆₄ 0#64) ∗ ((sp - 296#64) ↦₆₄ x8) ∗
    ((sp - 192#64) ↦₆₄ bytesToU64LE ((e.innerHash F).take 8)) ∗
    ((sp - 184#64) ↦₆₄ bytesToU64LE (((e.innerHash F).drop 8).take 8)) ∗
    ((sp - 176#64) ↦₆₄ bytesToU64LE (((e.innerHash F).drop 16).take 8)) ∗
    ((sp - 168#64) ↦₆₄ bytesToU64LE (((e.innerHash F).drop 24).take 8)) ∗
    ((sp - 160#64) ↦₆₄ 0x80#64) ∗ ((sp - 152#64) ↦₆₄ 0#64) ∗
    ((sp - 144#64) ↦₆₄ 0#64) ∗ ((sp - 136#64) ↦₆₄ x8) ⊢
    memRegion (sp - 352#64) 63 ∗
    (∃∗ b_cf : BitVec 8, (sp - 289#64) ↦₈ b_cf) ∗
    ((sp - 192#64) ↦ₛ ((sha256Pad (e.outerMsg F)).drop 64)) := by
  have hk := keyToBytes32_length macKey
  have hih_len : ((mkMacEnv sender receiver macKey message).innerHash F).length = 32 :=
    innerHash_len F _
  have houter_eq := LibsignalHmac.MD.outer_block (mkMacEnv sender receiver macKey message) F hk
  exact fold_pre_compress8_aux sp _ _ x8 hih_len houter_eq hx8

theorem fold_at_1d434 (sp ret : BitVec 64) (h_out : ShaState) (blk_word : BitVec 64)
    (outerBlk : List (BitVec 8)) (hblk_len : outerBlk.length = 64) :
    memRegion (sp - 352#64) 63 ∗ ((sp - 289#64) ↦₈ 0#8) ∗
    memRegion (sp - 288#64) 32 ∗ ((sp - 256#64) ↦₆₄ blk_word) ∗
    ((sp - 248#64) ↦₃₂ h_out.get 0) ∗ ((sp - 244#64) ↦₃₂ h_out.get 1) ∗
    ((sp - 240#64) ↦₃₂ h_out.get 2) ∗ ((sp - 236#64) ↦₃₂ h_out.get 3) ∗
    ((sp - 232#64) ↦₃₂ h_out.get 4) ∗ ((sp - 228#64) ↦₃₂ h_out.get 5) ∗
    ((sp - 224#64) ↦₃₂ h_out.get 6) ∗ ((sp - 220#64) ↦₃₂ h_out.get 7) ∗
    ((sp - 216#64) ↦₆₄ 1#64) ∗ memRegion (sp - 208#64) 8 ∗
    ((sp - 192#64) ↦ₛ outerBlk) ∗ memRegion ret 16 ⊢
    (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
     ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
      ((sp - 352#64) ↦₆₄ c0) ∗ ((sp - 344#64) ↦₆₄ c1) ∗ ((sp - 336#64) ↦₆₄ c2) ∗ ((sp - 328#64) ↦₆₄ c3) ∗
      ((sp - 320#64) ↦₆₄ c4) ∗ ((sp - 312#64) ↦₆₄ c5) ∗ ((sp - 304#64) ↦₆₄ c6) ∗ ((sp - 296#64) ↦₆₄ c7)) ∗
    memRegion (sp - 288#64) 88 ∗
    (∃∗ b0 : BitVec 64, ∃∗ b1 : BitVec 64, ∃∗ b2 : BitVec 64, ∃∗ b3 : BitVec 64,
     ∃∗ b4 : BitVec 64, ∃∗ b5 : BitVec 64, ∃∗ b6 : BitVec 64, ∃∗ b7 : BitVec 64,
      ((sp - 192#64) ↦₆₄ b0) ∗ ((sp - 184#64) ↦₆₄ b1) ∗ ((sp - 176#64) ↦₆₄ b2) ∗ ((sp - 168#64) ↦₆₄ b3) ∗
      ((sp - 160#64) ↦₆₄ b4) ∗ ((sp - 152#64) ↦₆₄ b5) ∗ ((sp - 144#64) ↦₆₄ b6) ∗ ((sp - 136#64) ↦₆₄ b7)) ∗
    (∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1)) := by
  have h352 :
      memRegion (sp - 352#64) 63 ∗ ((sp - 289#64) ↦₈ 0#8) ⊢
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
        ((sp - 352#64) ↦₆₄ c0) ∗ ((sp - 344#64) ↦₆₄ c1) ∗ ((sp - 336#64) ↦₆₄ c2) ∗ ((sp - 328#64) ↦₆₄ c3) ∗
        ((sp - 320#64) ↦₆₄ c4) ∗ ((sp - 312#64) ↦₆₄ c5) ∗ ((sp - 304#64) ↦₆₄ c6) ∗ ((sp - 296#64) ↦₆₄ c7) := by
    have hm64 : memRegion (sp - 352#64) 64 =
        memRegion (sp - 352#64) 63 ∗ memRegion (sp - 289#64) 1 := by
      have ha : sp - 352#64 + 63#64 = sp - 289#64 := by bv_arith
      rw [memRegion_split (sp - 352#64) 63 1 (by decide), ha]
    rw [← cells_352_8_eq sp, hm64]
    exact sepConj_mono_right (pointsTo8_entails_memRegion (sp - 289#64) 0#8)
  have h288 :
      memRegion (sp - 288#64) 32 ∗ ((sp - 256#64) ↦₆₄ blk_word) ∗
      ((sp - 248#64) ↦₃₂ h_out.get 0) ∗ ((sp - 244#64) ↦₃₂ h_out.get 1) ∗
      ((sp - 240#64) ↦₃₂ h_out.get 2) ∗ ((sp - 236#64) ↦₃₂ h_out.get 3) ∗
      ((sp - 232#64) ↦₃₂ h_out.get 4) ∗ ((sp - 228#64) ↦₃₂ h_out.get 5) ∗
      ((sp - 224#64) ↦₃₂ h_out.get 6) ∗ ((sp - 220#64) ↦₃₂ h_out.get 7) ∗
      ((sp - 216#64) ↦₆₄ 1#64) ∗ memRegion (sp - 208#64) 8 ⊢
      memRegion (sp - 288#64) 88 := by
    have h248 :
        ((sp - 248#64) ↦₃₂ h_out.get 0) ∗ ((sp - 244#64) ↦₃₂ h_out.get 1) ∗
        ((sp - 240#64) ↦₃₂ h_out.get 2) ∗ ((sp - 236#64) ↦₃₂ h_out.get 3) ∗
        ((sp - 232#64) ↦₃₂ h_out.get 4) ∗ ((sp - 228#64) ↦₃₂ h_out.get 5) ∗
        ((sp - 224#64) ↦₃₂ h_out.get 6) ∗ ((sp - 220#64) ↦₃₂ h_out.get 7) ⊢
        memRegion (sp - 248#64) 32 := by
      rw [← pointsToBytes_shaStateBytes_248_eq sp h_out]
      rw [← shaStateBytes_length h_out]
      exact pointsToBytes_entails_memRegion (sp - 248#64) (shaStateBytes h_out)
    have hm88 : memRegion (sp - 288#64) 88 =
        memRegion (sp - 288#64) 32 ∗ memRegion (sp - 256#64) 8 ∗
        memRegion (sp - 248#64) 32 ∗ memRegion (sp - 216#64) 8 ∗
        memRegion (sp - 208#64) 8 := by
      rw [memRegion_split (sp - 288#64) 32 56 (by decide),
        memRegion_split (sp - 288#64 + 32#64) 8 48 (by decide),
        memRegion_split (sp - 288#64 + 32#64 + 8#64) 32 16 (by decide),
        memRegion_split (sp - 288#64 + 32#64 + 8#64 + 32#64) 8 8 (by decide)]
      have a1 : sp - 288#64 + 32#64 = sp - 256#64 := by bv_arith
      have a2 : sp - 256#64 + 8#64 = sp - 248#64 := by bv_arith
      have a3 : sp - 248#64 + 32#64 = sp - 216#64 := by bv_arith
      have a4 : sp - 216#64 + 8#64 = sp - 208#64 := by bv_arith
      rw [a1, a2, a3, a4]
    rw [hm88]
    have hassoc :
        memRegion (sp - 288#64) 32 ∗ ((sp - 256#64) ↦₆₄ blk_word) ∗
        ((sp - 248#64) ↦₃₂ h_out.get 0) ∗ ((sp - 244#64) ↦₃₂ h_out.get 1) ∗
        ((sp - 240#64) ↦₃₂ h_out.get 2) ∗ ((sp - 236#64) ↦₃₂ h_out.get 3) ∗
        ((sp - 232#64) ↦₃₂ h_out.get 4) ∗ ((sp - 228#64) ↦₃₂ h_out.get 5) ∗
        ((sp - 224#64) ↦₃₂ h_out.get 6) ∗ ((sp - 220#64) ↦₃₂ h_out.get 7) ∗
        ((sp - 216#64) ↦₆₄ 1#64) ∗ memRegion (sp - 208#64) 8 =
        memRegion (sp - 288#64) 32 ∗ ((sp - 256#64) ↦₆₄ blk_word) ∗
        (((sp - 248#64) ↦₃₂ h_out.get 0) ∗ ((sp - 244#64) ↦₃₂ h_out.get 1) ∗
         ((sp - 240#64) ↦₃₂ h_out.get 2) ∗ ((sp - 236#64) ↦₃₂ h_out.get 3) ∗
         ((sp - 232#64) ↦₃₂ h_out.get 4) ∗ ((sp - 228#64) ↦₃₂ h_out.get 5) ∗
         ((sp - 224#64) ↦₃₂ h_out.get 6) ∗ ((sp - 220#64) ↦₃₂ h_out.get 7)) ∗
        ((sp - 216#64) ↦₆₄ 1#64) ∗ memRegion (sp - 208#64) 8 := by
      simp only [sepConj_assoc]
    rw [hassoc]
    exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion (sp - 256#64) blk_word)
      (sepConj_mono h248 (sepConj_mono_left (pointsTo64_entails_memRegion (sp - 216#64) 1#64))))
  have h192 :
      ((sp - 192#64) ↦ₛ outerBlk) ⊢
      ∃∗ b0 : BitVec 64, ∃∗ b1 : BitVec 64, ∃∗ b2 : BitVec 64, ∃∗ b3 : BitVec 64,
      ∃∗ b4 : BitVec 64, ∃∗ b5 : BitVec 64, ∃∗ b6 : BitVec 64, ∃∗ b7 : BitVec 64,
        ((sp - 192#64) ↦₆₄ b0) ∗ ((sp - 184#64) ↦₆₄ b1) ∗ ((sp - 176#64) ↦₆₄ b2) ∗ ((sp - 168#64) ↦₆₄ b3) ∗
        ((sp - 160#64) ↦₆₄ b4) ∗ ((sp - 152#64) ↦₆₄ b5) ∗ ((sp - 144#64) ↦₆₄ b6) ∗ ((sp - 136#64) ↦₆₄ b7) := by
    rw [← cells_192_8_eq sp]
    simpa only [hblk_len] using pointsToBytes_entails_memRegion (sp - 192#64) outerBlk
  have hret :
      memRegion ret 16 =
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) := by
    rw [memRegion_cells ret 2 (by decide)]
    simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_zero]
  rw [hret]
  have hassoc_all :
      memRegion (sp - 352#64) 63 ∗ ((sp - 289#64) ↦₈ 0#8) ∗
      memRegion (sp - 288#64) 32 ∗ ((sp - 256#64) ↦₆₄ blk_word) ∗
      ((sp - 248#64) ↦₃₂ h_out.get 0) ∗ ((sp - 244#64) ↦₃₂ h_out.get 1) ∗
      ((sp - 240#64) ↦₃₂ h_out.get 2) ∗ ((sp - 236#64) ↦₃₂ h_out.get 3) ∗
      ((sp - 232#64) ↦₃₂ h_out.get 4) ∗ ((sp - 228#64) ↦₃₂ h_out.get 5) ∗
      ((sp - 224#64) ↦₃₂ h_out.get 6) ∗ ((sp - 220#64) ↦₃₂ h_out.get 7) ∗
      ((sp - 216#64) ↦₆₄ 1#64) ∗ memRegion (sp - 208#64) 8 ∗
      ((sp - 192#64) ↦ₛ outerBlk) ∗
      (∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1)) =
      (memRegion (sp - 352#64) 63 ∗ ((sp - 289#64) ↦₈ 0#8)) ∗
      (memRegion (sp - 288#64) 32 ∗ ((sp - 256#64) ↦₆₄ blk_word) ∗
       ((sp - 248#64) ↦₃₂ h_out.get 0) ∗ ((sp - 244#64) ↦₃₂ h_out.get 1) ∗
       ((sp - 240#64) ↦₃₂ h_out.get 2) ∗ ((sp - 236#64) ↦₃₂ h_out.get 3) ∗
       ((sp - 232#64) ↦₃₂ h_out.get 4) ∗ ((sp - 228#64) ↦₃₂ h_out.get 5) ∗
       ((sp - 224#64) ↦₃₂ h_out.get 6) ∗ ((sp - 220#64) ↦₃₂ h_out.get 7) ∗
       ((sp - 216#64) ↦₆₄ 1#64) ∗ memRegion (sp - 208#64) 8) ∗
      ((sp - 192#64) ↦ₛ outerBlk) ∗
      (∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1)) := by
    simp only [sepConj_assoc]
  rw [hassoc_all]
  exact sepConj_mono h352 (sepConj_mono h288 (sepConj_mono_left h192))

theorem fold_epilogue_post (F : ShaCompress) (sp ret : BitVec 64)
    (sender receiver : IdentityKey) (macKey : BitVec 256) (message : List (BitVec 8))
    (h_out : ShaState)
    (hh_out : h_out = F ((mkMacEnv sender receiver macKey message).oState1 F)
      ((sha256Pad ((mkMacEnv sender receiver macKey message).outerMsg F)).drop 64))
    (tag_val : BitVec 64)
    (htag : tag_val = rev64 (BitVec.zeroExtend 64 (h_out.get 1) |||
      (BitVec.zeroExtend 64 (h_out.get 0) <<< 32)))
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : BitVec 64) :
    (ret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((ret + 8#64) ↦₆₄ tag_val) ∗
    ((sp - 352#64) ↦₆₄ 0#64) ∗ ((sp - 344#64) ↦₆₄ 0#64) ∗
    ((sp - 336#64) ↦₆₄ 0#64) ∗ ((sp - 328#64) ↦₆₄ 0#64) ∗
    ((sp - 320#64) ↦₆₄ 0#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
    ((sp - 304#64) ↦₆₄ 0#64) ∗ ((sp - 296#64) ↦₆₄ 0#64) ∗
    memRegion (sp - 288#64) 88 ∗
    ((sp - 192#64) ↦₆₄ 0#64) ∗ ((sp - 184#64) ↦₆₄ 0#64) ∗
    ((sp - 176#64) ↦₆₄ 0#64) ∗ ((sp - 168#64) ↦₆₄ 0#64) ∗
    ((sp - 160#64) ↦₆₄ 0#64) ∗ ((sp - 152#64) ↦₆₄ 0#64) ∗
    ((sp - 144#64) ↦₆₄ 0#64) ∗ ((sp - 136#64) ↦₆₄ 0#64) ∗
    ((sp - 96#64) ↦₆₄ s0) ∗ ((sp - 88#64) ↦₆₄ s1) ∗
    ((sp - 80#64) ↦₆₄ s2) ∗ ((sp - 72#64) ↦₆₄ s3) ∗
    ((sp - 64#64) ↦₆₄ s4) ∗ ((sp - 56#64) ↦₆₄ s5) ∗
    ((sp - 48#64) ↦₆₄ s6) ∗ ((sp - 40#64) ↦₆₄ s7) ∗
    ((sp - 32#64) ↦₆₄ s8) ∗ ((sp - 24#64) ↦₆₄ s9) ∗
    ((sp - 16#64) ↦₆₄ s10) ∗ ((sp - 8#64) ↦₆₄ s11) ⊢
    (ret ↦₆₄ okTagVec) ∗
    ((ret + 8#64) ↦ₛ computeMac F sender receiver macKey message) ∗
    memRegion (sp - 352#64) 0x98 ∗
    memRegion (sp - 192#64) 24 ∗
    memRegion (sp - 160#64) 24 ∗
    (∃∗ v, (sp - 168#64) ↦₆₄ v) ∗
    (∃∗ v, (sp - 136#64) ↦₆₄ v) ∗
    (∃∗ s0' : BitVec 64, ∃∗ s1' : BitVec 64, ∃∗ s2' : BitVec 64, ∃∗ s3' : BitVec 64,
     ∃∗ s4' : BitVec 64, ∃∗ s5' : BitVec 64, ∃∗ s6' : BitVec 64, ∃∗ s7' : BitVec 64,
     ∃∗ s8' : BitVec 64, ∃∗ s9' : BitVec 64, ∃∗ s10' : BitVec 64, ∃∗ s11' : BitVec 64,
      ((sp - 96#64) ↦₆₄ s0') ∗ ((sp - 88#64) ↦₆₄ s1') ∗ ((sp - 80#64) ↦₆₄ s2') ∗ ((sp - 72#64) ↦₆₄ s3') ∗
      ((sp - 64#64) ↦₆₄ s4') ∗ ((sp - 56#64) ↦₆₄ s5') ∗ ((sp - 48#64) ↦₆₄ s6') ∗ ((sp - 40#64) ↦₆₄ s7') ∗
      ((sp - 32#64) ↦₆₄ s8') ∗ ((sp - 24#64) ↦₆₄ s9') ∗ ((sp - 16#64) ↦₆₄ s10') ∗ ((sp - 8#64) ↦₆₄ s11')) := by
  let e := mkMacEnv sender receiver macKey message
  have hk := keyToBytes32_length macKey
  have htag_pts : ((ret + 8#64) ↦₆₄ tag_val) =
      ((ret + 8#64) ↦ₛ computeMac F sender receiver macKey message) := by
    rw [htag, ProofLib.pointsTo64_eq_pointsToBytes, unpack64_eq_toLEBytes_8,
      LibsignalHmac.OuterAux.toLEBytes_8_rev64_pair,
      ← LibsignalHmac.OuterAux.shaState_be_take_8 h_out, hh_out,
      ← LibsignalHmac.MD.hmac8_eq e F hk]
    rfl
  have h352 :
      ((sp - 352#64) ↦₆₄ 0#64) ∗ ((sp - 344#64) ↦₆₄ 0#64) ∗
      ((sp - 336#64) ↦₆₄ 0#64) ∗ ((sp - 328#64) ↦₆₄ 0#64) ∗
      ((sp - 320#64) ↦₆₄ 0#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
      ((sp - 304#64) ↦₆₄ 0#64) ∗ ((sp - 296#64) ↦₆₄ 0#64) ∗
      memRegion (sp - 288#64) 88 ⊢
      memRegion (sp - 352#64) 0x98 := by
    have hm152 : memRegion (sp - 352#64) 0x98 =
        memRegion (sp - 352#64) 64 ∗ memRegion (sp - 288#64) 88 := by
      have ha : sp - 352#64 + 64#64 = sp - 288#64 := by bv_arith
      rw [memRegion_split (sp - 352#64) 64 88 (by decide), ha]
    have hassoc352 :
        ((sp - 352#64) ↦₆₄ 0#64) ∗ ((sp - 344#64) ↦₆₄ 0#64) ∗
        ((sp - 336#64) ↦₆₄ 0#64) ∗ ((sp - 328#64) ↦₆₄ 0#64) ∗
        ((sp - 320#64) ↦₆₄ 0#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
        ((sp - 304#64) ↦₆₄ 0#64) ∗ ((sp - 296#64) ↦₆₄ 0#64) ∗
        memRegion (sp - 288#64) 88 =
        (((sp - 352#64) ↦₆₄ 0#64) ∗ ((sp - 344#64) ↦₆₄ 0#64) ∗
         ((sp - 336#64) ↦₆₄ 0#64) ∗ ((sp - 328#64) ↦₆₄ 0#64) ∗
         ((sp - 320#64) ↦₆₄ 0#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
         ((sp - 304#64) ↦₆₄ 0#64) ∗ ((sp - 296#64) ↦₆₄ 0#64)) ∗
        memRegion (sp - 288#64) 88 := by
      simp only [sepConj_assoc]
    rw [hassoc352, hm152, cells_352_8_eq sp]
    refine sepConj_mono_left ?_
    exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
        (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.refl _))))))))
  have h192 :
      ((sp - 192#64) ↦₆₄ 0#64) ∗ ((sp - 184#64) ↦₆₄ 0#64) ∗
      ((sp - 176#64) ↦₆₄ 0#64) ∗ ((sp - 168#64) ↦₆₄ 0#64) ∗
      ((sp - 160#64) ↦₆₄ 0#64) ∗ ((sp - 152#64) ↦₆₄ 0#64) ∗
      ((sp - 144#64) ↦₆₄ 0#64) ∗ ((sp - 136#64) ↦₆₄ 0#64) ⊢
      memRegion (sp - 192#64) 24 ∗ memRegion (sp - 160#64) 24 ∗
      (∃∗ v, (sp - 168#64) ↦₆₄ v) ∗ (∃∗ v, (sp - 136#64) ↦₆₄ v) := by
    rw [← memRegion_192_64_eq sp, cells_192_8_eq sp]
    exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
        (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.refl _))))))))
  have h96 :
      ((sp - 96#64) ↦₆₄ s0) ∗ ((sp - 88#64) ↦₆₄ s1) ∗
      ((sp - 80#64) ↦₆₄ s2) ∗ ((sp - 72#64) ↦₆₄ s3) ∗
      ((sp - 64#64) ↦₆₄ s4) ∗ ((sp - 56#64) ↦₆₄ s5) ∗
      ((sp - 48#64) ↦₆₄ s6) ∗ ((sp - 40#64) ↦₆₄ s7) ∗
      ((sp - 32#64) ↦₆₄ s8) ∗ ((sp - 24#64) ↦₆₄ s9) ∗
      ((sp - 16#64) ↦₆₄ s10) ∗ ((sp - 8#64) ↦₆₄ s11) ⊢
      ∃∗ s0' : BitVec 64, ∃∗ s1' : BitVec 64, ∃∗ s2' : BitVec 64, ∃∗ s3' : BitVec 64,
      ∃∗ s4' : BitVec 64, ∃∗ s5' : BitVec 64, ∃∗ s6' : BitVec 64, ∃∗ s7' : BitVec 64,
      ∃∗ s8' : BitVec 64, ∃∗ s9' : BitVec 64, ∃∗ s10' : BitVec 64, ∃∗ s11' : BitVec 64,
        ((sp - 96#64) ↦₆₄ s0') ∗ ((sp - 88#64) ↦₆₄ s1') ∗ ((sp - 80#64) ↦₆₄ s2') ∗ ((sp - 72#64) ↦₆₄ s3') ∗
        ((sp - 64#64) ↦₆₄ s4') ∗ ((sp - 56#64) ↦₆₄ s5') ∗ ((sp - 48#64) ↦₆₄ s6') ∗ ((sp - 40#64) ↦₆₄ s7') ∗
        ((sp - 32#64) ↦₆₄ s8') ∗ ((sp - 24#64) ↦₆₄ s9') ∗ ((sp - 16#64) ↦₆₄ s10') ∗ ((sp - 8#64) ↦₆₄ s11') := by
    exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
        (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
          (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
            (Entails.refl _))))))))))))
  rw [htag_pts, show (0xfffffffffffffffe#64 : BitVec 64) = okTagVec from rfl]
  have hassoc :
      (ret ↦₆₄ okTagVec) ∗ ((ret + 8#64) ↦ₛ computeMac F sender receiver macKey message) ∗
      ((sp - 352#64) ↦₆₄ 0#64) ∗ ((sp - 344#64) ↦₆₄ 0#64) ∗
      ((sp - 336#64) ↦₆₄ 0#64) ∗ ((sp - 328#64) ↦₆₄ 0#64) ∗
      ((sp - 320#64) ↦₆₄ 0#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
      ((sp - 304#64) ↦₆₄ 0#64) ∗ ((sp - 296#64) ↦₆₄ 0#64) ∗
      memRegion (sp - 288#64) 88 ∗
      ((sp - 192#64) ↦₆₄ 0#64) ∗ ((sp - 184#64) ↦₆₄ 0#64) ∗
      ((sp - 176#64) ↦₆₄ 0#64) ∗ ((sp - 168#64) ↦₆₄ 0#64) ∗
      ((sp - 160#64) ↦₆₄ 0#64) ∗ ((sp - 152#64) ↦₆₄ 0#64) ∗
      ((sp - 144#64) ↦₆₄ 0#64) ∗ ((sp - 136#64) ↦₆₄ 0#64) ∗
      ((sp - 96#64) ↦₆₄ s0) ∗ ((sp - 88#64) ↦₆₄ s1) ∗
      ((sp - 80#64) ↦₆₄ s2) ∗ ((sp - 72#64) ↦₆₄ s3) ∗
      ((sp - 64#64) ↦₆₄ s4) ∗ ((sp - 56#64) ↦₆₄ s5) ∗
      ((sp - 48#64) ↦₆₄ s6) ∗ ((sp - 40#64) ↦₆₄ s7) ∗
      ((sp - 32#64) ↦₆₄ s8) ∗ ((sp - 24#64) ↦₆₄ s9) ∗
      ((sp - 16#64) ↦₆₄ s10) ∗ ((sp - 8#64) ↦₆₄ s11) =
      (ret ↦₆₄ okTagVec) ∗ ((ret + 8#64) ↦ₛ computeMac F sender receiver macKey message) ∗
      (((sp - 352#64) ↦₆₄ 0#64) ∗ ((sp - 344#64) ↦₆₄ 0#64) ∗
       ((sp - 336#64) ↦₆₄ 0#64) ∗ ((sp - 328#64) ↦₆₄ 0#64) ∗
       ((sp - 320#64) ↦₆₄ 0#64) ∗ ((sp - 312#64) ↦₆₄ 0#64) ∗
       ((sp - 304#64) ↦₆₄ 0#64) ∗ ((sp - 296#64) ↦₆₄ 0#64) ∗
       memRegion (sp - 288#64) 88) ∗
      (((sp - 192#64) ↦₆₄ 0#64) ∗ ((sp - 184#64) ↦₆₄ 0#64) ∗
       ((sp - 176#64) ↦₆₄ 0#64) ∗ ((sp - 168#64) ↦₆₄ 0#64) ∗
       ((sp - 160#64) ↦₆₄ 0#64) ∗ ((sp - 152#64) ↦₆₄ 0#64) ∗
       ((sp - 144#64) ↦₆₄ 0#64) ∗ ((sp - 136#64) ↦₆₄ 0#64)) ∗
      (((sp - 96#64) ↦₆₄ s0) ∗ ((sp - 88#64) ↦₆₄ s1) ∗
       ((sp - 80#64) ↦₆₄ s2) ∗ ((sp - 72#64) ↦₆₄ s3) ∗
       ((sp - 64#64) ↦₆₄ s4) ∗ ((sp - 56#64) ↦₆₄ s5) ∗
       ((sp - 48#64) ↦₆₄ s6) ∗ ((sp - 40#64) ↦₆₄ s7) ∗
       ((sp - 32#64) ↦₆₄ s8) ∗ ((sp - 24#64) ↦₆₄ s9) ∗
       ((sp - 16#64) ↦₆₄ s10) ∗ ((sp - 8#64) ↦₆₄ s11)) := by
    simp only [sepConj_assoc]
  rw [hassoc]
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono h352 (Entails.trans (sepConj_mono h192 h96)
      (by simp only [sepConj_assoc]; exact Entails.refl _))))

theorem mkMacEnv_innerTail_len_norm (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    (mkMacEnv sender receiver macKey message).innerTail.length =
      (mkMacEnv sender receiver macKey message).innerPos :=
  mkMacEnv_innerTail_length sender receiver macKey message

@[arm64_norm]
theorem mkMacEnv_innerPos_zext (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    BitVec.zeroExtend 64 (BitVec.ofNat 8 (mkMacEnv sender receiver macKey message).innerPos) =
      BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos :=
  zext64_ofNat8_eq (mkMacEnv_innerTail_length sender receiver macKey message ▸
    mkMacEnv_innerTail_length_lt sender receiver macKey message)

@[arm64_norm]
theorem mkMacEnv_innerPos_setWidth (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    BitVec.setWidth 64 (BitVec.ofNat 8 (mkMacEnv sender receiver macKey message).innerPos) =
      BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos :=
  mkMacEnv_innerPos_zext sender receiver macKey message

@[arm64_norm]
theorem mkMacEnv_innerPos_trunc32_zext64 (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos)) =
      BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos := by
  have h := mkMacEnv_innerTail_length sender receiver macKey message ▸
    mkMacEnv_innerTail_length_lt sender receiver macKey message
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

@[arm64_norm]
theorem mkMacEnv_innerPos_setWidth32_setWidth64 (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos)) =
      BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos :=
  mkMacEnv_innerPos_trunc32_zext64 sender receiver macKey message

@[arm64_norm]
theorem mkMacEnv_innerPos_xor_63 (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos ^^^ 63#64 =
      BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos) :=
  ofNat64_xor_63 (mkMacEnv_innerTail_length sender receiver macKey message ▸
    mkMacEnv_innerTail_length_lt sender receiver macKey message)

@[arm64_norm]
theorem mkMacEnv_innerPos_sub63_toNat (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).toNat =
      63 - (mkMacEnv sender receiver macKey message).innerPos := by
  have h := mkMacEnv_innerTail_length sender receiver macKey message ▸
    mkMacEnv_innerTail_length_lt sender receiver macKey message
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

@[arm64_norm]
theorem mkMacEnv_innerBitlen (sender receiver : IdentityKey)
    (macKey : BitVec 256) (message : List (BitVec 8)) :
    (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB <<< 9) |||
      (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos <<< 3) =
      BitVec.ofNat 64 (8 * (mkMacEnv sender receiver macKey message).innerMsg.length) :=
  LibsignalHmac.MD.bitlen (mkMacEnv sender receiver macKey message) (keyToBytes32_length macKey)

private theorem SepWPp.with_join {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} (P_join : SepProp) (φ : State → Prop)
    (hjoin : ∀ sm : State, φ sm → SepWPp prog ret sm P_join Q Qp)
    (hbody : (∀ sm : State, φ sm → SepWPp prog ret sm P_join Q Qp) →
      SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hbody hjoin

theorem SepWPp_with_join_shared_lb {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} (P_join : SepProp) (φ : State → Prop)
    (hjoin : ∀ sm : State, φ sm → SepWPp prog ret sm P_join Q Qp)
    (hbody : (∀ sm : State, φ sm → SepWPp prog ret sm P_join Q Qp) →
      SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.with_join P_join φ hjoin hbody

private theorem SepWPp.apply_join {prog : Program} {ret : BitVec 64} {sm : State} {P P_join : SepProp}
    {Q Qp : State → SepProp → Prop} {φ : State → Prop}
    (hjoin : ∀ sm : State, φ sm → SepWPp prog ret sm P_join Q Qp)
    (hφ : φ sm) (hP : P = P_join ∗ emp) :
    SepWPp prog ret sm P Q Qp := by
  have hent : P ⊢ P_join := by rw [hP, sepConj_emp]; exact Entails.refl _
  exact SepWPp.weaken_pre hent (hjoin sm hφ)


theorem SepWPp_apply_join_shared_lb {prog : Program} {ret : BitVec 64} {sm : State} {P P_join : SepProp}
    {Q Qp : State → SepProp → Prop} {φ : State → Prop}
    (hjoin : ∀ sm : State, φ sm → SepWPp prog ret sm P_join Q Qp)
    (hφ : φ sm) (hP : P = P_join ∗ emp) :
    SepWPp prog ret sm P Q Qp :=
  SepWPp.apply_join hjoin hφ hP
namespace ComputeMacTactics

open Lean Meta Elab Tactic in
/-- Clear given variables and any hypotheses that transitively depend on them (if not in goal). -/
def clearDepsTac (ids : Array Name) : TacticM Unit := withMainContext do
  let lctx ← getLCtx
  let mut toClear : Array FVarId := #[]
  for id in ids do
    if let some decl := lctx.findFromUserName? id then
      toClear := toClear.push decl.fvarId
  for decl in lctx do
    if !decl.isImplementationDetail then
      let ty ← instantiateMVars decl.type
      if (ty.find? fun sub => sub.isFVar && toClear.contains sub.fvarId!).isSome then
        if !toClear.contains decl.fvarId then
          toClear := toClear.push decl.fvarId
  let mvarId ← (← getMainGoal).tryClearMany toClear
  replaceMainGoal [mvarId]

end ComputeMacTactics
open ComputeMacTactics


/-! ## Stack-parameterized `compute_mac` verification and corollaries -/

def computeMacSpecAt (F : ShaCompress) (A : RustAlloc) (pkStack : Nat) : Spec ComputeMacGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.senderA ∧ s.readReg64 .x2 = x.receiverA ∧
      s.readReg64 .x3 = x.keyA ∧ s.readReg64 .x4 = 32#64 ∧ s.readReg64 .x5 = x.msgA ∧
      (s.readReg64 .x6).toNat = x.message.length ∧ x.message.length < 2 ^ 63⌝ ∗
      memRegion x.ret 16 ∗
      (x.senderA ↦ₛ x.sender.publicKey.bytes.toList) ∗
      (x.receiverA ↦ₛ x.receiver.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      (x.msgA ↦ₛ x.message) ∗
      A.pool ∗ stackAt s.sp (pkStack + 496)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ret ↦₆₄ okTagVec) ∗
      ((x.ret + 8#64) ↦ₛ computeMac F x.sender x.receiver x.macKey x.message) ∗
      (x.senderA ↦ₛ x.sender.publicKey.bytes.toList) ∗
      (x.receiverA ↦ₛ x.receiver.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      (x.msgA ↦ₛ x.message) ∗
      A.pool ∗ stackAt s0.sp (pkStack + 496)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def publicKeySerializeSpecAt (A : RustAlloc) (pkStack : Nat) : Spec PublicKeySerializeCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self⌝ ∗ (x.self ↦ₛ x.pk.bytes.toList) ∗ A.pool ∗
    stackAt s.sp pkStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
    (x.self ↦ₛ x.pk.bytes.toList) ∗ boxU8Buf A (sf.readReg64 .x0) x.pk.serialize ∗
    A.pool ∗ stackAt s0.sp pkStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def publicKeySerializeSpecKeepAt (img : Obj.Image) (A : RustAlloc) (pkStack : Nat) :
    Spec PublicKeySerializeCall where
  pre := fun x s =>
    ⌜(img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧ s.readReg64 .x0 = x.self⌝ ∗
      (x.self ↦ₛ x.pk.bytes.toList) ∗
      A.pool ∗
      stackAt s.sp pkStack
  post := fun x s0 sf =>
    ⌜img.FrozenLoaded sf ∧ sf.symtab = img.symtab⌝ ∗
      (publicKeySerializeSpecAt A pkStack).post x s0 sf
  onPanic := (publicKeySerializeSpecAt A pkStack).onPanic

abbrev publicKeySerializeSpecKeepX (img : Obj.Image) (A : RustAlloc) :
    Spec PublicKeySerializeCall :=
  publicKeySerializeSpecKeepAt img A publicKeySerializeStackX

theorem publicKeySerializeKeepAt_of_inImage {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {A : RustAlloc} {pkStack : Nat}
    (h : subroutine_ok prog entry ((publicKeySerializeSpecAt A pkStack).inImage img)) :
    subroutine_ok prog entry (publicKeySerializeSpecKeepAt img A pkStack) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hcode => ?_
  have hpre' : s0.mem ⊨ ((publicKeySerializeSpecAt A pkStack).inImage img).pre x s0 ∗ R := by
    simp only [publicKeySerializeSpecKeepAt, Spec.inImage, publicKeySerializeSpecAt,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨hpre.1.1, hpre.1.2, hpre.2⟩
  have hinv : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab := by
    simp only [Spec.inImage, publicKeySerializeSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre'
    exact hpre'.1
  obtain ⟨sf, hsteps, hout, -⟩ :=
    subroutine_ok.no_fault_before_outcome h x R s0 hpc hrun hpre' hsp hcode
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [publicKeySerializeSpecKeepAt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hinv.1.of_keepsFrozen hsteps.keepsFrozen, hsteps.symtab_eq.trans hinv.2⟩, hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

private theorem publicKeySerializeKeep_of_inImage {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {A : RustAlloc}
    (h : subroutine_ok prog entry ((publicKeySerializeSpecX A).inImage img)) :
    subroutine_ok prog entry (publicKeySerializeSpecKeepX img A) :=
  publicKeySerializeKeepAt_of_inImage h

private theorem seq_inImage_compute {prog : Program} (mid : BitVec 64) {target_pc : BitVec 64}
    {img : Obj.Image} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP reaches_pc
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩
  · rcases (hnext (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym)).elim hmm (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hpost⟩ | ⟨_, hoom⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, Pf, hmf, hpost⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  · exact (not_satisfies_false_sepConj hoom).elim

local macro "wp_steps_inImage " mid:term : tactic =>
  `(tactic| (
    refine seq_inImage_compute $mid ‹_› ‹_› ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF_step hsym_step))

private theorem stackAt_pkX_eq_nfs (sp : BitVec 64) :
    stackAt sp publicKeySerializeStackX =
      stackAt sp newFromSliceStack ∗ memRegion (sp - 16416#64) 15872 := by
  simp only [stackAt, publicKeySerializeStackX, extHookStack, newFromSliceStack]
  rw [show (2 ^ 14 + 32 : Nat) = 15872 + 544 by decide,
    memRegion_split _ 15872 544 (by decide)]
  have e1 : sp - BitVec.ofNat 64 (15872 + 544) = sp - 16416#64 := by bv_arith
  have e2 : sp - 16416#64 + BitVec.ofNat 64 15872 = sp - BitVec.ofNat 64 544 := by bv_arith
  rw [e1, e2, sepConj_comm]

theorem stackAt_pkX_eq_ext (sp : BitVec 64) :
    stackAt sp publicKeySerializeStackX =
      stackAt sp extHookStack ∗ memRegion (sp - 16416#64) 32 := by
  simp only [stackAt, publicKeySerializeStackX, extHookStack]
  rw [show (2 ^ 14 + 32 : Nat) = 32 + 2 ^ 14 by decide,
    memRegion_split _ 32 (2 ^ 14) (by decide)]
  have e1 : sp - BitVec.ofNat 64 (32 + 2 ^ 14) = sp - 16416#64 := by bv_arith
  have e2 : sp - 16416#64 + BitVec.ofNat 64 32 = sp - BitVec.ofNat 64 (2 ^ 14) := by bv_arith
  rw [e1, e2, sepConj_comm]

def newFromSlicePkStackSpecAt (F : ShaCompress) (pkStack : Nat) : Spec NewFromSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.keyA ∧
      (s.readReg64 .x2).toNat = x.key.length ∧ x.key.length ≤ 64⌝ ∗
      memRegion x.ret 0x98 ∗ (x.keyA ↦ₛ x.key) ∗
      stackAt s.sp pkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ret ↦₆₄ 0#64) ∗ hmacCoreAt F (x.ret + 8#64) x.key [] ∗
      (x.keyA ↦ₛ x.key) ∗
      stackAt s0.sp pkStack

private abbrev newFromSlicePkStackSpecX (F : ShaCompress) : Spec NewFromSliceGhost :=
  newFromSlicePkStackSpecAt F publicKeySerializeStackX

private theorem newFromSlice_ok_at2_ext_x (img : Obj.Image) (C : Crypto)
    (ext : String → Option (State → State))
    (hnew : NewFromSliceOkExt img C ext)
    (entry : BitVec 64) (hfn : entry = (tripleRatchetProgAtExt img.base ext).fnAddr computeMacName) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      ((newFromSlicePkStackSpecX C.F).inImage img) := by
  have heq : entry + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") = (tripleRatchetProgAtExt img.base ext).fnAddr newFromSliceName := by
    subst hfn
    dsimp only [tripleRatchetProgAtExt]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::compute_mac"),
      (ls_lemma% fnOff "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]")]
    bv_omega
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [heq] at hpc
  refine subroutine_ok.mono_outcome hnew x (memRegion (s0.sp - 16416#64) 15872 ∗ R) s0 hpc hrun
    (by simpa only [Spec.inImage, newFromSliceSpec, newFromSlicePkStackSpecX, newFromSlicePkStackSpecAt,
      stackAt_pkX_eq_nfs, sepConj_assoc] using hpre) hsp fun _ hraw => ?_
  unfold SubroutineOutcome at hraw ⊢
  simpa only [Spec.inImage, newFromSliceSpec, newFromSlicePkStackSpecX, newFromSlicePkStackSpecAt,
    stackAt_pkX_eq_nfs, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw

def session2MemcpyPkStackSpecAt (pkStack : Nat) (sp_cur : BitVec 64) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
      s0.sp = sp_cur⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt sp_cur pkStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt sp_cur pkStack

abbrev session2MemcpyPkStackSpecX (sp_cur : BitVec 64) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  session2MemcpyPkStackSpecAt publicKeySerializeStackX sp_cur

private theorem memcpy_pkStack_ok_at2_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (sp_cur : BitVec 64)
    (hA : AllocContractsX img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff memcpyName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((session2MemcpyPkStackSpecX sp_cur).inImage img) := by
  have hm := hA.session_memcpy_region_ok_at name k publicKeySerializeStackX (by decide) (by decide) hk
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, session2MemcpyPkStackSpecX, session2MemcpyPkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hsp_eq⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((withStack sessionMemcpyRegionSpec publicKeySerializeStackX).inImage img).pre
      (dst, src, bs) s0 ∗ R := by
    simp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, framelessMemcpySpec,
      hsp_eq, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2⟩, hmem⟩
  refine subroutine_ok.mono_outcome hm (dst, src, bs) R s0 hpc hrun hpre' hsp fun _ hraw => ?_
  unfold SubroutineOutcome at hraw ⊢
  simpa only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, framelessMemcpySpec,
    session2MemcpyPkStackSpecX, session2MemcpyPkStackSpecAt, hsp_eq, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw

def session2Compress256PkStackSpecAt (F : ShaCompress) (pkStack : Nat) (sp_cur : BitVec 64) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) where
  pre := fun (stA, st, blkA, blk, n) s0 =>
    ⌜s0.readReg64 .x0 = stA ∧ s0.readReg64 .x1 = blkA ∧
      (s0.readReg64 .x2).toNat = n ∧ blk.length = 64 * n ∧ s0.sp = sp_cur⌝ ∗
      (stA ↦ₛ shaStateBytes st) ∗ (blkA ↦ₛ blk) ∗ stackAt sp_cur pkStack
  post := fun (stA, st, blkA, blk, _n) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (stA ↦ₛ shaStateBytes ((chunks64 blk).foldl F st)) ∗ (blkA ↦ₛ blk) ∗
      stackAt sp_cur pkStack

abbrev session2Compress256PkStackSpecX (F : ShaCompress) (sp_cur : BitVec 64) :
    Spec (BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) :=
  session2Compress256PkStackSpecAt F publicKeySerializeStackX sp_cur

private theorem compress256_pkStack_ok_at2_ext_x {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} (sp_cur : BitVec 64)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr compress256Name)
      ((withStack (compress256Spec F) extHookStack).inImage img))
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff compress256Name := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((session2Compress256PkStackSpecX F sp_cur).inImage img) := by
  have hc := sub_ok_at_of_fnAddr hcomp name k hk
  refine subroutine_ok_outcome_intro fun ⟨stA, st, blkA, blk, n⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, session2Compress256PkStackSpecX, session2Compress256PkStackSpecAt, stackAt_pkX_eq_ext,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hblk, hsp_eq⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((withStack (compress256Spec F) extHookStack).inImage img).pre
      (stA, st, blkA, blk, n) s0 ∗ (memRegion (sp_cur - 16416#64) 32 ∗ R) := by
    simp only [Spec.inImage, withStack, compress256Spec, session2Compress256Spec,
      hsp_eq, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hblk⟩, hmem⟩
  refine subroutine_ok.mono_outcome hc (stA, st, blkA, blk, n) (memRegion (sp_cur - 16416#64) 32 ∗ R) s0 hpc hrun hpre' hsp fun _ hraw => ?_
  unfold SubroutineOutcome at hraw ⊢
  simpa only [Spec.inImage, withStack, compress256Spec, session2Compress256Spec,
    session2Compress256PkStackSpecX, session2Compress256PkStackSpecAt, hsp_eq, stackAt_pkX_eq_ext, satisfies_pure_sepConj,
    false_and, sepConj_assoc] using hraw

def rustDeallocPkStackSpecAt (A : RustAlloc) (pkStack : Nat) : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (p, bs) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ (s.readReg64 .x2).toNat = 1 ∧
      bs.length = 33⌝ ∗
      A.pool ∗ A.live p bs.length 1 ∗ (p ↦ₛ bs) ∗ stackAt s.sp pkStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp pkStack

abbrev rustDeallocPkStackSpecX (A : RustAlloc) : Spec (BitVec 64 × List (BitVec 8)) :=
  rustDeallocPkStackSpecAt A publicKeySerializeStackX

private theorem dealloc_pkStack_ok_at2_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustDeallocPkStackSpecX A).inImage img) := by
  have hdeel := hA.dealloc_ok_at (name := name) (k := k) hk
  refine subroutine_ok_outcome_intro fun ⟨p, bs⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ ((rustDeallocExternSpecWithStack A extHookStack).inImage img).pre
      (p, bs.length, 1) s0 ∗ (memRegion (s0.sp - 16416#64) 32 ∗ R) := by
    simp only [Spec.inImage, rustDeallocExternSpecWithStack, rustDeallocPkStackSpecX, rustDeallocPkStackSpecAt,
      stackAt_pkX_eq_ext, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hbs⟩, hmem⟩
    have hlay : LayoutOk bs.length 1 := by
      rw [hbs]; exact ⟨by decide, ⟨0, rfl⟩, by decide⟩
    refine ⟨hinv, ⟨hx0, hx1, hx2, hlay⟩, ?_⟩
    have hm : s0.mem ⊨ (p ↦ₛ bs) ∗ (A.pool ∗ A.live p bs.length 1 ∗
        stackAt s0.sp extHookStack ∗ memRegion (s0.sp - 16416#64) 32 ∗ R) := by
      refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hmem
      ac_rfl
    have hm2 := Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion p bs)) hm
    refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hm2
    ac_rfl
  refine subroutine_ok.mono_outcome hdeel (p, bs.length, 1) (memRegion (s0.sp - 16416#64) 32 ∗ R) s0 hpc hrun hpre' hsp fun _ hraw => ?_
  unfold SubroutineOutcome at hraw ⊢
  simpa only [Spec.inImage, rustDeallocExternSpecWithStack, rustDeallocPkStackSpecX, rustDeallocPkStackSpecAt,
    stackAt_pkX_eq_ext, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw

def session2MemsetPkStackSpecAt (pkStack : Nat) (sp_cur : BitVec 64) :
    Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := fun (dst, val, n) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ (s0.readReg64 .x1).truncate 8 = val ∧
      (s0.readReg64 .x2).toNat = n ∧ s0.sp = sp_cur⌝ ∗
      memRegion dst n ∗ stackAt sp_cur pkStack
  post := fun (dst, val, n) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ List.replicate n val) ∗ stackAt sp_cur pkStack

abbrev session2MemsetPkStackSpecX (sp_cur : BitVec 64) :
    Spec (BitVec 64 × BitVec 8 × Nat) :=
  session2MemsetPkStackSpecAt publicKeySerializeStackX sp_cur

private theorem memset_pkStack_ok_at2_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (sp_cur : BitVec 64)
    (hA : AllocContractsX img A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff memsetName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((session2MemsetPkStackSpecX sp_cur).inImage img) := by
  have hm := hA.session_memset_region_ok_at name k publicKeySerializeStackX (by decide) (by decide) hk
  refine subroutine_ok_outcome_intro fun ⟨dst, val, n⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, session2MemsetPkStackSpecX, session2MemsetPkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hsp_eq⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((withStack sessionMemsetRegionSpec publicKeySerializeStackX).inImage img).pre
      (dst, val, n) s0 ∗ R := by
    simp only [Spec.inImage, withStack, sessionMemsetRegionSpec, memsetRegionSpec,
      hsp_eq, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ⟨hx0, ?_, hx2, by rw [← hx2]; exact Nat.le_of_lt (s0.readReg64 .x2).isLt⟩, hmem⟩
    rw [← hx1]; dsimp [State.readReg32]; bv_bits
  refine subroutine_ok.mono_outcome hm (dst, val, n) R s0 hpc hrun hpre' hsp fun _ hraw => ?_
  unfold SubroutineOutcome at hraw ⊢
  simpa only [Spec.inImage, withStack, sessionMemsetRegionSpec, memsetRegionSpec,
    session2MemsetPkStackSpecX, session2MemsetPkStackSpecAt, hsp_eq, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw

private theorem publicKeySerialize_ok_at2_ext_x (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hpk : PublicKeySerializeOkX img A ext)
    (entry : BitVec 64) (hfn : entry = (tripleRatchetProgAtExt img.base ext).fnAddr computeMacName) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      ((publicKeySerializeSpecX A).inImage img) := by
  have heq : entry + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") = (tripleRatchetProgAtExt img.base ext).fnAddr publicKeySerializeName := by
    subst hfn
    dsimp only [tripleRatchetProgAtExt]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::compute_mac"),
      (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::serialize")]
    bv_omega
  exact heq ▸ hpk

theorem stackAt_computeMacX_eq (sp : BitVec 64) :
    stackAt sp computeMacStackX =
      stackAt (sp - 496#64) publicKeySerializeStackX ∗
      computeMacFramePad sp ∗
      cells (sp - 496#64) 18 ∗
      memRegion (sp - 352#64) 0x98 ∗
      memRegion (sp - 192#64) 24 ∗
      memRegion (sp - 160#64) 24 ∗
      (∃∗ v, (sp - 168#64) ↦₆₄ v) ∗
      (∃∗ v, (sp - 136#64) ↦₆₄ v) ∗
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
       ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64, ∃∗ s6 : BitVec 64, ∃∗ s7 : BitVec 64,
       ∃∗ s8 : BitVec 64, ∃∗ s9 : BitVec 64, ∃∗ s10 : BitVec 64, ∃∗ s11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ s0) ∗ ((sp - 88#64) ↦₆₄ s1) ∗ ((sp - 80#64) ↦₆₄ s2) ∗ ((sp - 72#64) ↦₆₄ s3) ∗
        ((sp - 64#64) ↦₆₄ s4) ∗ ((sp - 56#64) ↦₆₄ s5) ∗ ((sp - 48#64) ↦₆₄ s6) ∗ ((sp - 40#64) ↦₆₄ s7) ∗
        ((sp - 32#64) ↦₆₄ s8) ∗ ((sp - 24#64) ↦₆₄ s9) ∗ ((sp - 16#64) ↦₆₄ s10) ∗ ((sp - 8#64) ↦₆₄ s11)) :=
  stackAt_computeMacAt_eq publicKeySerializeStackX (by decide) sp

theorem call_pk_serialize_at {prog : Program} {img : Obj.Image} {ret callee : BitVec 64}
    {A : RustAlloc} {pkStack : Nat} {s0 s : State} {P F R : SepProp} {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog callee ((publicKeySerializeSpecAt A pkStack).inImage img))
    (ret_pc sp_cur keyA : BitVec 64) (key : PublicKey)
    (hP : P = ((keyA ↦ₛ key.bytes.toList) ∗ A.pool ∗
      stackAt sp_cur pkStack) ∗ F)
    (hside : img.FrozenLoaded s ∧ s.symtab = img.symtab ∧
      s.pc = callee ∧ s.status = .Running ∧ s.spAligned = true ∧
      s.sp = sp_cur ∧ s.readReg64 Reg.lr = ret_pc ∧ s.trace = s0.trace ∧
      s.readReg64 (Reg.gpr 0#5) = keyA)
    (hnext : ∀ (sf : State),
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_cur → RegsSaved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0 → sf.readReg64 (Reg.gpr 1#5) = 33#64 →
      sf.trace = s0.trace →
      SepWPp prog ret sf
        ((keyA ↦ₛ key.bytes.toList) ∗
          A.live (sf.readReg64 (Reg.gpr 0#5)) key.serialize.length 1 ∗
          (sf.readReg64 (Reg.gpr 0#5) ↦ₛ key.serialize) ∗
          A.pool ∗ stackAt sp_cur pkStack ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  rcases hside with ⟨hF_s, hsym_s, hpc, hrun, hsp, hsp_cur, hlr, htr, hφ⟩
  have hφ' : (img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧ s.readReg64 (Reg.gpr 0#5) = keyA :=
    ⟨⟨hF_s, hsym_s⟩, hφ⟩
  refine SepWPp.call_frame (x := ⟨keyA, key⟩) (publicKeySerializeKeepAt_of_inImage hcall) hpc hrun hsp hlr
    (by simp only [publicKeySerializeSpecKeepAt, publicKeySerializeSpecAt, hsp_cur, Reg.x0, sepConj_assoc])
    hφ' hP
    (fun sf code R' _ hm => by
      dsimp only [publicKeySerializeSpecKeepAt, publicKeySerializeSpecAt] at hm
      exact allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [publicKeySerializeSpecKeepAt, publicKeySerializeSpecAt] at hm
      exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm)
    (fun sf hpcm hrunm hspm hcsm => ?_)
  have hne : key.serialize ≠ [] := by simp [PublicKey.serialize]
  conv =>
    arg 4
    simp only [publicKeySerializeSpecKeepAt, publicKeySerializeSpecAt, boxU8Buf, hne, ite_false,
      hsp_cur, Reg.x0, Reg.x1, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hF_sf, hsym_sf⟩ => ?_
  refine SepWPp.pure_elim fun ⟨hx1, htr'⟩ => ?_
  conv =>
    arg 4
    rw [sepConj_left_comm (keyA ↦ₛ key.bytes.toList)]
  refine SepWPp.pure_elim fun ⟨hx0, _⟩ => ?_
  exact hnext sf hF_sf hsym_sf hpcm hrunm (hspm.trans hsp_cur) (regsSaved_of_calleeSavedPreserved hcsm)
    hx0 hx1 (htr'.trans htr)

theorem call_pk_serialize_x {prog : Program} {img : Obj.Image} {ret callee : BitVec 64}
    {A : RustAlloc} {s0 s : State} {P F R : SepProp} {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog callee ((publicKeySerializeSpecX A).inImage img))
    (ret_pc sp_cur keyA : BitVec 64) (key : PublicKey)
    (hP : P = ((keyA ↦ₛ key.bytes.toList) ∗ A.pool ∗
      stackAt sp_cur publicKeySerializeStackX) ∗ F)
    (hside : img.FrozenLoaded s ∧ s.symtab = img.symtab ∧
      s.pc = callee ∧ s.status = .Running ∧ s.spAligned = true ∧
      s.sp = sp_cur ∧ s.readReg64 Reg.lr = ret_pc ∧ s.trace = s0.trace ∧
      s.readReg64 (Reg.gpr 0#5) = keyA)
    (hnext : ∀ (sf : State),
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_cur → RegsSaved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0 → sf.readReg64 (Reg.gpr 1#5) = 33#64 →
      sf.trace = s0.trace →
      SepWPp prog ret sf
        ((keyA ↦ₛ key.bytes.toList) ∗
          A.live (sf.readReg64 (Reg.gpr 0#5)) key.serialize.length 1 ∗
          (sf.readReg64 (Reg.gpr 0#5) ↦ₛ key.serialize) ∗
          A.pool ∗ stackAt sp_cur publicKeySerializeStackX ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) :=
  call_pk_serialize_at (pkStack := publicKeySerializeStackX) hcall ret_pc sp_cur keyA key hP hside hnext

set_option maxHeartbeats 1600000 in
theorem computeMac_ok_of_hooks_gen (pkStack : Nat) (hbound : pkStack + 496 < 2 ^ 64)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hnew_at : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      ((newFromSlicePkStackSpecAt C.F pkStack).inImage img))
    (hpk_at : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      ((publicKeySerializeSpecAt A pkStack).inImage img))
    (hmemcpy_all : ∀ sp_cur, subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")))
      ((session2MemcpyPkStackSpecAt pkStack sp_cur).inImage img))
    (hcompress_all : ∀ sp_cur, subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName + BitVec.ofNat 64 (num% (ls_off% "sha2::sha256::compress256" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")))
      ((session2Compress256PkStackSpecAt C.F pkStack sp_cur).inImage img))
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")))
      ((rustDeallocPkStackSpecAt A pkStack).inImage img))
    (hmemset_all : ∀ sp_cur, subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName + BitVec.ofNat 64 (num% (ls_off% "memset" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")))
      ((session2MemsetPkStackSpecAt pkStack sp_cur).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((computeMacSpecAt C.F A pkStack).inImage img) := by
  simp only [Spec.inImage, computeMacSpecAt, stackAt_computeMacAt_eq pkStack hbound,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  have hfn := computeMac_fnOff
  s2_ext_fetches (img.base) ext hfn 118720 1264
  clear hfn
  dsimp only [tripleRatchetProgAtExt, computeMacName] at *
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<libsignal_protocol::protocol::SignalMessage>::compute_mac" = entry
  wpp_init x s0
  have hmemcpy := hmemcpy_all (s0.sp - 496#64)
  have hcompress := hcompress_all (s0.sp - 496#64)
  have hmemset := hmemset_all (s0.sp - 496#64)
  clear hmemcpy_all hcompress_all hmemset_all
  examples_hide_fetches
  obtain ⟨ret, senderA, sender, receiverA, receiver, keyA, macKey, msgA, message⟩ := x
  dsimp only at *
  have hk_len := keyToBytes32_length macKey
  have hk_le : (keyToBytes32 macKey).length ≤ 64 := keyToBytes32_length_le_64 macKey
  have hlen_s : sender.publicKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have hlen_r : receiver.publicKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have hlen_r31 : (receiver.publicKey.serialize.take 31).length = 31 := by simp [PublicKey.serialize]
  have hlen_r2 : (receiver.publicKey.serialize.drop 31).length = 2 := by simp [PublicKey.serialize]
  have hblk2_len : (sender.publicKey.serialize ++ receiver.publicKey.serialize.take 31).length = 64 * 1 := by
    simp [PublicKey.serialize]
  have hx6_eq : s0.readReg64 (Reg.gpr 6#5) = BitVec.ofNat 64 message.length := by
    rw [← ‹(s0.readReg64 (Reg.gpr 6#5)).toNat = message.length›]
    simp
  refine of_sepWP_inImage (entry + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")) ‹img.FrozenLoaded s0› ‹s0.symtab = img.symtab› ?_
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF1 hsym1
  refine of_sepWP_inImage (entry + bv% (76)) hF1 hsym1 ?_
  wp_call hnew_at ⟨s0.sp - 352#64, keyA, keyToBytes32 macKey⟩
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF1a hsym1a
  clear hF1 hsym1 m m_1 m_2 m_3 m_4 m_5
  conv =>
    arg 4
    rw [hmacCoreAt_nil_eq_words64 C.F (s0.sp - 344#64) (keyToBytes32 macKey),
      cells_496_18_eq s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
    SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c9 =>
    SepWPp.exists_elim fun c10 => SepWPp.exists_elim fun c11 =>
    SepWPp.exists_elim fun c12 => SepWPp.exists_elim fun c13 =>
    SepWPp.exists_elim fun c14 => SepWPp.exists_elim fun c15 =>
    SepWPp.exists_elim fun c16 => SepWPp.exists_elim fun c17 =>
    SepWPp.exists_elim fun pad0 => ?_
  conv =>
    arg 4
    simp only [hmacWords64At, arm64_norm, sepConj_assoc]
  refine of_sepWP_inImage (entry + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")) hF1a hsym1a ?_
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF1b hsym1b
  clear c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17
  apply SepWPp.fold (fold_19_words_352 s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  · sep_focus
  apply SepWPp.fold
    (fold_18_words_496 s0.sp (hmacInnerInit C.F (keyToBytes32 macKey)) 1
      (hmacOuterInit C.F (keyToBytes32 macKey)) pad0.1 pad0.2)
  · sep_focus
  apply call_pk_serialize_at hpk_at (entry + bv% (164)) (s0.sp - 496#64) senderA sender.publicKey
  · sep_focus
  · refine ⟨hF1b, hsym1b, by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      spAligned_of_sub_496 s0.sp (by simp only [arm64_norm, *]) hsp_align,
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
  intro sf2 hF2 hsym2 hpc2 hrun2 hsp2 hcs2 hptr1 hx1_2 htr2
  simp only [RegsSaved, arm64_norm, *] at hcs2
  rcases hcs2 with ⟨h2_19, h2_20, h2_21, h2_22, h2_23, h2_24, h2_25, h2_26, h2_27, h2_28, h2_29, h2_v⟩
  refine of_sepWP_inImage (entry + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")) hF2 hsym2 ?_
  wp_steps_inImage (entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
  refine seq_inImage_compute (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")) ‹_› ‹_› ?_
  wp_call hmemcpy (s0.sp - 496#64, sf2.readReg64 (Reg.gpr 0#5), sender.publicKey.serialize)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF_step1 hsym_step1
  wp_call hdealloc (sf2.readReg64 (Reg.gpr 0#5), sender.publicKey.serialize)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF2a hsym2a
  have hsp_sf1 : sf_1.sp = s0.sp - 496#64 := by simp only [arm64_norm, *]
  conv =>
    arg 4
    rw [hsp_sf1]
  apply call_pk_serialize_at hpk_at (entry + bv% (400)) (s0.sp - 496#64) receiverA receiver.publicKey
  · sep_focus
  · refine ⟨hF2a, hsym2a, by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      spAligned_of_sub_496 s0.sp (by simp only [arm64_norm, *]) hsp_align,
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
  intro sf5 hF5 hsym5 hpc5 hrun5 hsp5 hcs5 hptr2 hx1_5 htr5
  simp only [RegsSaved, arm64_norm, *] at hcs5
  rcases hcs5 with ⟨h5_19, h5_20, h5_21, h5_22, h5_23, h5_24, h5_25, h5_26, h5_27, h5_28, h5_29, h5_v⟩
  refine of_sepWP_inImage (entry + bv% (544)) hF5 hsym5 ?_
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF5a hsym5a
  apply SepWPp.fold (fold_pre_memcpy_31 s0.sp (sf5.readReg64 (Reg.gpr 0#5))
    receiver.publicKey.serialize 33#8 hlen_r)
  · sep_focus
  refine of_sepWP_inImage (entry + bv% (548)) hF5a hsym5a ?_
  wp_steps_inImage (entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
  wp_call hmemcpy (s0.sp - 463#64, sf5.readReg64 (Reg.gpr 0#5),
    receiver.publicKey.serialize.take 31)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF5b hsym5b
  apply SepWPp.fold (fold_blk2 s0.sp sender.publicKey.serialize
    (receiver.publicKey.serialize.take 31) hlen_s)
  · sep_focus
  refine of_sepWP_inImage (entry + bv% (576)) hF5b hsym5b ?_
  wp_steps_inImage (entry + bv% (ls_off% "sha2::sha256::compress256" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
  wp_call hcompress (s0.sp - 432#64, hmacInnerInit C.F (keyToBytes32 macKey),
    s0.sp - 496#64, sender.publicKey.serialize ++ receiver.publicKey.serialize.take 31, 1)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF5c hsym5c
  apply SepWPp.fold (fold_post_blk2 s0.sp
    (sender.publicKey.serialize ++ receiver.publicKey.serialize.take 31)
    receiver.publicKey.serialize hblk2_len hlen_r)
  · sep_focus
  conv =>
    arg 4
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b63 => ?_
  refine of_sepWP_inImage (entry + bv% (644)) hF5c hsym5c ?_
  wp_steps_inImage (entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
  wp_call hmemcpy (s0.sp - 496#64, sf5.readReg64 (Reg.gpr 0#5) + 31#64,
    receiver.publicKey.serialize.drop 31)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF5d hsym5d
  apply SepWPp.fold (fold_rejoin_31 (sf5.readReg64 (Reg.gpr 0#5))
    receiver.publicKey.serialize hlen_r)
  · sep_focus
  refine of_sepWP_inImage (entry + bv% (660)) hF5d hsym5d ?_
  wp_steps_inImage (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
  wp_call hdealloc (sf5.readReg64 (Reg.gpr 0#5), receiver.publicKey.serialize)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF5e hsym5e
  have hsp_sf5 : sf_5.sp = s0.sp - 496#64 := by simp only [arm64_norm, *]
  have hlen_toNat : (BitVec.ofNat 64 message.length).toNat = message.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  conv =>
    arg 4
    rw [hsp_sf5, mkMacEnv_hState_two C.F sender receiver macKey message,
      mkMacEnv_oState1 C.F sender receiver macKey message]
  apply SepWPp.fold (fold_stk_192_64 s0.sp _ _)
  · sep_focus
  have hvregs_sf_6 : calleeSavedVRegs sf_6 = calleeSavedVRegs s0 := by simp only [arm64_norm, *]
  simp only [arm64_norm, *] at hsp_sf_6 h_73 h_74 h_75 h_79 h_80 h_81 h_82 hcs_sf_6 hpost_6
  run_tac clearDepsTac #[`sf, `sf2, `sf_1, `sf_2, `sf5, `sf_3, `sf_4, `sf_5, `m, `m_1, `m_2, `m_3, `m_4, `m_5, `m_6, `m_7, `pad0, `b63]
  refine SepWPp.with_join
    (memRegion (s0.sp - 192#64) 64 ∗
      hmacStateAt (s0.sp - 496#64)
        ((mkMacEnv sender receiver macKey message).hState C.F
          (mkMacEnv sender receiver macKey message).innerB)
        (mkMacEnv sender receiver macKey message).innerB
        ((mkMacEnv sender receiver macKey message).oState1 C.F)
        (mkMacEnv sender receiver macKey message).innerTail ∗
      msgA ↦ₛ message ∗
      A.pool ∗
      stackAt (s0.sp - 496#64) pkStack ∗
      receiverA ↦ₛ receiver.publicKey.bytes.toList ∗
      senderA ↦ₛ sender.publicKey.bytes.toList ∗
      memRegion (s0.sp - 352#64) 152 ∗
      keyA ↦ₛ keyToBytes32 macKey ∗
      memRegion ret 16 ∗
      computeMacFramePad s0.sp ∗
      (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
      (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
    (fun sm =>
      img.FrozenLoaded sm ∧
      sm.symtab = img.symtab ∧
      sm.pc = entry + bv% (808) ∧
      sm.status = ExecStatus.Running ∧
      sm.sp = s0.sp - 496#64 ∧
      sm.trace = s0.trace ∧
      sm.readReg64 (Reg.gpr 19#5) = ret ∧
      sm.readReg64 (Reg.gpr 27#5) = s0.sp - 352#64 ∧
      sm.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ (fun hjoin808 => ?_)
  · run_tac clearDepsTac #[`sf_6, `hnew_at, `hpk_at, `hmemcpy, `hdealloc]
    rintro sm808 ⟨hF808, hsym808, hpc808, hrun808, hsp808, htr808, h808_19, h808_27, h808_29, hv808⟩
    have htail_len := mkMacEnv_innerTail_length sender receiver macKey message
    have htail_lt := mkMacEnv_innerTail_length_lt sender receiver macKey message
    have hpos_lt : (mkMacEnv sender receiver macKey message).innerPos < 64 :=
      htail_len ▸ htail_lt
    have hzext_tail :
        BitVec.zeroExtend 64 (BitVec.ofNat 8 (mkMacEnv sender receiver macKey message).innerPos) =
          BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos :=
      zext64_ofNat8_eq hpos_lt
    have hxor_tail :
        BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos ^^^ 63#64 =
          BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos) :=
      ofNat64_xor_63 hpos_lt
    have hsub63_toNat :
        (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).toNat =
          63 - (mkMacEnv sender receiver macKey message).innerPos := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hbitlen :
        (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB <<< 9) |||
          (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos <<< 3) =
          BitVec.ofNat 64 (8 * (mkMacEnv sender receiver macKey message).innerMsg.length) :=
      LibsignalHmac.MD.bitlen (mkMacEnv sender receiver macKey message) hk_len
    have hlast_blk_len64 :
        ((mkMacEnv sender receiver macKey message).innerPadded.drop
          ((mkMacEnv sender receiver macKey message).innerPadded.length - 64)).length = 64 := by
      obtain ⟨hdrop_eq, h56_len⟩ := mkMacEnv_innerPadded_drop_eq sender receiver macKey message
      rw [hdrop_eq, List.length_append, h56_len, toBEBytes_len]
    have hlast_blk_len :
        ((mkMacEnv sender receiver macKey message).innerPadded.drop
          ((mkMacEnv sender receiver macKey message).innerPadded.length - 64)).length = 64 * 1 :=
      hlast_blk_len64
    have houter_blk_len64 :
        ((sha256Pad ((mkMacEnv sender receiver macKey message).outerMsg C.F)).drop 64).length = 64 := by
      rw [LibsignalHmac.MD.outer_block (mkMacEnv sender receiver macKey message) C.F hk_len]
      simp [innerHash_len, toBEBytes_len]
    have houter_blk_len :
        ((sha256Pad ((mkMacEnv sender receiver macKey message).outerMsg C.F)).drop 64).length = 64 * 1 :=
      houter_blk_len64
    have hlast_blk_len_sub :
        (mkMacEnv sender receiver macKey message).innerPadded.length -
          ((mkMacEnv sender receiver macKey message).innerPadded.length - 64) = 64 := by
      simpa only [List.length_drop] using hlast_blk_len64
    have houter_blk_len_sub :
        (sha256Pad ((mkMacEnv sender receiver macKey message).outerMsg C.F)).length - 64 = 64 := by
      simpa only [List.length_drop] using houter_blk_len64
    conv =>
      arg 4
      rw [hmacStateAt_eq_words64_sub (s0.sp - 496#64)
        ((mkMacEnv sender receiver macKey message).hState C.F
          (mkMacEnv sender receiver macKey message).innerB)
        (mkMacEnv sender receiver macKey message).innerB
        ((mkMacEnv sender receiver macKey message).oState1 C.F)
        (mkMacEnv sender receiver macKey message).innerTail htail_lt,
        memRegion_352_152_eq s0.sp, cells_352_18_eq s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
      SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
      SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun d5 =>
      SepWPp.exists_elim fun d6 => SepWPp.exists_elim fun d7 =>
      SepWPp.exists_elim fun d8 => SepWPp.exists_elim fun d9 =>
      SepWPp.exists_elim fun d10 => SepWPp.exists_elim fun d11 =>
      SepWPp.exists_elim fun d12 => SepWPp.exists_elim fun d13 =>
      SepWPp.exists_elim fun d14 => SepWPp.exists_elim fun d15 =>
      SepWPp.exists_elim fun d16 => SepWPp.exists_elim fun d17 =>
      SepWPp.exists_elim fun pad_tail => ?_
    conv =>
      arg 4
      simp only [hmacWords64At, arm64_norm, sepConj_assoc]
    refine of_sepWP_inImage (entry + bv% (864)) hF808 hsym808 ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF808a hsym808a
    apply SepWPp.fold (fold_18_words_496_cells s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    · sep_focus
    conv =>
      arg 4
      rw [word7_296_eq s0.sp htail_lt pad_tail.2]
      simp only [sepConj_assoc]
    refine of_sepWP_inImage (entry + bv% (888)) hF808a hsym808a ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF808b hsym808b
    clear d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
    apply SepWPp.fold (fold_post_copy_352 s0.sp
      ((mkMacEnv sender receiver macKey message).hState C.F
        (mkMacEnv sender receiver macKey message).innerB)
      (mkMacEnv sender receiver macKey message).innerB
      ((mkMacEnv sender receiver macKey message).oState1 C.F)
      htail_lt pad_tail.2)
    · sep_focus
    conv =>
      arg 4
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b_pad0 => ?_
    conv =>
      arg 4
      rw [htail_len]
    refine of_sepWP_inImage (entry + bv% (896)) hF808b hsym808b ?_
    wp_steps_inImage (entry + bv% (ls_off% "memset" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
    wp_call hmemset
      (s0.sp - 352#64 +
        BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos + 1#64,
       0#8,
       63 - (mkMacEnv sender receiver macKey message).innerPos)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF808c hsym808c
    conv =>
      arg 4
      rw [← htail_len]
    apply SepWPp.fold (fold_post_memset_352 s0.sp (mkMacEnv sender receiver macKey message).innerTail)
    · sep_focus
    conv =>
      arg 4
      rw [htail_len]
    refine SepWPp.with_join
      (words7At352 s0.sp (((mkMacEnv sender receiver macKey message).innerPadded.drop
          ((mkMacEnv sender receiver macKey message).innerPadded.length - 64)).take 56) ∗
        (∃∗ w7 : BitVec 64, (s0.sp - 296#64) ↦₆₄ w7) ∗
        memRegion (s0.sp - 192#64) 64 ∗
        ((s0.sp - 288#64) ↦ₛ shaStateBytes
          ((chunks64 ((mkMacEnv sender receiver macKey message).innerPadded.take
            ((mkMacEnv sender receiver macKey message).innerPadded.length - 64))).foldl C.F sha256IV)) ∗
        ((s0.sp - 256#64) ↦₆₄ BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB) ∗
        ((s0.sp - 248#64) ↦ₛ shaStateBytes ((mkMacEnv sender receiver macKey message).oState1 C.F)) ∗
        ((s0.sp - 216#64) ↦₆₄ 1#64) ∗
        memRegion (s0.sp - 208#64) 8 ∗
        cells (s0.sp - 496#64) 18 ∗
        msgA ↦ₛ message ∗
        A.pool ∗
        stackAt (s0.sp - 496#64) pkStack ∗
        receiverA ↦ₛ receiver.publicKey.bytes.toList ∗
        senderA ↦ₛ sender.publicKey.bytes.toList ∗
        keyA ↦ₛ keyToBytes32 macKey ∗
        memRegion ret 16 ∗
        computeMacFramePad s0.sp ∗
        (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
        (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
        (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
        (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
        (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
        (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
        (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
        (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
        (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
      (fun sm =>
        img.FrozenLoaded sm ∧
        sm.symtab = img.symtab ∧
        sm.pc = entry + bv% (952) ∧
        sm.status = ExecStatus.Running ∧
        sm.sp = s0.sp - 496#64 ∧
        sm.trace = s0.trace ∧
        sm.readReg64 (Reg.gpr 19#5) = ret ∧
        sm.readReg64 (Reg.gpr 20#5) = s0.sp - 352#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = 0x80#64 ∧
        sm.readReg64 (Reg.gpr 23#5) =
          BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos ∧
        sm.readReg64 (Reg.gpr 24#5) =
          BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB ∧
        sm.readReg64 (Reg.gpr 27#5) = s0.sp - 352#64 ∧
        sm.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ (fun hjoin952 => ?_)
    · run_tac clearDepsTac #[`sm808, `sf, `sf_7, `b_pad0, `pad_tail, `hmemset]
      rintro sm952 ⟨hF952, hsym952, hpc952, hrun952, hsp952, htr952, h952_19, h952_20, h952_22, h952_23, h952_24, h952_27, h952_29, hv952⟩
      conv =>
        arg 4
        rw [cells_192_8_eq s0.sp]
        dsimp only [words7At352]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun w7_pad =>
        SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
        SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
        SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
        SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun b7 => ?_
      refine of_sepWP_inImage (entry + bv% (996)) hF952 hsym952 ?_
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF952a hsym952a
      clear w7_pad b0 b1 b2 b3 b4 b5 b6 b7
      refine SepWPp.fold (fold_pre_compress7 s0.sp sender receiver macKey message _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine of_sepWP_inImage (entry + bv% (1000)) hF952a hsym952a ?_
      wp_steps_inImage (entry + bv% (ls_off% "sha2::sha256::compress256" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      wp_call hcompress (s0.sp - 288#64,
        (chunks64 ((mkMacEnv sender receiver macKey message).innerPadded.take
          ((mkMacEnv sender receiver macKey message).innerPadded.length - 64))).foldl C.F sha256IV,
        s0.sp - 192#64,
        (mkMacEnv sender receiver macKey message).innerPadded.drop
          ((mkMacEnv sender receiver macKey message).innerPadded.length - 64),
        1)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF952b hsym952b
      conv =>
        arg 4
        rw [chunks64_of_length_64 hlast_blk_len64, List.foldl_cons, List.foldl_nil,
          pointsToBytes_shaStateBytes_288_eq s0.sp, memRegion_352_64_pre_outer_eq s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun u7 => SepWPp.exists_elim fun u6 =>
        SepWPp.exists_elim fun u5 => SepWPp.exists_elim fun u4 =>
        SepWPp.exists_elim fun u3 => SepWPp.exists_elim fun u2 =>
        SepWPp.exists_elim fun u1 => SepWPp.exists_elim fun u0 =>
        SepWPp.exists_elim fun b320 => SepWPp.exists_elim fun z319 =>
        SepWPp.exists_elim fun z311 => ?_
      refine of_sepWP_inImage (entry + bv% (1096)) hF952b hsym952b ?_
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF952c hsym952c
      clear u7 u6 u5 u4 u3 u2 u1 u0 b320 z319 z311
      apply SepWPp.fold (fold_at_1d408 C.F s0.sp sender receiver macKey message _ rfl)
      · sep_focus
      conv =>
        arg 4
        rw [cells_192_8_eq s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun w6 => SepWPp.exists_elim fun w7 =>
        SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
        SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
        SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
        SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun b7 => ?_
      refine of_sepWP_inImage (entry + bv% (1124)) hF952c hsym952c ?_
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF952d hsym952d
      clear w6 w7 b0 b1 b2 b3 b4 b5 b6 b7
      refine SepWPp.fold (fold_pre_compress8 C.F s0.sp sender receiver macKey message _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      conv =>
        arg 4
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun b_cf => ?_
      refine of_sepWP_inImage (entry + bv% (1128)) hF952d hsym952d ?_
      wp_steps_inImage (entry + bv% (ls_off% "sha2::sha256::compress256" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      wp_call hcompress (s0.sp - 248#64,
        (mkMacEnv sender receiver macKey message).oState1 C.F,
        s0.sp - 192#64,
        (sha256Pad ((mkMacEnv sender receiver macKey message).outerMsg C.F)).drop 64,
        1)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF952e hsym952e
      conv =>
        arg 4
        rw [chunks64_of_length_64 houter_blk_len64, List.foldl_cons, List.foldl_nil,
          pointsToBytes_shaStateBytes_248_eq s0.sp]
        simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (1140))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      apply SepWPp.fold (fold_at_1d434 s0.sp ret _ _ _ houter_blk_len64)
      · sep_focus
      conv =>
        arg 4
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
        SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
        SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
        SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
        SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
        SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
        SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
        SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun b7 =>
        SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 => ?_
      apply SepWPp.of_sepWP (mid := s0.readReg64 Reg.lr)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      clear c0 c1 c2 c3 c4 c5 c6 c7 b0 b1 b2 b3 b4 b5 b6 b7 r0 r1
      refine SepWPp.fold (fold_epilogue_post C.F s0.sp ret sender receiver macKey message _ rfl _
        ?_ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        ⟨fun hm => ?_, by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *]⟩
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        sepConj_assoc] at hm ⊢
      rcases hm with ⟨v168, v136, s0', s1', s2', s3', s4', s5', s6', s7', s8', s9', s10', s11', hm⟩
      refine ⟨v168, v136, s0', s1', s2', s3', s4', s5', s6', s7', s8', s9', s10', s11', ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨by simp only [arm64_norm, *], Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
    by_cases hpad : (mkMacEnv sender receiver macKey message).innerPos < 56
    · have hhi_ult :
          (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ult 7#64 = false := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
      have hhi_ult' :
          ¬ (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ult 7#64 = true := by
        rw [hhi_ult]; decide
      have hhi_ne :
          BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos) ≠ 7#64 := by
        intro heq; have := congrArg BitVec.toNat heq; simp [BitVec.toNat_ofNat] at this; omega
      have hhi_beq :
          (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos) == 7#64) = false :=
        beq_false_of_ne hhi_ne
      have hhi_gt :
          (7#64 : BitVec 64).ult (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)) = true := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
      have hhi_ule :
          (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ule 7#64 = false := by
        simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
      refine of_sepWP_inImage (entry + bv% (952)) hF808c hsym808c ?_
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF_pad1 hsym_pad1
      apply SepWPp.fold (fold_pad_lt_378 C.F s0.sp sender receiver macKey message hpad)
      · sep_focus
      exact SepWPp.apply_join hjoin952
        ⟨hF_pad1, hsym_pad1,
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by sep_focus)
    · have hpad_ge : 56 ≤ (mkMacEnv sender receiver macKey message).innerPos := by omega
      have hhi_le : 63 - (mkMacEnv sender receiver macKey message).innerPos ≤ 7 := by omega
      have hhi_gt :
          (7#64 : BitVec 64).ult (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)) = false := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
      have hhi_ule :
          (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ule 7#64 = true := by
        simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
      have hhi_cond :
          ((!(BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ult 7#64) &&
           !((BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)) == 7#64)) = false :=
        bhi_7_false hhi_le
      have hhi_cond' :
          ¬ ((!(BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ult 7#64) &&
             !((BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)) == 7#64)) = true := by
        rw [hhi_cond]; decide
      have hpadBlk_len64 :
          ((mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
            List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8).length = 64 := by
        simp [htail_len]; omega
      have hpadBlk_len :
          ((mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
            List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8).length = 64 * 1 :=
        hpadBlk_len64
      have hpadBlk_len_sub :
          (mkMacEnv sender receiver macKey message).innerPos + 1 +
            (63 - (mkMacEnv sender receiver macKey message).innerPos) = 64 := by omega
      have hpadBlk_len_sub2 :
          (mkMacEnv sender receiver macKey message).innerPos +
            (63 - (mkMacEnv sender receiver macKey message).innerPos + 1) = 64 := by omega
      conv =>
        arg 4
        rw [pointsToBytes_64_352_eq s0.sp hpadBlk_len64, cells_192_8_eq s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
        SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
        SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
        SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun b7 => ?_
      refine of_sepWP_inImage (entry + bv% (932)) hF808c hsym808c ?_
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF_pad2a hsym_pad2a
      clear b0 b1 b2 b3 b4 b5 b6 b7
      conv =>
        arg 4
        rw [show (mkMacEnv sender receiver macKey message).innerTail ++
            0x80#8 :: List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 =
          (mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
            List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 by simp]
      apply SepWPp.fold (fold_8_words_192 s0.sp hpadBlk_len64)
      · sep_focus
      refine of_sepWP_inImage (entry + bv% (952)) hF_pad2a hsym_pad2a ?_
      wp_steps_inImage (entry + bv% (ls_off% "sha2::sha256::compress256" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      wp_call hcompress (s0.sp - 288#64,
        (mkMacEnv sender receiver macKey message).hState C.F
          (mkMacEnv sender receiver macKey message).innerB,
        s0.sp - 192#64,
        (mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
          List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8,
        1)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF_pad2b hsym_pad2b
      conv =>
        arg 4
        rw [show (mkMacEnv sender receiver macKey message).innerTail ++
            0x80#8 :: List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 =
          (mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
            List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 by simp]
      apply SepWPp.fold (fold_pad_ge_378 C.F s0.sp sender receiver macKey message _ hpad_ge)
      · sep_focus
      exact SepWPp.apply_join hjoin952
        ⟨hF_pad2b, hsym_pad2b,
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by sep_focus)
  by_cases hshort : message.length < 62
  · have hult62 : (BitVec.ofNat 64 message.length).ult 62#64 = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hpos_short :
        2#8 + BitVec.zeroExtend 8 (BitVec.ofNat 64 message.length) =
          BitVec.ofNat 8 (message.length + 2) := by
      bv_omega
    apply SepWPp.fold (fold_short_pre s0.sp message.length hshort)
    · sep_focus
    refine of_sepWP_inImage (entry + bv% (808)) hF5e hsym5e ?_
    wp_steps_inImage (entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
    wp_call hmemcpy (s0.sp - 494#64, msgA, message)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF_sh hsym_sh
    apply SepWPp.fold (fold_short_post C.F s0.sp sender receiver macKey message hshort _ rfl)
    · sep_focus
    exact SepWPp.apply_join hjoin808
      ⟨hF_sh, hsym_sh,
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
      (by sep_focus)
  · have hge62 : 62 ≤ message.length := by omega
    have hult62 : (BitVec.ofNat 64 message.length).ult 62#64 = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hult62' : ¬ (BitVec.ofNat 64 message.length).ult 62#64 = true := by
      rw [hult62]; decide
    have hlen_m62 : (message.take 62).length = 62 := by simp; omega
    have hlen_m62_min : min 62 message.length = 62 := by omega
    have hblk3_len : (receiver.publicKey.serialize.drop 31 ++ message.take 62).length = 64 * 1 := by
      simp [PublicKey.serialize]; omega
    refine of_sepWP_inImage (entry + bv% (704)) hF5e hsym5e ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF_lg1 hsym_lg1
    apply SepWPp.fold (fold_long_pre_62 s0.sp msgA message 2#8 hge62)
    · sep_focus
    refine of_sepWP_inImage (entry + bv% (708)) hF_lg1 hsym_lg1 ?_
    wp_steps_inImage (entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
    wp_call hmemcpy (s0.sp - 494#64, msgA, message.take 62)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF_lg2 hsym_lg2
    apply SepWPp.fold (fold_blk3 s0.sp (receiver.publicKey.serialize.drop 31)
      (message.take 62) hlen_r2)
    · sep_focus
    refine of_sepWP_inImage (entry + bv% (736)) hF_lg2 hsym_lg2 ?_
    wp_steps_inImage (entry + bv% (ls_off% "sha2::sha256::compress256" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
    wp_call hcompress (s0.sp - 432#64, (mkMacEnv sender receiver macKey message).hState C.F 2,
      s0.sp - 496#64, receiver.publicKey.serialize.drop 31 ++ message.take 62, 1)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF_lg3 hsym_lg3
    conv =>
      arg 4
      rw [mkMacEnv_hState_three C.F sender receiver macKey message hge62]
    have hlsr6 : (BitVec.ofNat 64 message.length - 62#64) >>> 6 =
        BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull :=
      sub62_ushiftRight_6 hge62 h
    have hand_mask : (BitVec.ofNat 64 message.length - 62#64) &&& 0x7fffffffffffffc0#64 =
        BitVec.ofNat 64 (64 * (mkMacEnv sender receiver macKey message).nFull) :=
      sub62_and_mask64 hge62 h
    have hand_63 : (BitVec.ofNat 64 message.length - 62#64) &&& 63#64 =
        BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerTail.length := by
      rw [mkMacEnv_innerTail_length, mkMacEnv_innerPos_eq sender receiver macKey message hge62]
      exact sub62_and_63 hge62 h
    have hpos_long :
        BitVec.zeroExtend 8 (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerTail.length) =
          BitVec.ofNat 8 (mkMacEnv sender receiver macKey message).innerTail.length := by
      bv_omega
    have htail_lt := mkMacEnv_innerTail_length_lt sender receiver macKey message
    have htail_toNat :
        (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerTail.length).toNat =
          (mkMacEnv sender receiver macKey message).innerTail.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hnFull_toNat :
        (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull).toNat =
          (mkMacEnv sender receiver macKey message).nFull := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      change (message.length - 62) / 64 < 2 ^ 64
      omega
    have hfull_len :
        ((message.drop 62).take (64 * (mkMacEnv sender receiver macKey message).nFull)).length =
          64 * (mkMacEnv sender receiver macKey message).nFull := by
      rw [List.length_take, List.length_drop]
      exact Nat.min_eq_left (Nat.mul_div_le (message.length - 62) 64)
    have hfull_len_min :
        min (64 * (mkMacEnv sender receiver macKey message).nFull) (message.length - 62) =
          64 * (mkMacEnv sender receiver macKey message).nFull := by
      simpa only [List.length_take, List.length_drop] using hfull_len
    apply SepWPp.fold (fold_post_blk3 s0.sp msgA sender receiver macKey message
      (receiver.publicKey.serialize.drop 31 ++ message.take 62) hblk3_len hge62)
    · sep_focus
    conv =>
      arg 4
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b63' => ?_
    by_cases hnFull : (mkMacEnv sender receiver macKey message).nFull = 0
    · have hcbz1 : (BitVec.ofNat 64 message.length - 62#64) >>> 6 = 0#64 := by
        rw [hlsr6, hnFull]
      have hinnerB_eq : (mkMacEnv sender receiver macKey message).innerB = 3 := by
        rw [mkMacEnv_innerB_eq sender receiver macKey message hge62, hnFull]
      refine of_sepWP_inImage (entry + bv% (808)) hF_lg3 hsym_lg3 ?_
      wp_steps_inImage (entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      wp_call hmemcpy (s0.sp - 496#64,
        msgA + 62#64 + BitVec.ofNat 64 (64 * (mkMacEnv sender receiver macKey message).nFull),
        (mkMacEnv sender receiver macKey message).innerTail)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF_lg4a hsym_lg4a
      conv =>
        arg 4
        rw [← hinnerB_eq]
      apply SepWPp.fold (fold_rejoin_msg_long msgA sender receiver macKey message hge62)
      · sep_focus
      apply SepWPp.fold (fold_long_post C.F s0.sp sender receiver macKey message _ _
        rfl rfl)
      · sep_focus
      exact SepWPp.apply_join hjoin808
        ⟨hF_lg4a, hsym_lg4a,
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by sep_focus)
    · have hcbz1 : (BitVec.ofNat 64 message.length - 62#64) >>> 6 ≠ 0#64 := by
        rw [hlsr6]
        intro heq
        apply hnFull
        have := congrArg BitVec.toNat heq
        simpa [hnFull_toNat] using this
      have hcbz1_ne : BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull ≠ 0#64 := by
        rw [← hlsr6]; exact hcbz1
      have hcbz1_beq : (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull == 0#64) = false :=
        beq_false_of_ne hcbz1_ne
      have hcbz1_beq' : ¬ (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull == 0#64) = true := by
        rw [hcbz1_beq]; decide
      have hblk_word1 :
          3#64 + BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull =
            BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB := by
        rw [mkMacEnv_innerB_eq sender receiver macKey message hge62]
        bv_omega
      refine of_sepWP_inImage (entry + bv% (808)) hF_lg3 hsym_lg3 ?_
      wp_steps_inImage (entry + bv% (ls_off% "sha2::sha256::compress256" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      refine seq_inImage_compute (entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")) ‹_› ‹_› ?_
      wp_call hcompress (s0.sp - 432#64, (mkMacEnv sender receiver macKey message).hState C.F 3,
        msgA + 62#64,
        (message.drop 62).take (64 * (mkMacEnv sender receiver macKey message).nFull),
        (mkMacEnv sender receiver macKey message).nFull)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF_step2 hsym_step2
      wp_call hmemcpy (s0.sp - 496#64,
        msgA + 62#64 + BitVec.ofNat 64 (64 * (mkMacEnv sender receiver macKey message).nFull),
        (mkMacEnv sender receiver macKey message).innerTail)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF_lg4b hsym_lg4b
      conv =>
        arg 4
        rw [mkMacEnv_hState_full C.F sender receiver macKey message hge62]
      apply SepWPp.fold (fold_rejoin_msg_long msgA sender receiver macKey message hge62)
      · sep_focus
      apply SepWPp.fold (fold_long_post C.F s0.sp sender receiver macKey message _ _
        rfl rfl)
      · sep_focus
      exact SepWPp.apply_join hjoin808
        ⟨hF_lg4b, hsym_lg4b,
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by sep_focus)


theorem computeMac_subroutine_ok_of_contracts (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr compress256Name) (compress256Spec C.F))
    (hnew : NewFromSliceOkExt img C ext)
    (hpk : PublicKeySerializeOkExt img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((computeMacSpec C.F A).inImage img) := by
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")))
      framelessMemcpySpec :=
    hA.session_memcpy_region_ok_at (name := computeMacName) (k := num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      (by fnoff_eq)
  have hcompress : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName + BitVec.ofNat 64 (num% (ls_off% "sha2::sha256::compress256" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")))
      (session2Compress256Spec C.F) :=
    sub_ok_at_of_fnAddr hcomp computeMacName (num% (ls_off% "sha2::sha256::compress256" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      (by fnoff_eq)
  have hdealloc0 := dealloc_pkStack_ok_at2_ext (b := img.base) (ext := ext)
    hA (name := computeMacName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
  have hmemset := session2Memset_of_sessionMemsetRegion
    (hA.session_memset_region_ok_at (name := computeMacName) (k := num% (ls_off% "memset" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      (by fnoff_eq))
  exact computeMac_ok_of_hooks_gen publicKeySerializeStack (by decide) img C A ext
    (newFromSlice_ok_at2_ext img C ext hnew _ rfl)
    (subroutine_ok_inImage_of_subroutine_ok img (publicKeySerialize_ok_at2_ext img.base A ext hpk _ rfl))
    (fun sp_cur => subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => by
        simp only [session2MemcpyPkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, _⟩, hmem⟩
        refine subroutine_ok.mono_outcome hmemcpy (dst, src, bs) (stackAt sp_cur publicKeySerializeStack ∗ R) s0 hpc hrun
          (by simpa only [framelessMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hx0, hx1, hx2⟩, hmem⟩) hsp fun _ hraw => ?_
        unfold SubroutineOutcome at hraw ⊢
        simpa only [framelessMemcpySpec, session2MemcpyPkStackSpecAt, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw))
    (fun sp_cur => subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_outcome_intro fun ⟨stA, st, blkA, blk, n⟩ R s0 hpc hrun hpre hsp => by
        simp only [session2Compress256PkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, hblk, _⟩, hmem⟩
        refine subroutine_ok.mono_outcome hcompress (stA, st, blkA, blk, n) (stackAt sp_cur publicKeySerializeStack ∗ R) s0 hpc hrun
          (by simpa only [session2Compress256Spec, sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hx0, hx1, hx2, hblk⟩, hmem⟩) hsp fun _ hraw => ?_
        unfold SubroutineOutcome at hraw ⊢
        simpa only [session2Compress256Spec, session2Compress256PkStackSpecAt, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw))
    (subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_outcome_intro fun ⟨p, bs⟩ R s0 hpc hrun hpre hsp => by
        simp only [rustDeallocPkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, _⟩, hmem⟩
        refine subroutine_ok.mono_outcome hdealloc0 (p, bs) R s0 hpc hrun
          (by simpa only [rustDeallocPkStackSpec, sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hx0, hx1, hx2⟩, hmem⟩) hsp fun _ hraw => ?_
        unfold SubroutineOutcome at hraw ⊢
        simpa only [rustDeallocPkStackSpec, rustDeallocPkStackSpecAt, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw))
    (fun sp_cur => subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_outcome_intro fun ⟨dst, val, n⟩ R s0 hpc hrun hpre hsp => by
        simp only [session2MemsetPkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, _⟩, hmem⟩
        refine subroutine_ok.mono_outcome hmemset (dst, val, n) (stackAt sp_cur publicKeySerializeStack ∗ R) s0 hpc hrun
          (by simpa only [session2MemsetSpec, sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hx0, hx1, hx2⟩, hmem⟩) hsp fun _ hraw => ?_
        unfold SubroutineOutcome at hraw ⊢
        simpa only [session2MemsetSpec, session2MemsetPkStackSpecAt, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw))

theorem computeMac_subroutine_ok_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel)
    (ext : String → Option (State → State))
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hnew : NewFromSliceOkExt img C ext)
    (hpk : PublicKeySerializeOkExt img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((computeMacSpec C.F A).inImage img) :=
  computeMac_subroutine_ok_of_contracts img C A ext hC.toAllocContracts hC.compress256 hnew hpk

theorem computeMac_subroutine_ok_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (hnew : NewFromSliceOk_trap img C abs)
    (hpk : PublicKeySerializeOk_trap img.base C A abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr computeMacName)
      ((computeMacSpec C.F A).inImage img) :=
  computeMac_subroutine_ok_of_contracts img C A (trTrapExterns C abs)
    (AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hA)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.compress256_ok_at_trap img.base C abs compress256Name 0 (Nat.add_zero _))
    hnew hpk

theorem computeMac_subroutine_ok (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (hnew : NewFromSliceOk img C ctl abs)
    (hpk : PublicKeySerializeOk img.base C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr computeMacName)
      ((computeMacSpec C.F A).inImage img) :=
  computeMac_subroutine_ok_of_contracts img C A (tripleRatchetExterns C ctl abs)
    (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.compress256_ok_at img.base C ctl abs compress256Name 0 (Nat.add_zero _))
    hnew hpk


theorem computeMac_subroutine_ok_of_contracts_x (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr compress256Name)
      ((withStack (compress256Spec C.F) extHookStack).inImage img))
    (hnew : NewFromSliceOkExt img C ext)
    (hpk : PublicKeySerializeOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((computeMacSpecX C.F A).inImage img) :=
  computeMac_ok_of_hooks_gen publicKeySerializeStackX (by decide) img C A ext
    (newFromSlice_ok_at2_ext_x img C ext hnew _ rfl)
    (publicKeySerialize_ok_at2_ext_x img A ext hpk _ rfl)
    (fun sp_cur => memcpy_pkStack_ok_at2_ext_x sp_cur hA (name := computeMacName) (k := num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      (by fnoff_eq))
    (fun sp_cur => compress256_pkStack_ok_at2_ext_x sp_cur hcomp (name := computeMacName) (k := num% (ls_off% "sha2::sha256::compress256" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      (by fnoff_eq))
    (dealloc_pkStack_ok_at2_ext_x (img := img) (ext := ext)
      hA (name := computeMacName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac")))
    (fun sp_cur => memset_pkStack_ok_at2_ext_x sp_cur hA (name := computeMacName) (k := num% (ls_off% "memset" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac"))
      (by fnoff_eq))
theorem computeMac_subroutine_ok_ext_x (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State))
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (hnew : NewFromSliceOkExt img C ext)
    (hpk : PublicKeySerializeOkX img A ext) :
    ComputeMacOkX img C A ext :=
  computeMac_subroutine_ok_of_contracts_x img C A ext hC.toAllocContractsX hC.compress256 hnew hpk

/-! ## Relocatable `[LibsignalPlacement]` contracts -/

class LsClInv (Inv : State → Prop) : Prop where
  of_keepsFrozen : ∀ {s s' : State}, Inv s → Memory.KeepsFrozen s.mem s'.mem → Inv s'

instance [LibsignalPlacement] : LsClInv (fun s => LibsignalCodeLoaded lsmpl s.mem) where
  of_keepsFrozen h hkf := LibsignalCodeLoaded.of_keepsFrozen h hkf

instance [LibsignalPlacement] : LsClInv (fun s => LibsignalCodeRoLoaded lsmpl s.mem) where
  of_keepsFrozen h hkf := LibsignalCodeRoLoaded.of_keepsFrozen h hkf

def LsSymState : Prop := True

def _root_.Arm64.Spec.withLsClState {LsClState : State → Prop} {α : Type} (spec : Spec α) : Spec α where
  pre := fun x s => ⌜LsClState s ∧ LsSymState⌝ ∗ spec.pre x s
  post := spec.post
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

private theorem subroutine_ok_withLsClState_of_lscl [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok prog addr (spec.withLsClState (LsClState := fun s => LibsignalCodeLoaded lsmpl s.mem)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [Spec.withLsClState, withLsCodeLoaded, LsSymState] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hpre.1.1, hpre.2⟩

private theorem subroutine_ok_withLsClState_of_lscro [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog addr (spec.withLsClState (LsClState := fun s => LibsignalCodeRoLoaded lsmpl s.mem)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [Spec.withLsClState, withLsCodeRoLoaded, LsSymState] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hpre.1.1, hpre.2⟩

private theorem subroutine_ok_withLsClState_of_plain {LsClState : State → Prop} {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr spec) :
    subroutine_ok prog addr (spec.withLsClState (LsClState := LsClState)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [Spec.withLsClState, LsSymState] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2

private theorem subroutine_ok_lscl_of_withLsClState [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (spec.withLsClState (LsClState := fun s => LibsignalCodeLoaded lsmpl s.mem))) :
    subroutine_ok prog addr (withLsCodeLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [Spec.withLsClState, withLsCodeLoaded, LsSymState] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hpre.1, trivial⟩, hpre.2⟩

private theorem subroutine_ok_lscro_of_withLsClState [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (spec.withLsClState (LsClState := fun s => LibsignalCodeRoLoaded lsmpl s.mem))) :
    subroutine_ok prog addr (withLsCodeRoLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome h x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [Spec.withLsClState, withLsCodeRoLoaded, LsSymState] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hpre.1, trivial⟩, hpre.2⟩

def publicKeySerializeSpecKeepPlacedAt {LsClState : State → Prop} (A : RustAlloc) (pkStack : Nat) :
    Spec PublicKeySerializeCall where
  pre := fun x s =>
    ⌜(LsClState s ∧ LsSymState) ∧ s.readReg64 .x0 = x.self⌝ ∗
      (x.self ↦ₛ x.pk.bytes.toList) ∗ A.pool ∗
      stackAt s.sp pkStack
  post := fun x s0 sf =>
    ⌜LsClState sf ∧ LsSymState⌝ ∗
      (publicKeySerializeSpecAt A pkStack).post x s0 sf
  onPanic := (publicKeySerializeSpecAt A pkStack).onPanic
  onExit := (publicKeySerializeSpecAt A pkStack).onExit
  onOom := (publicKeySerializeSpecAt A pkStack).onOom

theorem publicKeySerializeKeepPlacedAt_of_lscl {LsClState : State → Prop} [hInv : LsClInv LsClState]
    {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {pkStack : Nat}
    (h : subroutine_ok prog entry ((publicKeySerializeSpecAt A pkStack).withLsClState (LsClState := LsClState))) :
    subroutine_ok prog entry (publicKeySerializeSpecKeepPlacedAt (LsClState := LsClState) A pkStack) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hcode => ?_
  have hpre' : s0.mem ⊨ ((publicKeySerializeSpecAt A pkStack).withLsClState (LsClState := LsClState)).pre x s0 ∗ R := by
    simp only [publicKeySerializeSpecKeepPlacedAt, Spec.withLsClState, publicKeySerializeSpecAt,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨hpre.1.1, hpre.1.2, hpre.2⟩
  have hinv : LsClState s0 ∧ LsSymState := by
    simp only [Spec.withLsClState, publicKeySerializeSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre'
    exact hpre'.1
  obtain ⟨sf, hsteps, hout, -⟩ :=
    subroutine_ok.no_fault_before_outcome h x R s0 hpc hrun hpre' hsp hcode
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [publicKeySerializeSpecKeepPlacedAt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hInv.of_keepsFrozen hinv.1 hsteps.keepsFrozen, trivial⟩, hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

private theorem of_sepWP_lscl {LsClState : State → Prop} [hInv : LsClInv LsClState]
    {prog : Program} (mid : BitVec 64) {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : LsClState s) (_hsym : LsSymState)
    (h : SepWP prog mid s P (fun sm Pm =>
      LsClState sm → LsSymState → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hInv.of_keepsFrozen hF hsteps.keepsFrozen) trivial R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem seq_lscl_compute {LsClState : State → Prop} [hInv : LsClInv LsClState]
    {prog : Program} (mid : BitVec 64) {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hF : LsClState s) (_hsym : LsSymState)
    (h : SepWP prog mid s P (fun sm Pm =>
      LsClState sm → LsSymState → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold SepWP reaches_pc
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩
  · rcases (hnext (hInv.of_keepsFrozen hF hsteps.keepsFrozen) trivial).elim hmm (hsteps.codeLoaded hL) with
      ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hpost⟩ | ⟨_, hoom⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, Pf, hmf, hpost⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  · exact (not_satisfies_false_sepConj hoom).elim

local macro "wp_steps_lscl " mid:term : tactic =>
  `(tactic| (
    refine seq_lscl_compute $mid ‹_› ‹_› ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF_step hsym_step))

theorem call_pk_serialize_placed_at {LsClState : State → Prop} [LsClInv LsClState]
    {prog : Program} {ret callee : BitVec 64}
    {A : RustAlloc} {pkStack : Nat} {s0 s : State} {P F R : SepProp} {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog callee ((publicKeySerializeSpecAt A pkStack).withLsClState (LsClState := LsClState)))
    (ret_pc sp_cur keyA : BitVec 64) (key : PublicKey)
    (hP : P = ((keyA ↦ₛ key.bytes.toList) ∗ A.pool ∗
      stackAt sp_cur pkStack) ∗ F)
    (hside : LsClState s ∧ LsSymState ∧
      s.pc = callee ∧ s.status = .Running ∧ s.spAligned = true ∧
      s.sp = sp_cur ∧ s.readReg64 Reg.lr = ret_pc ∧ s.trace = s0.trace ∧
      s.readReg64 (Reg.gpr 0#5) = keyA)
    (hnext : ∀ (sf : State),
      LsClState sf → LsSymState →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_cur → RegsSaved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0 → sf.readReg64 (Reg.gpr 1#5) = 33#64 →
      sf.trace = s0.trace →
      SepWPp prog ret sf
        ((keyA ↦ₛ key.bytes.toList) ∗
          A.live (sf.readReg64 (Reg.gpr 0#5)) key.serialize.length 1 ∗
          (sf.readReg64 (Reg.gpr 0#5) ↦ₛ key.serialize) ∗
          A.pool ∗ stackAt sp_cur pkStack ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  rcases hside with ⟨hF_s, hsym_s, hpc, hrun, hsp, hsp_cur, hlr, htr, hφ⟩
  have hφ' : (LsClState s ∧ LsSymState) ∧ s.readReg64 (Reg.gpr 0#5) = keyA :=
    ⟨⟨hF_s, hsym_s⟩, hφ⟩
  refine SepWPp.call_frame (x := ⟨keyA, key⟩) (publicKeySerializeKeepPlacedAt_of_lscl hcall) hpc hrun hsp hlr
    (by simp only [publicKeySerializeSpecKeepPlacedAt, Spec.withLsClState, publicKeySerializeSpecAt, hsp_cur, Reg.x0, sepConj_assoc, pure_sepConj_pure])
    hφ' hP
    (fun sf code R' _ hm => by
      dsimp only [publicKeySerializeSpecKeepPlacedAt, publicKeySerializeSpecAt] at hm
      exact allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [publicKeySerializeSpecKeepPlacedAt, publicKeySerializeSpecAt] at hm
      exact allowPanic_frame (allocFailedIn_of_trace_eq htr) hm)
    (fun sf hpcm hrunm hspm hcsm => ?_)
  have hne : key.serialize ≠ [] := by simp [PublicKey.serialize]
  conv =>
    arg 4
    simp only [publicKeySerializeSpecKeepPlacedAt, publicKeySerializeSpecAt, boxU8Buf, hne, ite_false,
      hsp_cur, Reg.x0, Reg.x1, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hF_sf, hsym_sf⟩ => ?_
  refine SepWPp.pure_elim fun ⟨hx1, htr'⟩ => ?_
  conv =>
    arg 4
    rw [sepConj_left_comm (keyA ↦ₛ key.bytes.toList)]
  refine SepWPp.pure_elim fun ⟨hx0, _⟩ => ?_
  exact hnext sf hF_sf hsym_sf hpcm hrunm (hspm.trans hsp_cur) (regsSaved_of_calleeSavedPreserved hcsm)
    hx0 hx1 (htr'.trans htr)

set_option maxHeartbeats 1600000 in
theorem computeMac_placed_ok_of_hooks_gen [LibsignalPlacement]
    {LsClState : State → Prop} [LsClInv LsClState]
    (pkStack : Nat) (hbound : pkStack + 496 < 2 ^ 64)
    (C : Crypto) (A : RustAlloc)
    (H : String → Option (State → State))
    (hnew_at : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 114)
      ((newFromSlicePkStackSpecAt C.F pkStack).withLsClState (LsClState := LsClState)))
    (hpk_at : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 205)
      ((publicKeySerializeSpecAt A pkStack).withLsClState (LsClState := LsClState)))
    (hmemcpy_all : ∀ sp_cur, subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacMemcpySym)
      ((session2MemcpyPkStackSpecAt pkStack sp_cur).withLsClState (LsClState := LsClState)))
    (hcompress_all : ∀ sp_cur, subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacCompress256Sym)
      ((session2Compress256PkStackSpecAt C.F pkStack sp_cur).withLsClState (LsClState := LsClState)))
    (hdealloc : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacRustDeallocSym)
      ((rustDeallocPkStackSpecAt A pkStack).withLsClState (LsClState := LsClState)))
    (hmemset_all : ∀ sp_cur, subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacMemsetSym)
      ((session2MemsetPkStackSpecAt pkStack sp_cur).withLsClState (LsClState := LsClState))) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (blkPl_60).base
      ((computeMacSpecAt C.F A pkStack).withLsClState (LsClState := LsClState)) := by
  simp only [Spec.withLsClState, computeMacSpecAt, stackAt_computeMacAt_eq pkStack hbound,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wpp_init x s0
  have hmemcpy := hmemcpy_all (s0.sp - 496#64)
  have hcompress := hcompress_all (s0.sp - 496#64)
  have hmemset := hmemset_all (s0.sp - 496#64)
  clear hmemcpy_all hcompress_all hmemset_all
  obtain ⟨ret, senderA, sender, receiverA, receiver, keyA, macKey, msgA, message⟩ := x
  dsimp only at *
  have hk_len := keyToBytes32_length macKey
  have hk_le : (keyToBytes32 macKey).length ≤ 64 := keyToBytes32_length_le_64 macKey
  have hlen_s : sender.publicKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have hlen_r : receiver.publicKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have hlen_r31 : (receiver.publicKey.serialize.take 31).length = 31 := by simp [PublicKey.serialize]
  have hlen_r2 : (receiver.publicKey.serialize.drop 31).length = 2 := by simp [PublicKey.serialize]
  have hblk2_len : (sender.publicKey.serialize ++ receiver.publicKey.serialize.take 31).length = 64 * 1 := by
    simp [PublicKey.serialize]
  have hx6_eq : s0.readReg64 (Reg.gpr 6#5) = BitVec.ofNat 64 message.length := by
    rw [← ‹(s0.readReg64 (Reg.gpr 6#5)).toNat = message.length›]
    simp
  refine of_sepWP_lscl (lsmpl.base 114) ‹LsClState s0› trivial ?_
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF1 hsym1
  refine of_sepWP_lscl ((blkPl_60).base + 76#64) hF1 hsym1 ?_
  wp_call hnew_at ⟨s0.sp - 352#64, keyA, keyToBytes32 macKey⟩
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF1a hsym1a
  clear hF1 hsym1 m m_1 m_2 m_3 m_4 m_5
  conv =>
    arg 4
    rw [hmacCoreAt_nil_eq_words64 C.F (s0.sp - 344#64) (keyToBytes32 macKey),
      cells_496_18_eq s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
    SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c9 =>
    SepWPp.exists_elim fun c10 => SepWPp.exists_elim fun c11 =>
    SepWPp.exists_elim fun c12 => SepWPp.exists_elim fun c13 =>
    SepWPp.exists_elim fun c14 => SepWPp.exists_elim fun c15 =>
    SepWPp.exists_elim fun c16 => SepWPp.exists_elim fun c17 =>
    SepWPp.exists_elim fun pad0 => ?_
  conv =>
    arg 4
    simp only [hmacWords64At, arm64_norm, sepConj_assoc]
  refine of_sepWP_lscl (lsmpl.base 205) hF1a hsym1a ?_
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF1b hsym1b
  clear c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17
  apply SepWPp.fold (fold_19_words_352 s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  · sep_focus
  apply SepWPp.fold
    (fold_18_words_496 s0.sp (hmacInnerInit C.F (keyToBytes32 macKey)) 1
      (hmacOuterInit C.F (keyToBytes32 macKey)) pad0.1 pad0.2)
  · sep_focus
  apply call_pk_serialize_placed_at hpk_at ((blkPl_60).base + 164#64) (s0.sp - 496#64) senderA sender.publicKey
  · sep_focus
  · refine ⟨hF1b, hsym1b, by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      spAligned_of_sub_496 s0.sp (by simp only [arm64_norm, *]) hsp_align,
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
  intro sf2 hF2 hsym2 hpc2 hrun2 hsp2 hcs2 hptr1 hx1_2 htr2
  simp only [RegsSaved, arm64_norm, *] at hcs2
  rcases hcs2 with ⟨h2_19, h2_20, h2_21, h2_22, h2_23, h2_24, h2_25, h2_26, h2_27, h2_28, h2_29, h2_v⟩
  refine of_sepWP_lscl (lsmpl.base 205) hF2 hsym2 ?_
  wp_steps_lscl (lsρ lsMacMemcpySym)
  refine seq_lscl_compute (lsρ lsMacRustDeallocSym) ‹_› ‹_› ?_
  wp_call hmemcpy (s0.sp - 496#64, sf2.readReg64 (Reg.gpr 0#5), sender.publicKey.serialize)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF_step1 hsym_step1
  wp_call hdealloc (sf2.readReg64 (Reg.gpr 0#5), sender.publicKey.serialize)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF2a hsym2a
  have hsp_sf1 : sf_1.sp = s0.sp - 496#64 := by simp only [arm64_norm, *]
  conv =>
    arg 4
    rw [hsp_sf1]
  apply call_pk_serialize_placed_at hpk_at ((blkPl_60).base + 400#64) (s0.sp - 496#64) receiverA receiver.publicKey
  · sep_focus
  · refine ⟨hF2a, hsym2a, by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      spAligned_of_sub_496 s0.sp (by simp only [arm64_norm, *]) hsp_align,
      by simp only [arm64_norm, *], by simp only [arm64_norm, *],
      by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
  intro sf5 hF5 hsym5 hpc5 hrun5 hsp5 hcs5 hptr2 hx1_5 htr5
  simp only [RegsSaved, arm64_norm, *] at hcs5
  rcases hcs5 with ⟨h5_19, h5_20, h5_21, h5_22, h5_23, h5_24, h5_25, h5_26, h5_27, h5_28, h5_29, h5_v⟩
  refine of_sepWP_lscl ((blkPl_60).base + 544#64) hF5 hsym5 ?_
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF5a hsym5a
  apply SepWPp.fold (fold_pre_memcpy_31 s0.sp (sf5.readReg64 (Reg.gpr 0#5))
    receiver.publicKey.serialize 33#8 hlen_r)
  · sep_focus
  refine of_sepWP_lscl ((blkPl_60).base + 548#64) hF5a hsym5a ?_
  wp_steps_lscl (lsρ lsMacMemcpySym)
  wp_call hmemcpy (s0.sp - 463#64, sf5.readReg64 (Reg.gpr 0#5),
    receiver.publicKey.serialize.take 31)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF5b hsym5b
  apply SepWPp.fold (fold_blk2 s0.sp sender.publicKey.serialize
    (receiver.publicKey.serialize.take 31) hlen_s)
  · sep_focus
  refine of_sepWP_lscl ((blkPl_60).base + 576#64) hF5b hsym5b ?_
  wp_steps_lscl (lsρ lsMacCompress256Sym)
  wp_call hcompress (s0.sp - 432#64, hmacInnerInit C.F (keyToBytes32 macKey),
    s0.sp - 496#64, sender.publicKey.serialize ++ receiver.publicKey.serialize.take 31, 1)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF5c hsym5c
  apply SepWPp.fold (fold_post_blk2 s0.sp
    (sender.publicKey.serialize ++ receiver.publicKey.serialize.take 31)
    receiver.publicKey.serialize hblk2_len hlen_r)
  · sep_focus
  conv =>
    arg 4
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b63 => ?_
  refine of_sepWP_lscl ((blkPl_60).base + 644#64) hF5c hsym5c ?_
  wp_steps_lscl (lsρ lsMacMemcpySym)
  wp_call hmemcpy (s0.sp - 496#64, sf5.readReg64 (Reg.gpr 0#5) + 31#64,
    receiver.publicKey.serialize.drop 31)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF5d hsym5d
  apply SepWPp.fold (fold_rejoin_31 (sf5.readReg64 (Reg.gpr 0#5))
    receiver.publicKey.serialize hlen_r)
  · sep_focus
  refine of_sepWP_lscl ((blkPl_60).base + 660#64) hF5d hsym5d ?_
  wp_steps_lscl (lsρ lsMacRustDeallocSym)
  wp_call hdealloc (sf5.readReg64 (Reg.gpr 0#5), receiver.publicKey.serialize)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF5e hsym5e
  have hsp_sf5 : sf_5.sp = s0.sp - 496#64 := by simp only [arm64_norm, *]
  have hlen_toNat : (BitVec.ofNat 64 message.length).toNat = message.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  conv =>
    arg 4
    rw [hsp_sf5, mkMacEnv_hState_two C.F sender receiver macKey message,
      mkMacEnv_oState1 C.F sender receiver macKey message]
  apply SepWPp.fold (fold_stk_192_64 s0.sp _ _)
  · sep_focus
  have hvregs_sf_6 : calleeSavedVRegs sf_6 = calleeSavedVRegs s0 := by simp only [arm64_norm, *]
  simp only [arm64_norm, *] at hsp_sf_6 h_73 h_74 h_75 h_79 h_80 h_81 h_82 hcs_sf_6 hpost_6
  run_tac clearDepsTac #[`sf, `sf2, `sf_1, `sf_2, `sf5, `sf_3, `sf_4, `sf_5, `m, `m_1, `m_2, `m_3, `m_4, `m_5, `m_6, `m_7, `pad0, `b63]
  refine SepWPp.with_join
    (memRegion (s0.sp - 192#64) 64 ∗
      hmacStateAt (s0.sp - 496#64)
        ((mkMacEnv sender receiver macKey message).hState C.F
          (mkMacEnv sender receiver macKey message).innerB)
        (mkMacEnv sender receiver macKey message).innerB
        ((mkMacEnv sender receiver macKey message).oState1 C.F)
        (mkMacEnv sender receiver macKey message).innerTail ∗
      msgA ↦ₛ message ∗
      A.pool ∗
      stackAt (s0.sp - 496#64) pkStack ∗
      receiverA ↦ₛ receiver.publicKey.bytes.toList ∗
      senderA ↦ₛ sender.publicKey.bytes.toList ∗
      memRegion (s0.sp - 352#64) 152 ∗
      keyA ↦ₛ keyToBytes32 macKey ∗
      memRegion ret 16 ∗
      computeMacFramePad s0.sp ∗
      (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
      (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
    (fun sm =>
      LsClState sm ∧
      True ∧
      sm.pc = (blkPl_60).base + 808#64 ∧
      sm.status = ExecStatus.Running ∧
      sm.sp = s0.sp - 496#64 ∧
      sm.trace = s0.trace ∧
      sm.readReg64 (Reg.gpr 19#5) = ret ∧
      sm.readReg64 (Reg.gpr 27#5) = s0.sp - 352#64 ∧
      sm.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ (fun hjoin808 => ?_)
  · run_tac clearDepsTac #[`sf_6, `hnew_at, `hpk_at, `hmemcpy, `hdealloc]
    rintro sm808 ⟨hF808, hsym808, hpc808, hrun808, hsp808, htr808, h808_19, h808_27, h808_29, hv808⟩
    have htail_len := mkMacEnv_innerTail_length sender receiver macKey message
    have htail_lt := mkMacEnv_innerTail_length_lt sender receiver macKey message
    have hpos_lt : (mkMacEnv sender receiver macKey message).innerPos < 64 :=
      htail_len ▸ htail_lt
    have hzext_tail :
        BitVec.zeroExtend 64 (BitVec.ofNat 8 (mkMacEnv sender receiver macKey message).innerPos) =
          BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos :=
      zext64_ofNat8_eq hpos_lt
    have hxor_tail :
        BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos ^^^ 63#64 =
          BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos) :=
      ofNat64_xor_63 hpos_lt
    have hsub63_toNat :
        (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).toNat =
          63 - (mkMacEnv sender receiver macKey message).innerPos := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hbitlen :
        (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB <<< 9) |||
          (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos <<< 3) =
          BitVec.ofNat 64 (8 * (mkMacEnv sender receiver macKey message).innerMsg.length) :=
      LibsignalHmac.MD.bitlen (mkMacEnv sender receiver macKey message) hk_len
    have hlast_blk_len64 :
        ((mkMacEnv sender receiver macKey message).innerPadded.drop
          ((mkMacEnv sender receiver macKey message).innerPadded.length - 64)).length = 64 := by
      obtain ⟨hdrop_eq, h56_len⟩ := mkMacEnv_innerPadded_drop_eq sender receiver macKey message
      rw [hdrop_eq, List.length_append, h56_len, toBEBytes_len]
    have hlast_blk_len :
        ((mkMacEnv sender receiver macKey message).innerPadded.drop
          ((mkMacEnv sender receiver macKey message).innerPadded.length - 64)).length = 64 * 1 :=
      hlast_blk_len64
    have houter_blk_len64 :
        ((sha256Pad ((mkMacEnv sender receiver macKey message).outerMsg C.F)).drop 64).length = 64 := by
      rw [LibsignalHmac.MD.outer_block (mkMacEnv sender receiver macKey message) C.F hk_len]
      simp [innerHash_len, toBEBytes_len]
    have houter_blk_len :
        ((sha256Pad ((mkMacEnv sender receiver macKey message).outerMsg C.F)).drop 64).length = 64 * 1 :=
      houter_blk_len64
    have hlast_blk_len_sub :
        (mkMacEnv sender receiver macKey message).innerPadded.length -
          ((mkMacEnv sender receiver macKey message).innerPadded.length - 64) = 64 := by
      simpa only [List.length_drop] using hlast_blk_len64
    have houter_blk_len_sub :
        (sha256Pad ((mkMacEnv sender receiver macKey message).outerMsg C.F)).length - 64 = 64 := by
      simpa only [List.length_drop] using houter_blk_len64
    conv =>
      arg 4
      rw [hmacStateAt_eq_words64_sub (s0.sp - 496#64)
        ((mkMacEnv sender receiver macKey message).hState C.F
          (mkMacEnv sender receiver macKey message).innerB)
        (mkMacEnv sender receiver macKey message).innerB
        ((mkMacEnv sender receiver macKey message).oState1 C.F)
        (mkMacEnv sender receiver macKey message).innerTail htail_lt,
        memRegion_352_152_eq s0.sp, cells_352_18_eq s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
      SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
      SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun d5 =>
      SepWPp.exists_elim fun d6 => SepWPp.exists_elim fun d7 =>
      SepWPp.exists_elim fun d8 => SepWPp.exists_elim fun d9 =>
      SepWPp.exists_elim fun d10 => SepWPp.exists_elim fun d11 =>
      SepWPp.exists_elim fun d12 => SepWPp.exists_elim fun d13 =>
      SepWPp.exists_elim fun d14 => SepWPp.exists_elim fun d15 =>
      SepWPp.exists_elim fun d16 => SepWPp.exists_elim fun d17 =>
      SepWPp.exists_elim fun pad_tail => ?_
    conv =>
      arg 4
      simp only [hmacWords64At, arm64_norm, sepConj_assoc]
    refine of_sepWP_lscl ((blkPl_60).base + 864#64) hF808 hsym808 ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF808a hsym808a
    apply SepWPp.fold (fold_18_words_496_cells s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    · sep_focus
    conv =>
      arg 4
      rw [word7_296_eq s0.sp htail_lt pad_tail.2]
      simp only [sepConj_assoc]
    refine of_sepWP_lscl ((blkPl_60).base + 888#64) hF808a hsym808a ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF808b hsym808b
    clear d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
    apply SepWPp.fold (fold_post_copy_352 s0.sp
      ((mkMacEnv sender receiver macKey message).hState C.F
        (mkMacEnv sender receiver macKey message).innerB)
      (mkMacEnv sender receiver macKey message).innerB
      ((mkMacEnv sender receiver macKey message).oState1 C.F)
      htail_lt pad_tail.2)
    · sep_focus
    conv =>
      arg 4
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b_pad0 => ?_
    conv =>
      arg 4
      rw [htail_len]
    refine of_sepWP_lscl ((blkPl_60).base + 896#64) hF808b hsym808b ?_
    wp_steps_lscl (lsρ lsMacMemsetSym)
    wp_call hmemset
      (s0.sp - 352#64 +
        BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos + 1#64,
       0#8,
       63 - (mkMacEnv sender receiver macKey message).innerPos)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF808c hsym808c
    conv =>
      arg 4
      rw [← htail_len]
    apply SepWPp.fold (fold_post_memset_352 s0.sp (mkMacEnv sender receiver macKey message).innerTail)
    · sep_focus
    conv =>
      arg 4
      rw [htail_len]
    refine SepWPp.with_join
      (words7At352 s0.sp (((mkMacEnv sender receiver macKey message).innerPadded.drop
          ((mkMacEnv sender receiver macKey message).innerPadded.length - 64)).take 56) ∗
        (∃∗ w7 : BitVec 64, (s0.sp - 296#64) ↦₆₄ w7) ∗
        memRegion (s0.sp - 192#64) 64 ∗
        ((s0.sp - 288#64) ↦ₛ shaStateBytes
          ((chunks64 ((mkMacEnv sender receiver macKey message).innerPadded.take
            ((mkMacEnv sender receiver macKey message).innerPadded.length - 64))).foldl C.F sha256IV)) ∗
        ((s0.sp - 256#64) ↦₆₄ BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB) ∗
        ((s0.sp - 248#64) ↦ₛ shaStateBytes ((mkMacEnv sender receiver macKey message).oState1 C.F)) ∗
        ((s0.sp - 216#64) ↦₆₄ 1#64) ∗
        memRegion (s0.sp - 208#64) 8 ∗
        cells (s0.sp - 496#64) 18 ∗
        msgA ↦ₛ message ∗
        A.pool ∗
        stackAt (s0.sp - 496#64) pkStack ∗
        receiverA ↦ₛ receiver.publicKey.bytes.toList ∗
        senderA ↦ₛ sender.publicKey.bytes.toList ∗
        keyA ↦ₛ keyToBytes32 macKey ∗
        memRegion ret 16 ∗
        computeMacFramePad s0.sp ∗
        (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
        (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
        (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
        (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
        (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
        (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
        (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
        (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
        (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
      (fun sm =>
        LsClState sm ∧
        True ∧
        sm.pc = (blkPl_60).base + 952#64 ∧
        sm.status = ExecStatus.Running ∧
        sm.sp = s0.sp - 496#64 ∧
        sm.trace = s0.trace ∧
        sm.readReg64 (Reg.gpr 19#5) = ret ∧
        sm.readReg64 (Reg.gpr 20#5) = s0.sp - 352#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = 0x80#64 ∧
        sm.readReg64 (Reg.gpr 23#5) =
          BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerPos ∧
        sm.readReg64 (Reg.gpr 24#5) =
          BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB ∧
        sm.readReg64 (Reg.gpr 27#5) = s0.sp - 352#64 ∧
        sm.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ (fun hjoin952 => ?_)
    · run_tac clearDepsTac #[`sm808, `sf, `sf_7, `b_pad0, `pad_tail, `hmemset]
      rintro sm952 ⟨hF952, hsym952, hpc952, hrun952, hsp952, htr952, h952_19, h952_20, h952_22, h952_23, h952_24, h952_27, h952_29, hv952⟩
      conv =>
        arg 4
        rw [cells_192_8_eq s0.sp]
        dsimp only [words7At352]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun w7_pad =>
        SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
        SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
        SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
        SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun b7 => ?_
      refine of_sepWP_lscl ((blkPl_60).base + 996#64) hF952 hsym952 ?_
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF952a hsym952a
      clear w7_pad b0 b1 b2 b3 b4 b5 b6 b7
      refine SepWPp.fold (fold_pre_compress7 s0.sp sender receiver macKey message _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      refine of_sepWP_lscl ((blkPl_60).base + 1000#64) hF952a hsym952a ?_
      wp_steps_lscl (lsρ lsMacCompress256Sym)
      wp_call hcompress (s0.sp - 288#64,
        (chunks64 ((mkMacEnv sender receiver macKey message).innerPadded.take
          ((mkMacEnv sender receiver macKey message).innerPadded.length - 64))).foldl C.F sha256IV,
        s0.sp - 192#64,
        (mkMacEnv sender receiver macKey message).innerPadded.drop
          ((mkMacEnv sender receiver macKey message).innerPadded.length - 64),
        1)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF952b hsym952b
      conv =>
        arg 4
        rw [chunks64_of_length_64 hlast_blk_len64, List.foldl_cons, List.foldl_nil,
          pointsToBytes_shaStateBytes_288_eq s0.sp, memRegion_352_64_pre_outer_eq s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun u7 => SepWPp.exists_elim fun u6 =>
        SepWPp.exists_elim fun u5 => SepWPp.exists_elim fun u4 =>
        SepWPp.exists_elim fun u3 => SepWPp.exists_elim fun u2 =>
        SepWPp.exists_elim fun u1 => SepWPp.exists_elim fun u0 =>
        SepWPp.exists_elim fun b320 => SepWPp.exists_elim fun z319 =>
        SepWPp.exists_elim fun z311 => ?_
      refine of_sepWP_lscl ((blkPl_60).base + 1096#64) hF952b hsym952b ?_
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF952c hsym952c
      clear u7 u6 u5 u4 u3 u2 u1 u0 b320 z319 z311
      apply SepWPp.fold (fold_at_1d408 C.F s0.sp sender receiver macKey message _ rfl)
      · sep_focus
      conv =>
        arg 4
        rw [cells_192_8_eq s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun w6 => SepWPp.exists_elim fun w7 =>
        SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
        SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
        SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
        SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun b7 => ?_
      refine of_sepWP_lscl ((blkPl_60).base + 1124#64) hF952c hsym952c ?_
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF952d hsym952d
      clear w6 w7 b0 b1 b2 b3 b4 b5 b6 b7
      refine SepWPp.fold (fold_pre_compress8 C.F s0.sp sender receiver macKey message _ ?_) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      conv =>
        arg 4
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun b_cf => ?_
      refine of_sepWP_lscl ((blkPl_60).base + 1128#64) hF952d hsym952d ?_
      wp_steps_lscl (lsρ lsMacCompress256Sym)
      wp_call hcompress (s0.sp - 248#64,
        (mkMacEnv sender receiver macKey message).oState1 C.F,
        s0.sp - 192#64,
        (sha256Pad ((mkMacEnv sender receiver macKey message).outerMsg C.F)).drop 64,
        1)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF952e hsym952e
      conv =>
        arg 4
        rw [chunks64_of_length_64 houter_blk_len64, List.foldl_cons, List.foldl_nil,
          pointsToBytes_shaStateBytes_248_eq s0.sp]
        simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := (blkPl_60).base + 1140#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      apply SepWPp.fold (fold_at_1d434 s0.sp ret _ _ _ houter_blk_len64)
      · sep_focus
      conv =>
        arg 4
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
        SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
        SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
        SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
        SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
        SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
        SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
        SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun b7 =>
        SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 => ?_
      apply SepWPp.of_sepWP (mid := s0.readReg64 Reg.lr)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      clear c0 c1 c2 c3 c4 c5 c6 c7 b0 b1 b2 b3 b4 b5 b6 b7 r0 r1
      refine SepWPp.fold (fold_epilogue_post C.F s0.sp ret sender receiver macKey message _ rfl _
        ?_ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      · simp only [arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        ⟨fun hm => ?_, by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *]⟩
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        sepConj_assoc] at hm ⊢
      rcases hm with ⟨v168, v136, s0', s1', s2', s3', s4', s5', s6', s7', s8', s9', s10', s11', hm⟩
      refine ⟨v168, v136, s0', s1', s2', s3', s4', s5', s6', s7', s8', s9', s10', s11', ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨by simp only [arm64_norm, *], Satisfies.mono (Entails.of_eq (by ac_rfl)) hm⟩
    by_cases hpad : (mkMacEnv sender receiver macKey message).innerPos < 56
    · have hhi_ult :
          (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ult 7#64 = false := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
      have hhi_ult' :
          ¬ (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ult 7#64 = true := by
        rw [hhi_ult]; decide
      have hhi_ne :
          BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos) ≠ 7#64 := by
        intro heq; have := congrArg BitVec.toNat heq; simp [BitVec.toNat_ofNat] at this; omega
      have hhi_beq :
          (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos) == 7#64) = false :=
        beq_false_of_ne hhi_ne
      have hhi_gt :
          (7#64 : BitVec 64).ult (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)) = true := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
      have hhi_ule :
          (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ule 7#64 = false := by
        simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
      refine of_sepWP_lscl ((blkPl_60).base + 952#64) hF808c hsym808c ?_
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF_pad1 hsym_pad1
      apply SepWPp.fold (fold_pad_lt_378 C.F s0.sp sender receiver macKey message hpad)
      · sep_focus
      exact SepWPp.apply_join hjoin952
        ⟨hF_pad1, hsym_pad1,
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by sep_focus)
    · have hpad_ge : 56 ≤ (mkMacEnv sender receiver macKey message).innerPos := by omega
      have hhi_le : 63 - (mkMacEnv sender receiver macKey message).innerPos ≤ 7 := by omega
      have hhi_gt :
          (7#64 : BitVec 64).ult (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)) = false := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
      have hhi_ule :
          (BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ule 7#64 = true := by
        simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
      have hhi_cond :
          ((!(BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ult 7#64) &&
           !((BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)) == 7#64)) = false :=
        bhi_7_false hhi_le
      have hhi_cond' :
          ¬ ((!(BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)).ult 7#64) &&
             !((BitVec.ofNat 64 (63 - (mkMacEnv sender receiver macKey message).innerPos)) == 7#64)) = true := by
        rw [hhi_cond]; decide
      have hpadBlk_len64 :
          ((mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
            List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8).length = 64 := by
        simp [htail_len]; omega
      have hpadBlk_len :
          ((mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
            List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8).length = 64 * 1 :=
        hpadBlk_len64
      have hpadBlk_len_sub :
          (mkMacEnv sender receiver macKey message).innerPos + 1 +
            (63 - (mkMacEnv sender receiver macKey message).innerPos) = 64 := by omega
      have hpadBlk_len_sub2 :
          (mkMacEnv sender receiver macKey message).innerPos +
            (63 - (mkMacEnv sender receiver macKey message).innerPos + 1) = 64 := by omega
      conv =>
        arg 4
        rw [pointsToBytes_64_352_eq s0.sp hpadBlk_len64, cells_192_8_eq s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
        SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
        SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
        SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun b7 => ?_
      refine of_sepWP_lscl ((blkPl_60).base + 932#64) hF808c hsym808c ?_
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF_pad2a hsym_pad2a
      clear b0 b1 b2 b3 b4 b5 b6 b7
      conv =>
        arg 4
        rw [show (mkMacEnv sender receiver macKey message).innerTail ++
            0x80#8 :: List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 =
          (mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
            List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 by simp]
      apply SepWPp.fold (fold_8_words_192 s0.sp hpadBlk_len64)
      · sep_focus
      refine of_sepWP_lscl ((blkPl_60).base + 952#64) hF_pad2a hsym_pad2a ?_
      wp_steps_lscl (lsρ lsMacCompress256Sym)
      wp_call hcompress (s0.sp - 288#64,
        (mkMacEnv sender receiver macKey message).hState C.F
          (mkMacEnv sender receiver macKey message).innerB,
        s0.sp - 192#64,
        (mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
          List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8,
        1)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF_pad2b hsym_pad2b
      conv =>
        arg 4
        rw [show (mkMacEnv sender receiver macKey message).innerTail ++
            0x80#8 :: List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 =
          (mkMacEnv sender receiver macKey message).innerTail ++ [0x80#8] ++
            List.replicate (63 - (mkMacEnv sender receiver macKey message).innerPos) 0#8 by simp]
      apply SepWPp.fold (fold_pad_ge_378 C.F s0.sp sender receiver macKey message _ hpad_ge)
      · sep_focus
      exact SepWPp.apply_join hjoin952
        ⟨hF_pad2b, hsym_pad2b,
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by sep_focus)
  by_cases hshort : message.length < 62
  · have hult62 : (BitVec.ofNat 64 message.length).ult 62#64 = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hpos_short :
        2#8 + BitVec.zeroExtend 8 (BitVec.ofNat 64 message.length) =
          BitVec.ofNat 8 (message.length + 2) := by
      bv_omega
    apply SepWPp.fold (fold_short_pre s0.sp message.length hshort)
    · sep_focus
    refine of_sepWP_lscl ((blkPl_60).base + 808#64) hF5e hsym5e ?_
    wp_steps_lscl (lsρ lsMacMemcpySym)
    wp_call hmemcpy (s0.sp - 494#64, msgA, message)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF_sh hsym_sh
    apply SepWPp.fold (fold_short_post C.F s0.sp sender receiver macKey message hshort _ rfl)
    · sep_focus
    exact SepWPp.apply_join hjoin808
      ⟨hF_sh, hsym_sh,
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
      (by sep_focus)
  · have hge62 : 62 ≤ message.length := by omega
    have hult62 : (BitVec.ofNat 64 message.length).ult 62#64 = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hult62' : ¬ (BitVec.ofNat 64 message.length).ult 62#64 = true := by
      rw [hult62]; decide
    have hlen_m62 : (message.take 62).length = 62 := by simp; omega
    have hlen_m62_min : min 62 message.length = 62 := by omega
    have hblk3_len : (receiver.publicKey.serialize.drop 31 ++ message.take 62).length = 64 * 1 := by
      simp [PublicKey.serialize]; omega
    refine of_sepWP_lscl ((blkPl_60).base + 704#64) hF5e hsym5e ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF_lg1 hsym_lg1
    apply SepWPp.fold (fold_long_pre_62 s0.sp msgA message 2#8 hge62)
    · sep_focus
    refine of_sepWP_lscl ((blkPl_60).base + 708#64) hF_lg1 hsym_lg1 ?_
    wp_steps_lscl (lsρ lsMacMemcpySym)
    wp_call hmemcpy (s0.sp - 494#64, msgA, message.take 62)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF_lg2 hsym_lg2
    apply SepWPp.fold (fold_blk3 s0.sp (receiver.publicKey.serialize.drop 31)
      (message.take 62) hlen_r2)
    · sep_focus
    refine of_sepWP_lscl ((blkPl_60).base + 736#64) hF_lg2 hsym_lg2 ?_
    wp_steps_lscl (lsρ lsMacCompress256Sym)
    wp_call hcompress (s0.sp - 432#64, (mkMacEnv sender receiver macKey message).hState C.F 2,
      s0.sp - 496#64, receiver.publicKey.serialize.drop 31 ++ message.take 62, 1)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF_lg3 hsym_lg3
    conv =>
      arg 4
      rw [mkMacEnv_hState_three C.F sender receiver macKey message hge62]
    have hlsr6 : (BitVec.ofNat 64 message.length - 62#64) >>> 6 =
        BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull :=
      sub62_ushiftRight_6 hge62 h
    have hand_mask : (BitVec.ofNat 64 message.length - 62#64) &&& 0x7fffffffffffffc0#64 =
        BitVec.ofNat 64 (64 * (mkMacEnv sender receiver macKey message).nFull) :=
      sub62_and_mask64 hge62 h
    have hand_63 : (BitVec.ofNat 64 message.length - 62#64) &&& 63#64 =
        BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerTail.length := by
      rw [mkMacEnv_innerTail_length, mkMacEnv_innerPos_eq sender receiver macKey message hge62]
      exact sub62_and_63 hge62 h
    have hpos_long :
        BitVec.zeroExtend 8 (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerTail.length) =
          BitVec.ofNat 8 (mkMacEnv sender receiver macKey message).innerTail.length := by
      bv_omega
    have htail_lt := mkMacEnv_innerTail_length_lt sender receiver macKey message
    have htail_toNat :
        (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerTail.length).toNat =
          (mkMacEnv sender receiver macKey message).innerTail.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hnFull_toNat :
        (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull).toNat =
          (mkMacEnv sender receiver macKey message).nFull := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      change (message.length - 62) / 64 < 2 ^ 64
      omega
    have hfull_len :
        ((message.drop 62).take (64 * (mkMacEnv sender receiver macKey message).nFull)).length =
          64 * (mkMacEnv sender receiver macKey message).nFull := by
      rw [List.length_take, List.length_drop]
      exact Nat.min_eq_left (Nat.mul_div_le (message.length - 62) 64)
    have hfull_len_min :
        min (64 * (mkMacEnv sender receiver macKey message).nFull) (message.length - 62) =
          64 * (mkMacEnv sender receiver macKey message).nFull := by
      simpa only [List.length_take, List.length_drop] using hfull_len
    apply SepWPp.fold (fold_post_blk3 s0.sp msgA sender receiver macKey message
      (receiver.publicKey.serialize.drop 31 ++ message.take 62) hblk3_len hge62)
    · sep_focus
    conv =>
      arg 4
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b63' => ?_
    by_cases hnFull : (mkMacEnv sender receiver macKey message).nFull = 0
    · have hcbz1 : (BitVec.ofNat 64 message.length - 62#64) >>> 6 = 0#64 := by
        rw [hlsr6, hnFull]
      have hinnerB_eq : (mkMacEnv sender receiver macKey message).innerB = 3 := by
        rw [mkMacEnv_innerB_eq sender receiver macKey message hge62, hnFull]
      refine of_sepWP_lscl ((blkPl_60).base + 808#64) hF_lg3 hsym_lg3 ?_
      wp_steps_lscl (lsρ lsMacMemcpySym)
      wp_call hmemcpy (s0.sp - 496#64,
        msgA + 62#64 + BitVec.ofNat 64 (64 * (mkMacEnv sender receiver macKey message).nFull),
        (mkMacEnv sender receiver macKey message).innerTail)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF_lg4a hsym_lg4a
      conv =>
        arg 4
        rw [← hinnerB_eq]
      apply SepWPp.fold (fold_rejoin_msg_long msgA sender receiver macKey message hge62)
      · sep_focus
      apply SepWPp.fold (fold_long_post C.F s0.sp sender receiver macKey message _ _
        rfl rfl)
      · sep_focus
      exact SepWPp.apply_join hjoin808
        ⟨hF_lg4a, hsym_lg4a,
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by sep_focus)
    · have hcbz1 : (BitVec.ofNat 64 message.length - 62#64) >>> 6 ≠ 0#64 := by
        rw [hlsr6]
        intro heq
        apply hnFull
        have := congrArg BitVec.toNat heq
        simpa [hnFull_toNat] using this
      have hcbz1_ne : BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull ≠ 0#64 := by
        rw [← hlsr6]; exact hcbz1
      have hcbz1_beq : (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull == 0#64) = false :=
        beq_false_of_ne hcbz1_ne
      have hcbz1_beq' : ¬ (BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull == 0#64) = true := by
        rw [hcbz1_beq]; decide
      have hblk_word1 :
          3#64 + BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).nFull =
            BitVec.ofNat 64 (mkMacEnv sender receiver macKey message).innerB := by
        rw [mkMacEnv_innerB_eq sender receiver macKey message hge62]
        bv_omega
      refine of_sepWP_lscl ((blkPl_60).base + 808#64) hF_lg3 hsym_lg3 ?_
      wp_steps_lscl (lsρ lsMacCompress256Sym)
      refine seq_lscl_compute (lsρ lsMacMemcpySym) ‹_› ‹_› ?_
      wp_call hcompress (s0.sp - 432#64, (mkMacEnv sender receiver macKey message).hState C.F 3,
        msgA + 62#64,
        (message.drop 62).take (64 * (mkMacEnv sender receiver macKey message).nFull),
        (mkMacEnv sender receiver macKey message).nFull)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF_step2 hsym_step2
      wp_call hmemcpy (s0.sp - 496#64,
        msgA + 62#64 + BitVec.ofNat 64 (64 * (mkMacEnv sender receiver macKey message).nFull),
        (mkMacEnv sender receiver macKey message).innerTail)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hF_lg4b hsym_lg4b
      conv =>
        arg 4
        rw [mkMacEnv_hState_full C.F sender receiver macKey message hge62]
      apply SepWPp.fold (fold_rejoin_msg_long msgA sender receiver macKey message hge62)
      · sep_focus
      apply SepWPp.fold (fold_long_post C.F s0.sp sender receiver macKey message _ _
        rfl rfl)
      · sep_focus
      exact SepWPp.apply_join hjoin808
        ⟨hF_lg4b, hsym_lg4b,
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *],
         by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by sep_focus)

private theorem newFromSlice_placed_ok [LibsignalPlacement] (C : Crypto)
    {prog : Program} {addr : BitVec 64}
    (hnew : subroutine_ok prog addr (withLsCodeLoaded lsmpl (newFromSliceSpec C.F))) :
    subroutine_ok prog addr
      ((newFromSlicePkStackSpec C.F).withLsClState (LsClState := fun s => LibsignalCodeLoaded lsmpl s.mem)) := by
  have hnew' := subroutine_ok_withLsClState_of_lscl hnew
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome hnew' x (memRegion (s0.sp - 4128#64) 3584 ∗ R) s0 hpc hrun
    (by simpa only [Spec.withLsClState, newFromSliceSpec, newFromSlicePkStackSpec,
      stackAt_pk_eq_nfs, sepConj_assoc] using hpre) hsp fun _ hraw => ?_
  unfold SubroutineOutcome at hraw ⊢
  simpa only [Spec.withLsClState, newFromSliceSpec, newFromSlicePkStackSpec,
    stackAt_pk_eq_nfs, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw

private theorem newFromSlice_placed_ok_x [LibsignalPlacement] (C : Crypto)
    {prog : Program} {addr : BitVec 64}
    (hnew : subroutine_ok prog addr (withLsCodeLoaded lsmpl (newFromSliceSpec C.F))) :
    subroutine_ok prog addr
      ((newFromSlicePkStackSpecX C.F).withLsClState (LsClState := fun s => LibsignalCodeLoaded lsmpl s.mem)) := by
  have hnew' := subroutine_ok_withLsClState_of_lscl hnew
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome hnew' x (memRegion (s0.sp - 16416#64) 15872 ∗ R) s0 hpc hrun
    (by simpa only [Spec.withLsClState, newFromSliceSpec, newFromSlicePkStackSpecX, newFromSlicePkStackSpecAt,
      stackAt_pkX_eq_nfs, sepConj_assoc] using hpre) hsp fun _ hraw => ?_
  unfold SubroutineOutcome at hraw ⊢
  simpa only [Spec.withLsClState, newFromSliceSpec, newFromSlicePkStackSpecX, newFromSlicePkStackSpecAt,
    stackAt_pkX_eq_nfs, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw

private theorem dealloc_pkStack_placed_ok {prog : Program} {addr : BitVec 64}
    {A : RustAlloc} {pkStack : Nat}
    (hdeel : subroutine_ok prog addr (rustDeallocExternSpecWithStack A pkStack)) :
    subroutine_ok prog addr (rustDeallocPkStackSpecAt A pkStack) := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (rustDeallocExternSpecWithStack A pkStack).pre (p, bs.length, 1) s0 ∗ R := by
    simp only [rustDeallocExternSpecWithStack, rustDeallocPkStackSpecAt,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hbs⟩, hmem⟩
    have hlay : LayoutOk bs.length 1 := by
      rw [hbs]; exact ⟨by decide, ⟨0, rfl⟩, by decide⟩
    refine ⟨⟨hx0, hx1, hx2, hlay⟩, ?_⟩
    have hm : s0.mem ⊨ (p ↦ₛ bs) ∗ (A.pool ∗ A.live p bs.length 1 ∗ stackAt s0.sp pkStack ∗ R) := by
      refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hmem
      ac_rfl
    have hm2 := Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion p bs)) hm
    refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hm2
    ac_rfl
  refine subroutine_ok.mono_outcome hdeel (p, bs.length, 1) R s0 hpc hrun hpre' hsp fun _ hraw => ?_
  unfold SubroutineOutcome at hraw ⊢
  simpa only [rustDeallocExternSpecWithStack, rustDeallocPkStackSpecAt,
    satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw

private theorem newFromSlice_placed_cro_ok [LibsignalPlacement] (C : Crypto)
    {prog : Program} {addr : BitVec 64}
    (hnew : subroutine_ok prog addr (withLsCodeRoLoaded lsmpl (newFromSliceSpec C.F))) :
    subroutine_ok prog addr
      ((newFromSlicePkStackSpec C.F).withLsClState (LsClState := fun s => LibsignalCodeRoLoaded lsmpl s.mem)) := by
  have hnew' := subroutine_ok_withLsClState_of_lscro hnew
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine subroutine_ok.mono_outcome hnew' x (memRegion (s0.sp - 4128#64) 3584 ∗ R) s0 hpc hrun
    (by simpa only [Spec.withLsClState, newFromSliceSpec, newFromSlicePkStackSpec,
      stackAt_pk_eq_nfs, sepConj_assoc] using hpre) hsp fun _ hraw => ?_
  unfold SubroutineOutcome at hraw ⊢
  simpa only [Spec.withLsClState, newFromSliceSpec, newFromSlicePkStackSpec,
    stackAt_pk_eq_nfs, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw

theorem computeMac_placed_ok_of_contracts [LibsignalPlacement]
    (pkStack : Nat) (hbound : pkStack + 496 < 2 ^ 64 := by decide)
    (C : Crypto) (A : RustAlloc)
    (H : String → Option (State → State))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 114)
      ((newFromSlicePkStackSpecAt C.F pkStack).withLsClState (LsClState := fun s => LibsignalCodeLoaded lsmpl s.mem)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeSpecAt A pkStack)))
    (hmemcpy : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacMemcpySym) framelessMemcpySpec)
    (hcompress : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacCompress256Sym) (session2Compress256Spec C.F))
    (hdealloc : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacRustDeallocSym) (rustDeallocExternSpecWithStack A pkStack))
    (hmemset : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacMemsetSym) sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (blkPl_60).base
      (withLsCodeLoaded lsmpl (computeMacSpecAt C.F A pkStack)) := by
  have hmemset' := session2Memset_of_sessionMemsetRegion hmemset
  exact subroutine_ok_lscl_of_withLsClState (computeMac_placed_ok_of_hooks_gen pkStack hbound C A H
    hnew
    (subroutine_ok_withLsClState_of_lscl hpk)
    (fun sp_cur => subroutine_ok_withLsClState_of_plain
      (subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => by
        simp only [session2MemcpyPkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, _⟩, hmem⟩
        refine subroutine_ok.mono_outcome hmemcpy (dst, src, bs) (stackAt sp_cur pkStack ∗ R) s0 hpc hrun
          (by simpa only [framelessMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hx0, hx1, hx2⟩, hmem⟩) hsp fun _ hraw => ?_
        unfold SubroutineOutcome at hraw ⊢
        simpa only [framelessMemcpySpec, session2MemcpyPkStackSpecAt, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw))
    (fun sp_cur => subroutine_ok_withLsClState_of_plain
      (subroutine_ok_outcome_intro fun ⟨stA, st, blkA, blk, n⟩ R s0 hpc hrun hpre hsp => by
        simp only [session2Compress256PkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, hblk, _⟩, hmem⟩
        refine subroutine_ok.mono_outcome hcompress (stA, st, blkA, blk, n) (stackAt sp_cur pkStack ∗ R) s0 hpc hrun
          (by simpa only [session2Compress256Spec, sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hx0, hx1, hx2, hblk⟩, hmem⟩) hsp fun _ hraw => ?_
        unfold SubroutineOutcome at hraw ⊢
        simpa only [session2Compress256Spec, session2Compress256PkStackSpecAt, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw))
    (subroutine_ok_withLsClState_of_plain (dealloc_pkStack_placed_ok hdealloc))
    (fun sp_cur => subroutine_ok_withLsClState_of_plain
      (subroutine_ok_outcome_intro fun ⟨dst, val, n⟩ R s0 hpc hrun hpre hsp => by
        simp only [session2MemsetPkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, _⟩, hmem⟩
        refine subroutine_ok.mono_outcome hmemset' (dst, val, n) (stackAt sp_cur pkStack ∗ R) s0 hpc hrun
          (by simpa only [session2MemsetSpec, sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hx0, hx1, hx2⟩, hmem⟩) hsp fun _ hraw => ?_
        unfold SubroutineOutcome at hraw ⊢
        simpa only [session2MemsetSpec, session2MemsetPkStackSpecAt, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw)))

theorem computeMac_placed_cro_ok_of_contracts [LibsignalPlacement]
    (pkStack : Nat) (hbound : pkStack + 496 < 2 ^ 64 := by decide)
    (C : Crypto) (A : RustAlloc)
    (H : String → Option (State → State))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 114)
      ((newFromSlicePkStackSpecAt C.F pkStack).withLsClState (LsClState := fun s => LibsignalCodeRoLoaded lsmpl s.mem)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 205) (withLsCodeRoLoaded lsmpl (publicKeySerializeSpecAt A pkStack)))
    (hmemcpy : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacMemcpySym) framelessMemcpySpec)
    (hcompress : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacCompress256Sym) (session2Compress256Spec C.F))
    (hdealloc : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacRustDeallocSym) (rustDeallocExternSpecWithStack A pkStack))
    (hmemset : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsρ lsMacMemsetSym) sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (blkPl_60).base
      (withLsCodeRoLoaded lsmpl (computeMacSpecAt C.F A pkStack)) := by
  have hmemset' := session2Memset_of_sessionMemsetRegion hmemset
  exact subroutine_ok_lscro_of_withLsClState (computeMac_placed_ok_of_hooks_gen pkStack hbound C A H
    hnew
    (subroutine_ok_withLsClState_of_lscro hpk)
    (fun sp_cur => subroutine_ok_withLsClState_of_plain
      (subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => by
        simp only [session2MemcpyPkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, _⟩, hmem⟩
        refine subroutine_ok.mono_outcome hmemcpy (dst, src, bs) (stackAt sp_cur pkStack ∗ R) s0 hpc hrun
          (by simpa only [framelessMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hx0, hx1, hx2⟩, hmem⟩) hsp fun _ hraw => ?_
        unfold SubroutineOutcome at hraw ⊢
        simpa only [framelessMemcpySpec, session2MemcpyPkStackSpecAt, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw))
    (fun sp_cur => subroutine_ok_withLsClState_of_plain
      (subroutine_ok_outcome_intro fun ⟨stA, st, blkA, blk, n⟩ R s0 hpc hrun hpre hsp => by
        simp only [session2Compress256PkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, hblk, _⟩, hmem⟩
        refine subroutine_ok.mono_outcome hcompress (stA, st, blkA, blk, n) (stackAt sp_cur pkStack ∗ R) s0 hpc hrun
          (by simpa only [session2Compress256Spec, sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hx0, hx1, hx2, hblk⟩, hmem⟩) hsp fun _ hraw => ?_
        unfold SubroutineOutcome at hraw ⊢
        simpa only [session2Compress256Spec, session2Compress256PkStackSpecAt, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw))
    (subroutine_ok_withLsClState_of_plain (dealloc_pkStack_placed_ok hdealloc))
    (fun sp_cur => subroutine_ok_withLsClState_of_plain
      (subroutine_ok_outcome_intro fun ⟨dst, val, n⟩ R s0 hpc hrun hpre hsp => by
        simp only [session2MemsetPkStackSpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, _⟩, hmem⟩
        refine subroutine_ok.mono_outcome hmemset' (dst, val, n) (stackAt sp_cur pkStack ∗ R) s0 hpc hrun
          (by simpa only [session2MemsetSpec, sepConj_assoc, satisfies_pure_sepConj] using ⟨⟨hx0, hx1, hx2⟩, hmem⟩) hsp fun _ hraw => ?_
        unfold SubroutineOutcome at hraw ⊢
        simpa only [session2MemsetSpec, session2MemsetPkStackSpecAt, satisfies_pure_sepConj, false_and, sepConj_assoc] using hraw)))

theorem computeMac_placed_cro_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (H : String → Option (State → State))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 114) (withLsCodeRoLoaded lsmpl (newFromSliceSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 205) (withLsCodeRoLoaded lsmpl (publicKeySerializeSpec A)))
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256Spec C.F))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (blkPl_60).base
      (withLsCodeRoLoaded lsmpl (computeMacSpec C.F A)) :=
  computeMac_placed_cro_ok_of_contracts publicKeySerializeStack (by decide) C A H
    (newFromSlice_placed_cro_ok C hnew)
    hpk
    (mac_ls_hook_ok_of_mem hmemcpy)
    (mac_ls_hook_ok_of_mem hcompress)
    (rustDeallocExternWithStack_of_rustDealloc (mac_ls_hook_ok_of_mem hdealloc) (by decide) (by decide))
    (mac_ls_hook_ok_of_mem hmemset)

theorem computeMac_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (H : String → Option (State → State))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 114) (withLsCodeLoaded lsmpl (newFromSliceSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256Spec C.F))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (blkPl_60).base
      (withLsCodeLoaded lsmpl (computeMacSpec C.F A)) :=
  computeMac_placed_ok_of_contracts publicKeySerializeStack (by decide) C A H
    (newFromSlice_placed_ok C hnew)
    hpk
    (mac_ls_hook_ok_of_mem hmemcpy)
    (mac_ls_hook_ok_of_mem hcompress)
    (rustDeallocExternWithStack_of_rustDealloc (mac_ls_hook_ok_of_mem hdealloc) (by decide) (by decide))
    (mac_ls_hook_ok_of_mem hmemset)

theorem computeMac_placed_ok_x [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (H : String → Option (State → State))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 114) (withLsCodeLoaded lsmpl (newFromSliceSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (lsmpl.base 205) (withLsCodeLoaded lsmpl (publicKeySerializeSpecX A)))
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256Spec C.F))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base H)
      (blkPl_60).base
      (withLsCodeLoaded lsmpl (computeMacSpecX C.F A)) :=
  computeMac_placed_ok_of_contracts publicKeySerializeStackX (by decide) C A H
    (newFromSlice_placed_ok_x C hnew)
    hpk
    (mac_ls_hook_ok_of_mem hmemcpy)
    (mac_ls_hook_ok_of_mem hcompress)
    (rustDeallocExternWithStack_of_rustDealloc (mac_ls_hook_ok_of_mem hdealloc) (by decide) (by decide))
    (mac_ls_hook_ok_of_mem hmemset)

end CryptoVerification.LibsignalTripleRatchet


