/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.SpqrSimChain
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainDir
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.ChainRecv
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TightSize
import LibsignalBinary.Proofs.SpqrV1Sync.ChainSync
import LibsignalBinary.Proofs.SpqrV1Sync.ChainSyncBase
import Computational.Proofs.E2E.ComposedBinaryLinkV1

/-!
# SPQR V1 `ReductionDsl` `KeyHistory` and Receive-Chain Helpers

Implements `ReductionDsl` expressions and `Comp` programs for SPQR V1 `KeyHistory.get`,
table-backed `O(K)` list reversal, `KeyHistory.gc`, bounded `keyAdvanceLoop`,
`ChainEpochDirection.key`, and `Chain.recvKey`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.SpqrSimHist

open List Option Prod BitVec OracleSpec OracleComp
open ReductionDsl (Ty Ops Var Expr Comp Iface Env bits iterM)
open CryptoGames.HMAC (toBEBytes keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey)
open CryptoVerification.E2E (Bytes keyToBytes32_bytesToKey32 bytesToKey32_keyToBytes32)
open CryptoVerification.E2E.Costed (B U8 U32 U64 BV256 E2EPureOp
  e2eSig e2ePureOps e2eOps spqrParamsT spqrPrevEntryT spqrDirT spqrEpochLinkT spqrChainT
  e2eReadU32BE splitSpqrPrev joinSpqrPrev spqrParamsToV spqrDirToV spqrChainToV)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp eval_e2ePureOp cost_e2ePureOp)
open Computational.Proofs.E2E.Dsl.ClampsLossless (toBEBytes4_e2eReadU32BE
  joinSpqrPrev_splitSpqrPrev spqrChainNextKeyEval_take32_lossless spqrChainNextKeyRaw)
open Computational.Proofs.E2E.Dsl.SpqrSimChain (spqrChainNextKeyC cost_spqrChainNextKeyC
  queries_spqrChainNextKeyC eval_spqrChainNextKeyC
  listGetExpr eval_listGetExpr cost_listGetExpr
  listSetExpr eval_listSetExpr cost_listSetExpr
  spqrEpochIdxExpr eval_spqrEpochIdxExpr cost_spqrEpochIdxExpr)
open CryptoVerification.LibsignalSpqrV1 (MlKem Direction ChainParamsPB EpochDirectionPB
  Chain KeyHistory ChainEpoch ChainEpochDirection spqrHkdfWith ChainResult bytesLt)
open CryptoVerification.SpqrV1Sync.ChainSync (ChainOk RecvDirOk dparams seedAt)
open LibsignalBinary.Proofs.SpqrV1Sync.ChainSyncBase (dparams_maxOoo dparams_maxJump
  dparams_trimSize length_nextAt length_seedAt bytesLt_toBEBytes4 toBEBytes4_injective)
open CryptoVerification.SpqrV1Sync.SendTotal (RecvSmallTight crcv_epochIdx_eq st_recvPrev_tight)

/-! ## `KeyHistory` entry encoding -/

def encodePrevEntries (es : List (BitVec 32 × BitVec 256)) : Bytes :=
  joinSpqrPrev es []

def prevEntryBytes (e : BitVec 32 × BitVec 256) : Bytes :=
  toBEBytes 4 e.1 ++ keyToBytes32 e.2

private theorem length_toBEBytes4 (x : BitVec 32) : (toBEBytes 4 x).length = 4 := rfl

private theorem length_keyToBytes32 (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

theorem prevEntryBytes_length (e : BitVec 32 × BitVec 256) :
    (prevEntryBytes e).length = 36 := by
  rw [prevEntryBytes, List.length_append, length_toBEBytes4, length_keyToBytes32]

private theorem encodePrevEntries_eq_flatMap (es : List (BitVec 32 × BitVec 256)) :
    encodePrevEntries es = es.flatMap prevEntryBytes := by
  simp only [encodePrevEntries, joinSpqrPrev, List.take_nil, List.append_nil]
  rfl

@[simp] theorem encodePrevEntries_nil : encodePrevEntries [] = [] := rfl

theorem encodePrevEntries_cons (e : BitVec 32 × BitVec 256)
    (es : List (BitVec 32 × BitVec 256)) :
    encodePrevEntries (e :: es) = prevEntryBytes e ++ encodePrevEntries es := by
  simp [encodePrevEntries_eq_flatMap, List.flatMap_cons]

theorem encodePrevEntries_append (xs ys : List (BitVec 32 × BitVec 256)) :
    encodePrevEntries (xs ++ ys) = encodePrevEntries xs ++ encodePrevEntries ys := by
  simp [encodePrevEntries_eq_flatMap, List.flatMap_append]

theorem length_encodePrevEntries :
    ∀ es : List (BitVec 32 × BitVec 256), (encodePrevEntries es).length = 36 * es.length
  | [] => rfl
  | e :: es => by
    rw [encodePrevEntries_cons, List.length_append, prevEntryBytes_length,
      length_encodePrevEntries es, List.length_cons]
    omega

private theorem take_prefix_eq {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).take xs.length = xs
  | [], _ => rfl
  | _ :: xs, ys => by simp [take_prefix_eq xs ys]

private theorem drop_prefix_eq {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).drop xs.length = ys
  | [], _ => rfl
  | _ :: xs, ys => by simp [drop_prefix_eq xs ys]

private theorem take_of_len_eq {α : Type} {xs ys : List α} {n : ℕ} (h : xs.length = n) :
    (xs ++ ys).take n = xs := by
  subst h
  exact take_prefix_eq xs ys

private theorem drop_of_len_eq {α : Type} {xs ys : List α} {n : ℕ} (h : xs.length = n) :
    (xs ++ ys).drop n = ys := by
  subst h
  exact drop_prefix_eq xs ys

private theorem drop_add_eq {α : Type} :
    ∀ (a b : ℕ) (xs : List α), xs.drop (a + b) = (xs.drop a).drop b
  | 0, _, _ => by simp
  | a + 1, _, [] => by simp
  | a + 1, b, _ :: xs => by
    rw [Nat.succ_add]
    exact drop_add_eq a b xs

theorem encodePrevEntries_drop :
    ∀ (k : ℕ) (es : List (BitVec 32 × BitVec 256)),
      (encodePrevEntries es).drop (36 * k) = encodePrevEntries (es.drop k)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, e :: es => by
    have hmul : 36 * (k + 1) = (prevEntryBytes e).length + 36 * k := by
      rw [prevEntryBytes_length]; omega
    rw [encodePrevEntries_cons, hmul, drop_add_eq, drop_prefix_eq, encodePrevEntries_drop k es]
    rfl

theorem encodePrevEntries_take :
    ∀ (k : ℕ) (es : List (BitVec 32 × BitVec 256)),
      (encodePrevEntries es).take (36 * k) = encodePrevEntries (es.take k)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, e :: es => by
    have hlen : (prevEntryBytes e).length = 36 := prevEntryBytes_length e
    rw [encodePrevEntries_cons, List.take_append, hlen,
      List.take_of_length_le (by rw [hlen]; omega),
      show 36 * (k + 1) - 36 = 36 * k by omega,
      encodePrevEntries_take k es]
    rfl

theorem e2eReadU32BE_toBEBytes4 (x : BitVec 32) : e2eReadU32BE (toBEBytes 4 x) = x := by
  have h4 : toBEBytes 4 x =
      [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8] := rfl
  apply toBEBytes4_injective
  have hrt := toBEBytes4_e2eReadU32BE
    (x.extractLsb' 24 8) (x.extractLsb' 16 8) (x.extractLsb' 8 8) (x.extractLsb' 0 8)
  simpa [h4] using hrt

theorem splitSpqrPrev_encodePrevEntries :
    ∀ {fuel : ℕ} (es : List (BitVec 32 × BitVec 256)),
      es.length ≤ fuel → splitSpqrPrev fuel (encodePrevEntries es) = (es, [])
  | fuel, [], _ => by
    cases fuel <;> simp [splitSpqrPrev]
  | 0, _ :: _, h => by
    simp at h
  | fuel + 1, e :: rest, h => by
    have hrest : rest.length ≤ fuel := by
      simp only [List.length_cons] at h
      omega
    have hge36 : ¬ ((encodePrevEntries (e :: rest)).length < 36) := by
      rw [length_encodePrevEntries, List.length_cons]
      omega
    unfold splitSpqrPrev
    simp only [hge36, ↓reduceIte]
    have hcons : encodePrevEntries (e :: rest) =
        toBEBytes 4 e.1 ++ (keyToBytes32 e.2 ++ encodePrevEntries rest) := by
      rw [encodePrevEntries_cons, prevEntryBytes, List.append_assoc]
    have htake4 : (encodePrevEntries (e :: rest)).take 4 = toBEBytes 4 e.1 := by
      rw [hcons, take_of_len_eq (length_toBEBytes4 e.1)]
    have hdrop4_take32 : ((encodePrevEntries (e :: rest)).drop 4).take 32 = keyToBytes32 e.2 := by
      rw [hcons, drop_of_len_eq (length_toBEBytes4 e.1), take_of_len_eq (length_keyToBytes32 e.2)]
    have hdrop36 : (encodePrevEntries (e :: rest)).drop 36 = encodePrevEntries rest := by
      rw [encodePrevEntries_cons, drop_of_len_eq (prevEntryBytes_length e)]
    rw [htake4, hdrop4_take32, hdrop36, e2eReadU32BE_toBEBytes4, bytesToKey32_keyToBytes32,
      splitSpqrPrev_encodePrevEntries rest hrest]

private theorem splitSpqrPrev_mod36_aux :
    ∀ (fuel : ℕ) (bs : Bytes),
      bs.length ≤ 36 * fuel →
      bs.length % 36 = 0 →
      (splitSpqrPrev fuel bs).2 = [] ∧ (splitSpqrPrev fuel bs).1.length = bs.length / 36
  | 0, bs, hlen, _ => by
    have h0 : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h0
    simp [splitSpqrPrev]
  | fuel + 1, bs, hlen, hmod => by
    unfold splitSpqrPrev
    by_cases hlt : bs.length < 36
    · have h0 : bs.length = 0 := by omega
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero h0
      subst hbs
      simp
    · simp only [hlt, ↓reduceIte]
      have hdrop_len : (bs.drop 36).length ≤ 36 * fuel := by
        simp only [List.length_drop]
        omega
      have hdrop_mod : (bs.drop 36).length % 36 = 0 := by
        simp only [List.length_drop]
        omega
      obtain ⟨htail, hcnt⟩ := splitSpqrPrev_mod36_aux fuel (bs.drop 36) hdrop_len hdrop_mod
      refine ⟨htail, ?_⟩
      simp only [List.length_cons, hcnt, List.length_drop]
      omega

theorem splitSpqrPrev_of_mod36 {fuel : ℕ} {bs : Bytes}
    (hlen : bs.length ≤ 36 * fuel) (hmod : bs.length % 36 = 0) :
    ∃ es : List (BitVec 32 × BitVec 256),
      splitSpqrPrev fuel bs = (es, []) ∧
      es.length = bs.length / 36 ∧
      encodePrevEntries es = bs := by
  obtain ⟨htail, hcnt⟩ := splitSpqrPrev_mod36_aux fuel bs hlen hmod
  have hrt := joinSpqrPrev_splitSpqrPrev fuel bs (by omega)
  rw [htail] at hrt
  refine ⟨(splitSpqrPrev fuel bs).1, ?_, hcnt, hrt⟩
  cases hsp : splitSpqrPrev fuel bs with
  | mk a b =>
    rw [hsp] at htail
    dsimp only at htail ⊢
    subst htail
    rfl

theorem spqrDirToV_eq {ℓ : ℕ} (d : EpochDirectionPB) {es : List (BitVec 32 × BitVec 256)}
    {tail : Bytes} (hnext : d.next.length ≤ 64)
    (hsplit : splitSpqrPrev 2201 d.prev = (es, tail)) :
    spqrDirToV (ℓ := ℓ) d = (d.ctr, (d.next, (es, tail))) := by
  unfold spqrDirToV
  rw [hsplit, List.take_of_length_le hnext]

theorem encodePrevEntries_tag (es : List (BitVec 32 × BitVec 256)) (k : ℕ)
    (hk : k < es.length) :
    ((encodePrevEntries es).drop (36 * k)).take 4 = toBEBytes 4 es[k].1 := by
  rw [encodePrevEntries_drop, List.drop_eq_getElem_cons hk, encodePrevEntries_cons,
    prevEntryBytes, List.append_assoc, take_of_len_eq (length_toBEBytes4 es[k].1)]

theorem encodePrevEntries_key (es : List (BitVec 32 × BitVec 256)) (k : ℕ)
    (hk : k < es.length) :
    ((encodePrevEntries es).drop (36 * k + 4)).take 32 = keyToBytes32 es[k].2 := by
  rw [drop_add_eq, encodePrevEntries_drop, List.drop_eq_getElem_cons hk, encodePrevEntries_cons,
    prevEntryBytes, List.append_assoc, drop_of_len_eq (length_toBEBytes4 es[k].1),
    take_of_len_eq (length_keyToBytes32 es[k].2)]

private theorem swap_remove_list_eq {α : Type} (es : List α) (k : ℕ)
    (hk : k + 1 < es.length) :
    es.take k ++ [es[es.length - 1]'(by omega)] ++ (es.take (es.length - 1)).drop (k + 1) =
      (es.set k (es[es.length - 1]'(by omega))).take (es.length - 1) := by
  rw [List.append_assoc]
  apply List.ext_getElem
  · simp only [List.length_append, List.length_take, List.length_singleton, List.length_drop,
      List.length_set]
    omega
  · intro i hi1 hi2
    simp only [List.length_take, List.length_set] at hi2
    have hi_lt : i < es.length - 1 := by omega
    rw [List.getElem_take, List.getElem_set]
    by_cases h1 : i < (es.take k).length
    · rw [List.getElem_append_left h1, List.getElem_take]
      have hne : k ≠ i := by simp only [List.length_take] at h1; omega
      simp [hne]
    · rw [List.getElem_append_right (Nat.le_of_not_lt h1)]
      have htk_len : (es.take k).length = k := by simp only [List.length_take]; omega
      by_cases h2 : i - (es.take k).length < 1
      · rw [List.getElem_append_left h2]
        have heq : k = i := by omega
        simp [heq]
      · rw [List.getElem_append_right (Nat.le_of_not_lt h2)]
        simp only [List.length_singleton, List.getElem_drop, List.getElem_take]
        have hne : k ≠ i := by omega
        have hidx : k + 1 + (i - k - 1) = i := by omega
        simp [htk_len, hne, hidx]

theorem remove_encodePrevEntries (es : List (BitVec 32 × BitVec 256)) (k : ℕ)
    (hk : k < es.length) (params : ChainParamsPB) :
    ({ data := encodePrevEntries es } : KeyHistory).remove (36 * k) params =
      ({ data := encodePrevEntries ((es.set k es[es.length - 1]).take (es.length - 1)) } :
        KeyHistory) := by
  unfold KeyHistory.remove
  simp only [KeyHistory.KEY_SIZE, length_encodePrevEntries]
  by_cases hlt : 36 * k + (4 + 32) < 36 * es.length
  · have hk1 : k + 1 < es.length := by omega
    simp only [hlt, ↓reduceIte]
    have hend : 36 * es.length - (4 + 32) = 36 * (es.length - 1) := by omega
    have hstep : 36 * k + (4 + 32) = 36 * (k + 1) := by omega
    have hlast_drop : es.drop (es.length - 1) = [es[es.length - 1]] := by
      have hlt_last : es.length - 1 < es.length := by omega
      rw [List.drop_eq_getElem_cons hlt_last, List.drop_eq_nil_of_le (by omega)]
    rw [hend, hstep, encodePrevEntries_drop, hlast_drop, encodePrevEntries_take,
      encodePrevEntries_take, encodePrevEntries_drop, ← encodePrevEntries_append,
      ← encodePrevEntries_append, swap_remove_list_eq es k hk1]
    congr 1
    apply List.take_of_length_le
    rw [length_encodePrevEntries]
    simp only [List.length_take, List.length_set]
    omega
  · simp only [hlt, ↓reduceIte]
    have hk_eq : k = es.length - 1 := by omega
    subst hk_eq
    congr 1
    rw [encodePrevEntries_take]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.length_take] at hi1
      rw [List.getElem_take, List.getElem_take, List.getElem_set]
      have hne : es.length - 1 ≠ i := by omega
      simp [hne]

/-! ## Table-backed list reversal -/

private def tblSet {α : Type} (m : ℕ → α) (i : ℕ) (v : α) : ℕ → α :=
  fun j => if j = i then v else m j

private def sliceTbl {α : Type} (m : ℕ → α) : ℕ → ℕ → List α
  | _, 0 => []
  | off, len + 1 => m off :: sliceTbl m (off + 1) len

private theorem sliceTbl_length {α : Type} (m : ℕ → α) :
    ∀ (off len : ℕ), (sliceTbl m off len).length = len
  | _, 0 => rfl
  | off, len + 1 => by simp [sliceTbl, sliceTbl_length m (off + 1) len]

private theorem sliceTbl_getElem {α : Type} (m : ℕ → α) :
    ∀ (off len j : ℕ) (hj : j < (sliceTbl m off len).length),
      (sliceTbl m off len)[j] = m (off + j)
  | _, 0, _, hj => by simp [sliceTbl] at hj
  | off, len + 1, 0, _ => by simp [sliceTbl]
  | off, len + 1, j + 1, hj => by
    have hj' : j < (sliceTbl m (off + 1) len).length := by
      simp only [sliceTbl, List.length_cons] at hj
      omega
    simp only [sliceTbl, List.getElem_cons_succ, sliceTbl_getElem m (off + 1) len j hj']
    congr 1
    omega

private theorem foldr_loadTbl_aux {α : Type} (m0 : ℕ → α) :
    ∀ (ys : List α) (off : ℕ),
      (ys.foldr (fun y (p : ℕ × (ℕ → α)) =>
        (p.1 - 1, tblSet p.2 (p.1 - 1) y)) (off + ys.length, m0)).1 = off ∧
      ∀ j : ℕ,
        (ys.foldr (fun y (p : ℕ × (ℕ → α)) =>
          (p.1 - 1, tblSet p.2 (p.1 - 1) y)) (off + ys.length, m0)).2 j =
          if h : off ≤ j ∧ j < off + ys.length then ys[j - off]'(by omega) else m0 j
  | [], off => ⟨by simp, fun j => by simp⟩
  | y :: rest, off => by
    have hlen : off + (y :: rest).length = (off + 1) + rest.length := by
      simp only [List.length_cons]; omega
    obtain ⟨ih1, ih2⟩ := foldr_loadTbl_aux m0 rest (off + 1)
    simp only [List.foldr_cons, hlen]
    refine ⟨by rw [ih1]; omega, fun j => ?_⟩
    rw [ih1]
    have hsub1 : (off + 1) - 1 = off := Nat.add_sub_cancel off 1
    rw [hsub1]
    dsimp only [tblSet]
    by_cases hj : j = off
    · subst hj
      have hcond : j ≤ j ∧ j < (j + 1) + rest.length := ⟨le_refl j, by omega⟩
      simp [hcond]
    · simp only [hj, ↓reduceIte, ih2 j]
      by_cases hcond : off ≤ j ∧ j < (off + 1) + rest.length
      · have hcond' : off + 1 ≤ j ∧ j < (off + 1) + rest.length := ⟨by omega, hcond.2⟩
        have hidx : j - off = (j - (off + 1)) + 1 := by omega
        rw [dite_eq_left hcond', dite_eq_left hcond]
        simp [hidx]
      · have hcond' : ¬ (off + 1 ≤ j ∧ j < (off + 1) + rest.length) := by omega
        rw [dite_eq_right hcond', dite_eq_right hcond]

private theorem foldr_mapIdx_aux {α β : Type} (f : ℕ → α) :
    ∀ (ys : List β) (off : ℕ),
      ys.foldr (fun _ (p : ℕ × List α) => (p.1 - 1, f (p.1 - 1) :: p.2))
        (off + ys.length, []) =
        (off, sliceTbl f off ys.length)
  | [], off => by simp [sliceTbl]
  | y :: rest, off => by
    have hlen : off + (y :: rest).length = (off + 1) + rest.length := by
      simp only [List.length_cons]; omega
    rw [List.foldr_cons, hlen, foldr_mapIdx_aux f rest (off + 1)]
    simp [sliceTbl]

private theorem foldr_sliceTbl_aux {α β : Type} (m : ℕ → α) (curLen : ℕ) :
    ∀ (ys : List β) (off : ℕ),
      curLen ≤ off + ys.length →
      ys.foldr (fun _ (p : ℕ × List α) =>
        (p.1 - 1, if p.1 - 1 < curLen then m (p.1 - 1) :: p.2 else p.2))
        (off + ys.length, []) =
        (off, sliceTbl m off (curLen - off))
  | [], off, hle => by
    have h0 : curLen - off = 0 := by simp at hle; omega
    simp [h0, sliceTbl]
  | y :: rest, off, hle => by
    have hlen : off + (y :: rest).length = (off + 1) + rest.length := by
      simp only [List.length_cons]; omega
    by_cases hlt : off < curLen
    · have hle' : curLen ≤ (off + 1) + rest.length := by rw [← hlen]; exact hle
      have ih := foldr_sliceTbl_aux m curLen rest (off + 1) hle'
      have hsub : curLen - off = (curLen - (off + 1)) + 1 := by omega
      rw [List.foldr_cons, hlen, ih, hsub]
      simp [hlt, sliceTbl]
    · have hle' : curLen ≤ (off + 1) + rest.length := by omega
      have ih := foldr_sliceTbl_aux m curLen rest (off + 1) hle'
      have h0 : curLen - off = 0 := by omega
      have h0' : curLen - (off + 1) = 0 := by omega
      rw [List.foldr_cons, hlen, ih, h0, h0']
      simp [hlt, sliceTbl]

/-- Table-backed `O(K)` list reversal on lists of length at most `K`. -/
def spqrListRevExpr {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (dflt : Expr O Γ t) (l : Expr O Γ (.list t)) :
    Expr O Γ (.list t) :=
  .letE (.pair dflt (.take (.nat K) l))
    (.letE (.len (.snd .v0))
      (.letE (.snd (.foldrB K (.snd .v1)
          (.pair .v0 (.tconst (.fst .v1)))
          (.letE (.sub (.fst .v1) (.nat 1))
            (.pair .v0 (.tset (.snd .v2) .v0 .v1)))))
        (.snd (.foldrB K (.snd .v2)
          (.pair .v1 .nil)
          (.letE (.sub (.fst .v1) (.nat 1))
            (.pair .v0
              (.cons (.tget .v3 (.sub (.sub .v4 (.nat 1)) .v0)) (.snd .v2))))))))

theorem eval_spqrListRevExpr {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (dflt : Expr O Γ t) (l : Expr O Γ (.list t)) (ρ : Env Γ)
    (hlen : (l.eval ρ).length ≤ K) :
    (spqrListRevExpr K dflt l).eval ρ = (l.eval ρ).reverse := by
  simp only [spqrListRevExpr, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Env.get,
    List.take_of_length_le hlen]
  generalize l.eval ρ = xs at hlen ⊢
  generalize dflt.eval ρ = d0
  have hload := (foldr_loadTbl_aux (fun _ => d0) xs 0).2
  simp only [Nat.zero_add, Nat.zero_le, true_and, Nat.sub_zero] at hload
  let tbl := (xs.foldr (fun x acc => (acc.1 - 1, tblSet acc.2 (acc.1 - 1) x))
    (xs.length, fun _ => d0)).2
  have hread := foldr_mapIdx_aux (fun k => tbl (xs.length - 1 - k)) xs 0
  simp only [Nat.zero_add] at hread
  change (xs.foldr (fun _ acc => (acc.1 - 1, tbl (xs.length - 1 - (acc.1 - 1)) :: acc.2))
    (xs.length, [])).2 = xs.reverse
  rw [hread]
  dsimp only
  apply List.ext_getElem
  · rw [sliceTbl_length, List.length_reverse]
  · intro j hj1 hj2
    rw [sliceTbl_length] at hj1
    rw [sliceTbl_getElem, List.getElem_reverse]
    simp only [Nat.zero_add]
    have hlt : xs.length - 1 - j < xs.length := by omega
    simpa [tbl, hlt] using hload (xs.length - 1 - j)

theorem cost_spqrListRevExpr {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (K : ℕ) (dflt : Expr O Γ t) (l : Expr O Γ (.list t)) :
    (spqrListRevExpr K dflt l).cost ≤ dflt.cost + l.cost + 230 * K + 2 * bits K + 30 := by
  have hb1 : bits 1 = 1 := by decide
  simp only [spqrListRevExpr, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, hb1,
    Nat.reduceAdd]
  omega

/-! ## `KeyHistory.get` -/

private theorem u32_add_ovf_iff (a b : BitVec 32) :
    (0xffffffff#32 - b < a) ↔ a.toNat + b.toNat ≥ 2 ^ 32 := by
  have ha := a.isLt
  have hb := b.isLt
  have hle : b ≤ 0xffffffff#32 := by
    simp only [BitVec.le_def, BitVec.toNat_ofNat]
    omega
  simp only [BitVec.lt_def, BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat]
  omega

private def findPrevAt (atIdx : BitVec 32) :
    List (BitVec 32 × BitVec 256) → ℕ → Option (ℕ × BitVec 256)
  | [], _ => none
  | (idx, kval) :: rest, off =>
    if idx == atIdx then some (off, kval) else findPrevAt atIdx rest (off + 1)

private theorem foldr_findPrev_aux (atIdx : BitVec 32) :
    ∀ (ys : List (BitVec 32 × BitVec 256)) (off : ℕ),
      ys.foldr (fun y (p : ℕ × Option (ℕ × BitVec 256)) =>
        (p.1 - 1, if y.1 == atIdx then some (p.1 - 1, y.2) else p.2))
        (off + ys.length, none) =
        (off, findPrevAt atIdx ys off)
  | [], off => by simp [findPrevAt]
  | (idx, kval) :: rest, off => by
    have hlen : off + ((idx, kval) :: rest).length = (off + 1) + rest.length := by
      simp only [List.length_cons]; omega
    simp only [List.foldr_cons, hlen, foldr_findPrev_aux atIdx rest (off + 1),
      Nat.add_sub_cancel, findPrevAt]

private theorem getLoop_encodePrevEntries (es : List (BitVec 32 × BitVec 256))
    (atIdx : BitVec 32) (params : ChainParamsPB) :
    ∀ (rem k : ℕ),
      es.length - k = rem →
      KeyHistory.getLoop { data := encodePrevEntries es } atIdx (toBEBytes 4 atIdx) params (36 * k) =
        (match findPrevAt atIdx (es.drop k) k with
         | some (j, kval) =>
           .ok (({ data := encodePrevEntries es } : KeyHistory).remove (36 * j) params,
             keyToBytes32 kval)
         | none => .error (.err (.keyAlreadyRequested atIdx))) ∧
      ∀ p ∈ findPrevAt atIdx (es.drop k) k, p.1 < es.length
  | 0, k, hrem => by
    have hnlt : ¬ (36 * k < (encodePrevEntries es).length) := by
      rw [length_encodePrevEntries]; omega
    have hdrop : es.drop k = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨?_, ?_⟩
    · rw [KeyHistory.getLoop, dite_eq_right hnlt, hdrop, findPrevAt]
    · intro p hp
      rw [hdrop, findPrevAt] at hp
      cases hp
  | rem + 1, k, hrem => by
    have hk : k < es.length := by omega
    have hk_bytes : 36 * k < (encodePrevEntries es).length := by
      rw [length_encodePrevEntries]; omega
    have hdrop_cons : es.drop k = es[k] :: es.drop (k + 1) := List.drop_eq_getElem_cons hk
    have htag_beq : (toBEBytes 4 es[k].1 == toBEBytes 4 atIdx) = (es[k].1 == atIdx) := by
      by_cases heq : es[k].1 = atIdx
      · subst heq; simp
      · have hne_b : toBEBytes 4 es[k].1 ≠ toBEBytes 4 atIdx :=
          fun hb => heq (toBEBytes4_injective hb)
        simp [heq, hne_b]
    rw [KeyHistory.getLoop, dite_eq_left hk_bytes, encodePrevEntries_tag es k hk, htag_beq]
    rw [hdrop_cons]
    rcases hesk : es[k] with ⟨idxK, mkK⟩
    dsimp only [findPrevAt]
    by_cases hmatch : (idxK == atIdx) = true
    · simp only [hmatch, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · have hkey := encodePrevEntries_key es k hk
        rw [hesk] at hkey
        rw [hkey]
      · intro p hp
        simp only [Option.mem_def] at hp
        injection hp with hp'
        subst hp'
        exact hk
    · simp only [hmatch, Bool.false_eq_true, ↓reduceIte]
      have hstep : 36 * k + KeyHistory.KEY_SIZE = 36 * (k + 1) := by
        simp only [KeyHistory.KEY_SIZE]; omega
      rw [hstep]
      exact getLoop_encodePrevEntries es atIdx params rem (k + 1) (by omega)

def spqrPrevGetFuelExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (cap : ℕ)
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (tail : Expr (e2eOps ℓ P C K decT encT) Γ (B 35))
    (atIdx curCtr maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod (.list spqrPrevEntryT) BV256)) :=
  .letE (.pair (.pair entries tail) (.pair atIdx (.pair curCtr maxOoo)))
    (.ite (.not (e2ePureOp (.bytesEq 35 35)
        (.pair (.snd (.fst .v0)) (e2ePureOp (.bytesLit 35 []) .unit))))
      .none
      (.ite (e2ePureOp .u32Lt
          (.pair (e2ePureOp .u32Sub
            (.pair (e2ePureOp (.u32Lit 0xffffffff#32) .unit) (.snd (.snd (.snd .v0)))))
            (.fst (.snd .v0))))
        .none
        (.ite (e2ePureOp .u32Lt
            (.pair (e2ePureOp .u32Add (.pair (.fst (.snd .v0)) (.snd (.snd (.snd .v0)))))
              (.fst (.snd (.snd .v0)))))
          .none
          (.letE (.snd (.foldrB cap (.fst (.fst .v0))
              (.pair (.len (.take (.nat cap) (.fst (.fst .v0)))) .none)
              (.letE (.sub (.fst .v1) (.nat 1))
                (.pair .v0
                  (.ite (e2ePureOp .u32Eq (.pair (.fst .v1) (.fst (.snd .v3))))
                    (.some (.pair .v0 (.snd .v1)))
                    (.snd .v2))))))
            (.caseOpt .v0
              .none
              (.letE (.sub (.len (.fst (.fst .v2))) (.nat 1))
                (.caseOpt (listGetExpr cap .v0 (.fst (.fst .v3)))
                  .none
                  (.some (.pair
                    (.take .v1 (listSetExpr cap (.fst .v2) .v0 (.fst (.fst .v4))))
                    (.snd .v2))))))))))

/-- Implements `KeyHistory.get` on up to `2201` `(index, key)` entries plus `tail`. -/
def spqrPrevGetExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (tail : Expr (e2eOps ℓ P C K decT encT) Γ (B 35))
    (atIdx curCtr maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod (.list spqrPrevEntryT) BV256)) :=
  spqrPrevGetFuelExpr 2201 entries tail atIdx curCtr maxOoo

private theorem eval_spqrPrevGetFuelExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (cap : ℕ)
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (tail : Expr (e2eOps ℓ P C K decT encT) Γ (B 35))
    (atIdx curCtr maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (ρ : Env Γ) (params : ChainParamsPB)
    (hlen : (entries.eval ρ).length ≤ cap)
    (htail : tail.eval ρ = [])
    (hooo : maxOoo.eval ρ = params.maxOooKeysOrDefault) :
    match ({ data := encodePrevEntries (entries.eval ρ) } : KeyHistory).get
        (atIdx.eval ρ) (curCtr.eval ρ) params with
    | .error _ => (spqrPrevGetFuelExpr cap entries tail atIdx curCtr maxOoo).eval ρ = none
    | .ok (prev', out) =>
      ∃ entries' : List (BitVec 32 × BitVec 256),
        prev' = { data := encodePrevEntries entries' } ∧
        entries'.length < (entries.eval ρ).length ∧
        out.length = 32 ∧
        (spqrPrevGetFuelExpr cap entries tail atIdx curCtr maxOoo).eval ρ =
          some (entries', bytesToKey32 out) := by
  generalize hEs : entries.eval ρ = es at hlen ⊢
  generalize hAt : atIdx.eval ρ = atVal
  generalize hCtr : curCtr.eval ρ = ctrVal
  have hal : (({ data := encodePrevEntries es } : KeyHistory).data.length % KeyHistory.KEY_SIZE != 0) =
      false := by
    simp [KeyHistory.KEY_SIZE, length_encodePrevEntries]
  unfold KeyHistory.get
  rw [hal]
  dsimp only [Bool.false_eq_true, ↓reduceIte]
  simp only [spqrPrevGetFuelExpr, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Env.get, hEs, htail, hAt, hCtr, hooo,
    beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    List.take_of_length_le hlen]
  have hovf_iff := u32_add_ovf_iff atVal params.maxOooKeysOrDefault
  by_cases hovf : atVal.toNat + params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
  · have hovf_bv : 0xffffffff#32 - params.maxOooKeysOrDefault < atVal := hovf_iff.mpr hovf
    rw [ite_eq_left hovf]
    simp [hovf_bv]
  · have hovf_bv : ¬ (0xffffffff#32 - params.maxOooKeysOrDefault < atVal) :=
      fun h => hovf (hovf_iff.mp h)
    rw [ite_eq_right hovf]
    simp only [hovf_bv, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases htrim : atVal + params.maxOooKeysOrDefault < ctrVal
    · rw [ite_eq_left htrim]
      simp [htrim]
    · rw [ite_eq_right htrim]
      simp only [htrim, decide_false, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hgloop, hbound⟩ := getLoop_encodePrevEntries es atVal params es.length 0 (Nat.sub_zero _)
      simp only [Nat.mul_zero, List.drop_zero] at hgloop hbound
      have hfold := foldr_findPrev_aux atVal es 0
      simp only [Nat.zero_add] at hfold
      rw [hgloop, hfold]
      dsimp only
      cases hfind : findPrevAt atVal es 0 with
      | none => rfl
      | some p =>
        rcases p with ⟨j, mkBv⟩
        have hj : j < es.length := hbound (j, mkBv) hfind
        have hlast_lt : es.length - 1 < es.length := by omega
        dsimp only
        let argsVal :
            (List (BitVec 32 × BitVec 256) × Bytes) × (BitVec 32 × (BitVec 32 × BitVec 32)) :=
          ((es, []), (atVal, (ctrVal, params.maxOooKeysOrDefault)))
        let ρGet : Env (.nat :: .prod .nat BV256 :: .opt (.prod .nat BV256) ::
            .prod (.prod (.list spqrPrevEntryT) (B 35))
              (.prod U32 (.prod U32 U32)) :: Γ) :=
          Env.cons (t := .nat) (es.length - 1)
            (Env.cons (t := .prod .nat BV256) (j, mkBv)
              (Env.cons (t := .opt (.prod .nat BV256)) (some (j, mkBv))
                (Env.cons (t := .prod (.prod (.list spqrPrevEntryT) (B 35))
                    (.prod U32 (.prod U32 U32))) argsVal ρ)))
        have hget_last :
            (listGetExpr (O := e2eOps ℓ P C K decT encT) cap
              (Expr.var Var.zero)
              (.fst (.fst (Expr.var Var.zero.succ.succ.succ)))).eval ρGet =
              some es[es.length - 1] := by
          rw [eval_listGetExpr (O := e2eOps ℓ P C K decT encT) cap _ _ ρGet
            (by dsimp only [ρGet, argsVal]; simp only [Expr.eval, Env.get]; exact hlen)]
          dsimp only [ρGet, argsVal]
          simp [Expr.eval, Env.get, hlast_lt]
        dsimp only [ρGet, argsVal] at hget_last
        rw [hget_last]
        dsimp only
        let ρSet : Env (spqrPrevEntryT :: .nat :: .prod .nat BV256 ::
            .opt (.prod .nat BV256) ::
            .prod (.prod (.list spqrPrevEntryT) (B 35))
              (.prod U32 (.prod U32 U32)) :: Γ) :=
          Env.cons (t := spqrPrevEntryT) es[es.length - 1] ρGet
        have hset_eval :
            (listSetExpr (O := e2eOps ℓ P C K decT encT) cap
              (.fst (Expr.var Var.zero.succ.succ))
              (Expr.var Var.zero)
              (.fst (.fst (Expr.var Var.zero.succ.succ.succ.succ)))).eval ρSet =
              es.set j es[es.length - 1] := by
          rw [eval_listSetExpr (O := e2eOps ℓ P C K decT encT) cap _ _ _ ρSet
            (by dsimp only [ρSet, ρGet, argsVal]; simp only [Expr.eval, Env.get]; exact hlen)]
          dsimp only [ρSet, ρGet, argsVal]
          simp [Expr.eval, Env.get]
        dsimp only [ρSet, ρGet, argsVal] at hset_eval
        rw [hset_eval]
        refine ⟨(es.set j es[es.length - 1]).take (es.length - 1),
          remove_encodePrevEntries es j hj params, ?_, length_keyToBytes32 mkBv, ?_⟩
        · simp only [List.length_take, List.length_set]
          omega
        · rw [bytesToKey32_keyToBytes32]

theorem eval_spqrPrevGetExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (tail : Expr (e2eOps ℓ P C K decT encT) Γ (B 35))
    (atIdx curCtr maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (ρ : Env Γ) (params : ChainParamsPB)
    (hlen : (entries.eval ρ).length ≤ 2201)
    (htail : tail.eval ρ = [])
    (hooo : maxOoo.eval ρ = params.maxOooKeysOrDefault) :
    match ({ data := encodePrevEntries (entries.eval ρ) } : KeyHistory).get
        (atIdx.eval ρ) (curCtr.eval ρ) params with
    | .error _ => (spqrPrevGetExpr entries tail atIdx curCtr maxOoo).eval ρ = none
    | .ok (prev', out) =>
      ∃ entries' : List (BitVec 32 × BitVec 256),
        prev' = { data := encodePrevEntries entries' } ∧
        entries'.length < (entries.eval ρ).length ∧
        out.length = 32 ∧
        (spqrPrevGetExpr entries tail atIdx curCtr maxOoo).eval ρ =
          some (entries', bytesToKey32 out) :=
  eval_spqrPrevGetFuelExpr 2201 entries tail atIdx curCtr maxOoo ρ params hlen htail hooo

/-! ## `KeyHistory.gc` -/

private def gcStepPure (horizon : BitVec 32)
    (s : ℕ × (ℕ × (ℕ → BitVec 32 × BitVec 256))) :
    ℕ × (ℕ × (ℕ → BitVec 32 × BitVec 256)) :=
  let (i, (curLen, tbl)) := s
  if i < curLen then
    if (tbl i).1 < horizon then
      (i, (curLen - 1, tblSet tbl i (tbl (curLen - 1))))
    else
      (i + 1, (curLen, tbl))
  else
    s

private theorem sliceTbl_tblSet_swap {α : Type} (tbl : ℕ → α) (curLen i : ℕ) (hi : i < curLen) :
    sliceTbl (tblSet tbl i (tbl (curLen - 1))) 0 (curLen - 1) =
      ((sliceTbl tbl 0 curLen).set i
        ((sliceTbl tbl 0 curLen)[curLen - 1]'(by rw [sliceTbl_length]; omega))).take (curLen - 1) := by
  apply List.ext_getElem
  · simp [sliceTbl_length]
  · intro j hj1 hj2
    rw [sliceTbl_length] at hj1
    rw [sliceTbl_getElem, List.getElem_take, List.getElem_set]
    simp only [Nat.zero_add, tblSet]
    by_cases hji : j = i
    · cases hji
      simp [sliceTbl_getElem]
    · have hne : i ≠ j := fun h => hji h.symm
      simp [hji, hne, sliceTbl_getElem]

private theorem foldr_gcSteps_eq {β : Type} (horizon : BitVec 32) :
    ∀ (ys : List β) (s : ℕ × (ℕ × (ℕ → BitVec 32 × BitVec 256))),
      ys.foldr (fun _ acc => gcStepPure horizon acc) s =
        (gcStepPure horizon)^[ys.length] s
  | [], _ => rfl
  | _ :: rest, s => by
    simp only [List.foldr_cons, List.length_cons, foldr_gcSteps_eq horizon rest s,
      Function.iterate_succ_apply']

private theorem gcLoop_iterate_gcStepPure (horizon : BitVec 32) (params : ChainParamsPB) :
    ∀ (steps : ℕ) (s : ℕ × (ℕ × (ℕ → BitVec 32 × BitVec 256))),
      s.2.1 - s.1 ≤ steps →
      ((gcStepPure horizon)^[steps] s).2.1 ≤ s.2.1 ∧
      KeyHistory.gcLoop { data := encodePrevEntries (sliceTbl s.2.2 0 s.2.1) }
        (toBEBytes 4 horizon) params (36 * s.1) =
        .ok { data := encodePrevEntries
                (sliceTbl ((gcStepPure horizon)^[steps] s).2.2 0
                  ((gcStepPure horizon)^[steps] s).2.1) }
  | 0, ⟨i, curLen, tbl⟩, hrem => by
    dsimp only at hrem ⊢
    have hnlt : ¬ (36 * i < (encodePrevEntries (sliceTbl tbl 0 curLen)).length) := by
      rw [length_encodePrevEntries, sliceTbl_length]
      omega
    refine ⟨le_refl _, ?_⟩
    rw [KeyHistory.gcLoop, dite_eq_right hnlt]
    rfl
  | steps + 1, ⟨i, curLen, tbl⟩, hrem => by
    dsimp only at hrem ⊢
    by_cases hlt : i < curLen
    · have hlt_bytes : 36 * i < (encodePrevEntries (sliceTbl tbl 0 curLen)).length := by
        rw [length_encodePrevEntries, sliceTbl_length]
        omega
      have hnbounds : ¬ ((encodePrevEntries (sliceTbl tbl 0 curLen)).length < 36 * i + 4) := by
        rw [length_encodePrevEntries, sliceTbl_length]
        omega
      have hslice_len : i < (sliceTbl tbl 0 curLen).length := by
        rw [sliceTbl_length]; exact hlt
      have htag : ((encodePrevEntries (sliceTbl tbl 0 curLen)).drop (36 * i)).take 4 =
          toBEBytes 4 (tbl i).1 := by
        rw [encodePrevEntries_tag _ i hslice_len, sliceTbl_getElem]
        simp
      have hblt : bytesLt (toBEBytes 4 (tbl i).1) (toBEBytes 4 horizon) =
          decide ((tbl i).1 < horizon) := by
        rw [bytesLt_toBEBytes4]
        exact decide_eq_decide.mpr BitVec.lt_def.symm
      rw [Function.iterate_succ_apply, KeyHistory.gcLoop, dite_eq_left hlt_bytes,
        ite_eq_right hnbounds]
      dsimp only [gcStepPure]
      simp only [hlt, ↓reduceIte, htag, hblt]
      by_cases hkey_lt : (tbl i).1 < horizon
      · simp only [hkey_lt, decide_true, ↓reduceIte]
        have hrem_eq := remove_encodePrevEntries (sliceTbl tbl 0 curLen) i hslice_len params
        simp only [sliceTbl_length] at hrem_eq
        rw [hrem_eq, ← sliceTbl_tblSet_swap tbl curLen i hlt]
        obtain ⟨ih_le, ih_eq⟩ := gcLoop_iterate_gcStepPure horizon params steps
          (i, (curLen - 1, tblSet tbl i (tbl (curLen - 1)))) (by dsimp only; omega)
        exact ⟨Nat.le_trans ih_le (Nat.sub_le _ _), ih_eq⟩
      · simp only [hkey_lt, decide_false, Bool.false_eq_true, ↓reduceIte]
        have hstep : 36 * i + KeyHistory.KEY_SIZE = 36 * (i + 1) := by
          simp only [KeyHistory.KEY_SIZE]; omega
        rw [hstep]
        exact gcLoop_iterate_gcStepPure horizon params steps
          (i + 1, (curLen, tbl)) (by dsimp only; omega)
    · have hfix : gcStepPure horizon (i, (curLen, tbl)) = (i, (curLen, tbl)) := by
        simp [gcStepPure, hlt]
      rw [Function.iterate_succ_apply, hfix]
      exact gcLoop_iterate_gcStepPure horizon params steps (i, (curLen, tbl)) (by dsimp only; omega)

def spqrPrevGcFuelExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (cap : ℕ)
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (curKey maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.list spqrPrevEntryT)) :=
  .letE (.pair (.take (.nat cap) entries) (.pair curKey (.pair maxOoo trimSize)))
    (.letE (.len (.fst .v0))
      (.ite (.lt .v0 (.snd (.snd (.snd .v1))))
        (.some (.fst .v1))
        (.ite (e2ePureOp .u32Lt (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))))
          .none
          (.letE (e2ePureOp .u32Sub (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))))
            (.letE (.snd (.foldrB cap (.fst .v2)
                (.pair .v1 (.tconst (.pair (e2ePureOp (.u32Lit 0#32) .unit)
                  (e2ePureOp (.bv256Lit 0#256) .unit))))
                (.letE (.sub (.fst .v1) (.nat 1))
                  (.pair .v0 (.tset (.snd .v2) .v0 .v1)))))
              (.letE (.foldrB cap (.fst .v3)
                  (.pair (.nat 0) (.pair .v2 .v0))
                  (.ite (.lt (.fst .v1) (.fst (.snd .v1)))
                    (.ite (e2ePureOp .u32Lt
                        (.pair (.fst (.tget (.snd (.snd .v1)) (.fst .v1))) .v3))
                      (.letE (.sub (.fst (.snd .v1)) (.nat 1))
                        (.pair (.fst .v2)
                          (.pair .v0
                            (.tset (.snd (.snd .v2)) (.fst .v2)
                              (.tget (.snd (.snd .v2)) .v0)))))
                      (.pair (.add (.fst .v1) (.nat 1)) (.snd .v1)))
                    .v1))
                (.some (.snd (.foldrB cap (.fst .v4)
                  (.pair .v3 .nil)
                  (.letE (.sub (.fst .v1) (.nat 1))
                    (.pair .v0
                      (.ite (.lt .v0 (.fst (.snd .v3)))
                        (.cons (.tget (.snd (.snd .v3)) .v0) (.snd .v2))
                        (.snd .v2)))))))))))))

/-- Implements `KeyHistory.gc` on up to `4201` `(index, key)` entries. -/
def spqrPrevGcExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (curKey maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.list spqrPrevEntryT)) :=
  spqrPrevGcFuelExpr 4201 entries curKey maxOoo trimSize

private theorem eval_spqrPrevGcFuelExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (cap : ℕ)
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (curKey maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (ρ : Env Γ) (params : ChainParamsPB)
    (hlen : (entries.eval ρ).length ≤ cap)
    (hooo : maxOoo.eval ρ = params.maxOooKeysOrDefault)
    (htrim : trimSize.eval ρ = params.trimSize) :
    match ({ data := encodePrevEntries (entries.eval ρ) } : KeyHistory).gc
        (curKey.eval ρ) params with
    | .error _ => (spqrPrevGcFuelExpr cap entries curKey maxOoo trimSize).eval ρ = none
    | .ok prevGc =>
      ∃ entriesGc : List (BitVec 32 × BitVec 256),
        prevGc = { data := encodePrevEntries entriesGc } ∧
        entriesGc.length ≤ (entries.eval ρ).length ∧
        (spqrPrevGcFuelExpr cap entries curKey maxOoo trimSize).eval ρ = some entriesGc := by
  generalize hEs : entries.eval ρ = es at hlen ⊢
  generalize hCur : curKey.eval ρ = curVal
  unfold KeyHistory.gc
  simp only [KeyHistory.KEY_SIZE, length_encodePrevEntries, spqrPrevGcFuelExpr, Expr.eval,
    eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Env.get,
    hEs, hCur, hooo, htrim, List.take_of_length_le hlen]
  by_cases hlt_trim : es.length < params.trimSize
  · have hnge : ¬ (36 * es.length ≥ params.trimSize * (4 + 32)) := by omega
    simp only [hnge, hlt_trim, decide_true, ↓reduceIte]
    exact ⟨es, rfl, le_refl _, rfl⟩
  · have hge : 36 * es.length ≥ params.trimSize * (4 + 32) := by omega
    simp only [hge, hlt_trim, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hlt_cur : curVal < params.maxOooKeysOrDefault
    · simp [hlt_cur]
    · simp only [hlt_cur, decide_false, Bool.false_eq_true, ↓reduceIte]
      let horizon := curVal - params.maxOooKeysOrDefault
      let d0 : BitVec 32 × BitVec 256 := (0#32, 0#256)
      let tbl0 := (es.foldr (fun x acc => (acc.1 - 1, tblSet acc.2 (acc.1 - 1) x))
        (es.length, fun _ => d0)).2
      have hload := (foldr_loadTbl_aux (fun _ => d0) es 0).2
      simp only [Nat.zero_add, Nat.zero_le, true_and, Nat.sub_zero] at hload
      have hslice0 : sliceTbl tbl0 0 es.length = es := by
        apply List.ext_getElem
        · rw [sliceTbl_length]
        · intro j hj1 hj2
          rw [sliceTbl_getElem]
          simp only [Nat.zero_add]
          simpa [tbl0, hj2] using hload j
      have hstep_congr :
          es.foldr
            (fun _ acc =>
              if decide (acc.1 < acc.2.1) = true then
                if decide ((acc.2.2 acc.1).1 < horizon) = true then
                  (acc.1, (acc.2.1 - 1, tblSet acc.2.2 acc.1 (acc.2.2 (acc.2.1 - 1))))
                else (acc.1 + 1, acc.2)
              else acc)
            (0, (es.length, tbl0)) =
          (gcStepPure horizon)^[es.length] (0, (es.length, tbl0)) := by
        rw [← foldr_gcSteps_eq horizon es (0, (es.length, tbl0))]
        congr 1
        funext _ s
        rcases s with ⟨i, curLen, tbl⟩
        dsimp only [gcStepPure]
        by_cases h1 : i < curLen
        · by_cases h2 : (tbl i).1 < horizon <;> simp [h1, h2]
        · simp [h1]
      obtain ⟨hfin_le, hgc_ok⟩ := gcLoop_iterate_gcStepPure horizon params es.length
        (0, (es.length, tbl0)) (by dsimp only; omega)
      dsimp only at hfin_le hgc_ok
      rw [Nat.mul_zero, hslice0] at hgc_ok
      rw [hgc_ok]
      let sFin := (gcStepPure horizon)^[es.length] (0, (es.length, tbl0))
      have hread_congr :
          es.foldr
            (fun _ acc =>
              (acc.1 - 1,
                if decide (acc.1 - 1 < sFin.2.1) = true then sFin.2.2 (acc.1 - 1) :: acc.2
                else acc.2))
            (es.length, []) =
          (0, sliceTbl sFin.2.2 0 sFin.2.1) := by
        have hr := foldr_sliceTbl_aux sFin.2.2 sFin.2.1 es 0 (by simpa using hfin_le)
        simp only [Nat.zero_add, Nat.sub_zero] at hr
        refine Eq.trans ?_ hr
        congr 1
        funext _ p
        by_cases hc : p.1 - 1 < sFin.2.1 <;> simp [hc]
      refine ⟨sliceTbl sFin.2.2 0 sFin.2.1, rfl, ?_, ?_⟩
      · rw [sliceTbl_length]
        exact hfin_le
      · change some (es.foldr _ (es.length, [])).2 = some (sliceTbl sFin.2.2 0 sFin.2.1)
        have htblSet : ∀ {α : Type} (m : ℕ → α) (k : ℕ) (v : α),
            tblSet m k v = (fun j => if j = k then v else m j) := fun _ _ _ => rfl
        dsimp only [tbl0, sFin, horizon, d0] at hstep_congr hread_congr ⊢
        simp only [htblSet] at hstep_congr hread_congr ⊢
        rw [hstep_congr]
        exact congrArg (fun p => some p.2) hread_congr

theorem eval_spqrPrevGcExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (curKey maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (ρ : Env Γ) (params : ChainParamsPB)
    (hlen : (entries.eval ρ).length ≤ 4201)
    (hooo : maxOoo.eval ρ = params.maxOooKeysOrDefault)
    (htrim : trimSize.eval ρ = params.trimSize) :
    match ({ data := encodePrevEntries (entries.eval ρ) } : KeyHistory).gc
        (curKey.eval ρ) params with
    | .error _ => (spqrPrevGcExpr entries curKey maxOoo trimSize).eval ρ = none
    | .ok prevGc =>
      ∃ entriesGc : List (BitVec 32 × BitVec 256),
        prevGc = { data := encodePrevEntries entriesGc } ∧
        entriesGc.length ≤ (entries.eval ρ).length ∧
        (spqrPrevGcExpr entries curKey maxOoo trimSize).eval ρ = some entriesGc :=
  eval_spqrPrevGcFuelExpr 4201 entries curKey maxOoo trimSize ρ params hlen hooo htrim

/-! ## `keyAdvanceLoop` and `Chain.recvKey` -/

private theorem keyAdvanceLoop_err_of_last_ovf (hkdf : CryptoVerification.LibsignalSpqrV1.HkdfFn)
    (atIdx : BitVec 32) (params : ChainParamsPB)
    (hovf : (atIdx.toNat - 1) + params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) :
    ∀ (rem : ℕ) (s : ChainEpochDirection),
      atIdx.toNat - s.ctr.toNat ≤ rem →
      s.ctr.toNat + 1 < atIdx.toNat →
      ∀ sOut, s.keyAdvanceLoop hkdf atIdx params ≠ .ok sOut
  | 0, s, hrem, hlt, _, _ => by omega
  | rem + 1, s, hrem, hlt, sOut, hok => by
    rw [ChainEpochDirection.keyAdvanceLoop, dite_eq_left hlt] at hok
    split at hok
    · cases hok
    · rename_i next' ctr' k hnk
      have hctr' : ctr'.toNat = s.ctr.toNat + 1 :=
        ChainEpochDirection.nextKeyInternal_ctr hkdf s.next next' s.ctr ctr' k hnk
      dsimp only at hok
      by_cases hc : ctr'.toNat + params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
      · rw [ite_eq_left hc] at hok; cases hok
      · rw [ite_eq_right hc] at hok
        have hlt' : ctr'.toNat + 1 < atIdx.toNat := by omega
        exact keyAdvanceLoop_err_of_last_ovf hkdf atIdx params hovf rem _
          (by dsimp only; omega) (by dsimp only; exact hlt') sOut hok

private theorem nextKeyInternal_spqrHkdf_ok (F : ShaCompress) (next : Bytes) (ctr : BitVec 32)
    (hnext : next.length = 32) (hctr : ctr.toNat < 4294967295) :
    ∃ next' mkBytes,
      ChainEpochDirection.nextKeyInternal (spqrHkdfWith F) next ctr =
        .ok (next', ctr + 1#32, (ctr + 1#32, mkBytes)) ∧
      next'.length = 32 ∧
      mkBytes.length = 32 ∧
      (ctr + 1#32).toNat = ctr.toNat + 1 := by
  have hne32 : (next.length != 32) = false := by simp [hnext]
  have hne_max : (ctr == 0xffffffff#32) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    rw [heq] at hctr
    simp at hctr
  unfold ChainEpochDirection.nextKeyInternal
  rw [hne32, hne_max]
  dsimp only [Bool.false_eq_true, ↓reduceIte]
  let genr8r := spqrHkdfWith F (List.replicate 32 0#8) next
    (toBEBytes 4 (ctr + 1#32) ++ CryptoVerification.LibsignalSpqrV1.chainNextInfo) 64
  have hgen64 : genr8r.length = 64 := by simp [genr8r, spqrHkdfWith]
  refine ⟨genr8r.take 32, (genr8r.drop 32).take 32, rfl, ?_, ?_, ?_⟩
  · simp [hgen64]
  · simp [hgen64]
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

abbrev spqrCatchAccT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod .nat (.prod (.list spqrPrevEntryT) (.prod (B 32) U32))

def spqrKeyAdvanceStep {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))} :
    Comp (e2eOps ℓ P C K decT encT) I
      (spqrCatchAccT ℓ :: .prod .nat .nat :: Γ) (spqrCatchAccT ℓ) :=
  .ite (.lt (.nat 0) (.fst .v0))
    (.bind (spqrChainNextKeyC I (.snd (.snd .v0)))
      (.caseOpt (.snd .v0)
        (.ret .v1)
        (.ret
          (.letE (.sub (.fst .v2) (.nat 1))
            (.pair .v0
              (.pair
                (.ite (.lt .v0 (.snd .v4))
                  (.cons (.snd .v1) (.fst (.snd .v3)))
                  (.fst (.snd .v3)))
                (.pair (.fst .v1) (.fst (.snd .v1)))))))))
    (.ret .v0)

def spqrKeyAdvanceFuelComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (fuel revCap outCap : ℕ)
    (ctr0 : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (next0 : Expr (e2eOps ℓ P C K decT encT) Γ (B 32))
    (entries0 : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (atIdx maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    Comp (e2eOps ℓ P C K decT encT) I Γ
      (.opt (.prod U32 (.prod (B 32) (.list spqrPrevEntryT)))) :=
  .bind (.ret (.pair (.pair ctr0 next0) (.pair entries0 (.pair atIdx maxOoo))))
    (.bind (.ret
        (.pair
          (.sub
            (.sub (e2ePureOp .u32ToNat (.fst (.snd (.snd .v0))))
                  (e2ePureOp .u32ToNat (.fst (.fst .v0))))
            (.nat 1))
          (e2ePureOp .u32ToNat (.snd (.snd (.snd .v0))))))
      (.ite (.lt (.nat 0) (.fst .v0))
        (.ite (.and
            (.eqN (e2ePureOp (.bytesLen 32) (.snd (.fst .v1))) (.nat 32))
            (.not (e2ePureOp .u32Lt
              (.pair
                (e2ePureOp .u32Sub
                  (.pair (e2ePureOp (.u32Lit 0xffffffff#32) .unit) (.snd (.snd (.snd .v1)))))
                (e2ePureOp .u32Sub
                  (.pair (.fst (.snd (.snd .v1))) (e2ePureOp (.u32Lit 1#32) .unit)))))))
          (.bind
            (.iter fuel
              (.pair (.fst .v0) (.pair .nil (.pair (.snd (.fst .v1)) (.fst (.fst .v1)))))
              (spqrKeyAdvanceStep I))
            (.ret (.some
              (.pair (.snd (.snd (.snd .v0)))
                (.pair (.fst (.snd (.snd .v0)))
                  (.appendL outCap (.fst (.snd .v2))
                    (spqrListRevExpr revCap
                      (.pair (e2ePureOp (.u32Lit 0#32) .unit)
                        (e2ePureOp (.bv256Lit 0#256) .unit))
                      (.fst (.snd .v0)))))))))
          (.ret .none))
        (.ret (.some (.pair (.fst (.fst .v1)) (.pair (.snd (.fst .v1)) (.fst (.snd .v1))))))))

/-- Simulates `ChainEpochDirection.keyAdvanceLoop` via `Comp.iter 25000`. -/
def spqrKeyAdvanceComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (ctr0 : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (next0 : Expr (e2eOps ℓ P C K decT encT) Γ (B 32))
    (entries0 : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (atIdx maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    Comp (e2eOps ℓ P C K decT encT) I Γ
      (.opt (.prod U32 (.prod (B 32) (.list spqrPrevEntryT)))) :=
  spqrKeyAdvanceFuelComp I 25000 2000 4201 ctr0 next0 entries0 atIdx maxOoo

private theorem iterM_keyAdvance_eq {ℓ : ℕ} {ι : Type} {T : OracleSpec ι}
    (F : ShaCompress) (atIdx : BitVec 32) (params : ChainParamsPB)
    (hovf : (atIdx.toNat - 1) + params.maxOooKeysOrDefault.toNat < 2 ^ 32) :
    let maxOooNat := params.maxOooKeysOrDefault.toNat
    let stepF :
        ℕ × (List (BitVec 32 × BitVec 256) × (Bytes × BitVec 32)) →
        OracleComp T (ℕ × (List (BitVec 32 × BitVec 256) × (Bytes × BitVec 32))) :=
      fun acc =>
        if decide (0 < acc.1) = true then
          match (spqrChainNextKeyRaw (ℓ := ℓ) F acc.2.2.1 acc.2.2.2).2 with
          | none => pure acc
          | some out =>
            let rem' := acc.1 - 1
            pure (rem',
              (if decide (rem' < maxOooNat) = true then out.2 :: acc.2.1 else acc.2.1,
               (out.1, out.2.1)))
        else pure acc
    ∀ (n rem : ℕ) (rev : List (BitVec 32 × BitVec 256)) (next : Bytes) (ctr : BitVec 32),
      rem ≤ n →
      rem = (atIdx.toNat - 1) - ctr.toNat →
      ctr.toNat < atIdx.toNat →
      next.length = 32 →
      ∃ rev1 next1 ctr1,
        ReductionDsl.iterM stepF n (rem, (rev, (next, ctr))) =
          pure (0, (rev1, (next1, ctr1))) ∧
        rev1.length ≤ rev.length +
          ((atIdx.toNat - 1) - max ctr.toNat (atIdx.toNat - 1 - maxOooNat)) ∧
        next1.length = 32 ∧
        ∀ initBytes : Bytes,
          ChainEpochDirection.keyAdvanceLoop (spqrHkdfWith F)
            { ctr := ctr, next := next, prev := { data := initBytes ++ encodePrevEntries rev.reverse } }
            atIdx params =
          .ok { ctr := ctr1, next := next1,
                prev := { data := initBytes ++ encodePrevEntries rev1.reverse } } := by
  intro maxOooNat stepF n
  induction n with
  | zero =>
    intro rem rev next ctr hrem_le hrem_eq hctr_lt hnext
    have hrem0 : rem = 0 := by omega
    subst hrem0
    have hctr_end : ¬ (ctr.toNat + 1 < atIdx.toNat) := by omega
    have hctr_ne_max : (ctr == 0xffffffff#32) = false := by
      rw [beq_eq_false_iff_ne]
      intro heq
      rw [heq] at hctr_lt
      have := atIdx.isLt
      simp only [BitVec.toNat_ofNat] at hctr_lt
      omega
    refine ⟨rev, next, ctr, rfl, by omega, hnext, fun initBytes => ?_⟩
    rw [ChainEpochDirection.keyAdvanceLoop, dite_eq_right hctr_end]
    simp [hctr_ne_max]
  | succ n ih =>
    intro rem rev next ctr hrem_le hrem_eq hctr_lt hnext
    by_cases hpos : 0 < rem
    · have hlt1 : ctr.toNat + 1 < atIdx.toNat := by omega
      have hctr_max : ctr.toNat < 4294967295 := by
        have := atIdx.isLt
        omega
      obtain ⟨next', mkBytes, hnk, hnext'32, hmk32, hctr'_nat⟩ :=
        nextKeyInternal_spqrHkdf_ok F next ctr hnext hctr_max
      let ctr' := ctr + 1#32
      let rem' := rem - 1
      have hctr'_eq : ctr'.toNat = ctr.toNat + 1 := hctr'_nat
      let rev' :=
        if decide (rem' < maxOooNat) = true then (ctr', bytesToKey32 mkBytes) :: rev else rev
      have hstep :
          stepF (rem, (rev, (next, ctr))) = pure (rem', (rev', (next', ctr'))) := by
        dsimp only [stepF, spqrChainNextKeyRaw]
        simp [hpos, hnk, ctr', rem', rev']
      rw [ReductionDsl.iterM, hstep]
      simp only [pure_bind]
      obtain ⟨rev1, next1, ctr1, ih_iter, ih_len, ih_next, ih_loop⟩ :=
        ih rem' rev' next' ctr' (by dsimp only [rem']; omega)
          (by dsimp only [rem']; omega) (by omega) hnext'32
      refine ⟨rev1, next1, ctr1, ih_iter, ?_, ih_next, fun initBytes => ?_⟩
      · dsimp only [rev', rem'] at ih_len
        rw [hctr'_eq] at ih_len
        by_cases hwin : rem - 1 < maxOooNat
        · simp only [hwin, decide_true, ↓reduceIte, List.length_cons] at ih_len
          omega
        · simp only [hwin, decide_false, Bool.false_eq_true, ↓reduceIte] at ih_len
          omega
      · rw [ChainEpochDirection.keyAdvanceLoop, dite_eq_left hlt1]
        dsimp only
        rw [hnk]
        dsimp only
        change (let maxOoo := params.maxOooKeysOrDefault
          if ctr'.toNat + maxOoo.toNat ≥ 2 ^ 32 then _ else _) = _
        dsimp only
        have hno_ovf : ¬ (ctr'.toNat + params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) := by
          change ¬ (ctr'.toNat + maxOooNat ≥ 2 ^ 32)
          omega
        rw [ite_eq_right hno_ovf]
        have hwin_iff : (rem' < maxOooNat) ↔ (ctr' + params.maxOooKeysOrDefault ≥ atIdx) := by
          simp only [ge_iff_le, BitVec.le_def, BitVec.toNat_add, rem', maxOooNat, hctr'_eq]
          omega
        by_cases hwin : rem' < maxOooNat
        · have hge : ctr' + params.maxOooKeysOrDefault ≥ atIdx := hwin_iff.mp hwin
          have hrev' : rev' = (ctr', bytesToKey32 mkBytes) :: rev := by
            simp [rev', hwin]
          have hadd_data :
              ({ data := initBytes ++ encodePrevEntries rev.reverse } : KeyHistory).add
                (ctr', mkBytes) params =
              { data := initBytes ++ encodePrevEntries rev'.reverse } := by
            simp only [KeyHistory.add, hrev', List.reverse_cons, encodePrevEntries_append,
              encodePrevEntries_cons, encodePrevEntries_nil, List.append_nil, prevEntryBytes,
              keyToBytes32_bytesToKey32 mkBytes hmk32, List.append_assoc]
          rw [ite_eq_left hge, hadd_data]
          exact ih_loop initBytes
        · have hnge : ¬ (ctr' + params.maxOooKeysOrDefault ≥ atIdx) :=
            fun hg => hwin (hwin_iff.mpr hg)
          have hrev' : rev' = rev := by simp [rev', hwin]
          rw [ite_eq_right hnge, ← hrev']
          exact ih_loop initBytes
    · have hstep : stepF (rem, (rev, (next, ctr))) = pure (rem, (rev, (next, ctr))) := by
        dsimp only [stepF]
        simp [hpos]
      rw [ReductionDsl.iterM, hstep]
      simp only [pure_bind]
      exact ih rem rev next ctr (by omega) hrem_eq hctr_lt hnext

private theorem eval_spqrKeyAdvanceFuelComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (fuel revCap outCap : ℕ)
    (ctr0 : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (next0 : Expr (e2eOps ℓ P C K decT encT) Γ (B 32))
    (entries0 : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (atIdx maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (ρ : Env Γ) (params : ChainParamsPB)
    (hctr_lt : (ctr0.eval ρ).toNat < (atIdx.eval ρ).toNat)
    (hjump : (atIdx.eval ρ).toNat - (ctr0.eval ρ).toNat ≤ fuel)
    (hooo_eq : maxOoo.eval ρ = params.maxOooKeysOrDefault)
    (hooo_le : params.maxOooKeysOrDefault.toNat ≤ revCap)
    (hout_cap : (entries0.eval ρ).length + revCap ≤ outCap) :
    match ChainEpochDirection.keyAdvanceLoop (spqrHkdfWith C.F)
        { ctr := ctr0.eval ρ, next := next0.eval ρ,
          prev := { data := encodePrevEntries (entries0.eval ρ) } }
        (atIdx.eval ρ) params with
    | .error _ =>
      (spqrKeyAdvanceFuelComp I fuel revCap outCap ctr0 next0 entries0 atIdx maxOoo).eval ρ =
        pure none
    | .ok s1 =>
      ∃ entries1 : List (BitVec 32 × BitVec 256),
        s1.prev = { data := encodePrevEntries entries1 } ∧
        entries1.length ≤ outCap ∧
        (spqrKeyAdvanceFuelComp I fuel revCap outCap ctr0 next0 entries0 atIdx maxOoo).eval ρ =
          pure (some (s1.ctr, (s1.next, entries1))) := by
  generalize hCtr0 : ctr0.eval ρ = ctrVal at hctr_lt hjump ⊢
  generalize hNext0 : next0.eval ρ = nextVal
  generalize hEs0 : entries0.eval ρ = es0 at hout_cap ⊢
  generalize hAt : atIdx.eval ρ = atVal at hctr_lt hjump ⊢
  simp only [spqrKeyAdvanceFuelComp, Comp.eval, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    Expr.v0, Expr.v1, Expr.v2, Env.get, hCtr0, hNext0, hEs0, hAt, hooo_eq, pure_bind]
  by_cases hpos : 0 < atVal.toNat - ctrVal.toNat - 1
  · have hlt1 : ctrVal.toNat + 1 < atVal.toNat := by omega
    have hat_sub1 : (atVal - 1#32).toNat = atVal.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (show (1#32 : BitVec 32) ≤ atVal by
        simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
      rfl
    simp only [hpos, decide_true, ↓reduceIte]
    by_cases hlen32 : nextVal.length = 32
    · have hovf_iff := u32_add_ovf_iff (atVal - 1#32) params.maxOooKeysOrDefault
      rw [hat_sub1] at hovf_iff
      by_cases hovf : (atVal.toNat - 1) + params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
      · have hovf_bv : 0xffffffff#32 - params.maxOooKeysOrDefault < atVal - 1#32 :=
          hovf_iff.mpr hovf
        simp only [hlen32, hovf_bv, decide_true, Bool.not_true, Bool.and_false,
          Bool.false_eq_true, ↓reduceIte]
        cases hloop : ChainEpochDirection.keyAdvanceLoop (spqrHkdfWith C.F)
            { ctr := ctrVal, next := nextVal, prev := { data := encodePrevEntries es0 } }
            atVal params with
        | error _ => trivial
        | ok sOut =>
          exfalso
          exact keyAdvanceLoop_err_of_last_ovf (spqrHkdfWith C.F) atVal params hovf
            (atVal.toNat - ctrVal.toNat) _ (by dsimp only; exact le_refl _)
            (by dsimp only; exact hlt1) sOut hloop
      · have hovf_bv : ¬ (0xffffffff#32 - params.maxOooKeysOrDefault < atVal - 1#32) :=
          fun h => hovf (hovf_iff.mp h)
        have hovf_lt : (atVal.toNat - 1) + params.maxOooKeysOrDefault.toNat < 2 ^ 32 := by omega
        simp only [hlen32, hovf_bv, decide_true, decide_false, Bool.not_false, Bool.and_self,
          ↓reduceIte]
        obtain ⟨rev1, next1, ctr1, hiter_eq, hrev_len, _, hloop_ok⟩ :=
          iterM_keyAdvance_eq (ℓ := ℓ) (T := T) C.F atVal params hovf_lt
            fuel (atVal.toNat - ctrVal.toNat - 1) [] nextVal ctrVal
            (by omega) (by omega) hctr_lt hlen32
        let argsVal :
            (BitVec 32 × Bytes) × (List (BitVec 32 × BitVec 256) × (BitVec 32 × BitVec 32)) :=
          ((ctrVal, nextVal), (es0, (atVal, params.maxOooKeysOrDefault)))
        let ρIter : Env (.prod .nat .nat ::
            .prod (.prod U32 (B 32)) (.prod (.list spqrPrevEntryT) (.prod U32 U32)) :: Γ) :=
          Env.cons (t := .prod .nat .nat)
            (atVal.toNat - ctrVal.toNat - 1, params.maxOooKeysOrDefault.toNat)
            (Env.cons (t := .prod (.prod U32 (B 32))
                (.prod (.list spqrPrevEntryT) (.prod U32 U32))) argsVal ρ)
        have hstep_congr :
            (fun acc : (spqrCatchAccT ℓ).denote =>
              (spqrKeyAdvanceStep (Pt := Pt) (P := P) (C := C) (K := K)
                (decT := decT) (encT := encT) I).eval
                (Env.cons (t := spqrCatchAccT ℓ) acc ρIter)) =
            (fun acc : ℕ × (List (BitVec 32 × BitVec 256) × (Bytes × BitVec 32)) =>
              if decide (0 < acc.1) = true then
                match (spqrChainNextKeyRaw (ℓ := ℓ) C.F acc.2.2.1 acc.2.2.2).2 with
                | none => pure acc
                | some out =>
                  pure (acc.1 - 1,
                    (if decide (acc.1 - 1 < params.maxOooKeysOrDefault.toNat) = true then
                       out.2 :: acc.2.1
                     else acc.2.1,
                     (out.1, out.2.1)))
              else pure acc) := by
          funext acc
          dsimp only [ρIter, argsVal, spqrKeyAdvanceStep]
          by_cases ha : 0 < acc.1
          · simp only [Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Env.get,
              ha, decide_true, ↓reduceIte, eval_spqrChainNextKeyC,
              spqrChainNextKeyEval_take32_lossless, pure_bind]
            cases (spqrChainNextKeyRaw (ℓ := ℓ) C.F acc.2.2.1 acc.2.2.2).2 <;> rfl
          · simp [Comp.eval, Expr.eval, Expr.v0, Env.get, ha]
        dsimp only [ρIter, argsVal] at hstep_congr
        have hloop_inst := hloop_ok (encodePrevEntries es0)
        simp only [List.reverse_nil, encodePrevEntries_nil, List.append_nil,
          ← encodePrevEntries_append] at hloop_inst
        rw [hloop_inst, hstep_congr, hiter_eq]
        simp only [pure_bind]
        have hrev_cap : rev1.length ≤ revCap := by
          simp only [List.length_nil, Nat.zero_add] at hrev_len
          omega
        let ρRev : Env (spqrCatchAccT ℓ ::
            .prod .nat .nat ::
            .prod (.prod U32 (B 32)) (.prod (.list spqrPrevEntryT) (.prod U32 U32)) :: Γ) :=
          Env.cons (t := spqrCatchAccT ℓ) (0, (rev1, (next1, ctr1))) ρIter
        have hrev_eval :
            (spqrListRevExpr (O := e2eOps ℓ P C K decT encT) revCap
              (.pair (e2ePureOp (.u32Lit 0#32) .unit) (e2ePureOp (.bv256Lit 0#256) .unit))
              (.fst (.snd (Expr.var Var.zero)))).eval ρRev = rev1.reverse := by
          rw [eval_spqrListRevExpr (O := e2eOps ℓ P C K decT encT) revCap _ _ ρRev
            (by dsimp only [ρRev]; simp only [Expr.eval, Env.get]; exact hrev_cap)]
          rfl
        dsimp only [ρRev, ρIter, argsVal] at hrev_eval
        have happ_len : (es0 ++ rev1.reverse).length ≤ outCap := by
          rw [List.length_append, List.length_reverse]
          omega
        refine ⟨es0 ++ rev1.reverse, rfl, happ_len, ?_⟩
        rw [hrev_eval, List.take_of_length_le happ_len]
    · simp only [hlen32, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      have hnk_err : ChainEpochDirection.nextKeyInternal (spqrHkdfWith C.F) nextVal ctrVal =
          .error .nextKeyBadLen := by
        unfold ChainEpochDirection.nextKeyInternal
        simp [bne_iff_ne.mpr hlen32]
      rw [ChainEpochDirection.keyAdvanceLoop, dite_eq_left hlt1]
      dsimp only
      rw [hnk_err]
      trivial
  · simp only [hpos, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hnlt1 : ¬ (ctrVal.toNat + 1 < atVal.toNat) := by omega
    have hne_max : (ctrVal == 0xffffffff#32) = false := by
      rw [beq_eq_false_iff_ne]
      intro heq
      rw [heq] at hctr_lt
      have := atVal.isLt
      simp only [BitVec.toNat_ofNat] at hctr_lt
      omega
    rw [ChainEpochDirection.keyAdvanceLoop, dite_eq_right hnlt1]
    simp only [hne_max, Bool.false_eq_true, ↓reduceIte]
    exact ⟨es0, rfl, by omega, rfl⟩

theorem eval_spqrKeyAdvanceComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (ctr0 : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (next0 : Expr (e2eOps ℓ P C K decT encT) Γ (B 32))
    (entries0 : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (atIdx maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (ρ : Env Γ) (params : ChainParamsPB)
    (hent : (entries0.eval ρ).length ≤ 2201)
    (hctr_lt : (ctr0.eval ρ).toNat < (atIdx.eval ρ).toNat)
    (hjump : (atIdx.eval ρ).toNat - (ctr0.eval ρ).toNat ≤ 25000)
    (hooo_eq : maxOoo.eval ρ = params.maxOooKeysOrDefault)
    (hooo_le : params.maxOooKeysOrDefault.toNat ≤ 2000) :
    match ChainEpochDirection.keyAdvanceLoop (spqrHkdfWith C.F)
        { ctr := ctr0.eval ρ, next := next0.eval ρ,
          prev := { data := encodePrevEntries (entries0.eval ρ) } }
        (atIdx.eval ρ) params with
    | .error _ => (spqrKeyAdvanceComp I ctr0 next0 entries0 atIdx maxOoo).eval ρ = pure none
    | .ok s1 =>
      ∃ entries1 : List (BitVec 32 × BitVec 256),
        s1.prev = { data := encodePrevEntries entries1 } ∧
        entries1.length ≤ 4201 ∧
        (spqrKeyAdvanceComp I ctr0 next0 entries0 atIdx maxOoo).eval ρ =
          pure (some (s1.ctr, (s1.next, entries1))) :=
  eval_spqrKeyAdvanceFuelComp I 25000 2000 4201 ctr0 next0 entries0 atIdx maxOoo ρ params
    hctr_lt hjump hooo_eq hooo_le (by omega)

def spqrDirKeyFwdComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (ctr0 : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (next0 : Expr (e2eOps ℓ P C K decT encT) Γ (B 32))
    (entriesInit : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (atIdx maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.opt (.prod spqrDirT BV256)) :=
  .bind (.ret (.pair (.pair ctr0 next0) (.pair entriesInit (.pair atIdx (.pair maxOoo trimSize)))))
    (.bind
      (spqrKeyAdvanceComp I
        (.fst (.fst .v0))
        (.snd (.fst .v0))
        (.fst (.snd .v0))
        (.fst (.snd (.snd .v0)))
        (.fst (.snd (.snd (.snd .v0)))))
      (.caseOpt .v0
        (.ret .none)
        (.caseOpt
          (spqrPrevGcExpr
            (.snd (.snd .v0))
            (.fst .v0)
            (.fst (.snd (.snd (.snd .v2))))
            (.snd (.snd (.snd (.snd .v2)))))
          (.ret .none)
          (.bind (spqrChainNextKeyC I (.pair (.fst (.snd .v1)) (.fst .v1)))
            (.caseOpt (.snd .v0)
              (.ret .none)
              (.ret (.some (.pair
                (.pair (.fst (.snd .v0))
                  (.pair (.fst .v0)
                    (.pair .v2 (e2ePureOp (.bytesLit 35 []) .unit))))
                (.snd (.snd .v0))))))))))

theorem comp_eval_ret {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))} {a : Ty (e2eSig ℓ)}
    (e : Expr O Γ a) (ρ : Env Γ) :
    (Comp.ret (I := I) e).eval ρ = pure (e.eval ρ) := rfl

theorem comp_eval_bind {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))} {a b : Ty (e2eSig ℓ)}
    (c : Comp O I Γ a) (k : Comp O I (a :: Γ) b) (ρ : Env Γ) :
    (Comp.bind c k).eval ρ = (c.eval ρ) >>= fun x => k.eval (Env.cons x ρ) := rfl

theorem comp_eval_bind_ret {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))} {a b : Ty (e2eSig ℓ)}
    (e : Expr O Γ a) (k : Comp O I (a :: Γ) b) (ρ : Env Γ) :
    (Comp.bind (.ret e) k).eval ρ = k.eval (Env.cons (e.eval ρ) ρ) := by
  simp only [Comp.eval, pure_bind]

theorem comp_eval_bind_pure {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))} {a b : Ty (e2eSig ℓ)}
    (c : Comp O I Γ a) (k : Comp O I (a :: Γ) b) (ρ : Env Γ) (v : a.denote)
    (hc : c.eval ρ = pure v) :
    (Comp.bind c k).eval ρ = k.eval (Env.cons v ρ) := by
  rw [comp_eval_bind, hc, pure_bind]

theorem comp_eval_ite {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))} {a : Ty (e2eSig ℓ)}
    (c : Expr O Γ .bool) (t f : Comp O I Γ a) (ρ : Env Γ) :
    (Comp.ite c t f).eval ρ = if c.eval ρ then t.eval ρ else f.eval ρ := rfl

theorem comp_eval_ite_true {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))} {a : Ty (e2eSig ℓ)}
    (c : Expr O Γ .bool) (t f : Comp O I Γ a) (ρ : Env Γ) (hc : c.eval ρ = true) :
    (Comp.ite c t f).eval ρ = t.eval ρ := by
  simp only [Comp.eval, hc, ↓reduceIte]

theorem comp_eval_ite_false {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))} {a : Ty (e2eSig ℓ)}
    (c : Expr O Γ .bool) (t f : Comp O I Γ a) (ρ : Env Γ) (hc : c.eval ρ = false) :
    (Comp.ite c t f).eval ρ = f.eval ρ := by
  simp only [Comp.eval, hc, Bool.false_eq_true, ↓reduceIte]

theorem comp_eval_caseOpt {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))} {a b : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt a)) (n : Comp O I Γ b) (s : Comp O I (a :: Γ) b) (ρ : Env Γ) :
    (Comp.caseOpt e n s).eval ρ =
      match e.eval ρ with
      | none => n.eval ρ
      | some v => s.eval (Env.cons v ρ) := by
  simp only [Comp.eval]
  cases e.eval ρ <;> rfl

theorem comp_eval_caseOpt_none {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))} {a b : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt a)) (n : Comp O I Γ b) (s : Comp O I (a :: Γ) b) (ρ : Env Γ)
    (he : e.eval ρ = none) :
    (Comp.caseOpt e n s).eval ρ = n.eval ρ := by
  simp only [Comp.eval, he]

theorem comp_eval_caseOpt_some {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))} {a b : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt a)) (n : Comp O I Γ b) (s : Comp O I (a :: Γ) b) (ρ : Env Γ)
    {v : a.denote} (he : e.eval ρ = some v) :
    (Comp.caseOpt e n s).eval ρ = s.eval (Env.cons v ρ) := by
  simp only [Comp.eval, he]

private theorem eval_spqrDirKeyFwdComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (ctr0 : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (next0 : Expr (e2eOps ℓ P C K decT encT) Γ (B 32))
    (entriesInit : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (atIdx maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (ρ : Env Γ) (params : ChainParamsPB)
    (hent : (entriesInit.eval ρ).length ≤ 2201)
    (hctr_lt : (ctr0.eval ρ).toNat < (atIdx.eval ρ).toNat)
    (hjump : (atIdx.eval ρ).toNat - (ctr0.eval ρ).toNat ≤ 25000)
    (hooo : maxOoo.eval ρ = params.maxOooKeysOrDefault)
    (hooo_le : params.maxOooKeysOrDefault.toNat ≤ 2000)
    (htrim : trimSize.eval ρ = params.trimSize) :
    match (do
      let s1 ← ChainEpochDirection.keyAdvanceLoop (spqrHkdfWith C.F)
        { ctr := ctr0.eval ρ, next := next0.eval ρ,
          prev := { data := encodePrevEntries (entriesInit.eval ρ) } }
        (atIdx.eval ρ) params
      let prevGc ← ChainResult.ofPanic (s1.prev.gc s1.ctr params)
      let s2 : ChainEpochDirection := { s1 with prev := prevGc }
      let (next2, ctr2, _, outKey) ←
        ChainResult.ofPanic
          (ChainEpochDirection.nextKeyInternal (spqrHkdfWith C.F) s2.next s2.ctr)
      pure ({ s2 with next := next2, ctr := ctr2 }, outKey)) with
    | .error _ =>
      (spqrDirKeyFwdComp I ctr0 next0 entriesInit atIdx maxOoo trimSize).eval ρ = pure none
    | .ok (d', out) =>
      ∃ entriesOut : List (BitVec 32 × BitVec 256),
        d'.prev = { data := encodePrevEntries entriesOut } ∧
        d'.next.length ≤ 64 ∧
        out.length = 32 ∧
        (spqrDirKeyFwdComp I ctr0 next0 entriesInit atIdx maxOoo trimSize).eval ρ =
          pure (some ((d'.ctr, (d'.next, (entriesOut, []))), bytesToKey32 out)) := by
  generalize hCtr0 : ctr0.eval ρ = ctrVal at hctr_lt hjump ⊢
  generalize hNext0 : next0.eval ρ = nextVal
  generalize hEsInit : entriesInit.eval ρ = esInit at hent ⊢
  generalize hAt : atIdx.eval ρ = idxVal at hctr_lt hjump ⊢
  let argsT : Ty (e2eSig ℓ) :=
    .prod (.prod U32 (B 32)) (.prod (.list spqrPrevEntryT) (.prod U32 (.prod U32 .nat)))
  let argsVal : argsT.denote :=
    ((ctrVal, nextVal), (esInit, (idxVal, (params.maxOooKeysOrDefault, params.trimSize))))
  let ρArgs : Env (argsT :: Γ) := Env.cons argsVal ρ
  have hargs_eval :
      (Expr.pair (O := e2eOps ℓ P C K decT encT)
        (.pair ctr0 next0)
        (.pair entriesInit (.pair atIdx (.pair maxOoo trimSize)))).eval ρ = argsVal := by
    dsimp only [argsVal]
    simp only [Expr.eval, hCtr0, hNext0, hEsInit, hAt, hooo, htrim]
  have hlhs0 :
      (spqrDirKeyFwdComp I ctr0 next0 entriesInit atIdx maxOoo trimSize).eval ρ =
      (Comp.bind (O := e2eOps ℓ P C K decT encT)
        (spqrKeyAdvanceComp (Pt := Pt) (P := P) (C := C) (K := K)
          (decT := decT) (encT := encT) I
          (.fst (.fst .v0)) (.snd (.fst .v0)) (.fst (.snd .v0))
          (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))))
        (.caseOpt .v0
          (.ret .none)
          (.caseOpt
            (spqrPrevGcExpr
              (.snd (.snd .v0))
              (.fst .v0)
              (.fst (.snd (.snd (.snd .v2))))
              (.snd (.snd (.snd (.snd .v2)))))
            (.ret .none)
            (.bind (spqrChainNextKeyC I (.pair (.fst (.snd .v1)) (.fst .v1)))
              (.caseOpt (.snd .v0)
                (.ret .none)
                (.ret (.some (.pair
                  (.pair (.fst (.snd .v0))
                    (.pair (.fst .v0)
                      (.pair .v2 (e2ePureOp (.bytesLit 35 []) .unit))))
                  (.snd (.snd .v0)))))))))).eval ρArgs := by
    unfold spqrDirKeyFwdComp
    rw [comp_eval_bind_ret, hargs_eval]
  have hadv := eval_spqrKeyAdvanceComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I
    (.fst (.fst .v0))
    (.snd (.fst .v0))
    (.fst (.snd .v0))
    (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0))))
    ρArgs params
    (by dsimp only [ρArgs, argsVal]; simp only [Expr.eval, Expr.v0, Env.get]; exact hent)
    (by dsimp only [ρArgs, argsVal]; simp only [Expr.eval, Expr.v0, Env.get]; exact hctr_lt)
    (by dsimp only [ρArgs, argsVal]; simp only [Expr.eval, Expr.v0, Env.get]; exact hjump)
    (by dsimp only [ρArgs, argsVal]; simp [Expr.eval, Expr.v0, Env.get])
    hooo_le
  have hc_arg : (Expr.fst (O := e2eOps ℓ P C K decT encT) (.fst .v0)).eval ρArgs =
      ctrVal := rfl
  have hn_arg : (Expr.snd (O := e2eOps ℓ P C K decT encT) (.fst .v0)).eval ρArgs =
      nextVal := rfl
  have he_arg : (Expr.fst (O := e2eOps ℓ P C K decT encT) (.snd .v0)).eval ρArgs =
      esInit := rfl
  have hi_arg :
      (Expr.fst (O := e2eOps ℓ P C K decT encT) (.snd (.snd .v0))).eval ρArgs =
        idxVal := rfl
  rw [hc_arg, hn_arg, he_arg, hi_arg] at hadv
  cases hloop : ChainEpochDirection.keyAdvanceLoop (spqrHkdfWith C.F)
      { ctr := ctrVal, next := nextVal, prev := { data := encodePrevEntries esInit } }
      idxVal params with
  | error _ =>
    rw [hloop] at hadv
    dsimp only [Bind.bind, Except.bind]
    rw [hlhs0, comp_eval_bind_pure _ _ _ _ hadv, comp_eval_caseOpt_none _ _ _ _ rfl, comp_eval_ret]
    rfl
  | ok s1 =>
    rw [hloop] at hadv
    obtain ⟨entries1, hs1_prev, hent1_le, hadv_eval⟩ := hadv
    dsimp only [Bind.bind, Except.bind]
    rw [hs1_prev]
    let advT : Ty (e2eSig ℓ) := .prod U32 (.prod (B 32) (.list spqrPrevEntryT))
    let ρAdv : Env (advT :: .opt advT :: argsT :: Γ) :=
      Env.cons (s1.ctr, (s1.next, entries1))
        (Env.cons (some (s1.ctr, (s1.next, entries1))) ρArgs)
    have hlhs1 :
        (spqrDirKeyFwdComp I ctr0 next0 entriesInit atIdx maxOoo trimSize).eval ρ =
        (Comp.caseOpt (O := e2eOps ℓ P C K decT encT)
          (spqrPrevGcExpr
            (.snd (.snd .v0))
            (.fst .v0)
            (.fst (.snd (.snd (.snd .v2))))
            (.snd (.snd (.snd (.snd .v2)))))
          (.ret .none)
          (.bind (spqrChainNextKeyC I (.pair (.fst (.snd .v1)) (.fst .v1)))
            (.caseOpt (.snd .v0)
              (.ret .none)
              (.ret (.some (.pair
                (.pair (.fst (.snd .v0))
                  (.pair (.fst .v0)
                    (.pair .v2 (e2ePureOp (.bytesLit 35 []) .unit))))
                (.snd (.snd .v0)))))))).eval ρAdv := by
      rw [hlhs0, comp_eval_bind_pure _ _ _ _ hadv_eval, comp_eval_caseOpt_some _ _ _ _ rfl]
    have hgc := eval_spqrPrevGcExpr (Pt := Pt) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT)
      (.snd (.snd .v0))
      (.fst .v0)
      (.fst (.snd (.snd (.snd .v2))))
      (.snd (.snd (.snd (.snd .v2))))
      ρAdv params
      (by dsimp only [ρAdv]; simp only [Expr.eval, Expr.v0, Env.get]; exact hent1_le)
      (by dsimp only [ρAdv, ρArgs, argsVal]; simp [Expr.eval, Expr.v2, Env.get])
      (by dsimp only [ρAdv, ρArgs, argsVal]; simp [Expr.eval, Expr.v2, Env.get])
    have hgc_e :
        (Expr.snd (O := e2eOps ℓ P C K decT encT) (.snd .v0)).eval ρAdv =
          entries1 := rfl
    have hgc_c :
        (Expr.fst (O := e2eOps ℓ P C K decT encT) .v0).eval ρAdv = s1.ctr := rfl
    rw [hgc_e, hgc_c] at hgc
    cases hgc_res : ({ data := encodePrevEntries entries1 } : KeyHistory).gc s1.ctr params with
    | error _ =>
      rw [hgc_res] at hgc
      dsimp only [ChainResult.ofPanic, Bind.bind, Except.bind]
      rw [hlhs1, comp_eval_caseOpt_none _ _ _ _ hgc, comp_eval_ret]
      rfl
    | ok prevGc =>
      rw [hgc_res] at hgc
      obtain ⟨entriesGc, hgc_eq, _, hgc_eval⟩ := hgc
      dsimp only [ChainResult.ofPanic, Bind.bind, Except.bind]
      let ρGc : Env (.list spqrPrevEntryT :: advT :: .opt advT :: argsT :: Γ) :=
        Env.cons (t := .list spqrPrevEntryT) entriesGc ρAdv
      have hlhs2 :
          (spqrDirKeyFwdComp I ctr0 next0 entriesInit atIdx maxOoo trimSize).eval ρ =
          (Comp.bind (O := e2eOps ℓ P C K decT encT)
            (spqrChainNextKeyC I (.pair (.fst (.snd .v1)) (.fst .v1)))
            (.caseOpt (.snd .v0)
              (.ret .none)
              (.ret (.some (.pair
                (.pair (.fst (.snd .v0))
                  (.pair (.fst .v0)
                    (.pair .v2 (e2ePureOp (.bytesLit 35 []) .unit))))
                (.snd (.snd .v0))))))).eval ρGc := by
        rw [hlhs1, comp_eval_caseOpt_some _ _ _ _ hgc_eval]
      cases hnk : ChainEpochDirection.nextKeyInternal (spqrHkdfWith C.F) s1.next s1.ctr with
      | error _ =>
        dsimp only
        rw [hlhs2, comp_eval_bind, eval_spqrChainNextKeyC]
        have hnk_arg :
            (Expr.pair (O := e2eOps ℓ P C K decT encT) (.fst (.snd .v1)) (.fst .v1)).eval
              ρGc = (s1.next, s1.ctr) := rfl
        rw [hnk_arg, spqrChainNextKeyEval_take32_lossless]
        dsimp only [spqrChainNextKeyRaw]
        rw [hnk, pure_bind, comp_eval_caseOpt]
        rfl
      | ok nkOut =>
        rcases nkOut with ⟨next2, ctr2, kIdx, outKey⟩
        have hctr2_eq : kIdx = ctr2 ∧ next2.length ≤ 64 ∧ outKey.length = 32 := by
          unfold ChainEpochDirection.nextKeyInternal at hnk
          split_ifs at hnk with hb1 hb2
          injection hnk with hnk'
          rcases Prod.mk.inj hnk' with ⟨rfl, h2⟩
          rcases Prod.mk.inj h2 with ⟨rfl, h3⟩
          rcases Prod.mk.inj h3 with ⟨rfl, rfl⟩
          have h64 : (spqrHkdfWith C.F (List.replicate 32 0#8) s1.next
              (toBEBytes 4 (s1.ctr + 1#32) ++
                CryptoVerification.LibsignalSpqrV1.chainNextInfo) 64).length = 64 := by
            simp [spqrHkdfWith]
          exact ⟨rfl, Nat.le_trans (List.length_take_le 32 _) (by decide),
            by rw [List.length_take, List.length_drop, h64]; decide⟩
        obtain ⟨rfl, hnext2_64, hout32⟩ := hctr2_eq
        dsimp only [Pure.pure, Except.pure]
        refine ⟨entriesGc, hgc_eq, hnext2_64, hout32, ?_⟩
        rw [hlhs2, comp_eval_bind, eval_spqrChainNextKeyC]
        have hnk_arg :
            (Expr.pair (O := e2eOps ℓ P C K decT encT) (.fst (.snd .v1)) (.fst .v1)).eval
              ρGc = (s1.next, s1.ctr) := rfl
        rw [hnk_arg, spqrChainNextKeyEval_take32_lossless]
        dsimp only [spqrChainNextKeyRaw]
        rw [hnk, pure_bind, comp_eval_caseOpt]
        rfl

/-- Simulates `ChainEpochDirection.key` on `(recvDir, atIdx, params)`. -/
def spqrDirKeyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (recvDir : Expr (e2eOps ℓ P C K decT encT) Γ spqrDirT)
    (atIdx maxJump maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.opt (.prod spqrDirT BV256)) :=
  .bind (.ret (.pair recvDir (.pair atIdx (.pair maxJump (.pair maxOoo trimSize)))))
    (.ite (e2ePureOp .u32Lt (.pair (.fst (.snd .v0)) (.fst (.fst .v0))))
      (.caseOpt
        (spqrPrevGetExpr
          (.fst (.snd (.snd (.fst .v0))))
          (.snd (.snd (.snd (.fst .v0))))
          (.fst (.snd .v0))
          (.fst (.fst .v0))
          (.fst (.snd (.snd (.snd .v0)))))
        (.ret .none)
        (.ret (.some (.pair
          (.pair (.fst (.fst .v1))
            (.pair (.fst (.snd (.fst .v1)))
              (.pair (.fst .v0) (e2ePureOp (.bytesLit 35 []) .unit))))
          (.snd .v0)))))
      (.ite (e2ePureOp .u32Eq (.pair (.fst (.snd .v0)) (.fst (.fst .v0))))
        (.ret .none)
        (.ite (e2ePureOp .u32Lt
            (.pair (.fst (.snd (.snd .v0)))
              (e2ePureOp .u32Sub (.pair (.fst (.snd .v0)) (.fst (.fst .v0))))))
          (.ret .none)
          (.ite (e2ePureOp .u32Lt
              (.pair
                (e2ePureOp .u32Sub
                  (.pair (e2ePureOp (.u32Lit 0xffffffff#32) .unit)
                    (.fst (.snd (.snd (.snd .v0))))))
                (.fst (.fst .v0))))
            (.ret .none)
            (spqrDirKeyFwdComp I
              (.fst (.fst .v0))
              (.fst (.snd (.fst .v0)))
              (.ite (e2ePureOp .u32Lt
                  (.pair
                    (e2ePureOp .u32Add
                      (.pair (.fst (.fst .v0)) (.fst (.snd (.snd (.snd .v0))))))
                    (.fst (.snd .v0))))
                .nil
                (.fst (.snd (.snd (.fst .v0)))))
              (.fst (.snd .v0))
              (.fst (.snd (.snd (.snd .v0))))
              (.snd (.snd (.snd (.snd .v0)))))))))

private theorem spqrDirToV_of_prev_mod36 {ℓ : ℕ} (d : ChainEpochDirection)
    (hnext64 : d.next.length ≤ 64)
    (hprev_le : d.prev.data.length ≤ 79236)
    (hprev_mod : d.prev.data.length % 36 = 0) :
    ∃ es : List (BitVec 32 × BitVec 256),
      es.length ≤ 2201 ∧
      d.prev = { data := encodePrevEntries es } ∧
      spqrDirToV (ℓ := ℓ) d.intoPb = (d.ctr, (d.next, (es, []))) := by
  obtain ⟨es, hsplit, hent_div, henc_es⟩ :=
    splitSpqrPrev_of_mod36 (fuel := 2201) (bs := d.prev.data) (by omega) hprev_mod
  have hes_le : es.length ≤ 2201 := by
    rw [hent_div]; omega
  have hd_prev : d.prev = { data := encodePrevEntries es } := by
    rcases hp : d.prev with ⟨pdata⟩
    have hp_eq : encodePrevEntries es = pdata := by simpa [hp] using henc_es
    rw [hp_eq]
  exact ⟨es, hes_le, hd_prev, spqrDirToV_eq d.intoPb hnext64 hsplit⟩

theorem eval_spqrDirKeyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (recvDir : Expr (e2eOps ℓ P C K decT encT) Γ spqrDirT)
    (atIdx maxJump maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (ρ : Env Γ) (d : ChainEpochDirection) (params : ChainParamsPB)
    (hnext64 : d.next.length ≤ 64)
    (hprev_le : d.prev.data.length ≤ 79236)
    (hprev_mod : d.prev.data.length % 36 = 0)
    (hd : recvDir.eval ρ = spqrDirToV (ℓ := ℓ) d.intoPb)
    (hmj : maxJump.eval ρ = params.maxJumpOrDefault)
    (hmj_le : params.maxJumpOrDefault.toNat ≤ 25000)
    (hooo : maxOoo.eval ρ = params.maxOooKeysOrDefault)
    (hooo_le : params.maxOooKeysOrDefault.toNat ≤ 2000)
    (htrim : trimSize.eval ρ = params.trimSize) :
    match d.key (spqrHkdfWith C.F) (atIdx.eval ρ) params with
    | .error _ => (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize).eval ρ = pure none
    | .ok (d', out) =>
      ∃ entriesOut : List (BitVec 32 × BitVec 256),
        d'.prev = { data := encodePrevEntries entriesOut } ∧
        d'.next.length ≤ 64 ∧
        out.length = 32 ∧
        (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize).eval ρ =
          pure (some ((d'.ctr, (d'.next, (entriesOut, []))), bytesToKey32 out)) := by
  obtain ⟨es, hes_le, hd_prev, hd_val⟩ :=
    spqrDirToV_of_prev_mod36 (ℓ := ℓ) d hnext64 hprev_le hprev_mod
  generalize hAt : atIdx.eval ρ = idxVal
  let argsT : Ty (e2eSig ℓ) := .prod spqrDirT (.prod U32 (.prod U32 (.prod U32 .nat)))
  let argsVal : argsT.denote :=
    ((d.ctr, (d.next, (es, ([] : Bytes)))),
     (idxVal, (params.maxJumpOrDefault, (params.maxOooKeysOrDefault, params.trimSize))))
  let ρArgs : Env (argsT :: Γ) := Env.cons (t := argsT) argsVal ρ
  have hargs_eval :
      (Expr.pair (O := e2eOps ℓ P C K decT encT) recvDir
        (.pair atIdx (.pair maxJump (.pair maxOoo trimSize)))).eval ρ = argsVal := by
    dsimp only [argsVal]
    simp only [Expr.eval, hd, hd_val, hAt, hmj, hooo, htrim]
  have hlhs0 :
      (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize).eval ρ =
      (Comp.ite (O := e2eOps ℓ P C K decT encT)
        (e2ePureOp .u32Lt (.pair (.fst (.snd .v0)) (.fst (.fst .v0))))
        (.caseOpt
          (spqrPrevGetExpr
            (.fst (.snd (.snd (.fst .v0))))
            (.snd (.snd (.snd (.fst .v0))))
            (.fst (.snd .v0))
            (.fst (.fst .v0))
            (.fst (.snd (.snd (.snd .v0)))))
          (.ret .none)
          (.ret (.some (.pair
            (.pair (.fst (.fst .v1))
              (.pair (.fst (.snd (.fst .v1)))
                (.pair (.fst .v0) (e2ePureOp (.bytesLit 35 []) .unit))))
            (.snd .v0)))))
        (.ite (e2ePureOp .u32Eq (.pair (.fst (.snd .v0)) (.fst (.fst .v0))))
          (.ret .none)
          (.ite (e2ePureOp .u32Lt
              (.pair (.fst (.snd (.snd .v0)))
                (e2ePureOp .u32Sub (.pair (.fst (.snd .v0)) (.fst (.fst .v0))))))
            (.ret .none)
            (.ite (e2ePureOp .u32Lt
                (.pair
                  (e2ePureOp .u32Sub
                    (.pair (e2ePureOp (.u32Lit 0xffffffff#32) .unit)
                      (.fst (.snd (.snd (.snd .v0))))))
                  (.fst (.fst .v0))))
              (.ret .none)
              (spqrDirKeyFwdComp (Pt := Pt) (P := P) (C := C) (K := K)
                (decT := decT) (encT := encT) I
                (.fst (.fst .v0))
                (.fst (.snd (.fst .v0)))
                (.ite (e2ePureOp .u32Lt
                    (.pair
                      (e2ePureOp .u32Add
                        (.pair (.fst (.fst .v0)) (.fst (.snd (.snd (.snd .v0))))))
                      (.fst (.snd .v0))))
                  .nil
                  (.fst (.snd (.snd (.fst .v0)))))
                (.fst (.snd .v0))
                (.fst (.snd (.snd (.snd .v0))))
                (.snd (.snd (.snd (.snd .v0))))))))).eval ρArgs := by
    unfold spqrDirKeyComp
    rw [comp_eval_bind_ret, hargs_eval]
  unfold ChainEpochDirection.key
  by_cases hlt : idxVal < d.ctr
  · rw [ite_eq_left hlt, hd_prev]
    have hc1 :
        (e2ePureOp (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
          .u32Lt (.pair (.fst (.snd .v0)) (.fst (.fst .v0)))).eval ρArgs = true := by
      dsimp only [ρArgs, argsVal]
      simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get, hlt, decide_true]
    have hget := eval_spqrPrevGetExpr (Pt := Pt) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT)
      (.fst (.snd (.snd (.fst .v0))))
      (.snd (.snd (.snd (.fst .v0))))
      (.fst (.snd .v0))
      (.fst (.fst .v0))
      (.fst (.snd (.snd (.snd .v0))))
      ρArgs params
      (by dsimp only [ρArgs, argsVal]; simp only [Expr.eval, Expr.v0, Env.get]; exact hes_le)
      (by dsimp only [ρArgs, argsVal]; simp [Expr.eval, Expr.v0, Env.get])
      (by dsimp only [ρArgs, argsVal]; simp [Expr.eval, Expr.v0, Env.get])
    have hg_e :
        (Expr.fst (O := e2eOps ℓ P C K decT encT)
          (.snd (.snd (.fst .v0)))).eval ρArgs = es := rfl
    have hg_i :
        (Expr.fst (O := e2eOps ℓ P C K decT encT) (.snd .v0)).eval ρArgs =
          idxVal := rfl
    have hg_c :
        (Expr.fst (O := e2eOps ℓ P C K decT encT) (.fst .v0)).eval ρArgs =
          d.ctr := rfl
    rw [hg_e, hg_i, hg_c] at hget
    cases hg : ({ data := encodePrevEntries es } : KeyHistory).get idxVal d.ctr params with
    | error _ =>
      rw [hg] at hget
      dsimp only [Bind.bind, Except.bind]
      rw [hlhs0, comp_eval_ite_true _ _ _ _ hc1, comp_eval_caseOpt_none _ _ _ _ hget, comp_eval_ret]
      rfl
    | ok gOut =>
      rcases gOut with ⟨prev', out⟩
      rw [hg] at hget
      obtain ⟨entries', hprev'_eq, _, hout32, hget_eval⟩ := hget
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      refine ⟨entries', hprev'_eq, hnext64, hout32, ?_⟩
      rw [hlhs0, comp_eval_ite_true _ _ _ _ hc1, comp_eval_caseOpt_some _ _ _ _ hget_eval,
        comp_eval_ret]
      rfl
  · rw [ite_eq_right hlt]
    have hc1 :
        (e2ePureOp (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
          .u32Lt (.pair (.fst (.snd .v0)) (.fst (.fst .v0)))).eval ρArgs = false := by
      dsimp only [ρArgs, argsVal]
      simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get, hlt, decide_false]
    have hlhs1 :
        (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize).eval ρ =
        (Comp.ite (O := e2eOps ℓ P C K decT encT)
          (e2ePureOp .u32Eq (.pair (.fst (.snd .v0)) (.fst (.fst .v0))))
          (.ret .none)
          (.ite (e2ePureOp .u32Lt
              (.pair (.fst (.snd (.snd .v0)))
                (e2ePureOp .u32Sub (.pair (.fst (.snd .v0)) (.fst (.fst .v0))))))
            (.ret .none)
            (.ite (e2ePureOp .u32Lt
                (.pair
                  (e2ePureOp .u32Sub
                    (.pair (e2ePureOp (.u32Lit 0xffffffff#32) .unit)
                      (.fst (.snd (.snd (.snd .v0))))))
                  (.fst (.fst .v0))))
              (.ret .none)
              (spqrDirKeyFwdComp (Pt := Pt) (P := P) (C := C) (K := K)
                (decT := decT) (encT := encT) I
                (.fst (.fst .v0))
                (.fst (.snd (.fst .v0)))
                (.ite (e2ePureOp .u32Lt
                    (.pair
                      (e2ePureOp .u32Add
                        (.pair (.fst (.fst .v0)) (.fst (.snd (.snd (.snd .v0))))))
                      (.fst (.snd .v0))))
                  .nil
                  (.fst (.snd (.snd (.fst .v0)))))
                (.fst (.snd .v0))
                (.fst (.snd (.snd (.snd .v0))))
                (.snd (.snd (.snd (.snd .v0)))))))).eval ρArgs := by
      rw [hlhs0, comp_eval_ite_false _ _ _ _ hc1]
    by_cases heq : (idxVal == d.ctr) = true
    · rw [ite_eq_left heq]
      dsimp only
      have hc2 :
          (e2ePureOp (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
            .u32Eq (.pair (.fst (.snd .v0)) (.fst (.fst .v0)))).eval ρArgs = true := by
        dsimp only [ρArgs, argsVal]
        simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get, heq]
      rw [hlhs1, comp_eval_ite_true _ _ _ _ hc2, comp_eval_ret]
      rfl
    · rw [ite_eq_right heq]
      have hc2 :
          (e2ePureOp (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
            .u32Eq (.pair (.fst (.snd .v0)) (.fst (.fst .v0)))).eval ρArgs = false := by
        dsimp only [ρArgs, argsVal]
        simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get,
          Bool.eq_false_iff.mpr heq]
      have hlhs2 :
          (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize).eval ρ =
          (Comp.ite (O := e2eOps ℓ P C K decT encT)
            (e2ePureOp .u32Lt
              (.pair (.fst (.snd (.snd .v0)))
                (e2ePureOp .u32Sub (.pair (.fst (.snd .v0)) (.fst (.fst .v0))))))
            (.ret .none)
            (.ite (e2ePureOp .u32Lt
                (.pair
                  (e2ePureOp .u32Sub
                    (.pair (e2ePureOp (.u32Lit 0xffffffff#32) .unit)
                      (.fst (.snd (.snd (.snd .v0))))))
                  (.fst (.fst .v0))))
              (.ret .none)
              (spqrDirKeyFwdComp (Pt := Pt) (P := P) (C := C) (K := K)
                (decT := decT) (encT := encT) I
                (.fst (.fst .v0))
                (.fst (.snd (.fst .v0)))
                (.ite (e2ePureOp .u32Lt
                    (.pair
                      (e2ePureOp .u32Add
                        (.pair (.fst (.fst .v0)) (.fst (.snd (.snd (.snd .v0))))))
                      (.fst (.snd .v0))))
                  .nil
                  (.fst (.snd (.snd (.fst .v0)))))
                (.fst (.snd .v0))
                (.fst (.snd (.snd (.snd .v0))))
                (.snd (.snd (.snd (.snd .v0))))))).eval ρArgs := by
        rw [hlhs1, comp_eval_ite_false _ _ _ _ hc2]
      have hne_ctr : idxVal ≠ d.ctr := beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr heq)
      have hctr_lt_idx : d.ctr.toNat < idxVal.toNat := by
        have hnot : ¬ (idxVal.toNat < d.ctr.toNat) := fun h => hlt (BitVec.lt_def.mpr h)
        have hne_n : idxVal.toNat ≠ d.ctr.toNat := fun h => hne_ctr (BitVec.eq_of_toNat_eq h)
        omega
      by_cases hjump : idxVal - d.ctr > params.maxJumpOrDefault
      · rw [ite_eq_left hjump]
        dsimp only
        have hjump' : params.maxJumpOrDefault < idxVal - d.ctr := hjump
        have hc3 :
            (e2ePureOp (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
              .u32Lt (.pair (.fst (.snd (.snd .v0)))
                (e2ePureOp .u32Sub (.pair (.fst (.snd .v0)) (.fst (.fst .v0)))))).eval ρArgs =
              true := by
          dsimp only [ρArgs, argsVal]
          simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get, hjump',
            decide_true]
        rw [hlhs2, comp_eval_ite_true _ _ _ _ hc3, comp_eval_ret]
        rfl
      · rw [ite_eq_right hjump]
        have hjump' : ¬ (params.maxJumpOrDefault < idxVal - d.ctr) := hjump
        have hc3 :
            (e2ePureOp (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
              .u32Lt (.pair (.fst (.snd (.snd .v0)))
                (e2ePureOp .u32Sub (.pair (.fst (.snd .v0)) (.fst (.fst .v0)))))).eval ρArgs =
              false := by
          dsimp only [ρArgs, argsVal]
          simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get, hjump',
            decide_false]
        have hlhs3 :
            (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize).eval ρ =
            (Comp.ite (O := e2eOps ℓ P C K decT encT)
              (e2ePureOp .u32Lt
                (.pair
                  (e2ePureOp .u32Sub
                    (.pair (e2ePureOp (.u32Lit 0xffffffff#32) .unit)
                      (.fst (.snd (.snd (.snd .v0))))))
                  (.fst (.fst .v0))))
              (.ret .none)
              (spqrDirKeyFwdComp (Pt := Pt) (P := P) (C := C) (K := K)
                (decT := decT) (encT := encT) I
                (.fst (.fst .v0))
                (.fst (.snd (.fst .v0)))
                (.ite (e2ePureOp .u32Lt
                    (.pair
                      (e2ePureOp .u32Add
                        (.pair (.fst (.fst .v0)) (.fst (.snd (.snd (.snd .v0))))))
                      (.fst (.snd .v0))))
                  .nil
                  (.fst (.snd (.snd (.fst .v0)))))
                (.fst (.snd .v0))
                (.fst (.snd (.snd (.snd .v0))))
                (.snd (.snd (.snd (.snd .v0)))))).eval ρArgs := by
          rw [hlhs2, comp_eval_ite_false _ _ _ _ hc3]
        have hdiff_le : idxVal.toNat - d.ctr.toNat ≤ 25000 := by
          have hsub : (idxVal - d.ctr).toNat = idxVal.toNat - d.ctr.toNat :=
            BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; omega)
          simp only [BitVec.lt_def, hsub] at hjump'
          omega
        have hovf_iff := u32_add_ovf_iff d.ctr params.maxOooKeysOrDefault
        by_cases hovf : d.ctr.toNat + params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
        · rw [ite_eq_left hovf]
          dsimp only
          have hovf_bv : 0xffffffff#32 - params.maxOooKeysOrDefault < d.ctr := hovf_iff.mpr hovf
          have hc4 :
              (e2ePureOp (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
                .u32Lt (.pair
                  (e2ePureOp .u32Sub
                    (.pair (e2ePureOp (.u32Lit 0xffffffff#32) .unit)
                      (.fst (.snd (.snd (.snd .v0))))))
                  (.fst (.fst .v0)))).eval ρArgs = true := by
            dsimp only [ρArgs, argsVal]
            simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get, hovf_bv,
              decide_true]
          rw [hlhs3, comp_eval_ite_true _ _ _ _ hc4, comp_eval_ret]
          rfl
        · rw [ite_eq_right hovf]
          have hovf_bv : ¬ (0xffffffff#32 - params.maxOooKeysOrDefault < d.ctr) :=
            fun h => hovf (hovf_iff.mp h)
          have hc4 :
              (e2ePureOp (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
                .u32Lt (.pair
                  (e2ePureOp .u32Sub
                    (.pair (e2ePureOp (.u32Lit 0xffffffff#32) .unit)
                      (.fst (.snd (.snd (.snd .v0))))))
                  (.fst (.fst .v0)))).eval ρArgs = false := by
            dsimp only [ρArgs, argsVal]
            simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get, hovf_bv,
              decide_false]
          let esInit := if idxVal > d.ctr + params.maxOooKeysOrDefault then [] else es
          have hself0_eq :
              (if idxVal > d.ctr + params.maxOooKeysOrDefault then
                 { d with prev := d.prev.clear }
               else d) =
              { ctr := d.ctr, next := d.next, prev := { data := encodePrevEntries esInit } } := by
            dsimp only [esInit]
            by_cases hc : idxVal > d.ctr + params.maxOooKeysOrDefault
            · simp [hc, KeyHistory.clear]
            · rw [ite_eq_right hc, ite_eq_right hc]
              cases d
              dsimp only at hd_prev ⊢
              subst hd_prev
              rfl
          rw [hself0_eq]
          have hlhs_eq :
              (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize).eval ρ =
              (spqrDirKeyFwdComp (Pt := Pt) (P := P) (C := C) (K := K)
                (decT := decT) (encT := encT) I
                (.fst (.fst .v0))
                (.fst (.snd (.fst .v0)))
                (.ite (e2ePureOp .u32Lt
                    (.pair
                      (e2ePureOp .u32Add
                        (.pair (.fst (.fst .v0)) (.fst (.snd (.snd (.snd .v0))))))
                      (.fst (.snd .v0))))
                  .nil
                  (.fst (.snd (.snd (.fst .v0)))))
                (.fst (.snd .v0))
                (.fst (.snd (.snd (.snd .v0))))
                (.snd (.snd (.snd (.snd .v0))))).eval ρArgs := by
            rw [hlhs3, comp_eval_ite_false _ _ _ _ hc4]
          have hfwd := eval_spqrDirKeyFwdComp (Pt := Pt) (P := P) (C := C) (K := K)
            (decT := decT) (encT := encT) I
            (.fst (.fst .v0))
            (.fst (.snd (.fst .v0)))
            (.ite (e2ePureOp .u32Lt
                (.pair
                  (e2ePureOp .u32Add
                    (.pair (.fst (.fst .v0)) (.fst (.snd (.snd (.snd .v0))))))
                  (.fst (.snd .v0))))
              .nil
              (.fst (.snd (.snd (.fst .v0)))))
            (.fst (.snd .v0))
            (.fst (.snd (.snd (.snd .v0))))
            (.snd (.snd (.snd (.snd .v0))))
            ρArgs params
            (by
              dsimp only [ρArgs, argsVal]
              simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get]
              by_cases hc : d.ctr + params.maxOooKeysOrDefault < idxVal <;> simp [hc, hes_le])
            (by dsimp only [ρArgs, argsVal]; simp only [Expr.eval, Expr.v0, Env.get]; exact hctr_lt_idx)
            (by dsimp only [ρArgs, argsVal]; simp only [Expr.eval, Expr.v0, Env.get]; exact hdiff_le)
            (by dsimp only [ρArgs, argsVal]; simp [Expr.eval, Expr.v0, Env.get])
            hooo_le
            (by dsimp only [ρArgs, argsVal]; simp [Expr.eval, Expr.v0, Env.get])
          have hadv_esInit :
              (if decide (d.ctr + params.maxOooKeysOrDefault < idxVal) = true then [] else es) =
                esInit := by
            dsimp only [esInit, gt_iff_lt]
            by_cases hc : d.ctr + params.maxOooKeysOrDefault < idxVal <;> simp [hc]
          have hexpr_esInit :
              (Expr.ite (O := e2eOps ℓ P C K decT encT) (e2ePureOp .u32Lt
                  (.pair
                    (e2ePureOp .u32Add
                      (.pair (.fst (.fst .v0)) (.fst (.snd (.snd (.snd .v0))))))
                    (.fst (.snd .v0))))
                .nil
                (.fst (.snd (.snd (.fst .v0))))).eval ρArgs = esInit := by
            dsimp only [ρArgs, argsVal]
            simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get, hadv_esInit]
          have hctr_arg :
              (Expr.fst (O := e2eOps ℓ P C K decT encT) (.fst .v0)).eval ρArgs =
                d.ctr := rfl
          have hnext_arg :
              (Expr.fst (O := e2eOps ℓ P C K decT encT)
                (.snd (.fst .v0))).eval ρArgs = d.next := rfl
          have hat_arg :
              (Expr.fst (O := e2eOps ℓ P C K decT encT) (.snd .v0)).eval ρArgs =
                idxVal := rfl
          rw [hctr_arg, hnext_arg, hexpr_esInit, hat_arg, ← hlhs_eq] at hfwd
          exact hfwd

/-- Simulates `Chain.recvKey` on `(ch, epoch, index)`. -/
def spqrChainRecvKeyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (index : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    Comp (e2eOps ℓ P C K decT encT) I Γ (.opt (.prod spqrChainT (.opt BV256))) :=
  .bind (.ret (.pair ch (.pair epoch index)))
    (.ite (.and
        (e2ePureOp .u64Eq (.pair (.fst (.snd .v0)) (e2ePureOp (.u64Lit 0#64) .unit)))
        (e2ePureOp .u32Eq (.pair (.snd (.snd .v0)) (e2ePureOp (.u32Lit 0#32) .unit))))
      (.ret (.some (.pair (.fst .v0) .none)))
      (.caseOpt
        (spqrEpochIdxExpr
          (.fst (.snd (.fst .v0)))
          (.len (.fst (.snd (.snd (.fst .v0)))))
          (.fst (.snd .v0)))
        (.ret .none)
        (.caseOpt (listGetExpr 4 .v0 (.fst (.snd (.snd (.fst .v1)))))
          (.ret .none)
          (.caseOpt (.snd .v0)
            (.ret .none)
            (.caseOpt (.snd (.snd (.snd (.snd (.snd (.fst .v3))))))
              (.ret .none)
              (.bind (.ret
                  (.letE
                    (.ite (e2ePureOp .u32Lt
                        (.pair (e2ePureOp (.u32Lit 0#32) .unit) (.snd .v0)))
                      (.snd .v0)
                      (e2ePureOp (.u32Lit 2000#32) .unit))
                    (.pair
                      (.ite (e2ePureOp .u32Lt
                          (.pair (e2ePureOp (.u32Lit 0#32) .unit) (.fst .v1)))
                        (.fst .v1)
                        (e2ePureOp (.u32Lit 25000#32) .unit))
                      (.pair .v0
                        (.add (.divK 10 (.mulK 11 (e2ePureOp .u32ToNat .v0))) (.nat 1))))))
                (.bind
                  (spqrDirKeyComp I .v2
                    (.snd (.snd .v5))
                    (.fst .v0)
                    (.fst (.snd .v0))
                    (.snd (.snd .v0)))
                  (.caseOpt .v0
                    (.ret .none)
                    (.ret (.some (.pair
                      (.pair (.fst (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))
                        (.pair (.fst (.snd (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
                          (.pair
                            (listSetExpr 4 .v6
                              (.pair (.fst .v5) (.some (.fst .v0)))
                              (.fst (.snd (.snd (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
                            (.snd (.snd (.snd (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))))
                      (.some (.snd .v0)))))))))))))

theorem queries_spqrChainRecvKeyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (index : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (spqrChainRecvKeyComp I ch epoch index).queries w ws = 0 := by
  simp [spqrChainRecvKeyComp, spqrDirKeyComp, spqrDirKeyFwdComp, spqrKeyAdvanceComp,
    spqrKeyAdvanceFuelComp, spqrKeyAdvanceStep, Comp.queries]

theorem recvKey_out_empty_or_32 (F : ShaCompress) (ch ch' : Chain) (ep : BitVec 64)
    (idx : BitVec 32) (out : Bytes)
    (h : ch.recvKey (spqrHkdfWith F) ep idx = .ok (ch', out)) :
    out = [] ∨ out.length = 32 := by
  unfold Chain.recvKey at h
  by_cases hz : (ep == 0#64 && idx == 0#32) = true
  · simp only [hz, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
    exact Or.inl h.2.symm
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
    cases hep : ch.epochIdx ep with
    | error _ => rw [hep] at h; cases h
    | ok ei =>
      rw [hep] at h
      dsimp only [ChainResult.ofError, Bind.bind, Except.bind] at h
      cases hlk : ch.links[ei]? with
      | none => rw [hlk] at h; cases h
      | some lk =>
        rw [hlk] at h
        dsimp only at h
        cases hk : lk.recv.key (spqrHkdfWith F) idx ch.params with
        | error _ => rw [hk] at h; cases h
        | ok dout =>
          rcases dout with ⟨recv', out'⟩
          rw [hk] at h
          injection h with h'
          rcases Prod.mk.inj h' with ⟨_, rfl⟩
          right
          unfold ChainEpochDirection.key at hk
          by_cases hlt : idx < lk.recv.ctr
          · rw [ite_eq_left hlt] at hk
            cases hget : lk.recv.prev.get idx lk.recv.ctr ch.params with
            | error _ => rw [hget] at hk; cases hk
            | ok po =>
              rcases po with ⟨prev', out0⟩
              rw [hget] at hk
              injection hk with hk'
              rcases Prod.mk.inj hk' with ⟨_, rfl⟩
              unfold KeyHistory.get at hget
              by_cases hal : (lk.recv.prev.data.length % KeyHistory.KEY_SIZE != 0) = true
              · rw [ite_eq_left hal] at hget; cases hget
              · rw [ite_eq_right hal] at hget
                have hmod : lk.recv.prev.data.length % 36 = 0 := by
                  simp only [KeyHistory.KEY_SIZE, bne_iff_ne, Decidable.not_not] at hal
                  exact hal
                dsimp only at hget
                split_ifs at hget
                suffices ∀ (rem k : ℕ), lk.recv.prev.data.length - 36 * k ≤ rem →
                    KeyHistory.getLoop lk.recv.prev idx (toBEBytes 4 idx) ch.params (36 * k) =
                      .ok (prev', out0) → out0.length = 32 from
                  this lk.recv.prev.data.length 0 (by omega) (by simpa using hget)
                intro rem
                induction rem with
                | zero =>
                  intro k hrem hg
                  have hn : ¬ (36 * k < lk.recv.prev.data.length) := by omega
                  rw [KeyHistory.getLoop, dite_eq_right hn] at hg
                  cases hg
                | succ rem ih =>
                  intro k hrem hg
                  by_cases hk36 : 36 * k < lk.recv.prev.data.length
                  · rw [KeyHistory.getLoop, dite_eq_left hk36] at hg
                    by_cases hm : ((lk.recv.prev.data.drop (36 * k)).take 4 == toBEBytes 4 idx) = true
                    · rw [ite_eq_left hm] at hg
                      injection hg with hg'
                      rcases Prod.mk.inj hg' with ⟨_, rfl⟩
                      simp only [List.length_take, List.length_drop]
                      omega
                    · rw [ite_eq_right hm] at hg
                      have hstep : 36 * k + KeyHistory.KEY_SIZE = 36 * (k + 1) := by
                        simp only [KeyHistory.KEY_SIZE]; omega
                      rw [hstep] at hg
                      exact ih (k + 1) (by omega) hg
                  · rw [KeyHistory.getLoop, dite_eq_right hk36] at hg
                    cases hg
          · rw [ite_eq_right hlt] at hk
            dsimp only at hk
            by_cases h1 : (idx == lk.recv.ctr) = true
            · rw [ite_eq_left h1] at hk; cases hk
            · rw [ite_eq_right h1] at hk
              by_cases h2 : idx - lk.recv.ctr > ch.params.maxJumpOrDefault
              · rw [ite_eq_left h2] at hk; cases hk
              · rw [ite_eq_right h2] at hk
                by_cases h3 : lk.recv.ctr.toNat + ch.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
                · rw [ite_eq_left h3] at hk; cases hk
                · rw [ite_eq_right h3] at hk
                  dsimp only [Bind.bind, Except.bind, ChainResult.ofPanic, Pure.pure,
                    Except.pure] at hk
                  cases hl : ChainEpochDirection.keyAdvanceLoop (spqrHkdfWith F) _ idx ch.params with
                  | error _ => rw [hl] at hk; cases hk
                  | ok s1 =>
                    rw [hl] at hk
                    dsimp only at hk
                    cases hgc : s1.prev.gc s1.ctr ch.params with
                    | error _ => rw [hgc] at hk; cases hk
                    | ok pg =>
                      rw [hgc] at hk
                      dsimp only at hk
                      cases hnk : ChainEpochDirection.nextKeyInternal (spqrHkdfWith F) s1.next s1.ctr with
                      | error _ => rw [hnk] at hk; cases hk
                      | ok nko =>
                        rcases nko with ⟨n2, c2, c2', okOut⟩
                        rw [hnk] at hk
                        injection hk with hk'
                        rcases Prod.mk.inj hk' with ⟨_, rfl⟩
                        unfold ChainEpochDirection.nextKeyInternal at hnk
                        split_ifs at hnk
                        injection hnk with hnk'
                        rcases Prod.mk.inj hnk' with ⟨_, h2'⟩
                        rcases Prod.mk.inj h2' with ⟨_, h3'⟩
                        rcases Prod.mk.inj h3' with ⟨_, rfl⟩
                        have h64 : (spqrHkdfWith F (List.replicate 32 0#8) s1.next
                            (toBEBytes 4 (s1.ctr + 1#32) ++
                              CryptoVerification.LibsignalSpqrV1.chainNextInfo) 64).length = 64 := by
                          simp [spqrHkdfWith]
                        rw [List.length_take, List.length_drop, h64]
                        decide

private theorem recvDirOk_prev_mod36 (F : ShaCompress) {seed : Bytes} {R : Finset ℕ}
    {d : ChainEpochDirection} (h : RecvDirOk F seed R d) :
    d.prev.data.length % 36 = 0 := by
  obtain ⟨S, ⟨L, _, _, hdata⟩, _, _⟩ := h.hprev
  rw [hdata]
  suffices ∀ M : List ℕ,
      ((M.map fun j => CryptoVerification.SpqrV1Sync.ChainSync.histEntry j
        (CryptoVerification.SpqrV1Sync.ChainSync.keyAt F seed (j - 1))).flatten).length =
      36 * M.length by
    rw [this L]
    omega
  intro M
  induction M with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.flatten_cons, List.length_append, ih, List.length_cons]
    have h64 : (CryptoVerification.SpqrV1Sync.ChainSync.stepGen F
        (CryptoVerification.SpqrV1Sync.ChainSync.nextAt F seed (x - 1)) (x - 1)).length = 64 := by
      simp [CryptoVerification.SpqrV1Sync.ChainSync.stepGen, spqrHkdfWith]
    simp only [CryptoVerification.SpqrV1Sync.ChainSync.histEntry, length_toBEBytes4,
      CryptoVerification.SpqrV1Sync.ChainSync.keyAt, List.length_append, List.length_take,
      List.length_drop, h64]
    omega

theorem eval_spqrChainRecvKeyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (chExpr : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epExpr : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (idxExpr : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (ρ : Env Γ) (authKey : Bytes) (dir : Direction) (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ)
    (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (hok : ChainOk C.F authKey dir secret sendCtr recvSet ch)
    (hsmall : RecvSmallTight ch)
    (hlen4 : ch.links.length ≤ 4)
    (hch : chExpr.eval ρ = spqrChainToV (ℓ := ℓ) ch.intoPb) :
    (spqrChainRecvKeyComp I chExpr epExpr idxExpr).eval ρ =
      pure (match ch.recvKey (spqrHkdfWith C.F) (epExpr.eval ρ) (idxExpr.eval ρ) with
        | .ok (ch', out) =>
          some (spqrChainToV (ℓ := ℓ) ch'.intoPb,
            if out.isEmpty then none else some (bytesToKey32 out))
        | .error _ => none) := by
  let fLink : ChainEpoch → (spqrEpochLinkT (ℓ := ℓ)).denote := fun lk =>
    (some (spqrDirToV (ℓ := ℓ) lk.send.intoPb),
     some (spqrDirToV (ℓ := ℓ) lk.recv.intoPb))
  have hlks_eq : (spqrChainToV (ℓ := ℓ) ch.intoPb).2.2.1 = ch.links.map fLink := by
    dsimp only [spqrChainToV, Chain.intoPb, fLink]
    rw [List.take_of_length_le (by simpa using hlen4), List.map_map]
    rfl
  have hlks_len : ((spqrChainToV (ℓ := ℓ) ch.intoPb).2.2.1).length = ch.links.length := by
    rw [hlks_eq, List.length_map]
  have hcur_eq : (spqrChainToV (ℓ := ℓ) ch.intoPb).2.1 = ch.currentEpoch := rfl
  have hpar_eq : (spqrChainToV (ℓ := ℓ) ch.intoPb).2.2.2.2.2 =
      some (spqrParamsToV ch.params) := rfl
  generalize hep : epExpr.eval ρ = ep
  generalize hidx : idxExpr.eval ρ = idx
  let ρBase : Env (.prod spqrChainT (.prod U64 U32) :: Γ) :=
    Env.cons (t := .prod spqrChainT (.prod U64 U32))
      (spqrChainToV (ℓ := ℓ) ch.intoPb, (ep, idx)) ρ
  have hbase_eval :
      (Expr.pair (O := e2eOps ℓ P C K decT encT) chExpr (.pair epExpr idxExpr)).eval ρ =
        (spqrChainToV (ℓ := ℓ) ch.intoPb, (ep, idx)) := by
    simp only [Expr.eval, hch, hep, hidx]
  unfold spqrChainRecvKeyComp Chain.recvKey
  rw [comp_eval_bind_ret, hbase_eval]
  have hcond :
      (Expr.and (O := e2eOps ℓ P C K decT encT)
        (e2ePureOp .u64Eq (.pair (.fst (.snd .v0)) (e2ePureOp (.u64Lit 0#64) .unit)))
        (e2ePureOp .u32Eq (.pair (.snd (.snd .v0)) (e2ePureOp (.u32Lit 0#32) .unit)))).eval
        ρBase = (ep == 0#64 && idx == 0#32) := by
    dsimp only [ρBase]
    simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get]
  by_cases hzero : (ep == 0#64 && idx == 0#32) = true
  · rw [comp_eval_ite_true _ _ _ _ (hcond.trans hzero), comp_eval_ret]
    simp [ρBase, Expr.eval, Expr.v0, Env.get, hzero]
  · have hzero_f : (ep == 0#64 && idx == 0#32) = false := Bool.eq_false_iff.mpr hzero
    rw [comp_eval_ite_false _ _ _ _ (hcond.trans hzero_f)]
    simp only [hzero_f, Bool.false_eq_true, ↓reduceIte]
    have heidx :
        (spqrEpochIdxExpr (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
          (.fst (.snd (.fst .v0)))
          (.len (.fst (.snd (.snd (.fst .v0)))))
          (.fst (.snd .v0))).eval ρBase =
          (ch.epochIdx ep).toOption := by
      apply eval_spqrEpochIdxExpr
      · exact hcur_eq
      · simpa [ρBase, Expr.eval, Expr.v0, Env.get] using hlks_len
    cases hepIdx : ch.epochIdx ep with
    | error _ =>
      rw [hepIdx] at heidx
      rw [comp_eval_caseOpt_none _ _ _ _ heidx, comp_eval_ret]
      simp [ChainResult.ofError, Bind.bind, Except.bind, Expr.eval]
    | ok epochIndex =>
      rw [hepIdx] at heidx
      rw [comp_eval_caseOpt_some _ _ _ _ heidx]
      dsimp only [ChainResult.ofError, Bind.bind, Except.bind]
      obtain ⟨hlo, hhi, heq_idx⟩ := crcv_epochIdx_eq hok.hsend_le hok.hlen hepIdx
      obtain ⟨link, hlink_get, hlink_ok⟩ := hok.hrecvDir ep.toNat hlo hhi
      rw [← heq_idx] at hlink_get
      let ρEp : Env (.nat :: .prod spqrChainT (.prod U64 U32) :: Γ) :=
        Env.cons (t := .nat) epochIndex ρBase
      have hget_lk :
          (listGetExpr (O := e2eOps ℓ P C K decT encT) 4 .v0
            (.fst (.snd (.snd (.fst .v1))))).eval ρEp =
            some (fLink link) := by
        rw [eval_listGetExpr (O := e2eOps ℓ P C K decT encT) 4 _ _ ρEp
          (by dsimp only [ρEp, ρBase]; simp only [Expr.eval, Expr.v1, Env.get, hlks_len]; exact hlen4)]
        dsimp only [ρEp, ρBase]
        simp [Expr.eval, Expr.v0, Expr.v1, Env.get, hlks_eq, List.getElem?_map, hlink_get]
      rw [comp_eval_caseOpt_some _ _ _ _ hget_lk, hlink_get]
      dsimp only
      let ρLk : Env (spqrEpochLinkT :: .nat :: .prod spqrChainT (.prod U64 U32) :: Γ) :=
        Env.cons (t := spqrEpochLinkT) (fLink link) ρEp
      have hrecv_opt :
          (Expr.snd (O := e2eOps ℓ P C K decT encT) .v0).eval ρLk =
            some (spqrDirToV (ℓ := ℓ) link.recv.intoPb) := rfl
      rw [comp_eval_caseOpt_some _ _ _ _ hrecv_opt]
      let ρRd : Env (spqrDirT :: spqrEpochLinkT :: .nat :: .prod spqrChainT (.prod U64 U32) :: Γ) :=
        Env.cons (t := spqrDirT) (spqrDirToV (ℓ := ℓ) link.recv.intoPb) ρLk
      have hpar_opt :
          (Expr.snd (O := e2eOps ℓ P C K decT encT)
            (.snd (.snd (.snd (.snd (.fst .v3)))))).eval ρRd =
            some (spqrParamsToV ch.params) := by
        dsimp only [ρRd, ρLk, ρEp, ρBase]
        simp only [Expr.eval, Expr.v3, Env.get, hpar_eq]
      rw [comp_eval_caseOpt_some _ _ _ _ hpar_opt]
      let ρPar : Env (spqrParamsT :: spqrDirT :: spqrEpochLinkT :: .nat ::
          .prod spqrChainT (.prod U64 U32) :: Γ) :=
        Env.cons (t := spqrParamsT) (spqrParamsToV ch.params) ρRd
      have hmj_eval :
          (if decide (0#32 < ch.params.maxJump) = true then ch.params.maxJump else 25000#32) =
            ch.params.maxJumpOrDefault := by
        unfold ChainParamsPB.maxJumpOrDefault CryptoVerification.LibsignalSpqrV1.DEFAULT_CHAIN_PARAMS
        by_cases hc : 0#32 < ch.params.maxJump <;> simp [gt_iff_lt, hc]
      have hmo_eval :
          (if decide (0#32 < ch.params.maxOooKeys) = true then ch.params.maxOooKeys else 2000#32) =
            ch.params.maxOooKeysOrDefault := by
        unfold ChainParamsPB.maxOooKeysOrDefault CryptoVerification.LibsignalSpqrV1.DEFAULT_CHAIN_PARAMS
        by_cases hc : 0#32 < ch.params.maxOooKeys <;> simp [gt_iff_lt, hc]
      have htrim_eval : 11 * ch.params.maxOooKeysOrDefault.toNat / 10 + 1 = ch.params.trimSize := by
        simp [ChainParamsPB.trimSize, Nat.mul_comm]
      let pCfg : BitVec 32 × (BitVec 32 × ℕ) :=
        (ch.params.maxJumpOrDefault, (ch.params.maxOooKeysOrDefault, ch.params.trimSize))
      have hcfg_eval :
          (Expr.letE (O := e2eOps ℓ P C K decT encT)
            (.ite (e2ePureOp .u32Lt
                (.pair (e2ePureOp (.u32Lit 0#32) .unit) (.snd .v0)))
              (.snd .v0)
              (e2ePureOp (.u32Lit 2000#32) .unit))
            (.pair
              (.ite (e2ePureOp .u32Lt
                  (.pair (e2ePureOp (.u32Lit 0#32) .unit) (.fst .v1)))
                (.fst .v1)
                (e2ePureOp (.u32Lit 25000#32) .unit))
              (.pair .v0
                (.add (.divK 10 (.mulK 11 (e2ePureOp .u32ToNat .v0))) (.nat 1))))).eval ρPar =
            pCfg := by
        dsimp only [ρPar, pCfg, spqrParamsToV]
        simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Expr.v1, Env.get,
          hmj_eval, hmo_eval, htrim_eval]
      rw [comp_eval_bind_ret, hcfg_eval]
      let ρDir : Env (.prod U32 (.prod U32 .nat) :: spqrParamsT :: spqrDirT ::
          spqrEpochLinkT :: .nat :: .prod spqrChainT (.prod U64 U32) :: Γ) :=
        Env.cons (t := .prod U32 (.prod U32 .nat)) pCfg ρPar
      have hseed : (seedAt C.F authKey secret dir.switch ep.toNat).length = 32 :=
        length_seedAt C.F authKey secret dir.switch ep.toNat
      have hnext64 : link.recv.next.length ≤ 64 := by
        rw [hlink_ok.hnext, length_nextAt C.F _ hseed]
        decide
      have hlink_mem : link ∈ ch.links := List.mem_of_getElem? hlink_get
      have hprev_le : link.recv.prev.data.length ≤ 79236 := hsmall link hlink_mem
      have hprev_mod : link.recv.prev.data.length % 36 = 0 := recvDirOk_prev_mod36 C.F hlink_ok
      have hmj_le : ch.params.maxJumpOrDefault.toNat ≤ 25000 := by
        rw [hok.hparams, dparams_maxJump]; decide
      have hooo_le : ch.params.maxOooKeysOrDefault.toNat ≤ 2000 := by
        rw [hok.hparams, dparams_maxOoo]; decide
      have hdir := eval_spqrDirKeyComp (Pt := Pt) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) I
        .v2
        (.snd (.snd .v5))
        (.fst .v0)
        (.fst (.snd .v0))
        (.snd (.snd .v0))
        ρDir link.recv ch.params hnext64 hprev_le hprev_mod
        (by dsimp only [ρDir, ρPar, ρRd]; simp [Expr.eval, Expr.v2, Env.get])
        (by dsimp only [ρDir, pCfg]; simp [Expr.eval, Expr.v0, Env.get])
        hmj_le
        (by dsimp only [ρDir, pCfg]; simp [Expr.eval, Expr.v0, Env.get])
        hooo_le
        (by dsimp only [ρDir, pCfg]; simp [Expr.eval, Expr.v0, Env.get])
      have hidx_dir :
          (Expr.snd (O := e2eOps ℓ P C K decT encT) (.snd .v5)).eval ρDir = idx := rfl
      rw [hidx_dir] at hdir
      cases hkey : link.recv.key (spqrHkdfWith C.F) idx ch.params with
      | error _ =>
        rw [hkey] at hdir
        rw [comp_eval_bind_pure _ _ _ _ hdir, comp_eval_caseOpt_none _ _ _ _ rfl, comp_eval_ret]
        rfl
      | ok dOut =>
        rcases dOut with ⟨recv', out⟩
        rw [hkey] at hdir
        obtain ⟨entriesOut, hprev'_eq, hnext'64, hout32, hdir_eval⟩ := hdir
        rw [comp_eval_bind_pure _ _ _ _ hdir_eval, comp_eval_caseOpt_some _ _ _ _ rfl, comp_eval_ret]
        dsimp only [Pure.pure, Except.pure]
        have hout_ne_empty : out.isEmpty = false := by
          cases out with
          | nil => cases hout32
          | cons _ _ => rfl
        rw [hout_ne_empty]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hkey_dp : link.recv.key (spqrHkdfWith C.F) idx dparams = .ok (recv', out) := by
          simpa [hok.hparams] using hkey
        have hprev'_tight : recv'.prev.data.length ≤ 79236 :=
          st_recvPrev_tight C.F hseed hlink_ok hprev_le hkey_dp
        have hentOut_le : entriesOut.length ≤ 2201 := by
          rw [hprev'_eq, length_encodePrevEntries] at hprev'_tight
          omega
        have hdir'_toV :
            spqrDirToV (ℓ := ℓ) recv'.intoPb = (recv'.ctr, (recv'.next, (entriesOut, []))) :=
          spqrDirToV_eq recv'.intoPb hnext'64
            (by
              dsimp only [ChainEpochDirection.intoPb]
              rw [hprev'_eq]
              exact splitSpqrPrev_encodePrevEntries entriesOut hentOut_le)
        let ρSet : Env (.prod spqrDirT BV256 :: .opt (.prod spqrDirT BV256) ::
            .prod U32 (.prod U32 .nat) :: spqrParamsT :: spqrDirT ::
            spqrEpochLinkT :: .nat :: .prod spqrChainT (.prod U64 U32) :: Γ) :=
          Env.cons (t := .prod spqrDirT BV256)
            ((recv'.ctr, (recv'.next, (entriesOut, []))), bytesToKey32 out)
            (Env.cons (t := .opt (.prod spqrDirT BV256))
              (some ((recv'.ctr, (recv'.next, (entriesOut, []))), bytesToKey32 out)) ρDir)
        have hset_eval :
            (listSetExpr (O := e2eOps ℓ P C K decT encT) 4 .v6
              (.pair (.fst .v5) (.some (.fst .v0)))
              (.fst (.snd (.snd (.fst
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))).eval ρSet =
              (ch.links.set epochIndex { link with recv := recv' }).map fLink := by
          rw [eval_listSetExpr (O := e2eOps ℓ P C K decT encT) 4 _ _ _ ρSet
            (by
              dsimp only [ρSet, ρDir, ρPar, ρRd, ρLk, ρEp, ρBase]
              simp only [Expr.eval, Env.get, hlks_len]
              exact hlen4)]
          dsimp only [ρSet, ρDir, ρPar, ρRd, ρLk, ρEp, ρBase, fLink]
          simp only [Expr.eval, Expr.v0, Expr.v5, Expr.v6, Env.get, hlks_eq, List.map_set,
            ← hdir'_toV]
          rfl
        dsimp only [ρSet] at hset_eval
        simp only [Expr.eval, hset_eval]
        dsimp only [ρDir, ρPar, ρRd, ρLk, ρEp, ρBase, pCfg, fLink, Expr.v0, Env.get]
        apply congrArg PFunctor.FreeM.pure
        apply congrArg some
        refine Prod.ext ?_ rfl
        have hlen_set : (ch.links.set epochIndex { link with recv := recv' }).length ≤ 4 := by
          rw [List.length_set]; exact hlen4
        have hlks_out :
            (spqrChainToV (ℓ := ℓ)
              ({ ch with links := ch.links.set epochIndex { link with recv := recv' } } : Chain).intoPb).2.2.1 =
              (ch.links.set epochIndex { link with recv := recv' }).map fLink := by
          dsimp only [spqrChainToV, Chain.intoPb, fLink]
          rw [List.take_of_length_le (by simpa using hlen_set), List.map_map]
          rfl
        refine Prod.ext rfl (Prod.ext rfl (Prod.ext hlks_out.symm rfl))

/-! ## Cost bounds -/

theorem cost_spqrPrevGetExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (tail : Expr (e2eOps ℓ P C K decT encT) Γ (B 35))
    (atIdx curCtr maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (spqrPrevGetExpr entries tail atIdx curCtr maxOoo).cost ≤
      entries.cost + tail.cost + atIdx.cost + curCtr.cost + maxOoo.cost + 170000 := by
  let argsT : Ty (e2eSig ℓ) :=
    .prod (.prod (.list spqrPrevEntryT) (B 35)) (.prod U32 (.prod U32 U32))
  let Γg : List (Ty (e2eSig ℓ)) :=
    .nat :: .prod .nat BV256 :: .opt (.prod .nat BV256) :: argsT :: Γ
  let Γs : List (Ty (e2eSig ℓ)) := spqrPrevEntryT :: Γg
  have hcGet := cost_listGetExpr (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) (Γ := Γg)
    (t := spqrPrevEntryT) 2201 .v0 (.fst (.fst .v3))
  have hcSet := cost_listSetExpr (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) (Γ := Γs)
    (t := spqrPrevEntryT) 2201 (.fst .v2) .v0 (.fst (.fst .v4))
  have hb1 : bits 1 = 1 := by decide
  have hb2201 : bits 2201 = 12 := by decide
  have hp35 : ((35 : ℕ+) : ℕ) = 35 := rfl
  dsimp only [Γg, Γs, argsT] at hcGet hcSet
  simp only [Expr.cost, Expr.v0, Expr.v2, Expr.v3, Expr.v4, hb2201] at hcGet hcSet
  simp only [spqrPrevGetExpr, spqrPrevGetFuelExpr, Expr.cost, cost_e2ePureOp, E2EPureOp.cost, hp35,
    List.length_nil, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, hb1, hb2201]
  omega

theorem cost_spqrPrevGcExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (curKey maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    (spqrPrevGcExpr entries curKey maxOoo trimSize).cost ≤
      entries.cost + curKey.cost + maxOoo.cost + trimSize.cost + 2190000 := by
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb4201 : bits 4201 = 13 := by decide
  simp only [spqrPrevGcExpr, spqrPrevGcFuelExpr, Expr.cost, cost_e2ePureOp, E2EPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, hb0, hb1, hb4201]
  omega

theorem cost_spqrKeyAdvanceComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (ctr0 : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (next0 : Expr (e2eOps ℓ P C K decT encT) Γ (B 32))
    (entries0 : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (atIdx maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (spqrKeyAdvanceComp I ctr0 next0 entries0 atIdx maxOoo).cost ≤
      ctr0.cost + next0.cost + entries0.cost + atIdx.cost + maxOoo.cost + 1775000 := by
  let argsT : Ty (e2eSig ℓ) :=
    .prod (.prod U32 (B 32)) (.prod (.list spqrPrevEntryT) (.prod U32 U32))
  let accT : Ty (e2eSig ℓ) :=
    .prod .nat (.prod (.list spqrPrevEntryT) (.prod (B 32) U32))
  let Γr : List (Ty (e2eSig ℓ)) := accT :: .prod .nat .nat :: argsT :: Γ
  have hcRev := cost_spqrListRevExpr (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) (Γ := Γr)
    (t := spqrPrevEntryT) 2000
    (.pair (e2ePureOp (.u32Lit 0#32) .unit) (e2ePureOp (.bv256Lit 0#256) .unit))
    (.fst (.snd .v0))
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb2000 : bits 2000 = 11 := by decide
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  dsimp only [Γr, accT, argsT] at hcRev
  simp only [Expr.cost, cost_e2ePureOp, E2EPureOp.cost, Expr.v0, hb2000] at hcRev
  simp only [spqrKeyAdvanceComp, spqrKeyAdvanceFuelComp, spqrKeyAdvanceStep, Comp.cost,
    cost_spqrChainNextKeyC, Expr.cost, cost_e2ePureOp, E2EPureOp.cost, hp32,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, hb0, hb1, hb32]
  omega

private theorem cost_spqrDirKeyFwdComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (ctr0 : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (next0 : Expr (e2eOps ℓ P C K decT encT) Γ (B 32))
    (entriesInit : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (atIdx maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    (spqrDirKeyFwdComp I ctr0 next0 entriesInit atIdx maxOoo trimSize).cost ≤
      ctr0.cost + next0.cost + entriesInit.cost + atIdx.cost + maxOoo.cost + trimSize.cost +
        3966000 := by
  let argsT : Ty (e2eSig ℓ) :=
    .prod (.prod U32 (B 32)) (.prod (.list spqrPrevEntryT) (.prod U32 (.prod U32 .nat)))
  let advT : Ty (e2eSig ℓ) := .prod U32 (.prod (B 32) (.list spqrPrevEntryT))
  let Γ0 : List (Ty (e2eSig ℓ)) := argsT :: Γ
  let Γ2 : List (Ty (e2eSig ℓ)) := advT :: .opt advT :: Γ0
  have hcAdv := cost_spqrKeyAdvanceComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ0) I
    (.fst (.fst .v0))
    (.snd (.fst .v0))
    (.fst (.snd .v0))
    (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0))))
  have hcGc := cost_spqrPrevGcExpr (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ2)
    (.snd (.snd .v0))
    (.fst .v0)
    (.fst (.snd (.snd (.snd .v2))))
    (.snd (.snd (.snd (.snd .v2))))
  have hp35 : ((35 : ℕ+) : ℕ) = 35 := rfl
  dsimp only [Γ0, Γ2, argsT, advT] at hcAdv hcGc
  simp only [Expr.cost, Expr.v0, Expr.v2] at hcAdv hcGc
  simp only [spqrDirKeyFwdComp, Comp.cost, cost_spqrChainNextKeyC, Expr.cost, cost_e2ePureOp,
    E2EPureOp.cost, hp35, List.length_nil, Expr.v0, Expr.v1, Expr.v2]
  omega

theorem cost_spqrDirKeyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (recvDir : Expr (e2eOps ℓ P C K decT encT) Γ spqrDirT)
    (atIdx maxJump maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize).cost ≤
      recvDir.cost + atIdx.cost + maxJump.cost + maxOoo.cost + trimSize.cost + 3970000 := by
  let argsT : Ty (e2eSig ℓ) := .prod spqrDirT (.prod U32 (.prod U32 (.prod U32 .nat)))
  let Γ0 : List (Ty (e2eSig ℓ)) := argsT :: Γ
  have hcGet := cost_spqrPrevGetExpr (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ0)
    (.fst (.snd (.snd (.fst .v0))))
    (.snd (.snd (.snd (.fst .v0))))
    (.fst (.snd .v0))
    (.fst (.fst .v0))
    (.fst (.snd (.snd (.snd .v0))))
  have hcFwd := cost_spqrDirKeyFwdComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ0) I
    (.fst (.fst .v0))
    (.fst (.snd (.fst .v0)))
    (.ite (e2ePureOp .u32Lt
        (.pair (e2ePureOp .u32Add (.pair (.fst (.fst .v0)) (.fst (.snd (.snd (.snd .v0))))))
          (.fst (.snd .v0))))
      .nil
      (.fst (.snd (.snd (.fst .v0)))))
    (.fst (.snd .v0))
    (.fst (.snd (.snd (.snd .v0))))
    (.snd (.snd (.snd (.snd .v0))))
  have hp35 : ((35 : ℕ+) : ℕ) = 35 := rfl
  dsimp only [Γ0, argsT] at hcGet hcFwd
  simp only [Expr.cost, cost_e2ePureOp, E2EPureOp.cost, Expr.v0] at hcGet hcFwd
  simp only [spqrDirKeyComp, Comp.cost, Expr.cost, cost_e2ePureOp,
    E2EPureOp.cost, hp35, List.length_nil, Expr.v0, Expr.v1]
  omega

theorem cost_spqrChainRecvKeyComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (index : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (spqrChainRecvKeyComp I ch epoch index).cost ≤
      ch.cost + epoch.cost + index.cost + 3980000 := by
  let baseT : Ty (e2eSig ℓ) := .prod spqrChainT (.prod U64 U32)
  let Γ0 : List (Ty (e2eSig ℓ)) := baseT :: Γ
  let Γ1 : List (Ty (e2eSig ℓ)) := .nat :: Γ0
  let Γ5 : List (Ty (e2eSig ℓ)) :=
    .prod U32 (.prod U32 .nat) :: spqrParamsT :: spqrDirT :: spqrEpochLinkT :: Γ1
  let Γ7 : List (Ty (e2eSig ℓ)) :=
    .prod spqrDirT BV256 :: .opt (.prod spqrDirT BV256) :: Γ5
  have hcEp := cost_spqrEpochIdxExpr (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ0)
    (.fst (.snd (.fst .v0))) (.len (.fst (.snd (.snd (.fst .v0))))) (.fst (.snd .v0))
  have hcGet := cost_listGetExpr (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) (Γ := Γ1)
    (t := spqrEpochLinkT) 4 .v0 (.fst (.snd (.snd (.fst .v1))))
  have hcDir := cost_spqrDirKeyComp (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ5) I
    .v2 (.snd (.snd .v5)) (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hcSet := cost_listSetExpr (ℓ := ℓ) (O := e2eOps ℓ P C K decT encT) (Γ := Γ7)
    (t := spqrEpochLinkT) 4 .v6 (.pair (.fst .v5) (.some (.fst .v0)))
    (.fst (.snd (.snd (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
  have hb1 : bits 1 = 1 := by decide
  have hb4 : bits 4 = 3 := by decide
  have hb10 : bits 10 = 4 := by decide
  have hb11 : bits 11 = 4 := by decide
  dsimp only [Γ0, Γ1, Γ5, Γ7, baseT] at hcEp hcGet hcDir hcSet
  simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v5, Expr.v6, hb4] at hcEp hcGet hcDir hcSet
  simp only [spqrChainRecvKeyComp, Comp.cost, Expr.cost, cost_e2ePureOp, E2EPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5, Expr.v6, hb1, hb10, hb11]
  omega

end Computational.Proofs.E2E.Dsl.SpqrSimHist
