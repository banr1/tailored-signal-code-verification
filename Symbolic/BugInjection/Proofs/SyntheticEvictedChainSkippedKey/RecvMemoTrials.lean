/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBuckets
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTermAt
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrialsData0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrialsData1

/-!
# Receiver Trial `SafeMemo` Witness Bridge

Assembles `trialRowTree` from `trialSubTree0` and `trialSubTree1` and verifies by kernel
computation (`all_seed_entries_ok`) that each `(nSalts, seed, pIk, mIk, wire)` tuple in
`allSeedEntries` maps its `trMsgKeys` and `computeMac` nodes into the DAG. Lifts a matching tuple
to `SafeMemo` across `trialTerms salts msg ctx` (`safeMemo_of_seedTrialOk`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrials

open DY (Bytes)
open DY.Libsignal.TripleRatchet (TRSignalMsg trMsgKeys computeMac)
open DY.Libsignal.Composed.Refinement (OpaqueSymbolSemantics Ghost TrialCtx trialTerms)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs (DagOp)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree (BinTree btGet)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagSize dagOp dagBytes wmkInfo1Id wmkInfo2Id wmkInfo3Id honestSaltIds)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagBuckets (dag_nodes_ok)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators
  (SafeMemo TermAt)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTermAt
  (termAt_lit termAt_concat termAt_trMsgKeys termAt_computeMac safeMemo_trialTerms)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrialsData0
  (TrialRow defaultTrialRow trialSubTree0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrialsData1
  (trialSubTree1)

def trialRowTree : BinTree TrialRow := .branch trialSubTree0 trialSubTree1

def getTrialRow (ri : Nat) : TrialRow :=
  (btGet 10 trialRowTree ri).getD defaultTrialRow

def isKdfOp (op : DagOp) (a b : Nat) : Bool :=
  match op with | .kdf x y => decide (x = a) && decide (y = b) | _ => false

def isConcatOp (op : DagOp) (l r : Nat) : Bool :=
  match op with | .concat x y => decide (x = l) && decide (y = r) | _ => false

def isTrunc8Op (op : DagOp) (a : Nat) : Bool :=
  match op with | .trunc8 x => decide (x = a) | _ => false

def isLitOp (op : DagOp) (v : DY.Libsignal.HwBytes) : Bool :=
  match op with | .lit x => decide (x = v) | _ => false

def trialRowMatches (salt seed pIk mIk wire : Nat) (r : TrialRow) : Bool :=
  decide (r.salt = salt) && decide (r.seed = seed) &&
  decide (r.pIk = pIk) && decide (r.mIk = mIk) && decide (r.wire = wire) &&
  decide (r.prk < dagSize) && isKdfOp (dagOp r.prk) salt seed &&
  decide (r.ck < dagSize) && isKdfOp (dagOp r.ck) r.prk wmkInfo1Id &&
  decide (r.c2 < dagSize) && isConcatOp (dagOp r.c2) r.ck wmkInfo2Id &&
  decide (r.mkId < dagSize) && isKdfOp (dagOp r.mkId) r.prk r.c2 &&
  decide (r.c3 < dagSize) && isConcatOp (dagOp r.c3) r.mkId wmkInfo3Id &&
  decide (r.iv < dagSize) && isKdfOp (dagOp r.iv) r.prk r.c3 &&
  decide (r.miR < dagSize) && isConcatOp (dagOp r.miR) mIk wire &&
  decide (r.mi < dagSize) && isConcatOp (dagOp r.mi) pIk r.miR &&
  decide (r.fmac < dagSize) && isKdfOp (dagOp r.fmac) r.mkId r.mi &&
  decide (r.mac < dagSize) && isTrunc8Op (dagOp r.mac) r.fmac

/-- Witness tuple `(nSalts, seed_id, pIk_id, mIk_id, wire_id, rowIndices)` for receiver-trial DAG nodes. -/
abbrev SeedEntry := Nat × Nat × Nat × Nat × Nat × List Nat

def seedEntryOk (e : SeedEntry) : Bool :=
  let (nSalts, seed, pIk, mIk, wire, ris) := e
  decide (ris.map (fun ri => (getTrialRow ri).salt) = honestSaltIds.take nSalts) &&
  ris.all (fun ri => trialRowMatches (getTrialRow ri).salt seed pIk mIk wire (getTrialRow ri))

def allSeedEntries : List SeedEntry := [
  (3, 124, 30, 31, 133, [0, 1, 2]),
  (4, 169, 31, 30, 178, [3, 4, 5, 6]),
  (4, 213, 30, 31, 178, [7, 8, 9, 10]),
  (5, 282, 31, 30, 271, [11, 12, 13, 14, 15]),
  (5, 262, 30, 31, 271, [16, 17, 18, 19, 20]),
  (5, 363, 31, 30, 271, [21, 22, 23, 24, 25]),
  (6, 438, 31, 30, 427, [26, 27, 28, 29, 30, 31]),
  (6, 493, 30, 31, 427, [32, 33, 34, 35, 36, 37]),
  (6, 418, 31, 30, 427, [38, 39, 40, 41, 42, 43]),
  (6, 590, 30, 31, 427, [44, 45, 46, 47, 48, 49]),
  (7, 673, 31, 30, 662, [50, 51, 52, 53, 54, 55, 56]),
  (7, 738, 30, 31, 662, [57, 58, 59, 60, 61, 62, 63]),
  (7, 801, 31, 30, 662, [64, 65, 66, 67, 68, 69, 70]),
  (7, 653, 30, 31, 662, [71, 72, 73, 74, 75, 76, 77]),
  (7, 912, 31, 30, 662, [78, 79, 80, 81, 82, 83, 84]),
  (8, 1003, 31, 30, 992, [85, 86, 87, 88, 89, 90, 91, 92]),
  (8, 1074, 30, 31, 992, [93, 94, 95, 96, 97, 98, 99, 100]),
  (8, 1147, 31, 30, 992, [101, 102, 103, 104, 105, 106, 107, 108]),
  (8, 1218, 30, 31, 992, [109, 110, 111, 112, 113, 114, 115, 116]),
  (8, 983, 31, 30, 992, [117, 118, 119, 120, 121, 122, 123, 124]),
  (8, 1345, 30, 31, 992, [125, 126, 127, 128, 129, 130, 131, 132]),
  (9, 1444, 31, 30, 1433, [133, 134, 135, 136, 137, 138, 139, 140, 141]),
  (9, 1525, 30, 31, 1433, [142, 143, 144, 145, 146, 147, 148, 149, 150]),
  (9, 1604, 31, 30, 1433, [151, 152, 153, 154, 155, 156, 157, 158, 159]),
  (9, 1683, 30, 31, 1433, [160, 161, 162, 163, 164, 165, 166, 167, 168]),
  (9, 1762, 31, 30, 1433, [169, 170, 171, 172, 173, 174, 175, 176, 177]),
  (9, 1424, 30, 31, 1433, [178, 179, 180, 181, 182, 183, 184, 185, 186]),
  (9, 1905, 31, 30, 1433, [187, 188, 189, 190, 191, 192, 193, 194, 195]),
  (10, 2012, 31, 30, 2001, [196, 197, 198, 199, 200, 201, 202, 203, 204, 205]),
  (10, 2099, 30, 31, 2001, [206, 207, 208, 209, 210, 211, 212, 213, 214, 215]),
  (10, 2188, 31, 30, 2001, [216, 217, 218, 219, 220, 221, 222, 223, 224, 225]),
  (10, 2275, 30, 31, 2001, [226, 227, 228, 229, 230, 231, 232, 233, 234, 235]),
  (10, 2362, 31, 30, 2001, [236, 237, 238, 239, 240, 241, 242, 243, 244, 245]),
  (10, 2449, 30, 31, 2001, [246, 247, 248, 249, 250, 251, 252, 253, 254, 255]),
  (10, 1992, 31, 30, 2001, [256, 257, 258, 259, 260, 261, 262, 263, 264, 265]),
  (10, 2608, 30, 31, 2001, [266, 267, 268, 269, 270, 271, 272, 273, 274, 275]),
  (11, 2723, 31, 30, 2712, [276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286]),
  (11, 2820, 30, 31, 2712, [287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297]),
  (11, 2915, 31, 30, 2712, [298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308]),
  (11, 3010, 30, 31, 2712, [309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]),
  (11, 3105, 31, 30, 2712, [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330]),
  (11, 3200, 30, 31, 2712, [331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341]),
  (11, 3295, 31, 30, 2712, [342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352]),
  (11, 2703, 30, 31, 2712, [353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363]),
  (11, 3470, 31, 30, 2712, [364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374]),
  (12, 3593, 31, 30, 3582, [375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386]),
  (12, 3696, 30, 31, 3582, [387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398]),
  (12, 3801, 31, 30, 3582, [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410]),
  (12, 3904, 30, 31, 3582, [411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422]),
  (12, 4007, 31, 30, 3582, [423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434]),
  (12, 4110, 30, 31, 3582, [435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446]),
  (12, 4213, 31, 30, 3582, [447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458]),
  (12, 4316, 30, 31, 3582, [459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470]),
  (12, 3573, 31, 30, 3582, [471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482]),
  (12, 4507, 30, 31, 3582, [483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494]),
  (13, 4638, 31, 30, 4627, [495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507]),
  (13, 4751, 30, 31, 4627, [508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520]),
  (13, 4862, 31, 30, 4627, [521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533]),
  (13, 4973, 30, 31, 4627, [534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546]),
  (13, 5084, 31, 30, 4627, [547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]),
  (13, 5195, 30, 31, 4627, [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572]),
  (13, 5306, 31, 30, 4627, [573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585]),
  (13, 5417, 30, 31, 4627, [586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598]),
  (13, 5528, 31, 30, 4627, [599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611]),
  (13, 4618, 30, 31, 4627, [612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624]),
  (13, 5735, 31, 30, 4627, [625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637]),
  (13, 5855, 31, 30, 113, [638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650]),
  (13, 104, 30, 31, 113, [651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663]),
  (13, 6063, 31, 30, 113, [664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676]),
  (13, 6173, 31, 30, 113, [677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689]),
  (13, 6283, 31, 30, 113, [690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702]),
  (13, 6393, 31, 30, 113, [703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715]),
  (13, 6503, 31, 30, 113, [716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728]),
  (13, 6614, 30, 31, 113, [729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741])
]

def allSeedTuples : List (Nat × Nat × Nat × Nat × Nat) :=
  allSeedEntries.map fun (n, sd, p, m, w, _) => (n, sd, p, m, w)

def seedEntriesSliceOk (lo count : Nat) : Bool :=
  ((allSeedEntries.drop lo).take count).all seedEntryOk

private theorem seedEntryOk_of_slice {lo count : Nat} (h : seedEntriesSliceOk lo count = true)
    {idx : Nat} (hlo : lo ≤ idx) (hhi : idx < lo + count) {e : SeedEntry}
    (he : allSeedEntries[idx]? = some e) : seedEntryOk e = true := by
  unfold seedEntriesSliceOk at h
  have hsub : ((allSeedEntries.drop lo).take count)[idx - lo]? = some e := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_cancel' hlo, he]
  exact List.all_eq_true.mp h e (List.mem_of_getElem? hsub)

private theorem seedSlice_0 : seedEntriesSliceOk 0 25 = true := by decide +kernel
private theorem seedSlice_1 : seedEntriesSliceOk 25 25 = true := by decide +kernel
private theorem seedSlice_2 : seedEntriesSliceOk 50 24 = true := by decide +kernel

theorem all_seed_entries_ok : ∀ e ∈ allSeedEntries, seedEntryOk e = true := by
  intro e he
  obtain ⟨idx, hlt, hget⟩ := List.getElem_of_mem he
  have heq : allSeedEntries[idx]? = some e := by rw [List.getElem?_eq_getElem hlt, hget]
  have hlen : allSeedEntries.length = 74 := rfl
  rw [hlen] at hlt
  if hs0 : idx < 25 then
    exact seedEntryOk_of_slice seedSlice_0 (by omega) hs0 heq
  else
  if hs1 : idx < 50 then
    exact seedEntryOk_of_slice seedSlice_1 (by omega) hs1 heq
  else
    exact seedEntryOk_of_slice seedSlice_2 (by omega) hlt heq

private theorem kdf_of_isKdfOp {op : DagOp} {a b : Nat} (h : isKdfOp op a b = true) :
    op = .kdf a b := by
  cases op <;> simp [isKdfOp] at h; obtain ⟨rfl, rfl⟩ := h; rfl

private theorem concat_of_isConcatOp {op : DagOp} {l r : Nat} (h : isConcatOp op l r = true) :
    op = .concat l r := by
  cases op <;> simp [isConcatOp] at h; obtain ⟨rfl, rfl⟩ := h; rfl

private theorem trunc8_of_isTrunc8Op {op : DagOp} {a : Nat} (h : isTrunc8Op op a = true) :
    op = .trunc8 a := by
  cases op <;> simp [isTrunc8Op] at h; subst h; rfl

private theorem lit_of_isLitOp {op : DagOp} {v : DY.Libsignal.HwBytes} (h : isLitOp op v = true) :
    op = .lit v := by
  cases op <;> simp [isLitOp] at h; subst h; rfl

theorem termAt_strLit {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {s : String} {id : Nat} (hid : id < dagSize)
    (hop : isLitOp (dagOp id) (DY.Libsignal.Composed.Refinement.ofByteArray s.toList.utf8Encode) = true) :
    TermAt dagSize dagOp dagBytes S g pts (DY.Libsignal.TripleRatchet.lit s) id := by
  have hs : s.toUTF8 = s.toList.utf8Encode := by
    conv_lhs => rw [← String.ofList_toList (s := s)]
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  exact termAt_lit dag_nodes_ok hid (by rw [hs]; exact lit_of_isLitOp hop)

theorem wmkInfo_termAt (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes) :
    TermAt dagSize dagOp dagBytes S g pts
      (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
        (DY.Libsignal.TripleRatchet.litByte 1)) wmkInfo1Id ∧
    TermAt dagSize dagOp dagBytes S g pts
      (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
        (DY.Libsignal.TripleRatchet.litByte 2)) wmkInfo2Id ∧
    TermAt dagSize dagOp dagBytes S g pts
      (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
        (DY.Libsignal.TripleRatchet.litByte 3)) wmkInfo3Id := by
  have hl : TermAt dagSize dagOp dagBytes S g pts
      (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") 11 :=
    termAt_strLit (by decide) (by decide +kernel)
  have hb1 : TermAt dagSize dagOp dagBytes S g pts
      (DY.Libsignal.TripleRatchet.litByte 1) 2 :=
    termAt_lit dag_nodes_ok (by decide) (lit_of_isLitOp (by decide +kernel))
  have hb2 : TermAt dagSize dagOp dagBytes S g pts
      (DY.Libsignal.TripleRatchet.litByte 2) 3 :=
    termAt_lit dag_nodes_ok (by decide) (lit_of_isLitOp (by decide +kernel))
  have hb3 : TermAt dagSize dagOp dagBytes S g pts
      (DY.Libsignal.TripleRatchet.litByte 3) 4 :=
    termAt_lit dag_nodes_ok (by decide) (lit_of_isLitOp (by decide +kernel))
  exact ⟨termAt_concat dag_nodes_ok (by decide) (concat_of_isConcatOp (by decide +kernel)) hl hb1,
         termAt_concat dag_nodes_ok (by decide) (concat_of_isConcatOp (by decide +kernel)) hl hb2,
         termAt_concat dag_nodes_ok (by decide) (concat_of_isConcatOp (by decide +kernel)) hl hb3⟩

theorem safeMemo_of_trialRowMatches {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {salt seed pIk mIk wire : Bytes} {salt_id seed_id pIk_id mIk_id wire_id : Nat}
    {row : TrialRow}
    (hrow : trialRowMatches salt_id seed_id pIk_id mIk_id wire_id row = true)
    (hsalt : TermAt dagSize dagOp dagBytes S g pts salt salt_id)
    (hseed : TermAt dagSize dagOp dagBytes S g pts seed seed_id)
    (hpIk : TermAt dagSize dagOp dagBytes S g pts pIk pIk_id)
    (hmIk : TermAt dagSize dagOp dagBytes S g pts mIk mIk_id)
    (hwire : TermAt dagSize dagOp dagBytes S g pts wire wire_id) :
    SafeMemo dagSize dagOp dagBytes S g pts (trMsgKeys salt seed).cipherKey ∧
    SafeMemo dagSize dagOp dagBytes S g pts (trMsgKeys salt seed).macKey ∧
    SafeMemo dagSize dagOp dagBytes S g pts (trMsgKeys salt seed).iv ∧
    SafeMemo dagSize dagOp dagBytes S g pts
      (computeMac (trMsgKeys salt seed).macKey pIk mIk wire) := by
  unfold trialRowMatches at hrow
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩,
    hprk_lt⟩, hprk_op⟩, hck_lt⟩, hck_op⟩, hc2_lt⟩, hc2_op⟩, hmk_lt⟩, hmk_op⟩,
    hc3_lt⟩, hc3_op⟩, hiv_lt⟩, hiv_op⟩, hmiR_lt⟩, hmiR_op⟩, hmi_lt⟩, hmi_op⟩,
    hfmac_lt⟩, hfmac_op⟩, hmac_lt⟩, hmac_op⟩ := hrow
  obtain ⟨hi1, hi2, hi3⟩ := wmkInfo_termAt S g pts
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys dag_nodes_ok hi1 hi2 hi3
    ⟨hprk_lt, kdf_of_isKdfOp hprk_op⟩ ⟨hck_lt, kdf_of_isKdfOp hck_op⟩
    ⟨hc2_lt, concat_of_isConcatOp hc2_op⟩ ⟨hmk_lt, kdf_of_isKdfOp hmk_op⟩
    ⟨hc3_lt, concat_of_isConcatOp hc3_op⟩ ⟨hiv_lt, kdf_of_isKdfOp hiv_op⟩ hsalt hseed
  have tmac := termAt_computeMac dag_nodes_ok
    ⟨hmiR_lt, concat_of_isConcatOp hmiR_op⟩ ⟨hmi_lt, concat_of_isConcatOp hmi_op⟩
    ⟨hfmac_lt, kdf_of_isKdfOp hfmac_op⟩ ⟨hmac_lt, trunc8_of_isTrunc8Op hmac_op⟩
    tmk hpIk hmIk hwire
  exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩

theorem safeMemo_of_seedTrialOk {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {salts : List Bytes} {msg : TRSignalMsg} {ctx : TrialCtx}
    {nSalts seed_id pIk_id mIk_id wire_id : Nat}
    (htup : (nSalts, seed_id, pIk_id, mIk_id, wire_id) ∈ allSeedTuples)
    (hsalts : ∀ salt ∈ salts, ∃ s_id ∈ honestSaltIds.take nSalts,
      TermAt dagSize dagOp dagBytes S g pts salt s_id)
    (hextra : ∀ t ∈ ctx.extra, SafeMemo dagSize dagOp dagBytes S g pts t)
    (hct : SafeMemo dagSize dagOp dagBytes S g pts msg.ciphertext)
    (hpIk : TermAt dagSize dagOp dagBytes S g pts ctx.peerIk pIk_id)
    (hmIk : TermAt dagSize dagOp dagBytes S g pts ctx.myIk mIk_id)
    (hwire : TermAt dagSize dagOp dagBytes S g pts msg.wire wire_id)
    (hseed : ∀ seed, ctx.seed? = some seed →
      TermAt dagSize dagOp dagBytes S g pts seed seed_id) :
    ∀ t ∈ trialTerms salts msg ctx, SafeMemo dagSize dagOp dagBytes S g pts t := by
  unfold allSeedTuples at htup
  obtain ⟨⟨n', sd', p', m', w', ris⟩, hent, heq⟩ := List.mem_map.mp htup
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
  have hok := all_seed_entries_ok _ hent
  unfold seedEntryOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hmap, hall⟩ := hok
  refine safeMemo_trialTerms hextra hct (fun seed hs salt hsalt_mem => ?_)
  obtain ⟨s_id, hs_mem, tsalt⟩ := hsalts salt hsalt_mem
  rw [← hmap] at hs_mem
  obtain ⟨ri, hri_mem, rfl⟩ := List.mem_map.mp hs_mem
  have hrow := List.all_eq_true.mp hall ri hri_mem
  exact safeMemo_of_trialRowMatches hrow tsalt (hseed seed hs) hpIk hmIk hwire

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrials
