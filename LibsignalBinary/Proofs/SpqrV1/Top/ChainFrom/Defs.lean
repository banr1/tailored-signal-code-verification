/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Defs
import ProofLib.VCGen

/-!
# Specifications for `spqr::chain_from` (`0x531ac`) and `<Chain>::from_pb` (`0x60074`)

Protobuf layout predicates (`epochDirectionPBAt`, `chainEpochPBAt`, `chainPBAt`, `optChainPBAt`,
`optVersionNegotiationRefAt`) and contracts (`chainFromPbSpecX`, `chainFromSpecX`, `chainFromSpecExt`)
against pure `chainFrom`.

Note: `spqr::decode_varint` and `spqr::msg_preamble` are inlined into `spqr::recv` (`0x5462c`) in
`Computational/docs/spqr_v1/closure.txt`; their binary and pure equivalences are verified in
`SpqrRecvEmpty/Proof.lean` and `LibsignalSpqrV1/Wire.lean`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.ChainFrom

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

/-! ## Symbol names and stack budgets -/

/-- `spqr::chain_from` (`src/lib.rs:342–353`, image offset `0x531ac`, 76 instructions). -/
abbrev chainFromName : String :=
  "spqr::chain_from"

/-- `<spqr::chain::Chain>::from_pb` (`src/chain.rs:444–462`, image offset `0x60074`, 347 instructions). -/
abbrev chainFromPbName : String :=
  "<spqr::chain::Chain>::from_pb"

/-- `<spqr::chain::Chain>::from_pb` frame (`0xc0 = 192` B) + `chainNewStackX` (`224 + extHookStack`). -/
abbrev chainFromPbStackX : Nat := 192 + chainNewStackX

/-- `spqr::chain_from` frame (`0x90 = 144` B) + `chainFromPbStackX`. -/
abbrev chainFromStackX : Nat := 144 + chainFromPbStackX

/-! ## Protobuf layouts for `pqrpb::Chain` (`ChainPB`, 80 bytes = `0x50`) -/

/-- Ghost pins for `pqrpb::chain::epoch::EpochDirection` (`EpochDirectionPB`, 56 bytes),
    unified with `CryptoVerification.SpqrV1.ProtoRepr.EpochDirectionPBGhost`. -/
abbrev EpochDirectionPBGhost := CryptoVerification.SpqrV1.ProtoRepr.EpochDirectionPBGhost

/-- Ghost pins for `pqrpb::chain::Epoch` (`ChainEpochPB`, 112 bytes),
    unified with `CryptoVerification.SpqrV1.ProtoRepr.ChainEpochPBGhost`. -/
abbrev ChainEpochPBGhost := CryptoVerification.SpqrV1.ProtoRepr.ChainEpochPBGhost

/-- Ghost pins for `pqrpb::Chain` (`ChainPB`, 80 bytes), including per-epoch `VecPin`s
    `epochs : List ChainEpochPBGhost` alongside top-level `links` and `nextRoot` pins. -/
structure ChainPBGhost where
  linksCap : BitVec 64
  linksPtr : BitVec 64
  epochs : List ChainEpochPBGhost
  nextRoot : VecPin

/-- Forget the per-epoch `VecPin`s of `g : ChainPBGhost` to obtain the top-level
    `ProtoRepr.ChainPBGhost` (`{ links := ⟨g.linksCap, g.linksPtr⟩, nextRoot := ⟨g.nextRoot.cap, g.nextRoot.ptr⟩ }`). -/
def ChainPBGhost.toProtoRepr (g : ChainPBGhost) : CryptoVerification.SpqrV1.ProtoRepr.ChainPBGhost :=
  { links := ⟨g.linksCap, g.linksPtr⟩, nextRoot := ⟨g.nextRoot.cap, g.nextRoot.ptr⟩ }

/-- `pqrpb::chain::epoch::EpochDirection` (`EpochDirectionPB`) at `a` (56 bytes = `0x38`, align 8),
    unified with `CryptoVerification.SpqrV1.ProtoRepr.epochDirectionPBPinnedAt`:
- `+0x00..+0x18` (24B): `next: Vec<u8>`
- `+0x18..+0x30` (24B): `prev: Vec<u8>`
- `+0x30..+0x34` (4B): `ctr: u32`
- `+0x34..+0x38` (4B): 4-byte padding (`memRegion`) -/
abbrev epochDirectionPBAt := CryptoVerification.SpqrV1.ProtoRepr.epochDirectionPBPinnedAt

/-- `Option<pqrpb::chain::epoch::EpochDirection>` at `a` (56 bytes = `0x38`, align 8),
    unified with `CryptoVerification.SpqrV1.ProtoRepr.optEpochDirectionPBPinnedAt`:
niche-encoded in `next.cap` at `+0x00` (`noneCap = 0xFFFFFFFFFFFFFFFF#64` for `none`). -/
abbrev optEpochDirectionPBAt := CryptoVerification.SpqrV1.ProtoRepr.optEpochDirectionPBPinnedAt

/-- `pqrpb::chain::Epoch` (`ChainEpochPB`) at `a` (112 bytes = `0x70`, align 8),
    unified with `CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBPinnedAt`:
- `+0x00..+0x38` (56B): `send: Option<EpochDirection>`
- `+0x38..+0x70` (56B): `recv: Option<EpochDirection>` -/
abbrev chainEpochPBAt (A : RustAlloc) (gep : ChainEpochPBGhost × ChainEpochPB) (a : BitVec 64) :
    SepProp :=
  CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBPinnedAt A gep.1 a gep.2

/-- `pqrpb::Chain` (`ChainPB`) at `a` (80 bytes = `0x50`, align 8):
- `+0x00..+0x18` (24B): `links: Vec<pqrpb::chain::Epoch>` (stride 112, align 8)
- `+0x18..+0x30` (24B): `next_root: Vec<u8>`
- `+0x30..+0x38` (8B): `current_epoch: u64`
- `+0x38..+0x40` (8B): `send_epoch: u64`
- `+0x40..+0x4c` (12B): `params: Option<ChainParams>` (`optChainParamsPBAt`)
- `+0x4c..+0x50` (4B): `direction: i32` -/
def chainPBAt (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) (pb : ChainPB) : SepProp :=
  ⌜g.epochs.length = pb.links.length⌝ ∗
    vecAt A chainEpochSize chainEpochAlign (chainEpochPBAt A)
      a g.linksCap g.linksPtr (g.epochs.zip pb.links) ∗
    vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr pb.nextRoot ∗
    ((a + 0x30#64) ↦₆₄ pb.currentEpoch) ∗
    ((a + 0x38#64) ↦₆₄ pb.sendEpoch) ∗
    optChainParamsPBAt (a + 0x40#64) pb.params ∗
    ((a + 0x4c#64) ↦₃₂ pb.direction)

/-- `Option<pqrpb::Chain>` (`Option ChainPB`) at `a` (80 bytes = `0x50`, align 8):
- `none`: niche-encoded at `+0x00` with `a ↦₆₄ noneCap` (`0xFFFFFFFFFFFFFFFF#64`) and
  `memRegion (a + 0x08#64) 72`.
- `some pb`: `chainPBAt A g a pb` (where `g.linksCap.toNat * 112 < 2 ^ 63`, so `a ↦₆₄ g.linksCap`
  satisfies `g.linksCap ≠ noneCap`). -/
def optChainPBAt (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64) : Option ChainPB → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 0x08#64) 72
  | some pb => chainPBAt A g a pb

/-- `Option<&pqrpb::pq_ratchet_state::VersionNegotiation>` passed in register `vnOptPtr` (`x2`):
- `none`: `vnOptPtr = 0#64` and `emp`.
- `some vn`: `vnOptPtr ≠ 0#64` and `versionNegotiationPBAt A pin vnOptPtr vn`. -/
def optVersionNegotiationRefAt (A : RustAlloc) (pin : VecPin) (vnOptPtr : BitVec 64) :
    Option VersionNegotiationPB → SepProp
  | none => ⌜vnOptPtr = 0#64⌝
  | some vn => ⌜vnOptPtr ≠ 0#64⌝ ∗ versionNegotiationPBAt A pin vnOptPtr vn

/-! ## Bridges between `Top.ChainFrom` / `Top.ChainFromVersionNegotiation` and `ProtoRepr` -/

/-- `Top.ChainFromVersionNegotiation.optChainParamsPBAt` equals `ProtoRepr.optChainParamsPBAt`. -/
theorem optChainParamsPBAt_eq_protoRepr (a : BitVec 64) (opt : Option ChainParamsPB) :
    optChainParamsPBAt a opt = CryptoVerification.SpqrV1.ProtoRepr.optChainParamsPBAt a opt := by
  cases opt with
  | none => rfl
  | some cp =>
    dsimp only [optChainParamsPBAt, CryptoVerification.SpqrV1.ProtoRepr.optChainParamsPBAt,
      CryptoVerification.SpqrV1.ProtoRepr.chainParamsPBAt]
    have hadd : a + 4#64 + 4#64 = a + 8#64 := by rw [BitVec.add_assoc]; rfl
    rw [hadd]

/-- `Top.ChainFromVersionNegotiation.versionNegotiationPBAt` equals
    `ProtoRepr.versionNegotiationPBPinnedAt`. -/
theorem versionNegotiationPBAt_eq_protoRepr (A : RustAlloc) (pin : VecPin) (a : BitVec 64)
    (v : VersionNegotiationPB) :
    versionNegotiationPBAt A pin a v =
      CryptoVerification.SpqrV1.ProtoRepr.versionNegotiationPBPinnedAt A ⟨⟨pin.cap, pin.ptr⟩⟩ a v := by
  dsimp only [versionNegotiationPBAt,
    CryptoVerification.SpqrV1.ProtoRepr.versionNegotiationPBPinnedAt]
  rw [optChainParamsPBAt_eq_protoRepr]

/-- `ProtoRepr.versionNegotiationPBAt` unpacks to `∃∗ pin : VecPin, versionNegotiationPBAt A pin a v`. -/
theorem versionNegotiationPBAt_protoRepr_eq_exists (A : RustAlloc) (a : BitVec 64)
    (v : VersionNegotiationPB) :
    CryptoVerification.SpqrV1.ProtoRepr.versionNegotiationPBAt A a v =
      ∃∗ pin : VecPin, versionNegotiationPBAt A pin a v := by
  rw [CryptoVerification.SpqrV1.ProtoRepr.versionNegotiationPBAt_eq_exists_pinned]
  have hbody (c p : BitVec 64) :
      CryptoVerification.SpqrV1.ProtoRepr.versionNegotiationPBPinnedAt A ⟨⟨c, p⟩⟩ a v =
        versionNegotiationPBAt A ⟨c, p⟩ a v :=
    (versionNegotiationPBAt_eq_protoRepr A ⟨c, p⟩ a v).symm
  refine Entails.antisymm ?_ ?_
  · exact Entails.sepExists_elim fun ⟨⟨c, p⟩⟩ =>
      Entails.sepExists_right ⟨c, p⟩ (Entails.of_eq (hbody c p))
  · exact Entails.sepExists_elim fun ⟨c, p⟩ =>
      Entails.sepExists_right ⟨⟨c, p⟩⟩ (Entails.of_eq (hbody c p).symm)

/-- Unpinned `ProtoRepr.epochDirectionPBAt` equals `∃∗ g, epochDirectionPBAt A g a ed`. -/
theorem epochDirectionPBAt_protoRepr_eq_exists (A : RustAlloc) (a : BitVec 64)
    (ed : EpochDirectionPB) :
    CryptoVerification.SpqrV1.ProtoRepr.epochDirectionPBAt A a ed =
      ∃∗ g : EpochDirectionPBGhost, epochDirectionPBAt A g a ed :=
  CryptoVerification.SpqrV1.ProtoRepr.epochDirectionPBAt_eq_exists_pinned A a ed

/-- Unpinned `ProtoRepr.optEpochDirectionPBAt` equals `∃∗ g, optEpochDirectionPBAt A g a opt`. -/
theorem optEpochDirectionPBAt_protoRepr_eq_exists (A : RustAlloc) (a : BitVec 64)
    (opt : Option EpochDirectionPB) :
    CryptoVerification.SpqrV1.ProtoRepr.optEpochDirectionPBAt A a opt =
      ∃∗ g : EpochDirectionPBGhost, optEpochDirectionPBAt A g a opt :=
  CryptoVerification.SpqrV1.ProtoRepr.optEpochDirectionPBAt_eq_exists_pinned A a opt

/-- Unpinned `ProtoRepr.chainEpochPBAt` equals `∃∗ g, chainEpochPBAt A (g, ep) a`. -/
theorem chainEpochPBAt_protoRepr_eq_exists (A : RustAlloc) (a : BitVec 64) (ep : ChainEpochPB) :
    CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBAt A a ep =
      ∃∗ g : ChainEpochPBGhost, chainEpochPBAt A (g, ep) a :=
  CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBAt_eq_exists_pinned A a ep

private theorem exists_cap_ptr_pred_eq_pin (A : RustAlloc) (P : BitVec 64 → Prop)
    (v : BitVec 64) (bs : List (BitVec 8)) :
    (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜P cap⌝ ∗ vecU8At A v cap ptr bs) =
      ∃∗ pin : CryptoVerification.LibsignalSessionRepr.VecPin,
        ⌜P pin.cap⌝ ∗ vecU8At A v pin.cap pin.ptr bs := by
  refine Entails.antisymm ?_ ?_
  · exact Entails.sepExists_elim fun c => Entails.sepExists_elim fun p =>
      Entails.sepExists_right ⟨c, p⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨c, p⟩ =>
      Entails.sepExists_right c (Entails.sepExists_right p (Entails.refl _))

/-- Bridge for capacity-constrained `EpochDirectionPB` (such as `epochDirectionPBCapOkAt` in
    `Prost/MessageMerge/EpochDirection.lean`, where `P := fun cap => BytesMergeCapOk cap remLen`)
    to `∃∗ g : EpochDirectionPBGhost, ⌜P g.next.cap ∧ P g.prev.cap⌝ ∗ epochDirectionPBAt A g a ed`. -/
theorem epochDirectionPBCapPredAt_eq_exists (A : RustAlloc) (P : BitVec 64 → Prop)
    (a : BitVec 64) (ed : EpochDirectionPB) :
    ((∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜P cap⌝ ∗ vecU8At A a cap ptr ed.next) ∗
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜P cap⌝ ∗ vecU8At A (a + 0x18#64) cap ptr ed.prev) ∗
      ((a + 0x30#64) ↦₃₂ ed.ctr) ∗
      memRegion (a + 0x34#64) 4) =
    ∃∗ g : EpochDirectionPBGhost,
      ⌜P g.next.cap ∧ P g.prev.cap⌝ ∗ epochDirectionPBAt A g a ed := by
  have hbody (p1 p2 : CryptoVerification.LibsignalSessionRepr.VecPin) :
      ((⌜P p1.cap⌝ ∗ vecU8At A a p1.cap p1.ptr ed.next) ∗
        (⌜P p2.cap⌝ ∗ vecU8At A (a + 0x18#64) p2.cap p2.ptr ed.prev) ∗
        ((a + 0x30#64) ↦₃₂ ed.ctr) ∗ memRegion (a + 0x34#64) 4) =
      (⌜P p1.cap ∧ P p2.cap⌝ ∗
        (vecU8At A a p1.cap p1.ptr ed.next ∗
          vecU8At A (a + 0x18#64) p2.cap p2.ptr ed.prev ∗
          ((a + 0x30#64) ↦₃₂ ed.ctr) ∗ memRegion (a + 0x34#64) 4)) := by
    rw [← pure_sepConj_pure_assoc]
    ac_rfl
  simp only [exists_cap_ptr_pred_eq_pin, epochDirectionPBAt,
    CryptoVerification.SpqrV1.ProtoRepr.epochDirectionPBPinnedAt,
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.antisymm ?_ ?_
  · exact Entails.sepExists_elim fun p2 => Entails.sepExists_elim fun p1 =>
      Entails.sepExists_right ⟨p1, p2⟩ (Entails.of_eq (hbody p1 p2))
  · exact Entails.sepExists_elim fun ⟨p1, p2⟩ =>
      Entails.sepExists_right p2 (Entails.sepExists_right p1 (Entails.of_eq (hbody p1 p2).symm))

/-- Entailment from capacity-constrained `EpochDirectionPB` (such as `epochDirectionPBCapOkAt`)
    to `∃∗ g : EpochDirectionPBGhost, epochDirectionPBAt A g a ed` (`= ProtoRepr.epochDirectionPBAt A a ed`). -/
theorem epochDirectionPBCapPredAt_entails_exists (A : RustAlloc) (P : BitVec 64 → Prop)
    (a : BitVec 64) (ed : EpochDirectionPB) :
    ((∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜P cap⌝ ∗ vecU8At A a cap ptr ed.next) ∗
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜P cap⌝ ∗ vecU8At A (a + 0x18#64) cap ptr ed.prev) ∗
      ((a + 0x30#64) ↦₃₂ ed.ctr) ∗
      memRegion (a + 0x34#64) 4) ⊢
    ∃∗ g : EpochDirectionPBGhost, epochDirectionPBAt A g a ed := by
  rw [epochDirectionPBCapPredAt_eq_exists]
  refine Entails.sepExists_elim fun g => Entails.pure_left fun _ => ?_
  exact Entails.sepExists_intro (P := fun g' => epochDirectionPBAt A g' a ed) g

private theorem chainEpochPBArrayAt_cons (A : RustAlloc) (base : BitVec 64)
    (ep : ChainEpochPB) (rest : List ChainEpochPB) :
    CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBArrayAt A base (ep :: rest) =
      CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBAt A base ep ∗
        CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBArrayAt A (base + 112#64) rest := rfl

/-- `ProtoRepr.chainEpochPBArrayAt A base links` equals the existentially quantified per-epoch
    pinned array `∃∗ epochs, ⌜epochs.length = links.length⌝ ∗ arrayAt (chainEpochPBAt A) chainEpochSize base (epochs.zip links)`. -/
theorem chainEpochPBArrayAt_eq_exists_epochs (A : RustAlloc) (base : BitVec 64)
    (links : List ChainEpochPB) :
    CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBArrayAt A base links =
      ∃∗ epochs : List ChainEpochPBGhost,
        ⌜epochs.length = links.length⌝ ∗
        arrayAt (chainEpochPBAt A) chainEpochSize base (epochs.zip links) := by
  induction links generalizing base with
  | nil =>
    dsimp only [CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBArrayAt, arrayAt]
    refine Entails.antisymm ?_ ?_
    · exact Entails.sepExists_right [] (Entails.pure_right rfl (Entails.refl _))
    · refine Entails.sepExists_elim fun epochs => Entails.pure_left fun hlen => ?_
      cases epochs with
      | nil => exact Entails.refl _
      | cons _ _ => cases hlen
  | cons ep rest ih =>
    rw [chainEpochPBArrayAt_cons, chainEpochPBAt_protoRepr_eq_exists A base ep,
      ih (base + 112#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    have hcomm (g : ChainEpochPBGhost) (gs : List ChainEpochPBGhost) :
        (chainEpochPBAt A (g, ep) base ∗ (⌜gs.length = rest.length⌝ ∗
          arrayAt (chainEpochPBAt A) chainEpochSize (base + 112#64) (gs.zip rest))) =
        (⌜(g :: gs).length = (ep :: rest).length⌝ ∗
          arrayAt (chainEpochPBAt A) chainEpochSize base ((g :: gs).zip (ep :: rest))) := by
      dsimp only [List.zip_cons_cons, arrayAt, chainEpochSize]
      simp only [List.length_cons, Nat.add_right_cancel_iff]
      ac_rfl
    refine Entails.antisymm ?_ ?_
    · exact Entails.sepExists_elim fun gs => Entails.sepExists_elim fun g =>
        Entails.sepExists_right (g :: gs) (Entails.of_eq (hcomm g gs))
    · refine Entails.sepExists_elim fun epochs => Entails.pure_left fun hlen => ?_
      cases epochs with
      | nil => cases hlen
      | cons g gs =>
        exact Entails.sepExists_right gs
          (Entails.sepExists_right g
            (Entails.trans (Entails.pure_right hlen (Entails.refl _))
              (Entails.of_eq (hcomm g gs).symm)))

/-- `ProtoRepr.chainLinksVecPinnedAt A ⟨cap, ptr⟩ a links` equals
    `∃∗ epochs, ⌜epochs.length = links.length⌝ ∗ vecAt A chainEpochSize chainEpochAlign (chainEpochPBAt A) a cap ptr (epochs.zip links)`. -/
theorem chainLinksVecPinnedAt_eq_exists_epochs (A : RustAlloc) (cap ptr a : BitVec 64)
    (links : List ChainEpochPB) :
    CryptoVerification.SpqrV1.ProtoRepr.chainLinksVecPinnedAt A ⟨cap, ptr⟩ a links =
      ∃∗ epochs : List ChainEpochPBGhost,
        ⌜epochs.length = links.length⌝ ∗
        vecAt A chainEpochSize chainEpochAlign (chainEpochPBAt A) a cap ptr (epochs.zip links) := by
  dsimp only [CryptoVerification.SpqrV1.ProtoRepr.chainLinksVecPinnedAt, vecAt, vecBuf,
    CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBSize, chainEpochSize, chainEpochAlign]
  by_cases hcap : cap = 0
  · simp only [hcap, ↓reduceIte]
    have hcongr (epochs : List ChainEpochPBGhost) :
        (⌜epochs.length = links.length⌝ ∗
          (vecHeader a 0 ptr (BitVec.ofNat 64 (epochs.zip links).length) ∗
            ⌜(epochs.zip links).length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
            emp)) =
        (⌜epochs.length = links.length⌝ ∗
          (vecHeader a 0 ptr (BitVec.ofNat 64 links.length) ∗
            ⌜links.length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
            emp)) := by
      refine pure_sepConj_congr fun hlen => ?_
      have hzlen : (epochs.zip links).length = links.length := by
        rw [List.length_zip, hlen, Nat.min_self]
      rw [hzlen]
    simp only [hcongr]
    refine Entails.antisymm ?_ ?_
    · exact Entails.sepExists_right
        (List.replicate links.length ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩)
        (Entails.pure_right List.length_replicate (Entails.refl _))
    · exact Entails.sepExists_elim fun _ => Entails.pure_left fun _ => Entails.refl _
  · simp only [hcap, ↓reduceIte]
    change (vecHeader a cap ptr (BitVec.ofNat 64 links.length) ∗
        (⌜links.length ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (A.live ptr (cap.toNat * 112) 8 ∗
            CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBArrayAt A ptr links ∗
            memRegion (ptr + BitVec.ofNat 64 (links.length * 112))
              ((cap.toNat - links.length) * 112)))) = _
    rw [chainEpochPBArrayAt_eq_exists_epochs A ptr links]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    have hbody (epochs : List ChainEpochPBGhost) :
        (vecHeader a cap ptr (BitVec.ofNat 64 links.length) ∗
          (⌜links.length ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
            (A.live ptr (cap.toNat * 112) 8 ∗
              (⌜epochs.length = links.length⌝ ∗
                arrayAt (chainEpochPBAt A) 112 ptr (epochs.zip links)) ∗
              memRegion (ptr + BitVec.ofNat 64 (links.length * 112))
                ((cap.toNat - links.length) * 112)))) =
        (⌜epochs.length = links.length⌝ ∗
          (vecHeader a cap ptr (BitVec.ofNat 64 (epochs.zip links).length) ∗
            ⌜(epochs.zip links).length ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
            (A.live ptr (cap.toNat * 112) 8 ∗
              arrayAt (chainEpochPBAt A) 112 ptr (epochs.zip links) ∗
              memRegion (ptr + BitVec.ofNat 64 ((epochs.zip links).length * 112))
                ((cap.toNat - (epochs.zip links).length) * 112)))) := by
      have h1 : (vecHeader a cap ptr (BitVec.ofNat 64 links.length) ∗
          (⌜links.length ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
            (A.live ptr (cap.toNat * 112) 8 ∗
              (⌜epochs.length = links.length⌝ ∗
                arrayAt (chainEpochPBAt A) 112 ptr (epochs.zip links)) ∗
              memRegion (ptr + BitVec.ofNat 64 (links.length * 112))
                ((cap.toNat - links.length) * 112)))) =
        (⌜epochs.length = links.length⌝ ∗
          (vecHeader a cap ptr (BitVec.ofNat 64 links.length) ∗
            ⌜links.length ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
            (A.live ptr (cap.toNat * 112) 8 ∗
              arrayAt (chainEpochPBAt A) 112 ptr (epochs.zip links) ∗
              memRegion (ptr + BitVec.ofNat 64 (links.length * 112))
                ((cap.toNat - links.length) * 112)))) := by ac_rfl
      rw [h1]
      refine pure_sepConj_congr fun hlen => ?_
      have hzlen : (epochs.zip links).length = links.length := by
        rw [List.length_zip, hlen, Nat.min_self]
      rw [hzlen]
    simp only [hbody]

/-- `ProtoRepr.chainPBPinnedAt A g a pb` equals
    `∃∗ epochs, chainPBAt A ⟨g.links.cap, g.links.ptr, epochs, ⟨g.nextRoot.cap, g.nextRoot.ptr⟩⟩ a pb`. -/
theorem chainPBPinnedAt_eq_exists_epochs (A : RustAlloc)
    (g : CryptoVerification.SpqrV1.ProtoRepr.ChainPBGhost) (a : BitVec 64) (pb : ChainPB) :
    CryptoVerification.SpqrV1.ProtoRepr.chainPBPinnedAt A g a pb =
      ∃∗ epochs : List ChainEpochPBGhost,
        chainPBAt A ⟨g.links.cap, g.links.ptr, epochs, ⟨g.nextRoot.cap, g.nextRoot.ptr⟩⟩ a pb := by
  rcases g with ⟨⟨lcap, lptr⟩, ⟨ncap, nptr⟩⟩
  dsimp only [CryptoVerification.SpqrV1.ProtoRepr.chainPBPinnedAt, chainPBAt]
  rw [chainLinksVecPinnedAt_eq_exists_epochs A lcap lptr a pb.links,
    ← optChainParamsPBAt_eq_protoRepr]
  simp only [sepExists_sepConj_left, sepConj_assoc]

/-- Unpinned `ProtoRepr.chainPBAt A a pb` equals `∃∗ g : ChainPBGhost, chainPBAt A g a pb`. -/
theorem chainPBAt_protoRepr_eq_exists (A : RustAlloc) (a : BitVec 64) (pb : ChainPB) :
    CryptoVerification.SpqrV1.ProtoRepr.chainPBAt A a pb =
      ∃∗ g : ChainPBGhost, chainPBAt A g a pb := by
  simp only [CryptoVerification.SpqrV1.ProtoRepr.chainPBAt_eq_exists_pinned,
    chainPBPinnedAt_eq_exists_epochs]
  refine Entails.antisymm ?_ ?_
  · exact Entails.sepExists_elim fun ⟨⟨lcap, lptr⟩, ⟨ncap, nptr⟩⟩ =>
      Entails.sepExists_elim fun epochs =>
        Entails.sepExists_right ⟨lcap, lptr, epochs, ⟨ncap, nptr⟩⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨lcap, lptr, epochs, ⟨ncap, nptr⟩⟩ =>
      Entails.sepExists_right ⟨⟨lcap, lptr⟩, ⟨ncap, nptr⟩⟩
        (Entails.sepExists_right epochs (Entails.refl _))

/-- `ProtoRepr.optChainPBPinnedAt A g a opb` equals
    `∃∗ epochs, optChainPBAt A ⟨g.links.cap, g.links.ptr, epochs, ⟨g.nextRoot.cap, g.nextRoot.ptr⟩⟩ a opb`. -/
theorem optChainPBPinnedAt_eq_exists_epochs (A : RustAlloc)
    (g : CryptoVerification.SpqrV1.ProtoRepr.ChainPBGhost) (a : BitVec 64) (opb : Option ChainPB) :
    CryptoVerification.SpqrV1.ProtoRepr.optChainPBPinnedAt A g a opb =
      ∃∗ epochs : List ChainEpochPBGhost,
        optChainPBAt A ⟨g.links.cap, g.links.ptr, epochs, ⟨g.nextRoot.cap, g.nextRoot.ptr⟩⟩ a opb := by
  cases opb with
  | none =>
    dsimp only [CryptoVerification.SpqrV1.ProtoRepr.optChainPBPinnedAt, optChainPBAt]
    exact Entails.antisymm
      (Entails.sepExists_right ([] : List ChainEpochPBGhost) (Entails.refl _))
      (Entails.sepExists_elim fun _ => Entails.refl _)
  | some pb =>
    exact chainPBPinnedAt_eq_exists_epochs A g a pb

/-- Unpinned `ProtoRepr.optChainPBAt` equals `∃∗ g : ProtoRepr.ChainPBGhost, ProtoRepr.optChainPBPinnedAt`. -/
theorem optChainPBAt_eq_exists_protoRepr_pinned (A : RustAlloc) (a : BitVec 64)
    (opb : Option ChainPB) :
    CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A a opb =
      ∃∗ g : CryptoVerification.SpqrV1.ProtoRepr.ChainPBGhost,
        CryptoVerification.SpqrV1.ProtoRepr.optChainPBPinnedAt A g a opb := by
  cases opb with
  | none =>
    dsimp only [CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt,
      CryptoVerification.SpqrV1.ProtoRepr.optChainPBPinnedAt]
    exact Entails.antisymm
      (Entails.sepExists_right
        (⟨⟨0, 0⟩, ⟨0, 0⟩⟩ : CryptoVerification.SpqrV1.ProtoRepr.ChainPBGhost)
        (Entails.refl _))
      (Entails.sepExists_elim fun _ => Entails.refl _)
  | some pb =>
    exact CryptoVerification.SpqrV1.ProtoRepr.chainPBAt_eq_exists_pinned A a pb

/-- Unpinned `ProtoRepr.optChainPBAt A a opb` equals `∃∗ g : ChainPBGhost, optChainPBAt A g a opb`. -/
theorem optChainPBAt_protoRepr_eq_exists (A : RustAlloc) (a : BitVec 64) (opb : Option ChainPB) :
    CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A a opb =
      ∃∗ g : ChainPBGhost, optChainPBAt A g a opb := by
  cases opb with
  | none =>
    dsimp only [CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt, optChainPBAt]
    exact Entails.antisymm
      (Entails.sepExists_right (⟨0, 0, [], ⟨0, 0⟩⟩ : ChainPBGhost) (Entails.refl _))
      (Entails.sepExists_elim fun _ => Entails.refl _)
  | some pb =>
    exact chainPBAt_protoRepr_eq_exists A a pb

/-- `chainPBAt A g a pb` entails `ProtoRepr.chainPBPinnedAt A g.toProtoRepr a pb`. -/
theorem chainPBAt_entails_protoRepr_pinned (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64)
    (pb : ChainPB) :
    chainPBAt A g a pb ⊢
      CryptoVerification.SpqrV1.ProtoRepr.chainPBPinnedAt A g.toProtoRepr a pb := by
  rw [chainPBPinnedAt_eq_exists_epochs]
  exact Entails.sepExists_intro
    (P := fun epochs => chainPBAt A ⟨g.linksCap, g.linksPtr, epochs, ⟨g.nextRoot.cap, g.nextRoot.ptr⟩⟩ a pb)
    g.epochs

/-- `chainPBAt A g a pb` entails `ProtoRepr.chainPBAt A a pb`. -/
theorem chainPBAt_entails_protoRepr (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64)
    (pb : ChainPB) :
    chainPBAt A g a pb ⊢ CryptoVerification.SpqrV1.ProtoRepr.chainPBAt A a pb := by
  rw [chainPBAt_protoRepr_eq_exists]
  exact Entails.sepExists_intro (P := fun g' => chainPBAt A g' a pb) g

/-- `optChainPBAt A g a opb` entails `ProtoRepr.optChainPBPinnedAt A g.toProtoRepr a opb`. -/
theorem optChainPBAt_entails_protoRepr_pinned (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64)
    (opb : Option ChainPB) :
    optChainPBAt A g a opb ⊢
      CryptoVerification.SpqrV1.ProtoRepr.optChainPBPinnedAt A g.toProtoRepr a opb := by
  rw [optChainPBPinnedAt_eq_exists_epochs]
  exact Entails.sepExists_intro
    (P := fun epochs => optChainPBAt A ⟨g.linksCap, g.linksPtr, epochs, ⟨g.nextRoot.cap, g.nextRoot.ptr⟩⟩ a opb)
    g.epochs

/-- `optChainPBAt A g a opb` entails `ProtoRepr.optChainPBAt A a opb`. -/
theorem optChainPBAt_entails_protoRepr (A : RustAlloc) (g : ChainPBGhost) (a : BitVec 64)
    (opb : Option ChainPB) :
    optChainPBAt A g a opb ⊢ CryptoVerification.SpqrV1.ProtoRepr.optChainPBAt A a opb := by
  rw [optChainPBAt_protoRepr_eq_exists]
  exact Entails.sepExists_intro (P := fun g' => optChainPBAt A g' a opb) g

/-! ## Callee hypothesis: `<spqr::chain::Chain>::from_pb` (`0x60074`, 347 instructions) -/

/-- Ghost arguments of `<spqr::chain::Chain>::from_pb` (`0x60074`). -/
structure ChainFromPbCall where
  /-- Sret pointer `x8` (88-byte `Result<Chain, spqr::Error>` output). -/
  out : BitVec 64
  /-- `pb: pqrpb::Chain` pointer `x0` (80-byte input struct moved in by pointer). -/
  pbPtr : BitVec 64
  gPb : ChainPBGhost
  pb : ChainPB

/-- Spec of `<spqr::chain::Chain>::from_pb` (`src/chain.rs:444–462`, image offset `0x60074`,
347 instructions):
* `x8 = out` (88-byte `Result<Chain, Error>` return slot), `x0 = pbPtr` (80-byte `pqrpb::Chain`).
* Consumes `chainPBAt A x.gPb x.pbPtr x.pb` (leaving `memRegion x.pbPtr 80` in the caller's stack
  slot) and writes `chainResultAt A x.out (Chain.fromPb x.pb)` at `x.out` (or panics on OOM). -/
def chainFromPbSpecX (A : RustAlloc) : Spec ChainFromPbCall where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.pbPtr⌝ ∗
      memRegion x.out 88 ∗ chainPBAt A x.gPb x.pbPtr x.pb ∗
      A.pool ∗ stackAt s.sp chainFromPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chainResultAt A x.out (Chain.fromPb x.pb) ∗
      memRegion x.pbPtr 80 ∗
      A.pool ∗ stackAt s0.sp chainFromPbStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `<spqr::chain::Chain>::from_pb` meets `(chainFromPbSpecX A).inImage img` on
`tripleRatchetProgAtExt img.base ext`. -/
def ChainFromPbOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainFromPbName)
    ((chainFromPbSpecX A).inImage img)

/-! ## Target spec: `spqr::chain_from` (`0x531ac`, 76 instructions) -/

/-- Ghost arguments of `spqr::chain_from` (`0x531ac`). -/
structure ChainFromCall where
  /-- Sret pointer `x0` (88-byte `Result<Chain, spqr::Error>` output). -/
  out : BitVec 64
  /-- `pb: Option<pqrpb::Chain>` pointer `x1` (80-byte input slot). -/
  pbPtr : BitVec 64
  /-- `vn: Option<&pqrpb::pq_ratchet_state::VersionNegotiation>` pointer `x2` (`0#64` for `None`). -/
  vnOptPtr : BitVec 64
  gPb : ChainPBGhost
  /-- Ghost pin for `vn.auth_key` when `vn = some _`. -/
  vnPin : VecPin
  pb : Option ChainPB
  vn : Option VersionNegotiationPB

/-- Spec of `spqr::chain_from` (`src/lib.rs:342–353`, image offset `0x531ac`, 76 instructions)
against the pure model `chainFrom hkdf x.pb x.vn` (`LibsignalBinary/Specifications/LibsignalSpqrV1/Chain.lean`):
* Registers: `x0 = x.out` (88-byte `Result<Chain, Error>` sret), `x1 = x.pbPtr` (80-byte
  `Option<pqrpb::Chain>`), `x2 = x.vnOptPtr` (`Option<&VersionNegotiationPB>`).
* Writes `chainResultAt A x.out (chainFrom hkdf x.pb x.vn)` to `x.out`, leaves `memRegion x.pbPtr 80`
  at `x.pbPtr`, and preserves `optVersionNegotiationRefAt A x.vnPin x.vnOptPtr x.vn`. -/
def chainFromSpecX (hkdf : HkdfFn) (A : RustAlloc) : Spec ChainFromCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbPtr ∧ s.readReg64 .x2 = x.vnOptPtr⌝ ∗
      memRegion x.out 88 ∗
      optChainPBAt A x.gPb x.pbPtr x.pb ∗
      optVersionNegotiationRefAt A x.vnPin x.vnOptPtr x.vn ∗
      A.pool ∗ stackAt s.sp chainFromStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chainResultAt A x.out (chainFrom hkdf x.pb x.vn) ∗
      memRegion x.pbPtr 80 ∗
      optVersionNegotiationRefAt A x.vnPin x.vnOptPtr x.vn ∗
      A.pool ∗ stackAt s0.sp chainFromStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `spqr::chain_from` (`0x531ac`) meets `(chainFromSpecX hkdf A).inImage img` on
`tripleRatchetProgAtExt img.base ext`. -/
def ChainFromOkX (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainFromName)
    ((chainFromSpecX hkdf A).inImage img)

/-! ## Contract-Backed (`*Ext`) Specifications (`chainFromStackExt = 18176` B) -/

/-- `spqr::chain_from` stack budget under `CliExternsOk` (`144 + 192 + chainNewStackExt = 18176` B). -/
abbrev chainFromStackExt : Nat := 336 + chainNewStackExt

/-- Contract-backed spec of `spqr::chain_from` (`0x531ac`, 76 instructions) at
`chainFromStackExt` (`18176` B). -/
def chainFromSpecExt (hkdf : HkdfFn) (A : RustAlloc) : Spec ChainFromCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbPtr ∧ s.readReg64 .x2 = x.vnOptPtr⌝ ∗
      memRegion x.out 88 ∗
      optChainPBAt A x.gPb x.pbPtr x.pb ∗
      optVersionNegotiationRefAt A x.vnPin x.vnOptPtr x.vn ∗
      A.pool ∗ stackAt s.sp chainFromStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chainResultAt A x.out (chainFrom hkdf x.pb x.vn) ∗
      memRegion x.pbPtr 80 ∗
      optVersionNegotiationRefAt A x.vnPin x.vnOptPtr x.vn ∗
      A.pool ∗ stackAt s0.sp chainFromStackExt
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract-backed callee-contract predicate for `spqr::chain_from` (`0x531ac`). -/
def ChainFromOkExt (img : Obj.Image) (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainFromName)
    ((chainFromSpecExt hkdf A).inImage img)

end CryptoVerification.SpqrV1.Top.ChainFrom
