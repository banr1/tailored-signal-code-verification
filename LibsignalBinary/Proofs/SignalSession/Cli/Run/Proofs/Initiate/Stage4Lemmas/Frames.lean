/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Pure
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.CanonKey

/-!
# Stage 4 Stack Frame Carve/Merge and Pre-Stage-5 Session Folding

Layout-independent `logOff` bridges, disjoint stack-slot carve/merge lemmas over
`[fsp, s0.sp)` (`cliInitiateFrame = 7408` B), and pre-Stage-5 `SessionState` / `SessionGhost`
folding into `AtStage5`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

/-! ## Layout-Independent `logOff` Bridges -/

theorem logOff_eq_base (img : Obj.Image) :
    logOff img =
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))
        ↦₆₄ 0#64) :=
  rfl

theorem adrp_5064_eq_logFilterAddr {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img)
    {fnStart : BitVec 64}
    (hfn : fnStart = img.base + bv% (ls_off% "libsignal_cli_handshake::initiate")) :
    ((fnStart + bv% (5064) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) -
        page% (ls_off% "libsignal_cli_handshake::initiate" + 5064))) +
      bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      CryptoVerification.LibsignalSession.logFilterAddr img := by
  have hbal := ProofLib.base_aligned_of_loads hloads
  rw [hfn, BitVec.add_assoc img.base, adrp_page_of_aligned hbal,
    CryptoVerification.LibsignalSession.logFilterAddr]
  have hmask :
      (((bv% (ls_off% "libsignal_cli_handshake::initiate")) + bv% (5064) : BitVec 64) &&&
        bv% (2 ^ 64 - 4096)) =
      bv% (page% (ls_off% "libsignal_cli_handshake::initiate" + 5064)) := rfl
  rw [hmask]
  bv_omega

theorem logOff_eq_at_5064 {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img)
    {fnStart : BitVec 64}
    (hfn : fnStart = img.base + bv% (ls_off% "libsignal_cli_handshake::initiate")) :
    logOff img =
      ((((fnStart + bv% (5064) &&& bv% (2 ^ 64 - 4096)) +
        bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) -
          page% (ls_off% "libsignal_cli_handshake::initiate" + 5064))) +
        bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096))
        ↦₆₄ 0#64) := by
  unfold logOff
  rw [adrp_5064_eq_logFilterAddr hloads hfn]

theorem initEntry_eq_base_add (img : Obj.Image) (W : CliHooks) :
    initEntry img W = img.base + bv% (ls_off% "libsignal_cli_handshake::initiate") := by
  dsimp only [initEntry, initProg, tripleRatchetProgAtExt]
  rw [Program.fnAddr_rebase, cliInitiate_fnOff]

theorem s4EntryExt_eq_base_add (img : Obj.Image) (ext : String → Option (State → State)) :
    s4EntryExt img ext = img.base + bv% (ls_off% "libsignal_cli_handshake::initiate") := by
  dsimp only [s4EntryExt, s4ProgExt, tripleRatchetProgAtExt]
  rw [Program.fnAddr_rebase, cliInitiate_fnOff]

/-! ## Working Stack Slots Carve and Merge (`[fsp + 0x5ba, fsp + 0x1c90)`) -/

def stage4IdleSlots (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 1466#64) 438 ∗
    memRegion (fsp + 2216#64) 8 ∗
    memRegion (fsp + 2292#64) 12 ∗
    memRegion (fsp + 2452#64) 44 ∗
    memRegion (fsp + 2560#64) 1504 ∗
    memRegion (fsp + 4408#64) 1224 ∗
    memRegion (fsp + 5976#64) 1256 ∗
    memRegion (fsp + 7288#64) 24

theorem stage4Locals_carve_5ba (fsp : BitVec 64) :
    memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) =
      memRegion (fsp + 1466#64) 438 ∗
      memRegion (fsp + 1904#64) 288 ∗
      memRegion (fsp + 2192#64) 24 ∗
      memRegion (fsp + 2216#64) 8 ∗
      memRegion (fsp + 2224#64) 32 ∗
      memRegion (fsp + 2256#64) 36 ∗
      memRegion (fsp + 2292#64) 12 ∗
      memRegion (fsp + 2304#64) 32 ∗
      memRegion (fsp + 2336#64) 16 := by
  change memRegion (fsp + 1466#64) 886 = _
  rw [ProofLib.memRegion_split' (b := fsp + 1466#64) (n := 438) (k := 448)
        (b' := fsp + 1904#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1904#64) (n := 288) (k := 160)
        (b' := fsp + 2192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2192#64) (n := 24) (k := 136)
        (b' := fsp + 2216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2216#64) (n := 8) (k := 128)
        (b' := fsp + 2224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2224#64) (n := 32) (k := 96)
        (b' := fsp + 2256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2256#64) (n := 36) (k := 60)
        (b' := fsp + 2292#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2292#64) (n := 12) (k := 48)
        (b' := fsp + 2304#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2304#64) (n := 32) (k := 16)
        (b' := fsp + 2336#64) rfl (by bv_omega) (by decide)]

theorem stage4Locals_carve_994 (fsp : BitVec 64) :
    memRegion (fsp + 0x994#64) (initLocalsSize - 0x994) =
      memRegion (fsp + 2452#64) 44 ∗
      memRegion (fsp + 2496#64) 32 ∗
      memRegion (fsp + 2528#64) 32 ∗
      memRegion (fsp + 2560#64) 1504 ∗
      memRegion (fsp + 4064#64) 344 ∗
      memRegion (fsp + 4408#64) 1224 ∗
      memRegion (fsp + 5632#64) 344 ∗
      memRegion (fsp + 5976#64) 1256 ∗
      memRegion (fsp + 7232#64) 32 ∗
      memRegion (fsp + 7264#64) 24 ∗
      memRegion (fsp + 7288#64) 24 := by
  change memRegion (fsp + 2452#64) 4860 = _
  rw [ProofLib.memRegion_split' (b := fsp + 2452#64) (n := 44) (k := 4816)
        (b' := fsp + 2496#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2496#64) (n := 32) (k := 4784)
        (b' := fsp + 2528#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2528#64) (n := 32) (k := 4752)
        (b' := fsp + 2560#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2560#64) (n := 1504) (k := 3248)
        (b' := fsp + 4064#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 4064#64) (n := 344) (k := 2904)
        (b' := fsp + 4408#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 4408#64) (n := 1224) (k := 1680)
        (b' := fsp + 5632#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5632#64) (n := 344) (k := 1336)
        (b' := fsp + 5976#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 5976#64) (n := 1256) (k := 80)
        (b' := fsp + 7232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 7232#64) (n := 32) (k := 48)
        (b' := fsp + 7264#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 7264#64) (n := 24) (k := 24)
        (b' := fsp + 7288#64) rfl (by bv_omega) (by decide)]

theorem stage4Locals_merge_5ba (fsp : BitVec 64) :
    stage4IdleSlots fsp ∗
      memRegion (fsp + 1904#64) 288 ∗
      memRegion (fsp + 2192#64) 24 ∗
      memRegion (fsp + 2224#64) 32 ∗
      memRegion (fsp + 2256#64) 36 ∗
      memRegion (fsp + 2304#64) 32 ∗
      memRegion (fsp + 2336#64) 36 ∗
      memRegion (fsp + 2372#64) 80 ∗
      memRegion (fsp + 2496#64) 32 ∗
      memRegion (fsp + 2528#64) 32 ∗
      memRegion (fsp + 4064#64) 344 ∗
      memRegion (fsp + 5632#64) 344 ∗
      memRegion (fsp + 7232#64) 32 ∗
      memRegion (fsp + 7264#64) 24 =
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
  have h5ba994 :
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) =
        memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) ∗
        memRegion (fsp + 2352#64) 100 ∗
        memRegion (fsp + 0x994#64) (initLocalsSize - 0x994) := by
    change memRegion (fsp + 1466#64) 5846 =
      memRegion (fsp + 1466#64) 886 ∗ memRegion (fsp + 2352#64) 100 ∗
        memRegion (fsp + 2452#64) 4860
    rw [ProofLib.memRegion_split' (b := fsp + 1466#64) (n := 886) (k := 4960)
          (b' := fsp + 2352#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 2352#64) (n := 100) (k := 4860)
          (b' := fsp + 2452#64) rfl (by bv_omega) (by decide)]
  have h100 :
      memRegion (fsp + 2352#64) 100 =
        memRegion (fsp + 2352#64) 20 ∗ memRegion (fsp + 2372#64) 80 :=
    ProofLib.memRegion_split' (b := fsp + 2352#64) (n := 20) (k := 80)
      (b' := fsp + 2372#64) rfl (by bv_omega) (by decide)
  have h36 :
      memRegion (fsp + 2336#64) 36 =
        memRegion (fsp + 2336#64) 16 ∗ memRegion (fsp + 2352#64) 20 :=
    ProofLib.memRegion_split' (b := fsp + 2336#64) (n := 16) (k := 20)
      (b' := fsp + 2352#64) rfl (by bv_omega) (by decide)
  rw [h5ba994, stage4Locals_carve_5ba fsp, stage4Locals_carve_994 fsp, h100, h36]
  unfold stage4IdleSlots
  ac_rfl

theorem stage4Prefix_0xd0_merge (fsp kemCtPtr w70 w78 : BitVec 64) :
    memRegion fsp 0x60 ∗
      ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
      ((fsp + 0x70#64) ↦₆₄ w70) ∗ ((fsp + 0x78#64) ↦₆₄ w78) ∗
      memRegion (fsp + 0x80#64) 0x50 ⊢
      memRegion fsp 0xd0 := by
  have hcells :
      ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
      ((fsp + 0x70#64) ↦₆₄ w70) ∗ ((fsp + 0x78#64) ↦₆₄ w78) ⊢
        memRegion (fsp + 0x60#64) 0x20 := by
    rw [ProofLib.memRegion_split' (b := fsp + 0x60#64) (n := 8) (k := 24)
          (b' := fsp + 0x68#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x68#64) (n := 8) (k := 16)
          (b' := fsp + 0x70#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x70#64) (n := 8) (k := 8)
          (b' := fsp + 0x78#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (pointsTo64_entails_memRegion _ _)))
  rw [ProofLib.memRegion_split' (b := fsp) (n := 0x60) (k := 0x70)
        (b' := fsp + 0x60#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x60#64) (n := 0x20) (k := 0x50)
        (b' := fsp + 0x80#64) rfl (by bv_omega) (by decide)]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_right (sepConj_mono_left hcells))

/-! ## Full Frame Merge for Early `Err` Exit -/

theorem initArgsAt_entails_memRegion (img : Obj.Image) (fsp : BitVec 64)
    (x : InitGhost) (s0 : State) :
    initArgsAt img fsp x s0 ⊢ memRegion (fsp + 0xd0#64) 0x58 := by
  unfold initArgsAt
  rw [ProofLib.memRegion_split' (b := fsp + 0xd0#64) (n := 8) (k := 80)
        (b' := fsp + 0xd8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0xd8#64) (n := 8) (k := 72)
        (b' := fsp + 0xe0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0xe0#64) (n := 8) (k := 64)
        (b' := fsp + 0xe8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0xe8#64) (n := 8) (k := 56)
        (b' := fsp + 0xf0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0xf0#64) (n := 8) (k := 48)
        (b' := fsp + 0xf8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0xf8#64) (n := 8) (k := 40)
        (b' := fsp + 0x100#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x100#64) (n := 8) (k := 32)
        (b' := fsp + 0x108#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x108#64) (n := 8) (k := 24)
        (b' := fsp + 0x110#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x110#64) (n := 4) (k := 20)
        (b' := fsp + 0x114#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x114#64) (n := 4) (k := 16)
        (b' := fsp + 0x118#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x118#64) (n := 8) (k := 8)
        (b' := fsp + 0x120#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)))))))))))

theorem initFreshRecAt_entails_memRegion (fsp : BitVec 64) :
    initFreshRecAt fsp ⊢ memRegion (fsp + 0x128#64) 0x20 := by
  unfold initFreshRecAt
  rw [ProofLib.memRegion_split' (b := fsp + 0x128#64) (n := 8) (k := 24)
        (b' := fsp + 0x130#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x130#64) (n := 8) (k := 16)
        (b' := fsp + 0x138#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x138#64) (n := 8) (k := 8)
        (b' := fsp + 0x140#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (pointsTo64_entails_memRegion _ _)))

private theorem pointsToBytes_entails_memRegion_len (p : BitVec 64) (bs : List (BitVec 8))
    (n : Nat) (h : bs.length = n) :
    (p ↦ₛ bs) ⊢ memRegion p n :=
  h ▸ pointsToBytes_entails_memRegion p bs

theorem stage3KeySlotsNoHeap_entails_memRegion (fsp : BitVec 64) (b : BundleV)
    (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
    (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (hekA : ekAPk.length = 32) (hekASk : ekASk.length = 32) :
    let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
    ((fsp + 0x298#64) ↦ₛ ekAPk) ∗
      memRegion (fsp + 0x2b8#64) 0x48 ∗
      ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
      memRegion (fsp + 0x308#64) 0x40 ∗
      ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
      ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
      ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
      ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
      ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
      ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
      ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
      ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
      ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
      (match b.opk with
       | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
       | none => memRegion (fsp + 0x439#64) 32) ∗
      ((fsp + 0x459#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x45a#64) 6 ⊢
      memRegion (fsp + 0x298#64) 0x1c8 := by
  intro opkFlag
  have hopk :
      (match b.opk with
       | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
       | none => memRegion (fsp + 0x439#64) 32) ⊢
        memRegion (fsp + 0x439#64) 32 := by
    cases b.opk with
    | none => exact Entails.refl _
    | some pk =>
      exact pointsToBytes_entails_memRegion_len (fsp + 0x439#64) pk.2.bytes.toList 32
        (List.Vector.toList_length pk.2.bytes)
  rw [ProofLib.memRegion_split' (b := fsp + 0x298#64) (n := 32) (k := 424)
        (b' := fsp + 0x2b8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x2b8#64) (n := 0x48) (k := 352)
        (b' := fsp + 0x300#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x300#64) (n := 4) (k := 348)
        (b' := fsp + 0x304#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x304#64) (n := 4) (k := 344)
        (b' := fsp + 0x308#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x308#64) (n := 0x40) (k := 280)
        (b' := fsp + 0x348#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x348#64) (n := 32) (k := 248)
        (b' := fsp + 0x368#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x368#64) (n := 32) (k := 216)
        (b' := fsp + 0x388#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x388#64) (n := 32) (k := 184)
        (b' := fsp + 0x3a8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x3a8#64) (n := 32) (k := 152)
        (b' := fsp + 0x3c8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x3c8#64) (n := 32) (k := 120)
        (b' := fsp + 0x3e8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x3e8#64) (n := 32) (k := 88)
        (b' := fsp + 0x408#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x408#64) (n := 32) (k := 56)
        (b' := fsp + 0x428#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x428#64) (n := 8) (k := 48)
        (b' := fsp + 0x430#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x430#64) (n := 8) (k := 40)
        (b' := fsp + 0x438#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x438#64) (n := 1) (k := 39)
        (b' := fsp + 0x439#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x439#64) (n := 32) (k := 7)
        (b' := fsp + 0x459#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x459#64) (n := 1) (k := 6)
        (b' := fsp + 0x45a#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsToBytes_entails_memRegion_len _ _ 32 hekA)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsToBytes_entails_memRegion_len _ _ 32
        (List.Vector.toList_length kp.identityKey.publicKey.bytes))
    (sepConj_mono (pointsToBytes_entails_memRegion_len _ _ 32
        (List.Vector.toList_length kp.privateKey.bytes))
    (sepConj_mono (pointsToBytes_entails_memRegion_len _ _ 32 hekA)
    (sepConj_mono (pointsToBytes_entails_memRegion_len _ _ 32 hekASk)
    (sepConj_mono (pointsToBytes_entails_memRegion_len _ _ 32
        (List.Vector.toList_length b.idKey.publicKey.bytes))
    (sepConj_mono (pointsToBytes_entails_memRegion_len _ _ 32
        (List.Vector.toList_length b.spk.bytes))
    (sepConj_mono (pointsToBytes_entails_memRegion_len _ _ 32
        (List.Vector.toList_length b.spk.bytes))
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono hopk
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (Entails.refl _)))))))))))))))))

theorem initSaved_entails_memRegion (s0 : State) :
    initSaved s0 ⊢ memRegion (s0.sp - 0x60#64) 0x60 := by
  unfold initSaved
  dsimp only
  rw [BitVec.add_zero (s0.sp - 0x60#64),
      ProofLib.memRegion_split' (b := s0.sp - 0x60#64) (n := 8) (k := 88)
        (b' := (s0.sp - 0x60#64) + 0x08#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := (s0.sp - 0x60#64) + 0x08#64) (n := 8) (k := 80)
        (b' := (s0.sp - 0x60#64) + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := (s0.sp - 0x60#64) + 0x10#64) (n := 8) (k := 72)
        (b' := (s0.sp - 0x60#64) + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := (s0.sp - 0x60#64) + 0x18#64) (n := 8) (k := 64)
        (b' := (s0.sp - 0x60#64) + 0x20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := (s0.sp - 0x60#64) + 0x20#64) (n := 8) (k := 56)
        (b' := (s0.sp - 0x60#64) + 0x28#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := (s0.sp - 0x60#64) + 0x28#64) (n := 8) (k := 48)
        (b' := (s0.sp - 0x60#64) + 0x30#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := (s0.sp - 0x60#64) + 0x30#64) (n := 8) (k := 40)
        (b' := (s0.sp - 0x60#64) + 0x38#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := (s0.sp - 0x60#64) + 0x38#64) (n := 8) (k := 32)
        (b' := (s0.sp - 0x60#64) + 0x40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := (s0.sp - 0x60#64) + 0x40#64) (n := 8) (k := 24)
        (b' := (s0.sp - 0x60#64) + 0x48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := (s0.sp - 0x60#64) + 0x48#64) (n := 8) (k := 16)
        (b' := (s0.sp - 0x60#64) + 0x50#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := (s0.sp - 0x60#64) + 0x50#64) (n := 8) (k := 8)
        (b' := (s0.sp - 0x60#64) + 0x58#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)))))))))))

theorem stage4FrameRegions_entails_stackAt {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (img : Obj.Image) (x : InitGhost) (kp : IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (b5b8 b5b9 : BitVec 8) (s0 : State)
    (hekA : ekAPk.length = 32) (hekASk : ekASk.length = 32) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
    memRegion fsp 0xd0 ∗
      initArgsAt img fsp x s0 ∗
      initFreshRecAt fsp ∗
      memRegion (fsp + 0x148#64) 0x150 ∗
      (((fsp + 0x298#64) ↦ₛ ekAPk) ∗
        memRegion (fsp + 0x2b8#64) 0x48 ∗
        ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
        memRegion (fsp + 0x308#64) 0x40 ∗
        ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
        ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
        ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((fsp + 0x3e8#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
        (match x.bundle.opk with
         | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
         | none => memRegion (fsp + 0x439#64) 32) ∗
        ((fsp + 0x459#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x45a#64) 6) ∗
      memRegion (fsp + 0x460#64) 0x158 ∗
      ((fsp + 0x5b8#64) ↦₈ b5b8) ∗ ((fsp + 0x5b9#64) ↦₈ b5b9) ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
      memRegion (s0.sp - 0x60#64) 0x60 ∗
      stackAt fsp (stk - cliInitiateFrame) ⊢
      stackAt s0.sp stk := by
  intro fsp opkFlag
  have hge := stk_ge_frame hstk
  have hlocals :
      memRegion fsp 0xd0 ∗
      memRegion (fsp + 0xd0#64) 0x58 ∗
      memRegion (fsp + 0x128#64) 0x20 ∗
      memRegion (fsp + 0x148#64) 0x150 ∗
      memRegion (fsp + 0x298#64) 0x1c8 ∗
      memRegion (fsp + 0x460#64) 0x158 ∗
      memRegion (fsp + 0x5b8#64) 1 ∗
      memRegion (fsp + 0x5b9#64) 1 ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) =
        memRegion fsp initLocalsSize := by
    change memRegion fsp 0xd0 ∗
      memRegion (fsp + 0xd0#64) 0x58 ∗
      memRegion (fsp + 0x128#64) 0x20 ∗
      memRegion (fsp + 0x148#64) 0x150 ∗
      memRegion (fsp + 0x298#64) 0x1c8 ∗
      memRegion (fsp + 0x460#64) 0x158 ∗
      memRegion (fsp + 0x5b8#64) 1 ∗
      memRegion (fsp + 0x5b9#64) 1 ∗
      memRegion (fsp + 0x5ba#64) 5846 = memRegion fsp 7312
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0xd0) (k := 7104)
          (b' := fsp + 0xd0#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0xd0#64) (n := 0x58) (k := 7016)
          (b' := fsp + 0x128#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x128#64) (n := 0x20) (k := 6984)
          (b' := fsp + 0x148#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x148#64) (n := 0x150) (k := 6648)
          (b' := fsp + 0x298#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x298#64) (n := 0x1c8) (k := 6192)
          (b' := fsp + 0x460#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x460#64) (n := 0x158) (k := 5848)
          (b' := fsp + 0x5b8#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x5b8#64) (n := 1) (k := 5847)
          (b' := fsp + 0x5b9#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x5b9#64) (n := 1) (k := 5846)
          (b' := fsp + 0x5ba#64) rfl (by bv_omega) (by decide)]
  have hframe :
      memRegion fsp initLocalsSize ∗ memRegion (s0.sp - 0x60#64) 0x60 =
        memRegion fsp cliInitiateFrame :=
    (ProofLib.memRegion_split' (b := fsp) (n := 7312) (k := 96)
      (b' := s0.sp - 0x60#64) rfl (by dsimp [fsp, cliInitiateFrame]; bv_omega) (by decide)).symm
  have hstk_merge :
      stackAt fsp (stk - cliInitiateFrame) ∗ memRegion fsp cliInitiateFrame =
        stackAt s0.sp stk := by
    dsimp only [stackAt]
    have hbase : fsp - BitVec.ofNat 64 (stk - cliInitiateFrame) = s0.sp - BitVec.ofNat 64 stk := by
      dsimp only [fsp]
      have hsub : BitVec.ofNat 64 cliInitiateFrame + BitVec.ofNat 64 (stk - cliInitiateFrame) =
          BitVec.ofNat 64 stk :=
        bv64_ofNat_add_eq_of_mod (by omega)
      bv_omega
    rw [hbase]
    exact (ProofLib.memRegion_split' (b := s0.sp - BitVec.ofNat 64 stk)
      (n := stk - cliInitiateFrame) (k := cliInitiateFrame) (b' := fsp)
      (by omega) (by rw [← hbase]; bv_omega) (by omega)).symm
  refine Entails.trans
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (initArgsAt_entails_memRegion img fsp x s0)
    (sepConj_mono (initFreshRecAt_entails_memRegion fsp)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (stage3KeySlotsNoHeap_entails_memRegion fsp x.bundle kp ekASk ekAPk
        pqspkPtr opkId hekA hekASk)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (Entails.refl _))))))))) ?_
  have heq :
      memRegion fsp 0xd0 ∗
      memRegion (fsp + 0xd0#64) 0x58 ∗
      memRegion (fsp + 0x128#64) 0x20 ∗
      memRegion (fsp + 0x148#64) 0x150 ∗
      memRegion (fsp + 0x298#64) 0x1c8 ∗
      memRegion (fsp + 0x460#64) 0x158 ∗
      memRegion (fsp + 0x5b8#64) 1 ∗
      memRegion (fsp + 0x5b9#64) 1 ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
      memRegion (s0.sp - 0x60#64) 0x60 ∗
      stackAt fsp (stk - cliInitiateFrame) =
        stackAt s0.sp stk := by
    have h1 :
        memRegion fsp 0xd0 ∗
        memRegion (fsp + 0xd0#64) 0x58 ∗
        memRegion (fsp + 0x128#64) 0x20 ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        memRegion (fsp + 0x298#64) 0x1c8 ∗
        memRegion (fsp + 0x460#64) 0x158 ∗
        memRegion (fsp + 0x5b8#64) 1 ∗
        memRegion (fsp + 0x5b9#64) 1 ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
        memRegion (s0.sp - 0x60#64) 0x60 ∗
        stackAt fsp (stk - cliInitiateFrame) =
        stackAt fsp (stk - cliInitiateFrame) ∗
          ((memRegion fsp 0xd0 ∗
            memRegion (fsp + 0xd0#64) 0x58 ∗
            memRegion (fsp + 0x128#64) 0x20 ∗
            memRegion (fsp + 0x148#64) 0x150 ∗
            memRegion (fsp + 0x298#64) 0x1c8 ∗
            memRegion (fsp + 0x460#64) 0x158 ∗
            memRegion (fsp + 0x5b8#64) 1 ∗
            memRegion (fsp + 0x5b9#64) 1 ∗
            memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba)) ∗
           memRegion (s0.sp - 0x60#64) 0x60) := by ac_rfl
    rw [h1, hlocals, hframe, hstk_merge]
  exact Entails.of_eq heq

/-! ## Pre-Stage-5 `SessionState` and `SessionGhost` Folding -/

def stage5SessionState (ourIdentity theirIdentity : IdentityKey)
    (theirRatchetKey : PublicKey) (rk1 : RootKey) (ck0 : BitVec 256)
    (sendingKeyPair : KeyPair) (ck1 : ChainKey)
    (pq : List (BitVec 8)) : SessionState (List (BitVec 8)) :=
  { sessionVersion := 4#32
    localIdentity := ourIdentity
    remoteIdentity := some theirIdentity
    rootKey := rk1
    previousCounter := 0#32
    senderChain := some ⟨sendingKeyPair, ck1⟩
    receiverChains := [⟨theirRatchetKey, some ⟨ck0, 0#32⟩, []⟩]
    pendingPreKey := false
    pqRatchetState := pq }

def stage5SessionGhost
    (ourIdentity theirIdentity : IdentityKey) (theirRatchetKey baseKey : PublicKey)
    (sendingKeyPair : KeyPair)
    (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr baseKeyBoxPtr
     spqrCap spqrBufPtr
     receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
     senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
     kemCtSerPtr : BitVec 64)
    (pad_144 : BitVec 32)
    (kemCtSer : List (BitVec 8)) : SessionGhost :=
  { localIk := ⟨33#64, localIkBoxPtr, ourIdentity.publicKey.serialize⟩
    remoteIk := ⟨33#64, remoteIkBoxPtr, theirIdentity.publicKey.serialize⟩
    root := ⟨32#64, rootKeyBoxPtr⟩
    chainsCap := 4#64
    chainsPtr := chainBufPtr
    chains := [⟨⟨33#64, receiverRatchetPubBoxPtr, theirRatchetKey.serialize⟩,
                ⟨0#64, 1#64, []⟩, 0#64, 8#64, [], ⟨32#64, receiverChainKeyBoxPtr⟩⟩]
    alice := ⟨33#64, baseKeyBoxPtr, baseKey.serialize⟩
    pq := ⟨spqrCap, spqrBufPtr⟩
    sender := some ⟨⟨33#64, senderRatchetPubBoxPtr, sendingKeyPair.publicKey.serialize⟩,
                    ⟨32#64, senderRatchetPrivBoxPtr, sendingKeyPair.privateKey.bytes.toList⟩,
                    0#64, 8#64, ⟨32#64, senderChainKeyBoxPtr⟩⟩
    pending := none
    kyber := some ⟨⟨1569#64, kemCtSerPtr, kemCtSer⟩,
                   unpack32 0xffffffff#32 ++ unpack32 pad_144⟩
    regIds := unpack64 0#64 }

theorem sessionInline_stage5
    (ourIdentity theirIdentity : IdentityKey) (theirRatchetKey baseKey : PublicKey)
    (rk1 : RootKey) (ck0 : BitVec 256) (sendingKeyPair : KeyPair) (ck1 : ChainKey)
    (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr baseKeyBoxPtr
     spqrCap spqrBufPtr
     receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
     senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
     kemCtSerPtr : BitVec 64)
    (pad_f4 pad_144 : BitVec 32)
    (pad40 kemCtSer pq : List (BitVec 8))
    (hpad40 : pad40.length = 40)
    (hck1_idx : ck1.index = 0#32)
    (hkem_len : kemCtSer.length = 1569) :
    RawByteMove.SessionInline
      (stage5SessionGhost ourIdentity theirIdentity theirRatchetKey baseKey sendingKeyPair
        localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr baseKeyBoxPtr
        spqrCap spqrBufPtr
        receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
        senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
        kemCtSerPtr pad_144 kemCtSer)
      (stage5SessionState ourIdentity theirIdentity theirRatchetKey rk1 ck0 sendingKeyPair ck1 pq)
      (aliceSession344Bv8 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr baseKeyBoxPtr
        spqrCap spqrBufPtr (BitVec.ofNat 64 pq.length)
        senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
        pad_f4 pad40 1569#64 kemCtSerPtr 1569#64 0xffffffff#32 pad_144) := by
  refine ⟨by simp [stage5SessionGhost, unpack64], ?_⟩
  refine ⟨senderChainBytes100 senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
            0#32 ++ unpack32 pad_f4,
          unpack64 0xffffffffffffffff#64 ++ pad40,
          vecHeaderBytes 1569#64 kemCtSerPtr 1569#64 ++
            (unpack32 0xffffffff#32 ++ unpack32 pad_144),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [senderChainBytes100_length, unpack32]
  · dsimp only [RawByteMove.OptSenderChainInline, stage5SessionGhost, stage5SessionState,
      SenderChainGhost.toChainGhost, SenderChain.toReceiverChain, RawByteMove.ChainInline]
    refine ⟨vecHeaderBytes 32#64 senderChainKeyBoxPtr 32#64 ++ unpack32 0#32 ++ unpack32 pad_f4,
      by simp [vecHeaderBytes, unpack64, unpack32], ?_, ?_⟩
    · dsimp only [RawByteMove.OptChainKeyInline]
      refine ⟨unpack32 pad_f4, by simp [unpack32], ?_⟩
      rw [hck1_idx]
    · simp [RawByteMove.chainPrefixBytes, RawByteMove.vecGhostHeaderBytes, vecHeaderBytes,
        senderChainBytes100, PublicKey.serialize_length, List.Vector.toList_length,
        List.append_assoc]
  · simp [unpack64, hpad40]
  · dsimp only [RawByteMove.OptTailVecInline]
    exact ⟨pad40, hpad40, rfl⟩
  · simp [vecHeaderBytes, unpack64, unpack32]
  · dsimp only [RawByteMove.OptTailVecInline, stage5SessionGhost, RawByteMove.vecGhostHeaderBytes]
    refine ⟨by simp [unpack32], ?_⟩
    rw [hkem_len]
  · simp [aliceSession344Bv8, aliceHead144Bv8, alicePre72Bv8, receiverChainVecBytes24,
      aliceMid48Bv8, senderChainBytes100, aliceTail100Bv8,
      RawByteMove.sessionPrefixBytes, RawByteMove.sessionSuffixBytes,
      RawByteMove.vecGhostHeaderBytes,
      vecHeaderBytes, stage5SessionGhost, stage5SessionState,
      PublicKey.serialize_length, List.append_assoc]
    decide

theorem sessionHeap_stage5 (A : RustAlloc)
    (ourIdentity theirIdentity : IdentityKey) (theirRatchetKey baseKey : PublicKey)
    (rk1 : RootKey) (ck0 : BitVec 256) (sendingKeyPair : KeyPair) (ck1 : ChainKey)
    (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr baseKeyBoxPtr
     spqrCap spqrBufPtr
     receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
     senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
     kemCtSerPtr : BitVec 64)
    (pad_144 : BitVec 32)
    (kemCtSer pq : List (BitVec 8))
    (hlocalIk : localIkBoxPtr ≠ 0#64)
    (hremoteIk : remoteIkBoxPtr ≠ 0#64)
    (hroot : rootKeyBoxPtr ≠ 0#64)
    (hcb : chainBufPtr ≠ 0#64)
    (hbase : baseKeyBoxPtr ≠ 0#64)
    (hrpub : receiverRatchetPubBoxPtr ≠ 0#64)
    (hrck : receiverChainKeyBoxPtr ≠ 0#64)
    (hspub : senderRatchetPubBoxPtr ≠ 0#64)
    (hspriv : senderRatchetPrivBoxPtr ≠ 0#64)
    (hsck : senderChainKeyBoxPtr ≠ 0#64)
    (hkem : kemCtSerPtr ≠ 0#64)
    (hclamp : Ratchet.clampScalar sendingKeyPair.privateKey.bytes = sendingKeyPair.privateKey.bytes)
    (hkem_len : kemCtSer.length = 1569) :
    ((localIkBoxPtr ↦ₛ ourIdentity.publicKey.serialize) ∗ A.live localIkBoxPtr 33 1) ∗
    ((remoteIkBoxPtr ↦ₛ theirIdentity.publicKey.serialize) ∗ A.live remoteIkBoxPtr 33 1) ∗
    ((rootKeyBoxPtr ↦ₛ keyToBytes32 rk1) ∗ A.live rootKeyBoxPtr 32 1) ∗
    (A.live chainBufPtr 416 8 ∗
     receiverChainElemAt chainBufPtr receiverRatchetPubBoxPtr receiverChainKeyBoxPtr 0#32 ∗
     memRegion (chainBufPtr + 0x64#64) 316 ∗
     (receiverRatchetPubBoxPtr ↦ₛ theirRatchetKey.serialize) ∗
       A.live receiverRatchetPubBoxPtr 33 1 ∗
     (receiverChainKeyBoxPtr ↦ₛ keyToBytes32 ck0) ∗ A.live receiverChainKeyBoxPtr 32 1) ∗
    ((baseKeyBoxPtr ↦ₛ baseKey.serialize) ∗ A.live baseKeyBoxPtr 33 1) ∗
    vecU8Buf A spqrCap spqrBufPtr pq ∗
    ((senderRatchetPubBoxPtr ↦ₛ sendingKeyPair.publicKey.serialize) ∗
      A.live senderRatchetPubBoxPtr 33 1) ∗
    ((senderRatchetPrivBoxPtr ↦ₛ sendingKeyPair.privateKey.bytes.toList) ∗
      A.live senderRatchetPrivBoxPtr 32 1) ∗
    ((senderChainKeyBoxPtr ↦ₛ keyToBytes32 ck1.key) ∗ A.live senderChainKeyBoxPtr 32 1) ∗
    ((kemCtSerPtr ↦ₛ kemCtSer) ∗ A.live kemCtSerPtr 1569 1) ⊢
      RawByteMove.sessionHeap A
        (stage5SessionGhost ourIdentity theirIdentity theirRatchetKey baseKey sendingKeyPair
          localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr baseKeyBoxPtr
          spqrCap spqrBufPtr
          receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
          senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
          kemCtSerPtr pad_144 kemCtSer)
        (stage5SessionState ourIdentity theirIdentity theirRatchetKey rk1 ck0 sendingKeyPair ck1
          pq) := by
  unfold RawByteMove.sessionHeap RawByteMove.vecGhostHeap RawByteMove.optSenderChainHeap
    RawByteMove.protoChainHeap RawByteMove.optChainKeyHeap RawByteMove.optTailVecHeap
  dsimp only [stage5SessionGhost, stage5SessionState,
    SenderChainGhost.toChainGhost, SenderChain.toReceiverChain, List.zip_cons_cons,
    List.zip_nil_right]
  have hpure :
      RawByteMove.SessionPure
        (stage5SessionGhost ourIdentity theirIdentity theirRatchetKey baseKey sendingKeyPair
          localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr chainBufPtr baseKeyBoxPtr
          spqrCap spqrBufPtr
          receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
          senderRatchetPubBoxPtr senderRatchetPrivBoxPtr senderChainKeyBoxPtr
          kemCtSerPtr pad_144 kemCtSer)
        (stage5SessionState ourIdentity theirIdentity theirRatchetKey rk1 ck0 sendingKeyPair ck1
          pq) :=
    ⟨deserialize_serialize_pk_init ourIdentity.publicKey,
     deserialize_serialize_pk_init theirIdentity.publicKey,
     rfl, rfl, by simp [stage5SessionGhost, unpack64],
     PublicKey.serialize_length ourIdentity.publicKey,
     fun _ => PublicKey.serialize_length theirIdentity.publicKey⟩
  refine Entails.pure_right hpure ?_
  have h1 := vecU8Buf_of_live_pointsToBytes A 33#64 localIkBoxPtr ourIdentity.publicKey.serialize
    33 rfl (by decide) (by decide) (PublicKey.serialize_length ourIdentity.publicKey) hlocalIk
  have h2 := vecU8Buf_of_live_pointsToBytes A 33#64 remoteIkBoxPtr theirIdentity.publicKey.serialize
    33 rfl (by decide) (by decide) (PublicKey.serialize_length theirIdentity.publicKey) hremoteIk
  have h3 := vecU8Buf_of_live_pointsToBytes A 32#64 rootKeyBoxPtr (keyToBytes32 rk1)
    32 rfl (by decide) (by decide) (by simp [keyToBytes32]) hroot
  have h4 := receiverChainsVecBuf_aliceInitiated A chainBufPtr receiverRatchetPubBoxPtr
    receiverChainKeyBoxPtr theirRatchetKey ck0 hcb hrpub hrck
  have h5 := vecU8Buf_of_live_pointsToBytes A 33#64 baseKeyBoxPtr baseKey.serialize
    33 rfl (by decide) (by decide) (PublicKey.serialize_length baseKey) hbase
  have h6 : vecU8Buf A spqrCap spqrBufPtr pq ⊢ vecU8Buf A spqrCap spqrBufPtr pq := Entails.refl _
  have h7_spub := vecU8Buf_of_live_pointsToBytes A 33#64 senderRatchetPubBoxPtr
    sendingKeyPair.publicKey.serialize 33 rfl (by decide) (by decide)
    (PublicKey.serialize_length sendingKeyPair.publicKey) hspub
  have h7_spriv := vecU8Buf_of_live_pointsToBytes A 32#64 senderRatchetPrivBoxPtr
    sendingKeyPair.privateKey.bytes.toList 32 rfl (by decide) (by decide)
    (List.Vector.toList_length sendingKeyPair.privateKey.bytes) hspriv
  have h7_mk := vecBuf_empty_0_8_init A 104 (messageKeyAt A)
  have h7_sck := vecU8Buf_of_live_pointsToBytes A 32#64 senderChainKeyBoxPtr
    (keyToBytes32 ck1.key) 32 rfl (by decide) (by decide) (by simp [keyToBytes32]) hsck
  have h7 :
      ((senderRatchetPubBoxPtr ↦ₛ sendingKeyPair.publicKey.serialize) ∗
        A.live senderRatchetPubBoxPtr 33 1) ∗
      ((senderRatchetPrivBoxPtr ↦ₛ sendingKeyPair.privateKey.bytes.toList) ∗
        A.live senderRatchetPrivBoxPtr 32 1) ∗
      ((senderChainKeyBoxPtr ↦ₛ keyToBytes32 ck1.key) ∗ A.live senderChainKeyBoxPtr 32 1) ⊢
        ⌜RawByteMove.SenderChainPrivPure
          ⟨⟨33#64, senderRatchetPubBoxPtr, sendingKeyPair.publicKey.serialize⟩,
           ⟨32#64, senderRatchetPrivBoxPtr, sendingKeyPair.privateKey.bytes.toList⟩,
           0#64, 8#64, ⟨32#64, senderChainKeyBoxPtr⟩⟩
          ⟨sendingKeyPair, ck1⟩⌝ ∗
        ⌜RawByteMove.ProtoChainPure
          (⟨⟨33#64, senderRatchetPubBoxPtr, sendingKeyPair.publicKey.serialize⟩,
            ⟨32#64, senderRatchetPrivBoxPtr, sendingKeyPair.privateKey.bytes.toList⟩,
            0#64, 8#64, [], ⟨32#64, senderChainKeyBoxPtr⟩⟩,
           ⟨sendingKeyPair.publicKey, some ck1, []⟩)⌝ ∗
        vecU8Buf A 33#64 senderRatchetPubBoxPtr sendingKeyPair.publicKey.serialize ∗
        vecU8Buf A 32#64 senderRatchetPrivBoxPtr sendingKeyPair.privateKey.bytes.toList ∗
        vecBuf A 104 8 (messageKeyAt A) 0#64 8#64 [] ∗
        vecU8Buf A 32#64 senderChainKeyBoxPtr (keyToBytes32 ck1.key) := by
    refine Entails.pure_right ⟨rfl, hclamp⟩ ?_
    refine Entails.pure_right ⟨deserialize_serialize_pk_init sendingKeyPair.publicKey,
      Nat.zero_le _, rfl, PublicKey.serialize_length sendingKeyPair.publicKey⟩ ?_
    have heq_emp :
        (((senderRatchetPubBoxPtr ↦ₛ sendingKeyPair.publicKey.serialize) ∗
          A.live senderRatchetPubBoxPtr 33 1) ∗
         ((senderRatchetPrivBoxPtr ↦ₛ sendingKeyPair.privateKey.bytes.toList) ∗
           A.live senderRatchetPrivBoxPtr 32 1) ∗
         ((senderChainKeyBoxPtr ↦ₛ keyToBytes32 ck1.key) ∗ A.live senderChainKeyBoxPtr 32 1)) =
        (((senderRatchetPubBoxPtr ↦ₛ sendingKeyPair.publicKey.serialize) ∗
          A.live senderRatchetPubBoxPtr 33 1) ∗
         ((senderRatchetPrivBoxPtr ↦ₛ sendingKeyPair.privateKey.bytes.toList) ∗
           A.live senderRatchetPrivBoxPtr 32 1) ∗
         emp ∗
         ((senderChainKeyBoxPtr ↦ₛ keyToBytes32 ck1.key) ∗
           A.live senderChainKeyBoxPtr 32 1)) := by ac_rfl
    rw [heq_emp]
    exact sepConj_mono h7_spub (sepConj_mono h7_spriv (sepConj_mono h7_mk h7_sck))
  have h9 := vecU8Buf_of_live_pointsToBytes A 1569#64 kemCtSerPtr kemCtSer
    1569 rfl (by decide) (by decide) hkem_len hkem
  have heq_all :
      (((localIkBoxPtr ↦ₛ ourIdentity.publicKey.serialize) ∗ A.live localIkBoxPtr 33 1) ∗
       ((remoteIkBoxPtr ↦ₛ theirIdentity.publicKey.serialize) ∗ A.live remoteIkBoxPtr 33 1) ∗
       ((rootKeyBoxPtr ↦ₛ keyToBytes32 rk1) ∗ A.live rootKeyBoxPtr 32 1) ∗
       (A.live chainBufPtr 416 8 ∗
        receiverChainElemAt chainBufPtr receiverRatchetPubBoxPtr receiverChainKeyBoxPtr 0#32 ∗
        memRegion (chainBufPtr + 0x64#64) 316 ∗
        (receiverRatchetPubBoxPtr ↦ₛ theirRatchetKey.serialize) ∗
          A.live receiverRatchetPubBoxPtr 33 1 ∗
        (receiverChainKeyBoxPtr ↦ₛ keyToBytes32 ck0) ∗ A.live receiverChainKeyBoxPtr 32 1) ∗
       ((baseKeyBoxPtr ↦ₛ baseKey.serialize) ∗ A.live baseKeyBoxPtr 33 1) ∗
       vecU8Buf A spqrCap spqrBufPtr pq ∗
       ((senderRatchetPubBoxPtr ↦ₛ sendingKeyPair.publicKey.serialize) ∗
         A.live senderRatchetPubBoxPtr 33 1) ∗
       ((senderRatchetPrivBoxPtr ↦ₛ sendingKeyPair.privateKey.bytes.toList) ∗
         A.live senderRatchetPrivBoxPtr 32 1) ∗
       ((senderChainKeyBoxPtr ↦ₛ keyToBytes32 ck1.key) ∗ A.live senderChainKeyBoxPtr 32 1) ∗
       ((kemCtSerPtr ↦ₛ kemCtSer) ∗ A.live kemCtSerPtr 1569 1)) =
      (((localIkBoxPtr ↦ₛ ourIdentity.publicKey.serialize) ∗ A.live localIkBoxPtr 33 1) ∗
       ((remoteIkBoxPtr ↦ₛ theirIdentity.publicKey.serialize) ∗ A.live remoteIkBoxPtr 33 1) ∗
       ((rootKeyBoxPtr ↦ₛ keyToBytes32 rk1) ∗ A.live rootKeyBoxPtr 32 1) ∗
       (A.live chainBufPtr 416 8 ∗
        receiverChainElemAt chainBufPtr receiverRatchetPubBoxPtr receiverChainKeyBoxPtr 0#32 ∗
        memRegion (chainBufPtr + 0x64#64) 316 ∗
        (receiverRatchetPubBoxPtr ↦ₛ theirRatchetKey.serialize) ∗
          A.live receiverRatchetPubBoxPtr 33 1 ∗
        (receiverChainKeyBoxPtr ↦ₛ keyToBytes32 ck0) ∗ A.live receiverChainKeyBoxPtr 32 1) ∗
       ((baseKeyBoxPtr ↦ₛ baseKey.serialize) ∗ A.live baseKeyBoxPtr 33 1) ∗
       vecU8Buf A spqrCap spqrBufPtr pq ∗
       (((senderRatchetPubBoxPtr ↦ₛ sendingKeyPair.publicKey.serialize) ∗
          A.live senderRatchetPubBoxPtr 33 1) ∗
        ((senderRatchetPrivBoxPtr ↦ₛ sendingKeyPair.privateKey.bytes.toList) ∗
          A.live senderRatchetPrivBoxPtr 32 1) ∗
        ((senderChainKeyBoxPtr ↦ₛ keyToBytes32 ck1.key) ∗ A.live senderChainKeyBoxPtr 32 1)) ∗
       emp ∗
       ((kemCtSerPtr ↦ₛ kemCtSer) ∗ A.live kemCtSerPtr 1569 1)) := by ac_rfl
  rw [heq_all]
  exact sepConj_mono h1
    (sepConj_mono h2
    (sepConj_mono h3
    (sepConj_mono h4
    (sepConj_mono h5
    (sepConj_mono h6
    (sepConj_mono h7
    (sepConj_mono (Entails.refl emp) h9)))))))

theorem initializeInitiatorSession_eq_ok_stage5_ext
    (P : PEParams) (ourIdentity theirIdentity : IdentityKey) (theirRatchetKey : PublicKey)
    (rk0 ck0 pqrKey : BitVec 256) (coins : List (BitVec 8))
    (rk1 : RootKey) (ck1 : ChainKey)
    (hcc : rootCreateChain P.C rk0 theirRatchetKey
      ⟨Ratchet.clampScalar ⟨((padCoins coins).toList.drop 160).take 32, by simp; decide⟩⟩ =
      .ok (rk1, ck1)) :
    let ephVec : List.Vector (BitVec 8) 32 :=
      ⟨((padCoins coins).toList.drop 160).take 32, by simp; decide⟩
    let sendingKeyPair : KeyPair :=
      { publicKey := ⟨P.C.pubKey (Ratchet.clampScalar ephVec)⟩
        privateKey := ⟨Ratchet.clampScalar ephVec⟩ }
    let pq : List (BitVec 8) := (pqxdhSpqrSession P).init .a2b pqrKey
    initializeInitiatorSession P.C (pqxdhSpqrSession P)
      ourIdentity theirIdentity theirRatchetKey rk0 ck0 pqrKey
      (HKDF.bytesToKey32 (((padCoins coins).toList.drop 160).take 32)) =
      .ok (stage5SessionState ourIdentity theirIdentity theirRatchetKey rk1 ck0 sendingKeyPair
        ck1 pq) := by
  intro ephVec sendingKeyPair pq
  have hkvec :
      Ratchet.keyToBytesVec32 (HKDF.bytesToKey32 (((padCoins coins).toList.drop 160).take 32)) =
        ephVec := by
    apply Subtype.ext
    exact Keys.keyToBytes32_bytesToKey32 (((padCoins coins).toList.drop 160).take 32)
      (by simp; decide)
  have hgen :
      KeyPair.generate P.C (HKDF.bytesToKey32 (((padCoins coins).toList.drop 160).take 32)) =
        sendingKeyPair := by
    unfold KeyPair.generate
    dsimp only [sendingKeyPair]
    rw [hkvec]
  unfold initializeInitiatorSession
  dsimp only
  rw [hgen, hcc]
  rfl

theorem initializeInitiatorSession_eq_ok_stage5
    (W : CliHooks) (ourIdentity theirIdentity : IdentityKey) (theirRatchetKey : PublicKey)
    (rk0 ck0 pqrKey : BitVec 256) (coins : List (BitVec 8))
    (rk1 : RootKey) (ck1 : ChainKey)
    (hcc : rootCreateChain W.C rk0 theirRatchetKey
      ⟨Ratchet.clampScalar ⟨((padCoins coins).toList.drop 160).take 32, by simp; decide⟩⟩ =
      .ok (rk1, ck1)) :
    let ephVec : List.Vector (BitVec 8) 32 :=
      ⟨((padCoins coins).toList.drop 160).take 32, by simp; decide⟩
    let sendingKeyPair : KeyPair :=
      { publicKey := ⟨W.C.pubKey (Ratchet.clampScalar ephVec)⟩
        privateKey := ⟨Ratchet.clampScalar ephVec⟩ }
    let pq : List (BitVec 8) := (pqxdhSpqrSession ⟨W.C, W.Q⟩).init .a2b pqrKey
    initializeInitiatorSession W.C (pqxdhSpqrSession ⟨W.C, W.Q⟩)
      ourIdentity theirIdentity theirRatchetKey rk0 ck0 pqrKey
      (HKDF.bytesToKey32 (((padCoins coins).toList.drop 160).take 32)) =
      .ok (stage5SessionState ourIdentity theirIdentity theirRatchetKey rk1 ck0 sendingKeyPair
        ck1 pq) :=
  initializeInitiatorSession_eq_ok_stage5_ext ⟨W.C, W.Q⟩ ourIdentity theirIdentity theirRatchetKey
    rk0 ck0 pqrKey coins rk1 ck1 hcc

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
