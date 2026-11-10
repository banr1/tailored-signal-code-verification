/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.AllocWitness
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalSessionProofDefs
import ProofLib.VCGen

@[expose] public section

namespace CryptoVerification.LibsignalSession.NonVacuityWitness

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-! ## Concrete Ghost Witness -/

def pk0 : PublicKey := ⟨⟨List.replicate 32 0#8, by simp⟩⟩

theorem deserialize_pk0_serialize : PublicKey.deserialize pk0.serialize = .ok pk0 := by
  decide

def c0 : ReceiverChain :=
  { senderRatchetKey := pk0
    chainKey := none
    messageKeys := [] }

def st0 : RatchetState :=
  { rootKey := 0#256
    senderChain := none
    receiverChains := [c0]
    previousCounter := 0#32
    maxForwardJumps := 25000 }

def ck0 : ChainKey :=
  { key := 0#256
    index := 3#32 }

def g0 (B : BitVec 64) : ChainGhost :=
  { srk := ⟨33#64, B + 280#64, pk0.serialize⟩
    priv := ⟨0#64, 1#64, []⟩
    mkCap := 0#64
    mkPtr := 8#64
    keys := []
    ck := ⟨0#64, 1#64⟩ }

def G0 (B : BitVec 64) : RatchetGhost :=
  { chainsCap := 1#64
    chainsPtr := B + 176#64
    chains := [g0 B]
    senderPad := List.replicate 100 0#8 }

def witnessGhost (B : BitVec 64) : ConsumeMessageKeyGhost :=
  { self := B
    G := G0 B
    st := st0
    their := pk0
    theirA := B + 313#64
    ck := ck0
    ckA := B + 345#64
    counter := 5#32
    msgType := .whisper
    ret := B + 381#64 }

theorem witnessGhost_counter_gt (B : BitVec 64) :
    (witnessGhost B).counter.toNat > (witnessGhost B).ck.index.toNat + 1 := by
  dsimp only [witnessGhost, ck0]
  decide

theorem st0_findReceiverChainIndex : st0.findReceiverChainIndex pk0 = some 0 := by
  simp [st0, c0, RatchetState.findReceiverChainIndex, List.findIdx?, List.findIdx?.go]

theorem witnessGhost_findIdx (B : BitVec 64) :
    (witnessGhost B).st.findReceiverChainIndex (witnessGhost B).their = some 0 ∧
    ∃ (h0 : 0 < (witnessGhost B).G.chains.length), ((witnessGhost B).G.chains[0]'h0).mkCap = 0 := by
  refine ⟨st0_findReceiverChainIndex, ⟨by simp [witnessGhost, G0], rfl⟩⟩

set_option linter.unusedSimpArgs false in
theorem witnessGhost_model_ok (F : ShaState → List (BitVec 8) → ShaState) (B : BitVec 64) :
    ∃ k, ((witnessGhost B).model F).1 = .ok k := by
  let ck1 : ChainKey := ⟨bytesToKey32 (Ratchet.chainHmac F ck0.key Ratchet.chainKeySeed), 4#32⟩
  let ck2 : ChainKey := ⟨bytesToKey32 (Ratchet.chainHmac F ck1.key Ratchet.chainKeySeed), 5#32⟩
  refine ⟨ck2.messageKeys F, ?_⟩
  unfold ConsumeMessageKeyGhost.model witnessGhost RatchetState.consumeMessageKey
  have hlt0 : ¬ (5#32 < (3#32 : BitVec 32)) := by decide
  have hlt3 : (3#32 : BitVec 32) < 5#32 := by decide
  have hlt4 : (4#32 : BitVec 32) < 5#32 := by decide
  have hpk : (pk0 == pk0) = true := by decide
  simp [Mut.exec, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    ExceptT.lift, ExceptT.map, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
    StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.set, StateT.map,
    bind, pure, get, getThe, MonadStateOf.get, set, Functor.map,
    st0, c0, ck0, ck1, ck2, hlt0, hlt3, hlt4, hpk,
    RatchetState.advanceChain,
    RatchetState.storeSkippedKey, RatchetState.setReceiverChainKey,
    RatchetState.findReceiverChainIndex, List.findIdx?, List.findIdx?.go,
    ChainKey.nextChainKey, liftE, maxMessageKeys]

/-! ## Loaded Image Bounds -/

noncomputable abbrev dataOff : Nat := libsignalSessionImage.dataOff
noncomputable abbrev gotOff : Nat := libsignalSessionImage.gotOff
noncomputable abbrev logOff : Nat :=
  match Obj.lookup "log::MAX_LOG_LEVEL_FILTER" libsignalSessionImage.externData with
  | some (o, _) => o
  | none => 0

structure ImageFacts (img : Obj.Image) : Prop where
  base_aligned : img.base.toNat % 4096 = 0
  base_wrap : img.base.toNat + (gotOff + 8) ≤ 2 ^ 64
  got_end_le : gotOff + 8 ≤ 0x8000000
  code_eq : img.code = libsignalSessionImage.code
  code_len_le : img.code.length ≤ dataOff
  dataAddr_eq : img.dataAddr = img.base + BitVec.ofNat 64 dataOff
  data_len_le : dataOff + img.data.length ≤ logOff
  logAddr_eq : logFilterAddr img = img.base + BitVec.ofNat 64 logOff
  log_end_le : logOff + 8 ≤ gotOff
  gotAddr_eq : img.gotAddr = img.base + BitVec.ofNat 64 gotOff
  gotBytes_len : img.gotBytes.length = 8

theorem mem_of_lookup_eq_some {α : Type} {name : String} {v : α} {xs : List (String × α)}
    (h : Obj.lookup name xs = some v) : ∃ k, (k, v) ∈ xs := by
  unfold Obj.lookup at h
  cases hf : xs.find? (·.1 == name) with
  | none => rw [hf] at h; cases h
  | some p =>
    rw [hf, Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨p.1, List.mem_of_find?_eq_some hf⟩

theorem imageFacts_of_loads {img : Obj.Image} (hloads : Obj.Loads libsignalSessionImage img) :
    ImageFacts img := by
  obtain ⟨data, hdata, hal, hwf, hwrap, himg⟩ := ProofLib.ObjectLoad.load_eq_ok hloads
  have hgotLen : libsignalSessionImage.got.length = 1 := rfl
  have hgot_end : gotOff + 8 ≤ 0x8000000 := by decide
  have hlookup : Obj.lookup "log::MAX_LOG_LEVEL_FILTER" libsignalSessionImage.externData =
      some (logOff, 8) := rfl
  obtain ⟨k, hk_mem⟩ := mem_of_lookup_eq_some hlookup
  unfold Obj.LinkedImage.wellFormed at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  rcases hwf with ⟨⟨⟨⟨⟨⟨⟨⟨hcode_le, _⟩, _⟩, _⟩, _⟩, hext⟩, hrelocs⟩, _⟩, _⟩
  have hext_k := List.all_eq_true.mp hext (k, (logOff, 8)) hk_mem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hext_k
  have hdataEnd_le : libsignalSessionImage.dataEnd ≤ logOff := hext_k.1
  have hlog_end : logOff + 8 ≤ gotOff := hext_k.2
  have hrelocs' : libsignalSessionImage.relocs.all
      (fun r => decide (r.off + r.width ≤ libsignalSessionImage.data.length)) = true := by
    rw [List.all_eq_true] at hrelocs ⊢
    intro r hr
    have h := hrelocs r hr
    simp only [Bool.and_eq_true] at h
    exact h.2
  have hdata_len : data.length =
      (libsignalSessionImage.data ++ List.replicate libsignalSessionImage.bss 0).length :=
    ProofLib.ObjectLoad.RoDataFactsAux.foldlM_dataReloc_length
      libsignalSessionImage.relocs _ data hdata hrelocs'
      (by simp)
  simp only [List.length_append, List.length_replicate] at hdata_len
  have hdataEnd_eq : libsignalSessionImage.dataEnd = dataOff + data.length := by
    unfold Obj.LinkedImage.dataEnd
    rw [hdata_len, ← Nat.add_assoc]
  have himg_code : img.code = libsignalSessionImage.code := by rw [himg]
  have himg_dataAddr : img.dataAddr = img.base + BitVec.ofNat 64 dataOff := by
    rw [himg]
  have himg_data : img.data = data := by rw [himg]
  have himg_gotAddr : img.gotAddr = img.base + BitVec.ofNat 64 gotOff := by
    rw [himg]
  have himg_got : img.got = [Obj.GotEntry.value img.base (.tpoff 0x10)] := by
    rw [himg]; rfl
  have himg_gotBytes_len : img.gotBytes.length = 8 := by
    unfold Obj.Image.gotBytes
    rw [himg_got]
    simp [Obj.bytesLE]
  refine
    { base_aligned := hal
      base_wrap := by rw [hgotLen] at hwrap; omega
      got_end_le := hgot_end
      code_eq := himg_code
      code_len_le := by rw [himg_code]; exact hcode_le
      dataAddr_eq := himg_dataAddr
      data_len_le := by rw [himg_data]; omega
      logAddr_eq := rfl
      log_end_le := hlog_end
      gotAddr_eq := himg_gotAddr
      gotBytes_len := himg_gotBytes_len }

/-! ## Arena Base and Initial Memory -/

def arenaBase (img : Obj.Image) : BitVec 64 :=
  if img.base.toNat < 2 ^ 62 then 0x8000000000000000#64 else 0x10000000#64

theorem arenaBase_aligned (img : Obj.Image) : (arenaBase img).toNat % 4096 = 0 := by
  unfold arenaBase
  split <;> decide

theorem arenaBase_wrap (img : Obj.Image) : (arenaBase img).toNat + 2097152 ≤ 2 ^ 64 := by
  unfold arenaBase
  split <;> decide

theorem arenaBase_disjoint_image {img : Obj.Image} (hf : ImageFacts img)
    {a : BitVec 64} (ha : (a - arenaBase img).toNat < 2097152) :
    0x8000000 ≤ (a - img.base).toNat := by
  have hwrap := hf.base_wrap
  have hgot_end := hf.got_end_le
  have ha_lt : a.toNat < 2 ^ 64 := a.isLt
  have hb_lt : img.base.toNat < 2 ^ 64 := img.base.isLt
  unfold arenaBase at ha
  split at ha
  · rename_i hlt
    have hB : (0x8000000000000000#64 : BitVec 64).toNat = 2 ^ 63 := by decide
    rw [BitVec.toNat_sub, hB] at ha
    rw [BitVec.toNat_sub]
    omega
  · rename_i hge
    have hB : (0x10000000#64 : BitVec 64).toNat = 0x10000000 := by decide
    rw [BitVec.toNat_sub, hB] at ha
    rw [BitVec.toNat_sub]
    omega

noncomputable def baseMemByte (img : Obj.Image) (a : BitVec 64) : BitVec 8 :=
  if (a - img.base).toNat < img.code.length then
    img.code.getD (a - img.base).toNat 0#8
  else if dataOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat - dataOff < img.data.length then
    img.data.getD ((a - img.base).toNat - dataOff) 0#8
  else if gotOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat - gotOff < img.gotBytes.length then
    img.gotBytes.getD ((a - img.base).toNat - gotOff) 0#8
  else
    0#8

noncomputable def baseMemPerm (img : Obj.Image) (B : BitVec 64) (a : BitVec 64) : Option Perm :=
  if (a - img.base).toNat < img.code.length then
    some Perm.rx
  else if dataOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat - dataOff < img.data.length then
    img.dataPerm a
  else if gotOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat - gotOff < img.gotBytes.length then
    some Perm.ro
  else if logOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat < logOff + 8 then
    some Perm.rw
  else if (a - B).toNat < 16384 then
    some Perm.rw
  else
    none

noncomputable def baseMem (img : Obj.Image) (B : BitVec 64) : Memory :=
  Memory.ofFn (baseMemByte img) (baseMemPerm img B)

theorem getD_eq_getElem {α : Type} (xs : List α) (d : α) {i : Nat} (hi : i < xs.length) :
    xs.getD i d = xs[i] := by
  simp [List.getD, hi]

theorem sub_base_add_ofNat (base : BitVec 64) {off : Nat} (hoff : off < 2 ^ 64) :
    (base + BitVec.ofNat 64 off - base).toNat = off := by
  have heq : base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off := by
    bv_omega
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]

theorem sub_base_of_sub_add (base c a : BitVec 64)
    (h : (a - (base + c)).toNat + c.toNat < 2 ^ 64) :
    (a - base).toNat = c.toNat + (a - (base + c)).toNat := by
  have heq : a - base = a - (base + c) + c := by bv_omega
  rw [heq, BitVec.toNat_add, Nat.mod_eq_of_lt h, Nat.add_comm]

theorem baseMem_frozenLoaded {img : Obj.Image} (hf : ImageFacts img) (B : BitVec 64) :
    img.FrozenLoaded { mem := baseMem img B, symtab := img.symtab } := by
  have hcode_le := hf.code_len_le
  have hdata_le := hf.data_len_le
  have hlog_le := hf.log_end_le
  have hgot_end := hf.got_end_le
  have hgot_len := hf.gotBytes_len
  have hwrap := hf.base_wrap
  refine Obj.Image.frozenLoaded_iff.2 ⟨?_, ?_, ?_⟩
  · refine Program.CodeLoaded.intro ?_ ?_ fun i hi => ?_
    · change img.base.toNat % 4 = 0
      have hal := hf.base_aligned
      omega
    · change img.base.toNat + img.code.length ≤ 2 ^ 64
      omega
    · change (baseMem img B).read8 (img.base + BitVec.ofNat 64 i) = img.code[i] ∧
        (baseMem img B).perm (img.base + BitVec.ofNat 64 i) = some Perm.rx ∧
        (baseMem img B).isLazyFree (img.base + BitVec.ofNat 64 i) = false
      have hi_lt : i < img.code.length := hi
      have hoff : (img.base + BitVec.ofNat 64 i - img.base).toNat = i :=
        sub_base_add_ofNat img.base (by omega)
      simp only [baseMem, Memory.read8_ofFn, Memory.perm_ofFn, Memory.isLazyFree_ofFn,
        baseMemByte, baseMemPerm, hoff, hi_lt, ↓reduceIte, getD_eq_getElem _ _ hi_lt]
      exact ⟨rfl, rfl, rfl⟩
  · intro i hi a hro
    have haddr : a = img.base + BitVec.ofNat 64 (dataOff + i) := by
      change img.dataAddr + BitVec.ofNat 64 i = _
      rw [hf.dataAddr_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
    have hoff : (a - img.base).toNat = dataOff + i := by
      rw [haddr]
      exact sub_base_add_ofNat img.base (by omega)
    have hnot1 : ¬ (dataOff + i < img.code.length) := by omega
    have h2 : dataOff ≤ dataOff + i := Nat.le_add_right dataOff i
    have hsub : dataOff + i - dataOff = i := Nat.add_sub_cancel_left dataOff i
    simp only [baseMem, Memory.read8_ofFn, Memory.perm_ofFn, Memory.isLazyFree_ofFn,
      baseMemByte, baseMemPerm, hoff, hnot1, h2, hsub, hi, true_and, ↓reduceIte,
      getD_eq_getElem _ _ hi]
    unfold Obj.Image.dataPerm
    simp only [hro, ↓reduceIte]
    exact ⟨rfl, rfl⟩
  · intro i hi
    have haddr : img.gotAddr + BitVec.ofNat 64 i = img.base + BitVec.ofNat 64 (gotOff + i) := by
      rw [hf.gotAddr_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
    have hoff : (img.gotAddr + BitVec.ofNat 64 i - img.base).toNat = gotOff + i := by
      rw [haddr]
      exact sub_base_add_ofNat img.base (by omega)
    have hnot1 : ¬ (gotOff + i < img.code.length) := by omega
    have hnot2 : ¬ (dataOff ≤ gotOff + i ∧ gotOff + i - dataOff < img.data.length) := by omega
    have h3 : gotOff ≤ gotOff + i := Nat.le_add_right gotOff i
    have hsub : gotOff + i - gotOff = i := Nat.add_sub_cancel_left gotOff i
    simp only [baseMem, Memory.read8_ofFn, Memory.perm_ofFn, Memory.isLazyFree_ofFn,
      baseMemByte, baseMemPerm, hoff, hnot1, hnot2, h3, hsub, hi, true_and, ↓reduceIte,
      getD_eq_getElem _ _ hi]
    exact ⟨rfl, rfl⟩

theorem baseMem_unmapped_arena {img : Obj.Image} (hf : ImageFacts img) :
    Unmapped (baseMem img (arenaBase img)) (arenaBase img + 1048576#64) (2 ^ 20) := by
  intro a ha
  unfold InRegion at ha
  have h1 : (1048576#64 : BitVec 64).toNat = 1048576 := by decide
  have h20 : (2 ^ 20 : Nat) = 1048576 := by decide
  have ha_sub_B : (a - arenaBase img).toNat =
      1048576 + (a - (arenaBase img + 1048576#64)).toNat := by
    rw [← h1]
    exact sub_base_of_sub_add (arenaBase img) 1048576#64 a (by omega)
  have ha_in_arena : (a - arenaBase img).toNat < 2097152 := by omega
  have hoff_ge : 0x8000000 ≤ (a - img.base).toNat := arenaBase_disjoint_image hf ha_in_arena
  have hcode_le := hf.code_len_le
  have hdata_le := hf.data_len_le
  have hlog_le := hf.log_end_le
  have hgot_end := hf.got_end_le
  have hgot_len := hf.gotBytes_len
  have hnot1 : ¬ ((a - img.base).toNat < img.code.length) := by omega
  have hnot2 : ¬ (dataOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat - dataOff < img.data.length) := by omega
  have hnot3 : ¬ (gotOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat - gotOff < img.gotBytes.length) := by omega
  have hnot4 : ¬ (logOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat < logOff + 8) := by omega
  have hnot5 : ¬ ((a - arenaBase img).toNat < 16384) := by omega
  simp only [baseMem, Memory.perm_ofFn, baseMemPerm, hnot1, hnot2, hnot3, hnot4, hnot5, ↓reduceIte]
  rfl

theorem satisfies_two_disjoint_memRegions {m : Memory} {b1 : BitVec 64} {n1 : Nat}
    {b2 : BitVec 64} {n2 : Nat}
    (h1 : m.RW b1 n1) (h2 : m.RW b2 n2)
    (hdisj : ∀ a, InRegion b1 n1 a → InRegion b2 n2 a → False) :
    m ⊨ memRegion b1 n1 ∗ memRegion b2 n2 := by
  by_cases hn10 : n1 = 0
  · subst hn10; rw [memRegion_zero, emp_sepConj]; exact ProofLib.satisfies_memRegion m b2 n2 h2
  by_cases hn20 : n2 = 0
  · subst hn20; rw [memRegion_zero, sepConj_emp]; exact ProofLib.satisfies_memRegion m b1 n1 h1
  have hn1 : n1 ≤ 2 ^ 64 := by
    by_contra hgt
    exact hdisj b2 (by unfold InRegion; have := (b2 - b1).isLt; omega)
      (by unfold InRegion; rw [BitVec.sub_self, BitVec.toNat_zero]; omega)
  have hn2 : n2 ≤ 2 ^ 64 := by
    by_contra hgt
    exact hdisj b1 (by unfold InRegion; rw [BitVec.sub_self, BitVec.toNat_zero]; omega)
      (by unfold InRegion; have := (b1 - b2).isLt; omega)
  have hm1 := ProofLib.satisfies_memRegion m b1 n1 h1
  rw [ProofLib.memRegion_eq_exists_bytes b1 n1 hn1, satisfies_sepExists] at hm1
  obtain ⟨bs1, hm1⟩ := hm1
  rw [satisfies_pure_sepConj] at hm1
  obtain ⟨hbs1, hm1⟩ := hm1
  have hm2 := ProofLib.satisfies_memRegion m b2 n2 h2
  rw [ProofLib.memRegion_eq_exists_bytes b2 n2 hn2, satisfies_sepExists] at hm2
  obtain ⟨bs2, hm2⟩ := hm2
  rw [satisfies_pure_sepConj] at hm2
  obtain ⟨hbs2, hm2⟩ := hm2
  have hs1 : ProofLib.SupportedOn 0#64 (fun k => InRegion b1 n1 (BitVec.ofNat 64 k)) m (memRegion b1 n1) := by
    refine ProofLib.SupportedOn.mono (hbs1 ▸ ProofLib.pointsToBytes_entails_memRegion b1 bs1) ?_
    refine ProofLib.SupportedOn.of_pointsToBytes hm1 fun a ha => ?_
    rw [BitVec.sub_zero, BitVec.ofNat_toNat]
    exact hbs1 ▸ ha
  have hs2 : ProofLib.SupportedOn 0#64 (fun k => InRegion b2 n2 (BitVec.ofNat 64 k)) m (memRegion b2 n2) := by
    refine ProofLib.SupportedOn.mono (hbs2 ▸ ProofLib.pointsToBytes_entails_memRegion b2 bs2) ?_
    refine ProofLib.SupportedOn.of_pointsToBytes hm2 fun a ha => ?_
    rw [BitVec.sub_zero, BitVec.ofNat_toNat]
    exact hbs2 ▸ ha
  exact (ProofLib.SupportedOn.sepConj hs1 hs2 fun k hk1 hk2 => hdisj (BitVec.ofNat 64 k) hk1 hk2).satisfies

theorem baseMem_satisfies_initial_regions {img : Obj.Image} (hf : ImageFacts img) :
    baseMem img (arenaBase img) ⊨
      memRegion (logFilterAddr img) 8 ∗ memRegion (arenaBase img) 16384 := by
  have hcode_le := hf.code_len_le
  have hdata_le := hf.data_len_le
  have hlog_le := hf.log_end_le
  have hgot_end := hf.got_end_le
  have hgot_len := hf.gotBytes_len
  refine satisfies_two_disjoint_memRegions ?_ ?_ ?_
  · intro a ha
    unfold InRegion at ha
    rw [hf.logAddr_eq] at ha
    have h1 : (BitVec.ofNat 64 logOff).toNat = logOff := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hoff : (a - img.base).toNat = logOff + (a - (img.base + BitVec.ofNat 64 logOff)).toNat := by
      rw [← h1]
      exact sub_base_of_sub_add img.base (BitVec.ofNat 64 logOff) a (by omega)
    have hnot1 : ¬ ((a - img.base).toNat < img.code.length) := by omega
    have hnot2 : ¬ (dataOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat - dataOff < img.data.length) := by omega
    have hnot3 : ¬ (gotOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat - gotOff < img.gotBytes.length) := by omega
    have h4 : logOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat < logOff + 8 := ⟨by omega, by omega⟩
    rw [Memory.permNoLazy_eq_some_rw_iff]
    simp only [baseMem, Memory.perm_ofFn, Memory.isLazyFree_ofFn, baseMemPerm, hnot1, hnot2, hnot3, h4, and_self, ↓reduceIte]
    exact ⟨rfl, rfl⟩
  · intro a ha
    unfold InRegion at ha
    have ha_in_arena : (a - arenaBase img).toNat < 2097152 := by omega
    have hoff_ge : 0x8000000 ≤ (a - img.base).toNat := arenaBase_disjoint_image hf ha_in_arena
    have hnot1 : ¬ ((a - img.base).toNat < img.code.length) := by omega
    have hnot2 : ¬ (dataOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat - dataOff < img.data.length) := by omega
    have hnot3 : ¬ (gotOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat - gotOff < img.gotBytes.length) := by omega
    have hnot4 : ¬ (logOff ≤ (a - img.base).toNat ∧ (a - img.base).toNat < logOff + 8) := by omega
    rw [Memory.permNoLazy_eq_some_rw_iff]
    simp only [baseMem, Memory.perm_ofFn, Memory.isLazyFree_ofFn, baseMemPerm, hnot1, hnot2, hnot3, hnot4, ha, ↓reduceIte]
    exact ⟨rfl, rfl⟩
  · intro a ha1 ha2
    unfold InRegion at ha1 ha2
    rw [hf.logAddr_eq] at ha1
    have h1 : (BitVec.ofNat 64 logOff).toNat = logOff := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hoff : (a - img.base).toNat = logOff + (a - (img.base + BitVec.ofNat 64 logOff)).toNat := by
      rw [← h1]
      exact sub_base_of_sub_add img.base (BitVec.ofNat 64 logOff) a (by omega)
    have ha_in_arena : (a - arenaBase img).toNat < 2097152 := by omega
    have hoff_ge : 0x8000000 ≤ (a - img.base).toNat := arenaBase_disjoint_image hf ha_in_arena
    omega

/-! ## Populated Arena Witness for `consumeMessageKeySpec` -/

theorem arenaBase_add_176_ne_zero (img : Obj.Image) : arenaBase img + 176#64 ≠ 0 := by
  unfold arenaBase; split <;> decide

theorem arenaBase_add_280_ne_zero (img : Obj.Image) : arenaBase img + 280#64 ≠ 0 := by
  unfold arenaBase; split <;> decide

theorem arenaBase_add_100000_ne_zero (img : Obj.Image) : arenaBase img + 1048576#64 ≠ 0 := by
  unfold arenaBase; split <;> decide

theorem arenaBase_add_100000_mod_8 (img : Obj.Image) : (arenaBase img + 1048576#64).toNat % 8 = 0 := by
  unfold arenaBase; split <;> decide

theorem arenaBase_add_16384_aligned (img : Obj.Image) :
    ((arenaBase img + 16384#64) &&& 15#64 == 0#64) = true := by
  unfold arenaBase; split <;> decide

theorem pk0_serialize_length : pk0.serialize.length = 33 := by decide

theorem srk_vecGhostAt_eq (B : BitVec 64) (hne : B + 280#64 ≠ 0) :
    vecGhostAt A₀ (g0 B).srk (B + 176#64) =
      ((B + 176#64) ↦₆₄ 33#64) ∗ ((B + 184#64) ↦₆₄ (B + 280#64)) ∗
        ((B + 192#64) ↦₆₄ 33#64) ∗ ((B + 280#64) ↦ₛ pk0.serialize) := by
  unfold vecGhostAt vecU8At vecHeader g0 A₀
  simp only [pk0_serialize_length, BitVec.ofNat_eq_ofNat, true_and,
    show (33#64 : BitVec 64).toNat < 2 ^ 63 by decide,
    show (33#64 : BitVec 64).toNat - 33 = 0 by decide,
    memRegion_zero, emp_sepConj, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (33 ≤ (33#64 : BitVec 64).toNat ∧ B + 280#64 ≠ 0#64) ↔ True :=
    iff_true_intro ⟨by decide, hne⟩
  have hif : ¬ ((33#64 : BitVec 64) = 0#64) := by decide
  rw [propext hpure, pure_true, emp_sepConj]
  simp only [hif, ↓reduceIte]
  ac_rfl

theorem priv_vecGhostAt_eq (B : BitVec 64) :
    vecGhostAt A₀ (g0 B).priv (B + 176#64 + 24#64) =
      ((B + 200#64) ↦₆₄ 0#64) ∗ ((B + 208#64) ↦₆₄ 1#64) ∗ ((B + 216#64) ↦₆₄ 0#64) := by
  unfold vecGhostAt vecU8At vecHeader g0
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, true_and,
    show (0#64 : BitVec 64).toNat < 2 ^ 63 by decide,
    ↓reduceIte, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (1#64 : BitVec 64) ≠ 0#64) ↔ True := by decide
  rw [propext hpure, pure_true, sepConj_emp]

theorem mk_vecAt_eq (B : BitVec 64) :
    vecAt A₀ 104 8 (messageKeyAt A₀) (B + 176#64 + 48#64) (g0 B).mkCap (g0 B).mkPtr
      ((g0 B).keys.zip c0.messageKeys) =
      ((B + 224#64) ↦₆₄ 0#64) ∗ ((B + 232#64) ↦₆₄ 8#64) ∗ ((B + 240#64) ↦₆₄ 0#64) := by
  unfold vecAt vecHeader vecBuf g0 c0
  simp only [List.zip_nil_right, List.length_nil, BitVec.ofNat_eq_ofNat,
    true_and, show (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 by decide,
    ↓reduceIte, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (8#64 : BitVec 64) ≠ 0#64) ↔ True := by decide
  rw [propext hpure, pure_true, sepConj_emp]

theorem ck_optChainKeyAt_eq (B : BitVec 64) :
    optChainKeyAt A₀ (g0 B).ck c0.chainKey (B + 176#64 + 72#64) =
      ((B + 248#64) ↦₆₄ optChainKeyNone) ∗ memRegion (B + 256#64) 24 := by
  unfold optChainKeyAt g0 c0
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem chainAt_g0_c0_eq (B : BitVec 64) (hne280 : B + 280#64 ≠ 0) :
    chainAt A₀ (g0 B, c0) (B + 176#64) =
      ((B + 176#64) ↦₆₄ 33#64) ∗ ((B + 184#64) ↦₆₄ (B + 280#64)) ∗
        ((B + 192#64) ↦₆₄ 33#64) ∗ ((B + 280#64) ↦ₛ pk0.serialize) ∗
        ((B + 200#64) ↦₆₄ 0#64) ∗ ((B + 208#64) ↦₆₄ 1#64) ∗ ((B + 216#64) ↦₆₄ 0#64) ∗
        ((B + 224#64) ↦₆₄ 0#64) ∗ ((B + 232#64) ↦₆₄ 8#64) ∗ ((B + 240#64) ↦₆₄ 0#64) ∗
        ((B + 248#64) ↦₆₄ optChainKeyNone) ∗ memRegion (B + 256#64) 24 := by
  unfold chainAt
  rw [srk_vecGhostAt_eq B hne280, priv_vecGhostAt_eq B, mk_vecAt_eq B, ck_optChainKeyAt_eq B]
  have hpure : (PublicKey.deserialize (g0 B).srk.bytes = .ok c0.senderRatchetKey ∧
      c0.messageKeys.length ≤ maxMessageKeys ∧ (g0 B).keys.length = c0.messageKeys.length ∧
      (g0 B).srk.bytes.length = 33 ∧ (g0 B).priv.bytes = []) ↔ True := by
    simp [g0, c0, deserialize_pk0_serialize, maxMessageKeys]
    decide
  rw [propext hpure, pure_true, emp_sepConj]
  ac_rfl

theorem chains_vecAt_eq (B : BitVec 64) (hne176 : B + 176#64 ≠ 0) :
    vecAt A₀ 104 8 (chainAt A₀) B (G0 B).chainsCap (G0 B).chainsPtr
      ((G0 B).chains.zip st0.receiverChains) =
      (B ↦₆₄ 1#64) ∗ ((B + 8#64) ↦₆₄ (B + 176#64)) ∗ ((B + 16#64) ↦₆₄ 1#64) ∗
        chainAt A₀ (g0 B, c0) (B + 176#64) := by
  unfold vecAt vecHeader vecBuf G0 st0 A₀ arrayAt
  simp only [List.zip_cons_cons, List.zip_nil_right, List.length_singleton,
    BitVec.ofNat_eq_ofNat, true_and,
    show (1#64 : BitVec 64).toNat * 104 < 2 ^ 63 by decide,
    show ((1#64 : BitVec 64).toNat - 1) * 104 = 0 by decide,
    memRegion_zero, emp_sepConj, sepConj_emp]
  have hpure : (1 ≤ (1#64 : BitVec 64).toNat ∧ B + 176#64 ≠ 0#64) ↔ True :=
    iff_true_intro ⟨by decide, hne176⟩
  have hif : ¬ ((1#64 : BitVec 64) = 0#64) := by decide
  rw [propext hpure, pure_true, emp_sepConj]
  simp only [hif, ↓reduceIte]
  unfold arrayAt
  rw [sepConj_emp]
  ac_rfl

theorem ratchetAt_G0_st0_eq (B : BitVec 64) (hne176 : B + 176#64 ≠ 0) (hne280 : B + 280#64 ≠ 0) :
    ratchetAt A₀ B (G0 B) st0 =
      (B ↦₆₄ 1#64) ∗ ((B + 8#64) ↦₆₄ (B + 176#64)) ∗ ((B + 16#64) ↦₆₄ 1#64) ∗
        ((B + 176#64) ↦₆₄ 33#64) ∗ ((B + 184#64) ↦₆₄ (B + 280#64)) ∗
        ((B + 192#64) ↦₆₄ 33#64) ∗ ((B + 280#64) ↦ₛ pk0.serialize) ∗
        ((B + 200#64) ↦₆₄ 0#64) ∗ ((B + 208#64) ↦₆₄ 1#64) ∗ ((B + 216#64) ↦₆₄ 0#64) ∗
        ((B + 224#64) ↦₆₄ 0#64) ∗ ((B + 232#64) ↦₆₄ 8#64) ∗ ((B + 240#64) ↦₆₄ 0#64) ∗
        ((B + 248#64) ↦₆₄ optChainKeyNone) ∗ memRegion (B + 256#64) 24 ∗
        ((B + 24#64) ↦ₛ optSenderChainBytes none (List.replicate 100 0#8)) ∗
        ((B + 128#64) ↦ₛ keyToBytes32 0#256) ∗
        ((B + 160#64) ↦₆₄ BitVec.ofNat 64 25000) ∗
        ((B + 168#64) ↦₃₂ 0#32) ∗ memRegion (B + 172#64) 4 := by
  unfold ratchetAt
  rw [chains_vecAt_eq B hne176, chainAt_g0_c0_eq B hne280]
  have hpure : ((G0 B).chains.length = st0.receiverChains.length ∧
      (G0 B).senderPad.length = 100 ∧ st0.maxForwardJumps < 2 ^ 64) ↔ True := by
    simp [G0, st0]
  rw [propext hpure, pure_true, emp_sepConj]
  dsimp only [G0, st0]
  ac_rfl

def ValidMem (img : Obj.Image) (B : BitVec 64) (P : SepProp) : Prop :=
  ∃ m : Memory, m ⊨ P ∧ m.perm = (baseMem img B).perm ∧ (baseMem img B).KeepsFrozen m

theorem split_arena_region (B : BitVec 64) {off k off' rem' rem : Nat}
    (h : decide (off + k = off' ∧ k + rem' = rem ∧ rem ≤ 2 ^ 64) = true) :
    memRegion (B + BitVec.ofNat 64 off) rem =
      memRegion (B + BitVec.ofNat 64 off) k ∗ memRegion (B + BitVec.ofNat 64 off') rem' := by
  obtain ⟨hoff, hrem, hle⟩ := of_decide_eq_true h
  subst hoff; subst hrem
  rw [memRegion_split (B + BitVec.ofNat 64 off) k rem' hle,
    BitVec.add_assoc, ← BitVec.ofNat_add]

def bytesOf64 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]

def bytesOf32 (v : BitVec 32) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8]

theorem pointsTo64_eq_pointsToBytes (a v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦ₛ bytesOf64 v) := by
  unfold pointsTo64 bytesOf64
  simp only [pointsToBytes_cons, pointsToBytes_nil,
    BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]

theorem ValidMem.init {img : Obj.Image} (hf : ImageFacts img) :
    ValidMem img (arenaBase img)
      (memRegion (arenaBase img + BitVec.ofNat 64 0) 16384 ∗ (logFilterAddr img ↦₆₄ 0#64)) := by
  have h0 := baseMem_satisfies_initial_regions hf
  have hlen : (bytesOf64 0#64).length = 8 := rfl
  have hle : (bytesOf64 0#64).length ≤ 2 ^ 64 := by decide
  have h0' : baseMem img (arenaBase img) ⊨
      memRegion (logFilterAddr img) (bytesOf64 0#64).length ∗ memRegion (arenaBase img) 16384 := by
    rwa [hlen]
  refine ⟨(baseMem img (arenaBase img)).writeBytes (logFilterAddr img) (bytesOf64 0#64), ?_,
    Memory.perm_writeBytes _ _ _,
    keepsFrozen_writeBytes_of_memRegion (bytesOf64 0#64) hle h0'⟩
  have hw := satisfies_writeBytes (bytesOf64 0#64) hle h0'
  rw [← pointsTo64_eq_pointsToBytes, sepConj_comm] at hw
  have hz : arenaBase img + BitVec.ofNat 64 0 = arenaBase img := BitVec.add_zero _
  rwa [hz]

theorem ValidMem.stepBytes {img : Obj.Image} {B : BitVec 64} {off off' rem' rem : Nat} {R : SepProp}
    (k : Nat) (bs : List (BitVec 8)) (hlen : bs.length = k)
    (h : ValidMem img B (memRegion (B + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + k = off' ∧ k + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    ValidMem img B (memRegion (B + BitVec.ofNat 64 off') rem' ∗
      (((B + BitVec.ofNat 64 off) ↦ₛ bs) ∗ R)) := by
  rcases h with ⟨m, hsat, hperm, hfr⟩
  have ⟨_, hrem, hle⟩ := of_decide_eq_true hc
  have hbs_le : bs.length ≤ 2 ^ 64 := by omega
  rw [split_arena_region B hc, sepConj_assoc, ← hlen] at hsat
  refine ⟨m.writeBytes (B + BitVec.ofNat 64 off) bs, ?_,
    (Memory.perm_writeBytes _ _ _).trans hperm,
    hfr.trans (keepsFrozen_writeBytes_of_memRegion bs hbs_le hsat)⟩
  have hw := satisfies_writeBytes bs hbs_le hsat
  rwa [sepConj_left_comm] at hw

theorem ValidMem.step64 {img : Obj.Image} {B : BitVec 64} {off off' rem' rem : Nat} {R : SepProp}
    (v : BitVec 64)
    (h : ValidMem img B (memRegion (B + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + 8 = off' ∧ 8 + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    ValidMem img B (memRegion (B + BitVec.ofNat 64 off') rem' ∗
      (((B + BitVec.ofNat 64 off) ↦₆₄ v) ∗ R)) := by
  rw [pointsTo64_eq_pointsToBytes]
  exact h.stepBytes 8 (bytesOf64 v) rfl hc

theorem ValidMem.step32 {img : Obj.Image} {B : BitVec 64} {off off' rem' rem : Nat} {R : SepProp}
    (v : BitVec 32)
    (h : ValidMem img B (memRegion (B + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + 4 = off' ∧ 4 + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    ValidMem img B (memRegion (B + BitVec.ofNat 64 off') rem' ∗
      (((B + BitVec.ofNat 64 off) ↦₃₂ v) ∗ R)) := by
  rw [pointsTo32_eq_pointsToBytes]
  exact h.stepBytes 4 (bytesOf32 v) rfl hc

theorem ValidMem.stepSkip {img : Obj.Image} {B : BitVec 64} {off off' rem' rem : Nat} {R : SepProp}
    (k : Nat)
    (h : ValidMem img B (memRegion (B + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + k = off' ∧ k + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    ValidMem img B (memRegion (B + BitVec.ofNat 64 off') rem' ∗
      (memRegion (B + BitVec.ofNat 64 off) k ∗ R)) := by
  rcases h with ⟨m, hsat, hperm, hfr⟩
  rw [split_arena_region B hc, sepConj_assoc, sepConj_left_comm] at hsat
  exact ⟨m, hsat, hperm, hfr⟩

theorem ValidMem.stepDrop {img : Obj.Image} {B : BitVec 64} {off off' rem' rem : Nat} {R : SepProp}
    (k : Nat)
    (h : ValidMem img B (memRegion (B + BitVec.ofNat 64 off) rem ∗ R))
    (hc : decide (off + k = off' ∧ k + rem' = rem ∧ rem ≤ 2 ^ 64) = true := by decide) :
    ValidMem img B (memRegion (B + BitVec.ofNat 64 off') rem' ∗ R) := by
  rcases h with ⟨m, hsat, hperm, hfr⟩
  rw [split_arena_region B hc, sepConj_assoc] at hsat
  exact ⟨m, Satisfies.of_sep_right hsat, hperm, hfr⟩

theorem validMem_populated {img : Obj.Image} (hf : ImageFacts img) :
    let B := arenaBase img
    ValidMem img B
      (ratchetAt A₀ B (G0 B) st0 ∗
        ((B + 313#64) ↦ₛ pk0.bytes.toList) ∗ ((B + 345#64) ↦ₛ chainKeyBytes ck0) ∗
        memRegion (B + 381#64) 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
        stackAt (B + 16384#64) cmkStack ∗ A₀.pool) := by
  intro B
  have h0 : ValidMem img B (memRegion (B + BitVec.ofNat 64 0) 16384 ∗ (logFilterAddr img ↦₆₄ 0#64)) :=
    ValidMem.init hf
  have h1 := h0.step64 (off' := 8) (rem' := 16376) 1#64
  have h2 := h1.step64 (off' := 16) (rem' := 16368) (B + 176#64)
  have h3 := h2.step64 (off' := 24) (rem' := 16360) 1#64
  have h4 := h3.stepBytes (off' := 128) (rem' := 16256) 104
    (optSenderChainBytes none (List.replicate 100 0#8)) (by simp [optSenderChainBytes, leBytes])
  have h5 := h4.stepBytes (off' := 160) (rem' := 16224) 32
    (keyToBytes32 0#256) (by simp [keyToBytes32])
  have h6 := h5.step64 (off' := 168) (rem' := 16216) (BitVec.ofNat 64 25000)
  have h7 := h6.step32 (off' := 172) (rem' := 16212) 0#32
  have h8 := h7.stepSkip (off' := 176) (rem' := 16208) 4
  have h9 := h8.step64 (off' := 184) (rem' := 16200) 33#64
  have h10 := h9.step64 (off' := 192) (rem' := 16192) (B + 280#64)
  have h11 := h10.step64 (off' := 200) (rem' := 16184) 33#64
  have h12 := h11.step64 (off' := 208) (rem' := 16176) 0#64
  have h13 := h12.step64 (off' := 216) (rem' := 16168) 1#64
  have h14 := h13.step64 (off' := 224) (rem' := 16160) 0#64
  have h15 := h14.step64 (off' := 232) (rem' := 16152) 0#64
  have h16 := h15.step64 (off' := 240) (rem' := 16144) 8#64
  have h17 := h16.step64 (off' := 248) (rem' := 16136) 0#64
  have h18 := h17.step64 (off' := 256) (rem' := 16128) optChainKeyNone
  have h19 := h18.stepSkip (off' := 280) (rem' := 16104) 24
  have h20 := h19.stepBytes (off' := 313) (rem' := 16071) 33
    pk0.serialize pk0_serialize_length
  have h21 := h20.stepBytes (off' := 345) (rem' := 16039) 32
    pk0.bytes.toList (by simp [pk0])
  have h22 := h21.stepBytes (off' := 381) (rem' := 16003) 36
    (chainKeyBytes ck0) (by simp [chainKeyBytes, keyToBytes32, leBytes])
  have h23 := h22.stepSkip (off' := 469) (rem' := 15915) 88
  have h24 := h23.stepDrop (off' := 8192) (rem' := 8192) 7723
  rcases h24 with ⟨m, hsat, hperm, hfr⟩
  refine ⟨m, ?_, hperm, hfr⟩
  have hsp_eq : B + 16384#64 - BitVec.ofNat 64 cmkStack = B + BitVec.ofNat 64 8192 := by
    change B + 16384#64 - 8192#64 = B + 8192#64
    bv_omega
  rw [ratchetAt_G0_st0_eq B (arenaBase_add_176_ne_zero img) (arenaBase_add_280_ne_zero img)]
  unfold stackAt cmkStack A₀
  rw [hsp_eq]
  simp only [BitVec.add_zero] at hsat ⊢
  refine Eq.mp (congrArg (fun P => m ⊨ P) ?_) hsat
  ac_rfl

theorem cmkNonVacStmt_proof (F : ShaState → List (BitVec 8) → ShaState) (img : Obj.Image) :
    ConsumeMessageKeySpecSatisfiable F img := by
  intro hloads
  have hf := imageFacts_of_loads hloads
  let B := arenaBase img
  obtain ⟨m, hsat, hperm, hfr⟩ := validMem_populated hf
  refine ⟨A₀, witnessHooks, witnessHooks_allocHooks, witnessHooks_succeedsWithRoom,
    witnessGhost B, ?_⟩
  let s0 : State :=
    { regs := ⟨fun i =>
        if i = 0#5 then B
        else if i = 1#5 then B + 313#64
        else if i = 2#5 then B + 345#64
        else if i = 3#5 then 5#64
        else if i = 4#5 then 2#64
        else if i = 8#5 then B + 381#64
        else 0#64⟩
      sp := B + 16384#64
      mem := m
      status := .Running
      symtab := img.symtab }
  refine ⟨s0, rfl, arenaBase_add_16384_aligned img, ?_, ?_,
    witnessGhost_counter_gt B, ⟨0, witnessGhost_findIdx B⟩, witnessGhost_model_ok F B⟩
  · dsimp only [consumeMessageKeySpec, Spec.inImage]
    rw [satisfies_pure_sepConj]
    have hfr_s0 : img.FrozenLoaded s0 := by
      have hbase_fr : img.FrozenLoaded { mem := baseMem img B, symtab := img.symtab } :=
        baseMem_frozenLoaded hf B
      exact hbase_fr.of_keepsFrozen (s := { mem := baseMem img B, symtab := img.symtab }) (s' := s0) hfr
    refine ⟨⟨hfr_s0, rfl⟩, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hsat⟩
  · refine ⟨B + 1048576#64, arenaBase_add_100000_ne_zero img,
      arenaBase_add_100000_mod_8 img, ?_⟩
    intro a ha
    have hunm := baseMem_unmapped_arena hf a ha
    change (m.perm a).mapped = false
    rw [hperm]
    exact hunm

end CryptoVerification.LibsignalSession.NonVacuityWitness
