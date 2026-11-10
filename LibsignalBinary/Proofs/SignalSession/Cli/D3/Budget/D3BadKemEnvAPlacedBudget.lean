/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.Semantics
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V3StepsPlacedBudget
public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.Digits
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.SignalSession.PqDir

/-!
# Untyped/Bad-KEM Rejection Envelopes and Key-File Bounds

Defines the untyped and bad-KEM rejection allocation envelopes for `decrypt_prekey` and proves
`DecPkKeyFilesBounded` unconditionally on `CliPqxdhInputs` and `pqRecvInputs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget

open Arm64 (normalizePath splitSlash)
open Arm64.Process (initFsState)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (x3dhUnsupportedBytes)
open CryptoVerification.E2E (PEParams djbKey keyPairOf kyberKey partyAddressName)
open CryptoVerification.LibsignalProtoCodec (WireType encodeBytesField encodeKey encodeUint32Field)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet.Prost (encodeVarint_length_bounds)
open CryptoVerification.RecordCodecs (
  IdentityKeyPairStructure PreKeyRecordStructure SignedPreKeyRecordStructure encodeProto3BytesField
  encodeProto3Fixed64Field encodeProto3Uint32Field le64Bytes
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (
  CliHooks CliPqxdhInputs Inputs PqParty PqxdhPartyInSpecDomain PublicBundle baseKeysFile coinsFile
  encodeDir identityFile kyberRecordBytes lastResortKyberPreKeyFile oneTimeKyberPreKeyFile
  oneTimePreKeyFile oneTimeRecordBytes partyAddress pqInitInputs pqInputs pqRecvInputs pqSendInputs
  publicBundleOf sessionFile signedPreKeyFile signedRecordBytes
)
open CryptoVerification.SignalSession.Cli (StoresGhost cliInputs decimalText keyName pathOf utf8)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers (decimalText_digit decimalText_ge10)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRd readViewF)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSelfKitPlaced
  cliPollSessKitPlaced cliPollSpkKitPlaced pmKyberId pmPreKeyId
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SignalSession.CliExt (pathStr)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget (
  P2Sub1To3Arm1Env P2Sub1To3Arm2Env P2Sub1To4Arm3Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2V1Arm4Env P2V1Arm5EnvOfAcceptErr
)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter (initFsState_files_mem_norm)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget (
  StageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv cliPollIdBudgetEnv cliPollSessBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliPollKpkFullBudgetEnv cliPollPkFullBudgetEnv cliPollSpkFullBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (publicKeySerializeEvents)

/-! ## 1. Untyped / Bad-KEM Rejection Envelopes -/

def StageP2V3RejectEnv : List AllocEvent → Prop :=
  SeqEnv (fun evs => evs = publicKeySerializeEvents)
    (SeqEnv (fun evs => evs = rustDeallocEvents 33 1)
      (SeqEnv (fun evs => evs = rustAllocEvents x3dhUnsupportedBytes.length 1) FreeOnlyEvs))

def DecPkD3UntypedPollEnv [LibsignalPlacement] {A : RustAlloc} (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2Env : DecPkGhost → Option (SessionRecord (List (BitVec 8))) → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  CliDpPollUntrustedEnv (A := A) B ReadEnv DeserEnv g evs ∨
    ∃ opt : Option (SessionRecord (List (BitVec 8))),
      SeqEnv (StageP1OkEnv (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A g.F g.peer B ReadEnv DeserEnv) StoresGhost.opened.sessions
        (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A g.F g.peer B ReadEnv)
        StoresGhost.opened.identity g.peer.val g.msg.identityKey) (P2Env g opt) evs

def PqxdhAcceptBadKemErrEnv (evs : List AllocEvent) : Prop :=
  evs = [.alloc 28] ∨
  evs = [.alloc 192, .free 1 192] ∨
  evs = [.alloc 192, .alloc 32, .free 1 32, .free 1 192] ∨
  evs = [.alloc 192, .alloc 32, .free 1 32, .alloc 32, .free 1 32, .free 1 192] ∨
  evs = [.alloc 192, .alloc 32, .free 1 32, .alloc 32, .free 1 32, .alloc 32, .free 1 32,
    .free 1 192] ∨
  evs = [.alloc 192, .alloc 32, .free 1 32, .alloc 32, .free 1 32, .alloc 32, .free 1 32,
    .alloc 32, .free 1 32, .free 1 192]

def StageP2BadKemRejectEnv [LibsignalPlacement] {A : RustAlloc}
    (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (AcceptErrEnv : List AllocEvent → Prop)
    (g : DecPkGhost) (_opt : Option (SessionRecord (List (BitVec 8))))
    (evs : List AllocEvent) : Prop :=
  let spkId := g.msg.signedPreKeyId
  let kpkId := pmKyberId g.msg
  let opkWord := pmPreKeyId g.msg
  let kbk := g.msg.baseKey
  let spkBox := (cliPollSpkKitPlaced A g.F spkId (cliKitStk B)).getBoxSize
  let spkPoll := (cliPollSpkFullBudgetEnv A g.F spkId (cliKitStk B) ReadEnv).getPollEnv
    StoresGhost.opened.signed spkId
  let kpkBox := (cliPollKpkKitPlaced A g.F kpkId spkId kbk (cliKitStk B)).getBoxSize
  let kpkPoll := (cliPollKpkFullBudgetEnv A g.F kpkId spkId kbk (cliKitStk B) ReadEnv).getPollEnv
    StoresGhost.opened.kyber kpkId
  let pkBox := (cliPollPkKitPlaced A g.F opkWord (cliKitStk B)).getBoxSize
  let pkPoll := (cliPollPkFullBudgetEnv A g.F opkWord (cliKitStk B) ReadEnv).getPollEnv
    StoresGhost.opened.oneTime
  let kpBox := (cliPollSelfKitPlaced A g.F g.peer (cliKitStk B)).kpBoxSize
  let kpPoll := (cliPollSelfBudgetEnv A g.F g.peer (cliKitStk B) ReadEnv).kpPollEnv
    StoresGhost.opened.identity
  let opkId? := g.msg.preKeyId
  P2Sub1To3Arm1Env spkBox spkPoll evs ∨
  P2Sub1To3Arm2Env spkBox spkPoll kpkBox kpkPoll evs ∨
  P2Sub1To4Arm3Env spkBox spkPoll kpkBox kpkPoll pkBox pkPoll opkId? evs ∨
  P2V1Arm4Env spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId? kpPoll evs ∨
  P2V1Arm5EnvOfAcceptErr spkBox spkPoll kpkBox kpkPoll pkBox pkPoll kpBox opkId? kpPoll
    AcceptErrEnv evs

def StageP2UntypedRejectEnv [LibsignalPlacement] {A : RustAlloc}
    (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (AcceptErrEnv : List AllocEvent → Prop)
    (g : DecPkGhost) (opt : Option (SessionRecord (List (BitVec 8))))
    (evs : List AllocEvent) : Prop :=
  StageP2V3RejectEnv evs ∨ StageP2BadKemRejectEnv (A := A) B ReadEnv AcceptErrEnv g opt evs

def DecPkD3UntypedEnvOf [LibsignalPlacement] {A : RustAlloc}
    (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (AcceptErrEnv : List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  DecPkD3UntypedPollEnv (A := A) B ReadEnv DeserEnv
    (StageP2UntypedRejectEnv (A := A) B ReadEnv AcceptErrEnv) g evs

def DecPkD3UntypedEnv [LibsignalPlacement] (A : RustAlloc)
    (_W : CliHooks) (B : RunBudgets)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  DecPkD3UntypedEnvOf (A := A) B (ReadFileRuleEnv cliIo.rd)
    SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv g evs

abbrev DecPkD3UntypedRejectEnv := @DecPkD3UntypedEnv

/-! ## 2. Key-File Size Bounds (`DecPkKeyFilesBounded`) -/

/-- Byte-length bounds on the five pre-key and own-identity files read during Stage P2 of
`decrypt_prekey` (`identity-key-pair ≤ 256`, `signed-pre-keys ≤ 512`, `one-time-pre-keys ≤ 256`,
and `one-time-kyber-pre-keys` / `last-resort-kyber-pre-keys ≤ 4900`). -/
def DecPkKeyFilesBounded (F : FsFiles) : Prop :=
  (∀ bs, cliIo.rd F (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) =
    .ok bs → bs.length ≤ 256) ∧
  (∀ id bs, cliIo.rd F (pathOf StoresGhost.opened.signed.path (keyName id)) =
    .ok bs → bs.length ≤ 512) ∧
  (∀ id bs, cliIo.rd F (pathOf StoresGhost.opened.oneTime.path (keyName id)) =
    .ok bs → bs.length ≤ 256) ∧
  (∀ id bs, cliIo.rd F (pathOf StoresGhost.opened.kyber.oneTime.path (keyName id)) =
    .ok bs → bs.length ≤ 4900) ∧
  (∀ id bs, cliIo.rd F (pathOf StoresGhost.opened.kyber.lastResort.path (keyName id)) =
    .ok bs → bs.length ≤ 4900)

private theorem cliIo_rd_eq_ok_nil_or_files_some {i : Inputs} {path bs : List (BitVec 8)}
    (hrd : cliIo.rd (runFiles i) path = .ok bs) :
    bs = [] ∨ (initFsState (cliInputs i)).files (pathStr path) = some (.file bs) := by
  change cliRd (initFsState (cliInputs i)).files path = .ok bs at hrd
  unfold cliRd at hrd
  split at hrd
  · cases hrd
  · rename_i rbs hrv
    injection hrd with h
    subst h
    unfold CryptoVerification.SignalSession.Cli.MainHops.readViewF at hrv
    split at hrv
    · cases hrv
    · injection hrv with h; subst h; exact Or.inl rfl
    · split at hrv
      · rename_i fbs hfp
        split at hrv
        · injection hrv with h; subst h; exact Or.inr hfp
        · cases hrv
      · cases hrv
      · injection hrv with h; subst h; exact Or.inl rfl

private theorem splitSlash_go_cons_ne {cur : List Char} {c : Char} (hc : c ≠ '/')
    (cs : List Char) :
    splitSlash.go cur (c :: cs) = splitSlash.go (c :: cur) cs := by
  rw [splitSlash.go.eq_def]
  split
  · simp_all
  · simp_all
  · rename_i _ _ _ _ heq
    injection heq with h1 h2
    subst h1 h2
    rfl

private theorem splitSlash_go_slash (cur : List Char) (cs : List Char) :
    splitSlash.go cur ('/' :: cs) = String.ofList cur.reverse :: splitSlash.go [] cs := by
  rw [splitSlash.go.eq_def]
  simp

private theorem normalizePath_of_cons_slash {pre : List Char} (cs : List Char)
    (hns : ∀ c ∈ pre, c ≠ '/')
    (hne : pre ≠ [])
    (hndot : String.ofList pre ≠ ".") :
    normalizePath (String.ofList (pre ++ '/' :: cs)) =
      String.ofList pre :: normalizePath (String.ofList cs) := by
  have hgo : ∀ (xs acc : List Char), (∀ c ∈ xs, c ≠ '/') →
      splitSlash.go acc (xs ++ '/' :: cs) =
        String.ofList (acc.reverse ++ xs) :: splitSlash.go [] cs := by
    intro xs
    induction xs with
    | nil =>
      intro acc _
      simpa using splitSlash_go_slash acc cs
    | cons c rest ih =>
      intro acc h
      have hc : c ≠ '/' := h c List.mem_cons_self
      simp only [List.cons_append, splitSlash_go_cons_ne hc]
      rw [ih (c :: acc) (fun x hx => h x (List.mem_cons_of_mem c hx))]
      simp [List.reverse_cons, List.append_assoc]
  unfold normalizePath splitSlash
  rw [String.toList_ofList, String.toList_ofList, hgo pre [] hns]
  simp only [List.reverse_nil, List.nil_append]
  have hne_str : (String.ofList pre).isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro he
    exact hne (by simpa [String.toList_ofList] using congrArg String.toList (String.isEmpty_iff.mp he))
  have hndot_b : (String.ofList pre != ".") = true := bne_iff_ne.mpr hndot
  have hpred : (!(String.ofList pre).isEmpty && String.ofList pre != ".") = true := by
    rw [hne_str, hndot_b]; rfl
  rw [List.filter_cons_of_pos (p := fun seg => !seg.isEmpty && seg != ".") hpred]

private theorem normalizePath_string_append_slash {dir s : String}
    (hns : ∀ c ∈ dir.toList, c ≠ '/')
    (hne : dir.toList ≠ [])
    (hndot : dir ≠ ".") :
    normalizePath (dir ++ "/" ++ s) = dir :: normalizePath s := by
  have heq : dir ++ "/" ++ s = String.ofList (dir.toList ++ '/' :: s.toList) := by
    rw [String.append_assoc]
    have h1 : "/" ++ s = String.ofList ('/' :: s.toList) := by
      apply String.ext
      simp [String.toList_append]
    rw [h1]
    apply String.ext
    simp [String.toList_append]
  rw [heq]
  have hof : String.ofList dir.toList = dir := String.ofList_toList
  have hof_s : String.ofList s.toList = s := String.ofList_toList
  have h := normalizePath_of_cons_slash (pre := dir.toList) s.toList hns hne (by rw [hof]; exact hndot)
  simpa [hof, hof_s] using h

def kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni => rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

theorem utf8_eq_kutf8 (s : String) : utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

private theorem pathStr_utf8_of_toList {s : String}
    (h : ((kutf8 s).map fun b => Char.ofNat b.toNat) = s.toList) :
    pathStr (utf8 s) = s := by
  unfold pathStr
  rw [utf8_eq_kutf8]
  apply String.ext
  rw [String.toList_ofList]
  exact h

private theorem str_ne_of_toList {a b : String} (hne : decide (a.toList = b.toList) = false)
    (h : a = b) : False := by
  rw [congrArg String.toList h] at hne
  simp at hne

private theorem list1_str_ne {a b : String} (hne : decide (a.toList = b.toList) = false)
    (h : ([a] : List String) = [b]) : False :=
  str_ne_of_toList hne (List.cons.inj h).1

private theorem opt_str_ne {a b : String} (hne : decide (a.toList = b.toList) = false)
    (h : (some a : Option String) = some b) : False :=
  str_ne_of_toList hne (Option.some.inj h)

private theorem pathStr_append (a b : List (BitVec 8)) :
    pathStr (a ++ b) = pathStr a ++ pathStr b := by
  unfold pathStr
  apply String.ext
  simp [String.toList_append]

private theorem pathStr_pathOf_nonempty {p : List (BitVec 8)} (hp : p ≠ []) (n : List (BitVec 8)) :
    pathStr (pathOf p n) = pathStr p ++ "/" ++ pathStr n := by
  have hpOf : pathOf p n = p ++ utf8 "/" ++ n := by
    cases p with
    | nil => contradiction
    | cons _ _ => rfl
  rw [hpOf, pathStr_append, pathStr_append]
  have hslash : pathStr (utf8 "/") = "/" := pathStr_utf8_of_toList (by decide)
  rw [hslash]

private theorem decimalText_nonempty_and_ascii_digit :
    ∀ (m : Nat), decimalText m ≠ [] ∧ ∀ b ∈ decimalText m, 0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    have hd (r : Nat) (hr : r < 10) :
        0x30 ≤ (BitVec.ofNat 8 (0x30 + r)).toNat ∧ (BitVec.ofNat 8 (0x30 + r)).toNat ≤ 0x39 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    by_cases h10 : m < 10
    · rw [decimalText_digit m h10]
      refine ⟨List.cons_ne_nil _ _, fun b hb => ?_⟩
      rcases List.mem_singleton.mp hb with rfl
      exact hd m h10
    · rw [decimalText_ge10 m (by omega)]
      obtain ⟨_, hall⟩ := ih (m / 10) (by omega)
      refine ⟨by simp, fun b hb => ?_⟩
      rcases List.mem_append.mp hb with h1 | h2
      · exact hall b h1
      · rcases List.mem_singleton.mp h2 with rfl
        exact hd (m % 10) (Nat.mod_lt m (by decide))

private theorem keyName_no_dot_or_slash (id : BitVec 32) :
    ∀ c ∈ (pathStr (keyName id)).toList, c ≠ '.' ∧ c ≠ '/' := by
  intro c hc
  unfold pathStr keyName at hc
  rw [String.toList_ofList, List.mem_map] at hc
  rcases hc with ⟨b, hb, rfl⟩
  have h := (decimalText_nonempty_and_ascii_digit id.toNat).2 b hb
  rcases (by omega :
      b.toNat = 48 ∨ b.toNat = 49 ∨ b.toNat = 50 ∨ b.toNat = 51 ∨ b.toNat = 52 ∨
      b.toNat = 53 ∨ b.toNat = 54 ∨ b.toNat = 55 ∨ b.toNat = 56 ∨ b.toNat = 57) with
    h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 <;> (rw [h0]; decide)

private theorem keyName_nonempty (id : BitVec 32) :
    (pathStr (keyName id)).toList ≠ [] := by
  unfold pathStr keyName
  rw [String.toList_ofList]
  intro hnil
  exact (decimalText_nonempty_and_ascii_digit id.toNat).1 (List.map_eq_nil_iff.mp hnil)

private theorem normalizePath_single_no_slash {s : String}
    (hns : ∀ c ∈ s.toList, c ≠ '/')
    (hne : s.toList ≠ [])
    (hndot : s ≠ ".") :
    normalizePath s = [s] := by
  have hgo : ∀ (xs acc : List Char), (∀ c ∈ xs, c ≠ '/') →
      splitSlash.go acc xs = [String.ofList (acc.reverse ++ xs)] := by
    intro xs
    induction xs with
    | nil =>
      intro acc _
      simp [splitSlash.go]
    | cons c rest ih =>
      intro acc h
      have hc : c ≠ '/' := h c List.mem_cons_self
      rw [splitSlash_go_cons_ne hc, ih (c :: acc) (fun x hx => h x (List.mem_cons_of_mem c hx))]
      simp [List.reverse_cons, List.append_assoc]
  unfold normalizePath splitSlash
  rw [hgo s.toList [] hns]
  simp only [List.reverse_nil, List.nil_append, String.ofList_toList]
  have hne_str : s.isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro he
    exact hne (congrArg String.toList (String.isEmpty_iff.mp he))
  have hndot_b : (s != ".") = true := bne_iff_ne.mpr hndot
  have hpred : (!s.isEmpty && s != ".") = true := by rw [hne_str, hndot_b]; rfl
  rw [List.filter_cons_of_pos (p := fun seg => !seg.isEmpty && seg != ".") hpred, List.filter_nil]

private theorem normalizePath_keyName (id : BitVec 32) :
    normalizePath (pathStr (keyName id)) = [pathStr (keyName id)] := by
  apply normalizePath_single_no_slash
  · exact fun c hc => (keyName_no_dot_or_slash id c hc).2
  · exact keyName_nonempty id
  · intro hdot
    have hmem : '.' ∈ (pathStr (keyName id)).toList := by
      rw [hdot]; decide
    exact (keyName_no_dot_or_slash id '.' hmem).1 rfl

private theorem splitSlash_go_append_nonempty_no_slash {suf : List Char}
    (hsuf_ns : ∀ c ∈ suf, c ≠ '/') :
    ∀ (xs cur : List Char),
      ∃ pre rest, splitSlash.go cur (xs ++ suf) =
        rest ++ [String.ofList (pre ++ suf)] := by
  intro xs
  induction xs with
  | nil =>
    intro cur
    have hgo : ∀ (ys acc : List Char), (∀ c ∈ ys, c ≠ '/') →
        splitSlash.go acc ys = [String.ofList (acc.reverse ++ ys)] := by
      intro ys
      induction ys with
      | nil => intro acc _; simp [splitSlash.go]
      | cons c tl ih =>
        intro acc h
        rw [splitSlash_go_cons_ne (h c List.mem_cons_self),
          ih (c :: acc) (fun x hx => h x (List.mem_cons_of_mem c hx))]
        simp [List.reverse_cons, List.append_assoc]
    exact ⟨cur.reverse, [], by simpa using hgo suf cur hsuf_ns⟩
  | cons c xs ih =>
    intro cur
    by_cases hc : c = '/'
    · subst hc
      simp only [List.cons_append, splitSlash_go_slash]
      obtain ⟨pre, rest, heq⟩ := ih []
      exact ⟨pre, String.ofList cur.reverse :: rest, by rw [heq]; rfl⟩
    · simp only [List.cons_append, splitSlash_go_cons_ne hc]
      exact ih (c :: cur)

private theorem normalizePath_baseKeysFile_ne_keyName (id' id : BitVec 32) :
    normalizePath (baseKeysFile id') ≠
      ["last-resort-kyber-pre-keys", pathStr (keyName id)] := by
  have hbk : baseKeysFile id' =
      "last-resort-kyber-pre-keys" ++ "/" ++ (toString id'.toNat ++ ".base-keys") := rfl
  rw [hbk, normalizePath_string_append_slash (by decide) (by decide) (by decide)]
  intro heq
  injection heq with _ htail
  have hsuf_ns : ∀ c ∈ ".base-keys".toList, c ≠ '/' := by decide
  obtain ⟨pre, rest, hgo⟩ :=
    splitSlash_go_append_nonempty_no_slash hsuf_ns (toString id'.toNat).toList []
  unfold normalizePath splitSlash at htail
  rw [String.toList_append, hgo, List.filter_append] at htail
  let seg := String.ofList (pre ++ ".base-keys".toList)
  have hdot_in : '.' ∈ seg.toList := by
    dsimp only [seg]
    rw [String.toList_ofList]
    exact List.mem_append_right pre (by decide : '.' ∈ ".base-keys".toList)
  have hne_str : seg.isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro he
    have h0 := congrArg String.toList (String.isEmpty_iff.mp he)
    rw [h0] at hdot_in
    exact List.not_mem_nil hdot_in
  have hndot_b : (seg != ".") = true := by
    rw [bne_iff_ne]
    intro hd
    have hl := congrArg (fun x => x.toList.length) hd
    dsimp only [seg] at hl
    rw [String.toList_ofList, List.length_append] at hl
    have h10 : ".base-keys".toList.length = 10 := by decide
    have h1 : ".".toList.length = 1 := by decide
    omega
  have hpred : (!seg.isEmpty && seg != ".") = true := by rw [hne_str, hndot_b]; rfl
  change List.filter (fun s => !s.isEmpty && s != ".") rest ++
      List.filter (fun s => !s.isEmpty && s != ".") [seg] =
      [pathStr (keyName id)] at htail
  rw [List.filter_cons_of_pos (p := fun s => !s.isEmpty && s != ".") hpred, List.filter_nil] at htail
  have hmem : seg ∈ [pathStr (keyName id)] := by
    rw [← htail]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  rw [List.mem_singleton] at hmem
  rw [hmem] at hdot_in
  exact (keyName_no_dot_or_slash id '.' hdot_in).1 rfl

private theorem encodeKey_length_le_10 (tag : Nat) (wt : WireType) :
    (encodeKey tag wt).length ≤ 10 := by
  unfold encodeKey
  exact (encodeVarint_length_bounds _).2

private theorem encodeProto3Uint32Field_length_le_20 (tag : Nat) (v : BitVec 32) :
    (encodeProto3Uint32Field tag v).length ≤ 20 := by
  unfold encodeProto3Uint32Field encodeUint32Field
  split_ifs
  · simp
  · simp only [List.length_append]
    have hk := encodeKey_length_le_10 tag .varint
    have hv := (encodeVarint_length_bounds (BitVec.zeroExtend 64 v)).2
    omega

private theorem encodeProto3Fixed64Field_length_le_18 (tag : Nat) (v : BitVec 64) :
    (encodeProto3Fixed64Field tag v).length ≤ 18 := by
  unfold encodeProto3Fixed64Field le64Bytes
  split_ifs
  · simp
  · simp only [List.length_append, List.length_cons, List.length_nil]
    have hk := encodeKey_length_le_10 tag .sixtyFourBit
    omega

private theorem encodeProto3BytesField_length_le (tag : Nat) (v : List (BitVec 8)) :
    (encodeProto3BytesField tag v).length ≤ 20 + v.length := by
  unfold encodeProto3BytesField encodeBytesField
  split_ifs
  · simp
  · simp only [List.length_append]
    have hk := encodeKey_length_le_10 tag .lengthDelimited
    have hv := (encodeVarint_length_bounds (BitVec.ofNat 64 v.length)).2
    omega

private theorem head_normalizePath_encodeDir_or_extra {P : PEParams} {st : PqParty}
    {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ encodeDir P st) :
    (normalizePath p = ["address"]) ∨
    (normalizePath p = ["identity-key-pair"] ∧ bs.length ≤ 105) ∨
    (normalizePath p = ["registration-id"]) ∨
    ((normalizePath p).head? = some "identities") ∨
    ((normalizePath p).head? = some "sessions") ∨
    ((normalizePath p).head? = some "signed-pre-keys" ∧ bs.length ≤ 230) ∨
    ((normalizePath p).head? = some "one-time-pre-keys" ∧ bs.length ≤ 125) ∨
    ((normalizePath p).head? = some "one-time-kyber-pre-keys" ∧ bs.length ≤ 4900) ∨
    ((normalizePath p).head? = some "last-resort-kyber-pre-keys" ∧ bs.length ≤ 4900) ∨
    (∃ id', p = baseKeysFile id') := by
  unfold encodeDir at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with ((((((hf_hdr | hf_peer) | hf_sess) | hf_sig) | hf_ot) | hf_kot) | hf_klr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
    rcases hf_hdr with h | h | h
    · injection h with hp _; subst hp
      exact Or.inl (by decide)
    · injection h with hp hbs; subst hp hbs
      refine Or.inr (Or.inl ⟨by decide, ?_⟩)
      unfold IdentityKeyPairStructure.encode
      simp only [List.length_append]
      have h1 := encodeProto3BytesField_length_le 1
        (djbKey (keyPairOf P.C st.me.idPriv).publicKey.bytes)
      have h2 := encodeProto3BytesField_length_le 2 st.me.idPriv.toList
      have hdjb : (djbKey (keyPairOf P.C st.me.idPriv).publicKey.bytes).length = 33 := by
        simp [djbKey]
      have hpriv : st.me.idPriv.toList.length = 32 := st.me.idPriv.toList_length
      omega
    · injection h with hp _; subst hp
      exact Or.inr (Or.inr (Or.inl (by decide)))
  · cases hp : st.peerId with
    | none => simp [hp] at hf_peer
    | some k =>
      simp only [hp, List.mem_singleton] at hf_peer
      injection hf_peer with hp_eq _; subst hp_eq
      refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      have hid : identityFile (partyAddressName st.party.other) =
          "identities" ++ "/" ++ partyAddressName st.party.other := rfl
      rw [hid, normalizePath_string_append_slash (by decide) (by decide) (by decide)]
      rfl
  · cases hs : st.session with
    | none => simp [hs] at hf_sess
    | some xg =>
      rcases xg with ⟨_, _⟩
      simp only [hs, List.mem_singleton] at hf_sess
      injection hf_sess with hp_eq _; subst hp_eq
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      have hsf : sessionFile (partyAddress st.party.other) =
          "sessions" ++ "/" ++ (partyAddress st.party.other).text := rfl
      rw [hsf, normalizePath_string_append_slash (by decide) (by decide) (by decide)]
      rfl
  · rw [List.mem_map] at hf_sig
    rcases hf_sig with ⟨⟨id', k⟩, _, heq⟩
    injection heq with hp_eq hbs_eq; subst hp_eq hbs_eq
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))))
    · have hsp : signedPreKeyFile id' = "signed-pre-keys" ++ "/" ++ toString id'.toNat := rfl
      rw [hsp, normalizePath_string_append_slash (by decide) (by decide) (by decide)]
      rfl
    · unfold signedRecordBytes SignedPreKeyRecordStructure.encode
      simp only [List.length_append]
      have h1 := encodeProto3Uint32Field_length_le_20 1 id'
      have h2 := encodeProto3BytesField_length_le 2
        (djbKey (keyPairOf P.C k.priv).publicKey.bytes)
      have h3 := encodeProto3BytesField_length_le 3 k.priv.toList
      have h4 := encodeProto3BytesField_length_le 4 k.sig.toList
      have h5 := encodeProto3Fixed64Field_length_le_18 5 k.timestamp
      have hdjb : (djbKey (keyPairOf P.C k.priv).publicKey.bytes).length = 33 := by
        simp [djbKey]
      have hpriv : k.priv.toList.length = 32 := k.priv.toList_length
      have hsig : k.sig.toList.length = 64 := k.sig.toList_length
      omega
  · rw [List.mem_map] at hf_ot
    rcases hf_ot with ⟨⟨id', opt⟩, _, heq⟩
    injection heq with hp_eq hbs_eq; subst hp_eq hbs_eq
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))))))
    · have hop : oneTimePreKeyFile id' = "one-time-pre-keys" ++ "/" ++ toString id'.toNat := rfl
      rw [hop, normalizePath_string_append_slash (by decide) (by decide) (by decide)]
      rfl
    · cases opt with
      | none => simp
      | some sk =>
        unfold oneTimeRecordBytes PreKeyRecordStructure.encode
        simp only [List.length_append]
        have h1 := encodeProto3Uint32Field_length_le_20 1 id'
        have h2 := encodeProto3BytesField_length_le 2
          (djbKey (keyPairOf P.C sk).publicKey.bytes)
        have h3 := encodeProto3BytesField_length_le 3 sk.toList
        have hdjb : (djbKey (keyPairOf P.C sk).publicKey.bytes).length = 33 := by
          simp [djbKey]
        have hpriv : sk.toList.length = 32 := sk.toList_length
        omega
  · rw [List.mem_map] at hf_kot
    rcases hf_kot with ⟨⟨id', opt⟩, _, heq⟩
    injection heq with hp_eq hbs_eq; subst hp_eq hbs_eq
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))))))
    · have hkp : oneTimeKyberPreKeyFile id' =
          "one-time-kyber-pre-keys" ++ "/" ++ toString id'.toNat := rfl
      rw [hkp, normalizePath_string_append_slash (by decide) (by decide) (by decide)]
      rfl
    · cases opt with
      | none => simp
      | some k =>
        unfold kyberRecordBytes SignedPreKeyRecordStructure.encode
        simp only [List.length_append]
        have h1 := encodeProto3Uint32Field_length_le_20 1 id'
        have h2 := encodeProto3BytesField_length_le 2 (kyberKey k.pub)
        have h3 := encodeProto3BytesField_length_le 3 (0x08#8 :: k.sec.toList)
        have h4 := encodeProto3BytesField_length_le 4 k.sig.toList
        have h5 := encodeProto3Fixed64Field_length_le_18 5 k.timestamp
        have hpub : (kyberKey k.pub).length = 1569 := by simp [kyberKey]
        have hsec : (0x08#8 :: k.sec.toList).length = 3169 := by simp [k.sec.toList_length]
        have hsig : k.sig.toList.length = 64 := k.sig.toList_length
        omega
  · rw [List.mem_flatten] at hf_klr
    rcases hf_klr with ⟨sub, hsub, hf_in⟩
    rw [List.mem_map] at hsub
    rcases hsub with ⟨⟨id', k, seen⟩, _, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
    rcases hf_in with h | h
    · injection h with hp_eq hbs_eq; subst hp_eq hbs_eq
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))))))))
      · have hlr : lastResortKyberPreKeyFile id' =
            "last-resort-kyber-pre-keys" ++ "/" ++ toString id'.toNat := rfl
        rw [hlr, normalizePath_string_append_slash (by decide) (by decide) (by decide)]
        rfl
      · unfold kyberRecordBytes SignedPreKeyRecordStructure.encode
        simp only [List.length_append]
        have h1 := encodeProto3Uint32Field_length_le_20 1 id'
        have h2 := encodeProto3BytesField_length_le 2 (kyberKey k.pub)
        have h3 := encodeProto3BytesField_length_le 3 (0x08#8 :: k.sec.toList)
        have h4 := encodeProto3BytesField_length_le 4 k.sig.toList
        have h5 := encodeProto3Fixed64Field_length_le_18 5 k.timestamp
        have hpub : (kyberKey k.pub).length = 1569 := by simp [kyberKey]
        have hsec : (0x08#8 :: k.sec.toList).length = 3169 := by simp [k.sec.toList_length]
        have hsig : k.sig.toList.length = 64 := k.sig.toList_length
        omega
    · injection h with hp_eq _
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨id', hp_eq⟩))))))))

private theorem cliPqInputs_mem_encodeDir_or_bc {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ i.files) :
    (∃ st, (p, bs) ∈ encodeDir P st) ∨
    (normalizePath p).head? = some "bundle" ∨
    normalizePath p = ["coins"] := by
  rcases hi with ⟨st, _, hcase⟩
  have hcoins_norm : normalizePath coinsFile = ["coins"] := by decide
  rcases hcase with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ |
      ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩
  · simp only [pqInitInputs, pqInputs, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with (hed | hbun) | hcoins
    · exact Or.inl ⟨st, hed⟩
    · refine Or.inr (Or.inl ?_)
      dsimp only [publicBundleOf, PublicBundle.files] at hbun
      repeat (rcases List.mem_cons.mp hbun with h | hbun; · (rcases Prod.mk.inj h with ⟨rfl, _⟩; decide))
      split at hbun
      · rcases List.mem_singleton.mp hbun with h
        rcases Prod.mk.inj h with ⟨rfl, _⟩
        decide
      · exact False.elim (List.not_mem_nil hbun)
    · injection hcoins with hp _; subst hp; exact Or.inr (Or.inr hcoins_norm)
  · simp only [pqSendInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hed | hcoins
    · exact Or.inl ⟨st, hed⟩
    · injection hcoins with hp _; subst hp; exact Or.inr (Or.inr hcoins_norm)
  · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hed | hcoins
    · exact Or.inl ⟨st, hed⟩
    · injection hcoins with hp _; subst hp; exact Or.inr (Or.inr hcoins_norm)
  · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hed | hcoins
    · exact Or.inl ⟨st, hed⟩
    · injection hcoins with hp _; subst hp; exact Or.inr (Or.inr hcoins_norm)
  · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hed | hcoins
    · exact Or.inl ⟨st, hed⟩
    · injection hcoins with hp _; subst hp; exact Or.inr (Or.inr hcoins_norm)

/-- `DecPkKeyFilesBounded (runFiles i)` holds on any `CliPqxdhInputs P i`. -/
theorem decPkKeyFilesBounded_of_cliPqInputs {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    DecPkKeyFilesBounded (runFiles i) := by
  have hbk_head (id' : BitVec 32) :
      (normalizePath (baseKeysFile id')).head? = some "last-resort-kyber-pre-keys" := by
    have hbk : baseKeysFile id' =
        "last-resort-kyber-pre-keys" ++ "/" ++ (toString id'.toNat ++ ".base-keys") := rfl
    rw [hbk, normalizePath_string_append_slash (by decide) (by decide) (by decide)]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro bs hrd
    rcases cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
    · exact Nat.zero_le 256
    · obtain ⟨p, hmem, hp_norm⟩ := initFsState_files_mem_norm hfile
      have hp_of : pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair") =
          utf8 "identity-key-pair" := rfl
      have hq : normalizePath
          (pathStr (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair"))) =
          ["identity-key-pair"] := by
        rw [hp_of, pathStr_utf8_of_toList (by decide)]
        decide
      rw [hq] at hp_norm
      have hp_head : (normalizePath p).head? = some "identity-key-pair" := by rw [hp_norm]; rfl
      rcases cliPqInputs_mem_encodeDir_or_bc hi hmem with ⟨st, hed⟩ | hbun | hcoins
      · rcases head_normalizePath_encodeDir_or_extra hed with
          h | ⟨_, hle⟩ | h | h | h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨id', rfl⟩
        · rw [hp_norm] at h; exact False.elim (list1_str_ne (by decide) h)
        · omega
        · rw [hp_norm] at h; exact False.elim (list1_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hbk_head id'] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
      · rw [hp_head] at hbun; exact False.elim (opt_str_ne (by decide) hbun)
      · rw [hp_norm] at hcoins; exact False.elim (list1_str_ne (by decide) hcoins)
  · intro id bs hrd
    rcases cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
    · exact Nat.zero_le 512
    · obtain ⟨p, hmem, hp_norm⟩ := initFsState_files_mem_norm hfile
      have hp_eq : StoresGhost.opened.signed.path = utf8 "signed-pre-keys" := rfl
      have hdir_str : pathStr StoresGhost.opened.signed.path = "signed-pre-keys" := by
        rw [hp_eq]; exact pathStr_utf8_of_toList (by decide)
      have hne_p : StoresGhost.opened.signed.path ≠ [] := by
        rw [hp_eq, utf8_eq_kutf8]; decide
      have hq : (normalizePath
          (pathStr (pathOf StoresGhost.opened.signed.path (keyName id)))).head? =
          some "signed-pre-keys" := by
        rw [pathStr_pathOf_nonempty hne_p, hdir_str,
          normalizePath_string_append_slash (by decide) (by decide) (by decide)]
        rfl
      have hp_head : (normalizePath p).head? = some "signed-pre-keys" := by
        rw [hp_norm]; exact hq
      rcases cliPqInputs_mem_encodeDir_or_bc hi hmem with ⟨st, hed⟩ | hbun | hcoins
      · rcases head_normalizePath_encodeDir_or_extra hed with
          h | ⟨h, _⟩ | h | h | h | ⟨_, hle⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨id', rfl⟩
        · rw [h] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
        · rw [h] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
        · rw [h] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · omega
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hbk_head id'] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
      · rw [hp_head] at hbun; exact False.elim (opt_str_ne (by decide) hbun)
      · rw [hcoins] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
  · intro id bs hrd
    rcases cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
    · exact Nat.zero_le 256
    · obtain ⟨p, hmem, hp_norm⟩ := initFsState_files_mem_norm hfile
      have hp_eq : StoresGhost.opened.oneTime.path = utf8 "one-time-pre-keys" := rfl
      have hdir_str : pathStr StoresGhost.opened.oneTime.path = "one-time-pre-keys" := by
        rw [hp_eq]; exact pathStr_utf8_of_toList (by decide)
      have hne_p : StoresGhost.opened.oneTime.path ≠ [] := by
        rw [hp_eq, utf8_eq_kutf8]; decide
      have hq : (normalizePath
          (pathStr (pathOf StoresGhost.opened.oneTime.path (keyName id)))).head? =
          some "one-time-pre-keys" := by
        rw [pathStr_pathOf_nonempty hne_p, hdir_str,
          normalizePath_string_append_slash (by decide) (by decide) (by decide)]
        rfl
      have hp_head : (normalizePath p).head? = some "one-time-pre-keys" := by
        rw [hp_norm]; exact hq
      rcases cliPqInputs_mem_encodeDir_or_bc hi hmem with ⟨st, hed⟩ | hbun | hcoins
      · rcases head_normalizePath_encodeDir_or_extra hed with
          h | ⟨h, _⟩ | h | h | h | ⟨h, _⟩ | ⟨_, hle⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨id', rfl⟩
        · rw [h] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
        · rw [h] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
        · rw [h] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · omega
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hbk_head id'] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
      · rw [hp_head] at hbun; exact False.elim (opt_str_ne (by decide) hbun)
      · rw [hcoins] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
  · intro id bs hrd
    rcases cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
    · exact Nat.zero_le 4900
    · obtain ⟨p, hmem, hp_norm⟩ := initFsState_files_mem_norm hfile
      have hp_eq : StoresGhost.opened.kyber.oneTime.path = utf8 "one-time-kyber-pre-keys" := rfl
      have hdir_str : pathStr StoresGhost.opened.kyber.oneTime.path =
          "one-time-kyber-pre-keys" := by
        rw [hp_eq]; exact pathStr_utf8_of_toList (by decide)
      have hne_p : StoresGhost.opened.kyber.oneTime.path ≠ [] := by
        rw [hp_eq, utf8_eq_kutf8]; decide
      have hq : (normalizePath
          (pathStr (pathOf StoresGhost.opened.kyber.oneTime.path (keyName id)))).head? =
          some "one-time-kyber-pre-keys" := by
        rw [pathStr_pathOf_nonempty hne_p, hdir_str,
          normalizePath_string_append_slash (by decide) (by decide) (by decide)]
        rfl
      have hp_head : (normalizePath p).head? = some "one-time-kyber-pre-keys" := by
        rw [hp_norm]; exact hq
      rcases cliPqInputs_mem_encodeDir_or_bc hi hmem with ⟨st, hed⟩ | hbun | hcoins
      · rcases head_normalizePath_encodeDir_or_extra hed with
          h | ⟨h, _⟩ | h | h | h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hle⟩ | ⟨h, _⟩ | ⟨id', rfl⟩
        · rw [h] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
        · rw [h] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
        · rw [h] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · exact hle
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hbk_head id'] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
      · rw [hp_head] at hbun; exact False.elim (opt_str_ne (by decide) hbun)
      · rw [hcoins] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
  · intro id bs hrd
    rcases cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
    · exact Nat.zero_le 4900
    · obtain ⟨p, hmem, hp_norm⟩ := initFsState_files_mem_norm hfile
      have hp_eq : StoresGhost.opened.kyber.lastResort.path =
          utf8 "last-resort-kyber-pre-keys" := rfl
      have hdir_str : pathStr StoresGhost.opened.kyber.lastResort.path =
          "last-resort-kyber-pre-keys" := by
        rw [hp_eq]; exact pathStr_utf8_of_toList (by decide)
      have hne_p : StoresGhost.opened.kyber.lastResort.path ≠ [] := by
        rw [hp_eq, utf8_eq_kutf8]; decide
      have hq_full : normalizePath
          (pathStr (pathOf StoresGhost.opened.kyber.lastResort.path (keyName id))) =
          ["last-resort-kyber-pre-keys", pathStr (keyName id)] := by
        rw [pathStr_pathOf_nonempty hne_p, hdir_str,
          normalizePath_string_append_slash (by decide) (by decide) (by decide),
          normalizePath_keyName]
      have hp_head : (normalizePath p).head? = some "last-resort-kyber-pre-keys" := by
        rw [hp_norm, hq_full]; rfl
      rcases cliPqInputs_mem_encodeDir_or_bc hi hmem with ⟨st, hed⟩ | hbun | hcoins
      · rcases head_normalizePath_encodeDir_or_extra hed with
          h | ⟨h, _⟩ | h | h | h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hle⟩ | ⟨id', rfl⟩
        · rw [h] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
        · rw [h] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
        · rw [h] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · rw [hp_head] at h; exact False.elim (opt_str_ne (by decide) h)
        · exact hle
        · rw [hq_full] at hp_norm
          exact False.elim (normalizePath_baseKeysFile_ne_keyName id' id hp_norm)
      · rw [hp_head] at hbun; exact False.elim (opt_str_ne (by decide) hbun)
      · rw [hcoins] at hp_head; exact False.elim (opt_str_ne (by decide) hp_head)

/-- `DecPkKeyFilesBounded (runFiles i)` holds on either `CliPqxdhInputs P i` or any
`pqRecvInputs P st ct rc` call with `PqxdhPartyInSpecDomain P st`. -/
theorem decPkKeyFilesBounded_of_pqOrD3Recv {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc) :
    DecPkKeyFilesBounded (runFiles i) := by
  rcases hi with hcli | ⟨st, ct, rc, hwf, rfl⟩
  · exact decPkKeyFilesBounded_of_cliPqInputs hcli
  · have hrf : runFiles (pqRecvInputs P st ct rc) = runFiles (pqRecvInputs P st [] rc) := rfl
    rw [hrf]
    exact decPkKeyFilesBounded_of_cliPqInputs
      ⟨st, hwf, Or.inr (Or.inr (Or.inr (Or.inr ⟨[], rc, by decide, by decide, by decide, rfl⟩)))⟩

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
