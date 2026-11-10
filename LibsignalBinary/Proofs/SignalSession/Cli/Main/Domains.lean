/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqDir
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.ToString.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Model
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top

/-!
# Argument Parsing on `CliSpec` Domain Inputs

Proves that every command line `Cmd.argv` targeting `partyAddress P` (`DomainArgv`) parses under
`parseArgs uuidTryParse` to a `CallV` with nonzero tag (`init` = 1, `send` = 2, `recv` = 3,
excluding `keygen` = 0). Covers all inputs of `CliSpecE` and `CliSpecPqxdh`.
-/

@[expose] public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

/-! ## Party Addresses -/

private theorem addrParse_addrE_shape : ∀ P : Party,
    (addrParse uuidTryParse (bytesOfString (partyAddress P).text)).map (fun v => (v.name, v.device)) =
      some (utf8 (partyAddressName P), 1#8) := by
  intro P
  cases P <;> decide +kernel

/-- Both parties' address strings parse under `uuidTryParse` to `(utf8 (partyAddressName P), 1#8)`. -/
theorem addrParse_addrE (P : Party) :
    addrParse uuidTryParse (bytesOfString (partyAddress P).text) = some ⟨utf8 (partyAddressName P), 1#8⟩ := by
  have h := addrParse_addrE_shape P
  cases hv : addrParse uuidTryParse (bytesOfString (partyAddress P).text) with
  | none => rw [hv] at h; cases h
  | some v =>
    rw [hv] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hn, hd⟩ := h
    cases v
    simp only at hn hd
    rw [hn, hd]

/-! ## Domain Commands -/

def cmdPeer : Cmd → Address
  | .init peer _ => peer
  | .send peer => peer
  | .recv peer => peer

/-- Tag decoded by `main` for a domain command (`CallV.tag`): `init` = 1, `send` = 2, `recv` = 3. -/
def cmdTag : Cmd → Nat
  | .init .. => 1
  | .send _ => 2
  | .recv _ => 3

theorem cmdTag_ne_zero (cmd : Cmd) : cmdTag cmd ≠ 0 := by
  cases cmd <;> simp [cmdTag]

/-- Every domain command to `partyAddress P` parses under `uuidTryParse` with tag `cmdTag cmd ≠ 0`. -/
theorem parseArgs_cmd (cmd : Cmd) {P : Party} (hP : cmdPeer cmd = partyAddress P) :
    ∃ c, parseArgs uuidTryParse (cmd.argv.map bytesOfString) = some c ∧ c.tag = cmdTag cmd := by
  have hi : bytesOfString "init" = utf8 "init" := by decide +kernel
  have hs : bytesOfString "send" = utf8 "send" := by decide +kernel
  have hr : bytesOfString "recv" = utf8 "recv" := by decide +kernel
  have hk : utf8 "init" ≠ utf8 "keygen" := by decide +kernel
  have hrs : utf8 "recv" ≠ utf8 "send" := by decide +kernel
  have ha := addrParse_addrE P
  cases cmd with
  | init peer b =>
    simp only [cmdPeer] at hP
    subst hP
    refine ⟨.init ⟨utf8 (partyAddressName P), 1#8⟩ (bytesOfString b), ?_, rfl⟩
    simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hi, hk, ha, Option.map_some,
      ↓reduceIte]
  | send peer =>
    simp only [cmdPeer] at hP
    subst hP
    refine ⟨.send ⟨utf8 (partyAddressName P), 1#8⟩, ?_, rfl⟩
    simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hs, ha, Option.map_some,
      ↓reduceIte]
  | recv peer =>
    simp only [cmdPeer] at hP
    subst hP
    refine ⟨.recv ⟨utf8 (partyAddressName P), 1#8⟩, ?_, rfl⟩
    simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hr, hrs, ha, Option.map_some,
      ↓reduceIte]

/-! ## Domain Inputs -/

/-- Predicate asserting that `i.argv` is a domain command targeting some `partyAddress P`. -/
def DomainArgv (i : Inputs) : Prop :=
  ∃ (P : Party) (cmd : Cmd), cmdPeer cmd = partyAddress P ∧ i.argv = cmd.argv

/-- Every `DomainArgv` input parses under `uuidTryParse` to a call with nonzero tag. -/
theorem parseArgs_domain {i : Inputs} (h : DomainArgv i) :
    ∃ c, parseArgs uuidTryParse (i.argv.map bytesOfString) = some c ∧ c.tag ≠ 0 := by
  obtain ⟨P, cmd, hP, harg⟩ := h
  obtain ⟨c, hc, ht⟩ := parseArgs_cmd cmd hP
  exact ⟨c, harg ▸ hc, ht ▸ cmdTag_ne_zero cmd⟩

theorem parseArgs_of_run {Run : Inputs → RunAnswer → Prop} (hdom : ∀ i a, Run i a → DomainArgv i)
    {i : Inputs} {a : RunAnswer} (hr : Run i a) :
    ∃ c, parseArgs uuidTryParse (i.argv.map bytesOfString) = some c ∧ c.tag ≠ 0 :=
  parseArgs_domain (hdom i a hr)

/-- Discharges `main_ok`'s `hparse` hypothesis for any `Run` supported on `DomainArgv`. -/
theorem hparse_of_domains {Run : Inputs → RunAnswer → Prop}
    (hdom : ∀ i a, Run i a → DomainArgv i) :
    ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome := by
  intro i a hr
  obtain ⟨c, hc, -⟩ := parseArgs_of_run hdom hr
  simp only [hc, Option.isSome_some]

/-! ## Per-Input Corollaries -/

theorem domainArgv_smSend (g : GhostState Bytes) (m : List (BitVec 8)) :
    DomainArgv (smSendInputs g m) :=
  ⟨g.party.other, .send (partyAddress g.party.other), rfl, rfl⟩

theorem domainArgv_smRecv (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256) :
    DomainArgv (smRecvInputs g c rc) :=
  ⟨g.party.other, .recv (partyAddress g.party.other), rfl, rfl⟩

theorem domainArgv_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : DomainArgv (pqInitInputs W st b t) :=
  ⟨st.party.other, .init (partyAddress st.party.other) bundleDir, rfl, rfl⟩

theorem domainArgv_pqSend (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) : DomainArgv (pqSendInputs W st m r) :=
  ⟨st.party.other, .send (partyAddress st.party.other), rfl, rfl⟩

theorem domainArgv_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) :
    DomainArgv (pqRecvInputs W st c rc) :=
  ⟨st.party.other, .recv (partyAddress st.party.other), rfl, rfl⟩

theorem parseArgs_smSend (g : GhostState Bytes) (m : List (BitVec 8)) :
    ∃ c, parseArgs uuidTryParse ((smSendInputs g m).argv.map bytesOfString) = some c ∧
      c.tag ≠ 0 :=
  parseArgs_domain (domainArgv_smSend g m)

theorem parseArgs_smRecv (g : GhostState Bytes) (c : List (BitVec 8)) (rc : BitVec 256) :
    ∃ v, parseArgs uuidTryParse ((smRecvInputs g c rc).argv.map bytesOfString) = some v ∧
      v.tag ≠ 0 :=
  parseArgs_domain (domainArgv_smRecv g c rc)

theorem parseArgs_pqInit (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ∃ c, parseArgs uuidTryParse ((pqInitInputs W st b t).argv.map bytesOfString) = some c ∧
      c.tag ≠ 0 :=
  parseArgs_domain (domainArgv_pqInit W st b t)

theorem parseArgs_pqSend (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    ∃ c, parseArgs uuidTryParse ((pqSendInputs W st m r).argv.map bytesOfString) = some c ∧
      c.tag ≠ 0 :=
  parseArgs_domain (domainArgv_pqSend W st m r)

theorem parseArgs_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256) :
    ∃ v, parseArgs uuidTryParse ((pqRecvInputs W st c rc).argv.map bytesOfString) = some v ∧
      v.tag ≠ 0 :=
  parseArgs_domain (domainArgv_pqRecv W st c rc)

end CryptoVerification.SignalSession.Cli.MainHops
