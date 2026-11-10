/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Epilogue and Cut Combinators Re-export for `get_signed_pre_key::{closure#0}`

Re-exports `sepWP_frame_cut_placed`, `sepWPp_frame_cut_placed`, `spkEpiPost_pack_p`, and
`epilogue_placed_ok` on Block `571` (`lsProg_571 H`) from `Store/SpkGetPoll/CalleesPlaced.lean`.
-/

@[expose] public section

set_option autoImplicit false
