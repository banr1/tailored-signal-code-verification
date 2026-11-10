/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Syscalls.Common
public import Arm64.Trusted.Syscalls.Fs.Select

/-!
# Startup Standard-Descriptor `POLLNVAL` Probe

Re-exports [`Arm64.Trusted.Syscalls.Fs.Select`](Fs/Select.lean) (`fs/select.c`: `SYS_PPOLL`,
`POLLNVAL`, `evalPpollEntries`, `execPpoll`) and defines the single-entry syscall bundle
`Syscall.poll` for non-blocking standard-descriptor validity checks (`ppoll` with `events = 0` and
zero timeout).
-/

@[expose] public section

namespace Arm64

namespace Syscall

/-- Single-entry dispatch table for `ppoll` (`73`). -/
def pollTable : List (BitVec 64 × (State → State)) :=
  [(SYS_PPOLL, execPpoll)]

/-- Bundle permitting `ppoll` (`73`) for startup `POLLNVAL` probing on `fd ∈ {0, 1, 2}`
    (always reports `revents = 0` on open `.stdio`/`.localFile` fds; `POLLHUP`/`POLLERR` are not
    modeled). -/
def poll : State → State := dispatch pollTable

end Syscall

end Arm64
