import Lean
import Mathlib.Tactic.Linter.UnusedTacticExtension

/-!
# `claude` — ask the Claude Code CLI what to do next

`claude` pretty-prints the current proof state, hands it to the `claude` CLI in
headless mode (`claude -p`), and reports the answer: the tactic block it comes
back with is offered as a "Try this" suggestion, and the prose around it is
logged underneath.

    example : Gate.T ≫ Gate.T ≈zx Gate.S := by
      claude
      claude "I want to avoid unfolding Gate.T"

The tactic never touches the goal — it only logs — so it is safe to leave in a
proof, and `#allow_unused_tactic!` stops the linter flagging it.

It reads the goal and nothing else, so it works on either representation and
imports neither. It is also development scaffolding rather than part of the
library: `SpLean.All` deliberately does not import it, so nothing published
pulls it in, and this file is the only place its behaviour is written down.
`import SpLean.Claude` in whatever file you want to ask from, and take that
import back out again before the file is merged.

The CLI runs read-only (`--allowedTools Read,Grep,Glob`), so it can look at the
rules and `CLAUDE.md` for context but cannot edit the project. It is invoked in
Lean's working directory, which is the project root, so project `CLAUDE.md`
files are picked up automatically.

## Not calling the CLI on every keystroke

Lean re-elaborates a file on every edit, so a naive version fires a CLI call per
keystroke — including the half-typed ones, so merely typing `claude "..."` bills
a call for `claude`, one for `claude "I`, and so on. Three things stop that:

* **Call-site identity.** Every invocation is keyed by `file:line:column` of the
  `claude` token, and each key holds a generation counter. Starting a call at a
  key bumps its generation and kills whatever that key still had running, so a
  line never has more than one CLI process in flight. Editing the *message* on a
  line does not move the token, so the retyped invocation supersedes the old one
  rather than racing it.
* **A debounce.** Once claimed, the call waits `splean.claude.debounce`
  milliseconds (800 by default) before spawning anything, and drops out if a
  newer invocation for the same call site arrives, or if Lean cancels the
  elaboration in the meantime. Typing straight through a `claude` line therefore
  spawns nothing at all.
* **Cancellation.** While the CLI runs, the call polls `IO.checkCanceled` — the
  same flag `Lean.Core.checkSystem` reads — and kills the process the moment
  Lean loses interest in the elaboration that started it. Children are spawned
  with `setsid`, so the kill takes the CLI's own subprocesses with it.

A kill surfaces as a nonzero exit code (137), so staleness is checked *before*
the exit code is believed — both in the poll loop and once more after it — or a
superseded run would report itself as a CLI failure.

Answers are also cached per prompt in `claudeCache` for the life of the language
server, so re-elaborating an unchanged goal is free (and skips the debounce,
which is what makes an undo redisplay instantly). Restarting the server forgets
everything.

Each prompt opens with a `[splean-claude file:line:column]` tag, and the prompt
is argv, so `ps -eo pid,etime,command | grep "[s]plean-claude"` lists exactly the
CLI runs Lean started and where each one came from. Note that this puts the
proof state in `ps` output, which is visible to other users on a shared machine.

Elaboration *blocks* while Claude thinks; there is no timeout.
-/

open Lean Elab Tactic Meta Meta.Tactic.TryThis

register_option splean.claude.debounce : Nat := {
  defValue := 800
  descr := "Milliseconds the `claude` tactic waits before calling the CLI. A call \
    superseded from the same call site, or cancelled by Lean, during the wait never \
    spawns a process at all; raise this if typing still starts calls."
}

namespace SpLean

/-! ## The CLI process -/

/-- The stdio shape of every spawned run, named so that a `Child` can be stored. -/
private abbrev claudeStdio : IO.Process.StdioConfig :=
  { stdin := .null, stdout := .piped, stderr := .piped }

private abbrev ClaudeChild := IO.Process.Child claudeStdio

/-- Start the CLI headlessly. `setsid` puts it in its own process group, so
`Child.kill` takes the CLI's own subprocesses down with it rather than orphaning
them. -/
private def spawnClaude (prompt : String) : IO ClaudeChild :=
  IO.Process.spawn {
    cmd := "claude"
    args := #["-p", prompt, "--output-format", "text", "--allowedTools", "Read,Grep,Glob"]
    stdin := .null, stdout := .piped, stderr := .piped
    setsid := true
  }

/-! ## Per-call-site bookkeeping -/

/-- What one call site (`file:line:column`) currently has going on. -/
private structure ClaudeSlot where
  /-- Highest generation claimed here; anything older is superseded. -/
  latest : Nat := 0
  /-- The CLI process in flight, with the generation that spawned it. -/
  running : Option (Nat × ClaudeChild) := none

/-- Live state per call site. A `Ref` rather than an environment extension because
it has to be shared across the elaborations of *different* versions of the file —
that is the whole point of it. -/
initialize claudeRuns : IO.Ref (Std.HashMap String ClaudeSlot) ← IO.mkRef ∅

/-- Answers already received, keyed by the exact prompt sent. -/
initialize claudeCache : IO.Ref (Std.HashMap String String) ← IO.mkRef ∅

/-- Take ownership of a call site: bump its generation and kill whatever the
previous owner left running. Returns the new generation. -/
private def claimSite (site : String) : IO Nat := do
  let (gen, previous) ← claudeRuns.modifyGet fun runs =>
    let slot := runs.getD site {}
    let gen := slot.latest + 1
    ((gen, slot.running), runs.insert site { latest := gen, running := none })
  -- The killed run reaps its own child; it is still polling and will notice.
  if let some (_, child) := previous then
    try child.kill catch _ => pure ()
  return gen

/-- Has this call gone stale — either Lean gave up on the elaboration, or a newer
invocation from the same call site took over? -/
private def superseded (site : String) (gen : Nat) : IO Bool := do
  if ← IO.checkCanceled then return true
  let runs ← claudeRuns.get
  return runs[site]?.map (·.latest) != some gen

/-- Give up the slot, unless a newer generation already owns it. -/
private def releaseSite (site : String) (gen : Nat) : IO Unit :=
  claudeRuns.modify fun runs =>
    match runs[site]? with
    | some slot@{ running := some (g, _), .. } =>
      if g == gen then runs.insert site { slot with running := none } else runs
    | _ => runs

/-- Wait out the debounce in slices, watching for the call going stale.
Returns `true` if it did, in which case nothing should be spawned. -/
private def debounce (site : String) (gen : Nat) (ms : Nat) : IO Bool := do
  let mut waited := 0
  while waited < ms do
    if ← superseded site gen then return true
    IO.sleep (min 50 (ms - waited)).toUInt32
    waited := waited + 50
  superseded site gen

/-- Run the CLI to completion, killing it if the call goes stale meanwhile.
`none` means it did — the answer is no longer wanted, so there is nothing to
report. -/
private def runClaudeCLI (site : String) (gen : Nat) (prompt : String) : IO (Option String) := do
  let child ← spawnClaude prompt
  claudeRuns.modify fun runs =>
    let slot := runs.getD site {}
    -- Only register if we still own the site; otherwise the kill below is ours to do.
    if slot.latest == gen then runs.insert site { slot with running := some (gen, child) } else runs
  -- Drain both pipes concurrently: a full pipe would block the child forever.
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  let mut exitCode := 0
  repeat
    -- Staleness is checked *before* the exit code, so that a process killed out
    -- from under us is reported as superseded rather than as a CLI failure.
    if ← superseded site gen then
      try child.kill catch _ => pure ()
      discard <| child.wait
      releaseSite site gen
      return none
    if let some code ← child.tryWait then
      exitCode := code
      break
    IO.sleep 100
  releaseSite site gen
  -- A kill landing between the staleness check and `tryWait` surfaces here as a
  -- nonzero exit (SIGKILL, 137), so ask again before blaming the CLI for it.
  if ← superseded site gen then return none
  if exitCode != 0 then
    throw <| IO.userError s!"`claude` exited with code {exitCode}:\n{← IO.ofExcept stderr.get}"
  return some (← IO.ofExcept stdout.get)

/-! ## The prompt -/

/-- `file:line:column` of the `claude` token: the identity of this call site, and
the tag the prompt carries so that `ps` says where a running CLI came from. -/
private def callSite : TacticM String := do
  let fileName ← getFileName
  let fileMap ← getFileMap
  match (← getRef).getPos?.map fileMap.toPosition with
  | some pos => return s!"{fileName}:{pos.line}:{pos.column}"
  | none     => return fileName

/-- The whole proof state — every goal, with its hypotheses — as Claude sees it. -/
private def ppProofState : TacticM String := do
  let goals ← getGoals
  if goals.isEmpty then return "No goals remain."
  let printed ← goals.mapM fun g => return (← Meta.ppGoal g).pretty
  return String.intercalate "\n\n" printed

/-- Standing instructions: what the CLI is being asked for, and in what shape.

The answer is parsed by `splitResponse`, so the fenced block is a request for a
machine-readable answer rather than a formatting preference. -/
private def claudeInstructions : String :=
"You are being called from inside a Lean 4 proof by a tactic named `claude`.
The user is stuck at the proof state below and wants to know what to do next.

Answer with:
1. a fenced ```lean block holding ONLY the tactic lines you suggest, then
2. a short explanation — a few sentences, not an essay.

Read the project's files if you need to check what a rule, lemma or tactic
actually does; you have read-only access and must not try to edit anything.
If nothing obviously applies, say so plainly and suggest the most promising
next step rather than inventing a tactic that will not fire."

/-- Assemble the prompt: the call-site tag (which doubles as the `ps` marker),
the standing instructions, the user's message if they gave one, and the state. -/
private def buildPrompt (site : String) (msg : Option String) : TacticM String := do
  let mut prompt := s!"[splean-claude {site}]\n\n{claudeInstructions}"
  if let some m := msg then
    prompt := prompt ++ s!"\n\nThe user says: {m}"
  return prompt ++ s!"\n\nProof state:\n\n{← ppProofState}"

/-! ## Reporting the answer -/

private def trim (s : String) : String := s.trimAscii.toString

/-- Split an answer into its first fenced code block and the prose around it.

The text between the opening fence and the first newline is the fence's info
string (`lean`), not code, so it is dropped. Anything after the closing fence is
glued back onto the prose, further fences and all. -/
private def splitResponse (response : String) : Option String × String :=
  match response.splitOn "```" with
  | pre :: block :: rest =>
    let code := trim (String.intercalate "\n" ((block.splitOn "\n").drop 1))
    if code.isEmpty then (none, trim response)
    else (some code, trim (trim pre ++ "\n\n" ++ trim (String.intercalate "```" rest)))
  | _ => (none, trim response)

/-- Offer the tactic block as a "Try this" suggestion and log the prose under it. -/
private def report (response : String) : TacticM Unit := do
  let (code?, prose) := splitResponse response
  if let some code := code? then
    addSuggestion (← getRef) (code : SuggestionText) (header := "Claude suggests: ")
  unless prose.isEmpty do logInfo prose

/-! ## The tactic -/

/-- Ask the Claude Code CLI what to do with the current proof state.

    claude
    claude "the RHS is the one I can't get to"

Logs only; the goal is left exactly as it was. The call is debounced by
`splean.claude.debounce` milliseconds and superseded by any later call from the
same line, so typing does not start a pile of CLI processes. -/
elab (name := claudeTactic) "claude" msg:(str)? : tactic => withMainContext do
  let site ← callSite
  let prompt ← buildPrompt site (msg.map (·.getString))
  -- Claim first even when the answer turns out to be cached: an in-flight run
  -- from an earlier version of this line is stale either way, and wants killing.
  let gen ← claimSite site
  if let some cached := (← claudeCache.get)[prompt]? then
    report cached
    return
  if ← debounce site gen (splean.claude.debounce.get (← getOptions)) then return
  let response? ←
    try runClaudeCLI site gen prompt
    catch e => throwError "Could not run the `claude` CLI: {e.toMessageData}"
  let some response := response? | return
  claudeCache.modify (·.insert prompt response)
  report response

-- `claude` deliberately leaves the goal untouched, so the unused-tactic linter
-- would flag every use. The `!` carries the exemption into importing files.
#allow_unused_tactic! SpLean.claudeTactic

end SpLean
