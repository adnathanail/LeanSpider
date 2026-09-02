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

The CLI runs read-only, so it can look at the rules and `CLAUDE.md` for context
but cannot edit the project. That takes both tool flags, not one:
`--allowedTools Read,Grep,Glob` is an allow-list layered *on top of* whatever the
user's own `settings.json` already permits, so on its own it forbids nothing —
a `Bash(...)` rule sitting in that file would still fire, on a project the user
only opened in an editor. `--disallowedTools` is the half that actually denies,
and it wins over both. The CLI is invoked in Lean's working directory, which is
the project root, so project `CLAUDE.md` files are picked up automatically.

## Not calling the CLI on every keystroke

Lean re-elaborates a file on every edit, so a naive version fires a CLI call per
keystroke — including the half-typed ones, so merely typing `claude "..."` bills
a call for `claude`, one for `claude "I`, and so on. Four things stop that:

* **Call-site identity.** Every invocation is keyed by `file:line:column` of the
  `claude` token, and each key holds a generation counter. Starting a call at a
  key bumps its generation and supersedes whatever that key still had running, so
  a line never has more than one CLI process in flight. Editing the *message* on
  a line does not move the token, so the retyped invocation supersedes the old
  one rather than racing it.
* **Adoption.** Superseding only *kills* the run it takes over from if the prompt
  has changed. Lean re-elaborates on an edit anywhere above the `claude` line, so
  a version that always killed would throw away a run that was about to answer —
  and pay for its replacement — on every keystroke in a comment ten lines up; on
  a file being actively edited the answer would never arrive at all. A run whose
  prompt is byte-identical is handed to the new invocation instead, clock and
  activity list included.
* **A debounce.** Once claimed, the call waits `splean.claude.debounce`
  milliseconds (800 by default) before spawning anything, and drops out if a
  newer invocation for the same call site arrives, or if Lean cancels the
  elaboration in the meantime. Typing straight through a `claude` line therefore
  spawns nothing at all.
* **Cancellation.** While the CLI runs, the call polls the cancellation token of
  the background task it runs in, which Lean sets when it throws away the
  snapshot the task hangs off — including when the `claude` call is edited away,
  the one case no later invocation exists to supersede. The process dies the
  moment Lean loses interest. Note that this is *not* `IO.checkCanceled`:
  document edits leave the task flag alone, so a version polling only that one
  keeps running after the line is gone.

Adoption is why a run does not belong to the elaboration that started it. The
CLI process, the tasks draining its pipes and the answer they produce belong to
the call site, and are driven by a task of their own that no elaboration
cancels. What an elaboration's background task does is *watch* — for the answer,
or for its own call going stale — and it kills the run only when it goes stale
while the site still names it the run's owner, which is exactly the case where
no later invocation exists to decide.

Two smaller guards under those. Children are spawned with `setsid`, so a kill
takes the CLI's own subprocesses with it rather than orphaning them; and since
none of the above can run if the file worker itself dies — a server restart, a
crash — the CLI is started under a shell that watches the worker's pid and kills
it when that goes.

A kill surfaces as a nonzero exit code (137), so staleness is checked *before*
the exit code is believed — both in the poll loop and once more after it — or a
superseded run would report itself as a CLI failure.

Answers are also cached per prompt in `claudeCache` for the life of the language
server, so re-elaborating an unchanged goal is free (and skips the debounce,
which is what makes an undo redisplay instantly). Restarting the server forgets
everything.

Each prompt opens with a `[splean-claude file:line:column]` tag, and reaches the
CLI as argv, so

    ps -eo pid,etime,command | grep "[s]plean-claude"

lists exactly the CLI runs Lean started, one line each, and says which line of
which file each came from. The wrapper shell and its watchdog do not match: the
prompt reaches them through the environment, so only the CLI's own arguments
carry the tag. Note that this does put the proof state in `ps` output, which is
visible to other users on a shared machine.

## Not blocking the editor

Waiting for the CLI on the elaboration thread would freeze the file: no later
command elaborates, and the InfoView stops responding, for as long as Claude
thinks. So everything after the prompt is built — the debounce, the CLI run, and
the reporting of its answer — happens in a background task, registered with
`Core.logSnapshotTask` and given its own `IO.CancelToken`. The tactic itself
returns immediately (it has nothing to do to the goal), the rest of the file
elaborates as usual, and the answer arrives in the InfoView whenever it arrives,
as a diagnostic on the `claude` line; that line shows as still being processed
until it does. There is no timeout.

The suggestion is reported from the task rather than from the elaboration, so it
arrives as the message widget only: clicking "Try this" in the InfoView inserts
the tactics as ever, but the code action on the line — the editor lightbulb —
is not offered, since a background task's info tree is not kept.

A cached answer is still reported synchronously, so an undo redisplays it in the
same elaboration rather than a task later.

## Saying that it is running

A background call also means the `claude` line has nothing on it until the answer
lands, which reads exactly like a tactic that did nothing. So the elaboration
logs one more message: a widget that polls `claudeStatus` for its own call site
and redraws itself, since live output cannot otherwise reach a line Lean has
finished elaborating. It shows a spinner, the elapsed time, and the last few
things Claude said it was doing; when the run ends it collapses to a single line
with the turn count and the cost, and a run the server has since forgotten (a
newer call took the site, or the server restarted) renders as nothing at all.

Feeding it means asking the CLI for `--output-format stream-json` rather than
`text`: stdout is then one JSON event per line — each tool call, each thing
Claude says — with the answer in the last event, instead of the answer in one go
at the end. Events are parsed for display only, so an unrecognised or unparsable
line is skipped rather than raised; if the terminating `result` event never
arrives, the concatenated assistant text stands in for the answer.
-/

open Lean Server Elab Tactic Meta Meta.Tactic.TryThis

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

/-- The CLI run, wrapped in a watchdog that outlives nothing.

Killing the language server (or restarting the file worker) while a call is in
flight would otherwise leave the CLI running with no one left to stop it — Lean
runs no exit hook we could hang a kill on, and `setsid` has by then detached the
process from any signal the editor sends. So the CLI is started under a shell
that polls for `ppid`, the worker that spawned it, and kills the CLI when it
goes, firmly (`TERM`, then `KILL`) because the CLI does not always go on `TERM`.

The prompt is read from the environment rather than passed as an argument, so it
lands in exactly one process's `ps` line — the CLI's — instead of being copied
into the wrapper's and the watchdog subshell's as well. It cannot go on stdin,
which would be tidier still: the CLI reads a piped stdin as *context* and still
answers the `-p` argument, so a short argv tag pointing at stdin gets an answer
about the tag ("I'll analyze the proof state from stdin") rather than about the
goal. -/
private def watchdogScript (ppid : UInt32) : String :=
  s!"claude -p \"$SPLEAN_CLAUDE_PROMPT\" --output-format stream-json --verbose \
       --allowedTools Read,Grep,Glob \
       --disallowedTools Write,Edit,NotebookEdit,Bash,WebFetch,WebSearch,Task &
     kid=$!
     ( while kill -0 {ppid} 2>/dev/null; do sleep 2; done
       kill $kid 2>/dev/null; sleep 2; kill -KILL $kid 2>/dev/null ) &
     watchdog=$!
     wait $kid
     status=$?
     kill $watchdog 2>/dev/null
     exit $status"

/-- Start the CLI headlessly. `setsid` puts the shell, the CLI and the watchdog in
one process group, which is what `killRun` then aims at. -/
private def spawnClaude (site : String) (prompt : String) : IO ClaudeChild := do
  IO.Process.spawn {
    cmd := "sh"
    args := #["-c", watchdogScript (← IO.Process.getPID)]
    env := #[("SPLEAN_CLAUDE_PROMPT", some s!"[splean-claude {site}]\n\n{prompt}")]
    stdin := .null, stdout := .piped, stderr := .piped
    setsid := true
  }

/-- Stop a run and everything it started.

`Child.kill` alone is not enough: it signals the group, but the CLI does not
reliably die on `TERM` — the wrapper and the watchdog go, and the CLI is left
reparented to `init`, which is exactly the leak this whole file exists to avoid.
So the group gets `TERM` and then, two seconds later, `KILL`. The escalation runs
in a detached shell rather than here, so that killing a run never blocks the
elaboration doing the killing.

That shell is `wait`ed on, from a task whose whole job is to do so. Lean reaps no
child it is not told to wait for, so spawning the escalation and discarding it
leaves a zombie in the file worker per kill — and an edit above a `claude` line
is a kill, so an editing session accumulates them until the worker cannot spawn
anything at all, the CLI included. The killed run itself is reaped by `driveRun`,
which is the one place that waits on it.

`setsid` at spawn is what makes the child's pid its process group id, so `-pid`
names the shell, the CLI and the watchdog together. -/
private def killRun (child : ClaudeChild) : IO Unit := do
  let pgid := child.pid
  discard <| IO.asTask (prio := Task.Priority.dedicated) do
    try
      let killer ← IO.Process.spawn {
        cmd := "sh"
        args := #["-c", s!"kill -TERM -{pgid} 2>/dev/null; sleep 2; kill -KILL -{pgid} 2>/dev/null"]
        stdin := .null, stdout := .null, stderr := .null
        setsid := true
      }
      discard <| killer.wait
    catch _ => pure ()
  try child.kill catch _ => pure ()

/-! ## Per-call-site bookkeeping -/

/-- What a call has done so far, as the progress widget shows it.

Deliberately all strings and already formatted: the widget draws what it is
handed and knows nothing about the CLI's output format. -/
private structure ClaudeProgress where
  /-- `waiting` during the debounce, `running` once the CLI is up, then `done` or
  `failed`. The widget stops polling on the last two. -/
  phase : String := "waiting"
  /-- The last few things Claude said it was doing, oldest first. -/
  activity : Array String := #[]
  /-- `IO.monoMsNow` when the call site was claimed. -/
  startedMs : Nat := 0
  /-- `IO.monoMsNow` when the run ended, if it has; until then the clock runs. -/
  finishedMs : Option Nat := none
  /-- Turns and cost, once the CLI reports them. -/
  summary : String := ""
  deriving Inhabited

/-- A CLI run in flight, as the call site holds it rather than any one elaboration.

A run outlives the elaboration that started it: a later invocation that finds its
own prompt already running here adopts the run instead of paying for the same
answer twice. So everything needed to take one over lives in this structure,
rather than on the stack of whoever spawned it. -/
private structure ClaudeRun where
  /-- The generation that owns the run. Re-stamped on adoption, which is how the
  previous owner learns it has been handed on rather than simply superseded. -/
  gen : Nat
  /-- The prompt it was spawned with; a later call matching it adopts the run. -/
  prompt : String
  /-- The wrapper shell. `setsid` makes its pid the group `killRun` aims at. -/
  child : ClaudeChild
  /-- `gen` again, somewhere the pipe-draining task can see it change, so that an
  adopted run's activity lines land on the widget now watching it. -/
  genRef : IO.Ref Nat
  /-- The answer and the widget's summary line, or the failure, once `driveRun`
  has them; `none` until then. This is what a watcher polls. -/
  done : IO.Ref (Option (Except IO.Error (String × String)))

/-- What one call site (`file:line:column`) currently has going on. -/
private structure ClaudeSlot where
  /-- Highest generation claimed here; anything older is superseded. -/
  latest : Nat := 0
  /-- The run in flight, if there is one. Its `gen` says who owns it, which is not
  necessarily the generation that spawned it. -/
  running : Option ClaudeRun := none
  /-- What the widget on this line is showing; reset whenever the site is claimed,
  except by an adoption, which inherits it. -/
  progress : ClaudeProgress := {}

/-- Live state per call site. A `Ref` rather than an environment extension because
it has to be shared across the elaborations of *different* versions of the file —
that is the whole point of it. -/
initialize claudeRuns : IO.Ref (Std.HashMap String ClaudeSlot) ← IO.mkRef ∅

/-- Answers already received, keyed by the exact prompt sent. -/
initialize claudeCache : IO.Ref (Std.HashMap String String) ← IO.mkRef ∅

/-- Take ownership of a call site: bump its generation, and decide what becomes of
whatever the previous owner left running. Returns the new generation, and the run
this call has inherited if it inherited one.

A run for the *same* prompt is adopted rather than killed — see the module
docstring on why re-elaboration must not keep paying for the same answer — and
brings its progress with it, so the widget's clock does not restart. Anything
else is killed, and the site starts clean. -/
private def claimSite (site : String) (prompt : String) : IO (Nat × Option ClaudeRun) := do
  let now ← IO.monoMsNow
  let (gen, adopted, doomed) ← claudeRuns.modifyGet fun runs =>
    let slot := runs.getD site {}
    let gen := slot.latest + 1
    let fresh := { latest := gen, running := none, progress := { startedMs := now } }
    match slot.running with
    | some run =>
      if run.prompt == prompt then
        let run := { run with gen }
        ((gen, some run, none), runs.insert site { slot with latest := gen, running := some run })
      else ((gen, none, some run), runs.insert site fresh)
    | none => ((gen, none, none), runs.insert site fresh)
  -- The killed run's watcher is still polling and will notice; its driver reaps it.
  if let some run := doomed then killRun run.child
  -- Only now, so that the run's own reader starts labelling its lines with the
  -- generation that is going to display them.
  if let some run := adopted then run.genRef.set gen
  return (gen, adopted)

/-- The cancellation flag of the background task the call runs in.

`Core.wrapAsync` installs the token we hand `logSnapshotTask` as the context's
`cancelTk?`, and Lean sets it when it discards the snapshot the task hangs off —
including when the `claude` call is edited away, which is the one case no later
invocation is around to supersede. It is *not* the same flag as
`IO.checkCanceled`, which document edits leave untouched; we poll both, since the
task flag is what a `Task.cancel` elsewhere would set. -/
private def getCancelTk? : CoreM (Option IO.CancelToken) := return (← read).cancelTk?

/-- Has this call gone stale — either Lean gave up on the elaboration, or a newer
invocation from the same call site took over? -/
private def superseded (tk? : Option IO.CancelToken) (site : String) (gen : Nat) : IO Bool := do
  if let some tk := tk? then
    if ← tk.isSet then return true
  if ← IO.checkCanceled then return true
  let runs ← claudeRuns.get
  return runs[site]?.map (·.latest) != some gen

/-- Give up the slot, and say whether the run in it was still this call's to give
up. `false` means the run has been handed on — adopted by a newer generation,
which re-stamped its `gen` — or was killed and cleared already. -/
private def releaseSite (site : String) (gen : Nat) : IO Bool :=
  claudeRuns.modifyGet fun runs =>
    match runs[site]? with
    | some slot@{ running := some run, .. } =>
      if run.gen == gen then (true, runs.insert site { slot with running := none })
      else (false, runs)
    | _ => (false, runs)

/-- Stop watching a run that has gone stale, killing it only if it is still ours.
A newer generation that adopted it is watching it now, and one that did not
killed it in `claimSite`; the case left is a call Lean cancelled outright, where
there is no later invocation to decide and the process would otherwise run on. -/
private def relinquish (site : String) (run : ClaudeRun) : IO Unit := do
  if ← releaseSite site run.gen then killRun run.child

/-- Record something about the call in flight, unless a newer generation has taken
the site over — in which case the widget showing it is gone too. -/
private def setProgress (site : String) (gen : Nat) (f : ClaudeProgress → ClaudeProgress) :
    IO Unit :=
  claudeRuns.modify fun runs =>
    match runs[site]? with
    | some slot =>
      if slot.latest == gen then runs.insert site { slot with progress := f slot.progress } else runs
    | none => runs

/-- How many activity lines the widget keeps. Enough to see what Claude has been
reading, few enough that the message does not grow without bound. -/
private def maxActivity : Nat := 6

/-- Add a line to the activity list, dropping the oldest once it is full. -/
private def noteActivity (site : String) (gen : Nat) (line : String) : IO Unit :=
  setProgress site gen fun p =>
    let a := p.activity.push line
    { p with activity := if a.size ≤ maxActivity then a else a.extract (a.size - maxActivity) a.size }

/-- Stop the widget's clock and its polling. -/
private def finishProgress (site : String) (gen : Nat) (phase : String) : IO Unit := do
  let now ← IO.monoMsNow
  setProgress site gen fun p => { p with phase, finishedMs := now }

/-- Wait out the debounce in slices, watching for the call going stale.
Returns `true` if it did, in which case nothing should be spawned. -/
private def debounce (tk? : Option IO.CancelToken) (site : String) (gen : Nat) (ms : Nat) :
    IO Bool := do
  let mut waited := 0
  while waited < ms do
    if ← superseded tk? site gen then return true
    IO.sleep (min 50 (ms - waited)).toUInt32
    waited := waited + 50
  superseded tk? site gen

/-! ## Reading the CLI's event stream -/

private def trim (s : String) : String := s.trimAscii.toString

/-- A string field of a JSON object, or `none` if it is absent or not a string.
Every event field is read this way: the stream is parsed for display, so a shape
that has moved on should cost an activity line, not the answer. -/
private def jsonStr? (j : Json) (key : String) : Option String :=
  (j.getObjVal? key >>= (·.getStr?)).toOption

/-- A numeric field of a JSON object, as a `Nat`. -/
private def jsonNat? (j : Json) (key : String) : Option Nat :=
  (j.getObjVal? key >>= (·.getNum?)).toOption.map (·.toFloat.toUInt64.toNat)

/-- Text as it fits on one line of a proof: the first line, truncated. -/
private def oneLine (s : String) (width : Nat := 80) : String :=
  let s := trim ((s.splitOn "\n").headD s)
  if s.length ≤ width then s else (s.take width).toString ++ "…"

/-- A path as it is worth showing: the last two components, so that an absolute
`…/SpLean/Algebraic/Rules/EulerDecomp.lean` reads as `Rules/EulerDecomp.lean`
rather than pushing everything else off the line. -/
private def abbrevPath (path : String) : String :=
  let parts := path.splitOn "/"
  if parts.length ≤ 2 then path
  else String.intercalate "/" (parts.drop (parts.length - 2))

/-- One content block of an assistant message as a line of activity: what Claude
said, or which tool it reached for and on what. -/
private def blockActivity (b : Json) : Option String :=
  match jsonStr? b "type" with
  | some "text" =>
    let t := oneLine ((jsonStr? b "text").getD "")
    if t.isEmpty then none else some t
  | some "tool_use" =>
    let name := (jsonStr? b "name").getD "tool"
    let input := (b.getObjVal? "input").toOption.getD Json.null
    match ["file_path", "pattern", "path"].findSome? (jsonStr? input) with
    | some arg => some (oneLine s!"{name} {abbrevPath arg}")
    | none => some name
  | _ => none

/-- What an event is worth showing, if anything. The stream also carries hook,
rate-limit and tool-result events, which say nothing a proof line wants. -/
private def eventActivity (j : Json) : Option String := do
  guard (jsonStr? j "type" == some "assistant")
  let content ← (j.getObjVal? "message" >>= (·.getObjVal? "content") >>= (·.getArr?)).toOption
  let lines := content.filterMap blockActivity
  guard !lines.isEmpty
  return String.intercalate " · " lines.toList

/-- The assistant's own words in an event, untruncated: the answer to fall back on
if the run's `result` event never arrives. -/
private def assistantText (j : Json) : Array String :=
  match (j.getObjVal? "message" >>= (·.getObjVal? "content") >>= (·.getArr?)).toOption with
  | some blocks =>
    blocks.filterMap fun b => if jsonStr? b "type" == some "text" then jsonStr? b "text" else none
  | none => #[]

/-- The run's `total_cost_usd`, to the cent. -/
private def formatUsd (j : Json) : Option String := do
  let n ← (j.getObjVal? "total_cost_usd" >>= (·.getNum?)).toOption
  let cents := (n.toFloat * 100.0 + 0.5).toUInt64.toNat
  let pad := if cents % 100 < 10 then "0" else ""
  return s!"${cents / 100}.{pad}{cents % 100}"

/-- What the stream is read *for*, as opposed to what it shows on the way. -/
private structure ClaudeOutput where
  /-- The `result` event's answer, once it arrives. -/
  answer : Option String := none
  /-- Every assistant text block, in case no `result` event ever does. -/
  text : Array String := #[]
  /-- Turns and cost, for the widget's finished line. -/
  summary : String := ""
  deriving Inhabited

/-- Read stdout to EOF, one `stream-json` event per line, folding each into the
call's progress as it goes; the last event carries the answer.

Lines that do not parse, or that carry a type this does not know, are skipped —
they are only ever wanted for display, and EOF here means the CLI has exited or
been killed. -/
private def readEvents (h : IO.FS.Handle) (site : String) (genRef : IO.Ref Nat)
    (out : IO.Ref ClaudeOutput) : IO Unit := do
  repeat
    let line ← h.getLine
    if line.isEmpty then break
    let .ok j := Json.parse line | continue
    if jsonStr? j "type" == some "result" then
      let summary := String.intercalate " · " <|
        ((jsonNat? j "num_turns").map (s!"{·} turns")).toList ++ (formatUsd j).toList
      out.modify fun o => { o with answer := jsonStr? j "result", summary }
    else
      if let some act := eventActivity j then noteActivity site (← genRef.get) act
      let said := assistantText j
      unless said.isEmpty do out.modify fun o => { o with text := o.text ++ said }

/-- What a finished run produced: the answer, and the widget's summary line.
Throws if the CLI failed — whether that failure is worth *reporting* is not
decided here, since a killed run exits nonzero too. -/
private def runOutcome (exitCode : UInt32) (out : IO.Ref ClaudeOutput)
    (stdout : Task (Except IO.Error Unit)) (stderr : Task (Except IO.Error String)) :
    IO (String × String) := do
  if exitCode != 0 then
    throw <| IO.userError s!"`claude` exited with code {exitCode}:\n{← IO.ofExcept stderr.get}"
  -- Raise what the reader itself choked on, rather than reporting an empty answer.
  IO.ofExcept stdout.get
  let o ← out.get
  -- No `result` event is not on its own a failure: everything Claude said is
  -- still there, and is a better answer than an error about the stream's shape.
  let fallback := if o.text.isEmpty then none else some (String.intercalate "\n" o.text.toList)
  let some response := o.answer <|> fallback
    | throw <| IO.userError "`claude` produced no answer."
  return (response, o.summary)

/-- Drive one run to completion: drain both of its pipes, folding the events into
the owning call's progress as they arrive, and leave the answer or the failure in
`run.done`.

A task of its own, and the only thing that ever waits on the child, so the run is
reaped exactly once however many watchers come and go over its life. It is never
cancelled: the run belongs to the call site, and stopping it means killing the
process, which arrives here as the child exiting like any other ending. -/
private def driveRun (site : String) (run : ClaudeRun) : IO Unit := do
  -- Drain both pipes concurrently: a full pipe would block the child forever.
  -- stdout goes a line at a time rather than to the end, because each line is an
  -- event the widget wants *while* the CLI is still running.
  let out ← IO.mkRef {}
  let stdout ← IO.asTask (readEvents run.child.stdout site run.genRef out) Task.Priority.dedicated
  let stderr ← IO.asTask run.child.stderr.readToEnd Task.Priority.dedicated
  let exitCode ← run.child.wait
  run.done.set (some (← (runOutcome exitCode out stdout stderr).toBaseIO))

/-- Spawn a run for this call site and set its driver going.

Registering it in the slot is what makes it adoptable — and what makes it
killable, so a site that moved on between the spawn and the registration leaves
nobody to do either, and the run is killed here instead. -/
private def startRun (site : String) (gen : Nat) (prompt : String) : IO ClaudeRun := do
  let child ← spawnClaude site prompt
  let run : ClaudeRun := { gen, prompt, child, genRef := ← IO.mkRef gen, done := ← IO.mkRef none }
  discard <| IO.asTask (driveRun site run) Task.Priority.dedicated
  let registered ← claudeRuns.modifyGet fun runs =>
    let slot := runs.getD site {}
    if slot.latest == gen then (true, runs.insert site { slot with running := some run })
    else (false, runs)
  unless registered do killRun child
  setProgress site gen ({ · with phase := "running" })
  return run

/-- Watch a run — the one this call adopted, or a fresh one — to its answer,
killing it if the call goes stale meanwhile. `none` means it did: the answer is
no longer wanted, so there is nothing to report. -/
private def watchRun (tk? : Option IO.CancelToken) (site : String) (gen : Nat)
    (prompt : String) (adopted : Option ClaudeRun) : IO (Option String) := do
  let run ← match adopted with
    | some run => pure run
    | none => startRun site gen prompt
  let mut outcome : Option (Except IO.Error (String × String)) := none
  repeat
    -- Staleness is checked *before* the outcome, so that a run killed out from
    -- under us is reported as superseded rather than as a CLI failure.
    if ← superseded tk? site gen then
      relinquish site run
      return none
    if let some o ← run.done.get then
      outcome := some o
      break
    IO.sleep 100
  discard <| releaseSite site gen
  -- A kill landing between the staleness check and the run ending surfaces there
  -- as a nonzero exit (SIGKILL, 137), so ask again before blaming the CLI for it.
  if ← superseded tk? site gen then return none
  match outcome with
  | none => return none
  | some (.error e) =>
    finishProgress site gen "failed"
    throw e
  | some (.ok (response, summary)) =>
    setProgress site gen fun p => { p with summary }
    finishProgress site gen "done"
    return some response

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

/-- Assemble the prompt: the standing instructions, where the call sits, the
user's message if they gave one, and the proof state.

It reaches the CLI as a single argument, by way of the environment (see
`watchdogScript`), so nothing here has to be shell-safe — but it does have to
fit. Arguments and environment strings are bounded at `execve`, and a prompt over
that bound fails the spawn rather than the run, surfacing as "Could not run the
`claude` CLI". Only the proof state grows, and one large enough to hit the bound
is past the size an answer would help with; anything wanting to paste whole
*files* in here would need a way to send them that is not argv. -/
private def buildPrompt (site : String) (msg : Option String) : TacticM String := do
  let mut prompt := s!"Called at {site}.\n\n"
  prompt := prompt ++ claudeInstructions
  if let some m := msg then
    prompt := prompt ++ s!"\n\nThe user says: {m}"
  return prompt ++ s!"\n\nProof state:\n\n{← ppProofState}"

/-! ## Reporting the answer -/

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

/-- Offer the tactic block as a "Try this" suggestion and log the prose under it.

`ref` is passed rather than read, because this also runs from the background
task, whose messages have to land back on the `claude` line. -/
private def report (ref : Syntax) (response : String) : CoreM Unit := do
  let (code?, prose) := splitResponse response
  if let some code := code? then
    addSuggestion ref (code : SuggestionText) (header := "Claude suggests: ")
  unless prose.isEmpty do logInfoAt ref prose

/-! ## Saying that it is running -/

/-- What the progress widget is handed on each poll. Everything is preformatted:
the widget draws strings and a spinner, and makes no decisions of its own. -/
structure ClaudeStatus where
  /-- `waiting`, `running`, `done`, `failed`, or `gone` for a call this server no
  longer has — a restart, or a newer call taking the site over. -/
  phase : String
  /-- How long the call has been going, already rounded for display. -/
  elapsed : String
  /-- The last few things Claude said it was doing, oldest first. -/
  activity : Array String := #[]
  /-- Turns and cost, once the run has finished. -/
  summary : String := ""
  deriving ToJson, FromJson, Inhabited

/-- Which run the widget is asking about. -/
structure ClaudeStatusParams where
  /-- `file:line:column` of the `claude` token whose run this is. -/
  site : String
  /-- Which run at that site. A later one makes this widget's run `gone`. -/
  gen : Nat
  deriving ToJson, FromJson

/-- Milliseconds as the widget shows them: one decimal, which is enough to see
that something is moving without the digits flickering. -/
private def formatSecs (ms : Nat) : String := s!"{ms / 1000}.{(ms % 1000) / 100}s"

private def goneStatus : ClaudeStatus := { phase := "gone", elapsed := "" }

/-- The live state of one call, for the widget on its line. -/
@[server_rpc_method]
def claudeStatus (p : ClaudeStatusParams) : RequestM (RequestTask ClaudeStatus) :=
  RequestM.asTask do
    let runs ← claudeRuns.get
    let some slot := runs[p.site]? | return goneStatus
    if slot.latest != p.gen then return goneStatus
    let now ← IO.monoMsNow
    let pr := slot.progress
    return {
      phase := pr.phase
      elapsed := formatSecs ((pr.finishedMs.getD now) - pr.startedMs)
      activity := pr.activity
      summary := pr.summary
    }

/-- The spinner-and-activity line the `claude` tactic leaves on its own line.

A message widget rather than anything the tactic prints, because everything it
shows arrives after the elaboration that logged it: the component polls
`SpLean.claudeStatus` for the call site in its props and redraws itself, which is
the only way live output reaches a line Lean has finished elaborating. It stops
polling the moment the run reaches a terminal phase, and renders nothing at all
for a run the server has forgotten. -/
@[widget_module]
def claudeProgressWidget : Widget.Module where
  javascript := "
import * as React from 'react'
import { RpcContext } from '@leanprover/infoview'

const e = React.createElement
const FRAMES = ['⠋', '⠙', '⠹', '⠸', '⠼', '⠴', '⠦', '⠧', '⠇', '⠏']
const running = s => s.phase === 'waiting' || s.phase === 'running'

export default function (props) {
  const rs = React.useContext(RpcContext)
  const [st, setSt] = React.useState(null)
  const [tick, setTick] = React.useState(0)

  // Poll until the run stops; a failed call just stops showing anything.
  React.useEffect(() => {
    let live = true
    let timer = null
    const poll = () => {
      rs.call('SpLean.claudeStatus', { site: props.site, gen: props.gen })
        .then(s => {
          if (!live) return
          setSt(s)
          if (running(s)) timer = setTimeout(poll, 400)
        })
        .catch(() => { if (live) setSt(null) })
    }
    poll()
    return () => { live = false; if (timer) clearTimeout(timer) }
  }, [props.site, props.gen])

  // The spinner turns between polls, so the line never looks frozen.
  React.useEffect(() => {
    if (!st || !running(st)) return
    const id = setInterval(() => setTick(t => t + 1), 100)
    return () => clearInterval(id)
  }, [st === null, st && st.phase])

  if (!st || st.phase === 'gone') return null

  const icon = running(st) ? FRAMES[tick % FRAMES.length] : st.phase === 'failed' ? '✗' : '✓'
  const head =
    st.phase === 'waiting' ? 'Claude queued' :
    st.phase === 'running' ? 'Claude is thinking' :
    st.phase === 'failed' ? 'Claude failed' : 'Claude answered'
  const parts = [icon + ' ' + head, st.elapsed]
  if (st.summary) parts.push(st.summary)

  const rows = st.activity.map((a, i) => e('div', {
    key: i,
    style: {
      opacity: i === st.activity.length - 1 ? 0.95 : 0.55,
      overflow: 'hidden',
      textOverflow: 'ellipsis',
      whiteSpace: 'nowrap'
    }
  }, a))

  return e('div', { className: 'font-code' },
    e('div', null, parts.join(' · ')),
    running(st) && rows.length > 0 ? e('div', { style: { paddingLeft: '2ch' } }, rows) : null)
}"

/-- The message the tactic logs on its own line while a call is in flight. -/
private def progressMessage (site : String) (gen : Nat) : MessageData :=
  .ofWidget
    { id := ``claudeProgressWidget
      javascriptHash := claudeProgressWidget.javascriptHash.1
      props := return json% { site: $site, gen: $gen } }
    "Claude is thinking…"

/-! ## The tactic -/

/-- Ask the Claude Code CLI what to do with the current proof state.

    claude
    claude "the RHS is the one I can't get to"

Logs only; the goal is left exactly as it was. The call is debounced by
`splean.claude.debounce` milliseconds and superseded by any later call from the
same line, so typing does not start a pile of CLI processes. Waiting for the
answer happens in a background task, so elaboration is not held up by it. -/
elab (name := claudeTactic) "claude" msg:(str)? : tactic => withMainContext do
  let ref ← getRef
  let site ← callSite
  let prompt ← buildPrompt site (msg.map (·.getString))
  -- Claim first even when the answer turns out to be cached: an in-flight run
  -- from an earlier version of this line is stale either way. Whether that means
  -- killing it or taking it over is `claimSite`'s to decide.
  let (gen, adopted) ← claimSite site prompt
  if let some cached := (← claudeCache.get)[prompt]? then
    -- Only reachable if the run cached its answer between the claim and this
    -- read, in which case it has nothing left to tell us.
    if let some run := adopted then relinquish site run
    report ref cached
    return
  let debounceMs := splean.claude.debounce.get (← getOptions)
  -- Nothing else will appear on this line until the answer does, which reads
  -- exactly like a tactic that did nothing. This widget is what says otherwise.
  logInfoAt ref (progressMessage site gen)
  -- Everything from here on waits on the CLI, so it runs off the elaboration
  -- thread. The token is how Lean tells the task its answer is no longer wanted.
  let cancelTk ← IO.CancelToken.new
  let ask ← Term.wrapAsyncAsSnapshot (cancelTk? := some cancelTk) (desc := "SpLean.claude")
    fun (_ : Unit) => do
      let tk? ← getCancelTk?
      -- The debounce exists to stop keystrokes *spawning* processes. An adopted
      -- run is already spawned, and already on its way to an answer.
      if adopted.isNone then
        if ← debounce tk? site gen debounceMs then return
      let response? ←
        try watchRun tk? site gen prompt adopted
        catch e =>
          finishProgress site gen "failed"
          throwError "Could not run the `claude` CLI: {e.toMessageData}"
      let some response := response? | return
      claudeCache.modify (·.insert prompt response)
      report ref response
  -- `.dedicated`: the task spends its life asleep, and must not sit on one of
  -- the pool's threads while it does.
  let task ← BaseIO.asTask (ask ()) Task.Priority.dedicated
  Core.logSnapshotTask { stx? := ref, cancelTk? := cancelTk, task }

-- `claude` deliberately leaves the goal untouched, so the unused-tactic linter
-- would flag every use. The `!` carries the exemption into importing files.
#allow_unused_tactic! SpLean.claudeTactic

end SpLean
