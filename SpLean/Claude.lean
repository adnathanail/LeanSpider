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

Two things worth knowing:

* elaboration *blocks* on the CLI call, so the file's InfoView is stuck for as
  long as Claude takes to answer;
* Lean re-elaborates a file on every edit, which would re-run the CLI (and cost
  money) on every keystroke, so answers are cached per prompt in `claudeCache`
  for the lifetime of the language server. Editing the message or the goal is a
  new prompt and so a new call; restarting the server forgets everything.
-/

open Lean Elab Tactic Meta Meta.Tactic.TryThis

namespace SpLean

/-- Answers already received, keyed by the exact prompt sent.

Lives for as long as the language server process: it is what stops an idle
`claude` line in an open file calling the CLI again on every re-elaboration. -/
initialize claudeCache : IO.Ref (Std.HashMap String String) ← IO.mkRef ∅

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

/-- Assemble the prompt: instructions, where in the source the tactic sits, the
user's message if they gave one, and the proof state. -/
private def buildPrompt (msg : Option String) : TacticM String := do
  let fileName ← getFileName
  let fileMap ← getFileMap
  let mut prompt := claudeInstructions
  match (← getRef).getPos?.map fileMap.toPosition with
  | some p => prompt := prompt ++ s!"\n\nCalled at {fileName}:{p.line}."
  | none   => prompt := prompt ++ s!"\n\nCalled in {fileName}."
  if let some m := msg then
    prompt := prompt ++ s!"\n\nThe user says: {m}"
  return prompt ++ s!"\n\nProof state:\n\n{← ppProofState}"

/-- Run the CLI headlessly and return its stdout. -/
private def runClaudeCLI (prompt : String) : IO String := do
  let out ← IO.Process.output {
    cmd := "claude"
    args := #["-p", prompt, "--output-format", "text", "--allowedTools", "Read,Grep,Glob"]
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"`claude` exited with code {out.exitCode}:\n{out.stderr}"
  return out.stdout

/-- Split an answer into its first fenced code block and the prose around it.

The text between the opening fence and the first newline is the fence's info
string (`lean`), not code, so it is dropped. Anything after the closing fence is
glued back onto the prose, further fences and all. -/
private def trim (s : String) : String := s.trimAscii.toString

private def splitResponse (response : String) : Option String × String :=
  match response.splitOn "```" with
  | pre :: block :: rest =>
    let code := trim (String.intercalate "\n" ((block.splitOn "\n").drop 1))
    if code.isEmpty then (none, trim response)
    else (some code, trim (trim pre ++ "\n\n" ++ trim (String.intercalate "```" rest)))
  | _ => (none, trim response)

/-- Ask the Claude Code CLI what to do with the current proof state.

    claude
    claude "the RHS is the one I can't get to"

Logs only; the goal is left exactly as it was. -/
elab (name := claudeTactic) "claude" msg:(str)? : tactic => withMainContext do
  let prompt ← buildPrompt (msg.map (·.getString))
  let response ← match (← claudeCache.get)[prompt]? with
    | some cached => pure cached
    | none => do
      let r ←
        try runClaudeCLI prompt
        catch e => throwError "Could not run the `claude` CLI: {e.toMessageData}"
      claudeCache.modify (·.insert prompt r)
      pure r
  let (code?, prose) := splitResponse response
  if let some code := code? then
    addSuggestion (← getRef) (code : SuggestionText) (header := "Claude suggests: ")
  unless prose.isEmpty do logInfo prose

-- `claude` deliberately leaves the goal untouched, so the unused-tactic linter
-- would flag every use. The `!` carries the exemption into importing files.
#allow_unused_tactic! SpLean.claudeTactic

end SpLean
