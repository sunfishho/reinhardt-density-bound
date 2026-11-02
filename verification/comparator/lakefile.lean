import Lake
open Lake DSL

package ReinhardtComparator

/-- Compile the two entry modules against the recorded, existing artifacts.
The checker itself subsequently exports and rechecks the complete proof closure. -/
def buildEntry (name : String) : FetchM (Job Unit) := do
  let result ← IO.Process.output {
    cmd := "python3"
    args := #["build_entry.py", name]
  }
  IO.print result.stdout
  IO.eprint result.stderr
  if result.exitCode != 0 then
    error s!"Entry compilation failed: {name} (exit {result.exitCode})\n{result.stdout}\n{result.stderr}"
  pure (Job.pure ())

target Challenge : Unit := buildEntry "Challenge"
target Solution : Unit := buildEntry "Solution"
target ControlChallenge : Unit := buildEntry "ControlChallenge"
target ControlGood : Unit := buildEntry "ControlGood"
target ControlBadStatement : Unit := buildEntry "ControlBadStatement"
target ControlBadAxiom : Unit := buildEntry "ControlBadAxiom"
