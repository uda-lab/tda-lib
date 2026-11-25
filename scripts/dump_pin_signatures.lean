/-
Advisory helper for `scripts/check-released-signatures.sh` (#1154 check 3): prints one line
`name<TAB>type hash<TAB>pretty-printed type` for every declaration pinned in
`scripts/print_axioms/*.lean` of the current directory, read from the elaborated environment
produced by `lake build`. The script runs it in a worktree of the last release tag and in the
checkout, then compares the two dumps. Nothing here is a gate; no statement is read or altered.
Run via `scripts/lean.sh lake env lean <path to this file>` from the root of the tree to dump.
-/
import TDA

open Lean Meta System

/-- Names pinned by unindented `#print axioms <name>` lines, as in `scripts/check-axioms.sh`. -/
private def pinNames (dir : FilePath) : IO (Array String) := do
  let mut names : Array String := #[]
  for entry in (← dir.readDir) do
    if entry.path.extension == some "lean" then
      for line in (← IO.FS.readFile entry.path).splitOn "\n" do
        if line.startsWith "#print axioms " then
          let rest := (line.drop "#print axioms ".length).toString.replace "\t" " "
          if let some n := (rest.splitOn " ").find? (· ≠ "") then names := names.push n
  return names.qsort (· < ·)

#eval show MetaM Unit from do
  let env ← getEnv
  for n in (← pinNames "scripts/print_axioms") do
    match env.find? n.toName with
    | none => IO.println s!"{n}\t-\t<unresolved>"
    | some info =>
      let pp ← ppExpr info.type
      let flat := String.intercalate " " ((toString pp).splitOn "\n" |>.map (·.trimAscii.toString))
      IO.println s!"{n}\t{hash info.type}\t{flat}"
