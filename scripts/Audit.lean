module

public meta import Lean.Elab.Command
public meta import Lean.DocString
-- One `import all` line per module of the libraries, so that proofs are visible to the dependency
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find Basic External Pedregal Sverak Cassese -name '*.lean' ! -name Challenge.lean | sort |
--     sed 's/\.lean$//; s#/#.#g; s/^/import all /'
-- Every paper's Solution is imported, and no Challenge: a Challenge holds a copy of its paper's
-- definitions under the library's names.
import all Basic.LinearAlgebra.Matrix.RankTwo
import all Cassese.Bridges
import all Cassese.Defs
import all Cassese.Sverak
import all External.Kakutani.Theorem
import all Pedregal.Checks
import all Pedregal.Defs
import all Pedregal.Hn.Laminate
import all Pedregal.Hn.Mold
import all Pedregal.Introduction
import all Pedregal.LevelOne
import all Pedregal.Map
import all Pedregal.MoldTau
import all Pedregal.NonEmptiness.Counterexample
import all Pedregal.NonEmptiness.Statements
import all Pedregal.Reduction
import all Pedregal.Solution
import all Pedregal.Triangulation
import all Pedregal.Weights
import all Sverak.Construction
import all Sverak.Cube
import all Sverak.Defs
import all Sverak.Lemma1
import all Sverak.Lemma2
import all Sverak.Solution
import all Sverak.Theorem

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For every numbered result of the paper, this prints the axioms it depends on and the results from
prior work (`External/`) that it uses, whether proved there or, in a conditional
formalization, assumed as hypotheses of its statement. It then checks every declaration
of the library and the theorems that Palomar's comparator checks. The run fails if any of them
depends on an axiom other than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a
`sorry` shows up as the axiom `sorryAx`). Its table of results is the source of the report's
dependency table.

It also writes the *route* of every numbered result to `.lake/route_deps.tsv`: the other
numbered results that its proof uses, found by following the proof through the library's helper
lemmas and stopping at numbered results, together with the TeX label that the result's docstring
names in backticks. `route_check.py` (in the skill's `scripts/`) compares these routes with the
results that the paper's proofs cite.

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise. The traversal tests membership in a
precomputed set of the library's constants; looking up each constant's module instead
(`Environment.getModuleIdxFor?`) makes the interpreted script take minutes.

To adapt: generate the `import all` lines, fill in the three lists, and set the libraries' root
names in `isLibraryModule`: the paper's library, `External`, the results it cites, and `Basic`,
the library of general mathematics.
Keep one `import all` line per module of the libraries, each on its own line: a module that is
missing is still imported through the others, but without its proofs, and the audit then misses the
axioms and the routes inside them. The CI template checks the list.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work, with a short label: the theorems proved in `External/`
or, when general, in `Basic/`, and, in a conditional formalization, the propositions assumed as
hypotheses. The traversal
stops at them. -/
meta def externalResults : List (String × Name) :=
  [("Kakutani's fixed-point theorem (Thm 6.2)", ``External.Kakutani.exists_fixedPoint)]

/-- The numbered results of the paper, in the order of the paper. -/
meta def paperResults : List (String × Name) :=
  [("Prop 3.3", ``Pedregal.proposition3_3),
   ("Def 5.1 (assertions)", ``Pedregal.theta_nonempty),
   ("Def 5.1 (assertions)", ``Pedregal.convex_theta),
   ("Def 5.1 (assertions)", ``Pedregal.isCompact_theta),
   ("Def 5.1 (assertions)", ``Pedregal.theta_subset_simplex),
   ("Eq. (5.13)", ``Pedregal.equation5_13),
   ("Eq. (5.15)", ``Pedregal.equation5_15),
   ("Prop 6.1", ``Pedregal.proposition6_1),
   ("Thm 6.2 (Kakutani, cited)", ``External.Kakutani.exists_fixedPoint),
   ("Subsection 6.1", ``Pedregal.section6_1_isClosed_graph),
   ("Subsection 6.1", ``Pedregal.section6_1_isCompact),
   ("Subsection 6.1", ``Pedregal.section6_1_usc),
   ("Prop 6.3 (1)", ``Pedregal.proposition6_3_point),
   ("Prop 6.3 (1)", ``Pedregal.proposition6_3_dir),
   ("Prop 6.3 (2)", ``Pedregal.proposition6_3),
   ("Prop 7.1 (false)", ``Pedregal.proposition7_1_false),
   ("Cor 7.2 (false)", ``Pedregal.corollary7_2_false),
   ("Cor 7.2 from Prop 7.1", ``Pedregal.corollary7_2_of_proposition7_1),
   ("Step 2 summary (false)", ``Pedregal.step2Claim_false),
   ("Claim 7.4", ``Pedregal.claim7_4),
   ("Thm 1.1 (1), up to Cor 7.2", ``Pedregal.theorem1_1_of_nonempty),
   ("Thm 1.1 (1), l = 1", ``Pedregal.theorem1_1_part1_levelOne),
   ("Šverák Lemma 1", ``Sverak.lemma1),
   ("Šverák Lemma 1 (limit)", ``Sverak.lemma1_limit),
   ("Šverák Lemma 1 (witness)", ``Sverak.lemma1_witness),
   ("Šverák rank-one directions of L", ``Sverak.rank_ofRST_eq_one),
   ("Šverák f affine on rank-one lines of L", ``Sverak.sverakf_affine_of_rankOne),
   ("Šverák (4)", ``Sverak.equation4),
   ("Šverák (6)", ``Sverak.equation6),
   ("Šverák (7)", ``Sverak.equation7),
   ("Šverák (*)", ``Sverak.equation_star),
   ("Šverák (8)", ``Sverak.equation8),
   ("Šverák Lemma 2", ``Sverak.lemma2),
   ("Šverák (10)", ``Sverak.equation10),
   ("Šverák (11)", ``Sverak.equation11),
   ("Šverák Theorem", ``Sverak.theorem_main),
   ("Šverák Remark", ``Sverak.remark_polynomial),
   ("Šverák Corollary", ``Sverak.corollary),
   ("Cassese Section 1.1 (Šverák's example)", ``Cassese.sverak_example)]

/-- The theorems that Palomar's comparator checks (`theorem_names` of `comparator.json`). -/
meta def solutionResults : List Name :=
  [``PedregalChallenge.corollary7_2_false, ``PedregalChallenge.exists_T_eq_empty,
   ``PedregalChallenge.theorem1_1_of_nonempty, ``PedregalChallenge.theorem1_1_part1_levelOne,
   ``PedregalChallenge.mem_T_self,
   ``PedregalChallenge.card_C,
   ``SverakChallenge.theorem_main, ``SverakChallenge.corollary,
   ``SverakChallenge.remark_polynomial]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the libraries: the papers', `External` or `Basic`. -/
meta def isLibraryModule (m : Name) : Bool :=
  (`Pedregal).isPrefixOf m || (`Sverak).isPrefixOf m || (`Cassese).isPrefixOf m ||
    (`External).isPrefixOf m || (`Basic).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.insert c
  return s

/-- The constants used by the type and the value of `c`. -/
meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The external results reached from `root` through constants of the library, without looking
inside the proofs of the external results themselves. `deps` caches the constants of the library
that each constant uses, across calls. -/
meta def externalUses (env : Environment) (library : NameSet) (deps : NameMap (Array Name))
    (root : Name) :
    List Name × NameMap (Array Name) := Id.run do
  let externals := externalResults.map (·.2)
  let mut deps := deps
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut found : NameSet := {}
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      if c != root && externals.contains c then
        found := found.insert c
        continue
      let ds := match deps.find? c with
        | some ds => ds
        | none => (usedConstants env c).filter library.contains
      deps := deps.insert c ds
      for d in ds do
        if !visited.contains d then stack := d :: stack
  return (externalResults.filterMap fun (_, n) => if found.contains n then some n else none, deps)

/-- Where `#audit` writes the routes, relative to the project root (`.lake/` is not committed). -/
meta def routeFile : System.FilePath := ".lake/route_deps.tsv"

/-- The numbered results that the proof of `root` uses: those reached from it through constants
of the library, without looking inside the proofs of numbered results themselves. -/
meta def resultUses (env : Environment) (library results : NameSet) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := (usedConstants env root).toList
  let mut found : Array Name := #[]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c || c == root then continue
      visited := visited.insert c
      if results.contains c then
        found := found.push c
        continue
      if !library.contains c then continue
      for d in usedConstants env c do
        if !visited.contains d then stack := d :: stack
  return found

/-- The code spans of the docstring of `c` that contain no space or comma: the candidates for its
TeX label. -/
meta def docLabels (env : Environment) (c : Name) : IO (Array String) := do
  let some doc ← findDocString? env c | return #[]
  let mut out : Array String := #[]
  let mut inside := false
  for part in doc.splitOn "`" do
    if inside && !part.isEmpty && !part.any (fun ch => ch.isWhitespace || ch == ',') then
      out := out.push part
    inside := !inside
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    let (uses, deps') := externalUses env library deps n
    deps := deps'
    let usesStr := if uses.isEmpty then "–" else ", ".intercalate (uses.map fun u => s!"`{u}`")
    let axStr := ", ".intercalate (axs.toList.map toString)
    rows := rows.push s!"| {label} | `{n}` | {usesStr} | {axStr} |"
  for n in solutionResults ++ externalResults.map (·.2) do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
  -- Every declaration of the library, including private and auxiliary ones.
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  -- The routes: for each numbered result, its docstring's labels and the results it uses.
  let results : NameSet := paperResults.foldl (fun s p => s.insert p.2) {}
  let mut routes : Array String := #[]
  for (label, n) in paperResults do
    let labels ← docLabels env n
    let uses := resultUses env library results n
    routes := routes.push (s!"{label}\t{n}\t{",".intercalate labels.toList}\t" ++
      ",".intercalate (uses.map toString).toList)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile routeFile ("\n".intercalate routes.toList ++ "\n")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
