#!/usr/bin/env python3
"""Print the elaborated types and direct expression references for selected paper-map rows."""
import argparse
import csv
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("rows", nargs="+", help="IDs in docs/paper-map.tsv, for example T1 C2 T3")
    parser.add_argument("--build", required=True, type=Path, help="completed full verification directory")
    parser.add_argument("--dependencies", required=True, type=Path, help="dependency state.json used by that build")
    parser.add_argument("--lean", help="path to the installed pinned Lean executable")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    build = args.build.resolve()
    receipt = verify.read_json(build / "receipt.json")
    if receipt.get("mode") != "full" or receipt.get("status") != "TECHNICALLY_VERIFIED":
        parser.error("--build must contain a successful full verification receipt")
    if receipt["source_sha256"] != verify.source_identity(root):
        parser.error("the source tree and full-build receipt differ")
    if receipt["dependency_state_sha256"] != verify.sha(args.dependencies):
        parser.error("the dependency state differs from the full-build receipt")
    with (root / "docs/paper-map.tsv").open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
        mapping = {row["id"]:row for row in rows}
        if len(mapping) != len(rows):
            parser.error("duplicate ID in correspondence table")
    names = []
    owners = set()
    owner_for = {}
    edges = []
    modules = verify.load_modules(root)
    paths = {record["path"]:name for name, record in modules.items()}
    for selected in args.rows:
        if selected not in mapping:
            parser.error("unknown paper-map ID " + selected)
        row = mapping[selected]
        if not row["lean_declarations"]:
            print(f"{selected}: {row['coverage']}. {row['scope']}", file=sys.stderr)
            continue
        declarations = row["lean_declarations"].split(";")
        locations = row["lean_sources"].split(";")
        if len(declarations) != len(locations):
            parser.error("each declaration requires one source path in " + selected)
        for name, location in zip(declarations, locations, strict=True):
            if not all(re.fullmatch(r"[^\W\d]\w*'*", part) for part in name.split(".")):
                parser.error("invalid declaration name in correspondence table")
            if location not in paths:
                parser.error("unknown source module in correspondence table: " + location)
            owners.add(paths[location])
            if owner_for.setdefault(name, paths[location]) != paths[location]:
                parser.error("conflicting source paths for " + name)
            if name not in names:
                names.append(name)
        for entry in filter(None, row.get("key_dependencies", "").split(";")):
            parts = entry.split("|")
            if len(parts) != 3 or parts[0] not in {"value", "type"} or parts[1] not in declarations:
                parser.error("invalid direct dependency in " + selected)
            edges.append(parts)
    if not names:
        return 0
    paths, _ = verify.dependency_paths(args.dependencies, root)
    own = build / "lib/lean"
    compiled = {row["module"]:row for row in receipt["compiled_modules"]}
    if compiled.keys() != modules.keys():
        parser.error("full-build module inventory differs from the source inventory")
    for name, row in compiled.items():
        obj = own / (name.replace(".", "/") + ".olean")
        if row["source_sha256"] != modules[name]["sha256"] or verify.sha(obj) != row["olean_sha256"]:
            parser.error("changed source or compiled module: " + name)
    lean = verify.find_lean(root, args.lean)
    version = subprocess.check_output([lean, "--version"], text=True).strip()
    verify.validate_lean_version(version)
    if version != receipt["lean_version"]:
        parser.error("Lean version differs from the full-build receipt")
    # Encode names as string literals. Each was validated against the table and mapped to an owner.
    name_list = ", ".join(json.dumps(n) for n in names)
    imports = "".join(f"import {owner}\n" for owner in sorted(owners))
    program = imports + """import Lean
set_option maxHeartbeats 0
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
set_option pp.maxSteps 100000000
open Lean Elab Command
run_elab do
  let env ← getEnv
  let names : List String := [NAMES]
  for text in names do
    let n := text.toName
    let some ci := env.find? n | throwError "Missing declaration {n}"
    let some idx := env.getModuleIdxFor? n | throwError "No defining module for {n}"
    let owner := env.header.moduleNames[idx.toNat]!
    let full := (← Meta.ppExpr ci.type).pretty 160
    if full.contains '⋯' || full.contains '…' then throwError "Abbreviated type {n}"
    let refs (e : Expr) := (e.getUsedConstants.toList.map toString).mergeSort
    let row := Json.mkObj [("name", toJson text), ("module", toJson owner.toString), ("type", toJson full),
      ("universes", toJson (ci.levelParams.map toString)), ("direct_type_dependencies", toJson (refs ci.type)),
      ("direct_value_dependencies", toJson ((ci.value? (allowOpaque := true)).map refs))]
    logInfo m!"PAPER_ROW_TYPE\\t{row.compress}"
""".replace("NAMES", name_list)
    with tempfile.TemporaryDirectory(prefix="lean-paper-types-") as scratch:
        tmp = Path(scratch)
        (tmp / "home").mkdir()
        driver = tmp / "InspectPaperRow.lean"
        driver.write_text(program, encoding="utf-8")
        env = verify.clean_env(lean, tmp, [own, *paths])
        command = verify.sandbox_command([lean, "-j1", "-s65536", driver], tmp, root, env)
        result = subprocess.run(command, cwd=root, stdout=subprocess.PIPE, text=True, encoding="utf-8")
        if result.returncode:
            print(result.stdout, file=sys.stderr)
            return result.returncode
        outputs = [json.loads(line.split("PAPER_ROW_TYPE\t", 1)[1])
                   for line in result.stdout.splitlines() if "PAPER_ROW_TYPE\t" in line]
        if [record["name"] for record in outputs] != names:
            raise ValueError("incomplete Lean output")
        by_name = {row["name"]:row for row in outputs}
        for name, owner in owner_for.items():
            if by_name[name]["module"] != owner:
                raise ValueError("incorrect defining module for " + name)
        for kind, name, dependency in edges:
            if dependency not in (by_name[name][f"direct_{kind}_dependencies"] or []):
                raise ValueError(f"missing direct {kind} dependency of {name}: {dependency}")
        for record in outputs:
            print(json.dumps(record, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
