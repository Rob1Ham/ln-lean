#!/usr/bin/env python3
"""Reconcile the obligation catalog, the axiom-audit registry, and Traceability.

This checker is deterministic and offline.  It reads three source files as text:

* ``LnLean/Proofs/Obligations.lean`` -- the catalog rows and their
  ``leanTarget`` strings;
* ``LnLean/Proofs/PhaseC3/AxiomAudit.lean`` -- the ``#print axioms`` commands
  and the ``auditedTheorems`` name registry;
* ``LnLean/Proofs/Traceability.lean`` -- ``targetTable``, ``provedTable``, and
  ``provedDeclarations``.

It reports, and in ``--strict`` mode exits nonzero on:

1. catalog target occurrences and unique declaration names;
2. the names in ``#print axioms`` and in ``auditedTheorems``;
3. unique catalog targets missing from the print set or from the registry;
4. registry names with no ``#print axioms`` command (and printed names absent
   from the registry, for set equality);
5. traceability text/module equality mismatches that the transcribed tables
   permit checking: every ``provedTable`` row's target text must split into
   exactly the names of its ``provedDeclarations`` rows, in order, and the
   target's module list must equal those rows' module list.  The catalog's
   ``leanTarget`` sequence must also equal the ``targetTable`` text sequence.

The script does not run Lean, does not use the network, and does not edit any
file.  ``--report`` is the default: it prints the current counts and lists and
exits zero even when it finds a known coverage gap.  ``--strict`` is the gate
form.  ``--self-test`` runs an in-memory green fixture, mutates a copy, and
asserts that the mutation is detected; it never touches the repository files.

Do not wire this into CI until the registry/print reconciliation in
``agents/reports/wave14/W14-ASSURANCE.md`` is applied: the current tree has the
documented 72/35/42 gap and ``--strict`` therefore fails by design.
"""

from __future__ import annotations

import argparse
import dataclasses
import pathlib
import re
import sys
from collections import Counter
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

ROOT = pathlib.Path(__file__).resolve().parents[1]

CATALOG_PATH = "LnLean/Proofs/Obligations.lean"
AUDIT_PATH = "LnLean/Proofs/PhaseC3/AxiomAudit.lean"
TRACE_PATH = "LnLean/Proofs/Traceability.lean"

_CATALOG_ID_RE = re.compile(r'id\s*:=\s*"(LN-[^"]+)"')
_CATALOG_TARGET_RE = re.compile(r'leanTarget\s*:=\s*"([^"]*)"')
_CATALOG_STATUS_RE = re.compile(r'status\s*:=\s*\.([A-Za-z]+)')

_PRINT_RE = re.compile(r'^[ \t]*#print axioms[ \t]+([^\s]+)', re.MULTILINE)
_REGISTRY_NAME_RE = re.compile(r'`([^`\s,\]]+)')
_AUDITED_LENGTH_RE = re.compile(
    r'theorem\s+auditedTheorems_length\s*:\s*auditedTheorems\.length\s*=\s*(\d+)'
)

_TARGET_ENTRY_RE = re.compile(
    r'⟨\s*"([^"]*)"\s*,\s*\[([^\]]*)\]\s*⟩', re.DOTALL
)
_MODULE_RE = re.compile(r'"([^"]*)"')
_DECL_ENTRY_RE = re.compile(
    r'⟨\s*(\d+)\s*,\s*"([^"]*)"\s*,\s*"([^"]*)"\s*⟩'
)
_PROVED_ENTRY_RE = re.compile(r'⟨\s*(\d+)\s*,\s*\[([0-9,\s]*)\]\s*⟩')


def _section(text: str, start: str, ends: Sequence[str]) -> str:
    """Return the text from ``start`` up to the first following end marker."""
    begin = text.find(start)
    if begin < 0:
        return ""
    rest = text[begin + len(start):]
    cut = len(rest)
    for marker in ends:
        pos = rest.find(marker)
        if 0 <= pos < cut:
            cut = pos
    return rest[:cut]


def _split_targets(target_text: str) -> List[str]:
    return [part.strip() for part in target_text.split(";") if part.strip()]


@dataclasses.dataclass
class Catalog:
    row_ids: List[str]
    targets: List[str]
    statuses: List[str]
    occurrences: List[str]
    duplicates: Dict[str, List[str]]
    parse_errors: List[str]

    @property
    def unique_targets(self) -> List[str]:
        return sorted(set(self.occurrences))


def parse_catalog(text: str) -> Catalog:
    ids = _CATALOG_ID_RE.findall(text)
    target_strings = _CATALOG_TARGET_RE.findall(text)
    statuses = _CATALOG_STATUS_RE.findall(text)
    errors: List[str] = []
    if not (len(ids) == len(target_strings) == len(statuses)):
        errors.append(
            "catalog parse: id/target/status count mismatch "
            f"({len(ids)}/{len(target_strings)}/{len(statuses)})"
        )
    rows = min(len(ids), len(target_strings), len(statuses))
    occurrences: List[str] = []
    by_name: Dict[str, List[str]] = {}
    for i in range(rows):
        for name in _split_targets(target_strings[i]):
            occurrences.append(name)
            by_name.setdefault(name, []).append(ids[i])
    duplicates = {
        name: sorted(set(row_ids))
        for name, row_ids in by_name.items()
        if len(row_ids) > 1
    }
    return Catalog(
        row_ids=ids[:rows],
        targets=target_strings[:rows],
        statuses=statuses[:rows],
        occurrences=occurrences,
        duplicates=duplicates,
        parse_errors=errors,
    )


@dataclasses.dataclass
class Audit:
    printed: List[str]
    registry: List[str]
    declared_registry_length: Optional[int]
    parse_errors: List[str]


def parse_audit(text: str) -> Audit:
    printed = _PRINT_RE.findall(text)
    registry_text = _section(
        text, "def auditedTheorems", ["theorem auditedTheorems_length"]
    )
    registry = _REGISTRY_NAME_RE.findall(registry_text)
    length_match = _AUDITED_LENGTH_RE.search(text)
    declared = int(length_match.group(1)) if length_match else None
    errors: List[str] = []
    if not registry_text:
        errors.append("audit parse: auditedTheorems block not found")
    if declared is None:
        errors.append("audit parse: auditedTheorems_length literal not found")
    return Audit(
        printed=printed,
        registry=registry,
        declared_registry_length=declared,
        parse_errors=errors,
    )


@dataclasses.dataclass
class Traceability:
    target_texts: List[str]
    target_modules: List[List[str]]
    proved_rows: List[Tuple[int, List[int]]]
    decls: List[Tuple[int, str, str]]
    parse_errors: List[str]


def parse_traceability(text: str) -> Traceability:
    target_section = _section(
        text,
        "def targetTable",
        ["def targetTextAt", "def provedTable", "def provedDeclarations"],
    )
    proved_section = _section(
        text, "def provedTable", ["def provedDeclarations"]
    )
    decl_section = _section(
        text, "def provedDeclarations", ["def lneanModules"]
    )

    target_entries = _TARGET_ENTRY_RE.findall(target_section)
    target_texts = [entry[0] for entry in target_entries]
    target_modules = [
        _MODULE_RE.findall(entry[1]) for entry in target_entries
    ]

    proved_rows: List[Tuple[int, List[int]]] = []
    for idx_text, ids_text in _PROVED_ENTRY_RE.findall(proved_section):
        proved_rows.append(
            (int(idx_text), [int(x) for x in re.findall(r"\d+", ids_text)])
        )

    decls: List[Tuple[int, str, str]] = []
    for id_text, name, module in _DECL_ENTRY_RE.findall(decl_section):
        decls.append((int(id_text), name, module))

    errors: List[str] = []
    if not target_entries:
        errors.append("traceability parse: targetTable entries not found")
    if not proved_rows:
        errors.append("traceability parse: provedTable entries not found")
    if not decls:
        errors.append("traceability parse: provedDeclarations entries not found")
    return Traceability(
        target_texts=target_texts,
        target_modules=target_modules,
        proved_rows=proved_rows,
        decls=decls,
        parse_errors=errors,
    )


@dataclasses.dataclass
class Analysis:
    catalog: Catalog
    audit: Audit
    trace: Traceability
    catalog_missing_print: List[str]
    catalog_missing_registry: List[str]
    registry_no_print: List[str]
    print_not_registry: List[str]
    trace_catalog_text_mismatches: List[str]
    trace_text_mismatches: List[str]
    trace_module_mismatches: List[str]
    trace_structural: List[str]
    snapshot_missing_targets: List[str]
    snapshot_extra_targets: List[str]

    def strict_findings(self) -> List[str]:
        findings: List[str] = []
        findings.extend(self.catalog.parse_errors)
        findings.extend(self.audit.parse_errors)
        findings.extend(self.trace.parse_errors)

        findings.extend(
            f"catalog target missing from #print axioms: {name}"
            for name in self.catalog_missing_print
        )
        findings.extend(
            f"catalog target missing from auditedTheorems: {name}"
            for name in self.catalog_missing_registry
        )
        findings.extend(
            f"registry name has no #print axioms: {name}"
            for name in self.registry_no_print
        )
        findings.extend(
            f"printed name absent from auditedTheorems: {name}"
            for name in self.print_not_registry
        )
        findings.extend(self.trace_catalog_text_mismatches)
        findings.extend(self.trace_text_mismatches)
        findings.extend(self.trace_module_mismatches)
        findings.extend(self.trace_structural)
        findings.extend(
            f"catalog target absent from provedDeclarations: {name}"
            for name in self.snapshot_missing_targets
        )
        findings.extend(
            f"provedDeclarations name absent from catalog: {name}"
            for name in self.snapshot_extra_targets
        )

        declared = self.audit.declared_registry_length
        if declared is not None and declared != len(self.audit.registry):
            findings.append(
                "auditedTheorems_length literal mismatch: "
                f"declared {declared}, parsed {len(self.audit.registry)}"
            )
        return findings


def analyze(catalog_text: str, audit_text: str, trace_text: str) -> Analysis:
    catalog = parse_catalog(catalog_text)
    audit = parse_audit(audit_text)
    trace = parse_traceability(trace_text)

    catalog_names = set(catalog.occurrences)
    printed_names = set(audit.printed)
    registry_names = set(audit.registry)

    catalog_missing_print = sorted(catalog_names - printed_names)
    catalog_missing_registry = sorted(catalog_names - registry_names)
    registry_no_print = sorted(registry_names - printed_names)
    print_not_registry = sorted(printed_names - registry_names)

    trace_catalog_text_mismatches: List[str] = []
    catalog_target_sequence = catalog.targets
    if trace.target_texts != catalog_target_sequence:
        for i in range(max(len(trace.target_texts), len(catalog_target_sequence))):
            expected = (
                catalog_target_sequence[i]
                if i < len(catalog_target_sequence)
                else "<missing>"
            )
            actual = (
                trace.target_texts[i]
                if i < len(trace.target_texts)
                else "<missing>"
            )
            if expected != actual:
                trace_catalog_text_mismatches.append(
                    f"targetTable[{i}] text differs from catalog leanTarget"
                )

    trace_text_mismatches: List[str] = []
    trace_module_mismatches: List[str] = []
    trace_structural: List[str] = []

    decl_by_id = {decl_id: (name, module) for decl_id, name, module in trace.decls}
    if len(decl_by_id) != len(trace.decls):
        trace_structural.append("provedDeclarations has duplicate numeric ids")
    expected_ids = list(range(len(trace.decls)))
    if sorted(decl_by_id) != expected_ids:
        trace_structural.append(
            "provedDeclarations ids are not exactly 0.."
            f"{len(trace.decls) - 1}"
        )

    if len(trace.target_texts) != len(catalog.targets):
        trace_structural.append(
            "targetTable length differs from catalog row count: "
            f"{len(trace.target_texts)} vs {len(catalog.targets)}"
        )
    if len(trace.proved_rows) != sum(
        1 for status in catalog.statuses if status == "proved"
    ):
        trace_structural.append(
            "provedTable length differs from catalog proved row count: "
            f"{len(trace.proved_rows)} vs "
            f"{sum(1 for status in catalog.statuses if status == 'proved')}"
        )

    used_ids = set()
    for target_index, decl_ids in trace.proved_rows:
        if target_index >= len(trace.target_texts):
            trace_structural.append(
                f"provedTable targetIndex {target_index} out of range"
            )
            continue
        missing_ids = [i for i in decl_ids if i not in decl_by_id]
        if missing_ids:
            trace_structural.append(
                f"provedTable target {target_index} names unknown decl ids "
                f"{missing_ids}"
            )
            continue
        used_ids.update(decl_ids)
        expected_texts = _split_targets(trace.target_texts[target_index])
        actual_texts = [decl_by_id[i][0] for i in decl_ids]
        if expected_texts != actual_texts:
            trace_text_mismatches.append(
                f"provedTable target {target_index}: target text and "
                "provedDeclarations text differ"
            )
        expected_modules = trace.target_modules[target_index]
        actual_modules = [decl_by_id[i][1] for i in decl_ids]
        if expected_modules != actual_modules:
            trace_module_mismatches.append(
                f"provedTable target {target_index}: target modules and "
                "provedDeclarations modules differ"
            )

    all_ids = set(decl_by_id)
    if used_ids != all_ids:
        trace_structural.append(
            "provedTable does not use exactly the provedDeclarations ids"
        )

    snapshot_names = {name for _, name, _ in trace.decls}
    snapshot_missing_targets = sorted(catalog_names - snapshot_names)
    snapshot_extra_targets = sorted(snapshot_names - catalog_names)

    return Analysis(
        catalog=catalog,
        audit=audit,
        trace=trace,
        catalog_missing_print=catalog_missing_print,
        catalog_missing_registry=catalog_missing_registry,
        registry_no_print=registry_no_print,
        print_not_registry=print_not_registry,
        trace_catalog_text_mismatches=trace_catalog_text_mismatches,
        trace_text_mismatches=trace_text_mismatches,
        trace_module_mismatches=trace_module_mismatches,
        trace_structural=trace_structural,
        snapshot_missing_targets=snapshot_missing_targets,
        snapshot_extra_targets=snapshot_extra_targets,
    )


def _print_list(title: str, values: Iterable[str]) -> None:
    values = list(values)
    print(f"{title}: {len(values)}")
    for value in values:
        print(f"  {value}")


def render(result: Analysis) -> None:
    catalog = result.catalog
    audit = result.audit
    trace = result.trace
    status_counts = Counter(catalog.statuses)

    print("== assurance coverage report ==")
    print(f"catalog rows: {len(catalog.row_ids)}")
    print(
        "catalog statuses: "
        + ", ".join(
            f"{status}={status_counts.get(status, 0)}"
            for status in sorted(status_counts)
        )
    )
    print(f"catalog target occurrences: {len(catalog.occurrences)}")
    print(f"catalog unique target declarations: {len(catalog.unique_targets)}")
    print(f"duplicate target names: {len(catalog.duplicates)}")
    for name in sorted(catalog.duplicates):
        print(f"  {name} ({len(catalog.duplicates[name])}): "
              + ", ".join(catalog.duplicates[name]))
    print(f"#print axioms commands: {len(audit.printed)}")
    print(f"auditedTheorems registry names: {len(audit.registry)}")
    print(
        "auditedTheorems_length literal: "
        + (
            str(audit.declared_registry_length)
            if audit.declared_registry_length is not None
            else "<missing>"
        )
    )
    print(
        "traceability tables: "
        f"targetTable={len(trace.target_texts)}, "
        f"provedTable={len(trace.proved_rows)}, "
        f"provedDeclarations={len(trace.decls)}"
    )

    _print_list(
        "catalog unique targets missing from #print axioms",
        result.catalog_missing_print,
    )
    _print_list(
        "catalog unique targets missing from auditedTheorems",
        result.catalog_missing_registry,
    )
    _print_list(
        "auditedTheorems names with no #print axioms",
        result.registry_no_print,
    )
    _print_list(
        "printed names absent from auditedTheorems",
        result.print_not_registry,
    )

    print(
        "traceability catalog-vs-targetTable text mismatches: "
        f"{len(result.trace_catalog_text_mismatches)}"
    )
    for item in result.trace_catalog_text_mismatches:
        print(f"  {item}")
    print(
        "traceability target-vs-provedDeclarations text mismatches: "
        f"{len(result.trace_text_mismatches)}"
    )
    for item in result.trace_text_mismatches:
        print(f"  {item}")
    print(
        "traceability target-vs-provedDeclarations module mismatches: "
        f"{len(result.trace_module_mismatches)}"
    )
    for item in result.trace_module_mismatches:
        print(f"  {item}")
    print(
        "traceability structural mismatches: "
        f"{len(result.trace_structural)}"
    )
    for item in result.trace_structural:
        print(f"  {item}")
    _print_list(
        "catalog targets absent from provedDeclarations",
        result.snapshot_missing_targets,
    )
    _print_list(
        "provedDeclarations names absent from catalog",
        result.snapshot_extra_targets,
    )

    findings = result.strict_findings()
    print(f"== strict findings: {len(findings)} ==")
    for finding in findings:
        print(f"  {finding}")


def _read(root: pathlib.Path, rel: str) -> str:
    return (root / rel).read_text(encoding="utf-8")


GREEN_CATALOG = '''
def obligations : List Obligation :=
  [ { id := "LN-L1-001", leanTarget := "A.a; B.b", status := .proved }
  , { id := "LN-L1-002", leanTarget := "C.c", status := .proved }
  ]
theorem obligations_length : obligations.length = 2 := rfl
'''

GREEN_AUDIT = '''
#print axioms A.a
#print axioms B.b
#print axioms C.c
def auditedTheorems : List Lean.Name :=
  [ `A.a, `B.b, `C.c ]
theorem auditedTheorems_length : auditedTheorems.length = 3 := rfl
'''

GREEN_TRACE = '''
def targetTable : List TargetEntry :=
  [ ⟨"A.a; B.b", ["A", "B"]⟩
  , ⟨"C.c", ["C"]⟩
  ]
def provedTable : List ProvedEntry :=
  [ ⟨0, [0, 1]⟩
  , ⟨1, [2]⟩
  ]
def provedDeclarations : List DeclEntry :=
  [ ⟨0, "A.a", "A"⟩
  , ⟨1, "B.b", "B"⟩
  , ⟨2, "C.c", "C"⟩
  ]
def lneanModules : List String := ["A", "B", "C"]
'''


def self_test() -> int:
    failures: List[str] = []

    green = analyze(GREEN_CATALOG, GREEN_AUDIT, GREEN_TRACE)
    if green.strict_findings():
        failures.append(
            "green fixture unexpectedly produced findings: "
            + "; ".join(green.strict_findings())
        )

    missing_print = GREEN_AUDIT.replace("#print axioms C.c\n", "")
    mutated_print = analyze(GREEN_CATALOG, missing_print, GREEN_TRACE)
    if "C.c" not in mutated_print.catalog_missing_print:
        failures.append(
            "removed #print axioms line was not reported as missing print"
        )
    if not mutated_print.strict_findings():
        failures.append("removed #print axioms line did not fail strict mode")

    wrong_module = GREEN_TRACE.replace(
        '⟨1, "B.b", "B"⟩', '⟨1, "B.b", "WRONG"⟩'
    )
    mutated_module = analyze(GREEN_CATALOG, GREEN_AUDIT, wrong_module)
    if not mutated_module.trace_module_mismatches:
        failures.append("mutated module was not reported as a trace mismatch")
    if not mutated_module.strict_findings():
        failures.append("mutated module did not fail strict mode")

    if failures:
        print("self-test: FAIL")
        for failure in failures:
            print(f"  {failure}")
        return 1
    print("self-test: PASS")
    print("  green fixture: 0 findings")
    print("  removed #print axioms C.c: detected")
    print("  provedDeclarations module mutation: detected")
    return 0


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Reconcile catalog, axiom audit, and traceability sources."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--report",
        action="store_true",
        help="report counts and findings; exit zero (default)",
    )
    mode.add_argument(
        "--strict",
        action="store_true",
        help="exit nonzero when any mismatch is found",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run an in-memory negative fixture and exit",
    )
    parser.add_argument(
        "--root",
        type=pathlib.Path,
        default=ROOT,
        help="repository root (default: the parent of this script)",
    )
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    result = analyze(
        _read(args.root, CATALOG_PATH),
        _read(args.root, AUDIT_PATH),
        _read(args.root, TRACE_PATH),
    )
    render(result)

    if args.strict:
        return 1 if result.strict_findings() else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
