#!/usr/bin/env python3
"""Emit a row/merge tree for one fixed Gram expansion.

Python proposes exact intermediate values; every row and merge has a separate
Lean kernel check. Zero coefficients are intentionally retained so each merge
is checked by syntactic equality, with no repeated normalization. The final
polynomial is connected to the existing recorded Gram polynomial by one merge.
Nothing in the existing SOS/Generated/Assembly directories is modified.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def write_if_changed(path: Path, content: str) -> None:
    """Preserve mtimes and existing verification records on exact regeneration."""
    if not path.exists() or path.read_text() != content:
        path.write_text(content)


def integer(value: int) -> str:
    return f"Int.ofNat {value}" if value >= 0 else f"Int.negSucc {-value-1}"


def exponent_key(exponents: tuple[int, ...]) -> int:
    return sum(value * 16**i for i, value in enumerate(exponents))


def merge(left: list, right: list) -> list:
    """Mirror Sparse.merge on sorted lists, retaining zero coefficients."""
    out = []
    i = j = 0
    while i < len(left) and j < len(right):
        c, e = left[i]
        d, f = right[j]
        if e == f:
            out.append((c + d, e))
            i += 1
            j += 1
        elif exponent_key(e) < exponent_key(f):
            out.append((c, e))
            i += 1
        else:
            out.append((d, f))
            j += 1
    return out + left[i:] + right[j:]


def polynomial(name: str, terms: list) -> str:
    pieces = []
    declarations = []
    for start in range(0, len(terms), 64):
        piece = f"{name}_{start // 64:03d}"
        pieces.append(piece)
        values = [
            f"({integer(c)}, ⟨{', '.join(map(str, e))}⟩)"
            for c, e in terms[start : start + 64]
        ]
        declarations.append(
            f"noncomputable def {piece} : Polynomial := [\n  "
            + ",\n  ".join(values)
            + "]\n"
        )
    declarations.append(
        f"noncomputable def {name} : Polynomial := "
        + (" ++ ".join(pieces) if pieces else "[]")
        + "\n"
    )
    return "".join(declarations)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--identity", required=True, choices=["H1_0", "H1_1", "H1_2", "H2"])
    parser.add_argument("--block", required=True, type=int)
    parser.add_argument("--checks-per-module", type=int, default=128,
                        help="Group independent theorems to amortize compiler/import overhead")
    args = parser.parse_args()
    if args.checks_per_module < 1:
        parser.error("--checks-per-module must be positive")
    matrix_path = ROOT / "data/exact" / f"{args.identity}.json"
    poly_path = ROOT / "data/polynomials" / f"{args.identity}.json"
    matrix = json.loads(matrix_path.read_text())["blocks"][args.block]
    recorded = json.loads(poly_path.read_text())["blocks"][args.block]
    assert matrix["index"] == recorded["index"] == args.block
    size = matrix["n"]
    assert size > 0
    tag = f"{args.identity}B{args.block:03d}"
    package = f"Certificate.Chunked.{tag}"
    output = ROOT / "Certificate/Chunked" / tag
    output.mkdir(parents=True, exist_ok=True)
    data = f"Certificate.Generated.{tag}.data"
    original = f"Certificate.SOS.{tag}"
    options = "open Certificate.Sparse\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n"
    checks = []

    def write(name: str, text: str, kind: str, dependencies: list[str], terms: int) -> None:
        checks.append({
            "name": name, "kind": kind, "text": text,
            "dependencies": dependencies, "terms": terms,
        })

    level = []
    for i in range(size):
        name = f"Leaf{i:03d}"
        terms = []
        for j in range(size):
            e = tuple(a + b for a, b in zip(matrix["basis"][i], matrix["basis"][j]))
            # The formal GramData reflects the upper triangle to both halves.
            a = int(matrix["A"][min(i, j)][max(i, j)])
            b = int(matrix["B"][min(i, j)][max(i, j)])
            terms.extend([(a, e + (0,)), (b, e + (1,))])
        # Basis monomials are distinct, so each row has distinct exponents.
        assert len({e for _, e in terms}) == len(terms)
        terms.sort(key=lambda item: exponent_key(item[1]))
        index = f"(⟨{i}, by decide⟩ : Fin {data}.size)"
        source = f"import Certificate.SOS.{tag}Data\nimport Certificate.ChunkedExpansion\nnamespace {package}.{name}\n{options}"
        source += polynomial("witness", terms)
        source += f"def indices : List (Fin {data}.size) := [{index}]\n"
        source += f"theorem check : fastGramRow {data} {original}.basis {index} = witness := by\n  decide +kernel\n"
        source += f"theorem evaluation {{R : Type*}} [CommRing R] (x : Fin 8 → R) :\n    evalMany x (indices.map (fastGramRow {data} {original}.basis)) = eval x witness :=\n  gram_row_leaf x {data} {original}.basis {index} witness check\n"
        source += f"#print axioms evaluation\nend {package}.{name}\n"
        write(name, source, "row", [], len(terms))
        level.append((name, terms))

    node_number = 0
    while len(level) > 1:
        next_level = []
        for start in range(0, len(level), 2):
            if start + 1 == len(level):
                next_level.append(level[start])
                continue
            (left, lp), (right, rp) = level[start : start + 2]
            name = f"Node{node_number:03d}"
            node_number += 1
            terms = merge(lp, rp)
            source = f"import {package}.{left}\nimport {package}.{right}\nnamespace {package}.{name}\n{options}"
            source += polynomial("witness", terms)
            source += f"def indices : List (Fin {data}.size) := {left}.indices ++ {right}.indices\n"
            source += f"theorem check : merge {left}.witness {right}.witness = witness := by\n  decide +kernel\n"
            source += f"theorem evaluation {{R : Type*}} [CommRing R] (x : Fin 8 → R) :\n    evalMany x (indices.map (fastGramRow {data} {original}.basis)) = eval x witness :=\n  gram_rows_join x {data} {original}.basis {left}.indices {right}.indices\n    {left}.witness {right}.witness witness ({left}.evaluation x) ({right}.evaluation x) check\n"
            source += f"#print axioms evaluation\nend {package}.{name}\n"
            write(name, source, "merge", [f"{package}.{left}", f"{package}.{right}"], len(terms))
            next_level.append((name, terms))
        level = next_level

    root, terms = level[0]
    expected = [(int(c), tuple(e)) for c, e in recorded["gram_integer_poly"]]
    assert [(c, e) for c, e in terms if c != 0] == expected, "Python tree must replay the recorded Gram polynomial"
    source = f"import {package}.{root}\nimport Certificate.MergeArithmetic\nnamespace {package}\n{options}"
    source += f"theorem coverage : {root}.indices = List.ofFn (fun i : Fin {data}.size => i) := by\n  decide +kernel\n"
    source += f"theorem final_check : checkEqualMerged {root}.witness {original}.gram = true := by\n  decide +kernel\n"
    source += f"theorem gram_evaluation {{R : Type*}} [CommRing R] (x : Fin 8 → R) :\n    eval x (gramPolynomial {data} {original}.basis) = eval x {original}.gram := by\n  exact (gram_expansion_of_tree x {data} {original}.basis {root}.indices\n    {root}.witness coverage ({root}.evaluation x)).trans\n    (eq_of_checkMerged x _ _ final_check)\n"
    source += f"theorem gram_nonnegative (x : Fin 8 → ℝ) (hx : x 7 = Real.sqrt 3)\n    (hden : 0 < {data}.den)\n    (hPSD : (realGram {data}.A {data}.B {data}.den).PosSemidef) :\n    0 ≤ eval x {original}.gram := by\n  rw [← gram_evaluation]\n  exact eval_gramPolynomial_nonneg x hx {data} {original}.basis hden hPSD\n"
    source += f"#print axioms gram_evaluation\n#print axioms gram_nonnegative\nend {package}\n"
    write("Proof", source, "final", [f"{package}.{root}"], len(terms))
    jobs = []
    module_for = {}
    groups = [checks[start : start + args.checks_per_module]
              for start in range(0, len(checks) - 1, args.checks_per_module)]
    # Keep the final theorem in its own small module for downstream imports.
    if groups and groups[-1] and groups[-1][-1]["kind"] == "final":
        groups[-1].pop()
    groups = [group for group in groups if group]
    groups.append([checks[-1]])
    for group_number, group in enumerate(groups):
        module_name = "Proof" if group[0]["kind"] == "final" else f"Chunk{group_number:03d}"
        module = f"{package}.{module_name}"
        for check in group:
            module_for[f"{package}.{check['name']}"] = module
        imports = set()
        body = []
        for check in group:
            lines = []
            for line in check["text"].splitlines():
                if line.startswith("import "):
                    imported = line.removeprefix("import ")
                    imported = module_for.get(imported, imported)
                    if imported != module:
                        imports.add(imported)
                else:
                    lines.append(line)
            body.append("\n".join(lines))
        text = "".join(f"import {imported}\n" for imported in sorted(imports))
        text += "\n\n".join(body) + "\n"
        path = output / f"{module_name}.lean"
        write_if_changed(path, text)
        jobs.append({
            "module": module,
            "dependencies": sorted(imports),
            "checks": [{key: value for key, value in check.items()
                        if key not in {"text", "dependencies"}} for check in group],
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        })
    manifest = {
        "identity": args.identity, "block": args.block, "size": size,
        "generator": "scripts/emit_chunked_sos.py", "root_node": root,
        "matrix_sha256": hashlib.sha256(matrix_path.read_bytes()).hexdigest(),
        "polynomial_sha256": hashlib.sha256(poly_path.read_bytes()).hexdigest(),
        "checks_per_module": args.checks_per_module, "sources": jobs,
    }
    write_if_changed(output / "manifest.json", json.dumps(manifest, indent=2) + "\n")
    print(f"Generated {size} row checks, {node_number} merge checks, and one final check "
          f"in {len(jobs)} modules under {output}")


if __name__ == "__main__":
    main()
