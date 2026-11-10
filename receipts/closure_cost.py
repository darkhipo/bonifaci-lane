#!/usr/bin/env python3
"""Measure the build-closure cost of candidate Mathlib modules on the campaign pin.

For each module name, compute the transitive import closure and report how many of
those modules have NO built .olean in this workspace (i.e. how many the build would
have to compile before the module is usable).

Searches every lake package (mathlib, batteries, aesop, ...) for sources and oleans,
so external tooling modules are classified correctly rather than counted as unbuilt.

Read-only. No network. No build.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PKGS = os.path.join(ROOT, ".lake/packages")
# ROOT comes first: this project's own modules live at ROOT/<Dir>/*.lean with oleans at
# ROOT/.lake/build/lib/lean/..., i.e. the same shape as a package, but ROOT is not itself
# under .lake/packages. Without it every own-module query answered a definite
# "SOURCE: **ABSENT on this pin**" for a module that plainly exists (wound R-filed §9.7;
# measured on `closure_cost.py Bonnifaci.M6` while Bonnifaci/M6.lean and M6.olean were both
# present). The same list feeds `is_built`, so omitting ROOT also mis-classified our own
# oleans as unbuilt.
PACKAGES = [ROOT, PKGS] + [os.path.join(PKGS, p) for p in sorted(os.listdir(PKGS))]

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.'«»]+)", re.M)

_src_cache = {}
_built_cache = {}
_closure_cache = {}


def find_source(mod):
    if mod in _src_cache:
        return _src_cache[mod]
    rel = mod.replace(".", "/") + ".lean"
    hit = None
    for p in PACKAGES:
        cand = os.path.join(p, rel)
        if os.path.exists(cand):
            hit = cand
            break
    _src_cache[mod] = hit
    return hit


def is_built(mod):
    if mod in _built_cache:
        return _built_cache[mod]
    rel = mod.replace(".", "/") + ".olean"
    hit = any(os.path.exists(os.path.join(p, ".lake/build/lib/lean", rel)) for p in PACKAGES)
    _built_cache[mod] = hit
    return hit


def direct_imports(mod):
    p = find_source(mod)
    if p is None:
        return None
    with open(p, encoding="utf-8", errors="replace") as f:
        return IMPORT_RE.findall(f.read())


def closure(mod):
    if mod in _closure_cache:
        return _closure_cache[mod]
    seen, external = set(), set()
    stack = [mod]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        imps = direct_imports(m)
        if imps is None:
            external.add(m)
            continue
        stack.extend(imps)
    res = (seen - external, external)
    _closure_cache[mod] = res
    return res


def report(mod):
    if find_source(mod) is None:
        print(f"{mod}\n  SOURCE: **ABSENT** (no .lean under the project root or any lake package)")
        return
    mods, external = closure(mod)
    unbuilt = sorted(m for m in mods if not is_built(m))
    built = len(mods) - len(unbuilt)
    print(f"{mod}")
    print(f"  source: present ({os.path.relpath(find_source(mod), ROOT)})")
    print(f"  closure: {len(mods)} local modules (+{len(external)} external pkgs/lean-core)")
    print(f"  already built: {built}")
    print(f"  UNBUILT (compile-before-use cost): {len(unbuilt)}")
    for m in unbuilt[:10]:
        print(f"     - {m}")
    if len(unbuilt) > 10:
        print(f"     ... and {len(unbuilt) - 10} more")


if __name__ == "__main__":
    for name in sys.argv[1:]:
        report(name)
        print()
