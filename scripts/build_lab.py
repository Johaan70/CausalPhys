#!/usr/bin/env python3
"""Builds the Lean data for the teaching page docs/kausal-lab.html.

    python3 scripts/build_lab.py          # write the data into the page
    python3 scripts/build_lab.py --check  # fail if the page differs from Lean

For each model on the page the script reads the `causal_model` block from the
Lean source (laws, solving formulas, units, named setups) and asks Lean, via
scripts/Export.lean, for the causal order of every possible lab setup and of
every intervention. For every setup with a cyclic block it runs
`#causal_check`. The pinned messages of the named setups are compared with
what the export computes, so the page, the tests and Lean agree.
"""
import json, re, subprocess, sys, os, itertools

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PAGE = os.path.join(ROOT, "docs", "kausal-lab.html")
BEGIN, END = "/*LEAN-DATA-BEGIN*/", "/*LEAN-DATA-END*/"

# key, source file, model name, term for the model, parameter binder (for #causal_check)
MODELS = [
    ("gas", "Examples/Gas.lean", "Gas", "Gas.model", None),
    ("circuit", "Examples/Circuit.lean", "Circuit", "Circuit.model", None),
    ("divider", "Examples/Divider.lean", "Divider", "Divider.model", None),
    ("complexation", "Examples/Complexation.lean", "Complexation",
     "(Complexation.model ⟨1, 1, one_pos, one_pos⟩)", "(c : Complexation.Consts)"),
    ("weakacid", "Tests/Chemistry.lean", "WeakAcid", "CausalPhys.Tests.WeakAcid.model", None),
    ("market", "Examples/Market.lean", "Market",
     "(Market.model ⟨1, 1, 1, 1, 1, 1, one_pos, one_pos⟩)", "(m : Market.Params)"),
    ("keynes", "Tests/Economics.lean", "Keynes",
     "(CausalPhys.Tests.Keynes.model ⟨0, 1/2, by norm_num, by norm_num⟩)", "(k : Keynes.Params)"),
    ("quantity", "Tests/Economics.lean", "Quantity", "CausalPhys.Tests.Quantity.model", None),
]
CLAUSES = ("variables", "units", "domain", "law", "solve", "witness", "setup")


def model_block(path, name):
    src = open(os.path.join(ROOT, "CausalPhys", "Lang", path)).read()
    m = re.search(r"^causal_model " + name + r"\b.*?$\n((?:  .*\n|\s*\n)*?)(?=\S|\Z)", src, re.M)
    if not m:
        sys.exit(f"build_lab: no causal_model {name} in {path}")
    head = m.group(0).split("\n")[0]
    return head, m.group(1), src


def parse(path, name):
    head, body, src = model_block(path, name)
    lines = [l for l in body.split("\n") if l.strip()]
    # join continuation lines (deeper indentation that does not start a clause)
    items = []
    for l in lines:
        t = l.strip()
        word = t.split()[0]
        if word in CLAUSES and (l.startswith("  " + word) or l.startswith("    " + word)):
            items.append(t)
        else:
            items[-1] += " " + t
    out = {"name": name, "lawText": [], "named": [], "domain": None, "unitsClause": ""}
    for t in items:
        t = re.sub(r"\s+by .*$", "", t) if t.startswith("solve") else t
        t = t.split(" -- ")[0].strip() if not t.startswith("setup") else t
        if t.startswith("units "):
            out["unitsClause"] = t[len("units "):].strip()
            out["units_declared"] = [[x.strip() for x in u.split(":")] for u in out["unitsClause"].split(",")]
        elif t.startswith("domain "):
            out["domain"] = t[len("domain "):].strip()
        elif t.startswith("law "):
            n, e = t[4:].split(" : ", 1)
            out["lawText"].append({"name": n.strip(), "eq": e.strip(), "solve": []})
        elif t.startswith("solve "):
            v, f = t[6:].split(" := ", 1)
            out["lawText"][-1]["solve"].append({"var": v.strip(), "formula": f.strip()})
        elif t.startswith("setup "):
            code, _, comment = t.partition("--")
            n, fx = code[6:].split(" fixes ")
            out["named"].append({"name": n.strip(), "fixed": fx.split(), "comment": comment.strip()})
    out["source"] = (head + "\n" + body).rstrip()
    out["pinned"] = pinned(src, name, [s["name"] for s in out["named"]])
    return out


def pinned(src, name, setups):
    """The #guard_msgs-pinned outputs of #causal_order / #causal_check per named setup."""
    res = {}
    for m in re.finditer(r"/--\n(info: .*?)\n-/\n#guard_msgs in\n#(causal_order|causal_check) (\S+)(.*)", src, re.S | re.M):
        msg, cmd, target, rest = m.group(1), m.group(2), m.group(3), m.group(4).split("\n")[0]
        if rest.strip().startswith(".intervene"):
            continue
        t = target.split(".")[-1].strip("(")
        if t in setups:
            res.setdefault(t, {})[cmd] = msg[len("info: "):]
    return res


REJECTS = ["WrongFormula", "UnknownVariable", "OverFixed", "GasWithoutR", "GasWrongFormula",
           "ArrheniusWithoutR", "UndeclaredConstant", "MissingUnit"]


def rejects():
    """Wrong models and the errors Lean pins for them in Tests/Rejects.lean."""
    src = open(os.path.join(ROOT, "CausalPhys", "Lang", "Tests", "Rejects.lean")).read()
    out = []
    for name in REJECTS:
        m = re.search(r"/--\n(error: (?:(?!-/).)*?)\n-/\n#guard_msgs in\n(causal_model " + name + r" where\n(?:  [^\n]*\n)*)",
                      src, re.S)
        if not m:
            sys.exit(f"build_lab: no pinned rejection {name}")
        errs = [e.strip() for e in m.group(1).split("\n---\n")
                if e.startswith("error:") and "could not synthesize" not in e]
        msg = errs[0][len("error: "):]
        # keep the goal Lean could not prove, drop the anonymous hypotheses
        msg = "\n".join(l for l in msg.split("\n") if "✝ :" not in l and not l.startswith("⊢ Order"))
        msg = msg.replace("s✝ V.", "")
        out.append({"name": name, "code": m.group(2).rstrip(), "error": msg})
    return out


def lean(code):
    tmp = os.path.join(ROOT, ".lake", "lab_export.lean")
    os.makedirs(os.path.dirname(tmp), exist_ok=True)
    open(tmp, "w").write(code)
    r = subprocess.run(["lake", "env", "lean", tmp], cwd=ROOT, capture_output=True, text=True)
    out = r.stdout + r.stderr
    if r.returncode != 0 or re.search(r"^.*error", out, re.M):
        sys.exit("build_lab: Lean failed\n" + out[:4000])
    return out


def main():
    check = "--check" in sys.argv
    export = open(os.path.join(ROOT, "scripts", "Export.lean")).read()
    srcs = {key: parse(path, name) for key, path, name, _, _ in MODELS}
    calls = "\n".join(
        f'#export_model "{key}" "{srcs[key]["unitsClause"]}" {term}' for key, _, _, term, _ in MODELS)
    out = lean(export + "\n" + calls + "\n")
    data = {}
    for line in re.findall(r"EXPORT (\{.*\})", out):
        d = json.loads(line)
        d.update(srcs[d["key"]])
        data[d["key"]] = d

    # #causal_check for every setup with a cyclic block (and the interventions)
    jobs = []
    for key, path, name, term, binder in MODELS:
        d = data[key]
        ns = "CausalPhys.Tests." if path.startswith("Tests") else "CausalPhys.Examples."
        pre = f"open {ns}{name}\n"
        if binder:
            pre += f"variable {binder}\n"
            p = binder.strip("(").split(":")[0].strip()
            M = f"({ns}{name}.model {p})"
        else:
            M = f"{ns}{name}.model"
        for where, setups in [(None, d["setups"])] + list(d["without"].items()):
            for s in setups:
                if not s["valid"] or s["acyclic"]:
                    continue
                exo = "[" + ", ".join("." + v for v in s["fixed"]) + "]"
                Mw = M if where is None else f"({M}.remove .{where})"
                # a named definition, as `causal_model` makes for setups (an inline
                # structure literal makes the tactics unfold the validity proof)
                n = f"labSetup{len(jobs)}"
                arg = f" {p}" if binder else ""
                bnd = f" {binder}" if binder else ""
                cmd = (f"section\n{pre}noncomputable def {n}{bnd} : Setup {Mw} := {{ exo := {exo} }}\n"
                       f"#print \"@@CHECK@@\"\n#causal_check {n}{arg}\nend")
                jobs.append((key, where, s["fixed"], cmd))
    head = "import CausalPhys\nopen CausalPhys CausalPhys.Lang CausalPhys.Examples CausalPhys.Tests\n"
    # two Lean processes in parallel
    halves = [jobs[0::2], jobs[1::2]]
    procs = []
    for i, part in enumerate(halves):
        f = os.path.join(ROOT, ".lake", f"lab_checks{i}.lean")
        open(f, "w").write(head + "\n".join(j[3] for j in part) + "\n")
        procs.append(subprocess.Popen(["lake", "env", "lean", f], cwd=ROOT,
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True))
    for part, pr in zip(halves, procs):
        out = pr.communicate()[0]
        if pr.returncode != 0 or re.search(r"error", out):
            sys.exit("build_lab: Lean failed\n" + out[:4000])
        msgs = out.split("@@CHECK@@")[1:]
        if len(msgs) != len(part):
            sys.exit(f"build_lab: expected {len(part)} check messages, got {len(msgs)}\n{out[:3000]}")
        for (key, where, fixed, _), msg in zip(part, msgs):
            lst = data[key]["setups"] if where is None else data[key]["without"][where]
            next(x for x in lst if x["fixed"] == fixed)["check"] = msg.strip()

    # The pinned outputs of the named setups must agree with the export
    for key, d in data.items():
        for named in d["named"]:
            s = next(x for x in d["setups"] if set(x["fixed"]) == set(named["fixed"]))
            named["fixed"] = s["fixed"]
            pin = d["pinned"].get(named["name"], {})
            if "causal_order" in pin and pin["causal_order"] != order_text(s):
                sys.exit(f"build_lab: {key}.{named['name']}: export differs from pinned #causal_order\n"
                         f"{pin['causal_order']}\n---\n{order_text(s)}")
            if "causal_check" in pin:
                named["check"] = pin["causal_check"]

    blob = json.dumps({"models": data, "rejects": rejects()}, ensure_ascii=False, separators=(",", ":"))
    page = open(PAGE).read()
    i, j = page.index(BEGIN) + len(BEGIN), page.index(END)
    new = page[:i] + "\nconst LEAN = " + blob + ";\n" + page[j:]
    if check:
        if new != page:
            sys.exit("build_lab: docs/kausal-lab.html is out of date; run scripts/build_lab.py")
        print("lab page agrees with Lean")
    else:
        open(PAGE, "w").write(new)
        n = sum(len(d["setups"]) + sum(len(v) for v in d["without"].values()) for d in data.values())
        print(f"wrote {len(data)} models, {n} setups, {len(jobs)} checks")


def order_text(s):
    lines = [f'{r["law"]} determines {r["var"]}, reading [{", ".join(r["reads"])}]' for r in s["order"]]
    if s["acyclic"]:
        lines.append("acyclic: every intervention has exactly one outcome of the causal model")
    else:
        seen = []
        for r in s["order"]:
            if r["law"] in seen:
                continue
            seen += r["block"]
            if len(r["block"]) > 1:
                lines.append(f'cyclic block: [{", ".join(r["block"])}]')
    return "\n".join(lines)


if __name__ == "__main__":
    main()
