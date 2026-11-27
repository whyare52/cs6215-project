import json
import statistics
import sys
from collections import Counter

data = json.load(open(sys.argv[1]))
base = {(r["version"]): r for r in data if r["config"] == "baseline"}
for r in data:
  runs = [(s["script"], i, run) for s in r["scripts"] for i, run in enumerate(s["runs"])]
  viol = Counter()
  for _, _, run in runs:
    for v in run["violations"]:
      viol[(v[0], v[2], v[3], v[5], v[4], v[6])] += 1
  unseen = Counter(tuple(u) for _, _, run in runs for u in run["unseen"])
  crashes = Counter(run["crash"] for _, _, run in runs if run["crash"])
  key = "prompt_holds" if "prompt_holds" in runs[0][2] else "tool_holds"
  # B's run is index 1, A's second run index 2
  b_leak = sum(1 for _, i, run in runs if i == 1 and "A" in run[key])
  a_self = sum(1 for _, i, run in runs if i == 2 and "A" in run[key])
  a_b = sum(1 for _, i, run in runs if i == 2 and "B" in run[key])
  secs = [run["seconds"] for _, _, run in runs]
  upd = [run.get("update_seconds") for _, _, run in runs if run.get("update_seconds")]
  bsecs = [run["seconds"] for s in base[r["version"]]["scripts"] for run in s["runs"]] \
    if r["version"] in base else secs
  extra = ""
  if key == "tool_holds":
    extra = f" exists_refused={sum(1 for _, _, run in runs if run['exists_refused'])}"
  print(f"== {r['subject']} {r['version']} {r['config']}: runs={len(runs)} "
        f"violations={sum(viol.values())} crashes={dict(crashes)} "
        f"B-run holds A={b_leak} A2 holds A={a_self} A2 holds B={a_b}{extra}")
  print(f"   median run {statistics.median(secs)*1000:.1f} ms (baseline "
        f"{statistics.median(bsecs)*1000:.1f} ms, x{statistics.median(secs)/statistics.median(bsecs):.3f})"
        + (f", updater median {statistics.median(upd)*1000:.2f} ms" if upd else ""))
  for k, n in sorted(viol.items()):
    print(f"   {n:3d} {k}")
  for k, n in sorted(unseen.items()):
    print(f"   unseen {n:3d} {k}")
