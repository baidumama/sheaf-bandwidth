"""
Stage-2 preparation: N=1000 subset sanity check
================================================

Verifies that the b3pre skeleton continues to run at N=1000 and the
core hypothesis (cond rank ordering + numerical consistency at the
key seam) remains supported, before launching the full sweep.

Reuses entry points from B3pre_hodge_separating.py without modifying its source.

Output: stdout summary table + JSON dumped to code/B3_stage2_prep_results.json.
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

import numpy as np  # noqa: E402

# 复用 b3pre 的所有数值原语,但**不**跑它的 main(避免画 20 张图)
from B3pre_hodge_separating import (  # noqa: E402
    K_MAX,
    EIG_TOL,
    build_edges_from_delaunay,
    build_laplacian,
    low_spectrum,
    make_subsample_configs,
    sampling_metrics,
    traj_cartesian,
    traj_radial,
    traj_random_uniform,
    traj_sparkling,
    traj_stack_of_spirals,
)


N_TARGET = 1000
K_EIG_PREP = 80  # 与 b3pre N=300/K=50 相同的 N/K ≈ 6 比例

TRAJECTORIES = {
    "cartesian": traj_cartesian,
    "random": traj_random_uniform,
    "sparkling": traj_sparkling,
    "spiral": traj_stack_of_spirals,
    "radial": traj_radial,
}


def run_one(name: str, gen, n_target: int, K: int) -> dict:
    t0 = time.time()
    V = gen(n_target=n_target, k_max=K_MAX)
    V_unique, _ = np.unique(np.round(V, 8), axis=0, return_index=True)
    V = V_unique
    out = {"trajectory": name, "N": int(V.shape[0])}

    if V.shape[0] < K + 5:
        out["error"] = f"too few points (N={V.shape[0]} < K+5={K+5})"
        return out

    edges = build_edges_from_delaunay(V)
    out["n_edges"] = int(edges.shape[0])

    L = build_laplacian(V, edges)
    mu, U = low_spectrum(L, k=K)
    out["mu_min"] = float(mu.min())
    out["mu_max"] = float(mu.max())
    out["n_zero_eigs"] = int(np.sum(mu < EIG_TOL))

    configs = make_subsample_configs(V, K=K, k_max=K_MAX)
    cfg_metrics = {}
    for cname, idx in configs.items():
        m = sampling_metrics(U, idx, K)
        cfg_metrics[cname] = {
            "M": int(len(idx)),
            "rank": int(m.get("rank", -1)),
            "cond": float(m.get("cond", float("nan"))),
            "sigma_min": float(m.get("sigma_min", float("nan"))),
            "sigma_max": float(m.get("sigma_max", float("nan"))),
        }
    out["configs"] = cfg_metrics
    out["elapsed_sec"] = round(time.time() - t0, 2)
    return out


def main() -> None:
    print(f"=== B-3 阶段 2 预备 sanity (N≈{N_TARGET}, K={K_EIG_PREP}) ===\n")
    results = {"N_TARGET": N_TARGET, "K_EIG": K_EIG_PREP, "trajectories": {}}
    for name, gen in TRAJECTORIES.items():
        print(f"-- {name} --", flush=True)
        try:
            r = run_one(name, gen, n_target=N_TARGET, K=K_EIG_PREP)
        except Exception as e:
            r = {"trajectory": name, "error": f"{type(e).__name__}: {e}"}
            print(f"  ERROR: {r['error']}")
        results["trajectories"][name] = r
        if "error" in r:
            continue
        print(f"  N={r['N']}  edges={r['n_edges']}  "
              f"zero_eigs={r['n_zero_eigs']}  elapsed={r['elapsed_sec']}s")
        for cname, c in r["configs"].items():
            print(f"    {cname:>14s}  M={c['M']:4d}  rank={c['rank']:4d}  "
                  f"cond={c['cond']:.3e}  σ_min={c['sigma_min']:.3e}  "
                  f"σ_max={c['sigma_max']:.3e}")
        print()

    # 排序对比:tight oversampling cond 排序是否仍然是
    # cartesian < random < sparkling < spiral < radial(b3pre N=300 的判断)
    print("=== tight oversampling cond 排序(对照 b3pre N=300)===")
    rank_cartesian_lowest = []
    cond_tight = {}
    for name, r in results["trajectories"].items():
        if "error" in r:
            continue
        # tight = M ≈ K + 2
        for cname, c in r["configs"].items():
            if "tight" in cname:
                cond_tight[name] = c["cond"]
    if cond_tight:
        ranked = sorted(cond_tight.items(), key=lambda kv: kv[1])
        for i, (name, c) in enumerate(ranked):
            print(f"  rank{i+1}  {name:>10s}  cond={c:.3e}")
        b3pre_n300 = ["cartesian", "random", "sparkling", "spiral", "radial"]
        ranked_names = [n for n, _ in ranked]
        same = ranked_names == b3pre_n300
        print(f"\n  排序 vs b3pre N=300: {'✅ 相同' if same else '⚠️ 不同'}")
        print(f"  N=1000 排序: {ranked_names}")
        print(f"  N=300  排序: {b3pre_n300}")
        results["rank_match_n300"] = same
        results["rank_n1000_tight"] = ranked_names

    out_json = ROOT / "B3_stage2_prep_results.json"
    out_json.write_text(json.dumps(results, indent=2))
    print(f"\nresults -> {out_json}")


if __name__ == "__main__":
    main()
