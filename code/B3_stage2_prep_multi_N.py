"""
B-3 阶段 2 预备 sanity:N ∈ {1000, 3000, 5000} 多 N 扫
=====================================================

目的:验证 N=1000 prep 显示的 "random 取代 cartesian 第 1" 是 N 依赖的
连续现象还是 N 跳跃 artifact。

按 memory `feedback_verify_suspicious_immediately.md`:可疑信号当下验证,
不留作"等阶段 2 大 N 判决"。
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

import numpy as np  # noqa: E402

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


N_TARGETS = [1000, 3000, 5000]
K_RATIO = 12  # K = N // K_RATIO,与 b3pre N=300/K=50 (ratio≈6) 类似但更稀疏便于大 N

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
    out = {"trajectory": name, "N": int(V.shape[0]), "K": K}

    if V.shape[0] < K + 5:
        out["error"] = f"too few points (N={V.shape[0]} < K+5={K+5})"
        return out

    edges = build_edges_from_delaunay(V)
    out["n_edges"] = int(edges.shape[0])

    L = build_laplacian(V, edges)
    mu, U = low_spectrum(L, k=K)
    out["mu_min"] = float(mu.min())
    out["mu_max"] = float(mu.max())

    configs = make_subsample_configs(V, K=K, k_max=K_MAX)
    cfg_metrics = {}
    for cname, idx in configs.items():
        m = sampling_metrics(U, idx, K)
        cfg_metrics[cname] = {
            "M": int(len(idx)),
            "rank": int(m.get("rank", -1)),
            "cond": float(m.get("cond", float("nan"))),
        }
    out["configs"] = cfg_metrics
    out["elapsed_sec"] = round(time.time() - t0, 2)
    return out


def main() -> None:
    all_results = {"N_TARGETS": N_TARGETS, "K_RATIO": K_RATIO,
                   "by_N": {}}

    rankings = {}  # {N: [(traj, tight_cond), ...] sorted}

    for N in N_TARGETS:
        K = max(50, N // K_RATIO)
        print(f"\n=== N≈{N}, K={K} ===\n")
        results = {}
        for name, gen in TRAJECTORIES.items():
            print(f"  {name} ...", end=" ", flush=True)
            try:
                r = run_one(name, gen, n_target=N, K=K)
            except Exception as e:
                r = {"trajectory": name, "error": f"{type(e).__name__}: {e}"}
                print(f"ERROR {r['error']}")
                results[name] = r
                continue
            results[name] = r
            if "error" in r:
                print(f"ERROR {r['error']}")
                continue
            tight = r["configs"].get("tight_K_plus_2", {})
            print(f"N={r['N']} tight_cond={tight.get('cond', float('nan')):.3e}  elapsed={r['elapsed_sec']}s")

        all_results["by_N"][N] = results

        # tight ranking
        tight_conds = {}
        for name, r in results.items():
            if "error" in r:
                continue
            for cname, c in r["configs"].items():
                if "tight" in cname:
                    tight_conds[name] = c["cond"]
        ranked = sorted(tight_conds.items(), key=lambda kv: kv[1])
        rankings[N] = [n for n, _ in ranked]
        print(f"\n  tight cond 排序 N={N}: {rankings[N]}")

    # 汇总:N 依赖连续性
    print("\n\n=== N 依赖汇总 ===\n")
    print(f"{'N':>6}  {'rank1':>10}  {'rank2':>10}  {'rank3':>10}  {'rank4':>10}  {'rank5':>10}")
    print(f"{200:>6}  cartesian   random      sparkling   spiral      radial      [b3pre 历史]")
    print(f"{300:>6}  random      cartesian   sparkling   spiral      radial      [stage1 历史]")
    for N in N_TARGETS:
        r = rankings.get(N, [])
        cells = (r + ['-'] * 5)[:5]
        print(f"{N:>6}  " + "  ".join(f"{c:>10}" for c in cells))

    # 判断稳定性
    rank1_at_each_N = [rankings[N][0] for N in N_TARGETS if rankings.get(N)]
    print(f"\n  rank1 at N ∈ {N_TARGETS}: {rank1_at_each_N}")
    if len(set(rank1_at_each_N)) == 1:
        print(f"  ✅ N≥{N_TARGETS[0]} 内 rank1 = {rank1_at_each_N[0]} 稳定;接缝 8 N 依赖结论 = 'random 在 N≥300 取代 cartesian'")
    else:
        print(f"  ⚠️ rank1 在 N ∈ {N_TARGETS} 内仍变化;接缝 8 N 依赖更复杂,需更多 N")

    out_json = ROOT / "B3_stage2_prep_multi_N_results.json"
    out_json.write_text(json.dumps(all_results, indent=2))
    print(f"\nresults -> {out_json}")


if __name__ == "__main__":
    main()
