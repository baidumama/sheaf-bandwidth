"""Stage-1 simulation: 5 trajectories × 5 SNR × N=300, verifying cond vs NRMSE rank consistency.

Hypothesis:
  Under Rician-noised CG-on-V_B reconstruction, the cond(A) rank order across
  trajectories should match the NRMSE rank order — i.e., Spearman(cond, NRMSE)
  should be significantly positive (rho → +1, p → 0).
"""
import sys
import time
import json
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))

from B3_main_simulation import (  # noqa: E402
    make_shepplogan_like,
    make_trajectory,
    build_complex_and_spectrum,
    sampling_matrix,
    cg_on_VB,
    snr_to_sigma,
    add_rician_noise,
    evaluate_recon,
    spearman_rho,
)
import B3pre_hodge_separating as b3pre  # noqa: E402


def stage1() -> dict:
    rng = np.random.default_rng(20260506)
    phantom = make_shepplogan_like(seed=0)

    trajectories = ["cartesian", "random", "spiral", "radial", "sparkling"]
    snr_list = [30.0, 25.0, 20.0, 15.0, 10.0]
    n_target = 300
    K = 30

    print("=" * 64)
    print(f"B-3 v0.1 阶段 1: {len(trajectories)} traj × {len(snr_list)} SNR × N={n_target}")
    print("=" * 64)

    # 加 oversampling 维度: tight_K_plus_2 (M ≈ K) vs rand_50pct (M ≈ N/2 ≈ 5K)
    oversampling_keys = ["tight_K_plus_2", "rand_50pct"]

    rows = []
    per_traj_geometry: dict = {os_key: {} for os_key in oversampling_keys}

    t_total = time.time()
    for name in trajectories:
        t0 = time.time()
        V = make_trajectory(name, n_target=n_target)
        _, _, _, U = build_complex_and_spectrum(V, K_eig=K)
        S_true = phantom.analytic_kspace(V)
        coef_ref = U.conj().T @ S_true
        configs = b3pre.make_subsample_configs(V, K=K, k_max=b3pre.K_MAX)

        for os_key in oversampling_keys:
            V_s = configs[os_key]
            A = sampling_matrix(U, V_s, K)
            s = np.linalg.svd(A, compute_uv=False)
            sigma_max = float(s[0])
            sigma_min = float(s[-1])
            cond = float(sigma_max / sigma_min) if sigma_min > 0 else float("inf")

            per_traj_geometry[os_key][name] = {
                "N": int(V.shape[0]),
                "M": int(V_s.size),
                "K": K,
                "cond": cond,
                "sigma_max": sigma_max,
                "sigma_min": sigma_min,
            }

            for snr_db in snr_list:
                sigma = snr_to_sigma(S_true, snr_db)
                S_noisy = add_rician_noise(S_true, sigma, rng)
                y = S_noisy[V_s]
                recon = cg_on_VB(
                    A, y, K,
                    tikhonov=1e-6 * float(np.linalg.norm(A) ** 2),
                    rtol=1e-9,
                    max_iter=500,
                )
                m = evaluate_recon(recon.coef, coef_ref, A)
                rows.append({
                    "trajectory": name,
                    "oversampling": os_key,
                    "snr_db": snr_db,
                    "M": int(V_s.size),
                    "cond": cond,
                    "sigma_min": sigma_min,
                    "sigma_max": sigma_max,
                    "nrmse": m.nrmse,
                    "ssim_proxy": m.ssim_proxy,
                })

        elapsed = time.time() - t0
        tight_cond = per_traj_geometry["tight_K_plus_2"][name]["cond"]
        loose_cond = per_traj_geometry["rand_50pct"][name]["cond"]
        print(f"  {name:<10} N={V.shape[0]:>4}  "
              f"tight cond={tight_cond:>9.2f}  loose cond={loose_cond:>7.2f}  "
              f"elapsed={elapsed:.2f}s")

    print(f"\nTotal elapsed: {time.time() - t_total:.2f}s")

    # ===== 判据 1: per-(oversampling, SNR) Spearman(cond, NRMSE) =====
    print("\n--- 判据 1: per-(oversampling, SNR) Spearman(cond, NRMSE) ---")
    print("  (正 ρ ⇒ cond 大的 trajectory NRMSE 也大,排序一致)")
    per_snr_rho: dict = {os_key: {} for os_key in oversampling_keys}
    for os_key in oversampling_keys:
        print(f"  [{os_key}]")
        for snr_db in snr_list:
            sub = [r for r in rows
                   if r["snr_db"] == snr_db and r["oversampling"] == os_key]
            conds = np.array([r["cond"] for r in sub])
            nrmses = np.array([r["nrmse"] for r in sub])
            rho, p = spearman_rho(conds, nrmses)
            per_snr_rho[os_key][snr_db] = {"rho": rho, "p": p}
            print(f"    SNR={snr_db:>4.0f}dB: ρ={rho:+.3f}, p={p:.4f}, "
                  f"NRMSE range=[{nrmses.min():.3e}, {nrmses.max():.3e}]")

    # ===== 判据 2: per-oversampling 全局 Spearman =====
    print("\n--- 判据 2: per-oversampling 全局 Spearman ---")
    rho_per_os: dict = {}
    for os_key in oversampling_keys:
        sub = [r for r in rows if r["oversampling"] == os_key]
        all_conds = np.array([r["cond"] for r in sub])
        all_nrmses = np.array([r["nrmse"] for r in sub])
        rho, p = spearman_rho(all_conds, all_nrmses)
        rho_per_os[os_key] = {"rho": rho, "p": p, "n_cases": len(sub)}
        print(f"  [{os_key}] ρ_all={rho:+.3f}, p={p:.4e}, n={len(sub)}")

    # ===== 表格: per-oversampling NRMSE 表 =====
    for os_key in oversampling_keys:
        print(f"\n--- NRMSE 表 [{os_key}] (trajectory × SNR) ---")
        header = f"  {'traj':<10} {'cond':>10}  " + "  ".join(
            [f"SNR{int(s):>2}" for s in snr_list])
        print(header)
        for name in trajectories:
            sub = sorted([r for r in rows
                          if r["trajectory"] == name and r["oversampling"] == os_key],
                         key=lambda r: -r["snr_db"])
            nrmses_str = "  ".join([f"{r['nrmse']:>5.3f}" for r in sub])
            print(f"  {name:<10} {sub[0]['cond']:>10.2f}  {nrmses_str}")

    # ===== verdict (基于 tight,因为它是命题真正适用区间) =====
    print("\n--- 判定 ---")
    rho_tight = rho_per_os["tight_K_plus_2"]["rho"]
    p_tight = rho_per_os["tight_K_plus_2"]["p"]
    rho_loose = rho_per_os["rand_50pct"]["rho"]

    pos_count_tight = sum(
        1 for snr_db in snr_list
        if per_snr_rho["tight_K_plus_2"][snr_db]["rho"] > 0
    )

    if rho_tight > 0.5 and p_tight < 0.01:
        verdict = "PASS"
        verdict_msg = (f"PASS: tight rho={rho_tight:+.3f} (p={p_tight:.2e}) > 0.5")
    elif rho_tight > 0.3:
        verdict = "WEAK_PASS"
        verdict_msg = (f"WEAK_PASS: tight rho={rho_tight:+.3f} positive but not significant; "
                       f"large-N extension recommended")
    elif rho_tight > 0:
        verdict = "WEAK"
        verdict_msg = (f"WEAK: tight rho={rho_tight:+.3f} weakly positive; "
                       f"rerun at N=1000 before drawing conclusions")
    else:
        verdict = "FAIL"
        verdict_msg = (f"FAIL: tight rho={rho_tight:+.3f} non-positive; "
                       f"reconsider the engineering relevance of the hypothesis")

    print(f"  {verdict}: {verdict_msg}")
    print(f"  tight per-SNR 正 ρ 比例: {pos_count_tight}/{len(snr_list)}")
    print(f"  loose ρ_all={rho_loose:+.3f} (作为 oversampling 高时区分压缩的对照)")

    # 保存
    out = Path(__file__).parent / "B3_stage1_results.json"
    out.write_text(json.dumps({
        "trajectories": trajectories,
        "snrs": snr_list,
        "N": n_target,
        "K": K,
        "oversampling_keys": oversampling_keys,
        "rows": rows,
        "per_traj_geometry": per_traj_geometry,
        "per_snr_rho": per_snr_rho,
        "rho_per_os": rho_per_os,
        "verdict": verdict,
    }, indent=2, default=str))
    print(f"\n  saved: {out}")

    return {
        "verdict": verdict,
        "rho_per_os": rho_per_os,
        "per_snr_rho": per_snr_rho,
    }


if __name__ == "__main__":
    stage1()
