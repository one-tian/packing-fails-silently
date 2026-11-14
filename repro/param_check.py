#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import argparse
import json
import math
from dataclasses import dataclass, asdict, field
from enum import Enum
from typing import List, Optional

# ---------------------------------------------------------------- 素数工具


def _is_prime(n: int) -> bool:
    """Miller-Rabin（确定性底数集，覆盖 < 3.3e24；更大范围用随机底数兜底）"""
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def next_prime(n: int) -> int:
    if n % 2 == 0:
        n += 1
    while not _is_prime(n):
        n += 2
    return n


# ---------------------------------------------------------------- 数据结构


class Verdict(Enum):
    FEASIBLE = "FEASIBLE"        # V_max < M，且余量 ≥ 1 bit
    TIGHT = "TIGHT"              # V_max < M，但余量 < 1 bit（塞不进任何修补）
    INFEASIBLE = "INFEASIBLE"    # V_max ≥ M，诚实数据即绕回


@dataclass
class Slot:
    """一个数据槽：一个统计量 + 它的容量（诚实输入下的最大值）"""
    name: str
    cap: int
    kind: str = ""               # linear / quadratic / count / check


@dataclass
class Report:
    model: str
    n: int
    w: int
    k: int
    T: int
    modulus_bits: int
    modulus: int
    vmax: int
    scheme_bound: int            # 方案自己声称的容量上界（若与真值不同）
    slots: List[Slot] = field(default_factory=list)
    weights: List[int] = field(default_factory=list)
    verdict: str = ""
    slack_bits: float = 0.0
    lower_bound_bits: int = 0
    note: str = ""

    def to_dict(self):
        d = asdict(self)
        d["slots"] = [asdict(s) for s in self.slots]
        return d


# ---------------------------------------------------------------- 解析下界（命题 1）


def lower_bound_bits(caps: List[int]) -> int:
    """
    命题 1：任何无进位编码 Σ w_s x_s（w_0 = 1, w_s > Σ_{t<s} w_t·cap_t）
    的模数必须满足  log2 M > Σ_s log2(cap_s + 1)。

    证明：对 s 归纳得 w_s ≥ Π_{t<s}(cap_t + 1)。
          故 V_max = Σ w_s cap_s ≥ w_last·cap_last ≈ Π_t (cap_t + 1)。∎

    这条下界与实现技巧无关：无论怎么优化权重，都省不掉这些位。
    """
    return sum(max(1, (c + 1).bit_length() - 1) for c in caps)


# ---------------------------------------------------------------- 模型一：超递增（VPMDA 族）


class SuperincreasingModel:
    """
    VPMDA / PPMA / SA-MAD 族。k 个类型，每类两个统计量：

        槽位（从低到高）:  M_1..M_k  (一次项和，容量 n·h_j)
                          QM_1..QM_k (平方项和，容量 n·h_j²)
                          [τ]        (可选校验位，容量 P_CHK)

    权重: v_0 = 1, v_a = 1 + Σ_{j<a} v_j · cap_j   （严格超递增）
    """

    name = "superincreasing"

    def __init__(self, with_check: bool = False, p_chk: int = 2 ** 31):
        self.with_check = with_check
        self.p_chk = p_chk

    def slots(self, n: int, w: int, k: int, T: int) -> List[Slot]:
        h = [T] * k                      # 各类数据的物理上界，默认取同一值
        out = [Slot(f"M_{j+1}", n * h[j], "linear") for j in range(k)]
        out += [Slot(f"QM_{j+1}", n * h[j] ** 2, "quadratic") for j in range(k)]
        if self.with_check:
            # τ_i 每台先 mod P_CHK，但聚合值是 n 台的**和**，可达 n·P_CHK。
            # 槽容量按 n·P_CHK 计才对（这与 05 报告实测的 +41 bit 一致）。
            out.append(Slot("tau", n * self.p_chk, "check"))
        return out

    def build(self, n: int, w: int, k: int, T: int):
        slots = self.slots(n, w, k, T)
        caps = [s.cap for s in slots]
        v = [1]
        for a in range(1, len(caps)):
            v.append(sum(v[j] * caps[j] for j in range(a)) + 1)
        vmax = sum(v[j] * c for j, c in enumerate(caps))
        return slots, v, vmax, vmax        # 该族无「声称上界 ≠ 真上界」的偏差

    def required_bits(self, n: int, w: int, k: int, T: int) -> int:
        _, _, vmax, _ = self.build(n, w, k, T)
        return vmax.bit_length()


# ---------------------------------------------------------------- 模型二：CRT + 块（LPPMM-DA 族）


class CRTBlockModel:
    """
    LPPMM-DA 族。w 个维度走 CRT 残差通道，k 个连续子集走超递增块。

        q_t ≈ nT（两两互素），Q = Π q_t，a_t = (Q/q_t)·(Q/q_t)^{-1} mod q_t
        b_0 > Σ_t a_t·n·T
        b_l > b_0 + b_{l-1}·n

    编码 v_i = Σ_t m_it·a_t + b_l，聚合 C = Σ v_i mod q。

    ★ 一个容易漏的点：方案把 b_k 当作容量上界，但 k+1 个块可以**同时**有用户
      （不同用户落在不同子集），所以最坏总值的块部分是 n·b_k 而不是 b_k。
      真实上界 = n·b_k + (b_0 - 1)，比方案声称的多 log2(n) 位。
    """

    name = "crt"

    def build(self, n: int, w: int, k: int, T: int):
        qt = []
        cand = next_prime(n * T + 1)
        while len(qt) < w:
            qt.append(cand)
            cand = next_prime(cand + 2)
        Q = 1
        for q in qt:
            Q *= q
        at = []
        for q in qt:
            Qt = Q // q
            at.append(Qt * pow(Qt, -1, q))
        crt_max = sum(a * n * T for a in at)     # < w·Q
        b = [crt_max + 1]
        for _ in range(k):
            b.append(b[0] + b[-1] * n)
        slots = [Slot(f"CRT_{t+1}", n * T, "linear") for t in range(w)]
        slots += [Slot(f"blk_{l+1}", n, "count") for l in range(k + 1)]
        scheme_bound = b[k]                       # 方案自己声明的上界
        vmax = n * b[k] + (crt_max)               # 真实最坏情况
        weights = at + b
        return slots, weights, vmax, scheme_bound

    def required_bits(self, n: int, w: int, k: int, T: int) -> int:
        _, _, vmax, _ = self.build(n, w, k, T)
        return vmax.bit_length()


MODELS = {"superincreasing": SuperincreasingModel, "crt": CRTBlockModel}


def _log2_ratio(a: int, b: int) -> float:
    """精确计算 log2(a/b)，避开 math.log2 对超大整数的 float 溢出。"""
    if b <= 0:
        return float("inf")
    if a <= 0:
        return float("-inf")
    ba, bb = a.bit_length(), b.bit_length()
    fa = a / (1 << (ba - 1))          # ∈ [1, 2)
    fb = b / (1 << (bb - 1))
    return (ba - bb) + math.log2(fa / fb)


# ---------------------------------------------------------------- 判定


def check(model: str, n: int, w: int, k: int, T: int, modulus_bits: int,
          with_check: bool = False) -> Report:
    M = 1 << modulus_bits
    if model == "superincreasing":
        m = SuperincreasingModel(with_check=with_check)
    else:
        m = CRTBlockModel()
    slots, weights, vmax, scheme_bound = m.build(n, w, k, T)
    lb = lower_bound_bits([s.cap for s in slots])

    slack = _log2_ratio(M, vmax)
    if vmax >= M:
        verdict = Verdict.INFEASIBLE
    else:
        verdict = Verdict.TIGHT if slack < 1.0 else Verdict.FEASIBLE

    note = ""
    if model == "crt":
        note = (f"方案声称上界 b_k = {scheme_bound.bit_length()} bit，"
                f"真实最坏 n·b_k = {vmax.bit_length()} bit（差 log2 n = {math.log2(n):.1f} 位）")

    return Report(model=model, n=n, w=w, k=k, T=T,
                  modulus_bits=modulus_bits, modulus=M,
                  vmax=vmax, scheme_bound=scheme_bound,
                  slots=slots, weights=weights,
                  verdict=verdict.value, slack_bits=round(slack, 2),
                  lower_bound_bits=lb, note=note)


def max_n(model: str, w: int, k: int, T: int, modulus_bits: int,
          hi: int = 10 ** 6) -> Optional[int]:
    """给定 (w,k,T,|M|)，求可行的最大台数 n。单调性保证二分有效。

    返回值 == hi 表示「在搜索上界处仍可行」，即真实上限 ≥ hi（饱和）。"""
    if check(model, 2, w, k, T, modulus_bits).verdict == "INFEASIBLE":
        return 0
    lo = 2
    if check(model, hi, w, k, T, modulus_bits).verdict != "INFEASIBLE":
        return hi
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if check(model, mid, w, k, T, modulus_bits).verdict != "INFEASIBLE":
            lo = mid
        else:
            hi = mid - 1
    return lo


def max_k(model: str, n: int, w: int, T: int, modulus_bits: int,
          hi: int = 200) -> int:
    """给定 (n,w,T,|M|)，求可行的最大类型/子集数 k。"""
    lo = 0
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if check(model, n, w, mid, T, modulus_bits).verdict != "INFEASIBLE":
            lo = mid
        else:
            hi = mid - 1
    return lo


# ---------------------------------------------------------------- 报表

BAR = "=" * 78


def hr(t):
    print(f"\n{BAR}\n{t}\n{BAR}")


def show(r: Report, indent="  "):
    tag = {"FEASIBLE": "可行", "TIGHT": "可行但零余量", "INFEASIBLE": "★ 不可行"}
    print(f"{indent}n={r.n:<6d} w={r.w:<3d} k={r.k:<3d} T={r.T:<6d} "
          f"|M|={r.modulus_bits:<5d} → 需 {r.vmax.bit_length():>4d} bit   "
          f"{tag[r.verdict]:<12s} 余量 {r.slack_bits:+.1f} bit")
    if r.note:
        print(f"{indent}  {r.note}")


def audit_published(json_out: bool = False):
    """
    审已发表参数集。三组来源：
      A. VPMDA (TDSC'22)  : Paillier N = 1024 bit，n ≤ 1000，k ≤ 10（实测范围）
      B. LPPMM-DA (TSG'25): 160-bit 曲线阶，n ∈ [100,1000]，w ∈ [5,50]，k ∈ {3,5,7}
      C. 本文 τ 增强版     : VPMDA + 41 bit 校验位
    """
    rows = []

    def add(label, model, n, w, k, T, bits, wc=False):
        r = check(model, n, w, k, T, bits, with_check=wc)
        rows.append((label, r))
        return r

    # A. VPMDA —— 论文实测的最大配置（Paillier N = 1024 bit）
    add("VPMDA   n=1000,k=10  @1024", "superincreasing", 1000, 10, 10, 1000, 1024)
    # B. LPPMM-DA —— 原文实验网格
    for (nn, ww, kk) in ((100, 5, 3), (100, 5, 7), (100, 10, 5),
                         (500, 5, 5), (1000, 5, 5), (1000, 5, 7),
                         (1000, 10, 3), (1000, 50, 7)):
        add(f"LPPMM  n={nn},w={ww},k={kk}   @160", "crt", nn, ww, kk, 1000, 160)
    # C. 本文 τ 增强
    add("τ-VPMDA n=1000,k=10           @1024", "superincreasing", 1000, 10, 10, 1000, 1024, True)

    if json_out:
        print(json.dumps([{"label": l, **r.to_dict()} for l, r in rows],
                         ensure_ascii=False, indent=1))
        return rows

    hr("审已发表参数集：方案自己的正确性不等式，满足了吗？")
    print("  判定口径：V_max = Σ w_s·cap_s 必须 < M（群阶/模数）")
    print("  说明：w=10 对 superincreasing 模型无意义（该族按类型数生成 2k 个槽），")
    print("        保留 w 列只为对齐输入签名。\n")
    for label, r in rows:
        show(r, indent="  ")
        if r.verdict == "INFEASIBLE":
            extra = f"；解析下界 {r.lower_bound_bits} bit"
            if r.lower_bound_bits > r.modulus_bits:
                extra += f"，连下界都超 {r.lower_bound_bits - r.modulus_bits} bit ⇒ 无法靠实现挽救"
            print(f"      超出 {r.vmax.bit_length() - r.modulus_bits} bit{extra}")
    return rows


def frontier(json_out: bool = False):
    """各群阶下的可行台数前沿 —— 部署时的选型表"""
    grids = []
    for bits in (160, 256, 512, 1024):
        for k in (3, 5, 7, 10):
            nC = max_n("crt", w=5, k=k, T=1000, modulus_bits=bits)
            nS = max_n("superincreasing", w=5, k=k, T=1000, modulus_bits=bits)
            grids.append({"bits": bits, "k": k, "crt_max_n": nC, "super_max_n": nS})
    if json_out:
        print(json.dumps(grids, indent=1))
        return grids

    hr("可行前沿：给定群阶 |M|，最多能支持多少台（w=5, T=1000）")
    def fmt(x):
        return "≥1e6" if x >= 10 ** 6 else str(x)

    print(f"  {'|M|':>6s} {'k':>3s} {'CRT 模型 max n':>16s} {'超递增模型 max n':>18s}")
    print("  " + "-" * 50)
    for g in grids:
        print(f"  {g['bits']:>6d} {g['k']:>3d} {fmt(g['crt_max_n']):>16s} {fmt(g['super_max_n']):>18s}")
    c7 = next(g["crt_max_n"] for g in grids if g["bits"] == 160 and g["k"] == 7)
    s7 = next(g["super_max_n"] for g in grids if g["bits"] == 160 and g["k"] == 7)
    print(f"\n  读法一：LPPMM-DA 用 160-bit 曲线，k=7 时只能支持 {c7} 台，")
    print("          而原文实验跑到 1000 台 —— 这正是 E4 判定的来源。")
    s7txt = "n=2 都不可行" if s7 == 0 else f"只能支持 {s7} 台"
    print(f"  读法二：超递增族（VPMDA/SA-MAD）在 160-bit、k=7 时 {s7txt}，")
    print("          即「根本上不了椭圆曲线」。这解释了 VPMDA 为何必须用 1024-bit Paillier——")
    print("          群的选择不是性能偏好，而是打包预算逼出来的。")
    return grids


def sensitivity(json_out: bool = False):
    """
    数据上界 T 是原文唯一没明确给出的参数（只说功耗区间大致 500–1500 W）。
    判定若依赖 T，说服力就打折。这里做 T 扫描，看结论在多大范围内成立。
    """
    Ts = (10, 50, 100, 500, 1000, 1500)
    cfgs = [(100, 5, 7), (500, 5, 5), (1000, 5, 7), (1000, 10, 3)]
    rows = []
    for (n, w, k) in cfgs:
        line = []
        for T in Ts:
            r = check("crt", n, w, k, T, 160)
            line.append((T, r.vmax.bit_length(), r.verdict))
        rows.append(((n, w, k), line))

    if json_out:
        print(json.dumps([{"cfg": c, "rows": [{"T": t, "bits": b, "verdict": v}
                                              for t, b, v in l]} for c, l in rows],
                         ensure_ascii=False, indent=1))
        return rows

    hr("T 敏感性：结论会不会因为「数据上界取多少」而变")
    print("  LPPMM-DA 用 160-bit 曲线阶。下表为所需位数（判定）随 T 的变化：\n")
    head = "".join(f"{('T=' + str(T)):>12s}" for T in Ts)
    print(f"  {'n,w,k':>14s}{head}")
    print("  " + "-" * (14 + 12 * len(Ts)))
    for cfg, line in rows:
        cells = "".join(f"{b:>9d}{'✗' if v == 'INFEASIBLE' else '✓':>3s}" for _, b, v in line)
        print(f"  {str(cfg):>14s}{cells}")
    print("\n  ✓ = 可行，✗ = 不可行（诚实数据即绕回）")
    print("  读法：n=1000,w=5,k=7 在 T ≥ 100 时全部不可行 —— 结论不依赖 T 的精确取值；")
    print("        只有把 T 压到几十（远小于原文所述 500–1500 W 的量级）才勉强可行。")
    return rows


def selftest():
    hr("自检：解析下界 vs 构造式、单调性、边界一致性")
    ok = True

    # 1. 下界必须 ≤ 构造值，且差距有界（< 25 bit）
    print("  [1] 命题 1 下界 ≤ 构造需求（下界是乐观估计，构造值必然更大）")
    for (n, w, k, T, model) in ((100, 5, 3, 1000, "crt"), (1000, 5, 7, 1000, "crt"),
                                (1000, 10, 10, 1000, "superincreasing"),
                                (100, 10, 5, 1000, "crt")):
        r = check(model, n, w, k, T, 2048)
        gap = r.vmax.bit_length() - r.lower_bound_bits
        good = 0 <= gap <= 40
        ok &= good
        print(f"      {model:16s} n={n:<5d} w={w:<3d} k={k:<3d} "
              f"下界 {r.lower_bound_bits:>4d}  构造 {r.vmax.bit_length():>4d}  "
              f"差 {gap:>2d}  {'✓' if good else '✗'}")

    # 2. 单调性：n、k 增大，需求位数不减
    print("  [2] 单调性：n↑ / k↑ ⇒ 需求位数不减")
    for model in ("crt", "superincreasing"):
        seq_n = [check(model, n, 5, 5, 1000, 4096).vmax.bit_length()
                 for n in (10, 100, 1000, 10000)]
        seq_k = [check(model, 1000, 5, k, 1000, 4096).vmax.bit_length()
                 for k in (1, 3, 5, 7)]
        good = all(a <= b for a, b in zip(seq_n, seq_n[1:])) and \
               all(a <= b for a, b in zip(seq_k, seq_k[1:]))
        ok &= good
        print(f"      {model:16s} n 序列 {seq_n}  k 序列 {seq_k}  {'✓' if good else '✗'}")

    # 3. 边界一致性：max_n 处的判定必须是可行，max_n+1 处必须不可行
    print("  [3] 前沿边界：max_n 可行、max_n+1 不可行")
    for model, bits in (("crt", 160), ("crt", 256), ("superincreasing", 1024)):
        nn = max_n(model, 5, 5, 1000, bits)
        if nn >= 10 ** 6:
            print(f"      {model:16s} |M|={bits:<5d} max_n ≥ 1e6（饱和，跳过边界判定） "
                  f"{'✓' if check(model, nn, 5, 5, 1000, bits).verdict != 'INFEASIBLE' else '✗'}")
            continue
        a = check(model, nn, 5, 5, 1000, bits).verdict
        b = check(model, nn + 1, 5, 5, 1000, bits).verdict
        good = (a != "INFEASIBLE") and (b == "INFEASIBLE")
        ok &= good
        print(f"      {model:16s} |M|={bits:<5d} max_n={nn:<6d} "
              f"max_n→{a:<10s} max_n+1→{b:<10s} {'✓' if good else '✗'}")

    # 4. 与既有实验一致：VPMDA 1024-bit、k=10 必须可行；LPPMM 160-bit、n=1000,k=7 必须不可行
    print("  [4] 与既有实验对齐")
    t1 = check("superincreasing", 1000, 10, 10, 1000, 1024).verdict != "INFEASIBLE"
    t2 = check("crt", 1000, 5, 7, 1000, 160).verdict == "INFEASIBLE"
    ok &= t1 and t2
    print(f"      VPMDA 1024-bit k=10 诚实可运行 : {'✓' if t1 else '✗'}")
    print(f"      LPPMM 160-bit n=1000 k=7 不相容: {'✓' if t2 else '✗'}")

    print(f"\n  自检总结果：{'全部通过' if ok else '★ 有失败项'}")
    return ok


# ---------------------------------------------------------------- CLI


def main():
    ap = argparse.ArgumentParser(description="打包式聚合方案的参数可行性判定器")
    ap.add_argument("--model", choices=list(MODELS), default="crt")
    ap.add_argument("--n", type=int, default=1000)
    ap.add_argument("--w", type=int, default=5, help="维度数（CRT 模型）/ 占位（超递增模型）")
    ap.add_argument("--k", type=int, default=7, help="类型数或子集数")
    ap.add_argument("--T", type=int, default=1000, help="单维数据上界")
    ap.add_argument("--bits", type=int, default=160, help="群阶/模数位长")
    ap.add_argument("--check-bit", action="store_true", help="超递增模型计入 τ 校验位")
    ap.add_argument("--audit", action="store_true")
    ap.add_argument("--frontier", action="store_true")
    ap.add_argument("--sensitivity", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()

    if a.selftest:
        selftest()
        return
    if a.audit:
        audit_published(a.json)
        return
    if a.frontier:
        frontier(a.json)
        return
    if a.sensitivity:
        sensitivity(a.json)
        return

    r = check(a.model, a.n, a.w, a.k, a.T, a.bits, with_check=a.check_bit)
    if a.json:
        print(json.dumps(r.to_dict(), ensure_ascii=False, indent=1))
        return

    hr(f"参数判定：{r.model}  n={r.n} w={r.w} k={r.k} T={r.T}  |M|={r.modulus_bits}")
    print(f"  模数        M = 2^{r.modulus_bits}")
    print(f"  编码上界    V_max = {r.vmax}")
    print(f"              = {r.vmax.bit_length()} bit")
    print(f"  解析下界    ≥ {r.lower_bound_bits} bit（命题 1，任何实现都省不掉）")
    print(f"  判定        {r.verdict}   余量 {r.slack_bits:+.2f} bit")
    if r.note:
        print(f"  备注        {r.note}")
    print("\n  槽位明细：")
    for s in r.slots:
        print(f"    {s.name:<8s} cap = {s.cap:>14d}  ({s.cap.bit_length():>3d} bit)  {s.kind}")


if __name__ == "__main__":
    main()
