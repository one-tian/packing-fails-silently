#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import math
import random
import time

from overflow_demo import PackedAgg, P_CHK, hr
import param_check as pc

RNG = random.Random(20261113)
H1, H2 = 1000, 500          # 两类数据的物理上界
BOUNDS = (H1, H2)


# ================================================================ 分块聚合
class Chunked:
    """把 n 台切成 ceil(n/b) 个块，每块是一个独立的超递增打包域。"""

    def __init__(self, n, b, k=2, bounds=BOUNDS, bits=256):
        self.n, self.b, self.k = n, b, k
        self.nb = (n + b - 1) // b
        self.P = PackedAgg(n=b, k=k, bounds=bounds, with_check=True, bits=bits)

    def block_index(self, i):
        return i // self.b

    def segments(self, data):
        for blk in range(self.nb):
            yield blk, data[blk * self.b:(blk + 1) * self.b]

    # ---------------------------------------------------------- 全流程
    def run(self, rows, poisons=()):
        """poisons=[(i,j,V)]：第 i 台第 j 类改报 V。返回逐块结果 + 全局统计。"""
        data = [list(r) for r in rows]
        for i, j, V in poisons:
            data[i][j] = V
        blocks = []
        for blk, seg in self.segments(data):
            q = sum(self.P.encode(r) for r in seg)
            Q = self.P.cipher.dec(self.P.cipher.enc(q, 0))
            M, QM, tau = self.P.peel_full(Q)
            truthM = [sum(r[j] for r in seg) for j in range(self.k)]
            truthQM = [sum(r[j] ** 2 for r in seg) for j in range(self.k)]
            blocks.append(dict(
                blk=blk, lo=blk * self.b, hi=blk * self.b + len(seg),
                M=M, QM=QM,
                faithful=(M == truthM and QM == truthQM),
                ok_chk=self.P.verify(M, QM, tau),
            ))
        return blocks

    def global_stats(self, blocks, only_ok=False):
        """把各块剥离结果相加得全局统计；only_ok=True 时只累加通过校验的块。"""
        M = [0] * self.k
        QM = [0] * self.k
        cover = 0
        for b in blocks:
            if only_ok and not b["ok_chk"]:
                continue
            cover += b["hi"] - b["lo"]
            for j in range(self.k):
                M[j] += b["M"][j]
                QM[j] += b["QM"][j]
        return M, QM, cover


def block_q(P, seg):
    return sum(P.encode(r) for r in seg)


def peel_status(P, seg, q=None):
    if q is None:
        q = block_q(P, seg)
    M, QM, _ = P.peel_full(q)
    ok = (M == [sum(r[j] for r in seg) for j in range(P.k)]
          and QM == [sum(r[j] ** 2 for r in seg) for j in range(P.k)])
    return ok, M, QM


def min_carry_V(P, seg, colluders, lo=0, hi=None):
    """使块聚合刚好越容量（剥离不再忠实）的最小同值毒化 V（作用在第 1 类）。"""
    if hi is None:
        hi = 64 * H1
    # 先确保 hi 确实触发（否则说明模型假设有误，显式报错而不是静默返回）
    seg2 = [list(r) for r in seg]
    for i in colluders:
        seg2[i][0] = hi
    assert not peel_status(P, seg2)[0], "上界未触发进位，需增大 hi"
    while hi - lo > 1:
        mid = (lo + hi) // 2
        seg2 = [list(r) for r in seg]
        for i in colluders:
            seg2[i][0] = mid
        if peel_status(P, seg2)[0]:
            lo = mid
        else:
            hi = mid
    return hi


def fresh_rows(n, rng=None):
    r = rng or RNG
    return [[r.randrange(0, H1), r.randrange(0, H2)] for _ in range(n)]


# ================================================================ P0
def part0():
    hr("P0 · 可辨识性极限：一个打包域的输出不决定个体读数")
    print("  CC 能看到的东西只有 2k 个统计量（外加 τ 的一致性）。若两组不同的个体读数")
    print("  给出同一组统计量，CC 在信息论上就无法区分 —— 与实现无关。")
    print()
    P = PackedAgg(n=3, k=1, bounds=(1000, 1000), with_check=True, bits=256)
    A = [[1], [5], [6]]
    B = [[2], [3], [7]]
    print("  构造：3 台 1 类数据，两组读数")
    print(f"    A = {[r[0] for r in A]}   Σm={sum(r[0] for r in A)}  Σm²={sum(r[0]**2 for r in A)}")
    print(f"    B = {[r[0] for r in B]}   Σm={sum(r[0] for r in B)}  Σm²={sum(r[0]**2 for r in B)}")
    qa = sum(P.encode(r) for r in A)
    qb = sum(P.encode(r) for r in B)
    cta = P.cipher.enc(qa, 0)
    ctb = P.cipher.enc(qb, 0)
    print(f"\n    打包整数相同？ {qa == qb}     密文逐字节相同？ {cta == ctb}")
    print(f"    剥离结果：A → {P.peel_full(qa)[:2]}   B → {P.peel_full(qb)[:2]}")
    print(f"    τ 校验：A {'通过' if P.verify(*P.peel_full(qa)) else '失败'}，"
          f"B {'通过' if P.verify(*P.peel_full(qb)) else '失败'}")
    print()
    print("  ⇒ 单域内『哪一台报了什么』本就不被承诺，协议承诺的是统计量本身。")
    print("    因此『定位到单台』不可能靠一个域的输出来完成，只能靠缩小域（分块）")
    print("    或增加额外视图（重放）。这是 P4 判据的来源。")

    print()
    print("  附带的边界（必须写进 threats to validity）：")
    print("    只要 2k 个矩不变量相同，任意『矩等价重分配』都对 CC 不可见，")
    print("    这不是打包缺陷，而是『只发布 2k 个统计量』这一设计的固有语义边界。")


# ================================================================ P1
def part1():
    hr("P1 · 正确性：分块结果之和 == 全局结果（诚实数据）")
    n, k, b = 256, 2, 8
    rows = fresh_rows(n)
    C = Chunked(n, b, k)
    blocks = C.run(rows)

    S = PackedAgg(n=n, k=k, bounds=BOUNDS, with_check=True, bits=256)
    q = sum(S.encode(r) for r in rows)
    Mg, QMg, taug = S.peel_full(S.cipher.dec(S.cipher.enc(q, 0)))
    okg = S.verify(Mg, QMg, taug)

    Mc, QMc, cover = C.global_stats(blocks)
    print(f"  n={n}, b={b} → {C.nb} 块，每块 {b} 台；共享 1 个 Paillier 公钥与 1 组权重")
    print(f"  逐块 τ 通过：{sum(b_['ok_chk'] for b_ in blocks)}/{C.nb}，"
          f"逐块剥离忠实：{sum(b_['faithful'] for b_ in blocks)}/{C.nb}")
    print(f"  全局（单域）  M={Mg}  QM={QMg}  τ={'通过' if okg else '失败'}")
    print(f"  分块累加      M={Mc}  QM={QMc}  覆盖 {cover}/{n}")
    print(f"  两者逐项相等？ {Mc == Mg and QMc == QMg}")
    mean1 = Mc[0] / n
    var1 = QMc[0] / n - mean1 ** 2
    print(f"  类1 均值={mean1:.2f} 方差={var1:.2f}（分块不改变统计量，只是换了解包位置）")
    print()
    print("  ⇒ 分块对统计结果零影响；代价全在通信与解密次数上（见 P6）。")


# ================================================================ P2
def part2():
    hr("P2 · 隔离：最小触发攻击下的损失范围")
    n, k = 256, 2
    rows = fresh_rows(n)
    bad = 17
    single = PackedAgg(n=n, k=k, bounds=BOUNDS, with_check=True, bits=256)
    Mg, _, _ = single.peel_full(sum(single.encode(r) for r in rows))
    mean_true = Mg[0] / n
    print("  公平比较的前提：每个 b 先用【该块自己的】触发门槛 V*(b)，再乘 1.2 攻击。")
    print("  （用固定 V 会漏触发：b=32 时门槛已到 4.6× 上界，3× 根本不算进位污染。）")
    print()
    print(f"  {'b':>5s} {'块数':>5s} {'V*/h':>6s} {'攻击/h':>7s} {'失败块':>6s} "
          f"{'丢失覆盖':>8s} {'可出全局数?':>10s} {'均值误差':>9s}")
    print("  " + "-" * 70)
    for b in (1, 2, 4, 8, 16, 32, 64, 128, 256):
        C = Chunked(n, b, k)
        blk = bad // b
        seg = [list(r) for r in rows[blk * b:(blk + 1) * b]]
        Vs = min_carry_V(C.P, seg, [bad - blk * b], hi=200 * H1)
        V = int(1.2 * Vs)
        blocks = C.run(rows, [(bad, 0, V)])
        fail = [x for x in blocks if not x["ok_chk"]]
        Mc, _, cover = C.global_stats(blocks, only_ok=True)
        can = "是" if cover else "否（全损）"
        err = (Mc[0] / cover - mean_true) if cover else float("nan")
        print(f"  {b:>5d} {C.nb:>5d} {Vs/H1:>6.2f} {V/H1:>7.2f} {len(fail):>6d} "
              f"{100*(n-cover)/n:>7.1f}% {can:>10s} {err:>9.2f}")
    print()
    print("  读法：无论 b 多大，一次触发只废掉【一个块】的 2k 个统计量；差别在覆盖面。")
    print("        b=1..8 → 丢 1 台到 8 台的数据，其余块照常出数，均值误差 ~1；")
    print("        b=256（=单域，即 VPMDA 的现状）→ 失败块就是全集，一个数都出不来。")
    print("        注意误差符号与量级：丢块带来的是【覆盖率损失】而非污染，CC 可以如实报告覆盖。")
    print()
    print("  合谋分散到不同块（c 台各占一块、各按该块门槛的 1.2 倍上报）：")
    print(f"  {'c':>3s} {'b=8 失败块/覆盖':>16s} {'b=32':>12s} {'b=256':>12s}")
    print("  " + "-" * 48)
    for c in (1, 2, 4, 8):
        cells = []
        for b in (8, 32, 256):
            C = Chunked(n, b, k)
            idx = RNG.sample(range(n), c)
            seg = [list(r) for r in rows[0:b]]
            Vs = min_carry_V(C.P, seg, [0], hi=200 * H1)
            blocks = C.run(rows, [(i, 0, int(1.2 * Vs)) for i in idx])
            nf = sum(1 for x in blocks if not x["ok_chk"])
            cov = sum(x["hi"] - x["lo"] for x in blocks if x["ok_chk"])
            cells.append(f"{nf}/{100*(1-cov/n):.1f}%")
        print(f"  {c:>3d} {cells[0]:>16s} {cells[1]:>12s} {cells[2]:>12s}")
    print("  ⇒ 分散毒化时失败块数 ≈ min(c, 块数)，损失覆盖 ≈ c·b，且 c·b ≤ n 自动成立：")
    print("    分块给出损失上界 min(c·b, n)，单域连『少损一点』这个选项都没有。")


# ================================================================ P3
def part3():
    hr("P3 · 触发门槛：单台要报多大才能引爆一个 b 台块")
    print("  判据：块内一台上报 V、其余诚实（合计 μ），越界条件为")
    print("        V + μ > b·h          （一次项槽）  或  V² + Σm² > b·h²  （平方项槽）")
    print("        ⇒ 平方项槽先爆，V* ≈ h·√(b − Σ(m/h)²) ≈ h·√(2b/3)（均匀数据）")
    print("  下列实测在整数域直接剥离（Paillier 解密是精确还原整数，等价；已抽样核对）")
    print()
    # 等价性核对
    b = 16
    C = Chunked(64, b, 2)
    seg = fresh_rows(b)
    q = block_q(C.P, seg)
    Q = C.P.cipher.dec(C.P.cipher.enc(q, 0))
    print(f"  等价性抽样：b={b} 整数剥离 == 密文剥离？ {C.P.peel_full(q) == C.P.peel_full(Q)}")
    print()
    print(f"  {'b':>5s} {'样本':>4s} {'V*/h 实测':>10s} {'√(2b/3)':>9s} {'首爆槽':>8s} "
          f"{'沉默谎报上限':>12s}")
    print("  " + "-" * 60)
    for b in (1, 2, 4, 8, 16, 32, 64, 128, 256):
        if b == 1:
            print(f"  {b:>5d} {'—':>4s} {1.0:>10.2f} {0.82:>9.2f} {'—':>8s} "
                  f"{'1.0×（任何越界即触发）':>12s}")
            continue
        C = Chunked(max(b, 8), b, 2)
        vals = []
        slot_hit = {"M": 0, "QM": 0}
        T = 8 if b >= 128 else 16
        for _ in range(T):
            seg = fresh_rows(b)
            V = min_carry_V(C.P, seg, [0], hi=200 * H1)
            vals.append(V / H1)
            mu = sum(r[0] for r in seg[1:])
            mu2 = sum(r[0] ** 2 for r in seg[1:])
            slot_hit["M" if V + mu > b * H1 and V * V + mu2 <= b * H1 * H1 else "QM"] += 1
        vmean = sum(vals) / len(vals)
        model = math.sqrt(2 * b / 3)
        first = "QM" if slot_hit["QM"] >= slot_hit["M"] else "M"
        print(f"  {b:>5d} {T:>4d} {vmean:>10.2f} {model:>9.2f} {first:>8s} "
              f"{vmean:>11.1f}×")
    print()
    print("  这个门槛有两个读法，方向相反，论文里必须同时给：")
    print("  ① 安全读法（有利）：低于 V* 的谎报会被【静默接受】—— 它没超容量，剥离如实反映，")
    print("     τ 也自洽，CC 看到的是一组『正常』统计量。所以 V*/h 就是该块的【漏检上限】：")
    print("     b=256（单域）时，一台报 13 倍上界也不会触发任何信号，被直接计入均值；")
    print("     b=8 时这个上限降到 2.4 倍，b=2 时 1.3 倍。分块把『可静默谎报的幅度』压下来了。")
    print("  ② 可用性读法（不利）：门槛低意味着真实但超界的测量（传感器故障、尖峰）更容易")
    print("     把整块打成失败，从而丢一块数据。这是把 ① 的收益折回去的代价。")
    print()
    print("  ⇒ 与 √(2b/3) 吻合（偏差来自样本均值 μ 的波动）。b 决定『容忍多大谎报』，")
    print("    这是比『能否定位』更容易被审稿人接受的量化论点。")
    print()
    # 合谋摊薄
    print("  合谋摊薄（b=64，c 台各报同值 V）：")
    print(f"  {'c':>3s} {'V*/h 实测':>10s} {'√(2b/(3c))':>11s} {'单台越界倍数下降':>16s}")
    C = Chunked(256, 64, 2)
    base = None
    for c in (1, 2, 4, 8, 16):
        vals = []
        for _ in range(10):
            seg = fresh_rows(64)
            coll = RNG.sample(range(64), c)
            vals.append(min_carry_V(C.P, seg, coll, hi=200 * H1) / H1)
        v = sum(vals) / len(vals)
        base = base or v
        print(f"  {c:>3d} {v:>10.2f} {math.sqrt(2*64/(3*c)):>11.2f} "
              f"{100*(1 - v/base):>15.1f}%")
    print()
    print("  ⇒ 与 06·C1 同构：摊薄按 1/√c（平方项槽）而非 1/c，合谋收益递减；")
    print("    且 c ≤ b，所以分块给合谋设了上限：单块内最多摊薄到 h·√(2/3)。")


# ================================================================ P4
def bs_locate(P, block, culprit, V, b):
    """
    块内二分重放。culprit 为块内相对下标，V 为该台的越界上报值。
    返回 (轮数, 最终区间, 是否丢失目标)。
    不变量：目标始终在 [lo,hi) 内。若某次子集含目标却不越界（V 不够大），
    搜索会把目标划到区间外 —— 这正是失效形态，显式检出而不是静默错答。
    """
    lo, hi = 0, b
    rounds = 0
    while hi - lo > 1:
        mid = (lo + hi) // 2
        rounds += 1
        seg = [list(r) for r in block[lo:mid]]
        if lo <= culprit < mid:
            seg[culprit - lo][0] = V
        overflowed = not peel_status(P, seg)[0]
        if overflowed:
            hi = mid
        else:
            lo = mid
        if not (lo <= culprit < hi):
            return rounds, (lo, hi), True
    return rounds, (lo, hi), False


def part4():
    hr("P4 · 定位分辨率：块内二分重放能细化到单台吗")
    print("  判据（平方项槽，容量恒为 b·h²，与子集大小无关）：")
    print("    块触发：V² > b·h² − Σ_all ≈ (2/3)b·h²      ⇒ V* ≈ h·√(2b/3)（P3 已测）")
    print("    子集 S（s 台，含毒化台）仍越界：V² > b·h² − Σ_S ≈ (b − (s−1)/3)·h²")
    print("    ⇒ 缩到单台（s=1）需 V ≳ h·√b，即约 1.22 × 触发门槛。")
    print("    ⚠ 与『V > (b−s+1)h』的一次项直觉完全不同：后者只在一次项槽绑定时成立，")
    print("      而本族方案里平方项槽总是先爆（05 已实测），故必须用平方项判据。")
    print("    ⚠ 关键推论：门槛只比触发高 22%，所以【最小触发攻击】下二分第一步（s=b/2）")
    print("      就已经不越界 —— 定位会立刻退化到块级。能否细化到台，取决于攻击者越界多少。")
    print()
    n = 256
    print("  块级定位（失败块的下标直接给出候选集，0 轮交互）：")
    print(f"  {'b':>5s} {'V*/h':>6s} {'攻击/h':>7s} {'块失败率':>8s} {'命中率':>7s}")
    print("  " + "-" * 42)
    for b in (8, 16, 32, 64):
        C = Chunked(n, b, 2)
        hits = fails = 0
        vsum = 0.0
        T = 120
        for _ in range(T):
            rows = fresh_rows(n)
            i = RNG.randrange(n)
            blk = i // b
            seg = [list(r) for r in rows[blk * b:(blk + 1) * b]]
            Vs = min_carry_V(C.P, seg, [i - blk * b], hi=200 * H1)
            vsum += Vs / H1
            blocks = C.run(rows, [(i, 0, int(1.2 * Vs))])
            fail = [x for x in blocks if not x["ok_chk"]]
            fails += bool(fail)
            hits += (len(fail) == 1 and fail[0]["lo"] <= i < fail[0]["hi"])
        print(f"  {b:>5d} {vsum/T:>6.2f} {1.2*vsum/T:>7.2f} {100*fails/T:>7.0f}% "
              f"{100*hits/T:>6.0f}%")
    print("  ⇒ 一旦块失败，失败块必然是含毒化台的那一块（命中 100%），且定位为 0 轮。")
    print()

    print("  块内二分（候选集 b → 1；V 以「触发门槛的倍数」表示，便于跨 b 比较）：")
    print(f"  {'b':>4s} {'×V*':>5s} {'中位轮数':>8s} {'最终宽度':>8s} {'命中率':>7s} "
          f"{'丢失目标':>8s}  判定")
    print("  " + "-" * 66)
    for b in (8, 16, 32, 64):
        C = Chunked(n, b, 2)
        # 该 b 的触发门槛（取若干样本均值）
        ths = []
        for _ in range(10):
            seg = fresh_rows(b)
            ths.append(min_carry_V(C.P, seg, [0], hi=200 * H1))
        thr = sum(ths) / len(ths)
        for mult in (1.05, 1.2, 1.41, 2.0, 4.0):
            T = 60
            okc = lostc = 0
            widths = []
            rounds_l = []
            for _ in range(T):
                rows = fresh_rows(n)
                i = RNG.randrange(n)
                blk = i // b
                block = [list(r) for r in rows[blk * b:(blk + 1) * b]]
                V = int(mult * thr)
                rounds, (lo, hi), lost = bs_locate(C.P, block, i - blk * b, V, b)
                rounds_l.append(rounds)
                widths.append(hi - lo)
                lostc += lost
                okc += (not lost and (hi - lo) == 1)
            rounds_l.sort()
            med = rounds_l[len(rounds_l) // 2]
            verdict = "可靠定位到单台" if okc / T > 0.9 else (
                "部分收敛" if okc / T > 0.2 else "失效（退化为块级）")
            print(f"  {b:>4d} {mult:>5.2f} {med:>8d} {sum(widths)/T:>8.1f} "
                  f"{100*okc/T:>6.0f}% {100*lostc/T:>7.0f}%  {verdict}")
        print()
    print("  ⇒ 实测与判据一致：V 到触发门槛的 ~1.4 倍即可稳定缩到单台，轮数 = ⌈log2 b⌉；")
    print("    低于该值则子集不再越界、搜索中途丢失目标 —— 此时有效分辨率退化为 b。")
    print()

    def overflow(items, V):
        seg = []
        for r, isc in items:
            rr = list(r)
            if isc:
                rr[0] = V
            seg.append(rr)
        return not peel_status(C16.P, seg)[0]

    def bs_over(items, V):
        """在 items 上二分；返回命中的下标（该位置是毒化台则有效），否则 None。"""
        if len(items) < 2 or not overflow(items, V):
            return None
        lo, hi = 0, len(items)
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if overflow(items[lo:mid], V):
                hi = mid
            else:
                lo = mid
        return lo if items[lo][1] else None

    print("  块内合谋：两区制对照（b=16，c 台各报同值 V）")
    print("    区制 A『刚好触发』：V = c 台摊薄门槛 × 1.02 —— 正是 06·C3 构造的形态；")
    print("    区制 B『远超门槛』：V = 单台门槛 × 1.4 —— 攻击者不计隐蔽性。")
    print(f"  {'c':>3s} {'区制':>7s} {'V/h':>6s} {'V/单台门槛':>10s} {'一遍命中':>8s} "
          f"{'找齐 c 台':>9s} {'残留宽度':>8s}")
    print("  " + "-" * 62)
    C16 = Chunked(n, 16, 2)
    for c in (1, 2, 3):
        for tag, mult, ref in (("A 刚好", 1.02, "c 台"), ("B 远超", 1.4, "单台")):
            T = 40
            one = both = 0
            widths = []
            vsum = 0.0
            for _ in range(T):
                rows = fresh_rows(n)
                blk = RNG.randrange(n // 16)
                culprits = set(RNG.sample(range(16), c))
                block = [list(r) for r in rows[blk * 16:(blk + 1) * 16]]
                thr1 = min_carry_V(C16.P, block, [0], hi=200 * H1)
                thr_c = min_carry_V(C16.P, block, sorted(culprits), hi=200 * H1)
                V = int((thr_c if mult < 1.1 else thr1) * mult)
                vsum += V / H1
                items = [(block[i], i in culprits) for i in range(16)]
                i1 = bs_over(items, V)
                if i1 is not None:
                    one += 1
                rest = [it for k, it in enumerate(items) if k != i1]
                if i1 is not None and c > 1:
                    i2 = bs_over(rest, V)
                    if i2 is not None:
                        both += 1
                        widths.append(15 - 1)
                    else:
                        widths.append(len(rest))
                else:
                    both += (c == 1 and i1 is not None)
                    widths.append(1 if i1 is not None else 16)
            ref_v = vsum / T
            print(f"  {c:>3d} {tag:>7s} {ref_v:>6.2f} {ref_v:>10.2f} "
                  f"{100*one/T:>7.0f}% {100*both/T:>8.0f}% {sum(widths)/T:>8.1f}")
        print()
    print("  ⇒ 三条读法，缺一不可：")
    print("    ① 最小触发（区制 A）时，连【单源】都只能定位到块（命中 8%）：二分第一步的子集")
    print("       只剩一半质量，已不越界，搜索立刻失去方向。攻击者因此有明确最优策略 ——")
    print("       把越界量压到刚好触发：省暴露、且把定位锁死在 b。")
    print("    ② 越界量抬到 1.2–1.4× 触发门槛后，单源与多源都能逐台摘除（多源需 c 遍，")
    print("       每遍 ⌈log2 b⌉ 轮）；此时定位精度是攻击者『自己送出来的』。")
    print("    ③ 因此协议能承诺的是【最坏情况分辨率 = b】，块内细化属于 best-effort。")
    print("       b=n 时这个承诺就是 n（= 无法定位）；分块把它压到 b，这是可写进定理的部分。")


# ================================================================ P5
def part5():
    hr("P5 · 掉线：零和掩码要求块内全员到齐")
    print("  VPMDA 的掩码满足 Σg_i = −g_0，缺一台则掩码消不掉、整域不可解。")
    print("  分块后这条约束被限制在块内：一块缺人只废这一块。")
    print("  模型：每台独立以概率 p 缺席；块完整 ⇔ 块内全员到齐，概率 (1−p)^b。")
    print()
    n = 1000
    print(f"  n={n}，补报量 = 失败块数 × b（只需这些台重发），可用统计量占比 = 完整块覆盖/ n")
    print()
    print(f"  {'p':>5s} {'b':>5s} {'块数':>5s} {'期望可用占比':>12s} {'期望补报台数':>13s} "
          f"{'单域对照可用占比':>16s}")
    print("  " + "-" * 70)
    for p in (0.01, 0.05):
        single = (1 - p) ** n
        for b in (1, 2, 4, 8, 16, 32, 64, 128, 1000):
            nb = math.ceil(n / b)
            comp = (1 - p) ** b
            usable = comp                      # 完整块覆盖的期望比例
            repair = (1 - comp) * nb * b
            print(f"  {p:>5.0%} {b:>5d} {nb:>5d} {100*usable:>11.1f}% "
                  f"{repair:>13.0f} {100*single:>15.4f}%")
        print()
    print("  ⇒ 单域在 p=1% 时可用率已跌到 (1−p)^n ≈ 0.004%，分块把它抬到 (1−p)^b：")
    print("    b=8 时 92%，b=32 时 19%。补报量 ≈ n·b·p（小 p 展开），b 越小补报越省。")
    print("    ⇒ 掉线维度上『小块全面占优』，唯一的对手是 P6 的通信开销。")
    print()
    print("  注：这不是『容错』，而是『故障域隔离 + 按需补报』。真正的容错（缺人仍可算）")
    print("      要靠 Shamir 门限等机制，与本文的打包层正交，不在此声称。")


# ================================================================ P6
def part6():
    hr("P6 · 开销前沿：通信/解密次数 ∝ n/b")
    print("  每块一个密文 ⇒ 密文数 = ⌈n/b⌉，CC 解密次数 = ⌈n/b⌉（原方案恒为 1）。")
    print("  每块载荷位宽由 (b, k, h) 决定 —— b 变小，单块预算变小，可换更小的模数。")
    print("  下表取 k=10、T=1000、n=1000（VPMDA 的最大实验配置），校验位按 b·P_CHK 计。")
    print()
    n, k, T = 1000, 10, 1000
    r0 = pc.check("superincreasing", n, k, k, T, 4096, with_check=True)
    bits_single = r0.vmax.bit_length()
    print(f"  单域基准：b=n=1000 → 1 个密文、{bits_single} bit 载荷（需 1024 bit 模数）")
    print()
    print(f"  {'b':>5s} {'密文数':>6s} {'每块载荷':>9s} {'总载荷 bit':>11s} {'倍数':>6s} "
          f"{'解密次数':>8s} {'定位精度':>8s} {'触发门槛':>9s}")
    print("  " + "-" * 76)
    for b in (1000, 500, 250, 125, 50, 25, 10, 5, 1):
        r = pc.check("superincreasing", b, k, k, T, 4096, with_check=True)
        bits = r.vmax.bit_length()
        nb = math.ceil(n / b)
        total = nb * bits
        thr = math.sqrt(2 * b / 3) if b > 1 else 1.0
        print(f"  {b:>5d} {nb:>6d} {bits:>9d} {total:>11d} {total/bits_single:>5.1f}x "
              f"{nb:>8d} {b:>8d} {thr:>8.1f}x")
    print()
    print("  ⇒ 通信/解密成本 ∝ n/b，与定位精度 b 严格对立。两条曲线只在 b 上相遇：")
    print("    b=n 是 VPMDA（1 个密文、零定位能力）；b=1 是逐台加密（无隐私、无压缩）。")
    print("    分块把这条直线上的每一点都变成可选设计点 —— 这是它相对原方案的定位。")
    print()
    # 选 b 的可行域
    print("  设计规则（两条约束夹出可行区间）：")
    print("    · 通信上限 C 个密文  ⇒  b ≥ n/C")
    print("    · 补报上限 R·n 台    ⇒  b ≤ R/p        （小 p 展开：补报 ≈ n·b·p）")
    print("    · 匿名集大小 = b     ⇒  b ≥ 隐私下限")
    print()
    print(f"  {'p':>5s} {'R=5% C=20':>10s} {'R=5% C=100':>11s} {'R=20% C=20':>11s} {'R=20% C=100':>12s}")
    print("  " + "-" * 54)
    for p in (0.001, 0.005, 0.01, 0.05):
        cells = []
        for R, Cmax in ((0.05, 20), (0.05, 100), (0.20, 20), (0.20, 100)):
            lo = math.ceil(n / Cmax)
            hi = int(R / p)
            cells.append(f"{lo}–{hi}" if lo <= hi else "空")
        print(f"  {p:>5.2%} {cells[0]:>10s} {cells[1]:>11s} {cells[2]:>11s} {cells[3]:>12s}")
    print()
    print("  ⇒ 三件事一起读：")
    print("    ① 补报预算 5% 时，p≥0.5% 就基本无解 —— 分块的可用性收益被『整块重跑』吃掉；")
    print("       放到 20% 后区间重新打开（p=0.5%、C=100 → b∈[10,40]）。")
    print("    ② 想让 b 大（省通信）就必须容忍高补报；想让 b 小（强隔离）就得多发密文。")
    print("    ③ 空集本身就是结论：给定 (n, p, C, R) 可以事前判定该场景是否可做，")
    print("       这正是 param_check.py 那套『先判可行域再谈性能』的思路在协议层的对应物。")


# ================================================================ 结论
def conclusion(t0):
    hr("结论")
    print("  [P0·结构性] 单域输出只含 2k 个统计量，个体读数本就不被确定 ⇒ 分辨率不可能优于块大小")
    print("  [P1·已证实] 分块对统计结果零影响：块级剥离之和与全局逐项相等，逐块 τ 全通过")
    print("  [P2·已证实] 隔离：整轮报废 → 只丢一个块；b=8 丢 3.1% 覆盖且仍可出全局估计，")
    print("              b=n 时一个数都出不来（对照：VPMDA 现状）")
    print("  [P3·已证实] 触发门槛≈h·√(2b/3)（√b 增长）⇒ 该值同时是【漏检上限】：")
    print("              b=n 时 13× 上界的谎报被静默计入均值，b=8 时降到 2.4×")
    print("  [P4·已证实] 块级定位 0 轮、100% 命中；块内二分稳定缩到单台需 V ≳ h·√b")
    print("              （≈1.22×触发门槛，实测 1.2–1.4× 收敛），轮数 ⌈log2 b⌉；")
    print("              低于该值搜索即丢目标 ⇒ 协议只能承诺【最坏情况分辨率 = b】")
    print("  [P4·已证实] 最小触发（1.02×）时连单源都只到 8%：二分第一步子集就不越界。")
    print("              故『压到刚好触发』是攻击者最优策略，残可疑集 = b（C3 现象在块内重演）")
    print("  [P5·已证实] 掉线按块隔离：可用率 (1−p)^b（vs 单域 (1−p)^n），补报量 ≈ n·b·p")
    print("  [P6·量化]   通信/解密 ∝ n/b；与隔离强度、漏检上限严格对立，b 是唯一设计旋钮")
    print()
    print("  论文定位：不新增一个聚合方案，而是给出【单一密文压缩 ↔ 可定位性/可隔离性】的")
    print("  定量权衡，并证明 b=n（现有全部多子集方案）位于该权衡的最差端。")
    print()
    print(f"  总耗时 {time.time() - t0:.2f}s")


def main():
    t0 = time.time()
    print("=" * 78)
    print("分块聚合实验：隔离、定位、触发门槛、掉线与开销前沿")
    print("=" * 78)
    part0()
    part1()
    part2()
    part3()
    part4()
    part5()
    part6()
    conclusion(t0)


if __name__ == "__main__":
    main()
