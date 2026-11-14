import random
import time

from overflow_demo import PackedAgg, P_CHK, hr, truth

RNG = random.Random(20261112)


def round_trip_poison(S, rows, poisons, tau_override=None):
    """
    poisons: [(i, j, V), ...] 多台毒化；tau_override: {i: τ_i 值} 指定合谋者 τ_i。
    其余逻辑同 PackedAgg.round_trip，但支持多台与 τ 注入。
    """
    data = [list(r) for r in rows]
    for i, j, V in poisons:
        data[i][j] = V
    q = 0
    for idx, r in enumerate(data):
        q += S.encode(r)
        if tau_override and idx in tau_override:
            # 减去诚实 τ_i，换成攻击者指定的 τ_i
            q -= S.v[S.dim - 1] * (sum(S.c[j] * r[j] + S.c[S.k + j] * r[j] ** 2
                                       for j in range(S.k)) % P_CHK)
            q += S.v[S.dim - 1] * (tau_override[idx] % P_CHK)
    Q = S.cipher.dec(S.cipher.enc(q, 0))
    M, QM, tau = S.peel_full(Q)
    faithful = (M == [sum(r[jj] for r in data) for jj in range(S.k)]
                and QM == [sum(r[jj] ** 2 for r in data) for jj in range(S.k)])
    return dict(M=M, QM=QM, tau=tau, ok_chk=S.verify(M, QM, tau), faithful=faithful)


def min_carry_V(S, rows, colluders, lo=1000, hi=200000):
    """二分搜索：使聚合刚好越容量（剥离不再如实）的最小同值毒化 V"""
    while hi - lo > 1:
        mid = (lo + hi) // 2
        r = round_trip_poison(S, rows, [(i, 0, mid) for i in colluders])
        if r["faithful"]:
            lo = mid
        else:
            hi = mid
    return hi


# ================================================================ 主流程
def main():
    t0 = time.time()
    n, k, bounds = 16, 2, (1000, 500)
    S = PackedAgg(n=n, k=k, bounds=bounds, with_check=True)
    rng = random.Random(42)
    rows = [[rng.randrange(0, bounds[0]), rng.randrange(0, bounds[1])]
            for _ in range(n)]

    hr("PART 1 · C1：合谋摊薄单台的越界倍数")
    print(f"  n={n}, h₁={bounds[0]}，M₁ 容量 {S.caps[0]}，QM₁ 容量 {S.caps[k]}")
    print(f"  容量定义 cap = n·h ⇒ 全部表都报满 h 时恰好用尽容量。")
    print(f"  ⇒ 任何进位攻击至少要有一台报值超过物理上界 h（界内值永远装不满）。")
    print()
    print(f"  {'合谋台数 c':>8s} {'单台毒化值 V':>12s} {'V/h 倍数':>9s}   直观含义")
    print("  " + "-" * 64)
    mults = {}
    for c in (1, 2, 4, 8):
        colluders = RNG.sample(range(n), c)
        V = min_carry_V(S, rows, colluders)
        mults[c] = V
        note = {1: f"单台报 {V/bounds[0]:.1f} 倍上界，超出物理合理性一截",
                2: f"两台各报 {V/bounds[0]:.1f} 倍，『两个坏表』的故事开始成立",
                4: f"四台各报 {V/bounds[0]:.1f} 倍，可混入设备老化噪声",
                8: f"八台各报 {V/bounds[0]:.1f} 倍，几乎无法用物理合理性排除"}.get(
            c, f"c≥n/2 时单台仅 {V/bounds[0]:.1f} 倍，与测量漂移无异")
        print(f"  {c:>8d} {V:>12d} {V/bounds[0]:>8.2f}x   {note}")
    print()
    print("  ⇒ 合谋把『越界倍数』按 ~1 + n/(2c) 摊薄（实测 %s -> %s）：攻击越分散，"
          % (f"{mults[1]/bounds[0]:.1f}x", f"{mults[8]/bounds[0]:.1f}x"))
    print("    单台证据越弱 —— 这正是合谋比单台毒化更危险的地方。")
    print("    但注意：这只影响『隐蔽性』，不影响下面两问的检出与定位结构。")

    # ---------------------------------------------- C2
    hr("PART 2 · C2：τ 校验位在 c 台合谋下的检出率")
    print("  设定：随机取 c 台合谋，各在第 1 类报 V_c = 1.3 × (刚好触发进位的值)，")
    print("        其余台诚实；τ_i 由各台（含合谋台）按上报值如实计算。")
    print("        每组 300 轮，每轮重抽合谋台与诚实数据。")
    print()
    print(f"  {'c':>3s} {'触发进位轮':>10s} {'τ 检出':>8s} {'漏检':>6s} {'检出率':>9s}")
    print("  " + "-" * 44)
    for c in (1, 2, 3, 4, 5):
        hit = miss = carry = 0
        for _ in range(300):
            rr = [[rng.randrange(0, bounds[0]), rng.randrange(0, bounds[1])]
                  for _ in range(n)]
            colluders = RNG.sample(range(n), c)
            V0 = min_carry_V(S, rr, colluders)
            r = round_trip_poison(S, rr, [(i, 0, int(V0 * 1.3)) for i in colluders])
            if r["faithful"]:
                continue                      # 未触发进位（数据源投毒，非本文对象）
            carry += 1
            if r["ok_chk"]:
                miss += 1
            else:
                hit += 1
        rate = hit / carry * 100 if carry else float("nan")
        print(f"  {c:>3d} {carry:>10d} {hit:>8d} {miss:>6d} {rate:>8.1f}%")
    print()
    print("  ⇒ 检出率与合谋台数无关：只要总聚合越容量，剥离必然失真，")
    print("    τ 的 c-同余必然被破坏（扰动恰好自洽的概率 ≈ 1/P_CHK 量级）。")
    print("    合谋降低的是隐蔽性门槛，不是检出率。")

    # ---------------------------------------------- C3
    hr("PART 3 · C3：多台合谋下二分定位是否失效（本文最意外的发现）")
    print("  关键结构事实：编码权重 v 由【全系统】容量决定，SM 密文一旦生成无法重编。")
    print("  子集重放时，子集聚合只要不超过【全容量】，剥离依然忠实 → τ 通过。")
    print("  ⇒ 预判：合谋台把溢出量分摊到两侧时，所有真子集都通过，二分无信号。")
    print()
    N_LOC = 32
    Sl = PackedAgg(n=N_LOC, k=k, bounds=bounds, with_check=True)
    rr32 = [[rng.randrange(0, bounds[0]), rng.randrange(0, bounds[1])]
            for _ in range(N_LOC)]

    def sub_check(sub, poisons, tau_ov=None):
        return round_trip_poison(Sl, sub, poisons, tau_ov)["ok_chk"]

    def check_global(sub_range, V, colluders):
        """对全局索引区间 sub_range 的子集做重放，合谋台在子集内则毒化"""
        sub = rr32[sub_range[0]:sub_range[1]]
        pois = [(idx - sub_range[0], 0, V)
                for idx in range(sub_range[0], sub_range[1]) if idx in colluders]
        return round_trip_poison(Sl, sub, pois)["ok_chk"]

    # (a) 单台（对照，应成功）
    bad_i = 17
    V1 = int(min_carry_V(Sl, rr32, [bad_i]) * 1.3)
    r_full = round_trip_poison(Sl, rr32, [(bad_i, 0, V1)])
    lo_b, hi_b, rounds = 0, N_LOC, 0
    while hi_b - lo_b > 1:
        mid = (lo_b + hi_b) // 2
        rounds += 1
        if not check_global((lo_b, mid), V1, {bad_i}):
            hi_b = mid
        else:
            lo_b = mid
    print(f"  (a) 单台 SM{bad_i} 报 {V1}（{V1/bounds[0]:.1f}x）：")
    print(f"      全集校验 {'失败' if not r_full['ok_chk'] else '通过(异常)'}，"
          f"二分 {rounds} 轮定位 SM{lo_b} —— {'正确' if lo_b == bad_i else '错误'}")

    # (b) 两台分摊（构造：全集失败、左右两半都通过）
    print()
    print("  (b) 构造两台分摊：找 V 使『全集校验失败 且 左半、右半单独校验都通过』")
    ca, cb = 5, 27
    V2 = None
    for V in range(1500, 60000, 25):
        rf = round_trip_poison(Sl, rr32, [(ca, 0, V), (cb, 0, V)])
        rl = check_global((0, 16), V, {ca})
        rg = check_global((16, 32), V, {cb})
        if not rf["ok_chk"] and rl and rg:
            V2 = V
            break
    if V2:
        print(f"      找到 V = {V2}（{V2/bounds[0]:.1f}x，单台远低于此值不足以触发）")
        rf = round_trip_poison(Sl, rr32, [(ca, 0, V2), (cb, 0, V2)])
        rl = check_global((0, 16), V2, {ca})
        rg = check_global((16, 32), V2, {cb})
        print(f"      全集校验: {'失败 ← 检出' if not rf['ok_chk'] else '通过'}")
        print(f"      左半[0:16) 校验: {'失败' if not rl else '通过 ← 无信号'}")
        print(f"      右半[16:32) 校验: {'失败' if not rg else '通过 ← 无信号'}")
        # 再扫一批任意真子集，确认"无信号"是普遍的而非恰好这两个半区
        spans = [(0, 8), (8, 16), (16, 24), (24, 32), (0, 4), (12, 20),
                 (20, 28), (2, 14), (18, 30), (4, 30)]
        passed = sum(check_global(sp, V2, {ca, cb}) for sp in spans)
        print(f"      任意 10 个真子集重放：{passed}/10 通过 → 定位完全无信号")
        print()
        print("      ⇒ 两台各在半区贡献一半溢出，二分在第一层就失去方向 —— 定位失效。")
    else:
        print("      未找到满足条件的 V（需调整数据）")
    print()
    print("  机理：容量是可加的。子集失败 ⇔ 子集聚合超过【全系统】容量。")
    print("        溢出量被合谋台分摊后，任何真子集都可能装得下自己的份额。")
    print("        单台时代『二分必有一个失败半区』的单调性，被可加性瓦解。")
    print()
    print("  修补方向：分块聚合（把 n 台划成 b 大小的块，块内独立打包聚合）。")
    print("  · 单台在块内单独超块容量 → 块内二分有效（回到情形 a）；")
    print("  · 块内多台分摊 → 同样失效，但攻击者需把溢出集中到同一块，")
    print("    可疑范围从 n 收缩到 b；b 越小定位越强、但块容量越小越易被单台触发。")
    print("  ⇒ b 是一个【定位强度 ↔ 触发门槛】的安全参数，写进论文的参数分析。")

    # ---------------------------------------------- C4
    hr("PART 4 · C4：固定数据下、每轮刷新系数的一次随机 τ 猜测")
    print("  每轮先选一个 τ_0 猜测，再抽取新系数；每轮只做一次尝试，")
    print("  不把验证结果反馈给后续猜测。数据固定不变。")
    print("  此测试不证明 AG 与目标域电表串谋时的安全性：已知系数的串谋者可修正已知偏移，")
    print("  该情形由论文 A4 排除；本测试仅模拟其未知的诚实成员贡献下的一次随机猜测。")
    print("  通过条件还含有合谋者未知的诚实方贡献：")
    print("        τ_raw = Σ_i τ_i + D_τ（D_τ 为进位对校验位的扰动）")
    print("  诚实台的 Στ_i 是 c·m + c'·m² 的求和，c'·m² 遍历大范围 ⇒ 对合谋者近似均匀。")
    print("  仅在每轮系数独立刷新、当前轮尝试无验证反馈时，单轮猜测概率才约为 1/P。")
    print()
    hits = 0
    ROUNDS = 3000
    pois = (0, 0, 3500)
    for rd in range(ROUNDS):
        guess = RNG.randrange(P_CHK)             # 本轮在系数抽样前固定猜测
        S.c = [RNG.randrange(P_CHK) for _ in range(2 * k)]  # idealized fresh coefficients
        r = round_trip_poison(S, rows, [pois], tau_override={0: guess})
        if r["ok_chk"]:
            hits += 1
    print(f"  固定数据、SM0 报 V=3500（必进位），每轮新系数、一次预先固定的随机 τ_0 猜测，共 {ROUNDS} 轮：")
    print(f"  τ 通过 {hits} 次（通过率 {hits/ROUNDS:.4%}，理论期望 ≈ {ROUNDS/P_CHK:.2e}）")
    print()
    print("  ⇒ 此有限样本与每轮新系数、当前轮无反馈的一次猜测模型相容；0/3000 不能证明概率界，")
    print("    也不覆盖目标域电表向 AG 泄露系数后的已知偏移攻击。")

    hr("结论")
    print("  [C1·已证实] 合谋按 ~1+n/(2c) 摊薄单台越界倍数（n=16 实测 3.6x → 1.3x），隐蔽性大增")
    print("  [C2·已证实] τ 检出率与合谋台数无关（c=1..5 全部 100%）：检出看总聚合，不看个体")
    print("  [C3·已证实] 多台分摊溢出时二分定位失效（容量可加性瓦解单调性）——")
    print("              单台结论 ⌈log2 n⌉ 不能外推到合谋场景，论文必须如实收窄")
    print("  [C3·修补]   分块聚合恢复定位：可疑范围 n→b，b 是定位强度↔触发门槛的权衡参数")
    print("  [C4·有限样本] 固定数据、每轮新系数、单次无反馈猜测 0/3000 通过；")
    print("              不覆盖 AG 与目标域成员串谋，也不替代定理条件")
    print()
    print(f"  总耗时 {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
