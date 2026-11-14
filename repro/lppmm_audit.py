#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import hashlib
import random
import time

RNG = random.Random(20251112)


# =====================================================================
# 1. 真实 secp256k1 群运算（LPPMM-DA 是纯 ECC 方案，不用配对）
# =====================================================================
P_CURVE = 2**256 - 2**32 - 977
N_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
A_CURVE = 0
B_CURVE = 7
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8


def _inv(a, m):
    return pow(a, -1, m)


def ec_add(P1, P2):
    if P1 is None:
        return P2
    if P2 is None:
        return P1
    x1, y1 = P1
    x2, y2 = P2
    if x1 == x2 and (y1 + y2) % P_CURVE == 0:
        return None
    if P1 == P2:
        lam = (3 * x1 * x1 + A_CURVE) * _inv(2 * y1, P_CURVE) % P_CURVE
    else:
        lam = (y2 - y1) * _inv(x2 - x1, P_CURVE) % P_CURVE
    x3 = (lam * lam - x1 - x2) % P_CURVE
    y3 = (lam * (x1 - x3) - y1) % P_CURVE
    return (x3, y3)


def ec_mul(P1, k):
    k %= N_ORDER
    R, Q = None, P1
    while k:
        if k & 1:
            R = ec_add(R, Q)
        Q = ec_add(Q, Q)
        k >>= 1
    return R


G = (GX, GY)


def H(*parts) -> int:
    """把任意输入压成 Z_q 元素（对应原文 H1..H4, H6 的值域）"""
    h = hashlib.sha256()
    for p in parts:
        h.update(str(p).encode() if not isinstance(p, bytes) else p)
        h.update(b"|")
    return int.from_bytes(h.digest(), "big") % N_ORDER


def H5_to_G(msg) -> tuple:
    """H5: {0,1}* -> G，用 try-and-increment 实现"""
    ctr = 0
    while True:
        d = hashlib.sha256((str(msg) + ":" + str(ctr)).encode()).digest()
        x = int.from_bytes(d, "big") % P_CURVE
        rhs = (x * x * x + A_CURVE * x + B_CURVE) % P_CURVE
        y = pow(rhs, (P_CURVE + 1) // 4, P_CURVE)
        if y * y % P_CURVE == rhs:
            return (x, y if y % 2 == 0 else P_CURVE - y)
        ctr += 1


# =====================================================================
# 2. LPPMM-DA 参数与编码（原文 V-A / V-D / Algorithm 1）
# =====================================================================
def _is_prime(n):
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


def next_prime(n):
    if n % 2 == 0:
        n += 1
    while not _is_prime(n):
        n += 2
    return n


class LPPMMParams:
    """
    原文 V-A 第 3 步：
      q_t 两两互素；Q = Π q_t；Q_t = Q/q_t；a_t = Q_t·y_t，Q_t·y_t ≡ 1 (mod q_t)
      超递增序列 b：b_0 > Σ a_t·n·T，b_l > b_0 + b_{l-1}·n
      用户 w 维数据范围 [0, T)，k 个连续子集 [S_1,S_2)...[S_k,∞)
    """

    def __init__(self, n, w, k, T, verbose=False):
        self.n, self.w, self.k, self.T = n, w, k, T
        # q_t 需 > n*T，否则诚实聚合的 M_t 自身就会绕回（参数层面的静默失真）
        self.qt = []
        base = n * T
        cand = next_prime(base + 1)
        while len(self.qt) < w:
            if all(cand != q for q in self.qt):
                self.qt.append(cand)
            cand = next_prime(cand + 2)
        self.Q = 1
        for q in self.qt:
            self.Q *= q
        self.at, self.Qt = [], []
        for q in self.qt:
            Qt = self.Q // q
            yt = pow(Qt, -1, q)
            self.Qt.append(Qt)
            self.at.append(Qt * yt)          # a_t ≡ 1 (mod q_t)，≡ 0 (mod q_s≠t)
        # 超递增序列
        crt_max = sum(a * n * T for a in self.at)
        self.b = [crt_max + 1]                # b_0
        for l in range(1, k + 1):
            self.b.append(self.b[0] + self.b[l - 1] * n)   # b_1..b_k
        self.cap = self.b[k]                  # 整轮容量上限
        # 子集边界：按总电量均分 k 段，[S_1,S_2)...[S_k,∞)，S_1=0
        step = max(1, (w * T) // k)
        self.S = [0] + [step * i for i in range(1, k + 1)]
        if verbose:
            print(f"    q_t 位长 {self.qt[0].bit_length()}  Q 位长 {self.Q.bit_length()}  "
                  f"b_k 位长 {self.cap.bit_length()}  q(曲线阶) {N_ORDER.bit_length()}")
            print(f"    容量余量 q/b_k = {N_ORDER // self.cap:.3e}")

    def subset_of(self, m_total):
        l = 1
        while l < self.k and m_total >= self.S[l + 1]:
            l += 1
        return l

    def encode(self, row):
        """式 (4)：v_i = Σ_t m_it·a_t + b_l"""
        m_total = sum(row)
        l = self.subset_of(m_total)
        v = sum(m * a for m, a in zip(row, self.at)) + self.b[l]
        return v % N_ORDER, l

    def decode(self, V):
        """Algorithm 1：先剥 b 块得 |U_l|，再 CRT 得 M_t"""
        V %= N_ORDER
        cnt = [0] * (self.k + 1)
        for l in range(self.k, 0, -1):
            cnt[l] = (V - V % self.b[l]) // self.b[l]
            V -= self.b[l] * cnt[l]
        M0 = V
        M = [(M0 % self.Q) % q for q in self.qt]
        return cnt[1:], M


# =====================================================================
# 3. 协议实现（V-B..V-H 的聚合路径）
# =====================================================================
class Entity:
    def __init__(self, eid):
        self.id = eid
        self.x = RNG.randrange(2, N_ORDER)          # 私钥
        self.pk = ec_mul(G, self.x)                 # pk = xP
        self.R = None
        self.w_cert = None

    def set_cert(self, s_msk, pkpub):
        r = RNG.randrange(2, N_ORDER)
        self.R = ec_mul(G, r)
        self.w_cert = (r + s_msk * H(self.id, self.pk, self.R)) % N_ORDER   # 式 (3)


class LPPMM:
    def __init__(self, n, w, k, T, verbose=False):
        self.prm = LPPMMParams(n, w, k, T, verbose)
        self.n = n
        self.s_msk = RNG.randrange(2, N_ORDER)
        self.pkpub = ec_mul(G, self.s_msk)
        self.sms = [Entity(f"SM{i}") for i in range(n)]
        self.gw = Entity("GW")
        self.dc = Entity("DC")
        for e in self.sms + [self.gw, self.dc]:
            e.set_cert(self.s_msk, self.pkpub)
        self.kdc = RNG.randrange(2, N_ORDER)        # DC 私钥的标量（用于 H3(xdc·Yi)）
        self.pkdc = ec_mul(G, self.kdc)

    # ---- 单条签名，式 (13)：zjP = Lj + Kj·(pkj + Rj + H1(idj,pkj,Rj)·pkpub)
    def sign_c(self, e, c):
        l = RNG.randrange(2, N_ORDER)
        L = ec_mul(G, l)
        K = H(e.id, c, "T", L, e.pk, e.R)
        Q = ec_add(ec_add(e.pk, e.R), ec_mul(self.pkpub, H(e.id, e.pk, e.R)))
        z = (l + K * (e.x + e.w_cert)) % N_ORDER
        return {"c": c, "z": z, "L": L, "R": e.R}

    def verify_c(self, e, msg):
        K = H(e.id, msg["c"], "T", msg["L"], e.pk, msg["R"])
        Q = ec_add(ec_add(e.pk, e.R), ec_mul(self.pkpub, H(e.id, e.pk, e.R)))
        return ec_mul(G, msg["z"]) == ec_add(msg["L"], ec_mul(Q, K))

    # ---- SM 上报：式 (12) ci = v'i + H3(Y'i)
    def sm_reports(self, rows):
        out = []
        for i, row in enumerate(rows):
            v, l = self.prm.encode(row)
            li = RNG.randrange(2, N_ORDER)
            y = RNG.randrange(2, N_ORDER)
            Yi = ec_mul(G, y)
            Ytil = ec_mul(self.pkdc, y)             # y_i·pk_dc
            mask = H("H3", Ytil)
            c = (v + mask) % N_ORDER                # 式 (12)
            msg = self.sign_c(self.sms[i], c)
            out.append({"Yi": Yi, "msg": msg})
        return out

    # ---- GW 聚合与签名，式 (14)
    def gw_aggregate(self, reports, shift=0):
        C = sum(r["msg"]["c"] for r in reports) % N_ORDER
        C = (C + shift) % N_ORDER
        sig = self.sign_c(self.gw, C)               # Kgw 里含 C —— GW 自己算
        return {"C": C, "sig": sig, "Ys": [r["Yi"] for r in reports]}

    # ---- DC 侧：验签 + 恢复，式 (15)
    def dc_consume(self, pkg):
        sig = pkg["sig"]
        K = H(self.gw.id, sig["c"], "T", sig["L"], self.gw.pk, self.gw.R)
        Q = ec_add(ec_add(self.gw.pk, self.gw.R),
                   ec_mul(self.pkpub, H(self.gw.id, self.gw.pk, self.gw.R)))
        ok = ec_mul(G, sig["z"]) == ec_add(sig["L"], ec_mul(Q, K))
        if not ok:
            return False, None, None
        mask_sum = sum(H("H3", ec_mul(Y, self.kdc)) for Y in pkg["Ys"]) % N_ORDER
        V = (pkg["C"] - mask_sum) % N_ORDER          # 式 (15)
        cnt, M = self.prm.decode(V)
        return True, cnt, M


# =====================================================================
# 4. 实验
# =====================================================================
def hr(t):
    print("\n" + "=" * 78)
    print(" " + t)
    print("=" * 78)


def main():
    t0 = time.time()
    n, w, k, T = 8, 3, 2, 1000

    hr("E0 · 参数与编码自检")
    sch = LPPMM(n=n, w=w, k=k, T=T, verbose=True)
    prm = sch.prm
    print(f"    n={n} w={w} k={k} T={T}  子集边界 S={prm.S}")
    print(f"    b = {[hex(x)[:10] + '…' for x in prm.b]}")

    rows = [[RNG.randrange(0, T) for _ in range(w)] for _ in range(n)]
    print(f"\n    单条往返（式(4) → Algorithm 1）：")
    bad = 0
    for r in rows[:4]:
        v, l = prm.encode(r)
        cnt, M = prm.decode(v)
        ok = (M == r) and (cnt == [1 if i + 1 == l else 0 for i in range(k)])
        bad += not ok
        print(f"      {r}  →  子集{l}  恢复 {M}  {'✓' if ok else '✗'}")
    print(f"    ⇒ 编码层正确（错误 {bad} 条）")

    hr("E1 · 诚实全链路：SM 上报 → GW 聚合 → DC 验签恢复")
    rep = sch.sm_reports(rows)
    print(f"    GW 逐条验签（式 13）：{sum(sch.verify_c(sch.sms[i], rep[i]['msg']) for i in range(n))}/{n} 通过")
    pkg = sch.gw_aggregate(rep)
    ok, cnt, M = sch.dc_consume(pkg)
    true_cnt = [0] * k
    for r in rows:
        true_cnt[prm.subset_of(sum(r)) - 1] += 1
    true_M = [sum(r[j] for r in rows) for j in range(w)]
    print(f"    DC 验签 {'通过' if ok else '失败'} → 子集人数 {cnt}（真值 {true_cnt}）"
          f"  各维总和 {M}（真值 {true_M}）")
    print(f"    ⇒ {'完全一致' if (ok and cnt == true_cnt and M == true_M) else '不一致'}")

    hr("E2 · 聚合绑定攻击：GW 把 C 换成任意目标值并重签")
    print("    原文 DC 侧唯一的检查： zgwP = Lgw + Kgw·(pkgw + Rgw + H1(·)pkpub)")
    print("    而 Kgw = H2(idgw, C, Tgw, Lgw, pkgw, Rgw) —— C 由 GW 提供、GW 自己算 Kgw")
    print("    ⇒ 这正是 04 报告矩阵里的 AGGREGATE_BY_AG 格：签名人即攻击者。\n")

    # 攻击者先算出「想要的聚合值」，再反推 Δ。两个数都在公开参数下可算。
    V_true = sum(prm.encode(r)[0] for r in rows) % N_ORDER

    def target_V(cnt, M):
        return (sum(m * a for m, a in zip(M, prm.at))
                + sum(b * c for b, c in zip(prm.b[1:], cnt))) % N_ORDER

    cases = []
    # (a) 只抬第 1 维总和：人数不变
    cases.append(("抬高 M_1 → 8000（人数不变）",
                  target_V(true_cnt, [8000, true_M[1], true_M[2]])))
    # (b) 只改人数分布：把全部用户挪到第 2 个子集（电价档位操纵）
    cases.append(("重排档位 → 人数 [0,8]（总和不变）",
                  target_V([0, n], true_M)))
    # (c) 两者同时改：伪造一个「高价段用户变多、总电量也变高」的账单
    cases.append(("同时伪造 → 人数[2,6] 且 M_1=7000",
                  target_V([2, n - 2], [7000, true_M[1], true_M[2]])))

    for label, V_target in cases:
        delta = (V_target - V_true) % N_ORDER
        pkg2 = sch.gw_aggregate(rep, shift=delta)
        ok2, cnt2, M2 = sch.dc_consume(pkg2)
        print(f"    {label}")
        print(f"      Δ = V_target − V_true（攻击者用公开参数自算）")
        print(f"      攻击包验签：{'通过 ← 攻击成功' if ok2 else '失败 ← 已拦截'}")
        if ok2:
            print(f"      DC 输出  人数 {cnt2}   各维总和 {M2}")
            print(f"      与真值差  人数 {[a-b for a,b in zip(cnt2,true_cnt)]}"
                  f"   维度 {[a-b for a,b in zip(M2,true_M)]}")
        print()

    print("    ⇒ DC 侧没有任何一个量能区分『如实聚合的结果』与『GW 指定的结果』：")
    print("      C 的完整性只由 GW 自己的签名担保，而 GW 就是那个能改 C 的实体。")

    # 反向：GW 不改 C，只改 Y（掩码侧）—— 对照，验证 t_n 型检查在此方案中不存在
    print("    对照：若把 C 换成随机值（不重签）——")
    pkg3 = sch.gw_aggregate(rep)
    pkg3["C"] = RNG.randrange(2, N_ORDER)
    pkg3["sig"] = {"c": pkg3["C"], "z": pkg3["sig"]["z"],
                   "L": pkg3["sig"]["L"], "R": pkg3["sig"]["R"]}
    ok3, _, _ = sch.dc_consume(pkg3)
    print(f"      验签：{'通过 ← 说明式(13)与 C 无代数关联' if ok3 else '失败'}"
          f"（此处 Kgw 含 C，篡改会破坏签名，故按原文必须重签）")

    hr("E3 · 打包健壮性：上报值超出 CA 公布的 [0,T)")
    print(f"    原文正确性依赖两个前提（VI-A）：Σ_t M_t·a_t < b_0，且 M_t < q_t")
    print(f"    当前参数：n·T = {n*T}，q_t = {prm.qt[0]}，b_0 位长 {prm.b[0].bit_length()}，"
          f"b_k 位长 {prm.cap.bit_length()}\n")
    print(f"    {'上报值':>8s} {'M_1真值':>9s} {'M_1恢复':>9s} {'人数真值':>9s} {'人数恢复':>9s}"
          f"  {'CRT超界':>7s} {'b块超界':>7s}  判定")
    print("    " + "-" * 92)
    base_M1 = true_M[0]
    for extra in (0, 900, 3000, 8000, 30000, 120000):
        rows2 = [list(r) for r in rows]
        rows2[0][0] += extra
        rep2 = sch.sm_reports(rows2)
        pkg4 = sch.gw_aggregate(rep2)
        ok4, cnt4, M4 = sch.dc_consume(pkg4)
        true_M4 = [sum(r[j] for r in rows2) for j in range(w)]
        true_cnt4 = [0] * k
        for r in rows2:
            true_cnt4[prm.subset_of(sum(r)) - 1] += 1
        # 诊断：哪条前提被破坏
        crt_part = sum(m * a for m, a in zip(true_M4, prm.at))
        over_crt = any(m >= q for m, q in zip(true_M4, prm.qt))
        over_blk = crt_part >= prm.b[0]
        good_M = (M4 == true_M4)
        good_C = (cnt4 == true_cnt4)
        if good_M and good_C:
            tag = "如实反映" if extra == 0 else "如实反映（谎报但未溢出）"
        elif not good_M and not good_C:
            tag = "★ 人数与总和同时静默失真"
        elif not good_M:
            tag = "★ 总和静默失真（CRT 绕回）"
        else:
            tag = "★ 人数静默失真（b 块进位）"
        print(f"    {base_M1+extra:>8d} {true_M4[0]:>9d} {M4[0]:>9d} "
              f"{true_cnt4[0]:>9d} {cnt4[0]:>9d}  {str(over_crt):>7s} {str(over_blk):>7s}  {tag}")

    print("\n    两条前提的破坏机制：")
    print("      M_t ≥ q_t      → M_t mod q_t 绕回，总和少 q_t 的整数倍，无任何异常信号")
    print("      Σ M_t·a_t ≥ b_0 → CRT 部分向 b_1 块进位，人数统计被污染")
    print("    解出的 M_t 永远落在 [0, q_t)，|U_l| 永远落在 [0, n]，")
    print("    所以 DC 对恢复结果做任何区间检查都恒真 —— 与 VPMDA『剥离输出恒界内』同构。")

    hr("E4 · 参数可行性：编码空间还剩多少余量")
    print("    两条硬约束（均由 VI-A 导得）：")
    print("      (i)  M_t < q_t           —— 每条残差通道的上界，决定单维总和能表示多大")
    print("      (ii) b_k < q             —— 整轮编码值必须落在曲线的群阶内\n")
    print(f"    本组参数 n={n}, w={w}, k={k}, T={T}：")
    print(f"      q_t = {prm.qt[0]}，诚实上限 n·T = {n*T}，余量 {prm.qt[0]-n*T} "
          f"（{(prm.qt[0]-n*T)/(n*T)*100:.2f}%）")
    print(f"      ⇒ 单维总和只要超过诚实上限 {prm.qt[0]-n*T} 就会绕回——几乎零余量。")
    print()
    print("    按原文实验设置反推所需群阶（q_t 取 next_prime(nT) 的最小可行值）：")
    print(f"    {'n':>6s} {'w':>3s} {'k':>3s} {'b_k 位长':>9s} {'论文 q 位长':>11s}  结论")
    print("    " + "-" * 66)
    for nn, ww, kk in ((100, 5, 7), (1000, 5, 7), (1000, 10, 3), (100, 10, 5)):
        p2 = LPPMMParams(n=nn, w=ww, k=kk, T=1000)
        need = p2.cap.bit_length()
        print(f"    {nn:>6d} {ww:>3d} {kk:>3d} {need:>9d} {160:>11d}  "
              f"{'相容' if need < 160 else '★ 不相容：b_k 已超出 160-bit 群阶，编码值必然绕回 q'}")
    print()
    print("    注：这是按原文 VI-A 的不等式做的纯算术推导，不涉及任何实现选择。")
    print("        b_l ≈ b_0·n^l 是指数增长，而 q 只有 160 bit —— n 与 k 一放大就撞墙。")

    hr("E5 · 两种打包原语的失效形态对照")
    print("    VPMDA / SA-MAD：超递增序列 Σ b_i·m_i  → 越界 = 向高位进位")
    print("    LPPMM-DA      ：CRT 残差 a_t + b 块    → 越界 = (1) CRT 绕回 mod q_t")
    print("                                              (2) 向 b_{l+1} 块进位")
    print("    共同点：解码器的输出字母表由构造决定（余数 < 模数、计数 ≤ n），")
    print("            因此『恢复结果越界』这个信号在代数上不可用。")

    hr("结论")
    print("  [A 级] LPPMM-DA 的 DC 侧验证 = GW 对 C 的自签名（Kgw 含 C，签名人是 GW）")
    print("         → 落入 AGGREGATE_BY_AG，攻击者改 C 后重签即通过，无需任何秘密")
    print("  [A 级] 原文『Data Integrity』段引用式 (14)（聚合公式）作为验证依据，")
    print("         而式 (14) 是 C = Σcj mod q —— 不构成对 C 的独立检查")
    print("  [A 级] 上报值超出 [0,T) 时，CRT 残差静默绕回，维度总和失真而人数可能仍正确")
    print("         → 空位 B 在第二种打包原语上复现，普遍性论证闭环")
    print()
    print(f"  总耗时 {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
