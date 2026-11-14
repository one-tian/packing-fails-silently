import hashlib
import hmac
import random
import time
from math import gcd

import toybilinear as tb

RNG = random.Random(20260211)
SEP = "=" * 74


def hr(title=""):
    print()
    print(SEP)
    if title:
        print(title)
        print(SEP)


# ============================================================ Paillier 部分
def gen_prime(bits, rng):
    while True:
        n = rng.getrandbits(bits) | (1 << (bits - 1)) | 1
        if tb._is_prime(n):
            return n


class Paillier:
    """改造 Paillier：g = 1+N，随机数由 h1(T)^(N·g_i) 承担"""

    def __init__(self, bits=256):
        while True:
            self.q1 = gen_prime(bits, RNG)
            self.q2 = gen_prime(bits, RNG)
            if gcd(self.q1 * self.q2, (self.q1 - 1) * (self.q2 - 1)) == 1:
                break
        self.N = self.q1 * self.q2
        self.N2 = self.N * self.N
        self.lam = (self.q1 - 1) * (self.q2 - 1) // gcd(self.q1 - 1, self.q2 - 1)
        self.g = 1 + self.N
        # 论文要求：TTP 发完参数后销毁 λ
        self.lam_destroyed = False

    def destroy_lam(self):
        self.lam = None
        self.lam_destroyed = True


def h1_bytes(msg: bytes, N: int) -> int:
    """h1: {0,1}* → Z*_N"""
    d = hashlib.sha256(b"h1|" + msg).digest()
    v = int.from_bytes(d, "big") % N
    return v if v else 1


def h2_int(x: int, N: int, ORD: int) -> int:
    """h2: Z*_N → Z_p（映射到配对群阶）"""
    d = hashlib.sha256(b"h2|" + str(x % N).encode()).digest()
    return int.from_bytes(d, "big") % ORD


def h3_bytes(data: bytes, ORD: int) -> int:
    d = hashlib.sha256(b"h3|" + data).digest()
    return int.from_bytes(d, "big") % ORD


def prg(sk: bytes, nonce: bytes, count: int, ORD: int):
    """伪随机生成器：CC 与 AG 共享 sk_prg"""
    out = []
    for i in range(count):
        d = hmac.new(sk, nonce + i.to_bytes(4, "big"), hashlib.sha256).digest()
        out.append(int.from_bytes(d, "big") % ORD)
    return out


# ============================================================ 超递增序列
def build_superincreasing(k, bounds, n):
    """
    v_a > Σ_{j<a} (v_j·h_j·n)，v_1 = 1
    h_{k+j} = h_j^2
    返回 (v, labels)
    """
    h = list(bounds) + [b * b for b in bounds]
    labels = [("M", j + 1) for j in range(k)] + [("Q", j + 1) for j in range(k)]
    v = [1]
    for a in range(1, 2 * k):
        acc = sum(v[j] * h[j] * n for j in range(a))
        v.append(acc + 1)
    return v, h, labels


def peel(Q, v, k):
    """Algorithm 1：从高位往低位剥离"""
    QM = [0] * k
    M = [0] * k
    for j in range(k, 0, -1):
        idx = k + j - 1
        QM[j - 1] = (Q - Q % v[idx]) // v[idx]
        Q -= v[idx] * QM[j - 1]
    for j in range(k, 0, -1):
        idx = j - 1
        M[j - 1] = (Q - Q % v[idx]) // v[idx]
        Q -= v[idx] * M[j - 1]
    return M, QM, Q


# ============================================================ 系统初始化
class System:
    def __init__(self, n=5, k=2, bounds=(1000, 500)):
        self.n, self.k = n, k
        self.bounds = bounds
        self.pai = Paillier(bits=256)
        N = self.pai.N

        # --- 配对群
        self.ORD = tb.ORD
        self.eta = tb.hash_to_G1(b"eta")      # η ∈ G1
        self.gen = tb.hash_to_G1(b"r")        # r ∈ G1（配对第二个参数）
        self.publ = {}

        # --- 秘密份额 g_i，零和：g0 + Σg_i ≡ 0 (mod λ)
        self.g = [RNG.randrange(2, N) for _ in range(n)]
        gsum = sum(self.g) % self.pai.lam
        self.g0 = (-gsum) % self.pai.lam

        # --- 认证子公钥 b_i = r^{h2(g_i)}
        self.h2g = [h2_int(gi, N, self.ORD) for gi in self.g]
        self.b = [tb.pmul(self.gen, x) for x in self.h2g]

        # --- 超递增序列
        self.v, self.h, self.vlabels = build_superincreasing(k, bounds, n)

        # --- PRG 共享密钥
        self.sk_prg = bytes(RNG.getrandbits(8) for _ in range(32))

        # --- 自检：序列是否真的超递增，且总载荷 < N
        Qmax = sum(v * hh * n for v, hh in zip(self.v, self.h))
        self.Qmax = Qmax
        assert Qmax < N, "载荷超出 Paillier 模数，需增大 N 或减小 h/n"

        # --- TTP 发完参数后销毁 Paillier 私钥 λ
        self.pai.destroy_lam()

    # ---------------------------------------------------- 电表侧
    def sm_encrypt(self, i, m, T):
        """返回 (CT_i, s_i)"""
        N, N2, g = self.pai.N, self.pai.N2, self.pai.g
        Qi = 0
        for j in range(self.k):
            Qi += self.v[j] * m[j] + self.v[self.k + j] * m[j] * m[j]
        h1T = h1_bytes(T, N)
        rnd = pow(h1T, (N * self.g[i]), N2)
        CT = pow(g, Qi, N2) * rnd % N2

        att = f"RAID{i}".encode()
        Hi = tb.hash_to_G1(att)
        # s_i = (H(att_i) · η^{CT_i})^{h2(g_i)}
        inner = tb.padd(Hi, tb.pmul(self.eta, CT % self.ORD))
        s = tb.pmul(inner, self.h2g[i])
        return CT, s, Qi

    # ---------------------------------------------------- 聚合网关侧
    def ag_aggregate(self, payload, T, nonce=b"nonce-0001"):
        N2 = self.pai.N2
        CT = 1
        for (CTi, si, _) in payload:
            CT = CT * CTi % N2

        t = prg(self.sk_prg, nonce, self.n - 1, self.ORD)
        # t_n = h3(CT^N ‖ nonce)
        ctN = pow(CT, self.pai.N, N2)
        tn = h3_bytes(ctN.to_bytes((ctN.bit_length() + 7) // 8, "big") + b"|" + nonce, self.ORD)
        t.append(tn)

        s = None
        phi = None
        for i, (CTi, si, _) in enumerate(payload):
            s = tb.padd(s, tb.pmul(si, t[i]))
            phi = tb.padd(phi, tb.pmul(self.b[i], (t[i] * CTi) % self.ORD))
        return dict(CT=CT, s=s, phi=phi, t=t, T=T, nonce=nonce)

    # ---------------------------------------------------- 控制中心侧
    def cc_derive_tn(self, T, nonce, dropped=()):
        """CC 用 g0 独立算出与 AG 相同的 t_n（零交互）"""
        N, N2 = self.pai.N, self.pai.N2
        h1T = h1_bytes(T, N)
        h1inv = pow(h1T, -1, N2)
        ctN_expected = pow(h1inv, (N * N * self.g0), N2)   # h1^{-N²g0}
        return h3_bytes(ctN_expected.to_bytes((ctN_expected.bit_length() + 7) // 8, "big")
                        + b"|" + nonce, self.ORD), ctN_expected

    def cc_verify(self, agg, tn):
        t = agg["t"][:-1] + [tn]
        lhs = tb.pairing(agg["s"], self.gen)
        rhs = None
        for i in range(self.n):
            att = f"RAID{i}".encode()
            Hi = tb.hash_to_G1(att)
            term = tb.pairing(tb.pmul(Hi, t[i]), self.b[i])
            rhs = term if rhs is None else rhs * term
        rhs = rhs * tb.pairing(self.eta, agg["phi"])
        return lhs == rhs

    def cc_decrypt(self, agg, dropped=()):
        N, N2 = self.pai.N, self.pai.N2
        CT = agg["CT"]
        h1T = h1_bytes(agg["T"], N)
        W = CT * pow(h1T, (N * self.g0), N2) % N2
        assert (W - 1) % N == 0, "掩码未消掉"
        return (W - 1) // N


# ============================================================ 主流程
def main():
    tb.init(40)
    assert tb.self_test(verbose=False)
    hr("STEP 1 · 系统初始化")
    n, k = 5, 2
    bounds = (1000, 500)
    S = System(n=n, k=k, bounds=bounds)
    print(f"  电表数 n = {n}，数据类型 k = {k}，上界 h = {bounds}")
    print(f"  Paillier N = {S.pai.N.bit_length()} bit，λ 已销毁: {S.pai.lam_destroyed}")
    print(f"  超递增序列 v = {S.v}")
    print(f"  标签      = {S.vlabels}")
    print(f"  最大载荷 Q_max = {S.Qmax}  ({S.Qmax.bit_length()} bit，需 < N)")
    print(f"  配对群阶 r = {tb.ORD} ({tb.ORD.bit_length()} bit)")

    # ---- 真实数据（真实功率 W / 无功功率 VAR）
    data = [[523, 112], [148, 45], [907, 203], [612, 87], [355, 61]]
    T = b"2026-11-11T21:00:00"
    print(f"  上报数据 (P, Q) = {data}")

    hr("STEP 2 · 数据上报（电表加密 + 生成认证子）")
    payload = []
    for i, m in enumerate(data):
        CT, s, Qi = S.sm_encrypt(i, m, T)
        payload.append((CT, s, Qi))
        print(f"  SM{i}: Q_i = {Qi:<22d}  CT_i = {CT % 10**12:012d}…  s_i = {str(s[0].a)[:16]}…")

    hr("STEP 3 · 数据聚合（网关）")
    agg = S.ag_aggregate(payload, T)
    print(f"  CT  = {agg['CT'] % 10**18:018d}…")
    print(f"  t[] = {[hex(x)[:10] + '…' for x in agg['t']]}")

    hr("STEP 4 · 验证与解密（控制中心）")
    tn_cc, ctN_expected = S.cc_derive_tn(T, agg["nonce"])
    print(f"  AG 侧 t_n = {hex(agg['t'][-1])}")
    print(f"  CC 侧 t_n = {hex(tn_cc)}")
    print(f"  两方独立算出同一 t_n（零交互）: {'是' if tn_cc == agg['t'][-1] else '否'}")

    ok = S.cc_verify(agg, tn_cc)
    print(f"  完整性验证 e(s,r) = Πe(H^t_i,b_i)·e(η,φ) : {'通过' if ok else '失败'}")

    Q = S.cc_decrypt(agg)
    M, QM, rest = peel(Q, S.v, k)
    print(f"  解密得 Q = {Q}")
    print(f"  剥离后余项（应为 0）: {rest}")
    for j in range(k):
        avr = M[j] / n
        var = QM[j] / n - avr * avr
        print(f"  类型{j+1}: Σm = {M[j]:<6d} Σm² = {QM[j]:<8d} 均值 = {avr:8.2f} 方差 = {var:10.2f}")

    truth = [[d[j] for d in data] for j in range(k)]
    for j in range(k):
        sm = sum(truth[j])
        sq = sum(x * x for x in truth[j])
        avr = sm / n
        print(f"  [核对] 类型{j+1} 真实 Σm = {sm}, Σm² = {sq}, 均值 = {avr:.2f}, "
              f"方差 = {sq/n - avr*avr:.2f}")

    # ========================================================= 攻击 A
    hr("STEP 5 · 攻击 A：Δ-平移攻击（恶意聚合网关）")
    print("  攻击者能力：AG 可以改 CT，但不能伪造 s、φ（它没有 h2(g_i)）")
    print("  攻击目标：把第 2 类数据的均值抬高 δ，其余统计量完全不变")

    delta = 100
    # Δ 必须落在 v2 这一位上 → 只影响 M_2
    Delta = S.v[1] * delta
    print(f"  取 δ = {delta}，构造 Δ = v_2 · δ = {S.v[1]} × {delta} = {Delta}")

    CT_forged = agg["CT"] * pow(S.pai.g, Delta, S.pai.N2) % S.pai.N2
    print(f"  CT' = CT · g^Δ mod N²")
    print(f"  攻击者保留诚实的 s 与 φ，只替换 CT → CT'")

    # CC 收到 (CT', s, φ, T)，用自己算的 t_n 验证
    ok_forged = S.cc_verify(agg, tn_cc)      # 验证式不含 CT，故结果与诚实场景完全一致
    print(f"  CC 验证结果: {'通过 ← 攻击成功' if ok_forged else '失败'}")

    Q_forged = S.cc_decrypt(dict(agg, CT=CT_forged))
    M2, QM2, rest2 = peel(Q_forged, S.v, k)
    print(f"  CC 解密得 Q' = {Q_forged}  （真实 Q = {Q}）")
    print(f"  剥离后余项（应为 0）: {rest2}")
    for j in range(k):
        avr = M2[j] / n
        var = QM2[j] / n - avr * avr
        print(f"  类型{j+1}: Σm = {M2[j]:<6d} Σm² = {QM2[j]:<8d} 均值 = {avr:8.2f} 方差 = {var:10.2f}")
    print(f"  → 类型2 均值偏移 = {M2[1]/n - M[1]/n:+.2f}（期望 +{delta/n:.2f}）")
    print(f"  → 类型1 均值偏移 = {M2[0]/n - M[0]/n:+.2f}（期望 0）")
    print(f"  → 类型2 方差偏移 = {(QM2[1]/n - (M2[1]/n)**2) - (QM[1]/n - (M[1]/n)**2):+.2f}")

    # ========================================================= 攻击 A+
    hr("STEP 5B · 攻击 A+：完整伪造全部 2k 个统计量")
    print("  观察：Δ 可以同时落在多个位上 —— Δ = Σ_j (v_j·α_j + v_{k+j}·β_j)")
    print("  含义：攻击者能对每一个统计量做「加法平移」，即完全控制输出结果")

    target_M2 = 1000        # 目标：类型2 总量
    target_QM2 = 200000     # 目标：类型2 平方和 → 均值 200，方差 0
    a2 = target_M2 - M[1]
    b2 = target_QM2 - QM[1]
    Delta2 = S.v[1] * a2 + S.v[3] * b2
    print(f"  目标：类型2 均值 = {target_M2/n:.2f}，方差 = {target_QM2/n - (target_M2/n)**2:.2f}（伪造为 0）")
    print(f"  α₂ = {a2}（落在 v_2 位）, β₂ = {b2}（落在 v_4 位）")
    print(f"  Δ  = v_2·α₂ + v_4·β₂ = {Delta2}")

    CT_f2 = agg["CT"] * pow(S.pai.g, Delta2, S.pai.N2) % S.pai.N2
    ok_f2 = S.cc_verify(agg, tn_cc)
    Q_f2 = S.cc_decrypt(dict(agg, CT=CT_f2))
    M_f, QM_f, rest_f = peel(Q_f2, S.v, k)
    print(f"  CC 验证: {'通过 ← 攻击成功' if ok_f2 else '失败'}")
    print(f"  剥离后余项（应为 0）: {rest_f}")
    for j in range(k):
        avr = M_f[j] / n
        var = QM_f[j] / n - avr * avr
        flag = "  ← 攻击者指定的目标值" if j == 1 else ""
        print(f"  类型{j+1}: Σm = {M_f[j]:<6d} Σm² = {QM_f[j]:<8d} 均值 = {avr:8.2f} 方差 = {var:10.2f}{flag}")
    print()
    print("  注意：单点平移会让方差变成负数（可被察觉），")
    print("        但同时调 M 与 QM 两个位，伪造结果在统计上完全自洽 —— 无法靠常识识破。")

    # ========================================================= 修补测试
    hr("STEP 6 · 修补测试：CT^N 绑定校验能否拦住？")
    print("  直觉修补：CC 额外检查  CT'^N == h1(T)^{-N²g0}")
    lhs = pow(CT_forged, S.pai.N, S.pai.N2)
    rhs = ctN_expected
    print(f"  CT'^N      = {str(lhs)[:40]}…")
    print(f"  h1^(-N^2*g0) = {str(rhs)[:40]}…")
    print(f"  两者相等？  {'相等 → 校验通过，攻击未被发现' if lhs == rhs else '不等 → 校验能拦住'}")
    print()
    print("  原因：CT = g^Q·M，g = 1+N，故 g^{NΔ} = (1+N)^{NΔ} ≡ 1 (mod N²)")
    print("        乘 N 次方恰好把消息分量 Q 消掉，只留下与 Δ 无关的掩码。")
    print("        → 这个修补在代数上必然失效，不是实现问题。")

    # 更强的攻击：随机替换
    print()
    print("  加强版：把 CT 直接换成「任意随机值」——验证同样通过：")
    CT_rand = RNG.randrange(2, S.pai.N2)
    CT_rand = CT_rand * S.pai.g % S.pai.N2
    print(f"    CC 验证: {'通过' if S.cc_verify(agg, tn_cc) else '失败'}   "
          f"（验证函数只吃 s、φ、t、b，签名里根本没有 CT 这个参数）")

    # ========================================================= 掉线实验
    hr("STEP 7 · 附带实验：单台电表掉线")
    print("  零和掩码要求恰好 n 台全部到齐：g0 + Σg_i ≡ 0 (mod λ)")
    partial = payload[: n - 1]
    CT_p = 1
    for (CTi, _, _) in partial:
        CT_p = CT_p * CTi % S.pai.N2
    agg_p = dict(agg, CT=CT_p)
    N, N2 = S.pai.N, S.pai.N2
    W = CT_p * pow(h1_bytes(T, N), (N * S.g0), N2) % N2
    print(f"  少 1 台后 (W-1) 能否被 N 整除: {'能' if (W - 1) % N == 0 else '不能'}")
    if (W - 1) % N == 0:
        print(f"  解密值 = {(W-1)//N}")
    else:
        print("  → 掩码未消掉，解密失败：整轮 2k 个统计量全部作废")

    # ========================================================= 结论
    hr("结论")
    print("  [已证实] 诚实协议正确：解密、均值、方差与真实值完全一致")
    print("  [已证实] 攻击 A 成立：AG 只需改 CT，就能把指定类型的均值精确平移 δ，")
    print("           且验证方程照常通过、其余统计量不受影响")
    print("  [已证实] 最自然的 CT^N 绑定修补必然失效（g^{NΔ} ≡ 1 mod N²）")
    print("  [已证实] 单台掉线 → 掩码无法消除 → 整轮报废")
    print()
    print("  ★ Go 决策：题目成立，且比预期更难 —— 修补需要改协议结构，")
    print("    不能靠加一行检查。这反而是论文的分量所在。")


if __name__ == "__main__":
    t0 = time.time()
    main()
    print(f"\n总耗时 {time.time() - t0:.2f}s")
