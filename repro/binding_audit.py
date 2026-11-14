import hashlib
import random
import time
from math import isqrt

import toybilinear as tb

SEP = "=" * 78
RNG = random.Random(20261111)


def hr(t=""):
    print()
    print(SEP)
    if t:
        print(t)
        print(SEP)


def is_prime(n, rounds=32):
    return tb._is_prime(n, rounds)


def gen_prime(bits, rng):
    while True:
        n = rng.getrandbits(bits) | (1 << (bits - 1)) | 1
        if is_prime(n):
            return n


# =============================================================== BSGS
def bsgs(P, Q, bound):
    """求 x ∈ [0, bound) 使 x·P = Q（曲线点群）。用于小值域解密。"""
    m = isqrt(bound) + 1
    table = {}
    cur = None
    for j in range(m):
        if cur not in table:
            table[cur] = j
        cur = tb.padd(cur, P)
    mP = tb.pmul(P, m)
    negmP = None if mP is None else (mP[0], -mP[1])
    gamma = Q
    for i in range(m + 1):
        if gamma in table:
            x = i * m + table[gamma]
            return x if x < bound else None
        gamma = tb.padd(gamma, negmP)
    return None


def bsgs_mod(base, target, mod, bound):
    """求 x ∈ [0, bound) 使 base^x ≡ target (mod mod)。整数群版本。"""
    m = isqrt(bound) + 1
    table = {}
    cur = 1
    for j in range(m):
        table.setdefault(cur, j)
        cur = cur * base % mod
    bm = pow(base, m, mod)
    bminv = pow(bm, -1, mod)
    gamma = target
    for i in range(m + 1):
        if gamma in table:
            x = i * m + table[gamma]
            return x if x < bound else None
        gamma = gamma * bminv % mod
    return None


# =============================================================== L1 · 三种密码体制
class PaillierCipher:
    """VPMDA 用的改造 Paillier：g = 1+N，解密不需要 DLP"""

    name = "Paillier (g=1+N)"

    def __init__(self, bits=256):
        while True:
            self.p = gen_prime(bits, RNG)
            self.q = gen_prime(bits, RNG)
            if self.p != self.q:
                break
        self.N = self.p * self.q
        self.N2 = self.N * self.N
        self.g = 1 + self.N
        self.modulus = self.N2
        self.lam = (self.p - 1) * (self.q - 1)

    def enc(self, m, rnd_exp):
        """
        CT = g^m · h1^{N·rnd_exp}，掩码由零和机制在解密前消掉。
        本审计只关心 g^m 分量，故直接返回 g^m（随机化因子的处理见 03 报告）。
        """
        return pow(self.g, m, self.N2)

    def shift(self, CT, delta):
        """P1：公开可算的平移元素 g^Δ"""
        return CT * pow(self.g, delta, self.N2) % self.N2

    def dec(self, CT):
        W = CT % self.N2
        assert (W - 1) % self.N == 0
        return (W - 1) // self.N


class BGNCipher:
    """
    BGN 型：C = g^m · h^r，h 落在小子群中。
    真 BGN 用合数阶双线性群；这里用 Z_p^*（p 为素数）上的素数阶子群模拟
    g^m·h^r 的代数结构 —— 平移前提只依赖该结构，不依赖群阶的合数性。
    SA-MAD 的"四素数 BGN 双消息模式"再加一个 g_j^{m_j}，形式不变。
    """

    name = "BGN 型 (g^m·h^r)"

    def __init__(self, space=65537):
        self.s = space            # 明文空间
        e = 1024
        while True:
            p = e * self.s + 1
            if is_prime(p):
                self.p = p
                break
            e += 2
        self.e = e                # h 的阶
        while True:
            g = RNG.randrange(2, self.p - 1)
            if (pow(g, (self.p - 1) // 2, self.p) != 1
                    and pow(g, (self.p - 1) // self.s, self.p) != 1):
                self.g = g
                break
        self.h = pow(self.g, self.s, self.p)   # 阶为 e
        self.modulus = self.p
        self.bound = space

    def enc(self, m, r):
        return pow(self.g, m, self.p) * pow(self.h, r, self.p) % self.p

    def shift(self, CT, delta):
        return CT * pow(self.g, delta, self.p) % self.p

    def dec(self, CT):
        """C^e = g^{em}·(h^e)^r = (g^e)^m，消掉随机化后在阶为 s 的子群上解 DLP"""
        base = pow(self.g, self.e, self.p)
        t = pow(CT, self.e, self.p)
        return bsgs_mod(base, t, self.p, self.s)


class ECElGamalCipher:
    """EC-ElGamal 加法同态：CT = (rG, mG + r·pk)。LPPMM-DA 这一族的轻量路线。"""

    name = "EC-ElGamal (C1,C2)"

    def __init__(self):
        self.G = tb.hash_to_G1(b"ecgen")
        self.x = RNG.randrange(2, tb.ORD)
        self.pk = tb.pmul(self.G, self.x)
        self.modulus = None
        self.bound = 8000

    def enc(self, m, r):
        return (tb.pmul(self.G, r), tb.padd(tb.pmul(self.G, m), tb.pmul(self.pk, r)))

    def shift(self, CT, delta):
        """P1：第二分量直接加 Δ·G。攻击者不需要任何秘密。"""
        return (CT[0], tb.padd(CT[1], tb.pmul(self.G, delta)))

    def dec(self, CT):
        mG = tb.padd(CT[1], tb.pmul(CT[0], -self.x))
        return bsgs(self.G, mG, self.bound)


# =============================================================== L2 · 认证作用域
class Scope:
    NONE = "NONE"
    INDIVIDUAL = "INDIVIDUAL"
    AGGREGATE_BY_AG = "AGGREGATE_BY_AG"
    MAC_BINDING = "MAC_BINDING"


class BLSAggregator:
    """BLS 聚合签名（真实配对运算）。σ = Σ sk_i·H(msg_i)，验 e(σ,g) = Π e(H(msg_i), pk_i)"""

    def __init__(self, n):
        self.n = n
        self.g = tb.hash_to_G1(b"bls-gen")
        self.sk = [RNG.randrange(2, tb.ORD) for _ in range(n)]
        self.pk = [tb.pmul(self.g, s) for s in self.sk]

    def _h(self, msg: bytes):
        return tb.hash_to_G1(b"H|" + msg)

    def sign(self, i, msg: bytes):
        return tb.pmul(self._h(msg), self.sk[i])

    @staticmethod
    def agg(sigs):
        s = None
        for x in sigs:
            s = tb.padd(s, x)
        return s

    def verify(self, msgs, sigma):
        lhs = tb.pairing(sigma, self.g)
        rhs = None
        for i, m in enumerate(msgs):
            t = tb.pairing(self._h(m), self.pk[i])
            rhs = t if rhs is None else rhs * t
        return lhs == rhs


class AGAggregator:
    """聚合网关自己的密钥对——用来演示"让聚合者承诺聚合结果"为什么是循环论证"""

    def __init__(self):
        self.g = tb.hash_to_G1(b"bls-gen")
        self.sk = RNG.randrange(2, tb.ORD)
        self.pk = tb.pmul(self.g, self.sk)

    def sign(self, msg: bytes):
        return tb.pmul(tb.hash_to_G1(b"H|" + msg), self.sk)

    def verify(self, msg: bytes, sigma):
        return tb.pairing(sigma, self.g) == tb.pairing(tb.hash_to_G1(b"H|" + msg), self.pk)


# =============================================================== 超递增打包
def build_superincreasing(k, bounds, n):
    h = list(bounds) + [b * b for b in bounds]
    v = [1]
    for a in range(1, 2 * k):
        acc = sum(v[j] * h[j] * n for j in range(a))
        v.append(acc + 1)
    return v, h


def peel(Q, v, k):
    M = [0] * k
    QM = [0] * k
    for j in range(k, 0, -1):
        idx = k + j - 1
        QM[j - 1] = Q // v[idx]
        Q -= v[idx] * QM[j - 1]
    for j in range(k, 0, -1):
        idx = j - 1
        M[j - 1] = Q // v[idx]
        Q -= v[idx] * M[j - 1]
    return M, QM, Q


# =============================================================== 一个可审计的"方案"
class PackedScheme:
    """
    参数化的打包聚合方案。
      cipher  : 密码体制实例
      scope   : 认证作用域
      pack    : 是否使用超递增打包（Paillier 走打包，另两种走单类型小值域）
    攻击接口只有一个：tamper(CT, delta)
    """

    def __init__(self, cipher, scope, n=5, k=2, bounds=(1000, 500), use_pack=True, bound_dec=6000):
        self.cipher, self.scope = cipher, scope
        self.n, self.k, self.bounds = n, k, bounds
        self.use_pack = use_pack
        self.bound_dec = bound_dec
        self.bls = BLSAggregator(n)
        self.ag = AGAggregator()
        if use_pack:
            self.v, self.h = build_superincreasing(k, bounds, n)
        else:
            self.v, self.h = [1], [bounds[0]]
        self.msg = [None] * n

    # ---------------- 诚实流程
    def encode(self, row):
        if self.use_pack:
            q = 0
            for j in range(self.k):
                q += self.v[j] * row[j] + self.v[self.k + j] * row[j] * row[j]
            return q
        return row[0]

    def report(self, rows):
        CTs, sigs, Qs = [], [], []
        for i, row in enumerate(rows):
            q = self.encode(row)
            CT = self.cipher.enc(q, RNG.randrange(2, 10 ** 6))
            CTs.append(CT)
            Qs.append(q)
            self.msg[i] = f"SM{i}".encode() + b"|" + hashlib.sha256(repr(CT).encode()).digest()
            sigs.append(self.bls.sign(i, self.msg[i]))
        self.CTs, self.Qs = CTs, Qs
        self.sigma = BLSAggregator.agg(sigs)
        return CTs

    def combine(self, CTs):
        if isinstance(self.cipher, ECElGamalCipher):
            c1, c2 = None, None
            for a, b in CTs:
                c1 = tb.padd(c1, a)
                c2 = tb.padd(c2, b)
            return (c1, c2)
        out = CTs[0]
        M = self.cipher.modulus
        for c in CTs[1:]:
            out = out * c % M
        return out

    # ---------------- 验证（三种作用域）
    def verify(self, agg_CT, scope, extra=None):
        if scope == Scope.NONE:
            return True
        if scope == Scope.INDIVIDUAL:
            # 逐条消息的聚合签名：只承诺每个 (id_i, CT_i)
            return self.bls.verify(self.msg, self.sigma)
        if scope == Scope.AGGREGATE_BY_AG:
            # 聚合者自己对新 A 签名 —— 验证必然通过（AGC 是攻击者本人）
            A = hashlib.sha256(repr(agg_CT).encode()).digest()
            sig = self.ag.sign(b"A|" + A)
            return self.ag.verify(b"A|" + A, sig)
        if scope == Scope.MAC_BINDING:
            k_mac, taus, rhos, mod = extra
            Q = self.cipher.dec(agg_CT)
            lhs = (k_mac * Q) % mod
            rhs = (sum(taus) - sum(rhos)) % mod
            return lhs == rhs
        raise ValueError(scope)

    # ---------------- 攻击
    def tamper(self, agg_CT, delta):
        return self.cipher.shift(agg_CT, delta)


# =============================================================== 实验
def main():
    t0 = time.time()
    tb.init(40, verbose=False)
    assert tb.self_test(verbose=False)

    hr("PART 0 · 原语自检")
    A = tb.hash_to_G1(b"x")
    print(f"  BLS 配对双线性/非退化          : 通过")
    P = tb.hash_to_G1(b"bsgs")
    x0 = 1234
    print(f"  BSGS 曲线版 (x=1234)           : {bsgs(P, tb.pmul(P, x0), 5000)}")
    print(f"  BSGS 整数版 (x=1234)           : {bsgs_mod(7, pow(7, x0, 10**9 + 7), 10**9 + 7, 5000)}")

    # ---------------------------------------------------------------- L1
    hr("PART 1 · L1 密码体制层：平移元素是否存在（P1）")
    print("  检验：对同一明文 m，构造 CT' = CT ⊞ τ(Δ)，看解密是否恰为 m+Δ")
    print()

    rows_l1 = []
    for cipher in (PaillierCipher(256), BGNCipher(), ECElGamalCipher()):
        m, delta, r = 777, 321, RNG.randrange(2, 10 ** 5)
        CT = cipher.enc(m, r)
        CT2 = cipher.shift(CT, delta)
        try:
            d1, d2 = cipher.dec(CT), cipher.dec(CT2)
        except AssertionError:
            d1 = d2 = None
        # 本质判据：CT' 是否恰等于"用同一随机数加密 m+Δ"所得到的合法密文
        coset = (CT2 == cipher.enc(m + delta, r))
        ok = (d1 == m and d2 == m + delta and coset)
        rows_l1.append((cipher.name, d1, d2, coset, ok))
        print(f"  {cipher.name:32s} m={m} Δ={delta} → Dec={d1}/{d2}  "
              f"CT'≡Enc(m+Δ,r)={'是' if coset else '否'}  {'P1 成立' if ok else 'P1 不成立'}")

    print()
    print("  结论：三种体制的密文都形如 g^m·(随机化)，都允许公开计算 g^Δ。")
    print("        P1 不是 Paillier 的偶然性质，而是「加法同态 + 随机化因子与消息可分离」的直接推论。")

    # ---------------------------------------------------------------- L2
    hr("PART 2 · L2 认证层：IA ⇏ AB（个体认证不蕴含聚合绑定）")
    print("  同一个打包方案，换四种认证作用域，看攻击是否被拦。")
    print("  n=5, k=2, h=(1000,500)，数据 = [(523,112),(148,45),(907,203),(612,87),(355,61)]")
    print()

    data = [(523, 112), (148, 45), (907, 203), (612, 87), (355, 61)]
    scheme = PackedScheme(PaillierCipher(256), Scope.NONE)
    CTs = scheme.report(data)
    agg = scheme.combine(CTs)
    Q_true = scheme.cipher.dec(agg)
    M, QM, rest = peel(Q_true, scheme.v, scheme.k)
    print(f"  诚实结果：Σm = {M}，Σm² = {QM}，剥离余项 = {rest}")
    print()

    # MAC 参数（R1）
    r_mod = tb.ORD
    k_mac = RNG.randrange(2, r_mod)
    rhos = [RNG.randrange(2, r_mod) for _ in range(5)]
    taus = [(k_mac * q + r) % r_mod for q, r in zip(scheme.Qs, rhos)]
    mac_extra = (k_mac, taus, rhos, r_mod)

    # 攻击目标：类型2 均值 200、方差 0（完整伪造）
    target_M2, target_QM2 = 1000, 200000
    a2, b2 = target_M2 - M[1], target_QM2 - QM[1]
    Delta = scheme.v[1] * a2 + scheme.v[3] * b2
    print(f"  攻击：Δ = v₂·{a2} + v₄·{b2} = {Delta}")
    print(f"        目标：类型2 均值 {target_M2/5:.2f}、方差 {target_QM2/5 - (target_M2/5)**2:.2f}")
    print()

    results = []
    for scope in (Scope.NONE, Scope.INDIVIDUAL, Scope.AGGREGATE_BY_AG, Scope.MAC_BINDING):
        forged = scheme.tamper(agg, Delta)
        extra = mac_extra if scope == Scope.MAC_BINDING else None
        passed = scheme.verify(forged, scope, extra)
        Q_f = scheme.cipher.dec(forged)
        Mf, QMf, restf = peel(Q_f, scheme.v, scheme.k)
        avr = Mf[1] / 5
        var = QMf[1] / 5 - avr * avr
        results.append(dict(scope=scope, passed=passed, M=Mf, QM=QMf, avr=avr, var=var, rest=restf))
        tag = "验证通过 ← 攻击成功" if passed else "验证失败 ← 已拦截"
        print(f"  [{scope:18s}] {tag}")
        note = "（下行是伪造密文的解密值，说明攻击目标已达成，但验证层拒绝）" if not passed else ""
        print(f"      伪造密文解出 类型2: Σm={Mf[1]:<6d} 均值={avr:8.2f} 方差={var:10.2f}{note}")

    print()
    print("  ★ 关键一行：INDIVIDUAL 作用域下攻击照样通过。")
    print("    因为聚合签名承诺的是「每个 CT_i 没被改」，而不是「Π CT_i 等于什么」。")
    print("    这两个命题在代数上相互独立 —— IA（个体认证）不蕴含 AB（聚合绑定）。")

    # ---------------------------------------------------------------- L2b
    hr("PART 2B · 为什么「让聚合者签聚合结果」是循环论证")
    print("  AGGREGATE_BY_AG 的验证为什么通过？因为签名人就是攻击者本人。")
    print("  任何由 AG 生成的、对 CT_agg 的承诺，AG 在篡改后都能重新生成 —— 它不构成约束。")
    print("  ⇒ 聚合绑定必须由**被聚合者共同**生成，不能委托给聚合者。这是修补设计的硬约束。")

    # ---------------------------------------------------------------- R1
    hr("PART 3 · R1 修补：MAC 绑定实测")
    print("  机制：每台 SM 额外发 τ_i = (k·Q_i + ρ_i) mod M，ρ_i 由 SM 与 CC 的 PRG 生成。")
    print("        CC 验 k·Q ≟ Στ_i − Σρ_i (mod M)。")
    print()
    print("  先看模数选择的影响（用真实密文检验，不是纸面推演）：")
    for label, mod in (("mod r（配对群阶，41 bit）", tb.ORD),
                       ("mod N（Paillier 模数，512 bit）", scheme.cipher.N)):
        kk = RNG.randrange(2, min(mod, 10 ** 9))
        rr = [RNG.randrange(2, mod) for _ in range(5)]
        tt = [(kk * q + x) % mod for q, x in zip(scheme.Qs, rr)]
        ok_h = ((kk * Q_true) % mod) == ((sum(tt) - sum(rr)) % mod)
        # 攻击者令 Δ = M：MAC 是否漏检？前提是这步平移真的改变了明文
        CT_blind = scheme.tamper(agg, mod)
        Q_blind = scheme.cipher.dec(CT_blind)
        changed = (Q_blind != Q_true)
        ok_a = ((kk * Q_blind) % mod) == ((sum(tt) - sum(rr)) % mod)
        verdict = "盲区可用 ← 危险" if (changed and ok_a) else ("平移无效" if not changed else "被拦截")
        print(f"  {label:36s} 诚实={ok_h}  平移后明文改变={changed}  MAC通过={ok_a}  → {verdict}")
    print()
    print("  ⇒ mod r 确实存在盲区：Δ = r 时明文改变、MAC 却照样通过。")
    print("     mod N 看似安全，但只是因为 Paillier 里 g^N ≡ 1 (mod N²)——")
    print("     换到 EC-ElGamal（群阶 r），任何 Δ 都是有效平移，mod r 就无遮拦。")
    print("     ⇒ MAC 的模数必须与「明文空间」一致，而不是随手取群阶。")

    print("  正式配置（mod N）：")
    Nmod = scheme.cipher.N
    kk = RNG.randrange(2, Nmod)
    rr = [RNG.randrange(2, Nmod) for _ in range(5)]
    tt = [(kk * q + x) % Nmod for q, x in zip(scheme.Qs, rr)]
    extra = (kk, tt, rr, Nmod)

    for name, delta in (("单点平移 Δ=v₂·100", scheme.v[1] * 100),
                        ("完整伪造 Δ（均值200/方差0）", Delta)):
        forged = scheme.tamper(agg, delta)
        passed = scheme.verify(forged, Scope.MAC_BINDING, extra)
        print(f"  {name:28s} → {'通过 ← 失败' if passed else '拒绝 ← 已拦截'}")

    # 成本
    t_a = time.time()
    for _ in range(2000):
        _ = (kk * Q_true) % Nmod
    t_b = time.time()
    print(f"  验证开销：1 次模乘 ≈ {(t_b - t_a) / 2000 * 1e6:.1f} μs（512 bit N）")
    print(f"  通信开销：每台 SM 多 1 个 |N| bit 标量 → 总计 +{scheme.cipher.N.bit_length()}n bit")

    # ---------------------------------------------------------------- L1 × L2 交叉
    hr("PART 4 · 判定矩阵：3 种密码体制 × 4 种认证作用域")
    print("  每一格都是真跑出来的，不是查表。")
    print()
    header = f"  {'密码体制':<34s}" + "".join(f"{s[:16]:<19s}" for s in
                                            (Scope.NONE, Scope.INDIVIDUAL,
                                             Scope.AGGREGATE_BY_AG, Scope.MAC_BINDING))
    print(header)
    print("  " + "-" * (34 + 19 * 4))

    for cipher, bound, use_pack in ((PaillierCipher(256), 6000, True),
                                    (BGNCipher(96), 6000, False),
                                    (ECElGamalCipher(), 6000, False)):
        sch = PackedScheme(cipher, Scope.NONE, use_pack=use_pack, bound_dec=bound)
        if use_pack:
            rr_rows = data
        else:
            rr_rows = [(x[0], 0) for x in data]     # 单类型，便于 DLP 解密
        CTs = sch.report(rr_rows)
        ag = sch.combine(CTs)
        try:
            Q = cipher.dec(ag)
        except Exception:
            Q = None
        dl = 137
        # MAC 参数
        NM = getattr(cipher, "N", None) or getattr(cipher, "p", None) or tb.ORD
        km = RNG.randrange(2, min(NM, 10 ** 12))
        rs = [RNG.randrange(2, min(NM, 10 ** 12)) for _ in range(5)]
        ts = [(km * q + x) % NM for q, x in zip(sch.Qs, rs)]
        line = f"  {cipher.name:<34s}"
        for scope in (Scope.NONE, Scope.INDIVIDUAL, Scope.AGGREGATE_BY_AG, Scope.MAC_BINDING):
            forged = sch.tamper(ag, dl)
            ex = (km, ts, rs, NM)
            try:
                p = sch.verify(forged, scope, ex)
            except Exception:
                p = None
            line += f"{('中招' if p else '拦截') if p is not None else 'n/a':<19s}"
        print(line)

    print()
    print("  读法：前两列全中招 ⇒ 缺陷与密码体制无关，与打包方式也无关；")
    print("        第三列全中招 ⇒ 把承诺交给聚合者是循环论证；")
    print("        第四列全拦截 ⇒ 只有「被聚合者共同产生、聚合者无法伪造」的绑定才有效。")

    # ---------------------------------------------------------------- 结论
    hr("结论")
    print("  [定理] P1 ∧ P2 ⇒ 普遍伪造。密码体制只决定平移元素的形式，不决定是否存在。")
    print("  [已实证] Paillier / BGN 型 / EC-ElGamal 三种体制的 P1 全部成立。")
    print("  [已实证] IA ⇏ AB：逐条认证（聚合签名/批量验证）挡不住聚合结果的篡改。")
    print("  [已实证] 聚合者自签无效：约束必须来自被聚合者。")
    print("  [已实证] R1（MAC 绑定）可拦截，但模数必须与明文空间匹配，否则存在模数盲区。")
    print()
    print(f"  总耗时 {time.time() - t0:.2f}s")


if __name__ == "__main__":
    main()
