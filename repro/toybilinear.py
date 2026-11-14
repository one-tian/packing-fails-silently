import hashlib

# ---------------------------------------------------------------- F_{p^2}
P_PAIR = None      # 曲线基域素数，由 init() 设置
ORD = None         # 配对群阶 r，由 init() 设置
NEG_ONE = None     # F_{p^2} 中的 -1


class F2:
    """F_{p^2} = F_p[i] / (i^2 + 1)，元素 a + b·i"""
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a = a % P_PAIR
        self.b = b % P_PAIR

    def __add__(self, o):
        return F2(self.a + o.a, self.b + o.b)

    def __sub__(self, o):
        return F2(self.a - o.a, self.b - o.b)

    def __neg__(self):
        return F2(-self.a, -self.b)

    def __mul__(self, o):
        # (a+bi)(c+di) = (ac - bd) + (ad + bc)i
        return F2(self.a * o.a - self.b * o.b,
                  self.a * o.b + self.b * o.a)

    def __truediv__(self, o):
        return self * o.inv()

    def __pow__(self, e):
        e %= (P_PAIR * P_PAIR - 1)
        res, base = F2(1), self
        while e:
            if e & 1:
                res = res * base
            base = base * base
            e >>= 1
        return res

    def inv(self):
        # (a+bi)^-1 = (a - bi)/(a^2 + b^2)
        n = (self.a * self.a + self.b * self.b) % P_PAIR
        if n == 0:
            raise ZeroDivisionError
        ni = pow(n, -1, P_PAIR)
        return F2(self.a * ni, -self.b * ni)

    def __eq__(self, o):
        return isinstance(o, F2) and self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def is_one(self):
        return self.a == 1 and self.b == 0

    def is_zero(self):
        return self.a == 0 and self.b == 0

    def __repr__(self):
        return f"({self.a},{self.b})"


def F2_one():
    return F2(1)


# ------------------------------------------------------------ 曲线点运算
# 点用 (F2, F2) 表示，无穷远点用 None
def padd(P1, P2):
    if P1 is None:
        return P2
    if P2 is None:
        return P1
    x1, y1 = P1
    x2, y2 = P2
    if x1 == x2:
        if (y1 + y2).is_zero():
            return None
        return pdbl(P1)
    lam = (y2 - y1) / (x2 - x1)
    x3 = lam * lam - x1 - x2
    y3 = lam * (x1 - x3) - y1
    return (x3, y3)


def pdbl(P):
    if P is None:
        return None
    x, y = P
    if y.is_zero():
        return None
    # λ = (3x^2 + a) / 2y,  a = 1
    lam = (F2(3) * x * x + F2(1)) / (F2(2) * y)
    x3 = lam * lam - F2(2) * x
    y3 = lam * (x - x3) - y
    return (x3, y3)


def pmul(P, k):
    """标量乘（含负数）"""
    if k == 0 or P is None:
        return None
    if k < 0:
        P = (P[0], -P[1])
        k = -k
    R, B = None, P
    while k:
        if k & 1:
            R = padd(R, B)
        B = pdbl(B)
        k >>= 1
    return R


# --------------------------------------------------------------- 扭曲映射
def psi(P):
    """ψ(x, y) = (-x, i·y)：E(F_p) → E(F_{p^2})，是曲线自同构"""
    if P is None:
        return None
    x, y = P
    return (-x, F2(0) * y + F2(y.a, y.b) * F2(0, 1))


def psi_pt(P):
    if P is None:
        return None
    x, y = P
    return (-x, y * F2(0, 1))


# ------------------------------------------------------------- Miller 环
def _line(P1, P2, Q):
    """过 P1,P2 的直线在 Q 处的取值 l(Q) = (yQ - y1) - λ(xQ - x1)"""
    x1, y1 = P1
    x2, y2 = P2
    if x1 == x2:
        if (y1 + y2).is_zero():
            return F2(1)          # 竖直线，最终指数化后被消掉
        lam = (F2(3) * x1 * x1 + F2(1)) / (F2(2) * y1)
    else:
        lam = (y2 - y1) / (x2 - x1)
    return (Q[1] - y1) - lam * (Q[0] - x1)


def _miller(P, Q, order):
    T = P
    f = F2(1)
    for bit in bin(order)[3:]:          # 跳过最高位的 '1'
        f = f * f * _line(T, T, Q)
        T = pdbl(T)
        if bit == "1":
            f = f * _line(T, P, Q)
            T = padd(T, P)
    return f


def pairing(A, B):
    """ê(A,B) := Tate(A, ψ(B))，A,B ∈ E(F_p)[r]"""
    if A is None or B is None:
        return F2(1)
    f = _miller(A, psi_pt(B), ORD)
    return f ** ((P_PAIR * P_PAIR - 1) // ORD)


# --------------------------------------------------------------- 参数生成
def _is_prime(n, rounds=40):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for _ in range(rounds):
        a = int.from_bytes(hashlib.sha256(str(n).encode() +
                                          str(_).encode()).digest(), "big") % (n - 3) + 2
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


def _next_prime(n):
    if n % 2 == 0:
        n += 1
    while not _is_prime(n):
        n += 2
    return n


def init(bits=40, verbose=True):
    """构造 p = 4r-1，r 为 bits 位素数，p 为素数"""
    global P_PAIR, ORD
    r = _next_prime(2 ** bits + 12345)
    while True:
        p = 4 * r - 1
        if _is_prime(p):
            break
        r = _next_prime(r + 2)
    P_PAIR, ORD = p, r
    if verbose:
        print(f"[配对参数] r ({bits} bit) = {r}")
        print(f"[配对参数] p = 4r-1 = {p}   (p ≡ {p % 4} mod 4)")
        print(f"[配对参数] #E(F_p) = p+1 = 4r，嵌入次数 k = 2")
        print(f"[配对参数] GT ⊂ F_p^2*，元素 {2 * bits} bit 量级")
    return p, r


# ------------------------------------------------------------ 哈希到 G1
def hash_to_G1(msg: bytes):
    ctr = 0
    while True:
        h = hashlib.sha256(msg + ctr.to_bytes(4, "big")).digest()
        x = int.from_bytes(h, "big") % P_PAIR
        rhs = (pow(x, 3, P_PAIR) + x) % P_PAIR
        if rhs != 0 and pow(rhs, (P_PAIR - 1) // 2, P_PAIR) == 1:
            y = pow(rhs, (P_PAIR + 1) // 4, P_PAIR)
            Pt = pmul((F2(x), F2(y)), 4)      # 乘余因子 4 → 阶整除 r
            if Pt is not None:
                return Pt
        ctr += 1


def rand_G1(seed: bytes):
    return hash_to_G1(seed)


# ------------------------------------------------------------------ 自检
def self_test(verbose=True):
    ok = True
    g = hash_to_G1(b"generator")
    assert pmul(g, ORD) is None, "生成元阶应为 r"

    # 双线性： ê(aP, bQ) = ê(P,Q)^{ab}
    Q = hash_to_G1(b"second")
    a, b = 123456789, 987654321
    lhs = pairing(pmul(g, a), pmul(Q, b))
    rhs = pairing(g, Q) ** (a * b)
    b1 = (lhs == rhs)
    ok &= b1
    if verbose:
        print(f"[自检] 双线性 ê(aP,bQ)=ê(P,Q)^(ab) : {'通过' if b1 else '失败'}")

    # 非退化
    b2 = not pairing(g, Q).is_one()
    ok &= b2
    if verbose:
        print(f"[自检] 非退化 ê(P,Q) ≠ 1          : {'通过' if b2 else '失败'}")

    # 线性 ê(A+B, Q) = ê(A,Q)·ê(B,Q)
    A, B = pmul(g, 7), pmul(g, 11)
    b3 = pairing(padd(A, B), Q) == pairing(A, Q) * pairing(B, Q)
    ok &= b3
    if verbose:
        print(f"[自检] 第一分量线性               : {'通过' if b3 else '失败'}")

    b4 = pairing(g, padd(pmul(Q, 7), pmul(Q, 11))) == pairing(g, pmul(Q, 18))
    ok &= b4
    if verbose:
        print(f"[自检] 第二分量线性               : {'通过' if b4 else '失败'}")
    return ok


if __name__ == "__main__":
    init(40)
    self_test()
