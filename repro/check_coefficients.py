from __future__ import annotations

import hashlib
import hmac
import secrets
import struct
from typing import Sequence

P = (1 << 31) - 1
SEED_BYTES = 32


def new_master_key() -> bytes:
    """Generate a 256-bit master key with the operating system CSPRNG."""
    return secrets.token_bytes(SEED_BYTES)


def derive_round_seed(master_key: bytes, domain_id: bytes, epoch: int) -> bytes:
    """Domain-separated seed; never transmit/store master_key at meters."""
    if len(master_key) < SEED_BYTES:
        raise ValueError("master key must contain at least 256 bits")
    if not 0 <= epoch < (1 << 64):
        raise ValueError("epoch must fit uint64")
    msg = (b"smart-grid-checkdigit/round-seed/v1\0" +
           struct.pack(">I", len(domain_id)) + domain_id +
           struct.pack(">Q", epoch))
    return hmac.new(master_key, msg, hashlib.sha256).digest()


def _uniform_below(seed: bytes, p: int, context: bytes, index: int) -> int:
    """PRF-based rejection sampling, unbiased if HMAC is a PRF."""
    if p < 2:
        raise ValueError("p must be >= 2")
    space = 1 << 256
    cutoff = space - (space % p)
    counter = 0
    while True:
        msg = (b"smart-grid-checkdigit/coefficient/v1\0" +
               struct.pack(">I", len(context)) + context +
               struct.pack(">I", index) + struct.pack(">I", counter))
        x = int.from_bytes(hmac.new(seed, msg, hashlib.sha256).digest(), "big")
        if x < cutoff:
            return x % p
        counter += 1


def derive_coefficients(round_seed: bytes, domain_id: bytes, epoch: int,
                        k: int, p: int = P) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Return two independent k-vectors in Z_p, in manuscript ordering."""
    if len(round_seed) != SEED_BYTES:
        raise ValueError("round seed must be 256 bits")
    if k <= 0:
        raise ValueError("k must be positive")
    context = (struct.pack(">I", len(domain_id)) + domain_id +
               struct.pack(">Q", epoch))
    vals = tuple(_uniform_below(round_seed, p, context, i) for i in range(2*k))
    return vals[:k], vals[k:]


def verify_coefficient_delivery(master_key: bytes, delivered_seed: bytes,
                                domain_id: bytes, epoch: int) -> bool:
    """Constant-time check for the CC's epoch/domain seed commitment."""
    expected = derive_round_seed(master_key, domain_id, epoch)
    return hmac.compare_digest(expected, delivered_seed)


if __name__ == "__main__":
    master = new_master_key()
    d1, d2 = b"domain-01", b"domain-02"
    s11 = derive_round_seed(master, d1, 11)
    s12 = derive_round_seed(master, d1, 12)
    assert verify_coefficient_delivery(master, s11, d1, 11)
    assert not verify_coefficient_delivery(master, s11, d1, 12)
    c, cp = derive_coefficients(s11, d1, 11, k=3)
    assert len(c) == len(cp) == 3 and all(0 <= x < P for x in c + cp)
    assert derive_coefficients(derive_round_seed(master, d2, 11), d2, 11, 3) != (c, cp)
    assert derive_coefficients(s12, d1, 12, 3) != (c, cp)
    print("coefficient derivation self-check: OK")
