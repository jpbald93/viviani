"""Numeric check of the generalised Viviani identity for random simplices (dims 2-5).

For a simplex with vertices v_0..v_n in R^n and a point p (in the span = R^n):
  d_i(p) = signed distance from p to the hyperplane through the facet opposite v_i,
           positive on the side of v_i;  h_i = d_i(v_i).
Checks: sum_i d_i/h_i = 1; d_i/h_i = barycentric coordinate; and for a regular
simplex sum_i d_i = h (constant), unsigned for interior points.
"""
import numpy as np

rng = np.random.default_rng(0)

def signed_dists(V, p):
    n = V.shape[1]
    out, hs = [], []
    for i in range(n + 1):
        F = np.delete(V, i, axis=0)
        A = (F[1:] - F[0]).T                     # n x (n-1)
        q, _ = np.linalg.qr(A, mode="complete")
        nrm = q[:, -1]                           # normal to facet hyperplane
        if np.dot(V[i] - F[0], nrm) < 0:
            nrm = -nrm
        out.append(np.dot(p - F[0], nrm)); hs.append(np.dot(V[i] - F[0], nrm))
    return np.array(out), np.array(hs)

def regular_simplex(n):
    E = np.eye(n + 1)                            # regular simplex in R^{n+1}, project to R^n
    c = E - E.mean(axis=0)
    q, _ = np.linalg.qr(c.T)
    return c @ q[:, :n]

worst = 0.0
for n in range(2, 6):
    for _ in range(200):
        V = rng.normal(size=(n + 1, n))
        w = rng.normal(size=n + 1); w /= w.sum()
        p = w @ V
        d, h = signed_dists(V, p)
        worst = max(worst, abs((d / h).sum() - 1), np.abs(d / h - w).max())
    R = regular_simplex(n) * rng.uniform(0.5, 3)
    _, h = signed_dists(R, R[0])
    assert np.allclose(h, h[0])
    for _ in range(200):
        w = rng.normal(size=n + 1); w /= w.sum()
        d, _ = signed_dists(R, w @ R)
        worst = max(worst, abs(d.sum() - h[0]))
        w = rng.dirichlet(np.ones(n + 1))        # interior point: unsigned distances
        d, _ = signed_dists(R, w @ R)
        worst = max(worst, abs(np.abs(d).sum() - h[0]))
print(f"max error over dims 2-5: {worst:.3e}")
assert worst < 1e-9
print("OK")
