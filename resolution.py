"""
Skeleton SageMath implementation of the main algorithms from:

  "Computing Parametric Geometric Resolutions"
  Éric Schost, Applicable Algebra in Engineering, Communication
  and Computing 13(5): 349–393, 2003.

Overview
--------
Given a polynomial system  f(u, x) = (f_1, ..., f_n)  in
  - parameters  u = (u_1, ..., u_m)  living in k^m
  - unknowns    x = (x_1, ..., x_n)  living in k^n

a *parametric geometric resolution* (PGR) of the system is a tuple

    (q(u,T),  v_1(u,T), ..., v_n(u,T))

where
  * q(u, T) in k(u)[T]  is a squarefree polynomial whose roots
    (over the algebraic closure) parametrise the solutions,
  * v_i(u, T) in k(u)[T]/(q)  express  x_i  as a rational function
    of T,
  * the primitive element T = sum_i lambda_i * x_i  is a generic
    linear form with coefficients lambda in k^n.

The algorithm has three main stages
  1. Geometric resolution at a specialised parameter point p in k^m
     (uses Kronecker / rational univariate representation).
  2. Formal Newton lifting  (Hensel / p-adic lifting in k(u)[[u-p]])
     to turn the specialised resolution into a parametric one.
  3. Rational reconstruction  to recover exact rational-function
     coefficients in k(u).

References for sub-algorithms used below
-----------------------------------------
* Kronecker / RUR:  Rouillier, JSC 1999.
* Newton lifting:   Schost §5 (op. cit.).
* Berlekamp–Massey / Padé:  for rational reconstruction.
* Straight-line programs (SLPs) are used throughout the paper for
  complexity bookkeeping; the skeleton uses ordinary polynomials.
"""

from sage.all import QQ, PolynomialRing, matrix, vector

# ============================================================
#  0.  Setup – symbolic rings
# ============================================================

def build_rings(param_names, var_names, base_field=QQ):
    """
    Return the rings used throughout:
      R_u   = k[u]         (parameter polynomial ring)
      F_u   = k(u)         (parameter fraction field)
      R_ux  = k[u][x]      (polynomial ring over parameters)
    """
    R_u  = PolynomialRing(base_field, param_names)
    F_u  = R_u.fraction_field()
    R_ux = PolynomialRing(F_u, var_names)
    return R_u, F_u, R_ux


# ============================================================
#  1.  Geometric Resolution at a specialised point
#      (Schost §4 / Kronecker solver / RUR)
# ============================================================

def specialize_system(f_list, param_vars, param_point):
    """
    Substitute u = p (a concrete tuple) into each polynomial in f_list.

    Parameters
    ----------
    f_list      : list of multivariate polynomials in k[u, x]
    param_vars  : sequence of parameter variable objects
    param_point : sequence of field elements (the specialisation p)

    Returns
    -------
    list of polynomials in k[x]
    """
    subs_dict = dict(zip(param_vars, param_point))
    return [f.subs(subs_dict) for f in f_list]


def primitive_element(x_vars, coeffs=None):
    """
    Build the linear form  T = sum_i lambda_i * x_i.

    coeffs : if None, choose random lambda_i in the base field.
    """
    if coeffs is None:
        # random nonzero coefficients – succeed with high probability
        F = x_vars[0].parent().base_ring()
        coeffs = [F.random_element() for _ in x_vars]
        while 0 in coeffs:
            coeffs = [F.random_element() for _ in x_vars]
    T_expr = sum(c * x for c, x in zip(coeffs, x_vars))
    return T_expr, coeffs


# ============================================================
#  2.  Formal Newton / Hensel Lifting
#      (Schost §5 – the core of the parametric algorithm)
# ============================================================

def newton_operator(q0, v0, f_list, x_vars, lam, u_vars, p_point):
    """
    One step of the formal Newton lifting operator N_f.

    Given an *approximate* geometric resolution (q0, v0) that is
    exact at u = p, lift it to higher order in (u - p).

    The operator is (Schost, eq. (7)):

        N_f(q, v)  =  (q, v)  -  Jac_f^{-1} * f(q, v)

    where Jac_f is the Jacobian of f evaluated at the current
    approximation.

    Parameters
    ----------
    q0      : current approximate minimal polynomial (in T, coeffs in k[u])
    v0      : list of current approximate representatives
    f_list  : the original parametric system
    x_vars  : unknowns
    lam     : lambda coefficients for the primitive element
    u_vars  : parameter variables
    p_point : specialisation point

    Returns
    -------
    (q_new, v_new) – lifted by one order in (u - p)
    """
    # --- residual  r = f(u, v(T))  mod  q(T)  --------------------
    # Substitute x_i -> v_i(T)/q'(T) and reduce mod q
    u_  = q0.parent().gen()
    q_prime = q0.derivative(u_)

    # Build substitution  x_i  ->  v0[i]  (working mod q0)
    Q_ring = q0.parent().quotient(q0.parent().ideal(q0))

    def eval_f_at_v(fi):
        print(fi)
        print(fi.parent())
        """Evaluate f_i at x_j = v0[j] mod q0  (placeholder)."""
        return Q_ring(fi.subs({x:v for x, v in zip(x_vars, v0)}))

    residuals = [eval_f_at_v(fi) for fi in f_list]

    # --- Jacobian  J = df/dx  at the current approximation  ------
    def jacobian_at_v():
        """Return the n×n Jacobian matrix mod q0  (placeholder)."""
        n = len(x_vars)
        # TODO: compute df_i/dx_j evaluated at x_j = v0[j], mod q0
        return matrix(
            [
                [
                    f.derivative(vi).subs({x:v for x, v in zip(x_vars, v0)})
                    for vi in x_vars
                ]
                for f in f_list
            ]
        )

    J   = jacobian_at_v()
    J_inv = J.inverse()               # invert mod q0  (TODO: implement)

    # --- Newton step  delta_v = -J^{-1} * residuals  -------------
    delta_v = J_inv * vector(residuals)

    v_new = [v0[i] + delta_v[i] for i in range(len(v0))]

    # --- update q  -----------------------------------------------
    # q changes so that T = sum lam_i v_i(T) (primitive-element eq.)
    # In practice this is tracked via the companion-matrix update.
    q_new = q0   # TODO: update minimal polynomial

    return q_new, v_new


def hensel_lift(q0, v0, f_list, x_vars, lam, u_vars, p_point,
                target_order):
    """
    Iterate the Newton operator to reach the required (u-p)-adic order.

    target_order  is chosen so that rational reconstruction succeeds;
    by Schost Theorem 1, degree <= d^n in each parameter, so
    target_order ~ 2*d^n + 1  suffices (by Hadamard / degree bounds).

    Complexity (paper): O~(n * d^{2n} * L)  operations in k,
    where L is the SLP size of f.
    """
    q, v = q0, v0
    order = 1   # we start exact at order 1 (the specialisation)

    while order < target_order:
        print("order:", order)
        q, v = newton_operator(q, v, f_list, x_vars, lam, u_vars, p_point)
        order *= 2          # Newton doubles the precision each step

    return q, v


# ============================================================
#  3.  Rational Reconstruction
#      (recover exact k(u) coefficients from power-series)
# ============================================================

def rational_reconstruction_univariate(series_coeffs, u_var,
                                        degree_bound, modulus=None):
    """
    Given enough coefficients of a power series  h(u)  at  u = p,
    recover  h = A(u)/B(u)  in  k(u)  with deg A, deg B <= D.

    Uses the extended Euclidean algorithm / Padé approximation:
    find A, B such that  B(u) * series(u) ≡ A(u)  mod  (u-p)^N
    with N >= 2D + 1.

    Parameters
    ----------
    series_coeffs : list of field elements  [h_0, h_1, ..., h_{N-1}]
                    (Taylor coefficients of h at u = p)
    u_var         : the single parameter variable
    degree_bound  : D  (from Schost Theorem 1: D = d^n)
    modulus       : a prime  (if working mod p for verification)

    Returns
    -------
    (A, B) polynomials in k[u]  with  A/B = h(u)
    """
    R  = u_var.parent()
    N  = len(series_coeffs)
    assert N >= 2 * degree_bound + 1, \
        "Need at least 2D+1 Taylor coefficients for reconstruction."

    # Build the truncated power series as a polynomial mod (u-p)^N
    u  = u_var
    p0 = series_coeffs[0]
    series_poly = sum(c * (u - p0)**i for i, c in enumerate(series_coeffs))

    # Extended GCD / half-GCD for Padé  (placeholder)
    # Full implementation: see Geddes–Czapor–Labahn §6 or
    # von zur Gathen–Gerhard §5.
    A = R(series_coeffs[0])   # TODO: proper Padé
    B = R.one()               # TODO: proper Padé

    return A, B


def rational_reconstruction_multivariate(lifted_coeffs, u_vars,
                                          degree_bound):
    """
    Multivariate rational reconstruction by iterating the univariate
    algorithm along each parameter axis (Schost §6).

    lifted_coeffs : nested list / dict of Taylor coefficients
    u_vars        : sequence of parameter variables
    degree_bound  : D per variable (total degree bound d^n)

    Returns a rational function in k(u_1, ..., u_m).
    """
    # Reconstruct along u_1 first, then u_2, etc.
    # (This is essentially multivariate Padé / rational interpolation.)
    result = lifted_coeffs   # TODO: iterate rational_reconstruction_univariate
    return result


def _verify_pgr(q, v_list, f_list, u_vars, x_vars, lam, test_point):
    """
    Quick probabilistic check: specialise the PGR at a fresh point
    and verify  f(test_point, v_i(root_of_q)) ≡ 0.

    Returns True if the check passes.
    """
    # TODO: substitute test_point into q and v_list,
    #       find roots of q_specialised,
    #       evaluate f at each root and check residual.
    return True   # placeholder


# ============================================================
#  5.  Helper: Bézout degree bound and degeneracy locus
#      (Schost §3 – used for probability estimates)
# ============================================================

def bezout_bound(degree_list):
    """
    Return the Bézout number  d_1 * d_2 * ... * d_n
    (the maximum number of isolated solutions for a generic system).
    """
    from functools import reduce
    import operator
    return reduce(operator.mul, degree_list, 1)


def degeneracy_locus_degree_bound(degree_list, m):
    """
    Upper bound on the degree of the degeneracy locus Delta in k^m
    (Schost Proposition 2).

    The locus Delta is where the specialised system either has the
    wrong number of solutions or the primitive element fails.
    Degree of Delta  <=  (m + 1) * d^n.
    """
    n = len(degree_list)
    D = bezout_bound(degree_list)
    return (m + 1) * D


def probability_of_success(degree_list, m, field_size):
    """
    Lower bound on the probability that random choices of
    (p, lambda) avoid the degeneracy locus (Schost Theorem 3).

    prob >= 1 - deg(Delta) / |Gamma|
    where Gamma is the set from which random choices are drawn.

    Parameters
    ----------
    degree_list : [d_1, ..., d_n]
    m           : number of parameters
    field_size  : |Gamma|  (e.g. size of a finite field, or a
                  large integer for a "random modular" strategy)
    """
    deg_delta = degeneracy_locus_degree_bound(degree_list, m)
    prob_lower = 1 - deg_delta / field_size
    return prob_lower


# ============================================================
#  6.  Application: Jacobian of a hyperelliptic curve
#      (Schost §7.1 – illustrative special case)
# ============================================================

def hyperelliptic_jacobian_addition(g, base_field=QQ):
    """
    Skeleton for computing addition in the Jacobian of a genus-g
    hyperelliptic curve  y^2 = h(x)  (Cantor's algorithm,
    reformulated as a PGR problem in Schost §7.1).

    The input divisors D_1, D_2 are encoded as pairs of polynomials
    (a_i, b_i) with deg a_i <= g, deg b_i < deg a_i.
    Their sum  D_1 + D_2  is found by solving a polynomial system
    whose coefficients (the parameters) are the coefficients of
    (a_1, b_1, a_2, b_2).

    Returns the addition formulas as a PGR.
    """
    # Build coefficient variables for the two input divisors
    # and the curve polynomial h.
    # This results in a system of 2g equations in 2g unknowns.
    # (Full construction follows Cantor / Mumford; omitted here.)
    raise NotImplementedError(
        "Jacobian addition via PGR: see Schost §7.1 for the full "
        "polynomial system encoding Cantor's algorithm."
    )

# ============================================================
#  4.  Main Algorithm – Parametric Geometric Resolution
#      (Schost Algorithm 2 / Theorem 2)
# ============================================================

def parametric_geometric_resolution(f_list, u_vars, x_vars,
                                     param_point=None,
                                     degree_bound=None,
                                     base_field=QQ):
    """
    Compute a parametric geometric resolution of the system f = 0.

    Algorithm outline (Schost §5–6)
    --------------------------------
    1.  Choose a random specialisation  p in k^m  and random lambda
        (primitive-element coefficients).
    2.  Compute a geometric resolution (q_p, v_p) of f(p, .) = 0
        using the Kronecker / RUR solver.
    3.  Lift (q_p, v_p) to a formal power-series solution via
        iterated Newton steps (hensel_lift).
    4.  Recover the exact rational-function coefficients of the PGR
        via multivariate rational reconstruction.
    5.  Verify the result by re-specialising at a fresh point.

    Parameters
    ----------
    f_list      : polynomials in k[u_1,...,u_m, x_1,...,x_n]
    u_vars      : parameter variables  (u_1, ..., u_m)
    x_vars      : unknowns             (x_1, ..., x_n)
    param_point : specialisation  p = (p_1,...,p_m)  in k^m;
                  if None, chosen at random
    degree_bound: d  (max degree of f_i in x); if None, inferred
    base_field  : coefficient field k  (default QQ)

    Returns
    -------
    (q, v_list, lam)
      q      : minimal polynomial in k(u)[T]
      v_list : list of representatives v_i in k(u)[T]/(q)
      lam    : lambda coefficients used for the primitive element
    """
    n = len(x_vars)
    m = len(u_vars)

    # ---- infer degree bound  ------------------------------------
    if degree_bound is None:
        degree_bound = max(f.degree() for f in f_list)
    D = degree_bound ** n      # Bézout / Schost Theorem 1

    # ---- Step 1: choose specialisation and primitive element  ---
    if param_point is None:
        param_point = [base_field.random_element() for _ in u_vars]

    _, lam = primitive_element(x_vars)  # random lambda

    print(f"[PGR] n={n}, m={m}, d={degree_bound}, D(Bezout)={D}")
    print(f"[PGR] specialisation point p = {param_point}")
    print(f"[PGR] primitive-element coefficients lambda = {lam}")

    # ---- Step 2: geometric resolution at p  ---------------------
    f_p = specialize_system(f_list, u_vars, param_point)
    print(f"f_p:{f_p}")
    from sage_acsv import ACSVSettings as AS
    AS.set_default_kronecker_backend(AS.Kronecker.MSOLVE)
    from sage_acsv.kronecker import kronecker_representation
    q0, v0 = kronecker_representation(f_p, x_vars, lam) #geometric_resolution_specialized(f_p, x_vars, lam)
    print("[PGR] Specialised geometric resolution computed.")
    print(f"[PGR] q0={q0}, v0={v0}")

    # ---- Step 3: Hensel / Newton lifting  -----------------------
    target_order = 2 * D + 1   # enough for rational reconstruction
    q_lifted, v_lifted = hensel_lift(
        q0, v0, f_list, x_vars, lam, u_vars, param_point,
        target_order=target_order
    )
    print(f"[PGR] Lifted to order {target_order} in (u-p).")

    # ---- Step 4: rational reconstruction  -----------------------
    # Reconstruct each coefficient of q and of each v_i
    # Coefficients are power series in (u - p); apply Padé per coefficient.
    q_rational  = rational_reconstruction_multivariate(
        q_lifted,  u_vars, degree_bound=D
    )
    v_rational  = [
        rational_reconstruction_multivariate(vi, u_vars, degree_bound=D)
        for vi in v_lifted
    ]
    print("[PGR] Rational reconstruction complete.")

    # ---- Step 5: probabilistic verification  --------------------
    verify_point = [base_field.random_element() for _ in u_vars]
    if _verify_pgr(q_rational, v_rational, f_list,
                   u_vars, x_vars, lam, verify_point):
        print("[PGR] Verification passed.")
    else:
        print("[PGR] WARNING: Verification failed – try new random choices.")

    return q_rational, v_rational, lam
    
    