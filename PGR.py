from sage.all import QQ, QQbar, log, Ideal, PolynomialRing, xgcd, FractionField, matrix, SR, vector, PowerSeriesRing, TermOrder

def debug(*args, verbosity=1):
    threshold = 9
    if verbosity > threshold:
        print(*args)

def jacobian(sys, vs):
        return matrix(
            [
                [f.derivative(v) for v in vs]
                for f in sys
            ]
        )

def truncate_coeffs(f, params, degree):
    R_base_poly = params[0].numerator().parent()
    Quo_r = R_base_poly.quotient_ring(Ideal([R_base_poly(v) for v in params])**degree)
    return sum(
        [(Quo_r(c.numerator())*Quo_r(c.denominator()).inverse()).lift()*v for c, v in f]
    )

######## IMPLEMENTATION BY GEMINI - FOR TESTING

def truncate_base_poly(poly, params, max_degree):
    """Safely drops terms from a base polynomial exceeding max_degree."""
    if not poly: 
        return poly
    
    R_base = poly.parent()
    R = PolynomialRing(QQ, len(poly.parent().gens()), list(poly.parent().gens()))
    poly, params = apply_ring_morphism(R, poly, params)
    res = R(0)
    for c, v in poly:
        # exps is a tuple of degrees for each parameter
        if v.degree() < max_degree:
            res += c*v
    
    return R_base(res)

def expand_fraction(frac, params, max_degree):
    """Computes the Taylor expansion of N/D up to max_degree."""
    R_base = params[0].parent()
    num = R_base(frac.numerator())
    den = R_base(frac.denominator())
    
    # 1. Evaluate the denominator at the origin (params = 0)
    d0_val = den.subs({p: 0 for p in params})
    if d0_val == 0:
        raise ValueError("Division by zero: Denominator vanishes at expansion point.")
        
    # 2. Setup 1 / (d0 - M)
    d0 = R_base(d0_val)
    M = d0 - den
    M_over_d0 = M / d0
    
    inv_den = R_base(0)
    term = R_base(1) / d0
    
    # 3. Accumulate the geometric series
    for _ in range(max_degree):
        inv_den += term
        term = truncate_base_poly(term * M_over_d0, params, max_degree)
        
    # Multiply the numerator by the expanded denominator and truncate one last time
    return truncate_base_poly(num * inv_den, params, max_degree)

def truncate_coeffs(f, params, degree):
    """Truncates the fractional coefficients of a polynomial f."""
    res = 0
    for c, v in f:
        c_trunc = expand_fraction(c, params, degree)
        res += c_trunc * v
    return res

####### END

def mod_by_P(f, P):
    Quo = P.parent().quotient(P)
    return Quo(f).lift()

def mod_truncate(f, P, params, degree):
    return truncate_coeffs(mod_by_P(f, P), params, degree)

def inv(f, P):
    """
    Find inverse of f modulo P using extended Euclidean algorithm.
    Returns g such that f*g = 1 mod P.
    """

    Quo = P.parent().quotient(P)
    return Quo(f).inverse().lift()

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
    R = f_list[0].parent()
    R_new = PolynomialRing(QQ, [v for v in R.gens() if v not in param_vars])
    R_to_new = R.hom([param_point[i] for i in range(len(param_vars))] + list(R_new.gens()))
    return [R_to_new(f) for f in f_list], list(R_new.gens())

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

def to_shape_lemma(P, Qs, u_):
    Pd = P.derivative(u_)
    Pd_inv = xgcd(Pd, P)[1]
    return [Q*Pd_inv % P for Q in Qs]

def to_kronecker(P, Qs, params, u_, prec):
    Pd = P.derivative(u_)
    return [mod_truncate(Q*Pd, P, params, prec) for Q in Qs]

def apply_ring_morphism(R, *args):
    res = []
    for fs in args:
        if type(fs) == list:
            res.append([R(f) for f in fs])
        elif type(fs) == tuple:
            res.append((R(f) for f in fs))
        else:
            res.append(R(fs))
    return tuple(res)

def construct_rational(gamma, r, params, prec):
    debug("r:", r)
    #debug(params)
    R_base = r.parent()

    s = SR.var('s')
    ys = list(SR.var('y', len(params)-1)) if len(params) > 1 else []

    Rs = PolynomialRing(QQ, len(params)+1, [*params, s])
    R_base_to_Rs = R_base.hom(list(Rs.gens())[:-1])
    #debug("params", params)
    #debug(R_base_to_Rs)
    debug(R_base_to_Rs(params[0]))
    r, params = apply_ring_morphism(R_base_to_Rs, r, params)
    #debug("params", params)
    r_tilde = Rs(r.subs({v: v*s for v in params[1:]} | {params[0]: s}))
    s = Rs.gens()[-1]

    R_new_base = PolynomialRing(QQ, len(ys), [*ys]) if ys else QQ
    R_new = PowerSeriesRing(R_new_base, [s])
    R_poly = PolynomialRing(R_new_base, 1, [s])
    flatten_R_new = R_poly.flattening_morphism()

    # Convert to ring Q[y_2, ..., y_m][s]
    s_new = R_new.gen()
    ys = list(R_new_base.gens())
    r_tilde = R_new(r_tilde.subs({v: y + gamma for v, y, gamma in zip(params[1:],ys, gamma)} | {s: s_new}))
    #debug("rt:", r_tilde)

    pd = R_new(r_tilde).pade(prec, prec)
    #debug("pd:", pd)
    p, q = pd.numerator(), pd.denominator()
    p, q = R_new(p), R_new(q)
    p = p.truncate(prec)
    q = q.truncate(prec)
    #debug("pade p:", p)
    #debug("pade q:", q)

    # Divide p and q by degree 0 terms
    
    #p = (p/q.subs({s_new:0})).truncate(prec)
    #q = (q/q.subs({s_new:0})).truncate(prec)

    # Truncate coefficients by prec and convert everything back to polynomial
    p = R_poly(p)
    q = R_poly(q)
    p = sum([c * f for c, f in p if f.degree() < prec])
    q = sum([c * f for c, f in q if f.degree() < prec])
    p, q, s_new = R_poly(p), R_poly(q), R_poly(s_new.polynomial())

    # Sub back to original variables
    p, q, s_new = apply_ring_morphism(flatten_R_new, p, q, s_new)

    # 2. Build the exact algebraic inverse map
    # s maps to c (params[0])
    # y_i maps to (v / c) - gamma
    subs_dict = {flatten_R_new(s_new): R_base(params[0])}
    for y, v, g in zip(ys, params[1:], gamma):
        subs_dict[flatten_R_new(y)] = R_base(v) / R_base(params[0]) - R_base(g)

    # 3. Perform substitution directly. 
    # Because the values are in Frac_R, SageMath handles all division and clearing of denominators safely.
    r_final = p.subs(subs_dict) / q.subs(subs_dict)
    
    return r_final

def rational_reconstruction(gamma, P, kronecker_param, params, prec):
    debug("RECON START")
    #for r, v in P:
    #    debug(r, v)
    #    debug(construct_rational(gamma, r, params, u_, prec))
    #    debug("--")

    # Convert params to base ring
    R_base = params[0].parent()

    # Reconstruct coefficients of P as a polynomial in u_ with coefficients in params
    debug()
    debug("Reconstructing P")
    debug(P.parent())
    rat_P = sum(
        [construct_rational(gamma, r, params, prec)*v.change_ring(R_base) for r, v in P]
    )
    debug("RECON P:", P)
    debug()

    # Same thing with all kronecker terms
    debug("Reconstructing kronecker")
    debug(kronecker_param[0].parent())
    rat_kronecker = [
        sum([construct_rational(gamma, r, params, prec)*v.change_ring(R_base) for r, v in f])
        for f in kronecker_param
    ]
    debug()

    return rat_P, rat_kronecker

def newton_lift(F, P, shape_param, vs, u_, params, linear_form, prec):
    # 1. Define the substitution X -> V(U)
    Tsubs = {v: w for v, w in zip(vs, shape_param)}
    debug("prec:", prec)

    # sys = F in the algorithm by Schost
    T = [v - w for v, w in zip(vs, shape_param)] + [P]
    sys = F + [u_ - linear_form]

    # 2. Evaluate Jacobians and explicitly substitute X = V(U) early
    # This ensures no 'x' or 'y' variables sneak into the matrix inverses.
    JacF = jacobian(sys, [*vs, u_]).subs(Tsubs)
    JacT = jacobian(T, [*vs, u_]).subs(Tsubs)
    debug("JacF:", JacF)

    # 3. Invert JacF in the precision-k quotient ring (modulo P and params^prec)
    R = u_.parent()
    R_base = R.base_ring()
    #Quo_k_P = R.quotient_ring(Ideal(params)**prec + Ideal(P))

    debug("T:", T)
    debug("sys:", sys)
    #debug("JacF_det:", JacF.change_ring(Quo_k_P).determinant())

    JacF_inv = JacF.inverse()
    JacF_inv = matrix(
        [
            [f.numerator() * inv(f.denominator(), P) for f in row]
            for row in JacF_inv
        ]
    )
    debug("JacF_inv")
    debug(JacF_inv)

    # 4. Compute the iteration matrix M
    M = JacT * JacF_inv

    # 5. Evaluate the defect (sys) at X = V(U) to retain terms up to O(params^{2*prec})
    sys_eval = vector([f.subs(Tsubs) for f in sys])
    debug("eval:", sys_eval)

    # 6. Multiply M by the defect and reduce modulo P and params^{2*prec}
    deltas = M * sys_eval
    debug("deltas:", deltas)
    deltas = [mod_truncate(d, P, params, 2*prec) for d in deltas]
    debug("P:", P)
    debug("deltas:", deltas)
    
    # 7. Apply updates: V_new = V_old - delta_V, P_new = P_old + delta_P
    new_shape_param = [truncate_coeffs(w-delta, params, 2*prec) for w, delta in zip(shape_param, deltas[:-1])]
    newP =  truncate_coeffs(P+deltas[-1], params, 2*prec)
    debug("oldP", P)
    debug("P_update", deltas[-1])
    debug("test:", P+deltas[-1])
    debug("newP", newP)

    return newP, new_shape_param

def stop_criterion(F, P, params, kronecker_param, test_param, u_, vs):
    R_base = params[0].parent()
    test_subs = {v:p for v, p in zip(params, test_param)}
    f_subs = {v:q for v, q in zip(vs, kronecker_param)}

    # Test 1: Check that no denominators vanish at test parameter
    for coeff in P.coefficients():
        if R_base(coeff.denominator()).subs(test_subs) == 0:
            debug("Coefficient vanishes at test point", verbosity=10)
            return False
    for f in kronecker_param:
        for coeff in f.coefficients():
            if R_base(coeff.denominator()).subs(test_subs) == 0:
                debug("Coefficient vanishes at test point", verbosity=10)
                return False
            
    def specialize_at_param(f, subs):
        return sum(c.subs(subs) * v for c, v in f).change_ring(QQ)

    # Test 2: Check that P is square-free when specialized at test parameter
    P_specialized = specialize_at_param(P, test_subs)
    if not P_specialized.is_squarefree():
        debug("P is not square-free", verbosity=10)
        return False
    
    # Test 3: Check that the roots of P when specialized at test parameter
    # give solutions to the original system
    kronecker_specialized = [
        specialize_at_param(f, test_subs)
        for f in kronecker_param
    ]

    R_specialized = P_specialized.parent()
    u_ = R_specialized(u_)
    vs = [R_specialized(v) for v in vs]
    F_specialized = [
        sum(c.subs(test_subs) * v for c, v in f).change_ring(QQ)
        for f in F
    ]
    debug("F_specialized", F_specialized, verbosity=10)
    debug("P_Specialized:", P_specialized, verbosity=10)
    debug("kronecker_specialized:", kronecker_specialized, verbosity=10)
    sols = []
    for u in P_specialized.polynomial(u_).roots(QQbar, multiplicities=False):
        sols.append(
            {
                v: QQbar((Q/P_specialized.derivative(u_)).subs({u_:u}))
                for v, Q in zip(vs, kronecker_specialized)
            }
        )
    debug("sols:", sols, verbosity=10)

    for f in F_specialized:
        if any(f.subs(sol) != 0 for sol in sols):
            debug(f, verbosity=5)
            debug(sols, verbosity=5)
            for sol in sols:
                debug(f.subs(sol), verbosity=5)
            debug("Solution not satisfied", verbosity=10)
            return False

    det = jacobian(F_specialized, vs).determinant()
    if any(det.subs(sol) == 0 for sol in sols):
        debug("Singular Jacobian", verbosity=10)
        return False

    return True

def parametric_geometric_resolution(F, num_params, param_point=None, test_param=None, gamma=None):
    # Separate input by parameters and variables
    R_original = F[0].parent()
    params = list(R_original.gens())[:num_params]
    vs = list(R_original.gens())[num_params:]

    # Specialize F at random parameter point
    if param_point is None:
        param_point = [QQ.random_element(10) for _ in params]
    if test_param is None:
        test_param = [QQ.random_element(10) for _ in params]
    if gamma is None:
        gamma = [QQ.random_element(10) for _ in params[:-1]]

    # Shift F over by param point, so expansions are done around 0
    F = [f.subs({v:v+p for v, p in zip(params, param_point)}) for f in F]

    #linear_form, lam = primitive_element(vs)
    F_p, vsp = specialize_system(F, params, [0 for _ in params])

    # Compute kronecker and shape representations at specialized point
    from sage_acsv import ACSVSettings as AS
    AS.set_default_kronecker_backend(AS.Kronecker.MSOLVE)
    from sage_acsv.kronecker import kronecker_representation
    P, kronecker_param, linear_form = kronecker_representation(F_p, vsp, return_linear_form=True)
    u_ = P.parent().gen()
    shape_param = to_shape_lemma(P, kronecker_param, u_)

    # Generate rings that will be used throughout
    R_base = PolynomialRing(QQ, len(params), params).fraction_field()
    params = [R_base(p) for p in params]
    R = PolynomialRing(R_base, vs + [u_])
    original_to_R = R_original.hom(
        list(R_base.gens()) + list(R.gens())[:-1]
    )
    F, vs = apply_ring_morphism(original_to_R, F, vs)

    u_to_R = u_.parent().hom([R.gens()[-1]])
    u_, P, kronecker_param, shape_param = apply_ring_morphism(
        u_to_R, u_, P, kronecker_param, shape_param
    )
    debug("Original:", verbosity=10)
    debug("linear_form:", linear_form, verbosity=10)
    debug("P:", P, verbosity=10)
    debug("kronecker:", kronecker_param, verbosity=10)
    debug("shape:", shape_param, verbosity=10)
    debug(verbosity=10)

    D = max(f.degree() for f in F)
    n = len(F)
    MAX_ITER = int(log(2*D**n+1, 2))+1

    prec = 1
    for kappa in range(MAX_ITER):
        # Convert shape param to kronecker
        debug("ITER:", kappa, verbosity=10)
        kronecker_param = to_kronecker(P, shape_param, params, u_, prec)
        debug("PRE-KRONECKER", verbosity=10)
        debug(P, verbosity=10)
        debug(kronecker_param, verbosity=10)
        debug(verbosity=10)
        
        if prec >= 2:
            # Reconstruct rational coefficients and check if done
            rational_P, rational_params = rational_reconstruction(gamma, P, kronecker_param, params, prec//2)
            debug("KRONECKER:", verbosity=10)
            debug(rational_P, verbosity=10)
            debug(rational_params, verbosity=10)
            debug(verbosity=10)
            debug("STOP CRITERION:", verbosity=10)
            if stop_criterion(F, rational_P, params, rational_params, test_param, u_, vs):
                # Shift params back
                rational_P = sum(
                    c.subs({v:v-p for v, p in zip(params, param_point)}) * v for c, v in rational_P
                )
                rational_params = [
                    sum(
                        c.subs({v:v-p for v, p in zip(params, param_point)}) * v for c, v in f
                    )
                    for f in rational_params
                ]
                debug("DONE", verbosity=10)
                return rational_P, rational_params
            else:
                debug("CRITERION FAILED", verbosity=10)
            debug(verbosity=10)

        # Lift shape param to higher order
        P, shape_param = newton_lift(F, P, shape_param, vs, u_, params, linear_form, prec)
        debug("LIFTED", verbosity=10)
        debug(P, verbosity=10)
        debug(shape_param, verbosity=10)
        debug(verbosity=10)

        prec *= 2
        debug(verbosity=10)
        debug("------------------------------------", verbosity=10)

    return None
