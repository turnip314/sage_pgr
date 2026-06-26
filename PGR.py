from sage.all import QQ, QQbar, log, Ideal, PolynomialRing, xgcd, FractionField, matrix, SR, vector, PowerSeriesRing, TermOrder

def debug(*args, verbosity=1):
    threshold = 2
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
    return sum(
        [c*v for c, v in f if sum(v.degree(p) for p in params) < degree]
    )

def mod_by_P(f, P, u_=None):
    return f % P

def solve_right(A, b, P, prec):
    pass

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
    R = u_.parent()
    Quo = R.quotient_ring(Ideal(P))
    Pd = P.derivative(u_)
    Pd_inv = Quo(Pd).inverse()
    return [Quo(Q*Pd_inv).lift() for Q in Qs]

def to_kronecker(P, Qs, params, u_, prec):
    R = u_.parent()
    Quo = R.quotient_ring(Ideal(params)**(prec) + Ideal(P))
    Pd = P.derivative(u_)
    return [Quo(Q*Pd).lift() for Q in Qs]

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
    """
    p, q, s_new = apply_ring_morphism(flatten_R_new, p, q, s_new)
    p = Rs(p.subs({flatten_R_new(y): v - gamma for y, v, gamma in zip(ys, params[1:], gamma)} | {flatten_R_new(s_new): s}))
    q = Rs(q.subs({flatten_R_new(y): v - gamma for y, v, gamma in zip(ys, params[1:], gamma)} | {flatten_R_new(s_new): s}))
    #debug("q", q)

    # Homogenize and specialize to s=1
    #debug(q.parent())
    #debug(params[0])
    #debug(params[0].parent())
    #debug(q.homogenize(params[0]))
    p = p.homogenize(params[0])
    q = q.homogenize(params[0])
    #debug("hom p, q:", p, q)

    #debug("r_final:", (p/q).subs({s:1}))
    #rint("to_R:", to_R((p/q).subs({s:1})))
    #debug()
    rat = R_base.fraction_field()
    return rat((p/q).subs({s:1}))"""
    # Sub back to original variables using FractionField
    p, q, s_new = apply_ring_morphism(flatten_R_new, p, q, s_new)
    
    # 1. Access the exact Fraction Field of your original Base Ring (QQ(c, d))
    Frac_R = R_base.fraction_field()
    
    # 2. Build the exact algebraic inverse map
    # s maps to c (params[0])
    # y_i maps to (v / c) - gamma
    subs_dict = {flatten_R_new(s_new): Frac_R(params[0])}
    for y, v, g in zip(ys, params[1:], gamma):
        subs_dict[flatten_R_new(y)] = Frac_R(v) / Frac_R(params[0]) - Frac_R(g)

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
    rat = R_base.fraction_field()

    # Reconstruct coefficients of P as a polynomial in u_ with coefficients in params
    debug()
    debug("Reconstructing P")
    debug(P.parent())
    rat_P = sum(
        [construct_rational(gamma, r, params, prec)*v.change_ring(rat) for r, v in P]
    )
    debug("RECON P:", P)
    debug()

    # Same thing with all kronecker terms
    debug("Reconstructing kronecker")
    debug(kronecker_param[0].parent())
    rat_kronecker = [
        sum([construct_rational(gamma, r, params, prec)*v.change_ring(rat) for r, v in f])
        for f in kronecker_param
    ]
    debug()

    return rat_P, rat_kronecker

def newton_lift(F, P, shape_param, vs, u_, params, linear_form, prec):
    # 1. Define the substitution X -> V(U)
    Tsubs = {v: w for v, w in zip(vs, shape_param)}
    print("prec:", prec)

    # sys = F in the algorithm by Schost
    T = [v - w for v, w in zip(vs, shape_param)] + [P]
    sys = F + [u_ - linear_form]

    # 2. Evaluate Jacobians and explicitly substitute X = V(U) early
    # This ensures no 'x' or 'y' variables sneak into the matrix inverses.
    JacF = jacobian(sys, [*vs, u_]).subs(Tsubs)
    JacT = jacobian(T, [*vs, u_]).subs(Tsubs)

    # 3. Invert JacF in the precision-k quotient ring (modulo P and params^prec)
    R = u_.parent()
    R_base = R.base_ring()
    #Quo_k_P = R.quotient_ring(Ideal(params)**prec + Ideal(P))

    debug("T:", T)
    debug("sys:", sys)
    debug("JacF_det:", JacF.change_ring(Quo_k_P).determinant())

    Jac_Quo = JacF.change_ring(Quo_k_P)
    
    """
    JacF_inv = JacF.change_ring(Quo_k_P).inverse().change_ring(Quo_k_P)
    #JacF_inv = matrix(
    #    matrix(
    #
    #    )
    #)

    # 4. Compute the iteration matrix M and lift it back to the base ring R
    M = JacT.change_ring(Quo_k_P) * JacF_inv
    M = matrix(
        [
            [v.lift() for v in row]
            for row in M
        ]
    )
    """

    # 5. Evaluate the defect (sys) at X = V(U) to retain terms up to O(params^{2*prec})
    sys_eval = vector([f.subs(Tsubs) for f in sys])
    JacF_inv_times_sys = Jac_Quo.solve_right(sys_eval)

    # 6. Multiply M by the defect and reduce modulo P and params^{2*prec}
    Quo_2k_P = R.quotient_ring(Ideal(params)**(2*prec) + Ideal(P))
    deltas = M * sys_eval
    print("deltas original:", deltas)
    deltas = [Quo_2k_P(d).lift() for d in deltas]
    print("deltas1:", deltas)
    deltas2 = [mod_by_P(truncate_coeffs(d, params, 2*prec), P) for d in deltas]
    print("deltas2")
    for d in deltas:
        trunc = truncate_coeffs(d, params, 2*prec)
        print("trunc:", trunc)
        print("P:", P)
        print(mod_by_P(trunc, P))
        print()
    print("deltas2:", deltas2)
        
    debug("deltas:", deltas)
    
    # 7. Apply updates: V_new = V_old - delta_V, P_new = P_old + delta_P
    # We use Quo_2k (without Ideal(P)) here so we don't accidentally reduce P down to 0!
    Quo_2k = R.quotient_ring(Ideal(params)**(2*prec))
    
    #new_shape_param = [Quo_2k(w - delta).lift() for w, delta in zip(shape_param, deltas[:-1])]
    new_shape_param = [truncate_coeffs(w-delta, params, 2*prec) for w, delta in zip(shape_param, deltas[:-1])]
    newP =  truncate_coeffs(P+deltas[-1], params, 2*prec) #Quo_2k(P + deltas[-1]).lift()

    return newP, new_shape_param

def stop_criterion(F, P, params, kronecker_param, test_param, u_, vs):
    test_subs = {v:p for v, p in zip(params, test_param)}
    f_subs = {v:q for v, q in zip(vs, kronecker_param)}

    # Test 1: Check that no denominators vanish at test parameter
    for coeff in P.coefficients():
        if coeff.denominator().subs(test_subs) == 0:
            debug("Coefficient vanishes at test point", verbosity=10)
            return False
    for f in kronecker_param:
        for coeff in f.coefficients():
            if coeff.denominator().subs(test_subs) == 0:
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
    R_base = PolynomialRing(QQ, len(params), params)
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

    """
    # Convert flattened ring to block ordering with parameters last
    all_vars = [str(v) for v in vs] + [str(u_)] + [str(p) for p in params]
    block_order = TermOrder('degrevlex', len(vs) + 1) + TermOrder('degrevlex', len(params))
    R_flat_ordered = PolynomialRing(QQ, names=all_vars, order=block_order)
    flat_vsu, flat_params = list(R_flat_ordered.gens())[:-num_params], list(R_flat_ordered.gens())[-num_params:]

    flatten_R = R.flattening_morphism()
    flatten_R_ordered = flatten_R.codomain().hom(flat_params + flat_vsu)
    unflatten_R = flatten_R_ordered.codomain().hom(list(R.gens())+list(R_base.gens()))
    #flatten_R = R.flattening_morphism()
    #unflatten_R = flatten_R.inverse()

    D = max(f.degree() for f in F)
    n = len(F)
    MAX_ITER = min(int(log(2*D**n+1, 2))+1, 4) # TODO - capping precision until efficiency implementations

    # all elements should be flattened going into the loop
    F, P, shape_param, kronecker_param, vs, flat_params, u_, linear_form = apply_ring_morphism(
        flatten_R, F, P, shape_param, kronecker_param, vs, params, u_, linear_form
    )
    F, P, shape_param, kronecker_param, vs, flat_params, u_, linear_form = apply_ring_morphism(
        flatten_R_ordered, F, P, shape_param, kronecker_param, vs, flat_params, u_, linear_form
    )
    """

    prec = 1
    for kappa in range(MAX_ITER):
        # Convert shape param to kronecker
        debug("ITER:", kappa, verbosity=10)
        kronecker_param = to_kronecker(P, shape_param, vs, u_, prec)
        debug("PRE-KRONECKER", verbosity=10)
        debug(P, verbosity=10)
        debug(kronecker_param, verbosity=10)
        debug(verbosity=10)

        """
        F, P, kronecker_param, vs, u_, linear_form = apply_ring_morphism(
            unflatten_R, F, P, kronecker_param, vs, u_, linear_form
        )
        """
        
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
        

        """
        F, P, kronecker_param, vs, u_, linear_form = apply_ring_morphism(
            flatten_R, F, P, kronecker_param, vs, u_, linear_form
        )
        F, P, kronecker_param, vs, u_, linear_form = apply_ring_morphism(
            flatten_R_ordered, F, P, kronecker_param, vs, u_, linear_form
        )
        """

        # Lift shape param to higher order
        P, shape_param = newton_lift(F, P, shape_param, vs, u_, flat_params, linear_form, prec)
        debug("LIFTED", verbosity=10)
        debug(P, verbosity=10)
        debug(shape_param, verbosity=10)
        debug(verbosity=10)

        prec *= 2
        debug(verbosity=10)
        debug("------------------------------------", verbosity=10)

    return None
