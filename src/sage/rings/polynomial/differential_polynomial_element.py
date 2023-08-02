r"""
Univariate differential polynomials.

AUTHORS:

- Xavier Caruso, Raphaël Pagès (2023-06): initial version

"""

# ***************************************************************************
#    Copyright (C) 2023 Xavier Caruso <xavier.caruso@normalesup.org>
#                  2023 Raphaël Pagès <raphael.pages@math.u-bordeaux.fr>
#
#    This program is free software: you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation, either version 2 of the License, or
#    (at your option) any later version.
#                  http://www.gnu.org/licenses/
#****************************************************************************

from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.ore_polynomial_element import OrePolynomial_generic_dense
from sage.rings.finite_rings.finite_field_constructor import FiniteField
from sage.rings.quotient_ring import QuotientRing
from sage.matrix.constructor import matrix
from sage.matrix.special import companion_matrix

from sage.arith.functions import lcm
from sage.arith.misc import xgcd

def _from_falling_factorial(P, a, gen):
    if not P:
        return 0, 1
    l=len(P)
    if l==1:
        return (P[0], gen + a)
    P1=P[:l//2]
    P2=P[l//2:]
    Q1, m1 = _from_falling_factorial(P1, a, gen)
    Q2, m2 = _from_falling_factorial(P2, a-l//2, gen)
    return (Q2*m1 + Q1, m1*m2)

def _integrator(f, g):
    l = (g * f).list()
    l.pop(-1)
    return f.parent([0] + [ l[i]/(i+1) for i in range(len(l))]) 

def _incr(l, d, parent):
    for i in range(len(l)):
        l[i] += 1
        if l[i] != 0:
            break
    else:
        l.append(parent.zero())
        d += 1
    return d

def _eval(P, base):
    """Return the evaluation of a polynomial whose lift of coeffcients is L in base based on a
    divide and conquer algorithm.
    INPUT: L a list of elements of a ring R, base an element of an R-algebra
    OUTPUT : P(base) where P is a polynomial whose list of coefficients is L
    """
    if P.degree()*len(base.list())<=1000:
        return P(base), base**(P.degree()+1)
    L = P.list()
    n = len(L)
    P1, Q1 = _eval(P.parent()(L[:n//2]), base)
    P2, Q2 = _eval(P.parent()(L[n//2:]), base)
    return P2*Q1 + P1, Q2*Q1

def _local_phi(L, l, p):
    """Computes the list of f(t+a) mod t^p where f are polynomial coefficient of an
    operator L and a is a generator of the field l.
    
    INPUT:  - L a differential operator over some rational function field of
             characteristic p whose denominator is 1.
            - l a finite field extension of L's constant base field.
            - p, l's characteristic
    
    OUTPUT: - The list of f/lc(t+a) mod t^p where lc is the leading
              coefficient of L
            - 1/lc(t+a) mod t^p
    """
    pol = PolynomialRing(l, 's')
    shift = []
    for f in L.list():
        shift.append(_eval(f.numerator(), pol.gen()+l.gen())[0])
    modulo = QuotientRing(pol, pol.gen()**p)
    lc = modulo(shift[-1])
    lc_inv = lc**(-1)
    return [modulo(f)*lc_inv for f in shift], modulo, lc

def _local_zeta(l, p, modulus):
    if l.degree() == 1:
        return 0
    nu = l.gen()**p
    L = []
    a = l.one()
    for _ in range(l.degree()):
        L.append(a.list())
        a = a*nu
    zeta = l(matrix(L).solve_left(matrix(l.gen().list())).list())
    return zeta

def _local_phi_inverse(f, l, parent, zeta):
    P = _eval(f, parent.gen() - l.gen())[0]
    if not zeta:
        return parent(P)
    L = 0
    frob_inv = l.frobenius_endomorphism().inverse()
    for i in range(len(P.list())):
        g = parent(frob_inv(P.list()[i]).list())
        L += (parent(_eval(g, zeta)[0])**l.characteristic()).shift(i)
    return L

def _gluing(L, p):
    n=len(L)
    if n == 1:
        return L
    if n == 2:
        m, n = L[0][1], L[1][1]
        d, u, v = xgcd(m, n)
        if d != 1:
            raise ValueError('set of moduli are not pairwise coprime')
        g = (m*n)**p
        rem = lambda f: f.quo_rem(g)[1]
        return [(((u*m)**p*L[0][0]+(v*n)**p*L[1][0]).apply_map(rem), m*n)]
    return _gluing(_gluing(L[:n//2],p) + _gluing(L[n//2:], p), p)

def _fundamental_solutions(A, g):
    m, p = 2, A.parent().characteristic()
    der = g * A.parent().base_ring().derivation()
    integ = lambda f : _integrator(f, g)
    truncate = lambda n : lambda f : f.parent()(f.list()[:n])
    t = A.parent().base_ring().gen()
    Ir = A.parent()(1)
    Y, Z = Ir + t*A.apply_map(truncate(1)), Ir
    while m <= p:
        Z = Z + (Z * (Ir - Y*Z)).apply_map(truncate(m))
        S = Z * (Y.apply_morphism(der) - A.apply_map(truncate(2*m -1)) * Y)
        Y = Y - (Y * S.apply_map(integ)).apply_map(truncate(2*m))
        m = 2*m
    return Y

def _p_curvature_mod_xp(L, der):
    A = -companion_matrix(L)
    XS = _fundamental_solutions(A, der)
    sec = lambda f: f.list()[-1]
    return (XS * (A*XS).apply_map(sec) * XS.inverse())


class DifferentialPolynomial_generic_dense(OrePolynomial_generic_dense):
    r"""
    Generic implementation of dense differential polynomial supporting
    any valid base ring and derivation.

    TESTS::

         sage: R.<t> = ZZ[]
         sage: S.<D>=OrePolynomialRing(R, t*R.derivation())
         sage: D*t
         t*D + t
         sage: TestSuite(D + t).run()
    """

    def p_curvature(self, algorithm=None):
        r"""
        Return the `p`-curvature of this differential polynomial.

        INPUT:

        - ``algorithm`` -- a string or ``None`` (default: ``None``);
          the algorithm to use to compute the p-curvature, currenly
          only Katz's algorithm is available

        EXAMPLES::

            sage: A.<t> = FiniteField(5)[]
            sage: S.<d> = A['d', A.derivation()]
            sage: d.p_curvature()
            [0]
            sage: (d**2).p_curvature()
            [0 0]
            [0 0]

            sage: L = d**3 + t*d
            sage: M = L.p_curvature()
            sage: M
            [      0       0       0]
            [  4*t**2     4*t t**3 + 1]
            [      3   4*t**2       t]

        We verify that the coefficients of characteristic polynomial of
        the `p`-curvature are polynomials in `t**p`::

            sage: M.charpoly()
            x**3 + t**5*x

        When the base ring has characteristic zero, the `p`-curvature is
        not defined and an error is raised::

            sage: A.<t> = QQ[]
            sage: S.<d> = A['d', A.derivation()]
            sage: d.p_curvature()
            Traceback (most recent call last):
            ...
            ValueError: p-curvature only makes sense in positive characteristic

        TESTS::

            sage: A.<t> = FiniteField(5)[]
            sage: S.<d> = A['d', A.derivation()]
            sage: d.p_curvature(algorithm="fast")
            Traceback (most recent call last):
            ...
            ValueError: algorithm 'fast' is not available

        """
        p = self.parent().characteristic()
        if p == 0:
            raise ValueError("p-curvature only makes sense in positive characteristic")
        if algorithm is None:
            algorithm = "katz"
        methodname = "_p_curvature_" + algorithm
        if hasattr(self, methodname):
            method = getattr(self, "_p_curvature_%s" % algorithm)
            return method()
        raise ValueError("algorithm '%s' is not available" % algorithm)

    def _p_curvature_katz(self):
        r"""
        Return the `p`-curvature of this differential polynomial
        computed using Katz' algorithm.

        TESTS::

            sage: A.<t> = FiniteField(5)[]
            sage: K = A.fraction_field()
            sage: S.<d> = K['d', K.derivation()]
            sage: L = d**2 + t**2*d - 1/t
            sage: L.p_curvature(algorithm='katz')  # indirect doctest
            [                             (t**9 + 4*t**6 + 2*t**4 + 2*t**3 + t + 4)/t**4 (4*t**12 + 3*t**9 + 2*t**7 + 2*t**6 + 2*t**4 + 2*t**3 + 4*t**2 + 2*t + 1)/t**5]
            [                        (4*t**11 + 3*t**8 + 2*t**6 + 2*t**3 + 4*t + 4)/t**3                     (t**14 + 4*t**9 + t**6 + 3*t**4 + 3*t**3 + 4*t + 1)/t**4]

        ::

            sage: S.<x> = K['x', t*K.derivation()]
            sage: x.p_curvature(algorithm='katz')  # indirect doctest
            Traceback (most recent call last):
            ...
            NotImplementedError: computation of the p-curvature is only implemented when d**p = 0

        """
        KD = self.parent()
        d = KD.twisting_derivation()
        p = KD.characteristic()
        if d.pth_power() != 0:
            raise NotImplementedError("computation of the p-curvature is only implemented when d**p = 0")
        A = self.companion_matrix()
        B = A
        for _ in range(p-1):
            B = B.apply_morphism(d) + A*B
        return B

class DifferentialPolynomial_rationnal_field(DifferentialPolynomial_generic_dense):
    
    def _p_curvature_bocasc(self):
        base, der = self.parent()._constant_base_field, self.parent().twisting_derivation()
        gen_derivative = der(der.domain().gen())
        p = base.characteristic()
        P = self.right_monic()
        denom = lcm(f.denominator() for f in P.list())
        P = denom*P
        denom = P.leading_coefficient().numerator()
        pol = denom.parent()
        d = max(f.numerator().degree() for f in P.list())
        elements = []
        global_degree = 0
        l=[base(0)]
        local_degree = 1
        test = [gen_derivative.numerator(), gen_derivative.denominator(), denom]
        while global_degree <= d:
            poly = pol(l+[1])
            if poly.is_irreducible() and 0 not in [f.quo_rem(poly)[1] for f in test]:
                elements.append(poly)
                global_degree += local_degree
            local_degree = _incr(l, local_degree, base)
        local_p_curv = []
        for a in elements:
            local_field = FiniteField(p**(a.degree()), name='s', modulus = a)
            local_P, local_mod, local_lc = _local_phi(P, local_field, p)
            local_A = local_lc**p*_p_curvature_mod_xp(local_P,\
                    _eval(test[0], local_mod.gen() + local_field.gen())[0]\
                    /_eval(test[1], local_mod.gen() + local_field.gen())[0])
            reduction = lambda f: f.numerator()(f.parent().gen().numerator()+local_field.gen()).quo_rem(f.parent().gen().numerator()**p)[1]
            local_zeta = _local_zeta(local_field, p, a)
            phi_inverse = lambda f: _local_phi_inverse(f.lift(), local_field, denom.parent(), local_zeta)
            local_p_curv.append((local_A.apply_map(phi_inverse), a))
        return (1/(denom**p))*_gluing(local_p_curv, p)[0][0].change_ring(self.parent().base_ring())
