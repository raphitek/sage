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

from sage.rings.polynomial.ore_polynomial_element import OrePolynomial_generic_dense
from sage.matrix.constructor import matrix

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


def _fundamental_solutions(A, der):
    m, p=2, der.domain().characteristic()
    g = der(A.parent().base_ring().gen()).inverse()
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

def _p_curvature_mod_xp(L):
    der=L.parent().twisting_derivation()
    A = -L.companion_matrix()
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

            sage: A.<t> = GF(5)[]
            sage: S.<d> = A['d', A.derivation()]
            sage: d.p_curvature()
            [0]
            sage: (d^2).p_curvature()
            [0 0]
            [0 0]

            sage: L = d^3 + t*d
            sage: M = L.p_curvature()
            sage: M
            [      0       0       0]
            [  4*t^2     4*t t^3 + 1]
            [      3   4*t^2       t]

        We verify that the coefficients of characteristic polynomial of
        the `p`-curvature are polynomials in `t^p`::

            sage: M.charpoly()
            x^3 + t^5*x

        When the base ring has characteristic zero, the `p`-curvature is
        not defined and an error is raised::

            sage: A.<t> = QQ[]
            sage: S.<d> = A['d', A.derivation()]
            sage: d.p_curvature()
            Traceback (most recent call last):
            ...
            ValueError: p-curvature only makes sense in positive characteristic

        TESTS::

            sage: A.<t> = GF(5)[]
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

            sage: A.<t> = GF(5)[]
            sage: K = A.fraction_field()
            sage: S.<d> = K['d', K.derivation()]
            sage: L = d^2 + t^2*d - 1/t
            sage: L.p_curvature(algorithm='katz')  # indirect doctest
            [                             (t^9 + 4*t^6 + 2*t^4 + 2*t^3 + t + 4)/t^4 (4*t^12 + 3*t^9 + 2*t^7 + 2*t^6 + 2*t^4 + 2*t^3 + 4*t^2 + 2*t + 1)/t^5]
            [                        (4*t^11 + 3*t^8 + 2*t^6 + 2*t^3 + 4*t + 4)/t^3                     (t^14 + 4*t^9 + t^6 + 3*t^4 + 3*t^3 + 4*t + 1)/t^4]

        ::

            sage: S.<x> = K['x', t*K.derivation()]
            sage: x.p_curvature(algorithm='katz')  # indirect doctest
            Traceback (most recent call last):
            ...
            NotImplementedError: computation of the p-curvature is only implemented when d^p = 0

        """
        KD = self.parent()
        d = KD.twisting_derivation()
        p = KD.characteristic()
        if d.pth_power() != 0:
            raise NotImplementedError("computation of the p-curvature is only implemented when d^p = 0")
        A = self.companion_matrix()
        B = A
        for _ in range(p-1):
            B = B.apply_morphism(d) + A*B
        return B

class DifferentialPolynomial_function_field(DifferentialPolynomial_generic_dense):
    pass
