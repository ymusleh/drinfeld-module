import collections.abc
from time import perf_counter

from sage.structure.parent import Parent
from sage.categories.vector_spaces import VectorSpaces

from sage.rings.polynomial.ore_polynomial_element import OrePolynomial
from sage.rings.polynomial.ore_polynomial_ring import OrePolynomialRing
from sage.rings.polynomial.polynomial_ring import PolynomialRing_general
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.finite_rings.finite_field_base import FiniteField
from sage.rings.integer import Integer
from sage.matrix.constructor import Matrix, matrix
from sage.matrix.special import identity_matrix
from sage.rings.quotient_ring import QuotientRing
from sage.functions.other import ceil, sqrt
from sage.all import prod

from functools import lru_cache

from drinfeld import DrinfeldModule, get_coeffs, get_eval

"""
Apply the Frobenius endomorphism to a polynomial's coefficients

"""
def c_frob(elem, oexp, q, n, gr):
    true = oexp % n
    cfs = get_coeffs(elem)
    ret = 0
    for i, cf in enumerate(cfs):
        ret += (cf**(q**true))*gr**i
    return ret


class DrinfeldCohomology_Crys():
    def __init__(self, dm):
        self._dm = dm
        self._dim = dm.rank()
        self._basis_rep = identity_matrix(self.L(), self._dim)
        self.precision = self._dm.n()
        self.AL1 = PolynomialRing(self._dm.L(), 'w')
        self.AL = QuotientRing(self.AL1, (self.AL1.gen() - self._dm[0])**(2*self.precision))

    def dm(self):
        return self._dm

    def L(self):
        return self.dm().L()

    def fast_skew(self, a, iters = 1):
        return self.dm()._context._fast_skew(a, iters)

    """
    Initialize matrix for use in the recurrence method.
    """
    def init_matr(self, coeffs, k, ring):
        r = self._dim
        matr = matrix(ring, r, r)
        for i in range(r):
            matr[0, i] = self.fast_skew(coeffs[i], k)
        for i in range(r-1):
            matr[i + 1, i] = 1
        matr[0, r-1] += (1/(self.fast_skew(self.dm()[r], k)))*ring.gen()
        return matr

    def power_reduction(self, matr, ex, mod, ring):
        prmatr = matrix(ring, self._dim, self._dim)
        for i, row in enumerate(matr):
            for j, pol in enumerate(row):
                polmod = pol % mod
                prmatr[i, j] = ring([ self.fast_skew(c, ex) for c in get_coeffs(polmod) ])
        return prmatr




    """
    Uses the linear recurrence to determine the matrix representation of the Frobenius endomorphism on the
    Crystalline cohomology w.r.t. the standard basis.
    """

    def crys_rec(self, deg, precision = 0):
        r, n, q = self._dim, self.dm().n(), self.dm().q()
        nstar = ceil(sqrt(n*precision))
        n1, n0 = n // nstar, n % nstar
        if precision < 1:
            precision = self.dm().n() + 1
        rec_coeff = [ self.L()(-1)*self.dm()[r - i]/self.dm()[r] for i in range(1, r + 1) ]

        coeff_ring1 = PolynomialRing(self.L(), 'V')
        mu = (coeff_ring1.gen() - self.dm()[0])**precision
        mu_coeffs = get_coeffs(mu)
        coeff_ring = QuotientRing(coeff_ring1, mu)

        # The initial matrices
        C0 = prod([self.init_matr(rec_coeff, i, coeff_ring1) for i in range(n0, 0, -1)])
        C = prod([self.init_matr(rec_coeff, i, coeff_ring1) for i in range(nstar + n0, n0, -1)])

        # Compute the reduction moduli
        moduli = [ coeff_ring1([self.fast_skew(c, -i*nstar) for c in mu_coeffs ]) for i in range(1, n1) ]
        # Reduce and apply coefficient-wise frobenius
        power_reduction_matrs = [self.power_reduction(C, i*nstar, moduli[i-1], coeff_ring1) for i in range(1, n1) ]
        power_reduction_matrs.reverse()
        return prod(power_reduction_matrs)*C*C0

    def charpoly(self, prec = 0):
        return self.crys_rec(self.dm().n() + self.dm().rank(), prec).charpoly()


def double_replace(multi, c1, c2):
    coeffs1 = get_coeffs(multi)
    coeffsh = [ get_eval(a, c2) for a in coeffs1]
    return sum([coeff*(c1**i) for i, coeff in enumerate(coeffsh)])
