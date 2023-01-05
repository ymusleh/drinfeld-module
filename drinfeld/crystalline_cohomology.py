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

from drinfeld import DrinfeldModule, get_coeffs, get_eval, c_frob




class DrinfeldCohomology_Crys():
    def __init__(self, dm):
        # the associated Drinfeld Module
        self._dm = dm
        self._dim = dm.rank()
        # Not sure how necessary this is since we are mostly concerned with performance
        # over providing a framework for algebraic computation
        #self._init_category_(VectorSpaces(self.L()))
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



    """
    Uses the linear recurrence to determine the matrix representation of the Frobenius endomorphism on the
    Crystalline cohomology w.r.t. the standard basis.
    """

    def crys_rec(self, deg, precision = 0):
        r, n, q = self._dim, self.dm().n(), self.dm().q()
        k_0, k = self._basis_rep.nrows() - r, deg - r
        k_rel = k - k_0
        sstar = ceil(sqrt(k_rel))
        s0, s1 = k_rel % sstar, k_rel // sstar
        if precision < 1:
            precision = self.dm().n() + 1
        rec_coeff = [ self.L()(-1)*self.dm()[r - i]/self.dm()[r] for i in range(1, r + 1) ]

        coeff_ring1 = PolynomialRing(self.L(), 'V')
        ideal = coeff_ring1.gen() - self.dm()[0]
        coeff_ring = QuotientRing(coeff_ring1, ideal**precision)

        # The initial matrices
        c0 = prod([self.init_matr(rec_coeff, i, coeff_ring) for i in range(s0, 0, -1)])
        gstep = prod([self.init_matr(rec_coeff, i, coeff_ring) for i in range(sstar + s0, s0, -1)])
        power_eval_matrs = [matrix(gstep).apply_map(lambda a: c_frob(a, i*sstar, q, n, coeff_ring.gen())) for i in range(s1 -1, -1, -1)]
        return prod(power_eval_matrs)*c0


    def charpoly(self, prec = 0):
        return self.crys_rec(self.dm().n() + self.dm().rank(), prec).charpoly()

## TODO: GET RID OF MOST OF THESE SO THERE IS ONLY ONE CHECK_CHAR FUNCTION

def check_char(dm, cp, frob_norm = 1):
    return sum([dm(cp[i])*dm.ore_ring().gen()**(dm.n()*i) for i in range(1, cp.degree() + 1)]) + frob_norm*dm(dm.frob_norm())


def double_replace(multi, c1, c2):
    coeffs1 = get_coeffs(multi)
    coeffsh = [ get_eval(a, c2) for a in coeffs1]
    return sum([coeff*(c1**i) for i, coeff in enumerate(coeffsh)])
