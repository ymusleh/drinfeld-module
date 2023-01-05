from sage.structure.parent import Parent
from sage.categories.vector_spaces import VectorSpaces

from sage.rings.finite_rings.finite_field_base import FiniteField
from sage.rings.polynomial.ore_polynomial_element import OrePolynomial
from sage.rings.polynomial.ore_polynomial_ring import OrePolynomialRing
from sage.rings.polynomial.polynomial_ring import PolynomialRing_general
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.finite_rings.finite_field_base import FiniteField
from sage.rings.integer import Integer
from sage.matrix.constructor import Matrix, matrix, vector, identity_matrix
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.all import Field

from sage.functions.all import ceil, sqrt
from sage.misc.misc_c import prod
from drinfeld import DrinfeldModule, get_coeffs, get_eval, poly_to_base

"""
Represents the de Rham Cohomology.

Recall:
N = L{\tau}\tau

D(\phi, L) = { \eta: A -> N : \eta_{ab} = \gamma_a \eta_b + \eta_a \phi_b }

H_{dR}(\phi, L) = D(\phi, L)

Why a separate class?

1.  For theoretical purposes: the Cohomology spaces associated to a Drinfeld Module are
    very different algebraic objects from the underlying Drinfeld Module (ring homomorphism v.s. actual modules).

    As actual modules, the Cohomology spaces can make sense as parents within the SageMath
    model.

2.  For practical purposes: separating computations based on the cohomology spaces from
    the more "standard" computations attached to Drinfeld Modules makes the classes more
    maintainable.

To Do: Decide if and how algebraic objects such as D(\phi, L) should be instantiated
using existing SageMath classes. Should this be done using rings, categories, or some other
class? To be determined.
"""

"""
Class for the de Rham Cohomology of a Drinfeld Module which we will denote H_dR throughout.

An element \eta of H_dR is uniquely specified by its evaluation at the generator for A, \eta_x,
which is a skew polynomial of degree at most r and 0 constant term.

In particular, H_dR is a dimension r vector space with a canonical basis \eta_x = \tau^i for 1 <= i <= r.

Under this identification, many computations on H_dR can be realized using algorithms for skew polynomials.
"""

class DrinfeldCohomology_deRham():
    def __init__(self, dm):
        # The associated Drinfeld Module
        self._dm = dm
        self._dim = dm.rank()

        """
        As necessary, we can compute and cache representations of \eta
        in terms of the canonical basis.

        Each row i represents \eta_x = \tau^(i + 1)

        This is initialized to the r x r identity.

        """
        self._basis_rep = identity_matrix(self.L(), self.dm().rank())

    """
    An implementation of the matrix method for solving linearly recurrent sequence

    Given the cohomology space, compute the canonical basis representation of \eta^(i+1)_x = \tau^(i + 1) up to
    degree deg. This method extends previously computed and cached values.

    """
    def derham_rec(self, deg):
        r = self._dim
        k_0, k = self._basis_rep.nrows() - r, deg - r
        k_rel = k - k_0
        sstar = ceil(sqrt(k_rel))
        s0, s1 = k_rel % sstar, k_rel // sstar
        rec_matr = matrix(self.L(), r, r)
        rec_coeff = [ self.L()(-1)*self.dm()[r - i]/self.dm()[r] for i in range(1, r + 1) ]
        coeff_ring = PolynomialRing(self.L(), 'V')

        # Giant Step algorithm for recurrence evaluation
        # See notation from my presentations
        c0 = prod([self.init_matr(rec_coeff, i, self.L()) for i in range(s0, 0, -1)])
        # Matrix for the "giant step"
        gstep = prod([self.init_matr(rec_coeff, i, coeff_ring, True) for i in range(sstar + s0, s0, -1)])
        power_eval_matrs = [matrix(gstep).apply_map(lambda a: self.fast_skew(coeff_ring(a)(self.fast_skew(self.dm()[0], -i*sstar)), i*sstar)) for i in range(s1 -1, -1, -1)]
        start = self._basis_rep.matrix_from_rows_and_columns(range(self._basis_rep.nrows() - r, self._basis_rep.nrows()), range(r))
        return prod(power_eval_matrs)*c0*start

    def charpoly(self):
        if self._dm.m() < self._dm.n():
            print("Warning: de Rham cohomology being used for non-prime case.")
            return None
        cpolyring = PolynomialRing(self.dm().prime_field(), 'X')
        cpcoeffs = get_coeffs(self.derham_rec(self.dm().n() + self.dm().rank()).charpoly())
        l_coeffs = [self.dm().gamma_inv(self.dm().to_reg(coeff)) for coeff in cpcoeffs]
        p_coeffs = [self.dm().to_prime(coeff) for coeff in l_coeffs]
        ret = cpolyring.zero()
        for i, coef in enumerate(p_coeffs):
            ret += (poly_to_base(coef))*cpolyring.gen()**i
        return ret

    """
    Initialize matrix for use in the recurrence method.
    """
    def init_matr(self, coeffs, k, ring, usepoly = False):
        r = self._dim
        matr = matrix(ring, r, r)
        for i in range(r):
            matr[0, i] = self.fast_skew(coeffs[i], k)
        for i in range(r-1):
            matr[i + 1, i] = 1
        if usepoly:
            matr[0, r-1] += (1/(self.fast_skew(self.dm()[r], k)))*ring.gen()
        else:
            matr[0, r-1] += self.dm()[0]/(self.fast_skew(self.dm()[r], k))
        return matr

    """
    Getters
    """
    def dm(self):
        return self._dm

    def L(self):
        return self.dm().L()

    def fast_skew(self, a, iters = 1):
        return self.dm()._context._fast_skew(a, iters)
