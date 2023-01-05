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
from sage.matrix.constructor import Matrix

from functools import lru_cache

"""
SPECIAL FUNCTIONS

These functions are broadly useful and probably shouldn't belong to any particular class

So they are defined here.

"""

"""
Returns the constant term of a polynomial, useful for reinterpreting field elements
stuck as polynomials back to the base field
"""
def poly_to_base(poly):
    if isinstance(poly.parent(), PolynomialRing_general):
        ret = get_coeffs(poly)[0]
        return ret
    else:
        return poly

"""
Retrieve the coefficients of anything loosely structured as a "polynomial".

This handles the fact that there are many ways that procedures SageMath
can return polynomial objects but no universal interface that works
for all cases.

"""

def get_coeffs(a):
    if a == a.parent().zero():
        return [0]
    if hasattr(a, 'coefficients'):
        return a.coefficients(sparse=False)
    elif hasattr(a, 'list'):
        return a.list()
    elif hasattr(a, 'polynomial'):
        return a.polynomial().list()
    else:
        raise TypeError(f"object {a} does not have a standard way to extract coefficients")

"""
Evaluate a "polynomial" based on its coefficients via get_coeffs
"""
def get_eval(poly_obj, elem):
    coeffs = get_coeffs(poly_obj)
    return sum([ coeff*elem**i for i, coeff in enumerate(coeffs) ])

# TODO: give this a better name
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

def raw_frob(elem, oexp, q, n):
    true = oexp #% n
    return elem**(q**true)

def check_inv(gt, rt):
    print(f"checking root: {rt}")
    res = get_eval(gt, rt)
    print(f"result: {res}")


class DMContext():
    """
    A DMContext stores information about the underlying algebraic structures of a finite
    Drinfeld Module. This is essentially a lightweight version of the category

     It has the following members:
    _base: A finite field of order q.
    _L: An extension field of _base of order n
    _reg: A ring of functions of a curve over _base regular outside of a fixed place infty. For our purpose, this will always be constructed
          as the ring of polynomials with coefficients in _base.
    _ore_ring: The ring of Ore polynomials with coefficients in L

    base: Can be either a finite field or a prime power giving the order
    L:

    Examples:

    1. Constructing a context given a base field and an extension

    F = GF(2^3)
    Fp.<z> = PolynomialRing(F, 'z')
    L = F.extension(Fz.irreducible_element(2))
    context = DMContext(F, L)

    2. Constructing a context given a base field and an irreducible polynomial

    F = GF(2^3)
    Fz.<z> = PolynomialRing(F, 'z')
    L = Fz.irreducible_element(2)
    context = DMContext(F, L)

    """
    def __init__(self, base, L, var = 'x', svar = 't', lvar = 'y'):
        '''
        Create base field.

        '''
        if isinstance(base, FiniteField):
            self._base = base
        elif (base in ZZ or isinstance(base, int)) and is_prime_power(base):
            self._base = GF(base)
        else:
            raise TypeError("Can't construct the base field with the data given.")
        # Create regular function field (currently only F_q[x])
        self._reg = PolynomialRing(self._base, var)
        '''
        Currently allow initialization of the "large" field L from three possible types:
        1. An integer n representing its dimension over the base field
        '''
        if isinstance(L, Integer) or isinstance(L, int):
            Lp = PolynomialRing(self._base, lvar)
            self._L = self._base.extension(Lp.irreducible_element(L), lvar)
            self._n = L
        elif isinstance(parent(L), PolynomialRing_general) and parent(L).base() is self._base and len(L.variables()) == 1 and L.is_irreducible():
            lvar = L.variables()[0]
            Lp = PolynomialRing(self._base, lvar)
            self._L = self._base.extension(L, lvar)
            self._n = L.degree()
        elif isinstance(L, Field):
            if not ((L.base() is self._base) or (isinstance(L.base(), PolynomialRing_general) and  L.base().base() is self._base)):
                raise TypeError("Field is not an extension of the base!")
            self._L = L
            self._n = L.modulus().degree()
        else:
            raise TypeError("Can't construct the extension field with the data given.")


        self._modulus = self._L.modulus()
        sigma = self._L.frobenius_endomorphism(base.degree())
        self._ore_ring = OrePolynomialRing(self._L, sigma, svar)
        """
        Initialize variables for caching useful computational results.

        self._frob_L: cache of images of elements of self._L under powers of the frobenius endomorphism. These will be cached as tuples (a, i)
        such that self._frob_L[(a, i)] = a^(q^i)
        """
        self._frob_L = dict()



    """
    Should eventually replace this with a more efficient computations leveraging fast modular composition.
    Caching

    fast skew acts on elements of self._L

    Probably should add a flag to indicate whether the user wants to use caching or not for space saving purposes. Also need a method to clear cache for
    testing.


    """

    @lru_cache(maxsize=None)
    def _fast_skew(self, a, iters = 1):
        t_iters = iters % self._n
        # lacks generality, but faster for this specific case
        return (a)^((self._base.order())^t_iters)

    def _fast_skew_v2(self, a, iters = 1):
        # probably need a more robust way to check if a is an element of just the base (can it have L as a parent but still 'just' be an element of base?)
        t_iters = iters % self._n
        if parent(a) is self._base or t_iters == 0:
            return a
        if a in self._frob_L and t_iters in self._frob_L[a]:
            return self._frob_L[a][t_iters]

        # Should properly fix this to properly check for coercion

        if parent(a) is self._L or True:
            if not a in self._frob_L:
                self._frob_L[a] = dict()
                start = 0
                im = self._L(a)
            else:
                start = max(self._frob_L[a].keys())
                im = self._frob_L[a][start]
            for i in range(start, t_iters):
                """
                TODO: Replace this critical line with a more efficient approach.
                """
                im = self._ore_ring.twisting_morphism()(im)
                self._frob_L[a][i + 1] = im
            self._frob_L[a][t_iters] = im
            return im
        raise TypeError(f"{a} does not coerce into {self._L}")

    """
    Cast an element of L as an element of A via its canonical polynomial representative of degree at most n
    """
    def to_reg(self, a):
        return self._reg(get_coeffs(a))

    """
    Project L onto base using its constant term
    """
    def to_base(self, a):
        return get_coeffs(a)[0]





class DrinfeldModule():
    def __init__(self, ore, context=None):
        # determine if we are initializing from a skew polynomial or an array
        skew_gen = isinstance(parent(ore), OrePolynomialRing)
        """
        Check we are initializing with a valid data type.
        Valid data types: ore polynomial, python sequences, or sage seq
        We will later check that these data types contain entries or coefficients over a field.
        """
        if not skew_gen and not isinstance(ore, collections.abc.Sequence) and not isinstance(parent(ore), MatrixSpace):
            raise TypeError("Not a valid data type")

        if context == None:
            # init context from ore
            if skew_gen:
                L = parent(ore).base()
                F_q = L.base().base()
                self._context = DMContext(F_q, L)
        else:
            self._context = context
        if skew_gen:
            if parent(ore) is self.ore_ring():
                self._gen = ore
            else:
                raise TypeError(f'Ore polynomial {ore} not a valid member of Skew polynomial ring {context._ore_ring}')
        else:
            self._gen = self.ore_ring().zero()
            for i, coeff in enumerate(ore):
                self._gen += self.L()(coeff)*self.ore_ring().gen()^i
        self._rank = self._gen.degree()
        '''
        Cache for coefficients of skew polynomials \phi_x^i that are the images under the Drinfeld map
        \phi of x^i
        '''
        self._phi_x_matrix = [[self.L().one()], self._gen.coefficients(sparse=False)]

        """
        Intermediate Field parameters
        The intermediate field F_{\frak{p}} = \gamma(A) can be inferred since \gamma(x) is the constant term \phi_x
        The A-characteristic \frak{p} is therefore the minimal polynomial of \gamma(x)

        Strictly speaking, a lot of this is not necessary for any of the currently implemented algorithms, but nice to have.

        """
        self._gamma_x = self.gen().coefficients(sparse=False)[0] # image of x is the constant term
        self._a_char = self._gamma_x.minpoly()
        self._m = self._a_char.degree()
        self._prime_field = self.base().extension(self._a_char, 'j')
        self._gamma_reg = self._context.to_reg(self._gamma_x)
        '''
        The inverse of gamma is represented by the image of self._L.gen(). Currently computed by factoring
        L.modulus() over the prime field.
        '''
        self._gamma_inv = None
        for root, mult in self.modulus().roots(self.prime_field()):
            if get_eval(self._gamma_x, root) == self._prime_field.gen():
                self._gamma_inv = root
                break


    """
    Given a member \a in the ring of regular functions self._context._reg, compute its image under the Drinfeld Module map
    defined by x |--> self.gen().
    """
    def __call__(self, a):
        return self._map(a)

    """
    Get the ith coefficient of the skew polynomial \phi_x
    """
    def __getitem__(self, i):
        if isinstance(i, int) or isinstance(i, Integer) and i <= self.rank() and i >= 0:
            return self.gen().coefficients(sparse=False)[i]
        else:
            raise ValueError("Invalid subscript access for drinfeld module.")

    """
    Compute the image of a polynomial a under the A-characteristic map \gamma
    """

    def gamma(self, a):
        return sum([coeff*self._gamma_x^i for i, coeff in enumerate(a.coefficients(sparse=False))])

    """
    convert to representation in terms of prime field uniformizer
    """
    def to_prime(self, a):
        coeffs = get_coeffs(a)
        return sum([coeff*self.prime_field().gen()**i for i, coeff in enumerate(coeffs)])


    """
    Compute the reverse map from L to F_{\frak{p}} when they are equal
    """
    def gamma_inv(self, a):
        if self._gamma_inv == None:
            raise ValueError(f"Can't compute the inverse of the gamma map from {self.L()} to {self._prime_field}")
        res = sum([coeff*self._gamma_inv**i for i, coeff in enumerate(get_coeffs(a))])
        return res




    """
    Given a degree deg, expand the matrix self._phi_x_matrix to include coefficients of \phi_x^i for i up to degself.

    This is mostly an internal method i.e. this should only be called by other methods to compute and cache \phi_x^i
    when necessary to do so for other methods.
    """

    def _phi_x(self, deg):
        """
        We compute the matrix images \phi_x^i using the recurrence method (see Gekeler). By default we do this up to i = deg.

        """
        r, ext, phi_x = self._rank, len(self._phi_x_matrix), self._phi_x_matrix
        if ext > deg:
            return
        phi_x += [[self.L().zero() for j in range(r*i + 1)] for i in range(ext, deg + 1)]
        phi_x[1] = self._gen.coefficients(sparse=False)
        for i in range(max(2, ext), deg + 1):
            for j in range(r*i + 1):
                """
                low_deg: lowest degree term of \phi_x contributing to the skew degree term of \tau^j. This is 0 if j <= r*(i - 1) and j - r*(i-1) otherwise.
                high_deg: Highest degree term of \phi_x contributing to the skew degree term of \tau^j. This is min(r, j).

                [explain this computation further here]

                """
                low_deg, high_deg = max(j - r*(i-1), 0), min(r, j)
                recs = [ self.fast_skew(phi_x[i-1][j - k], k) for k in range(low_deg, high_deg + 1) ]
                phi_x[i][j] = sum([a*b for a, b in zip(phi_x[1][low_deg:high_deg + 1], recs)])

    """
    Given a member \a in the ring of regular functions self._context._reg, compute its image under the Drinfeld Module map
    defined by x |--> self.gen().
    """
    def _map(self, a):
        # Bad practice: this is coercive
        if not (a.parent() is self.reg()):
            coeffs = get_coeffs(a)
            if coeffs != None:
                a = self.reg()(coeffs)
            else:
                raise ValueError("Value {a} can't be interpreted as a polynomial expression.")

            # Expand the matrix of powers of \phi_x if degree of a is too large
        if a.degree() >= len(self._phi_x_matrix): self._phi_x(a.degree())
        im = self.ore_ring().zero()
        for i, coeff in enumerate(a.coefficients(sparse=False)):
            for j, roeff in enumerate(self._phi_x_matrix[i]):
                im += coeff*roeff*self.ore_ring().gen()^j
        return im


    '''
    Given a skew polynomial a, determine if it is in the image \phi(self.reg()), and if so return its preimage.
    Otherwise we return None
    '''
    def _inverse(self, a):
        '''

        '''
        if (a.degree() % self._rank != 0):
            return None
        d = a.degree() // self._rank
        if d >= len(self._phi_x_matrix): self._phi_x(d) # Extend phi_x^i cache if d is too large
        rhs = vector(self.L(), d + 1)
        inv_sys = matrix(self.L(), d + 1, d + 1 )

        """
        Build the system involving d + 1 unknowns by extracting coefficients of degree \tau^{ri} from
        \phi_x^i and a i.e. we use every rth equation.
        """
        for i in range(d + 1):
            rhs[i] = a[self._rank*i]
            for j in range(i, d + 1):
                inv_sys[i,j] = self._phi_x_matrix[j][self._rank*i]

        """
        Will likely change this to catch ValueError if no solution exists
        We should verify the coefficients lie in the base ring, and if they do
        coerce the result into a polynomial over the base field
        """
        try:
            sol = inv_sys.solve_right(rhs)
            return self.to_reg(sum([get_coeffs(coeff)[0]*self.reg().gen()**i for i, coeff in enumerate(sol)]))
        except ValueError:
            return None

    """
    Given either an element of self.reg() or a skew polynomial and an element of L
    Compute its image under the Drinfeld Module action.

    if a in A and b in L then this computes \phi_a(b)
    if a is a skew polynomial, this computes a(b)

    Technically should check if poly is actually in \phi(A). This could be done by
    inverting poly but that is quite costly so probably won't do that. Will likely
    just check degrees.
    """

    def _eval(self, poly, a):
        if parent(poly) is self.ore_ring():
            return sum([poly.coefficients(sparse=False)[i]*self.fast_skew(a, i) for i in range(poly.degree() + 1)])
        elif parent(poly) is self.reg():
            # For now, just compute the image and evaluate at a
            return self._eval(self(poly), a)
        else:
            raise TypeError(f"{poly} is not a valid polynomial in the domain or codomain of the Drinfeld Module")

    """
    Finds the characteristic polynomial by solving for a degree r polynomial for which the Frobenius element is a root.

    That is, we solve for a_i = \sum_{j=0}^{n(r - i)/r} a_{i,j}T^j such that

    \tau^n + \phi_{a_{r-1}} \tau^{n(r-1)} + \ldots + \phi_{a_1} \tau^n + \phi_{a_0} = 0

    Requires computing \phi_T^i for i up to O(n)
    """
    def char_poly_gek(self):
        tring = self.reg() #PolynomialRing(self.L(), 'k')
        x = tring.gen()
        self._phi_x(self.n())
        """
        Setting up the matrix

        ith row corresponds to the contribution to the degree i skew term coefficients
        from all sources; nr + 1 rows overall

        We will likely precompute the frobenius norm using the closed form formula

        The variable vector is [a_{1,0}, a_{1,1}, \ldots, a_{r-1, n/r}]^T

        """
        # For now code it to find the constant term as well
        r = self.rank()
        n = self.n()
        nrow = self.n()*self.rank() + 1
        degs = [ (self.n()*(self.rank() - j))//self.rank() for j in range(r) ]
        shifts = [degs[i] + 1 for i in range(len(degs))]
        deg_off = [0] + [ sum(shifts[:i]) for i in range(1,r) ]
        ncol = sum(degs) + r
        sys = matrix(self.L(), nrow, ncol)
        rhs = vector(self.L(), nrow)
        rhs[nrow - 1] = -1
        for j in range(r):
            for k in range(shifts[j]):
                # Assuming the rows contain the coefficients of \phi_x^i, should double check
                ims = self._phi_x_matrix[k]
                for i in range(len(ims)):
                    # may need to fix the column index offset to account for constant terms
                    sys[i + n*j, deg_off[j] + k] = ims[i]

        sol = sys.solve_right(rhs)
        coeffs = []
        for i in range(r):
            poly = 0
            for j in range(shifts[i]):
                poly += self.to_base(sol[deg_off[i] + j])*x**j
            coeffs.append(poly)
        return coeffs


    """
    getters

    """
    def gen(self):
        return self._gen

    """
    Getters for Context properties and methods
    """
    def q(self):
        return self.base().order()

    def n(self):
        return self._context._n

    def m(self):
        return self._m

    def modulus(self):
        return self._context._modulus

    def rank(self):
        return self._rank

    def base(self):
        return self._context._base

    def L(self):
        return self._context._L

    def prime_field(self):
        return self._prime_field

    def reg(self):
        return self._context._reg

    def ore_ring(self):
        return self._context._ore_ring

    def fast_skew(self, a, iters = 1):
        return self._context._fast_skew(a, iters)

    def to_reg(self, a):
        return self._context.to_reg(a)

    # convert elements in L to their base embedding (the constant term)
    def to_base(self, a):
        return self._context.to_base(a)



    """
    for testing purposes
    """
    def raw_im(self, ac):
        return sum([self.gen()^(i) *ac[i] for i in range(len(ac)) ])

    def frob_norm(self):
        return (-1)**((self._rank % 2) + (self.n() % 2)*((self._rank + 1) % 2 ))*(1/self[self._rank].norm())*(self._a_char)**(self.n()/self._m)



"""
Represents the de Rham and Crystalline Cohomology.

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

# TODO: ***FIX VARIABLE NAMES TO MAKE THEM MORE DESCRIPTIVE***


class DrinfeldCohomology_dR(Parent):
    def __init__(self, dm):
        # The associated Drinfeld Module
        self._dm = dm
        self._dim = dm.rank()
        # Not sure how necessary this is since we are mostly concerned with performance
        # over providing a framework for algebraic computation
        self._init_category_(VectorSpaces(self.L()))

        """
        As necessary, we can compute and cache representations of \eta^(i)
        in terms of the canonical basis.

        Each row i represents \eta^(i+1)_x = \tau^(i + 1)

        This is initialized to the r x r identity.

        """
        self._basis_rep = identity_matrix(self.L(), self._dim)

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

    def charpoly_slow_rec(self):
        r = self._dm.rank()
        n = self._dm.n()
        state = [[0 if i != r - 1 - j else 1 for i in range(r)] for j in range(r)]
        for k in range(1, n + 1):
            ri = len(state)
            invr = self._dm._context._fast_skew(self._dm[r], k)
            charqk = self._dm._context._fast_skew(self._dm[0], k)
            cfs = [sum([ self._dm._context._fast_skew(self._dm[r - i]/self._dm[r], k )*(-1)*state[ri - i][z] for i in range(1, r)] ) + (1/invr)*(self._dm[0] - charqk)*state[ri - r][z]  for z in range(r)]
            state.append(cfs)
        finmatr = []
        for i in range(r):
            finmatr.append(state.pop())
        smat = matrix(self._dm.L(), finmatr)
        return smat.charpoly('Z')


    """
    Getters
    """
    # Return the underlying Drinfeld Module
    def dm(self):
        return self._dm

    def L(self):
        return self.dm().L()

    def fast_skew(self, a, iters = 1):
        return self.dm()._context._fast_skew(a, iters)


class DrinfeldCohomology_Crys(Parent):
    def __init__(self, dm):
        # the associated Drinfeld Module
        self._dm = dm
        self._dim = dm.rank()
        # Not sure how necessary this is since we are mostly concerned with performance
        # over providing a framework for algebraic computation
        self._init_category_(VectorSpaces(self.L()))
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
        coeff_ring = QuotientRing(coeff_ring1, ideal^precision)

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

def check_char_gek(dm, cp):
    return sum([dm(cp[i])*dm.ore_ring().gen()**(nn*i) for i in range(len(cp))]) + dm.ore_ring().gen()**(dm.n()*dm.rank())


def double_replace(multi, c1, c2):
    coeffs1 = get_coeffs(multi)
    coeffsh = [ get_eval(a, c2) for a in coeffs1]
    return sum([coeff*c1**i for i, coeff in enumerate(coeffsh)])

"""
Tests
"""

base_test = True
extra_test = False
force_interm = False
randomize = False
# set_base_mod = True
# set_ext_mod = True

base_mod = x^2 + x + 1

if base_test:
    qq = 4
    nn = 6
    rr = 3
    mm = 2
    base_mod = x^2 + x + 1
    if randomize:
        F = GF(qq, 'c')
        print(f"base field modulus: {F.modulus()}")
    else:
        F = GF(qq, name='c', modulus = base_mod)
    c, cc = F.gen(), F.gen()
    Fp = PolynomialRing(F, 'y')
    y, yy = Fp.gen(), Fp.gen()

    ext_mod = y^6 + (c + 1)*y^4 + y^3 + (c + 1)*y^2 + c*y + 1  #yy^6 + yy^3 + (cc + 1)*(yy^2) + yy + 1 # modulus for extension (L)

    if randomize:
        ip = Fp.irreducible_element(nn)
        print(f"extension modulus: {ip}")
    else:
        ip = ext_mod
    LL = F.extension(ip, 'y')
    con = DMContext(F, LL)
    print(f'Base Field: {F}')
    print(f'Extension: {LL}')
    tau, t = con._ore_ring.gen(), con._ore_ring.gen()
    if randomize:
        sp = con._ore_ring.random_element(rr)
        print(f"sp: {sp}")
    else:
        sp = (c*y^5 + (c + 1)*y^4 + (c + 1)*y + 1)*t^3 + (y^5 + (c + 1)*y^4 + (c + 1)*y)*t^2 + ((c + 1)*y^5 + y^4 + c*y^3 + c*y^2 + c*y + 1)*t + y^5 + c*y^4 #tau^3 + (yy^2 + yy + 1)*tau^2 + tau + (yy^2 + 1)
    spn = sp.coefficients(sparse=False)
    if force_interm:
        min_po = Fp.random_element(mm)
        ro = min_po.roots(LL)
        while len(ro) == 0:
            min_po = Fp.random_element(mm)
        spn[0] = ro[0][0]

    print(f'Skew polynomial generator defining the dm: {spn} ')
    dm5 = DrinfeldModule(spn, con)
    drham = DrinfeldCohomology_dR(dm5)
    #io = drham.rec_rec(nn + rr)
    print("char poly (under gamma map)")
    print("testing char poly")
    cp_prime = drham.charpoly()
    print(f"char poly from derham: {cp_prime}")
    print("verification (this should be 0):")
    resultant = None
    if cp_prime != None:
        resultant = check_char(dm5, cp_prime) #sum([dm5(cp[i])*dm5.ore_ring().gen()**(nn*i) for i in range(a.degree() + 1)]) + dm5(dm5.frob_norm())
    print(resultant)
    print("crystalline")
    crys_cohom = DrinfeldCohomology_Crys(dm5)
    #print(crys_mat)
    print("char poly")
    crys_char_poly = crys_cohom.charpoly(nn/mm)
    print(crys_char_poly)
    cfer = get_coeffs(crys_char_poly)
    gamma_t = dm5[0]
    print("gekeler")
    cp_gek = dm5.char_poly_gek()
    print(cp_gek)
    print("checking gekeler algorithm (should be 0)")
    print(check_char_gek(dm5, cp_gek))
    h = dm5.n()//dm5._a_char.degree() # precision

    print("check mod")
    nring = PolynomialRing(dm5.L(), 'Xi')
    Xi = nring.gen()
    # cpsc = get_coeffs(cp_slow)
    ct1 = get_eval(cfer[1], Xi)
    print(f'Xi: {ct1}')
    tc = ct1 % (Xi - dm5[0])**h
    print(tc)


    # Testing lower precision
    KQ.<uu, tt, TT> = PolynomialRing(dm5.base(), 3, order='lex')
    KQ2.<aa, bb> = PolynomialRing(dm5.base(), 2, order='lex')
    mip = get_eval(dm5.L().modulus(), tt)
    #mip = get_eval(dm5._a_char, tt)

    gam = get_eval(dm5[0], tt)
    print("creating multi-ideal")
    ih = KQ((uu - gam))
    II = Ideal([KQ(mip), KQ(ih)])
    # II = Ideal([gamma_t.minimal_polynomial(tt), (TT - tt)**2])
    print("taking quo")
    ff = II.groebner_basis()
    print(f'grob: {ff}')
    fp = ff + [(TT - uu)**h]
    pu = get_eval(dm5._a_char, aa)
    xu = (bb - aa)**h
    Q = KQ.quo(fp)
    Q2 = KQ2.quo([pu, xu])
    tc = cfer[1]
    res1 = double_replace(tc, TT, tt)
    res2 = double_replace(tc, bb, aa)
    print(f'res1: {res1}')
    resq = Q(res1)
    resq2 = Q2(res2)
    print(f'quo: {resq}')
    print(f'quo: {resq2}')
