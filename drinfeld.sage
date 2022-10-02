import collections.abc
from time import perf_counter

from sage.structure.parent import Parent
from sage.categories.vector_spaces import VectorSpaces

from sage.rings.polynomial.ore_polynomial_element import OrePolynomial
from sage.rings.polynomial.ore_polynomial_ring import OrePolynomialRing
from sage.rings.polynomial.polynomial_ring import PolynomialRing_general
from sage.rings.finite_rings.finite_field_base import FiniteField
from sage.rings.integer import Integer
from sage.matrix.constructor import Matrix

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

# Retrieve the coefficients of anything loosely structured as a polynomial
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
        raise TypeError(f"object {a} does not have a standard coefficient attribute")

# retrieve the evaluation
def get_eval(poly_obj, elem):
    coeffs = get_coeffs(poly_obj)
    return sum([ coeff*elem**i for i, coeff in enumerate(coeffs) ])

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
        self._frob_L_v2 = dict()



    """
    Should eventually replace this with a more efficient computations leveraging fast modular composition.
    Caching

    fast skew acts on elements of self._L

    Probably should add a flag to indicate whether the user wants to use caching or not for space saving purposes. Also need a method to clear cache for
    testing.


    """


    def _fast_skew(self, a, iters = 1):
        # probably need a more robust way to check if a is an element of just the base (can it have L as a parent but still 'just' be an element of base?)
        t_iters = iters % self._n
        if a.parent() is self._base or t_iters == 0:
            return a
        if (a, t_iters) in self._frob_L:
            return self._frob_L[(a, t_iters)]

        # Should properly fix this to properly check for coercion

        if a.parent() is self._L or True:
            im = self._L(a)
            for i in range(t_iters):
                """
                TODO: Replace this critical line with a more efficient approach.
                """
                im = self._ore_ring.twisting_morphism()(im)
            self._frob_L[(a, t_iters)] = im
            return im
        raise TypeError(f"{a} does not coerce into {self._L}")

    def _fast_skew_v2(self, a, iters = 1):
        # probably need a more robust way to check if a is an element of just the base (can it have L as a parent but still 'just' be an element of base?)
        t_iters = iters % self._n
        if parent(a) is self._base or t_iters == 0:
            return a
        if a in self._frob_L_v2 and t_iters in self._frob_L_v2[a]:
            return self._frob_L_v2[a][t_iters]

        # Should properly fix this to properly check for coercion

        if parent(a) is self._L or True:
            if not a in self._frob_L_v2:
                self._frob_L_v2[a] = dict()
                start = 0
                im = self._L(a)
            else:
                start = max(self._frob_L_v2[a].keys())
                im = self._frob_L_v2[a][start]
            for i in range(start, t_iters):
                """
                TODO: Replace this critical line with a more efficient approach.
                """
                im = self._ore_ring.twisting_morphism()(im)
                self._frob_L_v2[a][i + 1] = im
            self._frob_L_v2[a][t_iters] = im
            return im
        raise TypeError(f"{a} does not coerce into {self._L}")

    """
    Interpret an element of L as an element of A via its canonical polynomial representative of degree at most n
    """
    def to_reg(self, a):
        return self._reg(get_coeffs(a))
        #return sum([coeff*self._reg.gen()**i for i, coeff in enumerate(a.list())])

    """
    Interpret an element of L as an element of base using its constant term
    """
    def to_base(self, a):
        return get_coeffs(a)[0]





class DrinfeldModule():
    def __init__(self, ore, context=None):
        # determine if we are initializing from a skew polynomial or an array
        skew_gen = isinstance(parent(ore), OrePolynomialRing)
        """
        Ensure we are initializing with a valid data type.
        Valid data types: ore polynomial, python sequences, or sage
        We will later check that these data types contain entries or coefficients over a field.
        """
        if not skew_gen and not isinstance(ore, collections.abc.Sequence) and not isinstance(parent(ore), MatrixSpace):
            raise TypeError("Not a valid data type")

        if context == None:
            # init context from ore
            if skew_gen:
                # This does some checking that is already done when the context is created. Should probably elminiate this.
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
        Cache for coefficients of powers \phi_x^i
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
    Compute the coefficients of the gamma-adic expansion
    This should only work
    """
    def gamma_adic(self, a):
        reg_a = self.reg()(get_coeffs(a))
        if reg_a == self.reg().zero() or reg_a.degree() < self._gamma_reg.degree():
            return reg_a
        expansion = []
        rem = reg_a
        while(rem != 0):
            res = rem % self._gamma_reg
            expansion.append(res)
            rem = rem // self._gamma_reg
        const = expansion[0]
        expansion[0] = self.reg().zero()
        result = self.reg()(expansion) + const
        return result

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
            raise ValueError(f"Can't compute the inverse of the gamma map from {self._L} to {self._prime_field}")
        res = sum([coeff*self._gamma_inv**i for i, coeff in enumerate(get_coeffs(a))])
        return res




    """
    Given a degree deg, expand the matrix self._phi_x_matrix to include coefficients of \phi_x^i for i up to degself.

    This is mostly an internal method i.e. this should only be called by other methods to compute and cache \phi_x^i
    when necessary to do so for other methods.
    """

    def _phi_x_v2(self, deg):
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
    def _map(self, ap):
        a = ap
        # if isinstance(ap, int):
        #     return ap
        if not (a.parent() is self.reg()):
            coeffs = get_coeffs(a)
            if coeffs != None:
                a = self.reg()(coeffs)
            else:
                raise ValueError("Value {a} can't be interpreted as a polynomial expression.")

            # Expand the matrix of powers of \phi_x if degree of a is too large
        if a.degree() >= len(self._phi_x_matrix): self._phi_x_v2(a.degree())
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
        if d >= len(self._phi_x_matrix): self._phi_x_v2(d) # Extend phi_x^i cache if d is too large
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
        self._phi_x_v2(self.n())
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
        #for i in range(nrow):
            # For columns we split the iteration to iterate over the a_j and then over the individual degree
            # coefficients a_{jk}
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


class DrinfeldCohomology_dR(Parent):
    def __init__(self, dm):
        # The associated Drinfeld Module
        self._dm = dm
        self._dim = dm.rank()
        # Not sure how necessary this is since we are mostly concerned with performance
        # over providing a framework for algebraic computation
        self._init_category_(VectorSpaces(self.L()))

        """
        As necessary, we can compute and cache representations of \eta
        in terms of the canonical basis.

        Each row i represents \eta_x = \tau^(i + 1)

        This is initialized to the r x r identity.

        """
        self._basis_rep = identity_matrix(self.L(), self._dim)

    """
    An implementation of the matrix method for solving linearly recurrent sequence

    Given the cohomology space, compute the canonical basis representation of \eta_x = \tau^deg

    """

    def rec_mat_meth(self, deg):
        r = self._dim
        k_0, k = self._basis_rep.nrows() - r, deg - r
        k_rel = k - k_0
        sstar = ceil(sqrt(k_rel))
        s0, s1 = k_rel % sstar, k_rel // sstar
        rec_matr = matrix(self.L(), r, r)
        rec_coeff = [ self.L()(-1)*self.dm()[r - i]/self.dm()[r] for i in range(1, r + 1) ]
        coeff_ring = PolynomialRing(self.L(), 'V')
        # The initial matrices
        matr0 = [self.init_matr(rec_coeff, i, self.L()) for i in range(s0, 0, -1)]
        # The polynomial matrices
        matry = [self.init_matr(rec_coeff, i, coeff_ring, True) for i in range(sstar + s0, s0, -1)]
        # See notation from my presentations
        c0 = prod(matr0)
        cy = prod(matry)
        matrs = [matrix(cy) for i in range(s1 - 1, -1, -1)]
        #eval_matrs = [matrs[i].apply_map(lambda a: coeff_ring(a)(self.fast_skew(self.dm()[0], -i*sstar))) for i in range(s1 -1, -1, -1)]
        #power_eval_matrs = [eval_matrs[s1 - 1 - i].apply_map(lambda a: self.fast_skew(a, i*sstar)) for i in range(s1 -1, -1, -1)]
        power_eval_matrs = [matrs[i].apply_map(lambda a: self.fast_skew(coeff_ring(a)(self.fast_skew(self.dm()[0], -i*sstar)), i*sstar)) for i in range(s1 -1, -1, -1)]
        start = self._basis_rep.matrix_from_rows_and_columns(range(self._basis_rep.nrows() - r, self._basis_rep.nrows()), range(r))
        return prod(power_eval_matrs)*c0*start

    # def char_poly(self):
    #     cpolyring = PolynomialRing(self.dm().reg(), 'X')
    #     # sometimes have to conver to the gamma adic representation
    #     return sum([self.dm()._context.to_reg(coeff)*cpolyring.gen()**i for i, coeff in enumerate(get_coeffs(self.rec_mat_meth(self.dm().n() + self.dm().rank()).charpoly())) ])
    #
    # def char_poly_v2(self):
    #     cpolyring = PolynomialRing(self.dm().reg(), 'X')
    #     return sum([self.dm()._context.to_reg(coeff)*cpolyring.gen()**i for i, coeff in enumerate(get_coeffs(self.rec_mat_meth(self.dm().n() + self.dm().rank()).charpoly())) ])
    #
    #
    # def char_poly_v0(self):
    #     cpolyring = PolynomialRing(self.dm().prime_field(), 'X')
    #     cpcoeffs = get_coeffs(self.rec_mat_meth(self.dm().n() + self.dm().rank()).charpoly())
    #     ieo = self.dm().to_prime(self.dm().gamma_inv(self.dm().to_reg(cpcoeffs[1])))
    #     l_coeffs = [self.dm().gamma_inv(self.dm().to_reg(coeff)) for coeff in cpcoeffs]
    #     prime_coeffs = [self.dm().to_prime(coeff) for coeff in l_coeffs]
    #     ret = cpolyring.zero()
    #     for i in range(len(prime_coeffs)):
    #         ret += (poly_to_base(prime_coeffs[i]))*cpolyring.gen()**i
    #     return ret

    def char_poly(self):
        cpolyring = PolynomialRing(self.dm().prime_field(), 'X')
        cpcoeffs = get_coeffs(self.rec_mat_meth(self.dm().n() + self.dm().rank()).charpoly())
        l_coeffs = [self.dm().gamma_inv(self.dm().to_reg(coeff)) for coeff in cpcoeffs]
        p_coeffs = [self.dm().to_prime(coeff) for coeff in l_coeffs]
        ret = cpolyring.zero()
        for i, coef in enumerate(p_coeffs):
            ret += (poly_to_base(coef))*cpolyring.gen()**i
        return ret

    # def char_poly_roots(self):
    #     cpolyring = PolynomialRing(self.dm().prime_field(), 'X')
    #     cpcoeffs = get_coeffs(self.rec_mat_meth(self.dm().n() + self.dm().rank()).charpoly())
    #     root_invs = []
    #     ieo = self.dm().to_prime(self.dm().gamma_inv(self.dm().to_reg(cpcoeffs[1])))
    #     for root in self.dm().roots:
    #         l_coeffs = [self.dm().gamma_inv2(self.dm().to_reg(coeff), root) for coeff in cpcoeffs]
    #         root_invs.append(l_coeffs)
    #     prime_coeffs = []
    #     for entry in root_invs:
    #         resg = [self.dm().to_prime(coeff) for coeff in entry]
    #         prime_coeffs.append(resg)
    #     cpoo = []
    #     for entry in prime_coeffs:
    #         ret = cpolyring.zero()
    #         for i in range(len(entry)):
    #             #print(f"prime coeff: {prime}")
    #             ret += (poly_to_base(entry[i]))*cpolyring.gen()**i
    #         cpoo.append(ret)
    #     #ret = sum([ (coeff)*cpolyring.gen()**i for i, coeff in enumerate(prime_coeffs) ])
    #     # print("returning")
    #     return cpoo

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

    def slow_rec(self):
        r = self._dm.rank()
        #X = self.AL.gen()
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

    # To simplify coding, we give an accessor to certain important objects.
    # Since H_dR is a vector space over L it makes sense to have direct access.
    def L(self):
        return self.dm().L()

    def fast_skew(self, a, iters = 1):
        return self.dm()._context._fast_skew_v2(a, iters)


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

    # To simplify coding, we give an accessor to certain important objects.
    # Since H_dR is a vector space over L it makes sense to have direct access.
    def L(self):
        return self.dm().L()

    def fast_skew(self, a, iters = 1):
        return self.dm()._context._fast_skew_v2(a, iters)

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
    Methods for computing representations of elements of the Crystalline cohomology

    Recall the the Crystalline Cohomology is a free module of rank r

    """
     # This does one round of long division by T - \gamma_T using the module action
     # It does this by computing a solution to the linear system S = R + (T - \gamma_T)*Q
     # Given S = a_i\tau^{i} +
     # This version uses the module action given in Angles
    def div_reduction(self, S):
        if parent(S) == self.dm().ore_ring():
            S = get_coeffs(S)
        kd = len(S)
        r = self._dm.rank()
        L = self._dm.L()
        q = self._dm.q()
        matr = matrix(L, kd, kd)
        vec = matrix(L, kd, 1)
        for i in range(kd):
            vec[i, 0] = L(S[i])
        for i in range(r):
            matr[i, i] = 1
        for i in range(kd-r):
            for j in range(r+1):
                matr[i + j, r + i] += self._dm[j]^(q^(i + 1))
        for i in range(kd - self._dim):
            matr[i, r + i] -= self._dm[0] #L(t)
        return matr.solve_right(vec)

    def full_reduction(self, S):
        mdeg = len(S)
        r = self._dm.rank()
        rep = []
        if mdeg <= r:
            rep.append(S)
            return rep
        S_p = S
        while(mdeg > r):
            rem = self.div_reduction(S_p)
            rem1 = [rem[i, 0] for i in range(r)]
            quo = [rem[i, 0] for i in range(r, mdeg)]
            rep.append(rem1)
            S_p = quo
            mdeg = mdeg - r
        return rep

    # find the coefficients of \tau^k in terms of the size r basis for H_{crys} over A_L
    def basis_rep(self, k):
        r = self._dm.rank()
        S = [0 for i in range(k)]
        S[k-1] = 1
        AL = self.AL
        rets = [AL(0) for i in range(r)]
        reps = self.full_reduction(S)
        # I need to understand how the truncation works: till unclear, for now its 0 because it works. But why? In theory I
        # should get the right answer no matter how I truncate
        # in theory: evaluate at any precision and set w = \gamma_T = t
        # Update: this does seem to work at any precision. Just need to evaluate at w = t i.e. mod (w - \gamma_T)
        # Next Step: what is the generalization of this for the non-prime field case?
        trunc = self.precision
        w = self.AL.gen()
        for i in range(min(trunc + 1, len(reps))):
            for j in range(len(reps[i])):
                rets[j] += reps[i][j]*((w - self._dm[0])**i)
        return rets

    def compute_charpoly_ILadic(self):
        r = self._dm._rank
        n = self._dm.n()
        matr = []
        for i in range(r):
            brep = self.basis_rep(n + i + 1)
            matr.append(brep)
            # print(f'brp: {n+i+1}')
            # print(brep)
            #matr.append(derham_force(drm, n + i + 1))
        smat = matrix(self.AL, matr)
        #print("ILadic matrix")
        #print(smat)
        #print("------------------------------")
        return smat.charpoly('Z')

    def slow_rec(self):
        r = self._dm.rank()
        X = self.AL.gen()
        n = self._dm.n()
        state = [[0 if i != r - 1 - j else 1 for i in range(r)] for j in range(r)]
        for k in range(1, n + 1):
            ri = len(state)
            invr = self._dm._context._fast_skew(self._dm[r], k)
            charqk = self._dm._context._fast_skew(self._dm[0], k)
            cfs = [sum([ self._dm._context._fast_skew(self._dm[r - i]/self._dm[r], k )*(-1)*state[ri - i][z] for i in range(1, r)] ) + (1/invr)*(X - charqk)*state[ri - r][z]  for z in range(r)]
            state.append(cfs)
        finmatr = []
        for i in range(r):
            finmatr.append(state.pop())
        smat = matrix(self.AL, finmatr)
        return smat.charpoly('Z')





    """
    An implementation of the matrix method for solving linearly recurrent sequence

    Given the cohomology space, compute the canonical basis representation of \eta_x = \tau^deg

    """

    def crys_mat_meth(self, deg):
        r = self._dim
        k_0, k = self._basis_rep.nrows() - r, deg - r
        k_rel = k - k_0
        sstar = ceil(sqrt(k_rel))
        s0, s1 = k_rel % sstar, k_rel // sstar
        rec_matr = matrix(self.L(), r, r)
        rec_coeff = [ self.L()(-1)*self.dm()[r - i]/self.dm()[r] for i in range(1, r + 1) ]
        n = self.dm().n()
        q = self.dm().q()

        precision = self.dm().n() / self.dm()._a_char.degree()

        c_ring = PolynomialRing(self.L(), 'V')
        ideal = c_ring.gen() - self.dm()[0]
        #coeff_ring = PolynomialRing(self.L(), 'V')
        coeff_ring = c_ring #QuotientRing(c_ring, ideal^precision)

        # The initial matrices
        matr0 = [self.init_matr(rec_coeff, i, coeff_ring) for i in range(s0, 0, -1)]
        # The polynomial matrices
        matry = [self.init_matr(rec_coeff, i, coeff_ring) for i in range(sstar + s0, s0, -1)]

        # print(f's0: {s0} | s1: {s1} | sstar: {sstar}')

        # See notation from my presentations
        c0 = prod(matr0)
        cy = prod(matry)
        matrs = [matrix(cy) for i in range(s1 - 1, -1, -1)]
        #eval_matrs = [matrs[i].apply_map(lambda a: get_eval(a,  self.raw_frob(coeff_ring.gen(), -i*sstar, q, n )  )  ) for i in range(s1 -1, -1, -1)]
        eval_matrs = [matrs[i] for i in range(s1 -1, -1, -1)]
        power_eval_matrs = [eval_matrs[s1 - 1 - i].apply_map(lambda a: c_frob(a, i*sstar, q, n, coeff_ring.gen())) for i in range(s1 -1, -1, -1)]
        #start = self._basis_rep.matrix_from_rows_and_columns(range(self._basis_rep.nrows() - r, self._basis_rep.nrows()), range(r))
        return prod(power_eval_matrs)*c0

    def char_poly(self):
        cpolyring = PolynomialRing(self.dm().reg(), 'X')
        # sometimes have to conver to the gamma adic representation
        return sum([self.dm().gamma_adic(self.dm()._context.to_reg(coeff))*cpolyring.gen()**i for i, coeff in enumerate(get_coeffs(self.rec_mat_meth(self.dm().n() + self.dm().rank()).charpoly())) ])

    def raw_frob(self, elem, oexp, q, n):
        true = oexp % n
        return elem**(q**true)


def check_char0(dm, cp, frob_norm = 1):
    return sum([dm(cp[i])*dm.ore_ring().gen()**(dm.n()*i) for i in range(cp.degree() + 1)]) + frob_norm*dm(dm.frob_norm())

def check_char(dm, cp, frob_norm = 1):
    return sum([dm(cp[i])*dm.ore_ring().gen()**(dm.n()*i) for i in range(1, cp.degree() + 1)]) + frob_norm*dm(dm.frob_norm())

def check_char_gamma(dm, cp, frob_norm = 1):
    return sum([dm(dm.gamma(dm._context.to_reg(cp[i])))*dm.ore_ring().gen()**(nn*i) for i in range(a.degree() + 1)]) + frob_norm*dm(dm.frob_norm())

def check_char_gek(dm, cp):
    return sum([dm(cp[i])*dm.ore_ring().gen()**(nn*i) for i in range(len(cp))]) + dm.ore_ring().gen()**(dm.n()*dm.rank())



def double_replace(multi, c1, c2):
    coeffs1 = get_coeffs(multi)
    coeffsh = [ get_eval(a, c2) for a in coeffs1]
    return sum([coeff*c1**i for i, coeff in enumerate(coeffsh)])


def crys_convert2(poly, dm, multivar, quor, var = 'X'):
    PP = PolynomialRing(dm.reg(), 'X')
    gamma_t = dm[0]
    coeffs = get_coeffs(poly)
    big = multivar.gens()[0]
    lit =  multivar.gens()[1]
    abg = double_replace(coeffs[1], big, lit)
    coo = []
    for i in range(1, len(coeffs)):
        a = double_replace(coeffs[i], big, lit)
        apl = a
        coo.append(apl)
    var = multivar.gens()[0]
    coop = []
    for poly in coo:
        coop.append(poly.polynomial(var))
    return sum([regr(coeff.polynomial(coeff.parent().gen()), dm)*PP.gen()**(i + 1) for i, coeff in enumerate(coop) ])


def regr(llst, dm):
    reg = dm.reg()
    base = dm.base()
    genr = reg.gen()
    llst2 = get_coeffs(llst)
    lest = []
    for ent in llst2:
        if len(get_coeffs(ent)) == 0:
            lest.append(dm.base().zero())
        else:
            lest.append( dm.to_base(get_coeffs(ent)[0]))
    return sum([coeff*genr**i for i, coeff in enumerate(lest)])


"""
Tests
"""

# def iinverse(dm, a, deg):
#     '''
#
#     '''
#     # if (a.degree() % self._rank != 0):
#     #     return None
#     # d = a.degree() // self._rank
#     # if d >= len(self._phi_x_matrix): self._phi_x_v2(d) # Extend phi_x^i cache if d is too large
#     d = deg / dm._rank
#     rhs = vector(dm.L(), 5)
#     inv_sys = matrix(dm.L(), 5, 5) # d+ 1
#     # print(f'd: {d}')
#     """
#     Build the system involving d + 1 unknowns by extracting coefficients of degree \tau^{ri} from
#     \phi_x^i and a i.e. we use every rth equation.
#     """
#     # print("len")
#     # print(len(rhs))
#
#     for i in range(d + 1):
#         #rhs[i]
#
#         # print(f"oloop: {i}")
#         # print(f'rhs: {rhs[1]}')
#         # print(f'adm: {a[dm._rank*i]}')
#         rhs[i] = a[dm._rank*i]
#         # print(f"oloopp: {i}")
#         for j in range(i, d + 1):
#             # print(f"inloop: {dm._rank*i} | {j}")
#             inv_sys[i,j] = dm._phi_x_matrix[j][dm._rank*i]
#             # print("donelo")
#
#     """
#     Will likely change this to catch ValueError if no solution exists
#     We should verify the coefficients lie in the base ring, and if they do
#     coerce the result into a polynomial over the base field
#     """
#     try:
#         sol = inv_sys.solve_right(rhs)
#         return dm.reg()([coeff.list()[0] for coeff in sol])
#     except ValueError:
#         return None


base_test = True
extra_test = False
force_interm = False
randomize = True
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
    #spn[0] = y

    print(f'Skew polynomial generator defining the dm: {spn} ')
    dm5 = DrinfeldModule(spn, con)
    drham = DrinfeldCohomology_dR(dm5)
    #io = drham.rec_mat_meth(nn + rr)
    print("char poly (under gamma map)")
    #chario = drham.char_poly_v2()
    #print(chario)
    #print("computing char poly")
    #cp = drham.char_poly() #io.charpoly()
    #print("h1")
    #opp = drham.char_poly_v0() #io.charpoly()
    #print("h2")
    #cp_v3 = drham.char_poly_v3() #io.charpoly()
    #cp_v4 = drham.char_poly_v4() #io.charpoly()
    # print("done char poly")
    #print(io.charpoly())
    #print(cp)

    #print(resultant)
    print("testing char poly")
    cp_prime = drham.char_poly()
    print(f"char poly from derham: {cp_prime}")
    print("verification (this should be 0):")
    resultant = check_char(dm5, cp_prime) #sum([dm5(cp[i])*dm5.ore_ring().gen()**(nn*i) for i in range(a.degree() + 1)]) + dm5(dm5.frob_norm())
    print(resultant)
    # root_ims = drham.char_poly_roots()
    # for root in root_ims:
    #     print(f'testing: {root}')
    #     rress = check_char(dm5, root)
    #     print(rress)

    print("crystalline")
    crys_cohom = DrinfeldCohomology_Crys(dm5)
    crys_mat = crys_cohom.crys_mat_meth(nn + rr)
    print(crys_mat)
    print("char poly")
    crys_char_poly = crys_mat.charpoly()
    print(crys_char_poly)
    cfer = get_coeffs(crys_char_poly)
    gamma_t = dm5[0]
    #mip = get_eval(dm5._a_char, tt)

    print("building new ring")
    KK.<TT, tt> = PolynomialRing(dm5.L(), 2, order='lex')
    mip = get_eval(dm5.L().modulus(), tt)
    #mip = get_eval(dm5._a_char, tt)
    h = dm5.n()//dm5._a_char.degree() # precision
    print("creating multi-ideal")
    ih = KK((TT - dm5[0])**h)
    print("tt")
    II = Ideal([KK(mip), KK(ih)])
    # II = Ideal([gamma_t.minimal_polynomial(tt), (TT - tt)**2])
    print("taking quo")
    II.groebner_basis()
    Q = KK.quo(II)
    print("cryscon2")
    crys_con2 = crys_convert2(crys_char_poly, dm5, KK, Q)
    print(crys_con2)
    print("check (should be 0)")
    #print(check_char(dm5, crys_con))
    print("check crys con 2 (should be 0)")
    char_res = check_char(dm5, crys_con2)
    print(char_res)
    # print("check crys con 2 with left shift")
    # print(check_char0(dm5, crys_con2))

    left = char_res.coefficients() #char_res/(dm5.ore_ring().gen()**nn)
    #re23 = iinverse(dm5, left, len(left) - 1)
    print("gekeler")
    cp_gek = dm5.char_poly_gek()
    print(cp_gek)
    print("checking gekeler algorithm (should be 0)")
    print(check_char_gek(dm5, cp_gek))
    print("testing factorization by (T - \gamma_T)")
    cp_direct = crys_cohom.compute_charpoly_ILadic()
    print(cp_direct)
    cdirect = get_coeffs(cp_direct)
    # print(cdirect[1]
    #RF.<TT, tt> = PolynomialRing(dm5.L(), 2, order='lex')
    # res3 = double_replace(cdirect[1], TT, tt)
    # #res2 = double_replace(cfer[2], TT, tt)
    # cc3 = Q(res3)
    # print(f"f quo: {cc3}")
    print("testing slow recurrence method (crystalline)")
    cp_slow = crys_cohom.slow_rec()
    print(cp_slow)
    print("testing slow recurrence method (crystalline)")
    cp_slow_derham = drham.slow_rec()
    print(cp_slow_derham)
