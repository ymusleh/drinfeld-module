import collections.abc

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
from functools import lru_cache



"""
SPECIAL FUNCTIONS

These functions are broadly useful and probably shouldn't belong to any particular class

So they are defined here

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
    def __init__(self, base, L, var = 'x', svar = 't', lvar = 'z'):
        if isinstance(base, Field):
            self._base = base
        elif (base in ZZ or isinstance(base, int)) and is_prime_power(base):
            self._base = GF(base)
        else:
            raise TypeError("Can't construct the base field with the data given.")
        # Currently only support the function ring F_q[x]
        self._reg = PolynomialRing(self._base, var)

        if isinstance(L, Integer) or isinstance(L, int):
            Lp = PolynomialRing(self._base, lvar)
            self._L = self._base.extension(Lp.irreducible_element(L))
            self._n = L
        elif isinstance(L.parent(), PolynomialRing_general) and L.parent().base() is self._base and len(L.variables()) == 1 and L.is_irreducible():
            lvar = L.variables()[0]
            Lp = PolynomialRing(self._base, lvar)
            self._L = self._base.extension(L)
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

    @lru_cache(maxsize=None)
    def _fast_skew(self, a, iters = 1):
        t_iters = iters % self._n
        # lacks generality, but faster for this specific case
        return (a)**((self._base.order())**t_iters)

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
        arr_gen = isinstance(ore, collections.abc.Sequence)
        skew_gen = not arr_gen
        """
        Ensure we are initializing with a valid data type.
        Valid data types: ore polynomial, python sequences, or sage
        We will later check that these data types contain entries or coefficients over a field.
        """
        if not skew_gen and not isinstance(ore, collections.abc.Sequence) and not isinstance(ore.parent(), MatrixSpace):
            print("Not a valid data type")

        if context == None:
            # Create context from skew polynomial
            if skew_gen:
                L = ore.parent().base()
                F_q = L.base().base()
                self._context = DMContext(F_q, L)
        else:
            self._context = context


        if skew_gen:
            if ore.parent() is self.ore_ring():
                self._gen = ore
            else:
                raise TypeError(f'Ore polynomial {ore} not a valid member of Skew polynomial ring {context._ore_ring}')
        else:
            self._gen = self.ore_ring().zero()
            for i, coeff in enumerate(ore):
                self._gen += self.L()(coeff)*self.ore_ring().gen()**i


        self._rank = self._gen.degree()
        '''
        Cache for coefficients of skew polynomials \phi_x^i that are the images under the Drinfeld map
        phi of x^i
        '''
        self._phi_x_matrix = [[self.L().one()], self._gen.coefficients(sparse=False)]

        """
        Intermediate Field parameters
        The intermediate field F_{frak{p}} = gamma(A) can be inferred since gamma(x) is the constant term of phi(x)
        The A-characteristic frak{p} is therefore the minimal polynomial of gamma(x)

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
    Given a member a in the ring of regular functions self._context._reg, compute its image under the Drinfeld Module map
    defined by x |--> self.gen().
    """
    def __call__(self, a):
        return self._map(a)

    """
    Get the ith coefficient of the skew polynomial phi_x
    """
    def __getitem__(self, i):
        if isinstance(i, int) or isinstance(i, Integer) and i <= self.rank() and i >= 0:
            return self.gen().coefficients()[i]
        else:
            raise ValueError("Invalid subscript access for drinfeld module.")

    """
    Compute the image of a polynomial a under the A-characteristic map gamma
    """
    def gamma(self, a):
        return sum([coeff*self._gamma_x**i for i, coeff in enumerate(a.coefficients(sparse=False))])

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
    Given a degree deg, expand the matrix self._phi_x_matrix to include coefficients of phi_x^i for i up to degself.

    This is mostly an internal method i.e. this should only be called by other methods to compute and cache phi_x^i
    when necessary to do so for other methods.
    """
    def _phi_x(self, deg):
        """
        We compute the matrix images phi_x^i using the recurrence method (see Gekeler). By default we do this up to i = deg.

        """
        r, ext, phi_x = self._rank, len(self._phi_x_matrix), self._phi_x_matrix
        if ext > deg:
            return
        phi_x += [[self.L().zero() for j in range(r*i + 1)] for i in range(ext, deg + 1)]
        for i in range(max(2, ext), deg + 1):
            for j in range(r*i + 1):
                """
                low_deg: lowest degree term of phi_x contributing to the skew degree term of tau^j. This is 0 if j <= r*(i - 1) and j - r*(i-1) otherwise.
                high_deg: Highest degree term of phi_x contributing to the skew degree term of tau^j. This is min(r, j).

                [explain this computation further here]

                """
                low_deg, high_deg = max(j - r*(i-1), 0), min(r, j)
                recs = [ self.fast_skew(phi_x[i-1][j - k], k) for k in range(low_deg, high_deg + 1) ]
                phi_x[i][j] = sum([a*b for a, b in zip(phi_x[1][low_deg:high_deg + 1], recs)])

    """
    Given a member a in the ring of regular functions self._context._reg, compute its image under the Drinfeld Module map
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
                im += coeff*roeff*self.ore_ring().gen()**j
        return im

    '''
    Given a skew polynomial a, determine if it is in the image phi(self.reg()), and if so return its preimage.
    Otherwise we return None
    '''
    def _inverse(self, a):
        if (a.degree() % self._rank != 0):
            return None
        d = a.degree() // self._rank
        if d >= len(self._phi_x_matrix): self._phi_x(d) # Extend phi_x^i cache if d is too large
        rhs = vector(self.L(), d + 1)
        inv_sys = matrix(self.L(), d + 1, d + 1 )

        """
        Build the system involving d + 1 unknowns by extracting coefficients of degree tau^{ri} from
        phi_x^i and a i.e. we use every rth equation.
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
            return self.reg()([coeff.list()[0] for coeff in sol])
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
        if poly.parent() is self.ore_ring():
            return sum([poly.coefficients(sparse=False)[i]*self.fast_skew(a, i) for i in range(poly.degree() + 1)])
        elif poly.parent() is self.reg():
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

    def frob_norm(self):
        return (-1)**((self._rank % 2) + (self.n() % 2)*((self._rank + 1) % 2 ))*(1/self[self._rank].norm())*(self._a_char)**(self.n()/self._m)



def check_char(dm, cp, frob_norm = 1):
    return sum([dm(cp[i])*dm.ore_ring().gen()**(dm.n()*i) for i in range(cp.degree() + 1)]) + frob_norm*dm(dm.frob_norm())

def check_char_gek(dm, cp):
    return sum([dm(cp[i])*dm.ore_ring().gen()**(dm.n()*i) for i in range(len(cp))]) + dm.ore_ring().gen()**(dm.n()*dm.rank())
