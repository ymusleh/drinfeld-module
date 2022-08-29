#from sage.rings.finite_rings.finite_field_constructor import GF
import collections.abc
from time import perf_counter

from sage.structure.parent import Parent
from sage.categories.vector_spaces import VectorSpaces

from sage.rings.finite_rings.finite_field_base import FiniteField
from sage.rings.polynomial.ore_polynomial_element import OrePolynomial
from sage.rings.polynomial.ore_polynomial_ring import OrePolynomialRing
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.polynomial_ring import PolynomialRing_general
from sage.rings.finite_rings.finite_field_base import FiniteField
from sage.rings.integer import Integer
from sage.matrix.constructor import Matrix
from sage.matrix.constructor import vector, matrix
#import sage.rings
from sage.structure.parent import Parent

from drinfeld import DMContext, DrinfeldModule, DrinfeldCohomology_dR, DrinfeldCohomology_Crys


F = GF(8)
Fp = PolynomialRing(F, 'y')
ip = Fp.irreducible_element(4)
LL = F.extension(ip)
con = DMContext(F, LL)

sp = con._ore_ring.random_element(5)

spp = sp.coefficients()
spp[0] = LL('y')

print("testing fast skew")
ell = con._L.random_element()
print(f'element: {ell}')
elli = ell**(8**3)
ellj = con._fast_skew(ell, 3)
ell0 = elli - ellj
print(f'q^3 test (should be 0): {ell0}')
ellip = ell**(8**5)
elljp = con._fast_skew(ell, 5)
ell0p = ellip - elljp
print(f'q^5 test (should be 0): {ell0p}')


print("making module")
dm5 = DrinfeldModule(sp, con)

print("generating element")
a = dm5.reg().random_element(8)

print("new")
t1 = perf_counter()
ima1 = dm5(a)
t2 = perf_counter()
print(f"new time: {t2 - t1}")
print("done1")
ac = a.coefficients(sparse=False)
print("old")
ima2 = dm5.raw_im(ac)

print("gamma map")
print(dm5.gamma(a))

print("check (should be 0)")
print(ima2 - ima1)
sigma = dm5.ore_ring().twisting_morphism()

print("true")
print(dm5.gen()^7)
print("reversed")
print(list(reversed(dm5._phi_x_matrix[7])))


print("testing inverse images")
z4 = dm5.base().gen()
xi = dm5.reg().gen()
tpoly = (z4 + 1)*xi^6 + (z4^2 + z4 + 1)*xi^5 + (z4^2 + z4)*xi^4 + (z4^2 + z4)*xi^3 + z4^2*xi^2 + 1
#dm5.reg().random_element(6)
tp_im = dm5(tpoly)
print(tpoly)
print("check inversion (should be 0)")
av = dm5._inverse(tp_im)
print(av - tpoly)

print("testing evaluation map")
a1_reg = dm5.reg().random_element(5)
ep = dm5.L().random_element()

a1_skew = dm5(a1_reg)

eva = dm5._eval(a1_reg, ep)

eva2 = dm5._eval(a1_skew, ep)

print("Should be the same")
print(eva2 - eva)

drham = DrinfeldCohomology_dR(dm5)
#sp = con._ore_ring.random_element(5)

#dm5 = DrinfeldModule(sp, con)

print("testing coefficient access")
print(dm5.gen())
print(f'0th: {dm5[0]}')
print(f'1st: {dm5[1]}')
print(f'3rd: {dm5[3]}')
print(f'5th: {dm5[5]}')
