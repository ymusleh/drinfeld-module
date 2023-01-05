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

from drinfeld import DrinfeldModule, DMContext, check_char, get_coeffs, get_eval, poly_to_base, check_char_gek
from derham_cohomology import DrinfeldCohomology_deRham
from crystalline_cohomology import DrinfeldCohomology_Crys, double_replace

q = 125
F = GF(q)
Fp = PolynomialRing(F, 'y')
ip = Fp.irreducible_element(4)
LL = F.extension(ip)
con = DMContext(F, LL)

sp = con._ore_ring.random_element(5)

#print(f'test 111')
spp = sp.coefficients()
spp[0] = LL('y')

print("testing fast skew")
ell = con._L.random_element()
print(f'element: {ell}')
elli = ell**(q**3)
ellj = con._fast_skew(ell, 3)
ell0 = elli - ellj
print(f'q^3 test (should be 0): {ell0}')
ellip = ell**(q**5)
elljp = con._fast_skew(ell, 5)
ell0p = ellip - elljp
print(f'q^5 test (should be 0): {ell0p}')


print("making module")
dm5 = DrinfeldModule(spp, con)

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
print(dm5.gen()**7)
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

drham = DrinfeldCohomology_deRham(dm5)
#sp = con._ore_ring.random_element(5)

#dm5 = DrinfeldModule(sp, con)

print("testing coefficient access")
print(dm5.gen())
print(f'0th: {dm5[0]}')
print(f'1st: {dm5[1]}')
print(f'3rd: {dm5[3]}')
print(f'5th: {dm5[5]}')


print("testing L to reg")
lreg = dm5.L().random_element()
print(f'elem: {lreg}')
print(f'reg: {dm5.to_reg(lreg)}')
print(f'reg map: {dm5(lreg) - dm5(dm5.to_reg(lreg))}')
print("computing char poly")
cp = drham.charpoly()
print(cp)
print("verification (this should be 0):")
resultant = check_char(dm5, cp)
print(resultant)

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
    drham = DrinfeldCohomology_deRham(dm5)
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
