"""
The first package for computations in intersection theory and enumerative 
geometry is Schubert in Maple which written by Sheldon Katz and Stein A. Stromme
from 1992, and had been revised and updated to new versions of Maple by 
Jan-Magnus Okland. However, it is no longer actively supported. 
The second package is Schubert2 in Macaulay2 which has being developed by 
Daniel R. Grayson, Michael E. Stillman, Stein A. Str\o mme, David Eisenbud and 
Charley Crissman.

Our package is Schubert3 which developed on Sage and written by Python 
programming language. This package provides the key functionality necessary for 
computations in intersection theory and enumerative geometry. It deals with 
abstract varieties, vector bundles on abstract varieties, morphisms between 
abstract varieties, equivariant vector bundles on abstract varieties endowed 
with a torus action, moduli spaces of stable maps, and graphs.

In Schubert3, an abstract variety is represented by a nonnegative integer which 
is its dimension, a list of variables which are the minimal generators of its 
Chow ring, a list of positive integers which are the degrees of the variables as
a graded ring, and a list of polynomials which are the relations between the 
variables such that we can determine its Chow ring. Sometime the relations are 
not known, but we must know its monomial values. This allows us to compute the 
degree of a certain zero-dimensional cycle class. Moreover, we also developed an
alternative method for computing the degree of a zero-dimensional cycle class 
via Bott's formula. 

There are two ways to give a vector bundle E on an abstract variety in Schubert3. 
The first one is to represent E by a positive integer which is the rank of E, 
and an element of the Chow ring which is the total Chern class of E. The second 
one is to represent E by only an element of the Chow ring which is the Chern 
character of E. The main idea for the implementation of vector bundles is based 
on the splitting principle. A morphism between two abstract varieties is 
represented by its pullback homomorphism. 

In order to use Bott's formula for computing the degree of a zero-dimensional 
cycle class, we have to deal with some computational odjects such as equivariant
vector bundles on abstract varieties endowed with a torus action and moduli 
spaces of stable maps. An equivariant vector bundle is represented by its 
weights of the torus action on the ordinary vector bundle. A moduli space of 
stable maps is represented by a projective space and a positive integer which is
the degree of stable maps. We also deal with graphs which allow us to represent 
the fixed point components of a torus action on a moduli space of stable maps.

In order to use Schubert3, we first must attach the file Schubert3.py to a 
running session using the %attach command in Sage as follows:

    sage: %attach ~/Schubert3.py

The current version of this package is the result of many discussions on 
mathematical background and on implementation algorithms, and of many hours of 
coding. It should not be considered a complete, unchangeable, totally stable 
version. We will keep working on this project by fixing bugs, improving 
algorithms, and by adding functionalities.
"""
from sage.structure.sage_object import SageObject
import sage.libs.singular
from sage.rings.arith import factorial
from sage.structure.parent_gens import normalize_names
#from sage.combinat.sf.sfa import SFAElementary
from sage.libs.singular.function import SingularLibraryFunction
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.interfaces.singular import singular
from sage.rings.all import ZZ, QQ
from sage.rings.quotient_ring import QuotientRing
from sage.rings.polynomial.term_order import TermOrder

################################################################################
########################   Tools  ##############################################
################################################################################

def part(f,d):
    """
    Returns the homogeneous component of degree d of the polynomial f.

    EXAMPLES::

        sage: R.<x,y,z>=PolynomialRing(QQ)
        sage: f = x+y+x^2+y^3+z^3
        sage: part(f,1)
        x + y
        sage: part(f,2)
        x^2
        sage: part(f,3)
        y^3 + z^3
        sage: part(f,4)
        0
    """
    result = 0
    if type(f) == Integer or type(f) == int:
        if d == 0:
            return f
        else:
            return result
    n = f.degree()
    if d == 0:
        return f.constant_coefficient()
    elif d>n:
        return result
    else:
        if f.parent().ngens() == 1:
            return f.truncate(d+1)-f.truncate(d)
        else:
            m = f.monomials()
            for i in range(len(m)):
                if m[i].degree() == d:
                    result = result + f.monomial_coefficient(m[i])*m[i]
            return result

def parts(f,i,j):
    """
    Returns a new polynomial that is the sum of the homogeneous components of 
    degree from i to j of given polynomial f.
    
    EXAMPLES::

        sage: R.<x,y,z>=PolynomialRing(QQ)
        sage: f = x+y+x^2+y^3+z^3
        sage: parts(f,1,2)
        x^2 + x + y
    """
    return sum(part(f,k) for k in range(i,j+1))

def logg(f,d):
    """
    f is the total chern class. The chern character is returned.

    EXAMPLES::

        sage: R.<x,y> = PolynomialRing(QQ, order=TermOrder('wdegrevlex',[1,2]))
        sage: f = 1+x+y
        sage: logg(f,3)
        1/6*x^3 - 1/2*x*y + 1/2*x^2 - y + x
    """
    if f == 1:
        return 0
    else:
        if d == 0:
            return 0
        elif d == 1:
            return part(f,1)
        else:
            e = [part(f,i) for i in range(d+1)]
            p = [e[0],-e[1]]
            for n in range(2,d+1):
                p.append(-n*e[n]-sum(e[j]*p[n-j] for j in range(1,n)))
            return sum(1/factorial(i)*(-1)**i*p[i] for i in range(1,d+1))

def expp(f,d):
    """
    f is the Chern character. The total Chern class is returned.

    EXAMPLES::

        sage: R.<x> = QQ[]
        sage: f = 3 + x
        sage: expp(f,3)
        1/6*x^3 + 1/2*x^2 + x + 1
    """
    if type(f) == Integer:
        return 1
    else:
        p = [factorial(i)*part(f,i) for i in range(d+1)]
        e = [1]
        for n in range(1,d+1):
            s = sum((-1)**(j-1)*e[n-j]*p[j]/n for j in range(1,n+1))
            e.append(s)
        return sum(e)

def adams(f,d):
    """
    Needs this to compute Adams operations.

    EXAMPLES::

        sage: R.<x,y,z>=PolynomialRing(QQ,order=TermOrder('wdegrevlex',[1,2,3]))
        sage: f = 1 + x + y + z
        sage: adams(f,3)
        27*z + 9*y + 3*x + 1
    """
    if type(f) == Integer or type(f) == int:
        n = 0
    else:
        n = f.degree()
    return sum(d**i*part(f,i) for i in range(n+1))

def wedges(n,f,d):
    """
    Needs this to compute the n-th symmetric power of a vector bundle.

    EXAMPLES::

        sage: R.<x,y,z>=PolynomialRing(QQ,order=TermOrder('wdegrevlex',[1,2,3]))
        sage: f = 1 + x + y + z
        sage: wedges(2,f,3)
        [1, z + y + x + 1, x*y - 3*z + 1/2*x^2 - y]
    """
    if n == 0:
        return [1]
    elif n == 1:
        return [1,f]
    else:
        w = [1,f]
        for i in range(2,n+1):
            s = sum((-1)**(i-j+1)*parts(w[j]*adams(f,i-j),0,d)/i for j in range(i))
            w.append(s)
        return w

def todd(f,d):
    """
    Needs this to compute the Todd class.
    f is a Chern character. The Todd class is returned.

    EXAMPLES::

        sage: R.<x,y> = PolynomialRing(QQ, order=TermOrder('wdegrevlex',[1,2]))
        sage: f = 1 + x + y
        sage: g = logg(f,2)+2;g
        1/2*x^2 - y + x + 2
        sage: todd(g,2)
        1/12*x^2 + 1/12*y + 1/2*x + 1
    """
    if f == 0:
        return 1
    l = [(-1)**i/factorial(i+1) for i in range(d+1)]
    c = [1]
    for n in range(1,d+1):
        c.append(- sum(l[i]*c[n-i] for i in range(1,n+1)))
    R = PolynomialRing(QQ,'t')
    t = R.gen()
    g = sum(c[i]*t**i for i in range(d+1))
    h = logg(g,d)
    H = sum(h[i]*factorial(i)*part(f,i) for i in range(d+1))
    return expp(H,d)

def segre(f,d):
    """
    Needs this to compute the Segre class.
    f is a total Chern class of a vector bundle.
    The Segre class of this vector bundle should be returned.
    
    EXAMPLES::
    
        sage: R.<x,y,z>=PolynomialRing(QQ,order=TermOrder('wdegrevlex',[1,2,3]))
        sage: f = 1 + x + y + z
        sage: segre(f,4)
        x^4 - 3*x^2*y + y^2 + 2*x*z + x^3 - 2*x*y + z + x^2 - y + x + 1
        sage: f = 1
        sage: segre(f,4)
        1
    """
    if f == 1:
        return 1
    g = sum((1-f)**i for i in range(d+1))
    return sum(part(g,k) for k in range(d+1))

def schur(p,f):
    """
    Returns the Schur polynomial.
    p is a partition of integers.
    Needs this to compute the Porteous formula.
    
    EXAMPLES::
    
        sage: B = Base(3,bundles=[[3,'c']])
        sage: E = B.bundle(1)
        sage: f = E._chern_class
        sage: p = [1,1,1]
        sage: schur(p,f)
        c1^3 - 2*c1*c2 + c3
        sage: p = [2,1]
        sage: schur(p,f)
        c1*c2 - c3
        sage: p = [3]
        sage: schur(p,f)
        c3
    """
    R = f.parent()
    n = len(p)
    M = matrix(R,n,n)
    for i in range(n):
        for j in range(n):
            M[i,j] = part(f,p[i]+j-i)
    return det(M)

def pieri(k, n, m, a):
    """
    Needs this to implement the Pieri's formula.

    EXAMPLES::

        sage: pieri(2,4,1,[2])   
        [[2, 1]]
        sage: pieri(2,4,1,[1])
        [[2], [1, 1]]
    """
    t = m + sum(a)
    result = []
    l = Partitions(t).list()
    for e in l:
        if len(e) > k or len(e) < len(a):
            pass
        elif len(e) == 1:
            if a[0] <= e[0] <= n-k:
                result.append(e)
        else:
            a = a + [0]*(len(e)-len(a))
            for i in range(1,len(e)):
                if a[i] <= e[i] <= a[i-1] and a[0] <= e[0] <= n-k:
                    result.append(e)
    return result

def partition_dual(k,n,p):
    """
    """
    while len(p) < k:
        p.append(0)
    return [n-k-p[-1-i] for i in range(len(p))]

def kontsevich(d):
    """
    Returns the number of rational curves of degree d passing through 3d-1 
    general points in P^2.

    These numbers are also the genus zero Gromov-Witten invariants for P^2. 
    
    EXAMPLES::
    
        sage: kontsevich(3)
        12
        sage: kontsevich(4)
        620
        sage: kontsevich(5)
        87304
    """
    if d == 1:
        return 1
    if d == 2:
        return 1
    f = 0
    for i in range(1,d):
        j = d - i
        a = kontsevich(i)
        b = kontsevich(j)
        f = f + i**2*j*(j*binomial(3*d-4,3*i-2)-i*binomial(3*d-4,3*i-1))*a*b
    return f

def bipart(l):
    """
    Needs this to compute genus zero Gromow-Witten invariants for projective 
    spaces.

    EXAMPLES::

        sage: bipart([1,2])  
        [[[2], [1]], [[1, 2], []], [[], [1, 2]], [[1], [2]]]
        sage: len(bipart([1,2]))
        4
        sage: type(bipart([1,2]))
        <type 'list'>
    """
    if len(l) == 0:
        return [[[],[]]]
    elif len(l) == 1:
        k = l[0]
        return [[[],[k]],[[k],[]]]
    else:
        ll = [l[i] for i in range(len(l)-1)]
        R = bipart(ll)
        R1 = [[R[i][0] + [l[-1]],R[i][1]] for i in range(len(R))]
        R2 = [[R[i][0],R[i][1] + [l[-1]]] for i in range(len(R))]
        return R1 + R2

################################################################################
############################# Abstract varieties ###############################
################################################################################

class Variety(SageObject):
    """
    Construct a variety.
    """
    def __init__(self,dim,var=None,degs=None,rels=None,point=None,tb=None):
        self._dim = dim                   
        if var is not None: 
            self._var = var
        if degs is not None:
            self._degs = degs
        if rels is not None:
            self._rels = rels
        if point is not None:
            self._point = point
        if tb is not None:
            self._tb = tb
        else:
            self._point = []
            self._tb = []
            pass

    def _repr_(self):
        """
        Returns a string representation of this variety.
        
        EXAMPLES::
            
            sage: R.<h,e> = QQ[]
            sage: V = Variety(dim=2,var=[h,e],degs=[1,1],rels=[h*e,h^2+e^2]); V
            A variety of dimension 2
        """
        return "A variety of dimension %s" % self._dim

    def is_variety(self):
        """
        Returns "True" if self is a variety, otherwise returns "False"

        EXAMPLES::

            sage: R.<h,e> = QQ[]
            sage: V = Variety(dim=2,var=[h,e],degs=[1,1],rels=[h*e,h^2+e^2])
            sage: V.is_variety()
            True
        """
        return True

    def variables(self):
        """
        Returns the Chern variables of this variety.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.variables()
            (q1, q2)
            sage: P = ProjectiveSpace(3)
            sage: P.variables()
            (h,)
        """
        return self._var

    def degrees(self):
        """
        Returns the list of degrees of Chern variables.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.degrees()
            [1, 2]
            sage: P = ProjectiveSpace(3)
            sage: P.degrees()
            [1]
        """
        return self._degs

    def relations(self):
        """
        Returns the relations between the Chern variables of this variety. 
        This helps us define the Chow ring of this variety.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.relations()
            [-q1^3 + 2*q1*q2, q1^4 - 3*q1^2*q2 + q2^2]
            sage: G.chow_ring()
            Quotient of Multivariate Polynomial Ring in q1, q2 over Rational 
            Field by the ideal (-q1^3 + 2*q1*q2, q1^4 - 3*q1^2*q2 + q2^2)
            sage: P = ProjectiveSpace(3)
            sage: P.relations()
            [h^4]
            sage: P.chow_ring()
            Univariate Quotient Polynomial Ring in h over Rational 
            Field with modulus h^4
        """
        return self._rels

    def point(self):
        """
        Returns the section class of this variety.
        The degree of this class should be 1.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.point()
            q2^2
            sage: G.integral(G.point())
            1
        """
        return self._point


    def dim(self):
        """
        Returns the dimension of this variety.
        
        EXAMPLES::
        
            sage: R.<h,e> = QQ[]
            sage: V = Variety(dim=2,var=[h,e],degs=[1,1],rels=[h*e,h^2+e^2])
            sage: V.dim()
            2
        """
        return self._dim

    def base_ring(self):
        """
        Returns a polynomial ring in Chern variables with corresponding degrees.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.base_ring()
            Multivariate Polynomial Ring in q1, q2 over Rational Field
            sage: P = ProjectiveSpace(3)
            sage: P.base_ring()
            Univariate Polynomial Ring in h over Rational Field
        """
        w = self._degs
        return PolynomialRing(QQ, self._var, order = TermOrder('wdegrevlex',w))

    def chow_ring(self):
        """
        Returns the Chow ring of this variety.

        EXAMPLES::

            sage: R.<h,e> = QQ[]
            sage: V = Variety(dim=2,var=[h,e],degs=[1,1],rels=[h*e,h^2+e^2])
            sage: V.chow_ring()
            Quotient of Multivariate Polynomial Ring in h, e over Rational Field
            by the ideal (h*e, h^2 + e^2)
        """
        R = self.base_ring()
        I = R.ideal(self._rels)
        return QuotientRing(R,I,self._var)

    def tangent_bundle(self):
        """
        Returns the tangent bundle of this variety.
        
        EXAMPLES::
        
            
        """
        if self._tb == []:
            raise ValueError("have no data to compute the tangent bundle")
        return VectorBundle(self,chern_character=self._tb)

    def monomials(self, d):
        """
        Returns all monomials in the variables of this variety up to weighted
        degree d.

        EXAMPLES::

            sage: R.<h,e> = QQ[]
            sage: V = Variety(dim=2,var=[h,e],degs=[1,1],rels=[h*e,h^2+e^2])
            sage: V.monomials(1)
            [e, h]
            sage: V.monomials(2)
            [e^2, h*e, h^2]
            sage: G = Grassmannian(2,4)
            sage: G.monomials(4)
            [q2^2, q1^2*q2, q1^4]
            sage: P = ProjectiveSpace(3)
            sage: P.monomials(3)
            [h^3]
        """
        if d == 0:
            return [1]
        degs = WeightedIntegerVectors(d, self._degs)
        v = list(self._var)
        return [prod(v[i]**t[i] for i in range(len(v))) for t in degs]

    def monomial_values(self):
        """
        Returns integrals of top degree monomials up to a common scalar. 
        If point is given, we normalize so that the integral of point is 1.

        EXAMPLES::

            sage: R.<h,e> = QQ[]
            sage: V = Variety(dim=2,var=[h,e],degs=[1,1],rels=[h^2+e^2,h*e])
            sage: V.monomial_values()
            {h*e: 0, h^2: 1, e^2: -1}
            sage: G = Grassmannian(2,4)
            sage: G.monomial_values()
            {q2^2: 1, q1^4: 2, q1^2*q2: 1}
            sage: P = ProjectiveSpace(3)
            sage: P.monomial_values()
            {h^3: 1}
        """
        dim = self._dim
        variables = self._var
        MONS = self.monomials(dim)
        rels_d = []
        for rel in self._rels:
            d = rel.degree()
            if d <= self._dim:
                rels_d.extend([rel*m for m in self.monomials(dim-d)])
        if len(rels_d) == 0:
            if len(MONS) == 1:
                return {MONS[0]:1}
            else:
                raise ValueError("no relations in top degree")
            pass
        else:
            all_monoms = set()
            for rel in rels_d:
                all_monoms.update(rel.monomials())
            all_monoms = list(all_monoms)
            M = matrix(QQ, len(rels_d), len(all_monoms))
            for i, rel in enumerate(rels_d):
                for j, m in enumerate(all_monoms):
                    M[i,j] = rel.monomial_coefficient(m)
            K = M.right_kernel().matrix().transpose()
            if K.ncols() == 1:
                l = dict(zip(all_monoms, K.column(0)))
            elif K.ncols() == 0:
                l = dict(zip(all_monoms, [0]*len(all_monoms)))
                for m in MONS:
                    if m not in all_monoms:
                        l[m] = 1
                    pass
            if self._point == []:
                return l
            else:
                t = l[self._point]
                for m in l.keys():
                    l[m] = l[m]/t
                return l
            
    def additive_basis(self):
        """
        Returns a pair of dual bases for the Chow ring of this variety.

        EXAMPLES::

            sage: R.<h,e> = QQ[]
            sage: V = Variety(dim=2,var=[h,e],degs=[1,1],rels=[h*e,h^2+e^2])
            sage: V.additive_basis()
            ({0: [1], 1: [e, h], 2: [-e^2]}, {0: [1], 1: [-e, h], 2: [-e^2]})
            sage: G = Grassmannian(2,4)
            sage: G.additive_basis()
            ({0: [1], 1: [q1], 2: [q2, q1^2], 3: [q1*q2], 4: [q2^2]}, {0: [1],
            1: [q1], 2: [-q1^2 + 2*q2, q1^2 - q2], 3: [q1*q2], 4: [q2^2]})
            sage: P = ProjectiveSpace(3)
            sage: P.additive_basis()
            ({0: [1], 1: [h], 2: [h^2], 3: [h^3]},
            {0: [1], 1: [h], 2: [h^2], 3: [h^3]})
        """
        P = self.base_ring()
        D = self._dim
        basis = {}
        dualbasis = {}
        monomial_values = self.monomial_values()
        for k in range(int(D)/2+1):
            Rk = self.monomials(k)
            RDk = self.monomials(D-k)
            A = matrix(QQ, len(Rk), len(RDk))
            for i in range(len(Rk)):
                for j in range(len(RDk)):
                    A[i,j] = monomial_values.get(Rk[i]*RDk[j],0)
            rows = list(A.pivot_rows())
            columns = list(A.pivots())
            B = A.matrix_from_rows_and_columns(rows, columns)
            B_inv = B.inverse()
            B_inv_transpose = B_inv.transpose()
            basis[k] = [ Rk[i] for i in rows ]
            monomial_matrix = matrix(P,len(columns),1,[RDk[i] for i in columns])
            dualbasis[D-k] = (B_inv_transpose*monomial_matrix).column(0).list()
        for k in range(int((D-1)/2)+1):
            basis[D-k] = dualbasis[D-k]
            dualbasis[k] = basis[k]   
        return basis, dualbasis
            
    def codim(self, f):
        """
        Returns the codim of f as a class on this variety.
        If f is not equidimal, the maximum of the codims of the 
        components is returned.

        EXAMPLES::

            sage: R.<h,e> = QQ[]
            sage: V = Variety(dim=2,var=[h,e],degs=[1,1],rels=[h*e,h^2+e^2])
            sage: V.codim(h^3 + h*e)
            3
        """
        P = self.base_ring()
        f = P(f)
        return f.degree()

    def integral1(self, c):
        """
        Returns the degree of the zero cycle by using the monomial values of
        this variety. We often use this method for the varieties that the
        Chow ring is not known but the monomial values is known.
        
        EXAMPLES::
        
            sage: P = ProjectiveSpace(2,'h')
            sage: Q = ProjectiveSpace(2,'H')
            sage: H = Q.hyperplane()
            sage: L = Q.O(4*H)
            sage: B = BundleSection(L)
            sage: f = Morphism(B,P,[3*H])
            sage: D = f.double_point(); D
            26*H
            sage: B.monomial_values()
            {H: 4}
            sage: B.integral1(D)
            104
        """
        if self.codim(c) != self._dim:
            return 0
        v = list(self._var)
        d = self.monomial_values()
        if len(v) == 1:
            return c[self._dim]*d[v[0]**self._dim]
        elif len(c.parent().gens()) == 1:
            return c[c.degree()]*d[c.monic()]
        else:
            mons = c.monomials()
            coefs = c.coefficients()
            return sum(coefs[i]*d.get(mons[i],0) for i in range(len(coefs)))

    def integral(self, c):
        """
        Returns the degree of zero cycle after reducing this cycle to the Chow ring of this variety.
        c is an element of the Chow ring and usually the top Chern class of some vector bundle. 
        The leading coefficient of c is returned.
        We use this method for the varieties that the Chow ring is known.
    
        EXAMPLES:
        
            sage: G = Grassmannian(2,4)
            sage: Q = G.tautological_quotient_bundle()
            sage: B = Q.symmetric_power(3)
            sage: c = B.top_chern_class()
            sage: G.integral(c)
            27
        """
        if type(self) == Blowup:
            return self.integral1(c)
        if self.codim(c) != self._dim:
            return 0
        R = self.chow_ring()
        c = R(c)
        if R.ngens() == 1:
            return c.lift()[c.lift().degree()]
        else:
            return c.lc()

    def betti_number(self, n):
        """
        The n-th Betti number is returned.
        The Betti numbers mean the dimensions of the graded pieces of the
        numerical Chow ring. So they are the numbers of elements in each degree
        in the basis of this variety.
        
        EXAMPLES::

            sage: R.<h,e> = QQ[]
            sage: V = Variety(dim=2,var=[h,e],degs=[1,1],rels=[h*e,h^2+e^2])
            sage: V.betti_number(1)
            2
        """
        return len(self.additive_basis()[0][n])

    def betti_numbers(self):
        """
        Returns all betti numbers of this variety.
        
        EXAMPLES::

            sage: R.<h,e> = QQ[]
            sage: V = Variety(dim=2,var=[h,e],degs=[1,1],rels=[h*e,h^2+e^2])
            sage: V.betti_numbers()
            [1,2,1]
        """
        return [self.betti_number(i) for i in range(self._dim+1)]

    def O(self, d):
        """
        Returns a line bundle on this variety, its first Chern class = d.
        
        EXAMPLES::
        
            sage: P = ProjectiveSpace(3)
            sage: h = P.hyperplane()
            sage: L = P.O(2*h); L
            A vector bundle of rank 1 on A projective space of dimension 3
            sage: L.total_chern_class()
            2*h + 1
        """
        return VectorBundle(self, 1, chern_class=1+d)

    def blowup_points(self, k, var=None):
        """
        Returns the Blowup along finte points of this variety.
        
        EXAMPLES::
        
            sage: P = ProjectiveSpace(2,'h')
            sage: B = P.blowup_points(6); B
            A variety of dimension 2
            sage: v = B._var
            sage: f = 3*v[6] - v[0]-v[1]-v[2]-v[3]-v[4]-v[5]; f
            -e0 - e1 - e2 - e3 - e4 - e5 + 3*h
            sage: B.integral(f^2)
            3
        """
        p = self._point
        dim = self._dim
        if var is not None:
            d = normalize_names(k,var)
        else:
            d = normalize_names(k,'e')
        v = tuple(self._var)
        w = self._degs + [1]*k
        R = PolynomialRing(QQ, d+v, order=TermOrder('wdegrevlex',w))
        h = R.gens()
        r = self._rels + [h[i]**dim + (-1)**dim*p for i in range(len(d))]
        for i in range(len(h)-1):
            for j in range(i+1,len(h)):
                r.append(h[i]*h[j])
        return Variety(dim=self._dim, var = h, degs = w, rels = r, point=p)

class Point(Variety):
    """
    Makes a point as an abstract variety.
    """
    def __init__(self):
        self._dim = 0
        self._var = ()
        self._degs = []
        self._rels = []
        self._point = 1
        pass

    def _repr_(self):
        """
        Returns a string representation of this abstract variety.
        """
        return "A variety of dimension %s" % (self._dim)

class Base(Variety):
    """
    Makes an abstract variety from nothing, equipped with some bundles.
    Its Chow ring is the polynomial ring.
    """
    def __init__(self, dim, bundles):
        self._dim = dim
        self._bundles = bundles
        var = []
        degs = []
        for i in range(len(bundles)):
            l = list(normalize_names(bundles[i][0]+1,bundles[i][1]))
            l.pop(0)
            var = var + l
            degs = degs + [j+1 for j in range(bundles[i][0])]
        R = PolynomialRing(QQ,var,order=TermOrder('wdegrevlex',degs))
        self._var = R.gens()
        self._rels = []
        self._degs = degs
        self._point = 1
        pass

    def _repr_(self):
        """
        Returns a string representation of this abstract variety.

        EXAMPLES::

            sage: B = Base(4,bundles=[[2,'c'],[3,'d']]); B
            A variety of dimension 4
            sage: B._var
            ('c0', 'c1', 'd0', 'd1', 'd2')
            sage: B._degs
            [1, 2, 1, 2, 3]
        """
        return "A variety of dimension %s" % (self._dim)

    def bundle(self, i):
        """
        EXAMPLES::

            sage: B = Base(4,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1); S
            A vector bundle of rank 2 on A variety of dimension 4
            sage: S.rank()
            2
            sage: S.total_chern_class()
            c1 + c2 + 1
            sage: Q = B.bundle(2); Q
            A vector bundle of rank 3 on A variety of dimension 4
            sage: Q.rank()
            3
            sage: Q.total_chern_class()
            d1 + d2 + d3 + 1
        """
        if i == 1:
            k = 0
        else:
            k = sum(self._bundles[j][0] for j in range(i-1))
        v = self.chow_ring().gens()
        r = self._bundles[i-1][0]
        f = 1 + sum(v[j] for j in range(k,k+r))
        return VectorBundle(variety = self, rank = r, chern_class = f)

    def is_base(self):
        """
        """
        return True

    def chow_ring(self):
        """
        Returns the Chow ring of this variety.
        In this case the Chow ring should be a polynomial ring.
        
        EXAMPLES::
        
            sage: B = Base(4,bundles=[[2,'c'],[3,'d']])
            sage: B.chow_ring()
            Multivariate Polynomial Ring in c1, c2, d1, d2, d3
            over Rational Field
        """
        w = self._degs
        return PolynomialRing(QQ, self._var, order=TermOrder('wdegrevlex',w))

################################################################################
######################### Projective spaces ####################################
################################################################################

class ProjectiveSpace(Variety):
    """
    Makes a projective space as a variety.
    Its Chow ring is the polynomial ring in one variable 'var' (default 'h'),
    that is the hyperplane class.
    """
    def __init__(self, n, var=None):
        self._dim = n
        if var is not None:
            pass
        else:
            var = 'h'
        self._degs = [1]
        #R = PolynomialRing(QQ, var)
        R = PolynomialRing(QQ,var,order=TermOrder('wdegrevlex',self._degs))
        self._var = R.gens()
        h = R.gen()
        self._rels = [h**(n+1)]
        self._point = h**n
        pass

    def _repr_(self):
        """
        Returns a string representation of this projective space.

        EXAMPLES::

            sage: P = ProjectiveSpace(3); P
            A projective space of dimension 3
            sage: P.chow_ring()
            Univariate Quotient Polynomial Ring in h over Rational Field
            with modulus h^4
            sage: P.monomial_values()
            {h^3: 1}
            sage: P.additive_basis()
            ({0: [1], 1: [h], 2: [h^2], 3: [h^3]},
            {0: [1], 1: [h], 2: [h^2], 3: [h^3]})
            sage: P.betti_numbers()
            [1, 1, 1, 1]
        """
        return "A projective space of dimension %s"%(self._dim)

    def is_projective_space(self):
        """
        """
        return True

    def hyperplane(self):
        """
        Returns the hyperplane class of this projective space

        EXAMPLES::

            sage: P = ProjectiveSpace(3)    
            sage: h = P.hyperplane(); h
            h
            sage: P = ProjectiveSpace(3,'H')
            sage: h = P.hyperplane(); h
            H
        """
        return self._var[0]

    def O(self, n):
        """
        Returns the line bundle on this projective space such that 
        the first Chern class is n*h.

        EXAMPLES::

            sage: P = ProjectiveSpace(3)
            sage: L = P.O(1)
            sage: L.total_chern_class()
            h + 1
        """
        h = self.hyperplane()
        return VectorBundle(self,rank=1,chern_class=1+n*h)

    def tangent_bundle(self):
        """
        Returns the tangent bundle of this projective space.
        
        EXAMPLES:
        
            sage: P = ProjectiveSpace(3)
            sage: T = P.tangent_bundle(); T
            A vector bundle of rank 3 on A projective space of dimension 3
            sage: T.total_chern_class()
            4*h^3 + 6*h^2 + 4*h + 1
            sage: T.chern_character()
            2/3*h^3 + 2*h^2 + 4*h + 3
            sage: T.todd_class()
            h^3 + 11/6*h^2 + 2*h + 1
            sage: T.rank() == P.dim()
            True
        """
        n = self._dim
        R = PolynomialRing(QQ, self._var)
        h = R.gen()
        f = (1+h)**(n+1) - h**(n+1)
        return VectorBundle(self, rank=n, chern_class=f)

    def cotangent_bundle(self):
        """
        Returns the cotangent bundle of this projective space.
        
        EXAMPLES::
        
            sage: P = ProjectiveSpace(3)
            sage: C = P.cotangent_bundle(); C
            A vector bundle of rank 3 on A projective space of dimension 3
            sage: C.total_chern_class()
            -4*h^3 + 6*h^2 - 4*h + 1
            sage: C.chern_character()
            -2/3*h^3 + 2*h^2 - 4*h + 3
            sage: C.todd_class()
            -h^3 + 11/6*h^2 - 2*h + 1
        """
        return self.tangent_bundle().dual()

    def todd_class(self):
        """
        Returns the Todd class of this projective space.

        EXAMPLES::

            sage: P = ProjectiveSpace(3)
            sage: P.todd_class()
            h^3 + 11/6*h^2 + 2*h + 1
        """
        return self.tangent_bundle().todd_class()

    def poincare_polynomial(self, variable_name='t'):
        """
        Returns the Poincare polynomial of this projective space.

        EXAMPLES::

            sage: P = ProjectiveSpace(3)
            sage: P.poincare_polynomial()
            t^3 + t^2 + t + 1
        """
        R = PolynomialRing(ZZ, variable_name)
        t = R.gen()
        def f(m):
            g = 1
            for i in range(1,m+1):
                g = g*(1-(t**i))
            return g
        return f(self._dim +1)//(f(1)*f(self._dim))

    def betti(self):
        """
        Returns the list of Betti numbers of this projective space.

        EXAMPLES::

            sage: P = ProjectiveSpace(3)
            sage: P.betti()
            [1, 1, 1, 1]
        """
        return [self.poincare_polynomial()[i] for i in range(self._dim+1)]

    def GW_invariant(self, d, l):
        """
        Returns the Gromov-Witten invariants for this projective space.

        INPUT: 
            d is the degree
            l is a list of non-negative integers: for example the number 3
            denotes the class h^3.

        OUTPUT:
            The number of degree d curves meeting some general subvarieties in
            this projective space.

        EXAMPLES::

            Computing the number of lines meeting 4 general lines in P^3.

            sage: P = ProjectiveSpace(3)
            sage: P.GW_invariant(1,[2,2,2,2])
            2

            Computing the number of conics meeting 8 general lines in P^3.

            sage: P = ProjectiveSpace(3)
            sage: P.GW_invariant(2,[2]*8)            
            92
        """
        r = self._dim
        l.sort()
        l.reverse()
        n = len(l)
        for i in l:
            if i > r:
                return 0
            pass
        if sum(l) != r*d + r + d + n - 3:
            return 0
        elif n == 0 or n == 1:
            return 0
        elif d == 0:
            if n == 3 and sum(l) == r:
                return 1
            else:
                return 0
        elif n == 2:
            if d == 1 and l == [r,r]:
                return 1
            else:
                return 0
        else:
            if l[-1] == 0:
                return 0
            elif l[-1] == 1:
                l.pop(-1)
                return d*self.GW_invariant(d,l)
            elif r == 2:
                if l == [2]*(3*d-1):
                    return kontsevich(d)
                else:
                    return 0
            else:
                l1 = l[-1] - 1
                l2 = 1
                ll = [l2] + [l[i] for i in range(n-2)] + [l1+l[n-2]]
                res = self.GW_invariant(d,ll)
                S = bipart([l[i] for i in range(n-3)])
                for s in S:
                    A = s[0]
                    nA = len(A)
                    cA = sum(A)
                    B = s[1]
                    for dA in range(1,d+1):
                        dB = d - dA
                        e = r*dA + r + dA + nA - cA - l1 - l[n-2]
                        if e >= 0 and e <= r:
                            a = self.GW_invariant(dA,[l1,l[n-2]]+A+[e])
                            b = self.GW_invariant(dB,[l2,l[n-3]]+B+[r-e])
                            res = res + a*b
                        f = r*dA + r + dA + nA - cA - l1 - l2
                        if f >= 0 and f <= r:
                            x = self.GW_invariant(dA,[l1,l2]+A+[f])
                            y = self.GW_invariant(dB,[l[n-2],l[n-3]]+B+[r-f])
                            res = res - x*y
                return res

    Gromov_Witten_invariant = GW_invariant

    def equivariant_chow_ring(self, dimT, T):
        """
        Returns the equivariant Chow ring of this projective space. 

        Input: 
            dimT : dimension of torus that acts on this projective space.
            T : list of weights of the action on this projective space.

        EXAMPLES::

            sage: P = ProjectiveSpace(4)
            sage: R = P.equivariant_chow_ring(1,[1,1,1,1,1])
            sage: I = R.defining_ideal()
            sage: f = I.gen(0)
            sage: factor(f)
            (h + t)^5
            sage: R = P.equivariant_chow_ring(5,[1,1,1,1,1])
            sage: I = R.defining_ideal()
            sage: f = I.gen(0)
            sage: factor(f)
            (h + p4) * (h + p3) * (h + p2) * (h + p1) * (h + p0)
        """
        if len(T) != self._dim + 1:
            raise ValueError("invalid data")
        elif dimT == self._dim + 1:
            var = self._var + normalize_names(self._dim+1,'p')
            R = PolynomialRing(QQ,var)
            v = R.gens()
            f = prod(v[0]+T[i]*v[i+1] for i in range(len(T)))
            I = R.ideal(f)
        elif dimT == 1:
            var = self._var + normalize_names(1,'p')
            R = PolynomialRing(QQ,var)
            v = R.gens()
            f = prod(v[0]+T[i]*v[1] for i in range(len(T)))
            I = R.ideal(f)
        else:
            raise ValueError("notImplemented")
        return QuotientRing(R,I,v)

    def fixed_points(self):
        """
        Returns a list of fixed points under a torus action on 
        this projective space with weights 0, 1, 2, ..., self._dim.

        EXAMPLES::

            sage: P = ProjectiveSpace(2) 
            sage: P.fixed_points()
            [{0}, {1}, {2}]
        """
        S = Set([i for i in range(self._dim+1)])
        return S.subsets(1).list()

    def equivariant_variable(self, p):
        """
        Returns a list of all Chern classes of equivariant tautological quotient
        bundle at a fixed point of a torus action on this Grassmannian.
        Need this to compute integral using Bott's formula for Grassmannians.
        
        EXAMPLES::
        
            sage: P = ProjectiveSpace(4)
            sage: F = P.fixed_points()
            sage: p = F[0]
            sage: P.equivariant_variable(p)
            [0]     
        """
        return list(p)

    def equivariant_tangent_bundle(self, p):
        """
        """
        h = self.equivariant_variable(p)[0]
        S = Set([i for i in range(self._dim+1)]) - p
        w = Set([h-k for k in S])
        return EquivariantVectorBundle(self,w)

    def bott(self, c):
        """
        Returns the degree of a zero-cycle on this projective space
        using Bott's formula.

        EXAMPLES::

            sage: P = ProjectiveSpace(2)
            sage: h = P.hyperplane()
            sage: P.bott(h^2)
            1
        """
        if c.degree() != self.dim():
            return 0
        r = 0
        for p in self.fixed_points():
            s = self.equivariant_variable(p)
            T = self.equivariant_tangent_bundle(p)
            t = T.euler_class()
            r = r + c(s)/t
        return r

################################################################################
########################### Grassmannians ######################################
################################################################################

class Grassmannian(Variety):
    """
    Makes a Grassmannian as a variety.
    """
    def __init__(self, k, n, var=None):
        self._k = k
        self._n = n
        self._dim = k*(n-k)
        if var is not None:
            pass
        else:
            var = 'q'
        self._degs = [i+1 for i in range(n-k)]
        v = list(normalize_names(n-k+1,var))
        v.pop(0)
        R = PolynomialRing(QQ,v,order=TermOrder('wdegrevlex',self._degs))
        c = R.gens()
        #f = sum(c[i] for i in range(n-k))
        #g = sum((-1)**i*f**i for i in range(n+1))
        self._var = c
        f = 1 + sum(c)
        self._rels = [schur([1]*i,f) for i in range(k+1,n+1)]
        #self._rels = [part(g,i) for i in range(k+1,n+1)]
        self._point = c[-1]**k
        pass

    def _repr_(self):
        """
        Returns a string representation of this Grassmannian.

        EXAMPLES::

            sage: G = Grassmannian(2,5); G
            A Grassmannian of all 2-planes in 5-space
        """
        return "A Grassmannian of all %s-planes in %s-space"%(self._k, self._n)

    def is_grassmannian(self):
        """
        """
        return True

    def dim(self):
        """
        Returns dimension of Grassmannian, where the Grassmannian is considered 
        as a A projective variety by Plucker embedding.
        
        This number should be k(n-k).

        EXAMPLES::

            sage: G = Grassmannian(2,5)
            sage: G.dim()
            6
        """
        return self._dim

    def degree(self):
        """
        Returns degree of Grassmannain, where the Grassmannian is considered as 
        a A projective variety by Plucker embedding.
        
        There is a combinatorial formula to compute the degree of Grassmannian.
        
        The degree of a Grassmannian is also equal to the degree of class
        'self._point'.

        EXAMPLES::

            sage: G = Grassmannian(3,6)
            sage: G.degree()
            42
            sage: G.dim()
            9
            sage: G.integral(G._point)
            42
        """
        s = 1
        t = 1
        for i in range(self._n-self._k):
            s = s*factorial(i)
            t = t*factorial(self._k+i)
        return s*factorial(self._k*(self._n-self._k))/t

    def poincare_polynomial(self, variable_name='t'):
        """
        Returns the Poincare polynomial of this Grassmannian.

        EXAMPLES::

            sage: G = Grassmannian(2,5)
            sage: G.poincare_polynomial()
            t^6 + t^5 + 2*t^4 + 2*t^3 + 2*t^2 + t + 1
        """
        R = PolynomialRing(ZZ, variable_name)
        t = R.gen()
        def f(m):
            g = 1
            for i in range(1,m+1):
                g = g*(1-(t**i))
            return g
        return f(self._n)//(f(self._k)*f(self._n-self._k))

    def betti(self):
        """
        Returns the list of Betti numbers of this Grassmannian.

        EXAMPLES::

            sage: G = Grassmannian(2,5)
            sage: G.betti()
            [1, 1, 2, 2, 2, 1, 1]
        """
        return [self.poincare_polynomial()[i] for i in range(self.dim()+1)]

    def schubert_classes(self):
        """
        Returns the list of all indices of the Schubert classes of
        this Grassmannian.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.schubert_classes()
            [[], [1], [2], [1, 1], [2, 1], [2, 2]]
            sage: len(_)               
            6
            sage: G = Grassmannian(2,5)
            sage: G.schubert_classes()
            [[], [1], [2], [1, 1], [3], [2, 1], [3, 1], [2, 2], [3, 2], [3, 3]]
            sage: len(_)
            10
        """
        result = [[]]
        for k in range(self._dim):
            l = Partitions(k+1).list()
            for e in l:
                if len(e) <= self._k and e[0] <= self._n-self._k:
                    result.append(list(e))
        return result

    def schubert_class(self, p):
        """
        Returns the Schubert classes of this Grassmannian.
        -- p is a list of integers, that is a partition.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.schubert_class([1,1])
            q1^2 - q2
            sage: G = Grassmannian(2,5)
            sage: G.schubert_class([2,1])
            q1*q2 - q3
        """
        f = 1 + sum(self._var)
        return schur(p,f)

    def Littlewood_Richardson_coefficient(self, a, b, c):
        """
        Returns the Littlewood Richardson coefficient corressponds to the
        Schubert class 'c' in the product of two Schubert classes 'a' and 'b'.

        EXAMPLES::

            sage: G = Grassmannian(4,8)
            sage: G.Littlewood_Richardson_coefficient([2,1],[2,1],[4,2])  
            1
            sage: G.Littlewood_Richardson_coefficient([2,1],[2,1],[3,2,1])
            2
        """
        if sum(a)+sum(b) != sum(c):
            return 0
        a = self.schubert_class(a)
        b = self.schubert_class(b)
        d = self.schubert_class(partition_dual(self._k,self._n,c))
        return self.integral(a*b*d)

    def Littlewood_Richardson_rule(self, a, b):
        """
        Returns the result of product of two Schubert classes 'a' and 'b'.

        EXAMPLES::

            sage: G = Grassmannian(4,8)
            sage: G.Littlewood_Richardson_rule([2,1],[2,1])
            [(1, [4, 2]), (1, [4, 1, 1]), (1, [3, 3]), (2, [3, 2, 1]),
            (1, [3, 1, 1, 1]), (1, [2, 2, 2]), (1, [2, 2, 1, 1])]
        """
        l1 = []
        for x in self.schubert_classes():
            if sum(x) == sum(a) + sum(b):
                l1.append(x)
        d = [self.Littlewood_Richardson_coefficient(a,b,c) for c in l1]
        l2 = []
        for x in self.schubert_classes():
            if sum(x) == sum(a) + sum(b):
                l2.append(x)
        return [(d[i],l2[i]) for i in range(len(d))]

    def pieri(self, m, a):
        """
        Input: 
            'm' is an integer, that should be from 0 to n-k and be an index of
            a special Schubert class.
            'a' is a list of integers, that is an index of a Schubert class.
        Output: 
            Returns a list of the indices that satisfying the Pieri's formula.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.pieri(1,[1])  
            [[2], [1, 1]]
            sage: G.pieri(1,[2])
            [[2, 1]]
            sage: G.pieri(1,[1,1])
            [[2, 1]]
            sage: G.pieri(1,[2,1])
            [[2, 2]]
            sage: G.pieri(2,[2])
            [[2, 2]]
        """
        if m < 0 or m > self._n-self._k:
            raise ValueError("the input be wrong")
        elif a not in self.schubert_classes():
            raise ValueError("the input be wrong")
        else:
            return pieri(self._k, self._n, m, a)

    def giambelli(self, a):
        """
        Returns the arbitrary Schubert class in terms of the Chern classes 
        of the tautological quotient bundle on this Grassmannian.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.giambelli([1,1])
            q1^2 - q2
            sage: G.giambelli([2,1])
            q1*q2
        """
        #if a not in self.schubert_classes():
            #raise ValueError("the input be wrong")
        #else:
        return self.schubert_class(a)

    def tautological_subbundle(self):
        """
        Returns the tautological subbundle on this Grassmannian.
        
        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: S = G.tautological_subbundle()
            sage: S.total_chern_class()
            q1^4 - 3*q1^2*q2 + q2^2 - q1^3 + 2*q1*q2 + q1^2 - q2 - q1 + 1
        """
        Q = self.tautological_quotient_bundle()
        f = self._n - Q._chern_character
        return VectorBundle(variety = self, chern_character = f)

    def tautological_quotient_bundle(self):
        """
        Returns the tautological quotient bundle on this Grassmannian.
        
        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: Q = G.tautological_quotient_bundle()    
            sage: Q.total_chern_class()
            q2 + q1 + 1
        """
        f = 1 + sum(self._var)
        return VectorBundle(variety=self, rank=self._n-self._k, chern_class = f)

    def tangent_bundle(self):
        """
        Returns the tangent bundle of this Grassmannian.
        
        EXAMPLES::
        
            sage: G = Grassmannian(2,4)
            sage: T = G.tangent_bundle(); T
            A vector bundle of rank 4 on A Grassmannian
            of all 2-planes in 4-space
            sage: T.total_chern_class()
            8*q1^4 - 16*q1^2*q2 + 6*q2^2 + 8*q1^3 - 4*q1*q2 + 7*q1^2 + 4*q1 + 1
        """
        S = self.tautological_subbundle()
        Q = self.tautological_quotient_bundle()
        return S.dual().tensor(Q)

    def cotangent_bundle(self):
        """
        Returns the cotangent bundle of this Grassmannian.
        
        EXAMPLES::
        
            sage: G = Grassmannian(2,4)
            sage: C = G.cotangent_bundle(); C
            A vector bundle of rank 4 on A Grassmannian
            of all 2-planes in 4-space
            sage: C.total_chern_class()
            8*q1^4 - 16*q1^2*q2 + 6*q2^2 - 8*q1^3 + 4*q1*q2 + 7*q1^2 - 4*q1 + 1
        """
        return self.tangent_bundle().dual()

    def todd_class(self):
        """
        Returns the Todd class of this Grassmannian.
        
        EXAMPLES::
        
            sage: G = Grassmannian(2,4)
            sage: T = G.tangent_bundle()
            sage: T.todd_class()
            q2^2 + 7/3*q1*q2 + 23/12*q1^2 + 2*q1 + 1
            sage: G.todd_class()
            q2^2 + 7/3*q1*q2 + 23/12*q1^2 + 2*q1 + 1
        """
        return self.chow_ring()(self.tangent_bundle().todd_class())

    def fixed_points(self):
        """
        Returns a list of fixed points under action of a torus of dimension 1 on
        this Grassmannian G(k,n) with weights 1, 2, ..., n.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.fixed_points()
            [{1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}]
        """
        S = Set([i for i in range(1,self._n+1)])
        return S.subsets(self._k).list()

    def equivariant_variable(self, p):
        """
        Returns a list of all Chern classes of equivariant tautological quotient
        bundle at a fixed point of a torus action on this Grassmannian.
        Need this to compute integral using Bott's formula for Grassmannians.
        
        EXAMPLES::
        
            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]
            sage: G.equivariant_variable(p)
            [7, 12]
        """
        Q = self.equivariant_quotient_bundle(p)
        return [Q.chern_class(i+1) for i in range(Q.rank())]

    def equivariant_quotient_bundle(self, p):
        """
        Returns a subset of integers {0, 1, 2, ..., n-1}.
        That is the indices of the equivariant tautological quotient bundle at
        point p on this Grassmannian.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]; p
            {1, 2}
            sage: Q = G.equivariant_quotient_bundle(p); Q
            A T-equivariant vector bundle of rank 2 over a point
            sage: Q.rank()
            2
            sage: Q.weights()
            {3, 4}
        """
        w = Set([i for i in range(1,self._n+1)]) - p
        return EquivariantVectorBundle(w)

    def equivariant_subbundle(self, p):
        """
        Returns a subset of integers {0, 1, 2, ..., n-1}, 
        that is the indices of the dual of equivariant tautological subbundle
        at point p on this Grassmannian.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]; p
            {1, 2}
            sage: S = G.equivariant_subbundle(p); S
            A T-equivariant vector bundle of rank 2 over a point
            sage: S.rank()
            2
            sage: S.weights()
            [1, 2]
        """
        return EquivariantVectorBundle(p)

    def equivariant_tangent_bundle(self, p):
        """
        Returns the equivariant tangent bundle at the fixed point p on
        this Grassmannian. The result should be an integer.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]; p
            {1, 2}
            sage: T = G.equivariant_tangent_bundle(p); T
            A T-equivariant vector bundle of rank 4 over a point
            sage: T.rank()
            4
            sage: T.weights()
            [2, 3, 1, 2]
        """
        Q = self.equivariant_quotient_bundle(p)
        S = self.equivariant_subbundle(p)
        return S.dual() & Q

    def bott(self, c):
        """
        Returns the integral by using the Bott's formula.
        This formula allows us compute the degree of zero cycles in terms of the
        fixed pionts under an action of torus on this Grassmannian.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(3)
            sage: G.bott(B.top_chern_class())
            27
            sage: G = Grassmannian(2,5)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(5)       
            sage: G.bott(B.top_chern_class())
            2875
            sage: G = Grassmannian(3,5)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(2)
            sage: P = ProjectiveBundle(B)
            sage: V = P.O(-1) & S.symmetric_power(3)
            sage: A = S.symmetric_power(5) - V
            sage: p = P.projection_morphism()
            sage: G.bott(p.pushforward(A.top_chern_class()))
            609250
        """
        if c.degree() != self.dim():
            return 0
        r = 0
        for p in self.fixed_points():
            s = self.equivariant_variable(p)
            T = self.equivariant_tangent_bundle(p)
            t = T.euler_class()
            r = r + c(s)/t
        return r

################################################################################
################# Equivariant intersection theory ##############################
################################################################################

class EquivariantVectorBundle(SageObject):
    """
    Makes an equivariant vector bundle on a point with the torus action.
    It is given by the weights of the corresponding representation of this torus.
    """
    def __init__(self, weights):
    #def __init__(self, variety, weights):
        #self._variety = variety
        self._weights = list(weights)
        pass

    def _repr_(self):
        """
        Retuens a string representation of this equivariant vector bundle.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]
            sage: Q = G.equivariant_quotient_bundle(p); Q
            A T-equivariant vector bundle of rank 2 over a point
        """
        w = self._weights
        #V = self._variety
        return "A T-equivariant vector bundle of rank %s over a point" %(len(w))

    def weights(self):
        """
        Returns the weights of this equivariant vector bundle.

        EXAMPLES::

            sage: R.<h1,h2,h3,h4> = QQ[]
            sage: w = [h1,h2,h3,h4]
            sage: E = EquivariantVectorBundle(w)
            sage: E.weights()
            [h1, h2, h3, h4]
            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p0 = F[0]; p0
            {1, 2}
            sage: Q = G.equivariant_quotient_bundle(p0)
            sage: Q.weights()
            [3, 4]
            sage: p1 = F[1]; p1
            [1, 3]
            sage: Q = G.equivariant_quotient_bundle(p1)
            sage: Q.weights()
            [2, 4]
        """
        return self._weights

    def rank(self):
        """
        Returns the rank of this equivariant vector bundle. This number is the
        length of weights and equal to the ordinary vector bundle.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]
            sage: Q = G.equivariant_quotient_bundle(p) 
            sage: Q.rank()
            2
        """
        return len(self.weights())

    def dual(self):
        """
        Returns the dual of this equivariant vector bundle.

        EXAMPLES::

            sage: R.<h1,h2,h3,h4> = QQ[]
            sage: w = [h1,h2,h3,h4]
            sage: E = EquivariantVectorBundle(w)
            sage: F = E.dual()
            sage: F.weights()
            [-h1, -h2, -h3, -h4]
            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]
            sage: S = G.equivariant_subbundle(p)       
            sage: B = S.dual()                         
            sage: S.weights()
            [1, 2]
            sage: B.weights()
            [-1, -2]
        """
        #V = self._variety
        w = [-s for s in self.weights()]
        return EquivariantVectorBundle(w)

    def __and__(self, arg):
        """
        Returns the tensor of two equivariant vector bundle.

        EXAMPLES::

            sage: R.<h1,h2,h3,h4> = QQ[]
            sage: w = [h1,h2,h3,h4]
            sage: E = EquivariantVectorBundle(w)
            sage: F = E.dual()
            sage: T = E & F; T
            An equivariant vector bundle of rank 16 over a point
            sage: T.weights()
            [0, h1 - h2, h1 - h3, h1 - h4, -h1 + h2, 0, h2 - h3, h2 - h4, -h1 + h3, -h2 + h3, 0, h3 - h4, -h1 + h4, -h2 + h4, -h3 + h4, 0]
            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]   
            sage: S = G.equivariant_subbundle(p).dual()
            sage: Q = G.equivariant_quotient_bundle(p)
            sage: B = S & Q
            sage: T = G.equivariant_tangent_bundle(p)
            sage: B.weights() == T.weights()
            True
        """
        #V = self._variety
        w = [a + b for a in self.weights() for b in arg.weights()]
        return EquivariantVectorBundle(w)

    def symmetric_power(self, d):
        """
        Returns the d-th symmetric power of this equivariant vector bundle.

        EXAMPLES::

            sage: R.<h1,h2,h3,h4> = QQ[]
            sage: w = [h1,h2,h3,h4]
            sage: E = EquivariantVectorBundle(w)
            sage: B = E.symmetric_power(2)
            sage: B.weights()             
            [2*h1, h1 + h2, h1 + h3, h1 + h4, 2*h2, h2 + h3, h2 + h4, 2*h3, h3 + h4, 2*h4]
            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]
            sage: Q = G.equivariant_quotient_bundle(p)
            sage: B = Q.symmetric_power(3)
            sage: B.weights()
            [9, 10, 11, 12]
        """
        #V = self._variety
        q = self.weights()
        r = self.rank()
        v = IntegerVectors(d,r)
        w = [sum(e[i]*q[i] for i in range(r)) for e in v]
        return EquivariantVectorBundle(w)

    def chern_class(self, k):
        """
        Returns the i-th Chern class of this equivariant vector bundle.
        This is the i-th elementary symmetric function in the weights.

        EXAMPLES::

            sage: R.<h1,h2,h3,h4> = QQ[]
            sage: w = [h1,h2,h3,h4]
            sage: E = EquivariantVectorBundle(w)
            sage: E.chern_class(1)
            h1 + h2 + h3 + h4
            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]
            sage: T = G.equivariant_tangent_bundle(p)
            sage: T.chern_class(0)
            1
            sage: T.chern_class(1)
            8
            sage: T.chern_class(2)
            23
            sage: T.chern_class(3)
            28
            sage: T.chern_class(4)
            12
            sage: T.euler_class() == T.chern_class(T.rank())
            True
        """
        if k == 0:
            return 1
        Sym = SymmetricFunctions(QQ)
        E = Sym.elementary()
        f = E[k].expand(self.rank())
        return f(self.weights())

    def euler_class(self):
        """
        Returns the equivariant Euler class of this equivariant vector bundle.
        This is the top Chern class of this equivariant vector bundle 
        and equal to the product of weights.

        EXAMPLES::

            sage: R.<h1,h2,h3,h4> = QQ[]
            sage: w = [h1,h2,h3,h4]
            sage: E = EquivariantVectorBundle(w)
            sage: E.euler_class()
            h1*h2*h3*h4
            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]
            sage: Q = G.equivariant_quotient_bundle(p)
            sage: B = Q.symmetric_power(3)
            sage: B.weights()
            [9, 10, 11, 12]
            sage: B.euler_class()         
            11880
            sage: B.euler_class() == prod(B.weights())
            True
        """
        return prod(self.weights())        

################################################################################
####################### Vector bundles and Chern classes #######################
################################################################################

class VectorBundle(SageObject):
    """
    Makes a vector bundle on a variety.
    It is given by the rank and the total Chern class or the Chern character.
    The total chern_class and the chern_character should be the polynomials in
    chern variables. They have a closed relation via 'logg' and 'expp'.
    """
    def __init__(self,variety,rank=None,chern_class=None,chern_character=None):
        self._variety = variety
        if rank==None:
            if chern_character==None:
                raise ValueError("Either rank or Chern character should be given")
            else:
                self._chern_character = chern_character
                self._rank = part(chern_character,0)
                self._chern_class = expp(chern_character, variety._dim)
        else:
            self._rank = rank
            if chern_class==None and chern_character==None:
                self._rank = rank
                self._chern_class = 1
                self._chern_character = rank
            elif chern_class==None:
                self._chern_character = chern_character
                self._chern_class = expp(chern_character, variety._dim)
            elif chern_character==None:
                self._chern_class = chern_class
                self._chern_character = rank + logg(chern_class, variety._dim)
            else:
                raise ValueError("The both Chern class and Chern character should not be given")
        pass

    def _repr_(self):
        """
        Returns a string representation of this vector bundle.
        
        EAMPLES::
        
            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1); S
            A vector bundle of rank 2 on A variety of dimension 2
        """
        return "A vector bundle of rank %s on %s" % (self._rank, self._variety)

    def is_VectorBundle(self):
        """
        """
        return True

    def rank(self):
        """
        Returns the rank of this vector bundle.
        
        EXAMPLES::
        
            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: S.rank()
            2
        """
        return self._rank

    def variety(self):
        """
        Returns the abstract variety of this vector bundle.
        
        EXAMPLES::
        
            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: S.variety()
            A variety of dimension 2
        """
        return self._variety

    def total_chern_class(self):
        """
        Returns the total Chern class of this vector bundle.
        
        EXAMPLES::
        
            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: S.total_chern_class()
            c1 + c0 + 1
        """
        return self._chern_class

    def chern_class(self, i):
        """
        Returns the ith Chern class of this vector bundle.
        
        EXAMPLES::
        
            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: S.chern_class(0)
            1
            sage: S.chern_class(1)
            c0
            sage: S.chern_class(2)
            c1
        """
        #R = self.variety().chow_ring()
        #S = self.variety().base_ring()
        f = self._chern_class
        return part(f,i)

    def top_chern_class(self):
        """
        Returns the top Chern class of this vector bundle.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: Q = G.tautological_quotient_bundle()
            sage: B = Q.symmetric_power(3)
            sage: B.top_chern_class()
            18*q1^2*q2 + 9*q2^2
        """
        return self.chern_class(self.rank())

    euler_class = top_chern_class

    def chern_polynomial(self):
        """
        Returns the Chern polynomial of this vector bundle.
        
        EXAMPLES::
        
            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: S.chern_polynomial()
            c1*t^2 + c0*t + 1
        """
        R = self._variety.chow_ring()
        S = PolynomialRing(R,'t')
        t = S.gen()
        return sum(R(part(self._chern_class,i))*t**i for i in range(self._rank+1))

    def chern_character(self):
        """
        Returns the Chern character of this vector bundle.

        EXAMPLES::

            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: S.chern_character()
            1/2*c0^2 - c1 + c0 + 2
        """
        #R = self.variety().chow_ring()
        return self._chern_character

    def adams(self, d):
        """
        Returns the Adams operator of this vector bundle.

        EXAMPLES:

            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: Q = S.adams(3); Q
            A vector bundle of rank 2 on A variety of dimension 2
            sage: Q.total_chern_class()
            9*c1 + 3*c0 + 1
        """
        X = self.variety()
        ch = adams(self._chern_character,d)
        return VectorBundle(X, chern_character=ch)

    def dual(self):
        """
        Returns the dual of this vector bundle.

        EXAMPLES::

            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: Q = S.dual(); Q
            A vector bundle of rank 2 on A variety of dimension 2
            sage: Q.total_chern_class()
            c1 - c0 + 1
        """
        return self.adams(-1)

    def minus(self):
        """
        Returns the negation of this vector bundle.

        EXAMPLES::

            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: Q = S.minus()
            sage: Q.total_chern_class()
            c0^2 - c1 - c0 + 1
            sage: Q.chern_character()
            -1/2*c0^2 + c1 - c0 - 2
        """
        ch = -self._chern_character
        return VectorBundle(self.variety(), chern_character = ch)

    def plus(self, arg):
        """
        Returns the sum of two vector bundles.

        EXAMPLES::

            sage: G = Grassmannian(3,5)
            sage: Q = G.tautological_subbundle()
            sage: B = Q.symmetric_power(2).dual()
            sage: P = ProjectiveBundle(B)
            sage: A = P.OO().tensor(Q.symmetric_power(3)).minus().plus(Q.symmetric_power(5)); A
            A vector bundle of rank 11 on A projective bundle of A vector bundle 
            of rank 6 on A Grassmannian of all 3-planes in 5-space
        """
        ch = self._chern_character+arg._chern_character
        V1 = self.variety()
        V2 = arg.variety()
        if V1 == V2:
            return VectorBundle(V1, chern_character = ch)
        elif len(V1.variables()) > len(V2.variables()):
            return VectorBundle(V1, chern_character = ch)
        else:
            return VectorBundle(V2, chern_character = ch)

    def __add__(self, arg):
        return self.plus(arg)

    def __sub__(self, arg):
        return self.plus(arg.minus())

    def __and__(self, arg):
        return self.tensor(arg)

    def __pow__(self, n):
        return self.exponent(n)
            
    def tensor(self, arg):
        """
        Returns the tensor of two vector bundles.

        EXAMPLES::

            sage: G = Grassmannian(3,5)
            sage: Q = G.tautological_quotient_bundle()
            sage: B = Q.symmetric_power(2).dual()
            sage: P = ProjectiveBundle(B)
            sage: A = P.OO().tensor(Q.symmetric_power(3)).minus().plus(Q.symmetric_power(5)); A
            A vector bundle of rank 11 on A projective bundle of A vector bundle 
            of rank 6 on A Grassmannian of all 3-planes in 5-space
        """
        #X = self._variety
        f = self._chern_character
        g = arg._chern_character
        #if f == 1:
            #return arg
        #elif g == 1:
            #return self
        #else:
            #ch = parts(f*g,0,X._dim)
            #return VectorBundle(X, chern_character = ch)
        V1 = self.variety()
        V2 = arg.variety()
        if V1 == V2:
            return VectorBundle(V1, chern_character = parts(f*g,0,V1._dim))
        elif len(V1.variables()) > len(V2.variables()):
            return VectorBundle(V1, chern_character = parts(f*g,0,V1._dim))
        else:
            return VectorBundle(V2, chern_character = parts(f*g,0,V2._dim))

    def symmetric_power(self,n):
        """
        Returns the n-th symmetric power of this vector bundle.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: Q = G.tautological_quotient_bundle()
            sage: B = Q.symmetric_power(3); B
            A vector bundle of rank 4 on A Grassmannian of all 2-planes in 4-space
            sage: B.top_chern_class()
            18*q1^2*q2 + 9*q2^2
        """
        f = self._chern_character
        X = self._variety
        d = X.dim()
        w = wedges(n,f,d)
        if n == 0:
            return VectorBundle(X, chern_character=1)
        elif n == 1:
            return VectorBundle(X, chern_character=f)
        else:
            s = [1,f]
            for i in range(2,n+1):
                r = min(i, self._rank)
                s.append(sum((-1)**(j+1)*parts(w[j]*s[i-j],0,d) for j in range(1,r+1)))
            return VectorBundle(X, chern_character=s[n])

    def total_segre_class(self):
        """
        Returns the total Segre class of this vector bundle.
        -- s(A)=1/c(A).
        
        EXAMPLES::
            
            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: S.total_segre_class()
            c0^2 - c1 + c0 + 1
        """
        d = self._variety._dim
        R = self._variety.chow_ring()
        f = self._chern_class
        return R(segre(f,d))

    def segre_class(self,i):
        """
        Returns the ith Segre class of this vector bundle.
        
        EXAMPLES::
        
            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: E.segre_class(2)
            c0^2 - c1
            sage: S.segre_class(1)
            c0
        """
        d = self._variety._dim
        #R = self._variety.chow_ring()
        f = self._chern_class
        g = segre(f,d)
        return (-1)**i*part(g,i)

    def segre_polynomial(self):
        """
        Returns the Segre polynomial of this vector bunlde.
        
        EXAMPLES::
        
            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: S.segre_polynomial()
            (c0^2 - c1)*t^2 + c0*t + 1
        """
        d = self._variety._dim
        f = self._chern_class
        g = segre(f,d)
        v = self._variety._var
        w = self._variety._degs
        R = PolynomialRing(QQ,v,order=TermOrder('wdegrevlex',w))
        S = PolynomialRing(R,'t')
        t = S.gen()
        return sum(part(g,i)*t**i for i in range(d+1))

    def todd_class(self):
        """
        Returns the Todd class of the vector bundle.

        EXAMPLES::

            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1); S
            A vector bundle of rank 2 on A variety of dimension 2
            sage: S.todd_class()
            1/12*c1^2 + 1/12*c2 + 1/2*c1 + 1
        """
        if self._chern_class == 1:
            return 1
        d = self.variety().dim()
        R = self.variety().chow_ring()
        f = self._chern_character
        return R(todd(f,d))
    
    def determinant(self):
        """
        Returns the determinant line bundle of this vector bundle.

        EXAMPLES::

            sage: B = Base(2,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: D = S.determinant(); D
            A vector bundle of rank 1 on A variety of dimension 2
            sage: D.total_chern_class()
            c0 + 1
            sage: D.chern_character()
            1/2*c0^2 + c0 + 1
        """
        X = self._variety
        d = X._dim
        c = part(self._chern_class,1)
        ch = sum(c**i/factorial(i) for i in range(d+1))
        return VectorBundle(X, chern_character=ch)

    def porteous(self, arg, k):
        """
        Returns the class of the locus over which a general morphism
        f of two bundles has rank at most k, that is, the locus of vanishing of the
        (k+1)x(k+1) minors of f.

        EXAMPLES::

            sage: B = Base(4,bundles=[[2,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: Q = B.bundle(2)
            sage: S.porteous(Q,1)
            c0^2 - c0*d0 - c1 + d1
        """
        n = self.rank()
        m = arg.rank()
        V = self.minus().plus(arg)
        Vd = self.dual().minus().plus(arg.dual())
        if m <= k:
            return 1
        elif k < 0:
            return 0
        elif n < m:
            f = Vd._chern_character
        else:
            f = V._chern_character
        p = [m-k]*(n-k)
        g = expp(f,(n-k)*(m-k))
        return (-1)**((n-k)*(m-k))*schur(p,g)
        
    def chi(self):
        """
        Returns the Euler-Poincare characteristic of a vector bundle
        using Hirzebruch-Riemann-Roch theorem.

        EXAMPLES::
            
            sage: P = ProjectiveSpace(3)
            sage: h = P.hyperplane()            
            sage: L = P.O(2*h)
            sage: L.chi()
            10
        """
        V = self._variety
        if type(V) == BundleSection or type(V) == Blowup:
            g = todd(V.tangent_bundle()._chern_character, V._dim)
            f = g*self._chern_character
            return V.integral1(f)
        else:
            f = V.tangent_bundle().todd_class()*self.chern_character()
            return V.integral(f)

    def wedge(self, k):
        """
        Returns the k-th exterior power of this vector bundle.

        EXAMPLES::

            sage: B = Base(2,bundles=[[4,'c'],[3,'d']])
            sage: S = B.bundle(1)
            sage: E = S.wedge(3); E
            A vector bundle of rank 4 on A variety of dimension 2
            sage: E.total_chern_class()
            3*c0^2 + c1 + 3*c0 + 1
            sage: E.chern_character()
            3/2*c0^2 - c1 + 3*c0 + 4
        """
        #f = self._chern_character
        #d = self.variety().dim()
        #w = wedges(k,f,d)
        #return VectorBundle(self.variety(),chern_character=w[k])
        r = self.rank()
        if k<0 or k>r:
            ch = 0
        elif k==0:
            ch = 1
        elif k == 1:
            ch = self.chern_character()
        elif 2*k>r:
            return self.determinant().tensor(self.wedge(r-k).dual())
        else:
            f = self._chern_character
            d = self.variety().dim()
            w = wedges(k,f,d)
            ch = w[k]
        return VectorBundle(self.variety(),chern_character=ch)

    def hom(self, arg):
        """
        Returns Hom(self,arg).

        EXAMPLES::

            sage: R.<h> = QQ[] 
            sage: P = ProjectiveSpace(3,'h')
            sage: T = P.tangent_bundle()
            sage: L = P.O(h)
            sage: H = T.hom(L); H
            A vector bundle of rank 3 on A projective space of dimension 3
            sage: H.chern_character()
            -1/6*h^3 - 1/2*h^2 - h + 3
        """
        return self.dual().tensor(arg)

    def end(self):
        """
        Returns End(self).

        EXAMPLES::

            sage: P = ProjectiveSpace(3)
            sage: T = P.tangent_bundle()
            sage: T.end()
            A vector bundle of rank 9 on A projective space of dimension 3
        """
        return self.hom(self)

    def exponent(self, n):
        """
        Returns the n-th exponent of this vector bundle.
        
        EXAMPLES::
        
            sage: P = ProjectiveSpace(3)
            sage: L = P.O(0)
            sage: E = L.exponent(5)
            sage: E.chern_character()
            5
        """
        ch = self.chern_character()
        return VectorBundle(self.variety(),chern_character=n*ch)

################################################################################
######################## Projective bundles ####################################
################################################################################

class ProjectiveBundle(Variety):
    """
    Makes a projective bundle as a variety. 
    This is a Grassmann bundle with k = rank of bundle - 1.
    """
    def __init__(self, bundle, var=None):
        self._bundle = bundle
        self._dim = bundle._rank-1 + bundle._variety._dim
        if var is not None:
            pass
        else:
            var = ('S')
        v = normalize_names(1,var)
        r = bundle._rank
        self._degs = [1] + bundle._variety._degs
        S = PolynomialRing(QQ, v + tuple(bundle._variety._var), order=TermOrder('wdegrevlex',self._degs))
        c = S.gens()
        self._var = c
        f = sum(c[0]**(r-i)*part(S(bundle._chern_class),i) for i in range(r+1))
        self._rels = [f] + bundle._variety._rels
        self._point = c[0]**(r-1)*bundle._variety._point
        pass

    def _repr_(self):
        """
        Returns a string representation of this projective bundle.

        EXAMPLES::

            sage: G = Grassmannian(3,5)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(2)
            sage: P = ProjectiveBundle(B); P
            A projective bundle of A vector bundle of rank 6 on A Grassmannian
            of all 3-planes in 5-space
        """
        return "A projective bundle of %s"%(self._bundle)

    def is_projective_bundle(self):
        """
        Returns True if this is a projective bundle, False if otherwise.

        EXAMPLES::

            sage: G = Grassmannian(3,5)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(2)
            sage: P = ProjectiveBundle(B)
            sage: P.is_projective_bundle()
            True
        """
        return True

    def rank(self):
        """
        Returns the rank of this projective bundle.

        EXAMPLES::

            sage: G = Grassmannian(3,5)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(2)
            sage: P = ProjectiveBundle(B)
            sage: P.rank()
            5
        """
        B = self._bundle
        return B.rank() - 1

    def zeta_class(self):
        """
        Returns the first Chern class of the dual of tautological line bundle
        on this projective bundle.

        EXAMPLES::

            sage: G = Grassmannian(3,5)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(2)
            sage: P = ProjectiveBundle(B)
            sage: P.zeta_class()
            S
        """
        c = self._var
        return c[0]

    def O(self, k):
        """
        Returns the line bundle O(k) on this projective bundle.

        EXAMPLES::

            sage: G = Grassmannian(3,5)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(2)
            sage: P = ProjectiveBundle(B)
            sage: O = P.O(1); O
            A vector bundle of rank 1 on A projective bundle of A vector bundle
            of rank 6 on A Grassmannian of all 3-planes in 5-space
            sage: O.total_chern_class()
            S + 1
        """
        c = self._var
        f = 1 + k*c[0]
        return VectorBundle(variety = self, rank = 1, chern_class = f)

    def projection_morphism(self):
        """
        Returns the projection morphism of this projective bundle.

        EXAMPLES::

            sage: G = Grassmannian(3,5)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(2)
            sage: P = ProjectiveBundle(B)
            sage: p = P.projection_morphism(); p
            A morphism between A projective bundle of A vector bundle of rank 6
            on A Grassmannian of all 3-planes in 5-space and A Grassmannian
            of all 3-planes in 5-space
            sage: p._upperstar
            (q1, q2)
            sage: p.pushforward(P.zeta_class()^6) == B.segre_class(1)
            True
        """
        V = self._bundle._variety
        return Morphism(self, V, V._var)

    def trivial_bundle(self):
        """
        """
        p = self.projection_morphism()
        B = self._bundle
        return p.pullback(B)

    def tautological_line_bundle(self):
        """
        """
        c = self._var
        f = 1 - c[0]
        return VectorBundle(variety = self, rank = 1, chern_class = f)

    def tautological_quotient_bundle(self):
        """
        """
        T = self.trivial_bundle()
        S = self.tautological_line_bundle()
        return T - S

    def tangent_bundle(self):
        """
        """
        S = self.tautological_line_bundle().dual()
        Q = self.tautological_quotient_bundle()
        return S & Q

    def section(self):
        """
        """
        v = self._var
        return v[0]**(self._bundle._rank - 1)

################################################################################
########################### Grassmann bundles ##################################
################################################################################

class GrassmannBundle(Variety):
    """
    Makes a Grassmann bundle as a variety.
    """
    def __init__(self, k, bundle, var=None):
        self._k = k
        self._bundle = bundle
        r = bundle._rank
        self._dim = k*(r-k) + bundle._variety._dim
        if var is not None:
            pass
        else:
            var = ('S')
        v = list(normalize_names(k+1,var[0]))
        v.pop(0)
        self._degs = [i+1 for i in range(k)] + bundle._variety._degs
        S = PolynomialRing(QQ, tuple(v) + tuple(bundle._variety._var), order=TermOrder('wdegrevlex',self._degs))
        c = S.gens()
        f = sum(c[i] for i in range(k))
        g = sum((-1)**i*f**(r-i)*part(S(bundle._chern_class),i) for i in range(r+1))
        self._var = c
        rels = [part(g,i) for i in range(r-k+1,r+1)]
        self._point = c[k-1]**(r-k)*bundle._variety._point
        self._rels = rels + bundle._variety._rels
        pass

    def _repr_(self):
        """
        Returns a string representation of this Grassmann bundle.

        EXAMPLES::

            sage: G = Grassmannian(3,4)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(2)
            sage: GB = GrassmannBundle(1,B); GB
            A Grassmann bundle of rank 1 subbundles of A vector bundle of rank 6
            on A Grassmannian of all 3-planes in 4-space
            sage: GB.chow_ring()
            Quotient of Multivariate Polynomial Ring in S1, q1 over Rational
            Field by the ideal
            (S1^6 - 4*S1^5*q1 + 10*S1^4*q1^2 - 20*S1^3*q1^3, q1^4)
            sage: GB._var
            (S1, q1)
            sage: GB._degs
            [1, 1]
            sage: GB._rels
            [S1^6 - 4*S1^5*q1 + 10*S1^4*q1^2 - 20*S1^3*q1^3, q1^4]
        """
        return "A Grassmann bundle of rank %s subbundles of %s"%(self._k, self._bundle)

    def is_grassmann_bundle(self):
        """
        """
        return True

    def tautological_subbundle(self):
        """
        Returns the tautological subbundle on this Grassmann bundle.
        
        EXAMPLES::

            sage: G = Grassmannian(3,4)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(2)
            sage: GB = GrassmannBundle(1,B)
            sage: S = GB.tautological_subbundle(); S
            A vector bundle of rank 1 on A Grassmann bundle of rank 1 subbundles
            of A vector bundle of rank 6 on A Grassmannian
            of all 3-planes in 4-space
            sage: S._chern_class
            S1 + 1
        """
        v = self._var
        f = 1 + sum(v[i] for i in range(self._k))
        return VectorBundle(variety = self, rank = self._k, chern_class = f)

    def tautological_quotient_bundle(self):
        """
        Returns the tautological quotient bundle on this Grassmann bundle.
        
        EXAMPLES::

            sage: G = Grassmannian(3,4)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(2)
            sage: GB = GrassmannBundle(1,B)
            sage: Q = GB.tautological_quotient_bundle(); Q
            A vector bundle of rank 5 on A Grassmann bundle of rank 1 subbundles
            of A vector bundle of rank 6 on A Grassmannian
            of all 3-planes in 4-space
        """
        R = self.base_ring()
        S = self.tautological_subbundle()._chern_character
        ch = self._bundle._chern_character - S
        return VectorBundle(variety=self, chern_character = ch)

################################################################################
######################## Product variety #######################################
################################################################################

class ProductVariety(Variety):
    """
    Makes a product variety of two varieties.
    """
    def __init__(self, V1, V2):
        self._V1 = V1
        self._V2 = V2
        self._dim = V1._dim + V2._dim
        self._degs = V1._degs + V2._degs
        v = V1._var + V2._var
        R = PolynomialRing(QQ, v, order=TermOrder('wdegrevlex',self._degs))
        self._var = R.gens()
        self._rels = V1._rels + V2._rels #not sure
        self._point = R(V1._point)*R(V2._point)
        pass

    def _repr_(self):
        """
        Returns a string representation of this product variety.

        EXAMPLES::

            sage: P = ProjectiveSpace(3)
            sage: G = Grassmannian(2,5)
            sage: PG = ProductVariety(P,G); PG
            A product variety of A projective space of dimension 3 and
            A Grassmannian of all 2-planes in 5-space
        """
        return "A product variety of %s and %s"%(self._V1,self._V2)

    def is_product_variety(self):
        """
        """
        return True

    def monomial_values(self):
        """
        Returns the top monomial values of this product variety.

        EXAMPLES::

            sage: P = ProjectiveSpace(3)
            sage: G = Grassmannian(2,5)
            sage: PG = ProductVariety(P,G)
            sage: PG.monomial_values()
            {h^3*q1^2*q2^2: 2, h^3*q1^4*q2: 3, h^3*q1^6: 5, h^3*q1^3*q3: 1,
            h^3*q1*q2*q3: 1, h^3*q3^2: 1, h^3*q2^3: 1}
        """
        V1 = self._V1
        V2 = self._V2
        m1 = V1.monomial_values()
        m2 = V2.monomial_values()
        R = PolynomialRing(QQ, self._var, order=TermOrder('wdegrevlex',self._degs))
        keys = [R(m)*R(n) for m in m1.keys() for n in m2.keys()]
        values = [m*n for m in m1.values() for n in m2.values()]
        return dict(zip(keys,values))

    def additive_basis(self):
        """
        Returns the additive basis of this product variety.

        EXAMPLES::

            sage: P = ProjectiveSpace(3)
            sage: G = Grassmannian(2,5)
            sage: PG = ProductVariety(P,G)
            sage: PG.additive_basis()[0]
            {0: [1], 1: [h, q1], 2: [h^2, h*q1, q2, q1^2],
            3: [h^3, h^2*q1, h*q2, h*q1^2, q3, q1*q2],
            4: [h^3*q1, h^2*q2, h^2*q1^2, h*q3, h*q1*q2, -q2^2 + 2*q1*q3, q2^2 - q1*q3],
            5: [h^3*q2, h^3*q1^2, h^2*q3, h^2*q1*q2, -h*q2^2 + 2*h*q1*q3, h*q2^2 - h*q1*q3, q2*q3],
            6: [h^3*q3, h^3*q1*q2, -h^2*q2^2 + 2*h^2*q1*q3, h^2*q2^2 - h^2*q1*q3, h*q2*q3, q3^2],
            7: [-h^3*q2^2 + 2*h^3*q1*q3, h^3*q2^2 - h^3*q1*q3, h^2*q2*q3, h*q3^2],
            8: [h^3*q2*q3, h^2*q3^2], 9: [h^3*q3^2]}
            sage: PG.additive_basis()[1]
            {0: [1], 1: [q1, h], 2: [q2, q1^2, h*q1, h^2],
            3: [-q1*q2 + 2*q3, q1*q2 - q3, h*q2, h*q1^2, h^2*q1, h^3],
            4: [-q2^2 + 2*q1*q3, q2^2 - q1*q3, -h*q1*q2 + 2*h*q3, h*q1*q2 - h*q3, h^2*q2, h^2*q1^2, h^3*q1],
            5: [q2*q3, -h*q2^2 + 2*h*q1*q3, h*q2^2 - h*q1*q3, -h^2*q1*q2 + 2*h^2*q3, h^2*q1*q2 - h^2*q3, h^3*q2, h^3*q1^2],
            6: [q3^2, h*q2*q3, -h^2*q2^2 + 2*h^2*q1*q3, h^2*q2^2 - h^2*q1*q3, -h^3*q1*q2 + 2*h^3*q3, h^3*q1*q2 - h^3*q3],
            7: [h*q3^2, h^2*q2*q3, -h^3*q2^2 + 2*h^3*q1*q3, h^3*q2^2 - h^3*q1*q3],
            8: [h^2*q3^2, h^3*q2*q3], 9: [h^3*q3^2]}
        """
        V1 = self._V1
        V2 = self._V2
        R = self.base_ring()
        b1 = V1.additive_basis()[0]
        db1 = V1.additive_basis()[1]
        b2 = V2.additive_basis()[0]
        db2 = V2.additive_basis()[1]
        basis = {}
        dualbasis = {}
        for d in range(self._dim+1):
            b = []
            db = []
            for i in range(max(0,d-V1._dim),min(d,V2._dim)+1):
                b = b+[R(b1[d-i][j])*R(b2[i][k]) for j in range(len(b1[d-i])) for k in range(len(b2[i]))]
                db = db+[R(db1[V1._dim-d+i][j])*R(db2[V2._dim-i][k]) for j in range(len(db1[V1._dim-d+i])) for k in range(len(db2[V2._dim-i]))]
            basis[d] = b
            dualbasis[self._dim-d] = db
        return basis, dualbasis

    def projection_morphism(self, i):
        """
        Returns the projection morphism from this product variety to
        the i-th variety.
        
        EXAMPLES::
        
            sage: P2 = ProjectiveSpace(2,'h')
            sage: P9 = ProjectiveSpace(9,'H')
            sage: P = ProductVariety(P9,P2)
            sage: p1 = P.projection_morphism(1)
            sage: v = P.variables(); v
            (H, h)
            sage: f = (v[0]+2*v[1])^3; f   
            H^3 + 6*H^2*h + 12*H*h^2 + 8*h^3
            sage: p1.pushforward(f)
            12*H
            sage: P9.integral(p1.pushforward(f))
            12
        """
        if i == 1:
            V = self._V1
        elif i == 2:
            V = self._V2
        else:
            raise ValueError("The number should be 1 or 2")
        #sb = V._var
        return Morphism(self, V, V._var)

    def poincare_polynomial(self):
        """
        Returns the Poincare polynomial of this product variety.
        
        EXAMPLES::
        
            sage: P = ProjectiveSpace(3)
            sage: G = Grassmannian(2,5)
            sage: PG = ProductVariety(P,G)
            sage: PG.poincare_polynomial()
            t^9 + 2*t^8 + 4*t^7 + 6*t^6 + 7*t^5 + 7*t^4 + 6*t^3 + 4*t^2 + 2*t + 1
        """
        return self._V1.poincare_polynomial()*self._V2.poincare_polynomial()
        
    def betti(self):
        """
        Returns the Betti numbers of this product variety.
        
        EXAMPLES::
        
            sage: G = Grassmannian(2,5)
            sage: H = Grassmannian(3,7)
            sage: P = ProductVariety(G,H)
            sage: P.betti()
            [1, 2, 5, 9, 15, 21, 29, 34, 39, 40, 39, 34, 29, 21, 15, 9, 5, 2, 1]
        """
        return [self.poincare_polynomial()[i] for i in range(self._dim+1)]

    def tangent_bundle(self):
        """
        """
        S = self.base_ring()
        V1 = self._V1
        V2 = self._V2
        f = S(V1.tangent_bundle()._chern_character)
        g = S(V2.tangent_bundle()._chern_character)
        return VectorBundle(variety=self,chern_character=f+g)

    def fixed_points(self):
        """
        """
        V1 = self._V1
        V2 = self._V2
        F1 = V1.fixed_points()
        F2 = V2.fixed_points()
        return [(p1,p2) for p1 in F1 for p2 in F2]

    def equivariant_variable(self, p):
        """
        """
        V1 = self._V1
        V2 = self._V2
        return V1.equivariant_variable(p[0])+V2.equivariant_variable(p[1])

    def bott(self, c):
        """
        Returns the degree of zero cycle c on this product variety.

        EXAMPLES::

            sage: P = ProjectiveSpace(19)
            sage: G = Grassmannian(2,4)
            sage: W = ProductVariety(P,G)
            sage: p1 = W.projection_morphism(1)
            sage: p2 = W.projection_morphism(2)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(3)
            sage: h = P.hyperplane()
            sage: L = P.O(h)
            sage: E = p2.pullback(B) & p1.pullback(L)
            sage: W.bott(E.top_chern_class()*h^19)
            27
            sage: sigma1 = G.schubert_class([1])
            sage: W.bott(E.top_chern_class()*h^18*sigma1)
            42
        """
        if c.degree() != self.dim():
            return 0
        V1 = self._V1
        V2 = self._V2
        r = 0
        for p in self.fixed_points():
            v = self.equivariant_variable(p)
            T1 = V1.equivariant_tangent_bundle(p[0])
            T2 = V2.equivariant_tangent_bundle(p[1])
            t = T1.euler_class()*T2.euler_class()
            r = r + c(v)/t
        return r

################################################################################
################################## Morphisms ###################################
################################################################################
 
class Morphism(SageObject):
    """
    Makes a morphism from variety1 to variety2.
    sb - a list of substituations of the form [s1, ..., sn], where n is 
    the number of variables of variety2. The substitions are just
    the pullbacks to "variety1" of the generating classes on "variety2"
    """
    def __init__(self, V1, V2, sb=None):
        self._V1 = V1
        self._V2 = V2
        if sb is None:
            self._upperstar = []
            pass
        else:
            if type(sb) == list or type(sb) == tuple and len(sb) == len(V2._var):
                self._upperstar = sb
            else:
                raise ValueError("invalid third argument")
            pass

    def _repr_(self):
        """
        Returns a string representation of a morphism.

        EXAMPLES::

            sage: P2 = ProjectiveSpace(2)
            sage: h = P2.hyperplane()
            sage: P5 = ProjectiveSpace(5)
            sage: H = P5.hyperplane()
            sage: f = Morphism(P2,P5,[2*h]); f
            A morphism between A projective space of dimension 2
            and A projective space of dimension 5
            sage: P = ProjectiveSpace(2,'h')
            sage: Q = ProjectiveSpace(2,'H')
            sage: H = Q.hyperplane()
            sage: L = Q.O(4*H)
            sage: B = BundleSection(L)
            sage: f = Morphism(B,P,[3*H])
            sage: f.double_point()
            26*H
            sage: B.monomial_values()
            {H: 4}
            sage: B.integral1(f.double_point())
            104
        """
        return "A morphism from %s to %s"%(self._V1, self._V2)

    def is_Morphism(self):
        """
        """
        return True

    def source(self):
        """
        Returns the source of this morphism. That is "variety1".
        
        EXAMPLES::

            sage: P2 = ProjectiveSpace(2,'h')
            sage: h = P2.hyperplane()
            sage: P5 = ProjectiveSpace(5,'H')
            sage: H = P5.hyperplane()
            sage: f = Morphism(P2,P5,[2*h])
            sage: f.source()
            A projective space of dimension 2
            sage: f.source() == P2
            True
        """
        return self._V1

    def target(self):
        """
        Returns the target of this morphism. That is "variety2".
        
        EXAMPLES::

            sage: P2 = ProjectiveSpace(2,'h')
            sage: h = P2.hyperplane()
            sage: P5 = ProjectiveSpace(5,'H')
            sage: H = P5.hyperplane()
            sage: f = Morphism(P2,P5,[2*h])
            sage: f.target()
            A projective space of dimension 5
            sage: f.target() == P5
            True
        """
        return self._V2

    def dim(self):
        """
        Returns the dimension of this morphism.
        
        EXAMPLES::
        
            sage: P2 = ProjectiveSpace(2,'h')
            sage: h = P2.hyperplane()
            sage: P5 = ProjectiveSpace(5,'H')
            sage: H = P5.hyperplane()
            sage: f = Morphism(P2,P5,[2*h])
            sage: f.dim()
            -3
        """
        return self.source()._dim - self.target()._dim
    
    def pullback(self, arg):
        """
        Returns the pullback of this morphism.

        EXAMPLES::

            sage: P2 = ProjectiveSpace(2,'h')
            sage: h = P2.hyperplane()
            sage: P5 = ProjectiveSpace(5,'H')
            sage: H = P5.hyperplane()
            sage: f = Morphism(P2, P5, [2*h])
            sage: f.pullback(5*H)
            10*h
            sage: G = Grassmannian(2,4)
            sage: v = G.variables()
            sage: f = Morphism(P2,G,[h,2*h]) 
            sage: f.pullback(v[0]+v[1])
            3*h
        """
        if type(arg) == VectorBundle:
            if arg._variety == self._V2:
                ch = arg._chern_character(self._upperstar)
                R = self._V1.base_ring()
                return VectorBundle(self._V1,chern_character=R(ch))
            else:
                raise ValueError("invaild VectorBundle")
        elif type(arg) == Integer or type(arg) == int:
            return arg
        else:
            R = self._V1.base_ring()
            return R(arg(tuple(self._upperstar)))

    def pushforward(self, f): 
        """
        Returns the pushforward of this morphism.
        
        EXAMPLES::

            sage: P2 = ProjectiveSpace(2,'h')
            sage: h = P2.hyperplane()
            sage: P5 = ProjectiveSpace(5,'H')
            sage: H = P5.hyperplane()
            sage: f = Morphism(P2, P5, [2*h])
            sage: f.pullback(2*H)
            4*h
            sage: f.pushforward(h)
            2*H^4
            sage: f.pushforward(1)
            4*H^3
        """
        X = self.source()
        Y = self.target()
        m = Y._dim
        n = X._dim
        k = X.codim(f)
        if n - k > m:
            return 0
        else:
            result = 0
            for j in range(len(Y.additive_basis()[1][n - k])):
                g = Y.additive_basis()[1][n-k][j]
                p1 = self.pullback(g)*f
                result = result + X.integral1(p1)*Y.additive_basis()[0][m - n + k][j]
            return result

    def tangent_bundle(self):
        """
        Returns the tangent bundle of this morphism.
        That is a vector bundle on the variety source.
        
        EXAMPLES::
        
            sage: P2 = ProjectiveSpace(2,'h')
            sage: h = P2.hyperplane()
            sage: P5 = ProjectiveSpace(5,'H')
            sage: H = P5.hyperplane()
            sage: f = Morphism(P2, P5, [2*h])
            sage: T = f.tangent_bundle(); T
            A vector bundle of rank 5 on A projective space of dimension 2
            sage: T.total_chern_class()
            60*h^2 + 12*h + 1
        """
        X = self.source()
        Y = self.target()
        g = Y.tangent_bundle()._chern_character
        ch = self.pullback(g)
        return VectorBundle(X, chern_character=ch)

    def normal_bundle(self):
        """
        Returns the normal bundle of this morphism.
        That is a vector bundle on the variety source. 
        
        EXAMPLES::

            sage: P2 = ProjectiveSpace(2,'h')
            sage: h = P2.hyperplane()
            sage: P5 = ProjectiveSpace(5,'H')
            sage: H = P5.hyperplane()
            sage: f = Morphism(P2, P5, [2*h])
            sage: N = f.normal_bundle(); N
            A vector bundle of rank 3 on A projective space of dimension 2
            sage: N.total_chern_class()
            30*h^2 + 9*h + 1
        """
        X = self.source()
        Y = self.target()
        f = X.tangent_bundle()._chern_character
        g = Y.tangent_bundle()._chern_character
        ch = self.pullback(g) - f
        return VectorBundle(X, chern_character = ch)

    def excess_bundle(self, bundle):
        """
        Returns the excess bundle of this morphism associate to another
        vector bundle on the variety target.
        That is a vector bundle on the variety source.
        
        Needs this to compute the excess intersection formula.
        
        EXAMPLES::
        
            sage: P2 = ProjectiveSpace(2,'h')
            sage: h = P2.hyperplane()
            sage: P5 = ProjectiveSpace(5,'H')
            sage: H = P5.hyperplane()
            sage: f = Morphism(P2, P5, [2*h])
            sage: B = VectorBundle(P5,5,chern_class=(1+2*H)^5)
            sage: E = f.excess_bundle(B); E
            A vector bundle of rank 2 on A projective space of dimension 2
            sage: E.total_chern_class()
            31*h^2 + 11*h + 1
        """
        X = self.source()
        g = bundle._chern_character
        A = self.pullback(g)
        B = self.normal_bundle()._chern_character
        return VectorBundle(X, chern_character=A-B)

    def double_point(self):
        """
        Returns the double point class of this morphism.
        
        EXAMPLES::

            sage: C = Curve(2,'p')
            sage: p = C.point()
            sage: P2 = ProjectiveSpace(2,'h')
            sage: h = P2.hyperplane()
            sage: f = Morphism(C,P2,[4*p])
            sage: f.double_point()
            2*p
            sage: P = ProjectiveSpace(2,'h')
            sage: h = P.hyperplane()
            sage: Q = ProjectiveSpace(2,'H')
            sage: H = Q.hyperplane()
            sage: L = Q.O(4)
            sage: B = BundleSection(L)
            sage: f = Morphism(B,P,[3*H])
            sage: f.double_point()
            26*H
        """
        n = -self.dim()
        A = self.pullback(self.pushforward(1))
        N = self.normal_bundle()
        B = part(N._chern_class,n)
        return A - B

    def triple_point(self):
        """
        Returns the triple-point class of this morphism
        """
        n = -self.dim()
        N = self.normal_bundle()
        A = self.pullback(self.pushforward(self.double_point()))-2*part(N._chern_class,n)*self.double_point()
        B = sum(2**(n-i)*part(N._chern_class,i)*part(N._chern_class,2*n-i) for i in range(n))
        return A + B

    def quadruple_point(self):
        """
        Return the quadruple-point class of morphisms have codimension 1
        """
        N = self.normal_bundle()
        A = self.pullback(self.pushforward(self.triple_point())) - 3*part(N._chern_class,1)*self.triple_point()
        B = 6*part(N._chern_class,2)*self.double_point()
        C = 6*(part(N._chern_class,1)*part(N._chern_class,2)+2*part(N._chern_class,3))
        return A + B - C

################################################################################

class Curve(Variety):
    """
    creates a curve C(g,p) by making C as a variety.
    -- g is the genus.
    -- p is the name of the class of a point on the curve.
    """
    def __init__(self, genus, var=None):
        self._genus = genus
        self._dim = 1
        if var is not None:
            pass
        else:
            var = 'p'
        self._degs = [1]
        R = PolynomialRing(QQ, var)
        self._var = R.gens()
        p = R.gen()
        self._rels = [p**2]
        self._point = p
        pass

    def _repr_(self):
        """
        EXAMPLES::

            sage:
        """
        return "A curve of genus %s"% self._genus
    
    def dim(self):
        """
        """
        return self._dim

    def genus(self):
        """
        """
        return self._genus

    def point(self):
        """
        """
        return self._point

    def tangent_bundle(self):
        """
        """
        f = 1 + (2-2*self.genus())*self.point()
        return VectorBundle(self,1,chern_class=f)

################################################################################

class BundleSection(Variety):
    """
    Makes a zero variety of the general section of vector bundle.
    """
    def __init__(self, bundle):
        self._bundle = bundle
        self._dim = bundle._variety._dim - bundle._rank
        self._var = bundle._variety._var
        self._degs = bundle._variety._degs
        pass

    def _repr_(self):
        """
        Returns a string representation of this bundle section.

        EXAMPLES::

            sage: P = ProjectiveSpace(3,'h')
            sage: h = P.hyperplane()
            sage: L = P.O(4*h)
            sage: B = BundleSection(L); B
            A bundle section of A vector bundle of rank 1 on A projective space
            of dimension 3
            sage: B.monomials(2)
            [h^2]
        """
        return "A bundle section of %s" % self._bundle
    
    def monomial_values(self):
        """
        Returns the monomial values of this bundle section.
        
        EXAMPLES::

            sage: P = ProjectiveSpace(3,'h')
            sage: h = P.hyperplane()
            sage: L = P.O(4*h)
            sage: B = BundleSection(L)
            sage: B.monomial_values()
            {h^2: 4}
        """
        S = self._bundle
        f = S.top_chern_class()
        V = S._variety
        M = {}
        for m in self.monomials(self.dim()):
            if V.integral1(m*f) != 0:
                M[m] = V.integral1(m*f)
        return M

    def inclusion(self):
        """
        Returns the inclusion of this bundle section in the ambient variety
        
        EXAMPPLES::

            sage: P = ProjectiveSpace(3,'h')
            sage: h = P.hyperplane()
            sage: L = P.O(4*h)
            sage: B = BundleSection(L)
            sage: i = B.inclusion()
            sage: i.dim()
            -1
            sage: i.pullback(h)
            h
            sage: i.pushforward(1)
            4*h
            sage: i.pushforward(h)
            4*h^2
        """
        V = self._bundle._variety
        sb = list(V._var)
        return Morphism(self, V, sb)

    def tangent_bundle(self):
        """
        Returns the tangent bundle of this bundle section.

        EXAMPLES::  

            sage: P = ProjectiveSpace(3,'h')
            sage: h = P.hyperplane()
            sage: L = P.O(4*h)
            sage: B = BundleSection(L)
            sage: T = B.tangent_bundle()
        """
        i = self.inclusion()
        V = self._bundle._variety
        f = V.tangent_bundle()._chern_character - self._bundle._chern_character
        ch = i.pullback(f)
        return VectorBundle(V, chern_character=ch)

class Blowup(Variety):
    """
    Makes a variety object which is the blowup of the target of a inclusion
    along its source (here E is the exceptional divisor).
    
    What is the Chow ring of a Blowup?
    
    What are its relations?
    """
    def __init__(self, inclusion, var=None):
        self._i = inclusion
        V = inclusion.target()
        if var is not None:
            pass
        else:
            var = 'E'
        self._dim = V._dim
        self._degs = [1] + V._degs
        v = tuple('E') + tuple(V._var)
        R = PolynomialRing(QQ,v,order=TermOrder('wdegrevlex',self._degs))
        self._var = R.gens()
        self._point = V._point
        pass

    def _repr_(self):
        """
        Returns a string representation of this blowup.

        EXAMPLES::

            sage: R.<h,H,E> = QQ[]
            sage: P2 = ProjectiveSpace(2,h)
            sage: P5 = ProjectiveSpace(5,H)
            sage: f = Morphism(P2,P5,[2*h])
            sage: B = Blowup(f, E); B
            The blowup of A projective space of dimension 5 along
            A projective space of dimension 2
        """
        return "The blowup of %s along %s" %(self._i.target(),self._i.source())

    def exceptional_divisor(self):
        """
        """
        return self._var[0]

    def monomial_values(self):
        """
        Returns the monomial values of this blowup.
        
        EXAMPLES::

            sage: P2 = ProjectiveSpace(2,'h')
            sage: h = P2.hyperplane()
            sage: P5 = ProjectiveSpace(5,'H')
            sage: H = P5.hyperplane()
            sage: f = Morphism(P2,P5,[2*h])
            sage: B = Blowup(f)
            sage: B.monomial_values()
            {E^3*H^2: 4, E^2*H^3: 0, E^4*H: 18, E^5: 51, H^5: 1, E*H^4: 0}
        """
        i = self._i
        X = i.source()
        Y = i.target()
        R = PolynomialRing(QQ, self._var)
        v = R.gens()
        d = X.dim()
        D = Y.dim()
        N = i.normal_bundle()
        f = N.dual()._chern_class
        g = sum((1-f)**i for i in range(d+1))
        M = Y.monomial_values()
        for k in range(1,D+1):
            for s in range(len(Y.monomials(D - k))):
                f = part(g,k-D+d)*i.pullback(Y.monomials(D-k)[s])
                M[v[0]**k*Y.monomials(D - k)[s]] = X.integral(f)*(-1)**(D-d+1)
        return M

################################################################################
################# EXAMPLES in Hiep's thesis ####################################
################################################################################

def lines_via_Schubert_calculus(n): #compute the number of lines on a general hypersurface
    d = 2*n-3 #degree of hypersurface
    G = Grassmannian(n-1,n+1)
    S = G.tautological_quotient_bundle()
    B = S.symmetric_power(d)
    return G.integral(B.top_chern_class())

def linear_subspaces_via_Schubert_calculus(k,d,n):
    """
    Compute the number of linear subspaces of dimension k on a general 
    hypersurface of degree d in P^n.
    
    EXAMPLES::

        sage: linear_subspaces_via_Schubert_calculus(2,4,7)
        3297280
        sage: linear_subspaces_via_Schubert_calculus(2,7,14)
        279101475496912988004267637
        sage: linear_subspaces_via_Schubert_calculus(3,3,8)
        321489
    """
    if d < 3:
        raise ValueError("This must be satisfied")
    if binomial(d+k,k) != (k+1)*(n-k):
        raise ValueError("This must be satisfied")
    G = Grassmannian(n-k,n+1)
    Q = G.tautological_quotient_bundle()
    B = Q.symmetric_power(d)
    return G.integral(B.top_chern_class())

def degree_Fano_schemes_via_Schubert_calculus(k,d,n):
    phi = (k+1)*(n-k)-binomial(d+k,d)
    if phi < 0:
        raise ValueError('The Fano scheme be empty')
    G = Grassmannian(n-k,n+1)
    Q = G.tautological_quotient_bundle()
    B = Q.symmetric_power(d)
    q1 = Q.chern_class(1)
    return G.integral(B.top_chern_class()*q1**phi)

def conics_quintic_threefold():
    """
    Compute the number of conics on a general quintic threefold
    """
    G = Grassmannian(3,5)
    S = G.tautological_subbundle().dual()
    B = S.symmetric_power(2)
    P = ProjectiveBundle(B)
    V = P.O(-1) & S.symmetric_power(3)
    A = S.symmetric_power(5) - V
    return P.integral(A.top_chern_class())

def conics_intersecting_8_lines():
    """
    Compute the number of lines intersecting 8 lines in general position
    """
    G = Grassmannian(3,4)
    S = G.tautological_subbundle()
    B = S.symmetric_power(2).dual()
    P = ProjectiveBundle(B)
    v = P.variables()
    c = 2*v[1]+v[0]
    return P.integral(c**8)

#Compute the number of lines on a general cubic hypersurface.

#There are two methods to solve this problem. 

#The first one is using directly the Bott's formula, 
#this means that we compute the symmetric power of the equivariant quotient bundle at each fixed point.
#However, this method is only used for the symmetric power and is impossible in general.

#Method 1:

"""
G = Grassmannian(2,4)
F = G.fixed_points()
result = 0
for p in F:
    Q = G.equivariant_quotient_bundle(p)
    B = Q.symmetric_power(3)
    s = B.euler_class()
    T = G.equivariant_tangent_bundle(p)
    t = T.euler_class()
    result = result + s/t

result
27
"""

#The second one is that we first compute the symmetric power of the tautological quotient bundle, 
#and then we use the Bott's formula for the top Chern class of this vector bundle.
#This method is used in general to implement the Bott's formula for the Grassmannians.

#Method 2:

"""
G = Grassmannian(2,4)
Q = G.tautological_quotient_bundle()
B = Q.symmetric_power(3)
G.bott(B.top_chern_class())
27

#Similarly, compute the number of lines on a general quintic threefold.

G = Grassmannian(3,5)
F = G.fixed_points()
result = 0
for p in F:
    Q = G.equivariant_quotient_bundle(p)
    B = Q.symmetric_power(5)
    s = B.euler_class()
    T = G.equivariant_tangent_bundle(p)
    t = T.euler_class()
    result = result + s/t

result
2875

G = Grassmannian(3,5)
Q = G.tautological_quotient_bundle()
B = Q.symmetric_power(5)
G.bott(B.top_chern_class())
2875
"""

#More generally, compute the number of linear subspaces of dimension k on a
#general hypersurface of degree d in P^n.

#The running time of this method is much faster than to use Schubert calculus.

def linear_subspaces_via_Bott_formula(k,d,n):
    """
    EXAMPLES:

        sage: linear_subspaces_via_Bott_formula(2,4,7)
        3297280
        sage: linear_subspaces_via_Bott_formula(2,7,14)
        279101475496912988004267637
        sage: linear_subspaces_via_Bott_formula(3,3,8)
        321489
    """
    if d < 3:
        raise ValueError("This must be satisfied")
    if binomial(d+k,k) != (k+1)*(n-k):
        raise ValueError("This must be satisfied")
    G = Grassmannian(n-k,n+1)
    F = G.fixed_points()
    result = 0
    for p in F:
        Q = G.equivariant_quotient_bundle(p)
        B = Q.symmetric_power(d)
        s = B.euler_class()
        T = G.equivariant_tangent_bundle(p)
        t = T.euler_class()
        result = result + s/t
    return result

def degree_Fano_schemes_via_Bott_formula(k,d,n):
    phi = (k+1)*(n-k)-binomial(d+k,d)
    if phi < 0:
        raise ValueError('The Fano scheme be empty')
    G = Grassmannian(n-k,n+1)
    F = G.fixed_points()
    result = 0
    for p in F:
        Q = G.equivariant_quotient_bundle(p)
        q1 = Q.chern_class(1)
        B = Q.symmetric_power(d)
        s = B.euler_class()
        T = G.equivariant_tangent_bundle(p)
        t = T.euler_class()
        result = result + (s*q1**phi)/t
    return result

#using Bott's formula to compute the top monomial values of a Grassmannian
#However, this way will take a longer time than using the relations of the Chow ring of a Grassmannian.

"""
G = Grassmannian(3,7)
F = G.fixed_points()
M = G.monomials(G.dim())
d = dict()
for m in M:
    r = 0
    for p in F:
        q = G.equivariant_variable(p)
        T = G.equivariant_tangent_bundle(p)
        t = T.euler_class()
        r = r + m(q) / t
    d[m] = r

d
{q1^9*q3: 84, q1^6*q2^3: 79, q2^2*q4^2: 1, q1^4*q2^2*q4: 6, q1^4*q2*q3^2: 12, q1^3*q2*q3*q4: 3, q1*q3*q4^2: 1, q2^4*q4: 3, q2^6: 16, q1^2*q2^2*q3^2: 7, q1^12: 462, q1^2*q3^2*q4: 2, q4^3: 1, q1*q2*q3^3: 3, q1^10*q2: 252, q1*q2^2*q3*q4: 2, q1^8*q2^2: 140, q1^2*q2^5: 26, q1^6*q2*q4: 9, q1^6*q3^2: 19, q1^8*q4: 14, q1^5*q2^2*q3: 29, q1*q2^4*q3: 10, q1^3*q3^3: 6, q1^3*q2^3*q3: 17, q1^2*q2^3*q4: 4, q2^3*q3^2: 4, q1^4*q4^2: 1, q1^7*q2*q3: 49, q3^4: 1, q1^4*q2^4: 45, q1^2*q2*q4^2: 1, q2*q3^2*q4: 1, q1^5*q3*q4: 4}
"""

#Compute the number of conics on a general quintic threefold.

"""
G = Grassmannian(3,5)
S = G.tautological_subbundle().dual()
B = S.symmetric_power(2)
P = ProjectiveBundle(B)
V = P.O(-1) & S.symmetric_power(3)
A = S.symmetric_power(5) - V
p = P.projection_morphism()
c = p.pushforward(A.top_chern_class())
G.bott(c)
609250
"""

#Compute the number of conics meeting 8 given lines in P^3 in general position.

"""
G = Grassmannian(3,4)
S = G.tautological_subbundle().dual()
B = S.symmetric_power(2)
P = ProjectiveBundle(B)
v = P.variables()
p = P.projection_morphism()
c = p.pushforward((2*v[1]+v[0])^8)
G.bott(c)
92
"""

#Compute the degree of the Fano scheme of lines on a general hypersurface of degree 3 in P^n.
"""
def fanoLine(n):
    G = Grassmannian(2,n+1)
    F = G.fixed_points()
    result = 0
    for p in F:
        Q = G.equivariant_quotient_bundle(p)
        S = G.equivariant_subbundle(p).dual()
        q1 = Q.chern_class(1)
        B = S.symmetric_power(3)
        s = B.euler_class()
        T = G.equivariant_tangent_bundle(p)
        t = T.euler_class()
        result = result + s*q1**(2*n-6)/t
    return result
"""
#More generally, we can compute the degree of Fano scheme of lines on a general hypersurface of degree d in P^n.
"""
def fano(d,n):
    if 2*n-d-3 < 0:
        return 0
    G = Grassmannian(n-1,n+1)
    F = G.fixed_points()
    result = 0
    for p in F:
        Q = G.equivariant_quotient_bundle(p)
        q1 = Q.chern_class(1)
        B = Q.symmetric_power(d)
        s = B.euler_class()
        T = G.equivariant_tangent_bundle(p)
        t = T.euler_class()
        result = result + s*q1**(2*n-d-3)/t
    return result

def degree_grassmannian(k,n):
    G = Grassmannian(k,n)
    return G.degree()
"""
#########################################################################

class VarietyBase(SageObject):
    def __init__(self, ideal):
        self._ideal = ideal
        self._ring = ideal.ring()
        pass

    def ideal(self):
        return self._ideal

    def ring(self):
        return self._ring

    def ngens(self):
        return self._ring.ngens()

class ProjectiveVariety(VarietyBase):
    def __init__(self, ideal):
        VarietyBase.__init__(self,ideal)
        if not ideal.is_homogeneous():
            raise ValueError('The ideal should be homogeneous')
        pass

    def _repr_(self):
        """
        Return a string representation of this projective variety.

        EXAMPLES::

            sage: R.<x,y,z> = QQ[]
            sage: I = R.ideal(x^2 + y^2)
            sage: V = ProjectiveVariety(I); V
            A projective variety defined by Multivariate Polynomial Ring in x, y, z over Rational Field modulo:
            [x^2 + y^2]
            sage: J = R.ideal(x^2 + y)
            sage: W = ProjectiveVariety(J)
            Traceback (most recent call last):
            ...
            ValueError: The ideal should be homogeneous
        """
        return "A projective variety defined by %s modulo: \n%s"%(self._ring,self._ideal.gens())

    def hilbert_polynomial(self):
        """
        Return the hilbert polynomial of this projective variety.

        EXAMPLES::

            sage: R.<x,y,z> = QQ[]
            sage: I = R.ideal(x^2 + y^2)
            sage: V = ProjectiveVariety(I)
            sage: V.hilbert_polynomial()
            2*t + 1
        """
        I = self._ideal
        if I.dimension() == -1:
            return 0
        return self._ideal.hilbert_polynomial()

    def hilbert_series(self, variable_name='t'):
        """
        EXAMPLES::

            sage: R.<x,y,z> = QQ[]
            sage: I = R.ideal(x^2 + y^2)
            sage: V = ProjectiveVariety(I)
            sage: V.hilbert_series()
            1 + t + O(t^2)
        """
        import sage.libs.singular
        hilb = sage.libs.singular.ff.hilb
        P2 = hilb(self.ideal().groebner_basis(),2)
        PS = ZZ[[variable_name]]
        t = PS.gen()
        d = len(P2) - 1
        import sage.rings.big_oh
        # FIXME: work around bug in sage, convert input to list
        HS = PS( list(P2) ) + sage.rings.big_oh.O(t**d)
        return HS

    def hilbert_function(self, n=None):
        """
        EXAMPLES::

            sage: R.<x,y,z> = QQ[]
            sage: I = R.ideal(x^2 + y^2)
            sage: V = ProjectiveVariety(I)
            sage: V.hilbert_function(2)
            5
            sage: V.hilbert_function(1)
            1
            sage: f = V.hilbert_function()
            sage: f(2)
            5
            sage: f(1)
            1
        """
        hpoly = self.hilbert_polynomial()
        hseries = self.hilbert_series()
        dim = hseries.prec()
        if n:
            if n >= dim:
                return hpoly(n)
            else:
                return hseries[n]
        
        def hilbert_func(m):
            if m >= dim:
                return hpoly(m)
            else:
                return hseries[m]
        return hilbert_func
        
    def dimension(self):
        """
        return the dimension of this projective variety. It is the degree of the hilbert polynomial.

        EXAMPLES::

            sage: R.<x,y,z> = QQ[]
            sage: I = R.ideal(x^2 + y^2)
            sage: V = ProjectiveVariety(I)
            sage: V.dim()
            1
        """
        hpoly = self.hilbert_polynomial()
        if hpoly == 0:
            return 0
        return hpoly.degree()

    dim = dimension

    def degree(self):
        """
        Return the degree of this projective variety.

        EXAMPLES::

            sage: R.<x,y,z> = QQ[]
            sage: I = R.ideal(x^2 + y^2)
            sage: V = ProjectiveVariety(I)
            sage: V.degree()
            2
        """
        hpoly = self.hilbert_polynomial()
        if hpoly == 0:
            return 0
        return hpoly.leading_coefficient()*factorial(self.dim())

    def arithmetic_genus(self):
        """
        Return the arithmetic genus of this projective variety. This is the arithmetic genus as defined in Hartshorne.

        EXAMPLES::

            sage: R.<x,y,z> = QQ[]
            sage: I = R.ideal(x^2 + y^2)
            sage: V = ProjectiveVariety(I)
            sage: V.arithmetic_genus()
            0
            sage: K = R.ideal(z*y^2-x*(x+z)*(x-z))
            sage: E = ProjectiveVariety(K); E                                              
            A projective variety defined by Multivariate Polynomial Ring in x, y, z over Rational Field modulo: 
            [-x^3 + y^2*z + x*z^2]
            sage: E.arithmetic_genus()                                                     
            1
        """
        hpoly = self.hilbert_polynomial()
        return (-1)**(self.dim())*(hpoly[0] - 1)

    def intersection(self, arg):
        """
        Return the intersection of two projective varietys.

        EXAMPLES::

            sage: R.<x,y,z,w,t> = QQ[]
            sage: I = R.ideal(x,y)
            sage: J = R.ideal(z,w)
            sage: Y = ProjectiveVariety(I); Y
            A projective variety defined by Multivariate Polynomial Ring in
            x, y, z, w, t over Rational Field modulo: 
            [x, y]
            sage: Z = ProjectiveVariety(J); Z
            A projective variety defined by Multivariate Polynomial Ring in
            x, y, z, w, t over Rational Field modulo: 
            [z, w]
            sage: Y.intersection(Z)
            A projective variety defined by Multivariate Polynomial Ring in
            x, y, z, w, t over Rational Field modulo: 
            [x, y, z, w]
        """
        return ProjectiveVariety(self.ideal() + arg.ideal())

    def affine_chart(self, v):
        """
        Return the affine chart of a projective variety. That is an affine acheme.

        EXAMPLES::

            sage: S.<t,x,y> = QQ[]
            sage: I = S.ideal(t*y - x^2)
            sage: Z = ProjectiveVariety(I); Z
            A projective variety defined by Multivariate Polynomial Ring in
            x, y, t over Rational Field modulo:
            [-x^2 + t*y]
            sage: Z.affine_chart(t)
            An affine variety defined by Multivariate Polynomial Ring in
            x, y over Rational Field modulo: 
            [-x^2 + y]
        """
        ngens = [p.subs({v:1}) for p in self.ideal().gens()]
        L = list(self.ring().gens())
        L.remove(v)
        R = PolynomialRing(self.ring().base_ring(),L)
        return AffineVariety(R.ideal(ngens))

    def geometric_multiplicity(self, arg, point):
        """
        Return the intersection multiplicity of two projective varietys at a point.

        EXAMPLES::
            sage: R.<x,y,t> = QQ[]
            sage: I = R.ideal(x^2 - y*t)
            sage: J = R.ideal(x)
            sage: Y = ProjectiveVariety(I)
            sage: Z = ProjectiveVariety(J)
            sage: point = (0,0,1)
            sage: Y.geometric_multiplicity(Z, point)
            1
            sage: S.<x,y,z,w,t> = QQ[]
            sage: K = S.ideal(x*z,x*w,y*z,y*w)
            sage: L = S.ideal(x - z, y - w)
            sage: Y1 = ProjectiveVariety(K)
            sage: Z1 = ProjectiveVariety(L)
            sage: point1 = (0,0,0,0,1)
            sage: Y1.geometric_multiplicity(Z1, point1)
            3
        """
        R = self.ring()
        i = 0 
        for i in range(R.ngens()):
            if point[i] != 0:
                break
        U = self.affine_chart(R.gen(i))
        V = arg.affine_chart(R.gen(i))
        p = list(point)
        pi = p.pop(i)
        new_point = tuple([1/pi*x for x in p])
        return U.geometric_multiplicity(V, new_point)

    def serre_multiplicity(self, arg, point):
        """
        Return the intersection multiplicity defined by Jean-Pierre Serre.

        EXAMPLES::

            sage: R.<x,y,z,w,t> = QQ[]
            sage: I = R.ideal(x*z, x*w, y*z, y*w)
            sage: J = R.ideal(x - z, y - w)
            sage: Y = ProjectiveVariety(I)
            sage: Z = ProjectiveVariety(J)
            sage: point = (0,0,0,0,1)
            sage: Y.serre_multiplicity(Z, point)
            2
        """
        R = self.ring()
        i = 0 
        for i in range(R.ngens()):
            if point[i] != 0:
                break
        U = self.affine_chart(R.gen(i))
        V = arg.affine_chart(R.gen(i))
        p = list(point)
        pi = p.pop(i)
        new_point = tuple([1/pi*x for x in p])
        return U.serre_multiplicity(V, new_point) 

    def chern_numbers(self):
        """
        Returns a list [deg c_0, ... , deg c_n], where 
        -- c_i = the i-th Chern class of 'self'
        -- deg c_i = its degree, defined as the degree of the pushforward to ambient space
        -- n = the dimension of 'self'

        EXAMPLES::

            sage: R.<x,y,z,w> = QQ[]
            sage: I = R.ideal(x^2-w*y,y^2-x*z,w*z-x*y)
            sage: Y = ProjectiveVariety(I)
            sage: Y.chern_numbers()
            [3, 2]
        """
        I = self.ideal()
        R = self.ring()
        from sage.interfaces.singular import singular
        singular.LIB('elim.lib')
        from sage.combinat.sf.sfa import SFAElementary
        e = SFAElementary(QQ)
        n = self.dim()
        r = R.ngens() - 1
        d = max(I.gens()[i].degree() for i in range(I.ngens()))
        l = [d for i in range(r)]
        D = vector(ZZ,n+1)
        M = matrix(ZZ,n+1,n+1)
        for i in range(n+1):
            G = [random_element(I, l[j]) for j in range(r)]
            N = [l[j] for j in range(r)]
            #Compute Linear_Relation_On_Chern_Numbers({G[0],...,G[r-1]};A[i],D[i])
            T = 1
            for j in range(r):
                T = T*N[j]
            J = R.ideal(G)
            K = R.ideal(singular.sat(J,I)[1])
            #Build vector D = [D_0, ... , D_n]
            D[i] = T - ProjectiveVariety(K).degree()
            #Build the (n+1) x (n+1) matrix M whose i-th row is A
            E = [e[j].expand(r)(N) for j in range(1,n+1)]
            E.insert(0,1)
            A = [sum((-1)**i*binomial(r+i,i)*E[n-k-i] for i in range(n-k+1)) for k in range(n+1)]
            M.set_row(i,A)
            l[i] = l[i] + 1
        return list(M.solve_right(D))

    def chern_numbers_2(self):
        """
        Return a list [deg c_0, ... , deg c_n], where 
        -- c_i = the i-th Chern class of 'self'
        -- deg c_i = its degree, defined as the degree of the pushforward to ambient space
        -- n = the dimension of 'self'

        EXAMPLES::

            sage: R.<x,y,z,w> = QQ[]
            sage: I = R.ideal(x^2-w*y,y^2-x*z,w*z-x*y)
            sage: Y = ProjectiveVariety(I)
            sage: Y.chern_numbers_2()
            [3, 2]
        """
        I = self.ideal()
        R = self.ring()
        from sage.interfaces.singular import singular
        singular.LIB('elim.lib')
        n = self.dim()
        r = R.ngens() - 1
        d = max(I.gens()[i].degree() for i in range(I.ngens()))
        c = []
        for k in range(n+1):
            s = r-n+k
            G = [random_element(I, d) for j in range(s)]
            H = [R.random_element(1,1) for j in range(s,r)]
            J = R.ideal(G+H)
            K = R.ideal(singular.sat(J,I)[1])
            D = ProjectiveVariety(K).degree()
            b = [sum((-1)**j*binomial(r+j,j)*binomial(s,k-i-j)*d**(k-i-j) for j in range(k-i+1)) for i in range(k+1)]
            c.append(d**s-D-sum(b[i]*c[i] for i in range(k)))
        return c

    def segre_numbers(self):
        """
        Return a list [deg s_0, ... , deg s_n], where 
        -- s_i = the i-th Segre class of 'self'
        -- deg s_i = its degree, defined as the degree of the pushforward to ambient space
        -- n = the dimension of 'self'

        EXAMPLES::

            sage: R.<x,y,z,w> = QQ[]
            sage: I = R.ideal(x^2-w*y,y^2-x*z,w*z-x*y)
            sage: Y = ProjectiveVariety(I)
            sage: Y.segre_numbers()
            [3, -10]
        """
        I = self.ideal()
        R = self.ring()
        from sage.interfaces.singular import singular
        singular.LIB('elim.lib')
        r = R.ngens()-1
        n = self.dim()
        d = max(g.degree() for g in I.gens())
        #Pick random elements in I of degree d, as many as the dimension of the ambient space, store in the list G.
        G = [random_element(I,d) for i in range(r)]
        s = []
        for k in range(r-n,r+1):
            J = R.ideal(G[:k])
            K = R.ideal(singular.sat(J,I)[1])
            a = ProjectiveVariety(K).degree()
            p = n - r + k
            degSegreClass = d**k - a - sum(binomial(k,p-i)*d**(p-i)*s[i] for i in range(p))
            s.append(degSegreClass)
        return s

    def chern_numbers_3(self):
        """
        Return a list [deg c_0, ... , deg c_n], where 
        -- c_i = the i-th Chern-Fulton class of 'self' 
        -- deg c_i = its degree, defined as the degree of the pushforward to ambient space
        -- n = the dimension of 'self'
        EXAMPLES::

            sage: R.<x,y,z,w> = QQ[]
            sage: I = R.ideal(x^2-w*y,y^2-x*z,w*z-x*y)
            sage: Y = ProjectiveVariety(I)
            sage: Y.chern_numbers_3()
            [3, 2]
        """
        n = self.dim()
        s = self.segre_numbers()
        c = [sum(binomial(self.ring().ngens(),i-j)*s[j] for j in range(i+1)) for i in range(n+1)]
        return c

    def euler_characteristic(self):
        """
        Return the Euler characteristic of this smooth projective variety.

        EXAMPLES::

            sage: R.<x,y,z,w> = QQ[]
            sage: I = R.ideal(x^2-w*y,y^2-x*z,w*z-x*y)
            sage: Y = ProjectiveVariety(I)
            sage: Y.euler_characteristic()
            2
        """
        return self.chern_numbers_3()[self.dim()]

class AffineVariety(VarietyBase):
    def __init__(self, ideal):
        VarietyBase.__init__(self, ideal)

    def _repr_(self):
        """
        EXAMPLES::

            sage: R.<x,y> = QQ[]
            sage: I = R.ideal(x^2 - y)
            sage: A = AffineVariety(I); A
            An affine variety defined by Multivariate Polynomial Ring in
            x, y over Rational Field modulo:
            [x^2 - y]
        """
        return "An affine variety defined by %s modulo: \n%s"%(self._ring,self._ideal.gens())

    def dimension(self):
        """
        Return the dimension of an affine variety.
        That is the degree of the affine hilbert polynomial of this affine variety.

        EXAMPLES::

            sage: R.<x,y> = QQ[]
            sage: I = R.ideal(x^2 - y)
            sage: A = AffineVariety(I)
            sage: A.dim()
            1
        """
        #affine_hpoly = self.affine_hilbert_polynomial()
        #if affine_hpoly == 0:
        #    return 0
        #return affine_hpoly.degree() 
        return AffineSpace(self.ring()).subscheme(self.ideal()).dimension()

    dim = dimension

    def intersection(self, arg):
        """
        Return the intersection of two affine varietys.

        EXAMPLES::

            sage: S.<x,y,z,w> = QQ[]
            sage: J = S.ideal(x,y)
            sage: K = S.ideal(z,w)
            sage: Y = AffineVariety(J); Y
            An affine variety defined by Multivariate Polynomial Ring in
            x, y, z, w over Rational Field modulo: 
            [x, y]
            sage: Z = AffineVariety(K); Z
            An affine variety defined by Multivariate Polynomial Ring in
            x, y, z, w over Rational Field modulo: 
            [z, w]
            sage: Y.intersection(Z)
            An affine variety defined by Multivariate Polynomial Ring in
            x, y, z, w over Rational Field modulo: 
            [x, y, z, w]
        """
        return AffineVariety(self.ideal() + arg.ideal())

    def degree(self):
        """
        Return the degree of an affine variety. That is the normalized leading
        coefficient of the affine hilbert function of this affine variety.

        EXAMPLES::

            sage: R.<x,y> = QQ[]
            sage: I = R.ideal(x)
            sage: J = R.ideal(y-x^2)
            sage: Y = AffineVariety(I)
            sage: Z = AffineVariety(J)
            sage: W = Y.intersection(Z)
            sage: W.degree()
            1
            sage: Y.degree()
            1
            sage: Z.degree()
            2
        """
        #affine_hpoly = self.affine_hilbert_polynomial()
        #return affine_hpoly.leading_coefficient()*factorial(self.dim())
        hilb = sage.libs.singular.ff.hilb
        g = self.ideal().groebner_basis()
        return sum(hilb(g,2)[:-1])
        
    def affine_hilbert_function(self, n=None):
        """
        Return the value of the affine hilbert function of an affine variety at
        a given integer.

        EXAMPLES::

            sage: R.<x,y> = QQ[]
            sage: I = R.ideal(x^2-y)
            sage: A = AffineVariety(I)
            sage: A.affine_hilbert_function(1)
            1
            sage: A.affine_hilbert_function(2)
            5
            sage: f = A.affine_hilbert_function()
            sage: f(1)
            1
            sage: f(2)
            5    
        """
        Ih = self.ideal().homogenize()
        V = ProjectiveVariety(Ih)
        return V.hilbert_function(n)

        def affine_hilbert_func(m):
            return V.hilbert_function(m)
        return affine_hilbert_func

    def affine_hilbert_polynomial(self):
        """
        EXAMPLES::

            sage: R.<x,y> = QQ[]
            sage: I = R.ideal(x^2 - y)
            sage: A = AffineVariety(I)
            sage: A.affine_hilbert_polynomial()
            2*t + 1
        """
        Ih = self.ideal().homogenize()
        V = ProjectiveVariety(Ih)
        return V.hilbert_polynomial()

    def tangent_cone(self, point):
        """
        Return the tangent cone of the affine variety at a given point.
        That is a projective variety.

        EXAMPLES::

            sage: R.<x,y,z> = QQ[]
            sage: I = R.ideal(y*z+z^2+x^3,y^2+x*z+y^4)
            sage: A = AffineVariety(I)
            sage: p = (0,0,0)
            sage: A.tangent_cone(p)
            A projective variety defined by Multivariate Polynomial Ring in
            x, y, z over Rational Field modulo: 
            [y^2 + x*z, y*z + z^2, x*z^2 + z^3]
        """
        jet = sage.libs.singular.ff.jet
        order = sage.libs.singular.ff.ord
        local_ring, trans = localize_at_point(self.ring(),point)
        I = trans(self.ideal())
        gens = [jet(p, order(p)) for p in I.groebner_basis()]
        In = self.ring().ideal(gens)
        return ProjectiveVariety(In)

    def hilbert_samuel_multiplicity(self, point):
        """
        Return the hilbert-samuel multiplicity of an affine variety at given point.

        EXAMPLES::

            sage: R.<x,y,z> = QQ[]
            sage: I = R.ideal(y*z+z^2+x^3,y^2+x*z+y^4)
            sage: A = AffineVariety(I)
            sage: p = (0,0,0)
            sage: A.hilbert_samuel_multiplicity(p)
            4
            sage: R.<x,y> = QQ[]
            sage: I = R.ideal(x^3,x^2*y,y^3)
            sage: Y = AffineVariety(I)
            sage: p = (0,0)
            sage: Y.hilbert_samuel_multiplicity(p)
            7
        """
        jet = sage.libs.singular.ff.jet
        order = sage.libs.singular.ff.ord
        mult = sage.libs.singular.ff.mult
        local_ring, trans = localize_at_point(self.ring(),point)
        I = trans(self.ideal())
        gens = [jet(p, order(p)) for p in I.groebner_basis()]
        In = local_ring.ideal(gens)
        return mult(In)

    def geometric_multiplicity(self, arg, point):
        """
        EXAMPLES::

            sage: R.<x,y> = QQ[]
            sage: I = R.ideal(x^2 - y)
            sage: J = R.ideal(x - 1)
            sage: point = (1,1)
            sage: Y = AffineVariety(I)
            sage: Z = AffineVariety(J)
            sage: Y.geometric_multiplicity(Z, point)
            1
            sage: K = R.ideal(2*x - y - 1)
            sage: W = AffineVariety(K)
            sage: Y.geometric_multiplicity(W, point)
            2
            sage: R.<x,y,z,w> = QQ[]
            sage: I = R.ideal(x*z,x*w,y*z,y*w)
            sage: J = R.ideal(x-z,y-w)
            sage: Y = AffineVariety(I)
            sage: Z = AffineVariety(J)
            sage: point = (0,0,0,0)
            sage: Y.geometric_multiplicity(Z,point)
            3
        """        
        local_ring1, trans1 = localize_at_point(self.ring(),point)
        local_ideal1 = trans1(self.ideal())
        local_ring2, trans2 = localize_at_point(arg.ring(),point)
        local_ideal2 = trans2(arg.ideal())
        return AffineVariety(local_ideal1 + local_ideal2).degree()

    def serre_multiplicity(self, arg, point):
        """
        EXAMPLES::

            sage: R.<x,y,z,w> = QQ[]
            sage: I = R.ideal(x*z,x*w,y*z,y*w)
            sage: J = R.ideal(x-z,y-w)
            sage: Y = AffineVariety(I)
            sage: Z = AffineVariety(J)
            sage: p = (0,0,0,0)
            sage: Y.serre_multiplicity(Z,p)
            2
        """
        local_ring, trans = localize_at_point(self.ring(),point)
        I = trans(self.ideal())
        J = trans(arg.ideal())
        from sage.interfaces.singular import singular
        singular.LIB('homolog.lib')
        i = 0
        s = 0
        t = sum(singular.Tor(i, I, J).std().hilb(2).sage())
        while t != 0:
            s = s + ((-1)**i)*t
            i = i + 1
            t = sum(singular.Tor(i, I, J).std().hilb(2).sage())
        return s

def random_element(ideal, degree):
    """
    Pick random an element of 'degree' in 'ideal'.
    """
    R = ideal.ring()
    singular.LIB('random.lib')
    singular.setring(singular(R))
    return sum(g*singular.sparsepoly(degree-g.degree()) for g in ideal.gens())

def localize_at_point(ring, point):
    """
    EXAMPLES:
        sage: R.<x,y,z,w> = QQ[]
        sage: p = (0,0,0,1)
        sage: localize_at_point(R,p)
        (Multivariate Polynomial Ring in x, y, z, w over Rational Field, Ring morphism:
        From: Multivariate Polynomial Ring in x, y, z, w over Rational Field
        To:   Multivariate Polynomial Ring in x, y, z, w over Rational Field
        Defn:   x |--> x
                y |--> y
                z |--> z
                w |--> 1 + w)
    """
    local_ring = PolynomialRing(ring.base_ring(), ring.variable_names(), order = 'ds')
    new_coordinate = [local_ring.gens()[i] + point[i] for i in range(local_ring.ngens())]
    trans = ring.hom(new_coordinate)
    return local_ring, trans

################################################################################
################## Schubert calculus on a Grassmann Algebra ####################
################################################################################

def sign(I):
    """
    It is defined as the sign of an arbitrary permuatation.
    EXAMPLES::
    
        sage: I = [2,4,3]
        sage: sign(I)    
        -1
    """
    s = 0
    for i in range(len(I)-1):
        for j in range(i+1,len(I)):
            if I[i]-I[j] > 0:
                s = s+1
    return (-1)**s

def p(k,m): 
    """
    Writes m as a sum of k non-negative integers not bigger than 
    m, and returns the corresponding multinomial coefficients. 
    EXAMPLES::
    
        sage: p(2,4)
        [[1, 4, 6, 4, 1], [(4, 0), (3, 1), (2, 2), (1, 3), (0, 4)]]
    """
    v = normalize_names(k,'x')
    R = PolynomialRing(QQ,v)
    c = R.gens()
    S = sum(c)**m
    C = S.coefficients()
    M = S.monomials()
    D = [M[i].degrees() for i in range(len(M))]
    return [C,D]
    
def r(k,n):
    """
    """
    if k > n:
        return 0
    else:
        return k

def reduce_zero(I):
    """
    EXAMPLES::
    
        sage: I = [1,3,0]; reduce_zero(I) 
        []
    """
    if prod(I[i] for i in range(len(I))) == 0:
        return []
    else:
        return I
        
def reduce_equal(I): 
    """
    EXAMPLES::
        
        sage: I = [1,3,3]; reduce_equal(I)
        sage: []
    """
    P = 1
    for i in range(len(I)):
        for j in range(i+1,len(I)):
            P = P*(I[j]-I[i])
    if P == 0:
        return []
    else:
        return I
                
def reduce(I):
    """
    EXAMPLES::
    
        sage: I = [(2,[1,2]),(1,[2,1]),(3,[1,0]),(4,[2,2])]
        sage: reduce(I)
        [(1, [1, 2])]
    """
    A = list()
    for i in range(len(I)):
        if len(reduce_zero(reduce_equal(I[i][1])))!= 0:
            A.append(I[i])
    B = list()
    for i in range(len(A)):
        a = sign(A[i][1])
        A[i][1].sort()
        B.append((A[i][0]*a, A[i][1]))
    result = list()
    allval=list()
    for t in B:
        if t[1] not in allval:
            allval.append(t[1])
    for val in allval:
        count = 0
        for t in B:
            if t[1] == val:
                count = count + t[0]
        result.append((count,val))
    return result
    
def Pieri_condition(I,J):
    """
    The condition in Pieri's formula.
    EXAMPLES::
    
        sage:
    """
    result = list()
    n = 0
    while n <= len(I)-2:
        if J[n] >= I[n+1]-I[n]:
            return []
        else:
            n = n + 1
    result.append(J)
    return result

def D(h,m,I,n):
    """
    EXAMPLES::
    
        sage: D(2,1,[2,3,5],8) # Pieri's formula
        [(1, [2, 4, 6]), (1, [2, 3, 7])]
        sage: D(2,1,[2,3,5],6)
        [(1, [2, 4, 6])]
        sage: D(1,4,[1,2],4) # Newton binomial formula
        [(2, [3, 4])]
        sage: D(1,2,[1,2,3],5)
        [(1, [1, 3, 4]), (1, [1, 2, 5])]
        sage: D(1,5,[1,3,6],6)
        [(5, [4, 5, 6])]
        sage: D(2,2,[1,2],4) # Corollary 2.3.10
        [(1, [3, 4])]
        sage: D(2,4,[1,2,3,4],6) 
        [(1, [3, 4, 5, 6])]
    """
    if len(reduce_zero(reduce_equal(I))) == 0:
        return [(1,[0])]
    elif m == 0 or h == 0:
        return [(1,I)]
    elif m == 1: 
        if len(I) == 1:
            return [(1,[r(I[0]+h,n)])]
        else: # Pieri's formula
            A = p(len(I),h)[1]
            result = list()
            B = []
            for i in range(len(A)):
                if len(Pieri_condition(I,A[i])) > 0:
                    L=[r(I[k]+A[i][k],n) for k in range(len(I))]
                    result.append((1,L))
            return reduce(result)
    elif h == 1:
        if len(I) == 1:
            return D(m,1,I,n)
        elif len(I) == 2: # Newton binomial formula
            result = list()
            for i in range(m + 1):
                L = [r(i+I[0],n),r(m-i+I[1],n)]
                result.append((binomial(m,i),L))
            return reduce(result)
        else: # Newton binomial formula's generalization
            result = list()
            P = p(len(I),m)
            for i in range(len(P[0])):
                L=[r(P[1][i][j]+I[j],n) for j in range(len(I))]
                result.append((P[0][i],L))
            return reduce(result)
    elif len(I) == 1:
        return [(1, [r(I[0]+m*h,n)])]
    elif len(I) == 2: # Corollary 2.3.10(1) 
        result = list()
        for i in range(m+1):
            A =list()
            B = D(h-1,i,[r(I[0]+i,n), r(I[1]+h*(m-i),n)],n)
            for j in range(len(B)):
                A.append((binomial(m,i)*B[j][0], B[j][1]))
            for k in range(len(A)):
                result.append(A[k])
        return reduce(result)
    else: # Corollary 2.3.10(2)
        result = list()
        for i in range(m+1):
            a = I[0]
            J = [I[j] for j in range(1,len(I))]
            K = []
            for d in range(len(D(h,m-i,J,n))):
                C = D(h,m-i,J,n)[d][0]
                V = [r(a+i,n)]+D(h,m-i,J,n)[d][1]
                K.append((C,V))
            re = list()
            for k in range(len(K)):
                L = D(h-1,i,K[k][1],n)
                for s in range(len(L)):
                    re.append((K[k][0]*L[s][0],L[s][1]))
            for t in range(len(re)):
                result.append((binomial(m,i)*re[t][0],re[t][1]))
        return reduce(result)
        
       

def degree_grassmann(k,n):
    """
    EXAMPLES::
    
        sage: degree_grassmann(2,4)
        2
        sage: degree_grassmann(3,10)
        1385670
    """
    I = [i for i in range(1,k+1)]
    return D(1,k*(n-k),I,n)[0][0]
    
def flexes_rationalCurves(n): 
    """
    Computes the number of space rational curves 
    having "hyperstalls" at prescribed 2n distinct points.
    EXAMPLES::
    
        sage: D(2,4,[1,2,3,4],6) 
        [(1, [3, 4, 5, 6])]
        sage: D(2,6,[1,2,3,4],7)
        [(5, [4, 5, 6, 7])]
        sage: D(2,8,[1,2,3,4],8)
        [(126, [5, 6, 7, 8])]
        sage: D(2,10,[1,2,3,4],9)
        [(3396, [6, 7, 8, 9])]
        sage: D(2,12,[1,2,3,4],10)
        [(114675, [7, 8, 9, 10])]
        sage: D(2,14,[1,2,3,4],11)
        [(4430712, [8, 9, 10, 11])]
        sage: D(2,16,[1,2,3,4],12)
        [(190720530, [9, 10, 11, 12])]
        sage: D(2,18,[1,2,3,4],13)
        [(8942188632, [10, 11, 12, 13])]
        sage: D(2,20,[1,2,3,4],14)
        [(449551230102, [11, 12, 13, 14])]
        sage: D(2,22,[1,2,3,4],15)
        [(23948593282950, [12, 13, 14, 15])]
        sage: D(2,24,[1,2,3,4],16)
        [(1339757254689348, [13, 14, 15, 16])]
        sage: D(2,26,[1,2,3,4],17)
        [(78153481093195800, [14, 15, 16, 17])]
        sage: D(2,28,[1,2,3,4],18)
        [(4727142898098368085, [15, 16, 17, 18])]
    """
    return D(2,2*n,[1,2,3,4],n+4)[0][0]
    
    
def intersection_number(a,b,n):
    """
    Computes the top intersection numbers in G(2,n+2).
    EXAMPLES::
    
        sage: intersection_number(0,2,2)  
        1
        sage: intersection_number(14,1,8)
        1001
        sage: intersection_number(8,4,8) 
        352
    """
    K = D(2,b,[1,2],n+3)
    result = list()
    for i in range(len(K)):
        L = D(1,a,K[i][1],n+3)
        for j in range(len(L)):
            result.append((L[j][0]*K[i][0], L[j][1]))
    for k in range(len(reduce(result))):
        if reduce(result)[k][1] == [n+1,n+2]:
            return reduce(result)[k][0]

################################################################################
############### Chern and Hilbert polynomials ##################################
################################################################################

R = PolynomialRing(ZZ,'t')
t = R.gen()

def poly_base(i):
    """
    Returns the Hilbert polynomial "P_i = binomial(t+i,i)" 
    of S_j=k[x_0, ..., x_d]/(x_0, ..., x_{d-1-j})
    EXAMPLES::
        
        sage: poly_base(2)
        1/2*t^2 + 3/2*t + 1
        sage: poly_base(3)
        1/6*t^3 + t^2 + 11/6*t + 1
    """
    return prod((t+k) for k in range (1,i+1))/factorial(i)

def chern_base(j,d):
    """
    Returns the Chern polynomial of the coherent sheaf 
    associated to S_j in P^d.
    EXAMPLES::
        
        sage: chern_base(0,3)
        2*t^3 + 1
        sage: chern_base(1,3)
        -2*t^3 - t^2 + 1
    """
    g = h = 1
    for i in range(d+1):
        if i % 2 == 0:
            g = g*taylor((1-i*t)**binomial(d-j,i),t,0,d)
        else:
            h = h*taylor((1-i*t)**binomial(d-j,i),t,0,d)
    return taylor(g/h,t,0,d)
    
def coeffs(f):
    """
    Returns the cofficients of the representation of f 
    via the polynomials P_i.
    EXAMPLS::
            
        sage: R.<t> = QQ[]
        sage: f = 2 + 4*t
        sage: coeffs(f)
        [-2, 4] 
        """
    if f == 0:
        return []
    dim = f.degree()
    deg = f.leading_coefficient()*factorial(dim)
    a = [0]*(dim+1)
    a[dim] = deg      
    f = f-deg*poly_base(dim)
    while f != 0:
        dim = f.degree()
        deg = f.leading_coefficient()*factorial(dim)
        a[dim] = deg
        f = f-deg*poly_base(dim)
    return a
        
def chern(f,d):
    """
    An Grothendieck element on P^d is characterized by 
    its Hilbert polynomial. Returns its Chern polynomial 
	by using the Chern polynomial of S_j.
    EXAMPLES::
            
        sage: R.<t> = QQ[]
        sage: f = 1 + 3*t
        sage: chern(f,3)
        -10*t^3 - 3*t^2 + 1
    """
    a = coeffs(f)
    C = prod(chern_base(i,d)**a[i] for i in range(len(a)))
    return taylor(C,t,0,d)
        
def coeffs1(f,d):
    """
    Returns the cofficients of the representation 
    of f via the Hilbert polynomials of 
	twisted structure sheaves o(-i), i = 0, ..., d.
    EXAMPLES::
            
        sage: R.<t> = QQ[]
        sage: f = 2 + 4*t
        sage: coeffs1(f,3)
        [2, -2, -2, 2]
    """
    a = coeffs(f)
    for i in range(d-len(a)+1):
        a.append(0)     
    b = []
    for j in range(d+1):
        s = sum((-1)**j*a[k]*binomial(d-k,j) for k in range(d-j+1))
        b.append(s)       
    return b
        
def chern1(f, d):
    """
    An Grothendieck element on P^d characterized 
    by its Hilbert polynomial. Returns its 
    Chern polynomial by using the Chern polynomial 
    of twisted structure sheaves o(-i), i = 0, ..., d.       
    EXAMPLES::
        
        sage: R.<t> = QQ[]
        sage: f = 2 + 4*t
        sage: chern1(f,3)
        -12*t^3 - 4*t^2 + 1
        sage: f = 1 + 3*t
        sage: chern1(f,3)
        -10*t^3 - 3*t^2 + 1
    """
    b = coeffs1(f,d)
    C = prod(taylor((1-i*t)**b[i],t,0,d) for i in range(d+1))       
    return taylor(C,t,0,d)
        
def rank(f,d):
    """
    Returns the rank of the coherent sheaf
    characterized by its Hilbert polynomial.
    EXAMPLES::
        
        sage: f = 1/3*t^3 + 2*t^2 + 23/3*t + 4
        sage: rank(f,3)                       
        2
    """
    return sum(coeffs1(f,d))


def ch(C,r,d):
    """
    Given a Grothendieck element of rank r on P^d 
    characterized by its Chern polynomial C, 
    returns its Chern character.
    EXAMPLES::
        
        sage: R.<t> = QQ[]
        sage: f = 1 - t + 4*t^2 
        sage: ch(f,2,4)   
        17/24*t^4 + 11/6*t^3 - 7/2*t^2 - t + 2
    """
    m = C.degree()
    a = C.coeffs()
    for i in range(d-m):
        a.append(0)
    p = [r, a[1]]
    for n in range(2,d+1):
        s1 = sum((-1)**(i+1)*a[i]*p[n-i] for i in range(1,n))
        s2 = (-1)**(n+1)*n*a[n] + s1 
        p.append(s2)
    return sum(p[i]/factorial(i)*t**i for i in range(d+1))  
        
def hilbert(C,r,d):
    """
	Given a Grothendieck element of rank r on P^d 
	characterized by its Chern polynomial, 
	returns its Hilbert polynomial.
    EXAMPLES::

        sage: R.<t> = QQ[]
        sage: C = 1 - t + 4*t^2
		sage: hilbert(C,2,4)
		1/12*t^4 + 2/3*t^3 - 1/12*t^2 - 17/3*t - 5
    """
    s = sum((-1)**n/factorial(n+1)*t**n for n in range(d+1))**(-1)
    h = taylor(s,t,0,d)
    f = taylor(h**(d+1),t,0,d)
    a = [f.coeffs()[i][0] for i in range(len(f.coeffs()))] 
    b = ch(C,r,d).coeffs()
    p = []
    for k in range(d+1):
        p.append(sum(a[i]*b[k-i] for i in range(k+1))/factorial(d-k))
    return sum(p[i]*t**(d-i) for i in range(d+1))
    
################################################################################
#################################### CSM classes ###############################
################################################################################

S = PolynomialRing(QQ,'h')
h = S.gen()

def next(F,n):
    """
    Need for the next function.
    EXAMPLES::
    
        sage:
    """
    res = list()
    t = len(F[0])+1
    A = list()
    for i in range(t,n+1):
        for j in range(len(F)):
            if len(F[j]) == 0:
                A = [i]
                res.append(F[j]+A)
            else:
                if F[j][len(F[j])-1] < i:
                    A = [i]
                    res.append(F[j]+A)
                else:
                    pass
    return res
    
def sub(d,n):
    """
    Lists all d numbers of the first n natural numbers with order.
    Need for the computation of CSM classes.
    EXAMPLES::
    
        sage: sub(2,3)
	    [[1, 2], [1, 3], [2, 3]]
    """ 
    res = [[]]
    for i in range(d):
        res = next(res,n)
    return res
    
def shadow(I):
    """
    Returns the shadow of the graph Gamma_I.
    EXAMPLES::
    
        sage: R.<x,y,z,w> = QQ[]
        sage: I = R.ideal(x*y,x*z,y*z)
        sage: shadow(I)
        [1, 2, 1, 0]
    """
    R = I.ring()
    n = R.ngens()-1
    v = R.gens()
    N = I.ngens()
    if I == R.ideal(0):
        return [0]*(n+1)
    R1 = PolynomialRing(QQ,normalize_names(N,'t'))
    R2 = PolynomialRing(QQ,normalize_names(N,'t') + v)
    li = [R2.gens()[i] for i in range(N)]
    R3 = PolynomialRing(QQ,normalize_names(1,'u')+normalize_names(N,'t')+v)
    J = R3.ideal()
    for i in range(N):
        J = J + R3.ideal(R1.gens()[i]-R3.gens()[0]*I.gens()[i])
    L = [1]   
    H = [0]*(n+1)
    l = [0]*(n+1)
    LL = [0]*(n+1)
    LLL = [0]*(n+1)
    H[0] = R2.ideal(J.elimination_ideal([R3.gens()[0]]))
    for i in range(1,n+1):
        while True:
            f = R1.random_element(1, N)
            l[i] = f - f.constant_coefficient()
            LL[i] = R2.ideal(l[i])
            if H[i-1].quotient(LL[i]).intersection(H[i-1])==H[i-1].quotient(LL[i]):
		        break 
        maxi = R2.ideal(R1.ideal(R1.gens()))
        singular.LIB('elim.lib')
        H[i] = R2.ideal(singular.sat(H[i-1] + LL[i],maxi)[1])
        LLL[i] = H[i].elimination_ideal(li)
        L.append(singular.mult(LLL[i]))
    return L
        
def segre2(I):
    """
    Returns the segre class of projective scheme defined by I.
    EXAMPLES::
    
        sage: R.<x,y,z,w> = QQ[]
	    sage: I = R.ideal(x*y,x*z,y*z)
	    sage: segre(I)
	    -10*h^3 + 3*h^2
    """
    R = I.ring()
    n = R.ngens()-1
    m = I.gens()[0].degree()
    L = shadow(I)
    f = g = 0
    for i in range(n+1):
        f = f + L[i]*h**i*(1+m*h)**(n-i)
        g = g + binomial(n+i,i)*(-m*h)**i
    return (1 - f*g).sage().truncate(n+1)
    
def fulton(I):
    """
    Returns the Chern-Fulton class of projective scheme defined by I.
    EXAMPLES::
    
        sage: R.<x,y,z,w> = QQ[]
	    sage: I = R.ideal(x*y,x*z,y*z)
	    sage: fulton(I)
	    2*h^3 + 3*h^2
    """
    R = I.ring()
    n = R.ngens()-1
    return ((1+h)**(n+1)*segre2(I)).truncate(n+1)
    
def csm(I):
    """
    Returns the Chern-Schwarzt-MacPherson class of 
    a hypersurface defined by I.
    EXAMPLES::
    
        sage: R.<x,y,z,w,t> = QQ[]    
	    sage: I = R.ideal(x^5+y^5+z^5+w^5+t^5)
	    sage: csm(I)
	    -200*h^4 + 50*h^3 + 5*h

    """
    R = I.ring()
    n = R.ngens()-1     
    J = I.gens()[0].jacobian_ideal()
    L = shadow(J)
    f = (1 + h)**(n+1)
    g = sum(L[i]*(-h)**i*(1+h)**(n-i) for i in range(n+1))
    return (f-g).sage().truncate(n+1)
    
def CSM(I):
    """
    Returns the Chern-Schwarzt-MacPherson class of 
    projective scheme defined by I.
    EXAMPLES::
    
        sage: R.<x,y,z,w> = QQ[]
	    sage: I = R.ideal(x*y,x*z,y*z)
	    sage: CSM(I)   
	    4*h^3 + 3*h^2
    """
    R = I.ring()
    n = R.ngens()-1
    r = I.ngens()
    if r <= 1:
        return csm(I)
    else:
        res = 0
        for d in range(1,r+1):
            L = sub(d,r)
            C = 0
            for i in range(len(L)):
                f = 1
                for j in range(len(L[i])):
                    f = f*I.gens()[L[i][j]-1]
                C = C + csm(R.ideal(f))
            res = res + (-1)**(d+1)*C
        return res
        
def CSMC(I):
    """
    Return the Chern-Schwarzt-MacPherson class of the 
    complement of projective scheme defined by I.
    EXAMPLES::
    
	    sage: R.<x,y,z,w> = QQ[]
	    sage: I = R.ideal(x*y,x*z,y*z)
	    sage: CSMC(I)
	    3*h^2 + 4*h + 1
    """
    R = I.ring()
    n = R.ngens()-1
    return (1+h)**(n+1)-h**(n+1) - CSM(I)
    
def milnor(I):
    """
    Returns the milnor class of projective scheme defined by I.
    EXAMPLES::
    
	    sage: R.<x,y,z,w> = QQ[]      
	    sage: I = R.ideal(x*y,x*z,y*z)
	    sage: milnor(I)               
	    2*h^3
    """
    return CSM(I) - fulton(I)

################################################################################
###################### Toric intersection theory ###############################
################################################################################

class ToricVariety(Variety):
    """
    Make a variety object as a toric variety which is defined by a given fan.
    The given fan should be simplicial and complete.
    """
    def __init__(self, fan, var=None):
        if fan.is_simplicial() == False or fan.is_complete() == False:
            raise ValueError("The fan should be simplicial and complete")
        self._fan = fan
        self._dim = fan.dim()
        if var is not None:
            pass
        else:
            var = 'x'
        self._degs = [1]*len(fan.cones(1))
        v = list(normalize_names(len(fan.cones(1))+1,var))
        v.pop(0)
        R = PolynomialRing(QQ,v)
        self._var = R.gens()
        I = fan.Stanley_Reisner_ideal(R) + fan.linear_equivalence_ideal(R)
        self._rels = I.gens()
        f = part(prod(1+c for c in R.gens()),fan.dim())
        self._point = f.reduce(I)/len(fan.cones(fan.dim()))
        pass

    def _repr_(self):
        """
        Returns a string representation of this toric variety.
        
        EXAMPLES::

            sage: s0 = Cone([(0,1),(1,0)])
            sage: s1 = Cone([(0,1),(-1,-2)])
            sage: s2 = Cone([(1,0),(-1,-2)])
            sage: F = Fan([s0,s1,s2])
            sage: X = ToricVariety(F); X
            A toric variety of dimension 2 corresponding to Rational polyhedral fan in 2-d lattice N
        """
        return "A toric variety of dimension %s corresponding to %s" % (self._dim, self._fan)

    def dim(self):
        """
        Returns the dimension of this toric vareity.

        EXAMPLES::

            sage: s0 = Cone([(0,1),(1,0)])
            sage: s1 = Cone([(0,1),(-1,-2)])
            sage: s2 = Cone([(1,0),(-1,-2)])
            sage: F = Fan([s0,s1,s2])
            sage: X = ToricVariety(F)
            sage: X.dim()
            2
        """
        return self._dim

    def is_smooth(self):
        return self._fan.is_smooth()

    def fan(self):
        """
        Returns the fan corresponding to this toric variety.

        EXAMPLES::

            sage: s0 = Cone([(0,1),(1,0)])
            sage: s1 = Cone([(0,1),(-1,-2)])
            sage: s2 = Cone([(1,0),(-1,-2)])
            sage: F = Fan([s0,s1,s2])
            sage: X = ToricVariety(F)
            sage: X.fan()
            Rational polyhedral fan in 2-d lattice N
        """
        return self._fan

    def plot(self):
        """
        Draw a picture of this toric variety.

        EXAMPLES::

            sage: s0 = Cone([(0,1),(1,0)])
            sage: s1 = Cone([(0,1),(-1,-2)])
            sage: s2 = Cone([(1,0),(-1,-2)])
            sage: F = Fan([s0,s1,s2])
            sage: X = ToricVariety(F)
            sage: X.plot()
        """
        return self._fan.plot()

    def coordinate_ring(self):
        """
        Returns the coordinate ring (Cox ring) of this toric variety.

        EXAMPLES::

            sage: s0 = Cone([(0,1),(1,0)])
            sage: s1 = Cone([(0,1),(-1,-2)])
            sage: s2 = Cone([(1,0),(-1,-2)])
            sage: F = Fan([s0,s1,s2])
            sage: X = ToricVariety(F)
            sage: X.coordinate_ring()
            Multivariate Polynomial Ring in z1, z2, z3 over Rational Field
        """
        return PolynomialRing(QQ,self._var)

    def tangent_bundle(self):
        """
        Returns the tangent bundle of this toric variety.
        The toric variety should be smooth.

        EXAMPLES::

            sage: C1 = Cone([(0,1),(1,0)])
            sage: C2 = Cone([(1,0),(-1,-1)])
            sage: C3 = Cone([(-1,-1),(0,1)])
            sage: F = Fan([C1,C2,C3])   
            sage: P2 = ToricVariety(F)            
            sage: P2.is_smooth()
            True
            sage: T = P2.tangent_bundle(); T
            A vector bundle of rank 2 on A toric variety of dimension 2 corresponding to Rational polyhedral fan in 2-d lattice N
        """
        if self._fan.is_smooth == False:
            raise ValueError("The fan should be smooth")
        R = self.coordinate_ring()
        f = parts(prod(1+c for c in R.gens()),0,self._dim)
        c = f.reduce(R.ideal(self._rels))
        return VectorBundle(self,self._dim,chern_class=c)

    def todd_class(self):
        """
        Returns the Todd class of this toric variety.

        EXAMPLES::

            sage: C1 = Cone([(0,1),(1,0)])
            sage: C2 = Cone([(1,0),(-1,-1)])
            sage: C3 = Cone([(-1,-1),(0,1)])
            sage: F = Fan([C1,C2,C3])   
            sage: P2 = ToricVariety(F)
            sage: P2.todd_class()
            z3^2 + 3/2*z3 + 1
        """
        T = self.tangent_bundle()
        return T.todd_class()

    def chern_character(self):
        """
        Returns the Chern character of this toric variety.

        EXAMPLES::

            sage: C1 = Cone([(0,1),(1,0)])
            sage: C2 = Cone([(1,0),(-1,-1)])
            sage: C3 = Cone([(-1,-1),(0,1)])
            sage: F = Fan([C1,C2,C3])   
            sage: P2 = ToricVariety(F)
            sage: P2.chern_character()
            3/2*z3^2 + 3*z3 + 2
        """
        T = self.tangent_bundle()
        return T.chern_character()

    def chern_class(self,k):
        """
        Returns the k-th Chern class of this toric variety.

        EXAMPLES::

            sage: C1 = Cone([(0,1),(1,0)])
            sage: C2 = Cone([(1,0),(-1,-1)])
            sage: C3 = Cone([(-1,-1),(0,1)])
            sage: F = Fan([C1,C2,C3])   
            sage: P2 = ToricVariety(F)
            sage: P2.chern_class(2)
            3*z3^2
            sage: P2.chern_class(1)
            3*z3
            sage: P2.chern_class(0)
            1
        """
        T = self.tangent_bundle()
        return T.chern_class(k)

    def total_chern_class(self):
        """
        Returns the total Chern class of this toric variety.

        EXAMPLES::

            sage: C1 = Cone([(0,1),(1,0)])
            sage: C2 = Cone([(1,0),(-1,-1)])
            sage: C3 = Cone([(-1,-1),(0,1)])
            sage: F = Fan([C1,C2,C3])   
            sage: P2 = ToricVariety(F)
            sage: P2.total_chern_class()
            3*z3^2 + 3*z3 + 1
        """
        T = self.tangent_bundle()
        return T.total_chern_class()        

    def divisor(self, l):
        """
        Returns a divisor on this toric variety.

        EXAMPLES::

            sage: C1 = Cone([(0,1),(1,0)])
            sage: C2 = Cone([(1,0),(0,-1)]) 
            sage: C3 = Cone([(0,-1),(-1,2)])
            sage: C4 = Cone([(-1,2),(0,1)])
            sage: F = Fan([C1,C2,C3,C4])
            sage: H2 = ToricVariety(F)          
            sage: H2.divisor([0,-5,3,0])
            -5*z2 + 3*z3
        """
        v = self._var
        return sum(l[i]*v[i] for i in range(len(v)))

def ToricProjectiveSpace(n):
    """
    Returns a projective space as a toric variety.
    """
    cones = []
    for i in range(n+1):
        e = [tuple(a) for a in IntegerVectors(1,n).list()] + [tuple([-1]*n)]
        e.pop(-i-1)
        cones.append(Cone(e))
    F = Fan(cones)
    return ToricVariety(F)

def HirzebruchSurface(r):
    """
    Returns a Hirzebruch surface as a toric variety.
    """
    C1 = Cone([(0,1),(1,0)])
    C2 = Cone([(1,0),(0,-1)])
    C3 = Cone([(0,-1),(-1,r)])
    C4 = Cone([(-1,r),(0,1)])
    F = Fan([C1,C2,C3,C4])
    return ToricVariety(F)

################################################################################
###################### Gromov-Witten invariants ################################
################################################################################

class ModuliSpace(SageObject):
    """
    Makes a class of moduli spaces of degree d stable maps from a genus 0 curve to 
    a projective space with no marked point.
    """
    def __init__(self, P, d, var='t'):
        self._r = P._dim
        self._d = d
        self._dim = P._dim*d+P._dim+d-3
        #R = PolynomialRing(QQ,normalize_names(P._dim+1,var))
        #S = FractionField(R)
        #self._v = S.gens()
        self._v = [10**i for i in range(P._dim+1)]
        pass

    def _repr_(self):
        """
        Returns a string representation of this moduli space.
        
        EXAMPLES::

            sage: P = ProjectiveSpace(4)
            sage: M = ModuliSpace(P,1); M
            A moduli space of dimension 6
        """
        return "A moduli space of dimension %s" % self._dim

    def dim(self):
        """
        Returns the dimension of this moduli space.
        
        EXAMPLES::

            sage: P = ProjectiveSpace(4)
            sage: M = ModuliSpace(P,1)
            sage: M.dim()
            6
        """
        return self._dim

    def fixed_points(self):
        """
        Returns the fixed point loci of this moduli space under the natural 
        torus action.
        
        EXAMPLES::

            sage: P = ProjectiveSpace(4)
            sage: M = ModuliSpace(P,1)
            sage: F = M.fixed_points()
            sage: type(F)
            <type 'dict'>
            sage: len(F)
            10
            sage: K = F.keys()
            sage: type(K)
            <type 'list'>
            sage: p = K[0]; p
            A graph on 2 vertices, 1 edges and 2 flags
            sage: p.vertices()
            [(0, 1, ((0, 1), (0, 1, 1))), (1, 1, ((1, 1), (1, 0, 1)))]
            sage: p.edges()
            [(0, 1, 1)]
            sage: p.flags()
            [((0, 1), (0, 1, 1)), ((1, 1), (1, 0, 1))]
        """
        S = Set(range(self._r+1))
        D = Partitions(self._d).list()
        R = {}
        for i in S:
            for j in S.difference({i}):
                R[Graph1(D[0],i,j)] = 2*self._d
        if self._d == 2:
            for i in S:
                for j in S.difference({i}):
                    for k in S.difference({j}):
                        R[Graph2(D[1],i,j,k)] = 2
        if self._d == 3:
            for i in S:
                for j in S.difference({i}):
                    for k in S.difference({j}):
                        R[Graph2(D[1],i,j,k)] = 2
                        for h in S:
                            if h != k:
                                R[Graph31(D[2],i,j,k,h)] = 2
                            if h != j:
                                R[Graph32(D[2],i,j,k,h)] = 6
        if self._d == 4:
            for i in S:
                for j in S.difference({i}):
                    for k in S.difference({j}):
                        R[Graph2(D[1],i,j,k)] = 3
                        R[Graph2(D[2],i,j,k)] = 8
                        for h in S:
                            if k != h:
                                R[Graph31(D[3],i,j,k,h)] = 2
                                R[Graph31([1,2,1],i,j,k,h)] = 4
                            if j != h:
                                R[Graph32(D[3],i,j,k,h)] = 4
                            for m in S:
                                if k != h and h != m:
                                    R[Graph41(D[4],i,j,k,h,m)] = 2
                                if k != h and k != m:
                                    R[Graph42(D[4],i,j,k,h,m)] = 2
                                if j != h and j != m:
                                    R[Graph43(D[4],i,j,k,h,m)] = 24
        if self._d == 5:
            for i in S:
                for j in S.difference({i}):
                    for k in S.difference({j}):
                        R[Graph2([4,1],i,j,k)] = 4
                        R[Graph2([3,2],i,j,k)] = 6
                        for h in S:
                            if k != h:
                                R[Graph31([3,1,1],i,j,k,h)] = 3
                                R[Graph31([1,3,1],i,j,k,h)] = 6
                                R[Graph31([2,2,1],i,j,k,h)] = 4
                                R[Graph31([2,1,2],i,j,k,h)] = 8
                            if j != h:
                                R[Graph32([3,1,1],i,j,k,h)] = 6
                                R[Graph32([2,2,1],i,j,k,h)] = 8
                            for m in S:
                                if k != h and h != m:
                                    R[Graph41([2,1,1,1],i,j,k,h,m)] = 2
                                    R[Graph41([1,2,1,1],i,j,k,h,m)] = 2
                                if k != h and k != m:
                                    R[Graph42([2,1,1,1],i,j,k,h,m)] = 4
                                    R[Graph42([1,2,1,1],i,j,k,h,m)] = 4
                                    R[Graph42([1,1,2,1],i,j,k,h,m)] = 2
                                if j != h and j != m:
                                    R[Graph43([2,1,1,1],i,j,k,h,m)] = 12
                                for n in S:
                                    if k != h and h != m and m != n:
                                        R[Graph51([1,1,1,1,1],i,j,k,h,m,n)] = 2
                                    if k != h and h != m and h != n:
                                        R[Graph52([1,1,1,1,1],i,j,k,h,m,n)] = 2
                                    if k != h and k != m and k != n:
                                        R[Graph53([1,1,1,1,1],i,j,k,h,m,n)] = 6
                                    if j != h and h != m and h != n:
                                        R[Graph54([1,1,1,1,1],i,j,k,h,m,n)] = 8
                                    if k != h and k != m and h != n:
                                        R[Graph55([1,1,1,1,1],i,j,k,h,m,n)] = 2
                                    if j != h and j != m and j != n:
                                        R[Graph56([1,1,1,1,1],i,j,k,h,m,n)] = 120
        if self._d == 6:
            for i in S:
                for j in S.difference({i}):
                    for k in S.difference({j}):
                        R[Graph2([5,1],i,j,k)] = 5
                        R[Graph2([4,2],i,j,k)] = 8
                        R[Graph2([3,3],i,j,k)] = 18
                        for h in S:
                            if k != h:
                                R[Graph31([4,1,1],i,j,k,h)] = 4
                                R[Graph31([1,4,1],i,j,k,h)] = 8
                                R[Graph31([3,2,1],i,j,k,h)] = 6
                                R[Graph31([3,1,2],i,j,k,h)] = 6
                                R[Graph31([1,3,2],i,j,k,h)] = 6
                                R[Graph31([2,2,2],i,j,k,h)] = 16
                            if j != h:
                                R[Graph32([4,1,1],i,j,k,h)] = 8
                                R[Graph32([3,2,1],i,j,k,h)] = 6
                                R[Graph32([2,2,2],i,j,k,h)] = 48
                            for m in S:
                                if k != h and h != m:
                                    R[Graph41([3,1,1,1],i,j,k,h,m)] = 3
                                    R[Graph41([1,3,1,1],i,j,k,h,m)] = 3
                                    R[Graph41([2,2,1,1],i,j,k,h,m)] = 4
                                    R[Graph41([2,1,2,1],i,j,k,h,m)] = 4
                                    R[Graph41([2,1,1,2],i,j,k,h,m)] = 8
                                    R[Graph41([1,2,2,1],i,j,k,h,m)] = 8
                                if k != h and k != m:
                                    R[Graph42([3,1,1,1],i,j,k,h,m)] = 6
                                    R[Graph42([1,3,1,1],i,j,k,h,m)] = 6
                                    R[Graph42([1,1,3,1],i,j,k,h,m)] = 3
                                    R[Graph42([2,2,1,1],i,j,k,h,m)] = 8
                                    R[Graph42([1,1,2,2],i,j,k,h,m)] = 8
                                    R[Graph42([2,1,2,1],i,j,k,h,m)] = 4
                                    R[Graph42([1,2,2,1],i,j,k,h,m)] = 4
                                if j != h and j != m:
                                    R[Graph43([3,1,1,1],i,j,k,h,m)] = 18
                                    R[Graph43([2,2,1,1],i,j,k,h,m)] = 16
                                for n in S:
                                    if k != h and h != m and m != n:
                                        R[Graph51([2,1,1,1,1],i,j,k,h,m,n)] = 2
                                        R[Graph51([1,2,1,1,1],i,j,k,h,m,n)] = 2
                                        R[Graph51([1,1,2,1,1],i,j,k,h,m,n)] = 4
                                    if k != h and h != m and h != n:
                                        R[Graph52([2,1,1,1,1],i,j,k,h,m,n)] = 4
                                        R[Graph52([1,2,1,1,1],i,j,k,h,m,n)] = 4
                                        R[Graph52([1,1,2,1,1],i,j,k,h,m,n)] = 4
                                        R[Graph52([1,1,1,2,1],i,j,k,h,m,n)] = 2
                                    if k != h and k != m and k != n:
                                        R[Graph53([2,1,1,1,1],i,j,k,h,m,n)] = 12
                                        R[Graph53([1,2,1,1,1],i,j,k,h,m,n)] = 12
                                        R[Graph53([1,1,2,1,1],i,j,k,h,m,n)] = 4
                                    if j != h and h != m and h != n:
                                        R[Graph54([2,1,1,1,1],i,j,k,h,m,n)] = 4
                                        R[Graph54([1,1,2,1,1],i,j,k,h,m,n)] = 16
                                    if k != h and k != m and h != n:
                                        R[Graph55([2,1,1,1,1],i,j,k,h,m,n)] = 2
                                        R[Graph55([1,2,1,1,1],i,j,k,h,m,n)] = 2
                                        R[Graph55([1,1,1,2,1],i,j,k,h,m,n)] = 4
                                    if j != h and j != m and j != n:
                                        R[Graph56([2,1,1,1,1],i,j,k,h,m,n)] = 48
                                    for p in S:
                                        if k != h and h != m and m != n and n != p:
                                            R[Graph61([1,1,1,1,1,1],i,j,k,h,m,n,p)] = 2
                                        if k != h and h != m and m != n and m != p:
                                            R[Graph62([1,1,1,1,1,1],i,j,k,h,m,n,p)] = 2
                                        if k != h and h != m and h != p and m != n:
                                            R[Graph63([1,1,1,1,1,1],i,j,k,h,m,n,p)] = 1
                                        if k != h and h != m and h != n and h != p:
                                            R[Graph64([1,1,1,1,1,1],i,j,k,h,m,n,p)] = 6
                                        if k != h and k != n and k != p and h != m:
                                            R[Graph65([1,1,1,1,1,1],i,j,k,h,m,n,p)] = 4
                                        if k != h and k != p and h != m and h != n:
                                            R[Graph66([1,1,1,1,1,1],i,j,k,h,m,n,p)] = 2
                                        if j != p and k != h and h != m and h != n:
                                            R[Graph67([1,1,1,1,1,1],i,j,k,h,m,n,p)] = 8
                                        if j != p and k != h and k != m and k != n:
                                            R[Graph68([1,1,1,1,1,1],i,j,k,h,m,n,p)] = 12
                                        if k != h and h != n and k != m and m != p:
                                            R[Graph69([1,1,1,1,1,1],i,j,k,h,m,n,p)] = 6
                                        if k != h and k != m and k != n and k != p:
                                            R[Graph610([1,1,1,1,1,1],i,j,k,h,m,n,p)] = 24
                                        if j != h and j != m and j != n and j != p:
                                            R[Graph611([1,1,1,1,1,1],i,j,k,h,m,n,p)] = 720
        return R

    def contribution_bundle(self, G, d=None):
        """
        Returns the equivariant Euler class of the contribution bundle on this 
        moduli space.

        EXAMPLES::

            sage: P = ProjectiveSpace(4)
            sage: M = ModuliSpace(P,2)
            sage: F = M.fixed_points(); K = F.keys()
            sage: p = K[0]; p
            A graph of 3 vertices and 2 edges
            sage: M.contribution_bundle(p)
            135014500030592000000000000000000000000000
        """
        t = self._v
        if d == None:
            d = 2*self._r - 3
        E = 1
        V = 1
        if self._r == 1:
            for v in G.vertices():
                V = V*(-t[v[0]])**(v[1]-1)
            for e in G.edges():
                f = 1
                if e[2] != 1:
                    for a in range(1,e[2]):
                        f=f*(-a*t[e[0]]-(e[2]-a)*t[e[1]])/Rational(e[2])
                E = E*f
            return (E*V)**2
        else:
            for v in G.vertices():
                V = V*((d*t[v[0]])**(v[1]-1))
            for e in G.edges():
                f = 1
                for a in range(d*e[2]+1):
                    f = f*(a*t[e[0]]+(d*e[2]-a)*t[e[1]])/Rational(e[2])
                E = E*f;
            return E/Rational(V)

    def equivariant_normal_bundle(self, G):
        """
        Returns the euqivariant Euler class of the tangent bundle on this moduli space.

        EXAMPLES::

            sage: P = ProjectiveSpace(4)
            sage: M = ModuliSpace(P,2)
            sage: F = M.fixed_points(); K = F.keys()
            sage: p = K[0]; p
            A graph of 3 vertices and 2 edges
            sage: M.equivariant_normal_bundle(p)
            513482889109633509700161000000000000
        """
        t = self._v
        N = 1
        for v in G.vertices():
            L = [v[i] for i in range(2,len(v))]
            F = Rational(prod((t[f[0]] - t[f[1]])/Rational(f[2]) for f in L))
            if v[1] == 1:
                N = N/F
            else:
                z = 1
                for j in range(len(t)):
                    if j != v[0]:
                        z = z*(t[v[0]]-t[j])
                if v[1] == 3:
                    N = N*F/Rational(z)**2
                else:
                    M = Rational(sum(f[2]/Rational(t[f[0]] - t[f[1]]) for f in L))
                    if v[1] == 2:
                        N = N*F*M/Rational(z)
                    else:
                        N = N*F/(M**(v[1]-3)*Rational(z)**(v[1]-1))
        for e in G.edges():
            d = e[2]
            x = Rational((-1)**d*factorial(d)**2/Rational(d**(2*d)))
            y = x*(t[e[0]]-t[e[1]])**(2*d)
            for a in range(d+1):
                for k in range(len(t)):
                    if k != e[0] and k != e[1]:
                        y = y*(Rational((a*t[e[0]]+(d-a)*t[e[1]])/Rational(d)) - t[k])
            N = N*y
        return N

def Graph1(d,i,j):
    v = [(i,1,(i,j,d[0])),(j,1,(j,i,d[0]))]
    e = [(i,j,d[0])]
    return MyGraph(v,e)

def Graph2(d,i,j,k):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,1,(k,j,d[1]))]
    e = [(i,j,d[0]),(j,k,d[1])]
    return MyGraph(v,e)

def Graph31(d,i,j,k,h):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,2,(k,j,d[1]),(k,h,d[2])),(h,1,(h,k,d[2]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2])]
    return MyGraph(v,e)

def Graph32(d,i,j,k,h):
    v = [(i,1,(i,j,d[0])),(j,3,(j,i,d[0]),(j,k,d[1]),(j,h,d[2])),(k,1,(k,j,d[1])),(h,1,(h,j,d[2]))]
    e = [(i,j,d[0]),(j,k,d[1]),(j,h,d[2])]
    return MyGraph(v,e)

def Graph41(d,i,j,k,h,g):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,2,(k,j,d[1]),(k,h,d[2])),(h,2,(h,k,d[2]),(h,g,d[3])),(g,1,(g,h,d[3]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(h,g,d[3])]
    return MyGraph(v,e)

def Graph42(d,i,j,k,h,g):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,3,(k,j,d[1]),(k,h,d[2]),(k,g,d[3])),(h,1,(h,k,d[2])),(g,1,(g,k,d[3]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(k,g,d[3])]
    return MyGraph(v,e)

def Graph43(d,i,j,k,h,g):
    v = [(i,1,(i,j,d[0])),(j,4,(j,i,d[0]),(j,k,d[1]),(j,h,d[2]),(j,g,d[3])),(k,1,(k,j,d[1])),(h,1,(h,j,d[2])),(g,1,(g,j,d[3]))]
    e = [(i,j,d[0]),(j,k,d[1]),(j,h,d[2]),(j,g,d[3])]
    return MyGraph(v,e)

def Graph51(d,i,j,k,h,m,n):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,2,(k,j,d[1]),(k,h,d[2])),(h,2,(h,k,d[2]),(h,m,d[3])),(m,2,(m,h,d[3]),(m,n,d[4])),(n,1,(n,m,d[4]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(h,m,d[3]),(m,n,d[4])]
    return MyGraph(v,e)

def Graph52(d,i,j,k,h,m,n):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,2,(k,j,d[1]),(k,h,d[2])),(h,3,(h,k,d[2]),(h,m,d[3]),(h,n,d[4])),(m,1,(m,h,d[3])),(n,1,(n,h,d[4]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(h,m,d[3]),(h,n,d[4])]
    return MyGraph(v,e)

def Graph53(d,i,j,k,h,m,n):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,4,(k,j,d[1]),(k,h,d[2]),(k,m,d[3]),(k,n,d[4])),(h,1,(h,k,d[2])),(m,1,(m,k,d[3])),(n,1,(n,k,d[4]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(k,m,d[3]),(k,n,d[4])]
    return MyGraph(v,e)

def Graph54(d,i,j,k,h,m,n):
    v = [(i,1,(i,j,d[0])),(j,3,(j,i,d[0]),(j,k,d[1]),(j,h,d[2])),(k,1,(k,j,d[1])),(h,3,(h,j,d[2]),(h,m,d[3]),(h,n,d[4])),(m,1,(m,h,d[3])),(n,1,(n,h,d[4]))]
    e = [(i,j,d[0]),(j,k,d[1]),(j,h,d[2]),(h,m,d[3]),(h,n,d[4])]
    return MyGraph(v,e)

def Graph55(d,i,j,k,h,m,n):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,3,(k,j,d[1]),(k,h,d[2]),(k,m,d[3])),(h,2,(h,k,d[2]),(h,n,d[4])),(m,1,(m,k,d[3])),(n,1,(n,h,d[4]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(k,m,d[3]),(h,n,d[4])]
    return MyGraph(v,e)

def Graph56(d,i,j,k,h,m,n):
    v = [(i,1,(i,j,d[0])),(j,5,(j,i,d[0]),(j,k,d[1]),(j,h,d[2]),(j,m,d[3]),(j,n,d[4])),(k,1,(k,j,d[1])),(h,1,(h,j,d[2])),(m,1,(m,j,d[3])),(n,1,(n,j,d[4]))]
    e = [(i,j,d[0]),(j,k,d[1]),(j,h,d[2]),(j,m,d[3]),(j,n,d[4])]
    return MyGraph(v,e)

def Graph61(d,i,j,k,h,m,n,p):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,2,(k,j,d[1]),(k,h,d[2])),(h,2,(h,k,d[2]),(h,m,d[3])),(m,2,(m,h,d[3]),(m,n,d[4])),(n,2,(n,m,d[4]),(n,p,d[5])),(p,1,(p,n,d[5]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(h,m,d[3]),(m,n,d[4]),(n,p,d[5])]
    return MyGraph(v,e)

def Graph62(d,i,j,k,h,m,n,p):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,2,(k,j,d[1]),(k,h,d[2])),(h,2,(h,k,d[2]),(h,m,d[3])),(m,3,(m,h,d[3]),(m,n,d[4]),(m,p,d[5])),(n,1,(n,m,d[4])),(p,1,(p,m,d[5]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(h,m,d[3]),(m,n,d[4]),(m,p,d[5])]
    return MyGraph(v,e)

def Graph63(d,i,j,k,h,m,n,p):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,2,(k,j,d[1]),(k,h,d[2])),(h,3,(h,k,d[2]),(h,m,d[3]),(h,p,d[5])),(m,2,(m,h,d[3]),(m,n,d[4])),(n,1,(n,m,d[4])),(p,1,(p,h,d[5]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(h,m,d[3]),(m,n,d[4]),(h,p,d[5])]
    return MyGraph(v,e)

def Graph64(d,i,j,k,h,m,n,p):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,2,(k,j,d[1]),(k,h,d[2])),(h,4,(h,k,d[2]),(h,m,d[3]),(h,n,d[4]),(h,p,d[5])),(m,1,(m,h,d[3])),(n,1,(n,h,d[4])),(p,1,(p,h,d[5]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(h,m,d[3]),(h,n,d[4]),(h,p,d[5])]
    return MyGraph(v,e)

def Graph65(d,i,j,k,h,m,n,p):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,4,(k,j,d[1]),(k,h,d[2]),(k,n,d[4]),(k,p,d[5])),(h,2,(h,k,d[2]),(h,m,d[3])),(m,1,(m,h,d[3])),(n,1,(n,k,d[4])),(p,1,(p,k,d[5]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(h,m,d[3]),(k,n,d[4]),(k,p,d[5])]
    return MyGraph(v,e)

def Graph66(d,i,j,k,h,m,n,p):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,3,(k,j,d[1]),(k,h,d[2]),(k,p,d[5])),(h,3,(h,k,d[2]),(h,m,d[3]),(h,n,d[4])),(m,1,(m,h,d[3])),(n,1,(n,h,d[4])),(p,1,(p,k,d[5]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(h,m,d[3]),(h,n,d[4]),(k,p,d[5])]
    return MyGraph(v,e)

def Graph67(d,i,j,k,h,m,n,p):
    v = [(i,1,(i,j,d[0])),(j,3,(j,i,d[0]),(j,k,d[1]),(j,p,d[5])),(k,2,(k,j,d[1]),(k,h,d[2])),(h,3,(h,k,d[2]),(h,m,d[3]),(h,n,d[4])),(m,1,(m,h,d[3])),(n,1,(n,h,d[4])),(p,1,(p,j,d[5]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(h,m,d[3]),(h,n,d[4]),(j,p,d[5])]
    return MyGraph(v,e)

def Graph68(d,i,j,k,h,m,n,p):
    v = [(i,1,(i,j,d[0])),(j,3,(j,i,d[0]),(j,k,d[1]),(j,p,d[5])),(k,4,(k,j,d[1]),(k,h,d[2]),(k,m,d[3]),(k,n,d[4])),(h,1,(h,k,d[2])),(m,1,(m,k,d[3])),(n,1,(n,k,d[4])),(p,1,(p,j,d[5]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(k,m,d[3]),(k,n,d[4]),(j,p,d[5])]
    return MyGraph(v,e)

def Graph69(d,i,j,k,h,m,n,p):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,3,(k,j,d[1]),(k,h,d[2]),(k,m,d[3])),(h,2,(h,k,d[2]),(h,n,d[4])),(m,2,(m,k,d[3]),(m,p,d[5])),(n,1,(n,h,d[4])),(p,1,(p,m,d[5]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(k,m,d[3]),(h,n,d[4]),(m,p,d[5])]
    return MyGraph(v,e)

def Graph610(d,i,j,k,h,m,n,p):
    v = [(i,1,(i,j,d[0])),(j,2,(j,i,d[0]),(j,k,d[1])),(k,5,(k,j,d[1]),(k,h,d[2]),(k,m,d[3]),(k,n,d[4]),(k,p,d[5])),(h,1,(h,k,d[2])),(m,1,(m,k,d[3])),(n,1,(n,k,d[4])),(p,1,(p,k,d[5]))]
    e = [(i,j,d[0]),(j,k,d[1]),(k,h,d[2]),(k,m,d[3]),(k,n,d[4]),(k,p,d[5])]
    return MyGraph(v,e)

def Graph611(d,i,j,k,h,m,n,p):
    v = [(i,1,(i,j,d[0])),(j,6,(j,i,d[0]),(j,k,d[1]),(j,h,d[2]),(j,m,d[3]),(j,n,d[4]),(j,p,d[5])),(k,1,(k,j,d[1])),(h,1,(h,j,d[2])),(m,1,(m,j,d[3])),(n,1,(n,j,d[4])),(p,1,(p,j,d[5]))]
    e = [(i,j,d[0]),(j,k,d[1]),(j,h,d[2]),(j,m,d[3]),(j,n,d[4]),(j,p,d[5])]
    return MyGraph(v,e)

class MyGraph(SageObject):
    def __init__(self, v, e):
        self._vertices = v
        self._edges = e
        pass

    def _repr_(self):
        return "A graph of %s vertices and %s edges" % (len(self._vertices),len(self._edges))

    def vertices(self):
        return self._vertices

    def edges(self):
        return self._edges

    def val(self, v):
        return v[1]

def lines_on_hypersurfaces(n):
    """
    Returns the Gromov-Witten invariants corresponding the numbers of lines on a
    general hypersurface of degree d = 2n - 3 in P^n. These numbers can be 
    obtained by Schubert calculus or using Bott's formula for Grassmannians.

    EXAMPLES::

        sage: lines_on_hypersurface(3)
        27
        sage: lines_on_hypersurface(4)
        2875
        sage: lines_on_hypersurface(5)
        698005
        sage: lines_on_hypersurface(6)
        305093061
        sage: lines_on_hypersurface(7)
        210480374951
        sage: lines_on_hypersurface(8)
        210776836330775
    """
    P = ProjectiveSpace(n)
    M = ModuliSpace(P,1)
    F = M.fixed_points()
    r = 0
    for p in F.keys():
        s = M.contribution_bundle(p)
        t = M.equivariant_normal_bundle(p)
        r = r + s/(F[p]*t)
    return r

def lines_on_complete_intersection(l):
    """
    Returns the Gromov-Witten invariants corresponding the numbers of lines on a
    general complete intersection of type d

    EXAMPLES::

        sage: lines_on_complete_intersection([5])  
        2875
        sage: lines_on_complete_intersection([4,2])
        1280
        sage: lines_on_complete_intersection([3,3])
        1053
        sage: lines_on_complete_intersection([3,2,2])
        720
        sage: lines_on_complete_intersection([2,2,2,2])
        512
    """
    P = ProjectiveSpace(len(l)+3)
    M = ModuliSpace(P,1)
    F = M.fixed_points()
    r = 0
    for p in F.keys():
        s = prod(M.contribution_bundle(p,i) for i in l)
        t = M.equivariant_normal_bundle(p)
        r = r + s/(F[p]*t)
    return r

def conics_on_complete_intersection(l):
    """
    Returns the Gromov-Witten invariants corresponding the numbers of conics
    on a general complete intersection of type l.

    EXAMPLES::

        sage: conics_on_complete_intersection([5])
        4876875/8
        sage: conics_on_complete_intersection([3,3])
        423549/8
        sage: conics_on_complete_intersection([4,2])
        92448
        sage: conics_on_complete_intersection([3,2,2])
        22518
        sage: conics_on_complete_intersection([2,2,2,2])
        9792
    """
    P = ProjectiveSpace(len(l)+3)
    M = ModuliSpace(P,2)
    F = M.fixed_points()
    r = 0
    for p in F.keys():
        s = prod(M.contribution_bundle(p,i) for i in l)
        t = M.equivariant_normal_bundle(p)
        r = r + s/(F[p]*t)
    return r

def rational_curves_on_quintic_threefold(d):
    """
    Returns the Gromov-Witten invariants corresponding the numbers of rational 
    curves of degree d on a general quintic threefold in P^4.

    EXAMPLES::

        sage: rational_curves_on_quintic_threefold(1)
        2875
        sage: rational_curves_on_quintic_threefold(2)
        4876875/8
        sage: rational_curves_on_quintic_threefold(3)
        8564575000/27
    """
    P = ProjectiveSpace(4)
    M = ModuliSpace(P,d)
    F = M.fixed_points()
    r = 0
    for p in F.keys():
        s = M.contribution_bundle(p)
        t = M.equivariant_normal_bundle(p)
        r = r + s/(F[p]*t)
    return r

def rational_curves(d,l):
    """
    Returns the Gromov-Witten invariants corresponding the numbers of rational 
    curves of degree d on a general complete intersection of type l.

    EXAMPLES::

        sage: T = [[5],[4,2],[3,3],[3,2,2],[2,2,2,2]]
        sage: [rational_curves(1,t) for t in T]
        [2875, 1280, 1053, 720, 512]
        sage: [rational_curves(2,t) for t in T]
        [4876875/8, 92448, 423549/8, 22518, 9792]
        sage: [rational_curves(3,t) for t in T]
        [8564575000/27, 422690816/27, 6424365, 4834592/3, 11239424/27]
    """
    P = ProjectiveSpace(len(l)+3)
    M = ModuliSpace(P,d)
    F = M.fixed_points()
    r = 0
    for p in F.keys():
        s = prod(M.contribution_bundle(p,i) for i in l)
        t = M.equivariant_normal_bundle(p)
        r = r + s/(F[p]*t)
    return r

def multiple_cover(d):
    """
    This is the contribution of degree d multiple covers of a smooth rational
    curve as a Gromov-Witten invariant.
    
    EXAMPLES::

        sage: [multiple_cover(d) for d in range(1,7)]
        [1, 1/8, 1/27, 1/64, 1/125, 1/216]
    """
    P = ProjectiveSpace(1)
    M = ModuliSpace(P,d)
    F = M.fixed_points()
    r = 0
    for p in F.keys():
        s = M.contribution_bundle(p)
        t = M.equivariant_normal_bundle(p)
        r = r + s/(F[p]*t)
    return r

################################################################################
####################### Examples for the furture works #########################
################################################################################

def Gromov_Witten_invariants_for_lines(k,a,b):
    G = Grassmannian(2,k+2)
    S = G.tautological_subbundle().dual()
    B = S.symmetric_power(k+2)
    qa = G.schubert_class([a-1])
    qb = G.schubert_class([b-1])
    qc = G.schubert_class([k-a-b-1])
    return G.integral(B.top_chern_class()*qa*qb*qc)

def Gromov_Witten_invariants_lines_Bott_formula(k,a,b):
    G = Grassmannian(2,k+2)
    F = G.fixed_points()
    result = 0
    for p in F:
        S = G.equivariant_subbundle(p)
        Q = G.equivariant_quotient_bundle(p)
        D = S.dual()
        B = D.symmetric_power(k+2)
        qa = Q.chern_class(a-1)
        qb = Q.chern_class(b-1)
        qc = Q.chern_class(k-a-b-1)
        s = B.euler_class()*qa*qb*qc
        T = G.equivariant_tangent_bundle(p)
        t = T.euler_class()
        result = result + s/t
    return result

#here is the code of Corollary 5.3.6:

def number_linear_subspaces(k,d,n):
    """
    Note that we replace the number lambda_i in Corollary 5.3.6 by the integer i
    """
    phi = (k+1)*(n-k)-binomial(d+k,d)
    if phi <> 0:
        raise ValueError('Invalid data')
    S = Set([i for i in range(1,n+2)])
    F = S.subsets(k+1).list()
    V = IntegerVectors(d,k+1)
    result = 0
    for p in F:
        q = S - p
        s = prod(sum(v[i]*p[i] for i in range(k+1)) for v in V)
        t = prod(i - j for i in p for j in q)
        result = result + s/t
    return result

#here is the code of Theorem 5.3.5:

def degree_fano_scheme(k,d,n):
    """
    Note that we replace the number lambda_i in Theorem 5.3.5 by the integer i
    """
    phi = (k+1)*(n-k)-binomial(d+k,d)
    if phi < 0:
        raise ValueError('Fano scheme is empty')
    S = Set([i for i in range(1,n+2)])
    F = S.subsets(k+1).list()
    V = IntegerVectors(d,k+1)
    result = 0
    for p in F:
        q = S - p
        s = prod(sum(v[i]*p[i] for i in range(k+1)) for v in V)
        t = prod(i - j for i in p for j in q)
        result = result + (s*(-sum(q))**phi)/t
    return result

#compute the algebraic degree of semidefinite programming

def algDegSDP(m,n,r):
    G = Grassmannian(r,n)
    S = G.tautological_subbundle().dual()
    Q = G.tautological_quotient_bundle()
    A = Q.symmetric_power(2)
    B = S.symmetric_power(2)
    c = A.segre_class(m-binomial(n-r+1,2))
    d = B.segre_class(binomial(n+1,2)-m-binomial(r+1,2))
    return G.integral(c*d)
