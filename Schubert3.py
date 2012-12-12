"""
Schubert3 is a Sage package which supports computation in Intersection Theory on smooth varieties. It is written by Python programming language.

A variety is not given by equations, it is given by dim, var, degs, rels such that we can compute its Chow ring or even its rels is not known, but we must know its monomial values. This helps us return the degree of cycle classes (integration).

A vector bundle on a variety and a morphism between varieties are similar to Schubert2 in Macaulay2.
"""
from sage.structure.sage_object import SageObject
import sage.libs.singular
from sage.rings.arith import factorial
from sage.structure.parent_gens import normalize_names
from sage.combinat.sf.sfa import SFAElementary
from sage.libs.singular.function import SingularLibraryFunction
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.interfaces.singular import singular
from sage.rings.all import ZZ, QQ
from sage.rings.quotient_ring import QuotientRing
from sage.rings.polynomial.term_order import TermOrder

######################################################################################
########################   Tools  ####################################################
######################################################################################

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
    Returns a new polynomial that is the sum of the homogeneous components of degree 
    from i to j of given polynomial f.
    
    EXAMPLES::

        sage: R.<x,y,z>=PolynomialRing(QQ)
        sage: f = R(x+y+x^2+y^3+z^3)
        sage: parts(f,1,2)
        x^2 + x + y
    """
    return sum(part(f,k) for k in range(i,j+1))

def logg(f,d):
    """
    f is the total chern class. The chern character is returned.

    EXAMPLES::

        sage: R.<x,y> = PolynomialRing(QQ, order=TermOrder('wdegrevlex',[1,2]))
        sage: f = R(1+x+y)
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

        sage: R.<x>=QQ[]
        sage: f = 3+x
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

        sage: R.<x,y,z> = PolynomialRing(QQ, order=TermOrder('wdegrevlex',[1,2,3]))
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

        sage: R.<x,y,z> = PolynomialRing(QQ, order=TermOrder('wdegrevlex',[1,2,3]))
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
    
        sage: R.<x,y,z> = PolynomialRing(QQ, order=TermOrder('wdegrevlex',[1,2,3]))
        sage: f = 1 - x + y - z
        sage: segre(f,4)
        x^4 - 3*x^2*y + 2*x*z + y^2 + x^3 - 2*x*y + z + x^2 - y + x + 1
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

def kontsevich(d):
    """
    Returns the number of rational curves of degree d passing through 3d-1 general points in P^2.

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
        f = f + i**2*j*(j*binomial(3*d-4,3*i-2)-i*binomial(3*d-4,3*i-1))*kontsevich(i)*kontsevich(j)
    return f

def bipart(l):
    """
    Needs this to compute genus zero Gromow-Witten invariants for projective spaces.

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

###########################################################################################
############################# Abstract varieties ##########################################
###########################################################################################

class Variety(SageObject):
    """
    Makes a variety generally.
    """
    def __init__(self, dim, var = None, degs = None, rels = None, point=None, tb=None):
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
            Quotient of Multivariate Polynomial Ring in q1, q2 over Rational Field by the ideal (-q1^3 + 2*q1*q2, q1^4 - 3*q1^2*q2 + q2^2)
            sage: P = ProjectiveSpace(3)
            sage: P.relations()
            [h^4]
            sage: P.chow_ring()
            Univariate Quotient Polynomial Ring in h over Rational Field with modulus h^4
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
        return PolynomialRing(QQ, self._var, order=TermOrder('wdegrevlex',self._degs))

    def chow_ring(self):
        """
        Returns the Chow ring of this variety.

        EXAMPLES::

            sage: R.<h,e> = QQ[]
            sage: V = Variety(dim=2,var=[h,e],degs=[1,1],rels=[h*e,h^2+e^2])
            sage: V.chow_ring()
            Quotient of Multivariate Polynomial Ring in h, e over Rational Field by the ideal (h*e, h^2 + e^2)
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
        Returns all monomials in the variables of this variety up to weighted degree d.

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
            ({0: [1], 1: [q1], 2: [q2, q1^2], 3: [q1*q2], 4: [q2^2]}, {0: [1], 1: [q1], 2: [-q1^2 + 2*q2, q1^2 - q2], 3: [q1*q2], 4: [q2^2]})
            sage: P = ProjectiveSpace(3)
            sage: P.additive_basis()
            ({0: [1], 1: [h], 2: [h^2], 3: [h^3]}, {0: [1], 1: [h], 2: [h^2], 3: [h^3]})
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
            monomial_matrix = matrix(P, len(columns), 1, [RDk[i] for i in columns])            
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
        Returns the degree of the zero cycle by using the monomial values of this variety.
        We often use this method for the varieties that the Chow ring is not known but 
        the monomial values is known.
        
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
        v = list(self._var)
        d = self.monomial_values()
        if len(v) == 1:
            return c[self._dim]*d[v[0]**self._dim]
        else:
            mons = c.monomials()
            coefs = c.coefficients()
            return sum(coefs[i]*self.monomial_values().get(mons[i],0) for i in range(len(coefs)))

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
        R = self.chow_ring()
        c = R(c)
        if R.ngens() == 1:
            return c.lift()[c.lift().degree()]
        else:
            return c.lc()

    def betti_number(self, n):
        """
        The n-th Betti number is returned.
        The Betti numbers mean the dimensions of the graded pieces of the numerical Chow ring.
        So they are the numbers of elements in each degree in the basis of this variety.
        
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
        if var is not None:
            d = normalize_names(k,var)
        else:
            d = normalize_names(k,'e')
        v = tuple(self._var)
        w = self._degs + [1]*k
        R = PolynomialRing(QQ, d+v, order=TermOrder('wdegrevlex',w))
        h = R.gens()
        r = self._rels + [h[i]**self._dim + (-1)**self._dim*self._point for i in range(len(d))]
        for i in range(len(h)-1):
            for j in range(i+1,len(h)):
                r.append(h[i]*h[j])
        return Variety(dim=self._dim, var = h, degs = w, rels = r, point=self._point)

class Base(Variety):
    """
    Makes an abstract variety from nothing, equipped with some bundles.
    Its Chow ring is the polynomial ring.
    """
    def __init__(self, d, bundles):
        self._dim = d
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
        f = 1 + sum(v[j] for j in range(k,k+self._bundles[i-1][0]))
        return VectorBundle(variety = self, rank = self._bundles[i-1][0], chern_class = f)

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
            Multivariate Polynomial Ring in c1, c2, d1, d2, d3 over Rational Field
        """
        return PolynomialRing(QQ, self._var, order=TermOrder('wdegrevlex',self._degs))

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
        
        The degree of a Grassmannian is also equal to the degree of class 'self._point'.

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
        Returns the list of all indices of the Schubert classes of this Grassmannian.

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
                    result.append(e)
        return result

    def schubert_class(self, p):
        """
        Returns the Schubert classes of this Grassmannian.
        -- p is a list of integers, that is a partition of n-k.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.schubert_class([1,1])
            q1^2 - q2
            sage: G = Grassmannian(2,5)
            sage: G.schubert_class([2,1])
            q1*q2 - q3
        """
        if p in self.schubert_classes():
            f = 1 + sum(self._var)
            return schur(p,f)
        else:
            raise ValueError("the input be wrong")

    def pieri_formula(self, m, a):
        """
        Input: 
            'm' is an integer, that should be from 0 to n-k and be an index of a special Schubert class.
            'a' is a list of integers, that is an index of a Schubert class.
        Output: 
            Returns a list of the indices that satisfying the Pieri's formula.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.pieri_formula(1,[1])  
            [[2], [1, 1]]
            sage: G.pieri_formula(1,[2])
            [[2, 1]]
            sage: G.pieri_formula(1,[1,1])
            [[2, 1]]
            sage: G.pieri_formula(1,[2,1])
            [[2, 2]]
            sage: G.pieri_formula(2,[2])
            [[2, 2]]
        """
        if m < 0 or m > self._n-self._k:
            raise ValueError("the input be wrong")
        elif a not in self.schubert_classes():
            raise ValueError("the input be wrong")
        else:
            return pieri(self._k, self._n, m, a)

    def giambelli_formula(self, a):
        """
        Returns the arbitrary Schubert class in terms of the Chern classes 
        of the tautological quotient bundle on this Grassmannian.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.schubert_class([1,1])
            q1^2 - q2
            sage: G.schubert_class([2,1])
            q1*q2
        """
        if a not in self.schubert_classes():
            raise ValueError("the input be wrong")
        else:
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
            A vector bundle of rank 4 on A Grassmannian of all 2-planes in 4-space
            sage: T.total_chern_class()
            8*q1^4 - 16*q1^2*q2 + 6*q2^2 + 8*q1^3 - 4*q1*q2 + 7*q1^2 + 4*q1 + 1
        """
        return self.tautological_subbundle().dual().tensor(self.tautological_quotient_bundle())

    def cotangent_bundle(self):
        """
        Returns the cotangent bundle of this Grassmannian.
        
        EXAMPLES::
        
            sage: G = Grassmannian(2,4)
            sage: C = G.cotangent_bundle(); C
            A vector bundle of rank 4 on A Grassmannian of all 2-planes in 4-space
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
        this Grassmannian G(k,n) with weights 0, 1, 2, ..., n.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: G.fixed_points()
            [{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}]
            sage: G = Grassmannian(2,5)
            sage: G.fixed_points()     
            [{0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}]
        """
        S = Set([i for i in range(self._n)])
        return S.subsets(self._k).list()
        
    def equivariant_quotient_bundle(self, p):
        """
        Returns a subset of integers {0, 1, 2, ..., n}, 
        that is the indices of the equivariant tautological quotient bundle at point p on this Grassmannian.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]; p
            {0, 1}
            sage: Q = G.equivariant_quotient_bundle(p); Q
            An equivariant vector bundle of rank 2 on A Grassmannian of all 2-planes in 4-space
            sage: Q.rank()
            2
            sage: Q.weights()
            {2, 3}
        """
        w = Set([i for i in range(self._n)]) - p
        return EquivariantVectorBundle(self,w)

    def equivariant_subbundle(self, p):
        """
        Returns a subset of integers {0, 1, 2, ..., n}, 
        that is the indices of the dual of equivariant tautological subbundle at point p on this Grassmannian.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]; p
            {0, 1}
            sage: S = G.equivariant_subbundle(p); S
            An equivariant vector bundle of rank 2 on A Grassmannian of all 2-planes in 4-space
            sage: S.rank()
            2
            sage: S.weights()
            {0, 1}
        """
        return EquivariantVectorBundle(self,p)

    def equivariant_tangent_bundle(self, p):
        """
        Returns the equivariant tangent bundle at the fixed point p on this Grassmannian.
        The result should be an integer.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]; p
            {0, 1}
            sage: T = G.equivariant_tangent_bundle(p); T
            An equivariant vector bundle of rank 4 on A Grassmannian of all 2-planes in 4-space
            sage: T.rank()
            4
            sage: T.weights()
            [2, 3, 1, 2]
        """
        Q = self.equivariant_quotient_bundle(p)
        S = self.equivariant_subbundle(p)
        return S.dual() & Q

    def bott_formula(self, c):
        """
        Returns the integral by using the Bott's formula.
        This formula allows us compute the degree of zero cycles in terms of the 
        fixed pionts under an action of torus on this Grassmannian.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(3)
            sage: G.bott_formula(B.top_chern_class())
            27
            sage: G = Grassmannian(2,5)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(5)       
            sage: G.bott_formula(B.top_chern_class())
            2875
            sage: G = Grassmannian(3,5)
            sage: S = G.tautological_subbundle().dual()
            sage: B = S.symmetric_power(2)
            sage: P = ProjectiveBundle(B)
            sage: V = P.O(-1) & S.symmetric_power(3)
            sage: A = S.symmetric_power(5) - V
            sage: p = P.projection_morphism()
            sage: G.bott_formula(p.pushforward(A.top_chern_class()))
            609250
        """
        r = 0
        for p in self.fixed_points():
            Q = self.equivariant_quotient_bundle(p)
            s = [Q.chern_class(i+1) for i in range(Q.rank())]
            T = self.equivariant_tangent_bundle(p)
            t = T.euler_class()
            r = r + c(s)/t
        return r

######################################################################################

class EquivariantVectorBundle(SageObject):
    """
    Makes an equivariant vector bundle on a variety with the torus action.
    It is given by the weights of the torus action on ordinary vector bundle.
    """
    def __init__(self, variety, weights):
        self._variety = variety
        self._weights = weights
        pass

    def _repr_(self):
        """
        Retuens a string representation of this equivariant vector bundle.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]
            sage: Q = G.equivariant_quotient_bundle(p); Q
            An equivariant vector bundle of rank 2 on A Grassmannian of all 2-planes in 4-space
        """
        return "An equivariant vector bundle of rank %s on %s" %(len(self._weights),self._variety)

    def weights(self):
        """
        Returns the weights of this equivariant vector bundle.
        Usually this is a set of integers.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p0 = F[0]; p0
            {0, 1}
            sage: Q = G.equivariant_quotient_bundle(p0)
            sage: Q.weights()
            {2, 3}
            sage: p1 = F[1]; p1
            {0, 2}
            sage: Q = G.equivariant_quotient_bundle(p1)
            sage: Q.weights()
            {1, 3}
        """
        return self._weights

    def rank(self):
        """
        Returns the rank of this equivariant vector bundle.
        This number is the length of weights and equal to the ordinary vector bundle.

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

            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]
            sage: S = G.equivariant_subbundle(p)       
            sage: B = S.dual()                         
            sage: S.weights()
            {0, 1}
            sage: B.weights()
            [0, -1]
        """
        V = self._variety
        w = [-s for s in self.weights()]
        return EquivariantVectorBundle(V, w)

    def __and__(self, arg):
        """
        Returns the tensor of two equivariant vector bundle.

        EXAMPLES::

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
        V = self._variety
        w = [a + b for a in self.weights() for b in arg.weights()]
        return EquivariantVectorBundle(V,w)

    def symmetric_power(self, d):
        """
        Returns the d-th symmetric power of this equivariant vector bundle.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]
            sage: Q = G.equivariant_quotient_bundle(p)
            sage: B = Q.symmetric_power(3)
            sage: B.weights()
            [6, 7, 8, 9]
        """
        V = self._variety
        q = self.weights()
        r = self.rank()
        v = IntegerVectors(d,r)
        w = [sum(e[i]*q[i] for i in range(r)) for e in v]
        return EquivariantVectorBundle(V,w)

    def chern_class(self, k):
        """
        Returns the i-th Chern class of this equivariant vector bundle.
        This is the i-th elementary symmetric function in the weights.

        EXAMPLES::

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
        e = SFAElementary(QQ)
        f = e[k].expand(self.rank())
        return f(self.weights().list())

    def euler_class(self):
        """
        Returns the equivariant Euler class of this equivariant vector bundle.
        This is the top Chern class of this equivariant vector bundle 
        and equal to the product of weights.

        EXAMPLES::

            sage: G = Grassmannian(2,4)
            sage: F = G.fixed_points()
            sage: p = F[0]
            sage: Q = G.equivariant_quotient_bundle(p)
            sage: B = Q.symmetric_power(3)
            sage: B.weights()
            [6, 7, 8, 9]
            sage: B.euler_class()         
            3024
            sage: B.euler_class() == prod(B.weights())
            True
        """
        return prod(self.weights())        

######################################################################################

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
        R = PolynomialRing(QQ, var)
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
            Univariate Quotient Polynomial Ring in h over Rational Field with modulus h^4
            sage: P.monomial_values()
            {h^3: 1}
            sage: P.additive_basis()
            ({0: [1], 1: [h], 2: [h^2], 3: [h^3]}, {0: [1], 1: [h], 2: [h^2], 3: [h^3]})
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

    def trivial_bundle(self):
        """
        Returns the trivial bundle on this projective space.

        EXAMPLES::

            sage: P = ProjectiveSpace(3)
            sage: T = P.trivial_bundle()
            sage: T.total_chern_class()
            1
            sage: T.chern_character()
            3
        """
        return VectorBundle(self,rank=self._dim,chern_class=1)

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
        Returns the (genus 0) Gromov-Witten invariants for this projective space.

        INPUT: 
            d is the degree
            l is a list of non-negative integers: for example the number 3 denotes the class h^3.

        OUTPUT:
            The number of degree d curves meeting some general subvarieties in this projective space.

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
                            res = res + self.GW_invariant(dA,[l1,l[n-2]]+A+[e])*self.GW_invariant(dB,[l2,l[n-3]]+B+[r-e])
                        f = r*dA + r + dA + nA - cA - l1 - l2
                        if f >= 0 and f <= r:
                            res = res - self.GW_invariant(dA,[l1,l2]+A+[f])*self.GW_invariant(dB,[l[n-2],l[n-3]]+B+[r-f])
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
            (h + t4) * (h + t3) * (h + t2) * (h + t1) * (h + t0)
        """
        if len(T) != self._dim + 1:
            raise ValueError("invalid data")
        elif dimT == self._dim + 1:
            var = self._var + normalize_names(self._dim+1,'t')
            R = PolynomialRing(QQ,var)
            v = R.gens()
            f = prod(v[0]+T[i]*v[i+1] for i in range(len(T)))
            I = R.ideal(f)
        elif dimT == 1:
            var = self._var + normalize_names(1,'t')
            R = PolynomialRing(QQ,var)
            v = R.gens()
            f = prod(v[0]+T[i]*v[1] for i in range(len(T)))
            I = R.ideal(f)
        else:
            raise ValueError("notImplemented")
        return QuotientRing(R,I,v)

class HirzebruchSurface(Variety):
    """
    """
    def __init__(self, n, var = None):
        self._n = n
        self._dim = 2
        if var is not None:
            pass
        else:
            var = ('f','e')
        self._degs = [1,1]
        R = PolynomialRing(QQ, var, order=TermOrder('wdegrevlex',self._degs))
        self._var = R.gens()
        v = R.gens()
        self._rels = [v[0]**2, v[1]**2 + self._n*v[0]*v[1]]
        self._point = v[0]*v[1]

    def _repr_(self):
        """
        Returns a string representation of this Hirzebruch surface.

        EXAMPLES::

        """
        return "A Hirzebruch surface that has a section with negative self-intersection number %s"%(-self._n)

    def canonical_class(self):
        """
        """
        v = self._var
        return -2*v[1] - (self._n + 2)*v[0]

################################################################################

class VectorBundle(SageObject):
    """
    Makes a vector bundle on a variety.
    A vector bundle on a variety in Schubert3 is similar to Schubert2. 
    It is given by the rank and the total Chern class or by Chern character.
    chern_class and chern_character should be the polynomials in chern variables. 
    They have a closed relation via 'logg' and 'expp'.
    """
    def __init__(self, variety, rank=None, chern_class=None, chern_character=None):
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
        #R = self.variety().chow_ring()
        #S = self.variety().base_ring()
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
            sage: S = G.tautological_subbundle()
            sage: B = S.symmetric_power(3); B
            A vector bundle of rank 4 on A Grassmannian of all 2-planes in 4-space
            sage: B.top_chern_class()
            27*q1^2
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
        return part(g,i)

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
            1/12*c0^2 + 1/12*c1 + 1/2*c0 + 1
        """
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
        return schur(p,g)
        
    def chi(self):
        """
        Returns the Euler-Poincare characteristic of a vector bundle using Riemann-Roch Theorem.

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
            A projective bundle of A vector bundle of rank 6 on A Grassmannian of all 3-planes in 5-space
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
        Returns the first Chern class of the dual of tautological line bundle on this projective bundle.

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
            A vector bundle of rank 1 on A projective bundle of A vector bundle of rank 6 on A Grassmannian of all 3-planes in 5-space
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
            A morphism between A projective bundle of A vector bundle of rank 6 on A Grassmannian of all 3-planes in 5-space and A Grassmannian of all 3-planes in 5-space
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
            A Grassmann bundle of rank 1 subbundles of A vector bundle of rank 6 on A Grassmannian of all 3-planes in 4-space
            sage: GB.chow_ring()
            Quotient of Multivariate Polynomial Ring in S1, q1 over Rational Field by the ideal (S1^6 - 4*S1^5*q1 + 10*S1^4*q1^2 - 20*S1^3*q1^3, q1^4)
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
            A vector bundle of rank 1 on A Grassmann bundle of rank 1 subbundles of A vector bundle of rank 6 on A Grassmannian of all 3-planes in 4-space
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
            A vector bundle of rank 5 on A Grassmann bundle of rank 1 subbundles of A vector bundle of rank 6 on A Grassmannian of all 3-planes in 4-space
        """
        R = self.base_ring()
        S = self.tautological_subbundle()._chern_character
        ch = self._bundle._chern_character - S
        return VectorBundle(variety=self, chern_character = ch)

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
            A product variety of A projective space of dimension 3 and A Grassmannian of all 2-planes in 5-space
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
            {h^3*q1^2*q2^2: 2, h^3*q1^4*q2: 3, h^3*q1^6: 5, h^3*q1^3*q3: 1, h^3*q1*q2*q3: 1, h^3*q3^2: 1, h^3*q2^3: 1}
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
            {0: [1], 1: [h, q1], 2: [h^2, h*q1, q2, q1^2], 3: [h^3, h^2*q1, h*q2, h*q1^2, q3, q1*q2], 4: [h^3*q1, h^2*q2, h^2*q1^2, h*q3, h*q1*q2, -q2^2 + 2*q1*q3, q2^2 - q1*q3], 5: [h^3*q2, h^3*q1^2, h^2*q3, h^2*q1*q2, -h*q2^2 + 2*h*q1*q3, h*q2^2 - h*q1*q3, q2*q3], 6: [h^3*q3, h^3*q1*q2, -h^2*q2^2 + 2*h^2*q1*q3, h^2*q2^2 - h^2*q1*q3, h*q2*q3, q3^2], 7: [-h^3*q2^2 + 2*h^3*q1*q3, h^3*q2^2 - h^3*q1*q3, h^2*q2*q3, h*q3^2], 8: [h^3*q2*q3, h^2*q3^2], 9: [h^3*q3^2]}
            sage: PG.additive_basis()[1]
            {0: [1], 1: [q1, h], 2: [q2, q1^2, h*q1, h^2], 3: [-q1*q2 + 2*q3, q1*q2 - q3, h*q2, h*q1^2, h^2*q1, h^3], 4: [-q2^2 + 2*q1*q3, q2^2 - q1*q3, -h*q1*q2 + 2*h*q3, h*q1*q2 - h*q3, h^2*q2, h^2*q1^2, h^3*q1], 5: [q2*q3, -h*q2^2 + 2*h*q1*q3, h*q2^2 - h*q1*q3, -h^2*q1*q2 + 2*h^2*q3, h^2*q1*q2 - h^2*q3, h^3*q2, h^3*q1^2], 6: [q3^2, h*q2*q3, -h^2*q2^2 + 2*h^2*q1*q3, h^2*q2^2 - h^2*q1*q3, -h^3*q1*q2 + 2*h^3*q3, h^3*q1*q2 - h^3*q3], 7: [h*q3^2, h^2*q2*q3, -h^3*q2^2 + 2*h^3*q1*q3, h^3*q2^2 - h^3*q1*q3], 8: [h^2*q3^2, h^3*q2*q3], 9: [h^3*q3^2]}
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
        Returns the projection morphism from this product variety to the i-th variety.
        
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
            A morphism between A projective space of dimension 2 and A projective space of dimension 5
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
        return "A morphism between %s and %s"%(self._V1, self._V2)

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
            return arg(tuple(self._upperstar))

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
        Returns the excess bundle of this morphism associate to another vector bundle on the variety target.
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
            sage: L = Q.O(4*H)
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

############################################################################################

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

####################################################################################

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
            A bundle section of A vector bundle of rank 1 on A projective space of dimension 3
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
    Makes a variety object which is the blowup of the target of a inclusion along
    its source (here E is the exceptional divisor).
    
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
            The blowup of A projective space of dimension 5 along A projective space of dimension 2
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

#######################################################################
########## EXAMPLES ###################################################
#######################################################################

def line(n): #compute the number of lines on a general hypersurface
    d = 2*n-3 #degree of hypersurface
    G = Grassmannian(2,n+1)
    S = G.tautological_subbundle().dual()
    B = S.symmetric_power(d)
    return G.integral(B.top_chern_class())

def linear_subspace(k,d,n): #compute the number of linear subspaces on a general hypersurface
    if d < 3:
        raise ValueError("This must be satisfied")
    if binomial(d+k,k) != (k+1)*(n-k):
        raise ValueError("This must be satisfied")
    G = Grassmannian(k+1,n+1)
    S = G.tautological_subbundle().dual()
    B = S.symmetric_power(d)
    return G.integral(B.top_chern_class())

def conics_quintic_threefold(): #compute the number of conics on a general quintic threefold
    G = Grassmannian(3,5)
    S = G.tautological_subbundle()
    B = S.symmetric_power(2).dual()
    P = ProjectiveBundle(B)
    V = P.O(-1) & S.symmetric_power(3)
    A = S.symmetric_power(5) - V
    return P.integral(A.top_chern_class())

def conics_intersecting_8_lines(): #compute the number of lines intersecting 8 lines in general position
    G = Grassmannian(3,4)
    S = G.tautological_subbundle()
    B = S.symmetric_power(2).dual()
    P = ProjectiveBundle(B)
    v = P.variables()
    c = 2*v[1]+v[0]
    return P.integral(c**8)
