"""
A toy implementation of the bar complex based on BP
"""
import sage.all
from sage.structure.sage_object import SageObject
from sage.structure.parent import Parent
from sage.misc.cachefunc import cached_method
from sage.rings.finite_rings.integer_mod_ring import IntegerModRing
from sage.modules.with_basis.morphism import ModuleMorphismByLinearity
from sage.misc.lazy_attribute import lazy_attribute
from sage.structure.unique_representation import UniqueRepresentation
from sage.rings.rational_field import QQ
from sage.combinat.free_module import CombinatorialFreeModule
from sage.categories.algebras_with_basis import AlgebrasWithBasis
from sage.matrix.constructor import Matrix
from itertools import zip_longest

class BasisEnumeratorTables(Parent,UniqueRepresentation):

    @staticmethod
    def __classcall__(cls,weights):
        return super(cls,BasisEnumeratorTables).__classcall__(cls,tuple(weights))

    def __init__(self,weights):
        self.weights = weights
        self.maxdim = -1

    def _repr_(self):
        return "enumerator for partitions with weights %s" % (self.weights,)
    
    def tables(self,dim):
        if self.maxdim<dim:
            # anticipate a few extra dimensions
            extradims = 2*max([0,]+list(self.weights))
            self.make_tables(dim+extradims)
        return self.dimtab,self.seqtab
        
    def make_tables(self,maxdim):
        # TODO: re-use the information that is already present
        self.maxdim = maxdim
        # dimtab[k][dim] = dimension after restriction to weights[0,...,k]
        self.dimtab = []
        for (idx,w) in enumerate(self.weights):
            dims = []
            for dim in range(maxdim+1):
                cnt,cf = 0,0
                while cf<=dim:
                    cnt += self._dimension(dim-cf,idx)
                    cf += w
                dims.append(cnt)
            self.dimtab.append(dims)
        
        self.seqtab = []
        self.seqtab.append( [0,] ) # this is all we need from seqtab[0][...]
        # seqtab[k+1][n] = dimtab[k][n-d] + dimtab[k][n-2d] + ... + dimtab[k][n%d]
        for (k,d) in enumerate(self.weights[1:]):
            stab = []
            for dim in range(maxdim+1):
                stab.append(sum(self.dimtab[k][dim-j*d] for j in range(1,(dim//d)+1)))
            self.seqtab.append(stab)
        
    def dimension(self,dim,idx=None):
        """
        TESTS::

            sage: len(BasisEnumerator((),0))
            1
        """
        if idx is None:
            idx = len(self.weights)
            if idx == 0:
                return 0 if dim else 1
        dt,_ = self.tables(dim)
        return dt[idx-1][dim]
        
    def _dimension(self,dim,idx):
        if idx<1:
            return 1 if dim==0 else 0
        return self.dimtab[idx-1][dim]

class BasisEnumerator(Parent,UniqueRepresentation):

    @staticmethod
    def __classcall__(cls,weights,dim):
        return super(cls,BasisEnumerator).__classcall__(cls,tuple(weights),dim)

    def __init__(self,weights,dim):
        self.tabs = BasisEnumeratorTables(weights)
        self.weights = weights
        self.dim = dim

    def _repr_(self):
        """
        TESTS::

            sage: B = BasisEnumerator((8,2,3),17) ; B
            enumerator for partitions with weights (8, 2, 3) in dimension 17
            sage: C = BasisEnumerator((8,2,3),5)
            sage: B.tabs is C.tabs
            True
            sage: len(B) == len(list(B))
            True
            sage: list(C)
            [(0, 1, 1)]
        """
        return "%s in dimension %d" % (self.tabs,self.dim)

    def __len__(self):
        return self.tabs.dimension(self.dim)

    def __getitem__(self,elem):
        """
        compute the sequence number of a partition
        """
        return self.seqno(elem)

    def seqno(self,elem):
        """
        Sequence number of an element of the basis::

            sage: B = BasisEnumerator((13,2,5,3),47) 
            sage: len(B)
            84
            sage: for (idx,elem) in enumerate(B):
            ....:    assert idx == B.seqno(elem)
        """
        cnt = 0
        _,seqtab = self.tabs.tables(self.dim)
        w = self.weights
        n = len(w)
        dim = self.dim
        for i in range(n):
            idx = n-i-1
            d = w[idx]
            actdeg = elem[idx] * d
            cnt += seqtab[idx][dim-actdeg]
            dim -= actdeg
        return cnt

    class Iterator(SageObject):
        """
        TESTS::

            sage: for w in ((7,3,2,3), (3,4), (9,1,1)):
            ....:     B = BasisEnumerator(w,30)
            ....:     for (num,x) in enumerate(B):
            ....:         assert B[x] == num
            ....:         assert sum(e*_ for (e,_) in zip(x,w))==30
            ....:     assert num+1 == B.__len__()
            sage: # test empty enumerator
            sage: C = BasisEnumerator((),1)
            sage: len(C), list(C)
            (0, [])
        """

        def __init__(self,par):
            self.be = par
            self.rem = -1
            self.e = []

        def first(self):
            w = self.be.weights
            self.e = [0 for _ in w]
            n = len(w)
            dim = self.be.dim
            for i in range(n):
                idx = n-i-1
                v = dim//w[idx]
                self.e[idx] = v
                dim = dim - w[n-i-1]*v
            self.rem = dim
            
        def __next__(self):
            """
            TESTS::

                sage: B = BasisEnumerator((4,),12) 
                sage: list(B)
                [(3,)]
            """
            #print "rem=%d, e=%s" % (self.rem,self.e)
            if self.rem<0:
                self.first()
                if 0==self.rem:
                    return tuple(self.e)
            # find first non-zero coefficient and diminish by one
            # then redistribute its weight to the lower slots
            w = self.be.weights
            dim = self.rem
            e = 0
            for (n,(e,d)) in enumerate(zip(self.e[1:],w[1:])):
                if e>0:
                    dim += d
                    self.e[n+1] -= 1
                    break
            if e==0:
                raise StopIteration
            dim += self.e[0]*w[0]
            for i in range(n+1):
                idx = n-i
                d = w[idx]
                #print "at %d to distribute=%d" % (idx,dim)
                v = dim//d
                self.e[idx] = v
                dim = dim - d*v
            self.rem = dim
            #print "data=%s remaining %d" % (tuple(self.e),dim)
            if self.rem>0:
                return next(self)
            return tuple(self.e)

    def __iter__(self):
        return BasisEnumerator.Iterator(self)

class BPBarBase(CombinatorialFreeModule):

    def __init__(self,p,base_ring,flavour,ideal):
        """
        TESTS::

            sage: X = BPBar(3,QQ) ; X
            Bar complex for BP with coefficients in Rational Field at prime 3
            sage: X is BPBar(3,QQ)
            True
            sage: BPBar(2,IntegerModRing(64))
            Bar complex for BP with coefficients in Ring of integers modulo 64 at prime 2
        """
        self.flavour = flavour
        self.prime = p
        CombinatorialFreeModule.__init__(self,base_ring,(),category=AlgebrasWithBasis(base_ring))
        self._assign_names(names=[flavour,"t"])
        self._print_options['latex_scalar_mult'] = '\\cdot{}'

    class GenFamily(SageObject):
        def __init__(self,owner,varname,idx):
            self.var = varname
            self.idx = idx
            self.owner = owner

        def _repr_(self):
            """
            TESTS::

                sage: X = BPBar(3,QQ)
                sage: X.inject_variables()
                Defining v, t
                sage: v
                v-family of generators of Bar complex for BP with coefficients in Rational Field at prime 3
                sage: t
                t-family of generators of Bar complex for BP with coefficients in Rational Field at prime 3
                sage: v[4]*t[2]*t[1]**5
                v4*t1**5*t2
            """
            return "%s-family of generators of %s" % (self.var,self.owner)

        def __getitem__(self,idx):
            if idx == 0:
                return self.owner.one()
            if idx>0:
                key = tuple([0,]*(idx-1)+[1,])
                if self.idx == 0:
                    return self.owner.monomial((key,))
                else:
                    return self.owner.monomial(((),key))

    def gens(self):
        gf = BPBarBase.GenFamily
        return (gf(self,self.flavour,0), gf(self,"t",1))

    def _repr_term(self,key):
        """
        TESTS::

            sage: X = BPBar(3,QQ)
            sage: X.monomial(((0,1,2),(2,1),(0,1),(),(0,0,2)))
            v2*v3**2*t1**2*t2|t2|1|t3**2
            sage: X.monomial(((0,1),))
            v2
            sage: X.monomial(((),(0,1)))
            t2
            sage: X.monomial(((),(),(0,1)))
            1|t2
            sage: Y = HBPBar(5,GF(5))
            sage: Y.monomial(((0,3),(1,),(),(0,1)))
            m2**3*t1|1|t2
        """
        # keys are tuples (v,t1,t2,...)
        if len(key) == 0:
            return "1"
        vpart = self._repr_mono(self.flavour,key[0],'')
        tpart = [self._repr_mono('t',k,'1' if idx>0 else '') for (idx,k) in enumerate(key[1:])]
        if len(vpart) and len(tpart) and len(tpart[0]):
            vpart += "*"
        elif vpart == "" and len(tpart) and tpart[0]=="":
            vpart = "1"
        return vpart + "|".join(tpart)
        
    def _latex_term(self,key):
        """
        TESTS::

            sage: X = BPBar(3,QQ)
            sage: latex(X.monomial(((0,1,2),(2,1),(0,1),(),(0,0,2))))
            v_{2}v_{3}^{2}t_{1}^{2}t_{2}\vert{}t_{2}\vert{}1\vert{}t_{3}^{2}
            sage: latex(X.monomial(((0,1),)))
            v_{2}
            sage: latex(2*X.monomial(((),(0,1))))
            2\cdot{}t_{2}
            sage: latex(2*X.monomial(((),(),(0,1))))
            2\cdot{}1\vert{}t_{2}
            sage: Y = HBPBar(5,GF(5))
            sage: latex(Y.monomial(((0,3),(1,),(),(0,1))))
            m_{2}^{3}t_{1}\vert{}1\vert{}t_{2}

        """
        # keys are tuples (v,t1,t2,...)
        if len(key) == 0:
            return "1"
        vpart = self._latex_mono(self.flavour,key[0],'')
        tpart = [self._latex_mono('t',k,'1' if idx>0 else '') for (idx,k) in enumerate(key[1:])]
        if vpart == "" and len(tpart) and tpart[0]=="":
            vpart = "1"
        return vpart + "\\vert{}".join(tpart)
        
    def _repr_mono(self,char,exponents,onevalue='1'):
        genpow = lambda e,idx : "%s%d" % (char,idx) if 1==e else "%s%d**%d" % (char,idx,e)
        ans = [genpow(e,idx+1) for (idx,e) in enumerate(exponents) if e>0]
        if len(ans)==0:
            return onevalue
        return "*".join(ans)

    def _latex_mono(self,char,exponents,onevalue='1'):
        genpow = lambda e,idx : "%s_{%d}" % (char,idx) if 1==e else "%s_{%d}^{%d}" % (char,idx,e)
        ans = [genpow(e,idx+1) for (idx,e) in enumerate(exponents) if e>0]
        if len(ans)==0:
            return onevalue
        return "".join(ans)

    def one(self):
        """
        TESTS::

            sage: HBPBar(7,GF(5)).one()
            1
        """
        return self.monomial(())

    def product_key(self,a,b):
        return tuple(x+y for (x,y) in zip_longest(a,b,fillvalue=0))

    def product_on_basis(self,key1,key2):
        """
        TESTS::

            sage: X = BPBar(5,QQ)
            sage: a = X.monomial(((1,3),)) ; a
            v1*v2**3
            sage: b = X.monomial(((0,3,1),)) ; b
            v2**3*v3
            sage: c = X.monomial(((),(0,1))) ; c
            t2
            sage: d = X.monomial(((0,1),(),(0,0,1))) ; d
            v2|t3
            sage: lst = [a,b,c,d]
            sage: matrix([[x*y for x in lst] for y in lst])
            [v1**2*v2**6 v1*v2**6*v3 v1*v2**3*t2 v1*v2**4|t3]
            [v1*v2**6*v3 v2**6*v3**2 v2**3*v3*t2 v2**4*v3|t3]
            [v1*v2**3*t2 v2**3*v3*t2       t2**2    v2*t2|t3]
            [v1*v2**4|t3 v2**4*v3|t3    v2*t2|t3 v2**2|t3**2]
        """
        return self.monomial(tuple(self.product_key(a,b) for (a,b) in zip_longest(key1,key2,fillvalue=())))

    class MultiplicativeMorphism(ModuleMorphismByLinearity):

        def __init__(self,domain=None,codomain=None,gen_map=None):
            self.gen_map = gen_map
            ModuleMorphismByLinearity.__init__(self,domain=domain,codomain=codomain,on_basis=self.on_basis)

        def on_basis(self,key):
            cod = self.codomain()
            ans = cod.one()
            for (idx1,k) in enumerate(key):
                for (idx2,e) in enumerate(k):
                    if e>0:
                        ans = cod.product(ans,self.gen_power(idx1,idx2,e))
                        if ans.is_zero():
                            return ans
            return ans

        @cached_method
        def gen_power(self,idx1,idx2,pow):
            pow = int(pow)
            cod = self.codomain()
            if pow==0:
                return cod.one()
            elif pow==1:
                return self.gen_map(idx1,idx2)
            elif pow&1 == 0:
                ans = self.gen_power(idx1,idx2,pow/2)
                return cod.product(ans,ans)
            return cod.product(self.gen_power(idx1,idx2,pow-1),self.gen_map(idx1,idx2))

    def multiplicative_morphism(self,domain = None, codomain=None,gen_map=None):
        if domain is None:
            domain = self
        if codomain is None:
            codomain = domain
        return BPBarBase.MultiplicativeMorphism(domain=self,codomain=codomain,gen_map=gen_map)

    def genpow(self,idx1,idx2,exp=1):
        if idx2==0:
            return self.one()
        k = tuple([0,]*(idx2-1) + [exp,])
        return self.monomial(tuple( [(),]*(idx1) + [k,] ))

    @cached_method
    def etaR_map(self):
        return self.multiplicative_morphism(gen_map=self._etaR)

    def etaR(self,x):
        return self.etaR_map()(x)

    @cached_method
    def Delta_map(self,k):
        """
        On spectra, the map that inserts a '1' in the k-th position.
        For k=0 this is the right unit map, otherwise the coproduct in the k-th bar factor
        """
        return self.multiplicative_morphism(gen_map=lambda i1,i2: self._delta_map(k,i1,i2))

    def Delta(self,x,idx=1):
        return self.Delta_map(idx)(x)

    def product_multiple(self,*args):
        k=-1
        for (k,x) in enumerate(*args):
            if 0==k:
                ans = x
            else:
                ans = self.product(ans,x)
        if k<0:
            return self.one()
        return ans

    def bar_basis(self,length,dimension):
        return BarBasis(self,length,dimension)

    @cached_method
    def differential(self,k):
        return self.module_morphism(codomain=self, function=lambda x:self._differential(k,x))

    def _differential(self,k,x):
        """
        TESTS::

            sage: Z = BPBar(2,QQ)
            sage: v,t = Z.gens()
            sage: e = Z.etaR
            sage: g = e(e(t[1])) ; g
            1|1|t1
            sage: Z.differential(3)(g)
            0
        """
        return self.sum( (-1)**j * self.Delta(x,j) for j in range(k+2))

    def matrix_differential(self,sdeg,dim,sparse=False):
        """
        Computes the transposed matrix of the differential
        """
        srcbasis = self.bar_basis(sdeg,dim)
        dstbasis = self.bar_basis(sdeg+1,dim)
        diff = self.differential(sdeg)
        ans = matrix(self.base_ring(),len(srcbasis),len(dstbasis),sparse=sparse)
        for (row,x) in enumerate(srcbasis):
            y = diff(x)
            for (col,cf) in dstbasis.seqno(y):
                ans[row,col] += cf
        return ans

    def Ext_smith(self,sdeg,dim,withcocycle=False):
        """
        Compute the matrix of the differential (sdeg-1) -> sdeg in dimension dim.
        Use the Smith normal form to find x such that d(x) is divisible by a non-trivial
        power q of the base prime p. The d(x)/q form a basis of Ext^{sdeg,dim}.

        Note this does not work with most base rings, but QQ is fine.

        TESTS::

            sage: X=BPBar(2)
            sage: for (cf,orig,cycle) in X.Ext_smith(2,10,withcocycle=True):
            ....:     print("  generator with order %d" % cf)
            generator with order 2
            generator with order 2
            sage: print(orig)   # random
            -4*t1**2*t2 + v1*v2*t1 - v1**2*t2 - v1**2*t1**3
            sage: print(cycle)  # random
            2*t2|t1**2 + 4*t1|t1*t2 + 2*t1|t1**4 + 18*t1*t2|t1 + 2*t1**2|t1**3 + 2*t1**2*t2 + 2*t1**3|t1**2 + 4*t1**4|t1 - v2*t1|t1 - 7*v1*t2|t1 + 2*v1*t1|t2 + 4*v1*t1|t1**3 + 4*v1*t1**2|t1**2 - 13*v1*t1**3|t1 - 1/2*v1*v2*t1 + 1/2*v1**2*t2 + 2*v1**2*t1|t1**2 + 11*v1**2*t1**2|t1 + 1/2*v1**2*t1**3 - v1**3*t1|t1

        """
        p = self.prime
        Zp = IntegerModRing(p)
        m = self.matrix_differential(sdeg-1,dim)
        srcbasis = self.bar_basis(sdeg-1,dim)
        #dstbasis = self.bar_basis(sdeg,dim)
        d,u,v = m.smith_form(integral=True)
        # now d = diagonal matrix = u * m * v with u, v integral and invertible
        for (k,cf) in enumerate(d.diagonal()):
            if cf != 0 and Zp(cf) == 0:
                # we have cf * v^{-T}(e_k) = diff(u^T(e_k)), so v^{-T}(e_k) is a non-trivial cohomology class
                #FIXME: we should remove coefficients from "origin" that are divisible by cf to get smaller formulas
                origin = self.linear_combination(list(zip(srcbasis,u.row(k))))
                # cocycle = self.linear_combination(zip(dstbasis,vinv.row(k))) - (but we' don't have vinv)
                cocycle = None if not withcocycle else self.differential(sdeg-1)(origin)/cf
                yield cf,origin,cocycle

    def __call__(self,x):
        if isinstance(x.parent(),BPBarBase):
            return self._from_dict(dict(x),coerce=True, remove_zeros=True)
        return super(BPBarBase,self).__call__(x)

    class Element(CombinatorialFreeModule.Element):
        pass

class ArakiGens(UniqueRepresentation, SageObject):
    """
    This class knows about Araki generators. It uses the QQ-based bar complexes to 
    compute etaR and Delta. The bar complexes for other coefficients use the 
    ArakiGens class to compute their structure maps.

    This class also knows how to map the m[k] to the v[k] and vice-versa.
    """

    def __init__(self,p):
        self.prime = p
        self.BP = BPBar(p,QQ)
        self.HBP = HBPBar(p,QQ)

    def _repr_(self):
        return "Araki generator factory for the prime %d" % self.prime

    @cached_method
    def mapv2m(self):
        """
        TESTS::

            sage: A=ArakiGens(3)
            sage: v2m = A.mapv2m()
            sage: m2v = A.mapm2v()
            sage: v2m.domain().inject_variables()
            Defining v, t
            sage: for i in range(4):
            ....:     x = v[i]
            ....:     y = v2m(x)
            ....:     z = m2v(y)
            ....:     print( "%s -> %s -> %s" % (x,y,z))
            1 -> 1 -> 1
            v1 -> -24*m1 -> v1
            v2 -> -19680*m2 + 13824*m1**4 -> v2
            v3 -> -7625597484984*m3 + 7622111232000*m1*m2**3 - 16062205132800*m1**5*m2**2 + 13924527243264*m1**9*m2 - 2641807540224*m1**13 -> v3
            sage: for i in range(6):
            ....:     assert t[i] == m2v(v2m(t[i]))
        """
        return self.BP.multiplicative_morphism(codomain=self.HBP,gen_map=self.v2m)

    @cached_method
    def mapm2v(self):
        return self.HBP.multiplicative_morphism(codomain=self.BP,gen_map=self.m2v)

    @cached_method
    def etaR(self):
        return self.BP.multiplicative_morphism(codomain=self.BP,gen_map=self._etaR)
    
    def _etaR(self,idx1,idx2):
        if idx1>0:
            # on the tk eta_R shifts the idx by one
            k = tuple([0,]*idx2 + [1,])
            return self.BP.monomial(tuple( [(),]*(1+idx1) + [k,] ))
        m = self.v2m(idx1,idx2)
        e = self.HBP.etaR(m)
        return self.mapm2v()(e)


    # FIXME: we probably use one redundant, expensive cache
    @cached_method
    def Delta_map(self,k):
        return self.BP.multiplicative_morphism(codomain=self.BP,gen_map=lambda i1,i2: self._delta(k,i1,i2))

    def _delta(self,k,idx1,idx2):
        """
        Compute Delta_k on HBP and transport the result back to BP
        """
        return self.mapm2v()(self.HBP.Delta_map(k)(self.v2m(idx1,idx2)))

    def v2m(self,idx1,idx2):
        """
        """
        if idx1!=0:
            k = tuple([0,]*idx2 + [1,])
            return self.HBP.monomial(tuple( [(),]*(idx1) + [k,] )) 
        # compute v_{idx2+1} as a polynomial in m_k using
        #  p*m[n] = v[n] + m[1]*v[n-1]**p + ... + m[n]*p**(p**n)
        m,_ = self.HBP.gens()
        p = self.prime
        ppow = 1
        idx2 += 1
        ans = []
        for i in range(1,idx2+1):
            ppow *= p
            ans.append( -m[i]*self.v2m(0,idx2-i-1)**ppow )
        ans.append( (p-p**(ppow)) * m[idx2] )
        return self.HBP.sum(ans)

    def m2v(self,idx1,idx2):
        if idx1!=0:
            k = tuple([0,]*idx2 + [1,])
            return self.BP.monomial(tuple( [(),]*(idx1) + [k,] )) 
        v,_ = self.BP.gens()
        p = self.prime
        ppow = p
        idx2 += 1
        ans = [v[idx2],]
        for i in range(1,idx2):
            ans.append( self.m2v(0,i-1) *v[idx2-i]**ppow )
            ppow *= p
        return self.BP.sum(ans) / (p-p**ppow)

class BarBasis(Parent, UniqueRepresentation):

    def __init__(self,obj,len,dim):
        self.bar = obj
        self.len = len
        self.dim = dim

        p = obj.prime
        wgts = []
        for n in range(1,100):
            deg = 2*(p**n-1)
            if deg>dim:
                break
            wgts.append(deg)

        indices = []
        weights = []
        monomials = []
        for idx in range(len+1):
            #FIXME: for idx=0 we need to take the ideals In into account
            k = [(),]*idx
            l = []
            for (i,w) in enumerate(wgts):
                indices.append((idx,i))
                weights.append(w)
                monomials.append(obj.monomial(tuple(k + [tuple(l+[1,]),])))
                l.append(0)
        
        self.basis = BasisEnumerator(weights,dim)
        self.indices = indices
        self.monomials = monomials

        if False:
            print("basis=",self.basis)
            print("indices=",self.indices)
            print("monomials=",self.monomials)

    def _repr_(self):
        return "Basis of %s in dimension %d, length %d" % (self.bar,self.dim,self.len)

    def __len__(self):
        return len(self.basis)

    def seqno(self,x):
        for (key,cf) in x.monomial_coefficients().items():
            yield self.seqno_key(key),cf

    def seqno_key(self,key):
        expos = []
        for (idx1,idx2) in self.indices:
            try:
                e = key[idx1][idx2]
            except IndexError:
                e = 0
            expos.append(e)
        return self.basis[expos]
            
    class Iterator(SageObject):

        def __init__(self,bb):
            self.bb = bb
            self.basis = iter(bb.basis)

        def __next__(self):
            expos = next(self.basis)
            return self.bb.bar.product_multiple(x**e for (x,e) in zip(self.bb.monomials,expos))

    def __iter__(self):
        return BarBasis.Iterator(self)

class BPBar(BPBarBase):
    """
    The homotopy of smash powers of BP
    """

    @staticmethod
    def __classcall__(self,p,base_ring=None,ideal=None):
        if base_ring is None:
            base_ring = QQ
        if ideal is None:
            ideal = -1
        return super(BPBar,self).__classcall__(self,p,base_ring,ideal)

    def __init__(self,p,base_ring=QQ,ideal=None):
        """
        TESTS::

            sage: X = BPBar(3,QQ) ; X
            Bar complex for BP with coefficients in Rational Field at prime 3
            sage: X is BPBar(3,QQ)
            True
            sage: BPBar(2,IntegerModRing(64))
            Bar complex for BP with coefficients in Ring of integers modulo 64 at prime 2
        """
        BPBarBase.__init__(self,p,base_ring,'v',ideal)

    @lazy_attribute
    def _araki(self):
        return ArakiGens(self.prime)

    def _repr_(self):
        return "Bar complex for BP with coefficients in %s at prime %d" % (self.base_ring(), self.prime)

    def _etaR(self,idx1,idx2):
        """
        TESTS::

            sage: X=BPBar(3,IntegerModRing(3**2))
            sage: X.inject_variables()
            Defining v, t
            sage: for i in range(3):
            ....:     print(X.etaR(v[i]))
            1
            3*t1 + v1
            3*t2 + v2 + v1*t1**3 + 5*v1**3*t1
        """
        if idx1==0:
            # compute result with QQ coefficients on the Araki class, then cast to self
            return self(self._araki._etaR(idx1,idx2))
        # on the tk eta_R shifts the idx by one
        k = tuple([0,]*idx2 + [1,])
        return self.monomial(tuple( [(),]*(1+idx1) + [k,] )) 
 
    @cached_method
    def Delta_map(self,k):
        """
        On spectra, the map that inserts a '1' in the k-th position.
        For k=0 this is the right unit map, otherwise the coproduct in the k-th bar factor
        """
        d = self._araki.Delta_map(k)
        BPQ = d.domain()
        return self.module_morphism(codomain=self,on_basis = lambda k : self(d(BPQ.monomial(k))))

class HBPBar(BPBarBase):
    """
    The homology of smash powers of BP
    """

    @staticmethod
    def __classcall__(self,p,base_ring=None,ideal=None):
        if base_ring is None:
            base_ring = QQ
        if ideal is None:
            ideal = -1
        return super(HBPBar,self).__classcall__(self,p,base_ring,ideal)

    def __init__(self,p,base_ring=QQ,ideal=None):
        """
        TESTS::

            sage: X = HBPBar(3,QQ) ; X
            Homology bar complex for BP with coefficients in Rational Field at prime 3
            sage: X is HBPBar(3,QQ)
            True
            sage: HBPBar(2,IntegerModRing(64))
            Homology bar complex for BP with coefficients in Ring of integers modulo 64 at prime 2

        """
        BPBarBase.__init__(self,p,base_ring,'m',ideal)
        
    def _repr_(self):
        return "Homology bar complex for BP with coefficients in %s at prime %d" % (self.base_ring(), self.prime)

    def _etaR(self,idx1,idx2):
        """
        TESTS::

            sage: X = HBPBar(3,QQ)
            sage: X.inject_variables()
            Defining m, t
            sage: for i in range(4):
            ....:    print("%s -> %s" % (m[i],X.etaR(m[i])))
            1 -> 1
            m1 -> t1 + m1
            m2 -> t2 + m2 + m1*t1**3
            m3 -> t3 + m3 + m2*t1**9 + m1*t2**3
            sage: X.etaR(m[2]**2)
            t2**2 + 2*m2*t2 + m2**2 + 2*m1*t1**3*t2 + 2*m1*m2*t1**3 + m1**2*t1**6
            sage: X.etaR(t[2])
            1|t2
        """
        m,t = self.gens()
        p = self.prime
        if idx1==0:
            # eta_R(m_n) = \sum_{i+j=n} m_i t_{n-i}^{p^i}
            ans=[]
            ppow = 1
            for i in range(idx2+2):
                j = idx2-i+1
                ans.append( m[i]*t[j]**ppow)
                ppow *= p
            return self.sum(ans)
        # on the tk eta_R shifts the idx by one
        k = tuple([0,]*idx2 + [1,])
        return self.monomial(tuple( [(),]*(1+idx1) + [k,] )) 

    def _delta_map(self,k,idx1,idx2):
        """
        TESTS::

            sage: Y = HBPBar(2,QQ)
            sage: [Y._delta_map(k,3,0) for k in range(5)]
            [1|1|1|t1, 1|1|1|t1, 1|1|1|t1, 1|1|1|t1 + 1|1|t1, 1|1|t1]

        """
        if k==0:
            return self._etaR(idx1,idx2)
        if k==1:
            if idx1 != 1:
                k = tuple([0,]*idx2 + [1,])
                offset = 0 if idx1<1 else 1
                return self.monomial(tuple( [(),]*(offset+idx1) + [k,] ))
            # we need to compute Delta(t[idx+1]). we use
            #    sum_{a+b=n} m[a]*Delta(t[b])**(p**a) = sum_{a+b+c=n} m[a]*t[b]**(p**a)*t[c]**(p**(a+b))
            ans = []
            m,t = self.gens()
            n = idx2+1
            p = self.prime
            ppowa = 1
            for a in range(n+1):
                ppowab = ppowa
                ma = m[a]
                for b in range(n+1-a):
                    c = n-a-b
                    ans.append( m[a]*self.genpow(1,b,ppowa)*self.genpow(2,c,ppowab))
                    ppowab *= p
                ppowa *= p
            ppow = 1
            for a in range(1,n):
                ppow *= p
                ans.append( -m[a] * self._delta_map(1,1,n-a-1)**ppow)
            ans.append(-m[n])
            return self.sum(ans)
        
        if idx1 != k:
            p = tuple([0,]*idx2 + [1,])
            offset = 0 if idx1<k else 1
            return self.monomial(tuple( [(),]*(offset+idx1) + [p,] ))

        Dkmo = self.Delta_map(k-1)
        t = self.genpow(idx1-1,idx2+1)
        return self.etaR(Dkmo(t))

# code for debugging if this file is %attached to sage session
if len([_ for _ in attached_files() if _.find("bpbar.py")]):
    X = BPBar(3,QQ)
    print(X)
    Y = HBPBar(2,QQ)
    print(Y)
    Y.inject_variables()
    for i in range(4):
        print(("%s -> %s" % (m[i],Y.etaR(m[i]))))
    Z = BPBar(2,QQ)