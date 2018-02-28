def sym(k,l):
	if k < 0 or k > len(l):
		return 0
	elif k == 0:
		return 1
	else:
		S = Set([i for i in range(len(l))])
		F = S.subsets(k).list()
		return sum(prod(l[i] for i in p) for p in F)

def algDeg(m,n,r):
	k = m - binomial(n-r+1,2)
	l = binomial(n+1,2) - m - binomial(r+1,2)
	if k < 0 or l < 0:
		return "invalid data"
	else:
		S = Set([i for i in range(n)])
		F = S.subsets(r).list()
		V = IntegerVectors(2,r)
		W = IntegerVectors(2,n-r)
		result = 0
		for I in F:
			Ic = S - I
			q = [sum(e[i]*Ic[i] for i in range(n-r)) for e in W]
			M1 = matrix(ZZ,k,k)
			for i in range(k):
				for j in range(k):
					M1[i,j] = sym(1+j-i,q)
			s1 = det(M1)
			s = [sum(e[i]*I[i] for i in range(r)) for e in V]
			M2 = matrix(ZZ,l,l)
			for i in range(l):
				for j in range(l):
					M2[i,j] = sym(1+j-i,s)
			s2 = det(M2)
			t = prod(j-i for i in I for j in Ic)
			result = result + (-1)**l*s1*s2/t
		return result