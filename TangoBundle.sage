%attach Dropbox/Sage/Schubert3.py

def TangoBundlePn(n):
    """
        Construct the Tango bundle on P^n.
    """
    P = ProjectiveSpace(n)
    T = P.tangent_bundle()
    L = P.O(0)
    F = L^binomial(n+1,2) - (T & P.O(-2))
    E = F - L^(binomial(n,2)-n+1)
    return E

def EulerCharPn(n):
    """
        Return the Euler characteristic of the Tango bundle on P^n.
    """
    return TangoBundlePn(n).chi()
