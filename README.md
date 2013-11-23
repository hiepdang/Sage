The first package for computations in intersection theory and enumerative 
geometry is Schubert in Maple which written by Sheldon Katz and Stein A. Stromme
from 1992, and had been revised and updated to new versions of Maple by 
Jan-Magnus Okland. However, it is no longer actively supported. 
The second package is Schubert2 in Macaulay2 which has being developed by 
Daniel R. Grayson, Michael E. Stillman, Stein A. Str\o mme, David Eisenbud and 
Charley Crissman.

Our package is Schubert3 which developed on Sage and written in the Python 
programming language. This package provides the key functionality necessary for 
computations in intersection theory and enumerative geometry. It deals with 
abstract varieties, vector bundles on abstract varieties, morphisms between 
abstract varieties, equivariant vector bundles on abstract varieties endowed 
with a torus action, moduli spaces of stable maps, and graphs.

In order to use Schubert3, we first must attach the file Schubert3.py to a 
running session using the %attach command in Sage as follows:

    sage: %attach ~/Schubert3.py

The current version of this package is the result of many discussions on 
mathematical background and on implementation algorithms, and of many hours of 
coding. It should not be considered a complete, unchangeable, totally stable 
version. We will keep working on this project by fixing bugs, improving 
algorithms, and by adding functionalities.
