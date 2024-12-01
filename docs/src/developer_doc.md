
# Developer Documentation


## Lattice Index


We will define a lattice $L$ as a hypercube of integers in a $N$-dimensional space
$$
L_{M_1, M_2, \ldots} = \left\{(n_1, n_2, \ldots n_N) \in \mathbb{Z}^N \; |\; n_i \in [-M_i, M_i - 1]  \right\}.
$$
We will omit the subscripts in $L$ to be concise. If we enumerate the lattice points, then
we establish a bijection between $[1, \prod_i^N 2 M_i]$ and $L$. With a slight but convenient 
abuse of notation, we can denote the bijection as $L$. $v = L(i)$ is the $i^{\text{th}}$ lattice point,
and $i = L^{-1}(v)$ is the lattice index of $v$.  This definition will have to be extended, but we will 
do that when the context arises.


Now consider a $N$-dimensional function $f$ discretized on the lattice $L$. 
We can access the value of $f$ on the $i^{\text{th}}$ lattice point $f(L(i))$ 
by offsetting its memory by `i`, so `f[i]` would suffices.



Given a function discretized on a $N$-dimensional lattice, the values of the 
function are stored contiguously in memory as a $1$-D array. To access the 
value on the lattice site 


Consider a $N$-dimensional lattice, which is a (potentially infinite) array of
lattice vectors. To retrieve a lattice vector, one needs to index the array
with some kind of indices. For reasons that will be explained later when the
contexts arise, we choose the lattice index to be the memory offset (index
starts from $1$) of the latex vector (providing that the arrays are
contiguous). If the lattice is $L$, then $v = L(i)$ is the $i^{\mathrm{th}}$
lattice vector in the memory. If one sees $L$ as a bijection between
$\mathbb{N}$ and $\mathbb{R}^3$, then one can invert it to find the memory
location of a vector $i =L^{-1}(v)$. We will see that the lattice indices
behave like modules rather than fields. Conflating the two is a major
(unnecessary) source of software complexity for periodic code.

We will denote a lattice index as $1_L, 2_L$, etc. The number denotes the
memory address, and the $L$ subscript distinguish it from the integers. Let's
denote the module as $\mathbb{L} \cong \mathbb{N}$, and the integer arithmetics are
defined as 
$$
\begin{aligned}
i \pm j &:= L^{-1}(L(i) \pm L(j)), \quad i, j \in \mathbb{L},\\
1_L &:= L^{-1}((0, 0, 0)^T), \quad \text{Identity}\\
a \cdot i &:= L(a \cdot L^{-1}(i)), \quad a \in \mathbb{Z}, i \in \mathbb{L}.
\end{aligned}
$$
In this definition, it is possible for $L(i) \pm L(j)$ to overflow the
lattice. This overflow does represent Physics such as lattice momentum
transfer, so it has to be tracked. This means that $L$ and $L^{-1}$ need to be
extended.


If we have a wavefunction $\psi$ discretized on a lattice $R$ as `psi`, we can
access its value on a site $i$ with `psi[i]`, whose value is $\psi(R(i))$.








<!-- What makes the lattice index different from the natural numbers is the
arithmetics on them, which is what warrants a separate abstraction. There are
two paths towards separating the lattice arithmetics from integer arithmetics:

1) make a new type of integers $1_L, 2_L, \ldots$ on which arithmetics are defined differently. 
2) make a set of new arithmetics $\pm_L$ and write $1 \pm_L 2$. -->
