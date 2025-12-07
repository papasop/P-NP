\begin{definition}[Energy Function]
For a CNF formula $\Phi_n$ over $n$ Boolean variables, the energy of an
assignment $\sigma \in \{0,1\}^n$ is defined as
\[
E_{\Phi_n}(\sigma)
  := \#\{ C \in \Phi_n \mid \sigma \not\models C \}.
\]
\end{definition}

\begin{definition}[Configuration Graph]
The configuration graph $\mathcal{G}_n$ is the $n$-dimensional Boolean
hypercube, where two assignments are adjacent iff they differ in exactly
one variable.
\end{definition}

\begin{definition}[Energy Barrier]
Let $S_0(n) \subseteq \{0,1\}^n$ be a ``low–energy region'' such as
\[
S_0(n) := \{ \sigma \mid E_{\Phi_n}(\sigma) \le c_0 n \}.
\]
We say that $\Phi_n$ has an \emph{energy barrier} of height $B(n)$ if
for every path
\[
\sigma_0 \to \sigma_1 \to \cdots \to \sigma_T
\]
in $\mathcal{G}_n$ with $\sigma_0 \in S_0(n)$ and
$\sigma_T \in \SAT(\Phi_n)$, there exists some $t$ such that
\[
E_{\Phi_n}(\sigma_t) \;\ge\; B(n).
\]
\end{definition}

\begin{conjecture}[Hard Energy Landscape Hypothesis (H-ELH)]
There exists a family of 3-SAT formulas $\{\Phi_n\}_{n\ge1}$ and a
super-polynomial function $B(n)$ such that each $\Phi_n$ has an energy
barrier of height at least $B(n)$.
\end{conjecture}

