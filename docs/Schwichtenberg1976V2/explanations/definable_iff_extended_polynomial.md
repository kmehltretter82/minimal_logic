We prove Schwichtenberg's definability theorem. For $f:\mathbb N^k\to\mathbb N$,

$$f \text{ is } \lambda\text{-definable over } \nu \iff f \text{ is an extended polynomial} \iff f \text{ is a piecewise polynomial},$$

where *piecewise polynomial* means: for every zero/non-zero pattern $\sigma$ of the arguments there is a polynomial $P_\sigma$ with $f(v)=P_\sigma(v)$ whenever $v$ has pattern $\sigma$.

**Piecewise ⇔ extended.**

- *(⇒)* On a fixed pattern, a polynomial with natural coefficients is either identically $0$ or nowhere $0$. So every conditional $d(f,g,h)$ selects a fixed branch, and polynomials are closed under substitution of polynomials. Induction on extended polynomials then gives the claim.
- *(⇐)* Free the argument positions one at a time. If $f$ is an extended polynomial $E_0$ where $v_j=0$ and $E_1$ where $v_j\neq0$, then $f=d(E_0,E_1,v_j)$ there.

**Extended ⇒ definable** is the sufficiency part of the first milestone.

**Definable ⇒ piecewise.** Instead of normal forms, we use a set-theoretic semantics together with a Kripke logical relation. This avoids proving normalization or confluence.

*Semantics.* Interpret $0$ as $\mathbb N$ and $\sigma\to\tau$ as the set of functions. Reduction preserves typing and meaning: a substitution lemma covers the capture-avoiding renaming in `substTerm`, and $\alpha$-conversion is sound. Hence, if $t$ defines $f$,

$$f(v)=[\![t]\!]\big(\bar v_1,\dots,\bar v_k\big)(\mathrm{succ})(0).$$

*The relation.* Fix a pattern $\sigma$. A family is a value depending on the input $v$ (with pattern $\sigma$) and on values $\zeta:\mathbb N\to\mathbb N$ of formal variables of type $0$. At world $n$:

- $R^0_n(a)$ holds iff, for a polynomial $P$, either $a(\zeta,v)=P(v)+\zeta_j$ for some $j<n$, or $a(\zeta,v)=P(v)$.
- $R^{\rho\to\tau}_n(g)$ holds iff $g$ does not depend on $\zeta_j$ for $j\ge n$, and $g$ maps $R^\rho_m$ into $R^\tau_m$ for all $m\ge n$.

The fundamental lemma follows by induction on typing: every typed term with related free variables is related.

*Probe lemma.* Apply a related $g:0\to0$ at world $m$ to the fresh formal variable $\zeta_m$. Then $g$ is a translation $x\mapsto Q(v)+x$ or a constant.

*Numerals are related.* Iterating a translation $v_i$ times adds $v_i\cdot Q(v)$, which is again polynomial. A constant iterated $v_i$ times stays constant when $v_i\ne0$ and gives the identity when $v_i=0$, and the pattern $\sigma$ fixes which case occurs.

*Conclusion.* Applying the relation of $[\![t]\!]$ to the numerals, $\mathrm{succ}$, and $\zeta_0$ yields a family $P(v)+\zeta_0$ or $P(v)$. Setting $\zeta=0$ gives $f(v)=P(v)$ on the pattern $\sigma$.

The proof is constructive: it uses no choice principle, only `propext` and `Quot.sound`.
