We prove the first part of Schwichtenberg's characterization (pp. 113–114). It has six parts:

1. Every closed $\beta$-normal term of type $\nu$ is $\alpha$-equivalent to a numeral $\bar n$ or to $\lambda\alpha.\alpha$.
2. `addComb` defines addition.
3. `mulComb` defines multiplication.
4. `constComb c` defines the constant $c$.
5. `condComb` defines the conditional $d(n,m,i)$.
6. Every extended polynomial is $\lambda$-definable.

**Closed normal numerals.** A closed normal term of type $\nu$ is an abstraction $\lambda a.b$ with $a:0\to0$, because a neutral term would have a free head variable. Its body $b$ is normal of type $0\to0$ with free variables among $\{a\}$. The subterm analysis of p. 114, with no $F_i$, gives two cases:

- $b=a$, so the term is $\lambda a.a$;
- $b=\lambda y.\,a^n z$. Here $z=y$, because a free $z$ would have to be $a$, which has the wrong type. Two $\alpha$-renamings turn $\lambda a.\lambda y.a^ny$ into $\bar n$.

**The combinators.** Each is verified by an explicit reduction. The key step is

$$\bar n\,a\,s\ \triangleright\ a^n s.$$

For instance

$$\mathrm{add}\,\bar n\,\bar m\ \triangleright\ \lambda\alpha x.\ \bar n\,\alpha\,(\bar m\,\alpha\,x)\ \triangleright\ \lambda\alpha x.\ \alpha^{n+m}x=\overline{n+m}.$$

Multiplication iterates $\lambda u.\alpha^m u$ $n$ times. The conditional reduces to $\lambda \alpha x.\ \bar\imath\,(\lambda y.\alpha^m x)\,(\alpha^n x)$. When $i=0$ this gives $\alpha^nx$. Otherwise the constant function $\lambda y.\alpha^mx$, applied at least once, gives $\alpha^mx$.

**Sufficiency.** We argue by induction on extended polynomials.

- *Projections* are defined by $\lambda F_1\dots F_k.\,F_i$.
- *Composition* $g(h_1(v),\dots,h_m(v))$ is defined by $\lambda\vec F.\ G\,(H_1\vec F)\dots(H_m\vec F)$, where $G$ and $H_j$ are closed terms defining $g$ and $h_j$.
- *Constants, $+$, $\cdot$ and $d$* are compositions with $\bar c$ (arity $0$) and with the combinators above.

The family $H_1,\dots,H_m$ is obtained by finite choice, proved by induction on $m$. Applying $\lambda\vec F.\,b$ to numerals substitutes them one at a time. Numerals are closed, so no variable is captured and the computation reduces to the defining reductions of $G$ and the $H_j$.

The proof is constructive and uses only `propext` and `Quot.sound`.
