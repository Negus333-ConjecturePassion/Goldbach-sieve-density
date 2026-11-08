---
title: "On Signed Möbius Correlations in a Binary Goldbach Research Framework"
subtitle: "Exact Reductions, Classical Cancellation, and an Open Coupled-Prime Obstruction"
author: "Dr. Gregory C. Stamp"
date: "November 2026 · Research Manuscript v2.3 · Working Preprint"
abstract: "This note documents exact identities and classical estimates motivated by an exploratory M3C approach to binary Goldbach. The principal auxiliary result establishes uniform logarithmic-power decay for a Möbius-weighted Euler factor over a dyadic interval, with uniformity in an integer modulus. We distinguish this arithmetic-model cancellation from the unproved cancellation of the genuine coupled-prime discrepancy. Further results include an exact truncated Möbius identity, a corrected local root-count formula, a slope-difference determinant, and elementary estimates for exceptional prime-power sectors. This revision integrates source-explicit paper-level proofs of the deterministic Component 1 matching and the classical-input Component 3 small-error theorem for the explicitly frozen H1/H4B1/M2A support. The full source hypotheses and remaining historical equivalence question are disclosed; additional uniformity and endpoint-transfer lemmas are now stated and proved. The all-integer decoupled zero-mean estimate, the proposed M3C matching condition, and binary Goldbach remain open. The work is offered as a reproducible research note, not a claim of novelty or a proof of Goldbach."
keywords: "binary Goldbach; Möbius function; sieve methods; prime correlations; parity barrier; singular series"
lang: en-US
---


# 1. Introduction and scope

The binary Goldbach conjecture asserts that every even integer $N\ge4$ is the sum of two primes. Its proof remains open. The present auxiliary calculations are motivated by an internally developed M3C proof architecture, not by an accepted theorem reducing Goldbach to the estimates below. No novelty is claimed for the classical-input estimates. An independent AI-assisted review classified the main auxiliary lemma as a consequence of classical techniques; no exhaustive novelty review or human peer review has been completed.

Our project distinguishes two targets:

1. **Original M3C Component 2 (open):** with the original selected prime-triple strip, original cutoffs $U_0=V_0=N^{0.08}$, $T_0=N^{0.499}$, and source-defined comparison $B_{\mathcal S}(N)$, prove
   $$
   R_{>T_0}(N)=B_{\mathcal S}(N)+O_\delta\!\left(\frac{N}{(\log N)^{2+\delta}}\right).
   $$
   This is the original project's proposed component-matching criterion, not a theorem established here. Its full definitions and claimed upstream reductions remain subject to source-level audit.
2. **Auxiliary all-integer DZ route (open):** for dyadic core size $x\asymp N^{0.5505}$--$N^{0.5555}$, auxiliary $U=N^{0.02}$, $Z=N^{0.05}$, and $X\asymp N^{0.447}$, one proposed sufficient estimate is
   $$
   |H_{\mathrm{dec}}(N,x)|\ll_\delta \frac{N^2}{x(\log N)^{3+2\delta}}.
   $$
   Its transfer to Component 2 requires several separately audited theorems, including full-chamber coverage and source-defined endpoint matching. **It is not assumed here.**

Let $L=\log N$, with $N$ sufficiently large and even. In the first switched cofactor block let $r$ range over a dyadic core interval of length $O(x)$ and let $Q_r$ be a *source-defined set of distinct primes* $q$ lying in an interval of size $O(X)$, satisfying $N/3\le rq\le2N/3$, as well as any other previously frozen restrictions. All finite equalities below apply to any such sets, provided the specified coprimality conditions hold. Define
$$
 S_r=\sum_{q_1\in Q_r}\Lambda(N-rq_1),\qquad
 M_U(u)=\sum_{d\mid u,\ d\le U}\mu(d).
$$
For $(r,u)=1$, put
$$
 K_{r,u}=\sum_{\substack{q_2\in Q_r\\u\mid N-rq_2\\ (N-rq_2)/u>\sqrt N}}
 \Lambda\!\left(\frac{N-rq_2}{u}\right).
$$
The prime variable $q_2$ is *unweighted* (prime indicator); the complementary integer is von-Mangoldt weighted and can be a proper prime power. The selected first-block contribution is
$$
\mathcal C_1=\sum_r S_r\sum_{\substack{U<u\le2U\\(u,Nr)=1}}M_U(u)K_{r,u}.
$$
**Diagonal caution:** the expression $S_rK_{r,u}$ includes the ordered pair $q_1=q_2$; in the source-defined distinct-pair $H_{\mathrm{dec}}$ that diagonal must be subtracted and separately estimated. We do not silently identify $\mathcal C_1$ with the distinct-slope DZ contribution.

# 1A. The three-component M3C framework: established results, conditional dependencies, and the remaining matching problem

This section states the *frozen internal research interface*, not a complete proof of Goldbach. Its provenance is the November 1, 2026 **M3C Component 2 GREEN Gate** brief and the October 30, 2026 **ES-09D Final Small-Error Integration Certificate**. The present version incorporates the S2C/S2D source proofs and the ES-09D/Friedlander–Iwaniec published-theorem transfer into dedicated proof sections. These are **internally reviewed paper-level arguments on the frozen canonical model**, not human-refereed or formally machine-checked certificates for the historical H1 manuscript.

## 1A.1. The actual counting objective and selected strip

The ultimate goal is the positivity of the binary Goldbach count
$$
G_2(N)=\#\{(p_1,p_2):p_1,p_2\ \text{prime},\ p_1+p_2=N\}>0
$$
for every even $N\ge4$. The M3C calculations in this paper instead count primes complementary to a **three-prime product**; this is a different statement.

For sufficiently large even $N$, the frozen reduced strip is
$$
\begin{aligned}
\mathcal S_N^\circ=\{n=\ell m q:\ &\ell,m,q\ \text{prime};\quad N^{0.1885}\le\ell<N^{0.1895},\\
&N^{0.362}\le m<N^{0.366},\quad N^{0.446}\le q<N^{0.448},\\
&N/3\le n\le2N/3,\quad (n,N)=1\}.
\end{aligned}
$$
Set
$$
G_{\mathcal S}(N)=\#\{n\in\mathcal S_N^\circ:N-n\ \text{prime}\}.
$$
The normalization of the comparison model is *not* chosen freely: according to the frozen ES-09D interface (which adopts M2A Revision 2, §2, eq. (6)),
$$
\begin{aligned}
g_N(1)&=1,\qquad g_N(p^a)=\begin{cases}0,&p\mid N,\\ (p-1)/(p-2),&p\nmid N,\end{cases}\\
C_N&=\prod_{p\mid N}(1-1/p)\prod_{p\nmid N}\left(1+\frac1{p(p-2)}\right),\\
\delta_N&=\frac{\operatorname{Li}(N)}{N C_N},\qquad b_N(n)=\delta_Ng_N(n),\\
B_{\mathcal S}(N)&=\sum_{n\in\mathcal S_N^\circ}b_N(n),\qquad
\mathcal D_{\mathcal S}(N)=G_{\mathcal S}(N)-B_{\mathcal S}(N).
\end{aligned}
$$
The definitions have been checked against M2A Revision 2 §2 Eq. (6), but their identity with the historical H1 choices remains unproved. In particular, a selected strip statement $G_{\mathcal S}(N)>0$ would yield a representation $N=p+\ell m q$, **not** a binary Goldbach representation $N=p+q$.

## 1A.2. The three-component ledger and signed matching theorem

The ES-09D note derives, for its explicitly frozen common support and normalization, the formal decomposition
$$
\boxed{\mathcal D_{\mathcal S}(N)=\mathbb K_\circ(N)+\mathcal R_{>T}^\circ(N)+\mathcal E_{\mathrm{small}}^\circ(N).}
\tag{M3C.1}
$$
Here $U_0=V_0=N^{0.08}$ and $T_0=N^{0.499}$. The cofactor restrictions and $vd>T_0$ condition remain in the exact Vaughan high-divisor term.

**Component 1 — deterministic/principal-model matching (paper-level result on the frozen model).** The S2C, S2D and C1-05 source proofs establish, subject to ordinary outside mathematical review,
$$
\mathbb K_\circ(N)=-B_{\mathcal S}(N)+O_A\left(\frac{N}{L^A}\right)
\qquad(A>0).
\tag{M3C.C1}
$$
A proof for the **newly frozen canonical convention** is given in Section 1B. The distinct question whether historical H1 used this same normalization has not been resolved. The theorem is not asserted for every Friedlander–Iwaniec coefficient family.

**Component 2 — signed high-divisor matching (OPEN).** For some fixed $\delta>0$, the decisive internal proposed matching statement is
$$
\boxed{\mathcal R_{>T}^\circ(N)=B_{\mathcal S}(N)+O_\delta\left(\frac{N}{L^{2+\delta}}\right)}
\quad\text{uniformly for all sufficiently large even }N.
\tag{M3C.C2}
$$
The source labels this the “GREEN-R” gate **conditional on the upstream identities and reductions**. It is **not proved**. An estimate for a single core block, or for the auxiliary all-integer DZ statistic alone without a verified transfer, is insufficient.

**Component 3 — exact decomposition and small-error transfer (paper-level result on the frozen model).** ES-09D records (M3C.1) as an exact Vaughan/prime-indicator decomposition and claims, from the specified classical distribution estimate with endpoint partial summation,
$$
\mathcal E_{\mathrm{small}}^\circ(N)=O_A\left(\frac{N}{L^A}\right)\qquad(A>0).
\tag{M3C.C3}
$$
The exact identities can be rechecked algebraically from the displayed definitions. The *analytic* transfer uses Friedlander–Iwaniec, *Opera de Cribro*, Theorem 9.17, as specialized to the specified convolution coefficients, endpoints, and the adopted M2A normalization. The literal published source was subsequently checked on printed pp. 169–170; the proof outline and hypothesis mapping are given in Section 1C. Its N-dependent windowed Siegel–Walfisz application and final endpoint bookkeeping still warrant outside review. The result is not automatically a theorem about unfrozen H1/FI coefficients.

Combining (M3C.1), (M3C.C1), (M3C.C2) and (M3C.C3), **if their uniform hypotheses and normalizations all hold**, gives
$$
\mathcal D_{\mathcal S}(N)=O_\delta\left(\frac{N}{L^{2+\delta}}\right),
\qquad G_{\mathcal S}(N)=B_{\mathcal S}(N)+O_\delta\left(\frac{N}{L^{2+\delta}}\right).
\tag{M3C.2}
$$
If a positive lower bound $B_{\mathcal S}(N)\gg N/L^2$ is independently verified with compatible constants, then (M3C.2) yields $G_{\mathcal S}(N)>0$ for large even $N$. **An additional, separately proved transfer is still necessary to deduce binary Goldbach.** Neither that transfer nor (M3C.C2) is supplied by the present paper.

## 1A.3. Why the HII first-block theorem is not Component 2

The first-block results in Sections 2–9 concern auxiliary parameters $U_*=N^{0.02}$, $Z=N^{0.05}$, $r\asymp x\asymp N^{0.5505}$–$N^{0.5555}$ and prime slopes $q\asymp X\asymp N^{0.447}$. Their proposed signed target $|\mathcal E_1|\ll xX^2/L^{4+2\delta}$ is a **subrange sufficient allocation within a proposed auxiliary DZ route**. Even a successful proof would not independently close the full DZ statistic or the original (M3C.C2) matching theorem. The auxiliary all-integer variance route is stronger than the direct selected-strip requirement and is not asserted necessary.

## 1A.4. Source-audit disclosure

“Source audit pending” means that a claimed theorem has been located in a project brief or certificate but its **original full proof, published theorem hypotheses, parameter transfer, and formal dependency chain have not all been rechecked for this manuscript**. It does *not* mean that the historical result is false. The separate architecture ledger records the original source names, what was recovered, which exact equalities are available, and what is missing. Neither a project-assigned GREEN label nor a finite Lean/Python check substitutes for verification of an analytic asymptotic theorem.

# 1B. Component 1: deterministic matching theorem and proof

The following statements are **on the explicitly frozen canonical support** of Section 1A, with $U=V=N^{2/25}$ and $T=N^{499/1000}$. The symbol $P_N$ counts ordered triples, which is the same as counting their distinct products on the disjoint windows; put
$$
P_N=\#\mathcal S_N^\circ,\qquad H_N=\sum_{n\in\mathcal S_N^\circ}\frac1{\log(N-n)},\qquad B_\circ(N)=\delta_N\sum_{n\in\mathcal S_N^\circ}g_N(n).
$$
Here $\mathbb K_\circ=\widehat M_1-\widehat M_2+M_{\le T}^{\mathrm{pr}}-B_\circ$ uses the source-defined canonical principal-character sums. The support and $g_N$ agree *by construction*, not by a claim of literal identity to every original H1 convention.

**Theorem C1 (deterministic matching; internal paper-level proof).** For every fixed $A>0$, uniformly for all sufficiently large even integers $N$,
$$
\boxed{\mathbb K_\circ(N)=-B_\circ(N)+O_A(N/\log^A N).}\tag{C1.1}
$$
Furthermore, on these selected prime windows,
$$
\boxed{\mathbb K_\circ(N)=-C_{\mathcal S}\mathfrak S(N)\frac N{(\log N)^2}+O\!\left(\frac{N\log\log N}{(\log N)^3}\right),}\tag{C1.2}
$$
where
$$
C_{\mathcal S}=\frac13\int_{0.1885}^{0.1895}\int_{0.446}^{0.448}\frac{db\,da}{ab(1-a-b)}>0.
$$
The theorem evaluates the structured term only; it makes **no** assertion that the large-divisor tail is negligible.

**Proof, step 1: exact finite reduction (S2C).** Define
$$
\begin{aligned}
a_1&=\sum_{\substack{d\le U\\(d,N)=1}}\frac{\mu(d)}{\varphi(d)}, &
a_{\log}&=\sum_{\substack{d\le U\\(d,N)=1}}\frac{\mu(d)\log d}{\varphi(d)},\\
a_2&=\sum_{d,v\le U,(dv,N)=1}\frac{\mu(d)\Lambda(v)}{\varphi(dv)}, &
\gamma_T&=-\sum_{\substack{d\le U,\ v>U,\ dv\le T\\(dv,N)=1}}\frac{\mu(d)\Lambda(v)}{\varphi(dv)}.
\end{aligned}
$$
The exact S2C principal-character identity reads
$$
\boxed{\mathbb K_\circ=(a_1-\delta_N)P_N+(\gamma_T-a_{\log}-a_2)H_N+E_{\mathrm{loc}}.}\tag{C1.3}
$$
Here $E_{\mathrm{loc}}$ corrects the low-Type-II $(n,t)=1$ condition and the model factor $g_N(n)$; it is not discarded. To see its size, set
$$
A_N(y)=\sum_{d\le y,(d,N)=1}\frac{\mu(d)}{\varphi(d)}
$$
and, for $n=\ell mq$, use the exact localization
$$
\begin{aligned}
c_T(n;N)-\gamma_T={}&a_1\log\ell\left(\frac1{\ell-1}+\frac1{\ell(\ell-1)}\right)
+a_1\frac{\log m}{m-1}\\
&+\frac{\log q}{q-1}A_N(T/q).
\end{aligned}\tag{C1.4}
$$
This keeps the $\ell^2$ prime-power term. The bounds $\sum_{d\le y}1/\varphi(d)\ll\log(2y)$ and $\min(\ell,m,q)\ge N^{0.1885}$ imply
$$
\sup_{n\in\mathcal S_N^\circ}|c_T(n;N)-\gamma_T|\ll N^{-0.1885}(\log N)^2,
\quad g_N(n)=1+O(N^{-0.1885}).
$$
Summing, and using $P_N\le N$, gives
$$
E_{\mathrm{loc}}(N)=O_\varepsilon(N^{0.8115+\varepsilon}),\tag{C1.5}
$$
for fixed $0<\varepsilon<0.1885$. It is negligible compared with $N/(\log N)^A$ for every fixed $A$.

**Proof, step 2: uniform scalar cancellation (C1-03).** Introduce the multiplicative kernel
$$
k_M(1)=1,\qquad k_M(p^j)=\begin{cases}p^{-j},&p\mid M,\\-1/(p^j(p-1)),&p\nmid M,\end{cases}\quad j\ge1.
$$
An exact prime-power check gives
$$
\mathbf1_{(n,M)=1}\frac{\mu(n)}{\varphi(n)}=\left(\frac\mu{\mathrm{id}}*k_M\right)(n).
$$
Its $\ell^1$ mass is $O(\log\log(3M))$ and, for fixed $\beta\in(0,1)$, its weighted mass $\sum_j|k_M(j)|j^\beta=M^{o(1)}$, uniformly for $M\le N^C$ with fixed $C$. Splitting the convolution at $j=\sqrt x$ and applying classical quantitative Möbius summation yields, for every fixed $A,c,C>0$, $N^c\le x\le N^C$ and $M\le N^C$,
$$
\sum_{d\le x,(d,M)=1}\frac{\mu(d)}{\varphi(d)}=O_{A,c,C}(\log^{-A}N),
$$
$$
\sum_{d\le x,(d,M)=1}\frac{\mu(d)\log d}{\varphi(d)}=-\sum_{j\ge1}k_M(j)+O_{A,c,C}(\log^{-A}N).
$$
For even $M$, the absolutely convergent Euler product is
$$
\sum_{j\ge1}k_M(j)=\prod_{p\mid M}(1-p^{-1})^{-1}\prod_{p\nmid M}\left(1-\frac1{(p-1)^2}\right)=\mathfrak S(M).
$$
In particular $a_1=O_A(\log^{-A}N)$ and $a_{\log}=-\mathfrak S(N)+O_A(\log^{-A}N)$.

**Lemma C1-U (uniform kernel and truncated convolution, quantified).** Fix $c,C>0$ and $A>0$. Let $N\to\infty$, $N^c\le x\le N^C$ and $1\le M\le N^C$. Set $u(n)=\mu(n)/n$, and let $k_M$ be the multiplicative function specified above. Then, uniformly in these parameters,
$$
\begin{aligned}
\sum_{j\ge1}|k_M(j)|&\ll \log\log(3M),\\
\sum_{j\ge1}|k_M(j)|j^{1/4}&\ll \exp(o(\log N))=N^{o(1)},\\
\sum_{j\ge1}|k_M(j)|\log(2j)&\ll (\log(2M))^{O(1)}.
\end{aligned}\tag{C1.U1}
$$
Consequently, writing $F_M(n)=\mathbf1_{(n,M)=1}\mu(n)/\varphi(n)$,
$$
\sum_{n\le x}F_M(n)=O_{A,c,C}(L^{-A}),\qquad
\sum_{n\le x}F_M(n)\log n=-\sum_{j\ge1}k_M(j)+O_{A,c,C}(L^{-A}).\tag{C1.U2}
$$
**Proof.** Computing the geometric series prime by prime gives the following ordinary absolute mass:
$$
\sum_j|k_M(j)|=\prod_{p\mid M}(1-1/p)^{-1}\prod_{p\nmid M}(1+1/(p-1)^2),
$$
which is $O(\log\log(3M))$ by the standard product bound for $M/\varphi(M)$. At weight $j^{1/4}$ the nondividing-prime factors form a convergent product, while the dividing-prime factors are $(1-p^{-3/4})^{-1}$. Split $p\mid M$ at $(\log(3M))^2$; the sum of $p^{-3/4}$ below that threshold is $O((\log(3M))^{1/2})$ by comparison with integers, and for larger primes it is $O(\log M/(\log M)^{3/2})$. Thus the logarithm of the weighted product is $o(\log N)$ uniformly for $M\le N^C$ (with bounded $M$ absorbed in the constant). The logarithmic moment follows by the inequality $\log(2j)\ll j^{1/8}$ and the same product argument; in fact a direct differentiation gives a polylogarithmic bound.

For $z\ge2$, the classical quantitative prime number theorem in zero-free-region form implies, for each fixed $B>0$,
$$
H_0(z):=\sum_{n\le z}\frac{\mu(n)}n=O_B((\log z)^{-B}),\qquad
H_1(z):=\sum_{n\le z}\frac{\mu(n)\log n}{n}=-1+O_B((\log z)^{-B}).\tag{C1.U3}
$$
One may use the Vinogradov--Korobov zero-free-region consequence $\sum_{n\le z}\mu(n)\ll z\exp[-c_0(\log z)^{3/5}(\log\log(3z))^{-1/5}]$, together with partial summation and the Dirichlet-series identities $1/\zeta(s)$ and its derivative at $s=1$. The arbitrary logarithmic power in (C1.U3) is essential, not merely the limit $H_0(z)\to0$.

The exact convolution yields
$$
\sum_{n\le x}F_M(n)=\sum_{j\le x}k_M(j)H_0(x/j),
$$
$$
\sum_{n\le x}F_M(n)\log n=\sum_{j\le x}k_M(j)\bigl(H_1(x/j)+(\log j)H_0(x/j)\bigr).
$$
For $j\le\sqrt x$, $\log(x/j)\ge(c/2)L$, so (C1.U3), the ordinary and logarithmic kernel masses, and a sufficiently large choice of $B$ give $O_A(L^{-A})$ for the first sum and $-\sum_{j\le\sqrt x}k_M(j)+O_A(L^{-A})$ for the second. For $j>\sqrt x$, use $|H_0(y)|\le \sum_{n\le y}1/n\ll1+\log y$ and $|H_1(y)|\ll(1+\log y)^2$, and
$$
\sum_{j>\sqrt x}|k_M(j)|\ll x^{-1/8}\sum_j|k_M(j)|j^{1/4}=N^{-c/8+o(1)}.
$$
This is power-small even after multiplying by any fixed power of $L$; the missing infinite-kernel tail is controlled in the same way. This proves (C1.U2). For even $M$, the Euler product $\sum_j k_M(j)=\mathfrak S(M)$; at $p=2$ the factor is legitimate because $2\mid M$. $\square$

**Analytic-source specification.** The external analytic input (C1.U3) is the standard classical zero-free-region prime-number-theorem estimate for $1/\zeta(s)$ (see Montgomery--Vaughan, *Multiplicative Number Theory I: Classical Theory*, chapters on the zero-free region and the prime number theorem; or Iwaniec--Kowalski, *Analytic Number Theory*, the prime-number-theorem and zero-free-region chapters). The proof uses that quantitative form rather than claiming it is a new theorem here. The project manuscript's source application remains subject to outside specialist review.

**Proof, step 3: the low-Type-II scalar defect.** Because $U^2<T$, the $v\le U$ and $v>U$ contributions fuse without overlap:
$$
\gamma_T-a_2=-\sum_{\substack{d\le U\\(d,N)=1}}\mu(d)\sum_{v\le T/d,(v,N)=1}\frac{\Lambda(v)}{\varphi(dv)}.
$$
For squarefree $d$, set $Q_N(y)=\sum_{p^k\le y,p\nmid N}\log p/\varphi(p^k)$ and $J(d)=\sum_{p\mid d}\log p/(p-1)^2$. The source's exact $\varphi(dp^k)$ separation and the strong prime-number theorem imply
$$
\gamma_T-a_{\log}-a_2=-(\log T+\kappa_N)a_1+J_N(U)+O_A(\log^{-A}N),
$$
where $|\kappa_N|\ll\log N$ and $J_N(U)=\sum_{\substack{d\le U\\(d,N)=1}}\mu(d)J(d)/\varphi(d)$. Opening $J(d)$ yields
$$
J_N(U)=-\sum_{p\le U,p\nmid N}\frac{\log p}{(p-1)^3}
\sum_{e\le U/p,(e,Np)=1}\frac{\mu(e)}{\varphi(e)}.
$$
For $p\le\sqrt U$, the inner sum has polynomially large cutoff and the uniform cancellation just proved applies; for $p>\sqrt U$, the absolutely convergent prime-weight tail is power-small. Therefore $J_N(U)=O_A(\log^{-A}N)$ and
$$
\boxed{\gamma_T-a_{\log}-a_2=O_A(\log^{-A}N).}\tag{C1.6}
$$
No distribution estimate for two complementary primes is invoked.

**Proof, step 4: exact normalization.** Substitute the scalar estimates and (C1.5) in (C1.3). Since $P_N\le N$ and $H_N\ll N/\log N$,
$$
\mathbb K_\circ=-\delta_N P_N+O_A(N/\log^A N).
$$
The model identity from M2A Revision 2, §2, Eq. (6) is $\delta_N=\mathfrak S(N)\operatorname{Li}(N)/N$. On the reduced strip $g_N(n)=1+O(N^{-0.1885})$, so
$$
B_\circ=\delta_NP_N+O_A(N/\log^A N),
$$
which proves (C1.1). Standard prime-number-theorem counts in the three fixed exponent windows yield
$$
P_N=C_{\mathcal S}\frac N{\log N}+O\left(\frac N{(\log N)^2}\right).
$$
Finally $\delta_N=\mathfrak S(N)/\log N+O(\mathfrak S(N)/(\log N)^2)$, and $\mathfrak S(N)\ll\log\log N$, giving (C1.2). $\square$

**Scope qualification.** The identification of the frozen canonical $b_N$ with the M2A formula is a declared project-interface convention. Earlier H1 notes do not uniquely fix the same model and every FI cell. Component 1 is therefore an **internally paper-proved theorem for this versioned support**, pending specialist refereeing of the exact finite localization and cited analytic inputs.

# 1C. Component 3: exact Vaughan assembly and classical small-error theorem

**Theorem C3 (small-error assembly; internal paper-level proof).** With the identical frozen support, model, and original $U,V,T$ as in Theorem C1, define for $s=N-n$,
$$
\begin{aligned}
I_1(s)&=\sum_{\substack{d\mid s\\d\le U}}\mu(d)\log(s/d),\\
I_2(s)&=\sum_{\substack{da\mid s\\d\le U,\ a\le U}}\mu(d)\Lambda(a),\\
\mathrm{II}(s)&=-\sum_{\substack{v>U,\ d\le U,vd\mid s,s/v>U}}\mu(d)\Lambda(v).
\end{aligned}
$$
The signed Vaughan identity $\Lambda(s)=I_1(s)-I_2(s)+\mathrm{II}(s)$ is exact for $s>U$. Split $\mathrm{II}_{\le T}$ and $\mathrm{II}_{>T}$ at $vd=T$, retaining the cofactor inequality $s/v>U$ in the high part. Let
$$
[F]_\circ=\sum_{n\in\mathcal S_N^\circ}\frac{F(N-n)}{\log(N-n)}.
$$
Take $\widehat M_1,\widehat M_2,M_{\le T}^{\mathrm{pr}}$ to be the identical canonical principal-character sums used in Section 1B (in particular the low-Type-II center retains $(n,t)=1$). Set
$$
\mathbb K_\circ=\widehat M_1-\widehat M_2+M_{\le T}^{\mathrm{pr}}-B_\circ,\qquad
\mathcal R_{>T}^\circ=[\mathrm{II}_{>T}]_\circ.
$$
Then the exact identity is
$$
\boxed{G_{\mathcal S}(N)-B_\circ(N)=\mathbb K_\circ(N)+\mathcal R_{>T}^\circ(N)+\mathcal E_{\mathrm{small}}^\circ(N),}\tag{C3.1}
$$
with the explicit error
$$
\begin{aligned}
\mathcal E_{\mathrm{small}}^\circ={}&([I_1]_\circ-\widehat M_1)-([I_2]_\circ-\widehat M_2)\\
&+([\mathrm{II}_{\le T}]_\circ-M_{\le T}^{\mathrm{pr}})+E_{pp}^\circ,
\end{aligned}
$$
where
$$
E_{pp}^\circ=-\sum_{\substack{n\in\mathcal S_N^\circ,N-n=p^k,\ k\ge2}}\frac1k.
$$
For each fixed $A>0$, the original project's classical-input transfer establishes at the **internal paper-proof level**
$$
\boxed{\mathcal E_{\mathrm{small}}^\circ(N)=O_A(N/\log^A N).}\tag{C3.2}
$$

**Proof.** For every integer $s>1$,
$$
\mathbf1_{\mathbb P}(s)=\frac{\Lambda(s)}{\log s}-\sum_{s=p^k,k\ge2}\frac1k.
$$
Since $N/3\le s\le2N/3$, the shifted proper-prime-power sum is at most $O(\sqrt N\log N)$. Substitute Vaughan's finite identity, group the low and high $vd$ sectors, and add and subtract their source-defined principal-character models. This gives (C3.1) with no distribution hypothesis. For $vd\le T$, the condition $s/v>U$ is automatic from $s\ge N/3$ and $UT=N^{0.579}=o(N)$; this must **not** be applied to $vd>T$.

To bound the three remaining discrepancies, write $\rho_N^\circ=\alpha*\beta$ with $\alpha(r)$ selecting the disjoint prime pair $r=\ell m$ and $\beta(q)$ selecting the third prime window, both excluding factors dividing $N$. They obey $|\alpha(r)|,|\beta(q)|\le1$. The prime indicator $\beta$ satisfies the required uniform Siegel–Walfisz condition by taking differences of classical initial-segment estimates; the finitely many excluded primes dividing $N$ contribute negligible error at the source theorem's scale.

Friedlander–Iwaniec, *Opera de Cribro*, **Theorem 9.17, equation (9.80), printed pp. 169–170**, states that for divisor-bounded coefficients with a Siegel–Walfisz sequence in one factor, and $\Delta=(\log Y)^{-B}$, one has
$$
\sum_{t\le\Delta\sqrt Y}\max_{(a,t)=1}
\left|\sum_{\substack{rq\le Y,\ r,q\le\Delta Y\\rq\equiv a\ (\mathrm{mod}\ t)}}\alpha(r)\beta(q)
-\frac1{\varphi(t)}\sum_{\substack{rq\le Y,\ r,q\le\Delta Y\\(rq,t)=1}}\alpha(r)\beta(q)\right|
\ll_A \frac Y{(\log Y)^A}.
$$
In our frozen support $r\asymp N^{0.55}$ and $q\asymp N^{0.447}$, and $Y\in[N/3,2N/3]$. Both bilinear variables are eventually at most $\Delta Y$. All required moduli satisfy $t\le T=N^{0.499}<\Delta\sqrt Y$ for sufficiently large $N$ and each fixed $B$. On the reduced support, only $t$ coprime to $N$ can contribute to the actual progression $rq\equiv N\pmod t$.

The weights $1/\log(N-n)$ and $\log((N-n)/d)/\log(N-n)$ have uniformly controlled variation on the central strip. Apply the printed estimate at **each fixed endpoint** $Y$ and integrate the *sum over moduli* by partial summation. This avoids the unjustified inequality that would replace $\sum_t$ of endpoint errors by $\sum_t\sup_Y$ of errors. The coefficients $\mu(d)$, $w(t)$ and $c_2(t)$ have magnitude at most $O(\log N)$ (after the relevant modulus grouping). Invoking Theorem 9.17 with a larger saving exponent absorbs these logarithms. It follows that each of
$$
[I_1]_\circ-\widehat M_1,\quad [I_2]_\circ-\widehat M_2,\quad [\mathrm{II}_{\le T}]_\circ-M_{\le T}^{\mathrm{pr}}
$$
is $O_A(N/\log^A N)$. Together with $E_{pp}^\circ=O(\sqrt N\log N)$ this gives (C3.2). $\square$

**Lemma C3-W (uniform Siegel--Walfisz for the moving prime window).** Let $N$ be the external sufficiently large even shift, $Q_-=N^{0.446}$ and $Q_+=N^{0.448}$, and
$$
\beta_N(q)=\mathbf1_{\{q\text{ prime},\ Q_-\le q<Q_+,\ q\nmid N\}}.
$$
For every fixed $A,D>0$, every real endpoint $2\le z\le N$, every integer $1\le k\le(\log(2z))^D$ and every $(a,k)=1$, the Siegel--Walfisz discrepancy for $\sum_{q\le z}\beta_N(q)$ is $O_{A,D}(z/(\log(2z))^A)$, uniformly in $N$ provided the endpoint is in the range relevant to $\beta_N$; outside the window the error is evaluated at its clipped upper endpoint. More precisely, for $z<Q_-$ the discrepancy vanishes, and for $Q_-\le z\le N$ it is
$$
O_{A,D}\!\left(\frac{\min(z,Q_+) }{(\log\min(z,Q_+))^A}+\frac{Q_-}{(\log Q_-)^A}+\omega(N)\right).
\tag{C3.W}
$$
In particular, on the required range $Q_-\le z\ll N$ this is $O_{A,D}(z/(\log z)^A)$, with sufficiently increased input exponents. **Proof.** The interval-weighted progression sum equals the difference of ordinary prime-counting functions at $\min(z,Q_+)$ and $Q_-$, with the usual harmless endpoint convention, and with at most $\omega(N)$ exclusions. Apply the classical Siegel--Walfisz theorem to both endpoints; since these are fixed positive powers of $N$, the constants and arbitrary logarithmic savings are uniform. For $z<Q_-$ the sequence has no mass. A prime-window restriction does not produce a new modulus-dependent exceptional character. $\square$

**Lemma C3-E (sum-over-moduli endpoint transfer).** Fix the external even shift $N$, let $Y$ denote only the variable *product endpoint* $rq\le Y$, and set
$$
D_t(Y;a)=\sum_{\substack{rq\le Y\\rq\equiv a\pmod t}}\alpha(r)\beta_N(q)
-\frac{1}{\varphi(t)}\sum_{\substack{rq\le Y\\(rq,t)=1}}\alpha(r)\beta_N(q),\qquad(a,t)=1.
$$
All sums here inherit the fixed supports $r\in[N^{0.5505},N^{0.5555}]$ (with the actual narrower source-imposed windows), $q\in[Q_-,Q_+)$, and the same coprimality conventions. Friedlander--Iwaniec's Theorem 9.17 applies at every $Y\in[N/3,2N/3]$ with $t\le T=N^{0.499}$ and yields
$$
\sum_{t\le T}\max_{(a,t)=1}|D_t(Y;a)|\ll_B N/L^B
\tag{C3.E1}
$$
for any fixed $B>0$, uniformly in such $Y$. The theorem **does not** assert $\sum_t\sup_Y|D_t(Y;a)|\ll N/L^B$.

Let $Y_0=N/3$, $Y_1=2N/3$. For any piecewise continuously differentiable family $f_t:[Y_0,Y_1]\to\mathbb R$, summation by parts implies
$$
\begin{aligned}
\sum_{t\le T}\left|\int_{Y_0}^{Y_1} f_t(y)\,dD_t(y;a_t)\right|
&\le (\sup_{t,y}|f_t(y)|)\sum_{t\le T}\bigl(|D_t(Y_0;a_t)|+|D_t(Y_1;a_t)|\bigr)\\
&\quad+\int_{Y_0}^{Y_1}\sup_{t}|f_t'(y)|\,\sum_{t\le T}|D_t(y;a_t)|\,dy.
\end{aligned}\tag{C3.E2}
$$
Here $a_t=N\pmod t$ where $(t,N)=1$. For $I_1$ the modulus is $d\le U$ and the weight is
$$
f_d(y)=\frac{\log((N-y)/d)}{\log(N-y)}=1-\frac{\log d}{\log(N-y)};
$$
for $I_2$ the modulus is $t=da\le U^2$ with coefficient $c_2(t)=\sum_{da=t,\,d,a\le U}\mu(d)\Lambda(a)$ and $f_t(y)=1/\log(N-y)$; for low $\mathrm{II}$ the modulus is $t=dv\le T$ with coefficient $-w(t)$ and the same weight $f_t(y)=1/\log(N-y)$. In both latter cases the arithmetic centre contains $\mathbf1_{(rq,t)=1}$ and **must not** be replaced by an unconditioned average. In the first case, $\log d\le 0.08L$. Uniformly for $y\in[Y_0,Y_1]$,
$$
|f_t(y)|\ll1,\qquad |f_t'(y)|\ll L^{C_0}/N,
$$
with a fixed $C_0$, and $|c_2(t)|,|w(t)|\ll L$ under the source's explicit coefficient bounds. Thus (C3.E1)--(C3.E2), multiplied by at most fixed powers of $L$, yield $O_A(N/L^A)$ by applying Theorem 9.17 with $B$ larger than $A$ by those powers. At no step is the sum over moduli moved outside the uniform endpoint bound incorrectly. $\square$

**Nonreduced-modulus rule.** On the reduced support $\gcd(n,N)=1$, one has $\gcd(N-n,N)=1$. Hence a divisor $t\mid N-n$ automatically has $\gcd(t,N)=1$. For $(t,N)>1$ the actual congruence $n\equiv N\pmod t$ is impossible, and the canonical comparison sum is defined to omit that modulus. This is a support-specific statement, not a claim that all moduli are coprime to the full (unreduced) source sequence.

**Uniformity boundary.** Lemmas C3-W and C3-E concern the frozen convolution $\rho_N^\circ=\alpha*\beta_N$ and its specific Type-I and low-Type-II coefficients. The full original Friedlander--Iwaniec family, historical H1-to-M2A identification, and the complementary high-Type-II bound are not consequences of these lemmas.

**Hypothesis and provenance boundary.** Theorem 9.17 has been checked against the book's printed statement, but the specialization to the external $N$-dependent prime window and the precise endpoint-weighted normalizations remain an internal paper-level audit, not specialist peer review. Theorem C3 is **not** a claim that arbitrary original FI Type-II coefficient families have the same error bound.

# 1D. Consolidated implications and theorem-status ledger

Theorems C1 and C3, combined **only on their common frozen definitions**, imply
$$
\boxed{G_{\mathcal S}(N)=\mathcal R_{>T}^\circ(N)+O_A(N/\log^A N).}\tag{1D.1}
$$
This is a *reduction* of the selected-strip count to the large-divisor signed tail. It supplies neither a lower bound for that tail nor binary Goldbach.

| Obligation | Proof status in v2.2 | Scope |
|:--|:--|:--|
| Exact S2C coefficient localization | Algebraic proof included | Frozen support |
| Uniform scalar and Euler estimates (C1-03) | Classical-input paper proof included | Uniform even $N$ |
| Theorem C1, $\mathbb K=-B+O_A(N/L^A)$ | **Internal paper-level PASS** | Frozen M2A model only |
| Exact Vaughan / prime-power assembly | Exact identity included | Frozen support |
| Friedlander–Iwaniec Theorem 9.17 | Printed statement checked | Published input |
| Theorem C3, $\mathcal E_{small}=O_A(N/L^A)$ | **Internal paper-level, source-explicit; specialist review pending** | Frozen support only |
| Component 2, $\mathcal R_{>T}=B+O_\delta(N/L^{2+\delta})$ | **OPEN** | Full selected strip |
| Full FI-to-binary-Goldbach implication | **OPEN** | Not supplied by M3C |

The original M3C parameters $(U,V,T)=(N^{0.08},N^{0.08},N^{0.499})$ must not be confused with the auxiliary switched-block parameters $(N^{0.02},N^{0.05})$. The distinction is substantive, not notational.


# 2. Exact first-block and cutoff lemmas

**Lemma 2.1 (truncated Möbius identity).** For every integer $u$ with $U<u\le2U$,
$$
 M_U(u)=-\mu(u).
$$
**Proof.** Since $u>U$, its proper divisors are at most $u/2\le U$. Therefore $M_U(u)=\sum_{d\mid u,d<u}\mu(d)=-\mu(u)$, by $\sum_{d\mid u}\mu(d)=0$ for $u>1$. $\square$

**Lemma 2.2 (inactive switched large-divisor cutoff).** Suppose $N/3\le rq\le2N/3$, $U=N^{0.02}$, and $U<u\le2U$. For sufficiently large $N$, $(N-rq)/u>\sqrt N$.

**Proof.** $(N-rq)/u\ge N/(6U)=N^{0.98}/6>\sqrt N$ when $N^{0.48}>6$. $\square$

Thus on the first block the cutoff may be dropped **without changing the actual arithmetic sum**. This does not remove any restrictions in $Q_r$.

# 3. Local arithmetic model (explicitly NOT an asymptotic)

Assume $(u,Nr)=1$. Choose $q_0$ satisfying $rq_0\equiv N\pmod u$, set $v_0=(N-rq_0)/u$, and write
$$
 q=q_0+ut,\qquad v=v_0-rt,\qquad rq+uv=N.
$$
**Proposition 3.1 (local root count; corrected coprimality).** Assume additionally $(r,N)=1$. For each prime $\ell$, the number of residue classes $t\pmod\ell$ such that $\ell\mid q(t)v(t)$ is $1$ if $\ell\mid Nru$, and $2$ otherwise. Indeed, a slope vanishes when $\ell\mid r$ or $\ell\mid u$, and if both slopes are nonzero the two roots coincide precisely when $\ell\mid N$, by the determinant $N$ of the two affine forms. The hypotheses exclude the case that one entire form vanishes modulo $\ell$.

**Exceptional core sector.** If $(r,N)>1$, choose a prime $p\mid(r,N)$. Then both $N-rq$ and, for $(u,Nr)=1$, $(N-rq)/u$ are divisible by $p$. Consequently a nonzero von Mangoldt factor on either number forces that number to be a power of $p$; these $r$ are excluded from the local model and handled separately by elementary prime-power bounds (Proposition 7.2). In particular, set $\mathfrak S_{r,u}=0$ in this exceptional sector, and otherwise define
$$
 \mathfrak S_{r,u}=2C_2\prod_{\substack{\ell\mid Nru\\\ell>2}}\frac{\ell-1}{\ell-2},
 \qquad C_2=\prod_{\ell>2}\left(1-\frac1{(\ell-1)^2}\right).
$$
This is a chosen local arithmetic factor, **not an established prime-pair asymptotic**. Write $g(u)=\prod_{\ell\mid u,\ell>2}(\ell-1)/(\ell-2)$. Let $J_r$ be the continuous q-window for $Q_r$ and $\operatorname{Li}(J_r)=\int_{J_r}dt/\log t$. Define
$$
 \mathcal K_{r,u}=\frac{\mathfrak S_{r,u}}{u}\operatorname{Li}(J_r).
$$
This definition sets the model to zero for $(r,N)>1$. For $(r,N)=1$ and $(u,Nr)=1$, the factor satisfies $\mathfrak S_{r,u}=\mathfrak S(Nr)g(u)$. The first-block cutoff is inactive by Lemma 2.2, so $J_r$ has no additional $u$-dependent restriction from $v>\sqrt N$. Other source-defined window conditions must still be checked.

# 4. Uniform signed Euler-weight cancellation

**Theorem 4.1 (classical zero-free-region deduction).** Let $\theta>0$ be fixed, $U=N^\theta$, and $M$ be any positive integer satisfying $1\le M\le N^2$. For every fixed $A>0$,
$$
 \sum_{\substack{U<u\le2U\\(u,M)=1}}\frac{\mu(u)g(u)}u
 =O_{A,\theta}((\log N)^{-A}),
$$
with constant independent of $M$. The proof uses the standard quantitative Mertens bound following from a classical zero-free region. This is not claimed as an original discovery.

**Proof.** Define $f_M(n)=\mu(n)g(n)\mathbf1_{(n,M)=1}$. Since $g$ is a product only over odd primes, $g(2)=1$ by definition. There is no parity restriction on $M$. For $\Re s>1$,
$$
 F_M(s)=\sum_{n\ge1}\frac{f_M(n)}{n^s}
 =\prod_{p\nmid M}(1-g(p)p^{-s})=\zeta(s)^{-1}C_M(s).
$$
The factors of $C_M$ are
$$
 C_{M,p}(s)=\begin{cases}
 (1-p^{-s})^{-1},&p\mid M,\\
 (1-g(p)p^{-s})/(1-p^{-s}),&p\nmid M.
 \end{cases}
$$
Write $C_M(s)=\sum_{d\ge1}c_M(d)d^{-s}$ and $f_M=\mu*c_M$. The coefficients at prime powers are, for $k\ge1$,
$$
 c_M(p^k)=\begin{cases}
 1,&p\mid M,\\
 -1/(p-2),&p\nmid M,\ p>2,\\
 0,&p=2,\ 2\nmid M.
 \end{cases}
$$
The last case is essential when $M$ is odd. For $\alpha=0.9$, the geometric expansions and $g(p)-1=1/(p-2)=O(1/p)$ for odd $p$ give
$$
 \sum_d\frac{|c_M(d)|}{d^{\alpha}}
 \le\exp\left(O\left(1+\sum_{p\mid M}p^{-\alpha}\right)\right).
$$
For $L=\log N$, split primes dividing $M$ at $L^2$. Since $\log M\le2L$,
$$
 \sum_{p\mid M}p^{-0.9}\le
 \sum_{n\le L^2}n^{-0.9}
 +\frac{2L}{\log(L^2)}(L^2)^{-0.9}
 =O(L^{0.2}).
$$
Hence the coefficient norm is at most $\exp(O(L^{0.2}))$. A standard quantitative Möbius summatory estimate deduced from a classical zero-free region supplies, for sufficiently large $y$,
$$
 h(y):=\sum_{m\le y}\frac{\mu(m)}m
 \ll \exp\bigl(-c\sqrt{\log y}\bigr)
$$
for some $c>0$. One obtains this estimate, for instance, by partial summation from the classical effective bound $\sum_{n\le y}\mu(n)\ll y\exp(-c\sqrt{\log y})$, decreasing $c$ if necessary. By convolution,
$$
 \sum_{n\le t}\frac{f_M(n)}n
 =\sum_{d\le t}\frac{c_M(d)}d h(t/d).
$$
For $t\in[U,2U]$, split at $d=\sqrt t$. For $d\le\sqrt t$, $\log(t/d)\ge (\theta/2)L$ and the zero-free-region saving $\exp(-c\sqrt{\theta L/2})$ dominates $\exp(O(L^{0.2}))$. Here $\sum_d|c_M(d)|/d\le\sum_d|c_M(d)|/d^{0.9}$ is used explicitly. For $d>\sqrt t$, use $|h(t/d)|\ll 1+\log t\ll L$ and
$$
 \sum_{d>\sqrt t}\frac{|c_M(d)|}{d}
 \le t^{-0.05}\sum_d\frac{|c_M(d)|}{d^{0.9}}
 \ll\exp(-0.05\log t+O(L^{0.2})).
$$
Both ranges are $O_A(L^{-A})$, uniformly in $M$. Subtract at $2U$ and $U$. $\square$

**Corollary 4.2 (benchmark-only cancellation).** If $S_r\ll X\log N$, $\operatorname{Li}(J_r)\ll X/\log N$, and $\mathfrak S(Nr)\ll\log\log(3N)$ on $(r,N)=1$, then for any fixed $A>0$ the chosen model contribution
$$
 \mathcal C_{\mathrm{model},1}=
 -\sum_{\substack{r\sim x\\(r,N)=1}} S_r\mathfrak S(Nr)\operatorname{Li}(J_r)
 \sum_{\substack{U<u\le2U\\(u,Nr)=1}}\frac{\mu(u)g(u)}u
 =O_A(xX^2/L^A).
$$
**Scope:** This does not estimate the actual coupled-prime count. In the notation of Section 5, since $\mathcal C_1=\mathcal E_1+\mathcal C_{\mathrm{model},1}$ and $\mathcal C_{\mathrm{model},1}=O_A(xX^2/L^A)$ for every fixed $A$, the assertion $|\mathcal E_1|\ll_\delta xX^2/L^{4+2\delta}$ is equivalent (up to adjusted implied constants) to $|\mathcal C_1|\ll_\delta xX^2/L^{4+2\delta}$. Thus benchmark subtraction alone does not reduce the difficulty of the target.

# 5. The exact unresolved first-block discrepancy

Let
$$
 D(u)=\sum_{\substack{r\sim x\\(u,Nr)=1}}S_r(K_{r,u}-\mathcal K_{r,u}),
 \qquad
 \mathcal E_1=-\sum_{U<u\le2U}\mu(u)D(u).
$$
Then the exact first-block decomposition is
$$
 \boxed{\mathcal C_1=\mathcal E_1+\mathcal C_{\mathrm{model},1}.}
$$
The **proposed sufficient first-block target**, not proved here, is
$$
 \boxed{|\mathcal E_1|\ll_\delta xX^2/L^{4+2\delta}.}
$$
Even successful proof of this target would leave the other switched cofactor blocks, moderate $v$, distinct-pair diagonal, and DZ-to-M3C transfer obligations to verify.

**Proposition 5.1 (parity-sector bookkeeping).** Set $W(u)=\sum_{\substack{r\sim x\\(u,Nr)=1}}S_rK_{r,u}\ge0$ and $W^\pm=\sum_{\substack{U<u\le2U\\\mu(u)=\pm1}}W(u)$. Then, exactly,
$$
 \mathcal C_1=W^- - W^+.
$$
**Proof.** Substitute Lemma 2.1 into the definition of $\mathcal C_1$ and split according to the two nonzero values of $\mu(u)$. Neither $W^+$ nor $W^-$ is individually negligible merely because their modeled difference is small. $\square$

# 6. Further exact identities

**Proposition 6.1 (reverse-core determinant).** Fix $q_1\ne q_2$, $(q_2,u)=1$, and let $a q_2\equiv N\pmod u$. Write $r=a+ut$,
$$
 v(t)=\frac{N-aq_2}{u}-q_2t,
 \qquad s_1(t)=N-aq_1-uq_1t.
$$
Then their determinant is
$$
 (-q_2)(N-aq_1)-(-uq_1)\frac{N-aq_2}{u}=N(q_1-q_2).
$$
This exact identity supplies no prime-distribution theorem.

**Proposition 6.2 (coprime splitting of Möbius).** For every integer $n\ge1$,
$$
 \mu(n)=\sum_{\substack{ab=n\\(a,b)=1}}\frac{\mu(a)\mu(b)}{2^{\omega(n)}}.
$$
For squarefree $n$ every prime divisor goes to exactly one factor in $2^{\omega(n)}$ ordered ways; otherwise all coprime factorizations contain a factor on which Möbius vanishes. The exact identity induces a Type-I/Type-II **bookkeeping partition** but does not supply a separable coefficient bound. In particular primes $n$ occur only in the $(1,n)$ and $(n,1)$ factors.

# 7. Classical majorants, exceptional sectors, and diagonal

**Proposition 7.1 (Brun–Titchmarsh majorant).** Assume $Q_r$ consists of primes in an interval of length $O(X)$ with $\log X\asymp L$, and $X\ge u^{1+\varepsilon}$ for a fixed $\varepsilon>0$ throughout $U<u\le2U$. For $(u,Nr)=1$, the congruence on $q_2$ is one reduced residue class modulo $u$. Brun–Titchmarsh gives $\left|\{q_2\in Q_r:q_2\equiv N\bar r\pmod u\}\right|\ll X/(\varphi(u)L)$. Since $\Lambda(v)\le L$, we have $K_{r,u}\ll X/\varphi(u)$. Moreover, $Q_r$ is a set of primes inside an interval of length $O(X)$ near magnitude $\asymp X$, coverable by $O(1)$ dyadic intervals. By the standard Chebyshev upper bound for the number of primes in these intervals, $|Q_r|\ll X/L$, whence
$$
 S_r=\sum_{q_1\in Q_r}\Lambda(N-rq_1)\le L|Q_r|\ll X.
$$
Consequently, using the elementary identity $n/\varphi(n)=\sum_{d\mid n}\mu(d)^2/\varphi(d)$,
$$
 \sum_{U<u\le2U}\frac1{\varphi(u)}\ll1,
 \qquad |\mathcal C_1|\ll xX^2.
$$
This baseline uses actual prime support for $q_1$ and $q_2$ but does not require a two-prime asymptotic or signed cancellation.

**Proposition 7.2 (exceptional $r$ are negligible).** If $(r,N)>1$, fix a prime $p\mid(r,N)$. For any $q_1\in Q_r$, $p\mid N-rq_1$, hence $\Lambda(N-rq_1)\ne0$ only when $N-rq_1=p^k$. For fixed $r$ and each exponent $k$, the value $q_1=(N-p^k)/r$ is unique. Therefore $S_r\ll L^2$ (or $\ll L^3$ harmlessly). Combining with the bound $K_{r,u}\ll X/\varphi(u)$ and the reciprocal-totient average gives
$$
 \sum_{\substack{r\sim x\\(r,N)>1}}S_r
 \sum_{\substack{U<u\le2U\\(u,Nr)=1}}|M_U(u)|K_{r,u}
 \ll xXL^3=o_A(xX^2/L^A)
$$
for every fixed $A$, as $X$ grows as a fixed positive power of $N$. This justifies treating exceptional $r$ separately and setting their chosen local model to zero.

**Proposition 7.3 (proper prime powers in $v$).** Restrict $K_{r,u}$ to $v=p^k$ with $k\ge2$. The number of possible pairs $(u,p^k)$ with $u\asymp U$ and $up^k\ll N$ is at most $O(U\sqrt N L)$; this is deliberately a coarse uniform bound (a stronger count may be possible). For each pair, $rq=N-up^k$ has at most $\tau(N-up^k)\ll_\varepsilon N^\varepsilon$ integer factorizations. Since $S_r\ll XL$, $\Lambda(p^k)\le L$ and $|M_U(u)|\le1$ in this block, the contribution to $\mathcal C_1$ is
$$
 O_\varepsilon\bigl(XU\sqrt N N^\varepsilon L^3\bigr)
 =o_A(xX^2/L^A)
$$
for the frozen ranges $x\asymp N^{0.5505}$--$N^{0.5555}$, $X\asymp N^{0.447}$, $U=N^{0.02}$, and sufficiently small fixed $\varepsilon>0$. This applies to the original signed arithmetic sum, not to a hypothetical prime-pair asymptotic.

**Proposition 7.4 (distinct-slope diagonal).** In $q_1=q_2=q$, a nonzero term contains $\Lambda(s)\Lambda(s/u)$ with $s=N-rq$, $U<u\le2U$, and $\mu(u)\ne0$. Thus $s=p^k$ and $s/u=p^j$, forcing $u=p^{k-j}$; squarefreeness forces $u=p$ and $k\ge2$. There are $O(UL)$ choices of $(p,k)$ and at most $\tau(N-p^k)\ll_\varepsilon N^\varepsilon$ factorizations $N-p^k=rq$. With the at-most $L^2$ logarithmic weight, the diagonal is
$$
 O_\varepsilon(UN^\varepsilon L^3)=o_A(xX^2/L^A)
$$
for every fixed $A$ and sufficiently small $\varepsilon>0$. The first-block product can therefore be converted to the distinct-slope form with a power-negligible correction; this does not settle the other DZ sectors.

A stronger **dimension-two upper-bound sieve** remains provisional until its coefficient dependencies, local exceptional factors, prime powers and endpoint uniformity are checked. Upper bounds alone cannot establish Möbius-sign cancellation.

# 8. What finite checks do and do not prove

The separately controlled verification script \`tests/test_identities.py\` deterministically checks (over finite bounded inputs): the first-block truncated divisor identity; a local residue-count formula under explicit coprimality conditions; the reverse-core determinant; the Möbius coprime-factorization identity; the exceptional local-root counterexample; and the decomposition of a finite product into its distinct-slope terms plus diagonal. Every finite test is an example and **does not imply** an asymptotic theorem. A finite-run execution record may be supplied by the author upon request; the working manuscript is not an authorization to copy or reuse proprietary source code.

# 9. Conditional Fourier-complexity criterion and five-gate audit

**Proposition 9.1 (conditional additive-approximation criterion, NOT verified for $D$).** Suppose on $U<u\le2U$ we have $D(u)=\sum_{j=1}^J c_j e(\alpha_j u)+R(u)$ and, for some fixed $B>0$,
$$
 \sum_j|c_j|\ll (xX^2/U)L^B,
 \qquad \sum_{U<u\le2U}|R(u)|\ll xX^2/L^{4+2\delta}.
$$
Then the standard uniform Davenport bound $\sup_\alpha|\sum_{U<u\le2U}\mu(u)e(\alpha u)|\ll_A U/L^A$ implies $|\mathcal E_1|\ll_\delta xX^2/L^{4+2\delta}$ by choosing $A>B+4+2\delta$. Davenport’s uniform exponential-sum estimate in this generality is commonly obtained with ineffective constants arising from Siegel-type inputs, so the derived constant is not asserted effective. This implication is elementary **conditional on the unproved coefficient-norm and remainder bounds**; it offers no result about our actual $D(u)$ without them.

**Five-gate audit:**

1. **Precision:** Freeze the original M3C and auxiliary DZ variables separately; retain $q_2$'s prime indicator, $\Lambda(v)$, and diagonal handling.
2. **Relevance:** A first-block estimate contributes to, but does not finish, the proposed all-chamber DZ theorem; a certified DZ-to-M3C transfer is also required.
3. **Alternatives:** Affine $t$-sums, reverse-core $t$-sums, coprime Möbius splitting, and Fourier complexity were considered as research *routes*.
4. **First gap:** No applicable theorem proves uniform signed orthogonality of $\mu(u)$ to the genuine $D(u)$ at the required scale.
5. **Reusable content:** The exact identities and classical-input weighted Möbius lemma can be independently inspected and tested.

# 10. References and priority considerations

These are methodological references, not endorsements of this research program:

- Classical zero-free-region input: the de la Vallée Poussin prime number theorem remainder $M(y)=\sum_{n\le y}\mu(n)\ll y\exp(-c\sqrt{\log y})$, together with partial summation; cf. H. Davenport, *Multiplicative Number Theory* (revised by H. L. Montgomery), 3rd ed., Springer, 2000, chapters on zeta zero-free regions and the prime number theorem. No theorem number is asserted without a page-level check.
- H. Iwaniec and E. Kowalski, *Analytic Number Theory*, American Mathematical Society Colloquium Publications 53 (2004), chapters on the prime number theorem and zero-free regions. Classical input for the quantified Mobius summations in (C1.U3).
- H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*, Cambridge Studies in Advanced Mathematics 97 (2007), prime-number-theorem and zero-free-region chapters. Alternative classical source for (C1.U3).
- J. Friedlander and H. Iwaniec, *Opera de Cribro*, AMS (2010), classical sieve methods.
- K. Matomäki and M. Radziwiłł, “Multiplicative functions in short intervals,” *Annals of Mathematics* **183** (2016): short averages, not arbitrary $\mu(u)D(u)$.
- K. Matomäki, M. Radziwiłł and T. Tao, “An averaged form of Chowla's conjecture,” *Algebra & Number Theory* **9** (2015): specialized shifted multiplicative correlations, not the present joint-prime discrepancy.
- H. Davenport, “On some infinite series involving arithmetical functions (II),” *Quarterly Journal of Mathematics, Oxford Series* **8** (1937), 313–320 (uniform Möbius exponential-sum method; ineffective constants in the general uniform estimate).
- H. L. Montgomery and R. C. Vaughan, “The large sieve,” *Mathematika* **20** (1973), 119–134; citation to the classical Brun–Titchmarsh framework.
- H. L. Montgomery and R. C. Vaughan, “The exceptional set in Goldbach's problem,” *Acta Arithmetica* **27** (1975), 353–370.
- G. Bhowmik and L. Grimmelt, “The exceptional set of the Goldbach problem,” arXiv:2607.27282 (2026). Journal metadata intentionally omitted pending a fresh source-level verification.

**Priority notice:** A literature search located other recent *unrelated* preprints on signed Möbius–prime and Goldbach-style architectures. No priority, novelty, or originality assertion is made for the lemmas in this release without a systematic comparison. This research release is a transparent public audit package rather than a claim to solve Goldbach.

- Project source register: S2C Exact Structured Term Matching Audit (30 Oct 2026), S2D Deterministic K Asymptotic Audit (30 Oct 2026), S2D Stage 1 Independent Referee Audit (30 Oct 2026), C1-05 Integrated Component 1 Certificate (7 Nov 2026), ES-09D Final Small-Error Integration Certificate (30 Oct 2026), C3 FI 9.17 Direct Source Audit (7 Nov 2026). These are unpublished project sources, not independent external certifications.

# 11. Conclusion

For the explicitly versioned frozen support, the integrated Component 1 and Component 3 arguments give a paper-level reduction of the selected-strip prime count to the signed large-divisor tail. Separately, the signed Möbius weights in the chosen first-block arithmetic model exhibit rapid decay under standard zero-free-region input. The corresponding genuine prime-pair discrepancy $\mathcal E_1$ remains beyond the established arguments. The auxiliary DZ estimate, the original Component 2 matching theorem, and Binary Goldbach remain **OPEN**. The purpose of this release is to provide exact, falsifiable statements and reproducible checks for independent mathematicians.


# Author disclosure and licensing

**Sole author:** Dr. Gregory C. Stamp, Independent Researcher.

**AI research assistance:** OpenAI ChatGPT (drafting, mathematical checking, reproducibility and document assembly), Anthropic Claude (independent AI referee report), and xAI Grok (adversarial mathematical discussions). These systems are not listed as authors. AI review does not constitute peer review by a human mathematical referee.

**Manuscript license:** © 2026 Dr. Gregory C. Stamp. This manuscript is licensed under the Creative Commons Attribution 4.0 International License (CC BY 4.0). The license applies to this manuscript only. Original research source code is All Rights Reserved and is not covered by this manuscript license.
