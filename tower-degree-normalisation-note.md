# Probability normalisation and Wasserstein rate for the tower degree census

**Source-level mathematical note — 25 October 2026.** All five requested Lean files and triage §2 were read. No Lean executable, build, toolchain installation, or project modification was used. The deductions below are ordinary mathematical proofs from the source statements, not newly kernel-checked results. Exact rational spot checks at levels 0–10 corroborated the displayed mean and transport-mass identities; they are not substitutes for the proofs.

## 1. Objects and existing results

Put \(q\in\mathbb N\), \(D=2^{q+3}\), \(N=2^q=D/8\), \(v_t=8t+4\), and \(c_t=\mathrm{censusT}(q,t)\), for \(0\le t<N\). Define
\[
 M_k=\sum_{t=0}^{N-1}c_t v_t^k,\qquad x_t=v_t/D=(t+\tfrac12)/N.
\]
The census counts **ordered admissible index pairs**, not arbitrary zero divisors or a sampling weighted by degree. Here admissible means nonzero distinct indices less than \(D\). The connection is `degreeCount` in `TowerDegreeCensus.lean:10`, together with `degreeCount_eq_censusT` at line 469 of that file and its degree quantisation/bounds. Use the source's degree statistic \(v\); do not silently change the algebra-dimension convention or insert a graph-degree factor of two.

Distinguish the finite subprobability measure and the empirical probability law:
\[
 \sigma_D=D^{-2}\sum_t c_t\delta_{x_t},\qquad
 Z_D=\sigma_D(\mathbb R)=M_0/D^2,\qquad
 P_D=\sigma_D/Z_D=M_0^{-1}\sum_t c_t\delta_{x_t}.
\]
Write \(\nu=\mathrm{censusLimitMeasure}\) and \(\mu_k=\mathrm{limitMoment}(k)=\int x^k\,d\nu\). The limit is a probability measure supported on \([0,1]\), with \(\mu_1=1/2\).

All Lean source references below are relative to
`user/workspace/uploads/try/sovereign/Sovereign/Combinatorics/`:

| File and location | Existing statement used |
|---|---|
| `TowerDegreeMoments.lean:78,125,177` | `censusMoment0_formula`, `censusMoment1_formula`, `censusMoment2_formula` |
| `TowerDegreeMomentRate.lean:28,65,75` | `censusMoment_rate`, `censusMoment_zero_rate`, `censusMoment_rate_measure` |
| `TowerDegreeLimitLaw.lean:200,213` | `censusMoment_poly` (degree \(k+2\), vanishing next coefficient for \(k\ge1\)); `limitMoment_one` |
| `TowerDegreeLimitMeasure.lean:62,210` | `censusT_wing_decomposition`, `censusIntegral_eq` |
| `TowerDegreeLimitMeasure.lean:269,515,522` | support, `censusLimitMeasure_moment`, `censusLimitMeasure_isProbability` |
| `TowerDegreeLimitDensity.lean:31,86` | `tendsto_census_average`, `censusLimitDensity_symm` |
| `TowerDegreeAsymptotics.lean:56,66,77,87` | existing rational mean cancellation/decomposition, mean-shift identity, and symmetrised mean |

**Correction to the triage's opportunity assessment:** probability-normalised weak convergence is already present in `tendsto_census_average`. The mean decomposition is also already present algebraically in `TowerDegreeAsymptotics.lean`, beyond the five requested files. Those theorems use a declared rational formula; the census moment theorems connect that formula to the actual census. Neither the mean identity nor probability weak convergence should be described as missing or first obtained here.

## 2. Exact count and mean

The source moment statements give, without asymptotics,
\[
 \boxed{M_0=(D-1)(D-2)},\qquad
 \boxed{2M_1=D^3-28D+48}.
\]
Since \(D\ge8\), all denominators below are positive. Factor and cancel:
\[
 D^3-28D+48=(D-2)(D-4)(D+6),
\]
\[
 \mathbb E_{P_D}[X]
 =\frac{M_1}{DM_0}
 =\frac{(D-4)(D+6)}{2D(D-1)}
 =\boxed{\frac12+\frac{3(D-8)}{2D(D-1)}}.
\]
The last equality follows because
\((D-4)(D+6)-D(D-1)=3(D-8)\).
Thus the excess mean is zero at \(D=8\), positive thereafter, and
\[
 \mathbb E_{P_D}[X]=\frac12+\frac{3}{2D}-\frac{21}{2D^2}+O(D^{-3}).
\]
In contrast,
\[
 \int x\,d\sigma_D=\frac{M_1}{D^3}
 =\frac12-\frac{14}{D^2}+\frac{24}{D^3},\qquad
 Z_D=1-\frac3D+\frac2{D^2}.
\]
**There is no contradiction with `censusMoment_rate`.** That theorem bounds positive moments of \(\sigma_D\), not of \(P_D\). Its separate zeroth-order theorem already records the \(D^{-1}\) mass defect.

## 3. Leading correction for every fixed positive moment

For fixed \(k\ge1\), let
\[
 a_k(D)=M_k/D^{k+2}=\mu_k+r_k(D),\qquad |r_k(D)|\le C_kD^{-2}.
\]
This is exactly the existing rate theorem. Then
\[
 p_k(D):=\mathbb E_{P_D}[X^k]=\frac{a_k(D)}{Z_D},
\]
\[
 \boxed{p_k(D)-\mu_k-\frac{3\mu_k}{D}
 =\frac{r_k(D)+\mu_k(7D^{-2}-6D^{-3})}{Z_D}}.
\]
Indeed, \(1-(1+3/D)Z_D=7D^{-2}-6D^{-3}\). As \(Z_D\ge Z_8=21/32\), and \(\mu_k>0\), this gives the explicit bound
\[
 \left|p_k(D)-\mu_k-\frac{3\mu_k}{D}\right|
 \le\frac{C_k+7\mu_k}{Z_DD^2}
 \le\frac{32(C_k+7\mu_k)}{21D^2}.
\]
In particular \(D(p_k(D)-\mu_k)\to3\mu_k\), so every fixed positive moment has an asymptotically nonzero \(D^{-1}\) correction after probability normalisation. Constants here may depend on \(k\); no uniform-in-order assertion is intended. At \(k=0\), \(p_0=\mu_0=1\) exactly, and this positive-order formula does not apply.

For a second coefficient, put \(\beta_k=[z^k]\mathrm{censusMomentPoly}(k)(z)\). The polynomial representation and vanishing \(z^{k+1}\) coefficient imply
\[
 p_k(D)=\mu_k+\frac{3\mu_k}{D}
       +\frac{7\mu_k+\beta_k}{D^2}+O_k(D^{-3}).
\]
For example, the source's second-moment formula gives
\(p_2=11/30+11/(10D)-623/(30D^2)+O(D^{-3})\), consistent with the general expression.

## 4. Wasserstein-1: explicit lower and matching-order upper bounds

Use cost \(|x-y|\) on \(\mathbb R\). For any coupling of \(P_D\) and \(\nu\),
\(\mathbb E|X-Y|\ge|\mathbb EX-\mathbb EY|\). Therefore
\[
 \boxed{W_1(P_D,\nu)\ge L_D:=\frac{3(D-8)}{2D(D-1)}}.
\]
This requires no transport duality theorem. In particular \(DL_D\to3/2\), though the mean bound is uninformative at \(D=8\).

**The wing decomposition does resolve a matching \(O(D^{-1})\) upper bound.** Here is a complete coupling argument, rather than an inference from moment convergence.

For \(q\ge1\), set \(h=1/N=8/D\), and define
\[
 a_m=2^{-(m+2)},\quad c_m=\frac38-\frac3{2^{m+6}},
\]
\[
 A_q=\frac{21}{32}\lambda|_{[0,1]}
   +\sum_{m=0}^{q-2}c_m
        (\lambda|_{[0,a_m]}+\lambda|_{[1-a_m,1]}),
 \qquad T_q=\nu-A_q.
\]
An empty finite sum is zero. Let \(Q_h\) send each cell \([th,(t+1)h]\) to its midpoint \(x_t\); endpoint choices have zero Lebesgue mass. For every retained wing, \(a_m/h=2^{q-m-2}\) is an integer. Thus the density of \(A_q\) is constant on each cell. The exact source identity `censusIntegral_eq` consequently gives the measure identity
\[
 \sigma_D=(Q_h)_\# A_q+b_D\delta_{1-h/2},\qquad
 b_D=\frac{6(2^{q+2}-1)}{D^2}=\frac3D-\frac6{D^2}.
\]
Equality can be read directly from its finite midpoint sums (or tested against continuous functions on the compact support).

The omitted-wing mass is an exact geometric tail:
\[
 \begin{aligned}
 t_D:=T_q(\mathbb R)
 &=\sum_{m=q-1}^{\infty}2c_ma_m\\
 &=\sum_{m=q-1}^{\infty}
       \left(\frac3{16}2^{-m}-\frac3{128}4^{-m}\right)\\
 &=\frac38\,2^{-(q-1)}-\frac1{32}\,4^{-(q-1)}
 =\boxed{\frac6D-\frac8{D^2}}.
 \end{aligned}
\]
Write \(s_D=A_q(\mathbb R)=1-t_D\), so \(s_D+b_D=Z_D\). Since \(Z_D<1\),
\[
 R_D:=P_D-(Q_h)_\# A_q
 =(Z_D^{-1}-1)(Q_h)_\# A_q
       +(b_D/Z_D)\delta_{1-h/2}
\]
is a **nonnegative** measure of mass \(1-s_D=t_D\). Couple the \(A_q\) portion of \(\nu\) to its midpoint image, a submeasure of \(P_D\). Its cost is exactly
\[
 \int |x-Q_h(x)|\,dA_q(x)=\frac h4s_D,
\]
because \(\int_{th}^{(t+1)h}|x-x_t|\,dx=h^2/4\) and the density is cellwise constant. Couple the remaining measures \(T_q\) and \(R_D\), both of mass \(t_D>0\), by \(t_D^{-1}T_q\otimes R_D\). Their supports lie in \([0,1]\), so this part costs at most \(t_D\). The sum of these two couplings has exactly the required probability marginals. Hence
\[
 \boxed{W_1(P_D,\nu)\le\frac{h s_D}{4}+t_D
 =\frac8D-\frac{20}{D^2}+\frac{16}{D^3}<\frac8D}
 \qquad(q\ge1).
\]
At \(q=0\), \(P_8=\delta_{1/2}\) and \(W_1(P_8,\nu)\le1/2<8/D\).

For every tower dimension \(D\ge16\), therefore,
\[
 \boxed{\frac4{5D}\le L_D\le W_1(P_D,\nu)
       \le\frac8D-\frac{20}{D^2}+\frac{16}{D^3}},
\]
since \((D-8)/(D-1)\ge8/15\). This proves **\(W_1(P_D,\nu)=\Theta(D^{-1})\)** in ordinary mathematics, conditional only on the inspected source statements. It does **not** identify an optimal constant, show \(DW_1\) has a limit, or make the mean lower bound an equality. The endpoint-unbounded density causes no logarithmic loss here: retained wings align exactly with the grid and the missing tail has mass \(O(D^{-1})\).

There is no unresolved analytic lemma for the order bound above. For eventual formalisation, the key additional transport lemma to implement is precise: if \(\nu=A+T\), \(P=Q_\#A+R\) are probabilities on \([0,1]\), \(T,R\ge0\) have equal mass \(t\), and \(\int|x-Q(x)|dA\le\varepsilon\), then \(W_1(P,\nu)\le\varepsilon+t\). Its proof is exactly the sum of the graph coupling of \(A\) and the normalised product coupling of \(T,R\). The source-to-measure identity and the cell-integral evaluation above also need formal Lean implementations. No uncompiled Lean draft is included, and no new formal theorem is claimed.

## 5. Prior-work check and limits on attribution

**Internal prior work.** The table in §1 identifies results already in this project. In particular, `mean_degree_decomposition` already contains the \(3/2\) mean shift before division by \(D\), and `tendsto_census_average` already handles the probability law. The contribution of this note is their explicit synthesis with the moment-rate theorem and a quantitative wing coupling; this is not a claim of publication priority.

**External literature, checked 25 October 2026.** A targeted web search and CiteRight report 1630839 identified two directly relevant publications; their accessible arXiv introductions and relevant structural sections were inspected, and Crossref metadata independently confirmed both 2021 journal publication dates:

1. S. Zhilina, *Orthogonality graphs of real Cayley–Dickson algebras. Part I: Doubly alternative zero divisors and their hexagons*, International Journal of Algebra and Computation (2021), DOI [10.1142/S0218196721500326](https://doi.org/10.1142/S0218196721500326). [Accessible text](https://arxiv.org/html/2608.28176v1). **From CiteRight, checked against accessible text.** Section 6 classifies basis-pair zero divisors and their orthogonality conditions; the paper also treats hexagons and double hexagons. It is structural prior work, not evidence for this note's probability correction or Wasserstein bound.
2. S. Zhilina, *Orthogonality graphs of real Cayley–Dickson algebras. Part II: The subgraph on pairs of basis elements*, International Journal of Algebra and Computation (2021), DOI [10.1142/S0218196721500338](https://doi.org/10.1142/S0218196721500338). [Accessible text](https://arxiv.org/html/2608.28163v1). **From CiteRight, checked against accessible text.** Theorem 4.6 supplies an inductive graph construction; Corollary 4.9 gives component counts/sizes; Proposition 4.10 and Lemma 5.1 discuss degrees. This is particularly close prior work for the finite graphs. Its line/projective and sign conventions must be matched to the ordered-pair census before identifying degree distributions. The 2026 arXiv posting should not be mistaken for the journal publication date.

CiteRight also suggested Moreno's foundational zero-divisor paper, Sbarra–Zanardo on zero-divisor functors, and Meroni–Reinke–Wang on algebraic degrees of Wasserstein distances. These do not verify the specific quantitative claim here: the first returned no usable abstract, the second concerns a general ring framework, and the third concerns algebraic complexity rather than this convergence rate. They are not used as supporting citations.

No matching probability-moment correction or Wasserstein rate was located in the inspected external material. That limited negative search does **not** establish originality. In particular, the algebra of normalisation and the coupling estimate are elementary consequences once the existing census and wings are known. A stronger priority assessment would require tracing the recursive degree formulas through Zhilina's references (including de Marrais) and matching conventions in detail.
