# Completing the finite chaining theorems

The first milestone is the expectation case of Dirksen's Theorem 3.5. Fix a nonempty finite index set $T$, a base point $t_0$, measurable real random variables $X_t$ with integrable increments, and two finite pseudometrics $d_1,d_2$. Suppose that for $u>0$ each increment exceeds $\sqrt u\,d_2(s,t)+u d_1(s,t)$ in absolute value with probability at most $2e^{-u}$. We seek a universal $C$ such that

$$
\mathbb E\max_{t\in T}|X_t-X_{t_0}|
\le C\bigl(\gamma_2(T,d_2)+\gamma_1(T,d_1)\bigr)
+2\max_{t\in T}\mathbb E|X_t-X_{t_0}|.
$$

Here $\gamma_\alpha$ is the infimum, over nets $N_k$, of $\max_t\sum_{k\ge0}2^{k/\alpha}d(t,N_k)$. The first net has one point and subsequent nets have at most $2^{2^k}$ points. The Lean definitions accept extended nonnegative costs. At the theorem boundary, coerce finite distances to those used by the functionals and justify finiteness before taking real values. The full moment and deviation forms can follow the finite expectation case. [Dirksen, Theorem 3.5](https://doi.org/10.1214/EJP.v20-3760)

1. Choose nets within $\varepsilon$ of the two infima. Once the level capacity exceeds $|T|$, use the whole set, choosing $t$ as its own center. This costs zero thereafter. Write $e_k(t)=2^k d_1(t,N_{1k})+2^{k/2}d_2(t,N_{2k})$. Apply `exists_common_representatives` at each level with these weights and nearest-center assignments. Write $r_k(t)$ for the representative so obtained. At the terminal level choose $r_K(t)=t$, including in a pseudometric with ties. The initial representative $r_0$ is common to all paths.
2. For $k\ge1$, count the distinct links $(r_{k-1}(t),r_k(t))$. At each end there are at most the product of the two net cardinalities, so the link count is bounded by $\exp(c2^k)$ for a numerical $c$ independent of $T$. Apply the checked `HasMixedTail.dyadic_edge_bound` to these links, taking the unused level zero empty. Define $w_k(s,t)=2^{k/2}d_2(s,t)+2^k d_1(s,t)$. The triangle inequalities and the one-step weight ratios give $w_k(r_{k-1}(t),r_k(t))\le 2e_k(t)+4e_{k-1}(t)$. This inequality is the next Lean target.
3. On the event that all links meet their thresholds, telescope the process along each path. For $v\ge1$, each threshold is at most $(1+c+v)w_k$ and the exceptional event has probability at most $2e^{-v}/(1-e^{-v})$. Integrate this bound by the layer-cake formula, using probability at most one for the initial interval. Equivalently, bound the expected maximum of the link-to-$w_k$ ratios by a numerical constant. For zero link length the increment vanishes almost surely by the tail hypothesis as $u\to\infty$. Add the base-point increment from $r_0$ to $t_0$, then let $\varepsilon\downarrow0$. Keep the constant outside the quantifiers for the process and the metrics.

The second milestone addresses the converse question for Gaussian processes. For finitely many vectors $a_t\in\mathbb R^r$, take $G\sim N(0,I_r)$, put $Y_t=\langle G,a_t\rangle$ and $d(s,t)=\|a_s-a_t\|_2$. The direction required by the rectangle CLT is the existence of a universal $C$ for which

$$
\gamma_2(T,d)\le C\,\mathbb E\max_{t\in T}Y_t .
$$

The expectation is the ordinary expected maximum. It is unchanged by a common translation of the vectors. The companion Gaussian upper bound follows by single-metric chaining once Gaussian increments and the base-point term are controlled. Together the two directions give the finite Gaussian equivalence. Infinite index sets and sample-path hypotheses can be addressed in a later release. [Talagrand, *Constructions of Majorizing Measures, Bernoulli Processes and Cotype*](https://arxiv.org/abs/math/9406216)

1. Work first on the finite image of $t\mapsto a_t$. Use `gamma_pullback` for the functional and `maximum_ae_eq_of_zero_contrasts` for process representations with coincident coordinates. Prove the Gaussian canonical-distance identity and translation invariance. A singleton has zero width after taking expectations.
2. Formalize the local growth inequality for $F(B)=\mathbb E\max_{t\in B}Y_t$ on nonempty finite subsets. For separated centers and local balls of sufficiently small relative radius, the gain over the smallest local width is at least a numerical constant times the separation times the square root of the logarithm of the number of centers. Check whether compatible proofs of Gaussian concentration for the local Lipschitz oscillations and Sudakov minoration for the centers exist on the pinned revision. For each proposed import, record its full Lean type and audit its axioms. Supply proofs for missing inputs. [Van Handel, *Probability in High Dimension*, chapter on Gaussian processes](https://swh.princeton.edu/~rvan/migrated-to-math-2018-06-20/APC550.pdf)
3. Prove the deterministic step from the growth inequality. Construct ordered partitions, bound their diameters along each branch by telescoping the local widths, and prove the cardinality bound at each admissible level. Choosing one point per cell gives a net whose distance from each member is at most the cell diameter. Apply `gamma_eq_finset` to close the Gaussian lower bound. This deterministic theorem can be developed while the Gaussian analytic estimates are underway.

For each completed step, add the declaration to `Audit.lean`, run the build and the audit, and record in the README which mathematical statement is now checked. In the rectangle-CLT project, import a fixed revision and instantiate both theorems on the signed coordinates and zero. Only the Gaussian distance may identify duplicate coordinates there. Keep the discrete distance on the original indices.
