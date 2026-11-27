# Eliminate the sign assumption in unrestricted and isotropic nonhomogeneous Morrey

23 November 2026. Elementary hand reduction, not a new solution or novelty claim. Assume the homogeneous isotropic result as a working hypothesis; the following reduction does not require it.

**Theorem.** In the finite-valued planar problem, RC implies QC for all integrands if and only if it does for strictly positive integrands. The same equivalence holds with isotropy imposed but without homogeneity.

Proof. Given a strict violation at A by a periodic Lipschitz test map, let X=A+Dphi and Delta=average F(X)-F(A)<0. F is continuous by finite-valued rank-one convexity, hence bounded on the compact ball containing X and A. Set G_e=exp(e F) for e>0. Composition with a convex increasing scalar function preserves RC, and G_e>0 globally, preserving any rotational invariance. Uniform Taylor expansion on the bounded range gives J(G_e)=e Delta+O(e^2), strictly negative for small e. The converse is immediate.

An even stronger reduction holds: it suffices to prove QC for positive smooth coercive uniformly strongly RC functions. First convolve F in matrix space with a nonnegative smooth compactly supported radial mollifier; this preserves RC and isotropy and converges uniformly on the witness ball. The strict gap survives. Exponentiate as above and add eta |X|^2, for eta>0 small enough to preserve the gap. The resulting function is smooth, positive, coercive and has rank-one Hessian at least 2 eta |H|^2 globally. All perturbations preserve isotropy if originally present. No uniform growth upper bound or homogeneous degree is asserted.

More explicitly, after exponentiation let gap=-d<0, and S=average |A+Dphi|^2-|A|^2=average |Dphi|^2>=0. Taking eta=d/(2(1+S)) leaves gap <=-d/2. Thus the positive smoothing restriction is logically equivalent to the full conjecture, not just a sufficient subclass. The construction works for arbitrary finite matrix dimensions and is elementary.

**Next gate:** prove QC for all smooth positive coercive uniformly strongly RC isotropic nonhomogeneous energies, or attack the full anisotropic class directly. The exponential non-PC example already in the ledger shows PC cannot be the conclusion. Neither positivity nor strict ellipticity supplies a uniform quantitative gradient Jensen estimate. No degree, mesh, or support-cardinality cutoff follows.

No Lean or CI run.