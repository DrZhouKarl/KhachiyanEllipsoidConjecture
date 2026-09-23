# Khachiyan's Conjecture of Inscribed-Ellipsoid Cutting Inequality: Mathematical Specification and Complete Proof

## 0. Definitions

Fix an integer $n\ge1$. Work in $\mathbb R^n$ with its standard inner product and Euclidean norm. Let $\operatorname{vol}_n$ denote Lebesgue volume, $B_n=\{x:\|x\|\le1\}$, and $\kappa_n=\operatorname{vol}_n(B_n)\in(0,\infty)$.

A convex body is a compact convex set with nonempty interior. For a real symmetric positive definite matrix $A$ and a vector $a\in\mathbb R^n$, define

$$
\mathcal E(a,A)=a+AB_n.
$$

Write $X\preceq Y$ when $Y-X$ is positive semidefinite. If $X=U\operatorname{diag}(\lambda_i)U^{\mathsf T}\succ0$, define, for $p\in\mathbb R$,

$$
X^p=U\operatorname{diag}(\lambda_i^p)U^{\mathsf T}.
$$

For positive semidefinite matrices, use the same definition when $p>0$, with the convention $0^p=0$.

For a convex body $K$, define

$$
w(K)=\max\{\operatorname{vol}_n(\mathcal E(a,A)):
A=A^{\mathsf T}\succ0,\ \mathcal E(a,A)\subset K\}.
$$

The maximum exists and the maximizing ellipsoid is unique, as proved in G03. Denote this ellipsoid by $J(K)$ and its center by $c(K)$. Define the exact constant

$$
r_* =\frac{e^{1/2}}2=\frac{\sqrt e}{2}.
$$

## 1. Main statements

**T01: Geometric upper bound.** For every $n\ge1$, convex body $K\subset\mathbb R^n$, and vector $p\ne0$, let

$$
H=\{x:p^{\mathsf T}(x-c(K))\ge0\}.
$$

Then $K\cap H$ is a convex body and

$$
w(K\cap H)\le r_*w(K).
$$

Replacing $p$ by $-p$ gives the same conclusion for the other side.

**T02: Uniform optimality.** For every real number $r<r_*$, there exist an integer $n\ge2$, a convex body $K\subset\mathbb R^n$, and a closed halfspace $H$ whose boundary passes through $c(K)$ such that

$$
w(K\cap H)>r\,w(K).
$$

## 2. Geometry and maximality

### G01: Volume, support functions, and affine transformations

For $A\succ0$,

$$
\operatorname{vol}_n(\mathcal E(a,A))=\kappa_n\det A,
\qquad h_{\mathcal E(a,A)}(v)=v^{\mathsf T}a+\|Av\|.
$$

Here $h$ denotes the support function. The volume identity follows from translation invariance of Lebesgue measure and its determinant scaling under invertible linear maps. The support identity follows from

$$
\max_{\|y\|\le1}v^{\mathsf T}(a+Ay)
=v^{\mathsf T}a+\max_{\|y\|\le1}(Av)^{\mathsf T}y
$$

and the Cauchy--Schwarz inequality. If $Av\ne0$, the maximum is attained at $y=Av/\|Av\|$.

Every invertible linear image $CB_n$ equals $AB_n$, where $A=(CC^{\mathsf T})^{1/2}\succ0$: the matrix $A^{-1}C$ is orthogonal. Consequently, an invertible affine transformation gives a bijection on nondegenerate ellipsoids and scales all volumes by the same factor. Maximality among inscribed ellipsoids and volume ratios are therefore preserved.

For a nonempty compact convex set $K$,

$$
K=\{x:\forall v,\ v^{\mathsf T}x\le h_K(v)\}.
$$

To prove the reverse inclusion, suppose $x\notin K$. Choose $y\in K$ minimizing the distance to $x$, and put $v=x-y\ne0$. For $z\in K$, the right derivative at $t=0$ of the squared distance along $y+t(z-y)$ gives $v^{\mathsf T}(z-y)\le0$. Hence $h_K(v)\le v^{\mathsf T}y<v^{\mathsf T}x$, contradicting the assumed support inequalities.

### G02: Intermediate ellipsoid

If a convex body $K$ contains $B_n$ and $\mathcal E(b,S)$, with $S\succ0$, then

$$
\mathcal E\left(\frac b2,\left(S+\frac14bb^{\mathsf T}\right)^{1/2}\right)\subset K.
$$

**Proof.** For $v\ne0$, write $h=h_K(v)>0$ and $s=v^{\mathsf T}b$. By G01 and Cauchy--Schwarz,

$$
\|v\|\le h,\qquad \|Sv\|\le h-s,
\qquad v^{\mathsf T}Sv\le h(h-s).
$$

It follows that

$$
v^{\mathsf T}(S+bb^{\mathsf T}/4)v
\le(h-s/2)^2.
$$

Since $s\le h$, we have $h-s/2>0$. The support function of the proposed ellipsoid is therefore at most

$$
s/2+\sqrt{v^{\mathsf T}(S+bb^{\mathsf T}/4)v}\le h.
$$

The inequality also holds for $v=0$. G01 now gives the required containment.

### G03: Existence and uniqueness of the maximum-volume inscribed ellipsoid

Temporarily allow positive semidefinite shape matrices $A\succeq0$. Feasibility implies $a\in K$ and $a\pm Au\in K$, so $2\|Au\|\le\operatorname{diam}K$ for every unit vector $u$. Thus the feasible parameter set is bounded. Containment and positive semidefiniteness are preserved under limits, so this set is closed and hence compact. The continuous function $\det A$ attains a maximum. Since $K$ contains a ball of positive radius, the maximum is positive, and every maximizing matrix is positive definite.

The feasible parameter set is convex: for $y\in B_n$,

$$
(1-t)(a_0+A_0y)+t(a_1+A_1y)\in K\quad(0\le t\le1).
$$

Suppose $(a_0,A_0)$ and $(a_1,A_1)$ are two maximizing parameters. Let $C=A_0^{-1/2}A_1A_0^{-1/2}\succ0$, with eigenvalues $\mu_i>0$. The scalar inequality $(1+\mu_i)/2\ge\sqrt{\mu_i}$ gives

$$
\det\frac{A_0+A_1}{2}
=\det A_0\prod_i\frac{1+\mu_i}{2}
\ge\det A_0\prod_i\sqrt{\mu_i}
=\sqrt{\det A_0\det A_1}.
$$

If $A_0\ne A_1$, then $C\ne I$, so at least one $\mu_i\ne1$ and the inequality is strict. The midpoint would then be feasible with a larger determinant, contradicting maximality. Thus $A_0=A_1$.

If the centers differ, affine normalization gives two maximizing ellipsoids $B_n$ and $b+B_n$, with $b\ne0$. G02 produces a feasible shape matrix $(I+bb^{\mathsf T}/4)^{1/2}$ whose determinant is $\sqrt{1+\|b\|^2/4}>1$, again contradicting maximality.

### G04: Normalization and center exclusion

The affine map $x\mapsto S_*^{-1}(x-a_*)$ sends $J(K)=a_*+S_*B_n$ to $B_n$. For a candidate ellipsoid $E=\mathcal E(a,A)$ in the normalized coordinates, its volume relative to the unit ball is $\det A$, and

$$
0\notin\operatorname{int}E\quad\Longleftrightarrow\quad\|A^{-1}a\|\ge1.
$$

Indeed, the unique solution of $0=a+Ay$ is $y=-A^{-1}a$. A nondegenerate ellipsoid contained in the halfspace $p^{\mathsf T}x\ge0$ cannot contain $0$ in its interior.

Conversely, if $\rho=\|A^{-1}a\|\ge1$, choose $v=A^{-2}a\ne0$. Then

$$
\min_{x\in E}v^{\mathsf T}x
=v^{\mathsf T}a-\|Av\|=\rho^2-\rho\ge0.
$$

Thus the center-exclusion formulation is equivalent to the formulation using halfspaces through the original center.

### G05: Necessary trace condition

If $J(K)=B_n$ and $\mathcal E(b,S)\subset K$, with $S\succ0$, then $\operatorname{tr}S\le n$.

**Proof.** For $y\in B_n$, convexity gives $(1-t)y+t(b+Sy)\in K$. Consequently,

$$
tb+((1-t)I+tS)B_n\subset K\quad(0\le t\le1).
$$

Therefore $\log\det((1-t)I+tS)\le0$, with equality at $t=0$. Taking the right derivative yields $\operatorname{tr}(S-I)\le0$. This derivative can also be computed directly by diagonalizing $S$ and differentiating $\sum_i\log(1+t(\lambda_i-1))$.

## 3. Matrix analysis

### M01: Spectral calculations

For $A\succ0$, write its eigenvalues as $\lambda_i>0$ and put $\alpha=\min_i\lambda_i>0$. Then

$$
\det A=\prod_i\lambda_i,\qquad
\operatorname{tr}(A^p)=\sum_i\lambda_i^p,
\qquad A\preceq A^2/\alpha.
$$

For $p>0$ and a unit vector $u$,

$$
u^{\mathsf T}A^{2p}u\ge\alpha^{2p}.
$$

These statements follow coordinatewise in an orthonormal eigenbasis of $A$. If $X\preceq Y$, then $\operatorname{tr}X\le\operatorname{tr}Y$, since the diagonal entries of the positive semidefinite matrix $Y-X$ are nonnegative.

### M02: Order properties of inverses and fractional powers

If $0\prec X\preceq Y$, then $Y^{-1}\preceq X^{-1}$. Indeed, write $Y=X^{1/2}CX^{1/2}$. Then $C\succeq I$, hence $C^{-1}\preceq I$, and a congruence transformation gives the conclusion.

For $0<p<1$, define

$$
c_p=\left(\int_0^\infty\frac{s^{p-1}}{1+s}\,ds\right)^{-1}>0.
$$

The integral converges and is positive because $0<p<1$. The substitution $s=xt$ for $x>0$, followed by orthogonal diagonalization, gives

$$
X^p=c_p\int_0^\infty s^{p-1}X(X+sI)^{-1}\,ds.
\tag{M02.1}
$$

Since $X(X+sI)^{-1}=I-s(X+sI)^{-1}$, inverse antitonicity shows that the matrix-valued integrand is increasing in $X$. Therefore

$$
X^p\preceq Y^p\quad(0<p<1).
$$

Combining this with $(X^{1-p})^{-1}=X^{p-1}$ gives

$$
X^{p-1}\succeq Y^{p-1}\quad(0<p<1).
$$

In particular, the square root preserves matrix order.

### M03: Trace differentiation along self-adjoint directions

Let $X\succ0$, $H=H^{\mathsf T}$, and $0<p<1$. At $t=0$,

$$
\frac d{dt}\operatorname{tr}((X+tH)^p)
=p\operatorname{tr}(X^{p-1}H).
$$

**Proof.** The matrix $X+tH$ remains positive definite in a neighborhood of zero. Matrix inversion is differentiable on the invertible matrices, as its entries are rational functions expressed using the adjugate and determinant. Put $R_s=(X+sI)^{-1}$. Taking the trace in (M02.1) and differentiating yields

$$
D[\operatorname{tr}(X^p)](H)
=c_p\int_0^\infty s^p\operatorname{tr}(R_s^2H)\,ds.
$$

Differentiation under the integral is justified as follows. In a positive definite neighborhood of $X$ within the self-adjoint matrices, the norm of the differentiated integrand is bounded by $Cs^p$ near zero and by $Cs^{p-2}$ at infinity. Both bounds are integrable. In an eigenbasis of $X$, integration by parts gives

$$
c_p\int_0^\infty\frac{s^p}{(\lambda+s)^2}\,ds
=p\lambda^{p-1},
$$

because the boundary term $s^p/(\lambda+s)$ vanishes at both endpoints. This proves the formula. The argument requires $H$ to be self-adjoint but does not require $XH=HX$.

### M04: Quantitative rank-one trace estimate

Let $A\succ0$, $\alpha=\lambda_{\min}(A)$, $\|u\|=1$, and $b=Au$. If $M\succ0$ and $m>0$ satisfy

$$
M\preceq\frac m{\alpha^2}A^2,
$$

then, for every $0<p<1$ and $t\ge0$,

$$
\operatorname{tr}((M+tbb^{\mathsf T})^p)-\operatorname{tr}(M^p)
\ge(m+t\alpha^2)^p-m^p.
\tag{M04.1}
$$

**Proof.** Since $uu^{\mathsf T}\preceq I$, we have $bb^{\mathsf T}\preceq A^2$. Thus, for $s\ge0$,

$$
M+sbb^{\mathsf T}\preceq\frac{m+s\alpha^2}{\alpha^2}A^2.
$$

Apply the negative-power antitonicity from M02 and evaluate the resulting quadratic form on $b=Au$. This gives

$$
\begin{aligned}
b^{\mathsf T}(M+sbb^{\mathsf T})^{p-1}b
&\ge\left(\frac{m+s\alpha^2}{\alpha^2}\right)^{p-1}u^{\mathsf T}A^{2p}u\\
&\ge\alpha^2(m+s\alpha^2)^{p-1}.
\end{aligned}
$$

By M03, multiplying the left side by $p$ gives the derivative of $\operatorname{tr}((M+sbb^{\mathsf T})^p)$. Integration over $[0,t]$ proves (M04.1).

If $u$ is a unit eigenvector of $A$ corresponding to $\alpha$ and $M=(m/\alpha^2)A^2$, the perturbation changes only the eigenvalue $m$ in that direction. Equality therefore holds in (M04.1).

### M05: Diminishing trace increments

If $0\prec X\preceq Y$, $H\succeq0$, and $0<p<1$, then

$$
\operatorname{tr}((X+H)^p)-\operatorname{tr}(X^p)
\ge\operatorname{tr}((Y+H)^p)-\operatorname{tr}(Y^p).
$$

Put $Z=Y-X\succeq0$ and apply M03 to

$$
g(t)=\operatorname{tr}((X+tZ+H)^p)-\operatorname{tr}((X+tZ)^p)
$$

By M02, the derivative is $p$ times the trace of a negative semidefinite matrix multiplied by $Z$, and is therefore nonpositive. Indeed, if $W\preceq0$ and $Z\succeq0$, then $\operatorname{tr}(WZ)=\operatorname{tr}(Z^{1/2}WZ^{1/2})\le0$. Integration gives the conclusion.

Equivalently, for $U,V,W\succeq0$,

$$
\operatorname{tr}((U+V+W)^p)+\operatorname{tr}(W^p)
\le\operatorname{tr}((U+W)^p)+\operatorname{tr}((V+W)^p).
$$

First take $X=W$, $Y=V+W$, and $H=U$ when $W\succ0$. Then replace $W$ by $W+\varepsilon I$ and let $\varepsilon\downarrow0$, using continuity.

## 4. Two spectral constraints and the sharp scalar bound

Throughout this section, assume $J(K)=B_n$, $\mathcal E(a,A)\subset K$, $A\succ0$, and $\rho=\|A^{-1}a\|\ge1$. Write $\alpha=\lambda_{\min}(A)$.

### R01: Two iterations

By G02 and G05,

$$
T_1=(A+aa^{\mathsf T}/4)^{1/2},\qquad
T_2=(T_1+aa^{\mathsf T}/16)^{1/2},\qquad
\operatorname{tr}T_1,\operatorname{tr}T_2\le n.
$$

The corresponding centers are $a/2$ and $a/4$, respectively. Set $u=\rho^{-1}A^{-1}a$ and $b=Au=\rho^{-1}a$, and define

$$
M_1=(A+bb^{\mathsf T}/4)^{1/2},\qquad
M_2=(M_1+bb^{\mathsf T}/16)^{1/2}.
$$

Since $bb^{\mathsf T}\preceq aa^{\mathsf T}$, M02 gives $M_j\preceq T_j$, hence $\operatorname{tr}M_j\le n$.

Define

$$
f_1(\alpha)=\sqrt{\alpha+\alpha^2/4},\qquad
f_2(\alpha)=\sqrt{f_1(\alpha)+\alpha^2/16}.
$$

Apply M04 with $(M,m,p,t)=(A,\alpha,1/2,1/4)$. Since $A\preceq A^2/\alpha$, this yields

$$
\operatorname{tr}M_1\ge\operatorname{tr}(A^{1/2})+f_1(\alpha)-\alpha^{1/2}.
$$

Moreover,

$$
M_1\preceq\left(A^2/\alpha+A^2/4\right)^{1/2}
=\frac{f_1(\alpha)}\alpha A
\preceq\frac{f_1(\alpha)}{\alpha^2}A^2.
$$

Applying M04 with $(M,m,p,t)=(A,\alpha,1/4,1/4)$ and $(M_1,f_1(\alpha),1/2,1/16)$, respectively, gives

$$
\operatorname{tr}(M_1^{1/2})-\operatorname{tr}(A^{1/4})
\ge f_1(\alpha)^{1/2}-\alpha^{1/4},
$$

$$
\operatorname{tr}M_2-\operatorname{tr}(M_1^{1/2})
\ge f_2(\alpha)-f_1(\alpha)^{1/2}.
$$

Adding these inequalities cancels the intermediate terms, so

$$
\operatorname{tr}M_2\ge\operatorname{tr}(A^{1/4})+f_2(\alpha)-\alpha^{1/4}.
$$

Label one occurrence of the minimum eigenvalue as $\lambda_1=\alpha$. M01 then gives

$$
f_j(\alpha)+\sum_{i=2}^n\lambda_i^{1/2^j}\le n,
\qquad j=1,2.
\tag{R01.1}
$$

### R02: Determinant bounds

The inequality $\log z\le z-1$ for $z>0$, together with (R01.1), yields

$$
\begin{aligned}
\log\det A
&=\log\alpha+2^j\sum_{i=2}^n\log(\lambda_i^{1/2^j})\\
&\le\log\alpha+2^j(1-f_j(\alpha)).
\end{aligned}
$$

Thus, on defining

$$
R_j(\alpha)=\alpha\exp\bigl(2^j(1-f_j(\alpha))\bigr),
$$

we obtain $\det A\le\min\{R_1(\alpha),R_2(\alpha)\}$. When $n=1$, the sums are empty and the conclusion remains valid.

For $n\ge2$, the arithmetic--geometric mean inequality also gives

$$
\det A\le\alpha\left(\frac{n-f_j(\alpha)}{n-1}\right)^{2^j(n-1)},
\qquad j=1,2.
\tag{R02.1}
$$

The base is positive because (R01.1) contains $n-1$ positive summands.

### S01: Joint scalar maximum

Put $x=\log\alpha$ and $F_j(x)=\log R_j(e^x)$. The functions

$$
\log f_1(e^x)=\frac12\log(e^x+e^{2x}/4),
\qquad
\log f_2(e^x)=\frac12\log\bigl(e^{\log f_1(e^x)}+e^{2x}/16\bigr)
$$

are convex. Indeed, $L(s,t)=\log(e^s+e^t)$ has positive partial derivatives and Hessian

$$
q(1-q)\begin{pmatrix}1&-1\\-1&1\end{pmatrix}\succeq0,
\qquad q=\frac{e^s}{e^s+e^t}.
$$

Composition with a convex function that is nondecreasing in each argument proves both asserted convexity statements. Every positive log-convex function is convex, so $F_j(x)=x+2^j(1-f_j(e^x))$ is concave for each $j$.

Let $x_0=-\log2$ and $C=1/2-\log2$. Direct calculation gives

$$
f_1(1/2)=3/4,\quad f_2(1/2)=7/8,
\quad f_1'(1/2)=5/6,\quad f_2'(1/2)=43/84,
$$

and hence

$$
F_1(x_0)=F_2(x_0)=C,\qquad F_1'(x_0)=1/6,\quad F_2'(x_0)=-1/42.
$$

The tangent bounds for concave functions imply

$$
F_1(x)\le C+\frac{x-x_0}{6},\qquad
F_2(x)\le C-\frac{x-x_0}{42}.
\tag{S01.1}
$$

Use the first bound when $x\le x_0$ and the second when $x\ge x_0$. This gives $\min(F_1,F_2)\le C$, with equality at $x=x_0$. Therefore

$$
\max_{\alpha>0}\min\{R_1(\alpha),R_2(\alpha)\}=e^C=r_*.
$$

Equivalently, the concave function $G=F_1/8+7F_2/8$ has derivative zero at $x_0$, so $\min(F_1,F_2)\le G\le C$.

## 5. Proof of T01

By G04, normalize the original maximal ellipsoid to the unit ball and represent any nondegenerate ellipsoid inscribed in the retained side as $\mathcal E(a,A)$ satisfying the center-exclusion condition. R02 and S01 give $\det A\le r_*$. Transforming back by G01 shows that its volume is at most $r_*w(K)$.

Since $c(K)$ lies in the interior of $K$, a hyperplane through this point intersects $K$ on both sides in compact convex sets with nonempty interior. Apply the preceding estimate to the maximum-volume inscribed ellipsoid of $K\cap H$ to obtain T01.

## 6. Cones and uniform optimality

### C01: Sufficient contact-point certificate

If $B_n\subset K$ and there are unit vectors $u_i$ and positive weights $c_i>0$ such that

$$
K\subset\{x:u_i^{\mathsf T}x\le1\}\quad\text{for all }i,
\qquad \sum_i c_i u_i=0,
\qquad \sum_i c_i u_i u_i^{\mathsf T}=I,
$$

then $J(K)=B_n$.

**Proof.** Every $\mathcal E(a,A)\subset K$ satisfies $u_i^{\mathsf T}a+\|Au_i\|\le1$ and $u_i^{\mathsf T}Au_i\le\|Au_i\|$. Taking weighted sums gives $\operatorname{tr}A\le\sum_i c_i=n$, so $\det A\le(\operatorname{tr}A/n)^n\le1$. The unit ball is feasible, and uniqueness follows from G03.

### C02: Explicit cones

For $n\ge2$, write $x=(t,y)\in\mathbb R\times\mathbb R^{n-1}$ and define

$$
K_n=\{(t,y):t\ge-1,\quad t+\sqrt{n^2-1}\,\|y\|\le n\}.
$$

This set is closed and convex. Its points satisfy $-1\le t\le n$ and $\|y\|\le(n+1)/\sqrt{n^2-1}$, so it is bounded and hence compact. Moreover, $B_n\subset K_n$: on the unit ball, $t\ge-1$, and Cauchy--Schwarz gives $t+\sqrt{n^2-1}\|y\|\le n$. Thus $K_n$ has nonempty interior.

Take the base normal $u_0=-e_1$ and the side normals

$$
u_v=\left(\frac1n,\sqrt{1-\frac1{n^2}}\,v\right),
\qquad v\in\{\pm e_1,\ldots,\pm e_{n-1}\}\subset\mathbb R^{n-1}.
$$

Assign weight $c_0=n/(n+1)$ to the base and weight $c_v=n^2/(2(n^2-1))$ to each side direction. The total side weight is $n^2/(n+1)$, so the first-coordinate first moment is zero and its second moment is 1. Transverse first moments and mixed second moments vanish by pairing opposite signs. Every transverse second moment is $2c_v(1-1/n^2)=1$. All $u_i$ are unit vectors and supporting directions of $K_n$. C01 therefore gives $J(K_n)=B_n$ and $c(K_n)=0$.

Take $H_n=\{t\le0\}$ and

$$
E_n=-\frac12e_1+
\operatorname{diag}\left(\frac12,\sqrt{\frac n{n-1}},\ldots,\sqrt{\frac n{n-1}}\right)B_n.
$$

Its first coordinate lies in $[-1,0]$. For every unit transverse vector $v$, its support function in the corresponding side-normal direction is

$$
-\frac1{2n}+
\sqrt{\frac1{4n^2}+\frac n{n-1}\left(1-\frac1{n^2}\right)}=1.
$$

Thus $E_n\subset K_n\cap H_n$.

### C03 and T02: Limit of the lower bounds

By feasibility and G01,

$$
\frac{w(K_n\cap H_n)}{w(K_n)}
\ge\frac{\operatorname{vol}_n(E_n)}{\kappa_n}
=\frac12\left(1+\frac1{n-1}\right)^{(n-1)/2}
\longrightarrow\frac{\sqrt e}{2}.
$$

The limit follows from $(1+1/m)^m\to e$ and continuity of the square root. For every $r<r_*$, the lower bound exceeds $r$ for all sufficiently large $n$, proving T02. It is unnecessary to prove that $E_n$ is the maximum-volume ellipsoid in the retained side.

## 7. Additional conclusions

**T03: Nonattainment in finite dimension.** Under the assumptions of R01, every nondegenerate $A$ satisfies $\det A<r_*$. If $\alpha\ne1/2$, the relevant tangent in (S01.1) is strictly below $C$. If $\alpha=1/2$ and $n\ge2$, the case $j=1$ of (R02.1) gives

$$
\det A\le\frac12\left(1+\frac1{4(n-1)}\right)^{2(n-1)}<\frac{\sqrt e}{2}.
$$

If $n=1$ and $\alpha=1/2$, the determinant is $1/2$. A one-dimensional convex body is a nondegenerate closed interval, which is itself its maximum-volume inscribed ellipsoid. Cutting at its center produces two subintervals, each of half the original length. The optimal one-dimensional cutting ratio is therefore $1/2$.

**T04: Constraint on the smallest semiaxis near equality.** Under the same assumptions,

$$
\log\frac{r_*}{\det A}\ge
\begin{cases}
\frac16\log\frac1{2\alpha},&\alpha\le1/2,\\
\frac1{42}\log(2\alpha),&\alpha\ge1/2.
\end{cases}
$$

Subtract the appropriate tangent bound in (S01.1) from $C$, using $\log\det A\le F_j(\log\alpha)$. Consequently, if $\varepsilon\ge0$ and $\det A\ge r_*e^{-\varepsilon}$, then

$$
\frac12e^{-6\varepsilon}\le\alpha\le\frac12e^{42\varepsilon}.
$$

**T05: Sequences of exact central cuts.** Suppose $K_0$ is a convex body, $K_{k+1}=K_k\cap H_k$, and each $H_k$ is a proper closed halfspace whose boundary passes through $c(K_k)$. Induction using T01 gives

$$
w(K_N)\le r_*^Nw(K_0),\qquad
\log\frac{w(K_0)}{w(K_N)}\ge N(\log2-1/2).
$$

## 8. Alternative proof of M04

Under the assumptions of M04, inverse antitonicity and M01 imply, for $s>0$,

$$
\begin{aligned}
b^{\mathsf T}(M+sI)^{-1}b
&\ge u^{\mathsf T}A^2\left(\frac m{\alpha^2}A^2+sI\right)^{-1}u\\
&\ge\frac{\alpha^2}{m+s}.
\end{aligned}
$$

The last step uses the fact that $\lambda^2/((m/\alpha^2)\lambda^2+s)$ is increasing for $\lambda>0$.

Let $N=M+tbb^{\mathsf T}$. By (M02.1), interchange of trace with finite-dimensional integration, and integration by parts,

$$
\operatorname{tr}(N^p)-\operatorname{tr}(M^p)
=p c_p\int_0^\infty s^{p-1}
\log\left(1+t\,b^{\mathsf T}(M+sI)^{-1}b\right)\,ds.
$$

More explicitly, let $L(s)=\log\det(N+sI)-\log\det(M+sI)$. Diagonalizing the fixed matrices $M$ and $N$ separately gives $L'(s)=\operatorname{tr}(N+sI)^{-1}-\operatorname{tr}(M+sI)^{-1}$. Taking the difference of traces yields $-c_p\int_0^\infty s^pL'(s)\,ds$, and integration by parts gives $p c_p\int_0^\infty s^{p-1}L(s)\,ds$.

For an invertible matrix $Q$, multilinearity of the determinant in its columns gives $\det(I+vw^{\mathsf T})=1+w^{\mathsf T}v$: terms with two or more perturbed columns vanish because those columns are proportional, and the single-column terms sum to $w^{\mathsf T}v$. Taking $Q=M+sI$, $v=tQ^{-1}b$, and $w=b$, we obtain

$$
\det(Q+tbb^{\mathsf T})=\det Q\,(1+t\,b^{\mathsf T}Q^{-1}b),
$$

and hence

$$
L(s)=\log\left(1+t\,b^{\mathsf T}(M+sI)^{-1}b\right).
$$

The boundary terms vanish: $L(s)$ has a finite limit as $s\downarrow0$, and $L(s)=O(s^{-1})$ as $s\to\infty$, while $0<p<1$. The quadratic-form lower bound above and monotonicity of the logarithm therefore give

$$
\operatorname{tr}(N^p)-\operatorname{tr}(M^p)
\ge p c_p\int_0^\infty s^{p-1}
\log\left(1+\frac{t\alpha^2}{m+s}\right)\,ds
=(m+t\alpha^2)^p-m^p,
$$

where the last identity is the scalar case of the same integral identity. This proves (M04.1).
