
# Finite-range physical separation (2026-11-26)

For c=m+2, D=c-2cos(k), define E_nu=z P_nu'(z), b_nu=Im(E_nu conj(P_nu)), S_r=sum_{j=0}^r j^2. Laurent Euler differentiation yields sum b_nu=0 and sum T_nu b_nu=-sin(k). Weighted Parseval gives sum T_nu sum_j a_nu,j^2=c. Cauchy-Schwarz gives J=sum T_nu|E_nu|^2<=c S_r. With H=sum (T_nu-D)^2 |P_nu|^2/T_nu=D sigma, the sum-of-squares identity H-2 ell sum (T_nu-D)b_nu+ell^2 J>=0 implies H+2 ell sin(k)+ell^2 c S_r>=0. Take ell=-sin(k)/(c S_r). Thus sigma>=sin(k)^2/(c S_r D)>=delta_r sin(k)^2 for delta_r=1/(c(c+2)S_r). All inequalities are pointwise at every unit z, including zeros of individual weights.

Let h=c^2/4-1=m(m+4)/4, K=1-delta_r h>0. If g=sum w_nu/T_nu, define the polynomial g_*=(g-delta_r(c/4+cos(k)/2))/K. Its degree is <=r, and D g_*-1=(sigma-delta_r sin(k)^2)/K>=0; hence it is a genuine scalar majorant. The exact majorant optimum yields (mean sigma-delta_r/2)/K>=L_r. Taking infima gives E_r >= L_r+delta_r(1/2-h L_r).

For p=r+1, t>1, c=t+t^-1, B_p=sum t^(2j)-(p+1)t^p=1/2 sum (t^j-t^(p-j))^2 >= (t^p-1)^2. When p>2, (t^p-1)^2 t^2-(t^2-1)^2 t^p=(t^p-t^2)(t^(p+2)-1)>0. Since (t^2-1)^2=4h t^2, B_p>4h t^p, h L_r=2h t^p/B_p<1/2. Therefore physical infimum strictly exceeds relaxation for every m>0, r>=2. At r=1, B_2=(t^2-1)^2; L_1=2/[m(m+4)] and the known nearest bath has that cost. The equal-cost-set result extends this conclusion to all finite individual nonnegative trigonometric rates of degree <=r.

Machine evidence: PointwiseBarrier session 30627, PointwiseBound 69274, FiniteGapBound 53276, FiniteGapStrict 10759, all exit 0; standard axioms only in printed principal declarations. See failed earlier compile logs for corrected elaboration errors. The universal proof is independent of the finite exact verifiers. This new separation does not establish sharp physical prefactors, attainment, or arbitrary nonpolynomial Golden Rule rate behavior.
