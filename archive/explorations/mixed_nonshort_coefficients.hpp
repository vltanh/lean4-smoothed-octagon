// Exact algebra verified by mixed_nonshort_coefficients.py.
// Returns sum(P_i/(a+c)^3 * eps^(i-2), i=2..8).
// Divide this result by 2*a*Q*(1+eps*l1)^2*q in Phi_base.
// Requires the caller's exact powi<T>(T,unsigned) helper.
template<class T>T centered_polynomial_cancelled(const T&a,const T&c,const T&eps,const T&l0,const T&l1,const T&l2){
 const T cx0=powi(a,2);
 const T cx1=a*c;
 const T cx2=2*cx1;
 const T cx3=cx0 + cx2 - 4;
 const T cx4=c*l1;
 const T cx5=powi(l2,3);
 const T cx6=cx0 + 4;
 const T cx7=a + c;
 const T cx8=powi(l1,3);
 const T cx9=c*cx8;
 const T cx10=cx7*cx9;
 const T cx11=powi(l1,2);
 const T cx12=cx3*l0;
 const T cx13=powi(l2,2);
 const T cx14=2*cx12;
 const T cx15=cx7*l2;
 const T cx16=a*l1;
 const T cx17=6*cx12*cx15*cx16;
 const T cx18=4*a;
 const T cx19=3*cx0;
 const T cx20=powi(l0,2);
 const T cx21=cx20*l2;
 const T cx22=8*cx1;
 const T cx23=cx13*cx16;
 const T cx24=powi(a,3);
 const T cx25=4*c;
 const T cx26=c*cx19 + cx25;
 const T cx27=cx16*cx20;
 const T cx28=12*c;
 const T cx29=powi(c,2);
 const T cx30=8*cx29;
 const T cx31=c*cx0;
 const T cx32=cx11*l2;
 const T cx33=cx29 + 4;
 const T cx34=3*a;
 const T cx35=2*c;
 const T cx36=cx25 + cx34;
 const T cx37=a*cx14;
 const T cx38=5*cx24;
 const T cx39=12*a;
 const T cx40=l1*l2;
 const T cx41=a*cx40;
 const T cx42=8*c;
 const T cx43=a*cx29;
 const T cx44=10*powi(a,4);
 const T cx45=powi(c,3);
 const T cx46=8*a;
 const T cx47=c*cx24;
 const T cx48=cx0*cx29;
 const T cx49=cx27*cx6;
 const T cx50=cx25 + cx38;
 const T cx51=cx21*cx6;
 const T cx52=cx11*cx15;
 const T C2=-cx3*powi(a*(l0 + l2) + cx4,2);
 const T C3=-c*cx32*(a*cx30 - 16*a + 6*cx24 - cx28 + 15*cx31) - cx0*cx13*cx14 - cx0*cx21*(c*cx18 + cx19 - 4) + cx0*cx5*cx6 - cx10*(cx1 + 4) - cx11*cx12*cx2 - cx17 - cx23*cx7*(5*cx0 + cx22 - 12) - cx27*(-cx18 + cx24 + cx26);
 const T C4=a*cx5*l1*(cx26 + cx38 + cx39) - cx1*cx11*cx20*cx6 - cx1*cx33*powi(l1,4) - cx11*cx13*(-12*cx0 - 24*cx1 - cx30 + cx44 + cx45*cx46 + 30*cx47 + 29*cx48) - 2*cx13*cx20*cx24*cx7 - cx14*cx23*(cx34 + cx35) - cx20*cx41*(cx18 + cx28 + 7*cx31 + cx38) - cx32*cx36*cx37 - cx9*l2*(7*cx24 + 18*cx31 + cx42 + 9*cx43);
 const T C5=cx40*(a*cx13*l1*(cx0*cx28 + 10*cx24 + cx29*cx34 + cx39 + cx42) - cx11*cx37*cx7 - cx15*cx18*cx20*(cx0 + 2) - cx17 - cx32*(13*a*cx45 - 4*cx0 - cx22 + 4*cx29 + cx44 + 33*cx47 + 38*cx48) - cx36*cx49 - cx9*(11*cx31 + 7*cx43 + cx46 + cx50));
 const T C6=cx52*(a*cx13*l1*(10*cx0 + cx22 + cx33) - 3*cx1*cx7*cx8 - cx14*cx41 - cx32*(14*cx31 + 10*cx43 + cx50) - cx34*cx51 - cx49);
 const T C7=a*cx15*cx8*(-cx10 + cx13*cx7*l1*(5*a + cx35) - cx51 - cx52*(a + cx25));
 const T C8=a*cx13*powi(cx7,2)*powi(l1,5)*(-cx4 + cx7*l2);
 return ((((((C8*eps+C7)*eps+C6)*eps+C5)*eps+C4)*eps+C3)*eps+C2);
}
