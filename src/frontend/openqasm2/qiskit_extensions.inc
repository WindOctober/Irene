// Qiskit 0.45.0 qelib1.inc extension definitions (Apache-2.0).
// Source: https://github.com/Qiskit/qiskit/blob/0.45.0/qiskit/qasm/libs/qelib1.inc
// Keep the exported library's phase conventions, including rzz's U1 form.
gate csx a,b { h b; cu1(pi/2) a,b; h b; }

gate cu(theta,phi,lambda,gamma) c, t
{ p(gamma) c;
  p((lambda+phi)/2) c;
  p((lambda-phi)/2) t;
  cx c,t;
  u(-theta/2,0,-(phi+lambda)/2) t;
  cx c,t;
  u(theta/2,phi,0) t;
}

gate rxx(theta) a,b
{
  u3(pi/2, theta, 0) a;
  h b;
  cx a,b;
  u1(-theta) b;
  cx a,b;
  h b;
  u2(-pi, pi-theta) a;
}

gate rzz(theta) a,b
{
  cx a,b;
  u1(theta) b;
  cx a,b;
}

gate rccx a,b,c
{
  u2(0,pi) c;
  u1(pi/4) c;
  cx b, c;
  u1(-pi/4) c;
  cx a, c;
  u1(pi/4) c;
  cx b, c;
  u1(-pi/4) c;
  u2(0,pi) c;
}

gate rc3x a,b,c,d
{
  u2(0,pi) d;
  u1(pi/4) d;
  cx c,d;
  u1(-pi/4) d;
  u2(0,pi) d;
  cx a,d;
  u1(pi/4) d;
  cx b,d;
  u1(-pi/4) d;
  cx a,d;
  u1(pi/4) d;
  cx b,d;
  u1(-pi/4) d;
  u2(0,pi) d;
  u1(pi/4) d;
  cx c,d;
  u1(-pi/4) d;
  u2(0,pi) d;
}

gate c3x a,b,c,d
{
    h d;
    p(pi/8) a;
    p(pi/8) b;
    p(pi/8) c;
    p(pi/8) d;
    cx a, b;
    p(-pi/8) b;
    cx a, b;
    cx b, c;
    p(-pi/8) c;
    cx a, c;
    p(pi/8) c;
    cx b, c;
    p(-pi/8) c;
    cx a, c;
    cx c, d;
    p(-pi/8) d;
    cx b, d;
    p(pi/8) d;
    cx c, d;
    p(-pi/8) d;
    cx a, d;
    p(pi/8) d;
    cx c, d;
    p(-pi/8) d;
    cx b, d;
    p(pi/8) d;
    cx c, d;
    p(-pi/8) d;
    cx a, d;
    h d;
}

gate c3sqrtx a,b,c,d
{
    h d; cu1(pi/8) a,d; h d;
    cx a,b;
    h d; cu1(-pi/8) b,d; h d;
    cx a,b;
    h d; cu1(pi/8) b,d; h d;
    cx b,c;
    h d; cu1(-pi/8) c,d; h d;
    cx a,c;
    h d; cu1(pi/8) c,d; h d;
    cx b,c;
    h d; cu1(-pi/8) c,d; h d;
    cx a,c;
    h d; cu1(pi/8) c,d; h d;
}

gate c4x a,b,c,d,e
{
    h e; cu1(pi/2) d,e; h e;
    c3x a,b,c,d;
    h e; cu1(-pi/2) d,e; h e;
    c3x a,b,c,d;
    c3sqrtx a,b,c,e;
}
