/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* Reference excerpt: Tate local reduction, original lines 2770-2940. */
/* return a_{ k,l } in Tate's notation, pl = p^l */
static ulong
aux(GEN ak, ulong q, ulong pl)
{ return umodiu(ak, q) / pl; }

static ulong
aux2(GEN ak, ulong p, GEN pl)
{ pari_sp av = avma; return gc_ulong(av, umodiu(diviiexact(ak, pl), p)); }

/* number of distinct roots of X^3 + aX^2 + bX + c modulo p = 2 or 3
 * assume a,b,c in {0, 1} [ p = 2 ] or {0, 1, 2} [ p = 3 ]
 * if there's a multiple root, put it in *mult */
static long
numroots3(long a, long b, long c, long p, long *mult)
{
  if (p == 2)
  {
    if (odd(c + a * b)) return 3;
    *mult = b; return odd(a + b)? 2: 1;
  }
  /* p = 3 */
  if (!a) { *mult = -c; return b? 3: 1; }
  *mult = a * b;
  if (b == 2)
    return (a + c) == 3 ? 2 : 3;
  else
    return c ? 3 : 2;
}

/* same for aX^2 +bX + c */
static long
numroots2(long a, long b, long c, long p, long *mult)
{
  if (p == 2) { *mult = c; return odd(b)? 2: 1; }
  /* p = 3 */
  *mult = a * b; return (b * b - a * c) % 3 ? 2 : 1;
}

/* p = 2 or 3 */
static GEN
localred_23(GEN e, long p)
{
  long c, nu, nu6, nuD, r, s, t;
  long k, theroot, p2, p3, p4, p5, a21, a42, a63, a32, a64;
  GEN v;

  k = get_vp_u_small(e, p, &nu6, &nuD);
  if (!k) v = init_ch();
  else
  {
    ellmin_t M;
    min_set_all(&M, e, powuu(p, k));
    v = min_get_v(&M, e);
    e = min_to_ell(&M, e);
  }
  /* model is minimal */
  if (!nuD) return localred_result(0, 1, 1, v); /* I0 */
  if (p == 2) { p2 = 4; p3 = 8;  p4 = 16; p5 = 32; }
  else        { p2 = 9; p3 = 27; p4 = 81; p5 =243; }

  if (umodiu(ell_get_b2(e), p)) /* p \nmid b2 */
  {
    if (umodiu(negi(ell_get_c6(e)), p == 2 ? 8 : 3) == 1)
      c = nuD;
    else
      c = odd(nuD)? 1: 2;
    return localred_result(1, 4 + nuD, c, v); /* Inu */
  }
  if (p == 2)
  {
    r = umodiu(ell_get_a4(e), 2);
    s = umodiu(ell_get_a2(e), 2);
    t = umodiu(ell_get_a6(e), 2);
    if (r) { t = (s + t) & 1; s = (s + 1) & 1; }
  }
  else /* p == 3 */
  {
    r = - umodiu(ell_get_b6(e), 3);
    s = umodiu(ell_get_a1(e), 3);
    t = umodiu(ell_get_a3(e), 3);
    if (s) { t  = (t + r*s) % 3; if (t < 0) t += 3; }
  }
  /* p | (a1, a2, a3, a4, a6) */
  if (r || s || t) e = coordch_rst(e, stoi(r), stoi(s), stoi(t));
  if (umodiu(ell_get_a6(e), p2))
    return localred_result(nuD, 2, 1, v); /* II */
  if (umodiu(ell_get_b8(e), p3))
    return localred_result(nuD - 1, 3, 2, v); /* III */
  if (umodiu(ell_get_b6(e), p3))
  {
    if (umodiu(ell_get_b6(e), (p==2)? 32: 27) == (ulong)p2)
      c = 3;
    else
      c = 1;
    return localred_result(nuD - 2, 4, c, v); /* IV */
  }

  if (umodiu(ell_get_a6(e), p3))
    e = coordch_t(e, p == 2? gen_2: modis(ell_get_a3(e), 9));
      /* p | a1, a2; p^2  | a3, a4; p^3 | a6 */
  a21 = aux(ell_get_a2(e), p2, p);
  a42 = aux(ell_get_a4(e), p3, p2);
  a63 = aux(ell_get_a6(e), p4, p3);
  switch (numroots3(a21, a42, a63, p, &theroot))
  {
    case 3:
      c = a63 ? 1: 2;
      if (p == 2)
        c += ((a21 + a42 + a63) & 1);
      else {
        if (((1 + a21 + a42 + a63) % 3) == 0) c++;
        if (((1 - a21 + a42 - a63) % 3) == 0) c++;
      }
      return localred_result(nuD - 4, -1, c, v); /* I0* */
    case 2:
    { /* compute nu */
      GEN pk, pk1, p2k;
      long al, be, ga;
      if (theroot) e = coordch_r(e, stoi(theroot * p));
          /* p | a1; p^2  | a2, a3; p^3 | a4; p^4 | a6 */
      nu = 1;
      pk  = utoipos(p2);
      p2k = utoipos(p4);
      for(;;)
      {
        be =  aux2(ell_get_a3(e), p, pk);
        ga = -aux2(ell_get_a6(e), p, p2k);
        al = 1;
        if (numroots2(al, be, ga, p, &theroot) == 2) break;
        if (theroot) e = coordch_t(e, mulsi(theroot,pk));
        pk1 = pk;
        pk  = mului(p, pk);
        p2k = mului(p, p2k); nu++;

        al = a21;
        be = aux2(ell_get_a4(e), p, pk);
        ga = aux2(ell_get_a6(e), p, p2k);
        if (numroots2(al, be, ga, p, &theroot) == 2) break;
        if (theroot) e = coordch_r(e, mulsi(theroot, pk1));
        p2k = mului(p, p2k); nu++;
      }
      if (p == 2)
        c = odd(ga)? 2: 4;
      else
        c = 3 + kross(be * be - al * ga, 3);
      return localred_result(nuD - 4 - nu, -4 - nu, c, v); /* Inu* */
    }
    case 1:
      if (theroot) e = coordch_r(e, stoi(theroot*p));
          /* p | a1; p^2  | a2, a3; p^3 | a4; p^4 | a6 */
      a32 = aux(ell_get_a3(e), p3, p2);
      a64 = aux(ell_get_a6(e), p5, p4);
      if (numroots2(1, a32, -a64, p, &theroot) == 2)
      {
        if (p == 2)
          c = 3 - 2 * a64;
        else
          c = 2 + kross(a32 * a32 + a64, 3);
        return localred_result(nuD - 6, -4, c, v); /* IV* */
      }
      if (theroot) e = coordch_t(e, stoi(theroot*p2));
          /* p | a1; p^2 | a2; p^3 | a3, a4; p^5 | a6 */
      if (umodiu(ell_get_a4(e), p4))
        return localred_result(nuD - 7, -3, 2, v); /* III* */

      /* p^6 \nmid a6, otherwise wouldn't be minimal */
      return localred_result(nuD - 8, -2, 1, v); /* II* */
  }
  return NULL; /* LCOV_EXCL_LINE */
}


/* Reference excerpt: Halberstadt root tables, original lines 4760-5038. */
/* x a t_INT */
static long
val_aux(GEN x, long p, long pk, long *u)
{
  long v;
  GEN z;
  if (!signe(x)) { *u = 0; return 12; }
  v = Z_lvalrem(x,p,&z);
  *u = umodiu(z,pk); return v;
}
static void
val_init(GEN e, long p, long pk,
         long *v4, long *u, long *v6, long *v, long *vD, long *d1)
{
  GEN c4 = ell_get_c4(e), c6 = ell_get_c6(e), D = ell_get_disc(e);
  pari_sp av = avma;
  *v4 = val_aux(c4, p,pk, u);
  *v6 = val_aux(c6, p,pk, v);
  *vD = val_aux(D , p,pk, d1); set_avma(av);
}

static long
kod_23(GEN e, long p)
{
  GEN S, nv;
  if ((S = obj_check(e, Q_GLOBALRED)))
  {
    GEN NP = gmael(S,3,1), L = gel(S,4);
    nv = absequaliu(gel(NP,1), p)? gel(L,1): gel(L,2); /* localred(p) */
  }
  else
    nv = localred_23(e, p);
  return itos(gel(nv,2));
}

/* v(c4), v(c6), v(D) for minimal model, +oo is coded by 12 */
static long
neron_2(long v4, long v6, long vD, long kod)
{
  if (kod > 4) return 1;
  switch(kod)
  {
    case 1: return (v6>0) ? 2 : 1;
    case 2:
      if (vD==4) return 1;
      else
      {
        if (vD==7) return 3;
        else return v4==4 ? 2 : 4;
      }
    case 3:
      switch(vD)
      {
        case 6: return 3;
        case 8: return 4;
        case 9: return 5;
        default: return v4==5 ? 2 : 1;
      }
    case 4: return v4>4 ? 2 : 1;
    case -1:
      switch(vD)
      {
        case 9: return 2;
        case 10: return 4;
        default: return v4>4 ? 3 : 1;
      }
    case -2:
      switch(vD)
      {
        case 12: return 2;
        case 14: return 3;
        default: return 1;
      }
    case -3:
      switch(vD)
      {
        case 12: return 2;
        case 14: return 3;
        case 15: return 4;
        default: return 1;
      }
    case -4: return v6==7 ? 2 : 1;
    case -5: return (v6==7 || v4==6) ? 2 : 1;
    case -6:
      switch(vD)
      {
        case 12: return 2;
        case 13: return 3;
        default: return v4==6 ? 2 : 1;
      }
    case -7: return (vD==12 || v4==6) ? 2 : 1;
    default: return v4==6 ? 2 : 1;
  }
}
/* p = 3; v(c4), v(c6), v(D) for minimal model, +oo is coded by 12 */
static long
neron_3(long v4, long v6, long vD, long kod)
{
  if (labs(kod) > 4) return 1;
  switch(kod)
  {
    case -1: case 1: return odd(v4)? 2: 1;
    case -3: case 3: return (2*v6>vD+3)? 2: 1;
    case -4: case 2:
      switch (vD%6)
      {
        case 4: return 3;
        case 5: return 4;
        default: return v6%3==1 ? 2 : 1;
      }
    default: /* kod = -2 et 4 */
      switch (vD%6)
      {
        case 0: return 2;
        case 1: return 3;
        default: return 1;
      }
  }
}

static long
ellrootno_2(GEN e)
{
  long n2, kod, u, v, x1, y1, D1, vD, v4, v6;
  long d = get_vp_u_small(e, 2, &v6, &vD);

  if (!vD) return 1;
  if (d) { /* not minimal */
    ellmin_t M;
    min_set_2(&M, e, d);
    min_set_D(&M, e);
    e = min_to_ell(&M, e);
  }
  val_init(e, 2,64,&v4,&u, &v6,&v, &vD,&D1);
  kod = kod_23(e,2);
  n2 = neron_2(v4,v6,vD, kod);
  if (kod>=5)
  {
    long a2, a3;
    a2 = ZtoF2(ell_get_a2(e));
    a3 = ZtoF2(ell_get_a3(e));
    return odd(a2 + a3) ? 1 : -1;
  }
  if (kod<-9) return (n2==2) ? -kross(-1,v) : -1;
  x1 = u+v+v;
  switch(kod)
  {
    case 1: return 1;
    case 2:
      switch(n2)
      {
        case 1:
          switch(v4)
          {
            case 4: return kross(-1,u);
            case 5: return 1;
            default: return -1;
          }
        case 2: return (v6==7) ? 1 : -1;
        case 3: return (v%8==5 || (u*v)%8==5) ? 1 : -1;
        case 4: if (v4>5) return kross(-1,v);
          return (v4==5) ? -kross(-1,u) : -1;
      }
    case 3:
      switch(n2)
      {
        case 1: return -kross(2,u*v);
        case 2: return -kross(2,v);
        case 3: y1 = (u - (v << (v6-5))) & 15;
          return (y1==7 || y1==11) ? 1 : -1;
        case 4: return (v%8==3 || (2*u+v)%8==7) ? 1 : -1;
        case 5: return v6==8 ? kross(2,x1) : kross(-2,u);
      }
    case -1:
      switch(n2)
      {
        case 1: return -kross(2,x1);
        case 2: return (v%8==7) || (x1%32==11) ? 1 : -1;
        case 3: return v4==6 ? 1 : -1;
        case 4: if (v4>6) return kross(-1,v);
          return v4==6 ? -kross(-1,u*v) : -1;
      }
    case -2: return n2==1 ? kross(-2,v) : kross(-1,v);
    case -3:
      switch(n2)
      {
        case 1: y1=(u-2*v)%64; if (y1<0) y1+=64;
          return (y1==3) || (y1==19) ? 1 : -1;
        case 2: return kross(2*kross(-1,u),v);
        case 3: return -kross(-1,u)*kross(-2*kross(-1,u),u*v);
        case 4: return v6==11 ? kross(-2,x1) : -kross(-2,u);
      }
    case -5:
      if (n2==1) return x1%32==23 ? 1 : -1;
      else return -kross(2,2*u+v);
    case -6:
      switch(n2)
      {
        case 1: return 1;
        case 2: return v6==10 ? 1 : -1;
        case 3: return (u%16==11) || ((u+4*v)%16==3) ? 1 : -1;
      }
    case -7:
      if (n2==1) return 1;
      else
      {
        y1 = (u + (v << (v6-8))) & 15;
        if (v6==10) return (y1==9 || y1==13) ? 1 : -1;
        else return (y1==9 || y1==5) ? 1 : -1;
      }
    case -8: return n2==2 ? kross(-1,v*D1) : -1;
    case -9: return n2==2 ? -kross(-1,D1) : -1;
    default: return -1;
  }
}

static long
ellrootno_3(GEN e)
{
  long n2, kod, u, v, D1, r6, K4, K6, vD, v4, v6;
  long d = get_vp_u_small(e, 3, &v6, &vD);

  if (!vD) return 1;
  if (d) { /* not minimal */
    ellmin_t M;
    min_set_3(&M, e, d);
    min_set_a(&M);
    min_set_D(&M, e);
    e = min_to_ell(&M, e);
  }
  val_init(e, 3,81, &v4,&u, &v6,&v, &vD,&D1);
  kod = kod_23(e,3);
  K6 = kross(v,3); if (kod>4) return K6;
  n2 = neron_3(v4,v6,vD,kod);
  r6 = v%9; K4 = kross(u,3);
  switch(kod)
  {
    case 1: case 3: case -3: return 1;
    case 2:
      switch(n2)
      {
        case 1: return (r6==4 || r6>6) ? 1 : -1;
        case 2: return -K4*K6;
        case 3: return 1;
        case 4: return -K6;
      }
    case 4:
      switch(n2)
      {
        case 1: return K6*kross(D1,3);
        case 2: return -K4;
        case 3: return -K6;
      }
    case -2: return n2==2 ? 1 : K6;
    case -4:
      switch(n2)
      {
        case 1:
          if (v4==4) return (r6==4 || r6==8) ? 1 : -1;
          else return (r6==1 || r6==2) ? 1 : -1;
        case 2: return -K6;
        case 3: return (r6==2 || r6==7) ? 1 : -1;
        case 4: return K6;
      }
    default: return -1;
  }
}

/* p > 3. Don't assume that e is minimal or even integral at p */
static long
ellrootno_p(GEN e, GEN p)
{
  long nuj, nuD, nu;
  GEN D = ell_get_disc(e);
  long ep, z;

  nuD = Q_pval(D, p);
  if (!nuD) return 1;
  nuj = j_pval(e, p);
