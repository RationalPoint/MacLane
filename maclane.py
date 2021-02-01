r"""

Implementations of MacLane's Algorithm for finding all valuations of a finite
extension of a field K that extend a valuation v on K, and MacLane's
construction of all valuations on the polynomial ring K[x] extending v.

REFERENCES:

.. [MacLane-1] Saunders MacLane, "A Construction for Absolute Values in
   Polynomial Rings", Trans. AMS., vol. 40 no. 3 (Dec. 1936), pp. 363-395

.. [MacLane-2] Saunders MacLane, "A Construction for Prime Ideals as Absolute
   Values of an Algebraic Field", Duke Math. J., v.2 (1936), pp. 492-510

.. [Serre] Jean-Pierre Serre, "Corps Locaux", Hermann, Paris (1968).

AUTHORS:

- Xander Faber <awfaber@super.org>, IDA/Center for Computing Sciences
- David Zelinsky <dsz@dedekind.net>


TABLE OF CONTENTS

- Utility Functions

  - extension_field_polynomial
  - expand_polynomial
  - reduce_at_infinity
  - newton_slopes
  - polynomial_from_inductive_valuation
  - inductive_valuation_from_invariants

- ExtensionOfFiniteField (class)

- InductiveValuation (class)

- StageZeroValuation (constructor)

- ExtensionFieldValuation (class)

- ExtensionFieldDecomposition (class)

- Applications

  - p_adic_inductive_valuation
  - p_adic_decomposition
  - number_field_decomposition
  - function_field_inductive_valuation
  - function_field_decomposition

- Construction and Visualization

  - compute_vertex_positions
  - sort_indvals
  - sort_decomp_graph
  - decomp_graph
  - indvals_from_decomp_graph
  - polynomial_from_indvals
  - polynomial_from_decomp_graph

"""

from sage.all import *



################################################################################
#############################  UTILITY FUNCTIONS  ##############################
################################################################################


def extension_field_polynomial(K):
  r"""
  Return the defining polynomial of an extension field.
  This accounts for different method names for different extension types.

  INPUT:

  - ``K`` -- an extension field object, satisfying one of the following:

    - K has a ``defining_polynomial`` method

    - K has a ``polynomial`` method

    - K.gen() has a ``minpoly`` method

  OUTPUT:

  - a polynomial over K.base() defining the extension

  """
  if hasattr(K,'defining_polynomial'):
    return K.defining_polynomial().change_ring(K.base())
  if hasattr(K,'polynomial'):
    return K.polynomial().change_ring(K.base())
  g = K.gen()
  if hasattr(g,'minpoly'):
    return g.minpoly().change_ring(K.base())
  raise TypeError('cannot get defining polynomial of field')



def expand_polynomial(f, g):
  r"""
  Return the coefficients of ``f`` when expressed as a polynomial in ``g``.

  INPUT:

  - ``f,g`` -- univariate polynomials over a field, with ``g`` nonzero

  OUTPUT:

  - a dict whose keys are nonnegative integers `i` and whose value at `i` is a
    polynomial `c_i` such that `f = \sum c_i g^i` and `\deg c_i < \deg g` for
    all `i`.

  EXAMPLES::

    sage: R.<x> = PolynomialRing(QQ)
    sage: f = x^5 + 3
    sage: g = 2*x^2 + 1
    sage: cc = expand_polynomial(f,g)
    sage: cc
    {0: 1/4*x + 3, 1: -1/2*x, 2: 1/4*x}
    sage: sum(c * g^i for i,c in cc.items()) == f
    True

  """
  R = g.parent()
  try:
    f = R(f)
  except TypeError:
    raise TypeError('Cannot find a common polynomial ring for "f" and "g"')
  if g == 0:
    raise ValueError('"g" must be nonzero')
  cc = {}
  i = 0
  while f != 0:
    f,c = f.quo_rem(g)
    cc[i] = R(c)
    i += 1
  return cc

#############################  UTILITY FUNCTIONS  ##############################

def reduce_at_infinity(f):
  r"""
  Return image of ``f`` in residue field of place at infinity.

  INPUT:

  - ``f`` -- an element of a (rational) FunctionField object `k(x)`

  OUTPUT:

  - The image of ``f`` in the residue field of `k(x)` at the place at infinity

  EXAMPLES::

    sage: K = FunctionField(QQ,'x')
    sage: x = K.gen()
    sage: reduce_at_infinity( 2*x^2 / (3*x^2 - 5) )
    2/3
    sage: reduce_at_infinity( 2*x^2 / x^3)
    0

  """
  k = parent(f).constant_field()
  num = f.numerator()
  den = f.denominator()
  if num.degree() > den.degree():
    raise ValueError('Cannot reduce element of negative valuation.')
  if num.degree() < den.degree():
    return k(0)
  return num.leading_coefficient()/den.leading_coefficient()

#############################  UTILITY FUNCTIONS  ##############################

def newton_slopes(val_dict):
  r"""
  Find the lower convex hull of a collection of points in the first quadrant.

  INPUT:

  - ``val_dict`` -- a dictionary with key-value pairs i:v, where i is a
    nonnegative integer and v is a rational number

  OUTPUT:

  - a list of pairs `(m_0,n_0), \ldots, (m_r,n_r)`, where

    * `m_i` is the slope of the i-th face of the lower convex hull of the points
      in ``val_dict``, and

    * `n_i` is the x-axis projection length of the i-th face.

    We have `m_0 < m_1 < \cdots < m_r`. The first slope is `m_0 = -Infinity` if
    the smallest key in ``val_dict`` is nonzero.

  NOTE:

  - Sage's newton_slopes function uses the opposite sign convention.

  EXAMPLES::

    sage: R.<x> = QQ[]
    sage: f = x^6 + x^4/5 + 5*x
    sage: f.newton_slopes(5,lengths=True)
    [(+Infinity, 1), (2/3, 3), (-1/2, 2)]

    sage: val_dict = {i:c.ord(5) for i,c in f.dict().items()}
    sage: newton_slopes(val_dict)
    [(-Infinity, 1), (-2/3, 3), (1/2, 2)]

  """
  val_seq = [(i,v) for i,v in val_dict.items() if v != Infinity]
  val_seq.sort()
  last,_ = val_seq[-1]
  newton_data = []
  i,v = val_seq[0]
  if i > 0:
    newton_data.append((-Infinity,i))
  while i < last:
    slope = Infinity
    for j,w in val_seq:
      if j <= i: continue
      mu = (w-v)/(j-i)
      if mu > slope: continue
      proj = j-i
      slope = mu
    newton_data.append((slope,proj))
    i += proj
    v = val_dict[i]
  return newton_data

#############################  UTILITY FUNCTIONS  ##############################

def polynomial_from_inductive_valuation(indval):
  r"""
  Return a polynomial `G` with indval in its decomposition.

  INPUT:

  - ``indval`` -- a commensurable inductive valuation

  OUTPUT:

  - a polynomial G such that ``indval``, or a valuation equivalent to it,
    appears as one of the InductiveValuations in the list returned by
    V0.decomposition(G), where V0 = indval.stage_zero().

  EXAMPLES::

    sage: R.<x> = QQ[]
    sage: polvals = [(x, 0), (x^2 + 1, 1/2), (x^4 + 2*x^2 + 8, 2)]
    sage: V = p_adic_inductive_valuation(7, key_polval_list=polvals)
    sage: G = polynomial_from_inductive_valuation(V)
    sage: print(G)
    x^8 + 4*x^6 + 69*x^4 + 130*x^2 + 17263
    sage: V0 = V.stage_zero()
    sage: V0.decomposition(G)
    [Stage 2 valuation over 7 with (keypol,keyval) sequence [(x, 0), (x^2 + 1, 1/2), (x^4 + 2*x^2 + 8, 3)],
     Stage 2 valuation over 7 with (keypol,keyval) sequence [(x, 0), (x^2 + 1, 1/2), (x^4 + 2*x^2 + 8, 2)]]

  """
  V = indval
  t = V.relative_ramification_index()
  P = V.keypol()
  if t == 1:
    # make G with proj(V,G)=1 and G not a key polynomial
    v = V.keyval()
    a = V.polynomial_with_value(v)
    d = ceil(2*v)
    p = V.base_uniformizer()
    G = p**(d+1) + a.mod(P)*P + P**2
    return G
  e = V.ramification_index()
  n = e * V.residue_degree()
  d = floor(n / (t*P.degree()))
  R = V.residue_ring()
  if R.is_field():
    raise ValueError('"indval" is not a commensurable valuation')
  g = R.irreducible_element(d, algorithm='random')
  return V.keypol_from_residual(g)

#############################  UTILITY FUNCTIONS  ##############################

def inductive_valuation_from_invariants(indval, resdeg_ramind_list):
  r"""
  Return an augmentation of indval with given relative ramification and residue degrees

  INPUT:

  - ``indval`` -- an inductive valuation on a polynomial ring `K[x]`

  - ``resdeg_ramind_list`` -- list of pairs (f_i,e_i) of positive integers,
    where f_i is the relative residue degree and e_i the relative ramification
    index requested for stage i+1.

  OUTPUT:

  - an (k+n)-stage InductiveValuation, that is an n-stage augmentation of indval
    where k = indval.stage() and n = len(ramind_resdeg_list), such that for
    i=0,...,n-1, if ramind_resdeg_list[i] = (f_i,e_i), then e_i is the relative
    ramification index (relative denominator of the value group) at stage k+i,
    and the constant field of the residue ring at stage k+i is an extension of
    degree f_i over the constant field of the residue ring at the previous
    stage.

  EXAMPLES::

    sage: V0 = p_adic_inductive_valuation(7,'x')
    sage: V1 = inductive_valuation_from_invariants(V0, [(2,1),(4,3)])
    sage: data = []
    sage: for V in V1.stages():
    ....:   resdeg = V.relative_residue_degree()
    ....:   ramind = V.relative_ramification_index()
    ....:   data.append((resdeg,ramind))
    ....:
    sage: print(data)
    [(1, 1), (2, 1), (4, 3)]

  """
  V = indval
  for f,t in resdeg_ramind_list:
    R = V.residue_ring()
    y = R.gen()
    h = y
    while h == y or not h.is_irreducible():
      h = y**f + R.random_element(degree=f-1)
    H = V.keypol_from_residual(h)
    e = t * V.ramification_index()
    n = e * V(H) + 1
    while gcd(n,e) != 1:
      n += 1
    V = V.augment(H,n/e)
  return V

#############################  UTILITY FUNCTIONS  ##############################

def discrete_generator(a,b):
  r"""
  Return the minimum positive ZZ-linear combination of a,b, and coefficients.

  INPUT:

  - ``a,b`` -- rational numbers

  OUTPUT:

  - `g,x0,y0,x1,y1` where `x0,y0,x1,y1` are integers and `g` a positive rational
    number, satisfying:

    *  g = x0*a + y0*b  and g is minimum positive of this form

    * -g = x1*a + y1*b

    * y0 and y1 are nonnegative

  """
  a = QQ(a)
  b = QQ(b)
  d = lcm(a.denom(),b.denom())
  na = ZZ(d*a)
  nb = ZZ(d*b)
  ng,x0,y0 = xgcd(na,nb)
  g = QQ(ng)/d
  ag = na//ng
  bg = nb//ng
  x1,y1 = -x0,-y0
  if y0 < 0:
    if (ag>0): m = ceil(-y0/ag)
    else: m = floor(-y0/ag)
    y0 += m*ag
    x0 -= m*bg
  else:
    if (ag>0): m = ceil(-y1/ag)
    else: m = floor(-y1/ag)
    y1 += m*ag
    x1 -= m*bg
  return g,x0,y0,x1,y1


################################################################################
###########################  ExtensionOfFiniteField  ###########################
################################################################################


class ExtensionOfFiniteField(object):
  r"""
  Class for relative extensions of finite fields with coercion and lifting maps.

  The extension field will be constructed as a Sage finite field, which is an
  absolute extension of the prime field.  The generator name (of the absolute
  extension) will be of the form X_d where X is the generator name for the base
  field and d is the degree of the relative extension.

  NOTE: This class would not be needed if Sage allowed construction of relative
  extensions of finite fields.

  INPUT:

  - ``base_field`` -- a finite field

  - ``defining_polynomial`` -- a polynomial over ``base_field``, which must be
    irreducible

  - ``check_irreducible`` -- boolean (default: False); whether to check that the
    defining polynomial is irreducible over the base

  EXAMPLES::

    sage: k.<a_3> = GF(7^3)
    sage: kpol.<x> = k[]

    sage: f = x^4 + (a_3^2+2*a_3+3)*x^2 + 1
    sage: try:
    ....:    K = ExtensionOfFiniteField(k,f,True)
    ....: except ValueError as err:
    ....:    print(err)
    Defining polynomial is not irreducible.

    sage: f = x^4 + (a_3^2+2*a_3+3)*x^2 + a_3
    sage: K = ExtensionOfFiniteField(k,f,True)
    sage: K
    Degree-4 extension of GF(7^3) with defining polynomial x^4 + (a_3^2 + 2*a_3 + 3)*x^2 + a_3
    sage: K.field()
    Finite Field in a_3_4 of size 7^12
    sage: b = K.coerce(a_3)
    sage: b
    6*a_3_4^10 + 5*a_3_4^9 + 6*a_3_4^8 + 6*a_3_4^5 + 3*a_3_4^4 + 6*a_3_4^3 + a_3_4 + 3
    sage: b.minpoly() == a_3.minpoly()
    True
    sage: K.lift(b)
    a_3
    sage: g = K.gen()
    sage: g
    6*a_3_4^11 + a_3_4^10 + a_3_4^9 + 6*a_3_4^8 + a_3_4^7 + 4*a_3_4^5 + 2*a_3_4^4 + 5*a_3_4^3 + 2*a_3_4
    sage: K.lift(g)
    x
    sage: z = (b+1)*g^2 + (b^2+2)*g + 1
    sage: K.lift(z)
    (a_3 + 1)*x^2 + (a_3^2 + 2)*x + 1
    sage: z == K.reduce((a_3 + 1)*x^2 + (a_3^2 + 2)*x + 1)
    True

  INSTANCE METHODS:

    -  __init__
    -  __repr__
    -  characteristic
    -  base_degree
    -  degree
    -  absolute_degree
    -  base_gen
    -  gen
    -  field
    -  base_field
    -  coerce
    -  lift
    -  coerce_coefficients
    -  reduce

  """


  def __init__(self, base_field, defining_polynomial, check_irreducible=False):
    if not base_field.is_finite():
      raise TypeError('base_field is not finite')
    if check_irreducible and not defining_polynomial.is_irreducible():
      raise ValueError('Defining polynomial is not irreducible.')
    self._base = k = base_field
    self._defpol = f = defining_polynomial
    self._polring = R = parent(defining_polynomial)
    self._char = p = k.characteristic()
    self._base_deg = dk = k.degree()
    self._deg = d = f.degree()
    self._abs_deg = D = d*dk

    if dk == 1:
      self._absolute = True
      var, = R._names
      if d == 1:
        name = '{}'.format(var)
      else:
        name = '{}_{}'.format(var,d)
      self._field = K = GF(p**d, name, f, check_irreducible=check_irreducible)
      self._base_gen = K(1)
      self._gen = K.gen()
      self._abs_mat_inv = None
      return

    self._absolute = False
    name_k, = k._names
    if d == 1:
      name = '{}'.format(name_k)
    else:
      name = '{}_{}'.format(name_k,d)
    self._field = K = GF(p**D, name)
    rr = k.polynomial().roots(K)
    if len(rr) == 0:
      raise ValueError('Defining polynomial has no roots (i.e. is not irreducible).')
    self._base_gen,_ = b,_ = sorted(rr)[0]
    self._gen,_ = g,_ = sorted(self.coerce_coefficients(f).roots(K))[0]
    # build the inverse of the DxD matrix whose (i*dk+j)-th row represents b^j*g^i
    M = matrix([vector(b**j * g**i) for i in range(d) for j in range(dk)])
    self._abs_mat = M
    self._abs_mat_inv = M**-1

  #########################  ExtensionOfFiniteField  ###########################

  def __repr__(self):
    s = 'Degree-{} extension of GF({}^{}) with defining polynomial {}'
    return s.format(self._deg, self._char, self._base_deg, self._defpol)

  def characteristic(self):
    return self._char

  def base_degree(self):
    return self._base_deg

  def degree(self):
    return self._deg

  def absolute_degree(self):
    return self._abs_deg

  def base_gen(self):
    return self._base_gen

  def gen(self):
    return self._gen

  def field(self):
    return self._field

  def base_field(self):
    return self._base

  def coerce(self, base_elt):
    r"""
    Evaluate the stored coercion map from self.base_field() into self.field().

    INPUT:

    - ``base_elt`` -- an element of self.base_field()

    OUTPUT:

    - the element of self.field() that is the image of ``base_elt`` under the
      coercion map that was fixed on initialization of self.
    """
    if self._absolute:
      return self._field(base_elt)
    pol = base_elt.polynomial()
    return pol(self._base_gen)

  #########################  ExtensionOfFiniteField  ###########################

  def lift(self, field_elt):
    r"""
    Lift an element of self.field() to a polynomial over self.base_field()

    INPUT:

    - ``field_elt`` -- an element of self.field()

    OUTPUT:

    - a polynomial over self.base_field() (in parent(self.polynomial())) that
      reduces to ``field_elt``.

    """
    if self._absolute:
      return self._polring(field_elt.polynomial())
    # get coefficients on basis [b^0*g^0, b^1*g^0, ... ]
    bb = vector(field_elt) * self._abs_mat_inv
    # bb[j*dk:j*dk+dk-1] is vector representative of coefficient of g^j
    dk = self._base_deg
    d = self._deg
    cc = [self._base(bb[j*dk:j*dk+dk]) for j in range(d)]
    return self._polring(cc)

  def coerce_coefficients(self, f, ring=None, name=None):
    r"""
    Coerce a polynomial over base to a polynomial over the extension.

    INPUT:

    - ``f`` -- a univariate polynomial over self.base_field()

    - ``ring`` -- optional polynomial ring over self.field(); defaults to a
      polynomial ring with generater name ``name`` if given, or the same name as
      for parent(f)

    - ``name`` -- (string) optional name of generator for polynomial ring parent
      of returned polynomial; defaults to the generator name of parent(f)

    """
    if ring is None:
      if name is None:
        name, = parent(f)._names
      ring = PolynomialRing(self._field, name)
    return ring([self.coerce(c) for c in list(f)])

  def reduce(self, f):
    r"""
    Return the image of f in self.field().

    INPUT:

    - ``f`` -- a polynomial over k = self.base()

    OUTPUT:

    - the image of f in self.field() = k[x]/(defining_polynomial)

    """
    return self.coerce_coefficients(f)(self._gen)




################################################################################
#############################  InductiveValuation  #############################
################################################################################


class InductiveValuation(SageObject):
  r"""
  Class for inductive valuations V on `K[x]` with values in `\QQ`.
  Here `K` is any field with a discrete valuation.  See the APPLICATIONS section
  for instantiations for particular types of valued fields.

  INPUT:

  - ``previous`` -- an optional InductiveValuation object; if not specified, a
    stage-0 valuation will be initialized

  - ``key_polynomial`` -- a polynomial, which must be key for ``previous`` if
    given, or a monic linear polynomial for a stage-0 valuation

  - ``key_value`` -- a rational number or Infinity, to assign as the new
    valuation of the key polynomial. (In particular, all InductiveValuation
    objects are assumed comensurable.)

  - ``key_polval_list`` -- a list of pairs [(P_0,v_0),...,(P_k,v_k)] where P_i
    is a polynomial and v_i is a rational number, that is the list of
    key-polynials and their values for a inductive valuation.  This must not
    be used if ``previous`` is given.

  - ``check`` -- boolean (default: False); whether to check that the given data
    define a valid inductive valuation

  - ``collapse`` -- boolean (default: True); whether to collapse the resulting
    valuation to the extent possible

  - The following additional keyword arguments are required to initialize a
    stage-0 valuation, but should be omitted if ``previous`` is given:

      * ``valuation`` -- optional function computing a discrete valuation on K
        with value group in QQ; if not given, elements of K must have a
        ``valuation`` method, possibly with the uniformizer as argument (as is
        the case for K=QQ).

      * ``uniformizer`` -- optional uniformizer for K; that is, an element of K
        with minimum positive valuation.  If not specified, K must be a
        valuation field with a ``uniformizer`` method.

      * ``residue_field`` -- residue field k of the valuation on K

      * ``reduce_map`` -- reduction map from K to k;

      * ``lift_map`` -- lifting map from `k` to `K`

      * ``extension_constructor`` -- optional class or constructor function to
        construct finite extensions of k.  If k is a finite field, this defaults
        to the class ExtensionOfFiniteField.  The constructor must take inputs:

        - ``k1`` -- a field that is a finite extension of k (or k itself)

        - ``f`` -- an irreducible polynomial over k1

        - ``proof`` -- optional boolean; whether to test that ``f`` is irreducible

        The object E = extension_constructor(k1,f) must have the following
        methods:

        - ``k1 = E.base()`` -- return the field k1

        - ``k2 = E.field()`` -- return a field k2 with a fixed isomorphism F: k1[x]/(f(x)) -> k2

        - ``xbar = E.gen()`` -- return a root of f in k2. Note that this might
          be different from E.field().gen().

        - ``z = E.reduce(g)`` -- for g in k1[x], return its image z = F(g) = g(xbar) in k2

        - ``g = E.lift(z)`` -- for z in k2, return g in k1[x] with deg(g) < deg(f) and F(g) = z

  Attributes present in all stages:

   - ``_stages`` --  list of earlier stages (not including `self`)

   - ``_keypol`` --  key polynomial `phi`

   - ``_keyval`` --  valuation of key polynomial

   - ``_denom`` --  denominator `e` of value group = (1/e) ZZ

   - ``_relative_denom`` --  index of previous value group in current one

   - ``_residue_extension`` -- extension field object, as returned by extension_constructor (see above)

   - ``_residue_constant_field`` --  constant field `F` of the residue ring of the valuation

   - ``_residue_degree`` -- degree of residue_constant_field over residue field of base

   - ``_residue_ring`` --  residue ring, a polynomial ring F[y] isomorphic to (K[x] meet O_V)/(K[x] meet m_V)

   - ``_genlift`` -- a polynomial over K with valuation 0, whose residue image
     is a transcendental generator of the residue ring.

   - ``_Q`` -- polynomial satisfying `V(Q) = W(Q) = t \mu` where V is the
     current stage and W the previous stage, `\mu` is the current key value and
     t is the relative denominator (index of the value group of W in the value
     group of V).  Then Q is an equivalence unit for V, and if Qinv is its
     equivalence inverse, then the residue image of `Y = Qinv * \phi^t` is the
     transcendental generator of the residue ring, where `\phi` is the current
     key polynomial. (See proofs of Theorems 10.2 and 12.1 in [MacLane-1].)
     This `Y` is taken as the value of ``_genlift``.

  Attributes present only in stage 0:

   - ``_base_valuation`` -- valuation on base field of which `self` is an extension

   - ``_base_reduce`` -- reduction map for base_field valuation

   - ``_base_lift`` -- lifting map for base_field valuation

   - ``_base_field`` -- the base field `K`

  ALGORITHM:

  - See [MacLane-1]_ and [MacLane-2]_.

  REFERENCES:

  .. [MacLane-1] Saunders MacLane, "A Construction for Absolute Values in
     Polynomial Rings", Trans. AMS., vol. 40 no. 3 (Dec. 1936), pp. 363-395

  .. [MacLane-2] Saunders MacLane, "A Construction for Prime Ideals as Absolute
     Values of an Algebraic Field", Duke Math. J., v.2 (1936), pp. 492-510

  NOTE:

  - When checking whether a given pair (key_polynomial, key_value) pair yields a
    valid augmentation, we completely ignore Definition 6.1 of [MacLane-1].

    * Set `\phi_k` and `\phi_{k-1}` to be the new and previous key polynomials,
      respectively. We may ignore the condition that

      ..math:: \deg(\phi_k) \geq \deg(\phi_{k-1})

      because otherwise the minimality condition on key polynomials would force `\phi_k`
      to be constant.         ****************  FIXME -- What??

    * We may ignore the condition that

      ..math:: \deg(\phi_k) \not\sim \deg(\phi_{k-1}) \text{ in V_{k-1}}

      because we can simply collapse the resulting valuation afterward as in
      Lemma 15.1 of [MacLane-1].


  INSTANCE METHODS:

    - __init__
    - _init_stage_zero
    - name
    - __repr__
    - __str__
    - str_compact
    - validate
    - expand
    - base_valuation
    - valuation
    - normalized_valuation
    - normalize
    - __call__
    - key_polval_list
    - invariants
    - __hash__
    - stages
    - __getitem__
    - base_field
    - polring
    - keypol
    - keyval
    - keypolval
    - residue_ring
    - residue_constant_field
    - residue_constant_field_gen
    - residue_constant_field_reduce
    - residue_constant_field_lift
    - residue_constant_field_expand
    - residue_constant_field_collapse
    - relative_residue_degree
    - residue_degree
    - relative_ramification_index
    - ramification_index
    - base_uniformizer
    - base_uniformizer_value
    - uniformizer
    - uniformizer_valuation
    - stage_zero
    - is_stage_zero
    - stage
    - prev
    - _expand_all
    - homogeneous_form
    - reduce
    - lift
    - value_group_contains
    - earliest_stage_with_value
    - decompose_value
    - polynomial_with_value
    - graded_map
    - graded_map_lift
    - graded_reduction
    - graded_reduction_lift
    - residual_polynomial
    - keypol_from_residual
    - new_keys
    - newton_slopes
    - new_values
    - new_key_value_pairs
    - augment
    - augmentations
    - is_minimal
    - is_key
    - projection
    - collapse
    - decomposition
    - equivalent_polynomials
    - is_equiv_divisible_by_key
    - effective_degree
    - is_equiv_unit
    - equiv_inverse
    - equal_valuation
    - __eq__
    - __ne__



  """
  _class_name = 'maclane.InductiveValuation'

  def __init__(self, previous=None, key_polynomial=None, key_value=None, key_polval_list=None,
               check=False, collapse=True, **kwargs):

    if previous is None:

      # Set stage-0 from (key_polynomial, key_value), or first pair in key_polval_list
      # Set key_list to the remaining pairs, if any.
      if key_polval_list is not None:
        if len(key_polval_list) == 0:
          raise TypeError('Empty "key_polval_list"')
        key_polynomial, key_value = key_polval_list[0]
        key_list = key_polval_list[1:]
      else:
        if None in (key_polynomial,key_value):
          msg = 'Either "key_polval_list" or both "key_polynomial" and "key_value" must be given.'
          raise TypeError(msg)
        key_list = []

      # Initialize the stage-0 valuation
      if len(key_list) == 0:
        # self is stage-0
        kwargs0 = {}
        for kw in ('uniformizer','valuation','residue_field','reduce_map','lift_map','extension_constructor'):
          kwargs0[kw] = kwargs.get(kw)
        self._init_stage_zero(key_polynomial, key_value, **kwargs0)
        return
      else:
        # Initialize previous as stage-0
        kwargs['key_polynomial'] = key_polynomial
        kwargs['key_value'] = key_value
        kwargs['check'] = check
        previous = InductiveValuation(**kwargs)

      # Initialize intermediate stages until previous is the penultimate stage.
      for pol, val in key_list[:-1]:
        previous = previous.augment(pol,val,check=check,collapse=collapse)
      key_polynomial, key_value = key_list[-1]

    # Now we have an initialized previous stage. Augment it.

    prev = previous # for brevity
    err_msg = '"{}" must be specified to augment an inductive valuation.'
    keypol = key_polynomial
    if keypol is None:
      raise TypeError(err_msg.format('key_polynomial'))
    keyval = key_value
    if keyval is None:
      raise TypeError(err_msg.format('key_value'))
    if check:
      # See the notes in the docstring for why it suffices to ignore Definition 6.1 of [MacLane-1]
      if not prev.is_key(keypol):
        raise ValueError('Polynomial is not key for given valuation')
      if not keyval > prev(keypol):
        raise ValueError('Given value is not greater than previous valuation of keypol')

    # Store some attributes
    self._stages = prev._stages + [prev]
    self._base_field = prev._base_field
    self._polring = prev._polring
    self._keypol = keypol
    self._keyval = keyval

    # Compute the denominator of the value group
    if keyval==Infinity:
      # the finite part of the value group is the same as previous
      denom = self._denom = prev._denom
      self._relative_denom = ZZ(1)
      self._relative_numer = Infinity
      self._uniformizer_val = prev._uniformizer_val
    else:
      prev_unif_val = prev._uniformizer_val
      unif_val,x0,y0,x1,y1 = discrete_generator(prev_unif_val,keyval)
      self._uniformizer_val = unif_val
      d = self._relative_denom = ZZ(prev_unif_val / unif_val)
      D = self._denom = prev._denom * d
      n = self._relative_numer = ZZ(D*keyval)
      g,a,b = xgcd(n,d)
      assert g == 1
      while a<0:
        a += d
        b -= n
      while a>=d:
        a -= d
        b += n
      self._relative_numer_inv = a
      self._relative_denom_inv = b


    # Find Q with V1(Q) = V(Q) = t*keyval
    t = self._relative_denom
    self._Q = Q = prev.polynomial_with_value(t*keyval)
    _,Qinv,_ = xgcd(Q,keypol)
    self._genlift = Qinv * keypol**t # lift of the residue ring generator

    # Compute residue ring:
    #   prev.residual_polynomial(keypol) is generating polynomial of new constant field
    f = prev.residual_polynomial(keypol)
    f = f / f.leading_coefficient()
    k_prev = prev._residue_constant_field
    E = self.stage_zero()._extension_constructor(k_prev,f)
    self._residue_extension = E
    self._residue_constant_field = E.field()
    self._residue_degree = prev._residue_degree * f.degree()
    if self._keyval == Infinity:
      self._residue_ring = E.field()
    else:
      name = '{}{}'.format(self.name(),self.stage())
      self._residue_ring = PolynomialRing(E.field(),name)


  ###########################  InductiveValuation  #############################

  def _init_stage_zero(self, key_polynomial, key_value, uniformizer, valuation,
                       residue_field, reduce_map, lift_map, extension_constructor):
    r"""
    Initialize a stage-0 inductive valuation.

    See docstring for InductiveValuation for explanation of all arguments.

    """
    # Set polring, base field, key polynomial, and key value
    keypol = key_polynomial
    if keypol.degree() != 1:
      raise ValueError('"key_polynomial" argument is not linear.')
    if not keypol.is_monic():
      raise ValueError('"key_polynomial" argument is not monic.')
    self._keypol = keypol
    self._keyval = keyval = Infinity if key_value == Infinity else QQ(key_value)
    self._polring = polring = keypol.parent()
    self._base_field = K = polring.base_ring()

    # Set base uniformizer
    self._intrinsic_uniformizer = False
    if uniformizer is None:
      try:
        unif = K.uniformizer()
        self._intrinsic_uniformizer = True
      except AttributeError:
        raise TypeError('Unable to determine a uniformizer for the base field')
    else:
      unif = K(uniformizer)

    # Set valmap
    valmap = valuation
    if valmap is None:
      # If no valuation map specified, we try to use
      # x -> x.valuation() (if base field is a valuation field), or
      # x -> x.valuation(unif) (if base field is QQ or k[x], for example).
      valmap = lambda x: x.valuation()
      msg = 'Unable to determine a valuation on the base field'
      try:
        v = valmap(K(1))
      except TypeError:
        valmap = lambda x: x.valuation(unif)
        try:
          v = valmap(K(1))
        except (AttributeError,TypeError):
          raise TypeError(msg)
      if v != 0 or valmap(unif) <= 0:
        raise TypeError(msg)
    self._base_unif_val = base_unif_val = QQ(valmap(unif))

    # Set residue field and reduce/lift maps
    resfield = residue_field
    if resfield is None:
      msg = 'Unable to determine a residue field for the base field.'
      if not hasattr(K,'residue_field'):
        raise TypeError(msg)
      try:
        resfield = K.residue_field()
      except TypeError:
        try:
          resfield = K.residue_field(unif)
        except TypeError:
          raise TypeError(msg)
    self._residue_constant_field = resfield
    self._residue_degree = ZZ(1)
    if reduce_map is None:
      msg = 'Unable to determine a reduction map to the residue field'
      try:
        r = resfield(1+unif)
      except TypeError:
        raise TypeError(msg)
      else:
        if r != 1:
          raise TypeError('Unable to determine a reduction map to the residue field')
        reduce_map = resfield
    if lift_map is None:
      msg = 'Unable to determine a lift map from the residue field'
      try:
        x = resfield.random_element()
        y = K(x)
      except TypeError:
        raise TypeError(msg)
      else:
        if reduce_map(y) != x:
          raise TypeError(msg)
      lift_map = lambda x: K(x)
    if extension_constructor is None:
      if not resfield.is_finite():
        raise TypeError('extension_constructor must be provided')
      extension_constructor = ExtensionOfFiniteField
    self._extension_constructor = extension_constructor

    self._stages = []
    self._base_uniformizer = unif
    self._base_valuation = valmap
    self._base_reduce = reduce_map
    self._base_lift = lift_map
    if keyval==Infinity:
      self._residue_ring = resfield
    else:
      self._residue_ring = PolynomialRing(resfield,'{}0'.format(self.name()))


    # Set uniformizer for stage 0
    if keyval==Infinity:
      self._denom = base_unif_val.denominator()
      self._relative_denom = t = ZZ(1)
      self._relative_denom_inv = ZZ(1)
      self._relative_numer = Infinity
      self._relative_numer_inv = ZZ(0)
      self._uniformizer_val = base_unif_val
      self._Q = polring(0) # Residue ring is a field
      self._genlift = polring(0) # Residue ring is a field
    else:
      self._denom = denom = LCM(keyval.denominator(),base_unif_val.denominator())

      # solve a*keyval + b*base_unif_val = g/denom with a>=0 and g>0 minimal
      X,Y = ZZ(denom*keyval), ZZ(denom*base_unif_val)
      g = gcd(X,Y) # gcd = g in above notation
      self._uniformizer_val = unif_val = QQ(g) / QQ(denom)
      self._relative_denom = t = ZZ(base_unif_val/unif_val)
      self._relative_numer = n = ZZ(denom * keyval)
      g,a,b = xgcd(n,t)
      assert g==1
      while a<0:
        a += t
        b -= n
      while a>=t:
        a -= t
        b += n
      self._relative_numer_inv = a
      self._relative_denom_inv = b

      s = ZZ(t*keyval/base_unif_val)
      Q = unif**(s)
      self._Q = polring(Q)
      self._genlift = keypol**t / Q # lift of the residue ring generator

  ###########################  InductiveValuation  #############################

  def name(self):
    r"""
    Return the name of the generator of the polynomial ring
    """
    return self._polring._names[0]

  def __repr__(self):
    s = self.stage()
    pv = [(V._keypol,V._keyval) for V in self.stages()]
    if self.stage_zero()._intrinsic_uniformizer:
      return 'Stage {} valuation with (keypol,keyval) sequence {}'.format(s,pv)
    u = self.stage_zero()._base_uniformizer
    return 'Stage {} valuation over {} with (keypol,keyval) sequence {}'.format(s,u,pv)

  def __str__(self):
    attr = []
    attr.append('_base_field')
    attr.append('_polring')
    attr.append('_keypol')
    attr.append('_keyval')
    attr.append('_denom')
    attr.append('_relative_denom')
    attr.append('_residue_constant_field')
    attr.append('_residue_ring')
    attr.append('_Q')
    attr.append('_genlift')
    n = max(len(a) for a in attr)
    u = self.stage_zero()._base_uniformizer
    K = self._base_field
    s = 'Inductive valuation over {} in {}:\n'.format(u,K)
    for V in self._stages + [self]:
      m = len('Stage {}:'.format(V.stage()))
      s += '  '+'-'*m + '\n'
      s += '  Stage {}:\n'.format(V.stage())
      s += '  '+'-'*m + '\n'
      for a in attr:
        v = getattr(V,a,None)
        if v is not None:
          s += '    {0:{1}}  =  {2}\n'.format(a,n,v)
    return s


  def str_compact(self):
    r"""
    Return a compact string representation of self.

    The format is:

          p;,c00,c01,...,:v0;...;,ck0,ck1,...:vk

    where ``p`` is the string representation of self.base_uniformizer(), ``cij``
    is the coefficient of x^j in the i-th key polynomial, and ``vi`` is the
    i-th key value.  All puntuation is literal, except for the ellipses (...).
    A key value of ``Infinity`` is represented as ``1/0``.

    EXAMPLES::

      sage: R.<x> = QQ[]
      sage: polvals = [(x, 0), (x^2 + 1, 1/2), (x^4 + 2*x^2 + 8, Infinity)]
      sage: V = p_adic_inductive_valuation(7, key_polval_list=polvals)
      sage: V.str_compact()
      '7;,0,1:0;,1,0,1:1/2;,8,0,2,0,1:1/0'
    """
    s = str(self.base_uniformizer())
    for i,V in enumerate(self.stages()):
      s += ';'
      for j,c in enumerate(list(V._keypol)):
        s += ',' + repr(c)
      s += ':'
      s += '1/0' if V._keyval == Infinity else str(V._keyval)
    return s


  def validate(self):
    r"""
    Check whether all stages of self are valid.

    OUTPUT:

    - True if the following hold:

      * The key polynomial of each stage of self satisfies Definition 4.1 of
        [MacLane-1];

      * Key polynomials of consecutive stages of self satisfy Definition 6.1 of
        [MacLane-1]; and

      * For each stage `V` that is an augmentation of `W`, we have `V\phi > W\phi`,
        where `\phi` is the key polynomial for `V`.

    """
    name = 'validate'
    for V in self._stages+[self]:
      if V.is_stage_zero(): continue
      W = V.prev()
      n = V.stage()
      keypol, keyval = V._keypol, V._keyval
      if not W.is_key(keypol):
        return False
      if keyval <= W(keypol):
        return False
    return True

  ###########################  InductiveValuation  #############################

  def expand(self, f):
    r"""
    Return the expansion of `f` as a polynomial in `self._keypol`.
    """
    return expand_polynomial(f,self._keypol)

  def base_valuation(self, c):
    r"""
    Return the valuation of an element of the base field
    """
    V0 = self.stage_zero()
    return V0._base_valuation(c)

  def valuation(self, f):
    r"""
    Return the valuation of a polynomial or rational function over the base field
    """
    if f == 0:
      return Infinity

    K = self._base_field
    if f in K:
      return self.base_valuation(K(f))

    R = self._polring
    if f not in R:
      try:
        num = R(f.numerator())
        den = R(f.denominator())
        return self.valuation(num) - self.valuation(den)
      except (AttributeError,TypeError):
        raise ValueError('"f" is not a polynomial or rational function over the base field')

    v = Infinity
    K = self._base_field
    W = self.prev()
    mu = self._keyval
    ff = self.expand(f)
    if mu == Infinity:
      # No contribution from higher degree terms if mu = Infinity
      ff = {0:ff[0]} if 0 in ff else {}
    for i,c in ff.items():
      if c == 0: continue
      if self.is_stage_zero():
        vi = self._base_valuation(K(c))
      else:
        vi = W.valuation(c)
      v = min(v,vi) if i==0 else min(v, vi + i*mu)
    return v

  def normalized_valuation(self, f):
    r"""
    Return the valuation of f with respect to self, normalized to have
    integer values
    """
    v = self.valuation(f)
    if v == Infinity: return v
    return ZZ(v/self._uniformizer_val)

  def normalize(self, v):
    r"""
    Return the normalized value associated with v

    INPUT:

    - ``v`` -- a rational number in the value group of self

    OUTPUT:

    - the unique integer `n` such that ``v`` is `n` times the value of the
      uniformizer of self

    """
    if v == Infinity: return v
    n = v / self._uniformizer_val
    if n not in ZZ:
      raise ValueError('"v" not in the value group of self.')
    return ZZ(n)

  def __call__(self, x):
    return self.valuation(x)

  ###########################  InductiveValuation  #############################

  def key_polval_list(self):
    return tuple((V.keypol(),V.keyval()) for V in self.stages())

  def invariants(self):
    r"""
    Return relative (residue_degree, ramification_index) for all stages of self.
    """
    cc = []
    for V in self.stages():
      cc.append((V.relative_residue_degree(), V.relative_ramification_index()))
    return cc

  def __hash__(self):
    return hash(self.key_polval_list())

  def stages(self):
    r"""
    Return an iterator over the stages of self.
    """
    for V in self._stages:
      yield V
    yield self

  def __getitem__(self,i):
    r"""
    Return the stage-i predecessor of self.
    """
    if i > len(self._stages):
      raise ValueError('No stage-{} valuation associated with self.'.format(i))
    if i == len(self._stages):
      return self
    return self._stages[i]

  def base_field(self):
    r"""
    Return the base field from which this valuation extends
    """
    return self._base_field

  def polring(self):
    r"""
    Return the polynomial ring on which self is a valuation
    """
    return self._polring

  def keypol(self):
    return self._keypol

  def keyval(self):
    return self._keyval

  def keypolval(self):
    r"""
    Return the last key polynomial and its value
    """
    return self._keypol, self._keyval

  def residue_ring(self):
    r"""
    Return the residue ring for self
    """
    return self._residue_ring

  def residue_constant_field(self):
    r"""
    Return the constant field of the residue ring
    """
    return self._residue_constant_field

  def residue_constant_field_gen(self):
    r"""
    Return the generator of the residue constant field over the previous one.
    This is a root of the previous-stage reduction of the current key polynomial.
    For a stage-zero valuation, return 1 as an element of the residue constant field.
    """
    if self.is_stage_zero():
      return self._residue_constant_field(1)
    return self._residue_extension.gen()

  def residue_constant_field_reduce(self, f):
    r"""
    Reduce a polynomial over the previous residue constant field into the current one.
    This amounts to evaluating f(z) where z = self.residue_constant_field_gen().
    For a stage-zero valuation, this just evaluates f(1).
    """
    if self.is_stage_zero():
      return f(self._residue_constant_field(1))
    return self._residue_extension.reduce(f)

  def residue_constant_field_lift(self, fbar):
    r"""
    Lift an element of the residue constant field to a polynomial over the previous one.
    This is an error if self is a stage-zero valuation.
    """
    if self.is_stage_zero():
      raise TypeError('No previous stage to lift to')
    return self._residue_extension.lift(fbar)

  def residue_constant_field_expand(self, elt):
    r"""
    Return a nested list of coefficients of ``elt`` with respect to the tower of extensions.

    INPUT:

    - ``elt`` -- an element of self.residue_constant_field()

    OUTPUT:

    - A nested list of lists [ [...], ... [...] ]  where the list at nesting
      level k (from the inside) represents the coefficient list of an element of
      the stage-k residue constant field, as a polynomial in the generator of
      the relative extension.  The innermost entries are elements of the residue
      constant field at stage-0.

    EXAMPLES::

      sage: Z = p_adic_inductive_valuation(11,'x')
      sage: V = inductive_valuation_from_invariants(Z,[(1,1),(2,1),(3,1)])
      sage: V0,V1,V2 = list(V.stages())
      sage: R0,R1,R2 = [v.residue_ring() for v in V.stages()]
      sage: M1 = V1.residue_constant_field_reduce
      sage: M2 = V2.residue_constant_field_reduce
      sage: g0,g1,g2 = [v.residue_constant_field_gen() for v in V.stages()]
      sage: z0 = M2(R1(M1(R0(g0))))
      sage: print(z0)
      1
      sage: z1 = M2(R1(g1))
      sage: z2 = g2
      sage: V.residue_constant_field_expand(z0)
      [[1, 0], [0, 0], [0, 0]]
      sage: V.residue_constant_field_expand(z1)
      [[0, 1], [0, 0], [0, 0]]
      sage: V.residue_constant_field_expand(z2)
      [[0, 0], [1, 0], [0, 0]]
      sage: c = (1+2*z1) + (3+4*z1)*z2 + (5+6*z1)*z2^2
      sage: V.residue_constant_field_expand(c)
      [[1, 2], [3, 4], [5, 6]]

      sage: QQpol.<x> = QQ[]
      sage: f0 = x - 4
      sage: f1 = x^2 - 8*x - 39
      sage: f2 = x^8 - 32*x^7 + 228*x^6 + 1333*x^5 - 9470*x^4 - 84294*x^3 + 99948*x^2 + 2252133*x + 3877729
      sage: V0 = p_adic_inductive_valuation(11, key_polynomial=f0, key_value=1/2)
      sage: V1 = V0.augment(f1, 5/4)
      sage: V2 = V1.augment(f2, 21/4)
      sage: invariants = [(V.relative_residue_degree(),V.relative_ramification_index()) for V in V2.stages()]
      sage: print(invariants)
      [(1, 2), (1, 2), (2, 1)]
      sage: R0,R1,R2 = [v.residue_ring() for v in V2.stages()]
      sage: M1 = V1.residue_constant_field_reduce
      sage: M2 = V2.residue_constant_field_reduce
      sage: g0,g1,g2 = [v.residue_constant_field_gen() for v in V2.stages()]
      sage: z0 = M2(R1(M1(R0(g0))))
      sage: print(z0)
      1
      sage: z1 = M2(R1(g1))
      sage: print(z1)
      5
      sage: z2 = g2
      sage: V2.residue_constant_field_expand(z0)
      [[1], [0]]
      sage: V2.residue_constant_field_expand(z1)
      [[5], [0]]
      sage: V2.residue_constant_field_expand(z2)
      [[0], [1]]

    """
    if self.is_stage_zero():
      return elt
    cc = list(self.residue_constant_field_lift(elt))
    F = self.residue_constant_field()
    while len(cc) < self.relative_residue_degree():
      cc.append(F(0))
    V = self.prev()
    return [ V.residue_constant_field_expand(c) for c in cc ]


  def residue_constant_field_collapse(self, coef_list):
    r"""
    Return the residue constant field with given expanded coefficient list.
    This is inverse to residue_constant_field_expand.

    INPUT:

    - ``coef_list`` -- a list of lists representing an element of the residue
      constant field.  The inner-most entries must be coercible to the residue
      constant field of the stage-zero valuation.  At each subsequent nesting
      level, the length of the list must equal the relative residue degree of
      the corresponding stage.

    OUTPUT:

    - An element of self.residue_constant_field().

    EXAMPLES::

      sage: Z = p_adic_inductive_valuation(11,'x')
      sage: V = inductive_valuation_from_invariants(Z, [(1,2),(2,3),(1,2),(3,2)])
      sage: V.invariants()
      [(1, 2), (2, 3), (1, 2), (3, 2)]
      sage: cc = [[[1, 2]], [[3, 4]], [[5, 6]]]
      sage: c = V.residue_constant_field_collapse(cc)
      sage: cc == V.residue_constant_field_expand(c)
      True
      sage: c = V.residue_constant_field().random_element()
      sage: cc = V.residue_constant_field_expand(c)
      sage: c == V.residue_constant_field_collapse(cc)
      True

    """
    if self.is_stage_zero():
      return self.residue_constant_field()(coef_list)
    V = self.prev()
    R = V.residue_ring()
    cc =  [V.residue_constant_field_collapse(c) for c in coef_list]
    f = R(cc)
    return self.residue_constant_field_reduce(f)

  def relative_residue_degree(self):
    r"""
    Return the residue degree of self over the base residue field
    """
    if self.is_stage_zero():
      return self._residue_degree
    prevdeg = self.prev()._residue_degree
    return self._residue_degree // prevdeg

  def residue_degree(self):
    r"""
    Return the residue degree of self over the base residue field
    """
    return self._residue_degree

  def relative_ramification_index(self):
    r"""
    Return the relative ramification index of self over the previous stage
    """
    return self._relative_denom

  def ramification_index(self):
    r"""
    Return the ramification index of self over the base field
    """
    e = self._relative_denom
    for V in self._stages:
      e *= V._relative_denom
    return e

  def base_uniformizer(self):
    r"""
    Return the uniformizer for the base-field valuation.
    """
    return self.stage_zero()._base_uniformizer

  def base_uniformizer_value(self):
    r"""
    Return the value of the uniformizer for the base-field valuation.
    This is a rational number.  It is usually 1, but may be anything.
    """
    return self.stage_zero()._base_unif_val

  def uniformizer(self):
    r"""
    Return a uniformizer for self

    OUTPUT:

    - A uniformizer for self, as an element of the polynomial ring.

    """
    return self.polynomial_with_value(self._uniformizer_val)

  def uniformizer_valuation(self):
    r"""
    Return the stored valuation of a uniformizer for self

    OUTPUT:

    - The stored valuation of a uniformizer for self

    """
    return self._uniformizer_val


  ###########################  InductiveValuation  #############################

  def stage_zero(self):
    r"""
    Return the stage-0 valuation associated to self
    """
    return self[0]

  def is_stage_zero(self):
    r"""
    Return True if self is a stage-0 valuation
    """
    return len(self._stages)==0

  def stage(self):
    r"""
    Return the stage of self
    """
    return len(self._stages)

  def prev(self):
    r"""
    Return the previous stage in the inductive valuation, or None
    """
    s = self._stages
    if len(s)==0:
      return None
    return s[-1]

  ###########################  InductiveValuation  #############################

  def _expand_all(self, f):
    r"""
    Return list of expansion data for f with respect to all stages of self.

    INPUT:

    - ``f`` -- A polynomial over the base field.

    OUTPUT:

    - Let K be the base field, p its uniformizer, k the current stage, and
      `\phi_j` the key polynomial at stage j.  The output is a sequence s of
      triples c,v,m, where c in K has valuation 0, v is an integer, and m is a
      list of k+1 nonnegative integers, satisfying:

      ..math::

        f =  \sum_{(c,v,m) \in s} c p^v \prod_{j=0}^{k} \phi_j^{m_j}

    EXAMPLES::

      sage: p = 2
      sage: R.<x> = QQ[]
      sage: G = x^4 + 4 # Newton slope -1/2
      sage: V0 = p_adic_inductive_valuation(p, key_polynomial=x, key_value=1/2)
      sage: V1 = V0.augmentations(G).pop()
      sage: V1
      Stage 1 valuation over 2 with (keypol,keyval) sequence [(x, 1/2), (x^2 + 2, 3/2)]
      sage: H = x^4 + x^3 + x^2 / 2 + 4
      sage: s = V1._expand_all(H)
      sage: s
      [(7, 0, [0, 0]),
       (-1, 1, [1, 0]),
       (-7, -1, [0, 1]),
       (1, 0, [1, 1]),
       (1, 0, [0, 2])]
      sage: P = V0.keypol(), V1.keypol()
      sage: H == sum(c * p^v * prod(Pi^mi for Pi,mi in zip(P,m)) for c,v,m in s)
      True

    """
    if f == 0:
      return []
    Kpol = self._polring
    K = self._base_field
    V0 = self.stage_zero()
    p = V0._base_uniformizer
    coeffs = self.expand(f)
    s = []
    if self.is_stage_zero():
      for i,c in coeffs.items():
        if c==0: continue
        c = K(c)
        v = ZZ(self._base_valuation(c) / self._base_unif_val)
        c /= p**v
        s.append( (c, v, [i]) )
    else:
      W = self.prev()
      for i,coef in coeffs.items():
        for c,v,m in W._expand_all(coef):
          s.append( ( c, v, m + [i] ) )
    return s

  def homogeneous_form(self, f):
    r"""
    Return a polynomial in homogeneous form that is equivalent to f

    INPUT:

    - ``f`` -- a polynomial in self._polring

    OUTPUT:

    - a polynomial `F` with the following properties:

      * `F` is equivalent to ``f``;

      * `F` has the form

        ..math:: \sum_{(c,v,m) \in s} c p^v \prod_{j=0}^{k} \phi_j^{m_j}

        where `c` is an element of valuation 0 in the base field, `v` is an
        integer, `p` is the base field uniformizer, the `\phi_j`'s are the key
        polynomials of the various stages of self, and `m` is a vector of
        exponents; and

      * every term in expansion from the previous bullet has the same valuation
        with respect to self.

    NOTE:

    - This is MacLane's notion of "homogeneous form".

    EXAMPLES::

      sage: p = 2
      sage: R.<x> = QQ[]
      sage: G = x^4 + 4 # Newton slope -1/2
      sage: V = p_adic_inductive_valuation(p, key_polynomial=x, key_value=1/2)
      sage: V1 = V.augmentations(G).pop()
      sage: H = V1.homogeneous_form(G)
      sage: V1.equivalent_polynomials(H,G)
      True

    """
    Kpol = self._polring
    f = Kpol(f)
    vf = self.valuation(f)
    s = self._expand_all(f)
    F = Kpol(0)
    V0 = self.stage_zero()
    p = V0._base_uniformizer
    pval = V0._base_unif_val
    for c,v,m in s:
      # compute valuation of this term
      w = v * pval # valuation of c*p^v
      for j, mj in enumerate(m):
        if mj == 0: continue
        w += mj * self[j]._keyval
      if w > vf:
        # omit this term
        continue
      # add this term
      c = V0._base_lift(V0._base_reduce(c)) # find representative of c
      F += c * p**v * prod(self[j]._keypol**mj for j,mj in enumerate(m))
    return F

  ###########################  InductiveValuation  #############################

  def reduce(self, H):
    r"""
    Return image in the residue ring of a polynomial over the base.

    INPUT:

    - ``H`` -- a polynomial with nonnegative valuation

    OUTPUT:

    - The image of ``H`` in the residue ring.

    EXAMPLES::

      sage: K.<x> = FunctionField(GF(5))
      sage: Kpol.<y> = K[]
      sage: p = x
      sage: G = y^2 + x  # Newton slope is -1/2
      sage: V0 = function_field_inductive_valuation(p, key_polynomial=y, key_value=1/2)
      sage: V0.reduce(G)
      0
      sage: V0.reduce((1/x)*G)
      y0 + 1


      sage: QQpol.<x> = PolynomialRing(QQ)
      sage: V = p_adic_inductive_valuation(3, key_polynomial=x, key_value=Infinity)
      sage: f = x^2 + x + 5
      sage: V.reduce(f)
      2


    """
    h,_,_,v = self.graded_reduction(H)
    if v<0:
      raise ValueError('cannot reduce element of negative valuation')
    if v>0:
      return self._residue_ring(0)
    return h


  ###########################  InductiveValuation  #############################

  def lift(self, h):
    r"""
    Return a polynomial over the base which reduces to given element of the residue ring.

    INPUT:

    - ``h`` -- an element of the residue ring; this is a polynomial over a
      finite field, or a finite field element if self._keyval is Infinity

    OUTPUT:

    - a polynomial over the base field that reduces to ``h``

    ALGORITHM:

    - The residue ring at stage n is R_n = k_n[y], where k_n is a finite
      extension of the stage-0 residue field, given by:

      ..math::

        k_n = R_{n-1}/(f_n)

      where R_{n-1} is the stage n-1 residue ring and f_n is the residual
      image of the key polynomial of self in R_{n-1}.

      To lift h, we need to lift its coefficients (which are in k_n) to elements
      of R_{n-1}, then use the previous stage lift function to lift them all the
      way up.  Those lifted coefficients are then used as coefficients in an
      expansion with respect to ...


    EXAMPLES::

      sage: K.<x> = FunctionField(GF(5))
      sage: Kpol.<y> = K[]
      sage: p = x
      sage: G = y^2 + x  # Newton slope is -1/2
      sage: V0 = function_field_inductive_valuation(p, key_polynomial=y, key_value=1/2)
      sage: h = V0.reduce((1/x)*G)
      sage: V0.lift(h) == (1/x)*G
      True

    Check that it works when key value is Infinity::

      sage: V1 = function_field_inductive_valuation(p, key_polynomial=y, key_value=Infinity)
      sage: R = V1.residue_ring()
      sage: R
      Finite Field of size 5
      sage: h = R(3)
      sage: V1.lift(h)
      3

    """
    return self.graded_reduction_lift(h,0,0)

  ###########################  InductiveValuation  #############################

  def value_group_contains(self, v):
    r"""
    Determine whether ``v`` is in the value group.

    INPUT:

    - ``v`` -- a rational number or +Infinity

    OUTPUT:

    - True if ``v`` is in the value group of self, or if ``v`` is infinite and
      the key value of self is Infinity.  Otherwise False.

    """
    if v == Infinity:
      return True
    if v in QQ:
      return v/self._uniformizer_val in ZZ
    raise ValueError('"v" not a rational number or Infinity.')


  def earliest_stage_with_value(self, v):
    r"""
    Return the earliest stage with value group containing ``v``.

    INPUT:

    - ``v`` -- a rational number or +Infinity

    OUTPUT:

    - the inductive valuation that is the earliest stage of self for which ``v``
      is in its value group, or None if ``v`` is not in the value group of self.

    """
    if not self.value_group_contains(v):
      return None
    V, U = self, self.prev()
    while U is not None and U.value_group_contains(v):
      V, U = U, U.prev()
    return V


  def decompose_value(self, v):
    r"""
    Return coeffients for v as linear combination of key values of stages of self.

    INPUT:

    - ``v`` -- a rational number in the value group of self

    OUTPUT:

    - a pair (z,cc) where z is an integer and cc =[`c_0,\dots,c_n`] a list of
      integers of length n+1, for n = self.stage(), satisfying

         `v = z \alpha + \displaystyle\sum_{i=0}^n c_i \rho_i, \quad 0 \le c_i < e_i`

    where

      - `e_i` is the relative ramification index at stage `i`
      - `\rho_i` is the key value at stage `i`
      - `\alpha` is the valuation of the base field uniformizer

    EXAMPLES::

        sage: V0 = p_adic_inductive_valuation(2,'x')
        sage: V = inductive_valuation_from_invariants(V0,[(1,2),(1,3),(1,5)])

      Note that inductive_valuation_from_invariants makes random choices, but
      over GF(2), there is only one choice of linear irreducible polynomial with
      nonzero constant term. ::

        sage: print(V.str_compact())
        2;,1,1:1/2;,3,2,1:7/6;,35,62,63,44,21,6,1:107/30
        sage: v0,v1,v2 = [W.keyval() for W in V.stages()]
        sage: V.decompose_value(127/30)
        (-1, [1, 1, 1])
        sage: 127/30 == -1 + v0 + v1 + v2
        True
        sage: V.decompose_value(-127/30)
        (-19, [1, 0, 4])
        sage: -127/30 == -19 + v0 + 4*v2
        True

        sage: try:
        ....:   V.decompose_value(1/12)
        ....: except ValueError as err:
        ....:   print(err)
        argument not in value group of self

        sage: W = V.augment(V.keypol(),Infinity)
        sage: print(W.str_compact())
        2;,1,1:1/2;,3,2,1:7/6;,35,62,63,44,21,6,1:1/0
        sage: v0,v1,v2 = [Z.keyval() for Z in W.stages()]
        sage: W.decompose_value(1/6)
        (-1, [0, 1, 0])
        sage: 1/6 == -1 + v1
        True
        sage: W.decompose_value(-1/6)
        (-3, [1, 2, 0])
        sage: -1/6 == -3 + v0 + 2*v1
        True
    """
    # work with normalized base valuation
    b = self.stage_zero()._base_unif_val
    v /= b  # use normalized base valuation
    z = floor(v)
    v -= z  # now v >= 0
    if v == 0: return z, [0 for _ in self.stages()]
    V = self
    cc = []
    while V is not None:
      if v in ZZ:
        cc.extend([0 for _ in V.stages()])
        break
      W = V.earliest_stage_with_value(b*v)
      if W is None:
        raise ValueError('argument not in value group of self')
      while V is not W:
        cc.append(0)
        V = V.prev()
      D = V.ramification_index()
      d = V.relative_ramification_index()
      k = V.keyval() / b
      Dk = ZZ(D*k)
      Dv = ZZ(D*v)
      g = gcd(Dv,Dk)
      num = Dv//g
      den = Dk//g
      c = (num * den.inverse_mod(d)) % d
      cc.append(c)
      v -= c*k
      V = V.prev()
    # now v should be an integer
    try:
      z += ZZ(v)
    except TypeError:
      raise ValueError('argument not in value group of self')
    cc.reverse()
    return z, cc


  def polynomial_with_value(self, v):
    r"""
    Return a polynomial with given valuation, stable under augmentation

    INPUT:

    - ``v`` -- a rational number in the value group of self

    OUTPUT:

    - A polynomial over the base field with valuation `v`, with the following
      properties:

      * its valuation under self is the same as its valuation under any
        augmentation of self;

      * if `v` is in the value group of a previous stage `W`, then the returned
        polynomial will also have the same valuation in self as in `W`.

    EXAMPLES::

        sage: V0 = p_adic_inductive_valuation(2,'x')
        sage: V = inductive_valuation_from_invariants(V0,[(1,2),(1,3),(1,5)])
        sage: print(V.str_compact())
        2;,1,1:1/2;,3,2,1:7/6;,35,62,63,44,21,6,1:107/30
        sage: f = V.polynomial_with_value(127/30)
        sage: print(f)
        1/2*x^9 + 9/2*x^8 + 22*x^7 + 70*x^6 + 159*x^5 + 267*x^4 + 334*x^3 + 302*x^2 + 361/2*x + 105/2
        sage: V(f) == 127/30
        True

      Try a function field example::

        sage: K.<x> = FunctionField(GF(5))
        sage: Kpol.<y> = K[]
        sage: V0 = function_field_inductive_valuation(x, key_polynomial=y, key_value=1/2)
        sage: V0
        Stage 0 valuation over x with (keypol,keyval) sequence [(y, 1/2)]

        sage: V0.polynomial_with_value(1/2)
        y
        sage: V0.polynomial_with_value(-1)
        1/x

        sage: ff = [y,  y^2 + 3*x,  y^6 + 4*x*y^4 + 2*x^2*y^2 + x^3*y + 2*x^3]
        sage: vv = [1/2, 7/6, 107/30]
        sage: kpl = list(zip(ff,vv))
        sage: V = function_field_inductive_valuation(x, key_polval_list=kpl)
        sage: print(V.str_compact())
        x;,0,1:1/2;,3*x,0,1:7/6;,2*x^3,x^3,2*x^2,0,4*x,0,1:107/30
        sage: f = V.polynomial_with_value(7/30)
        sage: print(f)
        1/x^5*y^9 + 2/x^4*y^7 + 4/x^3*y^5 + 1/x^2*y^4 + 3/x^2*y^3 + 3/x*y^2 + 1/x*y
        sage: V(f) == 7/30
        True


    """
    if v == Infinity:
      return self._polring(0)

    V = self.earliest_stage_with_value(v)
    if V is None:
      msg = 'Requested valuation {} is not in the value group ZZ<{}>.'
      raise ValueError(msg.format(v, self._uniformizer_val))

    if V is not self:
      return V.polynomial_with_value(v)

    z, cc = self.decompose_value(v)
    p = self.base_uniformizer()
    return p**z * prod(W.keypol()**c for W,c in zip(self.stages(),cc))


  ###########################  InductiveValuation  #############################

  ## --- GRADED RESIDUE RING ---
  ##
  ## The graded residue ring has the form R = k[s,t,1/t] where s is the image of
  ## the current key polynomial, and t is the image of the previous-stage
  ## uniformizer.  If d and D are relative and absolute value-group
  ## denominators, and the current key value is n/D, with the grading in R
  ## scaled to be integral, we have
  ##
  ##       grade(s) = n
  ##       grade(t) = d
  ##
  ##  and  R_0 = k[y]  where y = s^d/t^n.
  ##
  ## Any element of the value group can be written uniquely as i*n+j*d with i,j
  ## integers and 0<=i<d, and the reduction of an element with that value can be
  ## written uniquely as f(y) * s^i * t^j.  In the code, we represent such an
  ## element of R as a triple (f,i,j), with f in self.residue_ring().
  ##
  ## The following methods are provided:
  ##
  ## - graded_map
  ##     Computes the map of graded residue rings, from previous stage to
  ##     current stage, whose image is k[t,1/t].
  ##
  ## - graded_map_lift
  ##     Computes the inverse of graded_map on the subring k[t,1/t].
  ##
  ## - graded_reduction
  ##     Computes the graded residue image of a polynomial in K[x]
  ##
  ## - graded_reduction_lift
  ##     Computes the unique homogeneous-form preimage of graded_reduction.
  ##
  ##
  ## The map from the previous graded residue ring is computed as follows. If
  ## the previous ring is R' = k'[s',t',1/t'], then k = k'[z]/(f(z)) where f is
  ## the image in R' of the current key polynomial.  If a'n'+b'd' = 1, where
  ## n',d' are previous stage numerator and denominator and 0<=a'<d', then the
  ## map is given by
  ##
  ##         s' |--> t^n' z^b
  ##
  ##         t' |--> t^d' / z^a
  ##
  ## A lift of this is given by      FIXME -- Oh no!!!!!  Finish the sentence!


  def graded_map(self, f, i, j):
    r"""
    Map a homogeneous element of previous graded residue ring to that of self.

    The graded residue ring of self.prev() has the form `k_0[s_0,t_0,1/t_0]`,
    and the input element is `s_0^i t_0^j f(s_0^{d_0}/t_0^{n_0})` where
    `n_0,d_0` are the relative numerator and denominator for self.prev().

    The graded residue ring of self has the form `k[s,t,1/t]`, where `k=k(z)` is
    a finite extension of the residue constant fields (with `z` a root of the
    previous-stage reduction of the current key polymomial), and the map is
    given by

    ..math::

        s_0 &\mapsto t^{n_0}   z^b \\
        t_0 &\mapsto t^{d_0} / z^a

    where `a n_0 + b d_0 = 1`, with `0\le a<d`.  In particular,
    `s_0^{d_0}/t_0^{n_0}` maps to `z`, so

    ..math::

      s_^i t_^j f(s_^{d_0}/t_0^{n_0})  \mapsto  t^{in_0+jd_0} z^{ib-ja} f(z)

    INPUT:

    - ``f`` -- a polynomial in self.prev().residue_ring()

    - ``i,j`` -- integers, with i nonnegative

    OUTPUT:

    - c,m representing `c t^m`, image of `s_0^it_0^jf(s_0^{d_0}/t_0^{n_0})`,
      where

      * c = the element `z^{ib-ja} f(z)` in self.residue_constant_field()

      * m = the integer `m = in_0+jd_0`, exponent on `t`

    """
    if self.is_stage_zero():
      raise TypeError('This method is not valid for stage-zero valuations')
    prev = self.prev()
    n = prev._relative_numer
    d = prev._relative_denom
    a = prev._relative_numer_inv
    b = prev._relative_denom_inv
    m = i*n+j*d
    z = self.residue_constant_field_gen()
    c = self.residue_constant_field_reduce(f)
    c *= z**(i*b-j*a)
    return c,m


  def graded_map_lift(self, c, m):
    r"""
    Lift an element in graded residue ring to previous-stage graded residue ring.

    The graded residue ring has the form `k[s,t,1/t]`, and the elements that
    lift to the previous stage are the ones of the form `c t^m` with `c \in k`
    and `j \in \ZZ`.

    INPUT:

    - ``c`` -- an element of the residue constant field, `k`

    - ``m`` -- an integer

    OUTPUT:

    - a triple ``f,i,j`` representing `(s')^i (t')^j f((s')^{d'}/(t')^{n'})`, a
      lift of `c t^m` in the previous graded residue ring `k'[s',t',1/t']`.
      Here `n',d'` are the relative numerator and denominator of the previous
      stage, and

      * ``f`` is an element of self.prev().residue_ring()

      * ``i,j`` are integers

    """
    if self.is_stage_zero():
      raise TypeError('This method is not valid for stage-zero valuations')
    prev = self.prev()
    n = prev._relative_numer
    d = prev._relative_denom
    a = prev._relative_numer_inv
    b = prev._relative_denom_inv
    i = ZZ(a*m)
    if 0 <= i < d:
      j = b*m
      f = self.residue_constant_field_lift(c)
    else:
      v,i = i.quo_rem(d)
      j = n*v + b*m
      z = self.residue_constant_field_gen()
      f = self.residue_constant_field_lift(c * z**v)
    return f, i, j


  def graded_reduction(self, f):
    r"""
    Return graded residue image of f, and the valuation of f in self

    INPUT:

    - ``f`` -- element of self.polring()

    OUTPUT:

    - tuple fbar,i,j,v:

      - ``fbar`` -- univariate polynomial over the residue constant field k

      - ``i,j`` -- integers, with i in range(0,d)

      - ``v`` -- rational number

      representing the homogeneous element s^i t^j f(s^d/t^n) of grade v in the
      graded residue ring k[s,t,1/t], where

        * D = self._denom  [ = self.ramification_index() * self.base_uniformizer_value() ]

        * d = self.relative_ramification_index()

        * n = self.keyval() * D

        * v = (i*n+j*d)/D

    METHOD:

    If `\rho` is the reduction map, `\phi` the key polynomial and `\pi` a
    uniformizer for the previous stage, the residue ring is `k[s,t,1/t]`
    where

      * `s = \rho(\phi)`   has grade `n/D`

      * `t = \rho(\pi)`    has grade `d/D`

    and any homogeneous element of grade N/D has the form

    ..math::

      s^{i_0} t^{j_0} H(s^d/t^n)

    where `i_0,j_0` are the unique integers with `i_0*n+j_0*d=N` and
    `0\le{i_0}<d`, and H has coefficients in the constant field `k`. Thus
    for each term `c \phi^i` of minimum value `N/D` in the expansion of `f`, we
    get a term

    ..math::

      s^i \rho(c)  &=  s^{i_0} t^{mn} \rho(c) (s^d/t^n)^m \\
                   &=  s^{i_0} t^{j_0} cbar (s^d/t^n)^m \\

    where `m = (i-i_0)/d`, and `\rho(c)\in k[t,1/t]` necessarily has the form
    `\rho(c)=cbar t^{j_0-mn}` with `cbar\in k`.  To compute `\rho(c)`, we first
    reduce `c` with respect to the previous stage, as a homogeneous element of
    the residue ring k0[s_0,t_0,1/t_0], expressed analogously to the above, and
    then call self.graded_map() to get an element of `k[t,1/t]`.


    """
    R = self._residue_ring

    # Infinite key value
    if self._keyval == Infinity:
      c = f % self._keypol
      if c == 0:
        # FIXME:  Is it right to flag an error?  Or should it just map to zero?
        raise ValueError('Element with infinite value has no residual image')
      # Stage zero
      if self.is_stage_zero():
        # Use base-field valuation for coefficients.
        K = self._base_field
        V = self._base_valuation
        p = self._base_uniformizer
        v = V(K(c))
        j = ZZ(v/self._base_unif_val)
        cbar = self._base_reduce(c/p**j)
        return R(cbar),0,j,v
      # Augmentation
      prev = self.prev()
      c0,i0,j0,v = prev.graded_reduction(c)
      j = j0 + i0 * prev._keyval * prev._denom
      return R(c0),0,j,v

    # Finite key value

    ff = {}
    d = self._relative_denom
    n = self._relative_numer
    ninv = n.inverse_mod(d)

    # Stage zero
    if self.is_stage_zero():
      V = self._base_valuation
      p = self._base_uniformizer
      red = self._base_reduce
      K = self._base_field
      B = self._base_unif_val
      for i,c in self.expand(f).items():
        if c==0: continue
        v = V(K(c))
        j = ZZ(v/B)
        cbar = red(K(c)/p**j)   # NOTE: cbar has grade 0
        ff[i] = (j,i*n+j*d,cbar)
      Vfnum = min(vnum for _,vnum,_ in ff.values())
      i0 = None
      gg = {}
      for i,(j,vnum,cbar) in ff.items():
        if vnum != Vfnum: continue
        # Term is s^i t^j cbar = s^i0 t^j0 cbar (s^d/t^n)^m   for some m
        if i0 is None:
          i0 = i%d
          j0 = (Vfnum-i0*n)//d
        m = (i-i0)//d
        gg[m] = cbar
      assert len(gg) > 0, 'Graded reduction should not be zero!'
      return R(gg),i0,j0,Vfnum/self._denom

    # Augmentation
    D = self._denom
    prev = self.prev()
    for i,c in self.expand(f).items():
      if c==0: continue
      c1,i1,j1,Vc = prev.graded_reduction(c)
      Vnum = ZZ(Vc*D) + i*n
      ff[i] = (Vnum,i1,j1,c1)
    Vfnum = min(Vnum for Vnum,_,_,_ in ff.values())
    gg = {}
    i0 = None
    cc = {}
    for i,(Vnum,i1,j1,c1) in ff.items():
      if Vnum != Vfnum: continue
      if i0 is None:
        i0 = (ninv*Vfnum) % d
        j0 = (Vfnum - i0*n) // d
      m = (i-i0)//d
      cbar, j = self.graded_map(c1,i1,j1) # Image of map from previous ring.
      assert j==j0-m*n                    # Reality check.
      cc[m] = cbar
    return R(cc),i0,j0,Vfnum/D


  def graded_reduction_lift(self, f, i=None, j=None, v=None):
    r"""
    Return a lift to self.polring() of a homogeneous element of the residue ring of self.

    The residue ring is `k[s,t,1/t]` where `s = \rho(\phi)` and `t=\rho(\pi)`,
    for `\phi` the last key polynomial of self, and `\pi` a uniformizer for the
    previous stage.  Homogeneous elements have the form `f(s^d/t^n) s^i t^j`.

    INPUT:

    - ``f`` -- a polynomial over self.residue_constant_field().

    - ``i,j`` -- optional integers, with `i\ge 0`, exponents on `s` and `t`
      respectively.  Either of these that is not given is determined by ``v``
      (see below).  If ``v`` is not given, then the defaults are `i=0` and
      `j=n\deg(f)` (making the lift be monic in `\phi`).

    - ``v`` -- optional rational number, in the value group of self.  This is
      ignored if both ``i,j`` are given.  Otherwise, `i,j` (or whichever is not
      given) are determined as the integer solutions to `in+jd=vD`, where `d,D`
      are the relative and absolute denominators (respectively) of the value
      group, and `n/D` is the key value.  If `i` is not given, then this
      solution is made unique by also requiring `0\le i<d`.  An error is raised
      if no solution exists.

    OUTPUT:

    - a polynomial F(x) in self.polring().

    """
    resring = self._residue_ring
    polring = self._polring
    f = resring(f)
    if self._keyval == Infinity:
      if self.is_stage_zero():
        return polring(self._base_lift(f))
      f0,i,j = self.graded_map_lift(f,0) # i and j should both be
      assert i == j == 0
      return self.prev().graded_reduction_lift(f0,0,0)


    D = self._denom
    n = self._relative_numer
    d = self._relative_denom
    a = self._relative_numer_inv
    b = self._relative_denom_inv
    deg = f.degree()
    if i is None or j is None:
      if v is None:
        if i is None:
          i = 0
        if j is None:
          j = n * f.degree()
      else:
        vnum = ZZ(v*D)
        if i is None and j is None:
          # i*n + j*d = v*D
          i = (vnum * a) % d
          j = (vnum - i*n) // d
        elif i is None:
          inum = vnum - j*d
          if inum % n != 0:
            raise ValueError('Given values of j and v are incompatible')
          i = inum//n
        else:
          jnum = vnum - i*n
          if jnum % d != 0:
            raise ValueError('Given values of i and v are incompatible')
          j = jnum//d

    if i < 0:
      raise ValueError('Value of i must be non-negative')

    R = self.polring()
    F = R(0)
    phi = self.keypol()
    prev = self.prev()
    for k,c in enumerate(f.list()):
      if c==0: continue
      # Lift c t^(j-kn) s^(i+kd) -->  C \phi^(i+kd)
      ii = i+k*d
      jj = j-k*n
      if self.is_stage_zero():
        C = self._base_lift(c) * self._base_uniformizer**jj
      else:
        f0,i0,j0 = self.graded_map_lift(c,jj)
        C = prev.graded_reduction_lift(f0,i0,j0)
      F += C * phi**ii
    return F


  ###########################  InductiveValuation  #############################

  def residual_polynomial(self, f):
    r"""
    Return a residual polynomial of f with respect to self.

    INPUT:

    - ``f`` -- a polynomial over the base field that is not equivalence
      divisible by the current key polynomial.

    OUTPUT:

    - the reduction of R*f, where R is the polynomial returned by
      self.polynomial_with_value(v) for v = -self.valuation(f).

    EXAMPLES::

      sage: K.<x> = FunctionField(GF(5))
      sage: Kpol.<y> = K[]
      sage: p = x
      sage: G = y^2 + x  # Newton slope is -1/2
      sage: V0 = function_field_inductive_valuation(p, key_polynomial=y, key_value=1/2)
      sage: V0.residual_polynomial(G)
      y0 + 1

    """
    fbar,_,_,_ = self.graded_reduction(f)
    return fbar

  ###########################  InductiveValuation  #############################

  def keypol_from_residual(self, h):
    r"""
    Return a key polynomial by lifting an irreducible element of the residue ring

    INPUT:

    - ``h`` -- monic irreducible polynomial in the residue ring

    OUTPUT:

    - a key polynomial over self whose associated residual polynomial is a
      constant multiple of ``h``

    NOTE:

    - We do not check that ``h`` is monic or irreducible.

    ALGORITHM:

    - Lift `h`, normalize it so that its leading coefficient in the
      keypol-expansion is equivalent to 1, and then replace with an equivalent
      monic homogeneous polynomial

    EXAMPLES::

      sage: K.<x> = FunctionField(GF(5))
      sage: Kpol.<y> = K[]
      sage: p = x
      sage: G = y^2 + x  # Newton slope is -1/2
      sage: V0 = function_field_inductive_valuation(p, key_polynomial=y, key_value=1/2)
      sage: h = V0.reduce(G/x)
      sage: h
      y0 + 1
      sage: V0.keypol_from_residual(h)
      y^2 + x

    """
    if self._keyval == Infinity:
      raise ValueError('Current key value is infinite; no new key polynomials exist.')
    return self.graded_reduction_lift(h)


  def new_keys(self, G):
    r"""
    Return all key polynomials which lead to new approximants for G

    INPUT:

    - A polynomial over the base field

    OUTPUT:

    - A list of polynomials each of which is key over self

    EXAMPLES::

      sage: K.<x> = FunctionField(GF(5))
      sage: Kpol.<y> = K[]
      sage: p = x
      sage: G = y^4 + x^3 + 4*x^2  # Newton slope is -1/2
      sage: V0 = function_field_inductive_valuation(p, key_polynomial=y, key_value=1/2)
      sage: V0.new_keys(G)
      [y^2 + x, y^2 + 4*x]

    """
    if self.valuation(G) == Infinity:
      return []
    h = self.residual_polynomial(G)
    hfac = h.factor()
    # if G is (almost) a key polynomial, we should use it.
    if len(hfac) == 1 and hfac[0][1] == 1:
      G0 = G / G.leading_coefficient()
      if self.is_key(G0):
        return [G0]
    y = h.parent().gen()
    return [self.keypol_from_residual(u) for u,_ in hfac if u != y]

  ###########################  InductiveValuation  #############################

  def newton_slopes(self, f, P=None):
    r"""
    Return the Newton slopes of f relative to P

    INPUT:

    - ``f`` -- a polynomial over the base field

    - ``P`` -- optional nonzero polynomial; if not specified, use the current
      key polynomial

    OUTPUT:

    - a list of pairs `(m_0,n_0), \ldots, (m_r,n_r)`, where

      * `m_i` is the slope of the i-th face of the lower convex hull of the
        Newton polygon for the ``P``-expansion of ``f``;

      * `n_i` is the x-axis projection length of the i-th face.

      We have `m_0 < m_1 < \cdots < m_r`. The first slope is `m_0 = -Infinity` if
      the constant coefficient of the ``P``-expansion of ``f`` is 0.

    """
    if P is None:
      P = self._keypol
    cc = expand_polynomial(f,P)
    vv = {i:self.valuation(c) for i,c in cc.items() if c != 0}
    return newton_slopes(vv)

  def new_values(self, G, P):
    r"""
    Return all values v that lead to G-approximants for self with key polynomial P

    INPUT:

    - ``G`` -- a polynomial over the base field

    - ``P`` -- a key polynomial over self

    OUTPUT:

    - A list of rational numbers that lead to G-approximants for self with key
      polynomial P

    EXAMPLES::

      sage: K.<x> = FunctionField(GF(5))
      sage: Kpol.<y> = K[]
      sage: p = x
      sage: G = y^4 + x^3 + 4*x^2  # Newton slope is -1/2
      sage: V0 = function_field_inductive_valuation(p, key_polynomial=y, key_value=1/2)
      sage: phi = V0.new_keys(G)[0]
      sage: V0.new_values(G,phi)
      [2]

    """
    if G == P:
      return [Infinity]
    ss = [-v for v,_ in self.newton_slopes(G,P)]
    return [s for s in ss if s > self.valuation(P)] # keep only slopes for principal part

  def new_key_value_pairs(self, G):
    r"""
    Return a list of (key polynomial, key value) pairs for G-approximants to self

    INPUT:

    - ``G`` -- a polynomial over the base field

    OUTPUT:

    - A list of pairs `(P,v)` where

      * `P` is a key polynomial over self that is an
      equivalence factor of ``G``; and

      * `v` is a rational number that is a slope of the principal part of the
        Newton polygon of ``G`` relative to `P`.

    EXAMPLES::

      sage: K.<x> = FunctionField(GF(5))
      sage: Kpol.<y> = K[]
      sage: p = x
      sage: G = y^4 + x^3 + 4*x^2  # Newton slope is -1/2
      sage: V0 = function_field_inductive_valuation(p, key_polynomial=y, key_value=1/2)
      sage: V0.new_key_value_pairs(G)
      [(y^2 + x, 2), (y^2 + 4*x, 2)]

    """
    kv = []
    for k in self.new_keys(G):
      for v in self.new_values(G,k):
        kv.append((k,v))
    return kv

  ###########################  InductiveValuation  #############################

  def augment(self, keypol, keyval, check=False, collapse=True):
    r"""
    Return augmentation of self with given keypol and keyval.

    INTPUT:

    - ``keypol`` -- a key polynomial over self

    - ``keyval`` -- a rational number to assign as the new valuation of ``keypol``

    - ``check`` -- boolean (default: False); whether to verify that
      `(keypol,keyval)` is valid data for augmenting self

    - ``collapse`` -- boolean (default: False); whether to collapse the new
      stage if possible

    OUTPUT:

    - An InductiveValuation object constructed from self by MacLane's
      augmentation technique using the key polynomial ``keypol`` and the new key
      value ``keyval``. If ``collapse`` is True, then the final stage of self
      may be replaced by the augmented valuation as applicable.

    REFERENCES:

    -  [MacLane-1], Sections 4, 6, 15

    EXAMPLES::

      sage: K.<x> = FunctionField(GF(5))
      sage: Kpol.<y> = K[]
      sage: p = x
      sage: G = y^4 + x^3 + 4*x^2  # Newton slope is -1/2
      sage: V0 = function_field_inductive_valuation(p, key_polynomial=y, key_value=1/2)
      sage: key_val_pairs = V0.new_key_value_pairs(G)
      sage: phi,mu = key_val_pairs[1]
      sage: (phi, mu)
      (y^2 + 4*x, 2)
      sage: V1 = V0.augment(phi, mu, check=True)
      sage: V1
      Stage 1 valuation over x with (keypol,keyval) sequence [(y, 1/2), (y^2 + 4*x, 2)]

    """
    kwargs = {}
    kwargs['key_polynomial'] = keypol
    kwargs['key_value'] = keyval

    if check:
      if not self.is_key(keypol):
        raise ValueError('keypol is not a key polynomial')
      if keyval <= self(keypol):
        raise ValueError('keyval is not larger than current value')

    if collapse and self.keypol().degree() == keypol.degree():
      if self.is_stage_zero():
        # Need to initialize a new stage-0 valuation
        kwargs['valuation'] = self._base_valuation
        kwargs['uniformizer'] = self._base_uniformizer
        kwargs['residue_field'] = self._residue_constant_field
        kwargs['reduce_map'] = self._base_reduce
        kwargs['lift_map'] = self._base_lift
      else:
        kwargs['previous'] = self.prev()
    else:
      # No need to collapse
      kwargs['previous'] = self

    return InductiveValuation(**kwargs)

  def augmentations(self, G, collapse=True):
    r"""
    Return a list of all valid G-approximant augmentations of self

    INPUT:

    - ``G`` -- a nonzero polynomial over the base field

    - ``collapse`` -- boolean (default: False); whether to collapse the new stage
      if possible

    OUTPUT:

    - the list of all valid G-approximant augmentations of self as explained in
      [MacLane-2]

    """
    return [self.augment(k,v,collapse=collapse) for k,v in self.new_key_value_pairs(G)]


  def is_minimal(self, f):
    r"""
    Return whether f is minimal in the sense of MacLane

    INPUT:

    - ``f`` -- a polynomial over the base field

    OUTPUT:

    - True if ``f`` is a minimal polynomial in the sense of MacLane, and False
      otherwise.

    REFERENCES:

    - Remark 2.3 on p.495 of [MacLane-2]

    """
    vf = self.valuation(f)
    cc = self.expand(f)
    n = max(cc)  # degree of expansion
    cn = cc[n]   # leading coefficient
    K = self._base_field
    if cn not in K:
      return False
    if vf != self.base_valuation(K(cn)) + n*self._keyval:
      return False
    return True

  def is_key(self, f):
    r"""
    Return whether f is a key polynomial

    INPUT:

    - ``f`` -- a polynomial over the base field

    OUTPUT:

    - True if and only if ``f`` is a key polynomial in the sense of MacLane.

    REFERENCES:

    - Definition 4.1 and Theorem 9.4 of [MacLane-1]. We further assume that
      ``f`` is nonconstant in order to be a key polynomial, as this is clearly
      necessary in order to expand other polynomials in terms of ``f``.

    """
    name = 'is_key'
    vf = self.valuation(f)
    cc = self.expand(f)
    n = max(cc)
    if cc[n] != 1:
      # not monic
      return False
    if n*self._keyval != vf:
      # not minimal
      return False
    if n == 0:
      # constants are not key polynomials
      return False

    if self.valuation(cc.get(0,0)) > vf:
      # f is equivalence divisible by the key polynomial
      if n == 1:
        # f = keypol + f_0 is equivalent to the key polynomial, which is ok
        return True
      return False

    # Now f is not equivalence divisible by the key polynomial.
    R = self.residual_polynomial(f)
    if not R.is_irreducible():
      # f is not equivalence irreducible
      return False

    return True


  def projection(self, G):
    r"""
    Compute the length of the horizontal projection of polynomial G along self.

    INPUT:

    - ``G`` -- a nonzero polynomial over the base field

    OUTPUT:

    - a positive integer corresponding to the projection length of the segment
      of the Newton polygon of ``G`` (relative to the current key polynomial)
      that has slope equal to the negative of the current key value

    NOTE:

    - We compute the projection length as max(ii) - min(ii) where ii are the
      indices i such that self( a_i*P^i ) = self(G), where P=self._keypol and
      G = sum_i a_i P^i.

    EXAMPLES::

      sage: K.<x> = FunctionField(GF(5))
      sage: Kpol.<y> = K[]
      sage: p = x
      sage: G = y^4 + x^3 + 4*x^2  # Newton slope is -1/2
      sage: V0 = function_field_inductive_valuation(p, key_polynomial=y, key_value=1/2)
      sage: key_val_pairs = V0.new_key_value_pairs(G)
      sage: phi,mu = key_val_pairs[1]
      sage: (phi, mu)
      (y^2 + 4*x, 2)
      sage: V1 = V0.augment(phi, mu, check=True)
      sage: V1.projection(G)
      1

    """
    v = self.valuation(G)
    if v == Infinity:
      return 1
    e = self.expand(G)
    mu = self._keyval
    ii = [i for i,c in e.items() if self.valuation(c) + i*mu == v]
    return ii[-1] - ii[0]

  def collapse(self):
    r"""
    Return an equivalent inductive valuation with strictly increasing key polynomial degrees.

    OUTPUT:

    - Return `self` if it already has strictly increasing key polynomial
      degrees. Otherwise, return a new InductiveValuation that yields all the
      same values as `self`, but whose key polynomials have strictly increasing
      degrees.

    NOTE:

    - MacLane does not address the issue of whether one can collapse a stage-1
      valuation with a linear key polynomial. In fact, one can, provided that we
      extend his theory to include stage-0 valuations with arbitrary monic
      linear key polynomials.

    REFERENCES:

    - Lemma 15.1 of [MacLane-1]

    EXAMPLES::

      sage: p = 2
      sage: R.<x> = QQ[]
      sage: G = x^2 - 1 # Newton slope 0
      sage: V0 = p_adic_inductive_valuation(p, key_polynomial=x)
      sage: V1 = V0.augmentations(G,collapse=False).pop()
      sage: V2 = V1.augmentations(G,collapse=False).pop()
      sage: V2
      Stage 2 valuation over 2 with (keypol,keyval) sequence [(x, 0), (x + 1, 1), (x + 3, 2)]
      sage: V2.collapse()
      Stage 0 valuation over 2 with (keypol,keyval) sequence [(x + 3, 2)]

    """
    # Handle cases where we do not collapse anything.
    if self.is_stage_zero():
      return self
    S = self._stages[1:] + [self]
    if all(V.prev().keypol().degree() < V.keypol().degree() for V in S):
      return self

    # Proceed recursively.
    W = self.prev().collapse()
    if W.keypol().degree() != self.keypol().degree():
      return W.augment(self._keypol,self._keyval)
    # Now final key polynomial of W has same degree as current one
    if not W.is_stage_zero():
      return W.prev().augment(self._keypol,self._keyval)
    # We must initialize a new stage-0 InductiveValuation
    kwargs = {}
    kwargs['valuation'] = W._base_valuation
    kwargs['uniformizer'] = W._base_uniformizer
    kwargs['residue_field'] = W._residue_constant_field
    kwargs['reduce_map'] = W._base_reduce
    kwargs['lift_map'] = W._base_lift
    return StageZeroValuation(self._keypol,self._keyval,**kwargs)

  def decomposition(self, G, collapse=True):
    r"""
    Return a complete list of G-approximant extensions of `self`

    INPUT:

    - ``G`` -- a nonzero polynomial over the base field

    - ``collapse`` -- boolean (default: True); whether to collapse the new stage
      if possible

    OUTPUT:

    - a maximal list of pairwise incomparable InductiveValuation objects W
      extending self such that `self <= W <= V_g`, where `g` is some irreducible
      factor of `G`` and `V_g` is the unique semi-valuation on `K[x]` taking the
      value Infinity at `g`.

    NOTE:

    - If `G` is irreducible and a key polynomial for some stage, then this code
      will use it as a terminal stage. If `G` is reducible, this code will still
      work, but it is not guaranteed to choose factors of `G` as key
      polynomials.

    EXAMPLES::

        sage: p = 5
        sage: V = p_adic_inductive_valuation(p,name='x')

      The prime 5 is inert in Q(sqrt(-2))::

        sage: R.<x> = QQ[]
        sage: VV = V.decomposition(x^2+2)
        sage: VV
        [Stage 1 valuation over 5 with (keypol,keyval) sequence [(x, 0), (x^2 + 2, +Infinity)]]
        sage: VV[0].residue_degree()
        2

      The prime 5 splits in Q(sqrt(-1))::

        sage: V.decomposition(x^2+1)
        [Stage 0 valuation over 5 with (keypol,keyval) sequence [(x + 2, 1)],
        Stage 0 valuation over 5 with (keypol,keyval) sequence [(x - 2, 1)]]

      The prime 5 is ramified in Q(sqrt(5))::

        sage: G = x^2-5  # Newton slope is -1/2
        sage: V = p_adic_inductive_valuation(p,name='x',key_value=1/2)
        sage: VV = V.decomposition(G)
        sage: VV
        [Stage 1 valuation over 5 with (keypol,keyval) sequence [(x, 1/2), (x^2 - 5, +Infinity)]]
        sage: VV[0].ramification_index()
        2

      The resulting valuations are put into canonical form by collapsing::

        sage: p = 2
        sage: R.<x> = QQ[]
        sage: G = x^4 + 4 # Newton slope -1/2
        sage: G.factor() # Reducible!
        (x^2 - 2*x + 2) * (x^2 + 2*x + 2)
        sage: V = p_adic_inductive_valuation(p, key_polynomial=x, key_value=1/2)
        sage: V.decomposition(G,collapse=False)
        [Stage 2 valuation over 2 with (keypol,keyval) sequence [(x, 1/2), (x^2 + 2, 3/2), (x^2 + 2*x + 2, +Infinity)],
        Stage 2 valuation over 2 with (keypol,keyval) sequence [(x, 1/2), (x^2 + 2, 3/2), (x^2 + 2*x + 2, 5/2)]]

        sage: V.decomposition(G,collapse=True)
        [Stage 1 valuation over 2 with (keypol,keyval) sequence [(x, 1/2), (x^2 + 2*x + 2, +Infinity)],
        Stage 1 valuation over 2 with (keypol,keyval) sequence [(x, 1/2), (x^2 + 2*x + 2, 5/2)]]

    """
    VV = [self]
    EE = []
    while len(VV) > 0:
      V = VV.pop()
      AA = V.augmentations(G,collapse)
      for A in AA:
        if A.projection(G)==1:
          EE.append(A)
        else:
          VV.append(A)
    return EE

  ###########################  InductiveValuation  #############################

  def equivalent_polynomials(self, f, g):
    r"""
    Return whether `f` and `g` are equivalent relative to self.

    INPUT:

    - ``f,g`` -- two univariate polynomials over the base field

    OUTPUT:

    - True if `V(f) = V(g) < V(f-g)`, and False otherwise.

    """
    return self.valuation(f-g) > self.valuation(f)


  def is_equiv_divisible_by_key(self, f, key=None):
    r"""
    Return whether `f` is equivalence-divisible by a key polynomial in self.

    INPUT:

    - ``f`` -- a polynomial over the base field

    - ``key`` -- optional polynomial, which must be a key polynomial for self.
      If not given, self.keypol() is used.

    OUTPUT:

    - True if the there exists `q` such that `self(f-q*key) > self(f)`.
      Otherwise return False.

    ALGORITHM:

    - Write `f = q*key + r` with `\deg(r)<\deg(key)`.  By Lemma 4.3 of [MacLane-1],
      `f` is equivalence-divisible by `key` if and only if `V(r) > V(f)`.

    """
    if key is None:
      key = self._keypol
    else:
      key = self._polring(key)
      if not self.is_key(key):
        raise ValueError('"key" is not a key polynomial')
    f = self._polring(f)
    r = f.mod(key)
    return self.valuation(r) > self.valuation(f)


  def effective_degree(self, f):
    r"""
    Return the effective degree of `f` with respect to self.

    INPUT:

    - ``f`` -- a polynomial over the base field

    OUTPUT:

    - The largest index `k` in the `phi`-expansion of `f` such that the `k`-th
      term has the same valuation as `f`, where `phi` is the key polynomial for
      self.

    EXAMPLES::

      sage: p = 2
      sage: R.<x> = QQ[]
      sage: G = x^2 + 2*x + 3 # Newton slope 0
      sage: V0 = p_adic_inductive_valuation(p, key_polynomial=x)
      sage: V1 = V0.augmentations(G).pop()
      sage: V1
      Stage 0 valuation over 2 with (keypol,keyval) sequence [(x + 1, 1/2)]
      sage: f = 2*(x+1)^2 + 4
      sage: V1.effective_degree(f)
      2
      sage: g = (x+1) + 2
      sage: V1.effective_degree(g)
      1
      sage: h = 2*(x+1)^2 + (x+1) + 5
      sage: V1.effective_degree(h)
      0

    """
    if f == 0: return -Infinity
    if self._keyval == Infinity: return 0

    coefs = list(expand_polynomial(f,self._keypol).items())
    coefs.sort()

    if self.is_stage_zero():
      K = self._base_field
      prev = lambda c : self._base_valuation(K(c))
    else:
      prev = self._stages[-1]

    val = Infinity
    eff_deg = -Infinity
    for k, c in coefs:
      new_val = self._keyval*k + prev(c)
      if new_val <= val:
        val = new_val
        eff_deg = k
    return eff_deg

  def is_equiv_unit(self, f):
    r"""
    Return whether `f` is an equivalence unit with respect to self

    INPUT:

    - ``f`` -- a polynomial over the base field

    OUTPUT:

    - True if `f` is an equivalence unit (mod self). Otherwise, return False.

    EXAMPLES::

      sage: p = 2
      sage: R.<x> = QQ[]
      sage: G = x^2 + 2*x + 3 # Newton slope 0
      sage: V0 = p_adic_inductive_valuation(p, key_polynomial=x)
      sage: V1 = V0.augmentations(G).pop()
      sage: V1
      Stage 0 valuation over 2 with (keypol,keyval) sequence [(x + 1, 1/2)]
      sage: f = 2*(x+1)^2 + 4
      sage: V1.is_equiv_unit(f)
      False
      sage: g = (x+1) + 2
      sage: V1.is_equiv_unit(g)
      False
      sage: h = 2*(x+1)^2 + (x+1) + 5
      sage: V1.is_equiv_unit(h)
      True

    """
    return self.effective_degree(f) == 0


  def equiv_inverse(self, f, check=True):
    r"""
    Return the equivalence inverse of f if one exists.

    INPUT:

    - ``f`` -- a polynomial over the base field

    - ``check`` -- boolean (default: True); whether to check if ``f`` is an
      equivalence unit

    OUTPUT:

    - If ``check`` is True, return None if ``f`` is not an equivalence unit, and
      if it is, return its equivalence inverse: ``g`` such that ``f*g \equiv 1``.

    - If ``check`` is False, assume ``f`` is an equivalence unit and return its
      equivalence inverse.

    NOTE:

    - If ``f`` is known to be an equivalence unit, it is more efficient to set
      ``check=False``.  However, when called with ``check=False`` when ``f`` is
      not an equivalence, the method will return a meaningless result.

    EXAMPLES::
      sage: p = 7
      sage: R.<x> = QQ[]
      sage: V0 = p_adic_inductive_valuation(p,'x')
      sage: V0.equiv_inverse(p*x + 3)
      1/3
      sage: print(V0.equiv_inverse(x+3))
      None
      sage: V1 = V0.augment(x^3+x+1, 1)
      sage: print(V1.equiv_inverse(x^3+x+1))
      None
      sage: V1.equiv_inverse(x^3+x^2+3)
      x + 1

    """
    if check:
      if not self.is_equiv_unit(f):
        return None
    phi = self._keypol
    f0 = f.mod(phi)
    _,g,_ = xgcd(f0,phi)
    return g



  ###########################  InductiveValuation  #############################

  def equal_valuation(self, other):
    r"""
    Test equality as valuations.

    To be equal, self.collapse() and other.collapse() must have the same base
    field, and the same uniformizer with the same valuation (so the value groups
    are equal), and the same number of stages; and at each stage the the key
    values must agree, and the key polynomials must be equivalent modulo the
    current stage.

    EXAMPLES::

      sage: p = 2
      sage: R.<x> = QQ[]
      sage: V0 = p_adic_inductive_valuation(p, name='x')
      sage: V1 = V0.augment(x+1,2)
      sage: V = V1.augment(x-3,3)
      sage: W = V0.augment(x-3,3)
      sage: W.equal_valuation(V)
      True

      sage: val_map = lambda t: t.ord(p)/2  # Different value group
      sage: keypol, keyval = x, 0
      sage: U = StageZeroValuation(keypol,keyval,uniformizer=p,valuation=val_map)
      sage: U.equal_valuation(V0)
      False

    FIXME -- Add an example that are equal as valuations but not as inductive
    valuations.

    REFERENCES:

    - Theorem 15.3 of [MacLane-1]

    """
    if getattr(other,'_class_name',None) != self._class_name:
      return False
    V = self.collapse()
    W = other.collapse()
    if V.stage() != W.stage():
      return False
    Vpi = V.base_uniformizer()
    Wpi = W.base_uniformizer()
    if Vpi != Wpi or V.base_valuation(Vpi) != W.base_valuation(Vpi):
      return False
    Vstages = V._stages + [V]
    Wstages = W._stages + [W]
    n = V.stage()
    for i,(Vi,Wi) in enumerate(zip(Vstages,Wstages)):
      phi = Vi._keypol
      psi = Wi._keypol
      if phi.degree() != psi.degree():
        return False
      mu = Vi._keyval
      nu = Wi._keyval
      if mu != nu:
        return False
      if i == 0:
        u = self._base_field(phi-psi) # phi-psi is a constant
        val = V.base_valuation(u)
      else:
        val = V.prev().valuation(phi-psi)
      if val < mu:
        return False
    return True




  def __eq__(self, other):
    r"""
    Test equality as inductive valuations.

    To be equal, self and other must have the same base field and uniformizer
    with the same valuation (so the value groups are equal), and the same
    sequences of key polynomials and key values.

    EXAMPLES::

      sage: p = 2
      sage: R.<x> = QQ[]
      sage: V0 = p_adic_inductive_valuation(p, name='x')
      sage: V1 = V0.augment(x+1,2)
      sage: V = V1.augment(x-3,3)
      sage: W = V0.augment(x-3,3)
      sage: W == V
      True

      sage: val_map = lambda t: t.ord(p)/2  # Different value group
      sage: keypol, keyval = x, 0
      sage: U = StageZeroValuation(keypol,keyval,uniformizer=p,valuation=val_map)
      sage: U == V0
      False

    REFERENCES:

    - Theorem 15.3 of [MacLane-1]

    """
    if getattr(other,'_class_name',None) != self._class_name:
      return False

    V = self
    W = other

    if V.stage() != W.stage():
      return False
    Vpi = V.base_uniformizer()
    Wpi = W.base_uniformizer()
    if Vpi != Wpi or V.base_valuation(Vpi) != W.base_valuation(Vpi):
      return False

    Vstages = V._stages + [V]
    Wstages = W._stages + [W]
    n = V.stage()
    for i,(Vi,Wi) in enumerate(zip(Vstages,Wstages)):
      phi = Vi._keypol
      psi = Wi._keypol
      if phi != psi:
        return False

      mu = Vi._keyval
      nu = Wi._keyval
      if mu != nu:
        return False
    return True

  def __ne__(self, other):
    return not self.__eq__(other)

  # End of InductiveValuation

################################################################################
#############################  StageZeroValuation  #############################
################################################################################


def StageZeroValuation(key_polynomial=None, key_value=None, indval=None, **kwargs):
  r"""
  Construct a stage-0 InductiveValuation object.

  INTPUT:

  - ``key_polynomial`` -- a monic linear polynomial in a univariate polynomial
    ring `K[x]`

  - ``key_value`` -- a rational number

  - ``indval`` -- optional InductiveValuation object from which to get base
    field valuation and other necessary data.

  - Other keyword arguments will be passed to InductiveValuation with
    previous=None. These should be omitted if ``indval`` is given.  Otherwise
    all the arguments to InductiveValuation that are required for stage-0
    valuations must be given here.

  OUTPUT:

  - A stage-0 InductiveValuation object on `K[x]` with given key polynomial and
    key value that extends the given valuation on `K`.

  NOTE:

  - If ``indval`` is not given, this function does nothing but pass its
    arguments to InductiveValuation().  The only advantage to this function over
    calling InductiveValuation() directly is for creating a new stage-0
    valuation based on an existing InductiveValuation object.


  EXAMPLES:

    This function is used to easily create stage-0 valuations::

      sage: p = 5
      sage: R.<x> = QQ[]
      sage: key_pol = x
      sage: key_val = -1
      sage: W = StageZeroValuation(key_pol,key_val,uniformizer=p)
      sage: W(x^2 + 1/5)
      -2

    Given an InductiveValuation, we can create a new stage-0 valuation with the
    same base field valuation::

      sage: V = StageZeroValuation(x+1/25, 1, indval=W)
      sage: V(x+1/25)
      1
      sage: V(x^2 + 1/5)
      -4

    It can also be used to create more complicated stage-0 valuations, say with
    non-normalized value group::

      sage: ordp = lambda t: Infinity if t==0 else QQ(t).ord(p)*3/2
      sage: key_pol, key_val = x, 1/3
      sage: V0 = StageZeroValuation(key_pol,key_val,uniformizer=p,valuation=ordp)
      sage: V0.ramification_index()
      9
      sage: phi = x^9 + p^2
      sage: V0.is_key(phi)
      True
      sage: V0(phi)
      3
      sage: V1 = V0.augment(phi,16/5)
      sage: V1.ramification_index()
      45
      sage: V1.uniformizer().degree()
      13
      sage: V1(V1.uniformizer()) # 2/3 * 45
      1/30

    Let's compare with Sage's internal method for computing totally ramified
    extensions given by an Eisenstein polynomial::

      sage: K = Qp(5)
      sage: S.<y> = K[]
      sage: G = y^3 + 5*y^2 + 5 # roots have valuation 1/3
      sage: L.<t> = K.extension(G)
      sage: Lval = lambda t: t.valuation() / L.ramification_index() # Sage uses normalized valuation
      sage: key_pol, key_val = y, 1/3
      sage: V0 = StageZeroValuation(key_pol,key_val)
      sage: V1 = V0.augmentations(G).pop()
      sage: V1.ramification_index() == L.ramification_index() == 3
      True
      sage: Lval(t + 5)
      1/3
      sage: V1(y + 5)
      1/3

    Let's compare with Sage's internal method for computing unramified extensions::

      sage: K = Qp(5)
      sage: S.<y> = K[]
      sage: G = y^3 + 2*y + 1 # roots have valuation 0
      sage: key_pol,key_val = y, 0
      sage: L.<t> = K.extension(G)
      sage: V0 = StageZeroValuation(key_pol,key_val)
      sage: V1 = V0.augmentations(G).pop()
      sage: V1.residue_degree() == L.residue_field().degree() == 3
      True
      sage: (t + 5).valuation()
      0
      sage: V1(y + 5)
      0
      sage: G(t).valuation()
      20
      sage: V1(G)
      +Infinity

  """
  if indval is not None:
    Z = indval.stage_zero()
    kwargs['uniformizer'] = Z._base_uniformizer
    kwargs['valuation'] = Z._base_valuation
    kwargs['residue_field'] = Z._residue_constant_field
    kwargs['reduce_map'] = Z._base_reduce
    kwargs['lift_map'] = Z._base_lift
    kwargs['extension_constructor'] = Z._extension_constructor
    if key_polynomial is None:
      key_polynomial = Z._polring.gen()
    if key_value is None:
      key_value = 0
  kwargs['previous'] = None
  kwargs['key_polval_list'] = None
  kwargs['key_polynomial'] = key_polynomial
  kwargs['key_value'] = key_value

  return InductiveValuation(**kwargs)


################################################################################
##########################  ExtensionFieldValuation  ###########################
################################################################################


class ExtensionFieldValuation(SageObject):
  r"""
  Class for a valuation on a finite extension of a valued field

  INPUT:

  - ``field`` -- a finite extension field `K[x] / (G(x))`, where `G` is an
    irreducible polynomial over a field `K`

  - ``indval`` -- an InductiveValuation object with associated polynomial ring
    `K[x]`, with the property that its projection relative to `G` has length at
    most 1

  - ``polynomial`` -- optional irreducible polynomial to use for `G`; if not
    specified, it will be set to field.polynomial()

  - ``lift_to_polring`` -- optional function from ``field`` to ``K[x]``,
    representing a section of quotient map `K[x] \to K[x] / (G(x))`.  If not
    specified, the "polynomial" method of field elements will be used.

  - ``ident`` -- optional object of any type, used only in the string
    representation of self.

  NOTE:

  - The hypothesis on ``indval`` ensures that it has a unique (possibly empty)
    sequence of further `G`-approximants, and that its residue field and value
    group are stable under augmentation.

  EXAMPLES::

      sage: R.<x> = QQ[]
      sage: V0 = p_adic_inductive_valuation(5, key_polynomial=x, key_value=0)
      sage: G = x^3 + x^2 + 2*x + 7
      sage: V1 = V0.augmentations(G)[1]
      sage: V1
      Stage 1 valuation over 5 with (keypol,keyval) sequence [(x, 0), (x^2 + 2, 1)]

      sage: L.<t> = NumberField(G)
      sage: V = ExtensionFieldValuation(L,V1)
      sage: V
      Valuation over 5 with (f,e)=(2,1) on Number Field in t with defining polynomial x^3 + x^2 + 2*x + 7

      sage: W = ExtensionFieldValuation(L,V1,ident='ABC')
      sage: W
      Valuation 'ABC' over 5 with (f,e)=(2,1) on Number Field in t with defining polynomial x^3 + x^2 + 2*x + 7

      sage: a = t^2 + t + 1
      sage: abar = V.reduce(a)
      sage: b = V.lift(abar)
      sage: b
      t - 1
      sage: V(b - a) > 0
      True

    The inductive valuation used to define `V` must be augmented in order to
    compute valuations on `L` correctly::

      sage: f = x^2 + 15*x + 12
      sage: V1(f)
      1
      sage: V(f)
      2
      sage: V(f(t))
      2

      sage: V1.reduce(f/5) == 0
      False
      sage: V.reduce(f/5) == 0
      True

  INSTANCE METHODS:

    - __init__
    - __repr__
    - __call__
    - lift_to_polring
    - _augment_indval
    - normalized_valuation
    - field
    - inductive_valuation
    - augmented_inductive_valuations
    - defining_polynomial
    - residue_degree
    - residue_field
    - ramification_index
    - uniformizer
    - base_uniformizer
    - reduce
    - lift
    - local_generator
    - different_valuation
    - discriminant_contribution
    - __eq__
    - __ne__
    - other_valuations
    - ideal_power_generator
    - ideal_generators

  """
  _class_name = 'maclane.ExtensionFieldValuation'

  def __init__(self, field, indval, polynomial=None, lift_to_polring=None, ident=None, decomp_obj=None):
    K = field.base()
    V = indval
    if K is not V.base_field():
      raise ValueError('Base fields of "field" and "indval" do not agree.')
    if polynomial is not None:
      G = polynomial
    else:
      G = extension_field_polynomial(field)
    polring = V.polring()
    G = polring(G)

    self._field = field
    self._indval = V
    self._defining_poly = G
    self._polring = polring
    self._ident = ident
    self._decomp_obj = decomp_obj
    self._eq_attributes = ['defining_poly', 'field', 'indval'] # For equality testing

    # store a uniformizer for self
    unif_poly = V.uniformizer() # polynomial
    t = field.gen()
    self._uniformizer = unif_poly(t)

    # store the lift_to_polring map
    if lift_to_polring is not None:
      self._lift_to_polring = lift_to_polring
    else:
      msg = 'Unable to determine a lift map to polynomial ring.'
      if t in K:
        # Case of a degree-1 extension
        self._lift_to_polring = lambda y: K(y)
      elif hasattr(t,'polynomial'):
        self._lift_to_polring = lambda y: polring(y.polynomial())
        if self._lift_to_polring(t) != polring.gen():
          raise TypeError(msg)
      else:
        raise TypeError(msg)

    # If the last key value is not Infinity, we prepare "augmented" inductive
    # valuations with at least one more stage's worth of information.
    if V.keyval() == Infinity:
      self._augmented_indvals = None
    else:
      self._augmented_indvals = [None, V]
      self._augment_indval()

    self._ideal_power_generator = None # computed in ideal_power_generator()
    self._ideal_generators = None      # computed in ideal_generators()



  def __repr__(self):
    ident = self._ident
    s = 'Valuation'
    if ident is not None:
      s += ' {}'.format(repr(ident))
    p = self.base_uniformizer()
    f = self.residue_degree()
    e = self.ramification_index()
    s += ' over {} with (f,e)=({},{})'.format(p,f,e)
    s += ' on {}'.format(self._field)
    return s

  def __call__(self, elt):
    r"""
    Return the valuation of a field element

    INPUT:

    - ``elt`` -- an element of self._field

    OUTPUT:

    - the valuation of ``elt``, as computed using MacLane's method

    NOTE:

    - In order to determine the correct valuation of the element, the stored
      inductive valuation may need to be augmented one or more stages until the
      valuation of ``elt`` stablilizes.  These augmented valuations are stored
      for subsequent use.

    """
    f = self.lift_to_polring(elt)
    U = self._indval
    if U.keyval() == Infinity:
      return U(f)

    # By Theorem 5.1 of [MacLane-1], we can write f = q*phi + r with
    # phi = V.keypol(). Then V(f) = W(f) if and only if W(r) = W(f).
    W,V = self._augmented_indvals
    q,r = f.quo_rem(V.keypol())
    Wf = W(f)
    Wr = W(r)
    while Wr != Wf:
      Vf = min(Wr, V.keyval() + V(q)) # faster than V(f)
      self._augment_indval()
      W,V = self._augmented_indvals
      q,r = f.quo_rem(V.keypol())
      Wf = Vf
      Wr = W(r)
    return Wf

  ########################  ExtensionFieldValuation  ###########################

  def lift_to_polring(self, elt):
    r"""
    Return a lift of ``elt`` to the polynomial ring `K[x]`
    """
    L = self._field
    elt = L(elt)
    return self._lift_to_polring(elt)

  def _augment_indval(self):
    r"""
    Augment self._augmented_indvals by one stage
    """
    G = self._defining_poly
    U,V = self._augmented_indvals
    A = V.augmentations(G,collapse=True)
    if len(A) != 1:
      raise RuntimeError('Non-unique augmentation for {}:\n{}'.format(repr(V),repr(A)))
    W = A.pop()
    if W.ramification_index() != V.ramification_index():
      raise RuntimeError('Ramification index not stable under augmentation for {}'.format(repr(V)))
    if W.residue_degree() != V.residue_degree():
      raise RuntimeError('Residue degree not stable under augmentation for {}'.format(repr(V)))
    self._augmented_indvals = [V,W]

  def normalized_valuation(self, elt):
    r"""
    Return the valuation of a field element, normalized so a uniformizer has value 1

    INPUT:

    - ``elt`` -- an element of self._field

    OUTPUT:

    - the valuation of ``elt``, as computed using MacLane's method, and
      normalized so that a uniformizer has value 1

    """
    v = self(elt) # non-normalized valuation
    pi_val = self._indval.uniformizer_valuation()
    return ZZ(v / pi_val)

  ########################  ExtensionFieldValuation  ###########################

  def field(self):
    r"""
    Return the field for which self is a valuation
    """
    return self._field

  def inductive_valuation(self):
    r"""
    Return the inductive valuation attached to self
    """
    return self._indval

  def augmented_inductive_valuations(self):
    r"""
    Return the stored augmentations of self.inductive_valuation()
    """
    return self._augmented_indvals

  def defining_polynomial(self):
    r"""
    Return the defining polynomial for self.field()
    """
    return self._defining_poly

  ########################  ExtensionFieldValuation  ###########################

  def residue_degree(self):
    r"""
    Return the residue degree of self over the valuation of the base field
    """
    return self._indval.residue_degree()

  def residue_field(self):
    r"""
    Return the residue field of self
    """
    return self._indval.residue_constant_field()

  def ramification_index(self):
    r"""
    Return the ramification index of self over the valuation of the base field
    """
    return self._indval.ramification_index()

  def uniformizer(self):
    r"""
    Return an element of minimum positive valuation in self._field
    """
    return self._uniformizer

  def base_uniformizer(self):
    r"""
    Return the stored uniformizer for the base field
    """
    return self._indval.base_uniformizer()

  ########################  ExtensionFieldValuation  ###########################

  def reduce(self, elt):
    r"""
    Return the image of ``elt`` in the residue field

    INPUT:

    - ``elt`` -- an element of self._field

    OUTPUT:

    - The element of the residue field of self that is the image of ``elt``
      under the canonical reduction map.

    """
    v = self(elt)  # this augments enough to make W.reduce() do the right thing
    if v < 0:
      raise ValueError('Cannot reduce element of negative valuation.')
    f = self.lift_to_polring(elt)
    V = self._indval
    if V.keyval() == Infinity:
      return V.reduce(f)
    _,W = self._augmented_indvals
    return W.reduce(f).constant_coefficient()

  def lift(self, elt):
    r"""
    Return a lift of ``elt`` in self._field

    INPUT:

    - ``elt`` -- an element of the residue field of self

    OUTPUT:

    - An element of self._field that reduces to ``elt``

    EXAMPLES::

      sage: R.<x> = ZZ[]
      sage: G = x^4 + 6*x^3 - 17*x^2 - 4*x - 17
      sage: VV = p_adic_decomposition(2,G)
      sage: print(VV)
      (0:deg=2)^2
      sage: V = VV.extvals()[0]
      sage: h = V.residue_field().gen()
      sage: h == V.reduce(x)
      True
      sage: V.lift(h) == V.field()(x)
      True

    """
    V = self._indval
    if elt not in V._residue_constant_field:
      raise TypeError('elt cannot be coerced into the residue field')
    pol = V.lift(V._residue_ring(elt))
    return self._field(pol)

  ########################  ExtensionFieldValuation  ###########################

  def local_generator(self):
    r"""
    Return a monogenic generator for the valuation ring over the base

    OUTPUT:

    - An element `y` of self._field such that if `L/K` is the field extension
      and `L_w / K_v` is the corresponding extension of completions, then `y`
      generates the valuation ring of `L_w` as an algebra over `K_v`.

    NOTES:

    - This follows the algorithm in [Serre], Chapter III.6, Proposition 12 and
      its proof.

    """
    f = self.residue_degree()
    if f == 1:
      return self.uniformizer()

    yres = self.residue_field().gen()
    y = self.lift(yres)
    try:
      Rres = yres.minpoly()
    except AttributeError:
      msg = 'Minimal polynomial over base residue field not implemented.'
      raise NotImplementedError(msg)
    if Rres.degree() != f:
      msg = 'Minimal polynomial over base residue field not implemented correctly.'
      raise NotImplementedError(msg)

    polring = self._polring
    V0 = self._indval.stage_zero()
    R = polring([self.lift(c) for c in list(Rres)])
    assert self(R(y)) > 0

    e = self.ramification_index()
    if e*self(R(y)) > 1:
      y += self.uniformizer()
    assert e * self(R(y)) == 1, 'valuation is {}'.format(e*self(R(y)))
    return y

  def different_valuation(self):
    r"""
    Return the normalized local different valuation

    NOTES:

    - In the tame case, this is given by the ramification index - 1. In the wild
      case, we use the formula of [Serre], Chapter III.6, Corollaire 2.

    """
    p = self.residue_field().characteristic()
    e = self.ramification_index()

    # tame case
    if p == 0 or e % p != 0:
      return e - 1

    y = self.local_generator()
    try:
      g = y.minpoly() # FIXME: This is very slow for big examples!
      if g.degree() != self._defining_poly.degree():
        msg = 'Minimal polynomial over base residue field not implemented correctly.'
        raise NotImplementedError(msg)
    except AttributeError:
      msg = 'Minimal polynomial over base residue field not implemented.'
      raise NotImplementedError(msg)

    # Find factor of g over the completion corresponding to self
    v = None
    if g == self._defining_poly:
      v = self
    else:
      zv = self.ideal_power_generator()
      zpol = zv.minpoly()
      Kg = NumberField(g,'t')
      z = zpol.roots(ring=Kg,multiplicities=False)[0].lift() # element of polring
      V0 = self._indval.stage_zero()
      ww = ExtensionFieldDecomposition(g,indval=V0,collapse=True)
      for w in ww.extvals():
        if w(z) == 0: continue
        v = w
    if v is None:
      msg = 'No valuation in decomposition of g = {} corresponds to self.'
      raise RuntimeError(msg.format(g))

    if v._indval.keyval() == Infinity:
      v_ind = v._indval
    else:
      v._augment_indval() # for safety, to get closer to exact factor over completion
      _,v_ind = v._augmented_indvals
    phi = v_ind.keypol()
    return e * self(phi.derivative()(y))

  def discriminant_contribution(self):
    r"""
    Return the contribution of this valuation to the local discriminant
    """
    pi = self.base_uniformizer()
    return pi**(self.residue_degree() * self.different_valuation())

  ########################  ExtensionFieldValuation  ###########################

  def __eq__(self, other):
    if getattr(other,'_class_name',None) != self._class_name:
      return False
    attrs = ['_'+a for a in self._eq_attributes]
    return all(getattr(self,a) == getattr(other,a) for a in attrs)

  def __ne__(self, other):
    return not self.__eq__(other)

  ########################  ExtensionFieldValuation  ###########################


  def other_valuations(self):
    D = self._decomp_obj
    if D is None:
      return []
    return [E.inductive_valuation() for E in D._extvals if E is not self]

  def ideal_power_generator(self):
    r"""
    Return an element with positive valuation, and valution 0 at other extensions.

    OUTPUT:

    - an element f of self.field() satsifying:

      * self(f) > 0

      * V(f) = 0 for V != self in self.other_valuations()

    EFFECT:

    - The element f is stored as self._ideal_power_generator.

    EXAMPLES::

      sage: R.<x> = QQ[]
      sage: G = x^3 + x^2 + 2*x + 7
      sage: E = p_adic_decomposition(7, G, 'z')
      sage: VV = E.extvals()

      sage: for V in VV:
      ....:   print(V.ideal_power_generator())
      z - 21
      z^2 - 27*z - 26

      sage: for V in VV:
      ....:   f = V.ideal_power_generator()
      ....:   print([W.normalized_valuation(f) for W in VV])
      [2, 0]
      [0, 3]

    """
    if self._ideal_power_generator is not None:
      return self._ideal_power_generator

    K = self._field

    if self._indval.keyval() == Infinity:
      V = self._indval
      p = K(self._indval.base_uniformizer())
      self._ideal_power_generator = p
      return p

    other_valuations = self.other_valuations()

    # Find an element f0 with self(f0) > 0  and  W(f0) = 0  for W in other_valuations

    # First try the key polynomial
    phi = self._indval.keypol()
    if all(W(phi)==0 for W in other_valuations):
      g = K(phi)
      self._ideal_power_generator = g
      self._ideal_power_generator_augmentation = None
      return g

    # Try the uniformizer
    u = self.uniformizer()
    ulift = self.lift_to_polring(u)
    if all(W(ulift)==0 for W in other_valuations):
      g = K(u)
      self._ideal_power_generator = g
      self._ideal_power_generator_augmentation = None
      return g

    # Find the first pair of augmentations (V, V') of self, with key polynomials
    # (phi, phi') satisfying W(phi') = W(phi) for all W in other_valuations.

    def test(V):
      for W in other_valuations:
        if W is self: continue
        if W(V.prev().keypol()) != W(V.keypol()): return False
      return True

    G = self._defining_poly

    V = self._indval
    if V.is_stage_zero():
      V, = V.augmentations(G, collapse=False)
    while not test(V):
      V, = V.augmentations(G, collapse=False)
    # Save V for use in computing ideal generators.
    self._ideal_power_generator_augmentation = V
    phi0, phi1 = V.prev().keypol(), V.keypol()
    f = K(phi1)/K(phi0)
    self._ideal_power_generator = f
    return self._ideal_power_generator


  def ideal_generators(self, probabilistic_tries=5):
    r"""
    Return generators for the prime ideal corresponding to self, locally on the base.

    INPUT:

    - ``probabilistic_tries`` -- integer (default: 5); number of iterations of the
      probabilistic method to try before resorting to deterministic method.

    OUTPUT:

    - either one or two elements of self.field() generating the ideal
      corresponding to self in the integral closure of the valuation ring of the
      base field.  Specifically, one of the following:

        - (s0,) where:

          * V(s0) = 0  for V in self.other_valuations()

          * self.normalized_valuation(s0) = 1

        - (s0,s1)  where:

          * V(s0) = 0  for V in self.other_valuations()

          * self(s0) > 0

          * V(s1) >= 0  for V in self.other_valuations()

          * self.normalized_valuation(s1) = 1

    EFFECT:

    - the result is stored in an attribute for later retrieval

    EXAMPLES:

      sage: R.<x> = QQ[]
      sage: G = x^3 + x^2 + 2*x + 7

      sage: E = p_adic_decomposition(7, G, 'z')
      sage: VV = E.extvals()

      sage: K = VV[0].field()
      sage: z = K.gen()
      sage: print([(P.norm().factor(), e) for P,e in K.ideal(7).factor()])
      [(7^2, 1), (7, 1)]

      sage: for V in VV:
      ....:   print(V.ideal_generators())
      (2/199*z^2 + 44/199*z + 1127/199,)
      (3*z^2 + 1,)

      sage: for V in VV:
      ....:   print([[W.normalized_valuation(s) for W in VV] for s in V.ideal_generators()])
      [[1, 0]]
      [[0, 1]]

      sage: for V in VV:
      ....:   gg = [7] + list(V.ideal_generators())
      ....:   fac = K.ideal(gg).factor()
      ....:   print([(P.norm().factor(),e) for P,e in fac])
      [(7, 1), (199, -1)]
      [(7^2, 1)]

    """
    if self._ideal_generators is not None:
      return self._ideal_generators

    K = self._field

    if self._indval.keyval() == Infinity:
      U = self._uniformizer
      self._ideal_generators = (K(U),)
      return self._ideal_generators

    other_valuations = self.other_valuations()

    g = self.ideal_power_generator()

    # Check whether g is a generator
    if self.normalized_valuation(g) == 1:
      self._ideal_generators = (g,)
      return self._ideal_generators

    # METHOD 1:  Try ratio of key polynomials

    G = self._defining_poly
    V = self._ideal_power_generator_augmentation
    if V is None: V = self._indval
    h = None
    while probabilistic_tries > 0 and h is None:
      probabilistic_tries -= 1
      V, = V.augmentations(G, collapse=False)
      phi0, phi1 = V.prev().keypol(), V.keypol()
      if self.normalized_valuation(phi1) - self.normalized_valuation(phi0) > 1: continue
      h = K(phi1)/K(phi0)

    if h is not None:
      self._ideal_generators = (h,)
      return self._ideal_generators

    # METHOD 2: Start with h = self.uniformizer().  For W in other_valuations,
    # if W(h) < 0, multiply h by a suitable power of W.ideal_power_generator

    h = K(self.uniformizer())
    for W in other_valuations:
      m = W(h)
      if m >= 0: continue
      f = W.ideal_power_generator()
      n = -(m//W(f))
      h *= K(f)**n
    self._ideal_generators = (g,h)
    return self._ideal_generators

  # End ExtensionFieldValuation


################################################################################
########################  ExtensionFieldDecomposition  #########################
################################################################################


class ExtensionFieldDecomposition(object):
  r"""
  Class describing the decomposition of a valuation in an extension field.

  INPUT:

  - ``field_or_polynomial`` -- a finite extension of or polynomial over a field K

  - ``collapse`` -- boolean (default: True) whether to collapse redundant stages

  - ``sort_order`` -- string (default: 'resdeg-keycoefs') specifies which sort order to use
    for the valuations.  Allowed values are:

    * "resdeg-keycoefs" -- first by residue degree, then by the concatenated
      list of (keycoefs,keyval) pairs for all stages, starting with stage zero.
      Here ``keycoefs`` is the (little-endian) list of coefficients of the key
      polynomial.

    * "resdeg-keys" -- first by residue degree, then by the list of
      (keypol,keyval) pairs for all stages, starting with stage zero.
      This is the default.

    * "resdeg-keycoef-string" -- first by residue degree, then by a compact
      string representation of the list of (keypol,keyval) pairs, as returned by
      the ``str_compact`` method of InductiveValuation.

  - Remaining keyword arguments are passed to StageZeroValuation to specify a
    stage-zero valuation on K[x].  See docstring for StageZeroValuation and
    InductiveValuation for options.

  EXAMPLES::  # FIXME -- add some examples


  INSTANCE METHODS:

    - __init__
    - __repr__
    - extvals
    - indvals
    - numeric_data
    - base_uniformizer

  """

  def __init__(self, field_or_polynomial, collapse=True, sort_order='resdeg-keycoefs', **stage_zero_kwargs):

    Z = StageZeroValuation(**stage_zero_kwargs)
    self._base_stage_zero = Z
    R = Z.polring()
    K = Z.base_field()

    if isinstance(field_or_polynomial, Field):
      L = field_or_polynomial
      Lpol = extension_field_polynomial(L)
      F = R(Lpol)
    elif isinstance(field_or_polynomial, Polynomial):
      F = R(field_or_polynomial)
      L = K.extension(F,R._names)
    else:
      raise TypeError('first argument must be a field or polynomial')

    self._polynomial = F

    lift = lambda elt: R(elt.list())
    x = R.gen()

    val_dict = {i:Z(c) for i,c in F.dict().items()}
    VV = []
    for v,_ in newton_slopes(val_dict):
      V = StageZeroValuation(x,-v,**stage_zero_kwargs)
      VV.append(V)
    WW = []
    for V in VV:
      if V.keyval() == Infinity:
        # Deal with stage-0 terminating case
        approx_indvals = [V]
      else:
        approx_indvals = V.decomposition(F,collapse=collapse)
      WW += approx_indvals

    # sort if there are more than one
    if len(WW) > 1:
      def sort_key(W):
        p = W.base_uniformizer()
        d = W.residue_degree()
        if sort_order == 'resdeg-keycoefs':
          key_list = [(list(V._keypol),V._keyval) for V in W.stages()]
        elif sort_order == 'resdeg-keys':
          key_list = [(V._keypol,V._keyval) for V in W.stages()]
        elif sort_order == 'resdeg-keycoef-string':
          key_list = W.str_compact()
        else:
          raise ValueError('illegal value for sort_order: {}'.format(sort_order))
        return (p,d,key_list)
      WW.sort(key=sort_key)

    EE = []
    for i,W in enumerate(WW):
      kwargs = {'lift_to_polring':lift, 'ident':i, 'decomp_obj':self}
      EE.append(ExtensionFieldValuation(L,W,**kwargs))
    self._extvals = tuple(EE)

  def __repr__(self):
    ss = []
    for i,E in enumerate(self._extvals):
      s = '({}:deg={})'.format(i,E.residue_degree())
      e = E.ramification_index()
      if e > 1:
        s += '^{}'.format(e)
      ss.append(s)
    return ' * '.join(ss)

  def extvals(self):
    return self._extvals

  def indvals(self):
    return [E.inductive_valuation() for E in self._extvals]

  def numeric_data(self):
    return [(E.residue_degree(),E.ramification_index()) for E in self._extvals]

  def base_uniformizer(self):
    return self._base_stage_zero.base_uniformizer()

################################################################################
################################  Applications  ################################
################################################################################


def p_adic_inductive_valuation(p, name=None, key_polynomial=None, key_value=None,
                               key_polval_list=None, check=False, collapse=True):
  r"""
  Return a stage-0 inductive valuation extending the p-adic valuation on QQ

  INPUT:

  - ``p`` -- a rational prime

  - ``name`` -- optional variable name to use for polynomial ring over K; if not
      specified, use the variable name from the parent of `key_polynomial`

  - ``key_polynomial`` -- optional monic linear polynomial in `QQ[x]`; if not
    specified, use `x`

  - ``key_value`` -- optional rational number or for initial value of
    ``key_polynomial``; if not specified, use 0

  - ``key_polval_list`` -- optinal a list of pairs [(P_0,v_0),...,(P_k,v_k)]
    where P_i is a polynomial and v_i is a rational number, that is the list of
    key-polynials and their values for a inductive valuation.

  - ``check`` -- boolean (default: False); whether to check that the given data
    define a valid inductive valuation

  - ``collapse`` -- boolean (default: True); whether to collapse the resulting
    valuation to the extend possible

  OUTPUT:

  - A stage-0 InductiveValuation extending the p-adic valuation on QQ to `QQ[x]`
    with given ``key_polynomial`` and ``key_value``.

  EXAMPLES::

    sage: p = 5
    sage: R.<x> = QQ[]
    sage: V0 = p_adic_inductive_valuation(p, key_polynomial=x, key_value=1/2)
    sage: V0
    Stage 0 valuation over 5 with (keypol,keyval) sequence [(x, 1/2)]
    sage: V0(x-5)
    1/2
    sage: G = x^2 - 5
    sage: V0.augmentations(G)
    [Stage 1 valuation over 5 with (keypol,keyval) sequence [(x, 1/2), (x^2 - 5, +Infinity)]]
    sage: V1 = V0.augmentations(G).pop()
    sage: V1.ramification_index()
    2

    sage: W0 = p_adic_inductive_valuation(p, key_polynomial=x+1, key_value=1)
    sage: H = x^2 + x + 5
    sage: W0.augmentations(H,collapse=False)
    [Stage 1 valuation over 5 with (keypol,keyval) sequence [(x + 1, 1), (x - 4, 2)]]

    sage: W = p_adic_inductive_valuation(5, key_polval_list=[(x,2/3),(x^6+1250,9/2)])
    sage: F = 1/1220703125*x^23 + 6/1953125*x^17 + 17/3125*x^11 + 18/5*x^5
    sage: W.residual_polynomial(F)
    4*x0_2*x1 + 3*x0_2

  """
  if key_polval_list is None:
    if key_polynomial is None:
      if name is None:
        raise TypeError('Specify "name" if no polynomial is given')
      R = PolynomialRing(QQ,name=name)
      key_polynomial = R.gen()
    if key_value is None:
      key_value = ZZ(0)
    key_polval_list = [(key_polynomial,key_value)]
  else:
    if not all(v is None for v in (key_polynomial, key_value)):
      raise TypeError('Do not use "key_polynomial" or "key_value" when "key_polval_list" given')

  f,_ = key_polval_list[0]
  R = f.parent()
  FFp = GF(p)

  def lift_map(y):
    Ry = R(y)
    return Ry if 2*Ry <= ZZ(p) else Ry - p

  kwargs = {}
  kwargs['key_polval_list'] = key_polval_list
  kwargs['valuation'] = lambda t: t.valuation(p)
  kwargs['uniformizer'] = ZZ(p)
  kwargs['residue_field'] = FFp
  kwargs['reduce_map'] = lambda t: FFp(t)
  kwargs['lift_map'] = lift_map
  kwargs['check'] = check
  kwargs['collapse'] = collapse
  return InductiveValuation(**kwargs)

################################  Applications  ################################

def p_adic_decomposition(p, field_or_polynomial, name=None, collapse=True, **kwargs):
  r"""
  Return a complete list of extensions of the p-adic valuation to QQ[x] / (target_poly)

  INPUT:

  - ``p`` -- a rational prime

  - ``field_or_polynomial`` -- a finite extension K or irreducible polynomial G over QQ

  - ``name`` -- optional name for the image of `x` in `QQ[x] / (G)` if G is given;
    defaults to name of the variable in G; ignored if field_or_polynomial is a field.

  - ``collapse`` -- boolean (default: True) whether to collapse stages when possible

  - Remaining keyword arguments passed to ExtensionFieldComposition


  OUTPUT:

  - an ExtensionFieldDecomposition object

  EXAMPLES::

      sage: p = 5
      sage: R.<y> = QQ[]
      sage: H = y^2 + y + 5 # two roots in Qp
      sage: E = p_adic_decomposition(p,H)
      sage: VV = E.extvals()
      sage: VV
      (Valuation 0 over 5 with (f,e)=(1,1) on Number Field in y with defining polynomial y^2 + y + 5,
       Valuation 1 over 5 with (f,e)=(1,1) on Number Field in y with defining polynomial y^2 + y + 5)
      sage: [V(y+5) for V in VV]
      [0, 2]

    The trivial case of a degree-1 polynomial is also supported::

      sage: G = y - 1
      sage: E = p_adic_decomposition(p,G)
      sage: VV = E.extvals()
      sage: VV
      (Valuation 0 over 5 with (f,e)=(1,1) on Number Field in y with defining polynomial y - 1,)
      sage: [V(y+4) for V in VV]
      [1]

  """
  if isinstance(field_or_polynomial,Polynomial):
    G = field_or_polynomial
    R = G.parent().change_ring(QQ)
    G = R(G)
    if name is None:
      name, = R._names
    L = NumberField(G,name)
  else:
    L = field_or_polynomial
    if name is None:
      name, = L._names
  V = p_adic_inductive_valuation(p,name=name)
  return ExtensionFieldDecomposition(L,indval=V,collapse=collapse,**kwargs)


def number_field_decomposition(K, p, leading_coef_factors=None, **kwargs):
  r"""
  Return the factorization of p in a number field.

  INPUT:

  - ``K`` -- a number field

  - ``p`` -- a prime in ZZ

  - ``leading_coef_factors`` -- optional list of ExtensionFieldValuation objects
    representing all prime ideal factors of the leading coefficient of the
    integral defining polynomial of K.  If not given, it will be computed.

  - Remaining keyword arguments passed to p_adic_decomposition

  OUTPUT:

  - a list of pairs ``(gens, ramind)`` where ``gens`` is a tuple of elements of
    the field ``K`` that generate an integral prime ideal ``P`` over ``p`` and
    ``ramind`` is the multiplicity, such that (p) = prod( (gens)^ramind ).


  NOTE:

  - If leading_coef_factors is given but omits some prime ideal divisors of the
    leading coefficient, then the ideal returned may not be integral at those
    primes.

  EXAMPLES::

      sage: R.<x> = QQ[]
      sage: G = 6561*x^8 + 2916*x^6 + 5589*x^4 + 1170*x^2 + 17263
      sage: K = NumberField(G,'z')
      sage: z = K.gen()
      sage: decomp3 = number_field_decomposition(K, 3)
      sage: print(decomp3)
      [((3, 81*z^6 + 27*z^4 + 3*z^2 + 1/9), 4)]
      sage: fac3 = Factorization([(K.ideal(gg),e) for gg,e in decomp3])
      sage: fac3 == K.ideal(3).factor()
      True
      sage: decomp23 = number_field_decomposition(K, 23)
      sage: print(decomp23)
      [((23, 81*z^4 - 243*z^2 - 243), 1), ((23, 81*z^4 + 486*z^2 - 162), 1)]
      sage: fac23 = Factorization([(K.ideal(gg),e) for gg,e in decomp23])
      sage: fac23 == K.ideal(23).factor()
      True

  """
  name = K.variable_name()
  G = K.defining_polynomial()
  G *= G.denominator()

  LL = leading_coef_factors
  if LL is None:
    c = ZZ(G.leading_coefficient())
    LL = []
    for q in prime_factors(c):
      if q == p: continue
      E = p_adic_decomposition(q,G,name)
      LL.extend(E.extvals())

  E = p_adic_decomposition(p, K, name, **kwargs)
  VV = E.extvals()
  fac = []
  for V in VV:
    gg = list(V.ideal_generators())
    for i,g in enumerate(gg):
      # make integral
      d = g.denominator()
      d /= p**d.valuation(p)
      g *= d
      for L in LL:
        m = L(g)
        if m>=0: continue
        q = L.base_uniformizer()
        g *= q**ceil(-m)
      gg[i] = g
    if p not in gg:
      gg = [p] + gg
    fac.append((tuple(gg),V.ramification_index()))
  return fac


################################  Applications  ################################

def function_field_inductive_valuation(p, name=None, key_polynomial=None, key_value=None,
                                       key_polval_list=None, check=False, collapse=True,
                                       extension_constructor=None):
  r"""
  Return the stage-0 inductive valuation extending the p(x)-adic valuation on K = k(x).

  INPUT:

  - ``p`` -- a prime element of a rational function field `K` in one variable
    over a field `k`.  That is, if `K = k(x)`, then `p` is either `1/x` or an
    irreducible polynomial in `x`.

  - ``name`` -- optional variable name to use for polynomial ring over K; if not
    specified, use the variable name from the parent of `key_polynomial`

  - ``key_polynomial`` -- optional monic linear polynomial in `K[y]`; if not
    specified, use `y`

  - ``key_value`` -- optional rational number for initial value of
    ``key_polynomial``; if not specified, use 0

  - ``key_polval_list`` -- optional list of pairs [(P_0,v_0),...,(P_k,v_k)]
    where P_i is a polynomial and v_i is a rational number, that is the list of
    key-polynials and their values for a inductive valuation.

  - ``check`` -- boolean (default: False); whether to check that ``p`` defines a
    valuatin on `K` and the given polynomials and values define a valid
    inductive valuation

  - ``collapse`` -- boolean (default: True); whether to collapse the resulting
    valuation to the extend possible

  - ``extension_constructor`` -- optional class or constructor function to
    construct finite extensions of k.  If k is a finite field, this defaults
    to the class ExtensionOfFiniteField.  The constructor must take inputs:

    * ``k1`` -- a field that is a finite extension of k (or k itself)

    * ``f`` -- an irreducible polynomial over k1

    * ``proof`` -- optional boolean; whether to test that ``f`` is irreducible

    The object E = extension_constructor(k1,f) must have the following
    methods:

    * ``k1 = E.base()`` -- return the field k1

    * ``k2 = E.field()`` -- return a field k2 with a fixed isomorphism F: k1[x]/(f(x)) -> k2

    * ``xbar = E.gen()`` -- return a root of f in k2. Note that this might
      be different from E.field().gen().

    * ``z = E.reduce(g)`` -- for g in k1[x], return its image z = F(g) = g(xbar) in k2

    * ``g = E.lift(z)`` -- for z in k2, return g in k1[x] with deg(g) < deg(f) and F(g) = z


  OUTPUT:

  - A stage-0 InductiveValuation on the polynomial ring K[y] lifting p

  EXAMPLES::

    sage: K.<x> = FunctionField(GF(5))
    sage: Kpol.<y> = K[]

    sage: p = x^2 + x + 1
    sage: V0 = function_field_inductive_valuation(p,name='y')
    sage: V0
    Stage 0 valuation over x^2 + x + 1 with (keypol,keyval) sequence [(y, 0)]

    sage: p = x
    sage: G = y^2 + x  # roots have valuation 1/2
    sage: keypol, keyval = y, 1/2
    sage: V0 = function_field_inductive_valuation(p, key_polynomial=keypol, key_value=keyval)
    sage: V0.decomposition(G)
    [Stage 1 valuation over x with (keypol,keyval) sequence [(y, 1/2), (y^2 + x, +Infinity)]]

    sage: p = 1/x
    sage: H = y^3 + x^3 + 1/x  # roots have valuation -1
    sage: keypol, keyval = y, -1
    sage: W0 = function_field_inductive_valuation(p, key_polynomial=keypol, key_value=keyval)
    sage: W0.augmentations(H,collapse=False)
    [Stage 1 valuation over 1/x with (keypol,keyval) sequence [(y, -1), (y + x, 3)],
    Stage 1 valuation over 1/x with (keypol,keyval) sequence [(y, -1), (y^2 + 4*x*y + x^2, 2)]]

    sage: V = function_field_inductive_valuation(p, key_polval_list=[(y, -1), (y^2 + 4*x*y + x^2, 2)])
    sage: print(V.str_compact())
    1/x;,0,1:-1;,x^2,4*x,1:2


  """

  # Define the function field and constant field
  try:
    R = p.numerator().parent()
  except AttributeError:
    raise ValueError('"p" must be either an irreducible polynomial or "1/x"')
  k = R.base_ring()
  K = FunctionField(k,repr(R.gen()))
  x = K.gen()
  p = K(p)

  # Get the list of key polynomials and values

  if key_polval_list is None:
    if key_polynomial is None:
      if name is None:
        raise TypeError('Specify "name" if no polynomial is given')
      Kpol = PolynomialRing(K,name)
      key_polynomial = Kpol.gen()
    if key_value is None:
      key_value = ZZ(0)
    key_polval_list = [(key_polynomial,key_value)]
  else:
    if not all(v is None for v in (key_polynomial, key_value)):
      raise TypeError('Do not use "key_polynomial" or "key_value" when "key_polval_list" given')

  if check:
    ff = p.factor()
    if len(ff)>1:
      raise ValueError('Argument does not define a valuation.')
    f,m = ff[0]
    if m not in [1,-1]:
      raise ValueError('Argument does not define a valuation.')
  else:
    if p.is_integral():
      f,m = p, 1
    else:
      f,m = x, -1

  kwargs = {}
  kwargs['key_polval_list'] = key_polval_list
  kwargs['check'] = check
  kwargs['collapse'] = collapse

  # Make sure we have an extension_constructor.
  # InductiveValuation would take care of this,
  # but if deg(p)>1 we will need to use it, so we
  # may as well do it now.
  if extension_constructor is None:
    if not k.is_finite():
      raise ValueError('"exension_constructor" must be given for infinite constant field')
    extension_constructor = ExtensionOfFiniteField

  # place at infinity
  if f==x and m==-1:
    inf_val = lambda Y: Infinity if Y==0 else Y.denominator().degree()-Y.numerator().degree()
    kwargs['valuation'] = inf_val
    kwargs['uniformizer'] = 1/x
    kwargs['residue_field'] = k
    kwargs['reduce_map'] = reduce_at_infinity
    kwargs['lift_map'] = lambda y: K(y)
    kwargs['extension_constructor'] = extension_constructor
    return InductiveValuation(**kwargs)

  # finite place
  np = p.numerator()
  if np.degree()==1:
    resfld = k
    z = np.roots()[0][0]
    liftmap = lambda y: K(y)
  else:
    E = extension_constructor(k,np)
    z = E.gen()
    resfld = E.field()
    liftmap = E.lift
  redmap = lambda Y: Y.numerator()(z)/Y.denominator()(z)
  kwargs['uniformizer'] = p
  kwargs['valuation'] = lambda f: f.valuation(p)
  kwargs['residue_field'] = resfld
  kwargs['reduce_map'] = redmap
  kwargs['lift_map'] = liftmap
  kwargs['extension_constructor'] = extension_constructor
  return InductiveValuation(**kwargs)

################################  Applications  ################################

def function_field_decomposition(p, target_poly, name=None, check=False, collapse=True, **kwargs):
  r"""
  Return a complete list of extensions of a function field valuation on `K` to `K[y] / (target_poly)`

  INPUT:

  - ``p`` -- a prime element of a rational function field `K` in one variable
    over a field `k`.  That is, if `K = k(x)`, then `p` is either `1/x` or an
    irreducible polynomial in `x`.

  - ``target_poly`` -- a polynomial `G` over `K`

  - ``name`` -- optional name for the image of `x` in `QQ[x] / (target_poly)`;
    defaults to name of the variable in ``target_poly``

  - ``check`` -- (default: False) whether to test that ``p`` defines a valuation on `K`

  - ``collapse`` -- boolean (default: True); whether to collapse the resulting
    valuation to the extend possible

  - Remaining keyword arguments passed to ExtensionFieldDecomposition

  OUTPUT:

  - an ExtensionFieldDecomposition object

  EXAMPLES::

      sage: K.<x> = FunctionField(GF(5))
      sage: Kpol.<y> = K[]
      sage: p = 1/x
      sage: G = y^3 + x^3 + 1/x
      sage: E = function_field_decomposition(p,G)
      sage: VV = E.extvals()
      sage: VV
      (Valuation 0 over 1/x with (f,e)=(1,1) on Function field in y defined by y^3 + (x^4 + 1)/x,
       Valuation 1 over 1/x with (f,e)=(2,1) on Function field in y defined by y^3 + (x^4 + 1)/x)
      sage: [V(y+x) for V in VV]
      [3, -1]

    Test decomposition of prime of degree greater than one::

      sage: q = x^3+x+1
      sage: E = function_field_decomposition(q,G)
      sage: VV = E.extvals()
      sage: VV
      (Valuation 0 over x^3 + x + 1 with (f,e)=(1,1) on Function field in y defined by y^3 + (x^4 + 1)/x,
       Valuation 1 over x^3 + x + 1 with (f,e)=(2,1) on Function field in y defined by y^3 + (x^4 + 1)/x)

    The trivial case of a degree-1 polynomial is also supported::

      sage: H = y
      sage: E = function_field_decomposition(p,H)
      sage: VV = E.extvals()
      sage: VV
      (Valuation 0 over 1/x with (f,e)=(1,1) on Function field in y defined by y,)
      sage: [V(y+p) for V in VV]
      [1]

    Test large characteristic::

      sage: p = next_prime(2^65)
      sage: K.<x> = FunctionField(GF(p))
      sage: Kpol.<y> = K[]
      sage: G = y^2 + x^3 + x
      sage: Q = x^2+1
      sage: E = function_field_decomposition(Q,G)

  """
  R = target_poly.parent()
  if name is None:
    name, = R._names
  V = function_field_inductive_valuation(p, name, check=check)
  try:
    return ExtensionFieldDecomposition(target_poly, indval=V, collapse=collapse, **kwargs)
  except NotImplementedError:
    # Hack to work around SAGE refusal to create function field of characteristic > 2^29.
    # The FunctionFieldFactory constructor tests irreducibility, but factoring in Singular fails.
    # The hack is to bypass the factory, and call the function field constructor directly.
    #
    # FIXME -- This should be removed once FunctionField can handle large characteristic.
    #
    FF = sage.rings.function_field.function_field.FunctionField_global
    L = FF(target_poly, name)
    return ExtensionFieldDecomposition(L, indval=V, collapse=collapse, **kwargs)

################################################################################
#######################  CONSTRUCTION AND VISUALIZATION  #######################
################################################################################


def compute_vertex_positions(G, expansion=1):
  ss = G.sinks()
  ss.sort(reverse=True)
  n = len(ss)
  pos = {}
  for x,s in enumerate(ss):
    path = [s]
    v = s
    while G.in_degree(v) > 0:
      v = G.neighbors_in(v)[0]
      path.append(v)
    for y,v in enumerate(reversed(path)):
      pos[v] = (expansion*(n-x),y)
  G.set_pos(pos)

#######################  CONSTRUCTION AND VISUALIZATION  #######################

def sort_indvals(indval_list):
  r"""
  Return indval_list sorted by sequence of (f,e) values.
  """
  fe_vals_list = []
  for V in indval_list:
    fe_vals = []
    for W in V.stages():
      f = W.relative_residue_degree()
      e = W.relative_ramification_index()
      fe_vals.append((f,e))
    fe_vals_list.append(tuple(fe_vals))
  fe_indvals_sorted = sorted(zip(fe_vals_list,indval_list), key=lambda x: x[0])
  _, indvals_sorted = zip(*fe_indvals_sorted)
  return indvals_sorted

#######################  CONSTRUCTION AND VISUALIZATION  #######################

def sort_decomp_graph(G):
  r"""
  Return a decomposition graph the same as G but with leaf nodes sorted as in sort_indvals.

  INPUT:

  - ``G`` -- a decomposition graph; that is, a DiGraph object of the type
    returned by decomp_graph

  OUTPUT:

  - another decomposition graph with the same vertices and edges as G except for
    the follow modifications to vertex labels:

    * leaf node indices (third entry of vertex label) are permuted so that the
      ordering of leaf nodes agrees with the lexicographic ordering of the
      sequences of (f,e) values in the path from a root to the leaf node;

    * vertex indices (first entry of vertex label) are permuted so that the
      ordering of vertices agrees with the depth-first order along the paths
      from root to leaf nodes, taking according to the new ordering of leaf
      nodes;

    * key polynomial indices (second entry of vertex label) of vertices with a
      common parent (or with no parent) are permuted so that the polynomial
      indices increase with vertex index among those siblings.


  EXAMPLES::

    sage: G = DiGraph()
    sage: v0 = (0,0,None,(1,1))
    sage: v1 = (1,0,None,(2,2))
    sage: v2 = (2,0,None,(2,1))
    sage: v3 = (3,0,0,   (2,1))
    sage: v4 = (4,0,1,   (2,1))
    sage: v5 = (5,0,2,   (1,1))
    sage: v6 = (6,0,None,(1,1))
    sage: v7 = (7,0,None,(1,2))
    sage: v8 = (8,0,3,   (2,1))
    sage: v9 = (9,0,4,   (1,1))
    sage: G.add_vertices([v0,v1,v2,v3,v4,v5,v6,v7,v8,v9])
    sage: G.add_edges([(v0,v1),(v1,v2),(v2,v3)])
    sage: G.add_edge(v1,v4)
    sage: G.add_edge(v1,v5)
    sage: G.add_edges([(v6,v7),(v7,v8)])
    sage: G.add_edge(v7,v9)
    sage: H = sort_decomp_graph(G)
    sage: H.edges(labels=False)
    [((0, 0, None, (1, 1)), (1, 0, None, (1, 2))),
     ((1, 0, None, (1, 2)), (2, 0, 0, (1, 1))),
     ((1, 0, None, (1, 2)), (3, 0, 1, (2, 1))),
     ((4, 0, None, (1, 1)), (5, 0, None, (2, 2))),
     ((5, 0, None, (2, 2)), (6, 0, 2, (1, 1))),
     ((5, 0, None, (2, 2)), (7, 0, 3, (2, 1))),
     ((5, 0, None, (2, 2)), (8, 0, None, (2, 1))),
     ((8, 0, None, (2, 1)), (9, 0, 4, (2, 1)))]


  """
  paths = []
  leaves = sorted(G.sinks(),key=lambda v: v[2])
  for V in leaves:
    path = [V]
    W = V
    while G.in_degree(W) > 0:
      W = G.neighbors_in(W)[0]
      path.append(W)
    path.reverse()
    paths.append(path)
  # sort paths by (f,e) sequences
  paths.sort(key=lambda path: tuple(v[-1] for v in path))
  leafind = {path[-1]:i for i,path in enumerate(paths)}
  # determine vertex ordering
  vind = {}
  for path in paths:
    for v in path:
      vind.setdefault(v,len(vind))
  # determine ordering of key polynomials for each parent
  polinds = {}
  I = polinds[0] = {}
  for _,i,_,_ in sorted(G.sources(), key=lambda w: vind[w]):
    I.setdefault(i,len(I))
  for v in G.vertices():
    if G.out_degree(v) == 0: continue
    I = polinds[v] = {}
    for _,i,_,_ in sorted(G.neighbors_out(v), key=lambda w: vind[w]):
      I.setdefault(i,len(I))
  # make the new graph
  H = DiGraph()
  Hvert = {}
  for v in G.vertices():
    if G.in_degree(v) > 0:
      u = G.neighbors_in(v)[0]
    else:
      u = 0
    iv,jv,kv,fev = v
    i = vind[v]
    j = polinds[u][jv]
    k = None if kv is None else leafind[v]
    fe = fev
    w = (i,j,k,fe)
    Hvert[v] = w
    H.add_vertex(w)
  for v,w in G.edges(labels=False):
    H.add_edge(Hvert[v],Hvert[w])

  return H

#######################  CONSTRUCTION AND VISUALIZATION  #######################

def decomp_graph(arg, collapse=False, sort=True, expansion=1, **kwargs):
  r"""
  Return the graph of a list of valuations or of the decomposition of a polynomial.

  INPUT:

  - ``arg`` -- a polynomial or a list of InductiveValuation objects;

  - ``collapse`` -- boolean (default: False); whether to collapse inductive
    valuations before computing graph;

  - ``sort`` -- boolean (default: True); when ``arg`` is a polynomial,
    determines whether to sort the valuations according to sequence of
    (f,e)-values before computing graph;

  - ``expansion`` -- positive integer (default: 1); horizontal expansion factor
    for plotting graph;

  - If arg is a list of valuations, the remaining keyword arguments are ignored.
    If arg is a polynomial, the remaining keyword arguments are passed to
    ExtensionFieldDecomposition to specify the base valuation to decompose, and
    the decomp_graph is computed for the list of valuations in the resulting
    decomposition.

  OUTPUT:

  - a DiGraph object G associated to the list VV of valuations given by ``arg``,
    or by its decomposition if ``arg`` is a polynomial.  The vertices of G
    correspond to the stages of the inductive valuations in VV, with an edge V->W
    whenever V is W.prev().  The actual vertices of G are strings of the form
    ``(i, pol_ind, VV_ind, (f,e))`` where:

    * ``i`` is the index of the vertex, corresponding to an inductive valuation
      V occuring as a stage in one or more entries of VV; Note that ordering of
      the vertices is arbitrary.

    * ``pol_ind`` is the index of V.keypol() in the list of distinct key polynomials
      (in some fixed but arbitrary order) of:

      + all the children of V.prev(), if V is not stage-zero; or

      + all the stage-zero predecessors of entries of VV, if V is stage-zero;

    * ``VV_ind`` is the index of V in VV if the vertex is a leaf node, or None if
      not a leaf node.

    * ``f`` and ``e`` are the relative residue degree and ramfication index of
      V, respectively;

  - a dictionary { indval:vertex, ... } mapping inductive valuations in VV to
    vertices of G

  In addition, the mapping from vertices to inductive valuations is given by the
  dictionary returned by G.get_vertices().


  EXAMPLES::

    sage: QQpol.<x> = QQ[]
    sage: F = x^8 + 4*x^6 + 69*x^4 + 130*x^2 + 17263
    sage: E = p_adic_decomposition(7,F)
    sage: VV = E.indvals()
    sage: for V in VV: print(V.key_polval_list())
    ((x, 0), (x^2 + 1, 1/2), (x^4 + 2*x^2 + 8, 2))
    ((x, 0), (x^2 + 1, 1/2), (x^4 + 2*x^2 + 8, 3))
    sage: G,vals_to_G = decomp_graph(VV)
    sage: G.vertices()
    [(0, 0, None, (1, 1)), (1, 0, None, (2, 2)), (2, 0, 0, (1, 1)), (3, 0, 1, (1, 1))]
    sage: G.edges(labels=False)
    [((0, 0, None, (1, 1)), (1, 0, None, (2, 2))),
     ((1, 0, None, (2, 2)), (2, 0, 0, (1, 1))),
     ((1, 0, None, (2, 2)), (3, 0, 1, (1, 1)))]
    sage: for i,V in enumerate(VV):
    ....:   for j,W in enumerate(V.stages()):
    ....:     print('{} {} {}'.format(i, j, vals_to_G[W]))
    0 0 (0, 0, None, (1, 1))
    0 1 (1, 0, None, (2, 2))
    0 2 (2, 0, 0, (1, 1))
    1 0 (0, 0, None, (1, 1))
    1 1 (1, 0, None, (2, 2))
    1 2 (3, 0, 1, (1, 1))

    sage: F = 224*x^5 + 7504*x^4 - 1072*x^3 - 5360*x^2 + 60032*x - 469
    sage: V = p_adic_inductive_valuation(2,'x')
    sage: G,_ = decomp_graph(F, indval=V)
    sage: G.edges(labels=False)
    [((0, 0, None, (1, 1)), (1, 0, 0, (2, 1))),
     ((0, 0, None, (1, 1)), (2, 1, 1, (3, 1)))]

  """
  if type(arg) in [list,tuple]:
    VV = arg
  else:
    F = arg
    E = ExtensionFieldDecomposition(F, collapse=collapse, **kwargs)
    if sort:
      VV = sort_indvals(E.indvals())
    else:
      VV = E.indvals()
  G = DiGraph()
  vv = {}
  keypols = {}
  for VV_ind,V in enumerate(VV):
    for U in V.stages():
      v = vv.get(U)
      if v is None:
        i = len(G)
        f = U.relative_residue_degree()
        e = U.relative_ramification_index()
        phi = U.keypol()
        if U.prev() in keypols:
          D = keypols[U.prev()]
          phi_ind = D.setdefault(phi,len(D))
        else:
          phi_ind = 0
          keypols[U.prev()] = {phi:phi_ind}
        leaf_ind = VV_ind if U is V else None
        v = (i,phi_ind,leaf_ind,(f,e))
        G.add_vertex(v)
        G.set_vertex(v,U)
        vv[U] = v
      if not U.is_stage_zero():
        v_prev = vv[U.prev()]
        G.add_edge(v_prev,v)

  compute_vertex_positions(G,expansion)

  return G, vv

#######################  CONSTRUCTION AND VISUALIZATION  #######################

def indvals_from_decomp_graph(G, **stage_zero_kwargs):
  r"""
  Return a list of inductive valuations with decomposition graph G.

  INPUT:

  - ``G`` -- a DiGraph object of the type returned by decomp_graph()

  - Remaining keyword arguments are passed to StageZeroValuation to specify a
    stage-zero valuation.  See docstring for StageZeroValuation and
    InductiveValuation for options.

  OUTPUT:

  - ``VV`` a list of inductive valuations such that decomp_graph(VV) is G, and
    ordered by increasing index (first entry) of the corresponding vertices of G.


  EXAMPLES::

      sage: G = DiGraph()
      sage: verts = [(0, 0, None, (1, 1)), (1, 0, None, (2, 2)), (2, 0, 0, (1, 1)), (3, 0, 1, (1, 1))]
      sage: G.add_vertices(verts)
      sage: G.add_edge(((0, 0, None, (1, 1)), (1, 0, None, (2, 2))))
      sage: G.add_edge(((1, 0, None, (2, 2)), (2, 0, 0, (1, 1))))
      sage: G.add_edge(((1, 0, None, (2, 2)), (3, 0, 1, (1, 1))))
      sage: Z = p_adic_inductive_valuation(7,'x')
      sage: VV = indvals_from_decomp_graph(G,indval=Z)
      sage: len(VV)
      2
      sage: for V in VV: print(V.key_polval_list())
      ((x, 0), (x^2 + 3*x - 1, 1/2), (x^4 + 6*x^3 + 7*x^2 + 15*x + 8, 3/2))
      ((x, 0), (x^2 + 3*x - 1, 1/2), (x^4 + 6*x^3 + 7*x^2 + 15*x + 8, 5/2))

      sage: G1,_ = decomp_graph(VV)
      sage: G1 == G
      True

    Make a graph that looks like this, with "v(f,e)" meaning a vertex "v" with
    given values of residue degree (f) and ramification index (e):

      v0(1,1) -> v1(3,2) -> v2(1,2) -> v3(1,1)

      v4(1,3) -> v5(2,1) -> v6(1,1)
        \
         v7(2,1)

      v8(1,3) -> v9(1,1)

    where v4 and v8 have the same key polynomial but different values, and v0 has
    a different key polynomial; and v5 and v7 have different key polynomials ::

      sage: G = DiGraph()
      sage: verts = [(0, 0, None, (1, 1)), (1, 0, None, (3, 2)), (2, 0, None, (1, 2)), (3, 0, 0, (1, 1))]
      sage: verts += [(4, 1, None, (1, 3)), (5, 0, None, (2, 1)), (6, 0, 1, (1, 1))]
      sage: verts += [(7, 1, 2, (2, 1))]
      sage: verts += [(8, 1, None, (1, 3)), (9, 0, 3, (1, 1))]
      sage: G.add_vertices(verts)
      sage: v0, v1, v2, v3, v4, v5, v6, v7, v8, v9 = verts
      sage: G.add_edge(v0,v1)
      sage: G.add_edge(v1,v2)
      sage: G.add_edge(v2,v3)
      sage: G.add_edge(v4,v5)
      sage: G.add_edge(v5,v6)
      sage: G.add_edge(v4,v7)
      sage: G.add_edge(v8,v9)
      sage: Z = p_adic_inductive_valuation(3,'x')
      sage: VV = indvals_from_decomp_graph(G,indval=Z)
      sage: len(VV)
      4
      sage: for V in VV: print(V.key_polval_list()) # random
      ((x, 0), (x^3 + x^2 + x + 2, 1/2), (x^6 + 2*x^5 + 3*x^4 + 6*x^3 + 5*x^2 + 7*x + 7, 5/4), (x^12 + 4*x^11 + 10*x^10 + 24*x^9 + 43*x^8 + 70*x^7 + 108*x^6 + 148*x^5 + 169*x^4 + 172*x^3 + 155*x^2 + 98*x + 49, 11/4))
      ((x + 1, 2/3), (x^6 + 6*x^5 + 15*x^4 + 20*x^3 + 15*x^2 + 6*x + 82, 13/3), (x^6 + 12*x^5 + 45*x^4 + 80*x^3 + 129*x^2 + 144*x + 142, 14/3))
      ((x + 1, 2/3), (x^6 + 6*x^5 + 15*x^4 + 29*x^3 + 42*x^2 + 33*x + 172, 13/3))
      ((x + 1, 1/3), (x^3 + 3*x^2 + 3*x + 7, 4/3))
      sage: G1,_ = decomp_graph(VV)
      sage: G1 == G
      True

  """

  # Make the stage zero valuation with keypol x and keyval 0.  We need to
  # override any extraneous key_polynomial passed in.
  kw = stage_zero_kwargs
  if kw.get('name') is None:
    V = kw.get('indval')
    if V is not None:
      kw['name'] = V.polring()._names[0]
    else:
      pol = stage_zero_kwargs.get('key_polynomial')
      if pol is None:
        raise TypeError('Must give "name" if "indval" and "key_polynomial" not given')
      kw['name'] = pol.parent()._names[0]
  kw['key_polynomial'] = None
  kw['key_value'] = None
  Z = StageZeroValuation(**kw)

  VVgraph = DiGraph()

  all_keypols = set()

  # make the stage-0 valuations
  vv = G.sources()
  je = set()
  for i,j,_,(f,e) in vv:
    if f != 1:
      raise TypeError('Must have f=1 for all root nodes')
    je.add((j,e))
  jj = set(j for j,e in je)
  keypolvals = {}
  respols = set()
  x = Z.polring().gen()
  phi = x
  for j in jj:
    # make a new linear key polynomial
    num_tries = 0     # limit number of tries to prevent infinite loop
    while True:
      if phi not in all_keypols and Z.is_key(phi) and Z.reduce(phi) not in respols:
        respols.add(Z.reduce(phi))
        break
      num_tries += 1
      if num_tries == 10:
        raise RuntimeError('Failed to find {} distinct linear residuals in {}'.format(len(jj),R))
      phi += 1
    all_keypols.add(phi)

    # choose the key values for this polynomial
    ee = set(e for t,e in je if t==j)
    for e in ee:
      num = 0 if e==1 else 1
      for v in vv:
        _,jv,_,(_,ev) = v
        if (jv,ev) != (j,e): continue
        mu = QQ((num,e))
        # make the inductive valuation
        V = Z.augment(phi,mu)
        VVgraph.add_vertex(V)
        VVgraph.set_vertex(V,v)
        num += 1
        while gcd(num,e) > 1:
          num += 1

  # augment stage-0 valuations
  while len(VVgraph) < len(G):
    # pick a leaf node of VVgraph to augment
    ss = VVgraph.sinks()
    for V in ss:
      v = VVgraph.get_vertex(V)
      if G.out_degree(v) > 0: break
    else:
      raise RuntimeError('Something is wrong: ran out of nodes to process!')

    R = V.residue_ring()

    ww = G.neighbors_out(v)

    # make sure all vertices with same pol_ind have the same f
    pol_inds = set(j for _,j,_,(_,_) in ww)
    for j in pol_inds:
      ff = set(f for _,t,_,(f,_) in ww if t==j)
      if len(ff) != 1:
        raise RuntimeError("Invalid decomposition graph: multiple f's for same pol_ind")

    # for each f, make a key polynomial for each pol_ind with that residue degree
    keypols = {}
    ff = sorted(set(f for _,_,_,(f,_) in ww))
    for f in ff:
      pol_inds = set(j for _,j,_,(t,_) in ww if t==f)
      n = len(pol_inds)
      # make n monic irreducible polynomials of degree f in the residue ring
      pols = set()
      num_rpts = 0
      while len(pols) < n and num_rpts < 10: # limit repeats to avoid infinite loop
        psi = R.random_element(f)
        psi /= psi.leading_coefficient()
        if psi in pols:
          num_rpts += 1
          continue
        if not psi.is_irreducible() or psi == R.gen():
          continue
        phi = V.keypol_from_residual(psi)
        if phi in all_keypols:
          num_rpts += 1
          continue
        pols.add(psi)
        all_keypols.add(phi)
      if len(pols) < n:
        raise RuntimeError('Failed to find {} irreducibles of degree {} in {}'.format(n,f,R))
      for j,psi in zip(pol_inds,pols):
        keypols[j] = V.keypol_from_residual(psi)
    # make the list of valuations for pair phi,e
    keypolvals = {}
    for j,phi in keypols.items():
      mu0 = V(phi)
      ee = set(e for _,i,_,(_,e) in ww if i==j)
      for e in ee:
        wwej = [w for w in ww if w[3][1]==e and w[1]==j]
        d = V.ramification_index() * e
        # Need x/d > mu0 and gcd(x,d) = 1
        x = ceil(d*mu0)
        while (x == d*mu0): x += 1
        x -= 1
        for w in wwej:
          x += 1
          while gcd(x,d) != 1: x += 1
          mu = QQ((x,d))
          keypolvals[w] = (phi,mu)
    # make the augmentations
    for w in ww:
      phi,mu = keypolvals[w]
      W = V.augment(phi,mu,collapse=False)
      VVgraph.add_vertex(W)
      VVgraph.set_vertex(W,w)
      VVgraph.add_edge(V,W)

  VV = VVgraph.sinks()
  VV.sort(key=VVgraph.get_vertex)

  return VV

#######################  CONSTRUCTION AND VISUALIZATION  #######################

def polynomial_from_indvals(indval_list, new_vals=None):
  r"""
  Return a polynomial F with decomposition graph similar to that of given list of inductive valuations.

  INPUT:

  - ``indval_list`` -- a list of inductive valuations over a common base field
    valuation v, with the last-stage key polynomials all distinct

  - ``new_vals`` -- optional empty list in which to store modifications of
    ``indval_list`` that have the same graph, but with respect to which the
    returned polynomial will have projection 1.

  OUTPUT:

  - a polynomial F whose decomposition graph, with respect to v, is similar to
    the decomposition graph of indval_list. Exactly what "similar" should mean
    is somewhat unclear.  But if indval_list is the (collapsed, projection 1)
    decomposition of some polynomial F_0, then the decomposition graph of F
    *should* be the same as that of F_0.


  EXAMPLES::

    sage: R.<x> = QQ[]
    sage: F = x^8 + 4*x^6 + 69*x^4 + 130*x^2 + 17263
    sage: E = p_adic_decomposition(7,F)
    sage: VV = [V.augmentations(F)[0] for V in E.indvals()]
    sage: VV
    [Stage 2 valuation over 7 with (keypol,keyval) sequence [(x, 0), (x^2 + 1, 1/2), (x^4 + 2*x^2 + 57, 3)],
     Stage 2 valuation over 7 with (keypol,keyval) sequence [(x, 0), (x^2 + 1, 1/2), (x^4 + 2*x^2 + 351, 4)]]
    sage: F1 = polynomial_from_indvals(VV)
    sage: F1
    x^8 + 4*x^6 + 412*x^4 + 816*x^2 + 137656
    sage: E1 = p_adic_decomposition(7,F1)
    sage: WW = [V.augmentations(F1)[0] for V in E1.indvals()]
    sage: G,_ = decomp_graph(VV); H,_ = decomp_graph(WW)
    sage: G == H
    True

  Start with a polynomial F whose decomposition graph, G, looks like this:

    v0(1,6) -> v1(1,1)

    v2(1,3) -> v3(1,1)

    v4(1,2) -> v5(1,3) -> v6(1,1)

    v7(1,1) -> v8(3,4) -> v9(1,1)

  Compute a new polynomial F1 from the decomposition of F.

    sage: R.<x> = QQ[]
    sage: F = x^27 + 21*x^26 + 197*x^25 + 1203*x^24 + 5634*x^23 + 21736*x^22 + 72053*x^21
    sage: F += 211701*x^20 + 559308*x^19 + 1346328*x^18 + 2983734*x^17 + 6111099*x^16
    sage: F += 11674773*x^15 + 20760954*x^14 + 34512243*x^13 + 53745802*x^12 + 77640030*x^11
    sage: F += 105849947*x^10 + 131660301*x^9 + 154969548*x^8 + 163021213*x^7 + 159347766*x^6
    sage: F += 136828644*x^5 + 102804602*x^4 + 65848373*x^3 + 32799489*x^2 + 11495600*x + 1995376
    sage: Z = p_adic_inductive_valuation(3,name='x')
    sage: E = ExtensionFieldDecomposition(F,indval=Z)
    sage: G,_ = decomp_graph(E.indvals())
    sage: F1 = polynomial_from_indvals(E.indvals())
    sage: E1 = ExtensionFieldDecomposition(F1,indval=Z)
    sage: G1,_ = decomp_graph(E1.indvals())
    sage: G1 == G
    True

  Try the more complicated example.

      v0(1,3) -> v1(1,1)

      v2(1,3) -> v3(2,1)
        \
         v4(2,1)

      v5(1,1) -> v6(3,2) -> v7(1,2) -> v8(1,1)


    where v0 and v2 have the same key polynomial but different values, and v5 has
    a different key polynomial; and v4 and v5 have different key polynomials ::

    sage: G = DiGraph()
    sage: verts = []
    sage: verts += [(0, 0, None, (1, 3)), (1, 0, 0, (1, 1))]
    sage: verts += [(2, 0, None, (1, 3)), (3, 0, 1, (2, 1))]
    sage: verts += [(4, 1, 2, (2, 1))]
    sage: verts += [(5, 0, None, (1, 1)), (6, 0, None, (3, 2)), (7, 0, None, (1, 2)), (8, 0, 3, (1, 1))]
    sage: G.add_vertices(verts)
    sage: v0, v1, v2, v3, v4, v5, v6, v7, v8 = verts
    sage: G.add_edge(v0,v1)
    sage: G.add_edge(v2,v3)
    sage: G.add_edge(v2,v4)
    sage: G.add_edge(v5,v6)
    sage: G.add_edge(v6,v7)
    sage: G.add_edge(v7,v8)
    sage: Z = p_adic_inductive_valuation(3,'x')
    sage: VV = indvals_from_decomp_graph(G,indval=Z)
    sage: F = polynomial_from_indvals(VV)
    sage: G1,_ = decomp_graph(F,sort=False,indval=Z)
    sage: G1 == G
    True

  Try a crazy example.

    v0(1,1) -> v1(2,1) -> v2(1,1) -> v3(1,1) -> v4(1,1) -> v5(1,2) -> v6(1,1)
                           \          \          \
                            \          v8(1,1)    v7(2,1)
                             \
                              v9(2,1) -> v10(1,2) -> v11(1,1)
                                          \
                                           v12(1,1)
  ::

    sage: G = DiGraph()
    sage: verts = []
    sage: verts += [(0,0,None,(1,1))]
    sage: verts += [(1,0,None,(2,1))]
    sage: verts += [(2,0,None,(1,1))]
    sage: verts += [(3,0,None,(1,1))]
    sage: verts += [(4,0,None,(1,1))]
    sage: verts += [(5,0,None,(1,2))]
    sage: verts += [(6,0,0,(1,1))]
    sage: verts += [(7,1,1,(2,1))]      # same key polynomial as v4
    sage: verts += [(8,0,2,(1,1))]
    sage: verts += [(9,1,None,(2,1))]   # same key polynomial as v3
    sage: verts += [(10,0,None,(1,2))]
    sage: verts += [(11,0,3,(1,1))]
    sage: verts += [(12,1,4,(1,1))]     # same key polynomial as v10
    sage: G.add_vertices(verts)
    sage: v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12 = verts
    sage: G.add_edge(v0,v1)
    sage: G.add_edge(v1,v2)
    sage: G.add_edge(v2,v3)
    sage: G.add_edge(v3,v4)
    sage: G.add_edge(v4,v5)
    sage: G.add_edge(v5,v6)
    sage: G.add_edge(v4,v7)
    sage: G.add_edge(v3,v8)
    sage: G.add_edge(v2,v9)
    sage: G.add_edge(v9,v10)
    sage: G.add_edge(v10,v11)
    sage: G.add_edge(v10,v12)
    sage: compute_vertex_positions(G,2)

  We construct the valuations and the graph is the same::

    sage: Z = p_adic_inductive_valuation(3,'x')
    sage: VV = indvals_from_decomp_graph(G,indval=Z)
    sage: GVV,_ = decomp_graph(VV)
    sage: GVV == G
    True

  Construct the polynomial, and check that the modified valuations have expected
  properties::

    sage: WW = []
    sage: F = polynomial_from_indvals(VV, new_vals=WW)
    sage: print(F)               # random
       x^26 - 146*x^25 - 259*x^24 + 825142*x^23 - 35015723*x^22 + 509826803*x^21
       - 543614143*x^20 - 60557210383*x^19 + 574994541490*x^18 - 18215995661*x^17
       - 35463900426221*x^16 + 225410056296662*x^15 + 475904582253472*x^14
       - 9452318859479474*x^13 + 20413137602064254*x^12 + 129094931478251531*x^11
       - 810682555051461634*x^10 - 460086174945181547*x^9 + 7661267621604004187*x^8
       - 17933407623007247704*x^7 - 52671567760825067852*x^6 + 79641613850347429133*x^5
       - 30075808685289928651*x^4 - 165565815089804928383*x^3 + 384156854425326459886*x^2
       - 270803434901693859668*x + 60701450056052224337
    sage: [W.projection(F) for W in WW]
    [1, 1, 1, 1, 1]
    sage: GWW,_ = decomp_graph(WW)
    sage: GWW == GVV
    True

  The graph agrees with the original up to permutation::

    sage: GraphF,_ = decomp_graph(F,indval=Z)  # (GF would be a bad name!)
    sage: GraphF == G
    False
    sage: sort_decomp_graph(GraphF) == sort_decomp_graph(G)
    True

  """
  ff = [V.keypol() for V in indval_list]
  if len(set(ff)) < len(ff):
    raise TypeError('last key polynomials are not distinct')

  # FIXME -- the following definition of Z is bad if V.stage_zero().keyval() < 0
  # FIXME -- for some V in indval_list
  Z = StageZeroValuation(indval=indval_list[0])

  p = Z.uniformizer()
  vp = Z.uniformizer_valuation()

  # Choose e so that Generalized Hensel gives factorizations of F = prod(ff) + p^e
  # equivalent to (ff[i]) * (prod(ff)/ff[i])  for every i.
  v = sum(Z(f) for f in ff)
  fff = prod(ff)
  e = 0
  for f in ff:
    g = fff//f
    h,a,b = xgcd(f,g)
    if h != 1:
      raise RuntimeError('Something is wrong: distinct key polynomials are not relatively prime!')
    t = ceil(max(0,-Z(a),-Z(b))/vp)
    e = max(e, 1 + floor(max(v/vp, 2*t)))
  # Now ensure that the key values in indval_list can be modified to make F have
  # projection 1.  If new_vals is given, we also construct those modified
  # valuations and append them to new_vals.
  for V in indval_list:
    v = V.keyval()
    vv = sum(V(f) for f in ff if f != V.keypol())
    if e < v+vv:
      e = ceil(v+vv)
    if new_vals is None: continue
    w = e - vv
    f = V.keypol()
    if V.is_stage_zero():
      W = StageZeroValuation(f,w,indval=V)
    else:
      W = V.prev().augment(f,w,collapse=False,check=True)
    new_vals.append(W)
  q = p**e
  F = fff + q
  n = 1
  while not F.is_irreducible():
    n += 1
    if Z(n) > 0: n += 1
    F = fff + q*n
  return F

#######################  CONSTRUCTION AND VISUALIZATION  #######################

def polynomial_from_decomp_graph(G, **stage_zero_kwargs):
  r"""
  Return a polynomial whose decomposition graph is G, up to permutation.

  INPUT:

  - ``G`` -- a decomposition graph, such as returned by decomp_graph.

  - remaining keyword arguments required by StageZeroValuation to define a
    stage-zero inductive valuation over some field K

  OUTPUT:

  - a polynomial F over K (the base field of the stage-zero valuation specified
    by the keyword arguments) with decomposition graph G_F satisfying

      sort_decomp_graph(G_F) = sort_decomp_graph(G)

  """
  VV = indvals_from_decomp_graph(G, **stage_zero_kwargs)
  return polynomial_from_indvals(VV)


################################################################################
################################################################################
################################################################################
# End of File
