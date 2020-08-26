# MacLane
Sage code for MacLane valuations and applications

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
