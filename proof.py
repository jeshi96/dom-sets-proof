"""
File: proof.py
Author: Jessica Shi
Date: 4/29/2018

This file contains the constructions to prove Properties 6 and 22, assuming
Property 8. The main proofs are found in prop_6() and prop_22() respectively.
"""

import proof_utils as utils
import functools
import itertools
import networkx as nx
from sympy.utilities.iterables import multiset_permutations

def add_clone(i, node, g):
  """
  Adds a clone node to graph g, with edges to ((i-1)%5) and ((i+1)%5).

  Args:
    i (int): index of clone to be added
    node (node): clone to be added
    g (Graph): graph

  Returns:
    Graph: graph with added clone
  """
  g.add_node(node, type=("clone", i))
  g.add_edges_from([(node, (i-1) % 5), (node, (i+1) % 5)])
  return g

def add_leaf(i, node, g):
  """
  Adds a leaf node to graph g, with an edge to (i % 5).

  Args:
    i (int): index of leaf to be added
    node (node): leaf to be added
    g (Graph): graph

  Returns:
    Graph: graph with added leaf
  """
  g.add_node(node, type=("leaf", i))
  g.add_edges_from([(node, i % 5)])
  return g

def add_linker(node, g):
  """
  Adds a linker node to graph g, with no edges.

  Args:
    node (node): linker to be added
    g (Graph): graph

  Returns:
    Graph: graph with added linker
  """
  g.add_node(node, type="linker")
  return g

def set_up_nonedges(num_rep, list_clones, list_linkers, list_d_clones,
                    list_d_linkers):
  """
  Sets up the non-edges for the proof of Property 22, in prop_22. Uses
  Property 8 to define certain non-edges.

  Args:
    num_rep (int): number of repetitions
    list_clones (list(nodes)): list of a^r, b^r clones
    list_linkers (list(nodes)): list of e^r linkers in E'
    list_d_clones (list(nodes)): list of d_a^r, d_b^r
    list_d_linkers (list(nodes)): list of d_e^r

  Returns:
    set(tuple(nodes)): set of specified non-edges
  """
  # Set up non-edges
  # This follows from the definitions of d_a^r, d_b^r
  nonedges_set = set([(("da",i),("b",i)) for i in range(num_rep)] +
                     [(("db",i),("a",i)) for i in range(num_rep)])

  # This is because edges to C are well-defined
  nonedges_set.update(itertools.product(list_d_clones, range(5)))
  nonedges_set.update(itertools.product(list_d_linkers, range(5)))
  nonedges_set.update(itertools.product(list_linkers, range(5)))
  nonedges_set.update(itertools.product(list_clones, range(5)))

  # This is because all vertices in E' have pairwise disjoint neighborhoods
  nonedges_set.update(itertools.product(list_d_linkers, list_linkers))
  nonedges_set.update(itertools.product(list_clones, list_linkers))

  # This is by construction of E'
  nonedges_set.update(itertools.combinations(list_linkers, 2))

  # This is by definition of C
  nonedges_set.update(itertools.combinations(range(5), 2))

  # This is because G is triangle-free
  nonedges_set.update(itertools.combinations(list_clones, 2))

  # This follows from Property 8
  nonedges_set.update(itertools.product(list_d_clones, list_linkers))

  # Add the opposite ordering of tuples to the set, for ease of lookup
  nonedges_set_opp = [nonedge[::-1] for nonedge in nonedges_set]
  nonedges_set.update(nonedges_set_opp)
  
  return nonedges_set

def prop_22():
  """
  Proves Property 22, given Property 8. Tests (in an optimized, recursive
  manner) all possible edges given that the linkers in E' are adjacent
  to two anchors of the same type and index and that there exist
  d_a^r, d_b^r, and d_e^r for each repetition r to fix dominating vertices.
  Shows that in all scenarios, there exists either an induced triangle
  or an induced P_7, so as such, it is not possible for the linkers in E'
  to be adjacent to two anchors of the same type and index.
  """
  isg_lst = [nx.complete_graph(3), nx.path_graph(7)]
  g_base = nx.cycle_graph(5)
  num_rep = 3

  # Set up clones, linkers, and vertices relating to dominating vertices
  list_clones = ([("a",i) for i in range(num_rep)] +
                 [("b",i) for i in range(num_rep)])
  list_linkers = [("e",i) for i in range(num_rep)]
  list_d_clones = ([("da",i) for i in range(num_rep)] +
              [("db",i) for i in range(num_rep)])
  list_d_linkers = [("de",i) for i in range(num_rep)]

  g_base.add_nodes_from(list_linkers)

  nonedges_set = set_up_nonedges(num_rep, list_clones, list_linkers,
                                 list_d_clones, list_d_linkers)

  # Consider all possibilities for anchors, d_a^r, d_b^r, and d_e^r
  anchor_types = [functools.partial(add_clone, 0),
                 functools.partial(add_leaf, 0)]

  d_func_lst_c = [add_linker]
  d_func_lst_l = [add_linker]
  for i in range(5):
    if i != 0:
      d_func_lst_c.append(functools.partial(add_clone, i))
      d_func_lst_l.append(functools.partial(add_leaf, i))
    d_func_lst_c.append(functools.partial(add_leaf, i))
    d_func_lst_l.append(functools.partial(add_clone, i))

  for anchor_func, d_func_lst in zip(anchor_types,
                                     [d_func_lst_c, d_func_lst_l]):
    for d_func_tup in itertools.combinations_with_replacement(d_func_lst, 3):
      for (d_a_func, d_b_func, d_e_func) in multiset_permutations(d_func_tup):
        g = g_base.copy()
        # Add anchors, d_a^r, d_b^r, d_e^r
        for i in range(num_rep):
          g = anchor_func(("a",i), g)
          g = anchor_func(("b",i), g)
          g = d_a_func(("da",i), g)
          g = d_b_func(("db",i), g)
          g = d_e_func(("de",i), g)
          g.add_edges_from([(("a",i),("e",i)),(("b",i),("e",i)),
                            (("a",i),("da",i)), (("b",i),("db",i))])
        g.add_edges_from(zip(list_d_linkers, list_linkers))
        # Check all possibilities of unspecified edges, and print
        # any graphs that produce a graph without a triangle or a P7
        is_all_contra = utils.is_all_contra(g, nonedges_set, isg_lst)
        if not is_all_contra:
          print g.nodes(data="type")

def prop_6():
  """
  Proves Property 6. Tests all combinations of the types and indices of
  anchors a^r and b^r (and d^r or a second linker) adjacent to the linkers
  in E', and shows that the only allowable combinations are those in which
  at least two of {a^r, b^r, d^r} have the same type and index.
  
  Note that this proof is incomplete in that in the case where e^r is
  adjacent to three anchors, there are two situations in which all of
  {a^r, b^r, d^r} have different types and indices. These situations
  disappear if another repetition is added (only 2 repetitions are tested
  for this case); however, this does significantly increase the runtime.
  """
  anchor_func_lst = []
  for i in range(5):
    anchor_func_lst.append(functools.partial(add_clone, i))
    anchor_func_lst.append(functools.partial(add_leaf, i))
  base_g = nx.cycle_graph(5)
  isg_lst = [nx.complete_graph(3), nx.path_graph(7)]

  # Generate and check initial graph, with 2 repetitions and 2 anchors
  # adjacent to each linker
  fail_lst, anchor_edges_dict = utils.check_base_anchors(
    base_g, anchor_func_lst, 2, isg_lst, 2
  )

  # Consider the case where 3 anchors are adjacent to each linker
  s_fail_lst = utils.check_add_anchor(
    fail_lst, anchor_func_lst, 2, isg_lst, 2, anchor_edges_dict,
    update_dict=False
  )[0]

  # Output the cases in which it is possible for each linker in E'
  # to be attached to 3 anchors
  print "Case: 3 anchors: "
  for g in utils.only_isomorphic(s_fail_lst):
    print (g[0].nodes(data="type"))
    print (g[0].edges())

  # Consider the case where each linker is adjacent to another linker
  fail_lst, anchor_edges_dict = utils.check_add_linkers(
    fail_lst, anchor_func_lst, isg_lst, range(2)
  )

  # Add another repetition, and the linkers for that repetition
  fail_lst = utils.check_add_rep(
    utils.only_isomorphic(fail_lst), anchor_func_lst, 2, isg_lst,
    2, anchor_edges_dict, update_dict=False
  )[0]
  fail_lst = utils.check_add_linkers(
    utils.only_isomorphic(fail_lst), anchor_func_lst, isg_lst,
    [2], update_dict=False)[0]

  # Output the cases in which it is possible for each linker in E'
  # to be attached to 2 anchors and an additional linker
  print "Case: 2 anchors, 1 linker: "
  for g in utils.only_isomorphic(fail_lst):
    print (g[0].nodes(data="type"))
    print (g[0].edges())
