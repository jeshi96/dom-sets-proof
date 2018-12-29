"""
File: proof_utils.py
Author: Jessica Shi
Date: 4/29/2018

This file contains the functions to construct and check possible edges
in graphs with anchor and linker nodes, attached to a base graph.
While they are heavily tailored to somewhat optimally proving Properties
6 and 22, they can be used for any structure that involves a base graph
and functions to construct anchor nodes adjacent to that base graph.
"""

import copy
import itertools
import networkx as nx
import os
from operator import itemgetter
from networkx.algorithms.isomorphism import is_isomorphic
from sympy.utilities.iterables import multiset_permutations

def find_induced_subgraph(g, isg):
  """
  Checks if graph isg is an induced subgraph of graph g, and
  if so, returns one such subgraph in g.

  Args:
    g (Graph): graph to be checked
    isg (Graph): induced subgraph

  Returns:
    Graph: induced subgraph of g if isg is an induced subgraph of g,
      None otherwise
  """
  nodes = list(g)
  for set_isg in itertools.combinations(nodes, len(isg)):
    if is_isomorphic(nx.subgraph(g, set_isg), isg):
      return nx.subgraph(g, set_isg)
  return None

def find_induced_subgraphs(g, isg_lst):
  """
  Checks if any graph in isg_lst is an induced subgraph of graph g, and
  if so, returns one such subgraph in g.

  Args:
    g (Graph): graph to be checked
    isg_lst (list(Graph)): list of induced subgraphs

  Returns:
    Graph: induced subgraph of g if a graph in isg_lst is an induced subgraph
      of g, None otherwise
  """
  for isg in isg_lst:
    find_isg = find_induced_subgraph(g, isg)
    if find_isg is not None:
      return find_isg
  return None

def is_all_contra(g, nonedges_set, isg_lst):
  """
  Recusively checks all unspecified edges in graph g (where specified
  edges are given by g, and specified non-edges are given by nonedges_set),
  and determines if all of these variations of g have an induced subgraph
  in isg_lst or an induced K_4. If so, returns true, and otherwise,
  returns false.

  Args:
    g (Graph): graph to be checked
    nonedges_set (set(tuple(nodes))): set of specified non-edges in g
    isg_lst (list(Graph)): list of induced subgraphs

  Returns:
    bool: True if all possibilities of g have an induced subgraph in
      isg_lst or an induced K_4, False otherwise
  """
  isg = find_induced_subgraphs(g, isg_lst + [nx.complete_graph(4)])
  if isg is None:
    return False
  is_contra = True
  for nonedge in nx.non_edges(isg):
    if nonedge not in nonedges_set:
      nonedges_set.update([nonedge, nonedge[::-1]])
      g_new = g.copy()
      g_new.add_edge(*nonedge)
      is_contra = is_contra and is_all_contra(g_new, nonedges_set, isg_lst)
      if not is_contra:
        return is_contra
  return is_contra

def is_induced_subgraph(g, isg):
  """
  Checks if graph isg is an induced subgraph of graph g.

  Args:
    g (Graph): graph to be checked
    isg (Graph): induced subgraph

  Returns:
    bool: True if isg is an induced subgraph of g, False
          otherwise
  """
  nodes = list(g)
  for set_isg in itertools.combinations(nodes, len(isg)):
    if is_isomorphic(nx.subgraph(g, set_isg), isg):
      return True
  return False

def is_induced_subgraphs(g, isg_lst):
  """
  Checks if any graphs in isg_lst are induced subgraphs of graph g.

  Args:
    g (Graph): graph to be checked
    isg_lst (list(Graph)): list of induced subgraphs

  Returns:
    bool: True if any graph in isg_lst is an induced subgraph of g,
          False otherwise
  """
  for isg in isg_lst:
    if is_induced_subgraph(g, isg):
      return True
  return False

def is_dominated_vert(g):
  """
  Checks if there is a dominating vertex in graph g, and if so, returns
  true along with a dominating vertex. Otherwise, returns false.

  Args:
    g (Graph): graph to be checked

  Returns:
    (bool, tuple): True along with a pair consisting of a dominating vertex
      and a vertex it dominates, if there is a dominating vertex in g;
      (False, None) otherwise
  """
  nodes = list(g)
  for pair in itertools.combinations(nodes, 2):
    first = set(g.neighbors(pair[0]))
    second = set(g.neighbors(pair[1]))
    if first.issubset(second):
      return (True, pair)
    elif second.issubset(first):
      return (True, pair[::-1])
  return (False, None)

def add_anchors(g, linker, anchor_funcs, rep_idx, unique_idxs):
  """
  Adds to graph g the anchors given in anchor_funcs, each with an edge
  to linker.

  Each added anchor has the form (rep_idx, anchor_idx, unique_idx),
  where anchor_idx is given by anchor_funcs and unique_idx is given by
  unique_idxs (in order).

  Args:
    g (Graph): graph to be modified
    linker (node): node in g (that represents a linker)
    anchor_funcs (list((int, function))):
      anchors to be added; the int represents the index associated with
      the type of anchor, and the function takes as input a node and a graph,
      and adds the node to the graph as an anchor
    rep_idx (int): repetition index
    unique_idxs (list(int)):
      list of unique indices to distinguish between anchors added to the
      same repetition of the same type; must be the same length as
      anchor_funcs

  Returns:
    Graph: graph with the added anchors
    list(node): list of the added anchors
  """
  assert len(anchor_funcs) == len(unique_idxs)
  anchors = []
  for ((anchor_idx, anchor_func), unique_idx) in zip(anchor_funcs,
                                                     unique_idxs):
    anchors.append((rep_idx, anchor_idx, unique_idx))
    g = anchor_func(anchors[-1], g)
    g.add_edge(linker, anchors[-1])
  return (g, anchors)

def handle_failures(g, isg_lst, fail_lst,
                    anchor_set=None,
                    subg=None,
                    anchor_edges_dict=None):
  """
  Checks if graph g has an induced subgraph in isg_lst or an induced K_4. If
  g does have such an induced subgraph, adds g to fail_lst and updates
  anchor_edges_dict with an entry with key anchor_set and value subg if
  anchor_edges_dict is given.

  Args:
    g (Graph): graph to be checked
    isg_lst (list(Graph)): list of induced subgraphs
    fail_lst (list(Graph)): list to add g to if g has one of the specified
      induced subgraphs
    anchor_set (tuple(int)):
      tuple of sorted indices that represent the types of anchors used to
      construct g
    subg (Graph): a subgraph of g that encapsulates the edges
      between the anchors
    anchor_edges_dict (dict(tuple(int),Graph)):
      a dictionary that maps tuples of sorted anchor type indices to
      subgraphs of g that encapsulate the edges between anchors

  Returns:
    None
  """
  if (not is_induced_subgraphs(g,
                               isg_lst + [nx.complete_graph(4)])):
    fail_lst.append(g)
    if anchor_edges_dict is not None:
      if anchor_set not in anchor_edges_dict:
        anchor_edges_dict[anchor_set] = []
      anchor_edges_dict[anchor_set].append(subg)

def check_all_edges(g, subg, isg_lst, subg_fp, anchor_set=None,
                    anchor_edges_dict=None):
  """
  Runs through all possibilities of edges between the vertices in subg of
  graph g, where the possibilities are stored as graphs in graph6 format in
  folder subg_fp.

  Checks if g has an induced subgraph in isg_lst or an induced K_4, and
  updates anchor_edges_dict (if given) if g has such an induced subgraph.

  Args:
    g (Graph): graph to be checked
    subg (list(node)): list of nodes in g to try all
      possible edges of
    isg_lst (list(Graph)): list of induced subgraphs
    subg_fp (str): name of folder containing graphs in graph6 format
      that represent the possible edges in subg (importantly, not up to
      isomorphism; graphs are expected to be labeled); graphs are expected
      to be stored in files labeled "g_[num].txt", where num is the number of
      edges in the graphs in that file
    anchor_set (tuple(int)):
      tuple of sorted indices that represent the types of anchors used to
      construct g
    anchor_edges_dict (dict(tuple(int),Graph)):
      a dictionary that maps tuples of sorted anchor type indices to subgraphs
      of g that encapsulate the edges between anchors

  Return:
    list(Graph): list of graphs that have one of the specified induced
      subgraphs, considering all possible edges among subg
  """
  fail_lst = []
  if len(subg)==0:
    return [g]
  with open(subg_fp + "/g_" + str(len(subg)) + ".txt", "r") as subg_f:
    for subg_g6 in subg_f:
      subg_edges = nx.parse_graph6(subg_g6.rstrip("\n"))
      # Relabel subgraph given by subg_fp to subgraph in g
      g_mod = nx.compose(
        nx.relabel_nodes(subg_edges,
                         dict(zip(sorted(subg_edges.nodes()), subg))), g
      )
      handle_failures(g_mod, isg_lst, fail_lst,
                      anchor_set=anchor_set,
                      subg=g_mod.subgraph(subg),
                      anchor_edges_dict=anchor_edges_dict)
  return fail_lst

def check_base_anchors(base_graph, anchor_func_lst, num_anchors,
                       isg_lst, num_rep, anchor_edges_fp="k3freel",
                       update_dict=True):
  """
  Runs through all possibilities of adding num_anchors anchors from
  anchor_func_lst to the graph base_graph, with num_rep repetitions.

  Considers all possible edges between anchors as given in graph6 format in
  the folder anchor_edges_fp. Checks if any of these graphs has an induced
  subgraph in isg_lst or an induced K_4, and returns the graphs that have no
  such induced subgraphs.

  Also, if update_dict is true, returns a dictionary mapping all combinations
  of anchors to allowable edges between those anchors.

  Args:
    base_graph (Graph): initial graph
    anchor_func_lst (list(function)):
      list of functions that take as input an anchor node and a graph, and
      add that node to the graph as an anchor
    num_anchors (int): number of anchors to be added on each repetition
    isg_lst (list(Graph)): list of induced subgraphs
    num_rep (int): number of repetitions
    anchor_edges_fp (str): folder containing all possible edges between
      anchors in graph6 format
    update_dict (bool): indicates whether to keep a dictionary mapping
      tuples of anchor type indices to allowable edges between those anchors

  Returns:
    (list(Graph,list(node),list(node),tuple(int))):
      list of graphs that have none of the indicated induced subgraphs,
      with corresponding anchors, linkers, and anchor type indices
    (dict(tuple(int),Graph)): dictionary mapping tuples of anchor
      type indices to allowable edges between those anchors; None if
      update_dict is false
  """
  fail_lst = []
  anchor_edges_dict = {} if update_dict else None
  # Consider all permutations of anchors with replacement
  anchor_func_combs = itertools.combinations_with_replacement(
    enumerate(anchor_func_lst), num_anchors
  )
  for anchor_func_comb in anchor_func_combs:
    for anchor_funcs in multiset_permutations(anchor_func_comb):
      anchor_funcs = sorted(list(anchor_funcs), key=itemgetter(0))
      anchor_set = tuple(sorted(zip(*anchor_funcs)[0]))
      g = base_graph.copy()
      anchors = []
      linkers = []
      # In each repetition, add a linker and the corresponding anchors
      for rep_idx in range(num_rep):
        linkers.append((rep_idx, 0))
        g.add_node(linkers[-1])
        (g, new_anchors)  = add_anchors(
          g, linkers[-1], anchor_funcs, rep_idx, range(num_anchors)
        )
        anchors.append(new_anchors)
      # Consider all edges between anchors and check for failure
      fail_lst += zip(
        check_all_edges(g, list(itertools.chain(*anchors)),
                        isg_lst, anchor_edges_fp,
                        anchor_set=anchor_set,
                        anchor_edges_dict=anchor_edges_dict),
        itertools.repeat(anchors),
        itertools.repeat(linkers),
        itertools.repeat(anchor_set)
      )
  fail_lst = fail_lst if update_dict else only_isomorphic(fail_lst)
  return fail_lst, anchor_edges_dict

def check_add_reps(g_spec_lst, anchor_func_lst, num_anchors, isg_lst,
                   rep_idxs, anchor_edges_dict, update_dict=True):
  """
  See check_add_rep.

  Adds multiple repetitions to each graph in g_spec_lst, as in check_add_rep.

  Args:
    g_spec_lst (list(Graph,list(node),list(node),tuple(int))):
      list of graphs with corresponding anchors, linkers, and anchor type
      indices (in order)
    anchor_func_lst (list(function)):
      list of functions that take as input an anchor node and a graph, and
      add that node to the graph as an anchor
    num_anchors (int): number of anchors to be added on each repetition
    isg_lst (list(Graph)): list of induced subgraphs
    rep_idxs (iterable(int)): indices of repetitions to be added
    anchor_edges_dict (dict(tuple(int),Graph)):
      dictionary mapping tuples of anchor type indices to allowable edges
      between those anchors; the number and repetitions of these anchors
      must match those in g_spec_lst
    update_dict (bool): indicates whether to keep an updated
      dictionary mapping tuples of anchor type indices to allowable edges
      between those anchors, considering the new repetitions

  Returns:
    (list(Graph,list(node),list(node),tuple(int))):
      list of graphs that have none of the indicated induced subgraphs,
      with corresponding anchors, linkers, and anchor type indices
    (dict(tuple(int),Graph)): dictionary mapping tuples of anchor
      type indices to allowable edges between those anchors, considering
      the new repetitions; None if update_dict is false
  """
  for rep_idx in rep_idxs:
    g_spec_lst, anchor_edges_dict = check_add_rep(
      g_spec_lst, anchor_func_lst, num_anchors, isg_lst, rep_idx,
      anchor_edges_dict,
      update_dict=True if rep_idx != list(rep_idxs)[-1] else update_dict
    )
  return g_spec_lst, anchor_edges_dict

def check_add_rep(g_spec_lst, anchor_func_lst, num_anchors, isg_lst,
                  rep_idx, anchor_edges_dict, update_dict=True):
  """
  Given a list of graphs with their corresponding anchors and linkers
  (in g_spec_lst), adds another repetition to each graph; that is to
  say, adds another linker to each graph adjacent to anchors of the same
  type as those used to construct previous anchors.

  Considers all possible edges between the newly added anchors and the
  previous anchors, using a dictionary of allowable edges to reduce
  possibilities.

  Returns all graphs that have neither an induced subgraph in isg_lst or an
  induced K_4.

  If update_dict is true, also returns a dictionary mapping all combinations
  of anchors to allowable edges between those anchors, considering the new
  repetition.

  Args:
    g_spec_lst (list(Graph,list(node),list(node),tuple(int))):
      list of graphs with corresponding anchors, linkers, and
      anchor type indices (in order)
    anchor_func_lst (list(function)):
      list of functions that take as input an anchor node and a graph,
      and add that node to the graph as an anchor
    num_anchors (int): number of anchors to be added on each repetition
    isg_lst (list(Graph)): list of induced subgraphs
    rep_idx (int): index of repetition to be added
    anchor_edges_dict (dict(tuple(int),Graph)):
      dictionary mapping tuples of anchor type indices to allowable
      edges between those anchors; the number and repetitions of
      these anchors must match those in g_spec_lst
    update_dict (bool): indicates whether to keep an updated dictionary
      mapping tuples of anchor type indices to allowable edges between
      those anchors, considering the new repetitions

  Returns:
    (list(Graph,list(node),list(node),tuple(int))):
      list of graphs that have none of the indicated induced subgraphs,
      with corresponding anchors, linkers, and anchor type indices
    (dict(tuple(int),Graph)): dictionary mapping tuples of anchor
      type indices to allowable edges between those anchors, considering
      the new repetitions; None if update_dict is false
  """
  fail_lst = []
  anchor_edges_dict_new = {} if update_dict else None
  for (g, anchors, linkers, anchor_set) in g_spec_lst:
    if anchor_set not in anchor_edges_dict:
      continue
    fail_g_lst = []
    anchor_funcs = [(anchor_set_idx, anchor_func_lst[anchor_set_idx])
                    for anchor_set_idx in anchor_set]
    g_anch = g.copy()
    # Add a linker and corresponding anchors for the new repetition
    linkers.append((rep_idx, 0))
    g_anch.add_node(linkers[-1])
    (g_anch, new_anchors)  = add_anchors(
      g_anch, linkers[-1], anchor_funcs, rep_idx, range(num_anchors))
    # Consider all permutations of edges with repetition allowed
    # between all combinations of the newly added anchors and the
    # previous anchors
    edges_combs = itertools.combinations_with_replacement(
      anchor_edges_dict[anchor_set], len(anchors)
    )
    for edges_comb in edges_combs:
      for edges_lst in multiset_permutations(edges_comb):
        g_mod = g_anch.copy()
        # Add specified edges between the newly added anchors and
        # the previous anchors
        for (edges_idx, edges) in enumerate(edges_lst):
          map_anchors = (anchors[0:edges_idx] +
                         anchors[edges_idx+1:] +
                         [new_anchors])
          dict_anchors = [(rep_anch_idx,) + anchor[1:]
                          for (rep_anch_idx,
                               map_anchor) in enumerate(map_anchors)
                          for anchor in map_anchor]
          map_anchors = list(itertools.chain(*map_anchors))
          relabel = nx.relabel_nodes(edges,
                                     dict(zip(dict_anchors, map_anchors)))
          g_mod = nx.compose(relabel,g_mod)
        # Check for failures in the new graph with specified edges
        subg = g_mod.subgraph(list(itertools.chain(*anchors)) + new_anchors)
        handle_failures(g_mod, isg_lst, fail_g_lst, anchor_set=anchor_set,
                        subg=subg, anchor_edges_dict=anchor_edges_dict_new)
    # Consolidate failed graphs with their anchors, linkers, and anchor set
    anchors.append(new_anchors)
    fail_lst += zip(fail_g_lst,
                    itertools.repeat(anchors),
                    itertools.repeat(linkers),
                    itertools.repeat(anchor_set))
  fail_lst = fail_lst if update_dict else only_isomorphic(fail_lst)
  return fail_lst, anchor_edges_dict_new

def powerset(iterable):
  """
  From the Python Standard Library itertools documentation.
  Generates the powerset of iterable.
  """
  s = list(iterable)
  return itertools.chain.from_iterable(itertools.combinations(s, r)
                                       for r in range(len(s)+1))

def check_add_anchors(g_spec_lst, anchor_func_lst, anchor_idxs, isg_lst,
                      num_rep, anchor_edges_dict, update_dict=True):
  """
  See check_add_anchor.

  Adds multiple anchors in each repetition to each graph in g_spec_lst, as
  in check_add_anchor.

  Args:
    g_spec_lst (list(Graph,list(node),list(node),tuple(int))):
      list of graphs with corresponding anchors, linkers, and
      anchor type indices (in order)
    anchor_func_lst (list(function)):
      list of functions that take as input an anchor node and a graph,
      and add that node to the graph as an anchor
    anchor_idxs (iterable(int)): indices of anchors to be added
    isg_lst (list(Graph)): list of induced subgraphs
    num_rep (int): number of repetitions of the graphs in g_spec_lst
    anchor_edges_dict (dict(tuple(int),Graph)):
      dictionary mapping tuples of anchor type indices to allowable
      edges between those anchors; the number and repetitions of
      these anchors must match those in g_spec_lst
    update_dict (bool): indicates whether to keep an updated dictionary
      mapping tuples of anchor type indices to allowable edges
      between those anchors, considering the new anchors

  Returns:
    (list(Graph,list(node),list(node),tuple(int))):
      list of graphs that have none of the indicated induced subgraphs,
      with corresponding anchors, linkers, and anchor type indices
    (dict(tuple(int),Graph)): dictionary mapping tuples of anchor
      type indices to allowable edges between those anchors, considering
      the new anchors; None if update_dict is false
  """
  for anchor_idx in anchor_idxs:
    g_spec_lst, anchor_edges_dict = check_add_anchor(
      g_spec_lst, anchor_func_lst, anchor_idx, isg_lst, num_rep,
      anchor_edges_dict,
      update_dict=(True if anchor_idx != list(anchor_idxs)[-1]
                   else update_dict)
    )
  return g_spec_lst, anchor_edges_dict

def check_add_anchor(g_spec_lst, anchor_func_lst, anchor_idx,
                     isg_lst, num_rep, anchor_edges_dict,
                     update_dict=True):
  """
  Given a list of graphs with their corresponding anchors and linkers
  (in g_spec_lst), adds another anchor to each linker in each graph
  (where anchors are of the same type).

  Considers all possible edges between the newly added anchors and the
  previous anchors, using a dictionary of allowable edges to reduce
  possibilities.

  Returns all graphs that have neither an induced subgraph in isg_lst or an
  induced K_4.

  If update_dict is true, also returns a dictionary mapping all combinations
  of anchors to allowable edges between those anchors, considering the
  newly added anchors.

  Args:
    g_spec_lst (list(Graph,list(node),list(node),tuple(int))):
      list of graphs with corresponding anchors, linkers, and
      anchor type indices (in order)
    anchor_func_lst (list(function)):
      list of functions that take as input an anchor node and a graph,
      and add that node to the graph as an anchor
    anchor_idx (int): index of anchors to be added
    isg_lst (list(Graph)): list of induced subgraphs
    num_rep (int): number of repetitions of the graphs in g_spec_lst
    anchor_edges_dict (dict(tuple(int),Graph)):
      dictionary mapping tuples of anchor type indices to allowable
      edges between those anchors; the number and repetitions of
      these anchors must match those in g_spec_lst
    update_dict (bool): indicates whether to keep an updated dictionary
      mapping tuples of anchor type indices to allowable edges between
      those anchors, considering the new anchors

  Returns:
    (list(Graph,list(node),list(node),tuple(int))):
      list of graphs that have none of the indicated induced subgraphs,
      with corresponding anchors, linkers, and anchor type indices
    (dict(tuple(int),Graph)): dictionary mapping tuples of anchor
      type indices to allowable edges between those anchors, considering
      the new anchors; None if update_dict is false
  """
  anchor_edges_dict_new = {} if update_dict else None
  fail_lst = []
  for (g, anchors, linkers, anchor_set) in g_spec_lst:
    # Consider all possible anchor types to add
    for (anchor_func_idx, anchor_func) in enumerate(anchor_func_lst):
      g_anch = g.copy()
      new_anchors = []
      # Add a new anchor to each repetition
      for rep_idx in range(num_rep):
        (g_anch, new_anchors_temp) = add_anchors(
          g_anch, (rep_idx,0), [(anchor_func_idx, anchor_func)], rep_idx,
          [anchor_idx]
        )
        new_anchors += new_anchors_temp
      # Consider all possible edges between the new anchors
      # and the previous anchors
      edges_comb = [[] for _ in range(len(anchor_set))]
      to_cont = False
      for anchor_set_idx in range(len(anchor_set)):
        anchor_subset = tuple(sorted(anchor_set[:anchor_set_idx] +
                                     anchor_set[anchor_set_idx+1:] +
                                     (anchor_func_idx,)))
        if anchor_subset in anchor_edges_dict:
          edges_comb[anchor_set_idx] = anchor_edges_dict[anchor_subset]
        else:
          to_cont = True
          break
      if to_cont:
        continue
      # Iterate through all possible edges between the new anchors
      # and the previous anchors
      fail_g_lst = []
      for edges_lst in itertools.product(*edges_comb):
        g_mod = g_anch.copy()
        # Add the specified edges
        for (edges_idx, edges) in enumerate(edges_lst):
          anchors_subset = [[anchor for anchor in anchor_lst
                             if anchor[2] != edges_idx]
                            for anchor_lst in anchors]
          map_anchors = (list(itertools.chain(*anchors_subset)) +
                         [(rep_idx, anchor_func_idx, anchor_idx)
                          for rep_idx in range(num_rep)])
          sort_anchors = zip(*sorted(
            anchors_subset[0] + [(0, anchor_func_idx, anchor_idx)],
            key=itemgetter(1)
          ))[2]
          dict_anchor_idx = dict(zip(sort_anchors, range(len(anchor_set))))
          dict_anchors = [anchor[0:2] + (dict_anchor_idx[anchor[2]],)
                          for anchor in map_anchors]
          relabel = nx.relabel_nodes(edges,
                                     dict(zip(dict_anchors, map_anchors)))
          g_mod = nx.compose(relabel, g_mod)
        # Check for failures in the new graph with the specified edges
        subg = g_mod.subgraph(list(itertools.chain(*anchors))+
                              new_anchors)
        handle_failures(g_mod, isg_lst, fail_g_lst,
                        anchor_set=tuple(sorted(anchor_set +
                                                (anchor_func_idx,))),
                        subg=subg, anchor_edges_dict=anchor_edges_dict_new)
      # Consolidate failed graphs with their anchors, linkers, and anchor set
      new_anchors = copy.deepcopy(anchors)
      for (anchor_lst_idx, anchor_lst) in enumerate(new_anchors):
        anchor_lst.append((anchor_lst_idx, anchor_func_idx, anchor_idx))
      fail_lst += zip(fail_g_lst,
                      itertools.repeat(new_anchors),
                      itertools.repeat(linkers),
                      itertools.repeat(tuple(sorted(anchor_set +
                                                    (anchor_func_idx,)))))
  fail_lst = fail_lst if update_dict else only_isomorphic(fail_lst)
  return fail_lst, anchor_edges_dict_new

def check_add_linkers(g_spec_lst, anchor_func_lst, isg_lst, rep_idxs,
                      update_dict=True):
  """
  Given a list of graphs with their corresponding anchors and linkers
  (in g_spec_lst), adds a new linker adjacent to each linker corresponding
  to the repetition indices in rep_idxs.

  Considers all possible edges between the newly added linkers and the anchors.

  Returns all graphs that have neither an induced subgraph in isg_lst or K_4
  as an induced subgraph.

  If update_dict is true, also returns a dictionary mapping all combinations
  of anchors to allowable edges between those anchors, considering the new
  linkers.

  Args:
    g_spec_lst (list(Graph,list(node),list(node),tuple(int))):
      list of graphs with corresponding anchors, linkers, and anchor type
      indices (in order)
    anchor_func_lst (list(function)):
      list of functions that take as input an anchor node and a graph,
      and add that node to the graph as an anchor
    isg_lst (list(Graph)): list of induced subgraphs
    rep_idxs (int): indices of repetitions to which the new linkers are added
    update_dict (bool): indicates whether to keep an updated dictionary
      mapping tuples of anchor type indices to allowable edges between those
      anchors, considering the new linkers

  Returns:
    (list(Graph,list(node),list(node),tuple(int))):
      list of graphs that have none of the indicated induced subgraphs,
      with corresponding anchors, linkers, and anchor type indices
    (dict(tuple(int),Graph)): dictionary mapping tuples of anchor
      type indices to allowable edges between those anchors, considering
      the new linkers; None if update_dict is false
  """
  for rep_idx in rep_idxs:
    anchor_edges_dict_new = {} if update_dict else None
    fail_lst = []
    for (g, anchors, linkers, anchor_set) in g_spec_lst:
      # Add a new linker adjacent to every linker corresponding to
      # repetition rep_idx
      g_lnk = g.copy()
      new_linker = (rep_idx, 1)
      linkers.append(new_linker)
      g_lnk.add_node(new_linker)
      g_lnk.add_edge(new_linker, (rep_idx, 0))
      # Consider all combinations of edges between the new linker and
      # the anchors
      edges_comb = itertools.product([new_linker],
                                     list(itertools.chain(*anchors)))
      fail_g_lst = []
      for edges_lst in powerset(edges_comb):
        # Add the specified edges
        g_mod = g_lnk.copy()
        g_mod.add_edges_from(list(edges_lst))
        subg = g_mod.subgraph(list(itertools.chain(*anchors)))
        # Check for failures in the new graph with the specified edges
        handle_failures(
          g_mod, isg_lst, fail_g_lst, anchor_set=anchor_set, subg=subg,
          anchor_edges_dict=(
            anchor_edges_dict_new
            if rep_idx == list(rep_idxs)[-1]
            else None
          )
        )
      # Consolidate failed graphs with their anchors, linkers, and anchor set
      fail_lst += zip(fail_g_lst,
                      itertools.repeat(anchors),
                      itertools.repeat(linkers),
                      itertools.repeat(anchor_set))
    g_spec_lst = fail_lst if update_dict else only_isomorphic(fail_lst)
  return g_spec_lst, anchor_edges_dict_new

def only_isomorphic(graphs):
  """
  Prunes graphs such that all graphs in graphs are pairwise non-isomorphic.

  Args:
    graphs (list(Graph) or list(tuple(Graph,...)):
      list of graphs to be pruned; may also be in the format of
      tuples in which the first entry is a graph and the remaining entries
      contain other info

  Returns:
    list(Graph) or list(tuple(Graph,...)):
      list of pairwise non-isomorphic graphs, where the format matches that
      of the input
  """
  iso_lst = []
  for i in range(len(graphs)):
    keep = True
    for g in graphs[i+1:]:
      if ((type(g) is tuple and nx.is_isomorphic(graphs[i][0], g[0])) or
          (type(g) is not tuple and nx.is_isomorphic(graphs[i], g))):
        keep = False
        break
    if keep:
      iso_lst.append(graphs[i])
  return iso_lst
