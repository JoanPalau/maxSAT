#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse
import collections
import itertools
import sys

import msat_runner
import wcnf


# Graph class
###############################################################################

class Graph(object):
    """This class represents an undirected graph. The graph nodes are
    labeled 1, ..., n, where n is the number of nodes, and the edges are
    stored as pairs of nodes.
    """

    def __init__(self, file_path=""):
        self.edges = []
        self.n_nodes = 0

        if file_path:
            self.read_file(file_path)

    def read_file(self, file_path):
        """Loads a graph from the given file.

        :param file_path: Path to the file that contains a graph definition.
        """
        with open(file_path, 'r') as stream:
            self.read_stream(stream)

    def read_stream(self, stream):
        """Loads a graph from the given stream.

        :param stream: A data stream from which read the graph definition.
        """
        n_edges = -1
        edges = set()

        reader = (l for l in (ll.strip() for ll in stream) if l)
        for line in reader:
            l = line.split()
            if l[0] == 'p':
                self.n_nodes = int(l[2])
                n_edges = int(l[3])
            elif l[0] == 'c':
                pass  # Ignore comments
            else:
                edges.add(frozenset([int(l[1]), int(l[2])]))

        self.edges = tuple(tuple(x) for x in edges)
        if n_edges != len(edges):
            print("Warning incorrect number of edges")

    def min_vertex_cover(self, solver, n_solutions):
        """Computes the minimum vertex cover of the graph.

        :param solver: Path to a MaxSAT solver.
        :param n_solutions: Number of solutions to compute, 0 or negative
            means all posible solutions.
        :return: A list of solutions, each solution is a list of nodes.
        """
        formula = wcnf.WCNFFormula()
        n_vars = [formula.new_var() for _ in range(self.n_nodes)]

        # soft: including a vertex in the cover has a cost of 1
        for i in range(self.n_nodes):
            formula.add_clause([-n_vars[i]], 1)  # clause weight = 1

        # hard: all edges must be covered
        for n1, n2 in self.edges:
            v1, v2 = n_vars[n1-1], n_vars[n2-1]
            formula.add_clause([v1, v2], wcnf.TOP_WEIGHT)

        return compute_all_solutions(self, formula, solver, n_solutions)

    def min_dominating_set(self, solver, n_solutions):
        """Computes the minimum dominating set of the graph.

        :param solver: Path to a MaxSAT solver.
        :param n_solutions: Number of solutions to compute, 0 or negative
            means all posible solutions.
        :return: A list of solutions, each solution is a list of nodes.
        """

        formula = wcnf.WCNFFormula()
        n_vars = [formula.new_var() for _ in range(self.n_nodes)]

        # soft: including a vertex in the dominating set has a cost of 1
        for i in range(self.n_nodes):
            formula.add_clause([-n_vars[i]], 1)  # clause weight = 1

        neighbours = {}

        # We create a dictionary that for each node
        # has a list of him and his neighbours

        for i in range(self.n_nodes):
            neighbours[n_vars[i-1]] = [n_vars[i-1]]

        for n1, n2 in self.edges:
            v1, v2 = n_vars[n1 - 1], n_vars[n2 - 1]

            neighbours = add_neighbour(neighbours, v1, v2)

            neighbours = add_neighbour(neighbours, v2, v1)

            # hard: each vertex needs to either be in the DSet
            # or have at least one of their neighbours in the DSet

            for key in neighbours:
                literals = neighbours[key]
                formula.add_at_least_one(literals)  # [:-1]

        return compute_all_solutions(self, formula, solver, n_solutions, basic_compute)

    def max_independent_set(self, solver, n_solutions):
        """Computes the maximum independent set of the graph.

        :param solver: Path to a MaxSAT solver.
        :param n_solutions: Number of solutions to compute, 0 or negative
            means all posible solutions.
        :return: A list of solutions, each solution is a list of nodes.
        """
        formula = wcnf.WCNFFormula()
        n_vars = [formula.new_var() for _ in range(self.n_nodes)]

        # soft: not including a vertex in the independent set has a cost of 1
        for i in range(self.n_nodes):
            formula.add_clause([n_vars[i]], 1)  # clause weight = 1

        # hard: each vertex needs if in the independent set
        # not have any of their neighbours in the independent Set
        for n1, n2 in self.edges:
            v1, v2 = n_vars[n1 - 1], n_vars[n2 - 1]
            formula.add_clause([-v1, -v2], wcnf.TOP_WEIGHT)

        return compute_all_solutions(self, formula, solver, n_solutions, basic_compute)

    def min_graph_coloring(self, solver, n_solutions):
        """Computes the sets of nodes that can be painted using the
        same color, such that two adjacent nodes do not use the same
        color.

        :param solver: Path to a MaxSAT solver.
        :param n_solutions: Number of solutions to compute, 0 or negative
            means all posible solutions.
        :return: A list of solutions, each solution is a list of lists of
            nodes, where all the nodes in the same list are painted
            using the same color.
        """
        formula = wcnf.WCNFFormula()

        nodes = [i+1 for i in range(self.n_nodes)]

        neighbours = {}

        for i in range(self.n_nodes):
            neighbours[nodes[i-1]] = [nodes[i-1]]

        for n1, n2 in self.edges:
            v1, v2 = nodes[n1 - 1], nodes[n2 - 1]

            neighbours = add_neighbour(neighbours, v1, v2)

            neighbours = add_neighbour(neighbours, v2, v1)

        max_connectivity = 0

        for node in neighbours:
            max_connectivity = max(max_connectivity, len(neighbours.get(node)))

        vars_to_parent = {}

        matrix = []
        for node in nodes:
            row = [formula.new_var() for _ in range(max_connectivity)]
            matrix.append(row)
            for elem in row:
                vars_to_parent[elem] = node

        colors = []
        for _ in range(max_connectivity):
            colors.append(formula.new_var())

        # soft: using one colour has a cost of 1
        for color in colors:
            formula.add_clause([-color], 1)

        # hard: each variable has a colour associated,
        # but different variables represent the same colour
        for i in range(len(matrix[0])):
            for row in range(len(neighbours)):
                relation = [-matrix[row][i], colors[i]]
                formula.add_clause(relation, wcnf.TOP_WEIGHT)

        # hard: each node has to be painted in one colour only and exactly one colour
        for row in matrix:
            formula.add_exactly_one(row)

        # hard: only one neighbour or the node can have the same colour
        for node in neighbours:
            veins = neighbours[node]
            for vei in veins[1:]:
                for i in range(len(matrix[0])):
                    restriction = [matrix[veins[0]-1][i], matrix[vei-1][i]]
                    formula.add_at_most_one(restriction)

        return compute_all_solutions(self, formula, solver, n_solutions,
                                     advanced_compute, vars_to_parent, nodes, colors)


# Program main
###############################################################################


def main(argv=None):
    args = parse_command_line_arguments(argv)

    solver = msat_runner.MaxSATRunner(args.solver)
    graph = Graph(args.graph)

    mds_all = graph.min_dominating_set(solver, args.n_solutions)
    assert all(len(mds_all[0]) == len(x) for x in mds_all)

    mis_all = graph.max_independent_set(solver, args.n_solutions)
    assert all(len(mis_all[0]) == len(x) for x in mis_all)

    mgc_all = graph.min_graph_coloring(solver, args.n_solutions)
    assert all(len(mgc_all[0]) == len(x) for x in mgc_all)

    print("INDEPENDENT DOMINATION NUMBER", len(mds_all[0]))
    for mds in mds_all:
        print("MDS", " ".join(map(str, mds)))

    print("INDEPENDENCE NUMBER", len(mis_all[0]))
    for mis in mis_all:
        print("MIS", " ".join(map(str, mis)))

    print("CHROMATIC INDEX", len(mgc_all[0]))
    for mgc in mgc_all:
        nodes = (" ".join(map(str, x)) for x in mgc)
        print("GC", " | ".join(nodes))


# Utilities
###############################################################################

def parse_command_line_arguments(argv=None):
    parser = argparse.ArgumentParser(
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)

    parser.add_argument("solver", help="Path to the MaxSAT solver.")

    parser.add_argument("graph", help="Path to the file that descrives the"
                                      " input graph.")

    parser.add_argument("-n", "--n-solutions", type=int, default=1,
                        help="Number of solutions to compute, 0 or negative"
                             " means all solutions.")

    return parser.parse_args(args=argv)


def basic_compute(self, formula, model, vars_to_parent, nodes, colors):
    """
    Computes the min dominating set and max independent set problems solutions
    :param self:
    :param formula:
    :param model:
    :param vars_to_parent:
    :param nodes:
    :param colors:
    :return:
    """
    solution = [x for x in range(1, self.n_nodes + 1) if model[x - 1] > 0]
    new_clause = negate(solution)
    formula.add_clause(new_clause, wcnf.TOP_WEIGHT)
    return solution


def advanced_compute(self, formula, model, vars_to_parent, nodes, colors):
    """
    Computes the graph coloring problem solution
    :param self:
    :param formula:
    :param model:
    :param vars_to_parent: dict that maps a var to a node
    :param nodes: list of nodes
    :param colors: list of colours
    :return: returns one solution
    """

    # compute all solutions or one solution
    solution = []
    vertexcolor = [[] for _ in range(len(colors))]

    for x in range(0, len(nodes) * len(colors)):
        if model[x] > 0:
            col = model[x] % len(colors)
            node = vars_to_parent[model[x]]
            vertexcolor[col].append(node)

    for listVertex in vertexcolor:
        if len(listVertex) > 0:
            solution.append(listVertex)
    new_clause = negate(model)
    formula.add_clause(new_clause, wcnf.TOP_WEIGHT)
    return solution


def compute_all_solutions(self, formula, solver, n_solutions, compute=basic_compute, vars_to_parent=None, nodes=None, colors=None):
    """
    Abstract layer that processes different computes for different number of solutions
    :param self:
    :param formula:
    :param solver:
    :param n_solutions:
    :param compute: function that has to compute the solution
    :param vars_to_parent:
    :param nodes:
    :param colors:
    :return: all solutions requested
    """
    i = 0
    max_opt = 0
    all_solutions = []
    if n_solutions <= 0:
        n_solutions = sys.maxsize

    while i < n_solutions:
        opt, model = solver.solve(formula)
        if i == 0 and opt >= 0:
            max_opt = opt
        if opt == max_opt:
            solution = compute(self, formula, model, vars_to_parent, nodes, colors)
            if solution not in all_solutions:
                all_solutions.append(solution)
                i += 1
        else:
            break
    return all_solutions


def negate(formula):
    """Negates a given formula

    :param formula: list of literals
    :return: the list of literals negated
    """
    res = [-elem for elem in formula]

    return res


def add_neighbour(neighbours, node, new):
    """Adds a neighbour to the node list of neighbours + himself

    :param neighbours: dictionary of node, neighbours
    :param node: the key
    :param new: the neighbour to add
    :return: the updated dictionary
    """
    anterior = neighbours.get(node)
    anterior.append(new)
    neighbours[node] = anterior
    return neighbours

# Entry point
###############################################################################


if __name__ == "__main__":
    sys.exit(main())
