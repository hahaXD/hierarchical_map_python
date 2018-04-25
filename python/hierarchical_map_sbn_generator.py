import json
import tempfile
from graphillion import GraphSet
import gmplot
import sys
import itertools
import sdd
import sdd.models
import sdd.util
from optparse import OptionParser
import os
import random
import subprocess, shlex
import math
import string
from plot_mar_prediction import *
import logging

def byteify(input):
    if isinstance(input, dict):
        return {byteify(key): byteify(value)
                for key, value in input.iteritems()}
    elif isinstance(input, list):
        return [byteify(element) for element in input]
    elif isinstance(input, unicode):
        return input.encode('utf-8')
    else:
        return input
def other_end(edge_tup, orig):
    if edge_tup[0] == orig:
        return edge_tup[1]
    else:
        return edge_tup[0]

def sequence_path (path):
    if len(path) == 1:
        return list(path)
    result = []
    node_to_edge = {}
    for edge in path:
        node_to_edge.setdefault(edge[0],[]).append(edge)
        node_to_edge.setdefault(edge[1],[]).append(edge)
    starting_edge = []
    end_nodes = []
    for node in node_to_edge:
        if len(node_to_edge[node]) == 1:
            starting_edge.append(node_to_edge[node][0])
            end_nodes.append(node)
    assert len(starting_edge) == 2
    result.append(end_nodes[0])
    cur_node = other_end(starting_edge[0], end_nodes[0])
    result.append(cur_node)
    while cur_node != end_nodes[1]:
        edges = node_to_edge[cur_node]
        if result[-2] in edges[0]:
            cur_node = other_end(edges[1], cur_node)
        else:
            assert result[-2] in edges[1]
            cur_node = other_end(edges[0], cur_node)
        result.append(cur_node)
    return result

def generate_exactly_two_from_tuples(sdd_manager, tuples, variables):
    result_constraint = sdd.sdd_manager_false(sdd_manager)
    for cur_tup in tuples:
        cur_term = sdd.sdd_manager_true(sdd_manager)
        for cur_var in variables:
            if cur_var in cur_tup:
                cur_term = sdd.sdd_conjoin(cur_term, sdd.sdd_manager_literal(cur_var, sdd_manager), sdd_manager)
            else:
                cur_term = sdd.sdd_conjoin(cur_term, sdd.sdd_manager_literal(-cur_var, sdd_manager), sdd_manager)
        result_constraint = sdd.sdd_disjoin(cur_term, result_constraint, sdd_manager)
    return result_constraint

def EdgeToIndex(sbn_spec):
    edge_index_map = {} # key is edge and value is index
    variables = sbn_spec["variables"]
    for idx, variable_name in enumerate(variables):
        index = idx + 1
        if variable_name[0] == "e":
            str_pair = variable_name.split(" ")[1][1:-1].split(",")
            node_a, node_b = (int(str_pair[0]), int(str_pair[1]))
            node_a, node_b = (min(node_a, node_b), max(node_a, node_b))
            edge_index_map[(node_a, node_b)] = index
    return edge_index_map

def GenerateTrainingDataset(hm_network, sbn_spec, training_routes):
    edge_index_map = {} # key is edge and value is index
    cluster_index_map ={} #
    topological_order = hm_network.TopologicalSort()
    variables = sbn_spec["variables"]
    for idx, variable_name in enumerate(variables):
        index = idx + 1
        if variable_name[0] == "e":
            str_pair = variable_name.split(" ")[1][1:-1].split(",")
            node_a, node_b = (int(str_pair[0]), int(str_pair[1]))
            node_a, node_b = (min(node_a, node_b), max(node_a, node_b))
            edge_index_map[(node_a, node_b)] = index
        else:
            assert variable_name[0] == "c"
            cluster_name = variable_name[1:]
            cluster_index_map[cluster_name] = index
    data = {}
    data["variable_size"] = len(variables)
    root_cluster = topological_order[-1]
    data["data"] = []
    for route in training_routes:
        used_index = []
        used_nodes = set()
        for edge in route:
            edge_pair = (min(edge), max(edge))
            edge_index = edge_index_map[edge_pair]
            used_index.append(edge_index)
            used_nodes.add(edge[0])
            used_nodes.add(edge[1])
        cur_cluster = root_cluster
        while cur_cluster.children is not None:
            involved_child_clusters = []
            for child_name in cur_cluster.children:
                child_cluster = cur_cluster.children[child_name]
                if len(child_cluster.nodes.union(used_nodes)) != 0:
                    involved_child_clusters.append(child_name)
            if len(involved_child_clusters) == 1:
                used_index.append(cluster_index_map[involved_child_clusters[0]])
                cur_cluster = child_cluster
            else:
                break
        data["data"].append(used_index)
    return data

def generate_sdd_from_graphset(paths, sdd_manager, zdd_edge_to_sdd_edges):
    try:
        zdd_file = tempfile.TemporaryFile()
        paths.dump(zdd_file)
        zdd_file.seek(0)
        zdd_content = zdd_file.readlines()
    finally:
        zdd_file.close()
    # handle the trivial logic
    if zdd_content[0].strip() == "T":
        result_sdd = sdd.sdd_manager_true(sdd_manager)
        for sdd_edges in zdd_edge_to_sdd_edges:
            cur_neg_term = sdd.util.sdd_negative_term(sdd_manager, sdd_edges)
            result_sdd = sdd.sdd_conjoin(result_sdd, cur_neg_term, sdd_manager)
        return result_sdd
    if zdd_content[0].strip() == "B":
        result_sdd = sdd.sdd_manager_false(sdd_manager)
        return result_sdd
    pos_zdd_indicator_to_sdd = [None]
    neg_zdd_indicator_to_sdd = [None]
    for sdd_edges in zdd_edge_to_sdd_edges:
        if sdd_edges:
            pos_zdd_indicator_to_sdd.append(sdd.util.sdd_exactly_one(sdd_manager,sdd_edges))
            neg_zdd_indicator_to_sdd.append(sdd.util.sdd_negative_term(sdd_manager, sdd_edges))
    conversion_map = {} # key is the node index and the value is a sdd node
    decision_variable_map = {} # key is the node index and the value is the variable index
    last_node_index = None
    zdd_variable_size = len(zdd_edge_to_sdd_edges) - 1;
    def complete_zdd_child (variable_index, child, conversion_map, decision_variable_map, zdd_variable_size, sdd_manager):
        if child == "T":
            if variable_index != zdd_variable_size:
                skipped_variables = range(variable_index + 1, zdd_variable_size + 1)
                neg_terms = sdd.util.sdd_negative_term(sdd_manager, sum([zdd_edge_to_sdd_edges[x] for x in skipped_variables],[]))
                return neg_terms
            else:
                return sdd.sdd_manager_true(sdd_manager)
        elif child == "B":
            return sdd.sdd_manager_false(sdd_manager)
        else:
            child = int(child)
            child_variable = decision_variable_map[child]
            if child_variable == variable_index + 1:
                return conversion_map[child]
            else:
                skipped_variables = range(variable_index + 1, child_variable)
                neg_terms = sdd.util.sdd_negative_term(sdd_manager, sum([zdd_edge_to_sdd_edges[x] for x in skipped_variables],[]))
                return sdd.sdd_conjoin(neg_terms, conversion_map[child], sdd_manager)
    for line in zdd_content:
        line = line.strip()
        if line == ".":
            break;
        line_toks = line.split(" ")
        node_index = int(line_toks[0])
        variable_index = int(line_toks[1])
        low_child = line_toks[2]
        high_child = line_toks[3]
        sdd_low_child = None
        sdd_high_child = None
        sdd_low_child = complete_zdd_child(variable_index, low_child, conversion_map, decision_variable_map, zdd_variable_size, sdd_manager)
        sdd_high_child = complete_zdd_child(variable_index, high_child, conversion_map, decision_variable_map, zdd_variable_size, sdd_manager)
        cur_node_positive_element = sdd.sdd_conjoin(pos_zdd_indicator_to_sdd[variable_index], sdd_high_child, sdd_manager)
        cur_node_negative_element = sdd.sdd_conjoin(neg_zdd_indicator_to_sdd[variable_index], sdd_low_child, sdd_manager)
        conversion_map[node_index] = sdd.sdd_disjoin(cur_node_negative_element, cur_node_positive_element, sdd_manager)
        decision_variable_map[node_index] = variable_index
        last_node_index = node_index
    if decision_variable_map[last_node_index] == 1:
        return conversion_map[last_node_index]
    else:
        skipped_variables = range(1, decision_variable_map[last_node_index])
        neg_terms = sdd.util.sdd_negative_term(sdd_manager, sum([zdd_edge_to_sdd_edges[x] for x in skipped_variables], []))
        return sdd.sdd_conjoin(neg_terms, conversion_map[last_node_index], sdd_manager)


class Edge(object):
    def __init__(self,x,y,name):
        if cmp(x,y) > 0: x,y = y,x
        self.x = x
        self.y = y
        self.name = name
        self.nodes = set([x,y])
    def OtherEnd(self, input_end):
        if self.x == input_end:
            return self.y
        else:
            return self.x
    def global_id(self):
        return "e%d" % self.name

    def as_tuple(self):
        return (self.x,self.y)

    def __repr__(self):
        return "%s (%s,%s)" % (self.global_id(),str(self.x),str(self.y))

    def __cmp__(self,other):
        return cmp(self.name,other.name)

    def __eq__ (self, other):
        return (self.x, self.y, self.name) == (other.x, other.y, other.name)

    def __hash__(self):
        return hash((self.x, self.y, self.name))

class Graph(object):
    def __init__(self, edge_list):
        self.edge_list = edge_list
        self.node_to_edges = {}
        for idx,cur_node_pair in enumerate(edge_list):
            cur_edge = Edge(cur_node_pair[0], cur_node_pair[1], idx+1)
            self.node_to_edges.setdefault(cur_node_pair[0], []).append(cur_edge)
            self.node_to_edges.setdefault(cur_node_pair[1], []).append(cur_edge)

class HmCluster (object):
    @staticmethod
    def GetLeaveCluster(name, node_indexes, graph):
        a = HmCluster(name);
        a.nodes = set(node_indexes)
        a.internal_edges = set()
        a.external_edges = {}
        for node_index in node_indexes:
            neighboring_edges = graph.node_to_edges[node_index]
            for cur_neighboring_edge in neighboring_edges:
                cur_neighboring_node = cur_neighboring_edge.OtherEnd(node_index)
                if cur_neighboring_node in a.nodes:
                    a.internal_edges.add(cur_neighboring_edge)
                else:
                    a.external_edges[cur_neighboring_edge] = node_index
        return a
    @staticmethod
    def GetInternalCluster(name, child_clusters, graph):
        a = HmCluster(name);
        a.nodes = set.union(*[child.nodes for child in child_clusters])
        a.children = {}
        a.internal_edges = set()
        a.external_edges = {} # key is the Edge and value is the connection child region
        a.sub_region_edges = {}
        node_to_child = {}
        for child_cluster in child_clusters:
            a.children[child_cluster.name] = child_cluster
            for cur_node in child_cluster.nodes:
                node_to_child[cur_node] = child_cluster
        for child_cluster in child_clusters:
            for cur_node_index in child_cluster.nodes:
                neighboring_edges = graph.node_to_edges[cur_node_index]
                for cur_neighboring_edge in neighboring_edges:
                    cur_neighboring_node = cur_neighboring_edge.OtherEnd(cur_node_index)
                    if cur_neighboring_node not in child_cluster.nodes and cur_neighboring_node in a.nodes:
                        #internal edges
                        a.internal_edges.add(cur_neighboring_edge)
                        a_region_name = child_cluster.name
                        b_region_name = node_to_child[cur_neighboring_node].name
                        edge_tuple = (min(a_region_name, b_region_name), max(a_region_name, b_region_name))
                        a.sub_region_edges.setdefault(edge_tuple, set()).add(cur_neighboring_edge)
                    elif cur_neighboring_node not in a.nodes:
                        #external edges
                        a.external_edges[cur_neighboring_edge] = child_cluster.name
                    else:
                        pass
        return a
    @staticmethod
    def GetCluster(cluster_name, hm_clusters, graph,  cache):
        if cluster_name in cache:
            return cache[cluster_name]
        if "nodes" in hm_clusters[cluster_name]:
            result  = HmCluster.GetLeaveCluster(cluster_name, hm_clusters[cluster_name]["nodes"], graph)
            cache[cluster_name] = result
            return result
        else:
            child_clusters = [HmCluster.GetCluster(child_cluster_name, hm_clusters, graph, cache) for child_cluster_name in hm_clusters[cluster_name]["sub_clusters"]]
            result = HmCluster.GetInternalCluster(cluster_name, child_clusters, graph)
            cache[cluster_name] = result
            return result
    def GetLocalConstraints(self, file_prefix):
        if len(self.external_edges) == 0:
            # root variable
            return self.GetLocalConstraintsForRoot(file_prefix)
        elif self.children:
            # internal variable
            return self.GetLocalConstraintsForInternalClusters(file_prefix)
        else:
            # leaf variable
            return self.GetLocalConstraintsForLeaveClusters(file_prefix)
    def GetLocalConstraintsForRoot(self, file_prefix):
        then_vtree_filename = "%s/%s_then_vtree.vtree" % (file_prefix, self.name)
        then_sdd_filename = "%s/%s_then_sdd.sdd" % (file_prefix, self.name)
        constraint = {}
        constraint["then_vtree"] = then_vtree_filename
        constraint["then"] = [then_sdd_filename]
        universe = []
        # internal edges
        for sub_region_edge_tup in self.sub_region_edges:
            universe.append(sub_region_edge_tup)
        GraphSet.set_universe(universe)
        universe = GraphSet.universe()
        paths = GraphSet()
        child_names = self.children.keys()
        for (i,j) in itertools.combinations(child_names, 2):
            paths = paths.union(GraphSet.paths(i, j))
        name_to_sdd_index = {}
        zdd_to_sdd_index =  [None] # for generating sdd from graphset
        sdd_index = 0
        for child in child_names:
            sdd_index += 1
            name_to_sdd_index["c%s" %child] = sdd_index
        for sub_region_edge in universe:
            corresponding_network_edges = self.sub_region_edges[sub_region_edge]
            coresponding_network_edges_sdd_index = []
            for single_edge in corresponding_network_edges:
                sdd_index += 1
                name_to_sdd_index[str(single_edge)] = sdd_index;
                coresponding_network_edges_sdd_index.append(sdd_index)
            zdd_to_sdd_index.append(coresponding_network_edges_sdd_index)
        constraint["then_variable_mapping"] = name_to_sdd_index
        rl_vtree = sdd.sdd_vtree_new(sdd_index, "right")
        sdd_manager = sdd.sdd_manager_new(rl_vtree)
        sdd.sdd_vtree_free(rl_vtree)
        sdd.sdd_manager_auto_gc_and_minimize_off(sdd_manager)
        # Construct simple path constraint
        simple_path_constraint = generate_sdd_from_graphset(paths, sdd_manager, zdd_to_sdd_index)
        # non empty path in this region map
        none_of_child = sdd.util.sdd_negative_term(sdd_manager, [name_to_sdd_index["c%s"%child] for child in self.children])
        case_one = sdd.sdd_conjoin(none_of_child, simple_path_constraint, sdd_manager)
        # empty path in this region map
        exactly_one_child  = sdd.util.sdd_exactly_one(sdd_manager,[name_to_sdd_index["c%s"%child] for child in self.children])
        empty_path_constraint = sdd.util.sdd_negative_term(sdd_manager, sum(zdd_to_sdd_index[1:], []))
        case_two = sdd.sdd_conjoin(exactly_one_child, empty_path_constraint, sdd_manager)
        total_constraint = sdd.sdd_disjoin(case_one, case_two, sdd_manager)
        sdd.sdd_save(then_sdd_filename, total_constraint)
        sdd.sdd_vtree_save(then_vtree_filename, sdd.sdd_manager_vtree(sdd_manager))
        sdd.sdd_manager_free(sdd_manager)
        return constraint
    def GetLocalConstraintsForLeaveClusters(self, file_prefix):
        if_vtree_filename = "%s/%s_if_vtree.vtree" % (file_prefix, self.name)
        if_sdd_filename_prefix = "%s/%s_if_sdd" % (file_prefix, self.name)
        then_vtree_filename = "%s/%s_then_vtree.vtree" % (file_prefix, self.name)
        then_sdd_filename_prefix = "%s/%s_then_sdd" % (file_prefix, self.name)
        ifs = []
        thens = []
        if_variable_mapping = {}
        if_sdd_index = 0
        if_sdd_index += 1
        if_variable_mapping["c%s"% self.name] = if_sdd_index # cluster indicator for current cluster
        for external_edge in self.external_edges:
            if_sdd_index += 1
            if_variable_mapping[str(external_edge)] = if_sdd_index
        then_variable_mapping = {}
        zdd_to_sdd_index = [None]
        universe = []
        node_pair_to_edges = {}
        for internal_edge in self.internal_edges:
            if (internal_edge.x, internal_edge.y) not in node_pair_to_edges:
                universe.append((internal_edge.x, internal_edge.y))
            node_pair_to_edges.setdefault((internal_edge.x, internal_edge.y), []).append(internal_edge)
        GraphSet.set_universe(universe)
        universe = GraphSet.universe()
        then_sdd_index = 0
        for node_pair in universe:
            correponding_sdd_indexes = []
            for internal_edge in node_pair_to_edges[node_pair]:
                then_sdd_index += 1
                then_variable_mapping[str(internal_edge)] = then_sdd_index
                correponding_sdd_indexes.append(then_sdd_index)
            zdd_to_sdd_index.append(correponding_sdd_indexes)
        if_vtree, then_vtree = sdd.sdd_vtree_new(if_sdd_index, "right"), sdd.sdd_vtree_new(then_sdd_index, "right")
        if_manager, then_manager = sdd.sdd_manager_new(if_vtree), sdd.sdd_manager_new(then_vtree)
        sdd.sdd_manager_auto_gc_and_minimize_off(if_manager)
        sdd.sdd_manager_auto_gc_and_minimize_off(then_manager)
        sdd.sdd_vtree_free(if_vtree)
        sdd.sdd_vtree_free(then_vtree)
        #none of the external edges are used and cluster indicator is off
        case_index = 0
        case_one_if = sdd.util.sdd_negative_term(if_manager, range(1, if_sdd_index +1))
        case_one_then = sdd.util.sdd_negative_term(then_manager, range(1, then_sdd_index+1))
        sdd.sdd_save("%s_%s" % (if_sdd_filename_prefix, case_index), case_one_if)
        sdd.sdd_save("%s_%s" % (then_sdd_filename_prefix, case_index), case_one_then)
        ifs.append("%s_%s" % (if_sdd_filename_prefix, case_index))
        thens.append("%s_%s" % (then_sdd_filename_prefix, case_index))
        #none of the external edges are used and cluster indicator is on
        case_index += 1
        case_two_if = sdd.util.sdd_exactly_one_among(if_manager, [if_variable_mapping["c%s"%self.name]], range(1, if_sdd_index+1))
        paths = GraphSet()
        for (i,j) in itertools.combinations(self.nodes, 2):
            paths = paths.union(GraphSet.paths(i,j))
        case_two_then = generate_sdd_from_graphset(paths, then_manager, zdd_to_sdd_index)
        sdd.sdd_save("%s_%s" % (if_sdd_filename_prefix, case_index), case_two_if)
        sdd.sdd_save("%s_%s" % (then_sdd_filename_prefix, case_index), case_two_then)
        ifs.append("%s_%s" % (if_sdd_filename_prefix, case_index))
        thens.append("%s_%s" % (then_sdd_filename_prefix, case_index))
        #exactly one of the external edge is used and cluster indicator is off
        aggregated_cases = {}
        for external_edge in self.external_edges:
            aggregated_cases.setdefault(self.external_edges[external_edge],[]).append(external_edge)
        for entering_node in aggregated_cases:
            case_index += 1
            cur_case_if = sdd.util.sdd_exactly_one_among(if_manager, [if_variable_mapping[str(e)] for e in aggregated_cases[entering_node]], range(1, if_sdd_index+1))
            paths = GraphSet()
            for node in self.nodes:
                if node == entering_node:
                    continue
                paths = paths.union(GraphSet.paths(entering_node, node))
            cur_case_then = generate_sdd_from_graphset(paths, then_manager, zdd_to_sdd_index)
            # disjoin the empty path
            cur_case_then = sdd.sdd_disjoin(cur_case_then, sdd.util.sdd_negative_term(then_manager, range(1, then_sdd_index+1)), then_manager)
            sdd.sdd_save("%s_%s" % (if_sdd_filename_prefix, case_index), cur_case_if)
            sdd.sdd_save("%s_%s" % (then_sdd_filename_prefix, case_index), cur_case_then)
            ifs.append("%s_%s" % (if_sdd_filename_prefix, case_index))
            thens.append("%s_%s" % (then_sdd_filename_prefix, case_index))
        # exactly two of the external edge is used and cluster_indicator is off
        aggregated_cases = {}
        for (i,j) in itertools.combinations(self.external_edges.keys(), 2):
            entering_points = (self.external_edges[i], self.external_edges[j])
            entering_points = (max(entering_points), min(entering_points))
            aggregated_cases.setdefault(entering_points, []).append((i,j))
        for entering_points in aggregated_cases:
            case_index +=1
            entering_edges = aggregated_cases[entering_points]
            cur_case_if = generate_exactly_two_from_tuples(if_manager, [(if_variable_mapping[str(e1)], if_variable_mapping[str(e2)]) for (e1,e2) in entering_edges], range(1, if_sdd_index+1))
            if entering_points[0] == entering_points[1]:
                cur_case_then = sdd.util.sdd_negative_term(then_manager, range(1, then_sdd_index+1))
            else:
                paths = GraphSet.paths(entering_points[0], entering_points[1])
                cur_case_then = generate_sdd_from_graphset(paths, then_manager, zdd_to_sdd_index)
            sdd.sdd_save("%s_%s" % (if_sdd_filename_prefix, case_index), cur_case_if)
            sdd.sdd_save("%s_%s" % (then_sdd_filename_prefix, case_index), cur_case_then)
            ifs.append("%s_%s" % (if_sdd_filename_prefix, case_index))
            thens.append("%s_%s" % (then_sdd_filename_prefix, case_index))
        sdd.sdd_vtree_save(if_vtree_filename, sdd.sdd_manager_vtree(if_manager))
        sdd.sdd_vtree_save(then_vtree_filename, sdd.sdd_manager_vtree(then_manager))
        sdd.sdd_manager_free(if_manager)
        sdd.sdd_manager_free(then_manager)
        constraint = {}
        constraint["if_vtree"] = if_vtree_filename
        constraint["if"] = ifs
        constraint["if_variable_mapping"] = if_variable_mapping
        constraint["then_vtree"] = then_vtree_filename
        constraint["then"] = thens
        constraint["then_variable_mapping"] = then_variable_mapping
        return constraint

    def GetLocalConstraintsForInternalClusters(self, file_prefix):
        if_vtree_filename = "%s/%s_if_vtree.vtree" % (file_prefix, self.name)
        if_sdd_filename_prefix = "%s/%s_if_sdd" % (file_prefix, self.name)
        then_vtree_filename = "%s/%s_then_vtree.vtree" % (file_prefix, self.name)
        then_sdd_filename_prefix = "%s/%s_then_sdd" % (file_prefix, self.name)
        ifs = []
        thens = []
        if_variable_mapping = {}
        if_sdd_index = 0
        if_sdd_index += 1
        if_variable_mapping["c%s"% self.name] = if_sdd_index # cluster indicator for current cluster
        for external_edge in self.external_edges:
            if_sdd_index += 1
            if_variable_mapping[str(external_edge)] = if_sdd_index
        then_variable_mapping = {}
        # variables for the child clusters
        then_sdd_index = 0
        zdd_to_sdd_index = [None]
        for child in self.children:
            then_sdd_index += 1
            then_variable_mapping["c%s" %child] = then_sdd_index
        universe = self.sub_region_edges.keys()
        GraphSet.set_universe(universe)
        universe = GraphSet.universe();
        for node_pair in universe:
            correponding_sdd_indexes = []
            for internal_edge in self.sub_region_edges[node_pair]:
                then_sdd_index += 1
                then_variable_mapping[str(internal_edge)] = then_sdd_index
                correponding_sdd_indexes.append(then_sdd_index)
            zdd_to_sdd_index.append(correponding_sdd_indexes)
        if_vtree, then_vtree = sdd.sdd_vtree_new(if_sdd_index, "right"), sdd.sdd_vtree_new(then_sdd_index, "right")
        if_manager, then_manager = sdd.sdd_manager_new(if_vtree), sdd.sdd_manager_new(then_vtree)
        sdd.sdd_manager_auto_gc_and_minimize_off(if_manager)
        sdd.sdd_manager_auto_gc_and_minimize_off(then_manager)
        sdd.sdd_vtree_free(if_vtree)
        sdd.sdd_vtree_free(then_vtree)
        #none of the external edges are used and cluster indicator is off
        case_index = 0
        case_one_if = sdd.util.sdd_negative_term(if_manager, range(1, if_sdd_index +1))
        case_one_then = sdd.util.sdd_negative_term(then_manager, range(1, then_sdd_index+1))
        sdd.sdd_save("%s_%s" % (if_sdd_filename_prefix, case_index), case_one_if)
        sdd.sdd_save("%s_%s" % (then_sdd_filename_prefix, case_index), case_one_then)
        ifs.append("%s_%s" % (if_sdd_filename_prefix, case_index))
        thens.append("%s_%s" % (then_sdd_filename_prefix, case_index))
        #none of the external edges are used and cluster indicator is on
        case_index += 1
        case_two_if = sdd.util.sdd_exactly_one_among(if_manager, [if_variable_mapping["c%s"%self.name]], range(1, if_sdd_index+1))
        #***Non empty path in this region map
        none_of_child = sdd.util.sdd_negative_term(then_manager, [then_variable_mapping["c%s"%child] for child in self.children])
        paths = GraphSet()
        child_names = self.children.keys()
        for c1, c2 in itertools.combinations(child_names, 2):
            paths = paths.union(GraphSet.paths(c1, c2))
        simple_path_constraint = generate_sdd_from_graphset(paths, then_manager, zdd_to_sdd_index)
        case_one = sdd.sdd_conjoin(simple_path_constraint, none_of_child, then_manager)
        #***Empty path in the region map
        exactly_one_chlid = sdd.util.sdd_exactly_one(then_manager, [then_variable_mapping["c%s"%child] for child in self.children])
        empty_path_constraint = sdd.util.sdd_negative_term(then_manager, sum(zdd_to_sdd_index[1:], []))
        case_two = sdd.sdd_conjoin(empty_path_constraint, exactly_one_chlid, then_manager)
        case_two_then = sdd.sdd_disjoin(case_one, case_two, then_manager)
        sdd.sdd_save("%s_%s" % (if_sdd_filename_prefix, case_index), case_two_if)
        sdd.sdd_save("%s_%s" % (then_sdd_filename_prefix, case_index), case_two_then)
        ifs.append("%s_%s" % (if_sdd_filename_prefix, case_index))
        thens.append("%s_%s" % (then_sdd_filename_prefix, case_index))
        #Exactly one of the external edge is used and cluster_indicator is off
        aggregated_cases = {}
        for external_edge in self.external_edges:
            aggregated_cases.setdefault(self.external_edges[external_edge],[]).append(external_edge)
        for entering_node in aggregated_cases:
            case_index += 1
            cur_case_if = sdd.util.sdd_exactly_one_among(if_manager, [if_variable_mapping[str(e)] for e in aggregated_cases[entering_node]], range(1, if_sdd_index+1))
            paths = GraphSet()
            for child in self.children:
                if child == entering_node:
                    continue
                paths = paths.union(GraphSet.paths(entering_node, child))
            cur_case_then = generate_sdd_from_graphset(paths, then_manager, zdd_to_sdd_index)
            cur_case_then = sdd.sdd_disjoin(cur_case_then, sdd.util.sdd_negative_term(then_manager, [then_variable_mapping[str(e)] for e in self.internal_edges]), then_manager)
            #conjoin that all the child indicator is off
            cur_case_then = sdd.sdd_conjoin(cur_case_then, sdd.util.sdd_negative_term(then_manager, [then_variable_mapping["c%s"% child] for child in self.children]), then_manager)
            sdd.sdd_save("%s_%s" % (if_sdd_filename_prefix, case_index), cur_case_if)
            sdd.sdd_save("%s_%s" % (then_sdd_filename_prefix, case_index), cur_case_then)
            ifs.append("%s_%s" % (if_sdd_filename_prefix, case_index))
            thens.append("%s_%s" % (then_sdd_filename_prefix, case_index))
        #Exactly two of the external edge is used and cluster_indicator is off
        aggregated_cases = {}
        for (i,j) in itertools.combinations(self.external_edges.keys(), 2):
            entering_points = (self.external_edges[i], self.external_edges[j])
            entering_points = (max(entering_points), min(entering_points))
            aggregated_cases.setdefault(entering_points, []).append((i,j))
        for entering_points in aggregated_cases:
            case_index +=1
            entering_edges = aggregated_cases[entering_points]
            cur_case_if = generate_exactly_two_from_tuples(if_manager, [(if_variable_mapping[str(e1)], if_variable_mapping[str(e2)]) for (e1,e2) in entering_edges], range(1, if_sdd_index+1))
            if entering_points[0] == entering_points[1]:
                cur_case_then = sdd.util.sdd_negative_term(then_manager, range(1, then_sdd_index+1))
            else:
                paths = GraphSet.paths(entering_points[0], entering_points[1])
                cur_case_then = generate_sdd_from_graphset(paths, then_manager, zdd_to_sdd_index)
                cur_case_then = sdd.sdd_conjoin(cur_case_then, sdd.util.sdd_negative_term(then_manager, [then_variable_mapping["c%s" % child] for child in self.children]),then_manager)
            sdd.sdd_save("%s_%s" % (if_sdd_filename_prefix, case_index), cur_case_if)
            sdd.sdd_save("%s_%s" % (then_sdd_filename_prefix, case_index), cur_case_then)
            ifs.append("%s_%s" % (if_sdd_filename_prefix, case_index))
            thens.append("%s_%s" % (then_sdd_filename_prefix, case_index))
        sdd.sdd_vtree_save(if_vtree_filename, sdd.sdd_manager_vtree(if_manager))
        sdd.sdd_vtree_save(then_vtree_filename, sdd.sdd_manager_vtree(then_manager))
        sdd.sdd_manager_free(if_manager)
        sdd.sdd_manager_free(then_manager)
        constraint = {}
        constraint["if_vtree"] = if_vtree_filename
        constraint["if"] = ifs
        constraint["if_variable_mapping"] = if_variable_mapping
        constraint["then_vtree"] = then_vtree_filename
        constraint["then"] = thens
        constraint["then_variable_mapping"] = then_variable_mapping
        return constraint

    def __init__(self, name):
        self.name = name
        self.nodes = None
        self.children = None
        self.internal_edges = None
        self.external_edges = None
        self.sub_region_edges = None

class HmNetwork(object):
    def __init__(self):
        self.clusters = {}
        pass
    @staticmethod
    def ReadHmSpec(hm_spec):
        graph = Graph(hm_spec["edges"])
        cluster_spec = hm_spec["clusters"]
        cluster_node_indexes = {}
        variable_index = len(graph.edge_list) + 1
        for cluster_name in cluster_spec:
            cur_cluster_spec = cluster_spec[cluster_name]
            if "sub_clusters" in cur_cluster_spec:
                for sub_cluster_name in cur_cluster_spec["sub_clusters"]:
                    cluster_node_indexes[sub_cluster_name] = variable_index
                    variable_index += 1
        result = HmNetwork()
        for cluster_name in cluster_spec:
            if cluster_name not in result.clusters:
                HmCluster.GetCluster(cluster_name, cluster_spec, graph, result.clusters)
        return result

    def TopologicalSort(self):
        leave_to_root_order = []
        node_queue = [self.clusters[cluster_name] for cluster_name in self.clusters]
        while len(node_queue) > 0:
            leave_nodes = [x for x in node_queue if x.children == None or all( x.children[p] in leave_to_root_order for p in x.children)]
            node_queue = [x for x in node_queue if x not in leave_nodes]
            leave_to_root_order.extend(leave_nodes)
        return leave_to_root_order

    def write_hierarchy_to_dot(self, dot_filename):
        dot_file_content = "digraph g {\n"
        for cluster_name in self.clusters:
            cur_cluster = self.clusters[cluster_name]
            if cur_cluster.children == None:
                continue
            for child_cluster_name in cur_cluster.children:
                child_cluster = cur_cluster.children[child_cluster_name]
                dot_file_content += "%s -> %s\n" % (cluster_name, child_cluster.name)
        dot_file_content += "}"
        with open(dot_filename , "w") as fp:
            fp.write(dot_file_content)

    def CompileToSBN(self, prefix):
        variables = []
        for cluster_name in self.clusters:
            cluster = self.clusters[cluster_name]
            if cluster.children == None:
                continue
            for child_name in cluster.children:
                variables.append("c%s"%child_name)
        cluster_to_variables = {}
        for cluster_name in self.clusters:
            cluster = self.clusters[cluster_name]
            cur_variables = []
            for edge in cluster.internal_edges:
                variables.append(str(edge))
                cur_variables.append(str(edge))
            cluster_to_variables[cluster_name] = cur_variables
        spec = {}
        spec["variables"] = variables
        spec["clusters"] = []
        for cluster_name in self.clusters:
            logger = logging.getLogger()
            logger.info("Processing Cluster %s " % cluster_name)
            cluster = self.clusters[cluster_name]
            cluster_spec = {}
            cluster_spec["cluster_name"] = cluster.name
            cluster_spec["variables"] = []
            for edge in cluster.internal_edges:
                cluster_spec["variables"].append(str(edge))
            if cluster.children != None:
                for child_name in cluster.children:
                    cluster_spec["variables"].append("c%s"%child_name)
            cur_external_edges = cluster.external_edges.keys()
            cluster_spec["parents"] = []
            for parent_name in self.clusters:
                parent_cluster = self.clusters[parent_name]
                if any([x in parent_cluster.internal_edges for x in cur_external_edges]):
                    cluster_spec["parents"].append(parent_cluster.name)
            cluster_spec["constraint"] = cluster.GetLocalConstraints(prefix)
            spec["clusters"].append(cluster_spec)
        return spec

def RemoveSelfLoop (edges):
    new_edges = []
    for edge_tup in edges:
        if edge_tup[0] == edge_tup[1]:
            continue
        new_edges.append(edge_tup)
    return new_edges
def construct_cnf(src_edge_indexes, dst_edge_indexes, evid_edge_indexes, output_filename, variable_size):
    cnf = []
    cnf.append(list(src_edge_indexes))
    for i,j in itertools.combinations(src_edge_indexes,2):
        cnf.append([-i, -j])
    cnf.append(list(dst_edge_indexes))
    for i,j in itertools.combinations(dst_edge_indexes,2):
        cnf.append([-i, -j])
    for evid in evid_edge_indexes:
        cnf.append([evid])
    with open (output_filename, "w") as fp:
        fp.write("p cnf %s %s\n"%(variable_size, len(cnf)))
        for clause in cnf:
            fp.write("%s 0\n" % (" ".join([str(a) for a in clause])))

def TestSingleRoute(test_route, node_to_edge_indexes, pair_to_index, sdd_filename_prefix, inference_binary, learned_psdd_filename, learned_vtree_filename, variable_size):
    logger = logging.getLogger()
    sequence_route = sequence_path(test_route)
    used_edge_indexes = []
    for i in range(1, len(sequence_route)):
        node_a = sequence_route[i-1]
        node_b = sequence_route[i]
        cur_edge_pair = (min(node_a, node_b), max(node_a, node_b))
        used_edge_indexes.append(pair_to_index[cur_edge_pair])
    logger.info("Testing route with node sequence : %s, indexes of used edges : %s" % (sequence_route, used_edge_indexes))
    src_node = sequence_route[0]
    dst_node = sequence_route[-1]
    edges_index = []
    accurate = 0
    total_pred = 0
    for i in range(1, len(sequence_route)):
        succeed = False
        attempt_index = 0
        while not succeed:
            cnf_filename = "%s_%s_%s_evid.cnf" % (sdd_filename_prefix,i, attempt_index)
            construct_cnf(node_to_edge_indexes[src_node], node_to_edge_indexes[dst_node], edges_index, cnf_filename, variable_size)
            cmd = "%s --mar_query --cnf_evid %s %s %s" % (inference_binary, cnf_filename, learned_psdd_filename, learned_vtree_filename)
            logger.debug("Running command : %s" % cmd)
            output = subprocess.check_output(shlex.split(cmd))
            lines = output.split("\n")
            results = None
            for line in lines:
                if line.find("MAR result") != -1:
                    results = {}
                    raw_results = line.strip().split("=")[1].split(",")
                    for tok in raw_results:
                        if tok.strip() == "":
                            continue
                        var_index = int(tok.split(":")[0])
                        neg_logpr = float(tok.split(":")[1].split("|")[0])
                        pos_logpr = float(tok.split(":")[1].split("|")[1])
                        results[var_index] = (neg_logpr, pos_logpr)
                    logger.debug("Succeed in making prediction with evidence %s" % edges_index)
                    succeed = True
                if line.find("UNSATISFIED") != -1:
                    logger.debug("Evidence %s does not satisfy hierarchical simple constraint" % edges_index)
                    assert len(edges_index) > 0
                    edges_index = edges_index[1:]
            attempt_index += 1;
        node_a = sequence_route[i-1]
        node_b = sequence_route[i]
        cur_edge_pair = (min(node_a, node_b), max(node_a, node_b))
        assert results is not None
        if i == 1:
            candidate = list(node_to_edge_indexes[node_a])
        else:
            candidate = list(node_to_edge_indexes[node_a])
            if len(edges_index) > 0:
                candidate.remove(edges_index[-1])
        edges_index.append(pair_to_index[cur_edge_pair])
        candidate_weights = [results[i][1] for i in candidate]
        if abs(sum([math.exp(i) for i in candidate_weights]) - 1)  >= 0.1:
            logger.warning("Next route candidates' marginal added up to %s, which does not equal to 1" % sum([math.exp(i) for i in candidate_weights])) 
        max_candidate_index = candidate_weights.index(max(candidate_weights))
        pred = candidate[max_candidate_index]
        if pred == edges_index[-1]:
            accurate += 1
        candidate_weight_map = {}
        for idx, candidate_edge in enumerate(candidate):
            candidate_weight_map[candidate_edge] = math.exp(candidate_weights[idx])
        logging.info("Candidate distribution : %s. Prediction edge : %s. Actual used edge : %s." % (candidate_weight_map, pred, edges_index[-1])) 
        total_pred +=1
    return accurate, total_pred

if __name__ == "__main__":
    usage = "usage: %prog [options] hierarchical_spec"
    parser = OptionParser(usage=usage)
    parser.add_option("-d", "--data", action="store", type="string", dest="data")
    parser.add_option("--train_test_split", action="store", type="string", nargs=2, dest="train_test_split")
    parser.add_option("-s", "--seed", action="store", type="string", dest="seed")
    parser.add_option("--sdd_dir", action="store", type="string", dest="sdd_dir")
    parser.add_option("--sbn_compiler", action="store", type="string", dest="sbn_compiler")
    parser.add_option("--sbn_spec", action="store", type="string", dest="sbn_spec")
    parser.add_option("--psdd_inference", action="store", type="string", dest="psdd_inference")
    parser.add_option("--compiled_sbn", action="store", nargs=2, type="string", dest="compiled_sbn")
    parser.add_option("--test_size", action="store", type="string", dest="test_size")
    (options,args) = parser.parse_args()
    logging.basicConfig(level=logging.INFO)
    logger = logging.getLogger()
    if len(args) == 0:
        parser.print_usage()
        sys.exit(1)
    data = None
    training_routes = None
    testing_routes = None
    if options.train_test_split:
        assert options.data is None
        train_filename = options.train_test_split[0]
        test_filename = options.train_test_split[1]
        with open (train_filename, "r") as fp:
            training_routes = json.load(fp)
        with open (test_filename, "r") as fp:
            testing_routes = json.load(fp)
    test_size = None
    if options.test_size:
        test_size = int(options.test_size)
    if options.seed:
        random.seed(int(options.seed))
    with open (args[0], "r") as fp:
        hm_spec = json.load(fp)
        hm_spec = byteify(hm_spec)
        hm_spec["edges"] = RemoveSelfLoop(hm_spec["edges"])
    network = HmNetwork.ReadHmSpec(hm_spec)
    if options.sdd_dir:
        sdd_dir = options.sdd_dir
    else:
        sdd_dir = tempfile.gettempdir()
    if options.sbn_spec:
        with open(options.sbn_spec, "r") as fp:
            sbn_spec = json.load(fp)
    else:
        sbn_spec = network.CompileToSBN(os.path.abspath(sdd_dir)+"/")
    sbn_filename = "%s/sbn.json" % sdd_dir
    with open (sbn_filename, "w") as fp:
        json.dump(sbn_spec, fp, indent=2)
    if options.data:
        logger.info("Loading data %s" % options.data)
        assert training_routes is None
        assert testing_routes is None
        data_filename = options.data
        with open (data_filename, "r") as fp:
            data = json.load(fp)
        random.shuffle(data)
        training_size = len(data)/10*9
        training_routes = data[:training_size]
        if test_size:
            testing_routes = data[training_size:training_size + test_size]
        else:
            testing_routes = data[training_size:]
        training_routes_filename = "%s/training.json" % sdd_dir
        testing_routes_filename = "%s/testing.json" % sdd_dir
        with open(training_routes_filename, "w") as fp:
            json.dump(training_routes, fp)
        with open(testing_routes_filename, "w") as fp:
            json.dump(testing_routes, fp)
    training_data_filename = None
    if training_routes is not None:
        training_data_json = GenerateTrainingDataset(network, sbn_spec, training_routes)
        training_data_filename = "%s/training_data.json" % sdd_dir
        with open(training_data_filename, "w") as fp:
            json.dump(training_data_json, fp)
    if not options.compiled_sbn:
        psdd_filename = "%s/sbn.psdd" % sdd_dir
        vtree_filename = "%s/sbn.vtree" % sdd_dir
        if options.sbn_compiler:
            sbn_compiler = options.sbn_compiler
        else:  
            sbn_compiler = "structured_bn_main"
        cmd = "%s --psdd_filename %s --vtree_filename %s" % (sbn_compiler, psdd_filename, vtree_filename)
        if training_data_filename:
            cmd += " --sparse_learning_dataset %s" % training_data_filename
        cmd += " %s" % sbn_filename
        logger.info("Compiling sbn with commond : %s" % cmd)
        subprocess.call(shlex.split(cmd))
    else:
        psdd_filename = options.compiled_sbn[0]
        vtree_filename = options.compiled_sbn[1]
        logger.info("Load compiled psdd with filenames %s %s" % (psdd_filename, vtree_filename))
    edge_to_indexes = EdgeToIndex(sbn_spec)
    node_to_edges = {}
    inference_binary = None
    if options.psdd_inference is None:
        inference_binary = "psdd_inference_main"
    else:
        inference_binary = options.psdd_inference
    for tup in edge_to_indexes:
        node_to_edges.setdefault(tup[0], []).append(edge_to_indexes[tup])
        node_to_edges.setdefault(tup[1], []).append(edge_to_indexes[tup])
    if testing_routes is not None:
        total_prediction = 0
        total_accurate = 0
        for idx, test_route in enumerate(testing_routes):
            cur_accurate, cur_pred = TestSingleRoute(test_route, node_to_edges, edge_to_indexes, "%s/%s" %(sdd_dir,idx), inference_binary, psdd_filename, vtree_filename, len(sbn_spec["variables"]))
            total_prediction += cur_pred
            total_accurate += cur_accurate
        print "Accurate prediction: %s, Total prediction: %s, Accuracy: %s" % (total_accurate, total_prediction, float(total_accurate)/total_prediction)

