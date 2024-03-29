import json
import tempfile
from graphillion import GraphSet
import sdd
import sdd.models
import sdd.util
import logging
import itertools
import re
import simple_graph
Edge = simple_graph.Edge

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
    result = conversion_map[last_node_index]
    if decision_variable_map[last_node_index] != 1:
        skipped_variables = range(1, decision_variable_map[last_node_index])
        neg_terms = sdd.util.sdd_negative_term(sdd_manager, sum([zdd_edge_to_sdd_edges[x] for x in skipped_variables], []))
        result = sdd.sdd_conjoin(neg_terms, conversion_map[last_node_index], sdd_manager)
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

class Graph(object):
    def __init__(self, edge_list):
        self.edge_list = edge_list
        self.node_to_edges = {}
        for idx, edge_json in enumerate(edge_list):
            cur_edge = Edge.load_from_json(edge_json)
            self.node_to_edges.setdefault(cur_edge.x, []).append(cur_edge)
            self.node_to_edges.setdefault(cur_edge.y, []).append(cur_edge)

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
        total_constraint = simple_path_constraint
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
        for external_edge in self.external_edges:
            if_sdd_index += 1
            if_variable_mapping[str(external_edge)] = if_sdd_index
        then_variable_mapping = {}
        # variables for the child clusters
        then_sdd_index = 0
        zdd_to_sdd_index = [None]
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

    def GetRootCluster(self):
        cluster_names = set(self.clusters.keys())
        for cluster_name in self.clusters:
            cur_cluster = self.clusters[cluster_name]
            if cur_cluster.children is not None:
                for child_name in cur_cluster.children:
                    if child_name in cluster_names:
                        cluster_names.remove(child_name)
        assert len(cluster_names) == 1
        return self.clusters[cluster_names.pop()]

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
            for edge in cluster.internal_edges:
                variables.append(str(edge))
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
            cur_external_edges = cluster.external_edges.keys()
            cluster_spec["parents"] = []
            for parent_name in self.clusters:
                parent_cluster = self.clusters[parent_name]
                if any([x in parent_cluster.internal_edges for x in cur_external_edges]):
                    cluster_spec["parents"].append(parent_cluster.name)
            cluster_spec["constraint"] = cluster.GetLocalConstraints(prefix)
            spec["clusters"].append(cluster_spec)
        return spec

    def LoadVariableIndexesFromSbnSpec(self, sbn_spec):
        edge_index_map = {} # key is edge and value is index
        cluster_index_map ={} # key is cluster name
        variables = sbn_spec["variables"]
        for idx, variable_name in enumerate(variables):
            index = idx + 1
            assert variable_name[0] == "e"
            e = Edge.load_from_str(variable_name)
            edge_index_map[e] = index
        return edge_index_map
