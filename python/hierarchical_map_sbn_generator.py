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
from plot_prediction import *
import logging
from enum import Enum
from hierarchical_map import HmNetwork, HmCluster

class Haversine:
    '''
    use the haversine class to calculate the distance between
    two lon/lat coordnate pairs.
    output distance available in kilometers, meters, miles, and feet.
    example usage: Haversine([lon1,lat1],[lon2,lat2]).feet
    '''
    def __init__(self,coord1,coord2):
        lon1,lat1=coord1
        lon2,lat2=coord2
        R=6371000                               # radius of Earth in meters
        phi_1=math.radians(lat1)
        phi_2=math.radians(lat2)

        delta_phi=math.radians(lat2-lat1)
        delta_lambda=math.radians(lon2-lon1)

        a=math.sin(delta_phi/2.0)**2+\
           math.cos(phi_1)*math.cos(phi_2)*\
           math.sin(delta_lambda/2.0)**2
        c=2*math.atan2(math.sqrt(a),math.sqrt(1-a))
        self.meters=R*c                         # output distance in meters
        self.km=self.meters/1000.0              # output distance in kilometers
        self.miles=self.meters*0.000621371      # output distance in miles
        self.feet=self.miles*5280               # output distance in feet


class MpeRoutePredictionMode(Enum):
    simple = 1
    step_by_step = 2
    half_evidence = 3

class DistanceMetric(Enum):
    dsn = 1
    hausdorff = 2
    route_length = 3

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
        return [path[0][0], path[0][1]]
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
"""
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
"""

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

def ParseMpeOutput(output):
    lines = output.split("\n")
    results = None
    for line in lines:
        line = line.strip()
        if line.find("MPE result") != -1:
            results = set()
            raw_result = line.split("=")[1].split(",")
            for tok in raw_result:
                if tok.strip() == "":
                    continue
                var_index = int(tok.split(":")[0])
                value = int(tok.split(":")[1])
                if value > 0:
                    results.add(var_index)
    return results

def CalculateDSN(route_1, route_2):
    if type(route_1) is not set:
        route_1 = set(route_1)
    if type(route_2) is not set:
        route_2 = set(route_2)
    common = route_1.intersection(route_2)
    mis_match = 0;
    for i in route_1:
        if i not in common:
            mis_match += 1
    for i in route_2:
        if i not in common:
            mis_match += 1
    total_len = len(route_1) + len(route_2)
    return float(mis_match) / total_len

def CalculateHausdorffDistance(route_1, route_2, index_to_tuples, node_locations):
    edge_route_1 = []
    edge_route_2 = []
    for edge_index in route_1:
        edge_route_1.append(index_to_tuples[edge_index])
    for edge_index in route_2:
        edge_route_2.append(index_to_tuples[edge_index])
    sequence_1 = sequence_path(edge_route_1)
    sequence_2 = sequence_path(edge_route_2)
    inf_distances = []
    for node_1 in sequence_1:
        inf_distances.append(min([Haversine(node_locations[node_1], node_locations[i]).feet for i in sequence_2]))
    sup_1 = max(inf_distances)
    inf_distances = []
    for node_2 in sequence_2:
        inf_distances.append(min([Haversine(node_locations[node_2], node_locations[i]).feet for i in sequence_1]))
    sup_2 = max(inf_distances)
    return max(sup_1, sup_2)

def FindConnectedPath(edges_set, starting_node, index_to_edges):
    node_to_edge_pairs = {}
    pair_to_index = {}
    for edge in edges_set:
        edge_pair = index_to_edges[edge]
        pair_to_index[edge_pair] = edge
        node_to_edge_pairs.setdefault(edge_pair[0],[]).append(edge_pair)
        node_to_edge_pairs.setdefault(edge_pair[1],[]).append(edge_pair)
    found_edges = set()
    open_nodes = [starting_node]
    closed_nodes = set()
    if starting_node not in node_to_edge_pairs:
        return []
    while len(open_nodes) > 0:
        cur_node = open_nodes[0]
        open_nodes = open_nodes[1:]
        neighboring_edges = node_to_edge_pairs[cur_node]
        for pair in neighboring_edges:
            other_node = other_end(pair, cur_node)
            found_edges.add(pair)
            if other_node not in closed_nodes:
                open_nodes.append(other_node)
                closed_nodes.add(other_node)
    return [pair_to_index[i] for i in found_edges]

def FindPathBetween(edges_set, start_node, end_node, index_to_edges):
    node_to_edge_pairs = {}
    pair_to_index = {}
    for edge in edges_set:
        edge_pair = index_to_edges[edge]
        pair_to_index[edge_pair] = edge
        node_to_edge_pairs.setdefault(edge_pair[0],[]).append(edge_pair)
        node_to_edge_pairs.setdefault(edge_pair[1],[]).append(edge_pair)
    queue = [(start_node, [start_node])]
    path_sequence = None
    while len(queue) > 0:
        cur_state = queue[0]
        cur_node_index = cur_state[0]
        cur_sequence = cur_state[1]
        assert cur_sequence[0] == cur_node_index
        queue = queue[1:]
        if cur_node_index == end_node:
            path_sequence = cur_state[1]
            break
        neighboring_edges = node_to_edge_pairs[cur_node_index]
        for edge in neighboring_edges:
            other_end_index = other_end(edge, cur_node_index)
            if len(cur_sequence) == 1:
                new_state = (other_end_index, [other_end_index, cur_sequence[0]])
            else:
                last_node_index = cur_sequence[1]
                if last_node_index != other_end_index:
                    new_state = (other_end_index, [other_end_index] + cur_sequence)
                else:
                    continue
            queue.append(new_state)
    if path_sequence is None:
        return None
    assert path_sequence[0] == end_node and path_sequence[-1] == start_node
    result = []
    for i in range(0, len(path_sequence)-1):
        node_a = path_sequence[i]
        node_b = path_sequence[i+1]
        cur_edge = (min(node_a, node_b), max(node_a, node_b))
        result.append(pair_to_index[cur_edge])
    return result


# route_1 - route_2
def CalculateRouteLengthDistance(route_1, route_2, index_to_tuples, node_locations):
    edge_route_1 = []
    edge_route_2 = []
    for edge_index in route_1:
        edge_route_1.append(index_to_tuples[edge_index])
    for edge_index in route_2:
        edge_route_2.append(index_to_tuples[edge_index])
    sequence_1 = sequence_path(edge_route_1)
    sequence_2 = sequence_path(edge_route_2)
    route_1_length = sum([Haversine(node_locations[sequence_1[i]],node_locations[sequence_1[i+1]]).feet for i in range(0, len(sequence_1)-1)])
    route_2_length = sum([Haversine(node_locations[sequence_2[i]],node_locations[sequence_2[i+1]]).feet for i in range(0, len(sequence_2)-1)])
    return route_1_length - route_2_length

def CalculateRouteDistance(route, index_to_tuples, node_locations):
    edge_route_1 = []
    for edge_index in route:
        edge_route_1.append(index_to_tuples[edge_index])
    sequence_1 = sequence_path(edge_route_1)
    route_1_length = sum([Haversine(node_locations[sequence_1[i]],node_locations[sequence_1[i+1]]).feet for i in range(0, len(sequence_1)-1)])
    return route_1_length


def RoutePredictionPerRoute(test_route, node_to_edge_indexes, pair_to_index, sdd_filename_prefix, inference_binary, learned_psdd_filename, learned_vtree_filename, variable_size, running_mode, distance_metric, node_locations):
    logger = logging.getLogger()
    sequence_route = sequence_path(test_route)
    used_edge_indexes = []
    index_to_tuples = {}
    edge_indexes_set = set()
    for pair in pair_to_index:
        index_to_tuples[pair_to_index[pair]] = pair
        edge_indexes_set.add(pair_to_index[pair])
    for i in range(1, len(sequence_route)):
        node_a = sequence_route[i-1]
        node_b = sequence_route[i]
        cur_edge_pair = (min(node_a, node_b), max(node_a, node_b))
        used_edge_indexes.append(pair_to_index[cur_edge_pair])
    logger.info("Testing route with node sequence : %s, indexes of used edges : %s" % (sequence_route, used_edge_indexes))
    src_node = sequence_route[0]
    dst_node = sequence_route[-1]
    if running_mode is MpeRoutePredictionMode.simple:
        cnf_filename = "%s_src_and_dst_evid.cnf" % (sdd_filename_prefix)
        construct_cnf(node_to_edge_indexes[src_node], node_to_edge_indexes[dst_node], [], cnf_filename, variable_size)
        cmd = "%s --mpe_query --cnf_evid %s %s %s" % (inference_binary, cnf_filename, learned_psdd_filename, learned_vtree_filename)
        logger.debug("Running command : %s" % cmd)
        output = subprocess.check_output(shlex.split(cmd))
        mpe_result = ParseMpeOutput(output)
        plot_filename = "%s_src_and_dst.png" % sdd_filename_prefix
        plot_mpe_prediction(index_to_tuples, node_locations, mpe_result, [], used_edge_indexes, src_node, dst_node, plot_filename)
        if distance_metric is DistanceMetric.dsn:
            return [CalculateDSN(used_edge_indexes, mpe_result.intersection(edge_indexes_set))]
        elif distance_metric is DistanceMetric.route_length:
            return [CalculateRouteLengthDistance(mpe_result.intersection(edge_indexes_set), used_edge_indexes, index_to_tuples, node_locations)]
        else:
            assert distance_metric is DistanceMetric.hausdorff
            return [CalculateHausdorffDistance(used_edge_indexes, mpe_result.intersection(edge_indexes_set), index_to_tuples, node_locations)]
    elif running_mode is MpeRoutePredictionMode.step_by_step:
        edges_evid = []
        mpe_result = None
        distances = []
        for i in range(0, len(sequence_route)-1):
            logger.info("Making prediction with used edges: %s" % edges_evid)
            succeed = False
            attempt_index = 0
            while not succeed:
                cnf_filename = "%s_%s_%s_evid.cnf" % (sdd_filename_prefix, i, attempt_index)
                construct_cnf(node_to_edge_indexes[src_node], node_to_edge_indexes[dst_node], edges_evid, cnf_filename, variable_size)
                cmd = "%s --mpe_query --cnf_evid %s %s %s" % (inference_binary, cnf_filename, learned_psdd_filename, learned_vtree_filename)
                logger.debug("Running command : %s" % cmd)
                output = subprocess.check_output(shlex.split(cmd))
                mpe_result = ParseMpeOutput(output)
                if mpe_result is None:
                    edges_evid = edges_evid[1:]
                    continue
                else:
                    succeed = True
                    break
            assert mpe_result is not None
            plot_filename = "%s_%s.png" % (sdd_filename_prefix, i)
            plot_mpe_prediction(index_to_tuples, node_locations, mpe_result, edges_evid, used_edge_indexes, src_node, dst_node, plot_filename)
            edges_evid.append(used_edge_indexes[i])
            previous_edges = set()
            for j in range(0, i):
                node_a = sequence_route[j]
                node_b = sequence_route[j+1]
                node_pair = (min(node_a, node_b), max(node_a, node_b))
                previous_edges.add(pair_to_index[node_pair])
            mpe_remaining_route = set()
            actual_remaining_route = set()
            for edge_index in mpe_result:
                if edge_index in edge_indexes_set and edge_index not in previous_edges:
                    mpe_remaining_route.add(edge_index)
            for j in range(i,len(sequence_route)-1):
                node_a = sequence_route[j]
                node_b = sequence_route[j+1]
                node_pair = (min(node_a, node_b), max(node_a, node_b))
                actual_remaining_route.add(pair_to_index[node_pair])
            connected_remaining_route = FindConnectedPath(mpe_remaining_route, sequence_route[i], index_to_tuples)
            if len(connected_remaining_route) == 0 :
                mpe_remaining_route = FindConnectedPath(mpe_remaining_route, sequence_route[-1], index_to_tuples)
            else:
                mpe_remaining_route = connected_remaining_route
            if distance_metric is DistanceMetric.dsn:
                distances.append(CalculateDSN(actual_remaining_route, mpe_remaining_route))
            elif distance_metric is DistanceMetric.route_length:
                distances.append(CalculateRouteLengthDistance(mpe_remaining_route, actual_remaining_route, index_to_tuples, node_locations))
            else:
                assert distance_metric is DistanceMetric.hausdorff
                distances.append(CalculateHausdorffDistance(actual_remaining_route, mpe_remaining_route, index_to_tuples, node_locations))
        return distances
    else:
        assert running_mode is MpeRoutePredictionMode.half_evidence
        # generating evidence
        edge_evidence = []
        mid_point = len(sequence_route) / 2
        for i in range(0, mid_point-1):
            node_a = sequence_route[i]
            node_b = sequence_route[i+1]
            edge_pair = (min(node_a, node_b), max(node_a, node_b))
            edge_index = pair_to_index[edge_pair]
            edge_evidence.append(edge_index)
        used_edges = list(edge_evidence)
        logger.info("Making prediction with used edges: %s" % edge_evidence)
        cnf_filename = "%s_half_evid.cnf" % (sdd_filename_prefix)
        while True:
            if len(edge_evidence) == 0 and mid_point > 1:
                src_node = sequence_route[mid_point-1]
            construct_cnf(node_to_edge_indexes[src_node], node_to_edge_indexes[dst_node], edge_evidence, cnf_filename, variable_size)
            cmd = "%s --mpe_query --cnf_evid %s %s %s" % (inference_binary, cnf_filename, learned_psdd_filename, learned_vtree_filename)
            logger.debug("Running command : %s" % cmd)
            output = subprocess.check_output(shlex.split(cmd))
            mpe_result = ParseMpeOutput(output)
            if mpe_result is None:
                edge_evidence = edge_evidence[1:]
                continue
            else:
                break
        plot_filename = "%s_half_evid.png" % sdd_filename_prefix
        plot_mpe_prediction(index_to_tuples, node_locations, mpe_result, used_edges, used_edge_indexes, src_node, dst_node, plot_filename)
        actual_remaining_edges = set(used_edge_indexes).difference(used_edges)
        predicted_remaining_edges = FindPathBetween(mpe_result.intersection(edge_indexes_set), sequence_route[mid_point-1], sequence_route[-1], index_to_tuples)
        if distance_metric is DistanceMetric.dsn:
            return [CalculateDSN(actual_remaining_edges, predicted_remaining_edges)]
        elif distance_metric is DistanceMetric.route_length:
            return [CalculateRouteLengthDistance(predicted_remaining_edges, actual_remaining_edges, index_to_tuples, node_locations)], CalculateRouteDistance(predicted_remaining_edges, index_to_tuples, node_locations), CalculateRouteDistance(actual_remaining_edges, index_to_tuples, node_locations)
        else:
            assert distance_metric is DistanceMetric.hausdorff
            return [CalculateHausdorffDistance(actual_remaining_edges, predicted_remaining_edges, index_to_tuples, node_locations)]

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
    parser.add_option("--mpe_test", action="store_true", dest="mpe_test")
    parser.add_option("--mar_test", action="store_true", dest="mar_test")
    parser.add_option("--mpe_step", action="store_true", dest="mpe_step")
    parser.add_option("--mpe_half_evid", action="store_true", dest="mpe_half_evid")
    parser.add_option("--dsn_distance", action="store_true", dest="dsn_distance")
    parser.add_option("--hausdorff_distance", action="store_true", dest="hausdorff_distance")
    parser.add_option("--route_length_distance", action="store_true", dest="route_length_distance")
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
    if testing_routes is not None and options.mar_test:
        total_prediction = 0
        total_accurate = 0
        for idx, test_route in enumerate(testing_routes):
            cur_accurate, cur_pred = TestSingleRoute(test_route, node_to_edges, edge_to_indexes, "%s/%s" %(sdd_dir,idx), inference_binary, psdd_filename, vtree_filename, len(sbn_spec["variables"]))
            total_prediction += cur_pred
            total_accurate += cur_accurate
        print "Accurate prediction: %s, Total prediction: %s, Accuracy: %s" % (total_accurate, total_prediction, float(total_accurate)/total_prediction)
    if testing_routes is not None and options.mpe_test:
        dsns = []
        total_pred_distance = 0;
        total_actual_distance = 0
        for idx, test_route in enumerate(testing_routes):
            mpe_option = MpeRoutePredictionMode.simple
            if options.mpe_step:
                mpe_option = MpeRoutePredictionMode.step_by_step
            if options.mpe_half_evid:
                mpe_option = MpeRoutePredictionMode.half_evidence
            distance_metric = DistanceMetric.dsn
            if options.dsn_distance:
                distance_metric = DistanceMetric.dsn
            if options.hausdorff_distance:
                distance_metric = DistanceMetric.hausdorff
            if options.route_length_distance:
                distance_metric = DistanceMetric.route_length
            cur_dsn = RoutePredictionPerRoute(test_route, node_to_edges, edge_to_indexes, "%s/%s" % (sdd_dir, idx), inference_binary, psdd_filename, vtree_filename, len(sbn_spec["variables"]), mpe_option, distance_metric, hm_spec["nodes_location"])
            if distance_metric is DistanceMetric.route_length:
                total_pred_distance += cur_dsn[1]
                total_actual_distance += cur_dsn[2]
                cur_dsn = cur_dsn[0]
            logger.info("Testing route %s disimilar metrics : %s, Accumulated actual distance : %s, Accumulated predicted distance : %s" % (idx, cur_dsn, total_actual_distance, total_pred_distance))
            dsns.extend(cur_dsn)
        print "Average DSN for predicted route is : %s" % (sum(dsns)/ len(dsns))
        with open ("dsn_result.json", "w") as fp:
            json.dump(dsns,fp)
