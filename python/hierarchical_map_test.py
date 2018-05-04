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
import hierarchical_map
import simple_graph
import hm_plot

HmNetwork = hierarchical_map.HmNetwork
HmCluster = hierarchical_map.HmCluster
Edge = simple_graph.Edge
Route = simple_graph.Route
OsmStaticMapPlotter = hm_plot.OsmStaticMapPlotter

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

def load_routes(fp):
    raw_routes = json.load(fp)
    return [Route.get_route_from_edge_list([Edge(a["x"], a["y"], a["name"]) for a in single_route]) for single_route in raw_routes]

def dump_routes(routes, fp):
    raw_routes = [[a.as_json() for a in single_route.edges] for single_route in routes]
    json.dump(raw_routes, fp)

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

class MpeResult:
    def __init__(self, mpe_route = None, used_cluster = None):
        self.mpe_route = mpe_route
        self.used_cluster = used_cluster
    @staticmethod
    def GetMpeResultFromMpeOutput(mpe_output, hm_network, sbn_spec):
        edge_index_map, cluster_index_map = hm_network.LoadVariableIndexesFromSbnSpec(sbn_spec)
        index_to_edge = {}
        index_to_cluster_name = {}
        for edge in edge_index_map:
            index_to_edge[edge_index_map[edge]] = edge
        for cluster_name in cluster_index_map:
            index_to_cluster_name[cluster_index_map[cluster_name]] = cluster_name
        lines = mpe_output.split("\n")
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
        if results is None:
            return None 
        mpe_result = MpeResult([],None)
        used_edges = []
        for variable_index in results:
            if variable_index in index_to_edge:
                used_edges.append(index_to_edge[variable_index])
            else:
                assert variable_index in index_to_cluster_name
                mpe_result.used_cluster = index_to_cluster_name[variable_index]
        mpe_result.mpe_route = Route.get_route_from_edge_list(used_edges)
        if mpe_result.used_cluster is None:
            mpe_result.used_cluster = hm_network.GetRootCluster().name
        return mpe_result
    
    def as_json(self):
        return {"mpe_route" : [e.as_json() for e in self.mpe_route.edges], "top_cluster_name": self.used_cluster}

def GenerateTrainingDataset(hm_network, sbn_spec, training_routes):
    edge_index_map, cluster_index_map = hm_network.LoadVariableIndexesFromSbnSpec(sbn_spec)
    topological_order = hm_network.TopologicalSort()
    data = {}
    data["variable_size"] = len(edge_index_map) + len(cluster_index_map)
    root_cluster = hm_network.GetRootCluster()
    data["data"] = []
    for route in training_routes:
        used_index = []
        used_nodes = set()
        for edge in route.edges:
            used_index.append(edge_index_map[edge])
            used_nodes.add(edge.x)
            used_nodes.add(edge.y)
        cur_cluster = root_cluster
        while cur_cluster.children is not None:
            involved_child_clusters = []
            for child_name in cur_cluster.children:
                child_cluster = cur_cluster.children[child_name]
                if len(child_cluster.nodes.intersection(used_nodes)) != 0:
                    involved_child_clusters.append(child_name)
            if len(involved_child_clusters) == 1:
                used_index.append(cluster_index_map[involved_child_clusters[0]])
                cur_cluster = child_cluster
            else:
                break
        data["data"].append(used_index)
    return data

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

def route_length(route, node_locations):
    route_length = sum([Haversine(node_locations[a.x], node_locations[a.y]).feet for a in route.edges])
    return route_length

# route1 - route2
def get_distance_between_routes(route_1, route_2, node_locations, distance_metric):
    if distance_metric is DistanceMetric.route_length:
        result = {}
        result["route_length"] = [route_length(route_1, node_locations), route_length(route_2, node_locations)]
        result["distance"] = result["route_length"][0] - result["route_length"][1]
        return result
    else:
        pass

def mpe_prediction_per_route(test_route, edge_to_index, index_to_edge, node_to_edges, hm_network, sbn_spec, test_filename_prefix, inference_binary, learned_psdd_filename, learned_vtree_filename, variable_size, running_mode, distance_metric, node_locations):
    logger = logging.getLogger()
    if running_mode is MpeRoutePredictionMode.simple:
        cnf_filename = "%s_src_and_dst_evid.cnf" % (test_filename_prefix)
        src_neighboring_edges = node_to_edges[test_route.src_node()]
        dst_neighboring_edges = node_to_edges[test_route.dst_node()]
        src_neighboring_edges_indexes = [edge_to_index[e] for e in src_neighboring_edges]
        dst_neighboring_edges_indexes = [edge_to_index[e] for e in dst_neighboring_edges]
        construct_cnf(src_neighboring_edges_indexes, dst_neighboring_edges_indexes, [], cnf_filename, variable_size)
        cmd = "%s --mpe_query --cnf_evid %s %s %s" % (inference_binary, cnf_filename, learned_psdd_filename, learned_vtree_filename)
        logger.debug("Running command : %s" % cmd)
        output = subprocess.check_output(shlex.split(cmd))
        mpe_result = MpeResult.GetMpeResultFromMpeOutput(output, hm_network, sbn_spec)
        prediction_filename = "%s_src_and_dst_prediction_summary.json" % (test_filename_prefix)
        prediction_summary = {"cmd": cmd, "mpe_result": mpe_result.as_json(), "evid_route":[], "actual_remaining": [e.as_json() for e in test_route.edges], "predicted_remaining": [e.as_json() for e in mpe_result.mpe_route.edges]}
        with open(prediction_summary, "w") as fp:
            json.dump(prediction_summary, fp)
        plotter = OsmStaticMapPlotter()
        plotter.DrawRoute(test_route, node_locations, "green", 10)
        plotter.DrawRoute(mpe_result.mpe_route, "red", 5)
        plotter.SaveMap("%s_src_and_dst.png" % test_filename_prefix)
        return get_distance_between_routes(mpe_result.mpe_route, test_route, node_locations, distance_metric)
    elif running_mode is MpeRoutePredictionMode.half_evidence:
        cnf_filename = "%s_half_trip_evid.cnf" % (test_filename_prefix)
        src_neighboring_edges = node_to_edges[test_route.src_node()]
        dst_neighboring_edges = node_to_edges[test_route.dst_node()]
        src_neighboring_edges_indexes = [edge_to_index[e] for e in src_neighboring_edges]
        dst_neighboring_edges_indexes = [edge_to_index[e] for e in dst_neighboring_edges]
        route_length = len(test_route.edges)
        cur_evidence_len = route_length / 2
        evidence_edges = test_route.edges[: cur_evidence_len]
        evidence_route = Route.get_route_from_edge_list(evidence_edges)
        actual_remaining_route = Route.get_route_from_edge_list(test_route.edges[cur_evidence_len:])
        predicted_remaining_route = None
        remaining_src_node = actual_remaining_route.src_node()
        remaining_dst_node = actual_remaining_route.dst_node()
        while len(evidence_edges) > 0:
            evidence_edges_indexes = [edge_to_index[e] for e in evidence_edges]
            construct_cnf(src_neighboring_edges_indexes, dst_neighboring_edges_indexes, evidence_edges_indexes, cnf_filename, variable_size)
            cmd = "%s --mpe_query --cnf_evid %s %s %s" % (inference_binary, cnf_filename, learned_psdd_filename, learned_vtree_filename)
            logger.debug("Running command : %s" % cmd)
            output = subprocess.check_output(shlex.split(cmd))
            mpe_result = MpeResult.GetMpeResultFromMpeOutput(output, hm_network, sbn_spec)
            if mpe_result is not None:
                predicted_remaining_route = mpe_result.mpe_route.get_route_between(remaining_src_node, remaining_dst_node)
                break;
            else:
                evidence_edges = evidence_edges[1:]
        if predicted_remaining_route is None:
            remaining_src_node_neighboring_edges = node_to_edges[remaining_src_node]
            remaining_src_node_neighboring_edges_indexes = [edge_to_index[e] for e in remaining_src_node_neighboring_edges]
            remaining_dst_node_neighboring_edges = node_to_edges[remaining_dst_node]
            remaining_dst_node_neighboring_edges_indexes = [edge_to_index[e] for e in remaining_dst_node_neighboring_edges]
            construct_cnf(remaining_src_node_neighboring_edges_indexes, remaining_dst_node_neighboring_edges_indexes, [], cnf_filename, variable_size)
            cmd = "%s --mpe_query --cnf_evid %s %s %s" % (inference_binary, cnf_filename, learned_psdd_filename, learned_vtree_filename)
            logger.debug("Running command : %s" % cmd)
            output = subprocess.check_output(shlex.split(cmd))
            mpe_result = MpeResult.GetMpeResultFromMpeOutput(output, hm_network, sbn_spec)
            assert mpe_result is not None
            predicted_remaining_route = mpe_result.mpe_route
        prediction_summary = {"cmd": cmd, "mpe_result": mpe_result.as_json(), "evid_route":evidence_route.as_json(), "evid_after_retraction": [e.as_json() for e in evidence_edges], "actual_remaining": actual_remaining_route.as_json(), "predicted_remaining": predicted_remaining_route.as_json()}
        with open("%s_half_trip_prediction_summary.json" % test_filename_prefix , "w") as fp:
            json.dump(prediction_summary, fp)
        plotter = OsmStaticMapPlotter()
        plotter.DrawRoute(evidence_route, node_locations, "black", 5)
        plotter.DrawRoute(actual_remaining_route, node_locations, "green", 10)
        plotter.DrawRoute(predicted_remaining_route, node_locations, "red", 5)
        plotter.SaveMap("%s_half_trip.png" % test_filename_prefix)
        return get_distance_between_routes(predicted_remaining_route, actual_remaining_route, node_locations, distance_metric)
    else:
        return None

def RoutePredictionPerRoute(test_route, node_to_edge_indexes, edge_index_map, sdd_filename_prefix, inference_binary, learned_psdd_filename, learned_vtree_filename, variable_size, running_mode, distance_metric, node_locations):
    logger = logging.getLogger()
    sequence_route = sequence_path(test_route)
    used_edge_indexes = []
    index_to_tuples = {}
    edge_indexes_set = set()
    for edge in edge_index_map:
        index_to_tuples[edge_index_map[edge]] = edge 
        edge_indexes_set.add(edge_index_map[edge])
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
            #plot_filename = "%s_%s.png" % (sdd_filename_prefix, i)
            #plot_mpe_prediction(index_to_tuples, node_locations, mpe_result, edges_evid, used_edge_indexes, src_node, dst_node, plot_filename)
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
    parser.add_option("--test_dir", action="store", type="string", dest="test_dir")
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
    parser.add_option("--do_not_train", action="store_true", dest="do_not_train", default=False)
    (options,args) = parser.parse_args()
    logging.basicConfig(level=logging.INFO)
    logger = logging.getLogger()
    if len(args) == 0:
        parser.print_usage()
        sys.exit(1)
    with open (args[0], "r") as fp:
        hm_spec = json.load(fp)
        hm_spec = byteify(hm_spec)
    node_locations = hm_spec["nodes_location"]
    network = HmNetwork.ReadHmSpec(hm_spec)
    if options.seed:
        random.seed(int(options.seed))
    test_dir = None
    if options.test_dir:
        test_dir = options.test_dir +"/"
    else:
        logger.info("test_dir is not provided, tmp is used")
        test_dir = "/tmp"
    training_routes = None
    testing_routes = None
    if options.data:
        logger.info("Loading data %s" % options.data)
        data_filename = options.data
        with open (data_filename, "r") as fp:
            data = load_routes(fp)
        random.shuffle(data)
        if options.test_size:
            test_size = int(options.test_size)
        else:
            test_size = len(data) / 10
        training_size = len(data) - test_size
        training_routes = data[:training_size]
        testing_routes = data[training_size:]
        training_routes_filename = "%s/training.json" % test_dir
        testing_routes_filename = "%s/testing.json" % test_dir
        with open(training_routes_filename, "w") as fp:
            dump_routes(training_routes, fp)
        with open(testing_routes_filename, "w") as fp:
            dump_routes(testing_routes, fp)
    if options.train_test_split:
        logger.info("Loading training and testing data. Data is ignored if provided")
        train_filename = options.train_test_split[0]
        test_filename = options.train_test_split[1]
        with open (train_filename, "r") as fp:
            training_routes = load_routes(fp)
        with open (test_filename, "r") as fp:
            testing_routes = load_routes(fp)
    if options.test_size:
        test_size = int(options.test_size)
    sbn_spec = None
    sbn_filename = None
    if options.sbn_spec:
        sbn_filename = options.sbn_spec
        with open(options.sbn_spec, "r") as fp:
            sbn_spec = json.load(fp)
    else:
        logging.info("Compiling SBN")
        sbn_spec = network.CompileToSBN(test_dir)
        sbn_filename = "%s/sbn.json" % test_dir
        with open (sbn_filename, "w") as fp:
            json.dump(sbn_spec, fp, indent=2)
    if not options.compiled_sbn:
        psdd_filename = "%s/sbn.psdd" % test_dir
        vtree_filename = "%s/sbn.vtree" % test_dir
        if options.sbn_compiler:
            sbn_compiler = options.sbn_compiler
        else:
            sbn_compiler = "structured_bn_main"
        cmd = "%s --psdd_filename %s --vtree_filename %s" % (sbn_compiler, psdd_filename, vtree_filename)
        if training_routes and not options.do_not_train:
            training_data_filename = "%s/training_sparse_routes.json" % test_dir
            training_sparse_data = GenerateTrainingDataset(network, sbn_spec, training_routes)
            with open (training_data_filename, "w") as fp:
                json.dump(training_sparse_data, fp)
            cmd += " --sparse_learning_dataset %s" % training_data_filename
        cmd += " %s" % sbn_filename
        logger.info("Compiling sbn with commond : %s" % cmd)
        subprocess.call(shlex.split(cmd))
    else:
        psdd_filename = options.compiled_sbn[0]
        vtree_filename = options.compiled_sbn[1]
        logger.info("Load compiled psdd with filenames %s %s" % (psdd_filename, vtree_filename))
    psdd_inference = "psdd_inference"
    if options.psdd_inference:
        psdd_inference = options.psdd_inference
    if options.mpe_test and testing_routes:
        edge_index_map, cluster_index_map = network.LoadVariableIndexesFromSbnSpec(sbn_spec)
        variable_size = len(edge_index_map) + len(cluster_index_map)
        index_to_edge = {}
        node_to_edges = {}
        for edge in edge_index_map:
            index_to_edge[edge_index_map[edge]] = edge
            node_to_edges.setdefault(edge.x, []).append(edge)
            node_to_edges.setdefault(edge.y, []).append(edge)
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
        distances = []
        for idx, test_route in enumerate(testing_routes):
            result = mpe_prediction_per_route(test_route, edge_index_map, index_to_edge, node_to_edges, network, sbn_spec, "%s/%s"%(test_dir, idx), psdd_inference, psdd_filename, vtree_filename, variable_size, mpe_option, distance_metric, node_locations)
            logger.info("Make prediction for %s th test route %s with accuracy result %s" % (idx, test_route.edges, result))
            distances.append(result)
        print "Averaged Distance %s " % (sum([a["distance"] for a in distances])/ len(distances))
        if distance_metric is DistanceMetric.route_length:
            print "Total actual route length %s, Total predicted route length %s" % (sum([a["route_length"][1] for a in distances]), sum([a["route_length"][0] for a in distances]))
            difference_percent = [(a["route_length"][0]-a["route_length"][1])/a["route_length"][1] for a in distances]
            print "Average percentage difference %s " % (sum(difference_percent)/len(difference_percent))
