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
        return {"__MpeResult__": True, "mpe_route" : [e.as_json() for e in self.mpe_route.edges], "top_cluster_name": self.used_cluster}
    @staticmethod
    def from_json(dct):
        if "__MpeResult__" in dct:
            assert "mpe_route" in dct
            assert "top_cluster_name" in dct
            top_cluster_name = dct["top_cluster_name"]
            mpe_route = Route.from_json(dct)
            return MpeResult(mpe_route, top_cluster_name)
        return dct

def GenerateTrainingDataset(hm_network, sbn_spec, training_routes):
    edge_index_map, cluster_index_map = hm_network.LoadVariableIndexesFromSbnSpec(sbn_spec)
    topological_order = hm_network.TopologicalSort()
    data = {}
    data["variable_size"] = len(edge_index_map) + len(cluster_index_map)
    root_cluster = hm_network.GetRootCluster()
    data["data"] = []
    num_routes_used_cluster_index = 0;
    for route in training_routes:
        used_index = []
        used_nodes = set()
        for edge in route.edges:
            used_index.append(edge_index_map[edge])
            used_nodes.add(edge.x)
            used_nodes.add(edge.y)
        cur_cluster = root_cluster
        use_cluster_index = False
        while cur_cluster.children is not None:
            involved_child_clusters = []
            for child_name in cur_cluster.children:
                child_cluster = cur_cluster.children[child_name]
                if len(child_cluster.nodes.intersection(used_nodes)) != 0:
                    involved_child_clusters.append(child_name)
            if len(involved_child_clusters) == 1:
                use_cluster_index = True
                used_index.append(cluster_index_map[involved_child_clusters[0]])
                cur_cluster = cur_cluster.children[involved_child_clusters[0]]
            else:
                break
        if use_cluster_index:
            num_routes_used_cluster_index += 1
        data["data"].append(used_index)
    print "routes used cluster index %s / %s" % (num_routes_used_cluster_index, len(training_routes))
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



def mpe_prediction_per_route(test_route, edge_to_index, index_to_edge, node_to_edges, hm_network, sbn_spec, test_filename_prefix, inference_binary, learned_psdd_filename, learned_vtree_filename, variable_size, running_mode, node_locations):
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
        prediction_summary = {"cmd": cmd, "mpe_result": mpe_result, "evid_route": Route([]), "actual_remaining": test_route, "predicted_remaining": mpe_result.mpe_route}
        plotter = OsmStaticMapPlotter()
        plotter.DrawRoute(test_route, node_locations, "green", 10)
        plotter.DrawRoute(mpe_result.mpe_route, "red", 5)
        plotter.SaveMap("%s_src_and_dst.png" % test_filename_prefix)
        return prediction_summary
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
        prediction_summary = {"cmd": cmd, "mpe_result": mpe_result, "evid_route":evidence_route, "evid_after_retraction": Route(evidence_edges) , "actual_remaining": actual_remaining_route, "predicted_remaining": predicted_remaining_route}
        plotter = OsmStaticMapPlotter()
        plotter.DrawRoute(evidence_route, node_locations, "black", 5)
        plotter.DrawRoute(actual_remaining_route, node_locations, "green", 10)
        plotter.DrawRoute(predicted_remaining_route, node_locations, "red", 5)
        plotter.SaveMap("%s_half_trip.png" % test_filename_prefix)
        return prediction_summary
    else:
        return None

class DistanceMetricsSummary:
    @staticmethod
    def from_mpe_prediction_summary(prediction_summary):
        actual_routes = []
        predicted_routes = []
        for summary in prediction_summary:
            actual_routes.append(summary["actual_remaining"])
            predicted_routes.append(summary["predicted_remaining"])
        return DistanceMetricsSummary(actual_routes, predicted_routes)

    def __init__(self, actual_routes, predicted_routes):
        self.actual_routes = actual_routes
        self.predicted_routes = predicted_routes

    @staticmethod
    def route_length(route, node_locations):
        route_length = sum([Haversine(node_locations[a.x], node_locations[a.y]).feet for a in route.edges])
        return route_length

    def get_trip_length_distance(self, node_locations):
        result = {}
        result["number_of_routes"] = len(self.actual_routes)
        actual_route_trip_length = [DistanceMetricsSummary.route_length(r, node_locations) for r in self.actual_routes]
        predicted_route_trip_length = [DistanceMetricsSummary.route_length(r, node_locations) for r in self.predicted_routes]
        result["actual_route_trip_length_sum"] = sum(actual_route_trip_length)
        result["predicted_route_trip_length_sum"] = sum(predicted_route_trip_length)
        result["total_percent_difference"] = (result["predicted_route_trip_length_sum"] - result["actual_route_trip_length_sum"])/ result["actual_route_trip_length_sum"]
        percent_differences = [(predicted_route_trip_length[i] - actual_route_trip_length[i]) / actual_route_trip_length[i] for i in range(0, len(self.actual_routes))]
        result["averaged_percent_difference"] = sum(percent_differences) / len(self.actual_routes)
        result["averaged_distance"] = (result["predicted_route_trip_length_sum"] - result["actual_route_trip_length_sum"]) / len(self.actual_routes)
        return result

    @staticmethod
    def hausdorff_distance_between(route_1, route_2, node_locations):
        sequence_1 = route_1.node_sequence()
        sequence_2 = route_2.node_sequence()
        inf_distances = []
        for node_1 in sequence_1:
            inf_distances.append(min([Haversine(node_locations[node_1], node_locations[i]).feet for i in sequence_2]))
        sup_1 = max(inf_distances)
        inf_distances = []
        for node_2 in sequence_2:
            inf_distances.append(min([Haversine(node_locations[node_2], node_locations[i]).feet for i in sequence_1]))
        sup_2 = max(inf_distances)
        return max(sup_1, sup_2)

    def get_hausdorff_distance(self, node_locations):
        number_of_routes = len(self.actual_routes)
        distances = []
        actual_trip_lengths = []
        for i in range(0, number_of_routes):
            distances.append(DistanceMetricsSummary.hausdorff_distance_between(self.predicted_routes[i], self.actual_routes[i], node_locations))
        for i in range(0, number_of_routes):
            actual_trip_lengths.append(DistanceMetricsSummary.route_length(self.actual_routes[i], node_locations))
        normalized_hausdorff_distances = [distances[i]/actual_trip_lengths[i] for i in range(0, number_of_routes)]
        average_normalized_hausdorff_distance = sum(normalized_hausdorff_distances) / number_of_routes
        result = {"number_of_routes": number_of_routes, "averaged_distance": sum(distances)/len(distances), "averaged_normalized_hausdorff_distance" : average_normalized_hausdorff_distance}
        return result
    @staticmethod
    def dsn_between(route_1, route_2):
        route_1_edges = set(route_1.edges)
        route_2_edges = set(route_2.edges)
        common = route_1_edges.intersection(route_2_edges)
        mis_match = 0
        for i in route_1_edges:
            if i not in common:
                mis_match += 1
        for i in route_2_edges:
            if i not in common:
                mis_match += 1
        total_len = len(route_1_edges) + len(route_2_edges)
        return float(mis_match) / total_len

    def get_dsn(self):
        dsns = []
        number_of_routes = len(self.actual_routes)
        for i in range(0, number_of_routes):
            cur_predicted_route = self.predicted_routes[i]
            cur_actual_route = self.actual_routes[i]
            dsns.append(DistanceMetricsSummary.dsn_between(cur_predicted_route, cur_actual_route))
        result= {"number_of_routes": number_of_routes, "averaged_dsn" : sum(dsns)/number_of_routes}
        return result

class PredictionSummaryEncoder(json.JSONEncoder):
    def default(self, obj):
        if isinstance (obj, Route):
            return obj.as_json()
        if isinstance (obj, Edge):
            return obj.as_json()
        if isinstance (obj, MpeResult):
            return obj.as_json()
        return json.JSONEncoder.default(self, obj)
    @staticmethod
    def from_json(dct):
        if "__MpeResult__" in dct:
            return MpeResult.from_json(dct)
        if "__Route__" in dct:
            return Route.from_json(dct)
        return dct

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
    parser.add_option("--prediction_summary_filename", action="store", dest="prediction_summary_filename")
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
    prediction_summary = None
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
        prediction_summary = []
        for idx, test_route in enumerate(testing_routes):
            result = mpe_prediction_per_route(test_route, edge_index_map, index_to_edge, node_to_edges, network, sbn_spec, "%s/%s"%(test_dir, idx), psdd_inference, psdd_filename, vtree_filename, variable_size, mpe_option, node_locations)
            logger.info("Make prediction for %s th test route %s with accuracy result %s" % (idx, test_route.edges, result["predicted_remaining"].edges))
            prediction_summary.append(result)
        with open ("%s/test_summary.json" % test_dir, "w") as fp:
            json.dump(prediction_summary, fp, cls=PredictionSummaryEncoder)
    if options.prediction_summary_filename:
        with open(options.prediction_summary_filename, "r") as fp:
            prediction_summary = json.load(fp, object_hook=PredictionSummaryEncoder.from_json)
    if prediction_summary and len(prediction_summary) > 0:
        distance_metric_summary =DistanceMetricsSummary.from_mpe_prediction_summary(prediction_summary)
        print "Route length distance metric is :"
        print distance_metric_summary.get_trip_length_distance(node_locations)
        print "Hausdorff distance metric is :"
        print distance_metric_summary.get_hausdorff_distance(node_locations)
        print "DSN metric is :"
        print distance_metric_summary.get_dsn()
