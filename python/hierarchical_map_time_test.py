import optparse
import logging
import subprocess, shlex
import re
import hierarchical_map_test
import hierarchical_map
import uai_hierarchical_map
import json
import random
import time
import os, errno
import logging
from multiprocessing import Pool
import itertools
import numpy as np

MpeResult = hierarchical_map_test.MpeResult
construct_cnf = hierarchical_map_test.construct_cnf
OptionParser = optparse.OptionParser
HmNetwork = hierarchical_map.HmNetwork
UaiHmNetwork = uai_hierarchical_map.HmNetwork
byteify = hierarchical_map_test.byteify

def generate_hm_specs_from_osm(graph_hopper_map_filename, osm_filename, base_dir, iterations, seed = 0):
    logger = logging.getLogger()
    hm_spec_filenames = []
    directory_per_iterations = []
    for i in range(0, iterations):
        cur_seed = seed + i
        new_dir = "%s/iteration_%s/" % (base_dir, i)
        hm_spec_filename = "%s/hierarchical_map.json" % new_dir
        try:
            logger.info ("Try to create directory %s" % new_dir)
            os.makedirs(new_dir)
        except OSError as e:
            if e.errno != errno.EEXIST:
                raise
            else:
                logger.info("Directory %s exists" % new_dir)
        cmd = "jython %s --output_binary_hierarchy %s -m %s -s %s" % (graph_hopper_map_filename, hm_spec_filename, osm_filename, cur_seed)
        logger.info("Running cmd %s " % cmd)
        try:
            subprocess.call(shlex.split(cmd))
        except:
            logging.warning("Cannot create hm_spec %s" % cmd)
            continue
        directory_per_iterations.append(new_dir)
        hm_spec_filenames.append(hm_spec_filename)
    return {"directories" : directory_per_iterations, "hm_spec_filenames": hm_spec_filenames}

def generate_new_sbn_file(hm_spec_filename, iteration_dir):
    logger = logging.getLogger()
    logger.info ("Start generating sbn files for new hierarchical map")
    new_sbn_dir = "%s/new_sbn_sdds/" % iteration_dir
    try:
        logging.info ("Try to create directory %s" % new_sbn_dir)
        os.makedirs(new_sbn_dir)
    except OSError as e:
        if e.errno != errno.EEXIST:
            raise
        else:
            logging.info("Directory %s exists" % new_sbn_dir)
    with open (hm_spec_filename, "r") as fp:
        hm_spec = json.load(fp)
        hm_spec = byteify(hm_spec)
    hm = HmNetwork.ReadHmSpec(hm_spec)
    sbn_spec = hm.CompileToSBN(os.path.abspath(new_sbn_dir).encode('utf-8'))
    sbn_spec_filename = "%s/new_sbn.json" % iteration_dir
    with open (sbn_spec_filename, "w") as fp:
        json.dump(sbn_spec, fp)
    return sbn_spec_filename

def generate_uai_sbn_file(hm_spec_filename, iteration_dir):
    logger = logging.getLogger()
    logger.info ("Start generating sbn files for uai hierarchical map")
    uai_sbn_dir = "%s/uai_sbn_sdds/" % iteration_dir
    try:
        logging.info ("Try to create directory %s" % uai_sbn_dir)
        os.makedirs(uai_sbn_dir)
    except OSError as e:
        if e.errno != errno.EEXIST:
            raise
        else:
            logging.info("Directory %s exists" % uai_sbn_dir)
    with open (hm_spec_filename, "r") as fp:
        hm_spec = json.load(fp)
        hm_spec = byteify (hm_spec)
    hm = UaiHmNetwork.ReadHmSpec(hm_spec)
    sbn_spec = hm.CompileToSBN(os.path.abspath(uai_sbn_dir).encode('utf-8'))
    sbn_spec_filename = "%s/uai_sbn.json" % iteration_dir
    with open (sbn_spec_filename, "w") as fp:
        json.dump(sbn_spec, fp)
    return sbn_spec_filename

def get_node_to_edge_indexes_from_edge_to_indexes (edge_to_indexes):
    node_to_edge_indexes = {}
    for e in edge_to_indexes:
        node_to_edge_indexes.setdefault(e.x, []).append(edge_to_indexes[e])
        node_to_edge_indexes.setdefault(e.y, []).append(edge_to_indexes[e])
    return node_to_edge_indexes

def generate_src_and_dst_cnfs (hm_spec_filename, new_sbn_filename, uai_sbn_filename, iteration_dir, number_of_evidence):
    with open (hm_spec_filename, "r") as fp:
        hm_spec = json.load(fp)
    with open (new_sbn_filename, "r") as fp:
        new_sbn_spec = json.load(fp)
    with open (uai_sbn_filename, "r") as fp:
        uai_sbn_spec = json.load(fp)
    new_hm_network = HmNetwork.ReadHmSpec(hm_spec)
    uai_hm_network = UaiHmNetwork.ReadHmSpec(hm_spec)
    new_hm_network_edges_to_index,_ = new_hm_network.LoadVariableIndexesFromSbnSpec(new_sbn_spec)
    uai_hm_network_edges_to_index = uai_hm_network.LoadVariableIndexesFromSbnSpec(uai_sbn_spec)
    new_hm_network_node_to_edge_indexes = get_node_to_edge_indexes_from_edge_to_indexes(new_hm_network_edges_to_index)
    uai_hm_network_node_to_edge_indexes = get_node_to_edge_indexes_from_edge_to_indexes(uai_hm_network_edges_to_index)
    new_hm_network_evid_filenames = []
    uai_hm_network_evid_filenames = []
    new_hm_network_root = new_hm_network.GetRootCluster()
    new_hm_left_child_nodes = new_hm_network_root.children[new_hm_network_root.children.keys()[0]].nodes
    new_hm_right_child_nodes = new_hm_network_root.children[new_hm_network_root.children.keys()[1]].nodes
    for i in range(0, number_of_evidence):
        src_node = random.sample(new_hm_left_child_nodes, 1)[0]
        dst_node = random.sample(new_hm_right_child_nodes, 1)[0]
        cnf_filename = "%s/new_%s.evid" % (iteration_dir, i)
        new_hm_network_evid_filenames.append(cnf_filename)
        construct_cnf(new_hm_network_node_to_edge_indexes[src_node], new_hm_network_node_to_edge_indexes[dst_node], [], cnf_filename, len(new_sbn_spec["variables"]))
        cnf_filename = "%s/uai_%s.evid" % (iteration_dir, i)
        uai_hm_network_evid_filenames.append(cnf_filename)
        construct_cnf(uai_hm_network_node_to_edge_indexes[src_node], uai_hm_network_node_to_edge_indexes[dst_node], [], cnf_filename, len(uai_sbn_spec["variables"]))
    return {"psdd_inference_evid_filenames":new_hm_network_evid_filenames, "message_passing_evid_filenames":uai_hm_network_evid_filenames, "iteration_dir" : iteration_dir}

def compile_single_sbn_with_random_parameter(new_sbn_filename, hierarchy_iteration_index, random_iteration_index, sbn_compiler, iteration_dir):
    psdd_filename = "%s/sbn_%s.psdd" % (iteration_dir, random_iteration_index)
    vtree_filename = "%s/sbn_%s.vtree" % (iteration_dir, random_iteration_index)
    cmd = "%s --psdd_filename %s --vtree_filename %s -s %s --sample_parameter %s" % (sbn_compiler, psdd_filename, vtree_filename, random_iteration_index, new_sbn_filename)
    output = subprocess.check_output(shlex.split(cmd))
    lines = output.split("\n")
    ms_spent = None
    for line in lines:
        line = line.strip()
        if line.find("Compile Network Time") != -1:
            time_tok = line.split(":")[-1].strip()
            p = re.match(r"([0-9]*) ms", time_tok)
            ms_spent = int(p.group(1))
    return {"psdd_filename": psdd_filename, "vtree_filename": vtree_filename, "compile_network_time":ms_spent, "hierarchy_iteration_index": hierarchy_iteration_index, "iteration_dir":iteration_dir, "random_iteration_index":random_iteration_index}


def compile_single_sbn_with_random_parameter_helper(a):
    return compile_single_sbn_with_random_parameter(*a)

def compile_new_sbn_with_random_parameter(new_sbn_filename, number_of_iterations, sbn_compiler, iteration_dir, cores):
    p = Pool(cores)
    result = p.map(compile_single_sbn_with_random_parameter_helper, [(new_sbn_filename, i, sbn_compiler, iteration_dir) for i in range(0, number_of_iterations)])
    return result

def single_run(psdd_inference_binary, message_passing_binary, new_sbn_psdd_filename, new_sbn_vtree_filename, new_cnf_filename, uai_sbn_seed, uai_sbn_filename, uai_cnf_filename):
    logger = logging.getLogger()
    psdd_inf_cmd = "%s --mpe_query --cnf_evid %s %s %s" % (psdd_inference_binary, new_cnf_filename, new_sbn_psdd_filename, new_sbn_vtree_filename)
    logger.info("Running cmd %s " % psdd_inf_cmd)
    output =subprocess.check_output(shlex.split(psdd_inf_cmd))
    lines = output.split("\n")
    ms_spent = None
    for line in lines:
        line = line.strip()
        if line.find("Query Time") != -1:
            time_tok = line.split(":")[-1].strip()
            p = re.match(r"([0-9]*) ms", time_tok)
            ms_spent = int(p.group(1))
    new_inf_time = ms_spent
    cmd = "%s --sample_parameter --mpe_query --seed %s --cnf_evid %s %s" % (message_passing_binary, uai_sbn_seed, uai_cnf_filename, uai_sbn_filename)
    logger.info("Running cmd %s " % cmd)
    output = subprocess.check_output(shlex.split(cmd))
    ms_spent = None
    lines = output.split("\n")
    for line in lines:
        line = line.strip()
        if line.find("Message Passing Time") != -1:
            time_tok = line.split(":")[-1].strip()
            p = re.match(r"([0-9]*) ms", time_tok)
            ms_spent = int(p.group(1))
    uai_inf_time = ms_spent
    return {"psdd_inference_time": new_inf_time, "message_passing_time": uai_inf_time, "psdd_inf_cmd" : psdd_inf_cmd, "message_passing_inf_cmd" : cmd}

def single_run_helper(args):
    return single_run(*args)

if __name__ == "__main__":
    usage = "usage: %prog [options]"
    parser = OptionParser(usage=usage)
    parser.add_option("-o", "--osm", action="store", type="string", dest="osm")
    parser.add_option("--graph_hopper_map_script", action="store", type="string", dest="graph_hopper_map_script")
    parser.add_option("--sbn_compiler", action="store", type="string", dest="sbn_compiler")
    parser.add_option("--psdd_inference_binary", action="store", type="string", dest="psdd_inference_binary")
    parser.add_option("--message_passing_binary", action="store", type="string", dest="message_passing_binary")
    parser.add_option("--directory", action="store", type="string", dest="directory")
    parser.add_option("-l", action="store", type="string", dest="l", help="Number of hierarchical clusterings sampled for this map")
    parser.add_option("-m", action="store", type="string", dest="m", help="Number of random parameter sets to sample for each SBN")
    parser.add_option("-n", action="store", type="string", dest="n", help="Number of queries to perform for each map")
    parser.add_option("--cores", type="string", dest="cores", help = "Number of cores")
    (options,args) = parser.parse_args()
    logging.basicConfig(level=logging.INFO)
    logger = logging.getLogger()
    assert options.osm
    assert options.directory
    l = int(options.l) if options.l else 5
    m = int(options.m) if options.m else 5
    n = int(options.n) if options.n else 5
    cores = int(options.cores) if options.cores else 1
    random.seed(0)
    graph_hopper_map_script = "graph_hopper_map.py"
    if options.graph_hopper_map_script:
        graph_hopper_map_script = options.graph_hopper_map_script
    sbn_compiler = "structured_bn_main"
    if options.sbn_compiler:
        sbn_compiler = options.sbn_compiler
    psdd_inference_binary = options.psdd_inference_binary if options.psdd_inference_binary else "psdd_inference_main"
    message_passing_binary = options.message_passing_binary if options.message_passing_binary else "hierarchical_main"
    result = generate_hm_specs_from_osm(graph_hopper_map_script, options.osm, options.directory, l)
    iteration_dirs = result["directories"]
    hm_spec_filenames = result["hm_spec_filenames"]
    psdd_sbn_filenames = []
    mp_sbn_filenames = []
    for i in range(0, l):
        psdd_sbn_filenames.append(generate_new_sbn_file(hm_spec_filenames[i], iteration_dirs[i]))
        mp_sbn_filenames.append(generate_uai_sbn_file(hm_spec_filenames[i], iteration_dirs[i]))
    psdd_cnfs = []
    mp_cnfs = []
    for i in range(0, l):
        cnfs = generate_src_and_dst_cnfs (hm_spec_filenames[i], psdd_sbn_filenames[i], mp_sbn_filenames[i], iteration_dirs[i], n)
        psdd_cnfs.append(cnfs["psdd_inference_evid_filenames"])
        mp_cnfs.append(cnfs["message_passing_evid_filenames"])
    arguments = []
    for i in range(0, l):
        for j in range(0, m):
            arguments.append((psdd_sbn_filenames[i], i, j, sbn_compiler, iteration_dirs[i]))
    p = Pool(cores)
    compilation_result = p.map(compile_single_sbn_with_random_parameter_helper, arguments)
    compiled_psdd_sbns = [[] for i in range(0, l)]
    compiled_times = []
    for entry in compilation_result:
        compiled_psdd_sbns[entry["hierarchy_iteration_index"]].append(entry)
        compiled_times.append(entry["compile_network_time"])
    # Running single run
    arguments = []
    for i in range(0, l):
        for j in range(0, m):
            for k in range(0, n):
                arguments.append((psdd_inference_binary, message_passing_binary, compiled_psdd_sbns[i][j]["psdd_filename"], compiled_psdd_sbns[i][j]["vtree_filename"], psdd_cnfs[i][k], j, mp_sbn_filenames[i], mp_cnfs[i][k]))
    final_result = p.map(single_run_helper, arguments)
    with open ("final_result.json", "w") as fp:
        json.dump(final_result, fp)
    psdd_times = [float(k["psdd_inference_time"]) for k in final_result]
    mp_times = [float(k["message_passing_time"]) for k in final_result]
    psdd_compilation_times = compiled_times
    print "psdd_times avg : %s std : %s" % (np.mean(psdd_times), np.std(psdd_times))
    print "message_passing_times avg : %s std : %s" % (np.mean(mp_times), np.std(mp_times))
    print "compilation time avg avg : %s std : %s" % (np.mean(psdd_compilation_times), np.std(psdd_compilation_times))
