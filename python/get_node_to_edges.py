import json
import hierarchical_map
HmNetwork = hierarchical_map.HmNetwork

if __name__ == "__main__":
    import sys
    hm_spec_filename = sys.argv[1]
    sbn_spec_filename = sys.argv[2]
    node_to_edge_index_filename = sys.argv[3]
    with open(hm_spec_filename, "r") as fp:
        hm_spec = json.load(fp)
    with open(sbn_spec_filename, "r") as fp:
        sbn_spec = json.load(fp)
    hm_network = HmNetwork.ReadHmSpec(hm_spec)
    edge_to_indexes,_ = hm_network.LoadVariableIndexesFromSbnSpec(sbn_spec)
    node_to_edge_indexes = {}
    for e in edge_to_indexes:
        node_to_edge_indexes.setdefault(str(e.x), []).append(edge_to_indexes[e])
        node_to_edge_indexes.setdefault(str(e.y), []).append(edge_to_indexes[e])
    with open(node_to_edge_index_filename, "w") as fp:
        json.dump(node_to_edge_indexes, fp)
