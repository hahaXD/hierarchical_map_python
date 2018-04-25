from staticmap import CircleMarker, Line, StaticMap
import sys, json
import string
import math

def make_color_tuple( color ):
    """
    turn something like "#000000" into 0,0,0
    or "#FFFFFF into "255,255,255"
    """
    R = color[1:3]
    G = color[3:5]
    B = color[5:7]

    R = int(R, 16)
    G = int(G, 16)
    B = int(B, 16)

    return R,G,B

def interpolate_tuple( startcolor, goalcolor, density):
    """
    Take two RGB color sets and mix them over a specified number of steps.  Return the list
    """
    # white
    startcolor = make_color_tuple(startcolor)
    goalcolor = make_color_tuple(goalcolor)
    R = startcolor[0]
    G = startcolor[1]
    B = startcolor[2]

    targetR = goalcolor[0]
    targetG = goalcolor[1]
    targetB = goalcolor[2]

    DiffR = targetR - R
    DiffG = targetG - G
    DiffB = targetB - B

    buffer = []
    iR = int(R + (DiffR * density))
    iG = int(G + (DiffG * density))
    iB = int(B + (DiffB * density))
    hR = string.replace(hex(iR), "0x", "")
    hG = string.replace(hex(iG), "0x", "")
    hB = string.replace(hex(iB), "0x", "")
    if len(hR) == 1:
        hR = "0" + hR
    if len(hB) == 1:
        hB = "0" + hB
    if len(hG) == 1:
        hG = "0" + hG
    color = string.upper("#"+hR+hG+hB)
    return color
def get_color(density):
    return interpolate_tuple("#007FFF","#FF0000", density)

def plot_mar_prediction(edge_index_to_tuples, node_locations, marginals, correct_next,  used_edges, src_node, dst_node, map_name):
    m = StaticMap(2000, 1500, url_template="http://a.tile.osm.org/{z}/{x}/{y}.png")
    for key in marginals:
        if key in edge_index_to_tuples:
            cur_marginal = marginals[key]
            edge_tuple = edge_index_to_tuples[key]
            density = math.exp(cur_marginal[1])
            src_gps = node_locations[edge_tuple[0]]
            dst_gps = node_locations[edge_tuple[1]]
            m.add_line(Line(((src_gps[1], src_gps[0]), (dst_gps[1], dst_gps[0])), get_color(density), 5))    
    for used_edge in used_edges:
        src_gps = node_locations[edge_index_to_tuples[used_edge][0]]
        dst_gps = node_locations[edge_index_to_tuples[used_edge][1]]
        m.add_line(Line(((src_gps[1], src_gps[0]), (dst_gps[1], dst_gps[0])), "black", 5))
    src_gps = node_locations[src_node]
    dst_gps = node_locations[dst_node]
    m.add_marker(CircleMarker((src_gps[1], src_gps[0]), "blue", 3))
    m.add_marker(CircleMarker((dst_gps[1], dst_gps[0]), "blue", 3))
    src_gps = node_locations[edge_index_to_tuples[correct_next][0]]
    dst_gps = node_locations[edge_index_to_tuples[correct_next][1]]
    m.add_line(Line(((src_gps[1], src_gps[0]), (dst_gps[1], dst_gps[0])), "green", 2))
    image = m.render()
    image.save(map_name)

def plot_mpe_prediction(edge_index_to_tuples, node_location, mpe_result, used_edges, total_route, src_node, dst_node, map_name):
    m = StaticMap(2000, 1500, url_template="http://a.tile.osm.org/{z}/{x}/{y}.png")
    for used_edge in used_edges:
        src_gps = node_locations[edge_index_to_tuples[used_edge][0]]
        dst_gps = node_locations[edge_index_to_tuples[used_edge][1]]
        m.add_line(Line(((src_gps[1], src_gps[0]), (dst_gps[1], dst_gps[0])), "black", 5))
    src_gps = node_locations[src_node]
    dst_gps = node_locations[dst_node]
    m.add_marker(CircleMarker((src_gps[1], src_gps[0]), "blue", 8))
    m.add_marker(CircleMarker((dst_gps[1], dst_gps[0]), "blue", 8))
    for used_edge in total_route:
        if used_edge not in used_edges:
            src_gps = node_locations[edge_index_to_tuples[used_edge][0]]
            dst_gps = node_locations[edge_index_to_tuples[used_edge][1]]
            m.add_line(Line(((src_gps[1], src_gps[0]), (dst_gps[1], dst_gps[0])), "green", 10))
    for active_variable_index in mpe_result:
        if active_variable_index in edge_index_to_tuples:
            edge_tuple = edge_index_to_tuples[active_variable_index]
            src_gps = node_locations[edge_tuple[0]]
            dst_gps = node_locations[edge_tuple[1]]
            m.add_line(Line(((src_gps[1], src_gps[0]), (dst_gps[1], dst_gps[0])), "red", 5))
    image = m.render()
    image.save(map_name)
if __name__ == "__main__":
    if len(sys.argv) < 5:
        print "Usage sbn_filename map_filename mar_filename evid_filename"
        sys.exit(1)
    m = StaticMap(2000, 1500, url_template="http://a.tile.osm.org/{z}/{x}/{y}.png")
    sbn_filename = sys.argv[1]
    map_filename = sys.argv[2]
    mar_filename = sys.argv[3]
    evid_filename = sys.argv[4]
    used_edges = []
    with open(evid_filename, "r") as fp:
        for line in fp:
            if line[0] == "p":
                continue
            toks = line.split(" ")[:-1]
            if len(toks) == 1 and int(toks[0]) > 0:
                used_edges.append(int(toks[0]))
    with open (map_filename, "r") as fp:
        map_spec = json.load(fp)
        edges = map_spec["edges"]
        node_locations = map_spec["nodes_location"]

    def IndexToEdge(sbn_spec):
        edge_index_map = {} # key is edge and value is index
        variables = sbn_spec["variables"]
        for idx, variable_name in enumerate(variables):
            index = idx + 1
            if variable_name[0] == "e":
                str_pair = variable_name.split(" ")[1][1:-1].split(",")
                node_a, node_b = (int(str_pair[0]), int(str_pair[1]))
                node_a, node_b = (min(node_a, node_b), max(node_a, node_b))
                edge_index_map[index] = (node_a, node_b)
        return edge_index_map

    with open (map_filename, "r") as fp:
        spec = json.load(fp)
        node_locations = spec["nodes_location"]
    with open (sbn_filename, "r") as fp:
        spec = json.load(fp)
        index_to_edge = IndexToEdge(spec)
    with open (mar_filename, "r") as fp:
        lines = fp.readlines()
        for line in lines:
            line = line.strip()
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
    for key in results:
        if key in index_to_edge:
            density = math.exp(results[key][1])
            src_gps = node_locations[index_to_edge[key][0]]
            dst_gps = node_locations[index_to_edge[key][1]]
            m.add_line(Line(((src_gps[1], src_gps[0]), (dst_gps[1], dst_gps[0])), get_color(density), 5))    
    for used_edge in used_edges:
        src_gps = node_locations[index_to_edge[used_edge][0]]
        dst_gps = node_locations[index_to_edge[used_edge][1]]
        m.add_line(Line(((src_gps[1], src_gps[0]), (dst_gps[1], dst_gps[0])), "black", 5))    

    image = m.render()
    image.save("map.png")

