from staticmap import CircleMarker, Line, StaticMap
from matplotlib import cm
import simple_graph

Route = simple_graph.Route

class Plotter:
    def __init__(self):
        pass
    def DrawRoute(self, route, node_locations, color, width):
        for edge in route.edges:
            self.DrawLine(node_locations[edge.x],node_locations[edge.y], color, width)

    def DrawMpe(self, mpe_output, index_to_edges, node_locations, color, width):
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
        for edge_index in results:
            if edge_index in index_to_edges:
                #need to plot this
                cur_edge = index_to_edges[edge_index]
                self.DrawLine(node_locations[cur_edge.x], node_locations[cur_edge.y], color, width)
        return results

    def DrawHierarchicalMap(self, hm, cluster_name, node_locations, size):
        cur_cluster = hm.clusters[cluster_name]
        children = cur_cluster.children.values()
        step = 255/ len(children)
        for idx, child in enumerate(children):
            cur_level = idx * step
            cur_color =  '#%02x%02x%02x' % tuple(int(a*255) for a in cm.jet(cur_level)[:-1])
            for node in child.nodes:
                self.DrawPoint(node_locations[node], cur_color, size)

class OsmStaticMapPlotter(Plotter):
    def __init__(self, width = 2000, height = 1500):
        Plotter.__init__(self)
        self.static_map_ = StaticMap(width, height, url_template="http://a.tile.osm.org/{z}/{x}/{y}.png")
    def DrawLine(self, src_gps, dst_gps, color, width):
        self.static_map_.add_line(Line(((src_gps[1], src_gps[0]), (dst_gps[1], dst_gps[0])), color, width))
    def DrawPoint(self, node_gps, color, size):
        self.static_map_.add_marker(CircleMarker((node_gps[1], node_gps[0]), color, size))
    def SaveMap(self, map_filename):
        image = self.static_map_.render()
        image.save(map_filename)

if __name__ == "__main__":
    import sys, json
    from hierarchical_map import HmNetwork
    mpe_output_filename = sys.argv[1]
    sbn_spec_filename = sys.argv[2]
    hm_spec_filename = sys.argv[3]
    cluster_name = sys.argv[4]
    with open (hm_spec_filename, "r") as fp:
        hm_spec = json.load(fp)
    with open (sbn_spec_filename, "r") as fp:
        sbn_spec = json.load(fp)
    hm = HmNetwork.ReadHmSpec(hm_spec)
    edges_map, cluster_map = hm.LoadVariableIndexesFromSbnSpec(sbn_spec)
    index_to_edge = {}
    for edge in edges_map:
        index_to_edge[edges_map[edge]] = edge
    plotter = OsmStaticMapPlotter()
    with open(mpe_output_filename, "r") as fp:
        mpe_output = fp.read()
    results = plotter.DrawMpe(mpe_output, index_to_edge, hm_spec["nodes_location"], "red", 5)
    plotter.DrawHierarchicalMap(hm, cluster_name, hm_spec["nodes_location"], 5)
    children = hm.clusters[cluster_name].children.values()
    for child in children:
        print ("%s : %s" % (child.name, cluster_map[child.name] in results))
    plotter.SaveMap("test.png")
    print results
    p = [str(index_to_edge[i]) for i in results if i in index_to_edge]
    with open("edges.json", "w") as fp:
        json.dump(p, fp)
