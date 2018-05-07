from staticmap import Line, StaticMap
import sys, json

map_filename = sys.argv[1]
out_filename = sys.argv[2]
with open (map_filename, "r") as fp:
    map_spec = json.load(fp)
    edges = map_spec["edges"]
    node_locations = map_spec["nodes_location"]
m = StaticMap(800, 600, url_template="http://a.tile.osm.org/{z}/{x}/{y}.png")
for edge in edges:
    src_gps = node_locations[edge["x"]]
    dst_gps = node_locations[edge["y"]]
    m.add_line(Line(((src_gps[1], src_gps[0]), (dst_gps[1], dst_gps[0])), "blue", 1))
image = m.render()
image.save(out_filename)

