#!/usr/bin/env jython

# export CLASSPATH=lib:lib/graphhopper-web-0.8-SNAPSHOT-with-dep.jar:lib/graphhopper-map-matching-0.8-SNAPSHOT-jar-with-dependencies.jar
# http://www.openstreetmap.org/export#map=12/37.7300/-122.3190

import sys
sys.path.append("./lib/graphhopper-web-0.8-SNAPSHOT-with-dep.jar")
sys.path.append("./lib/graphhopper-map-matching-0.8-SNAPSHOT-jar-with-dependencies.jar")

import json
import Queue
import random
import glob
from collections import defaultdict
from optparse import OptionParser
import tempfile
import com.graphhopper.GraphHopper as GraphHopper
import com.graphhopper.storage.GraphHopperStorage as GraphHopperStorage
import com.graphhopper.reader.osm.GraphHopperOSM as GraphHopperOSM
import com.graphhopper.routing.util.CarFlagEncoder as CarFlagEncoder
import com.graphhopper.routing.util.EncodingManager as EncodingManager

import com.graphhopper.matching.MapMatching as MapMatching
import com.graphhopper.matching.LocationIndexMatch as LocationIndexMatch
import com.graphhopper.util.GPXEntry as GPXEntry

import java.lang.Exception
from operator import itemgetter
from simple_graph import *

def simple_graph(graph):
    nodes,edges = {},{}
    node_iterator = graph.getNodeAccess()
    edge_iterator = graph.getAllEdges()
    while edge_iterator.next():
        edge_id = edge_iterator.getEdge()
        edge_name = edge_iterator.getName()
        x,y = edge_iterator.getBaseNode(),edge_iterator.getAdjNode()

        if x not in nodes:
            lat,lon = node_iterator.getLat(x),node_iterator.getLon(x)
            nodes[x] = (lat,lon)
        if y not in nodes:
            lat,lon = node_iterator.getLat(y),node_iterator.getLon(y)
            nodes[y] = (lat,lon)

        if y < x: x,y = y,x
        edges[edge_id] = (x,y,edge_name)

    return SimpleGraph(nodes,edges)

def read_trips(filename):
    trips,last_occ = [],0
    with open(filename,'r') as f:
        for line in f.readlines():
            line = line.strip().split(' ')
            occ = int(line[2])
            if occ == 0: pass
            if occ == 1:
                if last_occ == 0: trips.append([])
                lat,lon,time = float(line[0]),float(line[1]),long(line[3])
                trips[-1].append((lat,lon,time))
            last_occ = occ

    # sort by time
    for trip in trips:
        trip.sort(key=itemgetter(2))

    return trips

def trip_to_gh(trip):
    gtrip = []
    for lat,lon,time in trip:
        entry = GPXEntry(lat,lon,time)
        gtrip.append(entry)
    return gtrip

def trips_to_gh(trips,mapMatching):
    matches = []
    for trip in trips:
        if len(trip) <= 2 :
            #print "skipping: length %d" % len(trip)
            continue
        gtrip = trip_to_gh(trip)
        try:
            match = mapMatching.doWork(gtrip).getEdgeMatches()
            matches.append(match)
        except java.lang.Exception as exception:
            #print "skipping: %s" % exception
            continue
    return matches

def parse_graph(graph):
    nodes,edges = {},{}
    edge_map = {}
    node_iterator = graph.getNodeAccess()
    edge_iterator = graph.getAllEdges()
    while edge_iterator.next():
        edge_id = edge_iterator.getEdge()
        edge_name = edge_iterator.getName()
        x,y = edge_iterator.getBaseNode(),edge_iterator.getAdjNode()

        if x not in nodes:
            lat,lon = node_iterator.getLat(x),node_iterator.getLon(x)
            nodes[x] = (lat,lon)
        if y not in nodes:
            lat,lon = node_iterator.getLat(y),node_iterator.getLon(y)
            nodes[y] = (lat,lon)

        if y < x: x,y = y,x
        edges[edge_id] = Edge(x,y, edge_id)
        if edge_map.get(x) == None:
            edge_map[x] = [y]
        else:
            edge_map[x].append(y)
        if edge_map.get(y) == None:
            edge_map[y] = [x]
        else:
            edge_map[y].append(x)

    return nodes,edges,edge_map

def split_graph(nodes, edges, edge_map):
    starting_nodes = random.sample(nodes, 2)
    node1 = starting_nodes[0]
    node2 = starting_nodes[1]
    usedNodes = set([node1, node2])
    leftNodes = set([node1])
    rightNodes= set([node2])
    q1 = Queue.Queue()
    q2 = Queue.Queue()
    q1.put(node1)
    q2.put(node2)
    while (not q1.empty()) or (not q2.empty()):
        if not q1.empty():
            nodeList1 = edge_map[q1.get()]
            for node in nodeList1:
                if node in nodes and node not in usedNodes:
                    leftNodes.add(node)
                    usedNodes.add(node)
                    q1.put(node)
        if not q2.empty():
            nodeList2 = edge_map[q2.get()]
            for node in nodeList2:
                if node in nodes and node not in usedNodes:
                    rightNodes.add(node)
                    usedNodes.add(node)
                    q2.put(node)
    assert leftNodes.isdisjoint(rightNodes)
    return leftNodes, rightNodes

#number of edges
#number of nodes

## Perform partition
def BinaryPartition(leaf_bound, nodes):
    p = Queue.Queue() # queue that contains clusters to process
    p.put((nodes, ""))
    r = Queue.Queue() # queue for deeper dive, allows saving shallower results
    leafSet = set([]) # keeps track of the set of leaves in the hierarchical tree structure
    count = leaf_bound
    totalNodes = 0
    retries = 0
    splits = 0
    clusters = {}
    while not p.empty():
        group = p.get()
        if len(group[0]) < count: # if the region is sufficiently small
            totalNodes += len(group[0]) # count the nodes at the leaf level
            clusters["root"+group[1]] = { "nodes": list(group[0]) }
            r.put(group)
        else:
            clusters["root"+group[1]] = {
                "sub_clusters":
                [ "root"+group[1]+"0", "root"+group[1]+"1"]
                }
            splits += 1
            split0, split1 = split_graph(group[0], edges, edge_map)
            while len(split0) <= len(group[0])/5 or len(split1) <= len(group[0])/5:
                retries += 1
                split0, split1 = split_graph(group[0], edges, edge_map)
            p.put((split0, group[1]+"0"))
            p.put((split1, group[1]+"1"))
    return clusters

class Cleaner:
    def __init__(self,graph):
        self.graph = graph
        self.order = [ tuple(graph.edges[i][:2]) for i in graph.edges ]
        self.edge2index = dict( (edge,i+1) for i,edge in enumerate(self.order) )

        self.neighbor_map = defaultdict(set)
        for x,y in self.order:
            self.neighbor_map[x].add(y)
            self.neighbor_map[y].add(x)

    def var_count(self):
        return len(self.graph.edges)

    def index(self,edge):
        if edge[1] < edge[0]:
            edge = edge[1],edge[0]
        return self.edge2index[edge]

    def edge(self,index):
        return self.order[index-1]

    def neighbors(self,node):
        return self.neighbor_map[node]

    def is_simple_path(self,match):
        if len(match) <= 1: return False
        visited = set()
        matchq = list(match)
        matchq.reverse()
        first,second = set(matchq[-1]),set(matchq[-2])
        x = first.intersection(second)
        if len(x) != 1: return False
        y = first.difference(x)

        cur,nxt = y.pop(),x.pop()
        visited.add(cur)
        visited.add(nxt)
        matchq.pop()

        while matchq:
            prv,cur = cur,nxt
            edge = set(matchq[-1])
            if cur not in edge: return False
            edge.remove(cur)
            nxt = edge.pop()
            if nxt in visited: return False
            visited.add(nxt)
            matchq.pop()

        return True

    @staticmethod
    def match_first_step(matchq):
        first,second = set(matchq[-1]),set(matchq[-2])
        x = first.intersection(second)
        if len(x) != 1: raise Exception
        x = first.difference(x)
        return x.pop()

    @staticmethod
    def match_next_step(matchq,last):
        if len(matchq) == 0: return None
        x,y = matchq[-1]
        if x == last:   return y
        elif y == last: return x
        else: raise Exception

    def edges_match(self,e1,e2):
        if e1 == e2: return True
        if e1 is None or e2 is None: return False
        a,b = e1
        c,d = e2
        a,b = (a,b) if a < b else (b,a)
        c,d = (c,d) if c < d else (d,c)
        return a == c and b == d

    def redundant_edge(self,edge):
        x,y = edge
        return x == y

    # remove consecutively repeating edges
    def filter_match(self,match):
        fmatch = []
        last = None
        for edge in match:
            if self.edges_match(edge,last) or self.redundant_edge(edge):
                continue
            fmatch.append(edge)
            last = edge
        return fmatch

    # a projected match is list of edge,region pairs
    def clean_matches(self, matched_edges):
        matches = [[p.as_tuple() for p in single_match] for single_match in matched_edges]
        clean_matches = []
        not_simple_count = 0
        for idx, match in enumerate(matches):
            filtered_match = self.filter_match(match) # remove redundant edges
            if not self.is_simple_path(filtered_match):
                not_simple_count += 1
                continue
            tuple_to_edge = {}
            for jdx,e in enumerate(match):
                tuple_to_edge[e] = matched_edges[idx][jdx]
            cur_matched_edges = []
            for e in filtered_match:
                cur_matched_edges.append(tuple_to_edge[e])
            clean_matches.append(cur_matched_edges)
        print "not-simple-path-count: %d/%d" % \
            (not_simple_count,len(matches))
        return clean_matches

def GenerateRoutesFromGps(graph, hopper, encoder, gps_filenames):
    locationIndex = LocationIndexMatch(graph,hopper.getLocationIndex())
    mapMatching = MapMatching(graph,locationIndex,encoder)
    total_trips = 0
    total_match = 0
    filenames = sorted(glob.glob(gps_filenames))
    print filenames
    saved_matches = []
    for i,filename in enumerate(filenames):
        print "filename: %s (%d/%d)" % (filename,i+1,len(filenames))
        trips = read_trips(filename)
        matches = trips_to_gh(trips,mapMatching)
        print "trips: %d/%d matched" % (len(matches),len(trips))
        total_trips += len(trips)
        total_match += len(matches)
        for match in matches:
            saved_match = []
            for point in match:
                edge = point.getEdgeState()
                edge_id = edge.getEdge()
                x,y = edge.getBaseNode(),edge.getAdjNode()
                saved_match.append(Edge(x,y,edge_id))
                """
                if y < x: x,y = y,x
                pair = (x,y)
                used_nodes[x] += 1
                used_nodes[y] += 1
                used_edges[pair] += 1
                saved_match.append(pair)
                """
            saved_matches.append(saved_match)
    base_graph = graph.getBaseGraph()
    sgraph = simple_graph(base_graph)
    cleaner = Cleaner(sgraph)
    clean_matches = cleaner.clean_matches(saved_matches)
    return clean_matches

if __name__ == '__main__':
    parser = OptionParser()
    parser.add_option("-d", "--temp_directory", action="store", type="string", dest="temp_directory")
    parser.add_option("-m", "--osm", action="store", type="string", dest="osm_filename")
    parser.add_option("--output_binary_hierarchy", action="store", type="string", dest="output_binary_hierarchy_filename")
    parser.add_option("-s", "--seed", action="store", type="int", dest="seed")
    parser.add_option("-l", "--leaf_bound", action="store", type="int", dest="leaf_bound")
    parser.add_option("--gps_routes", action="store", nargs=2, type="string", dest="gps_routes")
    (options, args) = parser.parse_args()
    hopper = None
    graph = None
    encoder = None
    if options.temp_directory:
        tmp_dir = options.temp_directory
    else:
        tmp_dir = tempfile.gettempdir()
    if options.seed:
        random.seed(options.seed)
    if options.osm_filename:
        filename = options.osm_filename
        hopper = GraphHopperOSM()
        hopper.setStoreOnFlush(False)
        hopper.setOSMFile(filename)
        hopper.setGraphHopperLocation(tmp_dir)
        encoder = CarFlagEncoder()
        hopper.setEncodingManager(EncodingManager([encoder]))
        hopper.setCHEnabled(False)
        hopper.importOrLoad()
        graph = hopper.getGraphHopperStorage()
    binary_hierarchy = None
    if not binary_hierarchy:
        if options.leaf_bound:
            leaf_bound = options.leaf_bound
        else:
            leaf_bound = 64
        base_graph = graph.getBaseGraph()
        node_map, edges, edge_map = parse_graph(base_graph)
        nodes = set(node_map.keys())
        clusters = BinaryPartition(leaf_bound, nodes)
        binary_hierarchy = {}
        binary_hierarchy["node_size"] = len(nodes)
        binary_hierarchy["clusters"] = clusters
        binary_hierarchy["edges"] = [i.as_json() for i in edges.values() if i.x != i.y]
        binary_hierarchy["edge_size"] = len(binary_hierarchy["edges"])
        binary_hierarchy["nodes_location"] = []
        for i in range(len(nodes)):
            binary_hierarchy["nodes_location"].append(node_map[i])
        if options.output_binary_hierarchy_filename:
            with open(options.output_binary_hierarchy_filename, "wb") as fp:
                json.dump(binary_hierarchy, fp, indent=2)
    if options.gps_routes:
        gps_routes_prefix = options.gps_routes[0]
        used_edges_filename = options.gps_routes[1]
        if hopper == None or graph == None or encoder == None:
            raise "need osm file to train gps route"
        used_edges = GenerateRoutesFromGps(graph, hopper, encoder, gps_routes_prefix)
        with open(used_edges_filename, "wb") as fp:
            json.dump([[p.as_json() for p in single_match] for single_match in used_edges], fp, indent=2)
