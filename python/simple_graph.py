import math

class SimpleGraph:

    def __init__(self,nodes,edges):
        self.nodes = nodes
        self.edges = edges
        self.print_all = False
        #self.graph_bounds = None

    def bounds(self):
        #if self.graph_bounds is not None: return self.graph_bounds

        lats = [ self.nodes[node][0] for node in self.nodes ]
        lons = [ self.nodes[node][1] for node in self.nodes ]

        rnd_up = lambda x: SimpleGraph.my_round(x,up=True)
        rnd_dn = lambda x: SimpleGraph.my_round(x,up=False)
        min_lat,max_lat = rnd_dn(min(lats)),rnd_up(max(lats))
        min_lon,max_lon = rnd_dn(min(lons)),rnd_up(max(lons))
        self.graph_bounds = (min_lat,max_lat,min_lon,max_lon)
        return self.graph_bounds

    @staticmethod    
    def my_round(number,up=True,digits=2):
        mult = 10.0**digits
        roundf = math.ceil if up else math.floor
        number = roundf(number * mult) / mult
        return number

    def __repr__(self):
        st = []

        min_lat,max_lat,min_lon,max_lon = self.bounds()
        st.append( "c BOUNDS:" )
        st.append( "c         %.2f" % max_lat )
        st.append( "c %.2f       %.2f" % (min_lon,max_lon) )
        st.append( "c         %.2f" % min_lat )

        if self.print_all is False: return "\n".join(st)

        st.append( "c NODES (%d):" % len(self.nodes) )
        for node in sorted(self.nodes.keys()):
            loc = self.nodes[node]
            st.append( "%d %.5f %.5f" % (node,loc[0],loc[1]) )

        st.append( "c EDGES (%d):" % len(self.edges) )
        for edge in self.edges:
            x,y,name = self.edges[edge]
            st.append( "%d %d %s" % (x,y,name) )

        return "\n".join(st)

def zero():
    return 0

def fix_sgraph(sgraph): #AC: should be fixed earlier?
    for index in sgraph.edges.keys():
        x,y,name = sgraph.edges[index]
        if x == y:
            sgraph.edges.pop(index)
