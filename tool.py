# find Cubical/ -type f | grep 'agda$' > agda-files
# agda Cubical/Cohomology/EilenbergMacLane/Rings/RP2wedgeS1.agda --dependency-graph=deps

import pygraphviz as pgv
import networkx as nx
import re

timings = {}
pattern = re.compile(r"^(.+?)\s+(\d+)ms$")

def load_timings():
    file = open("timings2", "r")

    for line in file:
        line = line.strip()
        match = pattern.match(line)
        key, time = match.groups()
        timings[key] = int(time)

def find_longest_path(dot_file):
    G = nx.DiGraph(pgv.AGraph(dot_file))
    path = nx.dag_longest_path(G)
    node_labels = {node: data.get('label', node) for node, data in G.nodes(data=True)}
    path_labels = [node_labels.get(node) for node in path]
    
    print(f"longest path: {path_labels}")
    times = [timings.get(node) for node in path_labels if timings.get(node) is not None]
    print(sum(times))

if __name__ == "__main__":
    import sys
    load_timings()
    find_longest_path(sys.argv[1])
    
