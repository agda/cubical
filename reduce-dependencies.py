#!/usr/bin/env python

import networkx as nx
import random
import sys

# import matplotlib.pyplot as plt

def makefile_to_dependency_graph():
    # Create a directed graph
    dependency_graph = nx.DiGraph()

    current_target = None
        
    for line in sys.stdin:
        line = line.strip()

        # Skip comments and empty lines
        if line.startswith("#") or not line:
            continue

        # Detect targets in Makefile lines
        if line.endswith(":"):
            # this line contains a target without dependency information
            target = line[:-1].strip()
            dependency_graph.add_node(target, command = None)
            current_target = target
        elif ":" in line:
            target , dependency = line.split(':')
            target = target.strip()
            dependency = dependency.strip()
            
            dependency_graph.add_edge(target, dependency)
            current_target = target
        elif "AGDA" in line:
            # this relies on the wild guess, that a line with build command contains 'AGDA'
            if current_target is None:
                raise Exception(f"current_target None while trying to set build command")
            if 'command' in dependency_graph.nodes[current_target]:
              data = dependency_graph.nodes[current_target]['command']
              raise Exception(f"data already set: {data}")

            dependency_graph.nodes[current_target]['command'] = line.strip()
            print(f"command added: {line.strip()} to {current_target}")
            print(f"node data: {dependency_graph.nodes[current_target]}")
            
    return dependency_graph


def write_reduced_makefile(makefile_path, dependency_graph):
    
    with open(makefile_path, 'w') as makefile:
        # write dependencies for the target 'check':
        for node in dependency_graph.nodes:
            if dependency_graph.nodes[node].get('command') is None:
                # not a real target
                continue
            
            makefile.write(f"check: {node}\n")

        makefile.write("\n")
            
        # write dependencies for all agdai-targets
        for node in dependency_graph.nodes:
            if dependency_graph.nodes[node].get('command') is None:
                # not a real target
                continue

            makefile.write(f"{node}:\n")
            for source, target in dependency_graph.edges(node):
                makefile.write(f"{source}: {target}\n")

            makefile.write(f"\t{dependency_graph.nodes[node]['command']}\n\n")
        
        
if __name__ == "__main__":
    raw_graph = makefile_to_dependency_graph()
    
    print("Original graph:")
    print("Nodes", raw_graph.number_of_nodes())
    print("Edges", raw_graph.number_of_edges())
    
    dependency_graph = nx.transitive_reduction(raw_graph) # WTF: this operation throws away node data
    for node_id, node_data in raw_graph.nodes(data=True):
        dependency_graph.nodes[node_id].update(node_data)
        
    print("Reduced graph:")
    print("Nodes", dependency_graph.number_of_nodes())
    print("Edges", dependency_graph.number_of_edges())

    # Print a random selection of 10 nodes and edges
    all_nodes = list(dependency_graph.nodes())
    all_edges = list(dependency_graph.edges())

    random_nodes = random.sample(all_nodes, min(len(all_nodes), 10))
    random_edges = random.sample(all_edges, min(len(all_edges), 10))
    
    print("Random Nodes:", [(node, dependency_graph.nodes[node].get('command')) for node in random_nodes])
    print("Random Edges:", random_edges)

    write_reduced_makefile("reduced_makefile", dependency_graph) # so far only raw_graph, because the reduced does not contain the build commands
    
