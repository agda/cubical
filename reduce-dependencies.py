#!/usr/bin/env python

import networkx as nx
import random
import sys
from itertools import islice

def take(n, iterable):
    """Return the first n items of the iterable as a list."""
    return list(islice(iterable, n))

def makefile_to_dependency_graph():
    # Create a directed graph
    dependency_graph = nx.DiGraph()

    current_target = None
        
    for line in sys.stdin:
        line = line.strip()

        # Skip comments and empty lines
        if not line or line.startswith("#") or line.startswith(".PHONY"):
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
            
    return dependency_graph

def reachable_subgraph(G, node):
    reachable_nodes = list(nx.dfs_preorder_nodes(G, source=node))
    
    reachable_subgraph = G.subgraph(reachable_nodes)

    return reachable_subgraph

def write_reduced_makefile(makefile_path, dependency_graph):
    
    with open(makefile_path, 'w') as makefile:
        # write dependencies for all targets
        for node in dependency_graph.nodes:
            if dependency_graph.nodes[node].get('command') is None:
                if node == 'check':
                     for target, dependency in dependency_graph.out_edges(node):
                         makefile.write(f"{target}: {dependency}\n")
                     makefile.write("\n")
            else:
                makefile.write(f"{node}:\n")
                for target, dependency in dependency_graph.out_edges(node):
                    makefile.write(f"{target}: {dependency}\n")

                makefile.write(f"\t{dependency_graph.nodes[node]['command']}\n\n")
        

def print_some_info(G):
    print(G)
    print("Nodes", G.number_of_nodes())
    print("Edges", G.number_of_edges())

    if G.number_of_nodes() > 10 or G.number_of_edges() > 10:
        # Print a random selection of 10 nodes and edges
        all_nodes = list(G.nodes())
        all_edges = list(G.edges())

        random_nodes = random.sample(all_nodes, min(len(all_nodes), 10))
        random_edges = random.sample(all_edges, min(len(all_edges), 10))

        print("")
        print("Random Nodes:", [(node, G.nodes[node].get('command')) for node in random_nodes])
        print("")
        print("Random Edges:", random_edges)
    else:
        print("")
        print("Nodes:", [(node, G.nodes[node].get('command')) for node in G.nodes()])
        print("")
        print("Edges:", G.edges())
        
        
    
            
if __name__ == "__main__":
    raw_graph = makefile_to_dependency_graph()
    
    dependency_graph = nx.transitive_reduction(raw_graph) # WTF: this operation throws away node data
    for node_id, node_data in raw_graph.nodes(data=True):
        dependency_graph.nodes[node_id].update(node_data)

    write_reduced_makefile("reduced_makefile", dependency_graph) 
    
    out_degrees = dict(dependency_graph.out_degree())
    max_degree = max(out_degrees.values())
    nodes_with_max_out_degree = [node for node, degree in out_degrees.items() if degree == max_degree]
    
    subgraph=reachable_subgraph(dependency_graph, '_build/2.6.4/agda/Cubical/Algebra/Everything.agdai')

    print("Dependencies examples: ")
    print_some_info(dependency_graph)
    print("")

    print("Dependencies below something: ")
    print_some_info(subgraph)
    print("")

    print(nodes_with_max_out_degree)
    print("")
    print(take(20, out_degrees.items()))
    print("")
    print(dependency_graph.out_edges('check'))
    print(dependency_graph.out_edges('_build/2.6.4/agda/Cubical/README.agdai'))
