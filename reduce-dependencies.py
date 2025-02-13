#!/usr/bin/env python

import networkx as nx
import random
import sys
from itertools import islice

def take(n, iterable):
    """Return the first n items of the iterable as a list."""
    return list(islice(iterable, n))

def makefile_to_dependency_graph():
    # Create a directed graph for the dependencies between build targets
    # targets should be 'check' and at this point all 'agdai' files
    G = nx.DiGraph()

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
            G.add_node(target, command = None, files = [])
            current_target = target
        elif ":" in line:
            target , dependency = line.split(':')
            target = target.strip()
            dependency = dependency.strip()

            if dependency.endswith(".agda"):   # just a dependency on a source file
                if target in G:
                    G.nodes[target]['files'].append(dependency)
                else:
                    G.add_node(target, command = None, files = [dependency])
            else:                              # dependency on another target
                if not(target in G):
                    G.add_node(target, command = None, files = [])
                if not(dependency in G):
                    G.add_node(dependency, command = None, files = [])
                G.add_edge(target, dependency)
                
            current_target = target
        elif "AGDA" in line:
            # this relies on the wild guess, that a line with build command contains 'AGDA'
            if current_target is None:
                raise Exception(f"current_target None while trying to set build command")

            G.nodes[current_target]['command'] = line.strip()
            
    return G

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
        

def print_some_info(G, with_nodes_and_edges=False):
    print(G)

    if with_nodes_and_edges:
         if G.number_of_nodes() > 10 or G.number_of_edges() > 10:
             # Print a random selection of 10 nodes and edges
             all_nodes = list(G.nodes())
             all_edges = list(G.edges())

             random_nodes = random.sample(all_nodes, min(len(all_nodes), 10))
             random_edges = random.sample(all_edges, min(len(all_edges), 10))

             print("")
             print("Random Nodes:")
             for node in random_nodes:
                 print("Name: ", node)
                 print("Command: ", G.nodes[node].get('command'))
                 print("Files: ", G.nodes[node].get('files'))
                 
             print("")
             print("Random Edges:", random_edges)
         else:
             print("")
             print("Nodes:", [(node, G.nodes[node].get('command')) for node in G.nodes()])
             print("")
             print("Edges:", G.edges())

def topological_order(G):
    # compute a comparison function
    # 1 -> 2 means that 1 depends on 2
    # and results in 1 > 2

    print("Computing topological order.")
    topological_order = list(nx.topological_sort(G))
    # Preprocess the topological order for efficient comparisons
    node_positions = {node: position for position, node in enumerate(reversed(topological_order))}

    def order(node):
        return node_positions[node]
    
    return order
        
def contract_composable(G, order):
    # contract all dependency situations that are 'a single arrow':
    #   .. *->* .. (not really yet, because *->*->* is a lot easier)
    # onto the left node
    # manipulates the given graph
    # BUG to fix: the file-dependencies should be collected when contracting
    
    print("-----------------------------------")
    print(f"Analysing graph with {G.number_of_nodes()} nodes and {G.number_of_edges()} edges.")
    contractible = [node for node in G.nodes() if G.in_degree(node) == 1 and G.out_degree(node) == 1]
    print(f"{len(contractible)} of {G.number_of_nodes()} nodes look like the middle one in: *->*->*")
    print("contracting right * to left one...")
    
    for node in sorted(contractible, key=order):
        # print(node, order(node))
        [(contract_onto, _)] = G.in_edges(node)
        nx.contracted_nodes(G, contract_onto, node, self_loops=False, copy=False)
        
    print(f"Reduced graph to {G.number_of_nodes()} nodes and {G.number_of_edges()} edges.")
    print("-----------------------------------")
    
            
if __name__ == "__main__":
    raw_graph = makefile_to_dependency_graph()
    
    G = nx.transitive_reduction(raw_graph) # WTF: this operation throws away node data
    for node_id, node_data in raw_graph.nodes(data=True):
        G.nodes[node_id].update(node_data)

    order = topological_order(G)
        
    contract_composable(G, order)
        
    write_reduced_makefile("reduced_makefile", G)

    print_some_info(G, with_nodes_and_edges=True)

