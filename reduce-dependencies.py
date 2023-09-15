import networkx as nx
import random
import matplotlib.pyplot as plt

def makefile_to_dependency_graph(makefile_path):
    # Create a directed graph
    dependency_graph = nx.DiGraph()

    with open(makefile_path, 'r') as makefile:
        lines = makefile.readlines()

    for line in lines:
        line = line.strip()

        # Skip comments and empty lines
        if line.startswith("#") or not line:
            continue

        # Detect targets in Makefile lines
        if line.endswith(":"):
            target = line[:-1].strip()
            dependency_graph.add_node(target)
        elif ":" in line:
            print(line)
            target , dependency = line.split(':')
            target = target.strip()
            dependency = dependency.strip()
            
            dependency_graph.add_edge(target, dependency)

    return dependency_graph

if __name__ == "__main__":
    makefile_path = "generated_makefile"
    raw_graph = makefile_to_dependency_graph(makefile_path)
    print("Original graph:")
    print("Nodes", raw_graph.number_of_nodes())
    print("Edges", raw_graph.number_of_edges())
    
    dependency_graph = nx.transitive_reduction(raw_graph)
    print("Reduced graph:")
    print("Nodes", dependency_graph.number_of_nodes())
    print("Edges", dependency_graph.number_of_edges())

    # Print a random selection of 10 nodes and edges
    all_nodes = list(dependency_graph.nodes())
    all_edges = list(dependency_graph.edges())

    random_nodes = random.sample(all_nodes, min(len(all_nodes), 10))
    random_edges = random.sample(all_edges, min(len(all_edges), 10))
    
    print("Random Nodes:", random_nodes)
    print("Random Edges:", random_edges)

    G = dependency_graph
    # Draw the graph using matplotlib
    pos = nx.spring_layout(G)  # Position nodes using a layout algorithm
    nx.draw(G, pos, with_labels=True, node_color='skyblue', node_size=500, font_size=12, font_color='black')
    plt.title("Graph Visualization")
    plt.show()
    
