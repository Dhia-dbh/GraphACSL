#include <stdlib.h>
#include <stdio.h>
#include "graph.h"

struct graph* cree_graph(){
   struct graph* graph = (struct graph*)malloc(sizeof(struct graph));
    for (int i = 0; i < n; i++)
        graph->liste_adj[i]=NULL;
   return graph;
}


void ajouter_arc(struct graph* graph, struct node src, struct node dest){

    struct node* new_node = (struct node*)malloc(sizeof(struct node));
    new_node->vertex = dest.vertex;
    new_node->suivant = NULL;
    struct node* current = graph->liste_adj[src.vertex];
    if (current == NULL) {
        graph->liste_adj[src.vertex] = new_node;
    } else {
        while (current->suivant != NULL) {
            current = current->suivant;
        }
        current->suivant = new_node;
    }
}

void supprimer_arc(struct graph* graph, struct node src, struct node dest){
    if (graph->liste_adj[src.vertex] == NULL) {
        printf("Error: Source vertex %u does not exist in the graph.\n", src.vertex);
        return;
    }

    //  Search for the node to be deleted in the source's adjacency list
    struct node* current = graph->liste_adj[src.vertex];
    struct node* prev = NULL;  // Keep track of the previous node for efficient deletion

    while (current != NULL) {
        if (current->vertex == dest.vertex) {
            // Arc found: remove the current node
            if (prev == NULL) {  // Deleting the head node
                graph->liste_adj[src.vertex] = current->suivant;
            } else {
                prev->suivant = current->suivant;
            }
            free(current);  // Free the memory allocated for the deleted node
            return;
        }
        prev = current;
        current = current->suivant;
    }

    // Arc not found: inform the user
    printf("Arc from vertex %u to %u does not exist in the graph.\n", src.vertex, dest.vertex);

}

void ajouter_sommet(struct graph* graph, unsigned vertex){
    // testi idha il slot fergha wala le w zid testi idha vertex<n (ACSL)
    struct node* new_node = (struct node*)malloc(sizeof(struct node));
    new_node->vertex = vertex;
    new_node->suivant = NULL;
    graph->liste_adj[vertex ] = new_node;
}


void supprimer_sommet(struct graph* graph, unsigned vertex) {
    // Delete incoming arcs
    for (int i = 0; i < n; i++) {
        if (i != vertex ) {  // Skip the vertex itself
            struct node* current = graph->liste_adj[i];
            struct node* prev = NULL;
            while (current != NULL) {
                if (current->vertex == vertex) {
                    // Arc found: remove it
                    if (prev == NULL) {  // Deleting the head node of the adjacency list
                        graph->liste_adj[i] = current->suivant;
                    } else {
                        prev->suivant = current->suivant;
                    }
                    free(current);  // Free the memory of the deleted node
                    break;  // Only need to remove one incoming arc
                }
                prev = current;
                current = current->suivant;
            }
        }
    }

    // Delete outgoing arcs
    struct node* current = graph->liste_adj[vertex];
    while (current != NULL) {
        struct node* next = current->suivant;
        free(current);
        current = next;
    }
    graph->liste_adj[vertex ] = NULL;

}

    unsigned ordre(struct graph graph){
   unsigned result=0;
   for(int i=0; i<n;++i){
      if (graph.liste_adj[i] != NULL)
         ++result;
   }
   return result;
}

unsigned arc(struct graph graph, struct node src, struct node dest){
    struct node* current = graph.liste_adj[src.vertex ];
    while (current != NULL) {
        if (current->vertex == dest.vertex) {
            return 1;  // Arc found
        }
        current = current->suivant;
    }
    return 0;  // Arc not found
}

int degre_exterieur(struct graph graph, struct node node){
    struct node* current = graph.liste_adj[node.vertex ]->suivant;
    int count = 0;
    while (current != NULL) {
        count++;
        current = current->suivant;
    }

    return count;
}

int degre_interieur(struct graph graph, struct node node){
    int count = 0;
    for (int i = 0; i < n; i++) {
        struct node* current = graph.liste_adj[i];
        while (current != NULL) {
            if (current->vertex == node.vertex) {
                count++;  // Incoming arc found from the current node (i) to the given node
                break;  // No need to check further for this node (i)
            }
            current = current->suivant;
        }
    }

    return count;
}

int degre(struct graph graph, struct node node){
   return degre_exterieur(graph, node) - degre_interieur(graph, node);
}

void DFS_mark_visited(struct graph* graph, unsigned vertex, int visited[]) {
    visited[vertex] = 1;  // Mark the current node as visited

    // Recur for all unvisited adjacent vertices
    struct node* current = graph->liste_adj[vertex];
    while (current) {
        if (!visited[current->vertex]) {
            DFS_mark_visited(graph, current->vertex, visited);
        }
        current = current->suivant;
    }
}

void DFS(struct graph* graph, unsigned vertex) {
    int visited[n]; // Visited flag for each vertex
    for (int i = 0; i < n; i++) {
        visited[i] = 0;  // Initialize all nodes as unvisited
    }

    DFS_mark_visited(graph, vertex, visited);  // Start DFS from the given vertex

    // Print visited vertices (optional)
    printf("DFS traversal (starting from vertex %u): ", vertex);
    for (int i = 0; i < n; i++) {
        if (visited[i]) {
            printf("%u ", i);
        }
    }
    printf("\n");
}

int nombre_composantes_connexes(struct graph* graph) {
        // Allocate visited array (all 0 for unvisited initially)
        unsigned* visited = malloc(n * sizeof(unsigned));
        for (int i = 0; i < n; i++) {
            visited[i] = 0;
        }

        // Count connected components using DFS
        int count = 0;
        for (int v = 0; v < n; v++) {
            if (!visited[v] && graph->liste_adj[v]!=NULL) {  // If the node hasn't been visited yet
                DFS_mark_visited(graph, v, visited);  // Perform DFS starting from this unvisited node
                count++;  // Increment component count as this DFS explores a new component
            }
        }

        // Free the memory allocated for the visited array
        free(visited);

        return count;
}


int main() {
    // Create a graph
    struct graph* graph = cree_graph();
    int i;
    // Test adding vertices
    printf("Adding vertices:\n");
    for (i = 0; i < 5; i++) {
        ajouter_sommet(graph, i);
        printf("  - Vertex %d added\n", i);
    }

    // Test adding arcs
    printf("\nAdding arcs:\n");
    ajouter_arc(graph, (struct node){.vertex = 0}, (struct node){.vertex = 1});
    ajouter_arc(graph, (struct node){.vertex = 0}, (struct node){.vertex = 2});
    ajouter_arc(graph, (struct node){.vertex = 1}, (struct node){.vertex = 3});
    ajouter_arc(graph, (struct node){.vertex = 2}, (struct node){.vertex = 3});
    printf("  - Arc (0, 1) added\n");
    printf("  - Arc (0, 2) added\n");
    printf("  - Arc (1, 3) added\n");
    printf("  - Arc (2, 3) added\n");

    // Test order (number of vertices)
    printf("\nGraph order (number of vertices): %u\n", ordre(*graph));

    // Test existence of an arc
    printf("\nDoes arc (0, 3) exist? %s\n", arc(*graph, (struct node){.vertex = 0}, (struct node){.vertex = 3}) ? "Yes" : "No");

    // Test outward degree of a node
    printf("\nOutward degree of vertex 0: %d\n", degre_exterieur(*graph, (struct node){.vertex = 0}));


    // Test inward degree of a node
    printf("\nInward degree of vertex 3: %d\n", degre_interieur(*graph, (struct node){.vertex = 3}));

    // Test total degree of a node
    printf("\nTotal degree of vertex 1: %d\n", degre(*graph, (struct node){.vertex = 1}));

    //Test supp node
  /*  supprimer_sommet(graph, 3);
    printf("deleted 3");
    printf("\nDoes arc (1, 3) exist? %s\n", arc(*graph, (struct node){.vertex = 1}, (struct node){.vertex = 3}) ? "Yes" : "No");
*/
    //Test supp arc
    /*
    printf("\nDoes arc (0, 1) exist? %s\n", arc(*graph, (struct node){.vertex = 0}, (struct node){.vertex = 1}) ? "Yes" : "No");
    supprimer_arc(graph, (struct node){.vertex = 0},(struct node){.vertex = 1});
    printf("\ndeleted 0 -> 1");
    printf("\nOutward degree of vertex 0: %d\n", degre_exterieur(*graph, (struct node){.vertex = 0}));
    printf("\nDoes arc (0, 1) exist? %s\n", arc(*graph, (struct node){.vertex = 1}, (struct node){.vertex = 3}) ? "Yes" : "No");
*/

    // Test DFS traversal
    printf("\nDFS traversal starting from vertex 0:\n");
    DFS(graph, 0);

    // Test number of connected components
    printf("\nNumber of connected components: %d\n", nombre_composantes_connexes(graph));

    // Add another vertex and arc to create a separate component
    ajouter_sommet(graph, 5);
    printf("\n5 added\n");
    ajouter_arc(graph, (struct node){.vertex = 5}, (struct node){.vertex = 4});

    // Test number of connected components after adding a separate component
    printf("\nNumber of connected components (after adding a separate component): %d\n", nombre_composantes_connexes(graph));

    // Free the memory allocated for the graph
    free(graph);

    return 0;
}