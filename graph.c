#include <stdlib.h>
#include <stdio.h>
#include "graph.h"

struct graph* cree_graph(){
   struct graph* graph = (struct graph*)malloc(sizeof(struct graph));
   return graph;
}

// Fonction pour créer une liste d'adjacence à partir des arêtes spécifiées
struct graph* cree_graph(struct arc liste_arc[], int nb_nodes)
{
    // alloue de l'espace de stockage pour la structure de données du graphe
    struct graph* graph = (struct graph*)malloc(sizeof(struct graph));
 
    // initialise le pointeur principal pour tous les sommets
    for (int i = 0; i < n; i++) {
        graph->liste_adj[i] = NULL;
    }
 
    // ajoute les arêtes au nodee orienté une par une
    for (int i = 0; i < n; i++)
    {
        // récupère le sommet source et destination
        int src = liste_arc[i].src;
        int dest = liste_arc[i].dest;
 
        // alloue un nouveau noeud de la liste d'adjacence de src à dest
        struct node* newDestNode = (struct node*)malloc(sizeof(struct node));
        struct node* newSrcNode = (struct node*)malloc(sizeof(struct node));

        newSrcNode->vertex = src;
        newSrcNode -> suivant = newDestNode;

        graph->liste_adj[src] = newSrcNode;
        graph->liste_adj[dest] = newDestNode;
    }
 
    return graph;
}

void ajouter_arc(struct graph* graph, struct node src, struct node dest, unsigned weight){
   (graph->liste_adj[src.vertex])->suivant = &dest;
}
