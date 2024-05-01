#include <limits.h>
#define n 100 // Le nombre de sommets de G
/**
 * We will create an array in which we will store all nodes of graph
 * The array if of fixed size
 * Each node is know by a unique number between 0 and n-1 named vertex
 * Each node is stored in liste_adj[vertex] inside the graph struct
 * For exemple if you have only 3 nodes the size of liste_adj will still be 100 and the cases 0, 7 and 99 will be occupied by nodes when 
 * 3 nodes with 0, 7 and 99 as vertex values are added to the initial graph
*/
/*@ predicate validGraph(graph* g) = \valid(g) && valid(g->liste_adj+(0..n-1));
predicate seperatedGraph(graph* g) = \seperated(g->liste_adj, g->liste_adj+(1..n-1));
predicate nullInitGraph(graph* g) = \forall int i;i<n && i>=0 ==> g->liste_adj[i] == NULL;
predicate validVertex(unsigned v) = \valid(v) && v>=0 && v<n-1;
predicate validNode(node* n) = \valid(n->vertex) && \valid(n->suivant) && validVertex(n->vertex);
*/


struct node{
   unsigned vertex;
   struct node* suivant;
};

struct graph{
   struct node* liste_adj[n]; //Un tableau de listes liniaries décriant les aretes de G
};
/*@ assings \nothing;
ensures validGraph(\result);
ensures seperatedGraph(\result);
ensures nullInitGraph(\result);
*/
struct graph* cree_graph();

/*@ assigns graph;
ensures validGraph(graph) && validNode(src) && validNode(dest);
ensures \at(graph->liste_adj[src.vertex], POST) != NULL;
*/
void ajouter_arc(struct graph* graph, struct node src, struct node dest);

//Dans notre implémentation, un arc sortant par
/*@ assigns garph;
ensures validGraph(graph) && validNode(src) && validNode(dest);
ensures \at(graph->liste_adj[src->vertex], Pre) != NULL;
*/
void supprimer_arc(struct graph* graph, struct node src, struct node dest);  
/*@ assigns garph;
ensures validGraph(graph) && validVertex(vertex);
ensures \at(graph->liste_adj[src->vertex], Pre) == NULL;
ensures \at(graph->liste_adj[src->vertex], Post) != NULL;
*/
void ajouter_sommet(struct graph* graph, unsigned vertex);
/*@ assigns garph;
ensures validGraph(graph) && validVertex(vertex);
ensures \at(graph->liste_adj[src->vertex], Pre) != NULL;
*/
void supprimer_sommet(struct graph* graph, unsigned vertex);
/*@ assigns \nothing;
ensures validGraph(g);
ensures \valid(\result);
ensures \result >= 0 && \result <= INT_MAX;
*/
unsigned ordre(struct graph g);
/*@ assigns \nothing;
predicate arcExists(node src, node dest) =
  \exists node current = src;
  current != NULL &&
  (
   current == dest || arcExists(*(current.suivant), dest)
  );
predicate arc(graph graph, node src, node dest, unsigned result) = ((result == 0) ==> !arcExists(graph.liste_adj[src.vertext], dest)) 
                                                                  && 
                                                                  ((result == 1) ==> arcExists(graph.liste_adj[src.vertext], dest));
ensures validGraph(graph) && validNode(src) && validNode(dest);
ensures arc(graph, src, dest; \result) ;
*/
unsigned arc(struct graph graph, struct node src, struct node dest);

int degre_exterieur(struct graph graph, struct node node);

int degre_interieur(struct graph graph, struct node node);

int degre(struct graph graph, struct node node);

void DFS_mark_visited(struct graph* graph, unsigned vertex, int visited[]);

void DFS(struct graph* graph, unsigned vertex);

int nombre_composantes_connexes(struct graph* graph);