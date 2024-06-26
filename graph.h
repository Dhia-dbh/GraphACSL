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
/*@ assigns \nothing;
requires validGraph(\result);
requires seperatedGraph(\result);
ensures nullInitGraph(\result);
*/
struct graph* cree_graph();

/*@ 
  assigns graph->liste_adj[src.vertex];
  requires validGraph(graph) && validVertex(src.vertex) && validVertex(dest.vertex);
  ensures \exists struct node* p; p == \old(graph->liste_adj[src.vertex]) || p == \new && p->vertex == dest.vertex && p->suivant == \old(graph->liste_adj[src.vertex]);
*/
void ajouter_arc(struct graph* graph, struct node src, struct node dest);

//Dans notre implémentation, un arc sortant par
/*@ 
  requires validGraph(graph) && validNode(src) && validNode(dest);
  assigns graph->liste_adj[src.vertex];
  ensures \at(graph->liste_adj[src->vertex], Pre) != NULL;
  ensures \forall struct node* p; \old(p == graph->liste_adj[src.vertex]) && p->vertex != dest.vertex ==> p->vertex == \old(p->vertex) && p->suivant == \old(p->suivant);
*/
void supprimer_arc(struct graph* graph, struct node src, struct node dest);

/*@ assigns garph;
requires validGraph(graph) && validVertex(vertex);
ensures \at(graph->liste_adj[src->vertex], Pre) == NULL;
ensures \at(graph->liste_adj[src->vertex], Post) != NULL;
*/
void ajouter_sommet(struct graph* graph, unsigned vertex);
/*@ assigns garph;
requires validGraph(graph) && validVertex(vertex);
ensures \at(graph->liste_adj[src->vertex], Pre) != NULL;
*/
void supprimer_sommet(struct graph* graph, unsigned vertex);
/*@ assigns \nothing;
requires validGraph(&g);
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
ensures validGraph(&graph) && validNode(&src) && validNode(&dest);
ensures arc(graph, src, dest; \result) ;
*/
unsigned arc(struct graph graph, struct node src, struct node dest);
/*@ assigns \nothing;
   logic degre_ext(node node, int result) = node.suivant!=NULL?degre_ext(node.suivant, result + 1):result;
   requires validGraph(&graph) && validNode(&node);
   predicate validDegre_ext(int result) = degre_ext(graph.liste_adj[src.vertex], 0) >= 0 && degre_ext(graph.liste_adj[src.vertex], 0) <= INT_MIN;
   ensures \result >= 0 && \result <= INT_MIN;
   ensures validDegre_ext(degre_ext(graph.liste_adj[src.vertex], 0));
   ensures degre_ext(graph.liste_adj[src.vertex], 0) == \result;
*/
int degre_exterieur(struct graph graph, struct node node);
/*@ assigns \nothing;
   logic degre_int(graph graph, node node, int counter, int result) = (counter < n) ?(
                                                                              (counter !=node.vertex) ?(
                                                                                 arcExists(graph.liste_adj[counter], node)?
                                                                                    degre_int(graph, node, counter + 1, result +1):
                                                                                    degre_int(graph, node, counter + 1, result)
                                                                              ):
                                                                              degre_int(graph, node, counter + 1, result):
                                                                              0                                                                                                                                                                       
                                                                           ):
                                                                           0;
   predicate validDegre_int(int result) = degre_int(graph, node, 0, 0) >= 0 && degre_int(graph, node, 0, 0) <= INT_MIN;
   requires validGraph(&graph) && validNode(&node);
   ensures \result >= 0 && \result <= INT_MIN;
   ensures validDegre_int(degre_int(graph, node, 0, 0));
   ensures degre_int(graph, node, 0, 0) == \result;
*/
int degre_interieur(struct graph graph, struct node node);
/*@ assigns \nothing;
requires validGraph(&graph) && validNode(&node);
ensures \result >= 0 && \result <= INT_MIN;
ensures degre_int(graph, node, 0, 0) >= 0 && degre_int(graph, node, 0, 0) <= INT_MIN;
ensures validDegre_ext(degre_ext(graph.liste_adj[src.vertex], 0));
ensures validDegre_int(degre_int(graph, node, 0, 0));
ensures degre_int(graph, node, 0, 0) - degre_ext(graph.liste_adj[node.vertex]) == \result;
*/
int degre(struct graph graph, struct node node);


/*@
  requires validGraph(&graph);
  requires \valid(visited + (0 .. n-1));
  assigns visited[0 .. n-1];
*/
void DFS(struct graph graph, unsigned vertex, int visited[],int printed);

/*@
  requires validGraph(graph);
  assigns \nothing;
  ensures \result >= 0 && \result <= n;
*/
int nombre_composantes_connexes(struct graph graph);