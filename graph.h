#define n 100 // Le nombre de sommets de G
/**
 * We will create an array in which we will store all nodes of graph
 * The array if of fixed size
 * Each node is know by a unique number between 0 and n-1 named vertex
 * Each node is stored in liste_adj[vertex] inside the graph struct
 * For exemple if you have only 3 nodes the size of liste_adj will still be 100 and the cases 0, 7 and 99 will be occupied by nodes when 
 * 3 nodes with 0, 7 and 99 as vertex values are added to the initial graph
*/

struct node{
   unsigned vertex;
   struct node* suivant;
   unsigned weight; //weight of the exiting arc if one exists
};
struct arc{
   unsigned src, dest;
   unsigned weight;
};
struct graph{
   struct node* liste_adj[n]; //Un tableau de listes liniaries décriant les aretes de G
};
struct graph* cree_graph();

struct graph* cree_graph(struct node nodes[], int nb_nodes);

void ajouter_arc(struct graph* graph, struct node src, struct node dest, unsigned weight);
//Dans notre implémentation, un arc sortant par
void supprimer_arc(struct graph* graph, struct node src, struct node dest);  

void ajouter_sommet(struct graph* graph, unsigned vertex);

void supprimer_sommet(struct graph* graph, unsigned vertex);

unsigned ordre(struct graph g);

unsigned arc(struct graph graph, struct node node1, struct node node2);

int degre_exterieur(struct graph graph, struct node node);

int degre_interieur(struct graph graph, struct node node);

int degre(struct graph graph, struct node node);