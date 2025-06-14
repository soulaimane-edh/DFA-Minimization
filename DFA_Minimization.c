/*
By Ed-dahmani Soulaimane
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#define MAX_STATES 64
#define ALPHABET_SIZE 2  // Binary alphabet (0/1 or a/b)
#define MAX_LABEL_LEN 512

// Structure representing a DFA state
// Structure représentant un état d'automate
typedef struct State {
    char  name[4];       // State name (3 chars max)
    bool  isFinal;       // Is this a final/accepting state?
    struct State *next[ALPHABET_SIZE];  // Transitions for each alphabet symbol
    int   id;            // Unique state ID
    int   partitionId;   // Current partition ID during minimization
} State;

// Global array tracking all states in the DFA
// Tableau global pour suivre tous les états de l'automate
static State *allStates[MAX_STATES];
static int    nStates = 0;  // Current number of states

// Structure representing a partition of states
// Structure représentant une partition d'états
typedef struct {
    State* states[MAX_STATES]; // States in this partition
    int    count;              // Number of states
    int    id;                 // Partition ID
    char   label[MAX_LABEL_LEN]; // Display label
} Partition;

static Partition partitions[MAX_STATES];
static int       nPartitions = 0;  // Current partition count

// Helper function to find state index by pointer
// Fonction utilitaire pour trouver l'index d'un état par son pointeur
static int getStateIndexByPtr(State *s) {
    if (!s) return -1;
    for (int i = 0; i < nStates; ++i) {
        if (allStates[i] == s) return i;
    }
    return -1;
}

// Creates a new state and adds it to global array
// Crée un nouvel état et l'ajoute au tableau global
static State *createState(const char *name, bool isFinal) {
    if (nStates >= MAX_STATES) {
        fprintf(stderr, "Error: MAX_STATES exceeded\n");
        exit(EXIT_FAILURE);
    }
    State *s = malloc(sizeof(State));
    if (!s) {
        perror("malloc for State failed");
        exit(EXIT_FAILURE);
    }
    snprintf(s->name, sizeof(s->name), "%s", name);
    s->isFinal = isFinal;
    s->next[0] = s->next[1] = NULL;
    s->id = nStates;
    s->partitionId = -1;
    allStates[nStates++] = s;
    return s;
}

// Array to track reachable states during cleanup
// Tableau pour suivre les états accessibles pendant le nettoyage
static bool reachable[MAX_STATES];

// Marks all states reachable from startNode using BFS
// Marque tous les états accessibles depuis startNode en utilisant BFS
static void markReachable(State *startNode) {
    if (!startNode) return;

    // Initialize all states as unreachable
    // Initialise tous les états comme inaccessibles
    for (int i = 0; i < nStates; ++i) {
        reachable[i] = false;
    }

    int startIndex = getStateIndexByPtr(startNode);
    if (startIndex == -1) {
         if (nStates > 0 && allStates[0] == startNode) startIndex = 0;
         else {
            fprintf(stderr, "Error: Start node not found in allStates during markReachable.\n");
            return;
         }
    }
    reachable[startIndex] = true;

    // Propagate reachability through transitions
    // Propage l'accessibilité à travers les transitions
    bool changed = true;
    while (changed) {
        changed = false;
        for (int i = 0; i < nStates; ++i) {
            if (!reachable[i]) continue;

            for (int sym = 0; sym < ALPHABET_SIZE; ++sym) {
                State *targetState = allStates[i]->next[sym];
                if (targetState) {
                    int targetIndex = getStateIndexByPtr(targetState);
                    if (targetIndex != -1 && !reachable[targetIndex]) {
                        reachable[targetIndex] = true;
                        changed = true;
                    }
                }
            }
        }
    }
}

// Removes unreachable states from the DFA
// Supprime les états inaccessibles de l'automate
static void removeUnreachable(State *startNode) {
    markReachable(startNode);

    // Clear transitions to unreachable states
    // Nettoie les transitions vers les états inaccessibles
    for (int i = 0; i < nStates; ++i) {
        if (reachable[i]) {
            for (int sym = 0; sym < ALPHABET_SIZE; ++sym) {
                State *targetState = allStates[i]->next[sym];
                if (targetState) {
                    int targetIndex = getStateIndexByPtr(targetState);
                    if (targetIndex != -1 && !reachable[targetIndex]) {
                        allStates[i]->next[sym] = NULL;
                    }
                }
            }
        }
    }

    // Compact the states array, removing unreachable states
    // Compacte le tableau d'états, supprimant les inaccessibles
    int writeIndex = 0;
    for (int readIndex = 0; readIndex < nStates; ++readIndex) {
        if (reachable[readIndex]) {
            if (readIndex != writeIndex) {
                allStates[writeIndex] = allStates[readIndex];
            }
            allStates[writeIndex]->id = writeIndex;
            writeIndex++;
        } else {
            free(allStates[readIndex]);
            allStates[readIndex] = NULL;
        }
    }
    nStates = writeIndex;
}

// Creates initial partitions (final vs non-final states)
// Crée les partitions initiales (états finaux vs non finaux)
static void initialPartition(void) {
    nPartitions = 0;
    Partition finalP;
    Partition nonFinalP;
    finalP.count = 0; finalP.id = -1; finalP.label[0] = '\0';
    nonFinalP.count = 0; nonFinalP.id = -1; nonFinalP.label[0] = '\0';

    // Separate final and non-final states
    // Sépare les états finaux et non finaux
    for (int i = 0; i < nStates; ++i) {
        allStates[i]->partitionId = -1;
        if (allStates[i]->isFinal) {
            finalP.states[finalP.count++] = allStates[i];
        } else {
            nonFinalP.states[nonFinalP.count++] = allStates[i];
        }
    }

    // Create partition for final states if any exist
    // Crée une partition pour les états finaux s'il y en a
    if (finalP.count > 0) {
        finalP.id = nPartitions;
        strcpy(finalP.label, "{");
        for (int i = 0; i < finalP.count; ++i) {
            finalP.states[i]->partitionId = finalP.id;
            strcat(finalP.label, finalP.states[i]->name);
            if (i < finalP.count - 1) strcat(finalP.label, ",");
        }
        strcat(finalP.label, "}");
        partitions[nPartitions++] = finalP;
    }

    // Create partition for non-final states if any exist
    // Crée une partition pour les états non finaux s'il y en a
    if (nonFinalP.count > 0) {
        nonFinalP.id = nPartitions;
        strcpy(nonFinalP.label, "{");
        for (int i = 0; i < nonFinalP.count; ++i) {
            nonFinalP.states[i]->partitionId = nonFinalP.id;
            strcat(nonFinalP.label, nonFinalP.states[i]->name);
            if (i < nonFinalP.count - 1) strcat(nonFinalP.label, ",");
        }
        strcat(nonFinalP.label, "}");
        partitions[nPartitions++] = nonFinalP;
    }

    printf("Initial Partitions (%d):\n", nPartitions);
    for (int i = 0; i < nPartitions; ++i) {
        printf("  Partition %d %s\n", partitions[i].id, partitions[i].label);
    }
}

// Refines partitions until no more splits are possible
// Raffine les partitions jusqu'à ce qu'aucune division ne soit possible
static void refineAllPartitions(void) {
    bool changedInPass;
    do {
        changedInPass = false;
        Partition newPartitionsList[MAX_STATES];
        int newNPartitionsCounter = 0;

        // Process each existing partition
        // Traite chaque partition existante
        for (int i = 0; i < nPartitions; ++i) {
            Partition *P = &partitions[i];
            if (P->count <= 1) {
                if (P->count > 0 && newNPartitionsCounter < MAX_STATES) {
                     newPartitionsList[newNPartitionsCounter++] = *P;
                }
                continue;
            }

            Partition subPartitions[MAX_STATES];
            int nSubPartitions = 0;

            // Start with first state in its own subpartition
            // Commence avec le premier état dans sa propre sous-partition
            subPartitions[0].count = 0;
            subPartitions[0].states[subPartitions[0].count++] = P->states[0];
            nSubPartitions = 1;

            // Compare each state with existing subpartitions
            // Compare chaque état avec les sous-partitions existantes
            for (int j = 1; j < P->count; ++j) {
                State *s_j = P->states[j];
                bool placed = false;

                for (int k = 0; k < nSubPartitions; ++k) {
                    State *s_k_rep = subPartitions[k].states[0];
                    bool distinguishable = false;

                    // Check if states lead to different partitions
                    // Vérifie si les états mènent à des partitions différentes
                    for (int sym = 0; sym < ALPHABET_SIZE; ++sym) {
                        State *next_s_j = s_j->next[sym];
                        State *next_s_k_rep = s_k_rep->next[sym];

                        int p_id_next_s_j = next_s_j ? next_s_j->partitionId : -2;
                        int p_id_next_s_k_rep = next_s_k_rep ? next_s_k_rep->partitionId : -2;

                        if (p_id_next_s_j != p_id_next_s_k_rep) {
                            distinguishable = true;
                            break;
                        }
                    }

                    if (!distinguishable) {
                        subPartitions[k].states[subPartitions[k].count++] = s_j;
                        placed = true;
                        break;
                    }
                }

                if (!placed) {
                    if (nSubPartitions >= MAX_STATES) { }
                    subPartitions[nSubPartitions].count = 0;
                    subPartitions[nSubPartitions].states[subPartitions[nSubPartitions].count++] = s_j;
                    nSubPartitions++;
                }
            }

            // Add all subpartitions to the new partition list
            // Ajoute toutes les sous-partitions à la nouvelle liste de partitions
            for (int k = 0; k < nSubPartitions; ++k) {
                if (newNPartitionsCounter < MAX_STATES) {
                    newPartitionsList[newNPartitionsCounter++] = subPartitions[k];
                }
            }

            if (nSubPartitions > 1) {
                changedInPass = true;
            }
        }

        // Update partitions if changes were made
        // Met à jour les partitions si des changements ont été faits
        if (changedInPass || newNPartitionsCounter != nPartitions) {
            nPartitions = newNPartitionsCounter;
            for (int i = 0; i < nPartitions; ++i) {
                partitions[i] = newPartitionsList[i];
                partitions[i].id = i;

                // Update labels and partition IDs
                // Met à jour les libellés et IDs de partition
                partitions[i].label[0] = '\0';
                strcat(partitions[i].label, "{");
                for (int j = 0; j < partitions[i].count; ++j) {
                    partitions[i].states[j]->partitionId = partitions[i].id;
                    strcat(partitions[i].label, partitions[i].states[j]->name);
                    if (j < partitions[i].count - 1) strcat(partitions[i].label, ",");
                }
                strcat(partitions[i].label, "}");
            }
             printf("Partitions refined (%d total):\n", nPartitions);
             for (int i = 0; i < nPartitions; ++i) {
                 printf("  Partition %d %s\n", partitions[i].id, partitions[i].label);
             }
        } else {
            changedInPass = false;
        }

    } while (changedInPass);

    printf("\nFinal Partitions after refinement (%d):\n", nPartitions);
    for (int i = 0; i < nPartitions; ++i) {
        printf("  Partition %d (New State S%d) %s\n", partitions[i].id, partitions[i].id, partitions[i].label);
    }
}

// Prints the minimized DFA transition table
// Affiche la table de transition de l'automate minimisé
static void printMinimizedDFA(void) {
    printf("\nMinimized DFA Transition Table:\n");
    printf("%-25s| %-15s| %-15s\n", "State (Original States)", "Next on 'a'", "Next on 'b'");
    printf("------------------------------------------------------------------\n");

    for (int i = 0; i < nPartitions; ++i) {
        Partition *currentP = &partitions[i];
        if (currentP->count == 0) continue;

        State *representative = currentP->states[0];
        char currentLabelWithName[MAX_LABEL_LEN + 5];
        bool isNewStateFinal = representative->isFinal;

        snprintf(currentLabelWithName, sizeof(currentLabelWithName), "S%d %s%c",
                 currentP->id, currentP->label, (isNewStateFinal ? '*' : ' '));

        char nextStateLabelA[20] = "-";
        char nextStateLabelB[20] = "-";

        if (representative->next[0]) {
            int targetPartitionIdA = representative->next[0]->partitionId;
            snprintf(nextStateLabelA, sizeof(nextStateLabelA), "S%d", targetPartitionIdA);
        }

        if (representative->next[1]) {
            int targetPartitionIdB = representative->next[1]->partitionId;
            snprintf(nextStateLabelB, sizeof(nextStateLabelB), "S%d", targetPartitionIdB);
        }

        printf("%-25s| %-15s| %-15s\n",
               currentLabelWithName, nextStateLabelA, nextStateLabelB);
    }
    printf("(* indicates final state in minimized DFA)\n");
}

int main(void) {
    /* Example DFA 1:
    State *q0 = createState("q0", false);
    State *q1 = createState("q1", true);
    State *q2 = createState("q2", true);
    State *q3 = createState("q3", false);
    State *q4 = createState("q4", true);
    State *q5 = createState("q5", false);

    State *initialDFAState = q0;

    q0->next[0] = q3; q0->next[1] = q1;
    q1->next[0] = q2; q1->next[1] = q5;
    q2->next[0] = q2; q2->next[1] = q5;
    q3->next[0] = q0; q3->next[1] = q4;
    q4->next[0] = q2; q4->next[1] = q5;
    q5->next[0] = q5; q5->next[1] = q5;
    */

    // Example DFA 2
    // Exemple d'automate 2
    State *q1 = createState("q1", false);
    State *q2 = createState("q2", true);
    State *q3 = createState("q3", true);
    State *q4 = createState("q4", false);

    State *initialDFAState = q1;

    q1->next[0] = q2; q1->next[1] = q3;
    q2->next[0] = q3; q2->next[1] = q2;
    q3->next[0] = q3; q3->next[1] = q2;
    q4->next[0] = q2; q4->next[1] = q3;

    printf("Original DFA defined. Initial state: %s. Number of states: %d\n", initialDFAState->name, nStates);

    printf("\n--- Step 1: Removing Unreachable States ---\n");
    removeUnreachable(initialDFAState);
    printf("States after removing unreachable: %d\n", nStates);

    printf("\n--- Step 2: Initial Partitioning ---\n");
    initialPartition();

    printf("\n--- Step 3: Refining Partitions ---\n");
    refineAllPartitions();

    printf("\n--- Step 4: Minimized DFA ---\n");
    printMinimizedDFA();

    // Clean up memory
    // Nettoyage de la mémoire
    for (int i = 0; i < nStates; ++i) {
        if(allStates[i] != NULL) free(allStates[i]);
    }
    return 0;
}
