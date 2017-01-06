#include <stdlib.h>
#include <stdio.h>

static const int QUEUE_SIZE = 10;

typedef struct node_t {
    int id;
    struct node_t* next;
} node_t;

typedef struct queue_t {
    node_t* start;
    node_t* end;
} queue_t;

queue_t create_queue(void) {
    queue_t queue = {
        .start = NULL,
        .end = NULL
    };
    return queue;
}

node_t* create_node(int id) {
    node_t* node = malloc(sizeof(node_t));
    node->id = id;
    node->next = NULL;
    return node;
}

void push(queue_t* queue, int id) {
    node_t* node = create_node(id);

    if (!queue->start) {
        // Case of an empty queue.
        queue->start = node;
    }

    // At initialisation the end field is NULL.
    if (queue->end) {
        queue->end->next = node;
    }

    queue->end = node;
}

node_t* pop(queue_t* queue) {
    node_t* node = queue->start;

    if (node) {
        queue->start = node->next;
    } else {
        // If the queue was empty we cannot dereference queue->star.
        queue->start = NULL;
    }

    return node;
}

int delete_node(queue_t* queue, int position) {
    int i = 0;
    node_t* current_node = queue->start;

    if (position == 0) {
        // If pop returns NULL, then the list is empty and we cannot remove elements.
        node_t* to_delete = pop(queue);
        if (to_delete) {
            free(to_delete);
        }
        return to_delete == NULL ? 1 : 0;
    }

    while (current_node && i < position) {
        // We need to stop before reaching the position, in order to change the linked structure.
        if (i == (position - 1)) {
            node_t* to_delete = current_node->next;

            // Case where we are asked to delete a position bigger than the size of the queue.
            if (to_delete == NULL) {
                return 1;
            }
            
            current_node->next = to_delete->next;
            free(to_delete);
            return 0;
        }
        i++;
        current_node = current_node->next;
    }

    // We failed to find the index.
    return 1;
}

int main(int argc, const char* argv[]) {
    queue_t queue = create_queue();    

    pop(&queue);
    
    for (int i = 0; i < QUEUE_SIZE; i++) {
        printf("%d \r\n", i);
        push(&queue, i);
    }

    delete_node(&queue, QUEUE_SIZE);
    delete_node(&queue, QUEUE_SIZE - 1);
    delete_node(&queue, 0);

    for (int i = 0; i < QUEUE_SIZE; i++) {
        node_t* node = pop(&queue);
        if (node) {
            printf("node #%d \r\n", node->id);
            free(node);
        }
    }

    return 0;
}
