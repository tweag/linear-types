#include <stdlib.h>
#include <stdio.h>
#include "queues.h"

static const int QUEUE_SIZE = 10;

void print_queue(queue_t* queue) {
  node_t* node = queue->start;
  while (node) {
    printf("%d ", node->id);
    node = node->next;
  }
  printf("\n");
}

queue_t* create_queue(void) {
  queue_t* queue = malloc(sizeof(queue_t));
  queue->start = NULL;
  queue->end = NULL;
  return queue;
}

void clear_queue(queue_t* queue) {
  while(pop(queue)) {};
  free(queue);
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
