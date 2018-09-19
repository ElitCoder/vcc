#ifndef OPTIMIZE_H
#define OPTIMIZE_H

#include "func.h"

typedef struct vertex_edge_t vertex_edge_t;

struct vertex_edge_t {
  vertex_t *from;
  vertex_t *to;
};

#endif
