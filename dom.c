#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include "util.h"
#include "cfg.h"
#include "func.h"
#include "sym.h"
#include "globals.h"
#include "error.h"

static bool visited(vertex_t* v)
{
	return v->dfnum != -1;
}

static void dfs(vertex_t* v, int* dfnum, vertex_t** vertex)
{
	v->dfnum = *dfnum;
	vertex[*dfnum] = v;
	v->sdom = v;
	v->ancestor = NULL;
	*dfnum = *dfnum + 1;

	for(int i = 0; i < MAX_SUCC; i++){
		if(v->succ[i] == NULL || visited(v->succ[i])){
			continue;
		}


		v->succ[i]->parent = v;
		dfs(v->succ[i], dfnum, vertex);
	}
	/* succ[0] corresponds to the target of a conditional branch.
	 * succ[0] is NULL for an unconditional branch (BA).
	 * succ[1] corresponds to the target of an unconditional branch.
	 *
	 */
}

static void link(vertex_t* parent, vertex_t* child)
{
	child->ancestor = parent;
	pr("ancestor(%d) = %d\n", child->index, parent->index);
}

static vertex_t* eval(vertex_t* v)
{
	vertex_t*		u;

	u = v;

	/* Find the ancestor of V with least semi-dominator. */

	while (v->ancestor != NULL) {

		if (v->sdom->dfnum < u->sdom->dfnum)
			u = v;

		v = v->ancestor;
	}

	return u;
}

static void remove_from_preds(vertex_t* w)
{
	int		i;

	for (i = 0; i < MAX_SUCC; ++i)
		if (w->succ[i] != NULL) {
			if(w->succ[i]->pred == NULL) {
				printf("PRED WAS NULL\n");

				continue;
			}
			remove_from_list(&w->succ[i]->pred, w);
		}
}

static void free_stmts(vertex_t* w)
{
	list_t*		p;
	list_t*		h;

	p = h = w->stmts;

	do {
		free_stmt(p->data);
		p = p->succ;
	} while (p != h);
}

void dominance(func_t* func)
{
	int		i;
	int		dfnum;
	vertex_t*	u;
	vertex_t*	v;
	vertex_t*	w;
	list_t*		p;
	list_t*		h;
	vertex_t*	original[func->nvertex];

	if (0) visited(NULL);	/* For silencing GCC. */

	/* Construct the immediate-dominator tree. */

	memcpy(original, func->vertex, sizeof original);

	use_pr = false;

	/* Step 1. */

	/* Initialise sdom of each vertex to itself. */
	for (i = 0; i < func->nvertex; i++)	{
		func->vertex[i]->dfnum		= -1;
		func->vertex[i]->sdom		= func->vertex[i];
		func->vertex[i]->idom		= NULL;
		func->vertex[i]->ancestor	= NULL;
		func->vertex[i]->parent		= NULL;
		func->vertex[i]->domchild	= NULL;
		func->vertex[i]->domsibling	= NULL;

		func->vertex[i]->rdfnum		= -1;
		func->vertex[i]->rsdom		= func->vertex[i];
		func->vertex[i]->ridom		= NULL;
		func->vertex[i]->rancestor	= NULL;
		func->vertex[i]->rparent		= NULL;
		func->vertex[i]->rdomchild	= NULL;
		func->vertex[i]->rdomsibling	= NULL;
		func->vertex[i]->rsucc	= NULL;
		func->vertex[i]->rpred	= NULL;

		//func->vertex[i]->u.visited = func->vertex[i]->u.live = false;

		if (func->vertex[i] == func->start) {
			u = func->vertex[0];
			func->vertex[0] = func->start;
			func->vertex[i] = u;
		}
	}

	dfnum = 0;

	assert(func->vertex[0] == func->start);

	dfs(func->vertex[0], &dfnum, func->vertex);

	printf("BEFORE CLEANING\n");

	for (i = 0; i < func->nvertex; ++i) {
		if (original[i]->dfnum == -1) {
			printf("remove from preds\n");
			remove_from_preds(original[i]);
			printf("free stmt\n");
			free_stmts(original[i]);
			printf("free vertex\n");
			free_vertex(original[i]);
		}
	}
	pr("dfnum = %d\n", dfnum);
	pr("n     = %d\n", func->nvertex);
	func->nvertex = dfnum;

	printf("Before cfg\n");

	print_cfg(func);

	for (i = func->nvertex - 1; i > 0; i--) {
		w = func->vertex[i];

		/* Step 2. */
		pr("\nstep 2 for %d:%d\n", w->index, w->dfnum);
		/* All vertices except the start node must have a predecessor.
		 *
		 */

		assert(w->pred != NULL);

		p = h = w->pred;

		//For each v belonging to pred(w) do..
		do {
			v = p->data;
			p = p->succ;

			u = eval(v);

			if(u->sdom->dfnum < w->sdom->dfnum) {
				w->sdom = u->sdom;
			}

			pr("pred %d\n", v->index);
			pr("eval(%d) = %d\n", v->index, u->index);
			pr("sdom(%d) = %d\n", u->index, u->sdom->index);


			/* MAKE COMPLETE DURING LAB 1 */

		} while (p != h);


/*
		if(w->sdom == w->parent) {
			w->idom = w->parent;
			w->domsibling = w->idom->domchild;
			w->idom->domchild = w;
		}
		else {
			insert_first(&w->sdom->bucket, w);
		}*/

		pr("sdom(%d) = %d\n", w->index, w->sdom->index);


		link(w->parent, w);

		/* Step 3. */
		insert_first(&w->sdom->bucket, w);

		pr("emptying bucket of %d\n", w->parent->index);

		p = h = w->parent->bucket;

		if (p == NULL)
			continue;

		do {

			v = p->data;
			p = p->succ;
			u = eval(v);

			/* MAKE COMPLETE DURING LAB 1 */

			if(u->sdom->dfnum < v->sdom->dfnum) {
				v->idom = u;
			}

			else {
				v->idom = w->parent;
			}

		} while (p != h);

		free_list(&w->parent->bucket);
	}



	/* Step 4. */
	pr("\nstep 4\n", "");
	for (i = 1; i < func->nvertex; i++) {
		w = func->vertex[i];

		/* MAKE COMPLETE DURING LAB 1 */

		if(w->idom != w->sdom) {
			w->idom = w->idom->idom;
		}

		w->domsibling = w->idom->domchild;
		w->idom->domchild = w;

		pr("final idom(%d) = %d\n", w->index, w->idom->index);
	}

	func->vertex[0]->idom = NULL;
	print_dt(func);
}
