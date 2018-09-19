#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include "util.h"
#include "func.h"
#include "sym.h"
#include "globals.h"
#include "stmt.h"
#include "error.h"

phi_t* new_phi(vertex_t* x)
{
	phi_t*		phi;

	phi		= calloc(1, sizeof(phi_t));
	phi->n		= length(x->pred);
	phi->rhs	= calloc(phi->n, sizeof(op_t));

	return phi;
}

void free_phi(phi_t* phi)
{
	free(phi->rhs);
	free(phi);
}

static void print_index(void* vp, FILE* fp)
{
	vertex_t*	v = vp;

	fprintf(fp, "%d", v->index);
}

static void df(vertex_t* u)
{
	if(u == NULL) {
		return;
	}

	df(u->domchild);
	df(u->domsibling);

	for(int i = 0; i < MAX_SUCC; i++) {
		if(u->succ[i] == NULL) {
			continue;
		}

		if(u->succ[i]->idom == u) {
			continue;
		}

		join_set(&u->df, u->succ[i]);
	}

	vertex_t **a;
	size_t n;

	vertex_t *child = u->domchild;

	while(child != NULL) {
		a = set_to_array(child->df, &n);

		for(int i = 0; i < n; i++) {
			if(a[i]->idom != u) {
				join_set(&u->df, a[i]);
			}
		}

		free(a);
		child = child->domsibling;
	}
}

void modsets(func_t* func)
{
	int		i;
	stmt_t*		stmt;
	vertex_t*	v;
	sym_t*		sym;
	list_t*		p;
	list_t*		h;

	for (i = 0; i < func->nvertex; i += 1) {
		v = func->vertex[i];
		if (v->stmts == NULL)
			continue;
		p = h = v->stmts;
		do {
			stmt = p->data;
			p = p->succ;
			sym = defined_sym(stmt);
			if (sym != NULL)
				join_set(&sym->modset, v);
		} while (p != h);
	}
}

void insert_phi_stmt(func_t* func, vertex_t* vertex, sym_t* sym)
{
	int		i;
	unsigned	line;
	phi_t*		phi;
	stmt_t*		stmt;
	list_t*		p;

	if (vertex == func->exit)
		return;

	p = vertex->stmts;

	stmt = p->data;
	assert(stmt->type == LABEL);
	line = stmt->line;

	stmt = new_stmt(PHI, no_op, no_op, new_sym_op(sym), line);
	insert_after(&p, stmt);

	phi = new_phi(vertex);
	stmt->phi = phi;
	phi->stmt = stmt;
	insert_last(&vertex->phi_func_list, phi);

	for (i = 0; i < phi->n; i += 1)
		phi->rhs[i] = new_sym_op(sym);
}

unsigned which_pred(vertex_t* pred, vertex_t* vertex)
{
	int		i;
	list_t*		h;
	list_t*		p;

	i = 0;

	h = p = vertex->pred;

	assert(p != NULL);

	do {
		if (p->data == pred)
			return i;

		i += 1;

		p = p->succ;

	} while (p != h);

	error(FATAL, "pred not found in which_pred");

	/* We will never get here. */

	return 0;
}

bool is_null(vertex_t *v) {
	if(v->stmts == NULL) {
		return false;
	}

	if(length(v->stmts) == 0) {
		return false;
	}

	return true;
}

void rename_symbols(vertex_t* x)
{
	list_t *current = x->stmts;
	list_t *list = NULL;

	sym_t *sym;
	sym_t *symbol;

	if(is_null(x)) {
		do {
			stmt_t *data = current->data;
			current = current->succ;

			int nOperands = 2;

			if(data->type == MOV && is_sym(data->op[0]) && !is_label(data->op[0])) {
				sym = data->op[0].u.sym;
				sym = top(sym->rename_stack);
				data->type = NOP;
				symbol = data->op[2].u.sym;
			}

			else {
				for(int i = 0; i < nOperands; i++) {
					if(data->op[i].type == NO_OP || is_label(data->op[i]) || !is_sym(data->op[i])) {
						continue;
					}

					symbol = data->op[i].u.sym;

					sym = top(symbol->rename_stack);
					//data->op[i].u.sym = sym;
					data->op[i] = new_sym_op(sym);

					add_use(sym, data);
				}

				symbol = defined_sym(data); //NULL if defined

				if(symbol == NULL) {
					continue;
				}

				//printf("Did not continue\n");


				data->op[2] = temp();
				sym = data->op[2].u.sym;

				set_sym_def(sym, data);
			}

			//printf("Pushing rename-stack\n");

			if(symbol->rename_stack == NULL || sym == NULL || symbol == NULL) {
				printf("WAS NULL\n");

				continue;
			}

			push(symbol->rename_stack, sym);

			//printf("PUSHED");

			symbol->ssa_version += 1;

			insert_last(&list, symbol);

		} while(current != x->stmts);
	}

	for(int i = 0; i < MAX_SUCC; i++) {
		if(x->succ[i] == NULL) {
			continue;
		}

		int j = which_pred(x, x->succ[i]);

		list_t *phi_list = x->succ[i]->phi_func_list;

		if(phi_list == NULL) {
			continue;
		}

		do {
			phi_t *phi_func = phi_list->data;
			phi_list = phi_list->succ;

			//if (phi_func->stmt->index == 502) bp();

			symbol = phi_func->rhs[j].u.sym;
			sym = top(symbol->rename_stack);

			if(sym == symbol) {
				//phi_func->rhs[j] = new_sym_op(0);
			}

			else {
				phi_func->rhs[j] = new_sym_op(sym);
			}

			add_use(sym, phi_func->stmt);
		} while(x->succ[i]->phi_func_list != phi_list);
	}

	vertex_t *child = x->domchild;

	while(child != NULL) {
		rename_symbols(child);

		child = child->domsibling;
	}


	if(list == NULL) {
		return;
	}

	current = list;

	do {

		sym = current->data;
		current = current->succ;

		pop(sym->rename_stack);

	} while(current != list);

	free_list(&list);
}

void insert_phi(func_t* func)
{
	/* Insert phi functions. Figure 11. */

	int		iter;		/* Itereration count of Figure 11. */
	sym_t*		sym;		/* Variable V of Figure 11. */
	vertex_t*	x;		/* Node X of Figure 11. */
	vertex_t*	y;		/* Node Y of Figure 11. */
	vertex_t**	a;		/* Node Y of Figure 11. */
	int		i;
	size_t		n;
	list_t*		p;
	list_t*		h;
	list_t*		worklist;

	iter = 0;

	if (func->var == NULL)
		return;

	for (i = 0; i < func->nvertex; i += 1)
		func->vertex[i]->work = func->vertex[i]->already = 0;

	p = h = func->var;

	worklist = NULL;

	do {

		sym = p->data;
		p = p->succ;
		iter += 1;

		/* Add all basic blocks where sym which have an assignment
		 * to sym to the basic block worklist.
		 *
		 */

		/* Create a temporary array for simplicity. */

		if (use_pr) {
			pr("modset(%s) = ", sym->id);
			print_set(sym->modset, print_index, stdout);
		}

		a = set_to_array(sym->modset, &n);
		for (i = 0; i < n; i += 1) {
			x = a[i];
			x->work = iter;
			insert_last(&worklist, x);
		}
		free(a);

		/* Now worklist contains all assignment nodes of sym. */

		while (worklist != NULL) {
			x = remove_first(&worklist);

			/* Create a temporary array for simplicity. */
			a = set_to_array(x->df, &n);
			for (i = 0; i < n; i += 1) {
				y = a[i];

				if (y->already >= iter)
					continue;

				assert(y != func->vertex[0]);
				insert_phi_stmt(func, y, sym);
				y->already = iter;
				if (y->work >= iter)
					continue;
				y->work = iter;
				insert_last(&worklist, y);
			}
			free(a);
		}

	} while (p != h);
}

void to_ssa(func_t* func)
{
	sym_t*		sym;
	list_t*		p;
	list_t*		h;

	if (func->var == NULL)
		return;

	df(func->vertex[0]);

	p = h = func->var;
	do {
		sym = p->data;
		p = p->succ;
		join_set(&sym->modset, func->vertex[0]);
		sym->rename_stack = new_stack();
		push(sym->rename_stack, sym);
	} while (p != h);

	modsets(func);
	insert_phi(func);
	rename_symbols(func->vertex[0]);

	p = h = func->var;
	do {
		sym = p->data;
		p = p->succ;
		free_stack(&sym->rename_stack);
	} while (p != h);

	free_list(&func->var);
}

static void fix_move(phi_t* phi, list_t** moves)
{
	stmt_t*		move;
	sym_t*		phi_dest;
	op_t		t;

	t = temp();

	phi_dest = phi->stmt->op[2].u.sym;
	phi->stmt->op[2].u.sym = t.u.sym;

	/* Save the real destination operand of the PHI function in
	 * move->op[1] and also tell the move which PHI this was.
	 */

	move = new_stmt(MOV, t, no_op, new_sym_op(phi_dest), line);
	move->op[1] = new_sym_op(phi_dest);
	move->phi = phi;

	/* This move will be put after all the normal moves inserted by
	 * from_ssa.
	 */
	insert_last(moves, move);
}

static void check_later_use(phi_t* phi, list_t* link, list_t** moves, int k)
{
	stmt_t*		stmt;

	link = link->succ;
	stmt = link->data;

	/* If there is a later use as a PHI-operand of the destination,
	 * then we must save the value so that use can consume it.
	 */

	while (stmt->type == PHI || stmt->type == NOP) {

		if (stmt->type == PHI
			&& is_sym(stmt->phi->rhs[k])
			&& stmt->phi->rhs[k].u.sym == phi->stmt->op[2].u.sym)
			fix_move(phi, moves);

		link = link->succ;
		stmt = link->data;
	}

}

static void insert_move(
	vertex_t*		pred,
	phi_t*		phi,
	int		k,
	list_t*		link,
	list_t**	moves)
{
	list_t*		p;
	stmt_t*		last_stmt;
	stmt_t*		stmt;
	stmt_t*		move;
	unsigned	line;
	op_t		op;

	/* We take as line number of our new move statement, the line
	 * number of the last statement in the basic block.
	 *
	 */

	last_stmt = pred->stmts->pred->data;
	assert(last_stmt->type == BA);

	line = last_stmt->line;

	check_later_use(phi, link, moves, k);

	op = new_sym_op(phi->stmt->op[2].u.sym);
	move = new_stmt(MOV, phi->rhs[k], no_op, op, line);

	p = pred->stmts->pred->pred;
	stmt = p->data;

	if (is_branch(stmt))
		insert_before(&p, move);
	else
		insert_after(&p, move);

}

static void insert_move_before_branch(vertex_t* w, stmt_t* move)
{
	list_t*		p;
	stmt_t*		stmt;

	if (w->stmts == NULL)
		return;

	assert(move->op[1].type != NO_OP);

	/* Now restore the PHI function so that it has the correct
	 * destination operand.
	 */

	move->phi->stmt->op[2] = move->op[1];
	move->op[1] = no_op;
	move->phi = NULL;

	p = w->stmts->pred->pred;
	stmt = p->data;

	if (is_branch(stmt))
		insert_before(&p, move);
	else
		insert_after(&p, move);
}

static void insert_move_list(vertex_t* w, list_t* moves)
{
	list_t*		p;

	p = moves;

	do {
		insert_move_before_branch(w, p->data);
		p = p->succ;
	} while (p != moves);
}

void from_ssa(func_t* func)
{
	vertex_t*	x;
	vertex_t*	pred;
	int		i;
	int		k;
	phi_t*		phi;
	stmt_t*		stmt;
	list_t*		q;
	list_t*		p;
	list_t*		more_moves;

	for (i = 1; i < func->nvertex; i += 1) {
		x = func->vertex[i];

		if (x == func->exit)
			continue;

		assert(x->stmts != NULL);

		p = x->pred;

		do {
			// Next predecessor vertex.
			pred = p->data;
			p = p->succ;
			k = which_pred(pred, x);

			// Find link of first PHI.
			q = x->stmts;
			q = q->succ;

			// Reset stmt to first PHI (which might be a NOP now).
			stmt = q->data;

			more_moves = NULL;

			while (stmt->type == PHI || stmt->type == NOP) {

				if (stmt->type == PHI) {
					phi = stmt->phi;
					insert_move(pred, phi, k, q,
						&more_moves);
				}

				q = q->succ;
				stmt = q->data;

			}

			if (more_moves != NULL) {
				insert_move_list(pred, more_moves);
				free_list(&more_moves);
			}

			q = q->succ;
			stmt = q->data;
		} while (p != x->pred);

		// Finally change each PHI into a NOP.
		q = x->stmts;
		q = q->succ;
		stmt = q->data;

		while (stmt->type == PHI || stmt->type == NOP) {
			stmt->type = NOP;
			q = q->succ;
			stmt = q->data;
		}
	}
}
