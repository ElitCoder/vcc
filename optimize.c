#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <string.h>
#include "util.h"
#include "func.h"
#include "cfg.h"
#include "globals.h"
#include "error.h"
#include "list.h"
#include "optimize.h"
#include "sym.h"
#include "stmt.h"

void rdf(vertex_t* u)
{
	if(u == NULL) {
		return;
	}

	rdf(u->rdomchild);
	rdf(u->rdomsibling);

	list_t *succ = u->rsucc;

	if(succ != NULL) {
		do {
			vertex_t *v_succ = succ->data;
			succ = succ->succ;

			if(v_succ == NULL) {
				continue;
			}

			if(v_succ->idom == u) {
				continue;
			}

			join_set(&u->rdf, v_succ);
		} while(succ != u->rsucc);
	}

	vertex_t **a;
	size_t n;

	vertex_t *child = u->rdomchild;

	while(child != NULL) {
		a = set_to_array(child->rdf, &n);

		for(int i = 0; i < n; i++) {
			if(a[i]->ridom != u) {
				join_set(&u->rdf, a[i]);
			}
		}

		free(a);
		child = child->rdomsibling;
	}
}

bool rvisited(vertex_t* v)
{
	return v->rdfnum != -1;
}

void rdfs(vertex_t* v, int* dfnum, vertex_t** vertex)
{
	v->rdfnum = *dfnum;
	vertex[*dfnum] = v;
	v->rsdom = v;
	v->rancestor = NULL;
	*dfnum = *dfnum + 1;

  list_t *succ = v->rsucc;

	if(succ == NULL) {
		return;
	}

  do {
    vertex_t *v_succ = succ->data;
    succ = succ->succ;

    if(v_succ == NULL || rvisited(v_succ)) {
      continue;
    }

    v_succ->rparent = v;
    rdfs(v_succ, dfnum, vertex);
  } while(succ != v->rsucc);
}

void rlink(vertex_t* parent, vertex_t* child)
{
	child->rancestor = parent;
}

vertex_t* reval(vertex_t* v)
{
	vertex_t*		u;

	u = v;

	while (v->rancestor != NULL) {

		if (v->rsdom->rdfnum < u->rsdom->rdfnum)
			u = v;

		v = v->rancestor;
	}

	return u;
}

void rdominance(func_t* func)
{
	int		i;
	int		dfnum;
	vertex_t*	u;
	vertex_t*	v;
	vertex_t*	w;
	list_t*		p;
	list_t*		h;
	vertex_t*	original[func->nvertex];

	memcpy(original, func->vertex, sizeof original);

  vertex_t *temp = func->exit;
  func->exit = func->start;
  func->start = temp;

	dfnum = 0;
	rdfs(func->start, &dfnum, original);

	func->start->ridom = func->start;

	for (i = func->nvertex - 1; i > 0; i--) {
		w = original[i];
		p = h = w->rpred;

		do {
			v = p->data;
			p = p->succ;

			u = reval(v);

			if(u->rsdom->rdfnum < w->rsdom->rdfnum) {
				w->rsdom = u->rsdom;
			}
		} while (p != h);

		rlink(w->rparent, w);
		insert_first(&w->rsdom->rbucket, w);

		p = h = w->rparent->rbucket;

		if (p == NULL)
			continue;

		do {

			v = p->data;
			p = p->succ;
			u = reval(v);

			if(u->rsdom->rdfnum < v->rsdom->rdfnum) {
				v->ridom = u;
			}

			else {
				v->ridom = w->rparent;
			}

		} while (p != h);

		free_list(&w->rparent->rbucket);
	}

	for (i = 1; i < func->nvertex; i++) {
		w = original[i];

		if(w->ridom != w->rsdom) {
			w->ridom = w->ridom->ridom;
		}

		w->rdomsibling = w->ridom->rdomchild;
		w->ridom->rdomchild = w;
	}

	func->start->ridom = NULL;

	temp = func->exit;
  func->exit = func->start;
  func->start = temp;
}

void dce_make_rcfg(func_t *func, list_t **edges) {
	for(unsigned i = 0; i < func->nvertex; i++) {
		vertex_t *v = func->vertex[i];

		for(unsigned j = 0; j < MAX_SUCC; j++) {
			if(v->succ[j] != NULL) {
				insert_last(&v->succ[j]->rsucc, v);
				insert_last(&v->rpred, v->succ[j]);
			}
		}
	}

	rdominance(func);
	rdf(func->exit);
}

bool is_prelive(stmt_t *s) {
	switch(s->type) {
		case RET: case PUT: case GET: case ST:
			return true;
		default: return false;
	}
}

vertex_t *get_vertex(func_t *func, stmt_t *s) {
	for(unsigned i = 0; i < func->nvertex; i++) {
		vertex_t *w = func->vertex[i];

		if(w == NULL) {
			continue;
		}

		list_t *stmts = w->stmts;

		if(stmts == NULL) {
			continue;
		}

		do {
			stmt_t *t = stmts->data;
			stmts = stmts->succ;

			if(t == s) {
				return w;
			}
		} while(stmts != w->stmts);
	}

	return NULL;
}

bool dce_dominates(vertex_t *w, vertex_t *u, vertex_t *start) {
	if(w == NULL || u == NULL){
		return false;
	}

	if(w == u) {
		return true;
	}

	bool found = dce_dominates(w->domchild, u, start);

	if(found != true) {
		if(start != w) {
			found = dce_dominates(w->domsibling, u, start);
		}
	}

	return found;
}

void dce_add_operand(func_t *func, vertex_t *w, vertex_t *u, vertex_t *v) {
	list_t *w_stmts = w->stmts;

	if(w_stmts == NULL) {
		return;
	}

	do {
		stmt_t *w_phi = w_stmts->data;
		w_stmts = w_stmts->succ;

		if(w_phi == NULL) {
			continue;
		}

		if(w_phi->type == PHI) {
			bool found = false;

			op_t phi_op;
			phi_op.type = SYM_OP;
			phi_op.u.sym = NULL;
			phi_op.v = u;

			unsigned n = w_phi->phi->n;

			for(unsigned i = 0; i < n; i++) {
				op_t *omega = &w_phi->phi->rhs[i];

				op_t tempOmega;
				tempOmega.type = SYM_OP;
				tempOmega.u.sym = NULL;
				tempOmega.v = u;
				tempOmega.def = NULL;

				if(!is_sym(*omega)) {
					if(is_num(*omega)) {
						tempOmega.type = NUM_OP;
						tempOmega.u.num = omega->u.num;
						tempOmega.def = omega->def;
					}

					else {
						continue;
					}
				}

				else {
					tempOmega.def = get_vertex(func, omega->u.sym->def);
					tempOmega.u.sym = omega->u.sym;
				}

				if(dce_dominates(tempOmega.def, u, tempOmega.def) && (found == false || dce_dominates(phi_op.def, tempOmega.def, phi_op.def))) {
					phi_op = tempOmega;
					found = true;

					switch(phi_op.type) {
						case NUM_OP: printf("dce_add_operand: updated with num_op\n");
							break;
						default: break;//printf("dce_add_operand: updated with sym_op\n");
					}
				}
			}

			if(!found) {
				printf("dce_add_operand: Sigma = NULL, no omega dom(u)\n");
				continue;
			}

			assert(found);

			phi_t *op_phi = new_phi(w);
			op_phi->stmt = w_phi;

			printf("Updating with PHI (n %d)", op_phi->n);

		/*	for(unsigned i = 0; i < w_phi->phi->n; i++){
					op_phi->rhs[i] = w_phi->phi->rhs[i];
			}*/

			unsigned j = 0;
			for(unsigned i = 0; i < w_phi->phi->n; i++) {
				vertex_t *vertex = NULL;
				vertex_t *def = NULL;

				if(w_phi->phi->rhs[i].type == NUM_OP) {
					vertex = w_phi->phi->rhs[i].v;
					def = w_phi->phi->rhs[i].def;
				}

				else {
					def = get_vertex(func, w_phi->phi->rhs[i].u.sym->def);

					list_t *cprop_pred = w->pred;
					unsigned iterate = 0;

					do {
						vertex_t *current_pred = cprop_pred->data;
						cprop_pred = cprop_pred->succ;

						if(i == iterate) {
							vertex = current_pred;

							break;
						}

						iterate++;
					} while(cprop_pred != w->pred);
				}

				if(def == u) {
					i++;
				}

				printf("VERTEX %d\n", vertex->dfnum);

				if(w_phi->phi->rhs[i].type == SYM_OP) {
					printf("%s ", w_phi->phi->rhs[i].u.sym->id);
				}

				else {
					printf("%d ", w_phi->phi->rhs[i].u.num);
				}

				op_phi->rhs[j] = w_phi->phi->rhs[i];
				//printf("%s (def %d)", op_phi->rhs[j].u.sym->id, get_vertex(func, w_phi->phi->rhs[i].u.sym->def)->dfnum);
				j++;
			}

			op_phi->rhs[op_phi->n - 1] = phi_op;
			list_t *phi_list = w->phi_func_list;

			do {
				phi_t *phi_phi = phi_list->data;

				if(phi_phi == w_phi->phi) {
					phi_list->data = op_phi;
					break;
				}

				phi_list = phi_list->succ;
			} while(phi_list != w->phi_func_list);
			free_phi(w_phi->phi);
			w_phi->phi = op_phi;
		}
	} while(w_stmts != w->stmts);
}

void dce_simplify(func_t *func) {
	func->exit->live = true;
	bool modified = false;

	for(unsigned i = 0; i < func->nvertex; i++) {
		vertex_t *u = func->vertex[i];

		if(u == NULL) {
			continue;
		}

		if(u->dfnum == -1) {
			continue;
		}

		if(!u->live) {
			continue;
		}

		for(unsigned j = 0; j < MAX_SUCC; j++) {
			if(u->succ[j] == NULL) {
				continue;
			}

			vertex_t *v = u->succ[j];

			if(v->live) {
				continue;
			}

			//printf("dce: u:s (%d) successor v (%d) is not live with j=%d\n", u->dfnum, v->dfnum, j);

			vertex_t *w = v->ridom;
			//printf("dce: u:s (%d) successor v (%d) got ridom w (%d)\n", u->dfnum, v->dfnum, w->dfnum);

			while(!w->live) {
				w = w->ridom;
				//printf("dce: updated w (%d)\n", w->dfnum);

				if(w->ridom == NULL) {
					//printf("ERROR_dce: w->ridom = NULL\n");
					break;
				}
			}


			//bool foundU = false;
			//insert_last(&w->pred, u);
		//	printf("dce: removed v (%d) as predecessor for w (%d)\n", v->dfnum, w->dfnum);


/*
			list_t *list_find = w->pred;
			unsigned place = 0;

			do {
				vertex_t *find_vertex = list_find->data;

				if(find_vertex == v) {
					printf("V was here\n");

				}

				if(find_vertex == u) {
					foundU = true;
					printf("FOUND U\n");

					break;
				}

				list_find = list_find->succ;
				place++;
			} while(list_find != w->pred);

			if(!foundU) {
				insert_last(&w->pred, u);
				printf("Inserted U\n");
			}*/


			//printf("dce: added u(%d) as predecessor for w (%d)", u->dfnum, w->dfnum);
			u->succ[j] = w;
			//printf("dce: added w (%d) as u:s (%d) successor with j=%d\n", w->dfnum, u->dfnum, j);



			list_t *s_list = u->stmts;

			do {
				stmt_t *s = s_list->data;
				s_list = s_list->succ;


				if(s->type == BA || s->type == BF || s->type == BT) {
					printf("%s\n", s->op[2].u.sym->id);
					printf("%s\n", v->label.u.sym->id);


					if(s->op[2].u.sym->id == v->label.u.sym->id) {
						s->op[2] = w->label;
						printf("UPDATED\n");
					}
				}

			} while(s_list != u->stmts);

			dce_add_operand(func, w, u, v);
			insert_last(&w->pred, u);



			modified = true;
		}
	}

	if(modified) {
		printf("dce: running dominance\n");
		dominance(func);
		//printf("dce: after dominance\n");
	}

	else {
		printf("the graph was not modified wtf?\n");
	}

	printf("Simplify was done\n");
}

void dce(func_t *func) {
	list_t *worklist = NULL;

	for(unsigned i = 0; i < func->nvertex; i++) {
		vertex_t *v = func->vertex[i];
		v->live = false;

		if(v == NULL) {
			continue;
		}

		list_t *stmts = v->stmts;

		if(stmts == NULL) {
			continue;
		}

		do {
			stmt_t *s = stmts->data;
			stmts = stmts->succ;

			if(is_prelive(s)) {
				s->live = true;
				insert_last(&worklist, s);
			}

			else {
				s->live = false;
			}
		} while(stmts != v->stmts);
	}

	while(length(worklist) != 0) {
		stmt_t *s = remove_first(&worklist);
		vertex_t *w = get_vertex(func, s);
		assert(w);

		w->live = true;

		if(s->type == PHI) {
			unsigned n = s->phi->n;
			op_t *op = s->phi->rhs;

			for(unsigned i = 0; i < n; i++) {
				if(is_sym(op[i])) {
					stmt_t *def = op[i].u.sym->def;

					if(!def->live) {
						def->live = true;
						insert_last(&worklist, def);
					}
				}
			}
		}

		else {
			for(unsigned i = 0; i < 2; i++) {
				if(is_sym(s->op[i])) {
					stmt_t *def = s->op[i].u.sym->def;

					if(!def->live) {
						def->live = true;
						insert_last(&worklist, def);
					}
				}
			}
		}

		size_t n;
		vertex_t **a = set_to_array(w->rdf, &n);

		if(a == NULL) {
			continue;
		}

		for(unsigned i = 0; i < n; i++) {
			list_t *cd_stmts = a[i]->stmts;

			if(cd_stmts == NULL) {
				continue;
			}

			do {
				stmt_t *cd_s = cd_stmts->data;
				cd_stmts = cd_stmts->succ;

				if(cd_s->type == BT || cd_s->type == BF) {
					if(!cd_s->live) {
						cd_s->live = true;
						insert_last(&worklist, cd_s);
					}
				}
			} while(cd_stmts != a[i]->stmts);
		}
	}

	for(unsigned i = 0; i < func->nvertex; i++) {
		vertex_t *v = func->vertex[i];

		if(v == NULL) {
			continue;
		}

		list_t *stmts = v->stmts;

		if(stmts == NULL) {
			continue;
		}

		do {
			stmt_t *s = stmts->data;
			stmts = stmts->succ;

			if(!s->live && s->type != LABEL) {
				if(s->type != BT && s->type != BF && s->type != BA) {
					if(s->type == PHI) {
						remove_from_list(&v->phi_func_list, s->phi);

						list_t *last_phi = stmts;

						while(((stmt_t*)last_phi->data)->type == PHI && last_phi != stmts->pred) {
							last_phi = last_phi->succ;
						}

						last_phi = last_phi->pred;

						if(last_phi->data != s) {
							void *data = last_phi->data;
							last_phi->data = stmts->pred->data;
							stmts->pred->data = data;
						}

						free(s->phi);
						s->phi = NULL;
					}

					s->type = NOP;
				}
			}
		} while(stmts != v->stmts);
	}

	dce_simplify(func);
}

bool cprop_is_executable(vertex_t *pred, vertex_t *succ) {
	for(unsigned i = 0; i < MAX_SUCC; i++) {
		if(pred->succ[i] == NULL) {
			continue;
		}

		if(pred->succ[i] == succ) {
			if(pred->succ_executable[i]) {
				return true;
			}

			return false;
		}
	}

	printf("cprop_is_executable: did not find arc\n");

	return false;
}

void cprop_set_executable(vertex_t *from, vertex_t *to) {
	for(unsigned i = 0; i < MAX_SUCC; i++) {
		if(from->succ[i] == NULL) {
			continue;
		}

		if(from->succ[i] == to) {
			from->succ_executable[i] = true;

			return;
		}
	}

	printf("cprop_set_executable: did not find successor\n");
}

void cprop_finalize(func_t *func) {
	for(unsigned i = 0; i < func->nvertex; i++) {
		vertex_t *v = func->vertex[i];

		if(v == NULL) {
			continue;
		}

		list_t *v_stmt = v->stmts;

		if(v_stmt == NULL) {
			continue;
		}

		do {
			//printf("CRASHED HERE?\n");

			stmt_t *stmt = v_stmt->data;
			v_stmt = v_stmt->succ;

			//printf("but now man?\n");

			if(stmt->lattice.type == L_CONST) {
				switch(stmt->type) {
					case ADD:	case PHI: case SUB: case DIV: case MUL: case NEG: case SEQ: case SGE: case SGT: case SLE: case SLT:	case SNE:
					{
						if(stmt->type == PHI) {
							remove_from_list(&v->phi_func_list, stmt->phi);

							list_t *last_phi = v_stmt;

							while(((stmt_t*)last_phi->data)->type == PHI && last_phi != v_stmt->pred) {
								last_phi = last_phi->succ;
							}

							last_phi = last_phi->pred;

							if(last_phi->data != stmt) {
								void *data = last_phi->data;
								last_phi->data = v_stmt->pred->data;
								v_stmt->pred->data = data;
							}

							free(stmt->phi);
							stmt->phi = NULL;
						}

						stmt->type = NOP;
						list_t *uses = stmt->op[2].u.sym->uses;

						if(uses == NULL) {
							continue;
						}

						do {
							stmt_t *u_stmt = uses->data;
							uses = uses->succ;

							if(u_stmt->type == PHI) {
								phi_t *phi = u_stmt->phi;

								for(unsigned i = 0; i < phi->n; i++) {
									if(phi->rhs[i].type == SYM_OP) {
										if(stmt->op[2].u.sym == phi->rhs[i].u.sym) {
											phi->rhs[i] = new_num_op(stmt->lattice.value);
											phi->rhs[i].def = v;

											list_t *cprop_pred = get_vertex(func, phi->stmt)->pred;
											unsigned iterate = 0;

											do {
												vertex_t *current_pred = cprop_pred->data;
												cprop_pred = cprop_pred->succ;

												if(i == iterate) {
													phi->rhs[i].v = current_pred;

													break;
												}

												iterate++;
											} while(cprop_pred != get_vertex(func, phi->stmt)->pred);
										}
									}
								}
							}

							else {
								for(unsigned i = 0; i < 2; i++) {
									if(u_stmt->op[i].type == SYM_OP) {
										if(stmt->op[2].u.sym == u_stmt->op[i].u.sym) {
											u_stmt->op[i] = new_num_op(stmt->lattice.value);
											u_stmt->op[i].def = v;

											list_t *cprop_pred = get_vertex(func, u_stmt)->pred;
											unsigned iterate = 0;

											do {
												vertex_t *current_pred = cprop_pred->data;
												cprop_pred = cprop_pred->succ;

												if(i == iterate) {
													u_stmt->op[i].v = current_pred;

													break;
												}

												iterate++;
											} while(cprop_pred != get_vertex(func, u_stmt)->pred);
										}
									}
								}
							}
						} while(uses != stmt->op[2].u.sym->uses);
					break;
					}

					default:
						break;
				}
			}
		} while(v_stmt != v->stmts);
	}
}

lattice_t cprop_meet(lattice_t *x, lattice_t *y) {
	lattice_t result;
	result.type = L_TOP;

	if(x->type == L_BOT || y->type == L_BOT) {
		result.type = L_BOT;
	}

	else if(x->type == L_TOP && y->type == L_TOP) {
		result.type = L_TOP;
	}

	else if(x->type == L_TOP && y->type == L_CONST) {
		result.type = L_CONST;
		result.value = y->value;
	}

	else if(x->type == L_CONST && y->type == L_TOP) {
		result.type = L_CONST;
		result.value = x->value;
	}

	else if(x->type == L_CONST && y->type == L_CONST) {
		if(x->value == y->value) {
			result.type = L_CONST;
			result.value = x->value;
		}

		else {
			result.type = L_BOT;
		}
	}

	return result;
}

void cprop_ba(func_t *func) {
	for(unsigned i = 0; i < func->nvertex; i++) {
		vertex_t *v = func->vertex[i];
		list_t *current = v->stmts;

		if(current == NULL) {
			continue;
		}

		bool inserted = false;

		do {
			stmt_t *s = current->data;
			current = current->succ;

			if(inserted) {
				s->type = NOP;

				continue;
			}

			if(s == NULL) {
				break;
			}

			if(s->type != BT && s->type != BF) {
				continue;
			}

			if(s->lattice.type != L_CONST) {
				continue;
			}

			s->type = BA;
			v->succ[1] = v->succ[s->lattice.value];

			assert(v->succ[1]);
			inserted = true;
		} while(current != v->stmts);
	}
}

void visit_stmt(vertex_t *w, stmt_t *t, list_t **edge_worklist, list_t **ssa_worklist){
	vertex_edge_t* edge;

	lattice_t result;

	switch(t->type){
		case BF: case BT:
		{
			bool added = false;

			result.type = L_TOP;

			if(is_num(t->op[0])) {
				result.type = L_CONST;
				result.value = t->op[0].u.num;
			}

			else if(is_sym(t->op[0])) {

				result = t->op[0].u.sym->def->lattice;
			}

			if(result.type == L_CONST) {
				edge = malloc(sizeof(vertex_edge_t));
				edge->from = w;

				if(t->type == BF ? result.value <= 0 : result.value > 0) { //IS FALSE, ADD ARC
					edge->to = w->succ[0];
					result.value = 0;
				}

				else {
					edge->to = w->succ[1];
					result.value = 1;
				}

				insert_last(edge_worklist, edge);
				added = true;
			}

			if(result.type < t->lattice.type) {
				t->lattice = result;
			}

			if(!added) {
				edge = malloc(sizeof(vertex_edge_t));
				edge->from = w;
				edge->to = w->succ[0];

				insert_last(edge_worklist, edge);

				edge = malloc(sizeof(vertex_edge_t));
				edge->from = w;
				edge->to = w->succ[1];

				insert_last(edge_worklist, edge);
			}
			break;
		}

		case BA:
			edge = malloc(sizeof(vertex_edge_t));
			edge->from = w;
			edge->to = w->succ[1];

			insert_last(edge_worklist, edge);
			break;

		case PHI:
			result.type = L_TOP;

			list_t *current = w->pred;
			unsigned i = 0;

			do{
				if(cprop_is_executable(current->data, w)) {
					lattice_t value = t->phi->rhs[i].u.sym->def->lattice;

					result = cprop_meet(&result, &value);
				}

				current = current->succ;
				i++;
			} while(current != w->pred);

			if(result.type < t->lattice.type) {
				t->lattice = result;

				list_t *current = t->op[2].u.sym->uses;

				do {
					if(current == NULL) {
						break;
					}

					insert_last(ssa_worklist, current->data);

					current = current->succ;
				} while(current != t->op[2].u.sym->uses);
			}
			break;

		case MOV: case NEG:
			result.type = L_TOP;

			if(is_sym(t->op[0])) {
				result = t->op[0].u.sym->def->lattice;
			}

			else if(is_num(t->op[0])){
				result.type = L_CONST;

				if(t->type == MOV) {
					result.value = t->op[0].u.num;
				}

				else if(t->type == NEG) {
					result.value = (-1) * t->op[0].u.num;
				}
			}

			if(result.type < t->lattice.type) {
				t->lattice = result;

				list_t *current = t->op[2].u.sym->uses;

				if(current != NULL) {
					do {
						insert_last(ssa_worklist, current->data);

						current = current->succ;
					} while(current != t->op[2].u.sym->uses);
				}
			}
			break;

		case ADD: case SUB: case DIV: case MUL: case SLT: case SEQ: case SGE: case SGT: case SLE: case SNE:
			result.type = L_TOP;

			lattice_t left_lattice;
			left_lattice.type = L_TOP;

			lattice_t right_lattice;
			right_lattice.type = L_TOP;

			if(is_sym(t->op[0])) {
				left_lattice = t->op[0].u.sym->def->lattice;
			}

			else if(is_num(t->op[0])) {
				left_lattice.type = L_CONST;
				left_lattice.value = t->op[0].u.num;
			}

			if(is_sym(t->op[1])) {
				right_lattice = t->op[1].u.sym->def->lattice;
			}

			else if(is_num(t->op[1])) {
				right_lattice.type = L_CONST;
				right_lattice.value = t->op[1].u.num;
			}

			if(left_lattice.type == L_CONST && right_lattice.type == L_CONST) {
				result.type = L_CONST;

				switch(t->type) {
					case ADD: result.value = left_lattice.value + right_lattice.value;
						break;
					case SUB: result.value = left_lattice.value - right_lattice.value;
						break;
					case MUL: result.value = left_lattice.value * right_lattice.value;
						break;
					case DIV: result.value = left_lattice.value / right_lattice.value;
						break;
					case SLT: result.value = left_lattice.value < right_lattice.value ? 1 : 0;
						break;
					case SEQ: result.value = left_lattice.value == right_lattice.value ? 1 : 0;
						break;
					case SGE: result.value = left_lattice.value >= right_lattice.value ? 1 : 0;
						break;
					case SGT: result.value = left_lattice.value > right_lattice.value ? 1 : 0;
						break;
					case SLE: result.value = left_lattice.value <= right_lattice.value ? 1 : 0;
						break;
					case SNE: result.value = left_lattice.value != right_lattice.value ? 1 : 0;
						break;
					default: result.value = 0; printf("visit_stmt: missing arithmetic type %d\n", t->type);//NOT GOOD
						//result.type = L_BOT;
						break;
				}
			}

			else if(left_lattice.type == L_BOT || right_lattice.type == L_BOT) {
				result.type = L_BOT;
			}

			if(result.type < t->lattice.type) {
				t->lattice = result;

				list_t *current = t->op[2].u.sym->uses;

				do {
					insert_last(ssa_worklist, current->data);

					current = current->succ;
				} while(current != t->op[2].u.sym->uses);
			}
		break;

		default: break;
	}
}

void visit_vertex(vertex_t *w, list_t **edge_worklist, list_t **ssa_worklist){
	bool onlyphi = w->visited;
	w->visited = true;
  list_t *current = w->stmts;

	if(current == NULL) {
		printf("visit_vertex: w->stmts == NULL\n");

		return;
	}

	do{
		stmt_t *data = current->data;
		current = current->succ;

		if(current == NULL) {
			printf("visit_vertex: current list object == NULL\n");
		}

		if(data == NULL) {
			printf("visit_vertex: current statement == NULL\n");
		}

		if(onlyphi && data->phi == NULL){
			continue;
		}

		visit_stmt(w, data, edge_worklist, ssa_worklist);
	} while(current != w->stmts);
}

void cprop(func_t *func) {
	list_t *ssa_worklist = NULL;
	list_t *edge_worklist = NULL;

	for(unsigned i = 0; i < func->nvertex; i++) {
		vertex_t *w = func->vertex[i];
		w->visited = false;

		for(unsigned j = 0; j < MAX_SUCC; j++) {
			w->succ_executable[j] = false;
		}

		if(w == NULL) {
			continue;
		}
		list_t *w_stmt = w->stmts;

		if(w_stmt == NULL) {
			continue;
		}

		do {
			stmt_t *s = w_stmt->data;
			w_stmt = w_stmt->succ;

			s->lattice.type = L_TOP;
		} while(w_stmt != w->stmts);
	}

	visit_vertex(func->start->succ[1], &edge_worklist, &ssa_worklist);

	while(length(edge_worklist) != 0 || length(ssa_worklist) != 0){
		if(length(edge_worklist) != 0){
			vertex_edge_t *edge = remove_first(&edge_worklist);

			if(!cprop_is_executable(edge->from, edge->to)) {
				cprop_set_executable(edge->from, edge->to);
				visit_vertex(edge->to, &edge_worklist, &ssa_worklist);
			}

			free(edge);
		}

		if(length(ssa_worklist) != 0){
			stmt_t *t = remove_first(&ssa_worklist);
			visit_stmt(get_vertex(func, t), t, &edge_worklist, &ssa_worklist);
		}
	}

	cprop_finalize(func);
	cprop_ba(func);
}

void optimize(func_t* func) {
	cprop(func);

	list_t *edges = NULL;
	dce_make_rcfg(func, &edges);
	dce(func);

	//dominance(func);

	printf("optimize done\n");
}
