#ifndef stmt_h
#define stmt_h

#include "list.h"
#include "op.h"

typedef enum {
	NOP,		/* No operation. */											//0
	ADD,		/* Add. */															//1
	BT,		/* Branch to op[2] if op[0] is true. */		//2
	BF,		/* Branch to op[2] if op[0] is false. */	//3
	BA,		/* Branch always. */											//4
	DIV,		/* Divide. */														//5
	GET,		/* Get integer from stdin. */						//6
	LABEL,		/* A label. */												//7
	LD,		/* Load from memory. */										//8
	MOV,		/* Copy. */															//9
	MUL,		/* Multiply. */													//10
	NEG,		/* Negate. */														//11
	PHI,		/* Phi-function. */											//12
	PUT,		/* Print integer to stdout. */					//13
	RET,		/* Return. */														//14
	SEQ,		/* Set to true if ==. */								//15
	SGE,		/* Set to true if >=. */								//16
	SGT,		/* Set to true if >. */									//17
	SLE,		/* Set to true if <=. */								//18
	SLL,		/* Shift left logical. */								//19
	SLT,		/* Set to true if <. */									//20
	SRA,		/* Shift right arithmetic. */						//21
	SRL,		/* Shift right logical. */							//22
	SNE,		/* Set to true if !=. */								//23
	ST,		/* Store to memory. */										//24
	SUB,		/* Subtract. */													//25
	NSTMT																						//26
} stmt_type_t;

typedef enum {
	L_BOT,
	L_CONST,
	L_TOP,
} lattice_type_t;

typedef struct {
	lattice_type_t type;
	int value;
} lattice_t;

typedef struct {
	int		n;	/* Number of operands, ie size of rhs array. */
	op_t*		rhs;	/* Right-hand side, i.e. operands. */
	stmt_t*		stmt;	/* The statement which owns this phi func. */
} phi_t;

struct stmt_t {
	unsigned	index;	/* Serial number for debugging. */
	stmt_type_t	type;	/* What the statement does (ADD, SUB, etc). */
	op_t		op[3];	/* Three operands. */
	int		addr;	/* The instruction address of this statement. */
	unsigned	line;	/* Source code line number. */
	phi_t*		phi;	/* Used only by phi-functions. */
	bool live;
	int value;
	lattice_t lattice;
};

stmt_t* new_stmt(stmt_type_t type, op_t a, op_t b, op_t dest, unsigned line);
void free_stmt(stmt_t* stmt);
void emit(stmt_type_t type, op_t a, op_t b, op_t dest, unsigned line);
bool is_branch(stmt_t* stmt);
bool is_real(stmt_t* stmt);
instr_t make_instr(stmt_t*);
sym_t* defined_sym(stmt_t*);
void init_stmt(void);
void print_stmt(stmt_t* stmt, FILE* fp);
void set_stmt_addr(stmt_t* stmt, int addr);
void relocate(stmt_t* stmt);
op_t branch_dest(stmt_t* stmt);

#endif
