typedef enum {	DONE, NAME, CHAR, ECHAR, VAL,
		ARG, ARGSTRING, PLAINSTRING,
		TIMES, DIVIDE, MOD, PLUS, MINUS,	/* gh_cpp3.c */
		BOR, BAND, XOR, GT, LT, TILDE, LNOT,
		UMIN, UPLUS, EQ, NE, GE, LE, LOR, LAND, LS, RS,
		QUEST, COLON,
		TPASTE	/* token pasting symbol */
	     }	Tokvals;

typedef struct TS   TS;
typedef struct ARL  ARL;
typedef struct ARGS ARGS;
typedef struct MD   MD;
typedef struct ML   ML;
typedef struct Stack Stack;

struct TS {	/* token structure */
	Tokvals	tok;
	int	val;
	char	*name;
	int	space;	/* white space preceding this token */
	ML	*ml;	/* list of macros used to produce this token */
	TS	*prv;
	TS	*nxt;
};

struct ML {	/* list of ptrs to macros */
	MD	*m;
	ML	*nxt;
};

struct ARL {	/* actual param list */
	TS	*al;	/* macro expanded */
	TS	*oal;	/* original */
	ARL	*nxt;
};

struct ARGS {	/* formal param list */
	char	*nm;
	ARGS	*nxt;
};

struct MD {	/* macro definition */
	char	*nm;
	int 	ln;
	char	*fnm;
	ARGS	*arg;	/* formal params */
	TS	*body;
	MD	*nxt;
};

struct Stack {	/* evaluation stack for #if expressions */
	int val;
	Tokvals tok;
};

#define MAXIN		4096	/* max size of a line before expansion */
#define MAXSTACK	256	/* max depth of eval stack for if expr */
#define MAXLEVEL	256	/* nesting of if/endif pairs */
