#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include "gh_cpp.h"

/* expression evaluation: interface fct: eval_expr(); no data exported */

static Stack	valstack[MAXSTACK];
static TS	*pp; /* parse point */
static int	valptr;
static Tokvals	lat;

extern char	ibuf[MAXIN];			/* gh_cpp2.c */
extern char	*filename, mychar, *myname;	/* gh_cpp1.c */
extern int	myval, lineno, verbose, misra_rules;		/* gh_cpp1.c */

static void	push_expr(int);
extern void	fatal_error(char *s);		/* gh_cpp1.c */
extern void	tokname(Tokvals, FILE *);	/* gh_cpp1.c */
extern void	show_line(int, FILE *);		/* gh_cpp1.c */
extern void	m_rule(int, int, char *);	/* gh_cpp5.c */

static int	interpret(void);

static void
syntax_error(char *s)
{
	fprintf(stderr, "%s,%d: expr: syntax error at '%s' (%s)\n",
		filename, lineno, ibuf, s);
	fprintf(stderr, "unexpected '");
	tokname(lat, stderr);
	fprintf(stderr, "'\n");

	show_line(0, stderr);
	exit(1);
}

static void
dump_stack(char *s)	/* verbose/debugging mode only */
{	int i;

	printf("=== ");
	printf("%s:\n", s);
	for (i = 0; i < valptr; i++)
	{	printf("%2d:	", i);
		tokname(valstack[i].tok, stdout);
		printf("[%d]", valstack[i].val);
		printf("\n");
	}
	printf("\n");
}

static Tokvals
nxt_token(void)
{
	if (!pp || !pp->nxt) return DONE;

	pp = pp->nxt;
	mychar = myval = pp->val;
	myname = pp->name;

	return pp->tok;
}

static void
emit(Tokvals n, int v)
{
	assert(n != CHAR);
	valstack[valptr].tok = n;
	valstack[valptr].val = v;
	if (++valptr >= MAXSTACK)
		syntax_error("formula too long");

	if (verbose>1) dump_stack("emit");
}

int
hexa(char *s)
{	int x = 0;
	int cnt = 0;

	for ( ; *s != '\'' && *s != '\0'; s++)
	{	cnt++;
		x = 16*x + *s;
		switch (*s) {
		case '0': case '1': case '2':
		case '3': case '4': case '5':
		case '6': case '7': case '8':
		case '9':
			x -= '0';
			break;
		case 'a': case 'b': case 'c':
		case 'd': case 'e': case 'f':
			x -= 'a' + 10;
			break;
		case 'A': case 'B': case 'C':
		case 'D': case 'E': case 'F':
			x -= 'A' + 10;
			break;
		default:
			fatal_error("bad hexadecimal char constant");
	}	}
	if (cnt == 0)
		fprintf(stderr, "%s,%d: warning, \\x with no hex digits\n",
			filename, lineno);


	return x;
}

int
octal(char *s)
{	int x = 0;
	int cnt = 0;

	for ( ; *s != '\'' && *s != '\0'; s++)
	{	if (++cnt > 3)
		{	x = (x << 8) + *s;
			continue;	/* octal sequence has only 3 significant digits */
		}
		x = 8*x + *s;
		switch (*s) {
		case '0': case '1': case '2':
		case '3': case '4': case '5':
		case '6': case '7': 
			x -= '0';
			break;
		default:
			fprintf(stderr, "saw character '%c'\n", *s);
			fatal_error("bad octal char constant");
	}	}

	if (cnt > 3)
		fprintf(stderr, "%s,%d: warning, multi-byte character constant\n",
			filename, lineno);

	return x;
}

static void
push_term(void)	/* (x), -x, ~x, !x, 9, NAME -- push onto evaluation stack */
{	Tokvals n = lat;

	switch (n) {
	case NAME:
		if (myname[0] == '"')	/* string */
			goto bad;
		if (myname[0] != '\'')	/* undefined macro name */
		{	if (misra_rules)
				m_rule(19, 11, "undefined macro name");
			myval = 0;
		} else	/* char constant, tokenized as a name */
		{	if (myname[1] == '\\')
			{	switch (myname[2]) {
				case 'n': myval = '\n'; break;
				case 'r': myval = '\r'; break;
				case 'f': myval = '\f'; break;
				case 't': myval = '\t'; break;
				case 'v': myval = '\v'; break;
				case 'b': myval = '\b'; break;
				case 'a': myval = '\a'; break;
				case 'x': case 'X':
					myval = hexa(&myname[3]);
					break;
				default:
					if (isdigit(myname[2]))
						myval = octal(&myname[2]);
					else
						myval = (int) myname[2];
					break;
			}	}
			else
			{	myval = myname[1];
		}	}
		/* fall thru */
	case VAL:
		emit(VAL, myval);
		lat = nxt_token();
		return;
	case CHAR:
		switch (mychar) {
		case '(':
			lat = nxt_token();
			push_expr(4);
			if (lat != CHAR || mychar != ')') break;
			lat = nxt_token();
			return;

		case '+': n = UPLUS; goto same;
		case '-': n = UMIN;  goto same;
		case '~': n = TILDE; goto same;
		case '!': n = LNOT;
same:			lat = nxt_token();
			push_term();
			assert(n != CHAR);
			emit(n, 0);
			return;
		}
		/* fall thru */
		fprintf(stderr, "CHAR: '%c'\n", mychar);
	default:
bad:		fprintf(stderr, "saw: "); tokname(n, stderr); fprintf(stderr, "\n");
		syntax_error("#if or #elif directive");
		break;
	}
}

#define IfNext(x, y)	if (pp->nxt && pp->nxt->tok == CHAR && pp->nxt->val == (x)) \
			{ pp = pp->nxt; lat = (y); goto yes; }

static void
push_expr(int prec)	/* precedence level prec -- push expr onto evaluation stack */
{	Tokvals t;
	int v;

	if (prec < 0) {	push_term(); return; }

	push_expr(prec-1);
again:
	if (lat == CHAR)
		switch (prec) {
		case 0:
			switch (mychar) {
			case '*': lat = TIMES; goto yes;
			case '/': lat = DIVIDE; goto yes;
			case '%': lat = MOD; goto yes;
			}
			break;
		case 1:
			switch (mychar) {
			case '+': lat = PLUS; goto yes;
			case '-': lat = MINUS; goto yes;
			}
			break;
		case 2:
			switch (mychar) {
			case '>': IfNext('=', GE); IfNext('>', RS); lat = GT; goto yes;
			case '<': IfNext('=', LE); IfNext('<', LS); lat = LT; goto yes;
			}
			break;
		case 3:
			switch (mychar) {
			case '=': IfNext('=', EQ); break;
			case '!': IfNext('=', NE); break;
			}
			break;
		case 4:
			switch (mychar) {
			case '|': IfNext('|',  LOR); lat = BOR; goto yes;
			case '&': IfNext('&', LAND); lat = BAND; goto yes;
			case '^': lat = XOR; goto yes;
			case '?': lat = QUEST; goto yes;
			case ':': lat = COLON; goto yes;
			}
			break;
		default:
			syntax_error("push_expr1");
		}
	else if (lat != DONE)
		syntax_error("push_expr2");
	return;
yes:
	assert(lat != VAL);
	t = lat;
	v = (int) mychar;

	lat = nxt_token(); /* can change lat and mychar */
	push_expr(prec-1);
	emit(t, v);
	goto again;
}

#define Two_Args(x)	w = interpret(); v = interpret(); emit(VAL, (x))
#define One_Arg(x)	v = interpret(); emit(VAL, (x))

static int	sh_err;
static char	err_s[1024];

static void
do_division(void)
{	int v, w;

	w = interpret();
	if (w == 0)
	{	strcpy(err_s, "divide by zero");
		if (!sh_err)	/* unless in a boolean subexpression */
			fatal_error("division by zero");
		v = interpret();
		emit(VAL, 0);
	} else
	{	v = interpret();
		emit(VAL, (v / w));
	}
}

static int
do_bool(int op)
{	int v, w;

	sh_err++;
	w = interpret();
	sh_err--;
	v = interpret();

	if ((op == LAND && v == 0)
	||  (op == LOR  && v != 0))
		strcpy(err_s, "");
	else if (sh_err == 0
	     &&  strlen(err_s) > 0)
		fatal_error(err_s);

	return (op == LOR) ? (v || w) : (v && w);
}

static int
do_shift(int op)
{	int v, w;

	sh_err++;
	w = interpret();
	v = interpret();
	sh_err--;

	if (w <= 0)
		strcpy(err_s, "shift by non-positive number");
	else if (w >= sizeof(long)*8)
		strcpy(err_s, "shift in preprocessor directive causes integer overflow");

	if (sh_err == 0
	&&  strlen(err_s) > 0)
	{	fprintf(stderr, "%s,%d: warning, %s\n",
			filename, lineno, err_s);
	}

	return (op == LS) ? (v << w) : (v >> w);
}

static void
do_colon(void)
{	int v, w, x;
	char err_t[1024];
	char err_f[1024];
	char err_o[1024];

	strcpy(err_o, err_s);

	sh_err++;
	v = interpret();	/* the else value */
	strcpy(err_f, err_s);	/* remember any error conditions */

	assert(valstack[--valptr].tok == QUEST);

	w = interpret();	/* the then value */
	strcpy(err_t, err_s);	/* remember any error conditions */
	sh_err--;

	x = interpret();	/* the condition */

	if (x)
	{	if (strlen(err_t) > 0)
		{	if (sh_err == 0)
				fatal_error(err_t);
			else
				strcpy(err_o, err_t);
		}
	} else
	{	if (strlen(err_f) > 0)
		{	if (sh_err == 0)
				fatal_error(err_f);
			else
				strcpy(err_o, err_f);
	}	}

	strcpy(err_s, err_o);
	emit(VAL, x?w:v);
}

static int
interpret(void)
{	int v, w;

	switch (valstack[--valptr].tok) {
	case VAL:	valptr++; break;
	case UMIN:	One_Arg(-(v)); break;
	case UPLUS:	One_Arg(+(v)); break;
	case TILDE:	One_Arg(~(v)); break;
	case LNOT:	One_Arg(!(v)); break;
	case TIMES:	Two_Args(v * w); break;
	case DIVIDE:	do_division(); break;
	case MOD:	Two_Args(v % w); break;
	case PLUS:	Two_Args(v + w); break;
	case MINUS:	Two_Args(v - w); break;
	case BAND:	Two_Args(v & w); break;
	case BOR:	Two_Args(v | w); break;
	case XOR:	Two_Args(v ^ w); break;
	case GT:	Two_Args(v > w); break;
	case LT:	Two_Args(v < w); break;
	case EQ:	Two_Args(v == w); break;
	case NE:	Two_Args(v != w); break;
	case GE:	Two_Args(v >= w); break;
	case LE:	Two_Args(v <= w); break;
	case LOR:	emit(VAL, do_bool(LOR)); break;
	case LAND:	emit(VAL, do_bool(LAND)); break;
	case LS:	emit(VAL, do_shift(LS)); break;
	case RS:	emit(VAL, do_shift(RS)); break;
	case QUEST:	syntax_error("internal error1"); break;
	case COLON:	do_colon(); break;
	default:	syntax_error("internal error2"); break;
	}

	if (verbose>1) dump_stack("now");

	assert(valstack[valptr-1].tok == VAL);
	return valstack[--valptr].val;
}

int
eval_expr(TS *p)
{	int v;

	if (!p
	||  !p->nxt
	||   p->tok != CHAR
	||   p->val != '#'
	||  !(p->nxt->tok == NAME)
	|| (strcmp(p->nxt->name, "if") != 0
	&&  strcmp(p->nxt->name, "elif") != 0))
		fatal_error("cannot happen, eval_expr");

	strcpy(err_s, "");

	pp = p->nxt;
	lat = nxt_token();
	push_expr(4);

	if (verbose>1) dump_stack("stack:");

	if (lat != DONE) syntax_error("bad expression");

	v = interpret();	/* evaluate expression on stack */
	assert(valptr == 0);
	if (verbose>1) printf("eval result: %d\n", v);
	return v?1:0;
}

