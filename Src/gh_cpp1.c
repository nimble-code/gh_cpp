#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <malloc.h>
#include "gh_cpp.h"

#define RECURSE			/* enable recursive macro expansion */
#undef DEBUG

static MD	*md;		/* list of macro defs */
static ARGS	*ca;		/* macro arguments */
static ARGS	*sfa;		/* start of formal arg list */
static ARL	*saa;		/* start of actual arg list */
static TS	*cb;		/* body of a macro definition */
static TS	*inl, *start, *frst, *lst, *last;
static TS	*free_ts;
static ML	*free_ml;
static char	lbuf[MAXIN];
static char	sbuf[MAXIN];
static int	numbered, Enesting, explanations, BlockDepth;


static char *predefs[] = {
	"__DATE__",
	"__TIME__",
	"__FILE__",
	"__LINE__",
	"__INCLUDE_LEVEL__",
	"__STDC__",
	"__STDC_HOSTED__",
	"__STDC_VERSION__",
	0,
};

char	*filename = "<predef>";
char	*now, mychar, *myname;	/* values returned by lexer */

int	verbose, no_includes, misra_rules, debugging;
int	lineno, white, sawcode, incomment, main_only;
int	myval, level, not_printing[MAXLEVEL];

extern char	ibuf[MAXIN];			/* gh_cpp2.c */
extern int	stack_depth;			/* gh_cpp2.c */

extern void	add_sysdir(char *);		/* gh_cpp2.c */
extern void	do_file(char *, int, char *);	/* gh_cpp2.c */
extern int	do_include(int, char *);	/* gh_cpp2.c */
extern int	eval_expr(TS *);		/* gh_cpp3.c */
extern void	need_more(void);		/* gh_cpp2.c */
extern char	*next_file(char *);		/* gh_cpp2.c */
extern void	show_expl(FILE *, TS *);	/* gh_cpp4.c */
extern void	m_rule(int, int, char *);	/* gh_cpp5.c */
extern void	show_violations(void);		/* gh_cpp5.c */

void
fatal_error(char *s)
{
	fprintf(stderr, "%s,%d: error: %s\n", filename, lineno, s);
	fprintf(stderr, "line: %s\n", ibuf);

	if (misra_rules > 1) show_violations();
	exit(1);
}

char *
emalloc(int n)
{	char *ptr;
#ifdef PC
	int m = n%sizeof(unsigned long);
	if (m != 0) n += sizeof(unsigned long)-m;
#endif
	ptr = (char *) malloc(n);
	if (!ptr) fatal_error("out of memory");
	memset(ptr, 0, n);
	return ptr;
}

static void
nested(char *s)
{	int i;
	for (i = 0; i < Enesting; i++)
		printf("\t");
	printf("%s", s);
}

void
tokname(Tokvals t, FILE *fd)
{
	switch (t) {
	case DONE:	fprintf(fd, "End-of-line"); break;
	case CHAR:	fprintf(fd, "Character"); break;
	case ECHAR:	fprintf(fd, "Escaped Character"); break;
	case NAME:	fprintf(fd, "NAME"); break;
	case ARG:	fprintf(fd, "ARG"); break;
	case ARGSTRING:	fprintf(fd, "ARGSTRING"); break;
	case PLAINSTRING: fprintf(fd, "#NAME"); break;
	case VAL:	fprintf(fd, "Value"); break;
	case BAND:	fprintf(fd, "&"); break;
	case BOR:	fprintf(fd, "|"); break;
	case DIVIDE:	fprintf(fd, "/"); break;
	case EQ:	fprintf(fd, "=="); break;
	case GE:	fprintf(fd, ">="); break;
	case GT:	fprintf(fd, ">"); break;
	case LAND:	fprintf(fd, "&&"); break;
	case LE:	fprintf(fd, "<="); break;
	case LNOT:	fprintf(fd, "!"); break;
	case LOR:	fprintf(fd, "||"); break;
	case LS:	fprintf(fd, "<<"); break;
	case LT:	fprintf(fd, "<"); break;
	case MINUS:	fprintf(fd, "-"); break;
	case MOD:	fprintf(fd, "%%"); break;
	case NE:	fprintf(fd, "!="); break;
	case PLUS:	fprintf(fd, "+"); break;
	case RS:	fprintf(fd, ">>"); break;
	case TILDE:	fprintf(fd, "~"); break;
	case TIMES:	fprintf(fd, "*"); break;
	case UMIN:	fprintf(fd, ".-"); break;
	case UPLUS:	fprintf(fd, ".+"); break;
	case XOR:	fprintf(fd, "^"); break;
	case QUEST:	fprintf(fd, "?"); break;
	case COLON:	fprintf(fd, ":"); break;
	case TPASTE:	fprintf(fd, "TPASTE"); break;
	}
}

static void
tokfull(TS *n, FILE *fd)
{
	tokname(n->tok, fd);
	switch (n->tok) {
	case NAME: fprintf(fd, " <%s> ", n->name); break;
	case CHAR: fprintf(fd, " <%c> ", n->val); break;
	case ECHAR: fprintf(fd, " <\\%c> ", n->val); break;
	case VAL: fprintf(fd, " <%d> ", n->val); break;
	default: fprintf(fd, " <?> "); break;
	}
}

void
skipwhite(void)
{
	white = 0;
	while (*now == ' ' || *now == '\t')
	{	if (*now == ' ')
			white++;
		else
			white += 8-((now - lbuf + white)%8);
		now++;
	}
}

static char *
is_predefined(char *q)
{
	if (strcmp(q, "__DATE__") == 0)
		return "Oct 8 2004";
	else if (strcmp(q, "__TIME__") == 0)
		return "00:00:00";
	else if (strcmp(q, "__FILE__") == 0)
	{	myname = emalloc(strlen(filename)+3);
		strcpy(myname, "\"");
		strcat(myname, filename);
		strcat(myname, "\"");
		return myname;
	} else if (strcmp(q, "__LINE__") == 0)
	{	sprintf(lbuf, "%d", lineno);
		myname = emalloc(strlen(lbuf));
		strcpy(myname, lbuf);
		return myname;
	} else if (strcmp(q, "__INCLUDE_LEVEL__") == 0)
	{	sprintf(lbuf, "%d", stack_depth-1);
		myname = emalloc(strlen(lbuf));
		strcpy(myname, lbuf);
		return myname;
	} else if (strcmp(q, "__STDC__") == 0)
		return "1";
	else if (strcmp(q, "__STDC_HOSTED__") == 0)
		return "0";
	else if (strcmp(q, "__STDC_VERSION__") == 0)
		return "199901";

	return NULL;
}

static void
get_digit(void)
{
	if (*now == '0'
	&& (*(now+1) == 'x' || *(now+1) == 'X'))
	{	now += 2;
		myval = 0;
		while (isdigit(*now)
		|| (*now >= 'a' && *now <= 'f')
		|| (*now >= 'A' && *now <= 'F'))
		{	myval = 16*myval + *now;
			switch (*now) {
			case '0': case '1': case '2':
			case '3': case '4': case '5':
			case '6': case '7': case '8':
			case '9':
				myval -= '0';
				break;
			case 'a': case 'b': case 'c':
			case 'd': case 'e': case 'f':
				myval -= 'a' + 10;
				break;
			case 'A': case 'B': case 'C':
			case 'D': case 'E': case 'F':
				myval -= 'A' + 10;
				break;
			}
			now++;
		}
	} else
	{	myval = atoi(now);
		while (isdigit(*now))
			now++;
	}
	while (*now == 'L' || *now == 'l'
	    || *now == 'U' || *now == 'u')
		now++;	/* 8989L 999U */
}

static void
lookfor(char c)
{
	for ( ; *now != c; now++)
	{	if (*now == '\0')
		{	if (!not_printing[level])
			fprintf(stderr, "%s,%d: unterminated string\n",
				filename, lineno);
			now--;
			break;
		}
		if (*now == '\\')
			now++;
	}
	now++;
}

static void
digraphs(void)
{
	switch (mychar) {
	case '<':
		switch (*now) {
		case ':': now++; mychar = '['; break;
		case '%': now++; mychar = '{'; break;
		default:  break;
		}
		break;
	case ':':
		if (*now == '>') { now++; mychar = ']'; break; }
		break;
	case '%':
		switch (*now) {
		case '>': now++; mychar = '}'; break;
		case ':': now++; mychar = '#'; break;
		default: break;
		} /* fall thru */
	default:
		break;
	}
}

static void
trigraphs(void)
{
	if (mychar != '?' || *now != '?') return;

	switch (*(now+1)) {
	case '=':  now += 2; mychar = '#'; break;
	case '(':  now += 2; mychar = '['; break;
	case ')':  now += 2; mychar = ']'; break;
	case '<':  now += 2; mychar = '{'; break;
	case '>':  now += 2; mychar = '}'; break;
	case '/':  now += 2; mychar = '\\'; break;
	case '\'': now += 2; mychar = '^'; break;
	case '!':  now += 2; mychar = '|'; break;
	case '-':  now += 2; mychar = '~'; break;
	default:   return;
	}

	if (misra_rules) m_rule(4, 2, "trigraph");
}

static void
rule_check(void)
{
	if (!misra_rules) return;

	if (*now == '0' && isdigit(*(now+1)))
		m_rule(7, 1, "octal constant or escape sequence");

	if (*now != '\\') return;

	switch (*(now+1)) {
	case '0': break;
	case '1': case '2':
	case '3': case '4': case '5':
	case '6': case '7': /* not 8 or 9 */
		m_rule(7, 1, "octal constant or escape sequence");
		break;

	case '\"': case '\\': case '\'':
	case 'a': case 'b': case 'f': case 'n':
	case 'r': case 't': case 'v':
	case 'x': case 'X': /* followed by a hexadecimal nr */
		/* these are valid escape sequences */
		break;

	default:
		m_rule(4, 1, "undefined escape sequence");
		break;
	}
}

struct { char *nm; int maj, min ; } m_patterns[] = {
	/* misra2004 rule numbers */
	{ "errno",	20, 5 },
	{ "offsetof",	20, 6 },
	{ "setjmp",	20, 7 },
	{ "atof",	20, 10 },
	{ "atoi",	20, 10 },
	{ "atol",	20, 10 },
	{ "abort",	20, 11 },
	{ "exit",	20, 11 },
	{ "getenv",	20, 11 },
	{ "system",	20, 11 },
	{ "union",	18, 4 },
	{ "goto",	14, 4 },
	{ "continue",	14, 5 },
	{ NULL,		 0, 0 },
};

static Tokvals
lex(void)
{	char *q;
	int c;

	skipwhite();

	if (*now == '\n'
	||  *now == '\r'
	||  *now == '\0')
		return DONE;

	if (isalpha(*now) || *now == '_')
	{	q = now++;
		while (isalnum(*now) || *now == '_' || *now == '-')
			now++;
same:		c = *now;
		*now = '\0';
		myname = emalloc(strlen(q) + 1);
		strcpy(myname, q);
		*now = c;

		if (misra_rules)
		for (c = 0; m_patterns[c].nm != NULL; c++)
			if (strcmp(myname, m_patterns[c].nm) == 0)
			m_rule(m_patterns[c].maj, m_patterns[c].min, m_patterns[c].nm);

		return NAME;
	}

	if (strncmp(now, "...", 3) == 0)
	{	now += 3;
		myname = "...";
		if (misra_rules) m_rule(16, 1, "elipsis");

		return NAME;
	}

	if (isdigit(*now))
	{	get_digit();	/* result is in myval */
		return VAL;
	}
	
	mychar = *now++;
	if (mychar == '\\')
	{	mychar = *now++;
		return ECHAR;
	}

	if (mychar == '"')	/* string */
	{	q = now - 1;
		lookfor('"');
		goto same;	/* store as NAME */
	}

	if (mychar == '\'')	/* char constant */
	{	rule_check();
		q = now - 1;
		lookfor('\'');
		goto same;	/* store as as NAME */
	}

	digraphs();
	trigraphs();

	if (misra_rules
	&&  mychar == ';'
	&& !incomment
	&& !not_printing[level]
	&&  stack_depth <= 1)
		sawcode++;

	return CHAR;
}

static void
newmacro(char *s)
{	MD *m;

	m = (MD *) emalloc(sizeof(MD));
	m->nm = emalloc(strlen(s)+1);
	strcpy(m->nm, s);
	m->ln = lineno;
	m->fnm = emalloc(strlen(filename)+1);
	strcpy(m->fnm, filename);
	m->nxt = md;
	md = m;
}

static void
conflict(MD *m1, MD *m2)
{	TS *b1, *b2;

	for (b1 = m1->body, b2 = m2->body; b1 && b2; b1 = b1->nxt, b2 = b2->nxt)
	{	if (b1->tok != b2->tok
		|| (b1->name && b2->name && strcmp(b1->name, b2->name) != 0)
		||  b1->val != b2->val)
		{	fprintf(stderr, "%s,%d: warning: macro %s redefined\n",
				filename, lineno, m1->nm);
			fprintf(stderr, "	previous definition: %s,%d\n",
				m1->fnm, m1->ln);
			return;
	}	}

	md = md->nxt;	/* remove new def, same as old */
}

static void
check_body_type(TS *b)
{	TS *w, *w_lst = (TS *) 0;
	int r_cnt = 0, c_cnt = 0, s_cnt = 0;

	/* misra 19.4 restricts macros to:
	 *	braced initializer
	 *	constant
	 *	parenthesized expression
	 *	type qualifier	
	 *	storage class specifier	such as extern, static, const, ...
	 *	do-while(0)
	 * furthermore:
	 *	(), {}, [] braces must balance
	 *	no use of ';' at end of macro
	 */

	if (!b) return;

	for (w = b; w; w_lst = w, w = w->nxt)
		if (w->tok == CHAR)
			switch(w->val) {
			case '(': r_cnt++; break;
			case ')': r_cnt--; break;
			case '{': c_cnt++; break;
			case '}': c_cnt--; break;
			case '[': s_cnt++; break;
			case ']': s_cnt--; break;
			}

	if (r_cnt != 0 || s_cnt != 0 || c_cnt != 0)
		m_rule(19, 40, "unbalanced use of braces in macro body");

	/* Note: list is in reversed order...! */

	if (b && b->tok == CHAR && b->val == ';')
		m_rule(19, 4, "semi-colon at end of macro body");

	if (!b->nxt		/* single token */
	&&  (b->tok == VAL	/* constant */
	 ||  b->tok == NAME))	/* name, string, char constant */
		return;

	if (b->tok == CHAR	/* parenthesized expression.. sort of */
	&&  b->val == ')'
	&&  w_lst
	&&  w_lst->tok == CHAR
	&&  w_lst->val == '(')
		return;

	if (b->tok == CHAR	/* braced initializer.. sort of */
	&&  b->val == '}'
	&&  w_lst
	&&  w_lst->tok == CHAR
	&&  w_lst->val == '{')
		return;

	if (w_lst
	&&  w_lst->tok == NAME	/* do-while(0) construct */
	&&  strcmp(w_lst->name, "do") == 0
	&&  b
	&&  b->tok == ')'
	&&  b->nxt
	&&  b->nxt->tok == VAL
	&&  b->nxt->val == 0
	&&  b->nxt->nxt
	&&  b->nxt->nxt->tok == CHAR
	&&  b->nxt->nxt->val == '('
	&&  b->nxt->nxt->nxt
	&&  b->nxt->nxt->nxt->tok == NAME
	&&  strcmp(b->nxt->nxt->nxt->name, "while") == 0)
		return;

	if (strcmp(filename, "<predef>") != 0)
		m_rule(19, 4, "possibly non-compliant macro type");
}

static void
closemacro(void)
{	MD *m;
	TS *w;
	int cnt_s = 0, cnt_p = 0;

	if (md)
	{	md->arg = ca;
		md->body = cb;

		for (m = md->nxt; m; m = m->nxt)
			if (strcmp(m->nm, md->nm) == 0)
			{	conflict(m, md);
				break;
			}

		if (misra_rules)
		{	if (ca) m_rule(19, 7, "function-like macro iso function");

			if (misra_rules) check_body_type(cb);

			for (w = cb; w; w = w->nxt)
				if (w->tok == CHAR
				&&  w->val == '#')
				{	if (w->nxt
					&&  w->nxt->tok == CHAR
					&&  w->nxt->val == '#')
					{	cnt_p++;
						w = w->nxt;
						if (w->nxt)
							w = w->nxt;
					} else
						cnt_s++;
				}
			if (cnt_s > 1) m_rule(19, 12, "more than one # in macro");
			else if (cnt_s > 0) m_rule(19, 13, "# in macro");
			if (cnt_p > 1) m_rule(19, 12, "more than one ## in macro");
			else if (cnt_p > 0) m_rule(19, 13, "## in macro");
		}
	}
	ca = (ARGS *) 0;
	cb = (TS *) 0;
}

static TS *
new_inl(Tokvals t)
{	TS *n;

	if (free_ts)
	{	n = free_ts;
		free_ts = free_ts->nxt;
		memset(n, 0, sizeof(TS));
	} else
		n = (TS *) emalloc(sizeof(TS));
	n->tok = t;
	return n;
}

static void
add_tag(TS *ni, MD *m)
{	ML *ml;

	for (ml = ni->ml; ml; ml = ml->nxt)
		if (ml->m == m)
			return;

	if (free_ml)
	{	ml = free_ml;
		free_ml = free_ml->nxt;
		memset(ml, 0, sizeof(ML));
	} else
		ml = (ML *) emalloc(sizeof(ML));
	ml->m = m;
	ml->nxt = ni->ml;
	ni->ml = ml;
}

static void
addbody(Tokvals tok, int v)
{	TS *b;

	b = new_inl(tok);
	b->space = white;
	b->val = v;
	b->nxt = cb;
	if (cb) cb->prv = b;
	cb = b;
}

static void
add_def(char *s)	/* e.g., NAME or NAME=... */
{	char *p, *z;

	z = emalloc(strlen(s)+1);
	strcpy(z, s);

	if ((p = strchr(z, '=')) != NULL)
	{	*p = '\0';
		newmacro(z);
		*p++ = '=';
		white = 0;
		if (isdigit(*p))
			addbody(VAL, atoi(p));
		else
		{	addbody(NAME, 0);
			cb->name = p;
		}
	} else
		newmacro(z);

	closemacro();
}

static void
rm_def(char *s)
{	MD *m, *lm = (MD *) 0;

	for (m = md; m; lm = m, m = m->nxt)
		if (strcmp(m->nm, s) == 0)
			break;
	if (m)
	{	if (!lm)
			md = m->nxt;
		else
			lm->nxt = m->nxt;
	}
}

static void
nested_comment_check(char *t, char *r)
{	int c = 0;

	if (!misra_rules) return;

	if (r != NULL)
	{	c = *r;
		*r = '\0';
	}
	if (strstr(t, "/*"))
		m_rule(2, 3, "nested /* comment");

	if (r != NULL)
		*r = c;
	
}

#if 1

static char *
find_delimiter(char *d, char *t)
{	char *p, *q, *r, *s;

zz:	p = strstr(t, d);
	if (!p) return NULL;

	s = t;
yy:	q = strchr(s, '"');

	if (q && q <= p)	/* in string */
	{	/* real string delimiter? */
		if (strncmp(q-1, "'\"'", 3) == 0
		||  strncmp(q-2, "'\\\"'", 4) == 0)
		{	s = q+2;
			goto yy; /* no, try again */
		}
		q++;	/* presumably real string */
xx:		r = strchr(q, '"');	/* find closing quote */
		if (!r) fatal_error("unterminated string");

		if (*(r-1) == '\\') { q++; goto xx; }

		if (r < p)	/* string ends before comment starts */
		{	s = r+1;
			goto yy; /* find another */
		} else	/* yes we're in a string */
		{	t = r;	/* find another delimiter */
			goto zz;
	}	}

	return p;
}

static void
strip_comments(void)
{	char *p, *q, *r, *t = lbuf;
	int i;

	if (incomment)	/* in C style comment block */
	{	q = t;
		goto c_style;
	} else
	{
more:		p = find_delimiter("//", t);
		q = find_delimiter("/*", t);

		if (p)
		{	if (!q || p < q)
			while (*p != '\0')
				*p++ = ' ';
			else /* q && p >= q */
			{	*q++ = ' ';
				*q++ = ' ';
				goto c_style;
			}
		} else if (q)
		{	*q++ = ' ';
			*q++ = ' ';
c_style:		r = strstr(q, "*/");
			nested_comment_check(q, r);
			if (!r)
			{	while (*q != '\0') *q++ = ' ';
				incomment = 1;
			} else
			{	while (q <= r+1) *q++ = ' ';
				t = q;
				incomment = 0;
				goto more;
	}	}	}

	i = strlen(lbuf)-1;
	if (i >= 0)
	for (p = &lbuf[i]; isspace(*p); p--)
		*p = '\0';	/* remove white space from end of line */
}

#else

static void
strip_comments(void)
{	char *p, *q, *r, *s, *t = lbuf;
	int i;

	if (!incomment)
	{
		strip_cpp_comments();

	zz:	p = strstr(t, "/*");

		if (!p) goto done;

		/* are we inside a string? */
		s = t;
	yy:	q = strchr(s, '"');

		if (!q || q > p)	/* not in a string */
		{	r = strstr(p, "*/");
			nested_comment_check(p+2, r);
			if (!r)
			{	while (*p != '\0') *p++ = ' ';
				incomment = 1;
			} else
			{	while (p <= r+1) *p++ = ' ';
				t = p;
				goto zz;
			}
		} else	/* could be in a string */
		{	/* is it a real string delimiter? */
			if (strncmp(q-1, "'\"'", 3) == 0
			||  strncmp(q-2, "'\\\"'", 4) == 0)
			{	s = q+2;
				goto yy;
			}
			q++;
	xx:		r = strchr(q, '"');
			if (!r) fatal_error("unterminated string");
			if (*(r-1) == '\\') { q++; goto xx; }

			if (r < p)	/* string ends before comment starts */
			{	s = r+1;
				goto yy;
			} else	/* yes we're in a string */
			{	t = r;	/* find another comment */
				goto zz;
		}	}
	} else	/* in comment */
	{	r = strstr(t, "*/");
		nested_comment_check(t, r);
		if (!r)
		{	for (p = t; *p != '\0'; p++)
				*p = ' ';
		} else
		{	for (p = t; p <= r+1; p++)
				*p = ' ';
			incomment = 0;
			t = p;
			goto zz;
	}	}
done:
	i = strlen(lbuf)-1;
	if (i >= 0)
	for (p = &lbuf[i]; isspace(*p); p--)
		*p = '\0';	/* remove white space from end of line */
}

#endif

static void
do_lineno(TS *d)
{
	if (d->tok != VAL)
	{
bad:		fprintf(stderr, "%s,%d: warning: malformed directive %s",
			filename, lineno, ibuf);
		return;
	}
	lineno = d->val;

	d = d->nxt;
	if (!d || d->tok != CHAR || d->val != '\"')
		return;	/* no filename */

	d = d->nxt;
	if (!d || d->tok != NAME)
		goto bad;

	filename = d->name;

	d = d->nxt;
	if (!d || d->tok != CHAR || d->val != '\"')
		goto bad;
}

static void
release_ml(ML *m)
{
	if (!m) return;
	release_ml(m->nxt);
	m->nxt = free_ml;
	free_ml = m;
}

static void
release_all(TS *s)
{
	if (!s) return;
	release_all(s->nxt);
	release_ml(s->ml);
	s->nxt = free_ts;
	free_ts = s;
}

static MD *
is_macro(char *s)
{	MD *m;

	for (m = md; m; m = m->nxt)
		if (strcmp(m->nm, s) == 0)
			return m;

	return (MD *) 0;
}

static void
do_ifdef(TS *s)
{	MD *m;

	if (s->tok != NAME)
		fatal_error("expecting name after #ifdef or #ifndef");
		
	if (level >= 255) 
		fatal_error("ifdefs nested too deep");

	m = is_macro(s->name);
	add_tag(s, m);

	not_printing[++level] = (m == NULL);
}

static void
do_ifndef(TS *s)
{
	do_ifdef(s);
	not_printing[level] = 1 - not_printing[level];
}

static void
do_if_pre(TS *s)	/* replace occurrences of "defined()" */
{	TS *d, *b, *n;
	int bracketed;

	for (d = s; d; d = d->nxt)
	{	bracketed = 0;
		if (d->tok == NAME
		&&  strcmp(d->name, "defined") == 0)
		{	b = d->nxt;
			if (!b) fatal_error("syntax of defined, missing name");

			if (b->tok == CHAR
			&&  b->val == '(')
			{	b = b->nxt;	/* the name */
				if (!b
				||  b->nxt->tok != CHAR
				||  b->nxt->val != ')')
				{	if (misra_rules) m_rule(19, 14, "malformed defined");
					fatal_error("missing ')' after defined(..");
				}
				bracketed = 1;
			}

			if (b->tok != NAME)
			{	if (misra_rules) m_rule(19, 14, "malformed defined");
				fatal_error("missing name after defined");
			}
			n = new_inl(VAL);
			n->val = (is_macro(b->name))?1:0;
			n->space = d->space;

			if (n->val) add_tag(n, is_macro(b->name));

			if (bracketed)
			{	b = b->nxt;	/* skip to ')' */
				if (!b) fatal_error("syntax of defined, missing ')'");
			}
			n->prv = d->prv;
			n->nxt = b->nxt;

			if (n->prv)
				n->prv->nxt = n;
			if (n->nxt)
				n->nxt->prv = n;

			b->nxt = (TS *) 0;
			release_all(d);

			d = n;
	}	}
}

static void
do_if_post(void)	/* post macro expansion */
{
	if (level >= 255) fatal_error("macros nested too deeply");

	if (not_printing[level] < 2)
		not_printing[++level] = !eval_expr(start);
}

static void
do_elif_post(void)
{
	if (not_printing[level] == 1)		/* all earlier if-exprs were False */
		not_printing[level] = !eval_expr(start);
	else if (not_printing[level] != 3)	/* 0 or 2 at least one earlier if-expr was True */
		not_printing[level] = 2; /* prevent next elifs to misinterpret state */
}

static void
do_else(TS *unused)
{
	if (level <= 0) fatal_error("unmatched #else");

	if (not_printing[level] < 2)
		not_printing[level] = 1 - not_printing[level];
	/* if it's 3 it remains unchanged */
}

static ARGS *
add_arg(char *s, ARGS *p)
{	ARGS *a = (ARGS *) emalloc(sizeof(ARGS));

	a->nm = emalloc(strlen(s)+1);
	strcpy(a->nm, s);
	if (p) p->nxt = a;
	return a;
}

static TS *
do_params(TS *s)
{
	if (!s) fatal_error("syntax of #define");

	if (s->tok == CHAR
	&&  s->val == ')')	/* empty param list */
		s = s->nxt;
	else
	for ( ; ; s = s->nxt)
	{
		if (s->tok != NAME)
			fatal_error("expected param name");

		ca = add_arg(s->name, ca);
		if (!sfa) sfa = ca;

		s = s->nxt;

		if (!s || s->tok != CHAR)
			fatal_error("bad syntax of #define");

		if (s->val == ')')
		{	s = s->nxt;
			break;
		}

		if (s->val != ',')
			fatal_error("bad syntax of #define");
	}

	return s;
}

static int
scan_args(char *s)
{	ARGS *an;
	int i;

	for (i = 0, an = ca; an; i++, an = an->nxt)
		if (strcmp(s, an->nm) == 0
		|| (strcmp(s, "__VA_ARGS__") == 0
		&&  strcmp(an->nm, "...") == 0))
			return i;

	return -1;
}

static void
do_stringarg(TS *s, int w)
{	int i;

	if (!s)
	{	addbody(CHAR, '#');
		return;
	}
	white = w;
	switch (s->tok) {
	case NAME:
		i = scan_args(s->name);
		addbody(i >= 0 ? ARGSTRING: PLAINSTRING, 0);
		cb->name = s->name;
		cb->val = (i >= 0)? i : 0;
		break;
	case VAL: /* was not a string arg */
		addbody(CHAR, '#');
		white = 0;
		addbody(VAL, s->val);
		break;
	case ECHAR:
		addbody(CHAR, '#');
		white = 0;
		addbody(ECHAR, s->val);
		break;
	case CHAR:
		addbody(CHAR, '#');
		white = s->space;
		addbody(CHAR, s->val);
		break;
	default:
		fatal_error("cannot happen");
		break;
	}
	white = 0;
}

static int
not_braced(TS *s)	/* formal param, not in parentheses */
{
	/* param is
	 * not preceded by #
	 * not preceded or followed by ##
	 */

	if (!s->prv
	||  !s->nxt
	||   s->prv->tok != CHAR
	||  (s->prv->val != '(' && s->prv->val != '#')
	||   s->nxt->tok != CHAR
	||  (s->nxt->val != ')' &&
	    (s->nxt->val != '#'
	 || !s->nxt->nxt
	 || s->nxt->nxt->tok != CHAR
	 || s->nxt->nxt->val != '#')))
		return 1;

	return 0;
}

static void
do_define(TS *s)
{	int i, j = 0;

	if (s->tok != NAME)
		fatal_error("expect name after #define");

	if (misra_rules
	&&  BlockDepth > 0)
		m_rule(19, 5, "#define within block scope");

	newmacro(s->name);

	s = s->nxt;

	sfa = (ARGS *) 0;
	if (s && s->tok == CHAR && s->val == '(' && s->space == 0)
		s = do_params(s->nxt);	/* puts formal par list in sfa */

	ca = sfa;	/* this is where scan_args and closemacro look for it */
	for (j = 0; s; j++, s?s = s->nxt:s)	/* body of define */
	{	white = (j>0)?s->space:0;
		switch (s->tok) {
		case NAME:
			i = scan_args(s->name);
			addbody(i >= 0 ? ARG: NAME, 0);
			cb->name = s->name;
			cb->val = (i >= 0)? i : 0;

			if (misra_rules && i > 0
			&&  not_braced(s))
				m_rule(19, 10, "formal param not enclosed in ()");

			break;
		case VAL:
			addbody(VAL, s->val);
			break;
		case ECHAR:
			addbody(ECHAR, s->val);
			break;
		case CHAR:
			if (s->val == '#')
			{	do_stringarg(s->nxt, s->space);
				s = s->nxt;
			} else
				addbody(CHAR, s->val);
			break;
		default:
			fatal_error("cannot happen");
	}	}

	white = 0;
	closemacro();
}

static void
do_undef(TS *s)
{
	if (s->tok != NAME)
		fatal_error("expect name after #undef");

	if (misra_rules
	&&  BlockDepth > 0)
		m_rule(19, 5, "#undef within block scope");

	if (misra_rules)
		m_rule(19, 6, "#undef");

	rm_def(s->name);
}

static void
do_endif(TS *unused)
{
	if (level-- <= 0)
		fatal_error("unmatched endif");
}

static void
do_nothing(TS *unused)
{
}

static void
do_error(TS *unused)
{
	if (!not_printing[level])
		fprintf(stderr, "%s,%d: %s\n", filename, lineno, ibuf);
}

static struct Table {
	char *nm;	void (*fct)(TS *);
} table[] = {
	{ "if",		do_if_pre,  },	/* 0 */
	{ "ifdef",	do_ifdef,   },	/* 1 */
	{ "ifndef",	do_ifndef,  },	/* 2 */
	{ "define",	do_define,  },	/* 3 */
	{ "undef",	do_undef,   },	/* 4 */
	{ "pragma",	do_nothing, },	/* 5 */
	{ "error",	do_error,   },	/* 6 */
	{ "warning",	do_error,   },	/* 7 */
	{ "line",	do_nothing,  },	/* 8 */
	{ "else",	do_else,    },	/* 9 */
	{ "elif",	do_if_pre,  },	/* 10 */
	{ "endif",	do_endif,   },	/* 11 */
	{ NULL,		NULL, },
};

static int
one_directive(TS *d)
{	int i;

	if (!d) return 1;

	switch (d->tok) {
	case VAL:		/* e.g.: # 12 "filename.c" */
		do_lineno(d);
		return 1;
	case NAME:
		for (i = 0; table[i].nm; i++)
			if (strcmp(d->name, table[i].nm) == 0)
			{	if (!not_printing[level]
				||  i >= 8)
					table[i].fct(d->nxt);
				else if (i < 3)
					not_printing[++level] = 3;
				return i+2; /* distinct from 1, 0, -1 */
			}
		if (strcmp(d->name, "include") == 0)
		{	if (misra_rules && !no_includes)
				m_rule(19, 3, "#include needing preprocessing");
			return -1;
		}
		break;
	default:
		break;
	}

	fprintf(stderr, "%s,%d: warning: unrecognized directive '#%s'\n",
		filename, lineno, d->name);
	return 0;
}

static void
string_merge(TS *from)	/* merge subsequent strings */
{	char *s;
	TS *n;

	for (n = from; n; n = n->nxt)
		if (n->tok == NAME
		&&  n->name[0] == '"'
		&&  n->nxt
		&&  n->nxt->tok == NAME
		&&  n->nxt->name[0] == '"')
		{	s = emalloc(strlen(n->name)+strlen(n->nxt->name)+1);
			strncpy(s, n->name, strlen(n->name)-1);
			strncat(s, &n->nxt->name[1], strlen(n->nxt->name)-1);
			n->name = s;
			n->nxt = n->nxt->nxt;
			if (n->nxt && n->nxt->nxt) n->nxt->nxt->prv = n;
			if (n->prv) n = n->prv; else n = from;
		}
}

static void
prep_line(TS *from)
{	char tmp[1024];
	TS *n;
	int i;
	static int saw_else_last;

	strcpy(lbuf, "");
	for (n = from; n; n = n->nxt)
	{	for (i = n->space; i > 0; i--)
			strcat(lbuf, " ");

		switch (n->tok) {
		case NAME:
			strcat(lbuf, n->name);
			saw_else_last = (strcmp(n->name, "else") == 0);
			break;
		case VAL:
			sprintf(tmp, "%d", n->val);
			strcat(lbuf, tmp);
			saw_else_last = 0;
			break;
		case ECHAR:
			strcat(lbuf, "\\");
			saw_else_last = 0;
			/* fall thru */
		case CHAR:
			sprintf(tmp, "%c", n->val);
			strcat(lbuf, tmp);

			if (saw_else_last && n->val == ';')
			fprintf(stderr, "%s,%d: 'else' is followed by ';'\n",
				filename, lineno);
			saw_else_last = 0;
			break;
		case TPASTE:
			strcat(lbuf, "##");
			break;
		default:
			fprintf(stderr, "saw: ");
			tokfull(n, stderr);
			fprintf(stderr, "\n");
			fatal_error("unknown token");
	}	}
}

void
show_line(int d, FILE *fd)
{
	if (verbose)
		fprintf(fd, "[%d:%d] ", level, not_printing[level]);
	if (numbered)
		fprintf(fd, "%s,%d: ", filename, lineno);
	if (verbose || explanations
	|| (!d && !not_printing[level]))	/* not a directive */
	{	prep_line(start);
		fprintf(fd, "%s", lbuf);
	}
	fprintf(fd, "\n");
}

static void
post_expansion(void)	/* process directives that need macro-expansion first */
{	TS *s;

	if (start && start->tok == CHAR && start->val == '#')
	{	s = start->nxt;
		if (s->tok == NAME)
		{	if (strcmp(s->name, "if") == 0)
				do_if_post();
			else if (strcmp(s->name, "elif") == 0)
				do_elif_post();
			else if (strcmp(s->name, "line") == 0)
				do_lineno(s->nxt);
	}	}
}

static int
do_directives(void)
{
	if (start && start->tok == CHAR && start->val == '#')
		return one_directive(start->nxt);

	return 0;
}

static void
do_parsing(void)
{	Tokvals t;
	TS *n;

	now = lbuf;
	strip_comments();

	while ((t = lex()) != DONE)
	{	n = new_inl(t);
		n->space = white;
		switch (n->tok) {
		case NAME:
			n->name = emalloc(strlen(myname)+1);
			strcpy(n->name, myname);
			break;
		case VAL:
			n->val = myval;
			break;
		case ECHAR:
			/* fall thru */
		case CHAR:
			n->val = (int) mychar;
			break;
		default:
			fatal_error("unknown token");
		}
		n->prv = inl;
		if (start) inl->nxt = n; else start = n;
		inl = n;
	}

	for (n = start; n; n = n->nxt)
		if (n->tok == CHAR)
		{	if (n->val == '{')
				BlockDepth++;
			else if (n->val == '}')
				BlockDepth--;

			if (n->val == '/'
			&&  n->nxt
			&&  n->nxt->tok == CHAR
			&&  n->nxt->val == '/')
			{	if (misra_rules)
					m_rule(2, 2, "C++ style comment");
				if (n->prv)
					n->prv->nxt = (TS *) 0;
				else
					start = (TS *) 0;
		}	}
}

static TS *
cpy_inl(TS *s, TS *prv)
{	TS *n;
	n = new_inl(s->tok);
	n->val = s->val;
	n->name = s->name;
	n->space = s->space;
	n->ml = s->ml;
	n->prv = prv;
	if (prv) prv->nxt = n;
	return n;
}

static ARL *
bld_arglst(TS *s, ARL *al)
{	ARL *a;
	a = (ARL *) emalloc(sizeof(ARL));
	a->al = s;
	if (al) al->nxt = a;
	return a;
}

static void
check_name(char *s)
{	int i;

	if (strcmp(s, "include") == 0)
		m_rule(19, 9, "macro argument matches directive name");
	for (i = 0; table[i].nm != NULL; i++)
		if (strcmp(s, table[i].nm) == 0)
		m_rule(19, 9, "macro argument matches directive name");
}

static TS *
parse_args(TS *sin)
{	int nesting = 1;
	TS *ls = sin;
	TS *s = sin->nxt;
	TS *narg = (TS *) 0;
	TS *sarg = (TS *) 0;
	ARL *arglst = (ARL *) 0;

	if (s
	&&  s->tok == CHAR
	&&  s->val == ')')
		return s;
more:
	for ( ; s; ls = s, s = s->nxt)
	{	switch (s->tok) {
		case CHAR:
			if (s->val == '(')
				nesting++;

			if (nesting == 1
			&&  (s->val == ',' || s->val == ')'))
			{	arglst = bld_arglst(sarg, arglst);
				if (!saa) saa = arglst;
				sarg = narg = (TS *) 0;
			} else
				narg = cpy_inl(s, narg);

			if (s->val == ')')
				nesting--;

			if (nesting == 0)
				return s;

			break;
		case ECHAR:
			narg = cpy_inl(s, narg);
			break;
		case VAL:
			narg = cpy_inl(s, narg);
			break;
		case NAME:
			narg = cpy_inl(s, narg);
			if (misra_rules) check_name(s->name);
			break;
		default:
			fatal_error("cannot happen");
			break;
		}
		if (!sarg) sarg = narg;
	}

	while (!s && nesting > 0)	/* line too short, need more input */
	{	need_more();		/* will fatal on eof */
		strcpy(lbuf, ibuf);
		do_parsing();
		if (ls->nxt)
		{	s = ls->nxt;
			if (debugging)
			fprintf(stderr, "%s,%d: extended line\n",
				filename, lineno);
			goto more;
		}
		if (debugging)
		fprintf(stderr, "%s,%d: line still too short\n",
			filename, lineno);
	}	

	return s;
}

static void
add_inl(Tokvals tt, int v, char *nm, int sp, int reuse)
{	TS *ni;

	ni = new_inl(tt);
	ni->val = v;

	if (reuse)
		ni->name  = nm;
	else
	{	ni->name = emalloc(strlen(nm)+1);
		strcpy(ni->name, nm);
	}
	ni->space = sp;

	if (lst) lst->nxt = ni;
	ni->prv = lst;
	if (!frst) frst = ni;
	lst = ni;
}

static int
string_size(TS *s)
{	int cnt, v;

	if (!s) return 0;

	cnt = s->space+1;
	switch (s->tok) {
	case NAME:	cnt = strlen(s->name);
			break;
	case VAL:	for (v = s->val; v >= 10; v /= 10)
				cnt++;
			break;
	case ECHAR:	cnt++; /* fall thru */
	default:	break;
	}

	return cnt+string_size(s->nxt);
}

static char *
stringify(TS *s, TS *f)
{	static char m[128];
	static char p[128];
	char *q;
	int i = 0;

	if (!s) return "";

	p[0] = m[1] = '\0';

	if (s)
	switch (s->tok) {
	case NAME:
		for (q = s->name; *q != '\0'; q++)
		{	if (*q == '\\'
			||  *q == '"')
				strcat(p, "\\");
			m[0] = *q;
			strcat(p, m);
		}
		break;

	case VAL:
		sprintf(p, "%d", s->val);
		break;

	case CHAR:
		if (s->val != '"')
		{	sprintf(p, "%c", s->val);  
			break;
		}
		/* else fall thru */
	case ECHAR:
		sprintf(p, "\\%c", s->val);
		break;

	default: break;
	}

	if (s != f)	/* not for first arg */
	for (i = 0; i < s->space; i++)
		m[i] = ' ';

	m[i] = '\0';
	strcat(m, p);

	return m;
}

static ARL *
hunt_param(MD *m, TS *b)
{	ARL  *ap;	/* actual */
	ARGS *fp;	/* formal */
	int i = 0, j = 0;
	int n = b->val;	/* nr of param in formal param list */
#ifdef DEBUG
	TS *x; printf("\n");
#endif
	for (ap = saa; ap; ap = ap->nxt)
	{	i++;	/* count actual params */
#ifdef DEBUG
		printf("actual %d ", i);
		for (x = ap->al; x; x = x->nxt)
			printf("%s ", x->name);
		if (i==n) printf("<<--%s", b->name);
			printf("\n");
#endif
	}

	for (fp = m->arg; fp; fp = fp->nxt)
	{	j++;	/* count formal params */
#ifdef DEBUG
		printf("formal %d %s\n", j, fp->nm);
#endif
	}

	if (strcmp(b->name, "__VA_ARGS__") == 0)
		n = j-1;	/* last formal */

	for (i = 0, ap = saa; ap; i++, ap = ap->nxt)
		if (i == n) break;	/* nth param in actual param list */

	if (!ap) fatal_error("did not find param");

	return ap;
}

static void
purge_body(TS *s, TS *x, MD *m, TS *b)
{	TS *aa;
	ML *ml;
	ARL *ap;	/* actual parameter - could be list */
	int w, original;
	char nm[MAXIN];	/* scratch */

	if (!b) return;

	purge_body(s, x, m, b->nxt);

	switch (b->tok) {
	case ARG:
		if (!saa)
		{	fprintf(stderr, "%s,%d: cannot find argument for %s\n",
				filename, lineno, b->name);
			break;
		}
		original = ((b->nxt
		&&   b->nxt->nxt
		&&   b->nxt->tok == CHAR && b->nxt->val == '#'
		&&   b->nxt->nxt->tok == CHAR && b->nxt->val == '#')
		||  (b->prv
		&&   b->prv->prv
		&&   b->prv->tok == CHAR && b->prv->val == '#'
		&&   b->prv->prv->tok == CHAR && b->prv->val == '#'));

		ap = hunt_param(m, b);

		w = 1;
more1:
		if (original) aa = ap->oal; else aa = ap->al;

		original = 0; /* reuse as counter */
		for ( ; aa; aa = aa->nxt)
		{	if (original) w = aa->space;
			add_inl(aa->tok, aa->val, aa->name, w, 1);
			for (ml = aa->ml; ml; ml = ml->nxt)
				add_tag(lst, ml->m);
			original++;
		}
		if (strcmp(b->name, "__VA_ARGS__") == 0)
		{	ap = ap->nxt;
			if (ap)
			{	add_inl(CHAR, ',', "", 1, 1);
				w = 1;
				goto more1;
		}	}
		break;
	case ARGSTRING:
		if (!saa)
		{	fprintf(stderr, "%s,%d: cannot find arg for %s\n",
				filename, lineno, b->name);
			break;
		}
		ap = hunt_param(m, b);
		strcpy(nm, "\"");
more2:		for (aa = ap->oal; aa; aa = aa->nxt)
			strcat(nm, stringify(aa, ap->oal));

		if (strcmp(b->name, "__VA_ARGS__") == 0)
		{	ap = ap->nxt;
			if (ap)
			{	strcat(nm, ", ");
				goto more2;
		}	}

		strcat(nm, "\"");
		add_inl(NAME, 0, nm, b->space, 0);

		break;
	case PLAINSTRING:
		sprintf(nm, "#%s", b->name);
		add_inl(NAME, 0, nm, b->space, 0);
		break;
	case ECHAR:
	case CHAR:
	default:
		if (debugging)
		{	nested("ADD NORMAL: ");
			tokfull(b, stdout);
			printf(" (space %d)\n", b->space);
		}
		add_inl(b->tok, b->val, b->name, b->space, 1);
		break;
	}
}

static int
pasterize(TS *f, TS *p, TS *n)
{	char *s;

	if (p->tok == NAME
	&&  n->tok == NAME
	&&  (p->name[0] == '"' || p->name[0] == '\''
	||   n->name[0] == '"' || n->name[0] == '\''))
	{	fprintf(stderr, "%s,%d: pasting %c and %c does not produce a valid new token\n",
			filename, lineno, p->val, n->val);
		return 0;
	}
	if (n->tok == CHAR
	&&  n->val == ';')
		fprintf(stderr, "%s,%d: pasting %c does not produce a valid new token\n",
			filename, lineno, n->val);

	if (p->tok == CHAR)
	{	if (n->tok == CHAR
		&&  p->val == '/'
		&& (n->val == '*' || n->val == '/'))
		fprintf(stderr, "%s,%d: pasting %c and %c did not produce a valid new token\n",
			filename, lineno, p->val, n->val);
		if (n->tok == NAME
		&&  p->val == '#'
		&&  (strcmp(n->name, "define") == 0
		||   strcmp(n->name, "include") == 0))
		fprintf(stderr, "%s,%d: pasting %c and %s did not produce a valid directive\n",
			filename, lineno, p->val, n->name);
	}

	s = emalloc(1 + 2*string_size(p) + 2*string_size(n) +4);
	strcpy(s, stringify(p, p));
	strcat(s, stringify(n, n));

	if (p->tok == VAL
	&&  n->tok == VAL)
	{	f->tok = VAL;
		f->val = atoi(s);
	} else
	{	f->tok = NAME;
		f->name = s;
	}
	return 1;
}

static void
token_pasting(void)
{	TS *f, *fn;

	for (f = frst; f; f = f->nxt)	/* find double-sharp sequences */
		if (f->tok == CHAR
		&&  f->val == '#'
		&&  f->nxt
		&&  f->nxt->tok == CHAR
		&&  f->nxt->val == '#'
		&&  f->nxt->space == 0)
		{	fn = f->nxt->nxt;
			if (f->prv
			&&  f->prv->tok == TPASTE)
				f = f->prv;
			else
				f->tok = TPASTE;
			f->nxt = fn;
			if (fn)
				fn->prv = f;
			else
				lst = f;
		}

	for (f = frst; f; f = f->nxt)
		if (f->tok == TPASTE)
		{	fn = f->nxt;

			if (!pasterize(f, f->prv, fn))
			{	if (f->prv)
					f->prv->nxt = fn;
				else
					frst = fn;

				f->nxt = fn->nxt;

				if (fn)
					f->nxt->prv = f->prv;
				else
					lst = f;

				continue;
			}

			if (f->prv) f->space = f->prv->space;

			if (!f->prv || !f->prv->prv)
			{	frst = f;
				f->space = 0;
				f->prv = (TS *) 0;
			} else
			{	f->prv->prv->nxt = f;
				f->prv = f->prv->prv;
			}

			if (!fn || !fn->nxt)
			{	lst = f;
				f->nxt = (TS *) 0;
			} else
			{	f->nxt = fn->nxt;
				f->nxt->prv = f;
		}	}
}

static TS *
pick_predefined(TS *s, char *str)
{	TS *ni;

	ni = new_inl(NAME);
	ni->name = str;
	ni->space = s->space;

	if (!s->prv)
	{	start = ni;
		ni->prv = start;
	} else
	{	s->prv->nxt = ni;
		ni->prv = s->prv;
	}

	if (s->nxt)
	{	s->nxt->prv = ni;
		ni->nxt = s->nxt;
	}
	return ni;
}

static void
show_args(ARL *sa, int j)
{	TS *wi;
	printf("ARG %d ", j);
	for(wi = sa->al; wi; wi = wi->nxt)
		tokfull(wi, stdout);
	printf("\n");
}

static TS *
prelude(TS *s, MD *m)	/* various types of checks */
{	char *str;
	int i, j, k = 0, covered;
	TS *sc;
	ML *ml;
	ARGS *a;
	ARL  *sa;

	if (strncmp(m->nm, "__", 2) == 0
	&& (str = is_predefined(m->nm)) != NULL)
		return pick_predefined(s, str);

	for (i = 0, a = m->arg; a; a = a->nxt)
	{	if (strcmp(a->nm, "...") == 0)
			k = 1; /* var length list */
		i++;
	}

	saa = (ARL *) 0;
	if (i > 0
	&&  s->nxt
	&&  s->nxt->tok == CHAR
	&&  s->nxt->val == '(')
		last = parse_args(s->nxt); /* sets saa with actual params */
	else
		last = s;

	covered = 1;	/* check if at least one token from call is non-covered */
	for (sc = s; ; sc = sc->nxt)
	{	for (ml = sc->ml; ml; ml = ml->nxt)
			if (ml->m == m)
				break;
		if (!ml)
		{	covered = 0;
			break;
		}

		if (sc == last)
			break;
	}

	if (covered)
	{	if (verbose)
		{	if (debugging)
			{	Enesting++;
				nested("");
				Enesting--;
			}
			printf("%s,%d: recursive use of macro %s\n",
				filename, lineno, m->nm);
		}
		return s;
	}

	for (j = 0, sa = saa; sa; sa = sa->nxt)
	{	j++;
		if (debugging) show_args(sa, j);
	}

	if (i != j && (k == 0 || j < i))
	{	if (!not_printing[level] && j > 0)
		{	fprintf(stderr, "%s,%d: error: macro '%s' requires %d args, saw %d\n",
				filename, lineno, m->nm, i, j);
			if (misra_rules && j < i)
			m_rule(19, 8, "macro call with insufficient arguments");
		} else if (misra_rules)
		{	m_rule(19, 16, "macro call with insufficient arguments");
		}
		return last;
	}

	return (TS *) 0;
}

static TS *
cpy_orig(TS *or)
{	TS *nw = (TS *) 0;
	ML *ml;

	if (or != (TS *) 0)
	{	nw = cpy_inl(or, (TS *) 0);
		nw->ml = (ML *) 0;
		for (ml = or->ml; ml; ml = ml->nxt)
			add_tag(nw, ml->m);

		nw->nxt = cpy_orig(or->nxt);
		if (nw->nxt)
			nw->nxt->prv = nw;
	}

	return nw;
}

#undef SIMPLER
#ifdef SIMPLER
/* the language definition is unclear on this point */
#define throughout(x,y,z)	1
#else
static int
throughout(TS *s, TS *last, MD *m)
{	ML *mp;

	if (!s || s == last) return 1;

	for (mp = s->ml; mp; mp = mp->nxt)
		if (mp->m == m)
			break;

	if (!mp) return 0;

	return throughout(s->nxt, last, m);
}
#endif

static void
inherit_tags(TS *s, TS *last, TS *ni)
{	ML *mp;

	for (mp = s->ml; mp; mp = mp->nxt)
		if (s == last
		||  throughout(s->nxt, last, mp->m))
		{	add_tag(ni, mp->m);
			if (debugging)
			{	nested("");
				printf("inherited tag on %p with %s\t", ni, mp->m->nm);
				tokfull(ni, stdout);
				printf("\n");
		}	}
}

static TS *
expand_macro(TS *s, MD *m)
{	TS *ni;
	ML *mp;
#ifdef RECURSE
	TS  *li, *hold_start, *hold_last;
	ARL *sa, *hold_saa;
	MD *mm;
#endif
	ni = prelude(s, m);
	if (ni) return ni;

	if (debugging)
	{	Enesting++; nested("");
		printf("Expand %s\n", m->nm);
	}

#ifdef RECURSE
	/* preserve copy of original actual params */
	/* to be used for formals preceded by # or ## in macro body */

	for (sa = saa; sa; sa = sa->nxt)
		sa->oal = cpy_orig(sa->al);

	/* expand actual params */
	hold_start = start;
	hold_saa   = saa;
	hold_last  = last;
	for (sa = saa; sa; sa = sa->nxt)	/* for each actual param */
	for (ni = sa->al; ni; ni = ni->nxt)	/* check token sequence  */
	{	if (ni->tok == NAME		/* for macro names */
		&& (mm = is_macro(ni->name)) != NULL)
		{
			if (debugging)
			{	nested("expanding macro ");
				printf("%s, pre-expand actual param %s\n",
					m->nm, ni->name);
				nested("Before: "); prep_line(start); printf("%s\n", lbuf);
				nested("Fragmt: "); prep_line(ni); printf("%s\n", lbuf);
			}
			start = ni;
			li = expand_macro(ni, mm);

			if (debugging)
			{	nested("Expnd : "); prep_line(start); printf("%s\n", lbuf);
				nested("LI    : "); prep_line(li); printf("%s\n", lbuf);
			}

			if (start != ni)
			{	if (ni->prv)
				{	ni->prv->nxt = start;
					if (start) start->prv = ni->prv;
				} else
				{	sa->al = start;
				}
				ni = li;
			}	/* else: macro not replaced - e.g., no params */

			start = hold_start;
			saa   = hold_saa;
			last  = hold_last;

			if (debugging)
			{	ARL *na;
				nested("new actual param list:\n");
				for (na = saa; na; na = na->nxt)
				{	prep_line(na->al);
					nested(""); printf("\t%s\n", lbuf);
					printf("\n"); fflush(stdout);
	}	}	}	}
#endif
	frst = lst = (TS *) 0;

	if (debugging && !m->body) printf("	empty body\n");

	purge_body(s, last, m, m->body);

	if (debugging)
	{	nested("PostPurge: ");
		prep_line(frst);
		printf("%s\n", lbuf);
	}

	token_pasting();

	if (debugging)
	{	nested("PostPaste: ");
		prep_line(frst);
		printf("%s\n", lbuf);
	}

	for (ni = frst; ni; ni = ni->nxt)		/* tag new TS seq with macro   */
	{	add_tag(ni, m);
		if (debugging)
		{	nested("");
			printf("tag expansion of %p with %s\t", ni, m->nm);
			tokfull(ni, stdout);
			printf("\n");
		}
		inherit_tags(s, last, ni);
	}

	if (frst)	/* replace macro s..last with expansion frst..lst */
	{	frst->space = s->space;
		if (!s->prv)
		{	start = frst;
			if (debugging) nested("new start\n");
		} else
		{	s->prv->nxt = frst;
			frst->prv = s->prv;
		}
	
		if (last && last->nxt)
		{	last->nxt->prv = lst;
			lst->nxt = last->nxt;
		}
	} else
	{	if (!s->prv)
		{	/* start = s->nxt; */
			start = last?last->nxt:last;
			if (debugging) nested("new start - no frst\n");
		} else
			s->prv->nxt = s->nxt;
	}
	if (debugging)
	{	nested("Done Expanding"); printf(" %s\n\n", m->nm);
		nested("PostAll: "); prep_line(start); printf("%s\n", lbuf);
	
		for (ni = start; ni; ni = ni->nxt)
		{	if (!ni->ml) continue;
			nested(""); printf("tags on %p ", ni);
			tokfull(ni, stdout);
			printf("are: ");
			for (mp = ni->ml; mp; mp = mp->nxt)
				printf(" %s,", mp->m->nm);
			printf("\n");
		}
		printf("\n");
		Enesting--;
	}

	return last;	/* point in parse string now reached */
}

static void
macro_expansion(void)
{	TS *s;
	MD *m;
	int count = 1, o_count = 0;

	while (count > o_count)
	{	o_count = count;
		prep_line(start);

		if (debugging) printf("%s,%d: Pass %d: <%s>\n",
			filename, lineno, count, lbuf);

		strcpy(sbuf, lbuf);
		for (s = start; s; s = s?s->nxt:s)
			if (s->tok == NAME
			&&  (m = is_macro(s->name)) != NULL)
			{	s = expand_macro(s, m);
				prep_line(start);
				if (strcmp(lbuf, sbuf) != 0)
				{	count++;
					break;	/* start over */
	}		}	}

	if (debugging) printf("Done: <%s>\n", lbuf);
}

void
preprocess(void)
{	int d;

	release_all(start);
	inl = start = (TS *) 0;

	strcpy(lbuf, ibuf);	/* from gh_cpp2.c */
	do_parsing();

	if (verbose>1) { printf("before: "); show_line(0, stdout); }

	d = do_directives();

	if ((d == 0 && !not_printing[level])
	|| d == -1	/* unrecognized include, may need macro expansion */
	|| d == 2	/*  0 + 2 -> #if   */
	|| d == 10	/*  8 + 2 -> #line */
	|| d == 12)	/* 10 + 2 -> #elif */
	{	macro_expansion();
		if (verbose>1) { printf("during: "); show_line(0, stdout); }
		post_expansion();
	}

	if (verbose>1) { printf("after%d: ", d); if (d) show_line(0, stdout); }

	if (d == -1 && !no_includes)					/* unrecognized include */
	{	prep_line(start->nxt->nxt);
		now = lbuf;
		d = do_include(lineno, filename);	/* post macro expansion */
		if (d == 0)	/* 0= not recognized, -1 failed, 1 ok */
		fprintf(stderr, "%s,%d: warning: unrecognized include directive\n",
			filename, lineno);
	}

	string_merge(start);
	if (stack_depth <= 1 || !main_only)
	{	show_line(d, stdout);
		if (explanations)
		 	show_expl(stdout, start);
	}
}

char *cnf[] = {			/* macros generated in makefile from cpp -dM */
	#include "configure.h"	/* violation of rule 19.1, include preceded by code */
	NULL,
};

void
preconfigure(void)
{	int i;

	for (i = 0; cnf[i] != NULL; i++)
	{	strcpy(ibuf, cnf[i]);
		preprocess();
	}
}

int
main(int argc, char *argv[])
{	int i;

	while (argc > 1 && argv[1][0] == '-')
	{	switch (argv[1][1]) {
		case 'D': add_def(&argv[1][2]); break;
		case 'd': debugging++; break;
		case 'I': add_sysdir(&argv[1][2]); break;
		case 'i': no_includes++; break;
		case 'm': misra_rules++; break;
		case 'n': numbered++; break;
		case 'U': rm_def(&argv[1][2]); break;
		case 'x': main_only = 1; break;
		case 'e': explanations = 1; break;
		case 'v': verbose++; break;
		default:
			fprintf(stderr, "usage: gh_cpp -[vinm] -[IDU] filename.c\n");
			fprintf(stderr, "	-I, -D, -U as in cpp\n");
			fprintf(stderr, "	-d	debugging, extra verbose\n");
			fprintf(stderr, "	-i	do not expand include files\n");
			fprintf(stderr, "	-m	check ~35 simple misra rules\n");
			fprintf(stderr, "	-m -m	check rules also for included files\n");
			fprintf(stderr, "	-n	numbered output\n");
			fprintf(stderr, "	-x	show only output for toplevel file\n");
			fprintf(stderr, "	-e	explain macro expansions\n");
			fprintf(stderr, "	-v	verbose\n");
			exit(1);
		}
		argc--; argv++;
	}

	add_sysdir("/usr/include");
	add_sysdir("/usr/include/sys");
#ifdef PC
	add_sysdir("/usr/lib/gcc-lib/i686-pc-cygwin/3.3.1/include");
#else
	add_sysdir("/usr/lib/gcc-lib/x86_64-redhat-linux/3.3.3/include");	/* ? */
#endif
	preconfigure();

	for (i = 0; predefs[i]; i++)
		add_def(predefs[i]);

	if (argc <= 1)
		do_file("<stdin>", 0, "<stdin>");	/* gh_cpp2.c */
	else while (argc > 1)
	{	do_file("<stdin>", 0, next_file(argv[1]));
		argc--; argv++;
	}

	if (misra_rules) show_violations();

	return 0;
}
