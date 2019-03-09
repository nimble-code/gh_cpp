#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include "gh_cpp.h"

extern int	verbose;

extern void	tokname(TS *, FILE *);
extern void	fatal_error(char *);
extern char	*emalloc(int);

/* provide an explanation of the preprocessing result */

typedef struct POS POS;

struct POS {
	int	from, len;
	MD	*m;
	POS	*nxt;
} *markings, *free_mark;

static void
add_mark(int from, int len, MD *m)
{	POS *p;

	for (p = markings; p; p = p->nxt)
		if (p->m == m
		&&  p->from + p->len == from)
		{	p->len += len;
			return;
		}

	if (free_mark)
	{	p = free_mark;
		free_mark = free_mark->nxt;
		memset(p, 0, sizeof(POS));
	} else
		p = (POS *) emalloc(sizeof(POS));

	p->from = from;
	p->len  = len;
	p->m = m;
	p->nxt = markings;
	markings = p;
}

static void
show_mark(FILE *fd, POS *p)
{	int i;

	if (!p) return;
	show_mark(fd, p->nxt);
	p->nxt = free_mark;
	free_mark = p;

	if (verbose) fprintf(fd, "      ");

	for (i = 0; i < p->from; i++)
		fprintf(fd, " ");
	for (i = 0; i < p->len; i++)
		fprintf(fd, "-");

	if (p->m)
		fprintf(fd, " [%s,%d: %s]",
			p->m->fnm, p->m->ln, p->m->nm);
	else
		fprintf(fd, " [undefined]");

	fprintf(fd, "\n");
}

static int
mark_macro(TS *s, int from, int len)
{	ML *m;

	for (m = s->ml; m; m = m->nxt)
		add_mark(from - s->space, len + s->space, m->m);

	return from+len;
}

void
show_expl(FILE *fd, TS *start)
{	char tmp[1024];
	TS *n;
	int pos = 0;

	markings = (POS *) 0;

	for (n = start; n; n = n->nxt)
	{	pos += n->space;

		switch (n->tok) {
		case NAME:
			pos = mark_macro(n, pos, strlen(n->name));
			break;
		case VAL:
			sprintf(tmp, "%d", n->val);
			pos = mark_macro(n, pos, strlen(tmp));
			break;
		case ECHAR:
			pos = mark_macro(n, pos, 1);
			/* fall thru */
		case CHAR:
			sprintf(tmp, "%c", n->val);
			pos = mark_macro(n, pos, strlen(tmp));
			break;
		case TPASTE:
			pos = mark_macro(n, pos, 2);
			break;
		default:
			fprintf(stderr, "saw: ");
			tokname(n, stderr);
			fprintf(stderr, "\n");
			fatal_error("unknown token");
	}	}

	show_mark(fd, markings);
}
