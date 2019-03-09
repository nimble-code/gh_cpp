#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <malloc.h>
#include "gh_cpp.h"

/**** handle include files: interface: add_sysdir(), next_file(), do_file() */

static FILE	*mfd;
static ARGS	*sysdirs, *stacker;
static int	delta;

char	ibuf[MAXIN];
int	stack_depth;

extern int	verbose, lineno, level, incomment, sawcode;
extern int	no_includes, misra_rules, main_only;
extern int	not_printing[MAXLEVEL];
extern char	*now, *filename;

extern void	fatal_error(char *s);	/* gh_cpp1.c */
extern char	*emalloc(int);		/* gh_cpp1.c */
extern void	skipwhite(void);	/* gh_cpp1.c */
extern void	preprocess(void);	/* gh_cpp1.c */
extern void	m_rule(int, int, char *); /* gh_cpp5.c */

void do_file(char *, int, char *);

static void
push_stacker(char *s)
{	ARGS *n;

	for (n = stacker; n; n = n->nxt)
		if (strcmp(s, n->nm) == 0)
		{	if (verbose>1)
			{	for (n = stacker; n; n = n->nxt)
					fprintf(stderr, "--");
			}
			if (misra_rules)
				m_rule(19, 15, "include file processed twice");
			fprintf(stderr, "warning: circular #include \"%s\" -- nesting depth %d\n",
				s, stack_depth);
			if (stack_depth > 1024)
				fatal_error("max nesting depth exceeded; circular #include");
			break;
		}

	if (verbose>1)
	{	for (n = stacker; n; n = n->nxt)
			fprintf(stderr, "  ");
		fprintf(stderr, "%s\n", s);
	}
	n = (ARGS *) emalloc(sizeof(ARGS));
	n->nm = (char *) emalloc(strlen(s)+1);
	strcpy(n->nm, s);
	n->nxt = stacker;
	stacker = n;
	stack_depth++;
}

static void
pop_stacker(char *s)
{
	if (!stacker || strcmp(stacker->nm, s) != 0)
		fatal_error("internal error stack");
	stacker = stacker->nxt;
	stack_depth--;
}

static int
search_sys(ARGS *n, char *f)
{	char *s;
	FILE *nfd;

	if (!n) return 0;

	if (search_sys(n->nxt, f))
		return 1;

	s = (char *) emalloc(strlen(f)+strlen(n->nm)+1+1);
	sprintf(s, "%s/%s", n->nm, f);

	if (misra_rules)
	{	if (strcmp(s, "malloc.h") == 0)
			m_rule(20, 4, "<malloc.h>");
		else if (strcmp(s, "signal.h") == 0)
			m_rule(20, 8, "<signal.h>");
		else if (strcmp(s, "stdio.h") == 0)
			m_rule(20, 9, "<stdio.h>");
		else if (strcmp(s, "time.h") == 0)
			m_rule(20, 12, "<time.h>");
	}

	if ((nfd = fopen(s, "r")) == NULL)
	{	free(s);
		return 0;
	}
	if (verbose>1) printf("/**** #include: %s ****/\n", s);

	fclose(nfd);
	do_file(filename, lineno, s);
	free(s);

	return 1;
}

void
add_sysdir(char *s)
{	ARGS *inc;

	if (!s || strlen(s) < 2) return;

	for (inc = sysdirs; inc; inc = inc->nxt)
		if (strcmp(s, inc->nm) == 0)
			return;

	inc = (ARGS *) emalloc(sizeof(ARGS));
	inc->nm = (char *) emalloc(strlen(s)+1);
	strcpy(inc->nm, s);
	inc->nxt = sysdirs;
	sysdirs = inc;
}

char *
next_file(char *s)
{	char *t = (char *) emalloc(strlen(s)+1);
	strcpy(t, s);
	return t;
}

static int
trimline(char *b)
{	int len;

	len = strlen(b);
	if (len >= MAXIN) fatal_error("input line too long");

	while (len > 1
	&& (b[len-2] == ' '
	||  b[len-2] == '\t'))
	{	b[len-2] = '\n';
		b[len-1] = '\0';
		len--;
	}

	return len;
}

void
need_more(void)
{
	if (fgets(ibuf, MAXIN, mfd) == NULL)
		fatal_error("gh_cpp: unexpected eof");
	delta++;
	trimline(ibuf);
	/* should check if the line ends in a \\ */
}

int
do_include(int ln, char *from)
{	FILE *tfd;
	char *p, *q, *s;

	if (misra_rules
	&&  ln == 0	/* check top level source file only */
	&&  sawcode)
		m_rule(19, 1, "#include preceded by code");

	skipwhite();
	sawcode = 0;

	if (*now == '"')
	{	now++;
		p = strchr(now, '"');
		if (!p) fatal_error("syntax error in directive");
		*p = '\0';

		if ((q = strrchr(filename, '/')) != NULL
		&&   strrchr(now, '/') == NULL)	/* new 3/24/05 */
		{	/* prepend directory to name in now */
			*q = '\0';
			s = (char *) emalloc(strlen(filename)+strlen(now)+1+1);
			sprintf(s, "%s/%s", filename, now);
			*q = '/';
		} else
			s = next_file(now);

		if ((tfd = fopen(s, "r")) != NULL)
		{	fclose(tfd);
			if (verbose>1) printf("/**** #include: %s ****/\n", s);
			do_file(from, lineno, s);
		} else
		{	if (q != NULL)
				s = next_file(now); /* revert */
			if (!search_sys(sysdirs, s))
			{	if (!not_printing[level])
				fprintf(stderr, "%s,%d: cannot find include file %s\n",
					filename, lineno, s);
				*p = '"';
				return -1;
		}	}
		*p = '"';
	} else if (*now == '<')
	{	now++;
		p = strchr(now, '>');
		if (!p) fatal_error("syntax error in directive");
		*p = '\0';
		if (!search_sys(sysdirs, now))
		{	if (!not_printing[level])
			fprintf(stderr, "%s,%d: cannot find include file %s\n",
				filename, lineno, now);
			*p = '>';
			return -1;
		}
		*p = '>';
	} else
		return 0;	/* passed to preprocessor */

	if (stack_depth <= 1 || !main_only)
		printf("# %d \"%s\"\n", lineno, from);
	return 1;		/* not passed to preprocessor */
}

void
do_file(char *from, int ln, char *to)
{	FILE *ofd = mfd;
	int len, olevel = level;

	if (not_printing[level])
		return;

	push_stacker(to);

	if (strcmp(to, "<stdin>") == 0)
		mfd = stdin;
	else if ((mfd = fopen(to, "r")) == NULL)
		fatal_error("no such file");

	filename = to;
	lineno = 0;
	sawcode = 0;
	printf("# 1 \"%s\"\n", to);

	while (fgets(ibuf, MAXIN, mfd) != NULL)
	{	lineno += 1+delta; delta = 0;
		now = ibuf;

		len = trimline(ibuf);
		while (len > 1 && ibuf[len-2] == '\\')	/* one before newline */
		{	len -= 2;
			ibuf[len] = '\0';	/* remove \\ */

			if (fgets(&ibuf[len], MAXIN, mfd) == NULL)
				fatal_error("unexpected eof");

			delta++;
			len = trimline(ibuf);

			if (verbose>1)
			{	fprintf(stderr, "len %d of ", len);
				fprintf(stderr, "expanded line: %s\n", ibuf);
			}
		}

		skipwhite();
		if (!no_includes && *now++ == '#')
		{	skipwhite();
			if (strncmp(now, "include", strlen("include")) == 0
			&&  ((*(now+strlen("include")) == ' ')
			||   (*(now+strlen("include")) == '\t')))
			{	now += strlen("include");
				if (do_include(ln, to) != 0)	/* can call do_file recursively */
					continue;
		}	}

		preprocess();	/* should really always do this before do_include */
	}
	if (incomment)
	{	fprintf(stderr, "%s,%d: unterminated comment\n", filename, lineno);
		incomment = 0;
	}
	if (misra_rules && olevel != level)
		m_rule(19, 17, "unbalanced #if/#ifdef/#else/#elif/#endif directives");

	filename = from;
	lineno = ln;	/* restore to previous file */
	fclose(mfd);
	mfd = ofd;
	sawcode = 0;

	pop_stacker(to);
}
