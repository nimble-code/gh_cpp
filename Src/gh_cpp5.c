#include <stdio.h>
#include <string.h>

typedef struct Rule Rule;
typedef struct Offd Offd;

struct Offd {
	char	*fnm;
	int	ln;
	Offd	*nxt;
};

static struct Rule {
	char	*tag;
	int	R_major, R_minor;
	Offd	*lst;
	Rule	*nxt;
} *violations;

extern char *filename;
extern int lineno, stack_depth, misra_rules;

extern char *emalloc(int);

void
m_rule(int R_major, int R_minor, char *tag)
{	Rule *r;
	Offd *o;

	if (misra_rules < 2 && stack_depth > 1) return;

	if (strcmp(filename, "<predef>") == 0) return;
	
	for (r = violations; r; r = r->nxt)
		if (r->R_major == R_major
		&&  r->R_minor == R_minor)
		{	for (o = r->lst; o; o = o->nxt)
				if (o->ln == lineno
				&&  strcmp(o->fnm, filename) == 0)
					return;
			break;
		}

	if (!r)
	{	r = (Rule *) emalloc(sizeof(Rule));
		r->R_major = R_major;
		r->R_minor = R_minor;
		r->tag = tag;
		r->nxt = violations;
		violations = r;
	}

	o = (Offd *) emalloc(sizeof(Offd));
	o->fnm = emalloc(strlen(filename)+1);
	strcpy(o->fnm, filename);
	o->ln = lineno;

	o->nxt = r->lst;
	r->lst = o;
}

static char *lastnm;

static void
show_one(Offd *o)
{
	if (!o) return;
	show_one(o->nxt);

	if (!lastnm || strcmp(lastnm, o->fnm) != 0)
		fprintf(stderr, "\n\t%s:\t", o->fnm);
	fprintf(stderr, "%d, ", o->ln);

	lastnm = o->fnm;
}

void
show_violations(void)
{	Rule *r;

	if (!violations) return;
	
	for (r = violations; r; r = r->nxt)
	{	fprintf(stderr, "non-compliance with misra-rule %d.%d: use of '%s'",
			r->R_major, r->R_minor, r->tag);
		lastnm = (char *) 0;
		show_one(r->lst);
		fprintf(stderr, "\n\n");
	}
}
