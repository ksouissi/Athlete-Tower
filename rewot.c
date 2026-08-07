/* an implementation of tower.c's solution 17), here is the approach:

sort athletes by descending weight+strength: x0, ... xn-1 results such that for no i < j xi.w+xi.s < xj.w+xj.s

(* idea: keep a heap of the tower so far, weightiest athlete at the root *)

w = 0	(* total weight of the tower so far *)
h = 0	(* height of the tower so far *)
i = n-1
H = {}	(* a heap of athletes, the weightiest at the root *)
do {
	if (xi.s >= w) {
		h++
		w += xi.w
		insert xi into H
	} else if (xi.w < root(H).w) {	(* if xi.s < w-root(H).w then xi.w > root(H).w [1] *)
		w = w - root(H).w + xi.w
		insert xi into (remove root(H) from H)
	}
} while (i--)

h = height of the tallest tower over x0, ... xn-1

[1]: We have, once athletes are sorted, i <= j => xi.w+xi.s >= xj.w+xj.s.
	Let w be the weight of tower-so-far at step i+1 proceeding backwards, m the max. athlete weight in said tower.
	xi.w+xi.s >= w (*) because athletes are sorted by descending weight+strength.
	If w > xi.s then w = xi.s+r with 0 < r <= xi.w (cf. (*)) hence w-m = xi.s+r-m.
	Now, if w-m > xi.s then r-m > 0 i.e., r > m. Since r <= xi.w, m < xi.w.
	Conclusion: if w-m > xi.s then max. athlete weight in tower-so-far smaller than athlete i weight.
*/

#define F(i)	((i) - 1 >> 1)
#define CH(i)	(((i) << 1) + 1)
#define R(i, cmp)	(CH(i) + 1 - cmp(CH(i), CH(i)+1))

#define MAXATHCOUNT 100000
struct a { int w, s; } x[MAXATHCOUNT];

/* heap, root = max., 0 <= x <= 2000000 */
struct a h[MAXATHCOUNT+1];
int l;	/* max. num of pushes = 100000 */

int cws(int i, int j) { return h[i].w+h[i].s > h[j].w+h[j].s; }
int cw(int i, int j) { return h[i].w > h[j].w; }
void swap(int i, int j)	{ h[i].w ^= h[j].w, h[i].s ^= h[j].s, h[j].w ^= h[i].w, h[j].s ^= h[i].s, h[i].w ^= h[j].w, h[i].s ^= h[j].s; }
void paws(int i, int j)	{ h[i].w ^= h[j].w, h[j].w ^= h[i].w, h[i].w ^= h[j].w; }

void push(struct a x, int (*cmp)(int i, int j), void (*swap)(int i, int j))
{
	int i = l;
	h[l].w = x.w;
	h[l].s = x.s;
	while (i) {
		if (cmp(i, F(i))) {
			swap(i, F(i));
			i = F(i);
		} else
			break;
	}
	l++;
	h[l].w = -1;	/* because of subst, strength: don't care */
}

/* non-empty heap, 0 <= w <= 2000000 */
void subst(int w)
{
	int i, j;
	h[0].w = w;
	for (i = 0; CH(i) < l; i = j) {
		j = R(i, cw);
		if (cw(j, i))
			paws(j, i);
		else
			break;
	}
}

/* non-empty heap */
void pop(struct a *r)
{
	int i, j;
	r->w = h[0].w;
	r->s = h[0].s;
	l--;
	h[0].w = h[l].w;
	h[0].s = h[l].s;
	h[l].w = -1;	/* so that, below R(i, cmp) does not return an out-of-bound index */
	h[l].s = 0;
	for (i = 0; CH(i) < l; i = j) {
		j = R(i, cws);
		if (cws(j, i))
			swap(j, i);
		else
			break;
	}
}

int f(int n)
{
	int H = 0,
		i = n-1;
	__int64 w = 0;

	do {
		if (x[i].s >= w) {
			H++;
			w += x[i].w;
			push(x[i], cw, paws);
		} else if (x[i].w < h[0].w) {	/* if xi.s < w-root(H).w then xi.w > root(H).w */
			w = w - h[0].w + x[i].w;
			subst(x[i].w);
		}
	} while (i--);
	return H;
}

#include <stdio.h>
#include <stdlib.h>
int main(int argc, char *argv[])
{
	if (argc == 1)	/* empty set (of athletes) */
		printf("0");
	else if (argc & 0x1) {
		int i = argc-1, n = i/2;
		do {
			x[0].s = atoi(argv[i--]);
			x[0].w = atoi(argv[i--]);
			push(x[0], cws, swap);
		} while (i);
		i = n-1;
		do {
			pop(&x[n-1-i]);
		} while (i--);
		/* l == 0 */
		/* x sorted by descending weight+strength */
		/*
		for (i = 0; i < n; i++) {
			printf("(%d, %d) ", x[i].w, x[i].s);
		} */
		printf("%d", f(n));
	} else	/* not sequence of pairs */
		printf("Usage: tower.exe (<weight> <strength>)*");
	return 0;
}
