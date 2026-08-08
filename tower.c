/*
BrainTeaser for Amazon interview:

*******

Coding exercise:

Every athlete is characterized by his mass 'm' (in kg) and strength 's' (in kg). You are to find the maximum number of athletes that can form a tower standing one upon another. An athlete can hold a tower of athletes with total mass equal to his strength or less than his strength. Input contains the number of athletes n and their parameters. These inputs can be assumed to be passed as arguments (Integer n and List<Pair<Integer, Integer>> parameterList) appropriate for your language of choice.

a0, ... an-1: n athletes
ai.s: ai strength, ai.w: ai weight

*******

Solutions:
-2) Suppose earth is spherical. Let (n+1)/2 athletes stand, each within leg distance of another athlete, somewhere on earth. The other n/2 athletes, let them stand at the antipodes (such that, for good measure, their feets' locations correspond to some feet-locations of the (n+1)/2 athletes). Then, all n athletes stand on 1 or 2 other athletes.

-1) Pile all athletes one on another (lay* them down).
* standing: 9 a : to remain stationary or inactive  *the car stood in the garage for a week*  b : to gather slowly and remain  *tears standing in her eyes* (Merriam-Webster's 11th Collegiate Dictionary)

0) A bruteforce solution:
i = n
L0:
Pi = { all ordered selections of i distinct elements from a0, ... an-1 }
if, for some (x0, ... xi-1) in Pi, for all 0 <= j < i-1, xj.s >= xj+1.w + ... xi-1.w then max_tower_athletes = i
else i = i - 1, goto L0

2) Another bf. sol.:
f(x0, ... xn-1) {
	w = x0.s	(* remaining weight-room *)
	for (i = 1; i < n; i++) {
		if (xi.w > w)
			break
		w = min(w-xi.w, xi.s)
	}
	return i;
}

P = { all permutations of a0, ... an-1 }
g() {
	m = 0
	foreach ((x0, ... xn-1) in P)
		if ((i = f(x0, ... xn-1)) > m)
			m = i
	return m
}

g() = max. num of athletes in a tower over a0, ... an-1

3) Yet another bf.:
g(X) {
	M	(* set of (h, w) where h is tower height and m the minimum weight of a tower of height h
			suppose M[h] = +infinity, for each h such that (h, w) in X, at the start *)
	foreach (x in X)
		if (x.w < M[x.h])
			M[x.h] = x.w
	return M
}

A = { a0, ... an-1 }
F[A] = { (h, w), where w is the minimum weight of all the towers in A of height h }, empty at the start

f(A) {
	if (A == {})
		F[A] = { (0, 0) }
	else {	(* A != {} *)
		foreach (x in A) {
			if (F[A - { x }] == {})	(* if f(A - { x }) hitherto not called *)
				f(A - { x })	(* memoize (f has no return value) *)
			(* now F[A - { x }] != {} *)
			foreach ((h, w) in F[A - { x }]) {
				F[A] += { (h, w) }	(* because later, it may turn out that this can be heightened above so-far-tallest towers *)
				if (x.s >= w)
					F[A] += { (h+1, x.w+w) }
			}
		}
		F[A] = g(F[A])	(* keep only, per height, the lightest since any new athletes won't be in any of A's towers *)
	}
}

f(A)
m = 0
foreach ((h, w) in F[A])
	if (m < h)
		m = h
m is the height of the tallest towers over A

4) Another bf. solution:
W(x) {
	w = 0
	foreach (y in x)
		w += y.w
	return w
}

A = { a0, ... an-1 }
B = { { x }, x in A }	(* elements of B are just sets *)
i = 1
L0:
	C = {}
	foreach (x in B)
		foreach (y in A \ x) {
			if (y.s >= W(x))
				C = C + { { y } + x }	(* C is a set: no redundance although x (in C) may have been constructed more than once *)
		}
	if (C == {})
		break
	B = C
	i++
goto L0

Then, i is the max. number of athletes in a tower over A.

5) Bf.:
W(x) {
	w = 0
	foreach (y in x)
		w += y.w
	return w
}

A = { a0, ... an-1 }
f(A) {
	B = { {} }
	i = 0
	for (;;) {
		C = {}
		foreach (x in P(A) such that |x| == i+1) {	(* P(A) = { x such that x inc. in A } *)
			foreach (y in x)
				if (x \ { y } in B and y.s >= W(x \ { y })) {
					C = C + { x }
					break
				}
		}
		if (C == {})
			break
		B = C
		i++
	}
	return i
}

f(A) gives the max number of athletes in a tower over A

6) Still bf.:
W(x) {
	w = 0
	foreach (y in x)
		w += y.w
	return w
}

F[X] = {} before f is called

f(A) {
	if (F[A] != {})
		return F[A]
	if (A == {})
		return F[{}] = 1
	foreach (x in A)
		if (x.s >= W(A \ { x }) && f(A \ { x }))
			return F[A] = 1
	return F[A] = 0
}

g(A) {
	for (i = |A|; i >= 0 (* i == 0: case A == {}, {} is subset of {} *); i--)
		foreach (X subset of A and |X| == i)
			if (f(X))
				goto L0
L0:
	return i
}

g(A) = height of the tallest towers over A

7) A solution:
x in A, S(x) = { y / x.s >= y.w and x != y }
choose an x0, next choices: x1 in S(x0), x2 in S(x0) ^ S(x1) ... xi in S(x0) ^ ... S(xi-1) (X ^ Y = intersection of X and Y)
remaining weight-room for xi = min(x0.s - x1.w - ... xi-1.w, xi-1.s)

f(A, w, h) {
	i = h
	foreach (x in A such that x.w <= w)	(* confine iteration to all xi in S(x0) ^ ... S(xi-1), then don't skip the rec. only if xi.w <= w *)
		if (i < (j = f(A ^ S(x), min(w-x.w, x.s), h+1)))	(* no y out of A ^ S(x) can stand on top of the current tower *)
			i = j
	return i	(* if { x in A such that x.w <= w } == {} then i = h *)
}

g(A) {
	h = 0
	foreach (x in A)
		if (h < (i = f(S(x), x.s, 1)))
			h = i
	return h
}

g(A) = height of the tallest towers over A

8) 7) * 3):
A = { a0, ... an-1 }
F[A] = { (h, w), where w is the minimum weight of all the towers in A of height h }, empty at the start
x in A, S(x) = { y / x.s >= y.w and x != y }
choose an x0, next choices: x1 in S(x0), x2 in S(x0) ^ S(x1) ... xi in S(x0) ^ ... S(xi-1) (X ^ Y = intersection of X and Y)

g(X) {
	M	(* set of (h, w) where h is tower height and m the minimum weight of a tower of height h
			suppose M[h] = +infinity, for each h such that (h, w) in X, at the start *)
	foreach (x in X)
		if (x.w < M[x.h])
			M[x.h] = x.w
	return M
}

f(A) {
	if (A == {})
		F[A] = { (0, 0) }
	else {	(* A != {} *)
		foreach (x in A) {
			if (F[A ^ S(x)] == {})	(* if f(A ^ S(x)) hitherto not called *)
				f(A ^ S(x))	(* memoize (f has no return value) *)
			(* now F[A ^ S(x)] != {} *)
			foreach ((h, w) in F[A ^ S(x)]) {
				F[A] += { (h, w) }	(* because later, it may turn out that this can be heightened above so-far-tallest towers *)
				if (x.s >= w)
					F[A] += { (h+1, x.w+w) }
			}
		}
		F[A] = g(F[A])	(* keep only, per height, the lightest since any athletes out of A won't be in any of A's towers *)
	}
}

f(A)
m = 0
foreach ((h, w) in F[A])
	if (m < h)
		m = h
m is the height of the tallest towers over A

R(x, y) = min(x.s - y.w, y.s) > min(y.s - x.w, x.s)
if x.w >= y.w & x.s >= y.s then swapping x and y does not shorten a tower, note that R(x, y)
x.w > y.s: x does not occur in any tower with base y

*******

The above statement of the exercise is actually incomplete. As a matter of fact, the problem is:

Every athlete is characterized by his mass 'm' (in kg) and strength 's' (in kg). You are to find the maximum number of athletes that can form a tower standing one upon another. An athlete can hold a tower of athletes with total mass equal to his strength or less than his strength. Input contains the number of athletes n and their parameters. These inputs can be assumed to be passed as arguments (Integer n and List<Pair<Integer, Integer>> parameterList) appropriate for your language of choice: For example:

n m1 s1 m2 s2 ... mn sn If mi > mj then si > sj, but athletes with equal masses can be of different strength. Number of athletes n < 100000. Masses and strengths are positive integers less than 2000000. For example: Input #1

4 3 4 2 2 7 6 4 5 Would yield Output #1

3

*******

xj.w < xi.w & xj.s < xi.s:
No tower (... xj, ... xi, ....) is going to collapse should such a xi and xj be exchanged: (... xi, ... xj, ....) is still a tower

x.w = y.w+z
x.s = y.s-z => x.w+x.s = y.w+y.s
x.w-y.w = y.s-x.s => same remaining weight-room whether y on x or x on y

9) Sorting, bf.:
xi.w = athlete i's mass
xi.s = strength of athlete i
(xi.w > xj.w => xi.s > xj.s) <=> (xi.s <= xj.s => xi.w <= xj.w)

Sort athletes by decreasing weight and, for equal weights, by decreasing strength, yielding the sequence x0, ... xn-1 such that 0 <= i < j < n => !(xj.s > xi.s)

h = 0
foreach (subsequence s of xi, ... xn-1)
	if (s is a tower && |s| > h)
		h = |s|

h is the height of the tallest towers over athletes x0, ... xn-1

10) Sorting:
f(i, j) {
	if (i == j)
		return { (1, xi.w, xi.s) }
	{
		F = {}
		foreach ((h, w, r) in f(i, (i+j)/2))	(* h: tower height, w: total tower weight, r: remaining weight-room *)
			foreach ((h', w', r') in f((i+j)/2+1, j)) {
				F += { (h, w, r), (h', w', r') }
				if (r >= w')
					F += { (h+h', w+w', min(r-w', r'))}	(* stack tower over x(i+j)/2+1, ... xj upon tower over xi, ... x(i+j)/2 *)
			}
	}
	return F
}

F = f(0, n-1)
H = 0
foreach ((h, w, r) in F)
	if (h > H)
		H = h
H is the height of the tallest towers over x0, ... xn-1

11) Ibid.:
g(X) {
	M	(* set of (h, r) where h is tower height and r the max. remaining weight-room of tower of height h
			suppose M[h] = -1, for each h such that (h, r) in X, at the start *)
	foreach (x in X)
		if (x.r > M[x.h])
			M[x.h] = x.r
	return M
}

f(i) {
	if (!i)
		return { (1, x0.s) }
	{
		F = {}
		foreach ((h, r) in f(i-1)) {	(* h: tower height, r: max. remaining weight-room for a tower of height h *)
			F += { (h, r) }	(* keep prev. tower params. so as to skip athletes *)
			if (r >= xi.w)
				F += { (h+1, min(r-xi.w, xi.s)) }	(* put xi on each height's strongest tower top so far *)
		}
	}
	return g(F)	(* return one pair per height corresponding to that height's strongest tower *)
}

F = f(n-1)
H = 0
foreach ((h, r) in F)
	if (h > H)
		H = h
H is the height of the tallest towers over x0, ... xn-1

12) etc.:
S[h] = per height h, the max. remaing weight-room for a tower of height h, intially = -1 (i.e., no tower of that height) except S[0] = x0.s
T = S (* T = back-buffer *)
for (i = 1; i < n; i++) {	(* x0 is the strongest tower of height 1 (because of the sorting) *)
	(* so as not to put xi on xi, below *)
	for (j = 1; j <= i; j++) {	(* check each possible height so far excet x0 *)
		if ((r = min(S[j-1] - xi.w, xi.s)) >= 0 && S[j] < r)
			T[j] = r	(* a stronger tower of height j has been found *)
		if (S[j] < 0)
			break
	}
	S = T	(* refresh S *)
}
i = n-1
while (S[i] < 0)	(* S[0] >= 0 because at least one athlete *)
	i--
i+1 is the height of the tallest tower over x0, ... xn-1

13)
g(X) {
	M	(* set of (h, w) where h is tower height and w the minimum weight of a tower of height h
			suppose M[h] = +infinity, for each h such that (h, w) in X, at the start *)
	foreach (x in X)
		if (x.w < M[x.h])
			M[x.h] = x.w
	return M
}

f(i) {
	if (i == n) {
		F = { (0, 0) }
		return
	}
	(* 0 <= i < n *)
	f(i+1)
	(* now F contains, for each height < n - i - 1, the lightest towers over xi+1, ... xn-1 *)
	G = {}
	foreach ((h, w) in F) {
		G += { (h, w) }
		if (xi.s >= w)
			G += { (h+1, xi.w + w) }
	}
	F = g(G)	(* keep only the lightest towers per height, over xi, ... xn-1 *)
}

f(0)
m = 0
foreach ((h, w) in F)
	if (m < h)
		m = h
m is the height of the tallest towers over x0, ... xn-1

14)
xi.w = athlete i's mass
xi.s = strength of athlete i
(xi.w > xj.w => xi.s > xj.s) <=> (xi.s <= xj.s => xi.w <= xj.w)

Sort athletes by decreasing weight and, for equal weights, by decreasing strength, yielding a sequence x0, ... xn-1 such that 0 <= i < j < n => !(xj.s > xi.s)

===

S = for each height, min. weight of all towers of that height, so far	(* 0 < i <= n => S[i] = M = x0.w + ... xn-1.w + 1 = max tower weight + 1
																			S[0] = 0 = weight of tower of height 0 *)
T = S	(* T back-buffer, so as not to put an athlete below itself *)
i = n-1
do {
	j = 0
	do {
		j++
		if (xi.s >= S[j-1] && xi.w + S[j-1] < S[j])
			T[j] = xi.w + S[j-1]
		if (S[j] == M)
			break
	} while (j < n - i)
	S = T
} while (i--)

i = n	(* max. tower height over n athletes *)
while (S[i] == M)
	i--

i = height of the tallest towers over x0, ... xn-1

===

S = for each height, min. weight of all towers of that height, so far. initially S0 = 0, don't care if i > 0
i = n-1	(* suppose n > 1 *)
m = 0	(* m = max. tower height *)
do {
	j = m
	if (xi.s >= S[j])	(* xi can support the tallest tower so far: max. height++ *)
		S[++m] = xi.w + S[j]
	while (j--)	(* not the tallest towers: must check whether a lighter tower results *)
		if (xi.s >= S[j] && xi.w + S[j] < S[j+1])
			S[j+1] = xi.w + S[j]
} while (i--)

m = height of the tallest towers over x0, ... xn-1

15) The better solution (perhaps worth implementing):
xi.w = athlete i's mass
xi.s = strength of athlete i
(xi.w > xj.w => xi.s > xj.s) <=> (xi.s <= xj.s => xi.w <= xj.w)
(xi.w > xj.w => xi.s > xj.s) => xi.w + xi.s > xj.w + xj.s

Sort athletes by decreasing weight and, for equal weights, by decreasing strength, yielding a sequence x0, ... xn-1 such that 0 <= i < j < n => !(xj.s > xi.s)

(* xn-1 is the lightest tower of height 1
binary-search in x0, ... xn-2 the rightmost, hence lighest, athlete xi that can hold (xn-1): (xi, xn-1) is the lightest tower of height 2
binary-search in x0, ... xi-1 the rightmost athlete xj that can hold (xi, xn-1): (xj, xi, xn-1) is the lightest tower of height 3
and so on *)
(* n > 0 *)
l = 0, r = n-2
h = 1
w = xn-1.w
while (r >= 0) {
	if (r < l) {
		(* xr is the lightest athlete who can bear weight w *)
		h++
		w += xr.w
		l = 0
		r--
		continue
	}
	m = (l+r)/2
	if (xm.s >= w)
		l = m+1
	else
		r = m-1
}

h = height of the tallest towers over x0, ... xn-1

*******

Now drop xi.w > xj.w => xi.s > xj.s

*******

if x0, ... xn-1 is sorted by decreasing weight+strength, 14) works

16) Complicated:
athletes x0, ... xn-1 sorted by decreasing weight+strength

S = for each height, min. weight of all towers of that height, so far. initially S0 = 0, don't care if i > 0
i = n-1	(* suppose n > 1 *)
m = 0	(* m = max. tower height so far *)
do {
	T = array of indices into S, sorted by descending S[T[i]], that is, for no i < j is S[T[i]] < S[T[j]]
	binary-search for p such that for all k >= p, xi.s >= S[T[k]]	(* restrict work to those towers-so-far that xi can support *)
	U = sorted T[p, m] (ascending T[i])	(* U[k] is an index into S, must update taller towers before the shorter *)
	if ((k = |U|-1) >= 0) {	(* there are towers-so-far that xi can support *)
		if (U[k] == m) {	(* add an additional height *)
			S[m+1] = xi.w + S[m]
			m++
			while (k--) {	(* the remaining not-tallest-towers-so-far *)
				if (xi.w + S[U[k]] < S[U[k]+1])
					S[U[k]+1] = xi.w + S[U[k]]
			}
		} else do {
			if (xi.w + S[U[k]] < S[U[k]+1])
				S[U[k]+1] = xi.w + S[U[k]]
		} while (k--)
	}
} while (i--)

m = height of the tallest towers over x0, ... xn-1

17) A better general solution,
	worth implementing: see rewot.c

Sort athletes by descending weight+strength: x0, ... xn-1 results such that for no i < j xi.w+xi.s < xj.w+xj.s

(* idea: keep a heap of the tower so far, weightiest athlete at the root.
	one is reminded of a of CG depth-sort-like procedure:
	incoming athlete = a new polygon, max-encountered-so-far-athletes-weight = min-depth-so-far
	with this difference that we need to keep the "prev. polygon-depths" since we're replacing max. weight by a smaller weight but still
	need the largest weight-so-far immediately accessible.
	this should solve the problem for, athletes in all towers of max. height must be, from bottom to top, stacked in descending weight+strength order.
	therefore, after sorting the athletes by descending weight+strength, for each i, xi cannot be anywhere in any largest-height-tower over xi, ... xn-1 except at the bottom.
	now, either max. height tower over xi+1, ... xn-1 can be supported by xi, extending it, or else said tower won't get any weightier (but perhaps lighter)
	and still be among the tallest (and then, lightest) towers that can be built over xi, ... xn-1. *)

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

/* Please notice that if xj.w+xj.s >= xi.w+xi.s and (xi, xj) (that is, xj on top of xi) is a tower, then (xj, xi) is also a tower with no less remaining weight-room = min(xj.s - xi.w, xi.s),
	and if (xj, xi) is no tower then neither is (xi, xj): there is no point in placing xj after xi, regardless of (xi.w > xj.w => xi.s > xj.s) => xi.w + xi.s > xj.w + xj.s.
	Conclusion: the athletes shall be ordered by descending weight + strength. */

struct a { int w, s; } x[100000];

#define SWAP(i, j)	do { x[i].w ^= x[j].w, x[i].s ^= x[j].s, x[j].w ^= x[i].w, x[j].s ^= x[i].s, x[i].w ^= x[j].w, x[i].s ^= x[j].s; } while (0)
/* sort by mass + strength, the output array is such that i < j => !(x[j].w+x[j].s > x[i].w+x[i].s) */
void radix_sort(int l, int r, int b)
{
	if (l < r) {
		int l0 = l, r0 = r;

		for(;;) {
L0:
			if (~(x[l0].w+x[l0].s) & 1 << b) {
				do {
					if ((x[r0].w+x[r0].s) & 1 << b) {
						SWAP(l0, r0);
						l0++, r0--;
						if (r0 < l0)
							goto L1;
						goto L0;
					}
					r0--;
					if (r0 < l0)
						goto L1;
				} while (1);
			}
			l0++;
			if (r0 < l0)
				break;
		}
L1:
		if (b) {
			radix_sort(l, r0, b - 1);
			radix_sort(r0 + 1, r, b - 1);
		}
	}
}

/* n > 0, x sorted */
/* relies on xi.w >= xj.w => xi.s >= xj.s */
int f(int n) {
	int l = 0, r = n-2, h = 1, m;
	__int64 w = x[n-1].w;	/* because acc. */

	while (r >= 0) {
		if (r < l) {	/* 0 <= r < l: no out-of-bounds access, below */
			/* x[r] is the lightest athlete who can bear weight w */
			h++;
			w += x[r].w;
			l = 0;
			r--;
			continue;	/* finis? */
		}
		m = (l+r)/2;
		if (x[m].s >= w)
			l = m+1;
		else
			r = m-1;
	}
	return h;
}

/* slow, works without xi.w > xj.w => xi.s > xj.s */
#define NNG(x) (~(x) >> 31 & (x))
__int64 S[100001];	/* S[i] = lightest tower, so far, of height i, S[0] = 0 */
int g(int n)
{
	int i, j, m;
	m = 0;	/* max. height so far */
	i = n-1;
	do {
		j = m;
		if (x[i].s >= S[j])	/* xi can support the tallest tower so far: max. height++ */
			S[++m] = x[i].w + S[j];
		while (j > NNG(m-i)) {	/* not the tallest towers: must check whether a lighter tower results.
									touch not heights which can no longer surpass the current top.
									given the number of remaining athletes = i+1,
									m-i = m-(i+1)+1 = smallest height that still may grow past m
									j > NNG(m-i) because j-- just afterwards */
			j--;
			if (x[i].s >= S[j] && x[i].w + S[j] < S[j+1])
				S[j+1] = x[i].w + S[j];
		}
	} while (i--);

	return m;	/* = height of the tallest towers over x0, ... xn-1 */
}

#include <stdio.h>
#include <stdlib.h>

/* contrary to the problem spec., the number of athletes is not to be input since it is redundant */
int main(int argc, char *argv[]) {
	if (argc == 1)	/* empty set (of athletes) */
		printf("0");
	else if (argc & 0x1) {
		int i = argc-1, n = i/2;
		struct a *p = &x[n-1];
		do {
			p->s = atoi(argv[i--]);
			p->w = atoi(argv[i--]);
			p--;
		} while (i);
		/* athletes read into x[0, n-1] */
		radix_sort(0, n-1, 21);	/* 2^21 < 2000000 + 2000000 < 2^22 */
		/* for (i = 0; i < n; i++)
			printf("(%d, %d) ", x[i].w, x[i].s); */
		printf("f(%d) = %d, g(%d) = %d", n, f(n), n, g(n));
	} else	/* not sequence of pairs */
		printf("Usage: tower.exe (<weight> <strength>)*");
	return 0;
}
