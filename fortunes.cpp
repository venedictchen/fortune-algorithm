#include <vector>
#include <tuple>
#include <queue>
#include <cmath>
#include <algorithm>
#include <cstdio>
#include <stack>
#include <iostream>
// #include <emscripten.h>

using namespace std;

typedef pair<int, int> pii;
typedef pair<double, double> pdd;

const double EPS = 1e-9;
int dcmp(double x) { return x < -EPS ? -1 : x > EPS ? 1
													: 0; }
static double dx = 0, dy = 0, scale = 1e-8;
vector<pdd> input;
vector<pdd> vertex;
vector<pii> edge;
vector<pii> area;

double operator/(pdd a, pdd b) { return a.first * b.second - a.second * b.first; }
pdd operator*(double b, pdd a) { return pdd(b * a.first, b * a.second); }
pdd operator+(pdd a, pdd b) { return pdd(a.first + b.first, a.second + b.second); }
pdd operator-(pdd a, pdd b) { return pdd(a.first - b.first, a.second - b.second); }

double sq(double x) { return x * x; }
double size(pdd p) { return hypot(p.first, p.second); }
double sz2(pdd p) { return sq(p.first) + sq(p.second); }
pdd r90(pdd p) { return pdd(-p.second, p.first); }

pdd line_intersect(pdd a, pdd b, pdd u, pdd v) { return u + (((a - u) / b) / (v / b)) * v; }
pdd get_circumcenter(pdd p0, pdd p1, pdd p2)
{
	return line_intersect(0.5 * (p0 + p1), r90(p0 - p1), 0.5 * (p1 + p2), r90(p1 - p2));
}

// https://www.youtube.com/watch?v=h_vvP4ah6Ck
double parabola_intersect(pdd left, pdd right, double sweepline)
{
	/*
	if(dcmp(left.second - right.second) == 0) return (left.first + right.first) / 2.0; /*/
	auto f2 = [](pdd left, pdd right, double sweepline)
	{
		int sign = left.first < right.first ? 1 : -1;
		pdd m = 0.5 * (left + right);
		pdd v = line_intersect(m, r90(right - left), pdd(0, sweepline), pdd(1, 0));
		pdd w = line_intersect(m, r90(left - v), v, left - v);
		double l1 = size(v - w), l2 = sqrt(sq(sweepline - m.second) - sz2(m - w)), l3 = size(left - v);
		return v.first + (m.first - v.first) * l3 / (l1 + sign * l2);
	};
	if (fabs(left.second - right.second) < fabs(left.first - right.first) * EPS)
		return f2(left, right, sweepline); // */
	int sign = left.second < right.second ? -1 : 1;
	pdd v = line_intersect(left, right - left, pdd(0, sweepline), pdd(1, 0));
	double d1 = sz2(0.5 * (left + right) - v), d2 = sz2(0.5 * (left - right));
	return v.first + sign * sqrt(max(0.0, d1 - d2));
}

class Beachline
{
public:
	struct node
	{
		node() {}
		node(pdd point, int idx) : point(point), idx(idx), end(0),
								   link{0, 0}, par(0), prv(0), nxt(0) {}
		pdd point;
		int idx;
		int end;
		node *link[2], *par, *prv, *nxt;
	};
	node *root;
	double sweepline;

	Beachline() : sweepline(-1e20), root(NULL) {}
	inline int dir(node *x) { return x->par->link[0] != x; }

	//     p        n          p            n
	//    / \      / \        / \          / \
		//   n   d => a   p   or a   n   =>   p   d
	//  / \          / \        / \      / \
		// a   b        b   d      c   d    a   c

	void rotate(node *n)
	{
		node *p = n->par;
		int d = dir(n);
		p->link[d] = n->link[!d];
		if (n->link[!d])
			n->link[!d]->par = p;
		n->par = p->par;
		if (p->par)
			p->par->link[dir(p)] = n;
		n->link[!d] = p;
		p->par = n;
	}

	void splay(node *x, node *f = NULL)
	{
		while (x->par != f)
		{
			if (x->par->par == f)
				;
			else if (dir(x) == dir(x->par))
				rotate(x->par);
			else
				rotate(x);
			rotate(x);
		}
		if (f == NULL)
			root = x;
	}

	void insert(node *n, node *p, int d)
	{
		splay(p);
		node *c = p->link[d];
		n->link[d] = c;
		if (c)
			c->par = n;
		p->link[d] = n;
		n->par = p;

		node *prv = !d ? p->prv : p, *nxt = !d ? p : p->nxt;
		n->prv = prv;
		if (prv)
			prv->nxt = n;
		n->nxt = nxt;
		if (nxt)
			nxt->prv = n;
	}

	void erase(node *n)
	{
		node *prv = n->prv, *nxt = n->nxt;
		if (!prv && !nxt)
		{
			if (n == root)
				root = NULL;
			return;
		}
		n->prv = NULL;
		if (prv)
			prv->nxt = nxt;
		n->nxt = NULL;
		if (nxt)
			nxt->prv = prv;
		splay(n);
		if (!nxt)
		{
			root->par = NULL;
			n->link[0] = NULL;
			root = prv;
		}
		else
		{
			splay(nxt, n);
			node *c = n->link[0];
			nxt->link[0] = c;
			c->par = nxt;
			n->link[0] = NULL;
			n->link[1] = NULL;
			nxt->par = NULL;
			root = nxt;
		}
	}
	bool get_event(node *cur, double &next_sweep)
	{
		if (!cur->prv || !cur->nxt)
			return false;
		pdd u = r90(cur->point - cur->prv->point);
		pdd v = r90(cur->nxt->point - cur->point);
		if (dcmp(u / v) != 1)
			return false;
		pdd p = get_circumcenter(cur->point, cur->prv->point, cur->nxt->point);
		next_sweep = p.second + size(p - cur->point);
		return true;
	}
	node *find_beachline(double x)
	{
		node *cur = root;
		while (cur)
		{
			double left = cur->prv ? parabola_intersect(cur->prv->point, cur->point, sweepline) : -1e30;
			double right = cur->nxt ? parabola_intersect(cur->point, cur->nxt->point, sweepline) : 1e30;
			if (left <= x && x <= right)
			{
				splay(cur);
				return cur;
			}
			cur = cur->link[x > right];
		}
	}
};
using BeachNode = Beachline::node;

static BeachNode *arr;
static int sz;
static BeachNode *new_node(pdd point, int idx)
{
	arr[sz] = BeachNode(point, idx);
	return arr + (sz++);
}

struct event
{
	event(double sweep, int idx) : type(0), sweep(sweep), idx(idx) {}
	event(double sweep, BeachNode *cur) : type(1), sweep(sweep), prv(cur->prv->idx), cur(cur), nxt(cur->nxt->idx) {}
	int type, idx, prv, nxt;
	BeachNode *cur;
	double sweep;
	bool operator>(const event &l) const { return sweep > l.sweep; }
};

void VoronoiDiagram(vector<pdd> &input, vector<pdd> &vertex, vector<pii> &edge, vector<pii> &area)
{
	Beachline beachline = Beachline();
	priority_queue<event, vector<event>, greater<event>> events;

	auto add_edge = [&](int u, int v, int a, int b, BeachNode *c1, BeachNode *c2)
	{
		if (c1)
			c1->end = edge.size() * 2;
		if (c2)
			c2->end = edge.size() * 2 + 1;
		edge.emplace_back(u, v);
		area.emplace_back(a, b);
	};
	auto write_edge = [&](int idx, int v)
	{ idx % 2 == 0 ? edge[idx / 2].first = v : edge[idx / 2].second = v; };
	auto add_event = [&](BeachNode *cur)
	{ double nxt; if(beachline.get_event(cur, nxt)) events.emplace(nxt, cur); };

	int n = input.size(), cnt = 0;
	arr = new BeachNode[n * 4];
	sz = 0;
	sort(input.begin(), input.end(), [](const pdd &l, const pdd &r)
		 { return l.second != r.second ? l.second < r.second : l.first < r.first; });

	BeachNode *tmp = beachline.root = new_node(input[0], 0), *t2;
	for (int i = 1; i < n; i++)
	{
		if (dcmp(input[i].second - input[0].second) == 0)
		{
			add_edge(-1, -1, i - 1, i, 0, tmp);
			beachline.insert(t2 = new_node(input[i], i), tmp, 1);
			tmp = t2;
		}
		else
			events.emplace(input[i].second, i);
	}
	while (events.size())
	{
		event q = events.top();
		events.pop();
		BeachNode *prv, *cur, *nxt, *site;
		int v = vertex.size(), idx = q.idx;
		beachline.sweepline = q.sweep;
		if (q.type == 0)
		{
			pdd point = input[idx];
			cur = beachline.find_beachline(point.first);
			beachline.insert(site = new_node(point, idx), cur, 0);
			beachline.insert(prv = new_node(cur->point, cur->idx), site, 0);
			add_edge(-1, -1, cur->idx, idx, site, prv);
			add_event(prv);
			add_event(cur);
		}
		else
		{
			cur = q.cur, prv = cur->prv, nxt = cur->nxt;
			if (!prv || !nxt || prv->idx != q.prv || nxt->idx != q.nxt)
				continue;
			vertex.push_back(get_circumcenter(prv->point, nxt->point, cur->point));
			write_edge(prv->end, v);
			write_edge(cur->end, v);
			add_edge(v, -1, prv->idx, nxt->idx, 0, prv);
			beachline.erase(cur);
			add_event(prv);
			add_event(nxt);
		}
	}
	delete arr;
}

struct Point
{
	double x, y;
};

// A global point needed for  sorting points with reference
// to  the first point Used in compare function of qsort()
Point p0;

// A utility function to find next to top in a stack
Point nextToTop(stack<Point> &S)
{
	Point p = S.top();
	S.pop();
	Point res = S.top();
	S.push(p);
	return res;
}

// A utility function to swap two points
void swap(Point &p1, Point &p2)
{
	Point temp = p1;
	p1 = p2;
	p2 = temp;
}

// A utility function to return square of distance
// between p1 and p2
int distSq(Point p1, Point p2)
{
	return (p1.x - p2.x) * (p1.x - p2.x) +
		   (p1.y - p2.y) * (p1.y - p2.y);
}

// To find orientation of ordered triplet (p, q, r).
// The function returns following values
// 0 --> p, q and r are collinear
// 1 --> Clockwise
// 2 --> Counterclockwise
int orientation(Point p, Point q, Point r)
{
	int val = (q.y - p.y) * (r.x - q.x) -
			  (q.x - p.x) * (r.y - q.y);

	if (val == 0)
		return 0;			  // collinear
	return (val > 0) ? 1 : 2; // clock or counterclock wise
}

// A function used by library function qsort() to sort an array of
// points with respect to the first point
int compare(const void *vp1, const void *vp2)
{
	Point *p1 = (Point *)vp1;
	Point *p2 = (Point *)vp2;

	// Find orientation
	int o = orientation(p0, *p1, *p2);
	if (o == 0)
		return (distSq(p0, *p2) >= distSq(p0, *p1)) ? -1 : 1;

	return (o == 2) ? -1 : 1;
}

// Prints convex hull of a set of n points.
vector<pdd> convexHull(Point points[], int n)
{
	// Find the bottommost point
	int ymin = points[0].y, min = 0;
	for (int i = 1; i < n; i++)
	{
		int y = points[i].y;

		// Pick the bottom-most or choose the left
		// most point in case of tie
		if ((y < ymin) || (ymin == y &&
						   points[i].x < points[min].x))
			ymin = points[i].y, min = i;
	}

	// Place the bottom-most point at first position
	swap(points[0], points[min]);

	// Sort n-1 points with respect to the first point.
	// A point p1 comes before p2 in sorted output if p2
	// has larger polar angle (in counterclockwise
	// direction) than p1
	p0 = points[0];
	qsort(&points[1], n - 1, sizeof(Point), compare);

	// If two or more points make same angle with p0,
	// Remove all but the one that is farthest from p0
	// Remember that, in above sorting, our criteria was
	// to keep the farthest point at the end when more than
	// one points have same angle.
	int m = 1; // Initialize size of modified array
	for (int i = 1; i < n; i++)
	{
		// Keep removing i while angle of i and i+1 is same
		// with respect to p0
		while (i < n - 1 && orientation(p0, points[i],
										points[i + 1]) == 0)
			i++;

		points[m] = points[i];
		m++; // Update size of modified array
	}

	// If modified array of points has less than 3 points,
	// convex hull is not possible
	if (m < 3)
		return {};

	// Create an empty stack and push first three points
	// to it.
	stack<Point> S;
	S.push(points[0]);
	S.push(points[1]);
	S.push(points[2]);

	// Process remaining n-3 points
	for (int i = 3; i < m; i++)
	{
		// Keep removing top while the angle formed by
		// points next-to-top, top, and points[i] makes
		// a non-left turn
		while (S.size() > 1 && orientation(nextToTop(S), S.top(), points[i]) != 2)
			S.pop();
		S.push(points[i]);
	}

	// Now stack has the output points, print contents of stack
	vector<pdd> hull;
	while (!S.empty())
	{
		Point p = S.top();
		hull.push_back({p.x, p.y});
		S.pop();
	}
	return hull;
}

extern "C"
{
	pair<vector<pdd>, vector<pdd>> display(
		vector<pdd> input, vector<pdd> vertex, vector<pii> edge, vector<pii> area)
	{
		vector<pdd> us, vs;

		double sx = -dx - 1. / scale, ex = -dx + 1. / scale;
		double sy = dy - 1. / scale, ey = dy + 1. / scale;
		pdd box[] = {
			pdd(sx, sy),
			pdd(sx, ey),
			pdd(ex, ey),
			pdd(ex, sy),
		};
		pdd dir[] = {
			pdd(0, 1),
			pdd(1, 0),
			pdd(0, -1),
			pdd(-1, 0)};
		auto f = [](pdd a, pdd b, pdd u, pdd v)
		{
			if (fabs(v / b) < 1e-9)
				return 1e18;
			return (((a - u) / b) / (v / b));
		};
		for (int i = 0; i < edge.size(); i++)
		{
			pdd d = r90(input[area[i].second] - input[area[i].first]), u, v;
			pdd m = 0.5 * (input[area[i].second] + input[area[i].first]);
			auto g = [&](pdd x)
			{ return sx - 1e-9 <= x.first && x.first <= ex + 1e-9 &&
					 sy - 1e-9 <= x.second && x.second <= ey + 1e-9; };
			if (edge[i] == pii(-1, -1))
			{
				double mn = 1e18, mx = -1e18;
				for (int i = 0; i < 4; i++)
				{
					double x = f(box[i], dir[i], m, d);
					if (x == 1e18)
						continue;
					pdd tp = m + x * d;
					if (!g(tp))
						continue;
					mn = std::min(mn, x);
					mx = std::max(mx, x);
				}
				if (mn != 1e18)
					u = m + mn * d, v = m + mx * d;
				else
					continue;
			}
			else if (edge[i].first == -1)
			{
				v = vertex[edge[i].second];
				double mn = 1e18, mx = -1e18;
				if (g(v))
					mx = 0;
				for (int i = 0; i < 4; i++)
				{
					double x = f(box[i], dir[i], v, d);
					if (x == 1e18)
						continue;
					pdd tp = v + x * d;
					if (x >= 0 || !g(tp))
						continue;
					mn = std::min(mn, x);
					mx = std::max(mx, x);
				}
				if (mn == 1e18)
					continue;
				u = v + mn * d;
				v = v + mx * d;
			}
			else if (edge[i].second == -1)
			{
				u = vertex[edge[i].first];
				double mn = 1e18, mx = -1e18;
				if (g(u))
					mn = 0;
				for (int i = 0; i < 4; i++)
				{
					double x = f(box[i], dir[i], u, d);
					if (x == 1e18)
						continue;
					pdd tp = u + x * d;
					if (x <= 0 || !g(tp))
						continue;
					mn = std::min(mn, x);
					mx = std::max(mx, x);
				}
				if (mx == -1e18)
					continue;
				v = u + mx * d;
				u = u + mn * d;
			}
			else
			{
				u = vertex[edge[i].first];
				v = vertex[edge[i].second];
			}

			us.push_back(u);
			vs.push_back(v);
		}

		return make_pair(us, vs);
	}

	pair<vector<pdd>, vector<pdd>> calcvor(vector<pdd> input)
	{
		vector<pdd> vertex;
		vector<pii> edge;
		vector<pii> area;
		VoronoiDiagram(input, vertex, edge, area);
		return display(
			input, vertex, edge, area);
	}

	int vor(double *inputPtr, int inputLen, double *outputPtr)
	{
		vector<pdd> input;
		for (int i = 0; i < inputLen; i += 2)
		{
			input.emplace_back(inputPtr[i], inputPtr[i + 1]);
		}

		// Call the calculateVoronoi function
		auto result = calcvor(input);

		// Store vertex points in output
		int index = 0;
		for (const auto &p : result.first)
		{
			outputPtr[index++] = p.first;
			outputPtr[index++] = p.second;
		}

		// Store edge points in output
		for (const auto &p : result.second)
		{
			outputPtr[index++] = p.first;
			outputPtr[index++] = p.second;
		}

		// return the length of the output array
		return index;
	}

	int chull(double *inputPtr, int inputLen, double *outputPtr)
	{
		vector<Point> points;
		for (int i = 0; i < inputLen; i += 2)
		{
			points.push_back({static_cast<double>(inputPtr[i]), static_cast<double>(inputPtr[i + 1])});
		}

		auto hull = convexHull(points.data(), points.size());

		int index = 0;
		for (const auto &p : hull)
		{
			outputPtr[index++] = p.first;
			outputPtr[index++] = p.second;
		}

		return index;
	}
}

int main()
{
	vector<pdd> input;
	input.push_back(pdd(-162, 73));
	input.push_back(pdd(126, -80));

	auto [us, vs] = calcvor(input);

	Point points[] = {{0, 3}, {1, 1}, {2, 2}, {4, 4}, {0, 0}, {1, 2}, {3, 1}, {3, 3}};
	int n = sizeof(points) / sizeof(points[0]);
	vector<pdd> hull = convexHull(points, n);
	for (auto p : hull)
	{
		cout << "(" << p.first << ", " << p.second << ")" << endl;
	}
	return 0;
}
