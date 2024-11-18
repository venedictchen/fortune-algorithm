#include <bits/stdc++.h>

using namespace std;

#define mp make_pair
#define fr first
#define sc second

const int MXN = 1e6;		  // Max number of input points
const long double MXXY = 1e9; // Max possible point coordinates
const long double EPS = 1e-9; // Floating point tolerance
const long double INF = 1e18; // Infinity

// Point struct
struct Point
{
	long double x, y;

	// Euclidean distance to (0)
	inline long double dis2()
	{
		return x * x + y * y;
	}
	inline long double dis()
	{
		return sqrt(dis2());
	}

	Point operator+(const Point &pt) const
	{
		return {x + pt.x, y + pt.y};
	}
	Point operator-(const Point &pt) const
	{
		return {x - pt.x, y - pt.y};
	}
	Point operator*(const long double &w) const
	{
		return {x * w, y * w};
	}
	Point operator/(const long double &w) const
	{
		return {x / w, y / w};
	}

	bool operator<(const Point &pt) const
	{
		return mp(x, y) < mp(pt.x, pt.y);
	}
};

// Cross product of two points
inline long double crossProduct(Point p1, Point p2)
{
	return p1.x * p2.y - p1.y * p2.x;
}

// Check if three points are collinear
inline bool collinear(Point p1, Point p2, Point p3)
{
	return abs(crossProduct(p2 - p1, p3 - p2)) <= EPS;
}

// Get circumcenter of three points - this will be a Voronoi vertex
inline Point circumcenter(Point p1, Point p2, Point p3)
{
	Point d1 = p2 - p1;
	Point d2 = p3 - p1;

	Point w = d2 * d1.dis2() - d1 * d2.dis2();
	Point wRot = {-w.y, w.x};

	long double denom = crossProduct(d2, d1) * 2;
	return p1 + wRot / denom;
}

// Current y coordinate of sweep line
long double sweepY = MXXY;

// Arc struct representing a piece of the beachline
struct Arc
{
	Point p = {INF, INF}, q = {INF, INF}; // Focus point and next focus point
	int id = -1, removalId = -1;		  // Site ID and removal event ID

	inline long double getX(long double curY) const
	{
		if (q.x >= INF / 2)
			return q.x;

		curY -= EPS;
		Point mid = (p + q) / 2;
		Point d = mid - p;

		long double w = sqrt((p.y - curY) * (q.y - curY));
		return mid.x + (w * d.dis() - (mid.y - curY) * d.x) / d.y;
	}

	bool operator<(const Arc &arc) const
	{
		return getX(sweepY) < arc.getX(sweepY);
	}

	bool operator<(const long double &x) const
	{
		return getX(sweepY) < x;
	}
};

// AVL tree struct
struct AVLTree
{
	int height = 0;	  // Height of its subtree
	int big = -1;	  // The child with the maximum height, -1 if it has no child
	Arc arc;		  // Arc stored (each leaf stores an arc, each non-leaf stores minimum active arc in the subtree for binary search)
	AVLTree *c[2];	  // Children, 0 is left, 1 is right
	AVLTree *par = 0; // Parent

	// Assign values from children's values
	void assign()
	{
		height = max(c[0]->height, c[1]->height) + 1;
		big = c[0]->height + 1 == height ? 0 : 1;
		arc = min(c[0]->arc, c[1]->arc);
	}

	// Subtree rotation, right rotate if dir = 0, left rotate if dir = 1
	void rot(int dir)
	{
		AVLTree *tmp = c[!dir];

		// Make a new node in the direction of the rotation
		c[!dir] = new AVLTree;
		c[!dir]->par = this;

		// Assign children to the new node
		c[!dir]->c[dir] = c[dir]->c[!dir];
		c[!dir]->c[dir]->par = c[!dir];
		c[!dir]->c[!dir] = tmp;
		tmp->par = c[!dir];

		c[!dir]->assign();

		// Finish the opposite direction
		c[dir] = c[dir]->c[dir];
		c[dir]->par = this;

		assign();
	}

	// Check if it's unbalanced
	void check()
	{
		assign();

		if (abs(c[0]->height - c[1]->height) > 1)
		{
			// Rotate big child if big's big child isn't in the same direction
			if (c[big]->big != big)
			{
				c[big]->rot(!big);
			}

			rot(big);
		}
	}

	// Initialize the AVL tree by making it a complete binary tree with two leaves that are inactive
	// This eliminates any corner case in insertion
	void init()
	{
		for (int ii = 0; ii < 2; ii++)
		{
			c[ii] = new AVLTree;
			c[ii]->par = this;
		}

		assign();
	}

	// Insert a leaf with arc
	// Returns the address of the new leaf
	AVLTree *ins(Arc curArc)
	{
		// Get which target child to recurse into and change x accordingly
		int e = curArc < c[1]->arc ? 0 : 1;

		// Insert new leaf if the target child is a leaf
		AVLTree *ret;
		if (c[e]->height == 0)
		{
			AVLTree *tmp = c[e];
			int e2 = curArc < c[e]->arc ? 0 : 1;

			// Make a new node in place of the target child
			c[e] = new AVLTree;
			c[e]->par = this;

			// Assign the existing leaf as one child
			c[e]->c[!e2] = tmp;
			tmp->par = c[e];

			// Assign a new leaf as the other child
			c[e]->c[e2] = new AVLTree;
			c[e]->c[e2]->arc = curArc;
			c[e]->c[e2]->par = c[e];

			c[e]->assign();

			ret = c[e]->c[e2];
		}
		else
		{
			ret = c[e]->ins(curArc);
		}

		check();

		return ret;
	}

	// Binary search on AVL tree to find the arc with the maximum intersection x coordinate smaller than an arbitrary x
	AVLTree *binLift(long double x)
	{
		if (height == 0)
		{
			return this;
		}
		else
		{
			// Get which target child to recurse into
			int e = c[1]->arc < x ? 1 : 0;

			return c[e]->binLift(x);
		}
	}

	AVLTree *begin()
	{
		if (height == 0)
		{
			return this;
		}
		else
		{
			int e = c[0]->arc.getX(sweepY) != INF ? 0 : 1;
			return c[e]->begin();
		}
	}
};

// Get previous active leaf
inline AVLTree *prv(AVLTree *it)
{
	// Iterate up to lowest relevant ancestor
	while (true)
	{
		if (!it->par)
		{
			return 0;
		}

		AVLTree *lastIt = it;
		it = it->par;
		if (it->c[0] != lastIt && it->c[0]->arc.getX(sweepY) != INF)
		{
			it = it->c[0];
			break;
		}
	}

	// Iterate down to rightmost active leaf
	while (it->height > 0)
	{
		int e = it->c[1]->arc.getX(sweepY) != INF ? 1 : 0;
		it = it->c[e];
	}

	return it;
}

// Get next active leaf
inline AVLTree *nxt(AVLTree *it)
{
	// Iterate up to lowest relevant ancestor
	while (true)
	{
		if (!it->par)
		{
			return 0;
		}

		AVLTree *lastIt = it;
		it = it->par;
		if (it->c[1] != lastIt && it->c[1]->arc.getX(sweepY) != INF)
		{
			it = it->c[1];
			break;
		}
	}

	// Iterate down to leftmost active leaf
	while (it->height > 0)
	{
		int e = it->c[0]->arc.getX(sweepY) != INF ? 0 : 1;
		it = it->c[e];
	}

	return it;
}

// Erase the leaf for some arc by making it inactive
inline void ers(AVLTree *it)
{
	it->arc = {{INF, INF}, {INF, INF}, -1};

	while (it->par)
	{
		it = it->par;
		it->assign();
	}
}

// Input points
Point pts[MXN + 69];

// Add Delaunay edge
inline void addEdge(int p1, int p2)
{
	if (p1 != -1 && p2 != -1)
	{
		printf("%.5Lf %.5Lf %.5Lf %.5Lf\n", pts[p1].x, pts[p1].y, pts[p2].x, pts[p2].y);
	}
}

// Input points
Point pts[MXN + 69];

// Store Voronoi edges
vector<pair<Point, Point>> voronoiEdges;

// Add Voronoi edge between circumcenters
inline void addVoronoiEdge(Point center1, Point center2)
{
	if (center1.x != INF && center1.y != INF &&
		center2.x != INF && center2.y != INF)
	{
		voronoiEdges.push_back({center1, center2});
	}
}

// Priority queue for events
priority_queue<pair<long double, pair<int, int>>> pq;
vector<AVLTree *> removals;
vector<bool> isValidRemoval;

// Update removal events and track Voronoi vertices
inline void updRemovals(AVLTree *it)
{
	if (it->arc.id == -1)
		return;

	if (it->arc.removalId != -1)
	{
		isValidRemoval[it->arc.removalId] = false;
	}

	AVLTree *it2 = prv(it);
	if (collinear(it2->arc.p, it->arc.p, it->arc.q))
		return;

	it->arc.removalId = removals.size();
	Point voronoiVertex = circumcenter(it2->arc.p, it->arc.p, it->arc.q);

	// Store this vertex - it's where three Voronoi regions meet
	long double nextY = voronoiVertex.y - (voronoiVertex - it->arc.p).dis();
	if (nextY < sweepY + EPS && it2->arc.getX(nextY) + EPS > it->arc.getX(nextY))
	{
		pq.push({nextY, {1, it->arc.removalId}});
	}
	removals.push_back(it);
	isValidRemoval.push_back(true);
}

int main()
{
	int N;
	scanf("%d", &N);

	for (int i = 1; i <= N; i++)
	{
		scanf("%Lf%Lf", &pts[i].x, &pts[i].y);
	}

	// Initialize events with site points
	for (int i = 1; i <= N; i++)
	{
		pq.push({pts[i].y, {0, i}});
	}

	// Initialize beachline
	AVLTree avl;
	avl.init();
	avl.ins({{-MXXY, MXXY + 1}, {MXXY, MXXY}, -1, -1});
	avl.ins({{MXXY, MXXY}, {INF / 2, INF / 2}, -1, -1});

	map<pair<int, int>, Point> circumcenters; // Store circumcenters for Voronoi vertices

	while (!pq.empty())
	{
		int type, k;
		sweepY = pq.top().fr;
		type = pq.top().sc.fr;
		k = pq.top().sc.sc;
		pq.pop();

		if (type == 0)
		{ // Site event
			AVLTree *it = nxt(avl.binLift(pts[k].x));
			AVLTree *it2 = avl.ins({it->arc.p, pts[k], it->arc.id});
			AVLTree *it3 = avl.ins({pts[k], it->arc.p, k});

			// Calculate and store circumcenter
			Point center = circumcenter(it->arc.p, pts[k], it->arc.q);
			circumcenters[mp(min(it->arc.id, k), max(it->arc.id, k))] = center;

			updRemovals(it);
			updRemovals(it2);
			updRemovals(it3);
		}
		else
		{ // Circle event
			if (!isValidRemoval[k])
				continue;

			AVLTree *it = removals[k];
			AVLTree *it2 = prv(it);
			AVLTree *it3 = nxt(it);

			// This circle event creates a Voronoi vertex
			Point voronoiVertex = circumcenter(it2->arc.p, it->arc.p, it3->arc.p);

			// Add Voronoi edges connecting this vertex
			Point center1 = circumcenters[mp(min(it2->arc.id, it->arc.id),
											 max(it2->arc.id, it->arc.id))];
			Point center2 = circumcenters[mp(min(it->arc.id, it3->arc.id),
											 max(it->arc.id, it3->arc.id))];

			addVoronoiEdge(voronoiVertex, center1);
			addVoronoiEdge(voronoiVertex, center2);

			ers(it);
			it2->arc.q = it3->arc.p;

			// Update circumcenter for new edge
			circumcenters[mp(min(it2->arc.id, it3->arc.id),
							 max(it2->arc.id, it3->arc.id))] = voronoiVertex;

			updRemovals(it2);
			updRemovals(it3);
		}
	}

	// Output Voronoi edges
	printf("%d\n", (int)voronoiEdges.size());
	for (const auto &edge : voronoiEdges)
	{
		printf("%.5Lf %.5Lf %.5Lf %.5Lf\n",
			   edge.first.x, edge.first.y,
			   edge.second.x, edge.second.y);
	}

	return 0;
}