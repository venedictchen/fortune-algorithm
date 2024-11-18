#include <vector>
#include <tuple>
#include <queue>
#include <cmath>
#include <algorithm>
#include <cstdio>
#include <stack>
#include <iostream>
#include <iomanip>

using namespace std;

#define mp make_pair
#define fr first
#define sc second

const int MXN = 1e6; // Max number of input points
const long double MXXY = 1e6; // Max possible point coordinates
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
	
	// Arithmetic operations for points
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
	
	// Compare points lexicographically
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

// Center of a circle going through three points
inline Point circumcenter(Point p1, Point p2, Point p3)
{
	Point d1, d2;
	d1 = p2 - p1;
	d2 = p3 - p1;
	
	Point w, wRot;
	w = d2 * d1.dis2() - d1 * d2.dis2();
	wRot = {-w.y, w.x};
	
	long double denom = crossProduct(d2, d1) * 2;
	return p1 + wRot / denom;
}

// Current y coordinate of sweep line (used in arc comparison)
long double sweepY = MXXY;

// Arc struct
struct Arc
{
	// Focus point of arc and the following arc (to the right) in the beach line
	Point p = {INF, INF}, q = {INF, INF};
	
	// ID of point and ID of removal event
	int id = -1, removalId = -1;
	
	// Source vertex of the line intersection of the two arcs from p and q
	Point v = {INF, INF};
	
	// Get the intersection of the arc and the following arc for the current sweepY
	inline long double getX(long double curSweepY) const
	{
		if(q.x >= INF / 2)
		{
			return q.x;
		}
		
		Point mid, d;
		mid = (p + q) / 2;
		d = mid - p;
		
		long double w = sqrt((p.y - curSweepY) * (q.y - curSweepY));
		return mid.x + (w * d.dis() - (mid.y - curSweepY) * d.x) / d.y;
	}
	
	inline Point getV(long double curSweepY) const
	{
		Point ret;
		ret.x = getX(curSweepY);
		if(p.y > curSweepY)
		{
			ret.y = (ret.x * ret.x - 2 * p.x * ret.x + p.x * p.x + p.y * p.y - curSweepY * curSweepY) / (2 * (p.y - curSweepY));
		}
		else
		{
			ret.y = (ret.x * ret.x - 2 * q.x * ret.x + q.x * q.x + q.y * q.y - curSweepY * curSweepY) / (2 * (q.y - curSweepY));
		}
		return ret;
	}
	
	// Initialize v (done at the time of each point or vertex event)
	inline void initV()
	{
		if(p.y >= MXXY || q.y >= MXXY)
		{
			v = {INF, INF};
		}
		else
		{
			v = getV(sweepY);
		}
	}
	
	// Compare arcs by their intersection x coordinates to the adjacent arc
	bool operator<(const Arc &arc) const
	{
		return getX(sweepY - EPS) < arc.getX(sweepY - EPS);
    }
	
	// Compare arc intersection x coordinate with arbitrary x coordinate
	bool operator<(const long double &x) const
	{
		return getX(sweepY - EPS) < x;
    }
};

// AVL tree struct
struct AVLTree
{
	int height = 0; // Height of its subtree
	int big = -1; // The child with the maximum height, -1 if it has no child
	Arc arc; // Arc stored (each leaf stores an arc, each non-leaf stores minimum active arc in the subtree for binary search)
	AVLTree *c[2]; // Children, 0 is left, 1 is right
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
		
		if(abs(c[0]->height - c[1]->height) > 1)
		{
			// Rotate big child if big's big child isn't in the same direction
			if(c[big]->big != big)
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
		for(int ii = 0; ii < 2; ii++)
		{
			c[ii] = new AVLTree;
			c[ii]->par = this;
		}
		
		assign();
	}
	
	// Insert a leaf with arc
	// Returns the address of the new leaf
	AVLTree* ins(Arc curArc)
	{
		// Get which target child to recurse into and change x accordingly
		int e = curArc < c[1]->arc ? 0 : 1;
		
		// Insert new leaf if the target child is a leaf
		AVLTree *ret;
		if(c[e]->height == 0)
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
	AVLTree* binLift(long double x)
	{
		if(height == 0)
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
	
	AVLTree* begin()
	{
		if(height == 0)
		{
			return this;
		}
		else
		{
			int e = c[0]->arc.getX(sweepY - EPS) != INF ? 0 : 1;
			return c[e]->begin();
		}
	}
};

// Get previous active leaf
inline AVLTree* prv(AVLTree *it)
{
	// Iterate up to lowest relevant ancestor
	while(true)
	{
		if(!it->par)
		{
			return 0;
		}
		
		AVLTree *lastIt = it;
		it = it->par;
		if(it->c[0] != lastIt && it->c[0]->arc.getX(sweepY - EPS) != INF)
		{
			it = it->c[0];
			break;
		}
	}
	
	// Iterate down to rightmost active leaf
	while(it->height > 0)
	{
		int e = it->c[1]->arc.getX(sweepY - EPS) != INF ? 1 : 0;
		it = it->c[e];
	}
	
	return it;
}

// Get next active leaf
inline AVLTree* nxt(AVLTree *it)
{
	// Iterate up to lowest relevant ancestor
	while(true)
	{
		if(!it->par)
		{
			return 0;
		}
		
		AVLTree *lastIt = it;
		it = it->par;
		if(it->c[1] != lastIt && it->c[1]->arc.getX(sweepY - EPS) != INF)
		{
			it = it->c[1];
			break;
		}
	}
	
	// Iterate down to leftmost active leaf
	while(it->height > 0)
	{
		int e = it->c[0]->arc.getX(sweepY - EPS) != INF ? 0 : 1;
		it = it->c[e];
	}
	
	return it;
}

// Relax ancestor values in AVL tree
inline void relax(AVLTree *it)
{
	while(it->par)
	{
		it = it->par;
		it->assign();
	}
}

// Erase the leaf for some arc by making it inactive
inline void ers(AVLTree *it)
{
	it->arc = {{INF, INF}, {INF, INF}, -1, -1};
	relax(it);
}

// Input points
Point pts[MXN + 69];
vector<pair<Point, Point>> delaunay_edges, voronoi_edges;

// Add Delaunay edge
inline void addDelaunayEdge(int p1, int p2)
{
	if(p1 != -1 && p2 != -1)
	{
		// printf("%.5Lf %.5Lf %.5Lf %.5Lf\n", pts[p1].x, pts[p1].y, pts[p2].x, pts[p2].y);
		delaunay_edges.emplace_back(pts[p1], pts[p2]);
	}
}

// Add Voronoi edge
inline void addVoronoiEdge(Point p1, Point p2)
{
	if(p1.x != INF && p2.x != INF)
	{
		// printf("%.5Lf %.5Lf %.5Lf %.5Lf\n", p1.x, p1.y, p2.x, p2.y);
		voronoi_edges.emplace_back(p1, p2);
	}
}

// Priority queue of events to handle both addition events and removal events
priority_queue<pair<long double, pair<int, int>>> pq;
vector<AVLTree*> removals;
vector<bool> isValidRemoval;

// Update removal events
inline void updRemovals(AVLTree* it)
{
	if(it->arc.id == -1)
	{
		return;
	}
	
	if(it->arc.removalId != -1)
	{
		isValidRemoval[it->arc.removalId] = false;
	}
	
	AVLTree *it2 = prv(it);
	if(collinear(it2->arc.p, it->arc.p, it->arc.q))
	{
		return;
	}
	
	it->arc.removalId = removals.size();
	Point mid = circumcenter(it2->arc.p, it->arc.p, it->arc.q);
	long double nextY = mid.y - (mid - it->arc.p).dis();
	if(nextY < sweepY + EPS && it2->arc.getX(nextY - EPS) + EPS > it->arc.getX(nextY - EPS))
	{
		pq.push({nextY, {1, it->arc.removalId}});
	}
	removals.push_back(it);
	isValidRemoval.push_back(true);
}

extern "C"
{
    void generate_voronoi_and_delaunay(int N, double *inputPtr, double *voronoiPtr, double *delaunayPtr, double *circlePtr, int *voronoiSize, int *delaunaySize)
    {
        for (int i = 1; i <= N; i++)
        {
            pts[i] = {inputPtr[2*(i-1)], inputPtr[2*(i-1) + 1]};
        }

        voronoi_edges.clear();
        delaunay_edges.clear();
		
		// Add all point events
		for(int i = 1; i <= N; i++)
		{
			pq.push({pts[i].y, {0, i}});
		}
		
		// Initialize AVL tree
		AVLTree avl;
		avl.init();
		avl.ins({{-MXXY, MXXY + 1}, {MXXY, MXXY}, -1, -1});
		avl.ins({{MXXY, MXXY}, {INF / 2, INF / 2}, -1, -1});
		
		// Process events
		long double maxRadius = -INF;
		Point circlePt;
		while(!pq.empty())
		{
			int type, k;
			sweepY = pq.top().fr;
			type = pq.top().sc.fr;
			k = pq.top().sc.sc;
			pq.pop();
			
			if(type == 0)
			{
				AVLTree *it = nxt(avl.binLift(pts[k].x));
				addDelaunayEdge(it->arc.id, k);
				
				Arc newArc = {it->arc.p, pts[k], it->arc.id};
				newArc.initV();
				AVLTree *it2 = avl.ins(newArc);
				
				newArc = {pts[k], it->arc.p, k};
				newArc.initV();
				AVLTree *it3 = avl.ins(newArc);
				
				updRemovals(it);
				updRemovals(it2);
				updRemovals(it3);
			}
			else
			{
				if(!isValidRemoval[k])
				{
					continue;
				}
				
				AVLTree *it = removals[k];
				AVLTree *it2 = prv(it);
				AVLTree *it3 = nxt(it);
				addDelaunayEdge(it2->arc.id, it3->arc.id);
				
				Point v = it->arc.getV(sweepY);
				addVoronoiEdge(it2->arc.v, v);
				addVoronoiEdge(it->arc.v, v);
				
				if(it->arc.id != -1 && it2->arc.id != -1 && it3->arc.id != -1)
				{
					long double radius = v.y - sweepY;
					if(radius > maxRadius)
					{
						maxRadius = radius;
						circlePt = v;
					}
				}
				
				ers(it);
				it2->arc.q = it3->arc.p;
				it2->arc.initV();
				relax(it2);
				
				updRemovals(it2);
				updRemovals(it3);
			}
		}
		
		// Add all unfinished half lines
		for(AVLTree *it = avl.begin(); it; it = nxt(it))
		{
			Point v = it->arc.getV(-MXXY);
			addVoronoiEdge(it->arc.v, v);
		}
		
		// Print max radius circle (x, y, r)
		{
			int index = 0;
			if(maxRadius != -INF)
			{
				circlePtr[index++] = circlePt.x;
				circlePtr[index++] = circlePt.y;
				circlePtr[index++] = maxRadius;
			} else {
				circlePtr[index++] = -1;
				circlePtr[index++] = -1;
				circlePtr[index++] = -1;
			}
		}

		// Store vertex points in output
		{
			int index = 0;
			for (const auto &p : voronoi_edges)
			{
				voronoiPtr[index++] = p.first.x;
				voronoiPtr[index++] = p.first.y;
				voronoiPtr[index++] = p.second.x;
				voronoiPtr[index++] = p.second.y;
			}

			index = 0;
			for (const auto &p : delaunay_edges)
			{
				delaunayPtr[index++] = p.first.x;
				delaunayPtr[index++] = p.first.y;
				delaunayPtr[index++] = p.second.x;
				delaunayPtr[index++] = p.second.y;
			}

			*voronoiSize = voronoi_edges.size() * 4;
			*delaunaySize = delaunay_edges.size() * 4;
		}
	}
}