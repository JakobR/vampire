/**
 * @file ClauseQueue.hpp
 * Defines class ClauseQueue.
 *
 * @since 30/12/2007 Manchester
 */

#ifndef __ClauseQueue__
#define __ClauseQueue__

#define MAX_HEIGHT 31

#if VDEBUG
#include <ostream>
using namespace std;
#endif

#include "../Debug/Assertion.hpp"

namespace Kernel {

class Clause;

/**
 * A clause queue organised as a skip list. The comparison of elements
 * is made using the virtual function compare.
 * @since 30/12/2007 Manchester
 */
class ClauseQueue
{
public:
  ClauseQueue()
    : _height(0)
  {
    _left.nodes[0] = 0;
  }
  virtual ~ClauseQueue();
  void insert(Clause*);
  bool remove(Clause*);
  void removeAll();
  Clause* pop();
  /** True if the queue is empty */
  bool isEmpty() const
  { return _left.nodes[0] == 0; }
#if VDEBUG
  void output(ostream&) const;
#endif

  friend class Iterator;
protected:
  /** comparison of clauses */
  virtual bool lessThan(Clause*,Clause*) = 0;
  /** Nodes in the skip list */
  class Node {
  public:
    /** Clause at this node */
    Clause* clause;
    /** Links to other nodes on the right, can be of any length */
    Node* nodes[1];
  };
  /** This class is just to have the leftmost dummy node of sufficient
   * size */
  class LargeNode
    : public Node
  {
  private:
    Node* _[MAX_HEIGHT];
  };
  /** Height of the leftmost node minus 1 */
  unsigned _height;
  /** the leftmost node with the dummy key and value */
  LargeNode _left;

public:
  /** Iterator over the queue
   * @since 04/01/2008 flight Manchester-Murcia
   */
  class Iterator {
  public:
    /** Create a new iterator */
    inline explicit Iterator(ClauseQueue& queue)
      : _current(&queue._left)
    {}
    /** true if there is a next clause */
    inline bool hasNext() const
    { return _current->nodes[0]; }
    /** return the next clause */
    inline Clause* next()
    {
      _current = _current->nodes[0];
      ASS(_current);
      return _current->clause;
    }
  private:
    /** Current node */
    Node* _current;
  }; // class ClauseQueue::Iterator

//  class DelIterator {
//  public:
//    explicit DelIterator(ClauseQueue& queue)
//    { }
//
//    bool hasNext()
//    { }
//
//    Clause* next()
//    { }
//
//    void del()
//    { }
//  private:
//  };
}; // class ClauseQueue

} // namespace Kernel

#endif
