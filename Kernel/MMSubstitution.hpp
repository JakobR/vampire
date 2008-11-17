/**
 * @file MMSubstitution.hpp
 * Defines class MMSubstitution.
 *
 */

#ifndef __MMSubstitution__
#define __MMSubstitution__

#include "../Lib/DHMap.hpp"
#include "../Lib/BacktrackData.hpp"
#include "Term.hpp"

#ifdef VDEBUG

#include <string>

#endif

namespace Kernel
{

using namespace Lib;

class MMSubstitution
:public Backtrackable
{
public:
  MMSubstitution() : _nextUnboundAvailable(0),_nextAuxAvailable(0) {}
  
  bool unify(TermList t1,int index1, TermList t2, int index2)
  {
    TermSpec ct=associate(TermSpec(t1,index1), TermSpec(t2,index2));
    return !ct.term.isEmpty();
  }
  bool isUnbound(unsigned var, int index)
  {
    return isUnbound(VarSpec(var,index));
  }
  bool isSpecialUnbound(unsigned var, int index)
  {
    return isUnbound(VarSpec(var,SPECIAL_INDEX));
  }
  void bindSpecialVar(unsigned var, TermList t, int index)
  {
    VarSpec vs(var, SPECIAL_INDEX);
    ASS(!_bank.find(vs));
    bind(vs, TermSpec(t,index));
  }
  TermList getSpecialVarTop(unsigned var)
  {
    return deref(VarSpec(var, SPECIAL_INDEX)).term;
  }
  TermList apply(TermList t, int index);
  
#ifdef VDEBUG
  std::string toString();
#endif
  
private:
  static const int AUX_INDEX=-3;
  static const int SPECIAL_INDEX=-2;
  static const int UNBOUND_INDEX=-1;
  
  struct TermSpec
  {
    /** Create a new VarSpec struct */
    TermSpec() {}
    /** Create a new VarSpec struct */
    TermSpec(TermList term, int index) : term(term), index(index) {}

    /** term reference */
    TermList term;
    /** index of term to which it is bound */
    int index;
  };
  /** Specifies instance of a variable (i.e. (variable, variable bank) pair) */
  struct VarSpec
  {
    /** Create a new VarSpec struct */
    VarSpec() {}
    /** Create a new VarSpec struct */
    VarSpec(unsigned var, int index) : var(var), index(index) {}

    bool operator==(const VarSpec& o) 
    { return var==o.var && index==o.index; }
    bool operator!=(const VarSpec& o) 
    { return !(*this==o); }

    /** number of variable */
    unsigned var;
    /** index of variable bank */
    int index;
    
    /** class containing first hash function for DHMap object storing variable banks */
    class Hash1
    {
    public:
      static unsigned hash(VarSpec& o, int capacity);
    };
    /** class containing second hash function for DHMap object storing variable banks */
    class Hash2
    {
    public:
      static unsigned hash(VarSpec& o);
    };
  };

  bool isUnbound(VarSpec v);
  TermSpec deref(VarSpec v);
  
  void bind(const VarSpec& v, const TermSpec& b);
  void bindVar(const VarSpec& var, const VarSpec& to);
  VarSpec root(VarSpec v);
  void add(VarSpec v, TermSpec b);
  TermSpec associate(TermSpec t1, TermSpec t2);
  bool makeEqual(VarSpec v1, VarSpec v2);

  VarSpec getAuxVar(VarSpec target)
  {
    CALL("MMSubstitution::getAuxVar");
    VarSpec res(_nextAuxAvailable++,AUX_INDEX);
    bindVar(res, target);
    return res; 
  }
  VarSpec getVarSpec(TermSpec ts)
  {
    return getVarSpec(ts.term, ts.index);
  }
  VarSpec getVarSpec(TermList tl, int index)
  {
    CALL("MMSubstitution::getVarSpec");
    ASS(tl.isVar());
    if(tl.isSpecialVar()) {
      return VarSpec(tl.var(), SPECIAL_INDEX);
    } else {
      return VarSpec(tl.var(), index);
    }
  }
  
  typedef DHMap<VarSpec,TermSpec,VarSpec::Hash1, VarSpec::Hash2> BankType; 
  
  BankType _bank;
  
  unsigned _nextUnboundAvailable;
  unsigned _nextAuxAvailable;
  
  class BindingBacktrackObject
  : public BacktrackObject
  {
  public:
    BindingBacktrackObject(MMSubstitution* subst, VarSpec v)
    :_subst(subst), _var(v) 
    {
      if(! _subst->_bank.find(_var,_term)) {
	_term.term.makeEmpty();
      }
    }
    void backtrack()
    {
      if(_term.term.isEmpty()) {
	_subst->_bank.remove(_var);
      } else {
	_subst->_bank.set(_var,_term);
      }
    }
  private:
    MMSubstitution* _subst;
    VarSpec _var;
    TermSpec _term;
  };
};

};


namespace Lib 
{
/**
 * Traits structure specialisation. (See DHMap.hpp) 
 */
template<>
struct HashTraits<Kernel::MMSubstitution::VarSpec::Hash1>
{
  enum {SINGLE_PARAM_HASH=0};
};
};

#endif /*__MMSubstitution__*/
