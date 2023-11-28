/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file RobSubstitution.hpp
 * Defines class RobSubstitution.
 *
 */

#ifndef __RobSubstitution__
#define __RobSubstitution__

#include "Forwards.hpp"
#include "Kernel/Polynomial.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/Recycled.hpp"
#include "Term.hpp"
#include "Lib/Hash.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/TypedTermList.hpp"

#if VDEBUG
#include <iostream>
#include "Lib/VString.hpp"
#endif


const int GLUE_INDEX=-3;
const int SPECIAL_INDEX=-2;
const int UNBOUND_INDEX=-1;
namespace Kernel
{
struct VarSpec
{
  /** Create a new VarSpec struct */
  VarSpec() {}
  /** Create a new VarSpec struct */
  VarSpec(unsigned var, int index) : var(var), index(index) {}

  friend std::ostream& operator<<(std::ostream& out, VarSpec const& self);

  /** number of variable */
  unsigned var;
  /** index of variable bank */
  int index;

  auto asTuple() const { return std::tie(var, index); }
  IMPL_COMPARISONS_FROM_TUPLE(VarSpec)
  IMPL_HASH_FROM_TUPLE(VarSpec)

  /** struct containing first hash function for DHMap object storing variable banks */
  struct Hash1
  {
   static unsigned hash(VarSpec const& o) {
     return HashUtils::combine(o.var, o.index);
   }
  };
  /** struct containing second hash function for DHMap object storing variable banks */
  struct Hash2
  {
    static unsigned hash(VarSpec const& o) {
      return HashUtils::combine(o.index, o.var);
    }
  };
};

struct TermSpec {
  TermSpec() {}
  TermSpec(TermList t, int i) : term(t), index(i) {}
  TermSpec(VarSpec v) : term(TermList::var(v.var)), index(v.index) {}
  auto asTuple() const -> decltype(auto) { return std::tie(term, index); }
  IMPL_COMPARISONS_FROM_TUPLE(TermSpec)
  IMPL_HASH_FROM_TUPLE(TermSpec)

  TermList term;
  int index;

  bool sameTermContent(const TermSpec& ts)
  {
    bool termSameContent=term.sameContent(&ts.term);
    if(!termSameContent && term.isTerm() && term.term()->isLiteral() &&
      ts.term.isTerm() && ts.term.term()->isLiteral()) {
      const Literal* l1=static_cast<const Literal*>(term.term());
      const Literal* l2=static_cast<const Literal*>(ts.term.term());
      if(l1->functor()==l2->functor() && l1->arity()==0) {
        return true;
      }
    }
    if(!termSameContent) {
      return false;
    }
    return index==ts.index || term.isSpecialVar() ||
      (term.isTerm() && (
  (term.term()->shared() && term.term()->ground()) ||
   term.term()->arity()==0 ));
  }

  friend std::ostream& operator<<(std::ostream& out, TermSpec const& self);
  TermSpec clone() const { return *this; }
  bool isVar() const { return term.isVar(); }
  VarSpec varSpec() const { return VarSpec(term.var(), term.isSpecialVar() ? SPECIAL_INDEX : index); }
  bool isTerm() const { return term.isTerm(); }

  unsigned nTypeArgs() const { return term.term()->numTermArguments(); }
  unsigned nTermArgs() const { return term.term()->numTermArguments(); }
  unsigned nAllArgs() const { return term.term()->arity(); }

  TermSpec termArg(unsigned i) const { return TermSpec(this->term.term()->termArg(i), this->index); }
  TermSpec typeArg(unsigned i) const { return TermSpec(this->term.term()->typeArg(i), this->index); }
  TermSpec anyArg (unsigned i) const { return TermSpec(*this->term.term()->nthArgument(i), this->index); }

  auto typeArgs() const { return range(0, nTypeArgs()).map([this](auto i) { return typeArg(i); }); }
  auto termArgs() const { return range(0, nTermArgs()).map([this](auto i) { return termArg(i); }); }
  auto allArgs()  const { return range(0, nAllArgs()).map([this](auto i) { return anyArg(i); }); }

  TermList toTerm(Kernel::RobSubstitution& s) const;

  bool isSort() const
  { return this->term.term()->isSort(); }

  bool sortIsBoolOrVar() const;

  TermList::Top top() const { return this->term.top(); }

  unsigned functor() const { return term.term()->functor(); }

  bool isNumeral() const { return theory->isInterpretedNumber(this->term); }

  bool definitelyGround() const 
  { return this->term.isTerm() 
        && this->term.term()->shared() 
        && this->term.term()->ground(); }

  unsigned groundWeight() const 
  {
    ASS(definitelyGround())
    return this->term.weight();
  }

  bool isSpecialVar() const { return this->term.isSpecialVar(); }

  template<class Deref>
  static int compare(TermSpec const& lhs, TermSpec const& rhs, Deref deref) {
    Recycled<Stack<std::pair<TermSpec, TermSpec>>> todo;
    todo->push(std::make_pair(lhs.clone(),rhs.clone()));
    // DBG("compare: ", lhs, " <> ", rhs)
    while (todo->isNonEmpty()) {
      auto lhs_ = std::move(todo->top().first);
      auto rhs_ =           todo->pop().second;
      auto& lhs = deref(lhs_);
      auto& rhs = deref(rhs_);

      if (lhs.isTerm() != rhs.isTerm()) {
        return lhs.isVar() ? -1 : 1;

      } else {
        if (lhs.isTerm()) {
          if (lhs.functor() != rhs.functor()) {
            return lhs.functor() < rhs.functor() ? -1 : 1;
          } else {
            todo->loadFromIterator(lhs.allArgs().zip(rhs.allArgs()));
          }
        } else {
          ASS(lhs.isVar() && rhs.isVar())
          auto v1 = lhs.varSpec();
          auto v2 = rhs.varSpec();
          if (v1 != v2) {
            return std::tie(v1.var, v1.index) < std::tie(v2.var, v2.index) ? -1 : 1;
          }
        }
      }
    }
    return 0;
  }
};

struct AutoDerefTermSpec
{
  TermSpec term;

  AutoDerefTermSpec(TermSpec const& t, RobSubstitution const* s);
  explicit AutoDerefTermSpec(AutoDerefTermSpec const& other) : term(other.term.clone()) {}
  AutoDerefTermSpec clone() const { return AutoDerefTermSpec(*this); }
  AutoDerefTermSpec(AutoDerefTermSpec && other) = default;
  friend std::ostream& operator<<(std::ostream& out, AutoDerefTermSpec const& self);
};

struct AutoDerefTermSpecContext 
{
  RobSubstitution const* subs;
};

template<class Result, unsigned SIZE>
class OnlyMemorizeBigAtomic {
  Map<TermSpec, Result> _memo;
public:
  OnlyMemorizeBigAtomic(OnlyMemorizeBigAtomic &&) = default;
  OnlyMemorizeBigAtomic& operator=(OnlyMemorizeBigAtomic &&) = default;
  OnlyMemorizeBigAtomic() : _memo() {}

  auto memoKey(AutoDerefTermSpec const& arg) -> Option<TermSpec>
  { 
    if (arg.term.term.isTerm()) {
      auto term = arg.term.term.term();
      return !term->shared() || term->weight() > SIZE ? Option<TermSpec>(arg.term) : Option<TermSpec>{};
    } else {
      return {};
    }
  }

  Option<Result> get(AutoDerefTermSpec const& arg)
  { 
    auto key = memoKey(arg);
    return key.isSome()
       ? _memo.tryGet(*key).toOwned()
       : Option<Result>(); 
  }

  template<class Init> Result getOrInit(AutoDerefTermSpec const& orig, Init init)
  { 
    auto key = memoKey(orig);
    return key.isSome() ? _memo.getOrInit(*key, init)
                        : init(); 
  }
  void reset() { _memo.reset(); }
};


template<class Result>
class OnlyMemorizeAtomicNonVar {
  Map<TermSpec, Result> _memo;
public:
  OnlyMemorizeAtomicNonVar(OnlyMemorizeAtomicNonVar &&) = default;
  OnlyMemorizeAtomicNonVar& operator=(OnlyMemorizeAtomicNonVar &&) = default;
  OnlyMemorizeAtomicNonVar() : _memo() {}

  auto memoKey(AutoDerefTermSpec const& arg) -> Option<TermSpec>
  { 
    if (arg.term.term.isTerm()) {
      return some(arg.term);
    } else {
      return {};
    }
  }

  Option<Result> get(AutoDerefTermSpec const& arg)
  { 
    auto key = memoKey(arg);
    return key.isSome()
       ? _memo.tryGet(*key).toOwned()
       : Option<Result>(); 
  }

  template<class Init> Result getOrInit(AutoDerefTermSpec const& orig, Init init)
  { 
    auto key = memoKey(orig);
    return key.isSome() ? _memo.getOrInit(*key, init)
                        : init(); 
  }
  void reset() { _memo.reset(); }
};

// template<class Result>
// class OnlyMemorizeVars {
//   Map<VarSpec, Result> _memo;
// public:
//   OnlyMemorizeVars(OnlyMemorizeVars &&) = default;
//   OnlyMemorizeVars& operator=(OnlyMemorizeVars &&) = default;
//   OnlyMemorizeVars() : _memo() {}
//
//   Option<Result> get(AutoDerefTermSpec const& arg)
//   { return arg.term.isVar()
//        ? _memo.tryGet(arg.term.varSpec()).toOwned()
//        : Option<Result>(); }
//
//   template<class Init> Result getOrInit(AutoDerefTermSpec const& orig, Init init)
//   { return orig.term.isVar() ? _memo.getOrInit(orig.term.varSpec(), init)
//                              : init(); }
//   void reset() { _memo.reset(); }
// };
class UnificationConstraint
{
  TermSpec _t1;
  TermSpec _t2;
public:
  // TODO get rid of default constr
  UnificationConstraint() {}
  USE_ALLOCATOR(UnificationConstraint)
  // UnificationConstraint(UnificationConstraint&&) = default;
  // UnificationConstraint& operator=(UnificationConstraint&&) = default;
  auto asTuple() const -> decltype(auto) { return std::tie(_t1, _t2); }
  IMPL_COMPARISONS_FROM_TUPLE(UnificationConstraint);
  IMPL_HASH_FROM_TUPLE(UnificationConstraint);

  UnificationConstraint clone() const { return UnificationConstraint(lhs().clone(), rhs().clone()); }

  UnificationConstraint(TermSpec t1, TermSpec t2)
  : _t1(std::move(t1)), _t2(std::move(t2))
  {}

  Option<Literal*> toLiteral(RobSubstitution& s);

  TermSpec const& lhs() const { return _t1; }
  TermSpec const& rhs() const { return _t2; }

  friend std::ostream& operator<<(std::ostream& out, UnificationConstraint const& self)
  { return out << self._t1 << " != " << self._t2; }

};




using namespace Lib;

class AbstractingUnifier;
class UnificationConstraint;

class RobSubstitution
:public Backtrackable
{
  friend class AbstractingUnifier;
  friend class UnificationConstraint;
 
  DHMap<VarSpec, TermSpec, VarSpec::Hash1, VarSpec::Hash2> _bindings;
  mutable DHMap<VarSpec, unsigned , VarSpec::Hash1, VarSpec::Hash2> _outputVarBindings;
  mutable bool _startedBindingOutputVars;
  mutable unsigned _nextUnboundAvailable;
  mutable unsigned _nextGlueAvailable;
  mutable OnlyMemorizeAtomicNonVar<TermList> _applyMemo;
  // mutable OnlyMemorizeAtomic<TermList> _applyMemo;
  // mutable OnlyMemorizeBigAtomic<TermList, 4> _applyMemo;

public:
  USE_ALLOCATOR(RobSubstitution);
  
  RobSubstitution() 
    : _startedBindingOutputVars(false)
    , _nextUnboundAvailable(0) 
    , _nextGlueAvailable(0) 
  {}

  SubstIterator matches(Literal* base, int baseIndex,
	  Literal* instance, int instanceIndex, bool complementary);
  SubstIterator unifiers(Literal* l1, int l1Index, Literal* l2, int l2Index, bool complementary);

  bool unify(TermList t1,int index1, TermList t2, int index2);
  bool match(TermList base,int baseIndex, TermList instance, int instanceIndex);

  bool unifyArgs(Term* t1,int index1, Term* t2, int index2);
  bool matchArgs(Term* base,int baseIndex, Term* instance, int instanceIndex);

  void denormalize(const Renaming& normalizer, int normalIndex, int denormalizedIndex);
  bool isUnbound(VarSpec v) const;

  /** introduces a new "glue" variable, and binds it to forTerm. 
   * Glue variables live in their own namespace that is only used within this rob substitution. They are used only to represent subterms of other terms in the substitution.
   * This is useful in cases where we want to create terms that contain two subterms of different variable banks in e.g. Unification with Abstraction:
   *
   * Say we want to unify
   * x + f(y)    <- var bank 0
   * and   
   * f(y)        <- var bank 1
   *
   * Then an mgu is x -> -f(y/0) + f(y/1)
   * This cannot be represented in vampire as our TermSpec can only hold 1 variable bank per term, and not multiple per subterm. So what we want to do instead is introduce two 
   * new glue variables varibles G0, G1
   *
   * G0 -> -f(y)/0
   * G1 ->  f(y)/1
   *
   * and return as mgu
   * {x -> G0 + G1, G0 -> -f(y)/0, G1 -> f(y)/1}
   */
  VarSpec introGlueVar(TermSpec forTerm);

  void reset()
  {
    _bindings.reset();
    _outputVarBindings.reset();
    _startedBindingOutputVars = false;
    _nextUnboundAvailable=0;
    _nextGlueAvailable=0;
    _applyMemo.reset();
  }
  bool keepRecycled() const { return _bindings.keepRecycled() || _outputVarBindings.keepRecycled(); }

  /**
   * Bind special variable to a specified term
   *
   * Calls to this method must happen before calls to any
   * other methods. Also no special variables can occur in
   * binding term, as no occur-check is performed.
   */
  void bindSpecialVar(unsigned var, TermList t, int index)
  {
    VarSpec vs(var, SPECIAL_INDEX);
    ASS(!_bindings.find(vs));
    bind(vs, TermSpec(t,index));
  }

  TermList::Top getSpecialVarTop(unsigned specialVar) const;
  TermList apply(TermList t, int index) const;
  Literal* apply(Literal* lit, int index) const;
  TypedTermList apply(TypedTermList t, int index) const { return TypedTermList(apply(TermList(t), index), apply(t.sort(), index)); }
  Stack<Literal*> apply(Stack<Literal*> cl, int index) const;
  size_t getApplicationResultWeight(TermList t, int index) const;
  size_t getApplicationResultWeight(Literal* lit, int index) const;

  bool isEmpty() const { return _bindings.size() == 0 && _outputVarBindings.size() == 0; }

  friend std::ostream& operator<<(std::ostream& out, RobSubstitution const& self);
  std::ostream& output(std::ostream& out, bool deref) const;

  typedef std::pair<TermSpec,TermSpec> TTPair;
  friend std::ostream& operator<<(std::ostream& out, VarSpec const& self)
  {
    if(self.index == SPECIAL_INDEX) {
      return out << "S" << self.var;
    } else {
      return out << "X" << self.var << "/" << self.index;
    }
  }


  RobSubstitution(RobSubstitution&& obj) = default;
  RobSubstitution& operator=(RobSubstitution&& obj) = default;
  TermSpec const& derefBound(TermSpec const& v) const;
  // TermSpec const& derefIntroducingNewVariables(VarSpec v) const;
  unsigned findOrIntroduceOutputVariable(VarSpec v) const;
  VarSpec root(VarSpec v) const;
private:
  TermList apply(TermSpec);
  friend struct TermSpec;
  RobSubstitution(const RobSubstitution& obj) = delete;
  RobSubstitution& operator=(const RobSubstitution& obj) = delete;


  void addToConstraints(const VarSpec& v1, const VarSpec& v2);
  template<class T, class H1, class H2>
  void bind(DHMap<VarSpec, T, H1, H2>& map, const VarSpec& v, T b);
  void bind(const VarSpec& v, TermSpec b);
  void bindVar(const VarSpec& var, const VarSpec& to);
  bool match(TermSpec base, TermSpec instance);
  bool unify(TermSpec t1, TermSpec t2);
  bool occurs(VarSpec const& vs, TermSpec const& ts);

  friend std::ostream& operator<<(std::ostream& out, RobSubstitution const& self)
  { return out << "(" << self._bindings << ", " << self._outputVarBindings << ")"; }

  template<class Fn>
  SubstIterator getAssocIterator(RobSubstitution* subst,
    Literal* l1, int l1Index, Literal* l2, int l2Index, bool complementary);

  template<class Fn>
  struct AssocContext;
  template<class Fn>
  class AssocIterator;

  struct MatchingFn;
  struct UnificationFn;

};


inline AutoDerefTermSpec::AutoDerefTermSpec(TermSpec const& t, RobSubstitution const* s) : term(s->derefBound(t).clone()) {}
};

namespace Lib {

  // TODO optimize to use TermList iterator
  template<>
  // struct BottomUpChildIter<pair<Kernel::TermSpec, Kernel::RobSubstitution const*>>
  struct BottomUpChildIter<Kernel::AutoDerefTermSpec>
  {
    using Item = Kernel::AutoDerefTermSpec;
    Item _self;
    unsigned _arg;

    BottomUpChildIter(Item const& self, Kernel::AutoDerefTermSpecContext c) : _self(Item(self)), _arg(0) {}
 
    Item const& self() { return _self; }

    Item next(Kernel::AutoDerefTermSpecContext c)
    { return Kernel::AutoDerefTermSpec(_self.term.anyArg(_arg++), c.subs); }

    bool hasNext(Kernel::AutoDerefTermSpecContext c)
    { return _self.term.isTerm() && _arg < _self.term.nAllArgs(); }

    unsigned nChildren(Kernel::AutoDerefTermSpecContext c)
    { return _self.term.isTerm() ? _self.term.nAllArgs() : 0; }
  };

} // namespace Lib

#endif /*__RobSubstitution__*/
