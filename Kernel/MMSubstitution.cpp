/**
 * @file MMSubstitution.cpp
 * Implements Martelli and Montanari unification.
 */

#include "../Lib/Environment.hpp"

#include "../Lib/Hash.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Random.hpp"
#include "../Lib/DHMultiset.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/SkipList.hpp"
#include "../Lib/Int.hpp"

#include "Term.hpp"
#include "Clause.hpp"
#include "Renaming.hpp"

#include "../Indexing/TermSharing.hpp"

#include "MMSubstitution.hpp"

#if VDEBUG
#include "../Test/Output.hpp"
#include "../Lib/Int.hpp"
#include "../Debug/Tracer.hpp"
#include <string>
#include <iostream>
using namespace Debug;
#endif

namespace Kernel
{

using namespace std;
using namespace Lib;

const int MMSubstitution::AUX_INDEX=-3;
const int MMSubstitution::SPECIAL_INDEX=-2;
const int MMSubstitution::UNBOUND_INDEX=-1;

/**
 * Unify @b t1 and @b t2, and return true iff it was successful.
 */
bool MMSubstitution::unify(TermList t1,int index1, TermList t2, int index2)
{
  CALL("MMSubstitution::unify/4");
  return unify(TermSpec(t1,index1), TermSpec(t2,index2));
}

/**
 * Unify arguments of @b t1 and @b t2, and return true iff it was successful.
 *
 * @b t1 and @b t2 can be either terms or literals.
 */
bool MMSubstitution::unifyArgs(Term* t1,int index1, Term* t2, int index2)
{
  CALL("MMSubstitution::unifyArgs");
  ASS_EQ(t1->functor(),t2->functor());

  TermList t1TL(t1);
  TermList t2TL(t2);
  return unify(TermSpec(t1TL,index1), TermSpec(t2TL,index2));
}

bool MMSubstitution::match(TermList base,int baseIndex,
	TermList instance, int instanceIndex)
{
  CALL("MMSubstitution::match(TermList...)");
  return match(TermSpec(base,baseIndex), TermSpec(instance,instanceIndex));
}
/**
 * Match arguments of @b t1 and @b t2, and return true iff it was successful.
 *
 * @b t1 and @b t2 can be either terms or literals.
 */
bool MMSubstitution::matchArgs(Term* base,int baseIndex,
	Term* instance, int instanceIndex)
{
  CALL("MMSubstitution::match(Literal*...)");
  ASS_EQ(base->functor(),instance->functor());

  TermList baseTL(base);
  TermList instanceTL(instance);
  return match(TermSpec(baseTL,baseIndex), TermSpec(instanceTL,instanceIndex));
}

/**
 * Bind variables from @b denormalizedIndex to variables in @b normalIndex
 * in a way, that applying the substitution to a term in @b denormalizedIndex
 * would give the same result as first renaming variables and then applying
 * the substitution in @b normalIndex.
 *
 * @warning All variables, that occured in some term that was matched or unified
 * in @b normalIndex, must be also present in the @b normalizer.
 */
void MMSubstitution::denormalize(const Renaming& normalizer, int normalIndex, int denormalizedIndex)
{
  CALL("MMSubstitution::denormalize");
  ASSERT_VALID(normalizer);

  VirtualIterator<Renaming::Item> nit=normalizer.items();
  while(nit.hasNext()) {
    Renaming::Item itm=nit.next();
    VarSpec normal(itm.second, normalIndex);
    VarSpec denormalized(itm.first, denormalizedIndex);
    ASS(!_bank.find(denormalized));
    bindVar(denormalized,normal);
  }
}

bool MMSubstitution::isUnbound(VarSpec v) const
{
  CALL("MMSubstitution::isUnbound");
  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found || binding.index==UNBOUND_INDEX) {
      return true;
    } else if(binding.term.isTerm()) {
      return false;
    }
    v=getVarSpec(binding);
  }
}

/**
 * If special variable @b specialVar is bound to a proper term,
 * return a term, thjat has the same top functor. Otherwise
 * return an arbitrary variable.
 */
TermList MMSubstitution::getSpecialVarTop(unsigned specialVar)
{
  VarSpec v(specialVar, SPECIAL_INDEX);
  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found || binding.index==UNBOUND_INDEX) {
      static TermList auxVarTerm(1,false);
      return auxVarTerm;
    } else if(binding.term.isTerm()) {
      return binding.term;
    }
    v=getVarSpec(binding);
  }
}

/**
 * If @b t is a non-variable, return @t. Else, if @b t is a variable bound to
 * a non-variable term, return the term. Otherwise, return the root variable
 * to which @b t belongs.
 */
MMSubstitution::TermSpec MMSubstitution::derefBound(TermSpec t) const
{
  CALL("MMSubstitution::derefBound");
  if(t.term.isTerm()) {
    return t;
  }
  VarSpec v=getVarSpec(t);
  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found || binding.index==UNBOUND_INDEX) {
      return TermSpec(v);
    } else if(binding.term.isTerm()) {
      return binding;
    }
    v=getVarSpec(binding);
  }
}

MMSubstitution::TermSpec MMSubstitution::deref(VarSpec v) const
{
  CALL("MMSubstitution::deref");
  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found) {
      binding.index=UNBOUND_INDEX;
      binding.term.makeVar(_nextUnboundAvailable++);
      const_cast<MMSubstitution&>(*this).bind(v,binding);
      return binding;
    } else if(binding.index==UNBOUND_INDEX || binding.term.isTerm()) {
      return binding;
    }
    v=getVarSpec(binding);
  }
}

void MMSubstitution::bind(const VarSpec& v, const TermSpec& b)
{
  CALL("MMSubstitution::bind");
  ASSERT_VALID(b.term);
  //Aux terms don't contain special variables, ergo
  //should be shared.
  ASS(!b.term.isTerm() || b.index!=AUX_INDEX || b.term.term()->shared());
  ASS_NEQ(v.index, UNBOUND_INDEX);

  if(bdIsRecording()) {
    bdAdd(new BindingBacktrackObject(this, v));
  }
  _bank.set(v,b);
}

void MMSubstitution::bindVar(const VarSpec& var, const VarSpec& to)
{
  CALL("MMSubstitution::bindVar");
  ASS_NEQ(var,to);

  bind(var,TermSpec(to));
}

MMSubstitution::VarSpec MMSubstitution::root(VarSpec v)
{
  CALL("MMSubstitution::root");
  static Stack<VarSpec> encountered(32);
  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found || binding.index==UNBOUND_INDEX || binding.term.isTerm()) {
      if(encountered.isNonEmpty()) {
	encountered.pop();
	while(encountered.isNonEmpty()) {
	  bind(encountered.pop(), TermSpec(v));
	}
      }
      return v;
    }
//    encountered.push(v);
    v=getVarSpec(binding);
  }
}

void MMSubstitution::makeEqual(VarSpec v1, VarSpec v2, TermSpec target)
{
  CALL("MMSubstitution::makeEqual");

  v1=root(v1);
  v2=root(v2);
  if(v1==v2) {
    bind(v2,target);
    return;
  }
  if(Random::getBit()) {
    bindVar(v1,v2);
    bind(v2,target);
  } else {
    bindVar(v2,v1);
    bind(v1,target);
  }
}

void MMSubstitution::unifyUnbound(VarSpec v, TermSpec ts)
{
  CALL("MMSubstitution::unifyUnbound");

  v=root(v);

  ASS(isUnbound(v));

  if(ts.isVar()) {
    VarSpec v2=root(getVarSpec(ts));
    if(v!=v2) {
    	makeEqual(v, v2, deref(v2));
    }
  } else {
    bind(v,ts);
  }
}


void MMSubstitution::swap(TermSpec& ts1, TermSpec& ts2)
{
  TermSpec aux=ts1;
  ts1=ts2;
  ts2=aux;
}

TermList MMSubstitution::getAuxTerm(TermSpec ts)
{
  CALL("MMSubstitution::getAuxTerm");

  int index=ts.index;
  if(index==AUX_INDEX) {
    return ts.term;
  }

  static Stack<TermList*> toDo(32);
  static Stack<Term*> terms(32);
  static Stack<TermList> args(32);

  toDo.push(&ts.term);

  while(!toDo.isEmpty()) {
    TermList* tt=toDo.pop();
    if(tt->isEmpty()) {
      Term* orig=terms.pop();
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);
      args.truncate(args.length() - orig->arity());
      TermList constructed;
      constructed.setTerm(Term::create(orig,argLst));
      args.push(constructed);
      continue;
    } else {
      //if tt==&trm, we're dealing with the top
      //term, for which the next() is undefined
      if(tt!=&ts.term) {
	toDo.push(tt->next());
      }
    }

    if(tt->isVar()) {
      TermList aux;
      aux.makeVar(getAuxVar(getVarSpec(*tt, index)).var);
      args.push(aux);
      continue;
    }
    Term* t=tt->term();
    if(t->shared() && t->ground()) {
      args.push(*tt);
      continue;
    }
    terms.push(t);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty() && terms.isEmpty() && args.length()==1);
  return args.pop();
}



bool MMSubstitution::handleDifferentTops(TermSpec t1, TermSpec t2,
	Stack<TTPair>& toDo, TermList* ct)
{
  CALL("MMSubstitution::handleDifferentTops");
  if(t1.isVar()) {
    VarSpec v1=getVarSpec(t1);
    if(ct) {
      VarSpec ctVar=getAuxVar(v1);
      ct->makeVar(ctVar.var);
    }
    if(isUnbound(v1)) {
      unifyUnbound(v1,t2);
    } else if(t2.isVar() && isUnbound(getVarSpec(t2))) {
      unifyUnbound(getVarSpec(t2),t1);
    } else {
      toDo.push(TTPair(t1,t2));
    }
  } else if(t2.isVar()) {
    VarSpec v2=getVarSpec(t2);
    if(ct) {
      VarSpec ctVar=getAuxVar(v2);
      ct->makeVar(ctVar.var);
    }
    if(isUnbound(v2)) {
      unifyUnbound(v2,t1);
    } else {
      toDo.push(TTPair(t2,t1));
    }
  } else {
    //tops are different and neither of them is variable, so we can't unify them
    ASS(t1.term.isTerm() && t2.term.isTerm() &&
	    t1.term.term()->functor()!=t2.term.term()->functor());
    return false;
  }
  return true;
}

bool MMSubstitution::unify(TermSpec t1, TermSpec t2)
{
  CALL("MMSubstitution::unify/2");

  if(t1.sameTermContent(t2)) {
    return true;
  }

  bool mismatch=false;
  BacktrackData localBD;
  bdRecord(localBD);

  //toDo stack contains pairs of terms to be unified.
  //Terms in those pairs can be either complex pairs
  //or bound variables. If pair consists of one complex
  //term and one bound variable, the bound variable has
  //to be first.
  static Stack<TTPair> toDo(64);
  static Stack<TermList*> subterms(64);
  ASS(toDo.isEmpty() && subterms.isEmpty());

  if(TermList::sameTopFunctor(t1.term,t2.term)) {
    toDo.push(TTPair(t1,t2));
  } else {
    if(!handleDifferentTops(t1,t2,toDo,0)) {
      mismatch=true;
      ASS(toDo.isEmpty());
    }
  }


  while(!toDo.isEmpty()) {
    TTPair task=toDo.pop();
    t1=task.first;
    t2=task.second;
    ASS(!t2.isVar() || t1.isVar());

    TermSpec dt1=derefBound(t1);
    TermSpec dt2=derefBound(t2);
    ASS(!dt1.isVar() && !dt2.isVar());

    TermList* ss=&dt1.term;
    TermList* tt=&dt2.term;
    TermList* ct;

    TermSpec commonTS;
    bool buildingCommon=t1.isVar();
    if(buildingCommon) {
      //we must ensure, that commonTS.term.tag()!=REF, because if
      //method handleDifferentTops(...,ct) returns false when
      //ct==&commonTS, value of commonTS.term is undefined, when we
      //get to releasing of created common term.
      commonTS.term.makeEmpty();
      commonTS.index=AUX_INDEX;
      ct=&commonTS.term;
    } else {
      ct=0;
    }

    Stack<TermList*> subterms(64);
    for (;;) {
      TermSpec tsss(*ss,dt1.index);
      TermSpec tstt(*tt,dt2.index);

      if (!tsss.sameTermContent(tstt) && TermList::sameTopFunctor(*ss,*tt)) {
        ASS(ss->isTerm() && tt->isTerm());

        Term* s = ss->term();
        Term* t = tt->term();
        ASS(s->arity() > 0);
        ASS(s->functor() == t->functor());

        if(ct) {
          ct->setTerm(Term::createNonShared(t));
        }

        ss = s->args();
        tt = t->args();
        ct = ct ? ct->term()->args() : 0;
        if (! ss->next()->isEmpty()) {
          subterms.push(ss->next());
          subterms.push(tt->next());
          subterms.push(ct ? ct->next() : 0);
        }
      } else {
        if (! TermList::sameTopFunctor(*ss,*tt)) {
          if(!handleDifferentTops(tsss,tstt,toDo,ct)) {
            mismatch=true;
            break;
          }
        } else { //tsss->sameContent(tstt)
          if(ct) {
            *ct=getAuxTerm(tsss);
          }
        }

        if (subterms.isEmpty()) {
          break;
        }
        ct = subterms.pop();
        tt = subterms.pop();
        ss = subterms.pop();
        if (! ss->next()->isEmpty()) {
          subterms.push(ss->next());
          subterms.push(tt->next());
          subterms.push(ct ? ct->next() : 0);
        }
      }
    }

    if(mismatch) {
      if(buildingCommon && commonTS.term.isTerm()) {
	commonTS.term.term()->destroyNonShared();
      }
      break;
    }

    if(t1.isVar()) {
      ASS(buildingCommon);
      ASS(!commonTS.isVar());
      VarSpec v1=root(getVarSpec(t1));

      Term* shared=env.sharing->insertRecurrently(commonTS.term.term());
      commonTS.term.setTerm(shared);

      if(t2.isVar()) {
	VarSpec v2=root(getVarSpec(t2));
	makeEqual(v1, v2, commonTS);
      } else {
	bind(v1, commonTS);
      }
    }
  }

  if(!mismatch) {
    mismatch=occurCheckFails();
  } else {
    subterms.reset();
    toDo.reset();
  }

  bdDone();

  if(mismatch) {
    localBD.backtrack();
  } else {
    if(bdIsRecording()) {
      bdCommit(localBD);
    }
    localBD.drop();
  }

  return !mismatch;
}

/**
 * Matches @b instance term onto the @b base term.
 * Ordinary variables behave, as one would expect
 * during matching, but special variables aren't
 * being assigned only in the @b base term, but in
 * the instance ass well. (Special variables appear
 * only in internal terms of substitution trees and
 * this behavior allows easy instance retrieval.)
 */
bool MMSubstitution::match(TermSpec base, TermSpec instance)
{
  CALL("MMSubstitution::match(TermSpec...)");

  if(base.sameTermContent(instance)) {
    return true;
  }

  bool mismatch=false;
  BacktrackData localBD;
  bdRecord(localBD);

  static Stack<TermList*> subterms(64);
  ASS(subterms.isEmpty());

  TermList* bt=&base.term;
  TermList* it=&instance.term;

  TermSpec binding1;
  TermSpec binding2;

  for (;;) {
    TermSpec bts(*bt,base.index);
    TermSpec its(*it,instance.index);

    if (!bts.sameTermContent(its) && TermList::sameTopFunctor(bts.term,its.term)) {
      Term* s = bts.term.term();
      Term* t = its.term.term();
      ASS(s->arity() > 0);

      bt = s->args();
      it = t->args();
    } else {
      if (! TermList::sameTopFunctor(bts.term,its.term)) {
	if(bts.term.isSpecialVar()) {
	  VarSpec bvs(bts.term.var(), SPECIAL_INDEX);
	  if(_bank.find(bvs, binding1)) {
	    ASS_EQ(binding1.index, base.index);
	    bt=&binding1.term;
	    continue;
	  } else {
	    bind(bvs,its);
	  }
	} else if(its.term.isSpecialVar()) {
	  VarSpec ivs(its.term.var(), SPECIAL_INDEX);
	  if(_bank.find(ivs, binding2)) {
	    ASS_EQ(binding2.index, instance.index);
	    it=&binding2.term;
	    continue;
	  } else {
	    bind(ivs,bts);
	  }
	} else if(bts.term.isOrdinaryVar()) {
	  VarSpec bvs(bts.term.var(), bts.index);
	  if(_bank.find(bvs, binding1)) {
	    ASS_EQ(binding1.index, instance.index);
	    if(!TermList::equals(binding1.term, its.term))
	    {
	      mismatch=true;
	      break;
	    }
	  } else {
	    bind(bvs,its);
	  }
	} else {
	  mismatch=true;
	  break;
	}
      }

      if (subterms.isEmpty()) {
	break;
      }
      bt = subterms.pop();
      it = subterms.pop();
    }
    if (!bt->next()->isEmpty()) {
      subterms.push(it->next());
      subterms.push(bt->next());
    }
  }

  ASS(!occurCheckFails());
  bdDone();

  subterms.reset();


  if(mismatch) {
    localBD.backtrack();
  } else {
    if(bdIsRecording()) {
      bdCommit(localBD);
    }
    localBD.drop();
  }

  return !mismatch;
}


Literal* MMSubstitution::apply(Literal* lit, int index)
{
  CALL("MMSubstitution::apply(Literal*...)");
  static DArray<TermList> ts(32);

  if (lit->ground()) {
    return lit;
  }

  int arity = lit->arity();
  ts.ensure(arity);
  int i = 0;
  for (TermList* args = lit->args(); ! args->isEmpty(); args = args->next()) {
    ts[i++]=apply(*args,index);
  }
  return Literal::create(lit,ts.array());
}

TermList MMSubstitution::apply(TermList trm, int index)
{
  CALL("MMSubstitution::apply(TermList...)");

  static Stack<TermList*> toDo(8);
  static Stack<int> toDoIndex(8);
  static Stack<Term*> terms(8);
  static Stack<VarSpec> termRefVars(8);
  static Stack<TermList> args(8);
  static DHMap<VarSpec, TermList, VarSpec::Hash1, VarSpec::Hash2> known;

  //is inserted into termRefVars, if respective
  //term in terms isn't referenced by any variable
  const VarSpec nilVS(-1,0);

  toDo.push(&trm);
  toDoIndex.push(index);

  while(!toDo.isEmpty()) {
    TermList* tt=toDo.pop();
    index=toDoIndex.pop();
    if(tt->isEmpty()) {
      Term* orig=terms.pop();
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);
      args.truncate(args.length() - orig->arity());
      TermList constructed;
      constructed.setTerm(Term::create(orig,argLst));
      args.push(constructed);

      VarSpec ref=termRefVars.pop();
      if(ref!=nilVS) {
	ALWAYS(known.insert(ref,constructed));
      }
      continue;
    } else {
      //if tt==&trm, we're dealing with the top
      //term, for which the next() is undefined
      if(tt!=&trm) {
	toDo.push(tt->next());
	toDoIndex.push(index);
      }
    }

    TermSpec ts(*tt,index);

    VarSpec vs;
    if(ts.term.isVar()) {
      vs=root(getVarSpec(ts));

      TermList found;
      if(known.find(vs, found)) {
	args.push(found);
	continue;
      }

      ts=deref(vs);
      if(ts.term.isVar()) {
	ASS(ts.index==UNBOUND_INDEX);
	args.push(ts.term);
	continue;
      }
    } else {
      vs=nilVS;
    }
    Term* t=ts.term.term();
    if(t->shared() && t->ground()) {
      args.push(ts.term);
      continue;
    }
    terms.push(t);
    termRefVars.push(vs);

    toDo.push(t->args());
    toDoIndex.push(ts.index);
  }
  ASS(toDo.isEmpty() && toDoIndex.isEmpty() && terms.isEmpty() && args.length()==1);
  known.reset();
  return args.pop();
}

bool MMSubstitution::occurCheckFails()
{
  CALL("MMSubstitution::occurCheckFails");

  static Stack<VarSpec> maybeUnref(8);
  static Stack<VarSpec> unref(8);
  DHMultiset<VarSpec,VarSpec::Hash1,VarSpec::Hash2> refCounter;

  ASS(maybeUnref.isEmpty() && unref.isEmpty());

  BankType::Iterator bit(_bank);
  while(bit.hasNext()) {
    VarSpec vs;
    TermSpec ts;
    bit.next(vs,ts);
    ASSERT_VALID(ts.term);
    if(!ts.term.isTerm()) {
      continue;
    }
    if(!refCounter.find(vs)) {
      maybeUnref.push(vs);
    }
    Term::VariableIterator vit(ts.term.term());
    while(vit.hasNext()) {
      VarSpec r=root(getVarSpec(vit.next(),ts.index));
      refCounter.insert(r);
    }
  }

  while(!maybeUnref.isEmpty()) {
    VarSpec vs=maybeUnref.pop();
    if(!refCounter.find(vs)) {
      unref.push(vs);
    }
  }
  while(!unref.isEmpty()) {
    VarSpec v=unref.pop();
    TermSpec ts=_bank.get(v);
    ASS(ts.term.isTerm());
    Term::VariableIterator vit(ts.term.term());
    while(vit.hasNext()) {
      VarSpec r=root(getVarSpec(vit.next(),ts.index));
      refCounter.remove(r);
      if(!refCounter.find(r)) {
	TermSpec rts;
	if(_bank.find(r, rts) && rts.term.isTerm()) {
	  unref.push(r);
	}
      }
    }
  }

  return refCounter.size()!=0;
}

/**
 * Return iterator on matching substitutions of @b l1 and @b l2.
 *
 * For guides on use of the iterator, see the documentation of
 * MMSubstitution::AssocIterator.
 */
SubstIterator MMSubstitution::matches(Literal* base, int baseIndex,
	Literal* instance, int instanceIndex, bool complementary)
{
  return getAssocIterator<MatchingFn>(this, base, baseIndex,
	  instance, instanceIndex, complementary);
}

/**
 * Return iterator on unifying substitutions of @b l1 and @b l2.
 *
 * For guides on use of the iterator, see the documentation of
 * MMSubstitution::AssocIterator.
 */
SubstIterator MMSubstitution::unifiers(Literal* l1, int l1Index,
	Literal* l2, int l2Index, bool complementary)
{
  return getAssocIterator<UnificationFn>(this, l1, l1Index,
	  l2, l2Index, complementary);
}

template<class Fn>
SubstIterator MMSubstitution::getAssocIterator(MMSubstitution* subst,
	  Literal* l1, int l1Index, Literal* l2, int l2Index, bool complementary)
{
  CALL("MMSubstitution::getAssocIterator");

  if( !Literal::headersMatch(l1,l2,complementary) ) {
    return SubstIterator::getEmpty();
  }
  if( !l1->commutative() ) {
    return pvi( getContextualIterator(getSingletonIterator(subst),
	    AssocContext<Fn>(l1, l1Index, l2, l2Index)) );
  } else {
    return vi(
	    new AssocIterator<Fn>(subst, l1, l1Index, l2, l2Index));
  }
}

template<class Fn>
struct MMSubstitution::AssocContext
{
  AssocContext(Literal* l1, int l1Index, Literal* l2, int l2Index)
  : _l1(l1), _l1i(l1Index), _l2(l2), _l2i(l2Index) {}
  bool enter(MMSubstitution* subst)
  {
    subst->bdRecord(_bdata);
    bool res=Fn::associate(subst, _l1, _l1i, _l2, _l2i);
    if(!res) {
      subst->bdDone();
      ASS(_bdata.isEmpty());
    }
    return res;
  }
  void leave(MMSubstitution* subst)
  {
    subst->bdDone();
    _bdata.backtrack();
  }
private:
  Literal* _l1;
  int _l1i;
  Literal* _l2;
  int _l2i;
  bool _complementary;
  BacktrackData _bdata;
};

/**
 * Iterator on associating[1] substitutions of two literals.
 *
 * Using this iterator requires special care, as the
 * substitution being returned is always the same object.
 * The rules for safe use are:
 * - After the iterator is created and before it's
 * destroyed, or hasNext() gives result false, the original
 * substitution is invalid.
 * - Substitution retrieved by call to the method next()
 * is valid only until the hasNext() method is called again
 * (or until the iterator is destroyed).
 * - Before each call to next(), hasNext() has to be called at
 * least once.
 *
 * There rules are quite natural, and the 3rd one is
 * required by many other iterators as well.
 *
 * Template parameter class Fn has to contain following
 * methods:
 * bool associate(MMSubstitution*, Literal* l1, int l1Index,
 * 	Literal* l2, int l2Index, bool complementary)
 * bool associate(MMSubstitution*, TermList t1, int t1Index,
 * 	TermList t2, int t2Index)
 * There is supposed to be one Fn class for unification and
 * one for matching.
 *
 * [1] associate means either match or unify
 */
template<class Fn>
class MMSubstitution::AssocIterator
:public IteratorCore<MMSubstitution*>
{
public:
  AssocIterator(MMSubstitution* subst, Literal* l1, int l1Index,
	  Literal* l2, int l2Index)
  : _subst(subst), _l1(l1), _l1i(l1Index), _l2(l2),
  _l2i(l2Index), _state(FIRST), _used(true)
  {
    ASS_EQ(_l1->functor(),_l2->functor());
    ASS(_l1->commutative());
    ASS_EQ(_l1->arity(),2);
  }
  ~AssocIterator()
  {
    CALL("MMSubstitution::AssocIterator::~AssocIterator");

    if(_state!=FINISHED && _state!=FIRST) {
	backtrack();
    }
    ASS(_bdata.isEmpty());
  }
  bool hasNext()
  {
    CALL("MMSubstitution::AssocIterator::hasNext");

    if(_state==FINISHED) {
      return false;
    }
    if(!_used) {
      return true;
    }
    _used=false;

    if(_state!=FIRST) {
      backtrack();
    }
    _subst->bdRecord(_bdata);

    switch(_state) {
    case NEXT_STRAIGHT:
      if(Fn::associate(_subst, _l1, _l1i, _l2, _l2i)) {
	_state=NEXT_REVERSED;
	break;
      }
      //no break here intentionally
    case NEXT_REVERSED:
    {
      TermList t11=*_l1->nthArgument(0);
      TermList t12=*_l1->nthArgument(1);
      TermList t21=*_l2->nthArgument(0);
      TermList t22=*_l2->nthArgument(1);
      if(Fn::associate(_subst, t11, _l1i, t22, _l2i)) {
	if(Fn::associate(_subst, t12, _l1i, t21, _l2i)) {
	  _state=NEXT_CLEANUP;
	  break;
	}
	//the first successful association will be undone
	//in case NEXT_CLEANUP
      }
    }
    //no break here intentionally
    case NEXT_CLEANUP:
      //undo the previous match
      backtrack();
      _state=FINISHED;
#if VDEBUG
      break;
    default:
      ASSERTION_VIOLATION;
#endif
    }
    ASS(_state!=FINISHED || _bdata.isEmpty());
    return _state!=FINISHED;
  }

  MMSubstitution* next()
  {
    _used=true;
    return _subst;
  }
private:
  void backtrack()
  {
    CALL("MMSubstitution::AssocIterator::backtrack");

    ASS_EQ(&_bdata,&_subst->bdGet());
    _subst->bdDone();
    _bdata.backtrack();
  }
  enum State {
    FIRST=0,
    NEXT_STRAIGHT=0,
    NEXT_REVERSED=1,
    NEXT_CLEANUP=2,
    FINISHED=3
  };

  MMSubstitution* _subst;
  Literal* _l1;
  int _l1i;
  Literal* _l2;
  int _l2i;
  BacktrackData _bdata;

  State _state;
  /**
   * true if the current substitution have already been
   * retrieved by the next() method, or if there isn't
   * any (hasNext() hasn't been called yet)
   */
  bool _used;
};
struct MMSubstitution::MatchingFn {
  static bool associate(MMSubstitution* subst, Literal* l1, int l1Index,
	  Literal* l2, int l2Index)
  { return subst->matchArgs(l1,l1Index,l2,l2Index); }

  static bool associate(MMSubstitution* subst, TermList t1, int t1Index,
	  TermList t2, int t2Index)
  { return subst->match(t1,t1Index,t2,t2Index); }
};
struct MMSubstitution::UnificationFn {
  static bool associate(MMSubstitution* subst, Literal* l1, int l1Index,
	  Literal* l2, int l2Index)
  { return subst->unifyArgs(l1,l1Index,l2,l2Index); }

  static bool associate(MMSubstitution* subst, TermList t1, int t1Index,
	  TermList t2, int t2Index)
  { return subst->unify(t1,t1Index,t2,t2Index); }
};


#if VDEBUG
string MMSubstitution::toString(bool deref)
{
  CALL("MMSubstitution::toString");
  string res;
  BankType::Iterator bit(_bank);
  while(bit.hasNext()) {
    VarSpec v;
    TermSpec binding;
    bit.next(v,binding);
    TermList tl;
    if(v.index==SPECIAL_INDEX) {
      res+="S"+Int::toString(v.var)+" -> ";
      tl.makeSpecialVar(v.var);
    } else {
      res+="X"+Int::toString(v.var)+"/"+Int::toString(v.index)+ " -> ";
      tl.makeVar(v.var);
    }
    if(deref) {
      tl=apply(tl, v.index);
      res+=Test::Output::singleTermListToString(tl)+"\n";
    } else {
      res+=Test::Output::singleTermListToString(binding.term)+"/"+Int::toString(binding.index)+"\n";
    }

  }
  return res;
}

std::string MMSubstitution::VarSpec::toString()
{
  if(index==SPECIAL_INDEX) {
    return "S"+Int::toString(var);
  } else {
    return "X"+Int::toString(var)+"/"+Int::toString(index);
  }
}

string MMSubstitution::TermSpec::toString()
{
  return Test::Output::singleTermListToString(term)+"/"+Int::toString(index);
}

ostream& operator<< (ostream& out, MMSubstitution::VarSpec vs )
{
  return out<<vs.toString();
}

ostream& operator<< (ostream& out, MMSubstitution::TermSpec ts )
{
  return out<<ts.toString();
}

#endif

/**
 * First hash function for DHMap.
 */
unsigned MMSubstitution::VarSpec::Hash1::hash(VarSpec& o, int capacity)
{
//  return o.var + o.index*(capacity>>1) + (o.index>>1)*(capacity>>3);
//  return o.var^(o.var/capacity) + o.index*(capacity>>1) + (o.index>>2)*(capacity>>3);
//This might work better

  int res=(o.var%(capacity<<1) - capacity);
  if(res<0)
    //this turns x into -x-1
    res = ~res;
  if(o.index&1)
    return static_cast<unsigned>(-res+capacity-o.index);
  else
    return static_cast<unsigned>(res);
}

/**
 * Second hash function for DHMap. It just uses the hash function from Lib::Hash
 */
unsigned MMSubstitution::VarSpec::Hash2::hash(VarSpec& o)
{
  return Lib::Hash::hash(reinterpret_cast<const unsigned char*>(&o), sizeof(VarSpec));
//  return o.var+o.index;
}

}
