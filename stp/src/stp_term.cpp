#include "stp_term.h"
#include "stp_solver.h"
#include "stp_sort.h"

namespace smt {

  const std::unordered_map<exprkind_t, PrimOp> type2primop({
    /* Logical Operations */
    {exprkind_t::AND, And},
    {exprkind_t::OR, Or},
    {exprkind_t::XOR, Xor},
    {exprkind_t::NOT, Not},
    {exprkind_t::IMPLIES, Implies},
    {exprkind_t::ITE, Ite},
    {exprkind_t::EQ, Equal},

    /* Bitwise Operations */
    {exprkind_t::BVNOT, BVNot},
    {exprkind_t::BVAND, BVAnd},
    {exprkind_t::BVOR, BVOr},
    {exprkind_t::BVXOR, BVXor},
    {exprkind_t::BVNAND, BVNand},
    {exprkind_t::BVNOR, BVNor},
    {exprkind_t::BVXNOR, BVXnor},

    /* Bitvector Manipulation */
    {exprkind_t::BVCONCAT, Concat},
    {exprkind_t::BVEXTRACT, Extract},
    {exprkind_t::BVLEFTSHIFT, BVShl},
    {exprkind_t::BVRIGHTSHIFT, BVLshr},
    {exprkind_t::BVSRSHIFT, BVAshr},

    /* Arithmetic Operations */
    {exprkind_t::BVPLUS, BVAdd},
    {exprkind_t::BVUMINUS, BVNeg},
    {exprkind_t::BVSUB, BVSub},
    {exprkind_t::BVMULT, BVMul},
    {exprkind_t::BVDIV, BVUdiv},
    {exprkind_t::SBVDIV, BVSdiv},
    {exprkind_t::SBVREM, BVSrem},
    {exprkind_t::SBVMOD, BVSmod},

    /* Comparison Operators (Unsigned & Signed) */
    {exprkind_t::BVLT, BVUlt},
    {exprkind_t::BVLE, BVUle},
    {exprkind_t::BVGT, BVUgt},
    {exprkind_t::BVGE, BVUge},
    {exprkind_t::BVSLT, BVSlt},
    {exprkind_t::BVSLE, BVSle},
    {exprkind_t::BVSGT, BVSgt},
    {exprkind_t::BVSGE, BVSge}
});


// StpTermIter Implementation

StpTermIter::StpTermIter(const StpTermIter & it) : expr(it.expr), pos(it.pos) {}

void StpTermIter::operator++()
{
  ++pos;
}

const Term StpTermIter::operator*()
{
  Expr e = getChild(expr, pos);
  return std::make_shared<StpTerm>(e, vc);
}

TermIterBase * StpTermIter::clone() const
{
  return new StpTermIter(expr, vc);
}

bool StpTermIter::operator==(const StpTermIter & it) const
{
  return equal(it);
}

bool StpTermIter::equal(const TermIterBase & other) const
{
  const StpTermIter & it = static_cast<const StpTermIter &>(other);
  return expr == it.expr && pos == it.pos;
}

// StpTerm Implementation

std::size_t StpTerm::hash() const
{
  return reinterpret_cast<std::size_t>(expr);
}

std::size_t StpTerm::get_id() const
{
  return getExprID(expr);
}

bool StpTerm::compare(const Term & absterm) const
{
  try
  {
    const StpTerm & st = static_cast<const StpTerm &>(*absterm);
    return expr == st.expr;
  }
  catch (std::bad_cast & e)
  {
    return false;
  }
}

Op StpTerm::get_op() const
{
  enum exprkind_t k = getExprKind(expr);
  if(!k || type2primop.find(k) == type2primop.end())
  {
    return Op();
  }
  return Op(type2primop.at(k));
}

Sort StpTerm::get_sort() const
{
  Type t = vc_getType(vc, expr);
  return std::make_shared<StpSort>(t, vc);
}

bool StpTerm::is_symbol() const
{
  return getExprKind(expr) == SYMBOL;
}

bool StpTerm::is_param() const
{
  return getExprKind(expr) == PARAMBOOL;
}

bool StpTerm::is_symbolic_const() const
{
  return is_symbol();
}

bool StpTerm::is_value() const
{
  return getExprKind(expr) == BVCONST || getExprKind(expr) == BOOLEAN;
}

std::string StpTerm::to_string()
{
  const char* str = vc_printSMTLIB(vc, expr);
  if (str)
  {
    return std::string(str);
  }
  return std::string();
}

uint64_t StpTerm::to_int() const
{
  if (getExprKind(expr) == BVCONST)
  {
    return static_cast<uint64_t>(getBVUnsignedLongLong(expr));
  }
  if (getType(expr) == BOOLEAN_TYPE)
  {
    int bool_val = vc_isBool(expr);
    if (bool_val == -1) {
      throw IncorrectUsageException("Term is not a constant");
    }
    return bool_val;
  }
  
  throw IncorrectUsageException("Term is not a constant");
}

TermIter StpTerm::begin()
{
  return TermIter(new StpTermIter(expr, vc));
}

TermIter StpTerm::end()
{
  return TermIter(new StpTermIter(expr, vc, getDegree(expr)));
}

std::string StpTerm::print_value_as(SortKind sk)
{
  if (sk == BOOL)
  {
    return getBVUnsigned(expr) ? "true" : "false";
  }
  else if (sk == BV)
  {
    return std::to_string(getBVUnsigned(expr));
  }
  throw IncorrectUsageException("Cannot print value as given sort kind");
}

} // namespace smt
