#include "stp_term.h"
#include "stp_solver.h"
#include "stp_sort.h"

namespace smt {

  const std::unordered_map<::stp::exprkind_t, PrimOp> kind2primop{
    /* Logical Operations */
    {::stp::exprkind_t::AND, And},
    {::stp::exprkind_t::OR, Or},
    {::stp::exprkind_t::XOR, Xor},
    {::stp::exprkind_t::NOT, Not},
    {::stp::exprkind_t::IMPLIES, Implies},
    {::stp::exprkind_t::ITE, Ite},
    {::stp::exprkind_t::EQ, Equal},

    /* Bitwise Operations */
    {::stp::exprkind_t::BVNOT, BVNot},
    {::stp::exprkind_t::BVAND, BVAnd},
    {::stp::exprkind_t::BVOR, BVOr},
    {::stp::exprkind_t::BVXOR, BVXor},
    {::stp::exprkind_t::BVNAND, BVNand},
    {::stp::exprkind_t::BVNOR, BVNor},
    {::stp::exprkind_t::BVXNOR, BVXnor},

    /* Bitvector Manipulation */
    {::stp::exprkind_t::BVCONCAT, Concat},
    {::stp::exprkind_t::BVEXTRACT, Extract},
    {::stp::exprkind_t::BVLEFTSHIFT, BVShl},
    {::stp::exprkind_t::BVRIGHTSHIFT, BVLshr},
    {::stp::exprkind_t::BVSRSHIFT, BVAshr},

    /* Arithmetic Operations */
    {::stp::exprkind_t::BVPLUS, BVAdd},
    {::stp::exprkind_t::BVSUB, BVSub},
    {::stp::exprkind_t::BVMULT, BVMul},
    {::stp::exprkind_t::BVDIV, BVUdiv},
    {::stp::exprkind_t::SBVDIV, BVSdiv},
    {::stp::exprkind_t::SBVREM, BVSrem},
    {::stp::exprkind_t::SBVMOD, BVSmod},

    /* Comparison Operators (Unsigned & Signed) */
    {::stp::exprkind_t::BVLT, BVUlt},
    {::stp::exprkind_t::BVLE, BVUle},
    {::stp::exprkind_t::BVGT, BVUgt},
    {::stp::exprkind_t::BVGE, BVUge},
    {::stp::exprkind_t::BVSLT, BVSlt},
    {::stp::exprkind_t::BVSLE, BVSle},
    {::stp::exprkind_t::BVSGT, BVSgt},
    {::stp::exprkind_t::BVSGE, BVSge}
};


// StpTermIter Implementation

StpTermIter::StpTermIter(const StpTermIter & it) : children(it.children), pos(it.pos) {}

void StpTermIter::operator++()
{
  ++pos;
}

const Term StpTermIter::operator*()
{
  if (pos < children.size())
  {
    Sort sort;
    const auto& child = children[pos];
    if (children[pos].GetValueWidth() > 0) {
      if (children[pos].GetIndexWidth() > 0) {
        sort = std::make_shared<StpSort>(::stp::Kind::ARRAY,
                                         children[pos].GetValueWidth(),
                                         std::make_shared<StpSort>(::stp::Kind::BITVECTOR,
                                                                   children[pos].GetIndexWidth()),
                                         std::make_shared<StpSort>(::stp::Kind::BITVECTOR,
                                                                   children[pos].GetValueWidth()));
      } else {
        sort = std::make_shared<StpSort>(::stp::Kind::BITVECTOR, children[pos].GetValueWidth());
      }
    } else {
      sort = std::make_shared<StpSort>(::stp::Kind::BOOLEAN);
    }
    const Term child_term = std::make_shared<StpTerm>(child, sort);
    return child_term;
  }
  throw std::out_of_range("StpTermIter out of range");
}

TermIterBase * StpTermIter::clone() const
{
  return new StpTermIter(*this);
}

bool StpTermIter::operator==(const StpTermIter & it) const
{
  return (children == it.children) && (pos == it.pos);
}

bool StpTermIter::equal(const TermIterBase & other) const
{
  const auto * other_it = dynamic_cast<const StpTermIter *>(&other);
  return other_it && (*this == *other_it);
}

// StpTerm Implementation

std::size_t StpTerm::hash() const
{
  return vc_getHashQueryStateToBuffer(vc, expr);
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
  enum stp::exprkind_t k = getExprKind(expr);
  if(!k || kind2primop.find(k) == kind2primop.end())
  {
    return Op();
  }
  return Op(kind2primop.at(k));
}

Sort StpTerm::get_sort() const
{
  if (!sort)
  {
    throw std::runtime_error("Sort not set");
  }
  return sort;
}

bool StpTerm::is_symbol() const
{
  return node.GetKind() == stp::SYMBOL;
}

bool StpTerm::is_param() const
{
  return node.GetKind() == stp::PARAMBOOL;
}

bool StpTerm::is_symbolic_const() const
{
  return is_symbol();
}

bool StpTerm::is_value() const
{
  return node.isConstant();
}

std::string StpTerm::to_string()
{
  if (!is_symbol()) {
    throw std::logic_error("Cannot convert non-symbol term to string");
  }
  return node.GetName();
}

uint64_t StpTerm::to_int() const
{
  if (!is_value())
  {
    throw std::logic_error("Cannot convert non-value term to integer");
  }
  return static_cast<uint64_t>(node.GetValueWidth());
}

TermIter StpTerm::begin()
{
  return TermIter(new StpTermIter(node.GetChildren(), 0));
}

TermIter StpTerm::end()
{
  return TermIter(new StpTermIter(node.GetChildren(), node.GetChildren().size() - 1));
}

std::string StpTerm::print_value_as(SortKind sk)
{
  throw std::runtime_error("Not implemented");
}

} // namespace smt
