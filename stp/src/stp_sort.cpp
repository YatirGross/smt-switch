#include "stp_sort.h"
#include "exceptions.h"

namespace smt {

std::size_t StpSort::hash() const
{
  return reinterpret_cast<size_t>(type);
}

uint64_t StpSort::get_width() const
{
  return vc_getValueSize(vc, type);
}

Sort StpSort::get_indexsort() const
{
  if (type2sortKind.at(getType(type)) != ARRAY)
  {
    throw IncorrectUsageException("get_indexsort called on a non-array sort");
  }
  Type index_type = vc_bvType(vc, vc_getIndexSize(vc, type));
  return std::make_shared<StpSort>(index_type, vc);
}

Sort StpSort::get_elemsort() const
{
  if (type2sortKind.at(getType(type)) != ARRAY)
  {
    throw IncorrectUsageException("get_elemsort called on a non-array sort");
  }
  Type elem_type = vc_bvType(vc, vc_getValueSize(vc, type));
  return std::make_shared<StpSort>(elem_type, vc);
}

std::vector<Sort> StpSort::get_domain_sorts() const
{
  throw NotImplementedException("get_domain_sorts not supported for STP");
}

Sort StpSort::get_codomain_sort() const
{
  throw NotImplementedException("get_codomain_sort no supported for STP");
}

std::string StpSort::get_uninterpreted_name() const
{
  throw NotImplementedException("get_uninterpreted_name not supported for STP");
}

size_t StpSort::get_arity() const
{
  throw NotImplementedException("get_arity not supported for STP");
}

std::vector<Sort> StpSort::get_uninterpreted_param_sorts() const
{
  throw NotImplementedException("get_uninterpreted_param_sorts not implemented for STP");
}

Datatype StpSort::get_datatype() const
{
  throw NotImplementedException("get_datatype not implemented for STP");
}

bool StpSort::compare(const Sort & sort) const
{
  Type other = std::static_pointer_cast<StpSort>(sort)->type;
  return getType(type) == getType(other)
         && vc_getValueSize(vc, type) == vc_getValueSize(vc, other)
         && vc_getIndexSize(vc, type) == vc_getIndexSize(vc, other);
}

SortKind StpSort::get_sort_kind() const
{
  Expr e = vc_varExpr(vc, "tmp", type);
  return type2sortKind.at(getType(e));
}

}  // namespace smt
