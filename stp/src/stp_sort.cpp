#include "stp_sort.h"
#include "exceptions.h"

namespace smt {

std::size_t StpSort::hash() const
{
  type_t type_kind = getType(type);
  std::size_t hash = static_cast<std::size_t>(type_kind);
  
  if (type_kind == BITVECTOR_TYPE)
  {
    hash ^= vc_getValueSize(vc, type);
  }
  else if (type_kind == ARRAY_TYPE)
  {
    // For arrays, hash the index and element sizes
    hash ^= vc_getIndexSize(vc, type);
    hash ^= vc_getValueSize(vc, type);
  }
  
  return hash;
}

uint64_t StpSort::get_width() const
{
  return vc_getValueSize(vc, type);
}

Sort StpSort::get_indexsort() const
{
  try {
    // Try to get index size - this will fail if type is not an array
    int index_size = vc_getIndexSize(vc, type);
    Type index_type = vc_bvType(vc, index_size);
    return std::make_shared<StpSort>(index_type, vc);
  } catch (...) {
    throw IncorrectUsageException("get_indexsort called on a non-array sort");
  }
}

Sort StpSort::get_elemsort() const
{
  try {
    // Try to get value size - this will fail if type is not an array
    int value_size = vc_getValueSize(vc, type);
    Type elem_type = vc_bvType(vc, value_size);
    return std::make_shared<StpSort>(elem_type, vc);
  } catch (...) {
    throw IncorrectUsageException("get_elemsort called on a non-array sort");
  }
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
