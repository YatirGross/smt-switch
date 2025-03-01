#include "stp_sort.h"
#include "exceptions.h"

namespace smt {

std::size_t StpSort::hash() const
{
  return static_cast<std::size_t>(sk);
}

uint64_t StpSort::get_width() const
{
  if (kind2sortKind.at(sk) != BV)
  {
    throw IncorrectUsageException("get_width called on a non-bitvector sort");
  }
  return width;
}

Sort StpSort::get_indexsort() const
{
  if (kind2sortKind.at(sk) != ARRAY)
  {
    throw IncorrectUsageException("get_indexsort called on a non-array sort");
  }
  return index_sort;
}

Sort StpSort::get_elemsort() const
{
  if (kind2sortKind.at(sk) != ARRAY)
  {
    throw IncorrectUsageException("get_elemsort called on a non-array sort");
  }
  return elem_sort;
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
  switch (kind2sortKind.at(sk))
  {
    case ARRAY:
      return 2;
    case BV:
      return 1;
    case BOOL:
      return 0;
    default:
      throw IncorrectUsageException("Unknown sort kind");
  }
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
  bool ret = kind2sortKind.at(sk) == sort->get_sort_kind();
  if (ret && kind2sortKind.at(sk) == BV)
  {
    ret = width == std::static_pointer_cast<StpSort>(sort)->width;
  }
  if (ret && kind2sortKind.at(sk) == ARRAY)
  {
    ret = ret && index_sort == std::static_pointer_cast<StpSort>(sort)->index_sort;
    ret = ret && elem_sort == std::static_pointer_cast<StpSort>(sort)->elem_sort;
  }
  return ret;
}

SortKind StpSort::get_sort_kind() const
{
  return kind2sortKind.at(sk);
}

}  // namespace smt
