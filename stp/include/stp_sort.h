#pragma once

#include "sort.h"
#include "stp/cpp_interface.h"
#include <unordered_map>

namespace smt {

const std::unordered_map<::stp::Kind, SortKind> kind2sortKind(
    { { ::stp::Kind::ARRAY, ARRAY },
      { ::stp::Kind::BITVECTOR, BV },
      { ::stp::Kind::BOOLEAN, BOOL }
    } );

const std::unordered_map<SortKind, ::stp::Kind> sortKind2kind(
    { { ARRAY, ::stp::Kind::ARRAY },
      { BV, ::stp::Kind::BITVECTOR },
      { BOOL, ::stp::Kind::BOOLEAN }
    } );

class StpSort : public AbsSort
{
 public:
  StpSort(::stp::Kind sk, uint64_t width = 0, Sort index_sort = nullptr, Sort elem_sort = nullptr)
      : sk(sk), width(width), index_sort(index_sort), elem_sort(elem_sort){};
  ~StpSort() override = default;

  std::size_t hash() const override;
  uint64_t get_width() const override;
  Sort get_indexsort() const override;
  Sort get_elemsort() const override;
  std::vector<Sort> get_domain_sorts() const override;
  Sort get_codomain_sort() const override;
  std::string get_uninterpreted_name() const override;
  size_t get_arity() const override;
  std::vector<Sort> get_uninterpreted_param_sorts() const override;
  Datatype get_datatype() const override;
  bool compare(const Sort & sort) const override;
  SortKind get_sort_kind() const override;

 protected:
  ::stp::Kind sk;
  uint64_t width = 0;
  Sort index_sort = nullptr;
  Sort elem_sort = nullptr;

  friend class StpSolver;
};

}  // namespace smt
