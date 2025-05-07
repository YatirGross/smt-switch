#pragma once

#include "sort.h"
#include "stp/c_interface.h"
#include <unordered_map>

namespace smt {

const std::unordered_map<type_t, SortKind> type2sortKind(
    { { BOOLEAN_TYPE, BOOL },
      { BITVECTOR_TYPE, BV },
      { ARRAY_TYPE, ARRAY }
    } );

const std::unordered_map<SortKind, type_t> sortKind2type(
    { { BOOL, BOOLEAN_TYPE },
      { BV, BITVECTOR_TYPE },
      { ARRAY, ARRAY_TYPE }
    } );

class StpSort : public AbsSort
{
 public:
  StpSort(Type t, VC vc) : type(t), vc(vc) {};
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
  Type type;
  VC vc;

  friend class StpSolver;
};

}  // namespace smt
