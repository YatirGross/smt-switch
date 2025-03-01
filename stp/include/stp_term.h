#pragma once

#include "stp/c_interface.h"
#include "term.h"
#include "utils.h"

namespace smt {
// forward declaration
class StpSolver;

class StpTermIter : public TermIterBase
{
 public:
  StpTermIter(const ASTVec& n, uint32_t p = 0) : children(n), pos(p) {};
  StpTermIter(const StpTermIter & it);
  ~StpTermIter() {};
  void operator++() override;
  const Term operator*() override;
  TermIterBase * clone() const override;
  bool operator==(const StpTermIter & it) const;

 protected:
  bool equal(const TermIterBase & other) const override;

 private:
  const ASTVec& children;
  uint32_t pos;
};

class StpTerm : public AbsTerm
{
 public:
  StpTerm(const Expr e) : expr(e) {};
  ~StpTerm() {};
  std::size_t hash() const override;
  std::size_t get_id() const override;
  bool compare(const Term & absterm) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  bool is_symbol() const override;
  bool is_param() const override;
  bool is_symbolic_const() const override;
  bool is_value() const override;
  virtual std::string to_string() override;
  uint64_t to_int() const override;
  TermIter begin() override;
  TermIter end() override;
  std::string print_value_as(SortKind sk) override;

 protected:
  Expr expr;

  friend class StpSolver;
};

}  // namespace smt