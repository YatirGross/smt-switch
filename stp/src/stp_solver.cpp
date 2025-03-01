#include "stp_solver.h"


namespace smt {

    const std::unordered_map<PrimOp, ::stp::exprkind_t> primop2kind{
        /* Logical Operations */
        {And, ::stp::exprkind_t::AND},
        {Or, ::stp::exprkind_t::OR},
        {Xor, ::stp::exprkind_t::XOR},
        {Not, ::stp::exprkind_t::NOT},
        {Implies, ::stp::exprkind_t::IMPLIES},
        {Ite, ::stp::exprkind_t::ITE},
        {Equal, ::stp::exprkind_t::EQ},
    
        /* Bitwise Operations */
        {BVNot, ::stp::exprkind_t::BVNOT},
        {BVAnd, ::stp::exprkind_t::BVAND},
        {BVOr, ::stp::exprkind_t::BVOR},
        {BVXor, ::stp::exprkind_t::BVXOR},
        {BVNand, ::stp::exprkind_t::BVNAND},
        {BVNor, ::stp::exprkind_t::BVNOR},
        {BVXnor, ::stp::exprkind_t::BVXNOR},
    
        /* Bitvector Manipulation */
        {Concat, ::stp::exprkind_t::BVCONCAT},
        {Extract, ::stp::exprkind_t::BVEXTRACT},
        {BVShl, ::stp::exprkind_t::BVLEFTSHIFT},
        {BVLshr, ::stp::exprkind_t::BVRIGHTSHIFT},
        {BVAshr, ::stp::exprkind_t::BVSRSHIFT},
    
        /* Arithmetic Operations */
        {BVAdd, ::stp::exprkind_t::BVPLUS},
        {BVSub, ::stp::exprkind_t::BVSUB},
        {BVMul, ::stp::exprkind_t::BVMULT},
        {BVUdiv, ::stp::exprkind_t::BVDIV},
        {BVSdiv, ::stp::exprkind_t::SBVDIV},
        {BVSrem, ::stp::exprkind_t::SBVREM},
        {BVSmod, ::stp::exprkind_t::SBVMOD},
    
        /* Comparison Operators (Unsigned & Signed) */
        {BVUlt, ::stp::exprkind_t::BVLT},
        {BVUle, ::stp::exprkind_t::BVLE},
        {BVUgt, ::stp::exprkind_t::BVGT},
        {BVUge, ::stp::exprkind_t::BVGE},
        {BVSlt, ::stp::exprkind_t::BVSLT},
        {BVSle, ::stp::exprkind_t::BVSLE},
        {BVSgt, ::stp::exprkind_t::BVSGT},
        {BVSge, ::stp::exprkind_t::BVSGE}
    };
    

// Constructor
StpSolver::StpSolver() : AbsSmtSolver(STP)
{
    stp_mgr = new ::stp::STPMgr();
    stp_mgr->defaultNodeFactory =
      new SimplifyingNodeFactory(*(bm->hashingNodeFactory), *bm);
    stp_interface = new ::stp::Cpp_interface(*stp_mgr);
    context_level = 0;
    stp_interface->startup();
}

// Destructor
StpSolver::~StpSolver()
{
    stp_interface->deleteGlobal();
    stp_interface->cleanUp();
    delete stp_interface;
    delete stp_mgr;
}

// Solver configuration
void StpSolver::set_opt(const std::string option, const std::string value)
{
    stp_interface->setOption(option, value);
}

void StpSolver::set_logic(const std::string logic)
{
    throw std::runtime_error("Not implemented");
}

// Assertions and satisfiability checking
void StpSolver::assert_formula(const Term & t)
{
    stp_interface->AddAssert(std::static_pointer_cast<StpTerm>(t)->get_stp_node());
}

Result StpSolver::check_sat()
{
    stp_interface->checkSat({});
    // Check the result
    // TODO: check what is the result of the checkSat function
    return Result(UNKNOWN);
}

Result StpSolver::check_sat_assuming(const TermVec & assumptions)
{
    throw std::runtime_error("Not implemented");
}

// Context management
void StpSolver::push(uint64_t num)
{
    try {
        for (uint64_t i = 0; i < num; ++i)
        {
            stp_interface->push();
            ++context_level;
        }
    }
    catch (const std::exception &e)
    {
        throw InternalSolverException(e.what());
    }
}

void StpSolver::pop(uint64_t num)
{
    try {
        for (uint64_t i = 0; i < num; ++i)
        {
            stp_interface->pop();
            --context_level;
        }
    }
    catch (const std::exception &e)
    {
        throw InternalSolverException(e.what());
    }
}

uint64_t StpSolver::get_context_level() const
{
    return context_level;
}

// Model-related methods
Term StpSolver::get_value(const Term & t) const
{
    throw std::runtime_error("Not implemented");
}

UnorderedTermMap StpSolver::get_array_values(const Term & arr, Term & out_const_base) const
{
    throw std::runtime_error("Not implemented");
}

void StpSolver::get_unsat_assumptions(UnorderedTermSet & out)
{
    throw std::runtime_error("Not implemented");
}

// Sort creation methods
Sort StpSolver::make_sort(const std::string name, uint64_t arity) const
{
    throw std::runtime_error("Not implemented");
}

Sort StpSolver::make_sort(const SortKind sk) const
{
    if (sk == BOOL) {
      return std::make_shared<StpSort>(sortKind2kind.at(sk));
    }
    else {
      std::string msg("Can't create sort with sort constructor ");
      msg += to_string(sk);
      msg += " and no arguments";
      throw IncorrectUsageException(msg.c_str());
    }
}

Sort StpSolver::make_sort(const SortKind sk, uint64_t size) const
{
    if (sk == BV) {
      auto s = std::make_shared<StpSort>(sortKind2kind.at(sk));
      s->width = size;
      return s;
    }
    else {
      std::string msg("Can't create sort with sort constructor ");
      msg += to_string(sk);
      msg += " and one argument";
      throw IncorrectUsageException(msg.c_str());
    }
}

Sort StpSolver::make_sort(const SortKind sk, const Sort & sort1) const
{
    throw NotImplementedException(
      "Smt-switch does not have any sorts that take one sort parameter yet.");
}

Sort StpSolver::make_sort(const SortKind sk, const Sort & sort1, const Sort & sort2) const
{
    if (sk == ARRAY) {
      auto s = std::make_shared<StpSort>(sortKind2kind.at(sk));
      s->index_sort = std::static_pointer_cast<StpSort>(sort1);
      s->elem_sort = std::static_pointer_cast<StpSort>(sort2);
      return s;
    }
    else {
      std::string msg("Can't create sort with sort constructor ");
      msg += to_string(sk);
      msg += " and two arguments";
      throw IncorrectUsageException(msg.c_str());
    }
}

Sort StpSolver::make_sort(const SortKind sk, const Sort & sort1, const Sort & sort2, const Sort & sort3) const
{
    throw std::runtime_error("Not implemented");
}

Sort StpSolver::make_sort(const SortKind sk, const SortVec & sorts) const
{
    if (sk == BOOL && sorts.size() == 0) {
      return make_sort(BOOL);
    }
    else if (sk == BV && sorts.size() == 1) {
      return make_sort(BV, sorts[0]->get_width());
    }
    else if (sk == ARRAY && sorts.size() == 2) {
      return make_sort(ARRAY, sorts[0], sorts[1]);
    }
    else {
      std::string msg("Can't create sort from sort constructor ");
      msg += to_string(sk);
      msg += " with a vector of sorts";
      throw IncorrectUsageException(msg.c_str());
    }
}

Sort StpSolver::make_sort(const Sort & sort_con, const SortVec & sorts) const
{
    throw std::runtime_error("Not implemented");
}

Sort StpSolver::make_sort(const DatatypeDecl & d) const
{
    throw std::runtime_error("STP does not support datatypes");
}

// Term creation methods
Term StpSolver::make_term(bool b) const
{
    ASTNode n = stp_interface->CreateNode(b ? ::stp::Kind::TRUE : ::stp::Kind::FALSE);
    return std::make_shared<StpTerm>(n, make_sort(BOOL));
}

Term StpSolver::make_term(int64_t i, const Sort & sort) const
{
    if (sort->get_sort_kind() == BV && i >= 0) {
        ASTNode n = stp_interface->CreateBVConst(std::static_pointer_cast<StpSort>(sort)->width, static_cast<unsigned long long int>(i));
        return std::make_shared<StpTerm>(n, sort);
    }
    else {
        throw IncorrectUsageException("STP does not support negative integers or non-bitvector sorts");
    }
}

Term StpSolver::make_term(const std::string val, const Sort & sort, uint64_t base) const
{
    if (sort->get_sort_kind() == BV) {
        // Convert the string value to an unsigned long long int using the specified base
        unsigned long long int value = std::stoull(val, nullptr, base);
        ASTNode n = stp_interface->CreateBVConst(std::static_pointer_cast<StpSort>(sort)->width, value);
        return std::make_shared<StpTerm>(n, sort);
    }
    else {
        throw IncorrectUsageException("Unsupported sort for creating a term from a string value");
    }
}

Term StpSolver::make_term(const Term & val, const Sort & sort) const
{
    throw std::runtime_error("Not implemented");
}

Term StpSolver::make_symbol(const std::string name, const Sort & sort)
{
    ASTNode n = stp_interface->LookupOrCreateSymbol(name);
    return std::make_shared<StpTerm>(n, sort);
}

Term StpSolver::get_symbol(const std::string & name)
{
    ASTNode n = stp_interface->LookupOrCreateSymbol(name);
    return std::make_shared<StpTerm>(n, Sort());
}

Term StpSolver::make_param(const std::string name, const Sort & sort)
{
    throw std::runtime_error("Not implemented");
}

// Operator handling (terms with operations)
Term StpSolver::make_term(const Op op, const Term & t) const
{
    if(!primop2kind.count(op.prim_op))
    {
        return Term();
    }
    stp::Kind kind = primop2kind.at(op.prim_op);
    stp::ASTVec children;
    children.push_back(std::static_pointer_cast<StpTerm>(t)->get_stp_node());
    if (t->get_sort()->get_sort_kind() == BV || t->get_sort()->get_sort_kind() == ARRAY)
    {
        ASTNode* node = stp_interface->newNode(kind, t->get_sort()->get_width(), children);
        return std::make_shared<StpTerm>(*node, t->get_sort());
    }
    ASTNode node = stp_interface->CreateNode(kind, children);
    return std::make_shared<StpTerm>(node, t->get_sort());
}

Term StpSolver::make_term(const Op op, const Term & t0, const Term & t1) const
{
    if (!primop2kind.count(op.prim_op))
    {
        return Term();
    }
    stp::Kind kind = primop2kind.at(op.prim_op);
    stp::ASTVec children;
    children.push_back(std::static_pointer_cast<StpTerm>(t0)->get_stp_node());
    children.push_back(std::static_pointer_cast<StpTerm>(t1)->get_stp_node());
    if (t0->get_sort() != t1->get_sort())
    {
        throw IncorrectUsageException("Sorts of terms do not match");
    }
    if (t0->get_sort()->get_sort_kind() == BV || t0->get_sort()->get_sort_kind() == ARRAY)
    {
        ASTNode* node = stp_interface->newNode(kind, t0->get_sort()->get_width(), children);
        return std::make_shared<StpTerm>(*node, t0->get_sort());
    }
    ASTNode node = stp_interface->CreateNode(kind, children);
    return std::make_shared<StpTerm>(node, t0->get_sort());
}

Term StpSolver::make_term(const Op op, const Term & t0, const Term & t1, const Term & t2) const
{
    if (!primop2kind.count(op.prim_op))
    {
        return Term();
    }
    stp::Kind kind = primop2kind.at(op.prim_op);
    stp::ASTVec children;
    children.push_back(std::static_pointer_cast<StpTerm>(t0)->get_stp_node());
    children.push_back(std::static_pointer_cast<StpTerm>(t1)->get_stp_node());
    children.push_back(std::static_pointer_cast<StpTerm>(t2)->get_stp_node());
    if (t0->get_sort() != t1->get_sort() || t0->get_sort() != t2->get_sort())
    {
        throw IncorrectUsageException("Sorts of terms do not match");
    }
    if (t0->get_sort()->get_sort_kind() == BV || t0->get_sort()->get_sort_kind() == ARRAY)
    {
        ASTNode* node = stp_interface->newNode(kind, t0->get_sort()->get_width(), children);
        return std::make_shared<StpTerm>(*node, t0->get_sort());
    }
    ASTNode node = stp_interface->CreateNode(kind, children);
    return std::make_shared<StpTerm>(node, t0->get_sort());
}

Term StpSolver::make_term(const Op op, const TermVec & terms) const
{
    if (!primop2kind.count(op.prim_op))
    {
        return Term();
    }
    stp::Kind kind = primop2kind.at(op.prim_op);
    stp::ASTVec children;
    for (const auto & t : terms)
    {
        children.push_back(std::static_pointer_cast<StpTerm>(t)->get_stp_node());
    }
    if (terms.size() == 0)
    {
        throw IncorrectUsageException("Can't create term with no children");
    }
    else if (terms[0]->get_sort()->get_sort_kind() == BV || terms[0]->get_sort()->get_sort_kind() == ARRAY)
    {
        ASTNode* node = stp_interface->newNode(kind, terms[0]->get_sort()->get_width(), children);
        return std::make_shared<StpTerm>(*node, terms[0]->get_sort());
    }
    else
    {
        ASTNode node = stp_interface->CreateNode(kind, children);
        return std::make_shared<StpTerm>(node, terms[0]->get_sort());
    }
}

// Reset methods
void StpSolver::reset()
{
    stp_interface->reset();
    context_level = 0;
}

void StpSolver::reset_assertions()
{
    throw std::runtime_error("Not implemented");
}

DatatypeDecl StpSolver::make_datatype_decl(const std::string & s)
{
    throw std::runtime_error("STP does not support datatypes.");
}

DatatypeConstructorDecl StpSolver::make_datatype_constructor_decl(const std ::string s)
{
    throw std::runtime_error("STP does not support datatypes.");
}

void StpSolver::add_constructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const {
    throw std::runtime_error("STP does not support datatypes.");
}

void StpSolver::add_selector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const {
    throw std::runtime_error("STP does not support datatypes.");
}

void StpSolver::add_selector_self(DatatypeConstructorDecl & dt, const std::string & name) const {
    throw std::runtime_error("STP does not support datatypes.");
}

Term StpSolver::get_constructor(const Sort & s, std::string name) const {
    throw std::runtime_error("STP does not support datatypes.");
}

Term StpSolver::get_tester(const Sort & s, std::string name) const {
    throw std::runtime_error("STP does not support datatypes.");
}

Term StpSolver::get_selector(const Sort & s, std::string con, std::string name) const {
    throw std::runtime_error("STP does not support datatypes.");
}

} // namespace smt