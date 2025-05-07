#include <limits>
#include <unordered_map>
#include <string>

#include "stp/c_interface.h"
#include "stp_solver.h"


namespace smt {

const std::unordered_map<PrimOp, exprkind_t> primop2kind( {
    /* Logical Operations */
    {And, exprkind_t::AND},
    {Or, exprkind_t::OR},
    {Xor, exprkind_t::XOR},
    {Not, exprkind_t::NOT},
    {Implies, exprkind_t::IMPLIES},
    {Ite, exprkind_t::ITE},
    {Equal, exprkind_t::EQ},

    /* Bitwise Operations */
    {BVNot, exprkind_t::BVNOT},
    {BVAnd, exprkind_t::BVAND},
    {BVOr, exprkind_t::BVOR},
    {BVXor, exprkind_t::BVXOR},
    {BVNand, exprkind_t::BVNAND},
    {BVNor, exprkind_t::BVNOR},
    {BVXnor, exprkind_t::BVXNOR},

    /* Bitvector Manipulation */
    {Concat, exprkind_t::BVCONCAT},
    {Extract, exprkind_t::BVEXTRACT},
    {BVShl, exprkind_t::BVLEFTSHIFT},
    {BVLshr, exprkind_t::BVRIGHTSHIFT},
    {BVAshr, exprkind_t::BVSRSHIFT},

    /* Arithmetic Operations */
    {BVAdd, exprkind_t::BVPLUS},
    {BVSub, exprkind_t::BVSUB},
    {BVMul, exprkind_t::BVMULT},
    {BVUdiv, exprkind_t::BVDIV},
    {BVSdiv, exprkind_t::SBVDIV},
    {BVSrem, exprkind_t::SBVREM},
    {BVSmod, exprkind_t::SBVMOD},
    
    /* Comparison Operators (Unsigned & Signed) */
    {BVUlt, exprkind_t::BVLT},
    {BVUle, exprkind_t::BVLE},
    {BVUgt, exprkind_t::BVGT},
    {BVUge, exprkind_t::BVGE},
    {BVSlt, exprkind_t::BVSLT},
    {BVSle, exprkind_t::BVSLE},
    {BVSgt, exprkind_t::BVSGT},
    {BVSge, exprkind_t::BVSGE} }
);

// Constructor
StpSolver::StpSolver() : AbsSmtSolver(STP)
{
    vc = vc_createValidityChecker();
    // vc_setFlag(vc, 'd');
    context_level = 0;
}

// Destructor
StpSolver::~StpSolver()
{
    vc_Destroy(vc);
}

// Solver configuration
void StpSolver::set_opt(const std::string option, const std::string value)
{
    std::cout << "STP does not support setting options" << std::endl;
}

void StpSolver::set_logic(const std::string logic)
{
    if ( logic != "QF_BV" && logic != "QF_ABV") {
        throw IncorrectUsageException("STP does not support logic " + logic +
            ". only QF_BV and QF_ABV are supported");
    }
}

// Assertions and satisfiability checking
void StpSolver::assert_formula(const Term & t)
{
    vc_assertFormula(vc, std::static_pointer_cast<StpTerm>(t)->expr);
}

Result StpSolver::check_sat()
{
    int res = vc_query(vc, vc_falseExpr(vc));
    if (res == 0)
    {
        return Result(SAT);
    }
    else if (res == 1)
    {
        return Result(UNSAT);
    }
    else
    {
        return Result(UNKNOWN);
    }
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
            vc_push(vc);
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
            vc_pop(vc);
            if (context_level == 0)
            {
                throw IncorrectUsageException("Context level cannot be negative");
            }
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
    Expr e = std::static_pointer_cast<StpTerm>(t)->expr;
    Expr e_val = vc_getCounterExample(vc, e);
    return std::make_shared<StpTerm>(e_val, vc);
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
        Type t = vc_boolType(vc);
        return std::make_shared<StpSort>(t, vc);
    }
    else {
        std::string msg("Can't create sort with sort constructor ");
        msg += to_string(sk);
        throw IncorrectUsageException(msg.c_str());
    }
}

Sort StpSolver::make_sort(const SortKind sk, uint64_t size) const
{
    if (sk == BV) {
        Type t = vc_bvType(vc, size);
        return std::make_shared<StpSort>(t, vc);
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
        Type t = vc_arrayType(vc, std::static_pointer_cast<StpSort>(sort1)->type, std::static_pointer_cast<StpSort>(sort2)->type);
        return std::make_shared<StpSort>(t, vc);
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
    throw std::runtime_error("Not implemented");
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
    if (b) {
        return std::make_shared<StpTerm>(vc_trueExpr(vc), vc);
    }
    else {
        return std::make_shared<StpTerm>(vc_falseExpr(vc), vc);
    }
}

Term StpSolver::make_term(int64_t i, const Sort & sort) const
{
    if (i < 0) {
        throw IncorrectUsageException("Integer value out of bounds");
    }
    if (sort->get_sort_kind() == BV) {
        Type t = std::static_pointer_cast<StpSort>(sort)->type;
        int width = vc_getValueSize(vc, t);
        unsigned long long val = static_cast<unsigned long long>(i);
        Expr e = vc_bvConstExprFromLL(vc, width, i);
        return std::make_shared<StpTerm>(e, vc);
    }
    else {
        throw IncorrectUsageException("Unsupported sort for creating a term from an integer value");
    }
}

Term StpSolver::make_term(const std::string val, const Sort & sort, uint64_t base) const
{
    if (sort->get_sort_kind() == BV) {
        Type t = std::static_pointer_cast<StpSort>(sort)->type;
        if (base == 10) {
            int width = vc_getValueSize(vc, t);
            Expr e = vc_bvConstExprFromDecStr(vc, width, val.c_str());
            return std::make_shared<StpTerm>(e, vc);
        }
        else if (base == 2) {
            Expr e = vc_bvConstExprFromStr(vc, val.c_str());
            return std::make_shared<StpTerm>(e, vc);
        }
        else {
            throw IncorrectUsageException("Unsupported base for creating a term from a string value");
        }
    }
    else {
        throw IncorrectUsageException("Unsupported sort for creating a term from a string value");
    }
}

Term StpSolver::make_term(const Term & val, const Sort & sort) const
{
    if (sort->get_sort_kind() == ARRAY) {
        Expr value = std::static_pointer_cast<StpTerm>(val)->expr;
        Type array_type = std::static_pointer_cast<StpSort>(sort)->type;
        int index_width = vc_getIndexSize(vc, array_type);
        unsigned long long num_indices = 1 << index_width;

        // Create an initial array expression with the first index
        Expr index = vc_bvConstExprFromLL(vc, index_width, 0);
        Expr array = vc_writeExpr(vc, vc_varExpr(vc, "initial_array", array_type), index, value);

        for (unsigned long long i = 0; i < num_indices; ++i) {
            index = vc_bvConstExprFromLL(vc, index_width, i);
            array = vc_writeExpr(vc, array, index, value);
        }
        return std::make_shared<StpTerm>(array, vc);
    }
    else {
        throw IncorrectUsageException("Unsupported sort for creating a term from a term value");
    }
}

Term StpSolver::make_symbol(const std::string name, const Sort & sort)
{
    Expr e = vc_varExpr(vc, name.c_str(), std::static_pointer_cast<StpSort>(sort)->type);
    return std::make_shared<StpTerm>(e, vc);
}

Term StpSolver::get_symbol(const std::string & name)
{
    throw std::runtime_error("Not implemented");
}

Term StpSolver::make_param(const std::string name, const Sort & sort)
{
    throw std::runtime_error("Not implemented");
}

// Operator handling (terms with operations)
Term StpSolver::make_term(const Op op, const Term & t) const
{
    if (!primop2kind.count(op.prim_op))
    {
        return Term();
    }
    enum exprkind_t kind = primop2kind.at(op.prim_op);
    Expr e = std::static_pointer_cast<StpTerm>(t)->expr;
    switch (kind)
    {
        case exprkind_t::NOT:
            return std::make_shared<StpTerm>(vc_notExpr(vc, e), vc);
        case exprkind_t::BVNOT:
            return std::make_shared<StpTerm>(vc_bvNotExpr(vc, e), vc);
        case exprkind_t::BVUMINUS:
            return std::make_shared<StpTerm>(vc_bvUMinusExpr(vc, e), vc);
        default:
            throw IncorrectUsageException("Unary operator not supported");
    }
}

Term StpSolver::make_term(const Op op, const Term & t0, const Term & t1) const
{
    if (!primop2kind.count(op.prim_op))
    {
        return Term();
    }
    enum exprkind_t kind = primop2kind.at(op.prim_op);
    Expr e0 = std::static_pointer_cast<StpTerm>(t0)->expr;
    Expr e1 = std::static_pointer_cast<StpTerm>(t1)->expr;
    int width = t0->get_sort()->get_width();
    switch (kind)
    {
        case exprkind_t::AND:
            return std::make_shared<StpTerm>(vc_andExpr(vc, e0, e1), vc);
        case exprkind_t::OR:
            return std::make_shared<StpTerm>(vc_orExpr(vc, e0, e1), vc);
        case exprkind_t::XOR:
            return std::make_shared<StpTerm>(vc_xorExpr(vc, e0, e1), vc);
        case exprkind_t::EQ:
            return std::make_shared<StpTerm>(vc_eqExpr(vc, e0, e1), vc);
        case exprkind_t::BVAND:
            return std::make_shared<StpTerm>(vc_bvAndExpr(vc, e0, e1), vc);
        case exprkind_t::BVOR:
            return std::make_shared<StpTerm>(vc_bvOrExpr(vc, e0, e1), vc);
        case exprkind_t::BVXOR:
            return std::make_shared<StpTerm>(vc_bvXorExpr(vc, e0, e1), vc);
        case exprkind_t::BVNAND:
            return std::make_shared<StpTerm>(vc_bvNotExpr(vc, vc_bvAndExpr(vc, e0, e1)), vc);
        case exprkind_t::BVNOR:
            return std::make_shared<StpTerm>(vc_bvNotExpr(vc, vc_bvOrExpr(vc, e0, e1)), vc);
        case exprkind_t::BVXNOR:
            return std::make_shared<StpTerm>(vc_bvNotExpr(vc, vc_bvXorExpr(vc, e0, e1)), vc);
        case exprkind_t::BVPLUS:
            return std::make_shared<StpTerm>(vc_bvPlusExpr(vc, width, e0, e1), vc);
        case exprkind_t::BVSUB:
            return std::make_shared<StpTerm>(vc_bvMinusExpr(vc, width, e0, e1), vc);
        case exprkind_t::BVMULT:
            return std::make_shared<StpTerm>(vc_bvMultExpr(vc, width, e0, e1), vc);
        case exprkind_t::BVDIV:
            return std::make_shared<StpTerm>(vc_bvDivExpr(vc, width, e0, e1), vc);
        case exprkind_t::SBVDIV:
            return std::make_shared<StpTerm>(vc_sbvDivExpr(vc, width, e0, e1), vc);
        case exprkind_t::BVMOD:
            return std::make_shared<StpTerm>(vc_bvModExpr(vc, width, e0, e1), vc);
        case exprkind_t::SBVMOD:
            return std::make_shared<StpTerm>(vc_sbvModExpr(vc, width, e0, e1), vc);
        case exprkind_t::SBVREM:
            return std::make_shared<StpTerm>(vc_sbvRemExpr(vc, width, e0, e1), vc);
        case exprkind_t::BVLT:
            return std::make_shared<StpTerm>(vc_bvLtExpr(vc, e0, e1), vc);
        case exprkind_t::BVLE:
            return std::make_shared<StpTerm>(vc_bvLeExpr(vc, e0, e1), vc);
        case exprkind_t::BVGT:
            return std::make_shared<StpTerm>(vc_bvGtExpr(vc, e0, e1), vc);
        case exprkind_t::BVGE:
            return std::make_shared<StpTerm>(vc_bvGeExpr(vc, e0, e1), vc);
        case exprkind_t::BVSLT:
            return std::make_shared<StpTerm>(vc_sbvLtExpr(vc, e0, e1), vc);
        case exprkind_t::BVSLE:
            return std::make_shared<StpTerm>(vc_sbvLeExpr(vc, e0, e1), vc);
        case exprkind_t::BVSGT:
            return std::make_shared<StpTerm>(vc_sbvGtExpr(vc, e0, e1), vc);
        case exprkind_t::BVSGE:
            return std::make_shared<StpTerm>(vc_sbvGeExpr(vc, e0, e1), vc);
        case exprkind_t::BVLEFTSHIFT:
            return std::make_shared<StpTerm>(vc_bvLeftShiftExprExpr(vc, width, e0, e1), vc);
        case exprkind_t::BVRIGHTSHIFT:
            return std::make_shared<StpTerm>(vc_bvRightShiftExprExpr(vc, width, e0, e1), vc);
        case exprkind_t::BVSRSHIFT:
            return std::make_shared<StpTerm>(vc_bvSignedRightShiftExprExpr(vc, width, e0, e1), vc);
        case exprkind_t::BVCONCAT:
            return std::make_shared<StpTerm>(vc_bvConcatExpr(vc, e0, e1), vc);
        case exprkind_t::IMPLIES:
            return std::make_shared<StpTerm>(vc_impliesExpr(vc, e0, e1), vc);
        default:
            throw IncorrectUsageException("Binary operator not supported");
    }
}

Term StpSolver::make_term(const Op op, const Term & t0, const Term & t1, const Term & t2) const
{
    if (!primop2kind.count(op.prim_op))
    {
        return Term();
    }
    enum exprkind_t kind = primop2kind.at(op.prim_op);
    Expr e0 = std::static_pointer_cast<StpTerm>(t0)->expr;
    Expr e1 = std::static_pointer_cast<StpTerm>(t1)->expr;
    Expr e2 = std::static_pointer_cast<StpTerm>(t2)->expr;
    switch (kind)
    {
        case ITE:
            return std::make_shared<StpTerm>(vc_iteExpr(vc, e0, e1, e2), vc);
        default:
            throw IncorrectUsageException("Ternary operator not supported");
    }
}

Term StpSolver::make_term(const Op op, const TermVec & terms) const
{
    switch (terms.size())
    {
        case 1:
            return make_term(op, terms[0]);
        case 2:
            return make_term(op, terms[0], terms[1]);
        case 3:
            return make_term(op, terms[0], terms[1], terms[2]);
        default:
            throw IncorrectUsageException("Too many terms for the given operator");
    }
}

// Reset methods
void StpSolver::reset()
{
    vc_Destroy(vc);
    vc = vc_createValidityChecker();
    vc_setFlag(vc, 'd');
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