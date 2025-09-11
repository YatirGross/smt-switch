#include <limits>
#include <unordered_map>
#include <string>
#include <iostream>

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
    // Note: Distinct is handled specially in make_term methods

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
    {Repeat, exprkind_t::BVCONCAT},  // Repeat will be implemented using concat
    {Sign_Extend, exprkind_t::BVCONCAT},  // Sign_Extend will be implemented using concat
    {Rotate_Left, exprkind_t::BVCONCAT},  // Rotate_Left will be implemented using extract and concat
    {Rotate_Right, exprkind_t::BVCONCAT},  // Rotate_Right will be implemented using extract and concat
    {BVShl, exprkind_t::BVLEFTSHIFT},
    {BVLshr, exprkind_t::BVRIGHTSHIFT},
    {BVAshr, exprkind_t::BVSRSHIFT},

    /* Arithmetic Operations */
    {BVAdd, exprkind_t::BVPLUS},
    {BVSub, exprkind_t::BVSUB},
    {BVMul, exprkind_t::BVMULT},
    {BVUdiv, exprkind_t::BVDIV},
    {BVSdiv, exprkind_t::SBVDIV},
    {BVUrem, exprkind_t::BVMOD},  // Note: STP doesn't have separate UREM, uses BVMOD
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
    symbol_table.clear();  // Clear symbol table first to avoid dangling references
    vc_Destroy(vc);
}

// Solver configuration
void StpSolver::set_opt(const std::string option, const std::string value)
{
    if (option == "produce-models") {
        if (value == "true") {
            vc_setFlag(vc, 'd');  // Enable counterexample generation
        }
    }
    else if (option == "incremental") {
        if (value == "true") {
            // STP is always incremental
            return;
        }
    }
    else if (option == "produce-unsat-assumptions") {
        if (value == "true") {
            // STP doesn't support unsat assumptions
            throw NotImplementedException("STP does not support unsat assumptions");
        }
    }
    else {
        throw NotImplementedException("STP does not support option: " + option);
    }
}

void StpSolver::set_logic(const std::string logic)
{
    if (logic != "QF_BV" && logic != "QF_ABV") {
        throw IncorrectUsageException("STP does not support logic " + logic +
            ". only QF_BV and QF_ABV are supported");
    }
}

// Assertions and satisfiability checking
void StpSolver::assert_formula(const Term & t)
{
    try {
        Expr e = std::static_pointer_cast<StpTerm>(t)->expr;
        if (!e) {
            throw InternalSolverException("Invalid expression in assert_formula");
        }
        vc_assertFormula(vc, e);
    }
    catch (const std::exception &e) {
        throw InternalSolverException(e.what());
    }
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
    // STP doesn't support direct assumption checking
    // So we need to simulate it by pushing a context, asserting assumptions,
    // checking satisfiability, and then popping context
    
    // Push a new context to save the current state
    push(1);
    
    // Create a conjunction of all assumptions
    Expr assumption_expr = vc_trueExpr(vc);
    for (const auto & a : assumptions) {
        Expr e = std::static_pointer_cast<StpTerm>(a)->expr;
        assumption_expr = vc_andExpr(vc, assumption_expr, e);
    }
    
    // Assert the conjunction
    vc_assertFormula(vc, assumption_expr);
    
    // Check satisfiability
    Result r = check_sat();
    
    // Pop the context to restore previous state
    pop(1);
    
    return r;
}

Result StpSolver::check_sat_assuming_list(const TermList & assumptions)
{
    // Convert TermList to TermVec for the existing implementation
    TermVec assumption_vec;
    assumption_vec.reserve(assumptions.size());
    
    for (const auto & a : assumptions) {
        assumption_vec.push_back(a);
    }
    
    // Use the existing implementation
    return check_sat_assuming(assumption_vec);
}

Result StpSolver::check_sat_assuming_set(const UnorderedTermSet & assumptions)
{
    // Convert UnorderedTermSet to TermVec for the existing implementation
    TermVec assumption_vec;
    assumption_vec.reserve(assumptions.size());
    
    for (const auto & a : assumptions) {
        assumption_vec.push_back(a);
    }
    
    // Use the existing implementation
    return check_sat_assuming(assumption_vec);
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
    UnorderedTermMap assignments;
    out_const_base = nullptr;
    
    if (!arr) {
        throw InternalSolverException("Null term in get_array_values");
    }
    
    // Get the array expression
    Expr array_expr = nullptr;
    try {
        array_expr = std::static_pointer_cast<StpTerm>(arr)->expr;
    } catch (const std::exception& e) {
        throw InternalSolverException(std::string("Error getting array expression: ") + e.what());
    }
    
    if (!array_expr) {
        throw InternalSolverException("Null array expression in get_array_values");
    }
    
    // Get array type information
    Type array_type = nullptr;
    int index_width = 0;
    int value_width = 0;
    
    try {
        array_type = vc_getType(vc, array_expr);
        
        if (!array_type) {
            throw InternalSolverException("Could not get array type");
        }
        
        index_width = vc_getIndexSize(vc, array_type);
        value_width = vc_getValueSize(vc, array_type);
    } catch (const std::exception& e) {
        throw InternalSolverException(std::string("Error getting array type info: ") + e.what());
    }

    // Get the array value from the model
    Expr array_val = vc_getCounterExample(vc, array_expr);    
    if (!array_val) {
        throw InternalSolverException("Could not get array value from model");
    }

    // Get all indices and values from the model
    Expr* indices = nullptr;
    Expr* values = nullptr;
    int size = 0;
    
    try {
        vc_getCounterExampleArray(vc, array_expr, &indices, &values, &size);

        if (size > 0 && indices && values) {
            // First pass: look for constant base by checking if all values are equal
            bool is_const_base = true;
            Expr first_value = values[0];
            
            for (int i = 1; i < size; i++) {
                if (values[i] != first_value) {
                    is_const_base = false;
                    break;
                }
            }
            
            if (is_const_base && first_value) {
                out_const_base = std::make_shared<StpTerm>(first_value, vc);
            }
            
            // Second pass: get all index-value pairs
            for (int i = 0; i < size; i++) {
                if (indices[i] && values[i]) {
                    // Get the actual value of the index from the model
                    Expr index_val = vc_getCounterExample(vc, indices[i]);
                    if (!index_val) {
                        continue;
                    }
                    
                    // Get the actual value from the model
                    Expr value_val = vc_getCounterExample(vc, values[i]);
                    if (!value_val) {
                        continue;
                    }

                    Term index_term = std::make_shared<StpTerm>(index_val, vc);
                    Term value_term = std::make_shared<StpTerm>(value_val, vc);
                    
                    if (index_term && value_term) {
                        assignments[index_term] = value_term;
                    }
                }
            }
        }

    } catch (const std::exception& e) {
        // Make sure to free memory even if an exception occurs
        if (indices) free(indices);
        if (values) free(values);
        throw InternalSolverException(std::string("Error getting array values: ") + e.what());
    }

    // Free memory in normal case
    if (indices) free(indices);
    if (values) free(values);
    
    return assignments;
}

void StpSolver::get_unsat_assumptions(UnorderedTermSet & out)
{
    // STP doesn't support unsat assumptions
    throw NotImplementedException("STP does not support unsat assumptions");
}

// Sort creation methods
Sort StpSolver::make_sort(const std::string name, uint64_t arity) const
{
    throw NotImplementedException("STP does not support uninterpreted sorts");
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
    throw NotImplementedException("STP does not support sorts that take one sort parameter");
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
    throw NotImplementedException("STP does not support sorts that take three sort parameters");
}

Sort StpSolver::make_sort(const SortKind sk, const SortVec & sorts) const
{
    throw NotImplementedException("STP does not support sorts that take multiple sort parameters");
}

Sort StpSolver::make_sort(const Sort & sort_con, const SortVec & sorts) const
{
    throw NotImplementedException("STP does not support sort constructors");
}

Sort StpSolver::make_sort(const DatatypeDecl & d) const
{
    throw NotImplementedException("STP does not support datatypes");
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
    if (sort->get_sort_kind() == BV) {
        Type t = std::static_pointer_cast<StpSort>(sort)->type;
        int width = vc_getValueSize(vc, t);
        
        unsigned long long val;
        if (i < 0) {
            // Calculate two's complement for negative values
            // For a negative number -n in width w: 2^w - n
            unsigned long long max_val = 1ULL << width;  // 2^width
            val = max_val + i;  // Since i is negative, this is subtraction
        } else {
            val = static_cast<unsigned long long>(i);
        }
        
        Expr e = vc_bvConstExprFromLL(vc, width, val);
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
        else if (base == 16) {
            // Expect val to be a hexadecimal string (e.g., "FF" for 8-bit 0xFF)
            // Convert it to a binary string because STP provides a binary helper.
            std::string bin;
            bin.reserve(val.size() * 4);
            for (char c : val) {
                switch (toupper(c)) {
                    case '0': bin.append("0000"); break;
                    case '1': bin.append("0001"); break;
                    case '2': bin.append("0010"); break;
                    case '3': bin.append("0011"); break;
                    case '4': bin.append("0100"); break;
                    case '5': bin.append("0101"); break;
                    case '6': bin.append("0110"); break;
                    case '7': bin.append("0111"); break;
                    case '8': bin.append("1000"); break;
                    case '9': bin.append("1001"); break;
                    case 'A': bin.append("1010"); break;
                    case 'B': bin.append("1011"); break;
                    case 'C': bin.append("1100"); break;
                    case 'D': bin.append("1101"); break;
                    case 'E': bin.append("1110"); break;
                    case 'F': bin.append("1111"); break;
                    default:
                        throw IncorrectUsageException("Invalid hex digit in bit-vector constant: " + std::string(1, c));
                }
            }
            // Trim or pad to the exact bit-width of the sort.
            int width = vc_getValueSize(vc, std::static_pointer_cast<StpSort>(sort)->type);
            if ((int)bin.size() > width) {
                // Keep the least-significant bits (rightmost)
                bin = bin.substr(bin.size() - width);
            } else if ((int)bin.size() < width) {
                bin.insert(0, width - bin.size(), '0');
            }
            Expr e = vc_bvConstExprFromStr(vc, bin.c_str());
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
    if (!val || !sort) {
        throw InternalSolverException("Null term or sort in make_term");
    }
    
    if (sort->get_sort_kind() == ARRAY) {
        Expr value = nullptr;
        try {
            value = std::static_pointer_cast<StpTerm>(val)->expr;
            if (!value) {
                throw InternalSolverException("Null value expression in constant array creation");
            }
        } catch (const std::exception& e) {
            throw InternalSolverException(std::string("Error getting value expression: ") + e.what());
        }
        
        Type array_type = nullptr;
        int index_width = 0;
        int value_width = 0;
        
        try {
            array_type = std::static_pointer_cast<StpSort>(sort)->type;
            if (!array_type) {
                throw InternalSolverException("Null array type in constant array creation");
            }
            
            index_width = vc_getIndexSize(vc, array_type);
            value_width = vc_getValueSize(vc, array_type);
        } catch (const std::exception& e) {
            throw InternalSolverException(std::string("Error getting array type info: ") + e.what());
        }

        // Create a simpler approach for constant arrays
        // This is less likely to cause segfaults
        
        try {
            // Create a fresh array symbol
            char buffer[64];
            static int id = 0;
            sprintf(buffer, "__const_array_%d", id++);
            
            // Create the array variable
            Expr array_var = vc_varExpr(vc, buffer, array_type);
            if (!array_var) {
                throw InternalSolverException("Failed to create array variable");
            }
            
            // Create a default index
            Expr idx = vc_bvConstExprFromInt(vc, index_width, 0);
            if (!idx) {
                throw InternalSolverException("Failed to create default index");
            }
            
            // Write the value to the array at the default index
            Expr write_expr = vc_writeExpr(vc, array_var, idx, value);
            if (!write_expr) {
                throw InternalSolverException("Failed to create write expression");
            }
            
            return std::make_shared<StpTerm>(write_expr, vc);
        } catch (const std::exception& e) {
            throw InternalSolverException(std::string("Error creating constant array: ") + e.what());
        }
    }
    else {
        throw IncorrectUsageException("Unsupported sort for creating a term from a term value");
    }
}

Term StpSolver::make_symbol(const std::string name, const Sort & sort)
{
    // Check if symbol already exists
    auto it = symbol_table.find(name);
    if (it != symbol_table.end()) {
        throw IncorrectUsageException("Symbol '" + name + "' already exists");
    }
    
    Type t = std::static_pointer_cast<StpSort>(sort)->type;
    Expr e = vc_varExpr(vc, name.c_str(), t);
    Term symbol = std::make_shared<StpTerm>(e, vc);
    
    // Store in symbol table
    symbol_table[name] = symbol;
    
    return symbol;
}

Term StpSolver::get_symbol(const std::string & name)
{
    auto it = symbol_table.find(name);
    if (it != symbol_table.end()) {
        return it->second;
    }
    throw IncorrectUsageException("Symbol '" + name + "' not found");
}

Term StpSolver::make_param(const std::string name, const Sort & sort)
{
    // STP doesn't support parameters
    throw NotImplementedException("STP does not support parameters");
}

// Operator handling (terms with operations)
Term StpSolver::make_term(const Op op, const Term & t) const
{
    // Special handling for Extract operation
    if (op.prim_op == Extract) {
        Expr e = std::static_pointer_cast<StpTerm>(t)->expr;
        uint64_t high = op.idx0;
        uint64_t low = op.idx1;
        return std::make_shared<StpTerm>(vc_bvExtract(vc, e, high, low), vc);
    }
    
    // Special handling for Repeat operation
    if (op.prim_op == Repeat) {
        if (op.idx0 < 1) {
            throw IncorrectUsageException("Can't create repeat with index < 1");
        }
        Expr e = std::static_pointer_cast<StpTerm>(t)->expr;
        Expr result = e;
        for (uint64_t i = 1; i < op.idx0; i++) {
            result = vc_bvConcatExpr(vc, e, result);
        }
        return std::make_shared<StpTerm>(result, vc);
    }
    
    // Special handling for Sign_Extend operation
    if (op.prim_op == Sign_Extend) {
        if (op.idx0 < 0) {
            throw IncorrectUsageException("Can't sign extend by negative number");
        }
        if (op.idx0 == 0) {
            return t;  // No extension needed
        }
        Expr e = std::static_pointer_cast<StpTerm>(t)->expr;
        // Get the width of the input bitvector
        Type input_type = vc_getType(vc, e);
        int width = vc_getValueSize(vc, input_type);
        // Get the most significant bit (sign bit)
        Expr sign_bit = vc_bvExtract(vc, e, width - 1, width - 1);  // Extract MSB
        // Create a bitvector of all sign bits
        Expr sign_bits = sign_bit;
        for (uint64_t i = 1; i < op.idx0; i++) {
            sign_bits = vc_bvConcatExpr(vc, sign_bit, sign_bits);
        }
        // Concatenate sign bits with original expression
        Expr result = vc_bvConcatExpr(vc, sign_bits, e);
        return std::make_shared<StpTerm>(result, vc);
    }
    
    // Special handling for Rotate_Left operation
    if (op.prim_op == Rotate_Left) {
        if (op.idx0 < 0) {
            throw IncorrectUsageException("Can't rotate by negative number");
        }
        Expr e = std::static_pointer_cast<StpTerm>(t)->expr;
        // Get the width of the input bitvector
        Type input_type = vc_getType(vc, e);
        int width = vc_getValueSize(vc, input_type);
        
        if (op.idx0 == 0 || width == 1) {
            return t;  // No rotation needed
        }
        
        // Rotate left by n: extract top n bits and bottom bits, then concat
        uint64_t n = op.idx0 % width;  // Handle rotation amounts >= width
        if (n == 0) {
            return t;  // No rotation needed
        }
        
        // Extract top n bits: [width-1 : width-n]
        Expr top_bits = vc_bvExtract(vc, e, width - 1, width - n);
        // Extract bottom bits: [width-n-1 : 0]
        Expr bottom_bits = vc_bvExtract(vc, e, width - n - 1, 0);
        // Concat: bottom_bits ++ top_bits
        Expr result = vc_bvConcatExpr(vc, bottom_bits, top_bits);
        return std::make_shared<StpTerm>(result, vc);
    }
    
    // Special handling for Rotate_Right operation
    if (op.prim_op == Rotate_Right) {
        if (op.idx0 < 0) {
            throw IncorrectUsageException("Can't rotate by negative number");
        }
        Expr e = std::static_pointer_cast<StpTerm>(t)->expr;
        // Get the width of the input bitvector
        Type input_type = vc_getType(vc, e);
        int width = vc_getValueSize(vc, input_type);
        
        if (op.idx0 == 0 || width == 1) {
            return t;  // No rotation needed
        }
        
        // Rotate right by n: extract top bits and bottom n bits, then concat
        uint64_t n = op.idx0 % width;  // Handle rotation amounts >= width
        if (n == 0) {
            return t;  // No rotation needed
        }
        
        // Extract top bits: [width-1 : n]
        Expr top_bits = vc_bvExtract(vc, e, width - 1, n);
        // Extract bottom n bits: [n-1 : 0]
        Expr bottom_n_bits = vc_bvExtract(vc, e, n - 1, 0);
        // Concat: bottom_n_bits ++ top_bits
        Expr result = vc_bvConcatExpr(vc, bottom_n_bits, top_bits);
        return std::make_shared<StpTerm>(result, vc);
    }
    
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
    if (op.prim_op == Select) {
        if (!t0 || !t1) {
            throw InternalSolverException("Null terms in array select operation");
        }
        
        Expr array = nullptr;
        Expr index = nullptr;
        
        try {
            array = std::static_pointer_cast<StpTerm>(t0)->expr;
            index = std::static_pointer_cast<StpTerm>(t1)->expr;
            
            if (!array || !index) {
                throw InternalSolverException("Null expression in array select operation");
            }
            
            Expr result = vc_readExpr(vc, array, index);
            if (!result) {
                throw InternalSolverException("Null result from array select operation");
            }
            
            return std::make_shared<StpTerm>(result, vc);
        } catch (const std::exception& e) {
            throw InternalSolverException(std::string("Error in array select operation: ") + e.what());
        }
    }
    
    // Special handling for Distinct - implement as NOT(EQ(...))
    if (op.prim_op == Distinct) {
        Expr e0 = std::static_pointer_cast<StpTerm>(t0)->expr;
        Expr e1 = std::static_pointer_cast<StpTerm>(t1)->expr;
        
        // Check if both are boolean - use NOT(IFF) for booleans
        if (t0->get_sort()->get_sort_kind() == BOOL && t1->get_sort()->get_sort_kind() == BOOL) {
            Expr iff_expr = vc_iffExpr(vc, e0, e1);
            return std::make_shared<StpTerm>(vc_notExpr(vc, iff_expr), vc);
        } else {
            // For non-boolean types, use NOT(EQ)
            Expr eq_expr = vc_eqExpr(vc, e0, e1);
            return std::make_shared<StpTerm>(vc_notExpr(vc, eq_expr), vc);
        }
    }
    
    // Special handling for Equal - use IFF for booleans, EQ for others
    if (op.prim_op == Equal) {
        Expr e0 = std::static_pointer_cast<StpTerm>(t0)->expr;
        Expr e1 = std::static_pointer_cast<StpTerm>(t1)->expr;
        
        // Check if both are boolean - use IFF for booleans
        if (t0->get_sort()->get_sort_kind() == BOOL && t1->get_sort()->get_sort_kind() == BOOL) {
            return std::make_shared<StpTerm>(vc_iffExpr(vc, e0, e1), vc);
        } else {
            // For non-boolean types (including arrays), use standard equality
            return std::make_shared<StpTerm>(vc_eqExpr(vc, e0, e1), vc);
        }
    }
    
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
    if (op.prim_op == Store) {
        if (!t0 || !t1 || !t2) {
            throw InternalSolverException("Null terms in array store operation");
        }
        
        Expr array = nullptr;
        Expr index = nullptr;
        Expr value = nullptr;
        
        try {
            array = std::static_pointer_cast<StpTerm>(t0)->expr;
            index = std::static_pointer_cast<StpTerm>(t1)->expr;
            value = std::static_pointer_cast<StpTerm>(t2)->expr;
            
            if (!array || !index || !value) {
                throw InternalSolverException("Null expression in array store operation");
            }
            
            Expr result = vc_writeExpr(vc, array, index, value);
            if (!result) {
                throw InternalSolverException("Null result from array store operation");
            }
            
            return std::make_shared<StpTerm>(result, vc);
        } catch (const std::exception& e) {
            throw InternalSolverException(std::string("Error in array store operation: ") + e.what());
        }
    }
    
    // Handle n-ary operations for exactly 3 arguments
    if (op.prim_op == And) {
        Expr e0 = std::static_pointer_cast<StpTerm>(t0)->expr;
        Expr e1 = std::static_pointer_cast<StpTerm>(t1)->expr;
        Expr e2 = std::static_pointer_cast<StpTerm>(t2)->expr;
        Expr exprs[3] = {e0, e1, e2};
        Expr result = vc_andExprN(vc, exprs, 3);
        return std::make_shared<StpTerm>(result, vc);
    }
    
    if (op.prim_op == Or) {
        Expr e0 = std::static_pointer_cast<StpTerm>(t0)->expr;
        Expr e1 = std::static_pointer_cast<StpTerm>(t1)->expr;
        Expr e2 = std::static_pointer_cast<StpTerm>(t2)->expr;
        Expr exprs[3] = {e0, e1, e2};
        Expr result = vc_orExprN(vc, exprs, 3);
        return std::make_shared<StpTerm>(result, vc);
    }
    
    if (op.prim_op == BVAdd) {
        Expr e0 = std::static_pointer_cast<StpTerm>(t0)->expr;
        Expr e1 = std::static_pointer_cast<StpTerm>(t1)->expr;
        Expr e2 = std::static_pointer_cast<StpTerm>(t2)->expr;
        Sort sort = t0->get_sort();
        uint64_t width = sort->get_width();
        Expr exprs[3] = {e0, e1, e2};
        Expr result = vc_bvPlusExprN(vc, width, exprs, 3);
        return std::make_shared<StpTerm>(result, vc);
    }
    
    if (op.prim_op == Xor) {
        Expr e0 = std::static_pointer_cast<StpTerm>(t0)->expr;
        Expr e1 = std::static_pointer_cast<StpTerm>(t1)->expr;
        Expr e2 = std::static_pointer_cast<StpTerm>(t2)->expr;
        Expr result = vc_xorExpr(vc, e0, vc_xorExpr(vc, e1, e2));
        return std::make_shared<StpTerm>(result, vc);
    }

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
        case exprkind_t::ITE:
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
            // Handle n-ary operations for operators that support it
            if (op.prim_op == And || op.prim_op == Or || op.prim_op == BVAdd || op.prim_op == Xor) {
                // Convert terms to STP expressions
                std::vector<Expr> exprs;
                exprs.reserve(terms.size());
                for (const auto & term : terms) {
                    if (!term) {
                        throw InternalSolverException("Null term in make_term");
                    }
                    exprs.push_back(std::static_pointer_cast<StpTerm>(term)->expr);
                }
                
                Expr result = nullptr;
                if (op.prim_op == And) {
                    // Use the n-ary AND operation
                    result = vc_andExprN(vc, exprs.data(), exprs.size());
                } else if (op.prim_op == Or) {
                    // Use the n-ary OR operation
                    result = vc_orExprN(vc, exprs.data(), exprs.size());
                } else if (op.prim_op == Xor) {
                    // Use the n-ary XOR operation
                    result = vc_xorExpr(vc, exprs[0], exprs[1]);
                    for (size_t i = 2; i < exprs.size(); ++i) {
                        result = vc_xorExpr(vc, result, exprs[i]);
                    }
                } else if (op.prim_op == BVAdd) {
                    // Get bit-width from the first term's sort
                    Sort sort = terms[0]->get_sort();
                    uint64_t width = sort->get_width();
                    
                    // Use the n-ary BVAdd operation
                    result = vc_bvPlusExprN(vc, width, exprs.data(), exprs.size());
                }
                
                if (!result) {
                    throw InternalSolverException("Failed to create n-ary term");
                }
                
                return std::make_shared<StpTerm>(result, vc);
            }
            std::cout << "the op is " << op.prim_op << std::endl;
            std::cout << "the terms size is " << terms.size() << std::endl;
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
    symbol_table.clear();  // Clear the symbol table
}

void StpSolver::reset_assertions()
{
    // Pop all contexts
    while (context_level > 0) {
        vc_pop(vc);
        --context_level;
    }
    
    // Create new validity checker
    vc_Destroy(vc);
    vc = vc_createValidityChecker();
    symbol_table.clear();  // Clear the symbol table
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