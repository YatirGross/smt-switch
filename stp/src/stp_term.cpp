#include "stp_term.h"
#include "stp_solver.h"
#include "stp_sort.h"
#include <cstring>
#include <functional>
#include <iostream>

namespace smt {

// Helper function to normalize STP string representations for comparison
std::string normalize_stp_string(const char* str) {
  if (!str) return "";
  
  std::string result;
  result.reserve(strlen(str));
  
  for (const char* p = str; *p; ++p) {
    char c = *p;
    
    // Remove pipe delimiters around symbols (|a| -> a)
    if (c == '|') {
      continue;
    }
    
    // Skip all whitespace characters
    if (c == ' ' || c == '\t' || c == '\n' || c == '\r') {
      continue;
    }
    
    result += c;
  }
  
  return result;
}

const std::unordered_map<exprkind_t, PrimOp> type2primop({
    /* Logical Operations */
    {exprkind_t::AND, And},
    {exprkind_t::OR, Or},
    {exprkind_t::XOR, Xor},
    {exprkind_t::NOT, Not},
    {exprkind_t::IMPLIES, Implies},
    {exprkind_t::ITE, Ite},
    {exprkind_t::EQ, Equal},
    {exprkind_t::IFF, Equal},  // IFF is treated as Equal for reverse mapping
    // Note: Distinct is handled specially in STP solver and doesn't have direct mapping

    /* Bitwise Operations */
    {exprkind_t::BVNOT, BVNot},
    {exprkind_t::BVAND, BVAnd},
    {exprkind_t::BVOR, BVOr},
    {exprkind_t::BVXOR, BVXor},
    {exprkind_t::BVNAND, BVNand},
    {exprkind_t::BVNOR, BVNor},
    {exprkind_t::BVXNOR, BVXnor},

    /* Bitvector Manipulation */
    {exprkind_t::BVCONCAT, Concat},
    {exprkind_t::BVEXTRACT, Extract},
    // Note: Repeat, Sign_Extend, Rotate_Left, and Rotate_Right operations will be mapped to Concat in get_op() since they use concat internally
    {exprkind_t::BVLEFTSHIFT, BVShl},
    {exprkind_t::BVRIGHTSHIFT, BVLshr},
    {exprkind_t::BVSRSHIFT, BVAshr},

    /* Arithmetic Operations */
    {exprkind_t::BVPLUS, BVAdd},
    {exprkind_t::BVUMINUS, BVNeg},
    {exprkind_t::BVSUB, BVSub},
    {exprkind_t::BVMULT, BVMul},
    {exprkind_t::BVDIV, BVUdiv},
    {exprkind_t::BVMOD, BVUrem},  // Note: STP uses BVMOD for UREM
    {exprkind_t::SBVDIV, BVSdiv},
    {exprkind_t::SBVREM, BVSrem},
    {exprkind_t::SBVMOD, BVSmod},

    /* Comparison Operators (Unsigned & Signed) */
    {exprkind_t::BVLT, BVUlt},
    {exprkind_t::BVLE, BVUle},
    {exprkind_t::BVGT, BVUgt},
    {exprkind_t::BVGE, BVUge},
    {exprkind_t::BVSLT, BVSlt},
    {exprkind_t::BVSLE, BVSle},
    {exprkind_t::BVSGT, BVSgt},
    {exprkind_t::BVSGE, BVSge},
});


// StpTermIter Implementation

StpTermIter::StpTermIter(const StpTermIter & it) : expr(it.expr), pos(it.pos) {}

void StpTermIter::operator++()
{
  ++pos;
}

const Term StpTermIter::operator*()
{
  Expr e = getChild(expr, pos);
  return std::make_shared<StpTerm>(e, vc);
}

TermIterBase * StpTermIter::clone() const
{
  return new StpTermIter(expr, vc);
}

bool StpTermIter::operator==(const StpTermIter & it) const
{
  return equal(it);
}

bool StpTermIter::equal(const TermIterBase & other) const
{
  const StpTermIter & it = static_cast<const StpTermIter &>(other);
  return expr == it.expr && pos == it.pos;
}

// StpTerm Implementation

// NOTE: The hash must be compatible with the equality semantics implemented
// in StpTerm::compare.
// For STP, two distinct Expr pointers can denote syntactically equivalent
// (and thus equal) terms that live in different STP contexts or were created
// at different times.  Using the raw pointer (or even the STP‐assigned Expr
// id) as the hash therefore violates the requirement that equal objects have
// identical hash values.  This manifested in subtle cache misses in
// TermTranslator which relies on an unordered_map keyed by Terms.
//
// To restore the required invariant, we hash a canonicalised SMT-LIB string
// representation of the expression – the very same representation that is
// used by compare() for the equality check.  Although this is more
// expensive than hashing a pointer, the cost is acceptable because hashing
// only happens when Terms are inserted in hash-based containers.
std::size_t StpTerm::hash() const
{
  if (!expr)
  {
    // Consistent hash for null expressions
    return 0;
  }

  char * buf = nullptr;
  unsigned long len = 0;
  vc_printExprToBuffer(vc, expr, &buf, &len);

  std::string normalized;
  if (buf)
  {
    normalized = normalize_stp_string(buf);
    free(buf);
  }

  return std::hash<std::string>{}(normalized);
}

std::size_t StpTerm::get_id() const
{
  if (!expr) {
    // Return a consistent ID for null expressions
    return 0;
  }
  
  // Otherwise get the expression ID
  return getExprID(expr);
}

bool StpTerm::compare(const Term & absterm) const
{
  // First check if absterm is null
  if (!absterm) {
    return false;
  }
  
  try {
    const StpTerm * st = dynamic_cast<const StpTerm *>(absterm.get());
    
    // If dynamic_cast failed, the types don't match
    if (!st) {
      return false;
    }
    
    // Check if either expression is null
    if (!expr || !st->expr) {
      return expr == st->expr;  // Both null = equal, otherwise not equal
    }
    
    // Quick check: if they're the same expression object, they're equal
    if (expr == st->expr) {
      return true;
    }
    
    // Fast path: compare by expression IDs
    std::size_t id1 = getExprID(expr);
    std::size_t id2 = getExprID(st->expr);
    if (id1 == id2) {
      return true;
    }

    // Fall back to string comparison
    char* buf1 = nullptr;
    char* buf2 = nullptr;
    unsigned long len1 = 0, len2 = 0;
    
    vc_printExprToBuffer(vc, expr, &buf1, &len1);
    vc_printExprToBuffer(st->vc, st->expr, &buf2, &len2);
    
    bool result = false;
    if (buf1 && buf2) {
      std::string str1 = normalize_stp_string(buf1);
      std::string str2 = normalize_stp_string(buf2);
      result = (str1 == str2);
    }
    
    if (buf1) free(buf1);
    if (buf2) free(buf2);
    
    return result;
    
  }
  catch (const std::exception & e) {
    return false;
  }
}

Op StpTerm::get_op() const
{
  if (!expr)
  {
    return Op();
  }

  // Return stored Op for indexed operations
  if (stored_op.prim_op != NUM_OPS_AND_NULL) {
    return stored_op;
  }

  try
  {
    enum exprkind_t k = getExprKind(expr);
    auto it = type2primop.find(k);
    if (it != type2primop.end())
    {
      PrimOp po = it->second;
      return Op(po);
    }
    else
    {
      // Non-operator term (e.g. symbol or value).
      return Op();
    }
  }
  catch (const std::exception & e)
  {
    return Op();
  }
}

Sort StpTerm::get_sort() const
{
  if (!expr) {
    // For null expressions, we cannot determine the sort
    throw IncorrectUsageException("Cannot get sort of null expression");
  }

  try {
    Type t = vc_getType(vc, expr);
    if (!t) {
      throw IncorrectUsageException("Failed to get type of expression");
    }
    return std::make_shared<StpSort>(t, vc);
  } catch (const std::exception& e) {
    throw IncorrectUsageException(std::string("Error getting sort: ") + e.what());
  }
}

bool StpTerm::is_symbol() const
{
  if (!expr) {
    return false;
  }
  try {
    enum exprkind_t k = getExprKind(expr);
    return k == SYMBOL || k == PARAMBOOL;
  } catch (const std::exception& e) {
    return false;
  }
}

bool StpTerm::is_param() const
{
  if (!expr) {
    return false;
  }
  try {
    return getExprKind(expr) == PARAMBOOL;
  } catch (const std::exception& e) {
    return false;
  }
}

bool StpTerm::is_symbolic_const() const
{
  return is_symbol();
}

bool StpTerm::is_value() const
{
  if (!expr) {
    return false;
  }
  try {
    enum exprkind_t k = getExprKind(expr);
    // TRUE and FALSE are also values, not compound terms with operators
    return k == BVCONST || k == BOOLEAN || k == TRUE || k == FALSE;
  } catch (const std::exception& e) {
    return false;
  }
}

std::string StpTerm::to_string()
{
  if (!expr) {
    return "null";
  }
  
  try {
    // Check if this is a TRUE or FALSE expression and handle specially
    enum exprkind_t k = getExprKind(expr);
    
    if (k == TRUE) {
      return "true";
    } else if (k == FALSE) {
      return "false";
    }
    
    // Use a simple string buffer to capture the output
    char* buf = nullptr;
    unsigned long len = 0;
    vc_printExprToBuffer(vc, expr, &buf, &len);
    
    if (buf)
    {
      std::string result(buf);
      free(buf);  // Free the buffer allocated by STP

      // For symbols STP prints identifiers surrounded by pipes (e.g. |a|).
      // These extra delimiters do *not* exist in the original name and break
      // the round-trip translation via TermTranslator which relies on an
      // exact textual match.  Remove them along with surrounding whitespace.
      if (k == SYMBOL)
      {
        // Strip whitespace
        result.erase(std::remove_if(result.begin(), result.end(), ::isspace),
                     result.end());

        if (result.size() >= 2 && result.front() == '|' && result.back() == '|')
        {
          result = result.substr(1, result.size() - 2);
        }
      }

      return result;
    }
    return "unknown";
  } catch (const std::exception& e) {
    return std::string("error: ") + e.what();
  }
}

uint64_t StpTerm::to_int() const
{
  if (!expr) {
    throw IncorrectUsageException("Cannot convert null term to int");
  }
  
  try {
    enum exprkind_t k = getExprKind(expr);
    
    // Handle TRUE/FALSE expressions directly
    if (k == TRUE) {
      return 1;
    } else if (k == FALSE) {
      return 0;
    } else if (k == BVCONST) {
      return static_cast<uint64_t>(getBVUnsignedLongLong(expr));
    }
    
    if (getType(expr) == BOOLEAN_TYPE) {
      int bool_val = vc_isBool(expr);
      if (bool_val == -1) {
        throw IncorrectUsageException("Term is not a constant");
      }
      return bool_val;
    }
  } catch (const std::exception& e) {
    throw IncorrectUsageException(std::string("Error converting to int: ") + e.what());
  }
  
  throw IncorrectUsageException("Term is not a constant");
}

// Helper function to check if an operation may be optimized away by STP
// These operations need special handling because STP may return the child
// expression directly instead of creating a node for the operation
// TODO: add other operations as needed
static bool mayBeOptimizedAway(PrimOp op) {
  switch (op) {
    case Extract:
      // Extract may be optimized away
      return true;
    default:
      return false;
  }
}

// Helper function to get the number of real term children (excluding indices)
static uint32_t getNumRealChildren(Expr expr) {
  if (!expr) return 0;

  exprkind_t kind = getExprKind(expr);

  // For indexed operations, STP internally stores indices as additional children
  // but we only want to iterate over the real term children
  switch (kind) {
    case exprkind_t::BVEXTRACT:
      // Extract has 1 real child (the expression) + 2 indices (high, low)
      // getDegree returns 3, but we only want 1
      return 1;
    default:
      // For all other operations, return the actual degree
      return getDegree(expr);
  }
}

TermIter StpTerm::begin()
{
  if (!expr) {
    throw IncorrectUsageException("Cannot iterate over null term");
  }
  
  try {
    return TermIter(new StpTermIter(expr, vc));
  } catch (const std::exception& e) {
    throw IncorrectUsageException(std::string("Error creating iterator: ") + e.what());
  }
}

TermIter StpTerm::end()
{
  if (!expr) {
    throw IncorrectUsageException("Cannot iterate over null term");
  }
  
  try {
    // For operations that STP may optimize away (currently only Extract)
    if (stored_op.prim_op != NUM_OPS_AND_NULL &&
        mayBeOptimizedAway(stored_op.prim_op)) {
        return TermIter(new StpTermIter(expr, vc, 1));
    }

    // For all other operations, check the actual expression structure
    return TermIter(new StpTermIter(expr, vc, getNumRealChildren(expr)));
  } catch (const std::exception& e) {
    throw IncorrectUsageException(std::string("Error creating end iterator: ") + e.what());
  }
}

std::string StpTerm::print_value_as(SortKind sk)
{
  if (!expr) {
    throw IncorrectUsageException("Cannot print null term as value");
  }
  
  try {
    enum exprkind_t k = getExprKind(expr);
    
    if (sk == BOOL) {
      // Handle TRUE/FALSE expressions directly
      if (k == TRUE) {
        return "true";
      } else if (k == FALSE) {
        return "false";
      } else if (k == BVCONST) {
        // For BVCONST of width 1
        return getBVUnsigned(expr) ? "true" : "false";
      } else {
        // For non-constant expressions, we can't extract a value
        throw IncorrectUsageException("Cannot print non-constant expression as boolean value");
      }
    }
    else if (sk == BV) {
      // Handle TRUE/FALSE expressions as BV
      if (k == TRUE) {
        return "1";
      } else if (k == FALSE) {
        return "0";
      } else if (k == BVCONST) {
        // For BVCONST, use STP's formatted output directly and convert to SMT-LIB2 format
        char* buf = nullptr;
        unsigned long len = 0;
        vc_printExprToBuffer(vc, expr, &buf, &len);
        
        if (buf) {
          std::string stp_output(buf);
          free(buf);
          
          // Remove trailing spaces
          while (!stp_output.empty() && stp_output.back() == ' ') {
            stp_output.pop_back();
          }
          
          Type t = vc_getType(vc, expr);
          int width = vc_getValueSize(vc, t);
          
          // Convert STP format to SMT-LIB2 format
          if (stp_output.substr(0, 2) == "0x") {
            // Hex format: "0x02" -> "#x02"
            std::string result = "#x" + stp_output.substr(2);
            return result;
          } else if (stp_output.substr(0, 2) == "0b") {
            // Binary format: "0b1" -> "#b1"
            std::string result = "#b" + stp_output.substr(2);
            return result;
          } else {
            // Decimal format: convert to (_ bv<num> <width>) format
            unsigned long long val = getBVUnsignedLongLong(expr);
            std::string result = "(_ bv" + std::to_string(val) + " " + std::to_string(width) + ")";
            return result;
          }
        }
        
        // Fallback to decimal format if we can't get STP output
        Type t = vc_getType(vc, expr);
        int width = vc_getValueSize(vc, t);
        unsigned long long val = getBVUnsignedLongLong(expr);
        std::string result = "(_ bv" + std::to_string(val) + " " + std::to_string(width) + ")";
        return result;
      } else {
        // For non-constant expressions, we can't extract a value
        throw IncorrectUsageException("Cannot print non-constant expression as bitvector value");
      }
    }
  } catch (const std::exception& e) {
    throw IncorrectUsageException(std::string("Error printing value: ") + e.what());
  }
  
  throw IncorrectUsageException("Cannot print value as given sort kind");
}

} // namespace smt
