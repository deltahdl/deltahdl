#include "elaborator/index_value_kind.h"

#include <algorithm>
#include <array>
#include <string_view>
#include <unordered_map>
#include <utility>

#include "elaborator/elaborator_helpers.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using VarTypes = std::unordered_map<std::string_view, DataTypeKind>;

constexpr std::array kArithmeticOps = {TokenKind::kPlus,    TokenKind::kMinus,
                                       TokenKind::kStar,    TokenKind::kSlash,
                                       TokenKind::kPercent, TokenKind::kPower};

// §6.16.1 to §6.16.15: the kind of value each string method gives.
constexpr std::array<std::pair<std::string_view, IndexValueKind>, 14>
    kStringMethods = {{{"len", IndexValueKind::kIntegral},
                       {"getc", IndexValueKind::kIntegral},
                       {"toupper", IndexValueKind::kString},
                       {"tolower", IndexValueKind::kString},
                       {"compare", IndexValueKind::kIntegral},
                       {"icompare", IndexValueKind::kIntegral},
                       {"substr", IndexValueKind::kString},
                       {"atoi", IndexValueKind::kIntegral},
                       {"atohex", IndexValueKind::kIntegral},
                       {"atooct", IndexValueKind::kIntegral},
                       {"atobin", IndexValueKind::kIntegral},
                       {"atoreal", IndexValueKind::kReal},
                       {"realtoa", IndexValueKind::kString},
                       {"itoa", IndexValueKind::kString}}};

// A variable an operator reads: real or integral, a string, a class or an
// enumeration having no place under an arithmetic or a unary operator but the
// integral one an enumeration's value gives.
IndexValueKind KindOfDeclared(std::string_view name, const VarTypes& types) {
  auto it = types.find(name);
  if (it == types.end()) return IndexValueKind::kUnknown;
  return IsRealType(it->second) ? IndexValueKind::kReal
                                : IndexValueKind::kIntegral;
}

// A method call is the call of a member access; any other call is a function
// whose result this reading does not see, and `new`, which the parser reads
// as a call, has no callee at all.
IndexValueKind KindOfCall(const Expr* call) {
  if (call->lhs == nullptr || call->lhs->kind != ExprKind::kMemberAccess) {
    return IndexValueKind::kUnknown;
  }
  std::string_view method = call->lhs->rhs->text;
  auto it =
      std::ranges::find(kStringMethods, method,
                        &std::pair<std::string_view, IndexValueKind>::first);
  return it != kStringMethods.end() ? it->second : IndexValueKind::kUnknown;
}

IndexValueKind KindOfBinary(const Expr* e, const VarTypes& types) {
  if (std::ranges::find(kArithmeticOps, e->op) == kArithmeticOps.end()) {
    return IndexValueKind::kIntegral;
  }
  IndexValueKind lhs = KindOfIndexValue(e->lhs, types);
  IndexValueKind rhs = KindOfIndexValue(e->rhs, types);
  return lhs == IndexValueKind::kReal || rhs == IndexValueKind::kReal
             ? IndexValueKind::kReal
             : IndexValueKind::kIntegral;
}

}  // namespace

IndexValueKind KindOfIndexValue(const Expr* e, const VarTypes& var_types) {
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
      return IndexValueKind::kIntegral;
    case ExprKind::kRealLiteral:
      return IndexValueKind::kReal;
    case ExprKind::kIdentifier:
      return KindOfDeclared(e->text, var_types);
    case ExprKind::kUnary:
      return KindOfIndexValue(e->lhs, var_types);
    case ExprKind::kBinary:
      return KindOfBinary(e, var_types);
    case ExprKind::kCall:
      return KindOfCall(e);
    default:
      return IndexValueKind::kUnknown;
  }
}

}  // namespace delta
