#include <algorithm>
#include <array>
#include <functional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §6.24.1 with §37.25: the typespec kind of each built-in type a cast names by
// keyword.
constexpr std::array<std::pair<std::string_view, int>, 13> kKeywordTypespecs = {
    {{"bit", vpiBitTypespec},
     {"logic", vpiLogicTypespec},
     {"reg", vpiLogicTypespec},
     {"byte", vpiByteTypespec},
     {"shortint", vpiShortIntTypespec},
     {"int", vpiIntTypespec},
     {"longint", vpiLongIntTypespec},
     {"integer", vpiIntegerTypespec},
     {"time", vpiTimeTypespec},
     {"real", vpiRealTypespec},
     {"realtime", vpiRealTypespec},
     {"shortreal", vpiShortRealTypespec},
     {"string", vpiStringTypespec}}};

// The typespec of the typedef named `name` that `from`, or a scope around it,
// declares; null for none.
VpiObject* TypedefAround(const VpiObject* from, std::string_view name) {
  for (const VpiObject* at = from; at != nullptr; at = at->parent) {
    for (VpiObject* child : at->children) {
      if (child->type != vpiTypeParameter && VpiIsTypespecType(child->type) &&
          child->name == name) {
        return child;
      }
    }
  }
  return nullptr;
}

// §6.11 Table 6-8 with §37.25: the typespec kind of the built-in type a
// variable of each kind is declared with.
constexpr std::array<std::pair<int, int>, 10> kVariableTypespecs = {
    {{vpiBitVar, vpiBitTypespec},
     {vpiByteVar, vpiByteTypespec},
     {vpiShortIntVar, vpiShortIntTypespec},
     {vpiIntVar, vpiIntTypespec},
     {vpiLongIntVar, vpiLongIntTypespec},
     {vpiIntegerVar, vpiIntegerTypespec},
     {vpiTimeVar, vpiTimeTypespec},
     {vpiRealVar, vpiRealTypespec},
     {vpiShortRealVar, vpiShortRealTypespec},
     {vpiStringVar, vpiStringTypespec}}};

// The typespec kind of `operand`'s type: its built-in type's where it is a
// variable of one, and a logic vector's otherwise.
int OperandTypespecKind(const VpiObject& operand) {
  for (const auto& [var, kind] : kVariableTypespecs) {
    if (operand.type == var) return kind;
  }
  return vpiLogicTypespec;
}

// §6.11 and §11.8.1: whether `expr` is 2-state. A variable is as its type
// is, a bit or a select of one as what it selects from, and an operation when
// every operand is; a literal and any other expression are taken as 4-state.
bool IsTwoState(VpiObject& expr) {
  if (expr.type == vpiOperation) {
    const std::vector<VpiHandle> kOperands = VpiOperationOperands(&expr);
    return !kOperands.empty() &&
           std::ranges::all_of(kOperands, [](VpiHandle operand) {
             return IsTwoState(*operand);
           });
  }
  switch (expr.type) {
    case vpiBitSelect:
    case vpiPartSelect:
    case vpiIndexedPartSelect:
    case vpiRegBit:
      return expr.parent != nullptr && IsTwoState(*expr.parent);
    default:
      break;
  }
  switch (OperandTypespecKind(expr)) {
    case vpiBitTypespec:
    case vpiByteTypespec:
    case vpiShortIntTypespec:
    case vpiIntTypespec:
    case vpiLongIntTypespec:
      return true;
    default:
      return false;
  }
}

// The typespec `cast` names, a typedef `from` or a scope around it declares
// or a built-in type a keyword names; null where it names neither.
VpiObject* NamedTypespec(const Expr& cast, const VpiObject* from,
                         const std::function<VpiObject*()>& alloc) {
  // The type is named as text or as an identifier, as the parser read it.
  const std::string_view kName = !cast.text.empty() ? cast.text
                                 : cast.rhs->kind == ExprKind::kIdentifier
                                     ? cast.rhs->text
                                     : std::string_view{};
  if (kName.empty()) return nullptr;
  VpiObject* typespec = TypedefAround(from, kName);
  for (const auto& [keyword, kind] : kKeywordTypespecs) {
    if (typespec != nullptr || keyword != kName) continue;
    typespec = alloc();
    typespec->type = kind;
  }
  return typespec;
}

// §6.24.1: the typespec a cast naming no type makes from `operand`, what it
// casts. A size cast's is a vector of the operand's 2- or 4-state nature and
// signedness, as wide as the value `width` holds; a signing cast's is the
// operand's type of the signedness it names; and a const cast's is the
// operand's type. Null for any other cast.
VpiObject* OperandTypespec(const Expr& cast, VpiObject& operand,
                           const VpiObject* width,
                           const std::function<VpiObject*()>& alloc) {
  const bool kSigning = cast.text == "signed" || cast.text == "unsigned";
  const bool kSize =
      cast.text.empty() && width != nullptr && width->var != nullptr;
  if (!kSigning && !kSize && cast.text != "const") return nullptr;
  VpiObject* typespec = alloc();
  typespec->type =
      kSize ? (IsTwoState(operand) ? vpiBitTypespec : vpiLogicTypespec)
            : OperandTypespecKind(operand);
  typespec->decl_signed =
      kSigning ? cast.text == "signed" : operand.decl_signed;
  typespec->size =
      kSize ? static_cast<int>(width->var->value.ToUint64()) : operand.size;
  return typespec;
}

}  // namespace

VpiObject* VpiTypedCast(VpiObject* op, const Expr& cast, const VpiObject* from,
                        const VpiObject* width,
                        const std::function<VpiObject*()>& alloc) {
  VpiObject* typespec = NamedTypespec(cast, from, alloc);
  if (typespec == nullptr && !op->children.empty()) {
    typespec = OperandTypespec(cast, *op->children.front(), width, alloc);
  }
  if (typespec != nullptr) op->children.push_back(typespec);
  return op;
}

}  // namespace delta
