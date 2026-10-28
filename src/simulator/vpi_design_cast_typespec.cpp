#include <algorithm>
#include <array>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_design_attach_assigns_internal.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_typespecs.h"
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

// The typespec of the typedef named `name` that `scope` declares, or of the
// type a type parameter so named stands for (§6.20.3); null for none.
VpiObject* TypedefIn(const VpiObject& scope, std::string_view name) {
  for (VpiObject* child : scope.children) {
    if (!VpiIsTypespecType(child->type) || child->name != name) continue;
    return child->type == vpiTypeParameter ? child->param_typespec : child;
  }
  return nullptr;
}

// §26.3 with §3.12.1: the typespec of the typedef or type parameter `name`
// that a cast written where `build` stands names: one the scope it is written
// in declares, or a scope around it out to its instance, then one a package
// the instance's module imports declares, then one the compilation unit
// declares; null for none.
VpiObject* TypedefVisible(std::string_view name, const AssignBuild& build) {
  for (const VpiObject* at = VpiScopeOrInstance(
           build.names.scope != nullptr ? build.names.scope
                                        : build.names.instance,
           build.names.objects, build.names.prefix);
       at != nullptr; at = VpiIsInstanceType(at->type) ? nullptr : at->parent) {
    if (VpiObject* found = TypedefIn(*at, name)) return found;
  }
  const VpiObjectMap& answered = build.names.unit_typespecs;
  if (VpiObject* imported =
          VpiImportedTypespec(name, build.names.imports, answered)) {
    return imported;
  }
  const auto kUnit = answered.find(name);
  return kUnit != answered.end() ? kUnit->second : nullptr;
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

bool IsTwoState(VpiObject& expr);

// §7.4 with §7.10 and §7.8: whether the elements of the unpacked array `array`
// are 2-state: a queue's, a dynamic array's or an associative array's as the
// run's store for them records, and a fixed array's as its elements are.
bool ElementsAreTwoState(const VpiObject& array) {
  if (array.queue != nullptr) return !array.queue->is_4state;
  if (array.assoc != nullptr) return !array.assoc->is_4state;
  return std::ranges::any_of(array.children, [](VpiObject* child) {
    return child->array_member && IsTwoState(*child);
  });
}

// §6.11 and §11.8.1: whether `expr` is 2-state. A variable of a built-in type
// is as its type is, and one of a structure, union, enumeration or packed
// array of them as the run's storage for it records (§7.2.1, §7.3.1, §6.19,
// §7.4.1), or, for a task's or function's variable, which has none, as its
// declaration does; a bit, a select or an element as what it selects from, an
// unpacked array as its elements, and an operation when every operand is; a
// literal and any other expression are taken as 4-state.
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
    case vpiVarSelect:
      return expr.parent != nullptr && IsTwoState(*expr.parent);
    case vpiArrayVar:
      return ElementsAreTwoState(expr);
    case vpiStructVar:
    case vpiUnionVar:
    case vpiEnumVar:
    case vpiPackedArrayVar:
      return expr.var != nullptr ? !expr.var->is_4state
                                 : expr.decl_facts.two_state;
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

// `made`, the object the model builds for `expr`, or where it builds none, as
// for a logical equivalence (§11.4.7), which no operation type names, a
// stand-in as wide and as signed as its value where the source wrote it, of a
// nature IsTwoState takes as 4-state.
VpiObject& ObjectOrStandIn(VpiObject* made, const Expr* expr,
                           const AssignBuild& build) {
  if (made != nullptr) return *made;
  const Logic4Vec kValue = ValueWhereWritten(expr, build);
  VpiObject* stand_in = build.alloc();
  stand_in->size = static_cast<int>(kValue.width);
  stand_in->decl_signed = kValue.is_signed;
  return *stand_in;
}

// §6.24.1 with §11.8.1: a vector typespec `size` bits wide, of the 2- or
// 4-state nature and the signedness of `like`.
VpiObject* VectorTypespec(VpiObject& like, int size, const AssignBuild& build) {
  VpiObject* typespec = build.alloc();
  typespec->type = IsTwoState(like) ? vpiBitTypespec : vpiLogicTypespec;
  typespec->decl_signed = like.decl_signed;
  typespec->size = size;
  return typespec;
}

// §6.23: the typespec of the type of `expr`, an expression a type reference
// writes where `build` stands: the typespec its object relates to, for a
// variable that of the type it was declared with (§37.17), and otherwise that
// of its self-determined type, a vector of its 2- or 4-state nature, width and
// signedness, as an operation's is (§11.8.1).
VpiObject* ExpressionTypespec(const Expr& expr, const AssignBuild& build) {
  VpiObject& typed =
      ObjectOrStandIn(ExpressionObject(&expr, build), &expr, build);
  for (VpiObject* child : typed.children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return VectorTypespec(typed, typed.size, build);
}

// §6.23: the typespec of the type the type reference `ref` refers to, where
// it is written as `build` stands: of a data type it writes, the typedef or
// type parameter a name finds there (TypedefVisible) or a built-in type over
// the packed dimensions written; of an expression it writes, the
// expression's type (ExpressionTypespec).
VpiObject* TypeRefTypespec(const Expr& ref, const AssignBuild& build) {
  const DataType* written = ref.type_value;
  if (written == nullptr) return ExpressionTypespec(*ref.lhs, build);
  if (written->kind == DataTypeKind::kNamed) {
    return TypedefVisible(written->type_name, build);
  }
  return VpiKeywordTypespec(*written, nullptr, *build.sim,
                            {build.alloc, build.keep, build.sim->GetArena()});
}

// The typespec `cast` names, where it is written as `build` stands: a typedef
// or type parameter visible there (TypedefVisible), one a package declares
// where the cast names it through the package, pk::t (§26.3), the type a type
// reference refers to (§6.23), or a built-in type a keyword names; null where
// it names none of them.
VpiObject* NamedTypespec(const Expr& cast, const AssignBuild& build) {
  if (cast.text.empty() && cast.rhs->kind == ExprKind::kTypeRef) {
    return TypeRefTypespec(*cast.rhs, build);
  }
  if (cast.text.empty() && cast.rhs->kind == ExprKind::kMemberAccess) {
    const auto kScoped = build.names.unit_typespecs.find(
        std::string(cast.rhs->lhs->text) +
        "::" + std::string(cast.rhs->rhs->text));
    return kScoped != build.names.unit_typespecs.end() ? kScoped->second
                                                       : nullptr;
  }
  // The type is named as text or as an identifier, as the parser read it.
  const std::string_view kName = !cast.text.empty() ? cast.text
                                 : cast.rhs->kind == ExprKind::kIdentifier
                                     ? cast.rhs->text
                                     : std::string_view{};
  if (kName.empty()) return nullptr;
  VpiObject* typespec = TypedefVisible(kName, build);
  for (const auto& [keyword, kind] : kKeywordTypespecs) {
    if (typespec != nullptr || keyword != kName) continue;
    typespec = build.alloc();
    typespec->type = kind;
  }
  return typespec;
}

// What the cast operation `op`, written as `cast`, casts: its operand's
// object, or ObjectOrStandIn's stand-in where the model builds none.
VpiObject& CastOperand(VpiObject& op, const Expr& cast,
                       const AssignBuild& build) {
  return ObjectOrStandIn(op.children.empty() ? nullptr : op.children.front(),
                         cast.lhs, build);
}

// §6.24.1: the typespec a cast naming no type makes from `operand`, what it
// casts. A size cast's is a vector of the operand's 2- or 4-state nature and
// signedness, as wide as the constant it is written with; a signing cast's is
// the operand's type of the signedness it names; and a const cast's is the
// operand's type. Null for any other cast.
VpiObject* OperandTypespec(const Expr& cast, VpiObject& operand,
                           const AssignBuild& build) {
  // A size cast's width is an expression the model has an object for, which
  // a type the cast names is not.
  if (cast.text.empty() && ExpressionObject(cast.rhs, build) != nullptr) {
    return VectorTypespec(
        operand, static_cast<int>(ConstantWhereWritten(cast.rhs, build)),
        build);
  }
  const bool kSigning = cast.text == "signed" || cast.text == "unsigned";
  if (!kSigning && cast.text != "const") return nullptr;
  VpiObject* typespec = build.alloc();
  typespec->type = OperandTypespecKind(operand);
  typespec->decl_signed =
      kSigning ? cast.text == "signed" : operand.decl_signed;
  typespec->size = operand.size;
  return typespec;
}

}  // namespace

VpiObject* VpiTypedCast(VpiObject* op, const Expr& cast,
                        const AssignBuild& build) {
  VpiObject* typespec = NamedTypespec(cast, build);
  if (typespec == nullptr) {
    typespec = OperandTypespec(cast, CastOperand(*op, cast, build), build);
  }
  if (typespec != nullptr) op->children.push_back(typespec);
  return op;
}

}  // namespace delta
