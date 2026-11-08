#include <algorithm>
#include <array>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/rtlir_scopes.h"
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
#include "simulator/vpi_typespec_shapes.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

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

VpiObject* TypedefIn(const VpiObject& scope, std::string_view name) {
  for (VpiObject* child : scope.children) {
    if (!VpiIsTypespecType(child->type) || child->name != name) continue;
    return child->type == vpiTypeParameter ? child->param_typespec : child;
  }
  return nullptr;
}

std::vector<const VpiObject*> ScopesOutToInstance(const AssignBuild& build) {
  std::vector<const VpiObject*> scopes;
  for (const VpiObject* at =
           VpiScopeOrInstance(InnermostScope(build.names), build.names.objects,
                              build.names.prefix);
       at != nullptr; at = VpiIsInstanceType(at->type) ? nullptr : at->parent) {
    scopes.push_back(at);
  }
  return scopes;
}

VpiObject* TypedefVisible(std::string_view name, const AssignBuild& build) {
  for (const VpiObject* at : ScopesOutToInstance(build)) {
    if (VpiObject* found = TypedefIn(*at, name)) return found;
  }
  return VpiPackageOrUnitTypespec({}, name, build.names.imports,
                                  build.names.unit_typespecs);
}

VpiObject* ScopedTypespec(std::string_view scope, std::string_view name,
                          const AssignBuild& build) {
  if (VpiObject* packaged = VpiPackageOrUnitTypespec(
          scope, name, {}, build.names.unit_typespecs)) {
    return packaged;
  }
  for (const VpiObject* at : ScopesOutToInstance(build)) {
    for (const VpiObject* child : at->children) {
      if (child->type == vpiClassDefn && child->name == scope) {
        return TypedefIn(*child, name);
      }
    }
  }
  return nullptr;
}

VpiObject* DimensionedTypespec(const PackedDims& packed, VpiObject* named,
                               const AssignBuild& build) {
  std::vector<VpiTypespecDim> dims;
  dims.reserve(packed.size());
  for (const PackedRange& dim : packed) {
    dims.push_back({false, dim, 0, nullptr});
  }
  const VpiAttachBuild kAttach{build.alloc, build.keep, build.sim->GetArena()};
  VpiTypespecShapes shapes(kAttach);
  VpiObject* typespec = build.alloc();
  shapes.Shape(typespec, dims, named);
  if (typespec->type == named->type) {
    for (VpiObject* range : named->children) {
      if (range->type == vpiRange) typespec->children.push_back(range);
    }
  }
  return typespec;
}

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

int OperandTypespecKind(const VpiObject& operand) {
  for (const auto& [var, kind] : kVariableTypespecs) {
    if (operand.type == var) return kind;
  }
  return vpiLogicTypespec;
}

bool IsTwoState(VpiObject& expr);

bool ElementsAreTwoState(const VpiObject& array) {
  if (array.queue != nullptr) return !array.queue->is_4state;
  if (array.assoc != nullptr) return !array.assoc->is_4state;
  return std::ranges::any_of(array.children, [](VpiObject* child) {
    return child->array_member && IsTwoState(*child);
  });
}

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

VpiObject& ObjectOrStandIn(VpiObject* made, const Expr* expr,
                           const AssignBuild& build) {
  if (made != nullptr) return *made;
  const Logic4Vec kValue = ValueWhereWritten(expr, build);
  VpiObject* stand_in = build.alloc();
  stand_in->size = static_cast<int>(kValue.width);
  stand_in->decl_signed = kValue.is_signed;
  return *stand_in;
}

VpiObject* VectorTypespec(VpiObject& like, int size, const AssignBuild& build) {
  VpiObject* typespec = build.alloc();
  typespec->type = IsTwoState(like) ? vpiBitTypespec : vpiLogicTypespec;
  typespec->decl_signed = like.decl_signed;
  typespec->size = size;
  return typespec;
}

VpiObject* ExpressionTypespec(const Expr& expr, const AssignBuild& build) {
  VpiObject& typed =
      ObjectOrStandIn(ExpressionObject(&expr, build), &expr, build);
  for (VpiObject* child : typed.children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return VectorTypespec(typed, typed.size, build);
}

VpiObject* TypeRefTypespec(const Expr& ref, const AssignBuild& build) {
  const DataType* written = ref.type_value;
  if (written == nullptr) return ExpressionTypespec(*ref.lhs, build);
  if (written->kind != DataTypeKind::kNamed) {
    return VpiKeywordTypespec(*written, nullptr, *build.sim,
                              {build.alloc, build.keep, build.sim->GetArena()});
  }
  VpiObject* named =
      written->scope_name.empty()
          ? TypedefVisible(written->type_name, build)
          : ScopedTypespec(written->scope_name, written->type_name, build);
  const PackedDims kPacked = WrittenPackedDims(written, *build.sim);
  if (named == nullptr || kPacked.empty()) return named;
  return DimensionedTypespec(kPacked, named, build);
}

VpiObject* NamedTypespec(const Expr& cast, const AssignBuild& build) {
  if (cast.text.empty() && cast.rhs->kind == ExprKind::kTypeRef) {
    return TypeRefTypespec(*cast.rhs, build);
  }
  if (cast.text.empty() && cast.rhs->kind == ExprKind::kMemberAccess) {
    return ScopedTypespec(cast.rhs->lhs->text, cast.rhs->rhs->text, build);
  }
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

VpiObject& CastOperand(VpiObject& op, const Expr& cast,
                       const AssignBuild& build) {
  return ObjectOrStandIn(op.children.empty() ? nullptr : op.children.front(),
                         cast.lhs, build);
}

VpiObject* OperandTypespec(const Expr& cast, VpiObject& operand,
                           const AssignBuild& build) {
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

VpiObject* VpiPackageOrUnitTypespec(std::string_view package,
                                    std::string_view name,
                                    const std::vector<RtlirImport>& imports,
                                    const VpiObjectMap& answered) {
  if (!package.empty()) {
    const auto kPackaged =
        answered.find(std::string(package) + "::" + std::string(name));
    return kPackaged != answered.end() ? kPackaged->second : nullptr;
  }
  if (VpiObject* imported = VpiImportedTypespec(name, imports, answered)) {
    return imported;
  }
  const auto kUnit = answered.find(name);
  return kUnit != answered.end() ? kUnit->second : nullptr;
}

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
