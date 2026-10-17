#include <array>
#include <functional>
#include <string_view>
#include <utility>

#include "parser/ast_expr.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"

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

}  // namespace

VpiObject* VpiTypedCast(VpiObject* op, const Expr& cast, const VpiObject* from,
                        const std::function<VpiObject*()>& alloc) {
  if (op == nullptr) return nullptr;
  // The type is named as text or as an identifier, as the parser read it.
  const std::string_view kName =
      !cast.text.empty() ? cast.text
      : cast.rhs != nullptr && cast.rhs->kind == ExprKind::kIdentifier
          ? cast.rhs->text
          : std::string_view{};
  if (kName.empty()) return op;
  VpiObject* typespec = TypedefAround(from, kName);
  for (const auto& [keyword, kind] : kKeywordTypespecs) {
    if (typespec != nullptr || keyword != kName) continue;
    typespec = alloc();
    typespec->type = kind;
  }
  if (typespec != nullptr) op->children.push_back(typespec);
  return op;
}

}  // namespace delta
