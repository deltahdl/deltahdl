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
  VpiObject* typespec = nullptr;
  if (!cast.text.empty()) {
    for (const auto& [keyword, kind] : kKeywordTypespecs) {
      if (keyword != cast.text) continue;
      typespec = alloc();
      typespec->type = kind;
    }
  } else if (cast.rhs != nullptr && cast.rhs->kind == ExprKind::kIdentifier) {
    typespec = TypedefAround(from, cast.rhs->text);
  }
  if (typespec != nullptr) op->children.push_back(typespec);
  return op;
}

}  // namespace delta
