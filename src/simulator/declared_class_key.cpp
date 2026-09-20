#include "simulator/declared_class_key.h"

#include <string>
#include <string_view>

#include "common/arena.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"

namespace delta {

std::string_view DeclaredClassKey(const DataType& type, SimContext& ctx,
                                  Arena& arena) {
  std::string_view scope = type.scope_name;
  std::string_view name = type.type_name;
  if (name.empty()) return {};
  if (!scope.empty()) {
    auto* scoped = arena.Create<std::string>(std::string(scope) +
                                             "::" + std::string(name));
    if (ctx.FindClassType(*scoped) != nullptr) return *scoped;
  }
  return ctx.FindClassType(name) != nullptr ? name : std::string_view{};
}

}  // namespace delta
