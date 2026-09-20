#include "simulator/declared_class_key.h"

#include <string>
#include <string_view>

#include "common/arena.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"

namespace delta {

// §26.7 with Syntax 26-5 (printed pages 816-817 of ~/LRM.pdf): the built-in
// package's names are written with or without the `std::` qualifier and reach
// one declaration, and no user package may be called std, so the run holds
// its classes under the bare name and SimContext::FindClassType drops the
// qualifier before asking its table. The scoped probe below then found
// `std::process` and answered that spelling as the key, so `std::process p =
// std::process::self();` recorded p's class as "std::process", which the
// process dispatch compares with "process" and missed: p.status() read 0 and
// p.kill() ran nothing.
constexpr std::string_view kStdPackage = "std";

std::string_view DeclaredClassKey(const DataType& type, SimContext& ctx,
                                  Arena& arena) {
  std::string_view scope = type.scope_name;
  std::string_view name = type.type_name;
  if (name.empty()) return {};
  if (!scope.empty() && scope != kStdPackage) {
    auto* scoped = arena.Create<std::string>(std::string(scope) +
                                             "::" + std::string(name));
    if (ctx.FindClassType(*scoped) != nullptr) return *scoped;
  }
  return ctx.FindClassType(name) != nullptr ? name : std::string_view{};
}

}  // namespace delta
