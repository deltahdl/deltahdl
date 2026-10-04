#pragma once

#include <functional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_module.h"

namespace delta {

// A module's interface instances, keyed by the name each is stored under: its
// own name at module level, the generate block's prefix followed by it inside
// a block (§27.4, §27.5), and mapped to the interface it is an instance of.
using InterfaceInstTypes =
    std::unordered_map<std::string_view, std::string_view>;

// §23.9: the key under which `name`, written inside the generate blocks
// `prefixes` names (outermost first), denotes an interface instance of
// `table`: the innermost block's own first, then each enclosing one's, then
// the module's. Empty when none of them declares one of that name.
std::string_view FindBlockInterface(std::string_view name,
                                    const GenBlockPrefixes& prefixes,
                                    const InterfaceInstTypes& table);

// The path, loop constants and generate prefixes of the block instances a
// declaration stands in (§27.4), outermost first.
struct GenBlockContext {
  const HierPath& path;
  const GenBlockConsts& consts;
  const GenBlockPrefixes& prefixes;
};

// §27.4 with §25.3 and §23.6: gives `inst` the context of the generate blocks
// it stands in, its path among them, ahead of its ports being bound and as
// ElaborateGenerateBlockItem stamps it again afterwards, since an interface
// port's actual is resolved through those blocks; and registers in `table`,
// under the name it is stored under, an interface instance a block declares,
// which such an actual resolves to.
void EnterGenBlockInstance(RtlirModuleInst& inst, const ModuleDecl* child_decl,
                           const GenBlockContext& context,
                           InterfaceInstTypes& table);

// §25.3 with §23.6, §27.4 and §27.5: registers in `table` each interface
// instance a named generate block among `items` declares, so a module-level
// connection `g.i` or `g[k].i` may name it before the block is elaborated: a
// conditional block's under the name it will be stored under, every
// alternative walked since which one is selected is not yet folded, and a loop
// block's under the block's name followed by `[]_`, its iterations' indices
// not yet folded either. `find_module` resolves an instance's module,
// interface or program name.
void RegisterGenerateBlockInterfaces(
    const std::vector<ModuleItem*>& items,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    InterfaceInstTypes& table, Arena& arena);

// §25.3 with §23.6, §23.9 and §27.4: rewrites each actual of `inst` that names
// an interface instance a generate block declares -- `i` or `i.mp` written in
// the block, `g.i` or `g[k].i` written through it -- to that instance's stored
// name, which the elaborator's interface checks and the simulator's connection
// both look an instance up by. `scope` folds the index of a loop block's path,
// and the stored name such a path resolves to is entered into `table`, the
// loop not yet having been elaborated where the path is written outside it.
void ResolveGenBlockInterfaceActuals(RtlirModuleInst& inst,
                                     InterfaceInstTypes& table,
                                     const ScopeMap& scope, Arena& arena);

}  // namespace delta
