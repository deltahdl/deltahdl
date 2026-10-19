#pragma once

#include <functional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
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
// connection `g.i` or `g[k].i` is known to reach it, and is refused, before
// the block is elaborated: a conditional block's under the name it will be
// stored under, every alternative walked since which one is selected is not
// yet folded, and a loop block's under the block's name followed by `[]_`,
// its iterations' indices not yet folded either. `find_module` resolves an
// instance's module, interface or program name.
void RegisterGenerateBlockInterfaces(
    const std::vector<ModuleItem*>& items,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    InterfaceInstTypes& table, Arena& arena);

// What resolving an interface port's actual needs: the declaration of the
// module the actual is written in, the design's top-level modules, which a
// full path starts at (§23.6), a lookup of an instance's module or interface
// by its name, the module's interface instance table, its parameters, which
// fold the index of a loop block's path, and where to report.
struct InterfaceActualScope {
  const ModuleDecl* parent;
  const std::vector<const ModuleDecl*>& tops;
  const std::function<const ModuleDecl*(std::string_view)>& find_module;
  InterfaceInstTypes& table;
  const ScopeMap& params;
  Arena& arena;
  DiagEngine& diag;
  SourceLoc loc;
};

// §23.9 with §27.4: rewrites each actual of `inst` that names an interface
// instance a generate block declares by its name written in the block, `i` or
// `i.mp`, to that instance's stored name, which the elaborator's interface
// checks and the simulator's connection both look an instance up by. §25.3:
// an actual reaching such an instance through the block, `g.i` or `g[k].i`,
// is reported and its binding marked refused. The stored name a loop block's
// path resolves to is entered into the table, the loop not yet having been
// elaborated where the path is written outside it.
void ResolveGenBlockInterfaceActuals(RtlirModuleInst& inst,
                                     const InterfaceActualScope& scope);

// §25.3 with §23.6: rewrites each interface port actual of `inst` that names,
// through module instances, an interface instance one of them declares, `h.i`
// or a modport of it, `h.i.mp`, to the instance's path as one name, `h.i`,
// entered into the table, under which the simulator keys that instance too;
// a full path from a top-level module, `top.h.i`, is kept whole.
// An actual whose path resolves through an arrayed instance, `h[0].i`, is
// reported and its binding marked refused.
void ResolveInstancePathActuals(RtlirModuleInst& inst,
                                const InterfaceActualScope& scope);

}  // namespace delta
