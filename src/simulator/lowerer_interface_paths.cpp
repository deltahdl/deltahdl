// §25.6 with §30.4: a module path whose destination is a signal of an
// interface the module reaches through an interface port delays that signal
// as a path to an output port delays the port.

#include <algorithm>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// §30.4.2: the signals of the interface port `port` a module path of `mod`
// ends at, `q` of `(posedge ch.c => (ch.q +: ch.d))` through `ch`.
std::vector<std::string_view> PathDestinationsThrough(const RtlirModule& mod,
                                                      std::string_view port) {
  std::vector<std::string_view> names;
  for (const ModuleItem* block : mod.specify_blocks) {
    for (const SpecifyItem* item : block->specify_items) {
      for (const SpecifyTerminal& t : item->path.dst_ports) {
        if (t.interface_name == port) names.push_back(t.name);
      }
    }
  }
  return names;
}

// An identifier naming `text` as the scope the connection is lowered in reads
// it.
Expr* NameExpr(std::string text, Arena& arena) {
  auto* owned = arena.Create<std::string>(std::move(text));
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = *owned;
  return id;
}

}  // namespace

// A variable of the interface instance `instance` that a module path of
// `inst` ends at, reached through its port `port_name`, is that path's output.
// The instance writes a variable of its own under the port's name for it, in
// place of the alias to the shared one, and a connection like an output
// port's carries its value to the shared variable, delayed by the paths that
// end at it.
void Lowerer::DrivePathDelayedMembers(const RtlirModuleInst& inst,
                                      std::string_view port_name,
                                      const RtlirModule* ifc,
                                      const std::string& port_prefix,
                                      const std::string& instance) {
  std::vector<std::string_view> delayed =
      PathDestinationsThrough(*inst.resolved, port_name);
  for (const RtlirVariable& var : ifc->variables) {
    if (std::ranges::find(delayed, var.name) == delayed.end()) continue;
    auto* key = arena_.Create<std::string>(port_prefix + std::string(var.name));
    ctx_.CreateVariable(*key, var.width)->is_4state = var.is_4state;
    RtlirContAssign ca;
    ca.gen_block_consts = inst.gen_block_consts;
    ca.gen_block_prefixes = inst.gen_block_prefixes;
    ca.lhs = NameExpr(instance + "." + std::string(var.name), arena_);
    ca.rhs = NameExpr(key->substr(inst_prefix_.size()), arena_);
    ca.width = var.width;
    ca.module_path_port = *key;
    path_delayed_ports_.insert(ca.module_path_port);
    LowerContAssign(ca, false);
  }
}

}  // namespace delta
