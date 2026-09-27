// §31.9.1 and §31.9.4 (printed pages 920-923): the delayed_reference and
// delayed_data a $setuphold or $recrem names are signals of the module, which
// "can be declared within the timing check so they can be used in the model's
// functional implementation". A name the module declares nowhere else is
// declared here as a net, of its original's type -- or, where the check writes
// `name[index]`, as a vector wide enough for every index written -- so that the
// module's own items can read it. What drives it is the simulator's
// (simulator/timing_check_delayed_signals.cpp): a copy of the original that
// §31.9.1 delays under the option enabling negative timing checks.

#include <algorithm>
#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_items_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_type.h"

namespace delta {
namespace {

// The declared type of every port and every net or variable of the module, by
// name, which is what a delayed signal is declared like and what tells a name
// the module declares from one it does not.
std::unordered_map<std::string_view, const DataType*> DeclaredTypes(
    const ModuleDecl* decl) {
  std::unordered_map<std::string_view, const DataType*> types;
  for (const auto& port : decl->ports) {
    if (!port.name.empty()) types[port.name] = &port.data_type;
  }
  for (const auto* item : decl->items) {
    if ((item->kind == ModuleItemKind::kNetDecl ||
         item->kind == ModuleItemKind::kVarDecl) &&
        !item->name.empty()) {
      types[item->name] = &item->data_type;
    }
  }
  return types;
}

Expr* MakeInteger(int64_t value, Arena& arena) {
  auto* lit = arena.Create<Expr>();
  lit->kind = ExprKind::kIntegerLiteral;
  lit->int_val = static_cast<uint64_t>(value);
  return lit;
}

// What one undeclared delayed name is to be declared as: the original a whole
// copy takes its type from, or the largest index written.
struct PendingNet {
  SourceLoc loc;
  const SpecifyTerminal* original = nullptr;
  bool indexed = false;
  int64_t max_index = 0;
};

class DelayedNetCollector {
 public:
  explicit DelayedNetCollector(const ModuleDecl* decl)
      : types_(DeclaredTypes(decl)) {}

  void Add(std::string_view name, const Expr* index,
           const SpecifyTerminal& original, SourceLoc loc) {
    if (name.empty() || types_.contains(name)) return;
    auto [it, fresh] = pending_.try_emplace(name);
    if (fresh) order_.push_back(name);
    PendingNet& net = it->second;
    net.loc = loc;
    if (index == nullptr) {
      net.original = &original;
      return;
    }
    int64_t idx = index->kind == ExprKind::kIntegerLiteral
                      ? static_cast<int64_t>(index->int_val)
                      : 0;
    net.max_index = net.indexed ? std::max(net.max_index, idx) : idx;
    net.indexed = true;
  }

  std::vector<ModuleItem*> Build(Arena& arena) const {
    std::vector<ModuleItem*> items;
    for (std::string_view name : order_) {
      const PendingNet& p = pending_.at(name);
      auto* net = arena.Create<ModuleItem>();
      net->kind = ModuleItemKind::kNetDecl;
      net->loc = p.loc;
      net->name = name;
      if (p.indexed) {
        net->data_type.packed_dim_left = MakeInteger(p.max_index, arena);
        net->data_type.packed_dim_right = MakeInteger(0, arena);
      } else if (p.original != nullptr &&
                 p.original->range_kind == SpecifyRangeKind::kNone) {
        auto it = types_.find(p.original->name);
        if (it != types_.end()) net->data_type = *it->second;
      }
      net->data_type.is_net = true;
      net->data_type.kind = DataTypeKind::kWire;
      items.push_back(net);
    }
    return items;
  }

 private:
  std::unordered_map<std::string_view, const DataType*> types_;
  std::unordered_map<std::string_view, PendingNet> pending_;
  std::vector<std::string_view> order_;
};

}  // namespace

std::vector<ModuleItem*> TimingCheckDelayedSignalItems(const ModuleDecl* decl,
                                                       Arena& arena) {
  DelayedNetCollector collector(decl);
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (const auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      const TimingCheckDecl& tc = si->timing_check;
      if (tc.check_kind != TimingCheckKind::kSetuphold &&
          tc.check_kind != TimingCheckKind::kRecrem) {
        continue;
      }
      collector.Add(tc.delayed_ref, tc.delayed_ref_expr, tc.ref_terminal,
                    si->loc);
      collector.Add(tc.delayed_data, tc.delayed_data_expr, tc.data_terminal,
                    si->loc);
    }
  }
  return collector.Build(arena);
}

}  // namespace delta
