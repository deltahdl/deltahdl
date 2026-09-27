// §31.9.1 and §31.9.4 (printed pages 920-923): the delayed_reference and
// delayed_data a $setuphold or $recrem names are signals of the module, which
// "can be declared within the timing check so they can be used in the model's
// functional implementation". Without the invocation option that enables
// negative timing checks "the delayed reference and data signals become copies
// of the original reference and data signals", so each is a net driven by its
// original. The items built here are that net, where the module declares none
// of the name, and the continuous assignment copying the original into it;
// ElaborateItems elaborates them after the module's own items, so a name the
// module declares further down is found declared.

#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "elaborator/elaborator_items_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

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

Expr* MakeIdentifier(std::string_view name, Arena& arena) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = name;
  return id;
}

// The original signal a terminal names, with the select it was written with.
Expr* TerminalExpr(const SpecifyTerminal& t, Arena& arena) {
  Expr* id = MakeIdentifier(t.name, arena);
  if (t.range_kind == SpecifyRangeKind::kNone || t.range_left == nullptr) {
    return id;
  }
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = id;
  sel->index = t.range_left;
  if (t.range_kind != SpecifyRangeKind::kBitSelect) {
    sel->index_end = t.range_right;
    sel->is_part_select_plus = t.range_kind == SpecifyRangeKind::kPlusIndexed;
    sel->is_part_select_minus = t.range_kind == SpecifyRangeKind::kMinusIndexed;
  }
  return sel;
}

// One delayed signal of one check: its name, the index it was written with,
// and the terminal it is a copy of.
struct DelayedSignal {
  std::string_view name;
  Expr* index;
  const SpecifyTerminal* original;
  SourceLoc loc;
};

class DelayedSignalBuilder {
 public:
  DelayedSignalBuilder(const ModuleDecl* decl, Arena& arena)
      : types_(DeclaredTypes(decl)), arena_(arena) {}

  // §31.9.1 Example 3 has a signal with a delayed signal in some checks share
  // it with the others, so a name is declared and driven once however many
  // checks write it.
  void Add(const DelayedSignal& sig) {
    if (sig.name.empty() || sig.original->name.empty() ||
        !sig.original->interface_name.empty()) {
      return;
    }
    if (sig.index == nullptr && !driven_.insert(sig.name).second) return;
    if (!types_.contains(sig.name) && sig.index == nullptr) Declare(sig);
    auto* assign = arena_.Create<ModuleItem>();
    assign->kind = ModuleItemKind::kContAssign;
    assign->loc = sig.loc;
    Expr* lhs = MakeIdentifier(sig.name, arena_);
    if (sig.index != nullptr) {
      auto* sel = arena_.Create<Expr>();
      sel->kind = ExprKind::kSelect;
      sel->base = lhs;
      sel->index = sig.index;
      lhs = sel;
    }
    assign->assign_lhs = lhs;
    assign->assign_rhs = TerminalExpr(*sig.original, arena_);
    items_.push_back(assign);
  }

  std::vector<ModuleItem*> Take() { return std::move(items_); }

 private:
  // A net of the original's declared type -- its range and signedness -- or a
  // scalar where the original is itself undeclared.
  void Declare(const DelayedSignal& sig) {
    auto* net = arena_.Create<ModuleItem>();
    net->kind = ModuleItemKind::kNetDecl;
    net->loc = sig.loc;
    net->name = sig.name;
    auto it = types_.find(sig.original->name);
    if (it != types_.end() &&
        sig.original->range_kind == SpecifyRangeKind::kNone) {
      net->data_type = *it->second;
    }
    net->data_type.is_net = true;
    net->data_type.kind = DataTypeKind::kWire;
    types_[sig.name] = &net->data_type;
    items_.push_back(net);
  }

  std::unordered_map<std::string_view, const DataType*> types_;
  std::unordered_set<std::string_view> driven_;
  std::vector<ModuleItem*> items_;
  Arena& arena_;
};

}  // namespace

std::vector<ModuleItem*> TimingCheckDelayedSignalItems(const ModuleDecl* decl,
                                                       Arena& arena) {
  DelayedSignalBuilder builder(decl, arena);
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (const auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kTimingCheck) continue;
      const TimingCheckDecl& tc = si->timing_check;
      if (tc.check_kind != TimingCheckKind::kSetuphold &&
          tc.check_kind != TimingCheckKind::kRecrem) {
        continue;
      }
      builder.Add(
          {tc.delayed_ref, tc.delayed_ref_expr, &tc.ref_terminal, si->loc});
      builder.Add(
          {tc.delayed_data, tc.delayed_data_expr, &tc.data_terminal, si->loc});
    }
  }
  return builder.Take();
}

}  // namespace delta
