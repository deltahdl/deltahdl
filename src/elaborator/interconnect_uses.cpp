#include "elaborator/interconnect_uses.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/assertion_name_rules.h"
#include "elaborator/covergroup_expr_slots.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_assertion_text.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

using InterconnectNames = std::unordered_set<std::string_view>;

bool IsInterconnectNetLvalue(const Expr* e, const InterconnectNames& names) {
  if (e == nullptr || e->is_parenthesized) return false;
  switch (e->kind) {
    case ExprKind::kIdentifier:
      return names.count(e->text) != 0;
    case ExprKind::kSelect:
      return !ExprUsesInterconnect(e->index, names) &&
             !ExprUsesInterconnect(e->index_end, names) &&
             IsInterconnectNetLvalue(e->base, names);
    case ExprKind::kConcatenation:
    case ExprKind::kAssignmentPattern:
      return !e->elements.empty() &&
             std::ranges::all_of(e->elements, [&](const Expr* element) {
               return IsInterconnectNetLvalue(element, names);
             });
    default:
      return false;
  }
}

static bool ConnectionIsLegal(const Expr* e, const InterconnectNames& names) {
  return !ExprUsesInterconnect(e, names) || IsInterconnectNetLvalue(e, names);
}

static bool ValuesUseInterconnect(const ModuleItem& item,
                                  const InterconnectNames& names) {
  const Expr* const kValues[] = {item.gate_delay, item.gate_delay_fall,
                                 item.gate_delay_decay, item.inst_range_left,
                                 item.inst_range_right};
  auto uses = [&](const Expr* e) { return ExprUsesInterconnect(e, names); };
  return std::ranges::any_of(kValues, uses) ||
         std::ranges::any_of(item.inst_params,
                             [&](const auto& p) { return uses(p.second); }) ||
         std::ranges::any_of(item.inst_dims, [&](const auto& dim) {
           return uses(dim.first) || uses(dim.second);
         });
}

namespace {

constexpr std::string_view kInExpression =
    "interconnect net cannot be used in expression";
constexpr std::string_view kInProceduralExpression =
    "interconnect net cannot be used in a procedural expression";

void ReportUse(SourceLoc loc, std::string_view message, DiagEngine& diag) {
  diag.ErrorOnce(loc, std::string(message), Subclause("6.6.8"));
}

InterconnectNames HidingArgs(InterconnectNames names,
                             const std::vector<FunctionArg>& args) {
  for (const FunctionArg& arg : args) names.erase(arg.name);
  return names;
}

bool DeclaresInitialValue(ModuleItemKind kind) {
  return kind == ModuleItemKind::kNetDecl || kind == ModuleItemKind::kVarDecl ||
         kind == ModuleItemKind::kLetDecl;
}

bool IsSubroutine(ModuleItemKind kind) {
  return kind == ModuleItemKind::kFunctionDecl ||
         kind == ModuleItemKind::kTaskDecl;
}

void ReportSubroutineBody(const ModuleItem& item,
                          const InterconnectNames& names, DiagEngine& diag) {
  const InterconnectNames kVisible = HidingArgs(names, item.func_args);
  for (const Stmt* s : item.func_body_stmts) {
    CheckInterconnectProcContAssign(s, kVisible, diag);
    CheckInterconnectProceduralRead(s, kVisible, diag);
  }
}

bool AssertionReadsInterconnect(const ModuleItem& item,
                                const InterconnectNames& names) {
  return std::ranges::any_of(item.assertion_reads,
                             [&](const AssertionRead& read) {
                               return names.count(read.name) != 0 &&
                                      !AssertionItemDeclares(&item, read.name);
                             });
}

bool CovergroupUsesInterconnect(const CovergroupDecl& group,
                                const InterconnectNames& names) {
  const InterconnectNames kVisible =
      HidingArgs(HidingArgs(names, group.formals), group.event.sample_formals);
  bool uses = false;
  ForEachCovergroupExpr(group, [&](const Expr* e) {
    uses = uses || ExprUsesInterconnect(e, kVisible);
  });
  return uses;
}

bool ClockingUsesInterconnect(const ModuleItem& item,
                              const InterconnectNames& names) {
  return EventsUseInterconnect(item.clocking_event, names) ||
         std::ranges::any_of(
             item.clocking_signals, [&](const ClockingSignalDecl& signal) {
               return signal.hier_expr != nullptr
                          ? ExprUsesInterconnect(signal.hier_expr, names)
                          : names.count(signal.name) != 0;
             });
}

bool TerminalsNameInterconnect(const std::vector<SpecifyTerminal>& terminals,
                               const InterconnectNames& names) {
  return std::ranges::any_of(terminals, [&](const SpecifyTerminal& terminal) {
    return names.count(terminal.name) != 0;
  });
}

bool SpecifyItemUsesInterconnect(const SpecifyItem& spec,
                                 const InterconnectNames& names) {
  const SpecifyPathDecl& path = spec.path;
  const TimingCheckDecl& check = spec.timing_check;
  return TerminalsNameInterconnect(path.src_ports, names) ||
         TerminalsNameInterconnect(path.dst_ports, names) ||
         ExprUsesInterconnect(path.condition, names) ||
         ExprUsesInterconnect(path.data_source, names) ||
         names.count(check.ref_terminal.name) != 0 ||
         names.count(check.data_terminal.name) != 0 ||
         ExprUsesInterconnect(check.ref_condition, names) ||
         ExprUsesInterconnect(check.data_condition, names);
}

bool ItemExpressionUsesInterconnect(const ModuleItem& item,
                                    const InterconnectNames& names) {
  if (DeclaresInitialValue(item.kind) &&
      ExprUsesInterconnect(item.init_expr, HidingArgs(names, item.func_args)))
    return true;
  if (item.kind == ModuleItemKind::kClockingBlock &&
      ClockingUsesInterconnect(item, names))
    return true;
  if (item.covergroup != nullptr &&
      CovergroupUsesInterconnect(*item.covergroup, names))
    return true;
  return !item.assertion_reads.empty() &&
         AssertionReadsInterconnect(item, names);
}

}  // namespace

void ReportInterconnectInItem(const ModuleItem& item,
                              const InterconnectNames& names,
                              DiagEngine& diag) {
  if (names.empty()) return;
  if (ItemExpressionUsesInterconnect(item, names))
    ReportUse(item.loc, kInExpression, diag);
  if (IsSubroutine(item.kind)) ReportSubroutineBody(item, names, diag);
  if (IsProceduralItemKind(item.kind) &&
      EventsUseInterconnect(item.sensitivity, names))
    ReportUse(item.loc, kInProceduralExpression, diag);
  for (const SpecifyItem* spec : item.specify_items) {
    if (SpecifyItemUsesInterconnect(*spec, names))
      ReportUse(spec->loc, kInExpression, diag);
  }
}

void ReportInterconnectInCheckerArguments(const ModuleItem& item,
                                          const InterconnectNames& names,
                                          DiagEngine& diag) {
  if (std::ranges::none_of(item.inst_ports, [&](const auto& port) {
        return ExprUsesInterconnect(port.second, names);
      }))
    return;
  ReportUse(item.loc, kInExpression, diag);
}

void ReportInterconnectInInstance(const ModuleItem& item,
                                  const InterconnectNames& names,
                                  DiagEngine& diag) {
  if (names.empty()) return;
  auto legal = [&](const Expr* e) { return ConnectionIsLegal(e, names); };
  const bool kConnectionsLegal =
      std::ranges::all_of(item.gate_terminals, legal) &&
      std::ranges::all_of(item.inst_ports,
                          [&](const auto& port) { return legal(port.second); });
  if (kConnectionsLegal && !ValuesUseInterconnect(item, names)) return;
  diag.Error(item.loc, "interconnect net cannot be used in expression",
             Subclause("6.6.8"));
}

}  // namespace delta
