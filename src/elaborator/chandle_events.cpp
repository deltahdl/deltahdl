#include "elaborator/chandle_events.h"

#include <algorithm>
#include <cstddef>
#include <initializer_list>
#include <ranges>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using ChandleNames = std::unordered_set<std::string_view>;

struct EventScan {
  const TypedefMap& typedefs;
  DiagEngine& diag;
};

bool IsChandleType(const DataType& type, const TypedefMap& typedefs) {
  std::vector<std::string_view> names;
  const DataType* resolved = FollowTypedefs(type, typedefs, names);
  return resolved != nullptr && resolved->kind == DataTypeKind::kChandle;
}

class VisibleNames {
 public:
  explicit VisibleNames(const ChandleNames& outer) : outer_(outer) {}

  void Declare(std::string_view name, bool is_chandle) {
    locals_.emplace_back(name, is_chandle);
  }

  bool NamesChandle(std::string_view name) const {
    auto reversed = locals_ | std::views::reverse;
    auto it = std::ranges::find_if(
        reversed, [&](const auto& local) { return local.first == name; });
    return it != reversed.end() ? it->second : outer_.contains(name);
  }

  size_t Mark() const { return locals_.size(); }

  void Restore(size_t mark) { locals_.resize(mark); }

 private:
  const ChandleNames& outer_;
  std::vector<std::pair<std::string_view, bool>> locals_;
};

void ReportEvents(const std::vector<EventExpr>& events, SourceLoc loc,
                  const VisibleNames& names, const EventScan& scan) {
  if (std::ranges::any_of(events, [&](const EventExpr& ev) {
        return names.NamesChandle(ExprIdent(ev.signal));
      })) {
    scan.diag.ErrorOnce(loc, "chandle cannot appear in event expression",
                        Subclause("6.14"));
  }
}

void WalkStmt(const Stmt* s, VisibleNames& names, const EventScan& scan) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) {
    names.Declare(s->var_name, IsChandleType(s->var_decl_type, scan.typedefs));
    return;
  }
  ReportEvents(s->events, s->range.start, names, scan);
  ReportEvents(s->assert_clock, s->range.start, names, scan);
  const size_t kMark = names.Mark();
  ForEachChildStmt(s, [&](Stmt* const& sub) { WalkStmt(sub, names, scan); });
  names.Restore(kMark);
}

ChandleNames ScopeNames(const std::vector<ModuleItem*>& items,
                        const ChandleNames& outer, const TypedefMap& typedefs) {
  ChandleNames names = outer;
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    if (IsChandleType(item->data_type, typedefs)) {
      names.insert(item->name);
    } else {
      names.erase(item->name);
    }
  }
  return names;
}

void WalkItem(const ModuleItem* item, const ChandleNames& outer,
              const EventScan& scan);

void WalkItems(const std::vector<ModuleItem*>& items, const ChandleNames& outer,
               const EventScan& scan) {
  const ChandleNames kNames = ScopeNames(items, outer, scan.typedefs);
  for (const ModuleItem* item : items) WalkItem(item, kNames, scan);
}

void WalkClass(const ClassDecl& cls, const ChandleNames& outer,
               const EventScan& scan) {
  ChandleNames names = outer;
  for (const ClassMember* m : cls.members) {
    if (m->kind != ClassMemberKind::kProperty) continue;
    if (IsChandleType(m->data_type, scan.typedefs)) {
      names.insert(m->name);
    } else {
      names.erase(m->name);
    }
  }
  for (const ClassMember* m : cls.members) {
    if (m->method != nullptr) WalkItem(m->method, names, scan);
    if (m->nested_class != nullptr) WalkClass(*m->nested_class, names, scan);
  }
}

void WalkItem(const ModuleItem* item, const ChandleNames& outer,
              const EventScan& scan) {
  VisibleNames names(outer);
  ReportEvents(item->sensitivity, item->loc, names, scan);
  ReportEvents(item->clocking_event, item->loc, names, scan);
  for (const FunctionArg& arg : item->func_args) {
    names.Declare(arg.name, IsChandleType(arg.data_type, scan.typedefs));
  }
  WalkStmt(item->body, names, scan);
  for (const Stmt* s : item->func_body_stmts) WalkStmt(s, names, scan);
  if (item->class_decl != nullptr) WalkClass(*item->class_decl, outer, scan);
  WalkItems(item->gen_body, outer, scan);
  if (item->gen_else != nullptr) WalkItem(item->gen_else, outer, scan);
  for (const GenerateCaseItem& ci : item->gen_case_items) {
    WalkItems(ci.body, outer, scan);
  }
}

void WalkScope(const std::vector<ModuleItem*>& items, const ChandleNames& outer,
               const TypedefMap& typedefs, DiagEngine& diag) {
  TypedefMap scoped = typedefs;
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kTypedef) {
      scoped.insert_or_assign(item->name, item->typedef_type);
    }
  }
  WalkItems(items, outer, {scoped, diag});
}

}  // namespace

void ReportChandleEvents(const CompilationUnit& unit,
                         const TypedefMap& typedefs, DiagEngine& diag) {
  const EventScan kUnitScan{typedefs, diag};
  const ChandleNames kUnitNames = ScopeNames(unit.cu_items, {}, typedefs);
  WalkItems(unit.cu_items, {}, kUnitScan);
  for (const ClassDecl* cls : unit.classes) {
    WalkClass(*cls, kUnitNames, kUnitScan);
  }
  for (const PackageDecl* pkg : unit.packages) {
    WalkScope(pkg->items, {}, typedefs, diag);
  }
  for (const auto* decls :
       {&unit.modules, &unit.interfaces, &unit.programs, &unit.checkers}) {
    for (const ModuleDecl* decl : *decls) {
      WalkScope(decl->items, kUnitNames, typedefs, diag);
    }
  }
}

}  // namespace delta
