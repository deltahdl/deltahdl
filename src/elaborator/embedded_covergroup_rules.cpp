#include "elaborator/embedded_covergroup_rules.h"

#include <algorithm>
#include <array>
#include <cstdint>
#include <format>
#include <functional>
#include <initializer_list>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/covergroup_context.h"
#include "elaborator/covergroup_instance_rules.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using Reads = std::vector<const Expr*>;

void CollectRanges(const std::vector<CovergroupValueRange>& ranges,
                   Reads& reads) {
  for (const CovergroupValueRange& range : ranges) {
    CollectBareIdents(range.lo, reads);
    CollectBareIdents(range.hi, reads);
  }
}

void CollectBinsReads(const BinsOrOptions& bins, Reads& reads) {
  CollectBareIdents(bins.option.value, reads);
  CollectRanges(bins.ranges, reads);
  for (const TransSet& set : bins.transitions) {
    for (const TransRangeList& step : set.steps) {
      CollectRanges(step.items, reads);
      CollectBareIdents(step.repeat_lo, reads);
      CollectBareIdents(step.repeat_hi, reads);
    }
  }
  for (const Expr* e :
       {bins.array_size, bins.with_expr, bins.set_expr, bins.iff}) {
    CollectBareIdents(e, reads);
  }
}

void CollectSelectReads(const SelectExpression* s, Reads& reads) {
  if (s == nullptr) return;
  CollectRanges(s->intersect, reads);
  CollectBareIdents(s->expr, reads);
  CollectBareIdents(s->matches, reads);
  CollectSelectReads(s->lhs, reads);
  CollectSelectReads(s->rhs, reads);
}

void CollectCrossReads(const CoverCrossDecl& cross, Reads& reads) {
  CollectBareIdents(cross.iff, reads);
  for (const CrossBodyItem& body : cross.body) {
    CollectBareIdents(body.option.value, reads);
    CollectSelectReads(body.bins.select, reads);
    CollectBareIdents(body.bins.iff, reads);
  }
}

Reads CovergroupReads(const CovergroupDecl& cg) {
  Reads reads;
  for (const CoverageSpecOrOption& item : cg.items) {
    if (item.kind == CoverageSpecKind::kOption) {
      CollectBareIdents(item.option.value, reads);
    } else if (item.kind == CoverageSpecKind::kCoverPoint) {
      CollectBareIdents(item.cover_point->expr, reads);
      CollectBareIdents(item.cover_point->iff, reads);
      for (const BinsOrOptions& bins : item.cover_point->bins) {
        CollectBinsReads(bins, reads);
      }
    } else {
      CollectCrossReads(*item.cover_cross, reads);
    }
  }
  return reads;
}

bool IsFormalOf(const CovergroupDecl& cg, std::string_view name) {
  if (FindCovergroupFormal(cg, name) != nullptr) return true;
  for (const FunctionArg& formal : cg.event.sample_formals) {
    if (formal.name == name) return true;
  }
  return false;
}

bool AnyStmt(const Stmt* s, const std::function<bool(const Stmt*)>& pred) {
  if (s == nullptr) return false;
  if (pred(s)) return true;
  bool found = false;
  ForEachChildStmt(
      s, [&](const Stmt* sub) { found = found || AnyStmt(sub, pred); });
  return found;
}

bool BuildsCovergroupAt(const Stmt* s, const ClassDecl* cls,
                        std::string_view cg) {
  return OwnPropertyAssigned(s, cls) == cg && s->rhs->text == "new";
}

bool AssignsTo(const Stmt* s, const ClassDecl* cls, std::string_view name) {
  return AnyStmt(
      s, [&](const Stmt* t) { return OwnPropertyAssigned(t, cls) == name; });
}

bool BuildsCovergroup(const Stmt* s, const ClassDecl* cls,
                      std::string_view cg) {
  return AnyStmt(s,
                 [&](const Stmt* t) { return BuildsCovergroupAt(t, cls, cg); });
}

void CheckConstructorNews(const std::vector<Stmt*>& stmts, const ClassDecl* cls,
                          const CovergroupDecl& cg, DiagEngine& diag) {
  const CovergroupDeclared kNoNets = [](std::string_view) { return false; };
  for (const Stmt* s : stmts) {
    AnyStmt(s, [&](const Stmt* t) {
      if (BuildsCovergroupAt(t, cls, cg.name)) {
        CheckCovergroupNewActuals(t->rhs, cg, kNoNets, diag);
      }
      return false;
    });
  }
}

enum class InitOrder : uint8_t { kUnknown, kInitFirst, kNewFirst, kTogether };

constexpr std::array<StmtKind, 7> kRepeatedOrForked = {
    StmtKind::kFor,    StmtKind::kForeach, StmtKind::kWhile, StmtKind::kForever,
    StmtKind::kRepeat, StmtKind::kDoWhile, StmtKind::kFork};

struct CtorOrder {
  const ClassDecl* cls;
  std::string_view constant;
  std::string_view cg;
};

InitOrder OrderIn(const std::vector<Stmt*>& stmts, const CtorOrder& order) {
  for (const Stmt* s : stmts) {
    bool init = AssignsTo(s, order.cls, order.constant);
    bool built = BuildsCovergroup(s, order.cls, order.cg);
    if (init && built) {
      if (std::ranges::find(kRepeatedOrForked, s->kind) !=
          kRepeatedOrForked.end()) {
        return InitOrder::kTogether;
      }
      return s->kind == StmtKind::kBlock ? OrderIn(s->stmts, order)
                                         : InitOrder::kUnknown;
    }
    if (init) return InitOrder::kInitFirst;
    if (built) return InitOrder::kNewFirst;
  }
  return InitOrder::kUnknown;
}

struct ClassSite {
  const ClassDecl* cls;
  const CovergroupDecl& cg;
  const CompilationUnit* unit;
  DiagEngine& diag;
};

bool IsInstanceConstant(const ClassDecl* cls, std::string_view name,
                        const CompilationUnit* unit) {
  const ClassMember* m = FindMemberInClass(cls, name, unit);
  return m != nullptr && m->is_const && m->init_expr == nullptr;
}

void CheckInstanceConstant(const Expr* read, const ClassSite& site,
                           const ModuleItem* ctor) {
  const CovergroupDecl& cg = site.cg;
  DiagEngine& diag = site.diag;
  const std::vector<Stmt*>& stmts = ctor->func_body_stmts;
  InitOrder order = OrderIn(stmts, {site.cls, read->text, cg.name});
  bool assigned = false;
  for (const Stmt* s : stmts) {
    assigned = assigned || AssignsTo(s, site.cls, read->text);
  }
  if (order == InitOrder::kNewFirst && assigned) {
    diag.Error(read->range.start,
               std::format("instance constant '{}', which covergroup '{}' "
                           "reads, is initialized after the covergroup's new "
                           "in the constructor",
                           read->text, cg.name),
               Subclause("19.5"));
  } else if (order == InitOrder::kTogether) {
    diag.Error(read->range.start,
               std::format("instance constant '{}', which covergroup '{}' "
                           "reads, is initialized in the same looping "
                           "statement or fork-join_none as the covergroup's "
                           "new",
                           read->text, cg.name),
               Subclause("19.5"));
  }
}

const ModuleItem* Constructor(const ClassDecl* cls) {
  for (const ClassMember* m : cls->members) {
    if (m->name == "new") return m->method;
  }
  return nullptr;
}

void CheckBaseLocal(const ClassSite& site, std::string_view name,
                    SourceLoc loc) {
  if (IsFormalOf(site.cg, name)) return;
  OwnedMember found = FindMemberAndOwner(site.cls, name, site.unit);
  if (found.member == nullptr || !found.member->is_local ||
      found.owner == site.cls) {
    return;
  }
  site.diag.Error(
      loc,
      std::format("covergroup '{}' of class '{}' cannot cover "
                  "'{}', a property local to its base class '{}'",
                  site.cg.name, site.cls->name, name, found.owner->name),
      Subclause("19.4"));
}

void CheckCovergroupOfClass(const ClassSite& site, const ModuleItem* ctor) {
  for (const Expr* read : CovergroupReads(site.cg)) {
    CheckBaseLocal(site, read->text, read->range.start);
    if (ctor != nullptr && !IsFormalOf(site.cg, read->text) &&
        IsInstanceConstant(site.cls, read->text, site.unit)) {
      CheckInstanceConstant(read, site, ctor);
    }
  }
  for (const CoverageSpecOrOption& item : site.cg.items) {
    if (item.kind != CoverageSpecKind::kCoverCross) continue;
    for (const CrossItem& cross_item : item.cover_cross->items) {
      CheckBaseLocal(site, cross_item.name, cross_item.loc);
    }
  }
}

}  // namespace

void CheckEmbeddedCovergroupUses(const ClassDecl* cls,
                                 const CompilationUnit* unit,
                                 DiagEngine& diag) {
  const ModuleItem* ctor = Constructor(cls);
  for (const ClassMember* m : cls->members) {
    if (m->kind != ClassMemberKind::kCovergroup) continue;
    CheckCovergroupOfClass({cls, *m->covergroup, unit, diag}, ctor);
    if (ctor != nullptr && m->covergroup->extends_base.empty()) {
      CheckConstructorNews(ctor->func_body_stmts, cls, *m->covergroup, diag);
    }
  }
}

}  // namespace delta
