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

// The names the expressions of `cg` read: its options' values, its
// coverpoints' expressions, guards and bins, and its crosses' guards, options
// and bins.
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

// Whether `name` is a formal of `cg`, of its covergroup or of its sample
// method (§19.8.1), which hides any property of that name.
bool IsFormalOf(const CovergroupDecl& cg, std::string_view name) {
  if (FindCovergroupFormal(cg, name) != nullptr) return true;
  for (const FunctionArg& formal : cg.event.sample_formals) {
    if (formal.name == name) return true;
  }
  return false;
}

// Whether `s` or a statement it holds satisfies `pred`.
bool AnyStmt(const Stmt* s, const std::function<bool(const Stmt*)>& pred) {
  if (s == nullptr) return false;
  if (pred(s)) return true;
  bool found = false;
  ForEachChildStmt(
      s, [&](const Stmt* sub) { found = found || AnyStmt(sub, pred); });
  return found;
}

// Whether `s` builds the covergroup `cg` of `cls`, assigning it a `new`.
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

// §19.3: each `new` the constructor statements `stmts` of `cls` build an
// instance of the covergroup `cg` with.
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

// Where a constructor initializes an instance constant relative to the
// statement building a covergroup that reads it.
enum class InitOrder : uint8_t { kUnknown, kInitFirst, kNewFirst, kTogether };

// The looping statements, and fork, which in a constructor is fork-join_none:
// a function holds no other fork (§13.4).
constexpr std::array<StmtKind, 7> kRepeatedOrForked = {
    StmtKind::kFor,    StmtKind::kForeach, StmtKind::kWhile, StmtKind::kForever,
    StmtKind::kRepeat, StmtKind::kDoWhile, StmtKind::kFork};

// A class whose constructor is read, with the names of an instance constant
// of it and of a covergroup it builds.
struct CtorOrder {
  const ClassDecl* cls;
  std::string_view constant;
  std::string_view cg;
};

// The order in which the statements `stmts` initialize the constant and build
// the covergroup `order` names: by the first statement doing either, a
// sequential block doing both being read in turn.
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

// A covergroup `cg` the class `cls` embeds, the unit holding the classes
// `cls` may extend, and where the reports go.
struct ClassSite {
  const ClassDecl* cls;
  const CovergroupDecl& cg;
  const CompilationUnit* unit;
  DiagEngine& diag;
};

// Whether `name` is an instance constant of `cls`: a const property declared
// without an initializer, which the constructor assigns (§8.19).
bool IsInstanceConstant(const ClassDecl* cls, std::string_view name,
                        const CompilationUnit* unit) {
  const ClassMember* m = FindMemberInClass(cls, name, unit);
  return m != nullptr && m->is_const && m->init_expr == nullptr;
}

// §19.5: each instance constant `read` of the class, read by the covergroup
// `cg`, is initialized in the constructor `ctor` before the statement
// building `cg`, and not in the same looping statement or fork-join_none.
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

// The constructor `cls` declares; null where it declares none.
const ModuleItem* Constructor(const ClassDecl* cls) {
  for (const ClassMember* m : cls->members) {
    if (m->name == "new") return m->method;
  }
  return nullptr;
}

// §19.4 with §8.18: a covergroup of a class covers no property local to a
// class it extends, the name `name` read at `loc` among them.
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

// CheckBaseLocal over the names a covergroup of a class reads and its cross
// items, and CheckInstanceConstant over the instance constants it reads where
// `ctor` is the class's constructor.
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
    // §19.4.1: a derived covergroup has its base's formals, which its own
    // declaration does not list.
    if (ctor != nullptr && m->covergroup->extends_base.empty()) {
      CheckConstructorNews(ctor->func_body_stmts, cls, *m->covergroup, diag);
    }
  }
}

}  // namespace delta
