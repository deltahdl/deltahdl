#include "elaborator/specparam_uses.h"

#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/scoped_walk.h"
#include "elaborator/specparam_paths.h"
#include "elaborator/unit_scope_order.h"
#include "elaborator/value_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

bool IsWithin(const Expr& e, const Expr* whole) {
  if (whole == nullptr) return false;
  return whole == &e || AnyExprChild(whole, [&e](const Expr* child) {
           return IsWithin(e, child);
         });
}

class SpecparamUseWalk : public ScopedWalk {
 public:
  SpecparamUseWalk(const CompilationUnit& unit, DiagEngine& diag)
      : ScopedWalk(unit), paths_(unit), diag_(diag) {
    for (const auto* decls :
         {&unit.modules, &unit.interfaces, &unit.programs, &unit.checkers}) {
      RecordScopes(*decls);
    }
  }

 private:
  void RecordScopes(const std::vector<ModuleDecl*>& decls) {
    for (const ModuleDecl* decl : decls) {
      elements_[&Scopes().ModuleScope(*decl)] = decl;
      std::vector<ModuleDecl*> nested;
      for (const ModuleItem* item : decl->items) {
        if (item->nested_module_decl != nullptr) {
          nested.push_back(item->nested_module_decl);
        }
      }
      RecordScopes(nested);
    }
  }

  void VisitExpr(const Expr& e, const NameScope& scope) override {
    for (const Expr* key : e.pattern_keys) names_of_members_.insert(key);
    switch (e.kind) {
      case ExprKind::kIdentifier:
      case ExprKind::kCast:
        if (!names_of_members_.contains(&e)) JudgeOrder(e, scope);
        break;
      case ExprKind::kMemberAccess:
        names_of_members_.insert(e.rhs);
        JudgePlace(e, scope);
        break;
      default:
        break;
    }
  }

  void VisitType(const DataType&, SourceLoc, const NameScope&) override {}

  void VisitClass(const ClassDecl&, const NameScope&) override {}

  void VisitRange(const Expr& bound, const NameScope& scope) override {
    const auto kJudge = [&](const Expr* e) {
      if ((e->kind != ExprKind::kIdentifier && e->kind != ExprKind::kCast) ||
          Scopes().ConstantNamed(e->text, scope) != ConstantKind::kSpecparam) {
        return;
      }
      diag_.Error(e->range.start,
                  std::format("specparam '{}' may not appear in a declaration "
                              "range specification",
                              e->text),
                  Subclause("6.20.5"));
    };
    ForEachExprUnder(&bound, kJudge);
  }

  void JudgeOrder(const Expr& e, const NameScope& scope) {
    const Expr* value = Scopes().ModuleSpecparamValue(e.text, scope);
    if (value == nullptr ||
        (!PrecedesInText(e.range.start, value->range.start) &&
         !IsWithin(e, value))) {
      return;
    }
    diag_.Error(
        e.range.start,
        std::format("specparam '{}' is referenced before its declaration",
                    e.text),
        Subclause("6.20.5"));
  }

  void JudgePlace(const Expr& access, const NameScope& scope) {
    const ModuleDecl* outermost = nullptr;
    for (const NameScope* at = &scope; at != nullptr; at = at->outer) {
      const auto kElement = elements_.find(at);
      if (kElement == elements_.end()) continue;
      outermost = kElement->second;
      if (outermost->decl_kind == ModuleDeclKind::kModule) return;
    }
    const InstancePath kPath = InstancePathOf(access);
    if (kPath.empty() || Scopes().Declares(kPath[0], scope) ||
        !paths_.EndsAtSpecparam(kPath, outermost)) {
      return;
    }
    diag_.Error(access.range.start,
                std::format("specparam '{}' may be used only inside a module "
                            "or a specify block",
                            access.rhs->text),
                Subclause("6.20.5"));
  }

  SpecparamPaths paths_;
  DiagEngine& diag_;
  std::unordered_map<const NameScope*, const ModuleDecl*> elements_;
  std::unordered_set<const Expr*> names_of_members_;
};

}  // namespace

void ReportMisusedSpecparams(const CompilationUnit& unit, DiagEngine& diag) {
  SpecparamUseWalk(unit, diag).WalkUnit(unit);
}

}  // namespace delta
