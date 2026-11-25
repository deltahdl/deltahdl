#include "elaborator/implicit_variable_calls.h"

#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/scoped_walk.h"
#include "elaborator/value_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

class ImplicitVariableWalk : public ScopedWalk {
 public:
  ImplicitVariableWalk(const CompilationUnit& unit, DiagEngine& diag)
      : ScopedWalk(unit), diag_(diag) {}

 private:
  void VisitExpr(const Expr& e, const NameScope& scope) override {
    if (e.kind == ExprKind::kSelect && e.base != nullptr) {
      Judge(*e.base, scope);
    }
    if (e.kind == ExprKind::kMemberAccess && !e.is_scope_resolution) {
      Judge(*e.lhs, scope);
    }
  }

  void VisitType(const DataType&, SourceLoc, const NameScope&) override {}

  void VisitClass(const ClassDecl&, const NameScope&) override {}

  void Judge(const Expr& e, const NameScope& scope) {
    if (e.kind != ExprKind::kMemberAccess || e.is_scope_resolution ||
        !IsBuiltinMethodNameWithoutArguments(e.rhs->text)) {
      return;
    }
    const ScopedValue kReceiver = Scopes().ValueOf(*e.lhs, scope);
    if (!Scopes().MethodOn(kReceiver, e.rhs->text, false).is_method ||
        !reported_.insert(&e).second) {
      return;
    }
    diag_.Error(e.rhs->range.start,
                "a built-in method call used as an implicit variable shall "
                "include its parentheses",
                Subclause("5.13"));
  }

  DiagEngine& diag_;
  std::unordered_set<const Expr*> reported_;
};

}  // namespace

void ReportBareCallsAsImplicitVariables(const CompilationUnit& unit,
                                        DiagEngine& diag) {
  ImplicitVariableWalk(unit, diag).WalkUnit(unit);
}

}  // namespace delta
