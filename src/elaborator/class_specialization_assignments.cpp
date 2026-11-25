#include "elaborator/class_specialization_assignments.h"

#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_set>
#include <vector>

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

using AssignmentNames = std::vector<std::string_view>;

AssignmentNames NamesOf(const std::vector<DataType>& assignments) {
  AssignmentNames names;
  for (const DataType& value : assignments) {
    names.push_back(value.param_arg_name);
  }
  return names;
}

AssignmentNames NamesOfLast(const DataType& type) {
  if (type.scope_param_assignment_written && !type.param_assignment_written) {
    return {};
  }
  return NamesOf(type.type_params);
}

class SpecializationAssignmentWalk : public ScopedWalk {
 public:
  SpecializationAssignmentWalk(const CompilationUnit& unit, DiagEngine& diag)
      : ScopedWalk(unit), diag_(diag) {}

 private:
  void VisitExpr(const Expr& e, const NameScope& scope) override {
    if (!e.has_param_spec) return;
    const Site kSite{e.range.start, scope};
    if (e.kind == ExprKind::kMemberAccess) {
      if (e.lhs->kind != ExprKind::kIdentifier) return;
      JudgeNamed(e.lhs->text, e.rhs->text, e.arg_names, kSite);
    } else {
      JudgeNamed(e.scope_prefix, e.text, e.arg_names, kSite);
    }
  }

  void VisitType(const DataType& type, SourceLoc loc,
                 const NameScope& scope) override {
    for (const DataType& specialized : type.specialized_scopes) {
      Judge(specialized, NamesOf(specialized.type_params), {loc, scope});
    }
    if (type.kind == DataTypeKind::kNamed) {
      Judge(type, NamesOfLast(type), {loc, scope});
    }
  }

  void VisitClass(const ClassDecl& cls, const NameScope& scope) override {
    const Site kHeader{cls.range.start, *scope.outer};
    JudgeNamed(cls.base_class_scope, cls.base_class,
               NamesOf(cls.base_class_type_params), kHeader);
    for (const auto* refs : {&cls.extends_interfaces, &cls.implements_types}) {
      for (const InterfaceRef& ref : *refs) {
        JudgeNamed(ref.scope, ref.name, NamesOf(ref.type_params), kHeader);
      }
    }
  }

  struct Site {
    SourceLoc loc;
    const NameScope& scope;
  };

  void JudgeNamed(std::string_view scope_name, std::string_view name,
                  const AssignmentNames& names, const Site& site) {
    DataType named;
    named.kind = DataTypeKind::kNamed;
    named.scope_name = scope_name;
    named.type_name = name;
    Judge(named, names, site);
  }

  void Judge(const DataType& named, const AssignmentNames& names,
             const Site& site) {
    if (names.empty()) return;
    const ClassDecl* cls = Scopes().ClassDeclaredAs(named, site.scope);
    if (cls == nullptr) return;
    if (names.front().empty()) {
      JudgeCount(*cls, names.size(), site.loc);
    } else {
      JudgeNames(*cls, names, site.loc);
    }
  }

  void JudgeCount(const ClassDecl& cls, std::size_t provided, SourceLoc loc) {
    const std::size_t kAllowed = PortParameters(cls).size();
    if (provided <= kAllowed) return;
    diag_.ErrorOnce(loc,
                    std::format("too many positional parameter overrides for "
                                "class '{}': {} provided, {} allowed",
                                cls.name, provided, kAllowed),
                    Subclause("23.10.2.1"));
  }

  void JudgeNames(const ClassDecl& cls, const AssignmentNames& names,
                  SourceLoc loc) {
    const std::unordered_set<std::string_view> kPortParameters =
        PortParameters(cls);
    std::unordered_set<std::string_view> assigned;
    for (const std::string_view kName : names) {
      if (!kPortParameters.contains(kName)) {
        diag_.ErrorOnce(
            loc,
            std::format("class '{}' has no parameter '{}'", cls.name, kName),
            Subclause("23.10.2.2"));
      } else if (!assigned.insert(kName).second) {
        diag_.ErrorOnce(loc,
                        std::format("parameter '{}' of class '{}' is assigned "
                                    "more than once",
                                    kName, cls.name),
                        Subclause("23.10.2.2"));
      }
    }
  }

  static std::unordered_set<std::string_view> PortParameters(
      const ClassDecl& cls) {
    std::unordered_set<std::string_view> names;
    for (const auto& [name, value] : cls.params) {
      if (!cls.localparam_port_names.contains(name)) names.insert(name);
    }
    return names;
  }

  DiagEngine& diag_;
};

}  // namespace

void ReportClassSpecializationAssignments(const CompilationUnit& unit,
                                          DiagEngine& diag) {
  SpecializationAssignmentWalk(unit, diag).WalkUnit(unit);
}

}  // namespace delta
