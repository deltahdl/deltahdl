#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct ConstClassProps {
  const ClassDecl* cls = nullptr;
  std::unordered_set<std::string_view> global_consts;
  std::unordered_set<std::string_view> instance_consts;
  std::unordered_set<std::string_view> inherited_instance_consts;
};

using HandleTypes = std::unordered_map<std::string_view, std::string_view>;

}  // namespace

static bool IsAssignStmt(const Stmt* s) {
  return s->kind == StmtKind::kBlockingAssign ||
         s->kind == StmtKind::kNonblockingAssign;
}

static void ReportConstPropertyWrite(std::string_view name, bool is_global,
                                     SourceLoc loc, DiagEngine& diag) {
  if (is_global) {
    diag.Error(loc, std::format("assignment to global constant '{}'", name),
               Subclause("8.19"));
  } else {
    diag.Error(
        loc,
        std::format("assignment to instance constant '{}' outside constructor",
                    name),
        Subclause("8.19"));
  }
}

static std::string_view OwnPropertyTargetName(const Expr* lhs,
                                              const ClassDecl* cls) {
  if (!lhs) return {};
  if (lhs->kind == ExprKind::kIdentifier) return lhs->text;
  if (lhs->kind != ExprKind::kMemberAccess || !lhs->lhs || !lhs->rhs) return {};
  if (lhs->lhs->kind != ExprKind::kIdentifier ||
      lhs->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  std::string_view self = lhs->is_scope_resolution ? cls->name : "this";
  return lhs->lhs->text == self ? lhs->rhs->text : std::string_view{};
}

std::string_view OwnPropertyAssigned(const Stmt* s, const ClassDecl* cls) {
  return IsAssignStmt(s) ? OwnPropertyTargetName(s->lhs, cls)
                         : std::string_view{};
}

static void WalkStmtsForConstClassProp(const Stmt* s,
                                       const ConstClassProps& props,
                                       bool in_constructor, DiagEngine& diag) {
  if (!s) return;
  if (IsAssignStmt(s)) {
    std::string_view name = OwnPropertyTargetName(s->lhs, props.cls);
    if (props.global_consts.count(name)) {
      ReportConstPropertyWrite(name, true, s->range.start, diag);
    } else if ((props.instance_consts.count(name) && !in_constructor) ||
               props.inherited_instance_consts.count(name)) {
      ReportConstPropertyWrite(name, false, s->range.start, diag);
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForConstClassProp(sub, props, in_constructor, diag);
  });
}

static void CollectConstClassProperties(ConstClassProps& props,
                                        DiagEngine& diag) {
  for (const auto* m : props.cls->members) {
    if (m->kind != ClassMemberKind::kProperty || !m->is_const) continue;
    if (!m->init_expr && m->is_static) {
      diag.Error(m->loc, "instance constant cannot be declared static",
                 Subclause("8.19"));
    }
    if (m->init_expr) {
      props.global_consts.insert(m->name);
    } else {
      props.instance_consts.insert(m->name);
    }
  }
}

static const ClassDecl* BaseOf(const ClassDecl* cls,
                               const CompilationUnit* unit) {
  return FindBaseClass(cls, unit);
}

static void AddBaseConstProperties(const ClassDecl* base,
                                   std::unordered_set<std::string_view>& seen,
                                   ConstClassProps& props) {
  for (const auto* m : base->members) {
    if (m->kind != ClassMemberKind::kProperty) continue;
    if (!seen.insert(m->name).second || !m->is_const) continue;
    auto& names =
        m->init_expr ? props.global_consts : props.inherited_instance_consts;
    names.insert(m->name);
  }
}

static void CollectInheritedConstProperties(ConstClassProps& props,
                                            const CompilationUnit* unit) {
  std::unordered_set<std::string_view> seen;
  for (const auto* m : props.cls->members) {
    if (m->kind == ClassMemberKind::kProperty) seen.insert(m->name);
  }
  std::unordered_set<const ClassDecl*> visited{props.cls};
  for (const ClassDecl* c = BaseOf(props.cls, unit);
       c != nullptr && visited.insert(c).second; c = BaseOf(c, unit)) {
    AddBaseConstProperties(c, seen, props);
  }
}

static void CheckInstanceConstSingleAssign(const ModuleItem* ctor,
                                           const ConstClassProps& props,
                                           DiagEngine& diag) {
  std::unordered_map<std::string_view, int> counts;
  for (const auto* s : ctor->func_body_stmts) {
    if (!s || !IsAssignStmt(s)) continue;
    std::string_view name = OwnPropertyTargetName(s->lhs, props.cls);
    if (!props.instance_consts.count(name)) continue;
    if (++counts[name] == 2) {
      diag.Error(s->range.start,
                 std::format("instance constant '{}' is assigned more than "
                             "once in the constructor",
                             name),
                 Subclause("8.19"));
    }
  }
}

static bool ClassDeclaredAmong(std::string_view name,
                               const std::vector<ModuleItem*>& items) {
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl->name == name) {
      return true;
    }
  }
  return false;
}

static void CheckConstClassPropsInMethod(const ModuleItem* method,
                                         const ConstClassProps& props,
                                         DiagEngine& diag) {
  bool is_ctor = method->name == "new";
  for (const auto* s : method->func_body_stmts) {
    WalkStmtsForConstClassProp(s, props, is_ctor, diag);
  }
  if (is_ctor) CheckInstanceConstSingleAssign(method, props, diag);
}

static const ClassMember* FindPropertyInHierarchy(const ClassDecl* cls,
                                                  std::string_view name,
                                                  const CompilationUnit* unit) {
  std::unordered_set<const ClassDecl*> visited;
  for (const ClassDecl* c = cls; c != nullptr && visited.insert(c).second;
       c = BaseOf(c, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kProperty && m->name == name) return m;
    }
  }
  return nullptr;
}

static const ClassMember* ConstPropertyOfQualifiedTarget(
    const Expr* lhs, const HandleTypes& handles, const CompilationUnit* unit) {
  if (!lhs || lhs->kind != ExprKind::kMemberAccess || !lhs->lhs || !lhs->rhs)
    return nullptr;
  if (lhs->lhs->kind != ExprKind::kIdentifier ||
      lhs->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  std::string_view class_name = lhs->lhs->text;
  if (!lhs->is_scope_resolution) {
    auto it = handles.find(class_name);
    if (it == handles.end()) return nullptr;
    class_name = it->second;
  }
  const ClassMember* m = FindPropertyInHierarchy(
      FindClassDecl(class_name, unit), lhs->rhs->text, unit);
  return (m != nullptr && m->is_const) ? m : nullptr;
}

static void RecordHandle(std::string_view name, const DataType& type,
                         const CompilationUnit* unit, HandleTypes& handles) {
  if (type.kind == DataTypeKind::kNamed &&
      FindClassDecl(type.type_name, unit) != nullptr) {
    handles[name] = type.type_name;
  }
}

static void WalkStmtsForQualifiedConstWrites(const Stmt* s,
                                             const ClassDecl* own,
                                             HandleTypes& handles,
                                             const CompilationUnit* unit,
                                             DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl) {
    RecordHandle(s->var_name, s->var_decl_type, unit, handles);
  }
  bool own_target = own != nullptr && IsAssignStmt(s) &&
                    !OwnPropertyTargetName(s->lhs, own).empty();
  if (IsAssignStmt(s) && !own_target) {
    if (const ClassMember* m =
            ConstPropertyOfQualifiedTarget(s->lhs, handles, unit)) {
      ReportConstPropertyWrite(m->name, m->init_expr != nullptr, s->range.start,
                               diag);
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForQualifiedConstWrites(sub, own, handles, unit, diag);
  });
}

static void WalkSubroutineForQualifiedConstWrites(const ModuleItem* sub,
                                                  const ClassDecl* own,
                                                  HandleTypes handles,
                                                  const CompilationUnit* unit,
                                                  DiagEngine& diag) {
  for (const auto& arg : sub->func_args) {
    RecordHandle(arg.name, arg.data_type, unit, handles);
  }
  for (const auto* s : sub->func_body_stmts) {
    WalkStmtsForQualifiedConstWrites(s, own, handles, unit, diag);
  }
}

void ElaboratorClassRules::ValidateConstClassProperties() {
  for (const auto* cls : AllClassDecls(unit_)) {
    ConstClassProps props;
    props.cls = cls;
    CollectConstClassProperties(props, diag_);
    CollectInheritedConstProperties(props, unit_);
    HandleTypes handles;
    for (const auto* m : cls->members) {
      if (m->kind == ClassMemberKind::kProperty) {
        RecordHandle(m->name, m->data_type, unit_, handles);
      }
    }
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      const ModuleItem* body = MethodBody(m->method);
      CheckConstClassPropsInMethod(body, props, diag_);
      WalkSubroutineForQualifiedConstWrites(body, cls, handles, unit_, diag_);
    }
  }
}

void ElaboratorClassRules::ValidateConstPropertyWritesFromOutside(
    const ModuleDecl* decl) {
  if (class_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      if (!item->method_class.empty() &&
          ClassDeclaredAmong(item->method_class, decl->items)) {
        continue;
      }
      WalkSubroutineForQualifiedConstWrites(item, nullptr, class_var_types_,
                                            unit_, diag_);
      continue;
    }
    if (!IsProceduralItemKind(item->kind) || !item->body) continue;
    HandleTypes handles = class_var_types_;
    WalkStmtsForQualifiedConstWrites(item->body, nullptr, handles, unit_,
                                     diag_);
  }
}

}  // namespace delta
