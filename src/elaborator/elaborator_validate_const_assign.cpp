#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/string_methods.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/parser_token_skips.h"

namespace delta {

namespace {

enum class Constness : uint8_t { kWritable, kConstant, kConstantHandle };

struct DeclaredName {
  Constness constness = Constness::kWritable;
  const ModuleDecl* instance_of = nullptr;
};

using SubroutineTable = std::unordered_map<std::string_view, const ModuleItem*>;

struct ConstantWriteTables {
  const CompilationUnit* unit;
  const NameSet& class_names;
  const NameSet& enum_members;
  const SubroutineTable* subroutines;
};

bool IsHandleType(const DataType& type, const NameSet& class_names) {
  return type.kind == DataTypeKind::kVirtualInterface ||
         (type.kind == DataTypeKind::kNamed &&
          class_names.count(type.type_name) != 0);
}

Constness ConstnessOfVariable(bool is_const, const DataType& type,
                              const NameSet& class_names) {
  if (!is_const) return Constness::kWritable;
  return IsHandleType(type, class_names) ? Constness::kConstantHandle
                                         : Constness::kConstant;
}

std::optional<Constness> ConstnessOfItem(const ModuleItem* item,
                                         const NameSet& class_names) {
  switch (item->kind) {
    case ModuleItemKind::kParamDecl:
    case ModuleItemKind::kSpecparam:
      return Constness::kConstant;
    case ModuleItemKind::kVarDecl:
      return ConstnessOfVariable(item->data_type.is_const, item->data_type,
                                 class_names);
    case ModuleItemKind::kNetDecl:
      return Constness::kWritable;
    default:
      return std::nullopt;
  }
}

std::optional<Constness> ConstnessAmong(const std::vector<ModuleItem*>& items,
                                        std::string_view name,
                                        const NameSet& class_names) {
  for (const ModuleItem* item : items) {
    if (item->name != name) continue;
    if (auto constness = ConstnessOfItem(item, class_names)) return constness;
  }
  return std::nullopt;
}

std::optional<Constness> ConstnessInModule(const ModuleDecl* decl,
                                           std::string_view name,
                                           const NameSet& class_names) {
  for (const auto& [param, value] : decl->params) {
    if (param == name) return Constness::kConstant;
  }
  if (DeclaredSpecparamNames(decl).contains(name)) return Constness::kConstant;
  return ConstnessAmong(decl->items, name, class_names);
}

std::optional<Constness> ConstnessInClass(const ClassDecl* cls,
                                          std::string_view name) {
  for (const auto& [param, value] : cls->params) {
    if (param == name) return Constness::kConstant;
  }
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty && m->name == name)
      return m->is_param ? Constness::kConstant : Constness::kWritable;
  }
  return std::nullopt;
}

NameSet ClassNamesIn(const NameSet& known, const CompilationUnit* unit) {
  NameSet names = known;
  for (const ClassDecl* cls : unit->classes) names.insert(cls->name);
  for (const PackageDecl* pkg : unit->packages) {
    for (const ModuleItem* item : pkg->items) {
      if (item->kind == ModuleItemKind::kClassDecl) names.insert(item->name);
    }
  }
  return names;
}

const ModuleDecl* FindDefinition(const CompilationUnit* unit,
                                 std::string_view name) {
  for (const auto* group :
       {&unit->modules, &unit->interfaces, &unit->programs}) {
    for (const ModuleDecl* decl : *group) {
      if (decl->name == name) return decl;
    }
  }
  return nullptr;
}

const PackageDecl* FindPackage(const CompilationUnit* unit,
                               std::string_view name) {
  for (const PackageDecl* pkg : unit->packages) {
    if (pkg->name == name) return pkg;
  }
  return nullptr;
}

const ModuleDecl* ChildInstanceModule(const CompilationUnit* unit,
                                      const ModuleDecl* decl,
                                      std::string_view instance) {
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kModuleInst &&
        item->inst_name == instance)
      return FindDefinition(unit, item->inst_module);
  }
  return nullptr;
}

bool IsIncOrDec(const Expr* e) {
  return (e->kind == ExprKind::kUnary || e->kind == ExprKind::kPostfixUnary) &&
         (e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus);
}

bool IsAssignmentExpr(const Expr* e) {
  return e->kind == ExprKind::kBinary &&
         (e->op == TokenKind::kEq || IsCompoundAssignOp(e->op));
}

bool IsCompoundAssignmentOf(const Stmt* s, const Expr* e) {
  return s->kind == StmtKind::kBlockingAssign && e != nullptr && e == s->rhs &&
         e->kind == ExprKind::kBinary && IsCompoundAssignOp(e->op) &&
         e->lhs == s->lhs;
}

bool IsLvalueAggregate(const Expr* e) {
  return e->kind == ExprKind::kConcatenation ||
         e->kind == ExprKind::kReplicate ||
         e->kind == ExprKind::kStreamingConcat ||
         e->kind == ExprKind::kAssignmentPattern;
}

const Expr* WithoutSelects(const Expr* e) {
  while (e->kind == ExprKind::kSelect && e->base != nullptr) e = e->base;
  return e;
}

const Expr* MemberRoot(const Expr* e) {
  while (e != nullptr) {
    if (e->kind == ExprKind::kSelect) {
      e = e->base;
    } else if (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution) {
      e = e->lhs;
    } else {
      break;
    }
  }
  return e != nullptr && e->kind == ExprKind::kIdentifier ? e : nullptr;
}

bool AppendMemberPath(const Expr* e, std::vector<std::string_view>& path) {
  if (e->kind == ExprKind::kIdentifier) {
    path.push_back(e->text);
    return true;
  }
  if (e->kind != ExprKind::kMemberAccess || e->lhs == nullptr ||
      e->rhs == nullptr || e->rhs->kind != ExprKind::kIdentifier)
    return false;
  if (!AppendMemberPath(e->lhs, path)) return false;
  path.push_back(e->rhs->text);
  return true;
}

std::string JoinedPath(const std::vector<std::string_view>& path) {
  std::string joined;
  for (std::string_view part : path) {
    if (!joined.empty()) joined += '.';
    joined += part;
  }
  return joined;
}

std::string_view WritingDirection(const FunctionArg& formal) {
  switch (formal.direction) {
    case Direction::kOutput:
      return "output";
    case Direction::kInout:
      return "inout";
    case Direction::kRef:
      return formal.is_const ? "" : "ref";
    default:
      return "";
  }
}

class ConstantWriteWalk {
 public:
  ConstantWriteWalk(const ConstantWriteTables& tables, DiagEngine& diag)
      : tables_(tables), diag_(diag) {}

  void DeclareModule(const ModuleDecl* decl);
  void DeclareItems(const std::vector<ModuleItem*>& items);
  void WalkItems(const std::vector<ModuleItem*>& items);
  void WalkScope(const std::vector<ModuleItem*>& items);
  void WalkClass(const ClassDecl* cls);

 private:
  struct Mark {
    size_t names;
    size_t subroutines;
    size_t imports;
    size_t classes;
  };

  Mark Here() const {
    return {names_.size(), subroutines_.size(), imports_.size(),
            classes_.size()};
  }
  void Restore(const Mark& mark);
  void Declare(std::string_view name, Constness constness,
               const ModuleDecl* instance_of = nullptr) {
    names_.emplace_back(name, DeclaredName{constness, instance_of});
  }
  void DeclareItem(const ModuleItem* item);
  void DeclareClass(const ClassDecl* cls);
  void DeclareClassMembers(const ClassDecl* cls);
  void DeclareLoopVariables(const Stmt* s);

  std::optional<DeclaredName> Find(std::string_view name) const;
  std::optional<Constness> ImportedConstness(std::string_view name) const;
  const ClassDecl* FindClass(std::string_view name) const;
  const ModuleItem* FindSubroutine(std::string_view name) const;
  std::optional<Constness> ScopeMemberConstness(std::string_view scope,
                                                std::string_view name) const;

  std::string WrittenConstant(const Expr* target) const;
  std::string ScopedConstant(const Expr* e) const;
  std::string MemberConstant(const Expr* e) const;
  std::string HierarchicalConstant(
      const ModuleDecl* decl, const std::vector<std::string_view>& path) const;
  void ForEachWrittenConstant(
      const Expr* target,
      const std::function<void(const std::string&)>& report) const;

  void WalkItem(const ModuleItem* item);
  void WalkSubroutine(const ModuleItem* item);
  void WalkOutOfBlockMethod(const ModuleItem* item);
  void WalkGenerate(const ModuleItem* item);
  void WalkStmt(const Stmt* s);
  void CheckStmt(const Stmt* s);
  void CheckExpr(const Expr* e);
  void CheckStringMethod(const Expr* call);
  void CheckActuals(const Expr* call);
  void ReportTarget(const Expr* target, SourceLoc loc);
  void ReportNonVariableTarget(const Expr* lhs, const Stmt* s);

  const ConstantWriteTables& tables_;
  DiagEngine& diag_;
  std::vector<std::pair<std::string_view, DeclaredName>> names_;
  std::vector<const ModuleItem*> subroutines_;
  std::vector<const ImportItem*> imports_;
  std::vector<const ClassDecl*> classes_;
};

void ConstantWriteWalk::Restore(const Mark& mark) {
  names_.resize(mark.names);
  subroutines_.resize(mark.subroutines);
  imports_.resize(mark.imports);
  classes_.resize(mark.classes);
}

void ConstantWriteWalk::DeclareModule(const ModuleDecl* decl) {
  for (const auto& [param, value] : decl->params) {
    Declare(param, Constness::kConstant);
  }
  for (std::string_view specparam : DeclaredSpecparamNames(decl)) {
    Declare(specparam, Constness::kConstant);
  }
  for (const PortDecl& port : decl->ports) {
    const ModuleDecl* bound =
        port.is_interface_port
            ? FindDefinition(tables_.unit, port.data_type.type_name)
            : nullptr;
    Declare(port.name, Constness::kWritable, bound);
  }
  DeclareItems(decl->items);
}

void ConstantWriteWalk::DeclareItems(const std::vector<ModuleItem*>& items) {
  for (const ModuleItem* item : items) DeclareItem(item);
}

void ConstantWriteWalk::DeclareItem(const ModuleItem* item) {
  switch (item->kind) {
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:
    case ModuleItemKind::kDpiImport:
      if (item->method_class.empty()) subroutines_.push_back(item);
      return;
    case ModuleItemKind::kImportDecl:
      imports_.push_back(&item->import_item);
      return;
    case ModuleItemKind::kModuleInst:
      Declare(item->inst_name, Constness::kWritable,
              FindDefinition(tables_.unit, item->inst_module));
      return;
    case ModuleItemKind::kClassDecl:
      classes_.push_back(item->class_decl);
      return;
    default:
      break;
  }
  if (auto constness = ConstnessOfItem(item, tables_.class_names))
    Declare(item->name, *constness);
}

void ConstantWriteWalk::DeclareClass(const ClassDecl* cls) {
  std::vector<const ClassDecl*> lineage;
  for (const ClassDecl* c = cls;
       c != nullptr &&
       std::find(lineage.begin(), lineage.end(), c) == lineage.end();
       c = FindBaseClass(c, tables_.unit)) {
    lineage.push_back(c);
  }
  for (auto it = lineage.rbegin(); it != lineage.rend(); ++it) {
    DeclareClassMembers(*it);
  }
}

void ConstantWriteWalk::DeclareClassMembers(const ClassDecl* cls) {
  for (const auto& [param, value] : cls->params) {
    Declare(param, Constness::kConstant);
  }
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty) {
      Declare(m->name,
              m->is_param ? Constness::kConstant : Constness::kWritable);
    } else if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
      subroutines_.push_back(m->method);
    }
  }
}

void ConstantWriteWalk::DeclareLoopVariables(const Stmt* s) {
  for (size_t i = 0; i < s->for_inits.size() && i < s->for_init_types.size();
       ++i) {
    if (s->for_init_types[i].kind == DataTypeKind::kImplicit) continue;
    Declare(ExprIdent(s->for_inits[i]->lhs), Constness::kWritable);
  }
  for (std::string_view var : s->foreach_vars) {
    Declare(var, Constness::kWritable);
  }
}

std::optional<DeclaredName> ConstantWriteWalk::Find(
    std::string_view name) const {
  for (auto it = names_.rbegin(); it != names_.rend(); ++it) {
    if (it->first == name) return it->second;
  }
  if (auto constness = ImportedConstness(name))
    return DeclaredName{*constness, nullptr};
  return std::nullopt;
}

std::optional<Constness> ConstantWriteWalk::ImportedConstness(
    std::string_view name) const {
  for (const ImportItem* import : imports_) {
    if (!import->is_wildcard && import->item_name != name) continue;
    const PackageDecl* pkg = FindPackage(tables_.unit, import->package_name);
    std::optional<Constness> constness =
        pkg == nullptr ? std::nullopt
                       : ConstnessAmong(pkg->items, name, tables_.class_names);
    if (constness.has_value()) return constness;
  }
  return std::nullopt;
}

const ClassDecl* ConstantWriteWalk::FindClass(std::string_view name) const {
  for (auto it = classes_.rbegin(); it != classes_.rend(); ++it) {
    if ((*it)->name == name) return *it;
  }
  return FindClassDecl(name, tables_.unit);
}

const ModuleItem* ConstantWriteWalk::FindSubroutine(
    std::string_view name) const {
  for (auto it = subroutines_.rbegin(); it != subroutines_.rend(); ++it) {
    if ((*it)->name == name) return *it;
  }
  if (tables_.subroutines == nullptr) return nullptr;
  auto it = tables_.subroutines->find(name);
  return it == tables_.subroutines->end() ? nullptr : it->second;
}

std::optional<Constness> ConstantWriteWalk::ScopeMemberConstness(
    std::string_view scope, std::string_view name) const {
  if (scope == "$unit")
    return ConstnessAmong(tables_.unit->cu_items, name, tables_.class_names);
  if (const PackageDecl* pkg = FindPackage(tables_.unit, scope))
    return ConstnessAmong(pkg->items, name, tables_.class_names);
  const ClassDecl* cls = FindClass(scope);
  return cls == nullptr ? std::nullopt : ConstnessInClass(cls, name);
}

std::string ConstantWriteWalk::WrittenConstant(const Expr* target) const {
  const Expr* e = WithoutSelects(target);
  if (e->kind == ExprKind::kIdentifier) {
    std::optional<DeclaredName> declared = Find(e->text);
    bool constant =
        declared.has_value() && declared->constness != Constness::kWritable;
    return constant ? std::string(e->text) : std::string();
  }
  if (e->kind != ExprKind::kMemberAccess) return {};
  return e->is_scope_resolution ? ScopedConstant(e) : MemberConstant(e);
}

std::string ConstantWriteWalk::ScopedConstant(const Expr* e) const {
  std::string_view scope = ExprIdent(e->lhs);
  std::string_view name = ExprIdent(e->rhs);
  std::optional<Constness> constness = ScopeMemberConstness(scope, name);
  if (!constness.has_value() || *constness == Constness::kWritable) return {};
  return std::format("{}::{}", scope, name);
}

std::string ConstantWriteWalk::MemberConstant(const Expr* e) const {
  const Expr* root = MemberRoot(e);
  if (root == nullptr) return {};
  std::optional<DeclaredName> declared = Find(root->text);
  const ModuleDecl* scope = nullptr;
  if (declared.has_value()) {
    if (declared->constness == Constness::kConstant)
      return std::string(root->text);
    scope = declared->instance_of;
  } else {
    scope = FindDefinition(tables_.unit, root->text);
  }
  std::vector<std::string_view> path;
  if (scope == nullptr || !AppendMemberPath(e, path)) return {};
  return HierarchicalConstant(scope, path);
}

std::string ConstantWriteWalk::HierarchicalConstant(
    const ModuleDecl* decl, const std::vector<std::string_view>& path) const {
  for (size_t i = 1; i + 1 < path.size() && decl != nullptr; ++i) {
    decl = ChildInstanceModule(tables_.unit, decl, path[i]);
  }
  if (decl == nullptr) return {};
  std::optional<Constness> constness =
      ConstnessInModule(decl, path.back(), tables_.class_names);
  if (!constness.has_value() || *constness == Constness::kWritable) return {};
  return JoinedPath(path);
}

void ConstantWriteWalk::ForEachWrittenConstant(
    const Expr* target,
    const std::function<void(const std::string&)>& report) const {
  if (target == nullptr) return;
  if (IsLvalueAggregate(target)) {
    for (const Expr* element : target->elements) {
      ForEachWrittenConstant(element, report);
    }
    return;
  }
  std::string written = WrittenConstant(target);
  if (!written.empty()) report(written);
}

void ConstantWriteWalk::WalkItems(const std::vector<ModuleItem*>& items) {
  for (const ModuleItem* item : items) WalkItem(item);
}

void ConstantWriteWalk::WalkScope(const std::vector<ModuleItem*>& items) {
  Mark mark = Here();
  DeclareItems(items);
  WalkItems(items);
  Restore(mark);
}

void ConstantWriteWalk::WalkItem(const ModuleItem* item) {
  if (IsProceduralItemKind(item->kind)) {
    WalkStmt(item->body);
    return;
  }
  switch (item->kind) {
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:
      WalkOutOfBlockMethod(item);
      break;
    case ModuleItemKind::kGenerateIf:
    case ModuleItemKind::kGenerateCase:
    case ModuleItemKind::kGenerateFor:
      WalkGenerate(item);
      break;
    case ModuleItemKind::kClassDecl:
      WalkClass(item->class_decl);
      break;
    default:
      break;
  }
}

void ConstantWriteWalk::WalkOutOfBlockMethod(const ModuleItem* item) {
  if (item->method_class.empty()) {
    WalkSubroutine(item);
    return;
  }
  const ClassDecl* cls = FindClass(item->method_class);
  if (cls == nullptr) return;
  Mark mark = Here();
  DeclareClass(cls);
  WalkSubroutine(item);
  Restore(mark);
}

void ConstantWriteWalk::WalkSubroutine(const ModuleItem* item) {
  Mark mark = Here();
  for (const FunctionArg& formal : item->func_args) {
    Declare(formal.name, Constness::kWritable);
  }
  for (const Stmt* s : item->func_body_stmts) WalkStmt(s);
  Restore(mark);
}

void ConstantWriteWalk::WalkClass(const ClassDecl* cls) {
  Mark mark = Here();
  DeclareClass(cls);
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
      WalkSubroutine(m->method);
    } else if (m->kind == ClassMemberKind::kClassDecl) {
      WalkClass(m->nested_class);
    }
  }
  Restore(mark);
}

void ConstantWriteWalk::WalkGenerate(const ModuleItem* item) {
  Mark mark = Here();
  if (item->kind == ModuleItemKind::kGenerateFor && item->gen_init != nullptr)
    Declare(ExprIdent(item->gen_init->lhs), Constness::kConstant);
  WalkScope(item->gen_body);
  Restore(mark);
  if (item->gen_else != nullptr) WalkGenerate(item->gen_else);
  for (const GenerateCaseItem& ci : item->gen_case_items) WalkScope(ci.body);
}

void ConstantWriteWalk::WalkStmt(const Stmt* s) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) {
    CheckStmt(s);
    Constness constness =
        s->var_is_param ? Constness::kConstant
                        : ConstnessOfVariable(s->var_is_const, s->var_decl_type,
                                              tables_.class_names);
    Declare(s->var_name, constness);
    return;
  }
  Mark mark = Here();
  DeclareLoopVariables(s);
  CheckStmt(s);
  ForEachChildStmt(s, [this](const Stmt* sub) { WalkStmt(sub); });
  Restore(mark);
}

void ConstantWriteWalk::CheckStmt(const Stmt* s) {
  switch (s->kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      ReportTarget(s->lhs, s->range.start);
      ReportNonVariableTarget(s->lhs, s);
      break;
    case StmtKind::kForce:
    case StmtKind::kAssign:
      ReportNonVariableTarget(s->lhs, s);
      break;
    default:
      break;
  }
  ForEachChildExpr(s, [this, s](const Expr* e) {
    CheckExpr(IsCompoundAssignmentOf(s, e) ? e->rhs : e);
  });
}

void ConstantWriteWalk::CheckExpr(const Expr* e) {
  if (e == nullptr) return;
  if (IsIncOrDec(e) || IsAssignmentExpr(e)) {
    ReportTarget(e->lhs, e->range.start);
  } else if (e->kind == ExprKind::kCall) {
    CheckStringMethod(e);
    CheckActuals(e);
  }
  ForEachExprChild(e, [this](const Expr* child) { CheckExpr(child); });
}

void ConstantWriteWalk::CheckStringMethod(const Expr* call) {
  const Expr* callee = call->lhs;
  if (callee == nullptr || callee->kind != ExprKind::kMemberAccess ||
      callee->is_scope_resolution || callee->rhs == nullptr ||
      !StringMethodWritesItsObject(callee->rhs->text))
    return;
  std::optional<DeclaredName> declared = Find(ExprIdent(callee->lhs));
  bool handle =
      declared.has_value() && declared->constness == Constness::kConstantHandle;
  if (!handle) ReportTarget(callee->lhs, call->range.start);
}

void ConstantWriteWalk::CheckActuals(const Expr* call) {
  if (call->lhs == nullptr || call->lhs->kind != ExprKind::kIdentifier) return;
  const ModuleItem* subroutine = FindSubroutine(call->callee);
  if (subroutine == nullptr) return;
  size_t positional = call->args.size() - call->arg_names.size();
  for (size_t i = 0; i < subroutine->func_args.size(); ++i) {
    const FunctionArg& formal = subroutine->func_args[i];
    std::string_view direction = WritingDirection(formal);
    int index = ResolveActualArgIndex(call, i, formal.name, positional);
    if (direction.empty() || index < 0) continue;
    const Expr* actual = call->args[static_cast<size_t>(index)];
    ForEachWrittenConstant(actual, [&](const std::string& written) {
      diag_.Error(
          actual->range.start,
          std::format("constant '{}' cannot be the actual of {} "
                      "argument '{}' of '{}'",
                      written, direction, formal.name, subroutine->name),
          Subclause("6.20"));
    });
  }
}

void ConstantWriteWalk::ReportTarget(const Expr* target, SourceLoc loc) {
  ForEachWrittenConstant(target, [this, loc](const std::string& written) {
    diag_.Error(loc, std::format("assignment to constant '{}'", written),
                Subclause("6.20"));
  });
}

void ConstantWriteWalk::ReportNonVariableTarget(const Expr* lhs,
                                                const Stmt* s) {
  if (lhs->kind == ExprKind::kConcatenation) {
    for (const Expr* element : lhs->elements)
      ReportNonVariableTarget(element, s);
    return;
  }
  const Expr* base = WithoutSelects(lhs);
  if (base->kind != ExprKind::kIdentifier) return;
  bool continuous = s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign;
  std::optional<DeclaredName> declared = Find(base->text);
  bool constant =
      declared.has_value() && declared->constness != Constness::kWritable;
  if (tables_.enum_members.count(base->text) == 0 && !(continuous && constant))
    return;
  std::string_view what = "assignment";
  std::string_view bound;
  std::string_view subclause = "10.4";
  if (s->kind == StmtKind::kForce) {
    what = "force";
    bound = " or a net";
    subclause = "10.6.2";
  } else if (s->kind == StmtKind::kAssign) {
    what = "procedural assign";
    subclause = "10.6.1";
  }
  diag_.Error(s->range.start,
              std::format("{} of constant '{}', which is not a variable{}",
                          what, base->text, bound),
              Subclause(subclause));
}

}  // namespace

void Elaborator::ValidateConstAssignments(const ModuleDecl* decl) {
  const NameSet kClassNames = ClassNamesIn(class_names_, unit_);
  const ConstantWriteTables kTables{unit_, kClassNames, enum_member_names_,
                                    &func_decls_};
  ConstantWriteWalk walk(kTables, diag_);
  walk.DeclareItems(unit_->cu_items);
  walk.DeclareModule(decl);
  walk.WalkItems(decl->items);
}

void Elaborator::ValidateUnitConstAssignments() {
  const NameSet kNoEnumMembers;
  const NameSet kClassNames = ClassNamesIn(class_names_, unit_);
  const ConstantWriteTables kTables{unit_, kClassNames, kNoEnumMembers,
                                    nullptr};
  ConstantWriteWalk walk(kTables, diag_);
  walk.DeclareItems(unit_->cu_items);
  walk.WalkItems(unit_->cu_items);
  for (const ClassDecl* cls : unit_->classes) walk.WalkClass(cls);
  for (const PackageDecl* pkg : unit_->packages) {
    ConstantWriteWalk package_walk(kTables, diag_);
    package_walk.WalkScope(pkg->items);
  }
}

}  // namespace delta
