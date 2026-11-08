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

#include "common/array_methods.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/string_methods.h"
#include "common/system_call_writes.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_enum_constants.h"
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

enum class Constness : uint8_t {
  kWritable,
  kConstant,
  kConstantHandle,
  kEnumMember
};

enum class EnumMemberTargets : uint8_t { kSkipped, kCounted };

struct DeclaredName {
  Constness constness = Constness::kWritable;
  const ModuleDecl* instance_of = nullptr;
  size_t unpacked_dims = 0;
  const DataType* type = nullptr;
};

struct SelectedObject {
  std::optional<DeclaredName> declared;
  size_t selects = 0;
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

bool CountsAsConstant(Constness constness, EnumMemberTargets enum_members) {
  if (constness == Constness::kEnumMember)
    return enum_members == EnumMemberTargets::kCounted;
  return constness != Constness::kWritable;
}

void ForEachDeclaredEnumMember(
    const DataType& type, const std::function<void(std::string_view)>& fn) {
  ForEachEnumTypeIn(type, [&fn](std::string_view, const DataType& enum_type) {
    for (const EnumMember& member : enum_type.enum_members) {
      if (member.range_start == nullptr) fn(member.name);
    }
  });
}

const DataType& DeclaredTypeOf(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kTypedef ? item->typedef_type
                                                : item->data_type;
}

const DataType& MemberDeclaredType(const ClassMember* m) {
  return m->typedef_item != nullptr ? DeclaredTypeOf(m->typedef_item)
                                    : m->data_type;
}

bool DeclaresEnumMember(const DataType& type, std::string_view name) {
  bool declares = false;
  ForEachDeclaredEnumMember(type, [name, &declares](std::string_view member) {
    declares = declares || member == name;
  });
  return declares;
}

std::optional<DeclaredName> DeclaredAmong(const std::vector<ModuleItem*>& items,
                                          std::string_view name,
                                          const NameSet& class_names) {
  for (const ModuleItem* item : items) {
    std::optional<Constness> constness =
        item->name == name ? ConstnessOfItem(item, class_names) : std::nullopt;
    if (constness.has_value())
      return DeclaredName{*constness, nullptr, item->unpacked_dims.size(),
                          &item->data_type};
    if (DeclaresEnumMember(DeclaredTypeOf(item), name))
      return DeclaredName{Constness::kEnumMember, nullptr, 0, nullptr};
  }
  return std::nullopt;
}

std::optional<Constness> ConstnessAmong(const std::vector<ModuleItem*>& items,
                                        std::string_view name,
                                        const NameSet& class_names) {
  std::optional<DeclaredName> declared =
      DeclaredAmong(items, name, class_names);
  if (!declared.has_value()) return std::nullopt;
  return declared->constness;
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
    if (DeclaresEnumMember(MemberDeclaredType(m), name))
      return Constness::kEnumMember;
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

NameSet EnumMembersIn(const std::vector<ModuleItem*>& items) {
  NameSet names;
  for (const ModuleItem* item : items) {
    ForEachEnumTypeOfItem(item,
                          [&names](std::string_view, const DataType& type) {
                            for (const EnumMember& member : type.enum_members) {
                              names.insert(member.name);
                            }
                          });
  }
  return names;
}

std::string_view ScopeRandomizeOf(const Expr* callee) {
  if (callee == nullptr) return {};
  if (callee->kind == ExprKind::kIdentifier) {
    return callee->text == "randomize" ? "randomize" : "";
  }
  bool from_std = callee->kind == ExprKind::kMemberAccess &&
                  ExprIdent(callee->lhs) == "std" &&
                  ExprIdent(callee->rhs) == "randomize";
  return from_std ? "std::randomize" : "";
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

const ModuleDecl* ModuleAlongPath(const CompilationUnit* unit,
                                  const ModuleDecl* decl,
                                  const std::vector<std::string_view>& path) {
  for (size_t i = 1; i + 1 < path.size() && decl != nullptr; ++i) {
    decl = ChildInstanceModule(unit, decl, path[i]);
  }
  return decl;
}

const ModuleItem* SubroutineAmong(const std::vector<ModuleItem*>& items,
                                  std::string_view name) {
  for (const ModuleItem* item : items) {
    bool subroutine = item->kind == ModuleItemKind::kFunctionDecl ||
                      item->kind == ModuleItemKind::kTaskDecl ||
                      item->kind == ModuleItemKind::kDpiImport;
    if (subroutine && item->method_class.empty() && item->name == name)
      return item;
  }
  return nullptr;
}

const ClassMember* ClassMemberOf(const ClassDecl* cls, std::string_view name,
                                 ClassMemberKind kind,
                                 const CompilationUnit* unit) {
  std::vector<const ClassDecl*> lineage;
  for (; cls != nullptr && std::ranges::find(lineage, cls) == lineage.end();
       cls = FindBaseClass(cls, unit)) {
    lineage.push_back(cls);
    for (const ClassMember* m : cls->members) {
      if (m->kind == kind && m->name == name) return m;
    }
  }
  return nullptr;
}

const ModuleItem* MethodOf(const ClassDecl* cls, std::string_view name,
                           const CompilationUnit* unit) {
  const ClassMember* method =
      ClassMemberOf(cls, name, ClassMemberKind::kMethod, unit);
  return method == nullptr ? nullptr : method->method;
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
               const ModuleDecl* instance_of = nullptr,
               size_t unpacked_dims = 0, const DataType* type = nullptr) {
    names_.emplace_back(
        name, DeclaredName{constness, instance_of, unpacked_dims, type});
  }
  void DeclareItem(const ModuleItem* item);
  void DeclareEnumMembers(const DataType& type);
  void DeclareClass(const ClassDecl* cls);
  void DeclareClassMembers(const ClassDecl* cls);
  void DeclareLoopVariables(const Stmt* s);

  std::optional<DeclaredName> Find(std::string_view name) const;
  std::optional<DeclaredName> ImportedName(std::string_view name) const;
  const ClassDecl* FindClass(std::string_view name) const;
  const ModuleItem* FindSubroutine(std::string_view name) const;
  const ModuleItem* CalledSubroutine(const Expr* callee) const;
  const ModuleItem* ScopedSubroutine(std::string_view scope,
                                     std::string_view name) const;
  const ModuleItem* HierarchicalSubroutine(const Expr* callee) const;
  const ClassDecl* ClassOfObject(const Expr* object) const;
  const ClassDecl* ClassOfProperty(const Expr* access) const;
  const ClassDecl* SelfClass(std::string_view self) const;
  const ClassDecl* ClassOfType(const DataType* type) const;
  const ModuleDecl* RootScope(const Expr* root) const;
  std::optional<Constness> ScopeMemberConstness(std::string_view scope,
                                                std::string_view name) const;
  SelectedObject ObjectSelected(const Expr* object) const;
  bool NamesAConstantHandle(const Expr* object) const;
  bool NamesAnArray(const Expr* object) const;

  std::string WrittenConstant(const Expr* target,
                              EnumMemberTargets enum_members) const;
  std::string IdentifiedConstant(std::string_view name,
                                 EnumMemberTargets enum_members) const;
  std::string ScopedConstant(std::string_view scope, std::string_view name,
                             EnumMemberTargets enum_members) const;
  std::string MemberConstant(const Expr* e) const;
  std::string HierarchicalConstant(
      const ModuleDecl* decl, const std::vector<std::string_view>& path) const;
  void ForEachWrittenConstant(
      const Expr* target, EnumMemberTargets enum_members,
      const std::function<void(const std::string&)>& report) const;

  void WalkItem(const ModuleItem* item);
  void WalkSubroutine(const ModuleItem* item);
  void WalkOutOfBlockMethod(const ModuleItem* item);
  void WalkGenerate(const ModuleItem* item);
  void WalkStmt(const Stmt* s);
  void CheckStmt(const Stmt* s);
  void CheckExpr(const Expr* e);
  void CheckWrite(const Expr* e);
  void CheckBuiltInMethod(const Expr* call);
  void CheckParenlessArrayMethod(const Expr* access);
  void CheckScopeRandomize(const Expr* call);
  void CheckSystemCall(const Expr* call);
  void CheckActuals(const Expr* call);
  void ReportTarget(const Expr* target, SourceLoc loc,
                    EnumMemberTargets enum_members);
  void ReportWrittenBy(const Expr* actual, std::string_view writer);
  void ReportNonVariableTarget(const Expr* lhs, const Stmt* s);

  const ConstantWriteTables& tables_;
  DiagEngine& diag_;
  std::vector<std::pair<std::string_view, DeclaredName>> names_;
  std::vector<const ModuleItem*> subroutines_;
  std::vector<const ImportItem*> imports_;
  std::vector<const ClassDecl*> classes_;
  const ClassDecl* current_class_ = nullptr;
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
    Declare(port.name, Constness::kWritable, bound, port.unpacked_dims.size(),
            &port.data_type);
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
    Declare(item->name, *constness, nullptr, item->unpacked_dims.size(),
            &item->data_type);
  DeclareEnumMembers(DeclaredTypeOf(item));
}

void ConstantWriteWalk::DeclareEnumMembers(const DataType& type) {
  ForEachDeclaredEnumMember(type, [this](std::string_view member) {
    Declare(member, Constness::kEnumMember);
  });
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
    DeclareEnumMembers(MemberDeclaredType(m));
    if (m->kind == ClassMemberKind::kProperty) {
      Declare(m->name,
              m->is_param ? Constness::kConstant : Constness::kWritable,
              nullptr, m->unpacked_dims.size(), &m->data_type);
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
  return ImportedName(name);
}

std::optional<DeclaredName> ConstantWriteWalk::ImportedName(
    std::string_view name) const {
  for (const ImportItem* import : imports_) {
    if (!import->is_wildcard && import->item_name != name) continue;
    const PackageDecl* pkg = FindPackage(tables_.unit, import->package_name);
    std::optional<DeclaredName> declared =
        pkg == nullptr ? std::nullopt
                       : DeclaredAmong(pkg->items, name, tables_.class_names);
    if (declared.has_value()) return declared;
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

const ModuleItem* ConstantWriteWalk::CalledSubroutine(
    const Expr* callee) const {
  if (callee->kind == ExprKind::kIdentifier) {
    return callee->scope_prefix.empty()
               ? FindSubroutine(callee->text)
               : ScopedSubroutine(callee->scope_prefix, callee->text);
  }
  bool member = callee->kind == ExprKind::kMemberAccess &&
                callee->lhs != nullptr && callee->rhs != nullptr;
  if (member && callee->is_scope_resolution)
    return ScopedSubroutine(ExprIdent(callee->lhs), callee->rhs->text);
  const ClassDecl* cls = member ? ClassOfObject(callee->lhs) : nullptr;
  if (cls != nullptr) return MethodOf(cls, callee->rhs->text, tables_.unit);
  return member ? HierarchicalSubroutine(callee) : nullptr;
}

const ModuleItem* ConstantWriteWalk::ScopedSubroutine(
    std::string_view scope, std::string_view name) const {
  if (scope == "$unit") return SubroutineAmong(tables_.unit->cu_items, name);
  if (const PackageDecl* pkg = FindPackage(tables_.unit, scope))
    return SubroutineAmong(pkg->items, name);
  const ClassDecl* cls = FindClass(scope);
  return cls == nullptr ? nullptr : MethodOf(cls, name, tables_.unit);
}

const ModuleItem* ConstantWriteWalk::HierarchicalSubroutine(
    const Expr* callee) const {
  const Expr* root = MemberRoot(callee);
  std::vector<std::string_view> path;
  if (root == nullptr || !AppendMemberPath(callee, path)) return nullptr;
  const ModuleDecl* decl = ModuleAlongPath(tables_.unit, RootScope(root), path);
  return decl == nullptr ? nullptr : SubroutineAmong(decl->items, path.back());
}

const ClassDecl* ConstantWriteWalk::ClassOfObject(const Expr* object) const {
  if (object->kind == ExprKind::kIdentifier &&
      (object->text == "this" || object->text == "super"))
    return SelfClass(object->text);
  if (object->kind == ExprKind::kMemberAccess) return ClassOfProperty(object);
  SelectedObject selected = ObjectSelected(object);
  bool element = selected.declared.has_value() &&
                 selected.selects >= selected.declared->unpacked_dims;
  return element ? ClassOfType(selected.declared->type) : nullptr;
}

const ClassDecl* ConstantWriteWalk::ClassOfProperty(const Expr* access) const {
  bool owned = !access->is_scope_resolution && access->lhs != nullptr &&
               access->rhs != nullptr;
  const ClassDecl* owner = owned ? ClassOfObject(access->lhs) : nullptr;
  const ClassMember* property =
      owner == nullptr
          ? nullptr
          : ClassMemberOf(owner, access->rhs->text, ClassMemberKind::kProperty,
                          tables_.unit);
  return property == nullptr ? nullptr : ClassOfType(&property->data_type);
}

const ClassDecl* ConstantWriteWalk::SelfClass(std::string_view self) const {
  if (self == "this" || current_class_ == nullptr) return current_class_;
  return FindBaseClass(current_class_, tables_.unit);
}

const ClassDecl* ConstantWriteWalk::ClassOfType(const DataType* type) const {
  if (type == nullptr || type->kind != DataTypeKind::kNamed) return nullptr;
  return FindClass(type->type_name);
}

const ModuleDecl* ConstantWriteWalk::RootScope(const Expr* root) const {
  std::optional<DeclaredName> declared =
      root->scope_prefix == "$root" ? std::nullopt : Find(root->text);
  if (!declared.has_value()) return FindDefinition(tables_.unit, root->text);
  if (declared->instance_of != nullptr) return declared->instance_of;
  bool virtual_interface =
      declared->type != nullptr &&
      declared->type->kind == DataTypeKind::kVirtualInterface;
  return virtual_interface
             ? FindDefinition(tables_.unit, declared->type->type_name)
             : nullptr;
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

SelectedObject ConstantWriteWalk::ObjectSelected(const Expr* object) const {
  SelectedObject selected;
  while (object->kind == ExprKind::kSelect && object->base != nullptr) {
    object = object->base;
    ++selected.selects;
  }
  if (object->kind == ExprKind::kIdentifier)
    selected.declared = Find(object->text);
  return selected;
}

bool ConstantWriteWalk::NamesAConstantHandle(const Expr* object) const {
  SelectedObject selected = ObjectSelected(object);
  return selected.declared.has_value() &&
         selected.declared->constness == Constness::kConstantHandle &&
         selected.selects >= selected.declared->unpacked_dims;
}

bool ConstantWriteWalk::NamesAnArray(const Expr* object) const {
  SelectedObject selected = ObjectSelected(object);
  return selected.declared.has_value() &&
         selected.selects < selected.declared->unpacked_dims;
}

std::string ConstantWriteWalk::WrittenConstant(
    const Expr* target, EnumMemberTargets enum_members) const {
  const Expr* e = WithoutSelects(target);
  if (e->kind == ExprKind::kIdentifier) {
    return e->scope_prefix == "$unit"
               ? ScopedConstant("$unit", e->text, enum_members)
               : IdentifiedConstant(e->text, enum_members);
  }
  if (e->kind != ExprKind::kMemberAccess) return {};
  return e->is_scope_resolution
             ? ScopedConstant(ExprIdent(e->lhs), ExprIdent(e->rhs),
                              EnumMemberTargets::kCounted)
             : MemberConstant(e);
}

std::string ConstantWriteWalk::IdentifiedConstant(
    std::string_view name, EnumMemberTargets enum_members) const {
  std::optional<DeclaredName> declared = Find(name);
  bool constant = declared.has_value()
                      ? CountsAsConstant(declared->constness, enum_members)
                      : enum_members == EnumMemberTargets::kCounted &&
                            tables_.enum_members.contains(name);
  return constant ? std::string(name) : std::string();
}

std::string ConstantWriteWalk::ScopedConstant(
    std::string_view scope, std::string_view name,
    EnumMemberTargets enum_members) const {
  std::optional<Constness> constness = ScopeMemberConstness(scope, name);
  if (!constness.has_value() || !CountsAsConstant(*constness, enum_members))
    return {};
  return std::format("{}::{}", scope, name);
}

std::string ConstantWriteWalk::MemberConstant(const Expr* e) const {
  const Expr* root = MemberRoot(e);
  if (root == nullptr) return {};
  if (root->scope_prefix == "$unit")
    return ScopedConstant("$unit", root->text, EnumMemberTargets::kSkipped);
  bool from_root = root->scope_prefix == "$root";
  std::optional<DeclaredName> declared =
      from_root ? std::nullopt : Find(root->text);
  if (declared.has_value() && declared->constness == Constness::kConstant)
    return std::string(root->text);
  const ModuleDecl* scope = RootScope(root);
  std::vector<std::string_view> path;
  if (scope == nullptr || !AppendMemberPath(e, path)) return {};
  std::string written = HierarchicalConstant(scope, path);
  return from_root && !written.empty() ? "$root." + written : written;
}

std::string ConstantWriteWalk::HierarchicalConstant(
    const ModuleDecl* decl, const std::vector<std::string_view>& path) const {
  decl = ModuleAlongPath(tables_.unit, decl, path);
  if (decl == nullptr) return {};
  std::optional<Constness> constness =
      ConstnessInModule(decl, path.back(), tables_.class_names);
  if (!constness.has_value() || *constness == Constness::kWritable) return {};
  return JoinedPath(path);
}

void ConstantWriteWalk::ForEachWrittenConstant(
    const Expr* target, EnumMemberTargets enum_members,
    const std::function<void(const std::string&)>& report) const {
  if (target == nullptr) return;
  if (IsLvalueAggregate(target)) {
    for (const Expr* element : target->elements) {
      ForEachWrittenConstant(element, enum_members, report);
    }
    return;
  }
  std::string written = WrittenConstant(target, enum_members);
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
  const ClassDecl* outer = std::exchange(current_class_, cls);
  DeclareClass(cls);
  WalkSubroutine(item);
  current_class_ = outer;
  Restore(mark);
}

void ConstantWriteWalk::WalkSubroutine(const ModuleItem* item) {
  Mark mark = Here();
  for (const FunctionArg& formal : item->func_args) {
    Declare(formal.name, Constness::kWritable, nullptr,
            formal.unpacked_dims.size(), &formal.data_type);
  }
  for (const Stmt* s : item->func_body_stmts) WalkStmt(s);
  Restore(mark);
}

void ConstantWriteWalk::WalkClass(const ClassDecl* cls) {
  Mark mark = Here();
  const ClassDecl* outer = std::exchange(current_class_, cls);
  DeclareClass(cls);
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
      WalkSubroutine(m->method);
    } else if (m->kind == ClassMemberKind::kClassDecl) {
      WalkClass(m->nested_class);
    }
  }
  current_class_ = outer;
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
    DeclareEnumMembers(s->var_decl_type);
    Declare(s->var_name, constness, nullptr, s->var_unpacked_dims.size(),
            &s->var_decl_type);
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
      ReportTarget(s->lhs, s->range.start, EnumMemberTargets::kSkipped);
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
  CheckWrite(e);
  ForEachExprChild(e, [this, e](const Expr* child) {
    if (e->kind == ExprKind::kCall && child == e->lhs && child != nullptr) {
      ForEachExprChild(child, [this](const Expr* sub) { CheckExpr(sub); });
    } else {
      CheckExpr(child);
    }
  });
}

void ConstantWriteWalk::CheckWrite(const Expr* e) {
  if (IsIncOrDec(e) || IsAssignmentExpr(e)) {
    ReportTarget(e->lhs, e->range.start, EnumMemberTargets::kCounted);
  } else if (e->kind == ExprKind::kCall) {
    CheckBuiltInMethod(e);
    CheckScopeRandomize(e);
    CheckActuals(e);
  } else if (e->kind == ExprKind::kSystemCall) {
    CheckSystemCall(e);
  } else if (e->kind == ExprKind::kMemberAccess) {
    CheckParenlessArrayMethod(e);
  }
}

void ConstantWriteWalk::CheckBuiltInMethod(const Expr* call) {
  const Expr* callee = call->lhs;
  if (callee == nullptr || callee->kind != ExprKind::kMemberAccess ||
      callee->is_scope_resolution || callee->rhs == nullptr)
    return;
  std::string_view method = callee->rhs->text;
  if (StringMethodWritesItsObject(method) ||
      ArrayMethodWritesItsArray(method)) {
    if (!NamesAConstantHandle(callee->lhs))
      ReportTarget(callee->lhs, call->range.start, EnumMemberTargets::kCounted);
  } else if (ArrayMethodWritesItsIndex(method) && !call->args.empty() &&
             NamesAnArray(callee->lhs)) {
    ReportWrittenBy(call->args.front(), method);
  }
}

void ConstantWriteWalk::CheckParenlessArrayMethod(const Expr* access) {
  if (access->is_scope_resolution || access->lhs == nullptr ||
      access->rhs == nullptr || !ArrayMethodWritesItsArray(access->rhs->text) ||
      !NamesAnArray(access->lhs))
    return;
  ReportTarget(access->lhs, access->range.start, EnumMemberTargets::kCounted);
}

void ConstantWriteWalk::CheckScopeRandomize(const Expr* call) {
  std::string_view randomize = ScopeRandomizeOf(call->lhs);
  if (randomize.empty()) return;
  if (randomize == "randomize" && FindSubroutine(randomize) != nullptr) return;
  for (const Expr* arg : call->args) ReportWrittenBy(arg, randomize);
}

void ConstantWriteWalk::CheckSystemCall(const Expr* call) {
  for (size_t i = 0; i < call->args.size(); ++i) {
    if (SystemCallWritesArgument(call->callee, i))
      ReportWrittenBy(call->args[i], call->callee);
  }
}

void ConstantWriteWalk::CheckActuals(const Expr* call) {
  const ModuleItem* subroutine =
      call->lhs == nullptr ? nullptr : CalledSubroutine(call->lhs);
  if (subroutine == nullptr) return;
  size_t positional = call->args.size() - call->arg_names.size();
  for (size_t i = 0; i < subroutine->func_args.size(); ++i) {
    const FunctionArg& formal = subroutine->func_args[i];
    std::string_view direction = WritingDirection(formal);
    int index = ResolveActualArgIndex(call, i, formal.name, positional);
    if (direction.empty() || index < 0) continue;
    const Expr* actual = call->args[static_cast<size_t>(index)];
    ForEachWrittenConstant(
        actual, EnumMemberTargets::kCounted, [&](const std::string& written) {
          diag_.Error(
              actual->range.start,
              std::format("constant '{}' cannot be the actual of {} "
                          "argument '{}' of '{}'",
                          written, direction, formal.name, subroutine->name),
              Subclause("6.20"));
        });
  }
}

void ConstantWriteWalk::ReportTarget(const Expr* target, SourceLoc loc,
                                     EnumMemberTargets enum_members) {
  ForEachWrittenConstant(
      target, enum_members, [this, loc](const std::string& written) {
        diag_.Error(loc, std::format("assignment to constant '{}'", written),
                    Subclause("6.20"));
      });
}

void ConstantWriteWalk::ReportWrittenBy(const Expr* actual,
                                        std::string_view writer) {
  ForEachWrittenConstant(
      actual, EnumMemberTargets::kCounted,
      [this, actual, writer](const std::string& written) {
        diag_.Error(actual->range.start,
                    std::format("constant '{}' cannot be written by '{}'",
                                written, writer),
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
  bool enum_member = declared.has_value()
                         ? declared->constness == Constness::kEnumMember
                         : tables_.enum_members.contains(base->text);
  bool constant =
      declared.has_value() && declared->constness != Constness::kWritable;
  if (!enum_member && !(continuous && constant)) return;
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
  const NameSet kClassNames = ClassNamesIn(class_names_, unit_);
  const NameSet kUnitEnumMembers = EnumMembersIn(unit_->cu_items);
  const ConstantWriteTables kTables{unit_, kClassNames, kUnitEnumMembers,
                                    nullptr};
  ConstantWriteWalk walk(kTables, diag_);
  walk.DeclareItems(unit_->cu_items);
  walk.WalkItems(unit_->cu_items);
  for (const ClassDecl* cls : unit_->classes) walk.WalkClass(cls);
  for (const PackageDecl* pkg : unit_->packages) {
    const NameSet kPackageEnumMembers = EnumMembersIn(pkg->items);
    const ConstantWriteTables kPackageTables{unit_, kClassNames,
                                             kPackageEnumMembers, nullptr};
    ConstantWriteWalk package_walk(kPackageTables, diag_);
    package_walk.WalkScope(pkg->items);
  }
}

}  // namespace delta
