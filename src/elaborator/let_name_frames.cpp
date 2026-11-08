#include "elaborator/let_name_frames.h"

#include <algorithm>
#include <cstddef>
#include <span>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/std_package.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

const NameBinding* FindInherited(const NameFrame& frame,
                                 std::string_view name) {
  for (const NameFrame* base : frame.bases) {
    if (const NameBinding* inherited = FindOwnName(base, name))
      return inherited;
  }
  return nullptr;
}

}  // namespace

const NameBinding* FindName(const NameFrame& frame, std::string_view name) {
  for (const NameFrame* at = &frame; at != nullptr; at = at->outer) {
    auto it = at->names.find(name);
    if (it != at->names.end()) return &it->second;
    if (const NameBinding* inherited = FindInherited(*at, name))
      return inherited;
  }
  return nullptr;
}

const NameBinding* FindOwnName(const NameFrame* frame, std::string_view name) {
  if (frame == nullptr) return nullptr;
  auto it = frame->names.find(name);
  if (it != frame->names.end() && it->second.scope == frame) return &it->second;
  return FindInherited(*frame, name);
}

const DataType* TypedefTypeOf(const NameBinding* named) {
  if (named == nullptr || named->kind != NameKind::kTypedef ||
      !named->item->typedef_ifc_port.empty())
    return nullptr;
  return &named->item->typedef_type;
}

namespace {

void Declare(NameFrame& frame, std::string_view name, NameBinding binding) {
  binding.scope = &frame;
  frame.names.insert_or_assign(name, binding);
}

void AddWildcardCandidates(NameFrame& frame, const NameFrame* package) {
  if (package == nullptr) return;
  for (const auto& [name, binding] : package->names) {
    if (binding.scope != package) continue;
    auto [it, inserted] = frame.names.try_emplace(name, binding);
    if (!inserted && it->second.scope != package) Declare(frame, name, {});
  }
}

void AddExplicitImport(NameFrame& frame, const ImportItem& import,
                       const NameFrame* package) {
  const NameBinding* declared = FindOwnName(package, import.item_name);
  if (declared == nullptr) {
    Declare(frame, import.item_name, {});
    return;
  }
  frame.names.insert_or_assign(import.item_name, *declared);
}

void ImportInto(NameFrame& frame, const std::vector<const ImportItem*>& imports,
                const PackageFrames& packages) {
  for (const ImportItem* import : imports) {
    if (import->is_wildcard)
      AddWildcardCandidates(frame, packages.Find(import->package_name));
  }
  for (const ImportItem* import : imports) {
    if (!import->is_wildcard)
      AddExplicitImport(frame, *import, packages.Find(import->package_name));
  }
}

void DeclareEnumLiterals(NameFrame& frame, const DataType& type) {
  ForEachEnumTypeIn(type, [&frame](std::string_view, const DataType& e) {
    for (const EnumMember& member : e.enum_members)
      DeclareOther(frame, member.name);
  });
}

void DeclareTypedef(NameFrame& frame, const ModuleItem* item) {
  const DataType& type = item->typedef_type;
  const bool kForward =
      type.kind == DataTypeKind::kImplicit && type.type_ref_expr == nullptr;
  if (kForward) return;
  Declare(frame, item->name, {.kind = NameKind::kTypedef, .item = item});
}

void DeclareItem(NameFrame& frame, const ModuleItem* item) {
  DeclareEnumLiterals(frame, item->typedef_type);
  DeclareEnumLiterals(frame, item->data_type);
  switch (item->kind) {
    case ModuleItemKind::kLetDecl:
      Declare(frame, item->name, {.kind = NameKind::kLet, .item = item});
      break;
    case ModuleItemKind::kVarDecl:
    case ModuleItemKind::kNetDecl:
      Declare(frame, item->name,
              {.kind = item->is_genvar ? NameKind::kOther : NameKind::kVariable,
               .type = &item->data_type,
               .dims = &item->unpacked_dims});
      break;
    case ModuleItemKind::kTypedef:
      DeclareTypedef(frame, item);
      break;
    case ModuleItemKind::kClassDecl:
      Declare(frame, item->name,
              {.kind = NameKind::kClass, .cls = item->class_decl});
      break;
    case ModuleItemKind::kModuleInst:
      DeclareOther(frame, item->inst_name);
      break;
    case ModuleItemKind::kGateInst:
    case ModuleItemKind::kUdpInst:
      DeclareOther(frame, item->gate_inst_name);
      break;
    case ModuleItemKind::kImportDecl:
    case ModuleItemKind::kExportDecl:
      break;
    default:
      if (item->method_class.empty()) DeclareOther(frame, item->name);
      break;
  }
}

std::vector<const ImportItem*> ImportsOf(
    const std::vector<ModuleItem*>& items) {
  std::vector<const ImportItem*> imports;
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kImportDecl)
      imports.push_back(&item->import_item);
  }
  return imports;
}

bool IsBlockImport(const Stmt* s) {
  return s->kind == StmtKind::kBlockItemDecl &&
         s->decl_item->kind == ModuleItemKind::kImportDecl;
}

void DeclareStatement(NameFrame& frame, const Stmt* s) {
  if (s->kind == StmtKind::kBlockItemDecl) {
    DeclareItem(frame, s->decl_item);
    return;
  }
  if (s->kind != StmtKind::kVarDecl) return;
  DeclareEnumLiterals(frame, s->var_decl_type);
  Declare(frame, s->var_name,
          {.kind = s->var_is_param ? NameKind::kOther : NameKind::kVariable,
           .type = &s->var_decl_type,
           .dims = &s->var_unpacked_dims});
}

void DeclareForVariables(NameFrame& frame, const Stmt& s) {
  for (size_t i = 0; i < s.for_inits.size(); ++i) {
    const DataType& type = s.for_init_types[i];
    if (type.kind == DataTypeKind::kImplicit) continue;
    Declare(frame, ExprIdent(s.for_inits[i]->lhs),
            {.kind = NameKind::kVariable, .type = &type});
  }
}

const DataType& ScalarNetType() {
  static const DataType kScalar = [] {
    DataType type;
    type.kind = DataTypeKind::kLogic;
    return type;
  }();
  return kScalar;
}

void DeclareImplicitNet(NameFrame& frame, const Expr* e) {
  if (e == nullptr || e->kind != ExprKind::kIdentifier ||
      FindName(frame, e->text) != nullptr)
    return;
  Declare(frame, e->text,
          {.kind = NameKind::kVariable, .type = &ScalarNetType()});
}

void DeclareTargetNets(NameFrame& frame, const Expr* target) {
  if (target->kind != ExprKind::kConcatenation) {
    DeclareImplicitNet(frame, target);
    return;
  }
  for (const Expr* element : target->elements)
    DeclareTargetNets(frame, element);
}

const NameBinding* ClassBinding(const NameBinding* named) {
  return named != nullptr && named->kind == NameKind::kClass ? named : nullptr;
}

std::vector<std::string_view> PrefixesOf(const DataType& type) {
  std::vector<std::string_view> prefixes = type.outer_scope_names;
  if (!type.scope_name.empty()) prefixes.push_back(type.scope_name);
  return prefixes;
}

void DeclareClassMembers(NameFrame& frame, const ClassDecl& cls) {
  for (const ClassMember* m : cls.members) {
    switch (m->kind) {
      case ClassMemberKind::kTypedef:
        DeclareEnumLiterals(frame, m->typedef_item->typedef_type);
        DeclareTypedef(frame, m->typedef_item);
        break;
      case ClassMemberKind::kClassDecl:
        Declare(frame, m->name,
                {.kind = NameKind::kClass, .cls = m->nested_class});
        break;
      default:
        DeclareOther(frame, m->name);
        break;
    }
  }
}

}  // namespace

PackageFrames::PackageFrames(const CompilationUnit* unit) {
  for (const StdPackageEntry& entry : StdPackageContents())
    DeclareOther(std_, entry.name);
  for (const PackageDecl* pkg : unit->packages) {
    NameFrame& frame = frames_.emplace_back(nullptr);
    DeclareScope(frame, pkg->items, *this);
    packages_.emplace_back(pkg, &frame);
  }
}

const NameFrame* PackageFrames::Find(std::string_view package) const {
  for (const auto& [pkg, frame] : packages_) {
    if (pkg->name == package) return frame;
  }
  return package == "std" ? &std_ : nullptr;
}

const NameFrame* ClassFrames::Of(const ClassDecl& cls,
                                 const NameFrame& declaring) {
  if (!cls.params.empty()) return nullptr;
  return MembersOf(cls, declaring);
}

const NameFrame* ClassFrames::MembersOf(const ClassDecl& cls,
                                        const NameFrame& declaring) {
  auto [it, inserted] = built_.try_emplace(&cls, nullptr);
  if (!inserted) return it->second;
  std::vector<const NameFrame*> bases;
  if (!cls.base_class.empty())
    bases.push_back(BaseFrame(cls.base_class, cls.base_class_scope, declaring));
  for (const InterfaceRef& extended : cls.extends_interfaces)
    bases.push_back(BaseFrame(extended.name, extended.scope, declaring));
  if (std::ranges::find(bases, nullptr) != bases.end()) return nullptr;
  NameFrame& frame = frames_.emplace_back(&declaring);
  frame.bases = std::move(bases);
  DeclareClassMembers(frame, cls);
  built_[&cls] = &frame;
  return &frame;
}

const NameBinding* ClassFrames::TypeName(const DataType& type,
                                         const NameFrame& scope) {
  const std::vector<std::string_view> kPrefixes = PrefixesOf(type);
  return Named(kPrefixes, type.type_name, scope);
}

const NameFrame* ClassFrames::PrefixClassMembers(const DataType& type,
                                                 const NameFrame& scope) {
  std::vector<std::string_view> prefixes = PrefixesOf(type);
  const std::string_view kLast = prefixes.back();
  prefixes.pop_back();
  const NameBinding* named =
      ClassBinding(ThroughTypedefs(Named(prefixes, kLast, scope)));
  if (named == nullptr) return nullptr;
  return MembersOf(*named->cls, *named->scope);
}

const NameBinding* ClassFrames::Named(
    std::span<const std::string_view> prefixes, std::string_view name,
    const NameFrame& scope) {
  if (prefixes.empty()) return FindName(scope, name);
  return FindOwnName(ScopeNamed(prefixes, scope), name);
}

const NameFrame* ClassFrames::ScopeNamed(
    std::span<const std::string_view> prefixes, const NameFrame& scope) {
  const NameFrame* frame = OutermostScope(prefixes.front(), scope);
  for (size_t i = 1; frame != nullptr && i < prefixes.size(); ++i)
    frame = ClassFrame(FindOwnName(frame, prefixes[i]));
  return frame;
}

const NameFrame* ClassFrames::OutermostScope(std::string_view prefix,
                                             const NameFrame& scope) {
  if (prefix == "$unit") return &unit_;
  const NameBinding* named = ClassBinding(FindName(scope, prefix));
  if (named == nullptr) return packages_.Find(prefix);
  return Of(*named->cls, *named->scope);
}

const NameFrame* ClassFrames::ClassFrame(const NameBinding* named) {
  const NameBinding* cls = ClassBinding(named);
  if (cls == nullptr) return nullptr;
  return Of(*cls->cls, *cls->scope);
}

const NameBinding* ClassFrames::ThroughTypedefs(const NameBinding* named) {
  for (int hop = 0; hop < kMaxTypedefHops; ++hop) {
    const DataType* type = TypedefTypeOf(named);
    if (type == nullptr) return named;
    named = TypeName(*type, *named->scope);
  }
  return nullptr;
}

const NameFrame* ClassFrames::BaseFrame(std::string_view name,
                                        std::string_view scope,
                                        const NameFrame& declaring) {
  std::vector<std::string_view> prefixes;
  if (!scope.empty()) prefixes.push_back(scope);
  return ClassFrame(ThroughTypedefs(Named(prefixes, name, declaring)));
}

void DeclareOther(NameFrame& frame, std::string_view name) {
  if (!name.empty()) Declare(frame, name, {});
}

void DeclareScope(NameFrame& frame, const std::vector<ModuleItem*>& items,
                  const PackageFrames& packages) {
  ImportInto(frame, ImportsOf(items), packages);
  for (const ModuleItem* item : items) DeclareItem(frame, item);
}

void DeclareUnitScope(NameFrame& frame, const std::vector<ModuleItem*>& items,
                      const CompilationUnit& unit,
                      const PackageFrames& packages) {
  DeclareScope(frame, items, packages);
  for (const ClassDecl* cls : unit.classes)
    Declare(frame, cls->name, {.kind = NameKind::kClass, .cls = cls});
}

void DeclareImplicitNets(NameFrame& frame,
                         const std::vector<ModuleItem*>& items) {
  for (const ModuleItem* item : items) {
    switch (item->kind) {
      case ModuleItemKind::kGateInst:
      case ModuleItemKind::kUdpInst:
        for (const Expr* terminal : item->gate_terminals)
          DeclareImplicitNet(frame, terminal);
        break;
      case ModuleItemKind::kAlias:
        for (const Expr* net : item->alias_nets) DeclareImplicitNet(frame, net);
        break;
      case ModuleItemKind::kModuleInst:
        for (const auto& [port, actual] : item->inst_ports)
          DeclareImplicitNet(frame, actual);
        break;
      case ModuleItemKind::kContAssign:
        DeclareTargetNets(frame, item->assign_lhs);
        break;
      default:
        break;
    }
  }
}

void DeclareHeader(NameFrame& frame, const ModuleDecl& decl) {
  for (const PortDecl& port : decl.ports) DeclareOther(frame, port.name);
  for (const auto& param : decl.params) DeclareOther(frame, param.first);
  for (std::string_view name : decl.type_param_names) DeclareOther(frame, name);
}

void DeclareStatements(NameFrame& frame, const std::vector<Stmt*>& stmts,
                       const PackageFrames& packages) {
  std::vector<const ImportItem*> imports;
  for (const Stmt* s : stmts) {
    if (IsBlockImport(s)) imports.push_back(&s->decl_item->import_item);
  }
  ImportInto(frame, imports, packages);
  for (const Stmt* s : stmts) DeclareStatement(frame, s);
}

void DeclareStatementScope(NameFrame& frame, const Stmt* s,
                           const PackageFrames& packages) {
  std::vector<Stmt*> children;
  ForEachChildStmt(s, [&children](Stmt* const& child) {
    if (child != nullptr) children.push_back(child);
  });
  DeclareStatements(frame, children, packages);
  DeclareForVariables(frame, *s);
  for (std::string_view name : s->foreach_vars) DeclareOther(frame, name);
}

}  // namespace delta
