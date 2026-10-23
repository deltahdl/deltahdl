#include <algorithm>
#include <cstddef>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_procedures_internal.h"

// The declarations a call the procedure walk resolves is made against: the
// class a name stands for where the call stands, the methods it declares, the
// class it extends under a specialization, and the variable a named block
// declares where a hierarchical name reaches it.

namespace delta {

namespace {

// The class among `decls` named `name`, null for none.
const ClassDecl* ClassNamed(const std::vector<ClassDecl*>& decls,
                            std::string_view name) {
  for (const ClassDecl* decl : decls) {
    if (decl->name == name) return decl;
  }
  return nullptr;
}

// The classes the package named `package` declares; none for a name no
// package of the design has.
std::vector<ClassDecl*> PackageClasses(const RtlirDesign& design,
                                       std::string_view package) {
  std::vector<ClassDecl*> classes;
  for (const PackageDecl* decl : design.packages) {
    if (decl->name == package) classes = VpiPackageClasses(*decl);
  }
  return classes;
}

// §8.25: the argument of the specialization `args` binding the class parameter
// `name`, the `index`th the class declares: by name where the specialization
// names its arguments, .T(B2), and by position otherwise, (2, B2); null where
// it binds none, which leaves the parameter its default (§8.25.1).
const DataType* TypeArgument(std::span<const DataType> args, std::size_t index,
                             std::string_view name) {
  const auto kNamed = std::ranges::find(args, name, &DataType::param_arg_name);
  if (kNamed != args.end()) return &*kNamed;
  const bool kPositional = std::ranges::all_of(
      args, [](const DataType& arg) { return arg.param_arg_name.empty(); });
  return kPositional && index < args.size() ? &args[index] : nullptr;
}

// §9.3.4: the declaration of the variable `name` that a block named `block`,
// written anywhere in the statement `s`, declares; null where none does.
const Stmt* NamedBlockVarDecl(const Stmt* s, std::string_view block,
                              std::string_view name) {
  if (s == nullptr) return nullptr;
  const Stmt* found = nullptr;
  if (s->label == block) {
    for (const Stmt* item : BlockItems(*s)) {
      if (item->kind == StmtKind::kVarDecl && item->var_name == name) {
        found = item;
      }
    }
  }
  ForEachChildStmt(s, [&](const Stmt* sub) {
    if (const Stmt* inner = NamedBlockVarDecl(sub, block, name)) found = inner;
  });
  return found;
}

}  // namespace

std::string_view VpiClassNameOf(const BodyWalk& walk, std::string_view name) {
  const auto kTarget = walk.design.type_targets.find(name);
  return kTarget == walk.design.type_targets.end() ? name : kTarget->second;
}

VpiScopedClass VpiFindClassDecl(const BodyWalk& walk, std::string_view name,
                                std::string_view package) {
  name = VpiClassNameOf(walk, name);
  if (!package.empty()) {
    return {ClassNamed(PackageClasses(walk.design, package), name),
            std::string(package)};
  }
  const ClassDecl* decl = ClassNamed(walk.mod.class_decls, name);
  if (decl != nullptr) return {decl, walk.prefix};
  decl = ClassNamed(walk.design.cu_class_decls, name);
  if (decl != nullptr) return {decl, "$unit"};
  for (const RtlirImport& entry : walk.mod.imports) {
    if (!entry.is_wildcard && entry.item_name != name) continue;
    decl = ClassNamed(PackageClasses(walk.design, entry.package_name), name);
    if (decl != nullptr) return {decl, std::string(entry.package_name)};
  }
  return {};
}

const ModuleItem* VpiMethodNamed(const ClassDecl& cls, std::string_view name) {
  for (const ClassMember* member : cls.members) {
    if (member->kind == ClassMemberKind::kMethod &&
        member->method->name == name) {
      return member->method;
    }
  }
  return nullptr;
}

VpiHeldClass VpiBaseOf(const ClassDecl& decl, std::span<const DataType> args) {
  if (!decl.type_param_names.contains(decl.base_class)) {
    return {decl.base_class, decl.base_class_type_params};
  }
  const auto kIndex = static_cast<std::size_t>(
      std::ranges::find(decl.params, decl.base_class,
                        &std::pair<std::string_view, Expr*>::first) -
      decl.params.begin());
  const DataType* arg = TypeArgument(args, kIndex, decl.base_class);
  const DataType& base = arg != nullptr ? *arg : decl.param_types.at(kIndex);
  return {base.type_name, base.type_params};
}

const Stmt* VpiNamedBlockVarDecl(const RtlirModule& mod, std::string_view block,
                                 std::string_view name) {
  const Stmt* found = nullptr;
  for (const RtlirProcess& proc : mod.processes) {
    if (const Stmt* decl = NamedBlockVarDecl(proc.body, block, name)) {
      found = decl;
    }
  }
  return found;
}

}  // namespace delta
