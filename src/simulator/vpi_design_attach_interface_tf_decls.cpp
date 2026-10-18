#include "simulator/vpi_design_attach_interface_tf_decls.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"

namespace delta {
namespace {

// The interface instance whose interface tf decls are made, with the prefix
// the lowerer keys its subroutines under, "i." for the instance "i".
struct TfDeclScope {
  VpiObject* iface;
  std::string key_prefix;
  const VpiSubroutineObjects& made;
  SimContext& ctx;
  const VpiAttachBuild& build;
};

// The task or function `made` holds for the definition of `name` that the
// instance `where` runs in gives through one of its interface ports, `task
// a.Read` (§25.7.3); null where `where` names no instance or it gives none.
VpiObject* DefinitionAt(const TfDeclScope& scope,
                        const GenBlockSubroutineScope* where,
                        std::string_view name) {
  if (where == nullptr) return nullptr;
  // The lowerer's prefix ends in a `.`, which the instance path `made` is
  // keyed by does not.
  const std::string_view kPrefix = where->inst_prefix;
  const std::string_view kInstance =
      kPrefix.substr(0, kPrefix.find_last_of('.'));
  VpiObject* found = nullptr;
  for (const auto& [key, tf] : scope.made) {
    if (key.second == kInstance && key.first->name == name) found = tf;
  }
  return found;
}

void MakeTfDecl(const TfDeclScope& scope, std::string_view name, int access,
                VpiObject* definition) {
  VpiObject* decl = scope.build.alloc();
  decl->type = vpiInterfaceTfDecl;
  decl->name = scope.build.keep(std::string(name));
  decl->full_name = scope.iface->full_name + "." + std::string(name);
  decl->parent = scope.iface;
  decl->access_type = access;
  decl->tf_decl = definition;
  scope.iface->children.push_back(decl);
}

// §25.7.4 with §37.8 detail 1: a decl per definition the connected modules
// give the extern forkjoin task `name`, and one reaching none where they give
// none.
void MakeForkjoinDecls(const TfDeclScope& scope, std::string_view name) {
  const std::vector<std::string_view>* defs =
      scope.ctx.FindForkjoinTask(scope.key_prefix + std::string(name));
  if (defs == nullptr || defs->empty()) {
    MakeTfDecl(scope, name, vpiForkJoinAcc, nullptr);
    return;
  }
  for (std::string_view own : *defs) {
    MakeTfDecl(
        scope, name, vpiForkJoinAcc,
        DefinitionAt(scope, scope.ctx.FindGenBlockSubroutineScope(own), name));
  }
}

// §25.7.3: the one module that exports `name` to the instance gives its
// definition, which a call through the instance runs in that module.
void MakeExternDecl(const TfDeclScope& scope, std::string_view name) {
  const GenBlockSubroutineScope* where = scope.ctx.FindGenBlockSubroutineScope(
      scope.key_prefix + std::string(name));
  MakeTfDecl(scope, name, vpiExternAcc, DefinitionAt(scope, where, name));
}

// §25.7: the interface declares a subroutine a module defines by `extern` or
// by `export` in a modport, and may do both for the same one.
void MakeInterfaceTfDecls(const TfDeclScope& scope, const RtlirModule& ifc) {
  std::vector<std::string_view> declared;
  for (const ModuleItem* proto : ifc.function_decls) {
    if (!proto->is_extern) continue;
    declared.push_back(proto->name);
    if (proto->is_forkjoin) {
      MakeForkjoinDecls(scope, proto->name);
    } else {
      MakeExternDecl(scope, proto->name);
    }
  }
  for (const ModportDecl* modport : ifc.modports) {
    for (const ModportPort& port : modport->ports) {
      if (!port.is_export ||
          std::ranges::find(declared, port.name) != declared.end()) {
        continue;
      }
      declared.push_back(port.name);
      MakeExternDecl(scope, port.name);
    }
  }
}

}  // namespace

void AttachInterfaceTfDecls(const RtlirDesign* design,
                            const VpiObjectMap& objects,
                            const VpiSubroutineObjects& made, SimContext& ctx,
                            const VpiAttachBuild& build) {
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix, VpiObject* iface) {
        if (!mod->is_interface) return;
        MakeInterfaceTfDecls(
            {iface, prefix.empty() ? "" : prefix + ".", made, ctx, build},
            *mod);
      });
}

}  // namespace delta
