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
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct TfDeclScope {
  VpiObject* iface;
  std::string key_prefix;
  const VpiSubroutineObjects& made;
  SimContext& ctx;
  const VpiAttachBuild& build;
};

VpiObject* DefinitionAt(const TfDeclScope& scope,
                        const GenBlockSubroutineScope* where,
                        std::string_view name) {
  if (where == nullptr) return nullptr;
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

void MakeForkjoinDecls(const TfDeclScope& scope, std::string_view name) {
  const std::vector<std::string_view>& defs =
      *scope.ctx.FindForkjoinTask(scope.key_prefix + std::string(name));
  if (defs.empty()) {
    MakeTfDecl(scope, name, vpiForkJoinAcc, nullptr);
    return;
  }
  for (std::string_view own : defs) {
    MakeTfDecl(
        scope, name, vpiForkJoinAcc,
        DefinitionAt(scope, scope.ctx.FindGenBlockSubroutineScope(own), name));
  }
}

void MakeExternDecl(const TfDeclScope& scope, std::string_view name) {
  const GenBlockSubroutineScope* where = scope.ctx.FindGenBlockSubroutineScope(
      scope.key_prefix + std::string(name));
  MakeTfDecl(scope, name, vpiExternAcc, DefinitionAt(scope, where, name));
}

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

VpiObject* ModportTfDecl(const TfDeclScope& scope, const RtlirModule& ifc,
                         VpiObject* io_decl, std::string_view name) {
  for (VpiObject* child : scope.iface->children) {
    if (child->type == vpiInterfaceTfDecl && child->name == name) return child;
  }
  const ModuleItem* own = *std::ranges::find_if(
      ifc.function_decls,
      [name](const ModuleItem* item) { return item->name == name; });
  VpiObject* decl = scope.build.alloc();
  decl->type = vpiInterfaceTfDecl;
  decl->name = io_decl->name;
  decl->full_name = io_decl->full_name;
  decl->parent = io_decl;
  decl->access_type = vpiExternAcc;
  std::string_view instance = scope.key_prefix;
  instance.remove_suffix(1);
  decl->tf_decl = scope.made.at({own, std::string(instance)});
  return decl;
}

void MakeModportTfIoDecls(const TfDeclScope& scope, const RtlirModule& ifc) {
  for (const ModportDecl* modport_decl : ifc.modports) {
    VpiObject* modport = *std::ranges::find_if(
        scope.iface->children, [modport_decl](const VpiObject* child) {
          return child->type == vpiModport && child->name == modport_decl->name;
        });
    for (const ModportPort& port : modport_decl->ports) {
      if (!port.is_import && !port.is_export) continue;
      VpiObject* io_decl = scope.build.alloc();
      io_decl->type = vpiIODecl;
      io_decl->name = scope.build.keep(std::string(port.name));
      io_decl->full_name = modport->full_name + "." + std::string(port.name);
      io_decl->parent = modport;
      io_decl->io_expr = ModportTfDecl(scope, ifc, io_decl, port.name);
      modport->children.push_back(io_decl);
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
        const TfDeclScope kScope{iface, prefix + ".", made, ctx, build};
        MakeInterfaceTfDecls(kScope, *mod);
        MakeModportTfIoDecls(kScope, *mod);
      });
}

}  // namespace delta
