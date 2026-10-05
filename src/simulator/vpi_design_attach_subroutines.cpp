#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// Where the tasks and functions of one scope are made: the scope object
// holding them, null for the compilation unit where its data made none; the
// flat name the made objects are keyed under; and whether the scope's default
// lifetime is automatic (§13.3.1, §13.4.2).
struct SubroutineScope {
  VpiObject* scope;
  std::string key;
  bool automatic;
};

// The module, interface or program the compilation unit declares under
// `name`, null for none.
const ModuleDecl* ElementDeclNamed(const RtlirDesign& design,
                                   std::string_view name) {
  if (design.compilation_unit == nullptr) return nullptr;
  const CompilationUnit& unit = *design.compilation_unit;
  for (const auto* list : {&unit.modules, &unit.interfaces, &unit.programs}) {
    for (const ModuleDecl* decl : *list) {
      if (decl != nullptr && decl->name == name) return decl;
    }
  }
  return nullptr;
}

// §37.41 with §37.3.7, §13.3.1 and §13.4.2: the task or function `item`
// stands as in `where`, named after it, full-named under the scope (detail 5
// for a package's), and automatic where it is declared so or declared without
// a lifetime in a scope whose default is automatic. An item that declares
// neither a task nor a function makes nothing.
void MakeSubroutine(const SubroutineScope& where, const ModuleItem* item,
                    const VpiAttachBuild& build, VpiSubroutineObjects& made) {
  if (item == nullptr || (item->kind != ModuleItemKind::kTaskDecl &&
                          item->kind != ModuleItemKind::kFunctionDecl)) {
    return;
  }
  VpiObject* tf = build.alloc();
  tf->type = item->kind == ModuleItemKind::kTaskDecl ? vpiTask : vpiFunction;
  tf->name = build.keep(std::string(item->name));
  tf->full_name = VpiScopedFullName(where.scope, item->name);
  tf->parent = where.scope;
  tf->automatic = item->is_automatic || (where.automatic && !item->is_static);
  if (where.scope != nullptr) where.scope->children.push_back(tf);
  made[{item, where.key}] = tf;
}

// The tasks and functions each module instance declares.
void MakeInstanceSubroutines(const RtlirDesign& design,
                             const VpiObjectMap& objects,
                             const VpiAttachBuild& build,
                             VpiSubroutineObjects& made) {
  WalkInstancePaths(
      &design, [&](const RtlirModule* mod, const std::string& prefix) {
        VpiObject* scope = FindObjectForFlatName(
            objects, prefix.empty() ? std::string(mod->name) : prefix);
        if (scope == nullptr) return;
        const ModuleDecl* decl = ElementDeclNamed(design, mod->name);
        const SubroutineScope kWhere{scope, prefix,
                                     decl != nullptr && decl->is_automatic};
        for (const ModuleItem* item : mod->function_decls) {
          MakeSubroutine(kWhere, item, build, made);
        }
      });
}

// The tasks and functions each package declares.
void MakePackageSubroutines(const RtlirDesign& design,
                            const VpiObjectMap& objects,
                            const VpiAttachBuild& build,
                            VpiSubroutineObjects& made) {
  for (const PackageDecl* pkg : design.packages) {
    if (pkg == nullptr) continue;
    const std::string kPackage(pkg->name);
    VpiObject* scope = FindObjectForFlatName(objects, kPackage);
    if (scope == nullptr) continue;
    const SubroutineScope kWhere{scope, kPackage, pkg->is_automatic};
    for (const ModuleItem* item : pkg->items) {
      MakeSubroutine(kWhere, item, build, made);
    }
  }
}

// The tasks and functions of the compilation unit, which the unit's scope
// object holds where its data made one. §37.10 detail 6: none is reached by
// name.
void MakeUnitSubroutines(const RtlirDesign& design, const VpiObjectMap& objects,
                         const VpiAttachBuild& build,
                         VpiSubroutineObjects& made) {
  auto unit = objects.find("$unit");
  const SubroutineScope kWhere{unit == objects.end() ? nullptr : unit->second,
                               "$unit", false};
  for (const ModuleItem* item : design.cu_function_decls) {
    MakeSubroutine(kWhere, item, build, made);
    auto found = made.find({item, kWhere.key});
    if (found != made.end()) found->second->in_compilation_unit = true;
  }
}

}  // namespace

VpiSubroutineObjects AttachSubroutines(const RtlirDesign* design,
                                       const VpiObjectMap& objects,
                                       const VpiAttachBuild& build) {
  // §37.41: each task and function a design declares is a task or function
  // object of the instance or package declaring it. Nothing made one, so
  // vpiTaskFunc reached none and no call reached what it calls.
  VpiSubroutineObjects made;
  if (design == nullptr) return made;
  MakeInstanceSubroutines(*design, objects, build, made);
  MakePackageSubroutines(*design, objects, build, made);
  MakeUnitSubroutines(*design, objects, build, made);
  return made;
}

}  // namespace delta
