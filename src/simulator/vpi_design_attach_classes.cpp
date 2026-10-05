#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// A class defn made for a class declaration, with the flat name of the scope
// the declaration's expressions resolve their names in.
struct MadeClassDefn {
  const ClassDecl* decl;
  VpiObject* defn;
  std::string prefix;
};

// §37.31: the class defn `decl` stands as, hung from the scope declaring it
// where a scope object holds it, reporting its name and whether it is virtual.
void MakeClassDefn(VpiObject* scope, const ClassDecl* decl,
                   const std::string& prefix, const VpiAttachBuild& build,
                   std::vector<MadeClassDefn>& made) {
  if (decl == nullptr) return;
  VpiObject* defn = build.alloc();
  defn->type = vpiClassDefn;
  defn->name = build.keep(std::string(decl->name));
  defn->full_name = VpiScopedFullName(scope, decl->name);
  defn->parent = scope;
  defn->is_virtual = decl->is_virtual;
  if (scope != nullptr) scope->children.push_back(defn);
  made.push_back({decl, defn, prefix});
}

// The class defns of the classes each module instance declares.
void MakeInstanceClassDefns(const RtlirDesign& design,
                            const VpiObjectMap& objects,
                            const VpiAttachBuild& build,
                            std::vector<MadeClassDefn>& made) {
  WalkInstancePaths(
      &design, [&](const RtlirModule* mod, const std::string& prefix) {
        VpiObject* scope = FindObjectForFlatName(
            objects, prefix.empty() ? std::string(mod->name) : prefix);
        if (scope == nullptr) return;
        for (const ClassDecl* decl : mod->class_decls) {
          MakeClassDefn(scope, decl, prefix, build, made);
        }
      });
}

// The class defns of the classes each package declares.
void MakePackageClassDefns(const RtlirDesign& design,
                           const VpiObjectMap& objects,
                           const VpiAttachBuild& build,
                           std::vector<MadeClassDefn>& made) {
  for (const PackageDecl* pkg : design.packages) {
    if (pkg == nullptr) continue;
    const std::string kPackage(pkg->name);
    VpiObject* scope = FindObjectForFlatName(objects, kPackage);
    if (scope == nullptr) continue;
    for (const ModuleItem* item : pkg->items) {
      if (item != nullptr && item->kind == ModuleItemKind::kClassDecl) {
        MakeClassDefn(scope, item->class_decl, kPackage, build, made);
      }
    }
  }
}

// The class defns of the compilation unit's classes, which the unit's scope
// object holds where its data made one and which are otherwise reached only
// with a NULL reference. §37.10 detail 6: none is reached by name.
void MakeUnitClassDefns(const RtlirDesign& design, const VpiObjectMap& objects,
                        const VpiAttachBuild& build,
                        std::vector<MadeClassDefn>& made) {
  auto unit = objects.find("$unit");
  VpiObject* scope = unit == objects.end() ? nullptr : unit->second;
  for (const ClassDecl* decl : design.cu_class_decls) {
    MakeClassDefn(scope, decl, "$unit", build, made);
    if (decl != nullptr) made.back().defn->in_compilation_unit = true;
  }
}

// The package a qualified class name such as `pkg::Base` names, and the class
// it names in it; an unqualified name names no package.
struct ClassReference {
  std::string_view package;
  std::string_view name;
};

ClassReference SplitClassReference(std::string_view written) {
  const std::size_t kColons = written.rfind("::");
  if (kColons == std::string_view::npos) return {{}, written};
  return {written.substr(0, kColons), written.substr(kColons + 2)};
}

// Whether `candidate` is the class `ref` names from the scope `derived` is
// declared in: the package's class of that name where `ref` is qualified, and
// otherwise a class of that name declared beside `derived`.
bool NamesClassBeside(const MadeClassDefn& candidate,
                      const MadeClassDefn& derived, const ClassReference& ref) {
  const VpiObject* scope = candidate.defn->parent;
  if (!ref.package.empty()) {
    return scope != nullptr && scope->type == vpiPackage &&
           scope->name == ref.package;
  }
  return scope == derived.defn->parent && candidate.defn->in_compilation_unit ==
                                              derived.defn->in_compilation_unit;
}

// §8.13: the class defn of the class `derived` extends, one declared beside it
// or a package's it names, and otherwise one of the compilation unit; null
// where the design declares none of that name.
VpiObject* BaseClassDefn(const MadeClassDefn& derived,
                         const std::vector<MadeClassDefn>& made) {
  const ClassReference kRef = SplitClassReference(derived.decl->base_class);
  VpiObject* in_unit = nullptr;
  for (const MadeClassDefn& candidate : made) {
    if (candidate.decl->name != kRef.name) continue;
    if (NamesClassBeside(candidate, derived, kRef)) return candidate.defn;
    if (kRef.package.empty() && candidate.defn->in_compilation_unit) {
      in_unit = candidate.defn;
    }
  }
  return in_unit;
}

// §37.31 details 5 and 6 with §8.13 and §8.17: the extends object of a derived
// class, related to a class typespec of its base and holding the arguments its
// constructor chaining passes; and the derived class among those its base's
// vpiDerivedClasses iteration returns.
void MakeExtends(const MadeClassDefn& derived,
                 const std::vector<MadeClassDefn>& made,
                 const VpiObjectMap& objects, SimContext& ctx,
                 const VpiAttachBuild& build) {
  VpiObject* extends = build.alloc();
  extends->type = vpiExtends;
  extends->parent = derived.defn;
  derived.defn->children.push_back(extends);
  VpiObject* typespec = build.alloc();
  typespec->type = vpiClassTypespec;
  typespec->name = build.keep(
      std::string(SplitClassReference(derived.decl->base_class).name));
  typespec->parent = extends;
  extends->children.push_back(typespec);
  for (const Expr* arg : derived.decl->extends_args) {
    VpiObject* obj =
        VpiInstanceExpression(arg, objects, derived.prefix, ctx, build);
    if (obj == nullptr) continue;
    obj->parent = extends;
    extends->children.push_back(obj);
  }
  VpiObject* base = BaseClassDefn(derived, made);
  if (base == nullptr) return;
  typespec->children.push_back(base);
  base->derived_classes.push_back(derived.defn);
}

// §37.17 detail 24 and §37.41 detail 4: the visibility `member` was declared
// with, 0 for a member declared neither local nor protected.
int DeclaredVisibility(const ClassMember& member) {
  if (member.is_local) return vpiLocalVis;
  return member.is_protected ? vpiProtectedVis : 0;
}

// §37.17 with §6.18 and §8.3: the kind of variable a property of `type`
// is, a class var where the type names a class or a typedef of one.
int PropertyKind(const DataType& type, const RtlirDesign& design,
                 const std::vector<MadeClassDefn>& made) {
  if (type.kind != DataTypeKind::kNamed) {
    return VpiDataTypeVariableKind(type.kind);
  }
  const bool kNamesMadeClass =
      std::ranges::any_of(made, [&](const MadeClassDefn& candidate) {
        return candidate.decl->name == type.type_name;
      });
  if (kNamesMadeClass || design.type_targets.contains(type.type_name)) {
    return vpiClassVar;
  }
  const auto kFound = design.type_kinds.find(type.type_name);
  if (kFound == design.type_kinds.end()) return kVpiReg;
  return VpiDataTypeVariableKind(kFound->second);
}

// §37.31 detail 1 with §37.17: the variable a property of the class stands
// as, static or automatic, of the kind its type takes and an array var where
// it declares unpacked dimensions. Detail 25 full-names a static property
// through its class defn, and gives an automatic one no full name.
void MakeProperty(const MadeClassDefn& owner, const ClassMember& member,
                  const RtlirDesign& design,
                  const std::vector<MadeClassDefn>& made,
                  const VpiAttachBuild& build) {
  VpiObject* var = build.alloc();
  var->type = member.unpacked_dims.empty()
                  ? PropertyKind(member.data_type, design, made)
                  : vpiArrayVar;
  var->name = build.keep(std::string(member.name));
  var->full_name = VpiClassMemberFullName(member.is_static, "",
                                          owner.defn->full_name, member.name);
  var->parent = owner.defn;
  var->visibility = DeclaredVisibility(member);
  owner.defn->children.push_back(var);
}

// §37.31 detail 1 with §37.41: the task or function a method the class
// declares stands as, a method of the class defn full-named through it
// (detail 5), with the visibility it was declared with, virtual where it
// was declared virtual or pure virtual (§8.20, §8.21), and automatic, the
// one lifetime §8.6 gives a method.
void MakeMethod(const MadeClassDefn& owner, const ClassMember& member,
                const VpiAttachBuild& build) {
  const ModuleItem* item = member.method;
  if (item == nullptr) return;
  VpiObject* method = build.alloc();
  method->type =
      item->kind == ModuleItemKind::kTaskDecl ? vpiTask : vpiFunction;
  method->name = build.keep(std::string(item->name));
  method->full_name = owner.defn->full_name + "::" + std::string(item->name);
  method->parent = owner.defn;
  method->visibility = DeclaredVisibility(member);
  method->is_virtual = member.is_virtual || member.is_pure_virtual;
  method->automatic = true;
  owner.defn->children.push_back(method);
}

// §37.31: the properties and methods of the class `owner` was made for, in
// the order the class declares them. A parameter is no property of it.
void MakeMembers(const MadeClassDefn& owner, const RtlirDesign& design,
                 const std::vector<MadeClassDefn>& made,
                 const VpiAttachBuild& build) {
  for (const ClassMember* member : owner.decl->members) {
    if (member == nullptr) continue;
    if (member->kind == ClassMemberKind::kMethod) {
      MakeMethod(owner, *member, build);
    } else if (member->kind == ClassMemberKind::kProperty &&
               !member->is_param) {
      MakeProperty(owner, *member, design, made, build);
    }
  }
}

}  // namespace

std::string VpiScopedFullName(const VpiObject* scope, std::string_view name) {
  if (scope == nullptr) return VpiCompilationUnitFullName(name);
  if (scope->full_name.ends_with("::")) {
    return scope->full_name + std::string(name);
  }
  return scope->full_name + "." + std::string(name);
}

VpiClassDefnObjects AttachClassDefinitions(const RtlirDesign* design,
                                           const VpiObjectMap& objects,
                                           SimContext& ctx,
                                           const VpiAttachBuild& build) {
  // §37.31: each class a design declares is a class defn, reached from the
  // instance or package declaring it, or with a NULL reference for a class of
  // the compilation unit. Nothing made one, so vpiClassDefn reached none.
  if (design == nullptr) return {};
  std::vector<MadeClassDefn> made;
  MakeInstanceClassDefns(*design, objects, build, made);
  MakePackageClassDefns(*design, objects, build, made);
  MakeUnitClassDefns(*design, objects, build, made);
  for (const MadeClassDefn& owner : made) {
    MakeMembers(owner, *design, made, build);
    if (!owner.decl->base_class.empty()) {
      MakeExtends(owner, made, objects, ctx, build);
    }
  }
  VpiClassDefnObjects defns;
  for (const MadeClassDefn& owner : made) {
    defns[{owner.decl, owner.prefix}] = owner.defn;
  }
  return defns;
}

}  // namespace delta
