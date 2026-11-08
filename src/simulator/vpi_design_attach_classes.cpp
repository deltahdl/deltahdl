#include <algorithm>
#include <cstddef>
#include <limits>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_attribute.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_class_objects.h"
#include "simulator/vpi_class_typespecs.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_prefixed_refs.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_method_contents.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_named_type_kinds.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

struct MadeClassDefn {
  const ClassDecl* decl;
  VpiObject* defn;
  std::string prefix;
  const RtlirNodeAttributes* attrs;
  const RtlirModule* mod = nullptr;
  std::string_view package = {};
  std::string block = {};
};

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
  scope->children.push_back(defn);
  made.push_back({decl, defn, prefix, nullptr});
}

bool DeclaredInGenerateBlock(const RtlirModule& mod, const ClassDecl* decl) {
  return std::ranges::any_of(mod.gen_block_classes,
                             [decl](const RtlirGenBlockClass& declared) {
                               return declared.decl == decl;
                             });
}

void MakeInstanceClassDefns(const RtlirDesign& design,
                            const VpiObjectMap& objects,
                            const VpiAttachBuild& build,
                            std::vector<MadeClassDefn>& made) {
  WalkInstancePaths(
      &design, [&](const RtlirModule* mod, const std::string& prefix) {
        VpiObject* scope = FindObjectForFlatName(
            objects, prefix.empty() ? std::string(mod->name) : prefix);
        if (scope == nullptr) return;
        const auto kMake = [&](VpiObject* within, const ClassDecl* decl) {
          MakeClassDefn(within, decl, prefix, build, made);
          made.back().attrs = &mod->node_attrs;
          made.back().mod = mod;
        };
        for (const ClassDecl* decl : mod->class_decls) {
          if (decl != nullptr && !DeclaredInGenerateBlock(*mod, decl)) {
            kMake(scope, decl);
          }
        }
        for (const RtlirGenBlockClass& declared : mod->gen_block_classes) {
          VpiObject* block = VpiGenScopeOf(scope, declared.gen_block_path);
          kMake(block, declared.decl);
          made.back().block = block->full_name;
        }
      });
}

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
      if (item != nullptr && item->kind == ModuleItemKind::kClassDecl &&
          item->class_decl != nullptr) {
        MakeClassDefn(scope, item->class_decl, kPackage, build, made);
        made.back().attrs = &design.node_attrs;
        made.back().package = pkg->name;
      }
    }
  }
}

void MakeUnitClassDefns(const RtlirDesign& design, const VpiObjectMap& objects,
                        const VpiAttachBuild& build,
                        std::vector<MadeClassDefn>& made) {
  for (const VpiUnitScope& at : VpiUnitScopes(design, objects)) {
    for (const ClassDecl* decl : at.unit->classes) {
      MakeClassDefn(at.scope, decl, "$unit", build, made);
      if (decl == nullptr) continue;
      made.back().defn->in_compilation_unit = true;
      made.back().attrs = &design.node_attrs;
    }
  }
}

void MakeNestedClassDefns(const VpiAttachBuild& build,
                          std::vector<MadeClassDefn>& made) {
  for (std::size_t i = 0; i < made.size(); ++i) {
    for (const ClassMember* member : made[i].decl->members) {
      if (member->kind != ClassMemberKind::kClassDecl) continue;
      const MadeClassDefn kOuter = made[i];
      MakeClassDefn(kOuter.defn, member->nested_class, kOuter.prefix, build,
                    made);
      MadeClassDefn& nested = made.back();
      nested.defn->full_name =
          kOuter.defn->full_name + "::" + std::string(nested.decl->name);
      nested.attrs = kOuter.attrs;
      nested.mod = kOuter.mod;
      nested.package = kOuter.package;
      nested.block = kOuter.block;
    }
  }
}

struct ClassReference {
  std::string_view package;
  std::string_view name;
};

ClassReference SplitClassReference(std::string_view written) {
  const std::size_t kColons = written.rfind("::");
  if (kColons == std::string_view::npos) return {{}, written};
  return {written.substr(0, kColons), written.substr(kColons + 2)};
}

constexpr int kNotAround = std::numeric_limits<int>::max();

int ScopesOutTo(const MadeClassDefn& candidate, const MadeClassDefn& derived,
                const ClassReference& ref) {
  const VpiObject* scope = candidate.defn->parent;
  if (!ref.package.empty()) {
    const bool kInPackage = scope != nullptr && scope->type == vpiPackage &&
                            scope->name == ref.package;
    return kInPackage ? 0 : kNotAround;
  }
  if (candidate.defn->in_compilation_unit !=
      derived.defn->in_compilation_unit) {
    return kNotAround;
  }
  int out = 0;
  for (const VpiObject* around = derived.defn->parent;;
       around = around->parent) {
    if (around == scope) return out;
    if (around->type != vpiGenScope && around->type != vpiGenScopeArray) {
      return kNotAround;
    }
    ++out;
  }
}

VpiObject* BaseClassDefn(const MadeClassDefn& derived,
                         const std::vector<MadeClassDefn>& made) {
  const ClassReference kRef{derived.decl->base_class_scope,
                            derived.decl->base_class};
  VpiObject* in_unit = nullptr;
  VpiObject* nearest = nullptr;
  int nearest_out = kNotAround;
  for (const MadeClassDefn& candidate : made) {
    if (candidate.decl->name != kRef.name) continue;
    const int kOut = ScopesOutTo(candidate, derived, kRef);
    if (kOut < nearest_out) {
      nearest = candidate.defn;
      nearest_out = kOut;
    }
    if (kRef.package.empty() && candidate.defn->in_compilation_unit) {
      in_unit = candidate.defn;
    }
  }
  return nearest != nullptr ? nearest : in_unit;
}

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
  typespec->name = build.keep(std::string(derived.decl->base_class));
  typespec->parent = extends;
  extends->children.push_back(typespec);
  static const std::vector<std::string_view> kNoGenBlocks;
  const VpiCallStand kStand{derived.defn, derived.mod, derived.package};
  const auto kExpression = [&](const Expr* expr) {
    return VpiGenBlockExpression(expr,
                                 {objects, derived.prefix, kNoGenBlocks,
                                  nullptr, derived.attrs, &kStand},
                                 ctx, build);
  };
  for (const Expr* arg : derived.decl->extends_args) {
    VpiObject* obj = kExpression(arg);
    if (obj == nullptr) continue;
    obj->parent = extends;
    extends->children.push_back(obj);
  }
  VpiObject* base = BaseClassDefn(derived, made);
  if (base == nullptr) return;
  typespec->children.push_back(base);
  base->derived_classes.push_back(derived.defn);
  const auto kBase = std::ranges::find(made, base, &MadeClassDefn::defn);
  VpiMakeExtendsParamAssigns(typespec, *derived.decl, *kBase->decl, kExpression,
                             build);
}

int DeclaredVisibility(const ClassMember& member) {
  if (member.is_local) return vpiLocalVis;
  return member.is_protected ? vpiProtectedVis : 0;
}

int PropertyKind(const DataType& type, const RtlirDesign& design,
                 const std::vector<MadeClassDefn>& made,
                 std::string_view package) {
  if (type.kind != DataTypeKind::kNamed) {
    return VpiDataTypeVariableKind(type.kind);
  }
  const bool kNamesMadeClass =
      std::ranges::any_of(made, [&](const MadeClassDefn& candidate) {
        return candidate.decl->name == type.type_name;
      });
  if (kNamesMadeClass) return vpiClassVar;
  return VpiScopedTypeVariableKind(design, package, type);
}

VpiObject* NamedTypeParameter(const MadeClassDefn& owner,
                              const DataType& type) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty()) {
    return nullptr;
  }
  const auto kFound = std::ranges::find_if(
      owner.defn->children, [&type](const VpiObject* child) {
        return child->type == vpiTypeParameter && child->name == type.type_name;
      });
  return kFound == owner.defn->children.end() ? nullptr : *kFound;
}

VpiObject* MakeProperty(const MadeClassDefn& owner, const ClassMember& member,
                        const RtlirDesign& design,
                        const std::vector<MadeClassDefn>& made,
                        const VpiAttachBuild& build) {
  const int kKind = PropertyKind(member.data_type, design, made, owner.package);
  VpiObject* var = build.alloc();
  if (member.unpacked_dims.empty()) {
    var->type = kKind;
  } else {
    var->type = kKind == vpiNamedEvent ? vpiNamedEventArray : vpiArrayVar;
  }
  var->name = build.keep(std::string(member.name));
  var->full_name = VpiClassMemberFullName(member.is_static, "",
                                          owner.defn->full_name, member.name);
  var->parent = owner.defn;
  var->decl_facts.visibility = DeclaredVisibility(member);
  VpiRecordPropertyDecl(*var, member);
  var->decl_facts.vif_interface =
      VpiVirtualInterfaceOf(design, &member.data_type, owner.mod);
  if (VpiObject* param = NamedTypeParameter(owner, member.data_type)) {
    var->children.push_back(param);
  }
  owner.defn->children.push_back(var);
  return var;
}

void MakeMethod(const MadeClassDefn& owner, const ClassMember& member,
                const RtlirDesign& design, SimContext& ctx,
                const VpiAttachBuild& build) {
  const ModuleItem* item = member.method;
  if (item == nullptr) return;
  VpiObject* method = build.alloc();
  method->type =
      item->kind == ModuleItemKind::kTaskDecl ? vpiTask : vpiFunction;
  method->name = build.keep(std::string(item->name));
  method->full_name = owner.defn->full_name + "::" + std::string(item->name);
  method->parent = owner.defn;
  method->decl_facts.visibility = DeclaredVisibility(member);
  method->is_virtual = member.is_virtual || member.is_pure_virtual;
  method->automatic = true;
  VpiRecordWrittenLocation(method, item->loc, ctx);
  owner.defn->children.push_back(method);
  const bool kInstance = owner.mod != nullptr && !owner.prefix.empty();
  VpiMakeMethodContents(
      method, *item,
      {design, owner.mod, owner.package, kInstance ? owner.prefix + "." : ""},
      ctx, build);
}

void MakeParameter(const MadeClassDefn& owner, std::string_view name, bool type,
                   bool local, const VpiAttachBuild& build) {
  VpiObject* param = build.alloc();
  param->type = type ? vpiTypeParameter : vpiParameter;
  param->name = build.keep(std::string(name));
  param->full_name = owner.defn->full_name + "::" + std::string(name);
  param->parent = owner.defn;
  param->local_param = local;
  owner.defn->children.push_back(param);
}

void MakeParameters(const MadeClassDefn& owner, const VpiAttachBuild& build) {
  const ClassDecl& decl = *owner.decl;
  for (const auto& param : decl.params) {
    MakeParameter(owner, param.first,
                  decl.type_param_names.contains(param.first),
                  decl.localparam_port_names.contains(param.first), build);
  }
  for (const ClassMember* member : decl.members) {
    if (member->kind == ClassMemberKind::kProperty && member->is_param) {
      MakeParameter(owner, member->name,
                    member->data_type.kind == DataTypeKind::kVoid, true, build);
    } else if (member->kind == ClassMemberKind::kTypedef &&
               member->typedef_item->is_localparam) {
      MakeParameter(owner, member->name, true, true, build);
    }
  }
}

struct ClassVarProperty {
  VpiObject* var;
  const ClassMember* member;
  const MadeClassDefn* owner;
};

std::vector<ClassVarProperty> MakeMembers(
    const MadeClassDefn& owner, const RtlirDesign& design,
    const std::vector<MadeClassDefn>& made, SimContext& ctx,
    const VpiAttachBuild& build) {
  std::vector<ClassVarProperty> class_vars;
  for (const ClassMember* member : owner.decl->members) {
    if (member == nullptr) continue;
    if (member->kind == ClassMemberKind::kMethod) {
      MakeMethod(owner, *member, design, ctx, build);
    } else if (member->kind == ClassMemberKind::kProperty &&
               !member->is_param) {
      VpiObject* var = MakeProperty(owner, *member, design, made, build);
      VpiRecordWrittenDims(*var, member->unpacked_dims, ctx);
      if (var->type == vpiClassVar) class_vars.push_back({var, member, &owner});
    }
  }
  return class_vars;
}

void MakeConstraints(const MadeClassDefn& owner, const VpiObjectMap& objects,
                     SimContext& ctx, const VpiAttachBuild& build) {
  static const std::vector<std::string_view> kNoGenBlocks;
  VpiObject* scope = VpiClassNameScope(owner.defn, owner.defn->parent, build);
  const VpiCallStand kStand{owner.defn, owner.mod, owner.package};
  for (const ClassMember* member : owner.decl->members) {
    if (member == nullptr || member->kind != ClassMemberKind::kConstraint) {
      continue;
    }
    VpiObject* constraint = VpiMakeConstraint(
        *member, owner.defn,
        {objects, owner.prefix, kNoGenBlocks, scope, ctx, owner.attrs, &kStand},
        build);
    owner.defn->children.push_back(constraint);
    VpiAttachAttributes(constraint, VpiNodeAttributes(owner.attrs, member),
                        false, ctx, build);
  }
}

}  // namespace

VpiObject* VpiNamedClassDefn(const VpiClassDefnObjects& defns,
                             std::string_view written,
                             const std::string& prefix) {
  const ClassReference kRef = SplitClassReference(written);
  constexpr int kNone = 3;
  VpiObject* best = nullptr;
  int best_rank = kNone;
  for (const auto& [key, defn] : defns) {
    if (key.first->name != kRef.name) continue;
    int rank = 2;
    if (!kRef.package.empty()) {
      rank = key.second == kRef.package ? 0 : kNone;
    } else if (key.second == prefix) {
      rank = 0;
    } else if (key.second == "$unit") {
      rank = 1;
    }
    if (rank < best_rank) {
      best = defn;
      best_rank = rank;
    }
  }
  return best;
}

namespace {

void AttachDeclaredClassTypespec(VpiObject* var, std::string_view written,
                                 VpiObject* defn,
                                 std::string_view specialization,
                                 const VpiAttachBuild& build) {
  VpiObject* held = nullptr;
  if (defn != nullptr) held = VpiSpecializationTypespec(*defn, specialization);
  if (held != nullptr) {
    var->children.push_back(held);
    return;
  }
  VpiObject* typespec = build.alloc();
  typespec->type = vpiClassTypespec;
  typespec->name = build.keep(std::string(SplitClassReference(written).name));
  typespec->parent = var;
  if (defn != nullptr) typespec->children.push_back(defn);
  var->children.push_back(typespec);
}

std::string WrittenClassType(const DataType& type, const RtlirDesign& design) {
  std::string written =
      type.scope_name.empty()
          ? std::string(type.type_name)
          : std::string(type.scope_name) + "::" + std::string(type.type_name);
  const auto kTarget = design.type_targets.find(written);
  return kTarget == design.type_targets.end() ? written
                                              : std::string(kTarget->second);
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
                                           const VpiAttachBuild& build,
                                           VpiClassCallSites& sites) {
  if (design == nullptr) return {};
  std::vector<MadeClassDefn> made;
  std::vector<ClassVarProperty> class_vars;
  MakeInstanceClassDefns(*design, objects, build, made);
  MakePackageClassDefns(*design, objects, build, made);
  MakeUnitClassDefns(*design, objects, build, made);
  MakeNestedClassDefns(build, made);
  for (const MadeClassDefn& owner : made) {
    VpiRecordWrittenLocation(owner.defn, owner.decl->range.start, ctx);
    VpiAttachAttributes(owner.defn, VpiNodeAttributes(owner.attrs, owner.decl),
                        false, ctx, build);
    MakeParameters(owner, build);
    const std::vector<ClassVarProperty> kOwnClassVars =
        MakeMembers(owner, *design, made, ctx, build);
    class_vars.insert(class_vars.end(), kOwnClassVars.begin(),
                      kOwnClassVars.end());
    if (!owner.decl->base_class.empty()) {
      MakeExtends(owner, made, objects, ctx, build);
    }
  }
  for (const MadeClassDefn& owner : made) {
    MakeConstraints(owner, objects, ctx, build);
  }
  VpiClassDefnObjects defns;
  for (const MadeClassDefn& owner : made) {
    defns[{owner.decl, owner.block.empty() ? owner.prefix : owner.block}] =
        owner.defn;
    sites[owner.defn] = {owner.mod, owner.package};
  }
  for (const ClassVarProperty& property : class_vars) {
    const std::string kWritten =
        WrittenClassType(property.member->data_type, *design);
    AttachDeclaredClassTypespec(
        property.var, kWritten,
        VpiNamedClassDefn(defns, kWritten, property.owner->prefix), {}, build);
  }
  VpiAttachClassSpecializations(defns, ctx, build);
  return defns;
}

void AttachClassVarTypespecs(const RtlirDesign* design,
                             const VpiObjectMap& objects,
                             const VpiClassDefnObjects& defns, SimContext& ctx,
                             const VpiAttachBuild& build) {
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirVariable& var : VpiDeclaredVariables(*mod)) {
          VpiObject* obj =
              FindObjectForFlatName(objects, VpiFlatName(prefix, var.name));
          if (obj == nullptr || obj->type != vpiClassVar) continue;
          AttachDeclaredClassTypespec(
              obj, var.class_type_name,
              VpiNamedClassDefn(defns, var.class_type_name, prefix),
              ctx.GetVariableClassType(VpiFlatName(prefix, var.name)), build);
        }
      });
}

}  // namespace delta
