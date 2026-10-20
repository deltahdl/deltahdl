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
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_class_objects.h"
#include "simulator/vpi_class_typespecs.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_method_contents.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// A class defn made for a class declaration, with the flat name of the scope
// the declaration's expressions resolve their names in, and the table the
// attributes elaboration resolved on it and its items are kept in (§37.83):
// its module's, or the design's for a class outside every module.
struct MadeClassDefn {
  const ClassDecl* decl;
  VpiObject* defn;
  std::string prefix;
  const RtlirNodeAttributes* attrs;
  // §37.42: the module declaring the class, whose declarations a call written
  // in it finds its callee among; null for a package's or the unit's class.
  const RtlirModule* mod = nullptr;
  // §26.2: the package declaring the class, empty for none.
  std::string_view package = {};
  // §27.4: the full name of the generate block instance declaring the class,
  // which tells the defns of one declaration in each instance of the block
  // apart; empty for a class declared outside every generate block.
  std::string block = {};
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
  made.push_back({decl, defn, prefix, nullptr});
}

// Whether a generate block of `mod` declares the class `decl`.
bool DeclaredInGenerateBlock(const RtlirModule& mod, const ClassDecl* decl) {
  return std::ranges::any_of(mod.gen_block_classes,
                             [decl](const RtlirGenBlockClass& declared) {
                               return declared.decl == decl;
                             });
}

// The class defns of the classes each module instance declares, and with
// §37.12 and §37.85 one of each class a generate block declares under each
// gen scope that is an instance of the block, full-named in it.
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
      if (item != nullptr && item->kind == ModuleItemKind::kClassDecl &&
          item->class_decl != nullptr) {
        MakeClassDefn(scope, item->class_decl, kPackage, build, made);
        made.back().attrs = &design.node_attrs;
        made.back().package = pkg->name;
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
    if (decl == nullptr) continue;
    made.back().defn->in_compilation_unit = true;
    made.back().attrs = &design.node_attrs;
  }
}

// §37.31 with §8.23: the class defns of the classes the classes `made` holds
// declare, each hung from the defn of the class declaring it, which reaches
// it through vpiInternalScope, full-named through that class as its members
// are (§37.10 detail 5), and standing where that class does. None is a class
// of the compilation unit's own, which a NULL reference reaches. A class
// nested in a nested class is made in turn, as `made` grows.
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

// How far out a class stands that is not the one a reference names.
constexpr int kNotAround = std::numeric_limits<int>::max();

// How far out from the scope `derived` is declared in `candidate` is the
// class `ref` names: the package's class of that name where `ref` is
// qualified, and otherwise a class of that name declared beside `derived` or,
// with §27.4, around the generate block instances it is declared in, one
// further out for each such instance or array of them passed; kNotAround
// where `candidate` is none of these.
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

// §8.13: the class defn of the class `derived` extends, the nearest of those
// declared beside it or around it or a package's it names, and otherwise one
// of the compilation unit; null where the design declares none of that name.
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
  typespec->name = build.keep(std::string(derived.decl->base_class));
  typespec->parent = extends;
  extends->children.push_back(typespec);
  static const std::vector<std::string_view> kNoGenBlocks;
  // §37.42: a call an argument makes stands in the derived class.
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
  // §37.32 detail 3: the parameter values the clause gives the base.
  const auto kBase = std::ranges::find(made, base, &MadeClassDefn::defn);
  VpiMakeExtendsParamAssigns(typespec, *derived.decl, *kBase->decl, kExpression,
                             build);
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

// §37.25 detail 11: the type parameter of the class `owner` was made for
// that `type` names, which, unresolved in the class defn, stands as the
// typespec of a property declared with it; null where it names none.
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

// §37.31 detail 1 with §37.17: the variable a property of the class stands
// as, static or automatic, of the kind its type takes, and where it declares
// unpacked dimensions, whose indices the caller records, a named event array
// for an array of events (§37.27) and an array var for any other. One declared
// with a type parameter of the class reaches it as its typespec.
// Detail 25 full-names a static property through its class defn, and gives an
// automatic one no full name.
VpiObject* MakeProperty(const MadeClassDefn& owner, const ClassMember& member,
                        const RtlirDesign& design,
                        const std::vector<MadeClassDefn>& made,
                        const VpiAttachBuild& build) {
  const int kKind = PropertyKind(member.data_type, design, made);
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
  if (VpiObject* param = NamedTypeParameter(owner, member.data_type)) {
    var->children.push_back(param);
  }
  owner.defn->children.push_back(var);
  return var;
}

// §37.31 detail 1 with §37.41: the task or function a method the class
// declares stands as, a method of the class defn full-named through it
// (detail 5), with the visibility it was declared with, virtual where it
// was declared virtual or pure virtual (§8.20, §8.21), automatic, the one
// lifetime §8.6 gives a method, and holding what any task or function holds.
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
  // §37.3.3: where the method was written.
  VpiRecordWrittenLocation(method, item->loc, ctx);
  owner.defn->children.push_back(method);
  // A width a module's class writes reads the parameters of the instance, as
  // the module's own tasks and functions do.
  const bool kInstance = owner.mod != nullptr && !owner.prefix.empty();
  VpiMakeMethodContents(
      method, *item,
      {design, owner.mod, owner.package, kInstance ? owner.prefix + "." : ""},
      ctx, build);
}

// §37.31 detail 7 with §37.28: the parameter `name` of the class `owner` was
// made for, hung from its class defn and full-named through it as its methods
// are (§37.41 detail 5), a type parameter where `type` says so, and reporting
// vpiLocalParam as `local` says.
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

// §37.31 detail 7: the parameters of the class `owner` was made for, those of
// its parameter port list, local where the list declares them localparam, and
// then those its body declares, every one of them local. A body's type
// parameter is one the parser carries as a typedef where it is a localparam,
// and as a parameter member of no data type where it is not.
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

// A property made as a class var, which reaches the class typespec it was
// declared with once every class defn is made (§37.33 detail 5).
struct ClassVarProperty {
  VpiObject* var;
  const ClassMember* member;
  const MadeClassDefn* owner;
};

// §37.31: the properties and methods of the class `owner` was made for, in
// the order the class declares them; the properties made class vars are
// returned. A parameter is no property of it.
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

// §37.31 with §37.34: the constraints of the class `owner` was made for, in
// the order the class declares them (detail 4). A name in one finds the
// properties of the class and of those it extends first, so they are made
// once every class's extends object is.
void MakeConstraints(const MadeClassDefn& owner, const VpiObjectMap& objects,
                     SimContext& ctx, const VpiAttachBuild& build) {
  static const std::vector<std::string_view> kNoGenBlocks;
  VpiObject* scope = VpiClassNameScope(owner.defn, owner.defn->parent, build);
  // §37.42: a call a constraint makes stands in the class.
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
    // §37.83: the attributes the constraint is written with.
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

// §37.33 detail 5 and §37.32 detail 1: the class typespec the class var
// `var` was declared with, the class type written `written`, whose class defn
// is `defn`: the typespec of the class specialization `specialization` names,
// where `defn` holds one, the type of a variable no class defn contains being
// a specialization; and otherwise one of its own, reaching `defn`.
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

// The class type `type` names, `p::B` behind its package's scope, and the
// class a typedef of one names (§6.18) as the design records it.
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
  // §37.31: each class a design declares is a class defn, reached from the
  // instance or package declaring it, or with a NULL reference for a class of
  // the compilation unit. Nothing made one, so vpiClassDefn reached none.
  if (design == nullptr) return {};
  std::vector<MadeClassDefn> made;
  std::vector<ClassVarProperty> class_vars;
  MakeInstanceClassDefns(*design, objects, build, made);
  MakePackageClassDefns(*design, objects, build, made);
  MakeUnitClassDefns(*design, objects, build, made);
  MakeNestedClassDefns(build, made);
  for (const MadeClassDefn& owner : made) {
    // §37.3.3: where the class was written.
    VpiRecordWrittenLocation(owner.defn, owner.decl->range.start, ctx);
    // §37.83: the attributes the class is written with.
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
  // §37.33 detail 5 with §37.31: a property of a class type, its class found
  // from the scope declaring the class whose property it is. None was made,
  // so vpiClassTypespec of such a property was null.
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
  // §37.33 detail 5: a class var reaches the class typespec it was declared
  // with, whatever class the object it references was created as. None was
  // made, so vpiClassTypespec of a class var was null.
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
