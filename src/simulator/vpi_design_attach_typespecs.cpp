#include "simulator/vpi_design_attach_typespecs.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <iterator>
#include <map>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_class_typespecs.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_typespec_shapes.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

using TypespecsByName = std::unordered_map<std::string_view, VpiObject*>;

using InstanceDefinitions =
    std::unordered_map<const VpiObject*, const ModuleDecl*>;

struct DesignTypespecs {
  const VpiAttachBuild& build;
  SimContext& ctx;
  VpiTypespecShapes& shapes;
  const VpiClassDefnObjects& classes;
  const VpiObjectMap& objects;
  const CompilationUnit& unit;
  const InstanceDefinitions& definitions;
};

struct ScopeTypespecs {
  VpiObject* scope;
  const std::string& prefix;
  const std::unordered_map<std::string_view, std::vector<RtlirEnumMember>>*
      enums;
  const TypespecsByName& outer;
  const std::vector<RtlirImport>& imports;
  const DesignTypespecs& design;
};

void HangIfMade(VpiObject* holder, VpiObject* child) {
  if (child != nullptr) holder->children.push_back(child);
}

void MakeEnumConst(VpiObject* typespec, const RtlirEnumMember& member,
                   const VpiAttachBuild& build) {
  VpiObject* constant = build.alloc();
  constant->type = vpiEnumConst;
  constant->name = build.keep(std::string(member.name));
  constant->parent = typespec;
  auto* storage = build.arena.Create<Variable>();
  storage->value =
      MakeLogic4VecVal(build.arena, 32, static_cast<uint64_t>(member.value));
  constant->var = storage;
  constant->size = 32;
  typespec->children.push_back(constant);
}

DataType MemberType(const StructMember& member) {
  if (member.nested_type != nullptr) return *member.nested_type;
  DataType type;
  type.kind = member.type_kind;
  type.is_signed = member.is_signed;
  type.packed_dim_left = member.packed_dim_left;
  type.packed_dim_right = member.packed_dim_right;
  type.extra_packed_dims = member.extra_packed_dims;
  type.type_name = member.type_name;
  type.scope_name = member.scope_name;
  return type;
}

DataType ElementOf(const DataType& type) {
  DataType element = type;
  element.enum_array_dims.clear();
  if (type.kind != DataTypeKind::kEnum) {
    element.packed_dim_left = nullptr;
    element.packed_dim_right = nullptr;
    element.extra_packed_dims.clear();
  }
  return element;
}

const ModuleDecl& InterfaceNamedFrom(const VpiObject* scope,
                                     const DesignTypespecs& design,
                                     std::string_view name) {
  const VpiObject* at = scope;
  while (at != nullptr && !design.definitions.contains(at)) at = at->parent;
  return VpiElementDeclFrom(at == nullptr ? nullptr : design.definitions.at(at),
                            design.unit, name);
}

struct NamedTypespec {
  VpiObject* typespec = nullptr;
  bool declared = false;
};

class TypespecMaker {
 public:
  TypespecMaker(const ScopeTypespecs& at, const TypespecsByName& made)
      : at_(at), made_(made), build_(at.design.build) {}

  VpiObject* Of(const DataType& type, const std::vector<Expr*>& unpacked,
                std::string_view name, VpiObject* parent) {
    return Shaped(type, DimsOf(type, unpacked), name, parent);
  }

  VpiObject* Shaped(const DataType& type,
                    const std::vector<VpiTypespecDim>& dims,
                    std::string_view name, VpiObject* parent) {
    if (type.kind == DataTypeKind::kNamed && dims.empty()) {
      const NamedTypespec kNamed = Named(type, name, parent);
      if (!kNamed.declared || name.empty()) return kNamed.typespec;
      VpiObject* alias = Alloc(name, parent);
      alias->type = kNamed.typespec->type;
      alias->aliased = kNamed.typespec;
      at_.design.shapes.Share(alias, kNamed.typespec);
      return alias;
    }
    if (dims.empty()) return Own(type, name, parent, name);
    VpiObject* typespec = Alloc(name, parent);
    VpiObject* base =
        type.kind == DataTypeKind::kNamed
            ? Named(type, std::string_view{}, typespec).typespec
            : Own(ElementOf(type), std::string_view{}, typespec, name);
    if (base == nullptr) return nullptr;
    at_.design.shapes.Shape(typespec, dims, base);
    return typespec;
  }

  std::vector<VpiTypespecDim> DimsOf(const DataType& type,
                                     const std::vector<Expr*>& unpacked) {
    std::vector<VpiTypespecDim> dims;
    dims.reserve(unpacked.size());
    for (const Expr* dim : unpacked) dims.push_back(UnpackedDim(dim));
    if (type.kind == DataTypeKind::kEnum) {
      for (const auto& [left, right] : type.enum_array_dims) {
        dims.push_back({false, VpiEvaluatedRange(left, right, at_.design.ctx),
                        0, nullptr});
      }
      return dims;
    }
    for (const PackedRange& dim : WrittenPackedDims(&type, at_.design.ctx)) {
      dims.push_back({false, dim, 0, nullptr});
    }
    return dims;
  }

 private:
  VpiObject* Alloc(std::string_view name, VpiObject* parent) const {
    VpiObject* typespec = build_.alloc();
    typespec->name =
        name.empty() ? std::string_view{} : build_.keep(std::string(name));
    typespec->parent = parent;
    return typespec;
  }

  VpiTypespecDim UnpackedDim(const Expr* dim) {
    VpiTypespecDim made = VpiUnpackedTypespecDim(dim, at_.design.ctx);
    if (made.array_type == vpiAssocArray) {
      made.index_typespec = IndexTypespec(dim->text);
    }
    return made;
  }

  VpiObject* IndexTypespec(std::string_view written) {
    if (std::optional<DataTypeKind> kind = VpiAssocIndexKeywordKind(written)) {
      DataType type;
      type.kind = *kind;
      return Own(type, std::string_view{}, nullptr, std::string_view{});
    }
    DataType named;
    named.kind = DataTypeKind::kNamed;
    named.type_name = written;
    return Named(named, std::string_view{}, nullptr).typespec;
  }

  NamedTypespec Named(const DataType& type, std::string_view name,
                      VpiObject* parent) const {
    const std::string kWritten =
        type.scope_name.empty()
            ? std::string(type.type_name)
            : std::string(type.scope_name) + "::" + std::string(type.type_name);
    auto it = made_.find(type.type_name);
    if (type.scope_name.empty() && it != made_.end()) return {it->second, true};
    auto outer = at_.outer.find(kWritten);
    if (outer != at_.outer.end()) return {outer->second, true};
    if (VpiObject* imported =
            VpiImportedTypespec(kWritten, at_.imports, at_.outer)) {
      return {imported, true};
    }
    VpiObject* defn =
        VpiNamedClassDefn(at_.design.classes, kWritten, at_.prefix);
    if (defn == nullptr) return {};
    VpiObject* typespec = Alloc(name.empty() ? type.type_name : name, parent);
    typespec->type = vpiClassTypespec;
    typespec->children.push_back(defn);
    return {typespec, false};
  }

  VpiObject* Own(const DataType& type, std::string_view name, VpiObject* parent,
                 std::string_view typedef_name) {
    const int kKind = VpiTypespecKind(type.kind);
    VpiObject* typespec = Alloc(name, parent);
    typespec->type = kKind;
    if (kKind == vpiEnumTypespec) {
      FillEnum(typespec, type, typedef_name);
    } else if (kKind == vpiStructTypespec || kKind == vpiUnionTypespec) {
      FillAggregate(typespec, type);
    } else if (kKind == vpiInterfaceTypespec) {
      FillInterface(typespec, type);
    } else if (!name.empty()) {
      typespec->aliased =
          Own(type, std::string_view{}, typespec, std::string_view{});
    }
    return typespec;
  }

  void FillEnum(VpiObject* typespec, const DataType& type,
                std::string_view typedef_name) {
    if (at_.enums != nullptr) {
      auto it = at_.enums->find(typedef_name);
      if (it != at_.enums->end()) {
        for (const RtlirEnumMember& member : it->second) {
          MakeEnumConst(typespec, member, build_);
        }
      }
    }
    DataType base;
    base.kind = type.enum_base_kind == DataTypeKind::kImplicit
                    ? DataTypeKind::kInt
                    : type.enum_base_kind;
    base.is_signed = type.is_signed;
    base.packed_dim_left = type.packed_dim_left;
    base.packed_dim_right = type.packed_dim_right;
    base.type_name = type.enum_base_name;
    typespec->inner_typespec = Of(base, {}, std::string_view{}, typespec);
  }

  void FillInterface(VpiObject* typespec, const DataType& type) {
    VpiObject* of_interface = typespec;
    if (!type.modport_name.empty()) {
      typespec->def_name = std::string(type.modport_name);
      typespec->is_modport = true;
      of_interface = Alloc(std::string_view{}, nullptr);
      of_interface->type = vpiInterfaceTypespec;
      typespec->parent = of_interface;
    }
    of_interface->def_name = std::string(type.type_name);
    const std::vector<std::string_view> kOrdered = OverridableParamNames(
        &InterfaceNamedFrom(at_.scope, at_.design, type.type_name));
    for (std::size_t i = 0; i < type.type_params.size(); ++i) {
      MakeInterfaceParamAssign(of_interface, type.type_params[i],
                               i < kOrdered.size() ? kOrdered[i] : "");
    }
  }

  void MakeInterfaceParamAssign(VpiObject* typespec, const DataType& actual,
                                std::string_view ordered) {
    VpiObject* assign = build_.alloc();
    assign->type = vpiParamAssign;
    assign->parent = typespec;
    VpiObject* param = build_.alloc();
    param->type =
        actual.type_ref_expr != nullptr ? vpiParameter : vpiTypeParameter;
    param->name = build_.keep(std::string(
        actual.param_arg_name.empty() ? ordered : actual.param_arg_name));
    param->parent = assign;
    assign->children.push_back(param);
    assign->rhs =
        actual.type_ref_expr != nullptr
            ? VpiInstanceExpression(actual.type_ref_expr, at_.design.objects,
                                    at_.prefix, at_.design.ctx, build_)
            : Of(actual, {}, std::string_view{}, assign);
    typespec->children.push_back(assign);
  }

  void FillAggregate(VpiObject* typespec, const DataType& type) {
    typespec->packed = type.is_packed;
    typespec->tagged = type.is_tagged;
    typespec->soft = type.is_soft;
    for (const StructMember& member : type.struct_members) {
      MakeTypespecMember(typespec, member);
    }
  }

  void MakeTypespecMember(VpiObject* typespec, const StructMember& member) {
    VpiObject* typespec_member = build_.alloc();
    typespec_member->type = vpiTypespecMember;
    typespec_member->name = build_.keep(std::string(member.name));
    typespec_member->parent = typespec;
    if (member.is_randc) {
      typespec_member->rand_type = vpiRandC;
    } else {
      typespec_member->rand_type = member.is_rand ? vpiRand : vpiNotRand;
    }
    HangIfMade(typespec_member, Of(MemberType(member), member.unpacked_dims,
                                   std::string_view{}, typespec_member));
    HangIfMade(typespec_member,
               member.init_expr == nullptr
                   ? nullptr
                   : VpiInstanceExpression(member.init_expr, at_.design.objects,
                                           at_.prefix, at_.design.ctx, build_));
    typespec->children.push_back(typespec_member);
  }

  const ScopeTypespecs& at_;
  const TypespecsByName& made_;
  const VpiAttachBuild& build_;
};

TypespecsByName MakeTypespecs(const std::vector<ModuleItem*>& items,
                              const ScopeTypespecs& at) {
  TypespecsByName made;
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kTypedef ||
        item->typedef_type.kind == DataTypeKind::kImplicit) {
      continue;
    }
    VpiObject* typespec = TypespecMaker(at, made).Of(
        item->typedef_type, item->unpacked_dims, item->name, at.scope);
    if (typespec == nullptr) continue;
    typespec->full_name = VpiScopedFullName(at.scope, item->name);
    at.scope->children.push_back(typespec);
    made[item->name] = typespec;
  }
  return made;
}

using InstanceDeclVisit =
    std::function<void(const RtlirModule& mod, const std::string& prefix,
                       VpiObject* instance, const ModuleDecl& decl)>;

void WalkInstanceDecls(const RtlirDesign* design, const VpiObjectMap& objects,
                       SimContext& ctx, InstanceDefinitions& definitions,
                       const InstanceDeclVisit& visit) {
  WalkInstanceObjects(design, objects,
                      [&](const RtlirModule* mod, const std::string& prefix,
                          VpiObject* instance) {
                        definitions[instance] = mod->decl;
                        if (mod->decl == nullptr) return;
                        InstancePrefixOverride in_instance(
                            ctx.InstancePrefixOverride(),
                            prefix.empty() ? "" : prefix + ".");
                        visit(*mod, prefix, instance, *mod->decl);
                      });
}

VpiObject* DeclaredTypespec(const DataType* written,
                            const TypespecsByName& local,
                            const TypespecsByName& unit) {
  if (written == nullptr || written->kind != DataTypeKind::kNamed) {
    return nullptr;
  }
  for (const TypespecsByName* scope : {&local, &unit}) {
    auto it = scope->find(written->type_name);
    if (it != scope->end()) return it->second;
  }
  return nullptr;
}

struct InstanceTypespecs {
  const TypespecsByName& local;
  const TypespecsByName& unit;
  const VpiObjectMap& objects;
  const ScopeTypespecs& at;

  void Relate(std::string_view name, const DataType* written,
              const std::vector<Expr*>* dims) const {
    VpiObject* typespec = DeclaredTypespec(written, local, unit);
    VpiObject* obj =
        FindObjectForFlatName(objects, VpiFlatName(at.prefix, name));
    if (obj == nullptr || written == nullptr) return;
    TypespecMaker maker(at, local);
    const bool kNet =
        VpiIsNetsType(obj->type) && !VpiIsInterconnectSubelementType(obj->type);
    const bool kTyped = kNet || VpiIsVariablesType(obj->type) ||
                        obj->type == vpiNamedEvent ||
                        obj->type == vpiNamedEventArray;
    if ((written->kind != DataTypeKind::kNamed || kNet) && kTyped) {
      static const std::vector<Expr*> kNoDims;
      typespec = maker.Of(*written, dims != nullptr ? *dims : kNoDims,
                          std::string_view{}, obj);
    } else if (typespec != nullptr && dims != nullptr) {
      typespec =
          at.design.shapes.Unnamed(obj, maker.DimsOf({}, *dims), typespec);
    }
    if (typespec != nullptr) obj->children.push_back(typespec);
  }
};

void RelateVariableTypespecs(const RtlirModule& mod,
                             const InstanceTypespecs& at) {
  for (const RtlirVariable& var : VpiDeclaredVariables(mod)) {
    at.Relate(var.name, var.written_type, var.declared_unpacked_dims);
  }
  for (const RtlirNet& net : VpiDeclaredNets(mod)) {
    at.Relate(net.name, net.written_type, net.declared_unpacked_dims);
  }
}

VpiObject* ExprPortTypespec(const RtlirPort& port, const ModuleDecl& decl,
                            TypespecMaker& maker, VpiObject* object) {
  if (port.port_expr->kind == ExprKind::kIdentifier) {
    for (const PortDecl& named : decl.port_expr_objects) {
      if (named.name != port.port_expr->text) continue;
      return maker.Of(named.data_type, named.unpacked_dims, std::string_view{},
                      object);
    }
  }
  DataType vector;
  vector.kind = port.type_kind == DataTypeKind::kBit ? DataTypeKind::kBit
                                                     : DataTypeKind::kLogic;
  vector.is_signed = port.is_signed;
  std::vector<VpiTypespecDim> dims;
  if (port.width > 1) {
    dims.push_back({false, PackedRange::Implicit(port.width), 0, nullptr});
  }
  return maker.Shaped(vector, dims, std::string_view{}, object);
}

void RelatePortTypespecs(const RtlirModule& mod, const ModuleDecl& decl,
                         const ScopeTypespecs& at) {
  TypespecsByName local;
  std::unordered_map<const DataType*, VpiObject*> ports;
  std::vector<VpiObject*> expr_ports;
  for (VpiObject* child : at.scope->children) {
    if (child->type == vpiTypeParameter) {
      local[child->name] = child->param_typespec;
    } else if (VpiIsTypespecType(child->type)) {
      local[child->name] = child;
    } else if (child->type == vpiPort) {
      const RtlirPort& port = mod.ports[child->index];
      if (port.port_expr != nullptr) {
        expr_ports.push_back(child);
      } else if (!port.is_interface_port) {
        ports[port.declared_type] = child;
      }
    }
  }
  TypespecMaker maker(at, local);
  for (const PortDecl& written : decl.ports) {
    auto it = ports.find(&written.data_type);
    if (it == ports.end()) continue;
    HangIfMade(it->second, maker.Of(written.data_type, written.unpacked_dims,
                                    std::string_view{}, it->second));
  }
  for (VpiObject* object : expr_ports) {
    HangIfMade(object,
               ExprPortTypespec(mod.ports[object->index], decl, maker, object));
  }
}

TypespecsByName AnswerPackageTypespecs(const PackageDecl& pkg,
                                       const VpiObjectMap& objects,
                                       const DesignTypespecs& design,
                                       VpiObjectMap& answered) {
  const TypespecsByName kNone;
  const std::vector<RtlirImport> kNoImports;
  const std::string kPrefix(pkg.name);
  const TypespecsByName kPackage = MakeTypespecs(
      pkg.items, {FindObjectForFlatName(objects, pkg.name), kPrefix, nullptr,
                  answered, kNoImports, design});
  for (const auto& [name, typespec] : kPackage) {
    answered[design.build.keep(std::string(pkg.name) +
                               "::" + std::string(name))] = typespec;
  }
  return kPackage;
}

using GenScopeTypespecs = std::unordered_map<const VpiObject*, TypespecsByName>;

struct BlockClassTypedefs {
  std::string prefix;
  TypespecsByName typedefs;
};

using ClassTypedefs =
    std::map<VpiClassDefnObjects::key_type, BlockClassTypedefs>;

GenScopeTypespecs MakeGenBlockTypespecs(const RtlirModule& mod,
                                        VpiObject* instance,
                                        const std::string& prefix,
                                        const DesignTypespecs& design,
                                        const VpiObjectMap& answered) {
  GenScopeTypespecs made;
  for (const RtlirGenBlockTypedef& declared : mod.gen_block_typedefs) {
    VpiObject* scope = VpiGenScopeOf(instance, declared.gen_block_path);
    const TypespecsByName kMade = MakeTypespecs(
        {declared.item},
        {scope, prefix, &mod.enum_types, answered, mod.imports, design});
    made[scope].insert(kMade.begin(), kMade.end());
  }
  return made;
}

TypespecsByName GenBlockTypedefs(VpiObject* instance, const HierPath& path,
                                 const TypespecsByName& local,
                                 const GenScopeTypespecs& gen) {
  TypespecsByName found = local;
  for (std::ptrdiff_t depth = 1; depth <= std::ssize(path); ++depth) {
    const HierPath kOuter(path.begin(), path.begin() + depth);
    const auto kScope = gen.find(VpiGenScopeOf(instance, kOuter));
    if (kScope == gen.end()) continue;
    for (const auto& [name, typespec] : kScope->second) {
      found[name] = typespec;
    }
  }
  return found;
}

const TypespecsByName& ExtendsTypedefs(
    const VpiClassDefnObjects::key_type& key, const ClassTypedefs& in_blocks,
    const std::unordered_map<std::string, TypespecsByName>& declaring,
    const TypespecsByName& none) {
  const auto kInBlock = in_blocks.find(key);
  if (kInBlock != in_blocks.end()) return kInBlock->second.typedefs;
  const auto kDeclaring = declaring.find(key.second);
  return kDeclaring == declaring.end() ? none : kDeclaring->second;
}

std::string RunClassName(const VpiObject* defn) {
  std::string name(defn->name);
  for (const VpiObject* at = defn->parent; at->type == vpiClassDefn;
       at = at->parent) {
    name.insert(0, "::").insert(0, at->name);
  }
  return name;
}

std::unordered_map<std::string_view, std::vector<RtlirEnumMember>> ClassEnums(
    const std::vector<ModuleItem*>& typedefs, const VpiObject* defn,
    const SimContext& ctx) {
  std::unordered_map<std::string_view, std::vector<RtlirEnumMember>> enums;
  const std::string kClass = RunClassName(defn);
  for (const ModuleItem* item : typedefs) {
    const EnumTypeInfo* info =
        ctx.FindEnumType(kClass + "::" + std::string(item->name));
    if (info == nullptr) continue;
    std::vector<RtlirEnumMember>& members = enums[item->name];
    for (const EnumMemberInfo& member : info->members) {
      RtlirEnumMember constant;
      constant.name = member.name;
      constant.value = static_cast<int64_t>(member.value);
      members.push_back(constant);
    }
  }
  return enums;
}

VpiObject& PropertyObject(const VpiObject& defn, std::string_view name) {
  return **std::ranges::find_if(defn.children, [name](const VpiObject* child) {
    const bool kVariable = VpiIsVariablesType(child->type) ||
                           child->type == vpiNamedEvent ||
                           child->type == vpiNamedEventArray;
    return kVariable && child->name == name;
  });
}

bool ReachesATypespec(const VpiObject& obj) {
  return std::ranges::any_of(obj.children, [](const VpiObject* child) {
    return VpiIsTypespecType(child->type);
  });
}

void AssignExtendsNamedTypes(const ClassDecl& decl, const ScopeTypespecs& at,
                             const TypespecsByName& declaring) {
  const VpiObject& defn = *at.scope;
  const auto kExtends =
      std::ranges::find(defn.children, vpiExtends, &VpiObject::type);
  if (kExtends == defn.children.end()) return;
  VpiObject* typespec = (*kExtends)->children.front();
  TypespecMaker maker(at, declaring);
  for (const auto& [key, base] : at.design.classes) {
    if (std::ranges::find(typespec->children, base) ==
        typespec->children.end()) {
      continue;
    }
    VpiAssignExtendsNamedTypes(
        typespec, decl, *key.first,
        [&maker](const DataType& type, VpiObject* assign) {
          return maker.Of(type, {}, std::string_view{}, assign);
        });
  }
}

void MakeClassTypespecs(const ClassDecl& decl, VpiObject* defn,
                        const std::string& prefix,
                        const DesignTypespecs& design,
                        const VpiObjectMap& answered) {
  std::vector<ModuleItem*> typedefs;
  for (const ClassMember* member : decl.members) {
    if (member->kind == ClassMemberKind::kTypedef &&
        !member->typedef_item->is_localparam) {
      typedefs.push_back(member->typedef_item);
    }
  }
  const std::vector<RtlirImport> kNoImports;
  const auto kEnums = ClassEnums(typedefs, defn, design.ctx);
  const ScopeTypespecs kAt{defn, prefix, &kEnums, answered, kNoImports, design};
  const TypespecsByName kMade = MakeTypespecs(typedefs, kAt);
  for (const auto& [name, typespec] : kMade) {
    typespec->full_name = defn->full_name + "::" + std::string(name);
  }
  TypespecMaker maker(kAt, kMade);
  for (const ClassMember* member : decl.members) {
    if (member->kind != ClassMemberKind::kProperty || member->is_param) {
      continue;
    }
    VpiObject& var = PropertyObject(*defn, member->name);
    if (ReachesATypespec(var)) continue;
    if (VpiObject* typespec = maker.Of(member->data_type, member->unpacked_dims,
                                       std::string_view{}, &var)) {
      var.children.push_back(typespec);
    }
  }
}

}  // namespace

VpiObject* VpiKeywordTypespec(const DataType& type, VpiObject* parent,
                              SimContext& ctx, const VpiAttachBuild& build) {
  VpiObject* typespec = build.alloc();
  typespec->type = VpiTypespecKind(type.kind);
  typespec->parent = parent;
  for (const PackedRange& dim : WrittenPackedDims(&type, ctx)) {
    typespec->children.push_back(VpiRangeObject(typespec, dim, build));
  }
  return typespec;
}

VpiObject* VpiImportedTypespec(std::string_view name,
                               const std::vector<RtlirImport>& imports,
                               const VpiObjectMap& answered) {
  for (const RtlirImport& imported : imports) {
    if (!imported.is_wildcard && imported.item_name != name) continue;
    const std::string kKey =
        std::string(imported.package_name) + "::" + std::string(name);
    auto it = answered.find(kKey);
    if (it != answered.end()) return it->second;
  }
  return nullptr;
}

VpiObjectMap AttachTypespecs(const RtlirDesign* design,
                             const VpiObjectMap& objects,
                             const VpiClassDefnObjects& classes,
                             SimContext& ctx, const VpiAttachBuild& build) {
  if (design->compilation_unit == nullptr) return {};
  const CompilationUnit& unit = *design->compilation_unit;
  VpiTypespecShapes shapes(build);
  InstanceDefinitions definitions;
  const DesignTypespecs kDesign{build,   ctx,  shapes,     classes,
                                objects, unit, definitions};
  const TypespecsByName kNone;
  const std::vector<RtlirImport> kNoImports;
  const std::string kUnitPrefix("$unit");
  InstancePrefixOverride unprefixed(ctx.InstancePrefixOverride(), "");
  TypespecsByName unit_typedefs;
  for (const VpiUnitScope& at : VpiUnitScopes(*design, objects)) {
    const TypespecsByName kOwn = MakeTypespecs(
        at.unit->cu_items,
        {at.scope, kUnitPrefix, nullptr, kNone, kNoImports, kDesign});
    unit_typedefs.insert(kOwn.begin(), kOwn.end());
  }
  VpiObjectMap answered(unit_typedefs.begin(), unit_typedefs.end());
  std::unordered_map<std::string, TypespecsByName> declaring;
  ClassTypedefs in_blocks;
  for (const PackageDecl* pkg : design->packages) {
    declaring.emplace(std::string(pkg->name),
                      AnswerPackageTypespecs(*pkg, objects, kDesign, answered));
  }
  WalkInstanceDecls(
      design, objects, ctx, definitions,
      [&](const RtlirModule& mod, const std::string& prefix, VpiObject* scope,
          const ModuleDecl& decl) {
        const ScopeTypespecs kAt{scope,    prefix,      &mod.enum_types,
                                 answered, mod.imports, kDesign};
        const TypespecsByName kLocal = MakeTypespecs(decl.items, kAt);
        declaring.emplace(prefix, kLocal);
        const GenScopeTypespecs kGen =
            MakeGenBlockTypespecs(mod, scope, prefix, kDesign, answered);
        for (const RtlirGenBlockClass& declared : mod.gen_block_classes) {
          const HierPath& path = declared.gen_block_path;
          in_blocks[{declared.decl, VpiGenScopeOf(scope, path)->full_name}] = {
              prefix, GenBlockTypedefs(scope, path, kLocal, kGen)};
        }
        RelateVariableTypespecs(mod, {kLocal, unit_typedefs, objects, kAt});
      });
  for (const auto& [key, defn] : classes) {
    const auto kInBlock = in_blocks.find(key);
    const std::string& prefix =
        kInBlock == in_blocks.end() ? key.second : kInBlock->second.prefix;
    MakeClassTypespecs(*key.first, defn, prefix, kDesign, answered);
    AssignExtendsNamedTypes(
        *key.first, {defn, prefix, nullptr, answered, kNoImports, kDesign},
        ExtendsTypedefs(key, in_blocks, declaring, kNone));
  }
  return answered;
}

void AttachPortTypespecs(const RtlirDesign* design, const VpiObjectMap& objects,
                         const VpiCallObjects& calls, SimContext& ctx,
                         const VpiAttachBuild& build) {
  VpiTypespecShapes shapes(build);
  InstanceDefinitions definitions;
  const DesignTypespecs kDesign{build,      ctx,
                                shapes,     calls.classes,
                                objects,    *design->compilation_unit,
                                definitions};
  WalkInstanceDecls(design, objects, ctx, definitions,
                    [&](const RtlirModule& mod, const std::string& prefix,
                        VpiObject* instance, const ModuleDecl& decl) {
                      RelatePortTypespecs(
                          mod, decl,
                          {instance, prefix, &mod.enum_types,
                           calls.unit_typespecs, mod.imports, kDesign});
                    });
}

}  // namespace delta
