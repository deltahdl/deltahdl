#include "simulator/vpi_design_attach_typespecs.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
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
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_typespec_shapes.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// The typespecs one scope declares, by typedef name.
using TypespecsByName = std::unordered_map<std::string_view, VpiObject*>;

// What making typespecs reads across the whole design: the model to build in,
// the run whose scope a dimension is evaluated in, the shapes of the
// typespecs made so far, which a type written over one of them unwinds
// through (§37.25 detail 8), the class defns a class type names (§37.32), and
// the objects an expression a member's default value writes names.
struct DesignTypespecs {
  const VpiAttachBuild& build;
  SimContext& ctx;
  VpiTypespecShapes& shapes;
  const VpiClassDefnObjects& classes;
  const VpiObjectMap& objects;
};

// What making one scope's typespecs reads: the scope object they hang from,
// the key its class defns and its expressions are found under, an instance's
// path, a package's name or "$unit", the enumerations the run resolved under
// each typedef name, and, for a typedef of the scope to alias, the typespecs
// answered beyond it, the compilation unit's by name and the packages' as
// pkg::name, and the scope's imports, through which a package's are visible
// (§26.3).
struct ScopeTypespecs {
  VpiObject* scope;
  const std::string& prefix;
  const std::unordered_map<std::string_view, std::vector<RtlirEnumMember>>*
      enums;
  const TypespecsByName& outer;
  const std::vector<RtlirImport>& imports;
  const DesignTypespecs& design;
};

// Hangs `child` from `holder` where one was made.
void HangIfMade(VpiObject* holder, VpiObject* child) {
  if (child != nullptr) holder->children.push_back(child);
}

// §37.25: an enum const of `typespec`, named after the member and holding its
// value.
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

// §7.2: the type a member of a structure or union was declared with: the
// whole of an aggregate or enumeration written in place, and otherwise the
// keyword or name with the packed dimensions it was written with.
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

// §37.25 detail 8: the type `type`'s dimensions are written over, the type
// without its packed dimensions; for an enumeration, without those written
// after its body, the one in its base type staying with it.
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

// The typespec a named type finds, and whether it is one a typedef declares,
// which a typedef of it aliases (§37.25 detail 1), rather than a class
// typespec of the class it names.
struct NamedTypespec {
  VpiObject* typespec = nullptr;
  bool declared = false;
};

// Makes the typespecs of the types written in one scope, the scope's typedefs
// made before the one being made, `made`, among those a name finds.
class TypespecMaker {
 public:
  TypespecMaker(const ScopeTypespecs& at, const TypespecsByName& made)
      : at_(at), made_(made), build_(at.design.build) {}

  // §37.25: the typespec of `type` written with the unpacked dimensions
  // `unpacked`, named `name`, an empty one for a type no typedef declares,
  // and hung from `parent`: where nothing is written over a named type, its
  // typespec, or an alias of it reaching it through vpiTypedefAlias for a
  // typedef (detail 1); where dimensions are, the typespec they make over the
  // type's (detail 8); and otherwise one of the type's own kind. Null for a
  // type it draws no typespec for.
  VpiObject* Of(const DataType& type, const std::vector<Expr*>& unpacked,
                std::string_view name, VpiObject* parent) {
    return Shaped(type, DimsOf(type, unpacked), name, parent);
  }

  // As Of, with the dimensions written over `type` already drawn as `dims`,
  // outermost first.
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

  // §37.25 detail 10: the dimensions of a type written with the unpacked
  // dimensions `unpacked` over the packed ones of `type`, outermost first; an
  // enumeration's packed dimensions are those written after its body (§7.4.1),
  // the one written in its base type being the base type's.
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
  // A typespec named `name`, hung from `parent`, of a kind its maker sets;
  // one of no name reports none through vpiName (§37.25 detail 1).
  VpiObject* Alloc(std::string_view name, VpiObject* parent) const {
    VpiObject* typespec = build_.alloc();
    typespec->name =
        name.empty() ? std::string_view{} : build_.keep(std::string(name));
    typespec->parent = parent;
    return typespec;
  }

  // §7.4: an unpacked dimension, the kind of array it makes (§37.17 detail
  // 21) and, for an associative one, the typespec of its index type.
  VpiTypespecDim UnpackedDim(const Expr* dim) {
    VpiTypespecDim made = VpiUnpackedTypespecDim(dim, at_.design.ctx);
    if (made.array_type == vpiAssocArray) {
      made.index_typespec = IndexTypespec(dim->text);
    }
    return made;
  }

  // §37.25 detail 2 with §7.8: the typespec of the index type an associative
  // dimension writes as `written`, a keyword's own or the one the name finds;
  // none for the wildcard.
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

  // §37.25 detail 1 and §26.3: the typespec the typedef a named type names
  // declares: one written through its package, pk::t, among the packages',
  // and otherwise one of the scope's before it, the compilation unit's or a
  // package's an import makes visible. Where no typedef is so named, §37.32:
  // a class typespec named `name`, or after the class where that is empty,
  // hung from `parent` and reaching the class defn the name finds; none where
  // it finds none.
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

  // §37.25: a typespec of the kind `type` is, with nothing written over it,
  // named `name` and hung from `parent`: an enumeration's with its constants,
  // those of the typedef `typedef_name`, and its base type's typespec, a
  // structure's or union's with its members, and a predefined type's named by
  // a typedef standing as an alias of that type's own (detail 6). Null for a
  // type it draws no typespec for.
  VpiObject* Own(const DataType& type, std::string_view name, VpiObject* parent,
                 std::string_view typedef_name) {
    const int kKind = VpiTypespecKind(type.kind);
    if (kKind == 0) return nullptr;
    VpiObject* typespec = Alloc(name, parent);
    typespec->type = kKind;
    if (kKind == vpiEnumTypespec) {
      FillEnum(typespec, type, typedef_name);
    } else if (kKind == vpiStructTypespec || kKind == vpiUnionTypespec) {
      FillAggregate(typespec, type);
    } else if (!name.empty()) {
      typespec->aliased =
          Own(type, std::string_view{}, typespec, std::string_view{});
    }
    return typespec;
  }

  // §37.25: an enum typespec's constants, those the run resolved under the
  // name of the typedef `typedef_name` that writes the enumeration, itself or
  // as the element of its dimensions (detail 8), and its base type's
  // typespec, which vpiBaseTypespec reaches: the one its base names, its
  // keyword's with the packed dimensions it was written with, or int's where
  // it names none (§6.19).
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

  // §37.25 and §37.26: a struct or union typespec's vpiPacked, vpiTagged and
  // vpiSoft, and a typespec member per member, in declaration order.
  void FillAggregate(VpiObject* typespec, const DataType& type) {
    typespec->packed = type.is_packed;
    typespec->tagged = type.is_tagged;
    typespec->soft = type.is_soft;
    for (const StructMember& member : type.struct_members) {
      MakeTypespecMember(typespec, member);
    }
  }

  // §37.25 details 3, 4 and 7: a typespec member of `typespec`, named after
  // the member, reaching the typespec of the member's type, the default
  // value it was declared with through vpiExpr, and saying through
  // vpiRandType whether it is rand or randc.
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

// §37.25 and §37.26: the typespecs of the typedefs among `items`, each named
// after its typedef and hung from `at.scope`, which reaches it through
// vpiTypedef; none for a type it draws no typespec for here.
TypespecsByName MakeTypespecs(const std::vector<ModuleItem*>& items,
                              const ScopeTypespecs& at) {
  TypespecsByName made;
  for (const ModuleItem* item : items) {
    // §6.18: a forward typedef, whose type is left implicit, names a type the
    // class or the typedef resolving it defines, and draws no typespec of its
    // own.
    if (item->kind != ModuleItemKind::kTypedef ||
        item->typedef_type.kind == DataTypeKind::kImplicit) {
      continue;
    }
    VpiObject* typespec = TypespecMaker(at, made).Of(
        item->typedef_type, item->unpacked_dims, item->name, at.scope);
    if (typespec == nullptr) continue;
    typespec->full_name = at.scope != nullptr
                              ? VpiScopedFullName(at.scope, item->name)
                              : std::string(item->name);
    if (at.scope != nullptr) at.scope->children.push_back(typespec);
    made[item->name] = typespec;
  }
  return made;
}

// The module, interface or program `unit` declares under `name`.
const ModuleDecl* ElementNamed(const CompilationUnit& unit,
                               std::string_view name) {
  for (const auto* list : {&unit.modules, &unit.interfaces, &unit.programs}) {
    for (const ModuleDecl* decl : *list) {
      if (decl->name == name) return decl;
    }
  }
  return nullptr;
}

// One instance of `mod` at `prefix`: its object and the module, interface or
// program the compilation unit declares it from.
using InstanceDeclVisit =
    std::function<void(const RtlirModule& mod, const std::string& prefix,
                       VpiObject* instance, const ModuleDecl& decl)>;

// Visits each instance of the design whose module, interface or program
// `unit` declares, `ctx`'s instance prefix set to the instance's own so that
// the dimensions its declarations write evaluate there.
void WalkInstanceDecls(const RtlirDesign* design, const CompilationUnit& unit,
                       const VpiObjectMap& objects, SimContext& ctx,
                       const InstanceDeclVisit& visit) {
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        VpiObject* instance = FindObjectForFlatName(
            objects, prefix.empty() ? std::string(mod->name) : prefix);
        const ModuleDecl* decl = ElementNamed(unit, mod->name);
        if (decl == nullptr) return;
        InstancePrefixOverride in_instance(ctx.InstancePrefixOverride(),
                                           prefix.empty() ? "" : prefix + ".");
        visit(*mod, prefix, instance, *decl);
      });
}

// §37.17: the typespec of the typedef a variable declared with the type
// `written` was declared with, its own scope's or else the compilation unit's;
// null where its type names no typedef either declares.
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

// Whether the module `mod`'s variables list holds a variable named `name`.
bool HasVariable(const RtlirModule& mod, std::string_view name) {
  return std::ranges::any_of(mod.variables, [name](const RtlirVariable& var) {
    return var.name == name;
  });
}

// Where the variables of one instance find their typespecs: the typedefs of
// its module and of the compilation unit, by name, the instance's objects,
// keyed under `at.prefix` in `objects`, and what makes a typespec of the
// dimensions a variable writes over its typedef.
struct InstanceTypespecs {
  const TypespecsByName& local;
  const TypespecsByName& unit;
  const VpiObjectMap& objects;
  const ScopeTypespecs& at;

  // §37.17: relates the variable `name` of the instance, declared with the
  // type `written` and the unpacked dimensions `dims`, to the typespec of the
  // typedef that type names, if any, or, where it writes unpacked dimensions
  // of its own, to an unnamed array typespec of them over that one (§37.25
  // detail 8).
  void Relate(std::string_view name, const DataType* written,
              const std::vector<Expr*>* dims) const {
    VpiObject* typespec = DeclaredTypespec(written, local, unit);
    VpiObject* obj =
        FindObjectForFlatName(objects, VpiFlatName(at.prefix, name));
    if (typespec == nullptr || obj == nullptr) return;
    if (dims != nullptr) {
      TypespecMaker maker(at, local);
      typespec =
          at.design.shapes.Unnamed(obj, maker.DimsOf({}, *dims), typespec);
    }
    obj->children.push_back(typespec);
  }
};

// §37.17: relates each variable of an instance of `mod` to its typespec: each
// the module's variables list holds, and each variable port it does not.
// §23.2.2.3 has a variable port declare a variable, which the list holds where
// the port is of a structure or union type or the body declares it again; any
// other relates to the type the port's declaration wrote.
void RelateVariableTypespecs(const RtlirModule& mod,
                             const InstanceTypespecs& at) {
  for (const RtlirVariable& var : mod.variables) {
    at.Relate(var.name, var.written_type, var.declared_unpacked_dims);
  }
  for (const RtlirPort& port : mod.ports) {
    if (port.is_var && !HasVariable(mod, port.name)) {
      at.Relate(port.name, port.declared_type, nullptr);
    }
  }
}

// §37.14 (figure) with §23.2.2.1 and §23.2.2.2: the typespec of `port`, of
// the module `decl` declares, written as an expression, made by `maker` and
// hung from the port's object `object`. Where the expression is the name of an
// object a body port declaration declares, it is the type that declaration
// wrote; otherwise a vector of the expression's width and signedness, bit
// where the port's type is bit and logic otherwise (§11.5.1, §11.4.12), one of
// no range for a single bit.
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

// §37.14 (figure): relates each port of `at.scope`, an instance of `mod`, the
// module `decl` declares, to the typespec of the type its declaration wrote
// with the unpacked dimensions it wrote, found among the typedefs the instance
// declares, a type parameter's name standing for the type it has there, and
// those beyond it `at` holds; and a port written as an expression to the
// typespec ExprPortTypespec makes for it. A port of an interface has no
// declaration of its own to read a type from.
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

// §37.10 detail 1: a package is an instance too, whose typedefs are its
// typespecs, answered in `answered` under the package's name and "::" for a
// scope that imports them (§26.3) to reach.
void AnswerPackageTypespecs(const PackageDecl& pkg, const VpiObjectMap& objects,
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
}

// §37.85 detail 5: the typedefs a generate block instance of `mod`, whose
// instance object is `instance`, declares are typespecs of the instance's gen
// scope, which AttachGenScopes made.
void MakeGenBlockTypespecs(const RtlirModule& mod, VpiObject* instance,
                           const std::string& prefix,
                           const DesignTypespecs& design,
                           const VpiObjectMap& answered) {
  for (const RtlirGenBlockTypedef& declared : mod.gen_block_typedefs) {
    MakeTypespecs({declared.item},
                  {VpiGenScopeOf(instance, declared.gen_block_path), prefix,
                   &mod.enum_types, answered, mod.imports, design});
  }
}

// §8.23: the name the run registers the class of `defn` under, a nested
// class's through the classes holding it, as "Outer::Inner".
std::string RunClassName(const VpiObject* defn) {
  std::string name(defn->name);
  for (const VpiObject* at = defn->parent;
       at != nullptr && at->type == vpiClassDefn; at = at->parent) {
    name.insert(0, "::").insert(0, at->name);
  }
  return name;
}

// §6.19 with §8.23: the members of each enumeration a typedef among
// `typedefs` of the class of `defn` writes, under the typedef's name, as the
// run resolved them under "Class::name" when it lowered the class.
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

// §37.31: the typedefs the class `decl` declares are typespecs its class defn
// `defn` reaches through vpiTypedef, full-named through the class as its
// methods are (§37.41 detail 5), an enumeration's with its constants, and
// found under `prefix`, the key of the scope declaring the class. A body's
// `localparam type`, which the parser carries as a typedef, is a parameter of
// the class (detail 7) instead.
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
  const TypespecsByName kMade = MakeTypespecs(
      typedefs, {defn, prefix, &kEnums, answered, kNoImports, design});
  for (const auto& [name, typespec] : kMade) {
    typespec->full_name = defn->full_name + "::" + std::string(name);
  }
}

}  // namespace

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
  // §37.25, §37.26 and §37.85 detail 5: each typedef a scope declares is a
  // typespec named after it, an enum's with its constants and a struct's or
  // union's with its members; and §37.17 relates a variable declared with one
  // to it. No typespec of any kind was made, so vpiTypedef reached none and a
  // variable's vpiTypespec was null.
  if (design->compilation_unit == nullptr) return {};
  const CompilationUnit& unit = *design->compilation_unit;
  VpiTypespecShapes shapes(build);
  const DesignTypespecs kDesign{build, ctx, shapes, classes, objects};
  auto unit_scope = objects.find("$unit");
  const TypespecsByName kNone;
  const std::vector<RtlirImport> kNoImports;
  const std::string kUnitPrefix("$unit");
  InstancePrefixOverride unprefixed(ctx.InstancePrefixOverride(), "");
  const TypespecsByName kUnit =
      MakeTypespecs(unit.cu_items,
                    {unit_scope == objects.end() ? nullptr : unit_scope->second,
                     kUnitPrefix, nullptr, kNone, kNoImports, kDesign});
  VpiObjectMap answered(kUnit.begin(), kUnit.end());
  for (const PackageDecl* pkg : design->packages) {
    AnswerPackageTypespecs(*pkg, objects, kDesign, answered);
  }
  WalkInstanceDecls(
      design, unit, objects, ctx,
      [&](const RtlirModule& mod, const std::string& prefix, VpiObject* scope,
          const ModuleDecl& decl) {
        const ScopeTypespecs kAt{scope,    prefix,      &mod.enum_types,
                                 answered, mod.imports, kDesign};
        const TypespecsByName kLocal = MakeTypespecs(decl.items, kAt);
        MakeGenBlockTypespecs(mod, scope, prefix, kDesign, answered);
        RelateVariableTypespecs(mod, {kLocal, kUnit, objects, kAt});
      });
  for (const auto& [key, defn] : classes) {
    MakeClassTypespecs(*key.first, defn, key.second, kDesign, answered);
  }
  return answered;
}

void AttachPortTypespecs(const RtlirDesign* design, const VpiObjectMap& objects,
                         const VpiCallObjects& calls, SimContext& ctx,
                         const VpiAttachBuild& build) {
  // §37.14 (figure): a port reaches the typespec of its type through
  // vpiTypespec, which reached nothing for every port.
  VpiTypespecShapes shapes(build);
  const DesignTypespecs kDesign{build, ctx, shapes, calls.classes, objects};
  WalkInstanceDecls(design, *design->compilation_unit, objects, ctx,
                    [&](const RtlirModule& mod, const std::string& prefix,
                        VpiObject* instance, const ModuleDecl& decl) {
                      RelatePortTypespecs(
                          mod, decl,
                          {instance, prefix, &mod.enum_types,
                           calls.unit_typespecs, mod.imports, kDesign});
                    });
}

}  // namespace delta
