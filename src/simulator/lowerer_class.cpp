#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/class_typedef_layout.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_class_params.h"
#include "simulator/eval_class_scope_types.h"
#include "simulator/eval_class_sync.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"

namespace delta {

// §8.20: the method a virtual call through this class reaches. Taken from
// info->methods rather than from the member, because §8.24 lets the member be
// an `extern` prototype whose body stands outside the class, and by the time
// the vtable is built AttachScopeMethodBodies has put that body in the map;
// a class derived later copies the entry with the body in it.
static ModuleItem* VTableMethodOf(const ClassTypeInfo* info,
                                  const ClassMember* member) {
  if (member->is_pure_virtual) return nullptr;
  auto it = info->methods.find(std::string(member->method->name));
  return it == info->methods.end() ? member->method : it->second;
}

static void AddOrUpdateVTableEntry(ClassTypeInfo* info,
                                   const ClassMember* member) {
  int idx = info->FindVTableIndex(member->method->name);
  auto* method_ptr = VTableMethodOf(info, member);
  if (idx >= 0) {
    info->vtable[static_cast<size_t>(idx)].method = method_ptr;
    info->vtable[static_cast<size_t>(idx)].owner = info;
  } else {
    info->vtable.push_back({member->method->name, method_ptr, info});
  }
}

static bool VTableHasMethodName(const ClassTypeInfo* info,
                                std::string_view method_name) {
  for (const auto& existing : info->vtable) {
    if (existing.method_name == method_name) return true;
  }
  return false;
}

static void MergeInterfaceVTableEntries(ClassTypeInfo* info,
                                        const ClassTypeInfo* iface) {
  for (const auto& entry : iface->vtable) {
    if (!VTableHasMethodName(info, entry.method_name))
      info->vtable.push_back(entry);
  }
}

static void MergeInterfaceVTables(ClassTypeInfo* info) {
  for (const auto* iface : info->extended_interfaces) {
    if (!iface) continue;
    MergeInterfaceVTableEntries(info, iface);
  }
}

static bool MemberContributesToVTable(ClassTypeInfo* info,
                                      const ClassMember* member) {
  // A method that redeclares an inherited virtual entry overrides it and
  // stays virtual even when the 'virtual' keyword is omitted (8.20). A
  // ':initial' method is excluded: it explicitly does not act as a virtual
  // override, so it never updates an inherited slot.
  bool overrides_inherited_virtual =
      !member->method->is_method_initial &&
      info->FindVTableIndex(member->method->name) >= 0;
  return member->is_virtual || member->is_pure_virtual ||
         member->method->is_method_extends || overrides_inherited_virtual;
}

static void BuildVTable(ClassTypeInfo* info, const ClassDecl* cls) {
  if (info->parent) info->vtable = info->parent->vtable;
  MergeInterfaceVTables(info);
  for (auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kMethod || !member->method) continue;
    if (!MemberContributesToVTable(info, member)) continue;
    AddOrUpdateVTableEntry(info, member);
  }
}

// §8.25 with §7.4 and §7.5: the elements of the static array property
// `name` and a dynamic one's count, held under keys of their own beside the
// property's name (ClassArrayElementKey, ClassArraySizeKey), are dropped, so
// a specialization copied from the generic class starts with none of the
// generic's elements; an element not yet written reads its default.
static void ClearStaticArrayElements(ClassTypeInfo* info,
                                     std::string_view name) {
  std::string element_prefix = std::string(name) + "[";
  std::string size_key = ClassArraySizeKey(name);
  std::erase_if(info->static_properties, [&](const auto& entry) {
    return entry.first == size_key || entry.first.starts_with(element_prefix);
  });
}

// §8.9 (printed page 186 of IEEE 1800-2023): each static property's one
// copy is created as the class is built, at its zero default, so that an object
// constructed by a declaration of the same scope before the initializers run
// (Lowerer::LowerModule lowers a module's variables between
// RegisterClassDecl and InitClassStaticProperties) reads and writes the
// class's copy rather than finding none; ClassObject::SetProperty writes the
// object's own slot for a static its type holds no entry for.
// §8.9 with §6.8 (Table 6-7): a static property's one copy takes its type's
// default as an instance property does when it is constructed
// (InitClassPropertyDefault in eval_class_new.cpp) -- 'x for a 4-state type,
// 0 for a 2-state one -- until its initializer, if any, runs
// (InitStaticProperty). Filled with 0 whatever the type, `static logic sl`
// read 0 while the class's `logic l` read x.
static void CreateStaticProperties(ClassTypeInfo* info, Arena& arena) {
  for (const auto& p : info->properties) {
    if (!p.is_static) continue;
    info->static_properties[std::string(p.name)] =
        p.is_4state ? MakeAllX(arena, p.width)
                    : MakeLogic4VecVal(arena, p.width, 0);
    if (p.IsArray() || !p.dim_sizes.empty())
      ClearStaticArrayElements(info, p.name);
  }
}

// §8.9 with §7.4 and §7.5: a static fixed-size or dynamic array property holds
// its elements in the class's static map under their element keys, so an
// assignment-pattern initializer is stored item by item there
// (StoreClassArrayPattern), as an instance property's is on the object
// (TryInitClassArrayPattern in eval_class_new.cpp). Evaluated as one value
// and stored under the property's name, which holds no element, the pattern
// left every element 0 and a dynamic one empty.
static bool TryInitStaticArrayPattern(ClassTypeInfo* info,
                                      const ClassTypeInfo::PropertyInfo& p,
                                      SimContext& ctx, Arena& arena) {
  if (p.init_expr->kind != ExprKind::kAssignmentPattern || !p.IsArray() ||
      p.dim_sizes.size() >= 2) {
    return false;
  }
  ClassArrayRef ref;
  ref.prop = &p;
  ref.static_owner = info;
  ref.size = p.array_size;
  ref.lo = p.is_dynamic ? 0 : p.array_lo;
  return StoreClassArrayPattern(ref, p.init_expr, ctx, arena);
}

// §8.9 (printed page 186) with §6.21 (printed 132-133): each static
// property's one copy takes its initializer once, here, in the frame
// Lowerer::InitClassStaticProperties pushes for the class's scope, after the
// scope's own variables exist; a property with no initializer keeps the
// default CreateStaticProperties gave it, or what a constructor run before
// this wrote. §15.3.1 (printed 373) and §15.4.1 (printed 374): a `static
// semaphore s = new(K)` or `static mailbox mb = new(K)` builds the class's
// bucket or queue into its static map (TryInitStaticSyncProperty), which
// stores the handle's carrier under the name, nonzero for a copy that holds
// an object (§8.4, printed 181-182); evaluated as a value, the `new` built
// nothing and the copy was built on the first reference, reading K as it
// then stood. Evaluated as the class was built, `module top; int K = 3;
// class C; static int s = K;` read K before LowerVar had given it 3. The
// value is stored as an assignment to the property stores it
// (CoerceToPropertyType): §6.12.1 rounds a real into an integral property, so
// `static int t = 3.6` holds 4 as the instance property `int p = 3.6` does;
// stored as evaluated, the static held the real's pattern and read 3.
static void InitStaticProperty(ClassTypeInfo* info,
                               const ClassTypeInfo::PropertyInfo& p,
                               SimContext& ctx, Arena& arena) {
  if (TryInitStaticSyncProperty(info, p.name, p.init_expr, ctx)) return;
  if (p.init_expr == nullptr) return;
  if (TryInitStaticArrayPattern(info, p, ctx, arena)) return;
  if (p.init_expr->kind == ExprKind::kCall && p.init_expr->text == "new") {
    // §8.7: a bare `new` names no class of its own; the property's declared
    // class is the one constructed, `static C inst = new;` an object of C.
    // Evaluated as a value, it constructed nothing and left the handle null.
    std::string_view cls = PropertyClassName(nullptr, info, p.name, ctx);
    if (!cls.empty()) {
      info->static_properties[std::string(p.name)] =
          EvalClassNew(cls, p.init_expr, ctx, arena, p.init_expr->range.start);
      return;
    }
  }
  info->static_properties[std::string(p.name)] = CoerceToPropertyType(
      info, p.name, EvalExpr(p.init_expr, ctx, arena), arena);
}

// The static initializers of `info` and, §8.23, of every class nested in it,
// which LowerNestedClass registered under "Outer::Inner"; run in the frame
// the caller pushed, where a nested class's were run in none before.
static void InitStaticProperties(ClassTypeInfo* info, SimContext& ctx,
                                 Arena& arena) {
  for (const auto& p : info->properties) {
    if (p.is_static) InitStaticProperty(info, p, ctx, arena);
  }
  for (const auto* member : info->decl->members) {
    if (member->kind != ClassMemberKind::kClassDecl || !member->nested_class)
      continue;
    std::string key = std::string(info->name) +
                      "::" + std::string(member->nested_class->name);
    if (ClassTypeInfo* nested = ctx.FindClassType(key))
      InitStaticProperties(nested, ctx, arena);
  }
}

// §8.25 with §8.9: each value parameter of the class `info` bound, in the
// frame its static initializers run in, to the value `info` holds for it --
// a specialization's actual, or the declaration's default for the class
// itself, which §8.25.1 makes the default specialization. Bound for a
// specialization alone, `static int s = N;` under `class P #(int N = 2)`
// held 0 in P#() where it holds 2.
static void BindStaticInitValueParams(const ClassTypeInfo* info,
                                      SimContext& ctx) {
  for (const auto& [pname, pexpr] : info->decl->params) {
    if (info->decl->type_param_names.count(pname) != 0) continue;
    auto entry = info->static_properties.find(std::string(pname));
    if (entry == info->static_properties.end()) continue;
    auto* v = ctx.CreateLocalVariable(pname, entry->second.width);
    v->value = entry->second;
  }
}

// §8.25 (printed page 204) with §8.9 (printed 186): a specialization's static
// properties take their initializers in a frame where that specialization's
// value parameters are bound, so `static const int W = size` holds 4 under
// `V #(4)` and 8 under `V #(8)`. The generic class's copy is evaluated with
// nothing bound -- the class declaration names no actuals -- so the name
// `size` read nothing and the one shared copy held 0 for every
// specialization.
//
// §8.25 also makes the storage the specialization's own from the start: it is
// copied from the generic class (SpecializationOf in class_specialization.cpp)
// with whatever that class's copy holds by then, so each static property is
// first set back to the default CreateStaticProperties gives it. Kept as
// copied, `S #(byte)::n` made after `S s = new;` had run read the count the
// default specialization's constructor had made.
//
// A type parameter is no value, so the frame binds it as the type the
// specialization's actual names (BindStaticInitTypeActuals) rather than as a
// local. With no type bound, `static int w = $bits(T)` held 32 under
// `C #(byte)`.
void InitSpecializationStaticProperties(ClassTypeInfo* spec, SimContext& ctx,
                                        Arena& arena) {
  if (spec == nullptr || spec->decl == nullptr) return;
  CreateStaticProperties(spec, arena);
  if (!spec->package.empty()) ctx.PushScope(spec->package);
  ctx.PushScope();
  BindStaticInitTypeActuals(spec, ctx);
  BindStaticInitValueParams(spec, ctx);
  InitStaticProperties(spec, ctx, arena);
  ctx.PopScope();
  if (!spec->package.empty()) ctx.PopScope();
}

// §6.12: the real family, whose members §6.12.1 converts a value into rather
// than reinterpreting its bits.
static bool IsRealKind(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
}

// §8.24: a default argument value stands in the prototype and may be left out
// of the out-of-block declaration, which otherwise matches it formal for
// formal. The body's formals are what a call binds against once the body has
// replaced the prototype, so each formal the body gives no default takes the
// prototype's; a default the body repeats is the prototype's own, the
// elaborator having required the two to be syntactically identical. §13.5.3
// then has a call omitting the argument evaluate that default.
static void CarryPrototypeDefaults(const ModuleItem* proto, ModuleItem* body) {
  if (proto->func_args.size() != body->func_args.size()) return;
  for (size_t i = 0; i < body->func_args.size(); ++i) {
    if (body->func_args[i].default_value == nullptr)
      body->func_args[i].default_value = proto->func_args[i].default_value;
  }
}

// §8.24: makes `body`, an out-of-block method definition, the method of `cls`
// its name selects, in place of the in-class prototype. The definition repeats
// neither the lifetime nor the static qualifier of the prototype, so the body
// item parses with is_static_method false; the static-ness is carried forward
// from the prototype before the body replaces it, so that a call through the
// class scope resolution operator of §8.23 still resolves it as static, and so
// are the prototype's default argument values.
static void AttachMethodBody(ClassTypeInfo* cls, ModuleItem* body) {
  std::string name(body->name);
  auto existing = cls->methods.find(name);
  if (existing != cls->methods.end()) {
    if (existing->second->is_static_method) body->is_static_method = true;
    CarryPrototypeDefaults(existing->second, body);
  }
  cls->methods[name] = body;
}

// §8.24: an out-of-block declaration stands in the same scope as its class,
// so the bodies of `cls` are the function and task items of `scope_items`,
// the items of the compilation unit, package or module declaring the class,
// whose `C::` prefix names it. Each replaces the prototype CollectClassMembers
// took from the class body.
static void AttachScopeMethodBodies(
    ClassTypeInfo* info, const ClassDecl* cls,
    const std::vector<ModuleItem*>& scope_items) {
  for (auto* item : scope_items) {
    if (item->kind != ModuleItemKind::kFunctionDecl &&
        item->kind != ModuleItemKind::kTaskDecl)
      continue;
    if (item->method_class != cls->name) continue;
    AttachMethodBody(info, item);
  }
}

// The two things a class declaration reads from the scope declaring it: the
// out-of-block method bodies of §8.24, which a compilation unit, package or
// module carries in its items and a class carries none of, and the constants
// of the compilation unit (RtlirDesign::unit_constants), which §3.12.1 has a
// name search reach once the class body itself holds no declaration of the
// name, for any class wherever it is declared.
struct ClassDeclScope {
  const std::vector<ModuleItem*>& items;
  const ScopeMap& constants;
};

// §8.25: the value parameters a property's packed dimension may name, `bit
// [size-1:0] a` in the subclause's `vector #(int size = 1)`, each at the
// default the class declares for it -- the header parameters in order, a
// later default free to name an earlier one, then the parameters and
// localparams of the class body (§6.20.1), which may name the header's. A
// type parameter stands for no value and is left out, as is a default that
// does not fold to a constant. The widths this sizes are those of the default
// specialization (§8.25.1).
//
// The class's own parameters are laid over `constants`, the compilation
// unit's: §6.20.4 lets a localparam be declared at compilation-unit scope and
// §26.3 names a package's parameter through `pkg::`, and §7.4.1 has a packed
// dimension's bounds be constant expressions, so `logic [W-1:0] v` under
// `localparam int W = 10;` outside the class and `logic [p::W-1:0] v` are
// ten bits, as the same dimension on a module's variable already was. Folded
// against the class's parameters alone, neither bound folded, and the
// property fell to the one bit of its base type.
static ScopeMap ClassParamScope(const ClassDecl* cls,
                                const ScopeMap& constants) {
  ScopeMap scope = constants;
  for (const auto& [pname, pexpr] : cls->params) {
    if (pexpr == nullptr || cls->type_param_names.count(pname) != 0) continue;
    if (auto v = ConstEvalInt(pexpr, scope)) scope[pname] = *v;
  }
  for (const auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kProperty || !member->is_param ||
        member->init_expr == nullptr) {
      continue;
    }
    if (auto v = ConstEvalInt(member->init_expr, scope))
      scope[member->name] = *v;
  }
  return scope;
}

// §7.2 with §8.5: the layout of the structure a property's declared type
// names by its typedef name, registered under `key`; null for any other type.
// Sized against no typedef table, the name had no width and the property took
// the 32-bit carrier, which cut an element of an array of such structures to
// 32 bits.
static const StructTypeInfo* StructPropertyLayout(const DataType& type,
                                                  std::string_view key,
                                                  SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty() ||
      type.packed_dim_left != nullptr)
    return nullptr;
  return ctx.FindStructType(key);
}

// §8.23 with §6.18: the key the type a property's declaration names is looked
// up by. A bare name of a structure or union typedef that the property's class
// declares, or one its extends chain declares (§8.13), is a name of that class
// scope, whose layout the design registers under "Class::name", as the
// elaborator's typedef table keys it; it is registered there here where the
// design gave it none. Asked by the bare name, such a property had no layout,
// so a member select of it in a method read 0. A typedef of the property's own
// class with value parameters has the widths its specialization binds (§8.25):
// the default specialization's layout, folded with `params`, stands under
// "Class#()::name", the key a method's local of the type registers
// (MethodClassTypedefLayout), and SizeValueParamProperties gives each other
// specialization its own. A base's typedef of a class with value parameters
// has the widths of the base specialization the class extends
// (ClassTypedefLayoutKey). Any other name keeps the name as written.
static std::string_view PropertyTypeKey(const DataType& type,
                                        const ClassTypeInfo& info,
                                        const ClassDecl& cls,
                                        const ScopeMap& params,
                                        SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty())
    return type.type_name;
  const ClassDecl* decl = nullptr;
  const ClassTypeInfo* owner =
      ClassTypedefDeclarer(type.type_name, info, cls, decl);
  const DataType* aggregate =
      owner != nullptr ? ClassAggregateTypedef(*decl, type.type_name) : nullptr;
  if (aggregate == nullptr) return type.type_name;
  if (ClassHasValueParams(*decl)) {
    if (owner != &info)
      return ClassTypedefLayoutKey(*owner, type.type_name, *aggregate, ctx);
    return RegisterSpecializationTypedefLayout(std::string(info.name) + "#()",
                                               type.type_name, *aggregate,
                                               params, ctx);
  }
  Arena& arena = ctx.GetArena();
  const auto* key = arena.Create<std::string>(
      std::string(owner->name) + "::" + std::string(type.type_name));
  if (ctx.FindStructType(*key) == nullptr)
    RegisterTypeLayout(*key, aggregate, ctx, arena);
  return *key;
}

// §6.11 with §7.2: whether a member of the structure `layout` lays out is of
// a 4-state type, a nested structure's members included. A property of such
// a structure keeps the x and z bits written into it; asked of the typedef
// name against no typedef table, it read 2-state and lost them.
static bool LayoutHas4StateMember(const StructTypeInfo& layout) {
  for (const auto& field : layout.fields) {
    if (field.nested != nullptr ? LayoutHas4StateMember(*field.nested)
                                : Is4stateType(field.type_kind))
      return true;
  }
  return false;
}

// The record of the property `member` declares: its width, folded against
// the class's parameters `params` or taken from the layout a structure's
// typedef name stands for, with the 32-bit carrier for a type neither sizes,
// and the facts of its declaration a write and a read consult.
static ClassTypeInfo::PropertyInfo PropertyRecord(const ClassMember* member,
                                                  const ScopeMap& params,
                                                  std::string_view type_key,
                                                  SimContext& ctx) {
  const DataType& type = member->data_type;
  uint32_t w = EvalTypeWidth(type, {}, params);
  const StructTypeInfo* layout =
      w == 0 ? StructPropertyLayout(type, type_key, ctx) : nullptr;
  if (layout != nullptr) w = layout->total_width;
  bool sized = w != 0;
  bool four_state = layout != nullptr ? LayoutHas4StateMember(*layout)
                                      : Is4stateType(type, {});
  return {member->name,
          sized ? w : 32,
          member->is_static,
          member->is_local,
          member->is_protected,
          member->is_const,
          member->init_expr,
          four_state,
          sized,
          IsRealKind(type.kind),
          type.kind == DataTypeKind::kString,
          IsSignedType(type, {}),
          type_key,
          type.kind == DataTypeKind::kVirtualInterface};
}

static void CollectClassMembers(ClassTypeInfo* info, const ClassDecl* cls,
                                const ScopeMap& constants, SimContext& ctx) {
  ScopeMap params = ClassParamScope(cls, constants);
  for (auto* member : cls->members) {
    if (member->kind == ClassMemberKind::kProperty) {
      info->properties.push_back(PropertyRecord(
          member, params,
          PropertyTypeKey(member->data_type, *info, *cls, params, ctx), ctx));
    } else if (member->kind == ClassMemberKind::kMethod && member->method) {
      std::string name(member->method->name);
      info->methods[name] = member->method;
    }
  }
}

// Gives the property named `name` the unpacked dimension RecordArrayProperties
// read for it.
static void MarkArrayProperty(ClassTypeInfo* info, std::string_view name,
                              const PropertyArrayDim& dim, bool dynamic) {
  for (auto& prop : info->properties) {
    if (prop.name != name) continue;
    prop.array_size = dim.size;
    prop.array_lo = dim.lo;
    prop.array_descending = dim.descending;
    prop.is_dynamic = dynamic;
  }
}

// §7.4.2 with §20.7: gives `prop` the extents of the unpacked dimensions
// `dims` declares where it declares more than one and each folds to a fixed
// one, which is what the array query functions read, and which way each was
// declared, which a foreach walks it by (§12.7.3).
static void FoldMultiDimExtents(const std::vector<Expr*>& dims,
                                const ScopeMap& scope, SimContext& ctx,
                                Arena& arena,
                                ClassTypeInfo::PropertyInfo* prop) {
  if (prop == nullptr) return;
  std::vector<uint32_t> los;
  std::vector<uint32_t> sizes;
  std::vector<bool> descending;
  for (const Expr* dim : dims) {
    PropertyArrayDim folded = FoldPropertyDimension(dim, scope, ctx, arena);
    if (folded.size == 0) return;
    los.push_back(static_cast<uint32_t>(folded.lo));
    sizes.push_back(folded.size);
    descending.push_back(folded.descending);
  }
  prop->dim_los = std::move(los);
  prop->dim_sizes = std::move(sizes);
  prop->dim_descending = std::move(descending);
}

// The property `info` itself declares under `name`, null where it declares
// none.
static ClassTypeInfo::PropertyInfo* OwnProperty(ClassTypeInfo* info,
                                                std::string_view name) {
  for (auto& prop : info->properties) {
    if (prop.name == name) return &prop;
  }
  return nullptr;
}

// §7.4.2/§7.5/§18.5.7: mark each property declared with one fixed or
// dynamic unpacked dimension as the array it is, so the object holds its
// elements one by one and a constraint can iterate over them or reduce them.
// §7.4.4 (printed page 155): the dimension may be the typedef's the property
// is declared through (PropertyTypedefItem), `arr_t a;` under `typedef int
// arr_t[3];`, which left read off the declaration made `a` one element wide.
// §8.25: a dimension naming one of the class's parameters, `int g[N]`, folds
// against the constants `constants` and the parameters' defaults give it.
// A property with more than one unpacked dimension keeps one value, and has
// only its extents recorded.
static void RecordArrayProperties(ClassTypeInfo* info, const ClassDecl* cls,
                                  const ScopeMap& constants, SimContext& ctx,
                                  Arena& arena) {
  ScopeMap scope = ClassParamScope(cls, constants);
  for (const auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kProperty) continue;
    const ModuleItem* item = PropertyTypedefItem(member, info, ctx);
    const std::vector<Expr*>& dims =
        item != nullptr ? item->unpacked_dims : member->unpacked_dims;
    if (dims.size() > 1) {
      FoldMultiDimExtents(dims, scope, ctx, arena,
                          OwnProperty(info, member->name));
    }
    if (dims.size() != 1) continue;
    const bool kDynamic = dims[0] == nullptr;
    PropertyArrayDim dim =
        kDynamic ? PropertyArrayDim{}
                 : FoldPropertyDimension(dims[0], scope, ctx, arena);
    if (dim.size == 0 && !kDynamic) continue;
    MarkArrayProperty(info, member->name, dim, kDynamic);
  }
}

static void StoreClassParam(ClassTypeInfo* info, std::string_view pname,
                            const Logic4Vec& value) {
  info->static_properties[std::string(pname)] = value;
}

// §8.25 with §6.20.2: each default is sized by the parameter's declared type
// (ClassParamSizer), so `logic [W-1:0] INIT = '1` after `int W = 8` holds
// eight bits of ones and not the literal's one bit.
static void InitClassParams(ClassTypeInfo* info, const ClassDecl* cls,
                            SimContext& ctx, Arena& arena) {
  ClassParamSizer sizer(cls);
  // §6.20: parameters supplied through the class's parameter port list.
  for (size_t i = 0; i < cls->params.size(); ++i) {
    const auto& [pname, pexpr] = cls->params[i];
    info->properties.push_back({pname, 32, false});
    StoreClassParam(info, pname,
                    pexpr ? sizer.Value(i, pexpr, ctx, arena)
                          : MakeLogic4VecVal(arena, 32, 0));
  }
  // §8.25/§8.26.3: parameters declared in the class body (carried as kProperty
  // members with is_param) become static compile-time constants of the class,
  // readable via the class name with the scope resolution operator.
  for (const auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kProperty || !member->is_param)
      continue;
    uint32_t w = EvalTypeWidth(member->data_type, {});
    if (w == 0) w = 32;
    StoreClassParam(info, member->name,
                    member->init_expr
                        ? sizer.Value(member->name, &member->data_type,
                                      member->init_expr, ctx, arena)
                        : MakeLogic4VecVal(arena, w, 0));
  }
  // §6.20.4: a body parameter naming a header one, `N = W * 2`, is folded
  // with the defaults just stored, which the loop above had no name for.
  FoldClassBodyParams(cls, ClassStaticLookup(info), ClassStaticStore(info), ctx,
                      arena);
}

// §8.23 with §6.19: the literals of every enumeration a typedef of the class
// declares, each bound in the class scope, and the enumeration itself
// registered under "Class::name", the key a property or a variable declared
// with the class-scoped typedef resolves its type by (EnumTypeOfDeclaredType
// in eval_enum.cpp), so that §6.19.5's methods on such a value have members
// to walk. A nested class's typedef is entered by no other path: the design's
// typedef table (RtlirDesign::type_enums) holds the unit's classes alone.
static void CollectClassEnumMembers(ClassTypeInfo* info, const ClassDecl* cls,
                                    SimContext& ctx, Arena& arena) {
  for (const auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kTypedef || !member->typedef_item)
      continue;
    const auto& enum_members = member->typedef_item->typedef_type.enum_members;
    if (enum_members.empty()) continue;
    EnumTypeInfo type;
    type.type_name = *arena.Create<std::string>(
        std::string(info->name) + "::" + std::string(member->name));
    const DataType& decl_type = member->typedef_item->typedef_type;
    type.width = EvalTypeWidth(decl_type);
    type.is_4state = Is4stateType(decl_type, TypedefMap{});
    int64_t next_val = 0;
    for (const auto& em : enum_members) {
      if (em.value) next_val = static_cast<int64_t>(em.value->int_val);
      info->enum_members[std::string(em.name)] =
          static_cast<uint64_t>(next_val);
      type.members.push_back({em.name, static_cast<uint64_t>(next_val)});
      ++next_val;
    }
    if (ctx.FindEnumType(type.type_name) == nullptr)
      ctx.RegisterEnumType(type.type_name, type);
  }
}

static void InheritInterfaceStaticsAndEnums(ClassTypeInfo* info,
                                            const ClassTypeInfo* src) {
  for (const auto& [k, v] : src->static_properties) {
    if (info->static_properties.find(k) == info->static_properties.end())
      info->static_properties[k] = v;
  }
  for (const auto& [k, v] : src->enum_members) {
    if (info->enum_members.find(k) == info->enum_members.end())
      info->enum_members[k] = v;
  }
}

static void InheritInterfaceMembers(ClassTypeInfo* info) {
  if (info->parent && info->parent->is_interface)
    InheritInterfaceStaticsAndEnums(info, info->parent);
  for (const auto* iface : info->extended_interfaces)
    InheritInterfaceStaticsAndEnums(info, iface);
}

// §8.25: the class the extends clause of `cls` names as its base. The base
// may be named by a type parameter of the derived class, `class D4 #(type P =
// C#(byte)) extends P;`, which §8.25 has resolve to a class type after
// elaboration (printed page 205 of IEEE 1800-2023). What this registers is the
// declaration's own type, which §8.25.1 makes the default specialization, so
// the base it records is the one the parameter's default names; a
// specialization whose actual names another class is given that class as it
// is created (SpecializationOf in class_specialization.cpp). The type actuals
// the default or the actual carries for the base's own parameters are bound
// as each object is constructed (BaseTypeBindings in eval_class_new.cpp). A
// parameter given no default, or a default that is no named type, names no
// base. Looked up by the parameter's name, the base was never found, and the
// derived class inherited nothing.
static ClassTypeInfo* BaseClassOf(const ClassDecl* cls, SimContext& ctx) {
  if (cls->type_param_names.count(cls->base_class) == 0)
    return ctx.FindClassType(cls->base_class);
  const DataType* def = TypeParamActual(nullptr, cls, cls->base_class);
  if (def == nullptr || def->kind != DataTypeKind::kNamed) return nullptr;
  return ctx.FindClassType(def->type_name);
}

// The base, the interfaces, the members, the vtable and the static storage of
// the class `cls` declares, filled into `info` whichever scope declares the
// class: a compilation unit, package or module, whose `scope.items` carry the
// out-of-block method bodies of §8.24, or another class (§8.23), which carries
// none. Before the two shared this, a nested class was given its properties
// and methods alone -- no declared type name on a property, so `link = new`
// on a `Node link` constructed nothing, and no vtable.
static void PopulateClassType(ClassTypeInfo* info, const ClassDecl* cls,
                              const ClassDeclScope& scope, SimContext& ctx,
                              Arena& arena) {
  if (!cls->base_class.empty()) info->parent = BaseClassOf(cls, ctx);
  info->unit_constants = &scope.constants;
  for (const auto& ref : cls->extends_interfaces) {
    auto* iface = ctx.FindClassType(ref.name);
    if (iface) info->extended_interfaces.push_back(iface);
  }
  for (const auto& ref : cls->implements_types) {
    auto* iface = ctx.FindClassType(ref.name);
    if (iface) info->extended_interfaces.push_back(iface);
  }
  CollectClassMembers(info, cls, scope.constants, ctx);
  AttachScopeMethodBodies(info, cls, scope.items);
  RecordArrayProperties(info, cls, scope.constants, ctx, arena);
  BuildVTable(info, cls);
  CreateStaticProperties(info, arena);
  InitClassParams(info, cls, ctx, arena);
  CollectClassEnumMembers(info, cls, ctx, arena);
  if (cls->is_interface) InheritInterfaceMembers(info);
}

static void LowerNestedClasses(ClassTypeInfo* outer, const ClassDecl* cls,
                               const ScopeMap& constants, SimContext& ctx,
                               Arena& arena);

// §26.2: records `package` as the one `info` is declared in, and each of the
// class's methods -- the in-class bodies and the §8.24 out-of-block ones
// AttachScopeMethodBodies put in their place -- as a subroutine of that
// package, so ExecClassMethod gives a method's frame the package as
// EvalFunctionCall gives a package function's, and the package's parameters,
// enum literals, variables and functions answer to their bare names inside
// the body. §3.12.1 (printed page 56): the compilation unit's scope is
// recorded the same way under kUnitScopeName for a class the unit declares,
// so a method's frame and the property defaults' frame
// (ConstructBaseThenDefaults in eval_class_new.cpp) resolve a bare name to
// the unit's "$unit.name" storage ahead of the calling module's like-named
// declaration, which the class's scope never contains (§23.9). With nothing
// recorded, a unit class's `return g;` and `int p = g;` read the top's own
// `int g = 7` for the unit's 5. Nothing is recorded for a module's class.
static void RecordClassPackage(ClassTypeInfo* info, std::string_view package,
                               SimContext& ctx) {
  if (package.empty()) return;
  info->package = package;
  for (const auto& entry : info->methods) {
    ctx.RegisterSubroutinePackage(entry.second, package);
  }
}

// §8.23: a class declared inside `outer` is a type of its own, reached from
// outside as `Outer::Inner`, which is the key it is registered under; a
// method of the containing class names it bare, which SimContext::FindClassType
// resolves through `enclosing`. A nested class of the nested class is lowered
// under it in turn. The enclosing class carries no out-of-block bodies; the
// unit's constants reach the nested class as they reach the outer one.
static void LowerNestedClass(ClassTypeInfo* outer, const ClassDecl* nested,
                             const ScopeMap& constants, SimContext& ctx,
                             Arena& arena) {
  auto qualified = std::string(outer->name) + "::" + std::string(nested->name);
  auto* info = arena.Create<ClassTypeInfo>();
  info->name = *arena.Create<std::string>(std::move(qualified));
  info->decl = nested;
  info->is_abstract = nested->is_virtual;
  info->is_interface = nested->is_interface;
  info->enclosing = outer;
  const std::vector<ModuleItem*> kNoItems;
  PopulateClassType(info, nested, {kNoItems, constants}, ctx, arena);
  RecordClassPackage(info, outer->package, ctx);
  ctx.RegisterClassType(info->name, info);
  BindDeclarationBase(info, ctx, arena);
  LowerNestedClasses(info, nested, constants, ctx, arena);
}

static void LowerNestedClasses(ClassTypeInfo* outer, const ClassDecl* cls,
                               const ScopeMap& constants, SimContext& ctx,
                               Arena& arena) {
  for (const auto* member : cls->members) {
    if (member->kind == ClassMemberKind::kClassDecl && member->nested_class)
      LowerNestedClass(outer, member->nested_class, constants, ctx, arena);
  }
}

// §26.2: the name of the package whose items declare `cls`, or an empty view
// for a class a module or the compilation unit declares. LowerPackageClass in
// lowerer_import.cpp hands LowerClassDecl the package's items alone, so the
// package is found from the declaration itself.
std::string_view Lowerer::DeclaringPackage(const ClassDecl* cls) const {
  if (design_ == nullptr) return {};
  for (const auto* pkg : design_->packages) {
    for (const auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kClassDecl && item->class_decl == cls)
        return pkg->name;
    }
  }
  return {};
}

// §3.12.1 (printed page 56): the name the compilation-unit scope's frames
// are pushed with and its items keyed under, "$unit.name", as
// lowerer_package_data.cpp spells it for the unit's storage and its own
// initializers' frames (kUnitScope there); no package can be named so, `$`
// starting no identifier.
constexpr std::string_view kUnitScopeName = "$unit";

// §3.12.1: kUnitScopeName for a class the compilation unit itself declares
// (RtlirDesign::cu_class_decls), and an empty view for a package's or a
// module's class, or with no design behind the class.
static std::string_view UnitScopeOf(const RtlirDesign* design,
                                    const ClassDecl* cls) {
  if (design == nullptr) return {};
  for (const ClassDecl* unit_cls : design->cu_class_decls) {
    if (unit_cls == cls) return kUnitScopeName;
  }
  return {};
}

void Lowerer::RegisterClassDecl(const ClassDecl* cls,
                                const std::vector<ModuleItem*>& scope_items) {
  auto* info = arena_.Create<ClassTypeInfo>();
  info->name = cls->name;
  info->decl = cls;
  info->is_abstract = cls->is_virtual;
  info->is_interface = cls->is_interface;
  // A class lowered with no design behind it -- a test that builds the
  // ClassDecl by hand -- reads an empty unit scope.
  static const ScopeMap kNoConstants;
  const ScopeMap& constants =
      design_ != nullptr ? design_->unit_constants : kNoConstants;
  // §8.9 (printed page 186) with §23.9 (printed 761) and §26.2 (printed
  // 808): a static property's initializer is evaluated once, as an
  // expression of the class declaration's scope, so the class is populated
  // in a frame of the package or the compilation unit declaring it
  // (InitClassParams, and the static initializers InitClassStaticProperties
  // evaluates in the same frame later), through which
  // SimContext::FindInPackageScope
  // resolves a bare name to the scope's "pkg.name" or "$unit.name" storage.
  // Populated in no frame, a unit class's `static int s = g;` resolved g by
  // its bare key, which holds nothing once the unit's storage stands under
  // "$unit.g" (CreateUnitDataVariables in lowerer_package_data.cpp), and
  // `C::s` read 0; a package class's read the package's variable through
  // no key at all. A module's class is populated in no frame, as before.
  std::string_view scope = DeclaringPackage(cls);
  if (scope.empty()) scope = UnitScopeOf(design_, cls);
  if (!scope.empty()) ctx_.PushScope(scope);
  PopulateClassType(info, cls, {scope_items, constants}, ctx_, arena_);
  if (!scope.empty()) ctx_.PopScope();
  RecordClassPackage(info, scope, ctx_);
  ctx_.RegisterClassType(cls->name, info);
  // §6.18 with §8.3: the class's typedefs naming a class, its own included,
  // bound before InitClassStaticProperties runs its methods.
  RegisterClassScopeTypedefAliases(info, ctx_, arena_);
  // §8.25: an extends clause writing a `#(...)` list names a specialization
  // of the base, found once the class is registered under its own name.
  BindDeclarationBase(info, ctx_, arena_);
  LowerNestedClasses(info, cls, constants, ctx_, arena_);
}

// §8.9 (printed page 186) with §23.9 (printed 761) and §26.2 (printed 808):
// the static initializers of `cls`, registered by RegisterClassDecl, run
// once in a frame of the scope declaring the class -- its package, the
// compilation unit's "$unit", or none for a module's -- the scope
// RecordClassPackage recorded on the class. A same-named class of another
// scope bound under the bare name since is not `cls` and is left alone. The
// class's own copy is the default specialization's (§8.25.1, printed page
// 205), so a frame of its own binds each type parameter to the default the
// class declares, which `static int w = $bits(T)` sizes; with nothing bound
// it held 1 under `class C #(type T = int)`.
void Lowerer::InitClassStaticProperties(const ClassDecl* cls) {
  ClassTypeInfo* info = ctx_.FindClassType(cls->name);
  if (info == nullptr || info->decl != cls) return;
  if (!info->package.empty()) ctx_.PushScope(info->package);
  ctx_.PushScope();
  BindStaticInitTypeActuals(info, ctx_);
  BindStaticInitValueParams(info, ctx_);
  InitStaticProperties(info, ctx_, arena_);
  ctx_.PopScope();
  if (!info->package.empty()) ctx_.PopScope();
}

void Lowerer::LowerClassDecl(const ClassDecl* cls,
                             const std::vector<ModuleItem*>& scope_items) {
  RegisterClassDecl(cls, scope_items);
  InitClassStaticProperties(cls);
}

}  // namespace delta
