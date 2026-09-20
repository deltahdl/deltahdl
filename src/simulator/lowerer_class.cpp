#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

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

static void InitStaticProperties(ClassTypeInfo* info, SimContext& ctx,
                                 Arena& arena) {
  for (const auto& p : info->properties) {
    if (p.is_static) {
      if (p.init_expr) {
        info->static_properties[std::string(p.name)] =
            EvalExpr(p.init_expr, ctx, arena);
      } else {
        info->static_properties[std::string(p.name)] =
            MakeLogic4VecVal(arena, p.width, 0);
      }
    }
  }
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
// item parses with is_static false; the static-ness is carried forward from
// the prototype before the body replaces it, so that a call through the class
// scope resolution operator of §8.23 still resolves it as static, and so are
// the prototype's default argument values.
static void AttachMethodBody(ClassTypeInfo* cls, ModuleItem* body) {
  std::string name(body->name);
  auto existing = cls->methods.find(name);
  if (existing != cls->methods.end()) {
    if (existing->second->is_static) body->is_static = true;
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

// §8.25: the value parameters a property's packed dimension may name, `bit
// [size-1:0] a` in the subclause's `vector #(int size = 1)`, each at the
// default the class declares for it -- the header parameters in order, a
// later default free to name an earlier one, then the parameters and
// localparams of the class body (§6.20.1), which may name the header's. A
// type parameter stands for no value and is left out, as is a default that
// does not fold to a constant. The widths this sizes are those of the default
// specialization (§8.25.1).
static ScopeMap ClassParamScope(const ClassDecl* cls) {
  ScopeMap scope;
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

static void CollectClassMembers(ClassTypeInfo* info, const ClassDecl* cls) {
  ScopeMap params = ClassParamScope(cls);
  for (auto* member : cls->members) {
    if (member->kind == ClassMemberKind::kProperty) {
      uint32_t w = EvalTypeWidth(member->data_type, {}, params);
      bool sized = w != 0;
      if (w == 0) w = 32;
      info->properties.push_back(
          {member->name, w, member->is_static, member->is_local,
           member->is_protected, member->is_const, member->init_expr,
           Is4stateType(member->data_type, {}), sized,
           IsRealKind(member->data_type.kind),
           IsSignedType(member->data_type, {}), member->data_type.type_name,
           member->data_type.kind == DataTypeKind::kVirtualInterface});
    } else if (member->kind == ClassMemberKind::kMethod && member->method) {
      std::string name(member->method->name);
      info->methods[name] = member->method;
    }
  }
}

// §7.4.2: the element count and lowest index the one unpacked dimension `dim`
// of a class property declares, a literal `[N]` addressing 0 to N-1 and a
// range `[a:b]` addressing the smaller of a and b to the larger. Zero elements
// for a dimension of any other form -- a dynamic array's absent bound, a
// queue's `$`, an associative array's index type, or an expression the
// simulator does not fold here -- which the object then models as it did, one
// value under the property's name.
static uint32_t FixedDimensionSize(const Expr* dim, int64_t& lo,
                                   SimContext& ctx, Arena& arena) {
  if (dim == nullptr) return 0;
  if (dim->kind == ExprKind::kIntegerLiteral) {
    lo = 0;
    return static_cast<uint32_t>(dim->int_val);
  }
  if (dim->kind != ExprKind::kBinary || dim->op != TokenKind::kColon ||
      dim->lhs == nullptr || dim->rhs == nullptr) {
    return 0;
  }
  auto left = static_cast<int64_t>(EvalExpr(dim->lhs, ctx, arena).ToUint64());
  auto right = static_cast<int64_t>(EvalExpr(dim->rhs, ctx, arena).ToUint64());
  lo = left < right ? left : right;
  return static_cast<uint32_t>(left < right ? right - left + 1
                                            : left - right + 1);
}

// §7.4.2/§7.5/§18.5.7: mark each property declared with one fixed or
// dynamic unpacked dimension as the array it is, so the object holds its
// elements one by one and a constraint can iterate over them or reduce them.
// A property with more than one unpacked dimension is left as it was.
static void RecordArrayProperties(ClassTypeInfo* info, const ClassDecl* cls,
                                  SimContext& ctx, Arena& arena) {
  for (const auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kProperty ||
        member->unpacked_dims.size() != 1) {
      continue;
    }
    const bool kDynamic = member->unpacked_dims[0] == nullptr;
    int64_t lo = 0;
    uint32_t size =
        kDynamic ? 0
                 : FixedDimensionSize(member->unpacked_dims[0], lo, ctx, arena);
    if (size == 0 && !kDynamic) continue;
    for (auto& prop : info->properties) {
      if (prop.name != member->name) continue;
      prop.array_size = size;
      prop.array_lo = lo;
      prop.is_dynamic = kDynamic;
    }
  }
}

static void StoreClassParam(ClassTypeInfo* info, std::string_view pname,
                            const Logic4Vec& value) {
  info->static_properties[std::string(pname)] = value;
}

static void InitClassParams(ClassTypeInfo* info, const ClassDecl* cls,
                            SimContext& ctx, Arena& arena) {
  // §6.20: parameters supplied through the class's parameter port list.
  for (const auto& [pname, pexpr] : cls->params) {
    info->properties.push_back({pname, 32, false});
    StoreClassParam(
        info, pname,
        pexpr ? EvalExpr(pexpr, ctx, arena) : MakeLogic4VecVal(arena, 32, 0));
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
                    member->init_expr ? EvalExpr(member->init_expr, ctx, arena)
                                      : MakeLogic4VecVal(arena, w, 0));
  }
}

static void CollectClassEnumMembers(ClassTypeInfo* info, const ClassDecl* cls) {
  for (const auto* member : cls->members) {
    if (member->kind != ClassMemberKind::kTypedef || !member->typedef_item)
      continue;
    const auto& enum_members = member->typedef_item->typedef_type.enum_members;
    int64_t next_val = 0;
    for (const auto& em : enum_members) {
      if (em.value) next_val = static_cast<int64_t>(em.value->int_val);
      info->enum_members[std::string(em.name)] =
          static_cast<uint64_t>(next_val);
      ++next_val;
    }
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

static void CollectNestedClassMembers(ClassTypeInfo* nested_info,
                                      const ClassDecl* nested_class) {
  for (auto* m : nested_class->members) {
    if (m->kind == ClassMemberKind::kProperty) {
      uint32_t w = EvalTypeWidth(m->data_type, {});
      bool sized = w != 0;
      if (w == 0) w = 32;
      nested_info->properties.push_back(
          {m->name, w, m->is_static, m->is_local, m->is_protected, m->is_const,
           m->init_expr, Is4stateType(m->data_type, {}), sized,
           IsRealKind(m->data_type.kind), IsSignedType(m->data_type, {})});
    } else if (m->kind == ClassMemberKind::kMethod && m->method) {
      nested_info->methods[std::string(m->method->name)] = m->method;
    }
  }
}

static void LowerNestedClass(const ClassDecl* outer, const ClassMember* member,
                             SimContext& ctx, Arena& arena) {
  auto qualified =
      std::string(outer->name) + "::" + std::string(member->nested_class->name);
  auto* nested_info = arena.Create<ClassTypeInfo>();
  nested_info->name = *arena.Create<std::string>(std::move(qualified));
  nested_info->decl = member->nested_class;
  nested_info->is_abstract = member->nested_class->is_virtual;
  nested_info->is_interface = member->nested_class->is_interface;
  if (!member->nested_class->base_class.empty())
    nested_info->parent = ctx.FindClassType(member->nested_class->base_class);
  CollectNestedClassMembers(nested_info, member->nested_class);
  InitStaticProperties(nested_info, ctx, arena);
  ctx.RegisterClassType(nested_info->name, nested_info);
}

void Lowerer::LowerClassDecl(const ClassDecl* cls,
                             const std::vector<ModuleItem*>& scope_items) {
  auto* info = arena_.Create<ClassTypeInfo>();
  info->name = cls->name;
  info->decl = cls;
  info->is_abstract = cls->is_virtual;
  info->is_interface = cls->is_interface;

  if (!cls->base_class.empty())
    info->parent = ctx_.FindClassType(cls->base_class);
  for (const auto& ref : cls->extends_interfaces) {
    auto* iface = ctx_.FindClassType(ref.name);
    if (iface) info->extended_interfaces.push_back(iface);
  }
  for (const auto& ref : cls->implements_types) {
    auto* iface = ctx_.FindClassType(ref.name);
    if (iface) info->extended_interfaces.push_back(iface);
  }
  CollectClassMembers(info, cls);
  AttachScopeMethodBodies(info, cls, scope_items);
  RecordArrayProperties(info, cls, ctx_, arena_);
  BuildVTable(info, cls);
  InitStaticProperties(info, ctx_, arena_);
  InitClassParams(info, cls, ctx_, arena_);
  CollectClassEnumMembers(info, cls);

  if (cls->is_interface) InheritInterfaceMembers(info);
  ctx_.RegisterClassType(cls->name, info);

  for (const auto* member : cls->members) {
    if (member->kind == ClassMemberKind::kClassDecl && member->nested_class)
      LowerNestedClass(cls, member, ctx_, arena_);
  }
}

}  // namespace delta
