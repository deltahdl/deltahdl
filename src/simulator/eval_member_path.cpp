#include "simulator/eval_member_path.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

// §23.6 with §8.5: the first dot of `h.p` parts the handle from the property,
// but a handle reached by a hierarchical path -- `i.c.v` for the class
// variable `c` an interface instance `i` declares -- has the instance path
// ahead of the handle's name, and the first dot puts `i`, which names no
// variable, on the handle side. Where the first segment names no variable, the
// split moves to the first dot after which the path so far names one, so the
// handle side is the instance-qualified variable and the property side what
// remains. A path no prefix of which names a variable keeps the first-dot
// split, and one with no dot answers npos.
size_t MemberPathSplit(const std::string& path, SimContext& ctx) {
  size_t first = path.find('.');
  if (first == std::string::npos) return first;
  std::string_view whole = path;
  if (ctx.FindVariable(whole.substr(0, first)) != nullptr) return first;
  for (size_t dot = path.find('.', first + 1); dot != std::string::npos;
       dot = path.find('.', dot + 1)) {
    if (ctx.FindVariable(whole.substr(0, dot)) != nullptr) return dot;
  }
  return first;
}

static const StructTypeInfo* StructLayoutOfWholeName(std::string_view name,
                                                     SimContext& ctx) {
  if (ctx.FindLocalVariable(name) != nullptr) {
    return ctx.GetVariableStructType(name);
  }
  std::string prefixed = ctx.ActiveInstancePrefix() + std::string(name);
  if (const StructTypeInfo* info = ctx.GetVariableStructType(prefixed)) {
    return info;
  }
  return ctx.GetVariableStructType(name);
}

const StructTypeInfo* StructLayoutOfName(std::string_view name,
                                         SimContext& ctx) {
  if (const StructTypeInfo* info = StructLayoutOfWholeName(name, ctx))
    return info;
  // §7.4.2 with §7.2: an element of an unpacked array of structures, the
  // variable `c[1]` of `c_t c[3]`, has the array's element layout, which the
  // array registers under its own name.
  if (name.empty() || name.back() != ']') return nullptr;
  auto open = name.find('[');
  if (open == std::string_view::npos || open == 0) return nullptr;
  return StructLayoutOfWholeName(name.substr(0, open), ctx);
}

// §11.9 (printed page 304) with §3.12.1 (printed 56) and §26.3 (printed
// 810): a tagged union variable has one tag, whichever name it is written or
// read by, and the tag table (SimContext::var_tags_) keys it by name with no
// alias of its own, so an alias of a variable -- a module's bare `u` bound to
// the unit's "$unit.u" by AliasUnitDataItems, or an import's name bound to
// "pk.u" -- resolves to the key its storage stands under: the key its layout
// is registered by (StructTypeInfo::type_name, which the builder spells as
// the registration's key), where that key names the same variable as `key`
// does. A module's own declaration registers its layout under its storage
// key (RegisterAggregateLayout), so its key answers itself, and a package's
// or the unit's variable is given a registration under its own key when it
// is first aliased (AliasLayout in lowerer_alias_kinds.cpp); a name bound to
// a typedef's registration, which names no variable, keeps its key. Under
// the alias's own key, `u = tagged Other 3;` in a module declaring no u
// recorded Other under "u" while `$unit::u.Valid` read the initializer's
// Valid under "$unit.u" and passed a read the subclause reports.
static std::string StorageKeyOfLayout(const std::string& key, SimContext& ctx) {
  const StructTypeInfo* info = ctx.GetVariableStructType(key);
  if (info == nullptr || info->type_name == key) return key;
  Variable* own = ctx.FindVariable(key);
  if (own == nullptr || ctx.FindVariable(info->type_name) != own) return key;
  return std::string(info->type_name);
}

std::string TagKeyOfName(std::string_view name, SimContext& ctx) {
  if (ctx.FindLocalVariable(name) != nullptr) return std::string(name);
  std::string prefixed = ctx.ActiveInstancePrefix() + std::string(name);
  if (ctx.GetVariableStructType(prefixed) != nullptr)
    return StorageKeyOfLayout(prefixed, ctx);
  return std::string(name);
}

const StructTypeInfo* TaggedMemberLayout(const StructTypeInfo& sinfo,
                                         std::string_view member) {
  for (const auto& field : sinfo.fields) {
    if (field.name == member && field.nested) return field.nested;
  }
  return nullptr;
}

// The class whose static property the bare name `name` reads inside a method
// (§8.10 for a static method, §8.23 for a nested class's), or the class the
// scope `C::name` or `p::C::name` names; null for a name a local shadows or
// a base of another shape. §8.13 (printed pages 189-190): the class answered
// is the one declaring the property, C for `D::m_inst` where D extends C
// (ClassTypeInfo::StaticPropertyDeclarer), whose one storage holds the
// handle; asked of D's own static_properties, `D::m_inst.k` read x.
static const ClassTypeInfo* StaticPropertyClassOf(const Expr* base,
                                                  SimContext& ctx, Arena& arena,
                                                  std::string_view& name) {
  if (base->kind == ExprKind::kIdentifier) {
    if (NameDenotesVariable(base->text, ctx)) return nullptr;
    name = base->text;
    const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
    return method_cls != nullptr ? method_cls->StaticPropertyOwner(name)
                                 : nullptr;
  }
  if (base->kind != ExprKind::kMemberAccess || !base->is_scope_resolution ||
      base->rhs == nullptr || base->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  name = base->rhs->text;
  const ClassTypeInfo* cls =
      ctx.FindClassType(ScopedClassKey(base->lhs, arena));
  return cls != nullptr ? cls->StaticPropertyDeclarer(name) : nullptr;
}

bool ResolveStaticPropertyBase(const Expr* base, SimContext& ctx, Arena& arena,
                               StaticPropertyRef& out) {
  if (base == nullptr) return false;
  std::string_view name;
  const ClassTypeInfo* cls = StaticPropertyClassOf(base, ctx, arena, name);
  if (cls == nullptr) return false;
  auto it = cls->static_properties.find(std::string(name));
  if (it == cls->static_properties.end()) return false;
  out = {cls, &it->second, name};
  return true;
}

ClassObject* StaticPropertyObject(const StaticPropertyRef& ref, SimContext& ctx,
                                  std::string_view* declared_key) {
  const ClassTypeInfo::PropertyInfo* prop = ref.owner->FindProperty(ref.name);
  if (prop != nullptr && prop->IsArray()) return nullptr;
  *declared_key = PropertyClassName(nullptr, ref.owner, ref.name, ctx);
  const ClassTypeInfo* declared = ctx.FindClassType(*declared_key);
  // §9.7 with §26.7: a built-in class's handle, `static process p`, numbers
  // no ClassObject of the run and is the built-in method paths' to read; the
  // built-in class is the one registered with no declaration of its own
  // (RegisterProcessClassType in lowerer_register.cpp).
  if (declared == nullptr || declared->decl == nullptr) return nullptr;
  return ctx.GetClassObject(ref.slot->ToUint64());
}

bool ResolveStaticHandlePath(const Expr* access, SimContext& ctx, Arena& arena,
                             StaticPropertyRef& ref, std::string& path) {
  path.clear();
  const Expr* base = access;
  while (base != nullptr && base->kind == ExprKind::kMemberAccess &&
         !base->is_scope_resolution && base->rhs != nullptr &&
         base->rhs->kind == ExprKind::kIdentifier) {
    std::string member(base->rhs->text);
    if (!path.empty()) {
      member += '.';
      member += path;
    }
    path = std::move(member);
    base = base->lhs;
  }
  return base != access && ResolveStaticPropertyBase(base, ctx, arena, ref);
}

bool TryStaticHandleMember(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  StaticPropertyRef ref;
  std::string path;
  if (!ResolveStaticHandlePath(expr, ctx, arena, ref, path)) return false;
  std::string_view declared_key;
  ClassObject* obj = StaticPropertyObject(ref, ctx, &declared_key);
  if (obj == nullptr) return false;
  out = ResolveClassFieldChain(obj, ctx.FindClassType(declared_key), path, ctx,
                               arena);
  return true;
}

// The root variable's name and the member path a chain of member accesses
// names, `m` and `s.v` for `m.s.v`; false where the chain does not end at a
// plain identifier.
static bool MemberChainPath(const Expr* access, std::string_view& root,
                            std::string& path) {
  path.clear();
  const Expr* e = access;
  while (e != nullptr && e->kind == ExprKind::kMemberAccess &&
         !e->is_scope_resolution && e->rhs != nullptr &&
         e->rhs->kind == ExprKind::kIdentifier) {
    if (!path.empty()) path.insert(0, 1, '.');
    path.insert(0, e->rhs->text);
    e = e->lhs;
  }
  if (e == access || e == nullptr || e->kind != ExprKind::kIdentifier)
    return false;
  root = e->text;
  return true;
}

// §8.5: the structure layout of the property `name` the class of `obj`
// declares or inherits, null where its type names no structure.
static const StructTypeInfo* PropertyStructLayout(const ClassObject* obj,
                                                  std::string_view name,
                                                  SimContext& ctx) {
  for (const ClassTypeInfo* t = obj->type; t != nullptr; t = t->parent) {
    for (const auto& p : t->properties) {
      if (p.name != name || p.is_static) continue;
      return p.type_name.empty() ? nullptr : ctx.FindStructType(p.type_name);
    }
  }
  return nullptr;
}

// The structure a member path starts from: the root variable's, or, §8.5,
// the one a class property holds, reached through a handle variable or
// `this` with the property as the path's first member, or named bare in a
// method. The path is left as the part inside the structure.
struct StructRoot {
  Logic4Vec* value = nullptr;
  Variable* var = nullptr;
  const StructTypeInfo* info = nullptr;
};

static bool PropertyRoot(ClassObject* obj, std::string_view prop,
                         SimContext& ctx, StructRoot& root) {
  if (obj == nullptr) return false;
  auto it = obj->properties.find(std::string(prop));
  if (it == obj->properties.end()) return false;
  root.info = PropertyStructLayout(obj, prop, ctx);
  if (root.info == nullptr) return false;
  // A property its collector could not size holds the 32-bit carrier until a
  // member write widens it to its layout; an element of an array member may
  // stand above the carrier, so the value is widened here as that write
  // widens it, keeping the bits it holds.
  if (it->second.width < root.info->total_width) {
    Logic4Vec wide = MakeLogic4Vec(ctx.GetArena(), root.info->total_width);
    DepositBitField(wide, 0, it->second, it->second.width);
    it->second = wide;
  }
  root.value = &it->second;
  return true;
}

static bool FindStructRoot(std::string_view name, std::string& path,
                           SimContext& ctx, StructRoot& root) {
  Variable* var = ctx.FindVariable(name);
  if (var != nullptr) {
    if (const StructTypeInfo* info = StructLayoutOfName(name, ctx)) {
      root = {&var->value, var, info};
      return true;
    }
  }
  ClassObject* obj = nullptr;
  if (name == "this") {
    obj = ctx.CurrentThis();
  } else if (var != nullptr && !ctx.GetVariableClassType(name).empty()) {
    obj = ctx.GetClassObject(var->value.ToUint64());
  }
  if (obj != nullptr) {
    auto dot = path.find('.');
    if (dot == std::string::npos) return false;
    std::string prop = path.substr(0, dot);
    path.erase(0, dot + 1);
    return PropertyRoot(obj, prop, ctx, root);
  }
  return var == nullptr && PropertyRoot(ctx.CurrentThis(), name, ctx, root);
}

const StructTypeInfo* ContainerElementLayout(const Expr* base,
                                             SimContext& ctx) {
  if (base == nullptr) return nullptr;
  if (base->kind == ExprKind::kIdentifier) {
    // §8.11 with §23.9: in a method a property of the object is found ahead
    // of a variable of the module the class is declared in; a local of the
    // method shadows both.
    const ClassObject* self = ctx.CurrentThis();
    if (self != nullptr && ctx.FindLocalVariable(base->text) == nullptr) {
      if (const StructTypeInfo* info =
              PropertyStructLayout(self, base->text, ctx))
        return info;
    }
    return StructLayoutOfName(base->text, ctx);
  }
  std::string_view name;
  std::string path;
  if (base->kind != ExprKind::kMemberAccess ||
      !MemberChainPath(base, name, path) || path.find('.') != std::string::npos)
    return nullptr;
  ClassObject* obj = nullptr;
  if (name == "this") {
    obj = ctx.CurrentThis();
  } else if (Variable* var = ctx.FindVariable(name);
             var != nullptr && !ctx.GetVariableClassType(name).empty()) {
    obj = ctx.GetClassObject(var->value.ToUint64());
  }
  return obj != nullptr ? PropertyStructLayout(obj, path, ctx) : nullptr;
}

const StructFieldInfo* ResolveStructMember(const Expr* access,
                                           SimContext& ctx) {
  if (access == nullptr || access->kind != ExprKind::kMemberAccess)
    return nullptr;
  std::string_view name;
  std::string path;
  if (!MemberChainPath(access, name, path)) return nullptr;
  StructRoot root;
  if (!FindStructRoot(name, path, ctx, root)) return nullptr;
  uint32_t offset = 0;
  return ResolveStructField(root.info, path, &offset);
}

const StructFieldInfo* ResolveStructArrayMember(const Expr* access,
                                                SimContext& ctx) {
  const StructFieldInfo* field = ResolveStructMember(access, ctx);
  return field != nullptr && field->elem_count > 0 ? field : nullptr;
}

bool ResolveStructArrayElement(const Expr* select, SimContext& ctx,
                               Arena& arena, StructArrayElementRef& out) {
  if (select->kind != ExprKind::kSelect || select->index_end != nullptr ||
      select->base == nullptr || select->base->kind != ExprKind::kMemberAccess)
    return false;
  std::string_view name;
  std::string path;
  if (!MemberChainPath(select->base, name, path)) return false;
  StructRoot root;
  if (!FindStructRoot(name, path, ctx, root)) return false;
  uint32_t offset = 0;
  const StructFieldInfo* field = ResolveStructField(root.info, path, &offset);
  if (field == nullptr || field->elem_count == 0) return false;
  out.value = root.value;
  out.var = root.var;
  out.width = field->width / field->elem_count;
  out.is_signed = field->is_signed;
  Logic4Vec idx = EvalExpr(select->index, ctx, arena);
  if (!idx.IsKnown()) return true;
  auto i = static_cast<int64_t>(idx.ToUint64());
  int64_t pos = field->elem_left <= field->elem_right ? i - field->elem_left
                                                      : field->elem_left - i;
  if (pos < 0 || pos >= static_cast<int64_t>(field->elem_count)) return true;
  // The leftmost element stands in the member's most significant bits.
  out.bit_offset =
      offset + (field->elem_count - 1 - static_cast<uint32_t>(pos)) * out.width;
  out.in_range = true;
  return true;
}

bool TryContainerElementMember(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  const Expr* select = expr->lhs;
  if (select == nullptr || select->kind != ExprKind::kSelect ||
      select->index_end != nullptr || select->base == nullptr ||
      expr->rhs == nullptr || expr->rhs->kind != ExprKind::kIdentifier)
    return false;
  const StructTypeInfo* info = ContainerElementLayout(select->base, ctx);
  if (info == nullptr) return false;
  uint32_t offset = 0;
  const StructFieldInfo* field =
      ResolveStructField(info, expr->rhs->text, &offset);
  if (field == nullptr) return false;
  Logic4Vec element = EvalExpr(select, ctx, arena);
  if (element.width < info->total_width) return false;
  out = ExtractBitField(arena, element, offset, field->width);
  out.is_real = field->type_kind == DataTypeKind::kReal ||
                field->type_kind == DataTypeKind::kShortreal ||
                field->type_kind == DataTypeKind::kRealtime;
  out.is_signed = field->is_signed && !out.is_real;
  return true;
}

}  // namespace delta
