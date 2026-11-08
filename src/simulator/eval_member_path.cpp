#include "simulator/eval_member_path.h"

#include <algorithm>
#include <array>
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
#include "simulator/dyn_struct_member.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_struct_property.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/struct_string_member.h"
#include "simulator/variable.h"

namespace delta {

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
  if (const Variable* local = ctx.FindLocalVariable(name)) {
    if (local->local_layout != nullptr) return local->local_layout;
    return ctx.GetVariableStructType(name);
  }
  for (const std::string& key : ctx.ScopedObjectKeys(name)) {
    if (const StructTypeInfo* info = ctx.GetVariableStructType(key))
      return info;
  }
  return nullptr;
}

const StructTypeInfo* StructLayoutOfName(std::string_view name,
                                         SimContext& ctx) {
  if (const StructTypeInfo* info = StructLayoutOfWholeName(name, ctx))
    return info;
  if (name.empty() || name.back() != ']') return nullptr;
  auto open = name.find('[');
  if (open == std::string_view::npos || open == 0) return nullptr;
  return StructLayoutOfWholeName(name.substr(0, open), ctx);
}

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

const StructTypeInfo* PropertyAggregateLayout(std::string_view name,
                                              SimContext& ctx,
                                              std::string& key) {
  ClassObject* obj = nullptr;
  std::string_view prop = name;
  size_t dot = name.find('.');
  if (dot == std::string_view::npos) {
    if (NameDenotesVariable(name, ctx)) return nullptr;
    obj = ctx.CurrentThis();
  } else {
    std::string_view base = name.substr(0, dot);
    prop = name.substr(dot + 1);
    if (prop.find('.') != std::string_view::npos) return nullptr;
    const Variable* handle = ctx.FindVariable(base);
    if (handle == nullptr || StructLayoutOfName(base, ctx) != nullptr)
      return nullptr;
    obj = ctx.GetClassObject(handle->value.ToUint64());
  }
  if (obj == nullptr || obj->type == nullptr) return nullptr;
  const ClassTypeInfo::PropertyInfo* info = obj->type->FindProperty(prop);
  if (info == nullptr || info->type_name.empty()) return nullptr;
  const StructTypeInfo* layout = ctx.FindStructType(info->type_name);
  if (layout == nullptr) return nullptr;
  key = "@" + std::to_string(obj->handle) + "." + std::string(prop);
  return layout;
}

const StructTypeInfo* TaggedMemberLayout(const StructTypeInfo& sinfo,
                                         std::string_view member) {
  for (const auto& field : sinfo.fields) {
    if (field.name == member && field.nested) return field.nested;
  }
  return nullptr;
}

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

bool TryStaticStructMember(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  StaticPropertyRef ref;
  std::string path;
  if (!ResolveStaticHandlePath(expr, ctx, arena, ref, path)) return false;
  const ClassTypeInfo::PropertyInfo* prop = ref.owner->FindProperty(ref.name);
  const StructTypeInfo* layout =
      prop != nullptr ? ctx.FindStructType(prop->type_name) : nullptr;
  if (layout == nullptr) return false;
  out = ExtractStructField(*ref.slot, layout, path, arena);
  return true;
}

static const Expr* MemberChainRoot(const Expr* access, std::string& path) {
  path.clear();
  const Expr* e = access;
  while (e != nullptr && e->kind == ExprKind::kMemberAccess &&
         !e->is_scope_resolution && e->rhs != nullptr &&
         e->rhs->kind == ExprKind::kIdentifier) {
    if (!path.empty()) path.insert(0, 1, '.');
    path.insert(0, e->rhs->text);
    e = e->lhs;
  }
  return e;
}

static bool MemberChainPath(const Expr* access, std::string_view& root,
                            std::string& path) {
  const Expr* e = MemberChainRoot(access, path);
  if (e == access || e == nullptr || e->kind != ExprKind::kIdentifier)
    return false;
  root = e->text;
  return true;
}

static bool MemberChainKey(const Expr* access, std::string& key,
                           std::string& path) {
  const Expr* e = MemberChainRoot(access, path);
  if (e == access || e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) {
    key = e->text;
    return true;
  }
  if (!e->is_scope_resolution) return false;
  key = std::string(e->lhs->text) + "." + std::string(e->rhs->text);
  return true;
}

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

static const StructTypeInfo* SelectChainElementLayout(const Expr* base,
                                                      SimContext& ctx) {
  const Expr* root = base;
  while (root != nullptr && root->kind == ExprKind::kSelect &&
         root->index_end == nullptr) {
    root = root->base;
  }
  if (root == nullptr || root->kind != ExprKind::kIdentifier) return nullptr;
  return StructLayoutOfName(root->text, ctx);
}

const StructTypeInfo* ContainerElementLayout(const Expr* base,
                                             SimContext& ctx) {
  if (base == nullptr) return nullptr;
  if (base->kind == ExprKind::kSelect) {
    return SelectChainElementLayout(base, ctx);
  }
  if (base->kind == ExprKind::kIdentifier) {
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

bool PropertyPackedMemberBits(const Expr* access, const ClassObject* obj,
                              SimContext& ctx, PackedMemberBits& out) {
  std::string path;
  if (access == nullptr || obj == nullptr ||
      access->kind != ExprKind::kMemberAccess ||
      !MemberChainPath(access, out.prop, path)) {
    return false;
  }
  const StructTypeInfo* info = PropertyStructLayout(obj, out.prop, ctx);
  if (info == nullptr || !info->is_packed) return false;
  out.offset = 0;
  const StructFieldInfo* field = ResolveStructField(info, path, &out.offset);
  if (field == nullptr) return false;
  out.width = field->width;
  return true;
}

const StructTypeInfo* StructLayoutOfOperand(const Expr* e, SimContext& ctx) {
  if (e == nullptr) return nullptr;
  if (e->kind == ExprKind::kIdentifier) return StructLayoutOfName(e->text, ctx);
  std::string_view name;
  std::string path;
  if (e->kind != ExprKind::kMemberAccess || !MemberChainPath(e, name, path))
    return nullptr;
  if (path.find('.') == std::string::npos) {
    Variable* var = ctx.FindVariable(name);
    ClassObject* obj = name == "this" ? ctx.CurrentThis() : nullptr;
    if (var != nullptr && !ctx.GetVariableClassType(name).empty())
      obj = ctx.GetClassObject(var->value.ToUint64());
    if (obj != nullptr) return PropertyStructLayout(obj, path, ctx);
  }
  StructRoot root;
  if (!FindStructRoot(name, path, ctx, root)) return nullptr;
  if (path.empty()) return root.info;
  uint32_t offset = 0;
  const StructFieldInfo* field = ResolveStructField(root.info, path, &offset);
  return field != nullptr ? field->nested : nullptr;
}

QueueObject* ResolveStructDynMember(const Expr* access, SimContext& ctx,
                                    Arena& arena, bool write) {
  std::string_view name;
  std::string path;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      !MemberChainPath(access, name, path)) {
    return nullptr;
  }
  StructRoot root;
  if (!FindStructRoot(name, path, ctx, root)) return nullptr;
  uint32_t offset = 0;
  const StructFieldInfo* field = ResolveStructField(root.info, path, &offset);
  if (field == nullptr || !field->is_dynamic) return nullptr;
  if (!write) {
    QueueObject* held = DynMemberQueue(
        ExtractBitField(arena, *root.value, offset, field->width));
    return held != nullptr ? held : DynMemberEmpty(*field);
  }
  QueueObject* copy = DynMemberForWrite(*root.value, offset, *field, arena);
  if (root.var != nullptr) root.var->NotifyWatchers();
  return copy;
}

const StructFieldInfo* ResolveStructMember(const Expr* access,
                                           SimContext& ctx) {
  if (access == nullptr || access->kind != ExprKind::kMemberAccess)
    return nullptr;
  std::string key;
  std::string path;
  if (!MemberChainKey(access, key, path)) return nullptr;
  StructRoot root;
  if (!FindStructRoot(key, path, ctx, root)) return nullptr;
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
  out.is_string = field->type_kind == DataTypeKind::kString;
  Logic4Vec idx = EvalExpr(select->index, ctx, arena);
  if (!idx.IsKnown()) return true;
  auto i = static_cast<int64_t>(idx.ToUint64());
  int64_t pos = field->elem_left <= field->elem_right ? i - field->elem_left
                                                      : field->elem_left - i;
  if (pos < 0 || pos >= static_cast<int64_t>(field->elem_count)) return true;
  out.bit_offset =
      offset + (field->elem_count - 1 - static_cast<uint32_t>(pos)) * out.width;
  out.in_range = true;
  return true;
}

constexpr std::array kTwoStateMemberKinds = {
    DataTypeKind::kBit,    DataTypeKind::kByte,     DataTypeKind::kShortint,
    DataTypeKind::kInt,    DataTypeKind::kLongint,  DataTypeKind::kShortreal,
    DataTypeKind::kReal,   DataTypeKind::kRealtime, DataTypeKind::kString,
    DataTypeKind::kChandle};

static bool LayoutIsTwoState(const StructTypeInfo& layout, SimContext& ctx);

bool MemberIsTwoState(const StructFieldInfo& f, SimContext& ctx) {
  if (f.nested != nullptr) return LayoutIsTwoState(*f.nested, ctx);
  DataTypeKind kind = f.type_kind == DataTypeKind::kNamed
                          ? ctx.FindTypeKind(f.type_name)
                          : f.type_kind;
  return std::ranges::find(kTwoStateMemberKinds, kind) !=
         kTwoStateMemberKinds.end();
}

static bool LayoutIsTwoState(const StructTypeInfo& layout, SimContext& ctx) {
  return std::ranges::all_of(layout.fields, [&](const StructFieldInfo& f) {
    return MemberIsTwoState(f, ctx);
  });
}

static void ClearTwoStateMembers(Logic4Vec& value, const StructTypeInfo& layout,
                                 uint32_t base, SimContext& ctx, Arena& arena) {
  size_t count = layout.is_union ? 1 : layout.fields.size();
  for (size_t i = 0; i < count; ++i) {
    const StructFieldInfo& f = layout.fields[i];
    if (f.nested != nullptr && !f.nested->is_packed) {
      ClearTwoStateMembers(value, *f.nested, base + f.bit_offset, ctx, arena);
    } else if (MemberIsTwoState(f, ctx)) {
      DepositBitField(value, base + f.bit_offset,
                      MakeLogic4VecVal(arena, f.width, 0), f.width);
    }
  }
}

Logic4Vec NonexistentAggregateElement(const StructTypeInfo& layout,
                                      SimContext& ctx, Arena& arena) {
  Logic4Vec value = MakeAllX(arena, layout.total_width);
  ClearTwoStateMembers(value, layout, 0, ctx, arena);
  ApplyLayoutDefaults(value, layout, 0, ctx, arena);
  return value;
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
  if (field->type_kind == DataTypeKind::kString) {
    out = StringMemberText(out, arena);
    return true;
  }
  out.is_real = field->type_kind == DataTypeKind::kReal ||
                field->type_kind == DataTypeKind::kShortreal ||
                field->type_kind == DataTypeKind::kRealtime;
  out.is_signed = field->is_signed && !out.is_real;
  return true;
}

}  // namespace delta
