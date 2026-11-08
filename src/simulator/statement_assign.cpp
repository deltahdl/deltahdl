#include "simulator/statement_assign.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "simulator/assoc_element.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/eval_array.h"
#include "simulator/eval_class_array_handles.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/struct_string_member.h"
#include "simulator/variable.h"
#include "simulator/virtual_interface.h"

namespace delta {

struct MemberPathCursor {
  std::string key;
  std::string name;
  std::string_view path;
  const StructTypeInfo* layout = nullptr;
};

static MemberPathCursor BeginMemberPath(std::string_view base_name,
                                        const StructTypeInfo* info,
                                        std::string_view field_name,
                                        SimContext& ctx) {
  return {TagKeyOfName(base_name, ctx), std::string(base_name), field_name,
          info};
}

static bool DescendMemberPath(MemberPathCursor& c) {
  if (c.path.empty() || c.layout == nullptr) return false;
  size_t dot = c.path.find('.');
  std::string_view seg = c.path.substr(0, dot);
  const StructFieldInfo* field = FindStructField(c.layout, seg);
  if (field == nullptr) return false;
  c.key += '.';
  c.key += seg;
  c.name += '.';
  c.name += seg;
  c.path = dot == std::string_view::npos ? std::string_view{}
                                         : c.path.substr(dot + 1);
  c.layout = field->nested;
  return true;
}

UnionTagMismatch FindUnionTagMismatch(std::string_view base_name,
                                      const StructTypeInfo* info,
                                      std::string_view field_name,
                                      SimContext& ctx) {
  MemberPathCursor c = BeginMemberPath(base_name, info, field_name, ctx);
  UnionTagMismatch found;
  while (c.layout != nullptr && !c.path.empty()) {
    if (c.layout->is_union) {
      std::string_view tag = ctx.GetVariableTag(c.key);
      if (!tag.empty() && tag != c.path.substr(0, c.path.find('.'))) {
        found.union_name = c.name;
        found.member = std::string(c.path);
        found.tag = std::string(tag);
        found.found = true;
        return found;
      }
    }
    if (!DescendMemberPath(c)) break;
  }
  return found;
}

MemberLayout ResolveMemberLayout(std::string_view base_name,
                                 const StructTypeInfo* info,
                                 std::string_view field_name, SimContext& ctx) {
  MemberPathCursor c = BeginMemberPath(base_name, info, field_name, ctx);
  while (!c.path.empty()) {
    if (!DescendMemberPath(c)) return {};
  }
  MemberLayout member;
  member.layout = c.layout;
  if (c.layout != nullptr && c.layout->is_union) {
    member.tag = std::string(ctx.GetVariableTag(c.key));
  }
  return member;
}

static bool TaggedUnionTagMismatch(std::string_view base_name,
                                   const StructTypeInfo* info,
                                   std::string_view field_name, SimContext& ctx,
                                   SourceLoc loc) {
  UnionTagMismatch m = FindUnionTagMismatch(base_name, info, field_name, ctx);
  if (!m.found) return false;
  ctx.GetDiag().Error(loc,
                      "run-time error: assigning member '" + m.member +
                          "' of tagged union '" + m.union_name +
                          "' which currently has tag '" + m.tag + "'",
                      Subclause("11.9"));
  return true;
}

static const ClassTypeInfo::PropertyInfo* FindPropertyInfo(
    const ClassTypeInfo* type, std::string_view name) {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    for (const auto& prop : t->properties) {
      if (prop.name == name) return &prop;
    }
  }
  return nullptr;
}

PropertyFieldWindow ResolveClassPropertyField(const ClassTypeInfo* type,
                                              std::string_view path,
                                              SimContext& ctx) {
  PropertyFieldWindow window;
  auto dot = path.find('.');
  if (type == nullptr || dot == std::string_view::npos) return window;
  auto first = path.substr(0, dot);
  const auto* prop = FindPropertyInfo(type, first);
  if (prop == nullptr || prop->type_name.empty()) return window;
  const StructTypeInfo* info = ctx.FindStructType(prop->type_name);
  if (info == nullptr) return window;
  if (!ResolveStructFieldPath(info, path.substr(dot + 1), &window.bit_offset,
                              &window.width, &window.member_kind)) {
    return window;
  }
  window.property = first;
  window.total_width = info->total_width;
  window.valid = true;
  return window;
}

Logic4Vec CoerceToPropertyType(const ClassTypeInfo* type, std::string_view name,
                               Logic4Vec val, Arena& arena) {
  val = OwnRhsWords(val, arena);
  const auto* prop = FindPropertyInfo(type, name);
  if (prop == nullptr || !prop->width_is_declared) return val;
  val = ConvertRealForKnownLhs(val, prop->is_real, prop->width, arena);
  if (!prop->is_4state && !prop->is_real) CoerceTo2State(val);
  if (!prop->is_real) val.is_signed = prop->is_signed;
  return val;
}

static void SetClassField(ClassObject* obj, const ClassTypeInfo* declared_type,
                          std::string_view field, const Logic4Vec& rhs_val,
                          Arena& arena) {
  const ClassTypeInfo* start = declared_type ? declared_type : obj->type;
  Logic4Vec stored = CoerceToPropertyType(start, field, rhs_val, arena);
  if (declared_type)
    obj->SetPropertyForType(field, declared_type, stored);
  else
    obj->SetProperty(std::string(field), stored);
}

static FieldTarget StaticPropertyTarget(const ClassTypeInfo* cls,
                                        std::string_view field_name);

static const ClassTypeInfo* HandlePropertyClass(const ClassTypeInfo* holder,
                                                std::string_view name,
                                                const ClassObject* next,
                                                SimContext& ctx) {
  const ClassTypeInfo::PropertyInfo* prop =
      holder != nullptr ? holder->FindProperty(name) : nullptr;
  if (prop != nullptr && !prop->type_name.empty()) {
    if (const ClassTypeInfo* declared = ctx.FindClassType(prop->type_name))
      return declared;
  }
  return next->type;
}

static FieldTarget ResolveClassFieldTarget(ClassObject* obj,
                                           const ClassTypeInfo* declared_type,
                                           std::string_view field_path,
                                           SimContext& ctx) {
  auto dot = field_path.find('.');
  if (dot != std::string_view::npos) {
    auto& arena = ctx.GetArena();
    auto first = field_path.substr(0, dot);
    PropertyFieldWindow window = ResolveClassPropertyField(
        declared_type ? declared_type : obj->type, field_path, ctx);
    if (window.valid) {
      FieldTarget bits;
      bits.kind = FieldTarget::Kind::kPropertyBits;
      bits.obj = obj;
      bits.type = declared_type;
      bits.field = std::string(window.property);
      bits.bit_offset = window.bit_offset;
      bits.width = window.width;
      bits.member_kind = window.member_kind;
      bits.holder_width = window.total_width;
      return bits;
    }
    Logic4Vec handle_val =
        declared_type ? obj->GetPropertyForType(first, declared_type, arena)
                      : obj->GetProperty(first, arena);
    if (auto* next_obj = ctx.GetClassObject(handle_val.ToUint64())) {
      return ResolveClassFieldTarget(
          next_obj,
          HandlePropertyClass(declared_type ? declared_type : obj->type, first,
                              next_obj, ctx),
          field_path.substr(dot + 1), ctx);
    }
  }
  const ClassTypeInfo* scope = declared_type ? declared_type : obj->type;
  if (scope != nullptr && scope->StaticPropertyDeclarer(field_path) != nullptr)
    return StaticPropertyTarget(scope, field_path);
  FieldTarget target;
  target.kind = FieldTarget::Kind::kProperty;
  target.obj = obj;
  target.type = declared_type;
  target.field = std::string(field_path);
  return target;
}

static FieldTarget ResolveClassObjectField(Variable* base_var,
                                           std::string_view base_name,
                                           std::string_view field_name,
                                           SimContext& ctx) {
  auto* obj = ctx.GetClassObject(base_var->value.ToUint64());
  if (!obj) return {};
  const ClassTypeInfo* declared_type = nullptr;
  auto declared = ctx.GetVariableClassType(base_name);
  if (!declared.empty()) declared_type = ctx.FindClassType(declared);
  FieldTarget target =
      ResolveClassFieldTarget(obj, declared_type, field_name, ctx);
  target.notify = base_var;
  return target;
}

static FieldTarget ResolveOwnPropertyTarget(std::string_view field_name,
                                            SimContext& ctx) {
  auto* self = ctx.CurrentThis();
  if (!self) return {};
  FieldTarget target;
  target.kind = FieldTarget::Kind::kProperty;
  target.obj = self;
  target.type = ctx.CurrentMethodClass();
  target.field = std::string(field_name);
  return target;
}

static FieldTarget ResolveOwnPropertyMemberTarget(std::string_view base_name,
                                                  std::string_view field_name,
                                                  SimContext& ctx,
                                                  bool* handled) {
  *handled = false;
  auto* self = ctx.CurrentThis();
  if (self == nullptr || NameDenotesVariable(base_name, ctx)) return {};
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  const ClassTypeInfo* start = enclosing != nullptr ? enclosing : self->type;
  if (FindPropertyInfo(start, base_name.substr(0, base_name.find('['))) ==
      nullptr) {
    return {};
  }
  *handled = true;
  std::string path = std::string(base_name) + "." + std::string(field_name);
  return ResolveClassFieldTarget(self, enclosing, path, ctx);
}

static FieldTarget StaticPropertyTarget(const ClassTypeInfo* cls,
                                        std::string_view field_name);

FieldTarget ResolveBarePropertyTarget(std::string_view name, SimContext& ctx) {
  auto* self = ctx.CurrentThis();
  if (self != nullptr && self->type != nullptr &&
      self->type->FindProperty(name) != nullptr) {
    return ResolveOwnPropertyTarget(name, ctx);
  }
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  const ClassTypeInfo* owner =
      method_cls != nullptr ? method_cls->StaticPropertyOwner(name) : nullptr;
  return owner != nullptr ? StaticPropertyTarget(owner, name) : FieldTarget{};
}

static FieldTarget ResolveThisField(std::string_view base_name,
                                    std::string_view field_name,
                                    SimContext& ctx, bool* handled) {
  *handled = false;
  if (base_name != "this") return {};
  *handled = true;
  auto* self = ctx.CurrentThis();
  if (self != nullptr && field_name.find('.') != std::string_view::npos) {
    return ResolveClassFieldTarget(self, ctx.CurrentMethodClass(), field_name,
                                   ctx);
  }
  return ResolveOwnPropertyTarget(field_name, ctx);
}

static FieldTarget ResolveSuperField(std::string_view base_name,
                                     std::string_view field_name,
                                     SimContext& ctx, bool* handled) {
  *handled = false;
  if (base_name != "super") return {};
  *handled = true;
  auto* self = ctx.CurrentThis();
  if (!(self && self->type && self->type->parent)) return {};
  FieldTarget target;
  target.kind = FieldTarget::Kind::kProperty;
  target.obj = self;
  target.type = self->type->parent;
  target.field = std::string(field_name);
  return target;
}

static FieldTarget StaticPropertyTarget(const ClassTypeInfo* cls,
                                        std::string_view field_name) {
  const ClassTypeInfo* declarer = cls->StaticPropertyDeclarer(field_name);
  if (declarer == nullptr) return {};
  FieldTarget target;
  target.kind = FieldTarget::Kind::kStatic;
  target.type = declarer;
  target.slot =
      &declarer->static_properties.find(std::string(field_name))->second;
  target.field = std::string(field_name);
  return target;
}

static FieldTarget ResolveSpecializationStaticField(const Expr* lhs,
                                                    SimContext& ctx,
                                                    bool* handled) {
  *handled = false;
  if (lhs->kind != ExprKind::kMemberAccess || !lhs->is_scope_resolution ||
      lhs->rhs == nullptr || lhs->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  const ClassTypeInfo* spec =
      ScopeNamedSpecialization(lhs->lhs, ctx, ctx.GetArena());
  if (spec == nullptr) return {};
  *handled = true;
  return StaticPropertyTarget(spec, lhs->rhs->text);
}

static FieldTarget ResolveStaticClassField(std::string_view base_name,
                                           std::string_view field_name,
                                           SimContext& ctx, bool* handled) {
  *handled = false;
  auto* cls_type = ctx.FindClassType(base_name);
  if (!cls_type) return {};
  *handled = true;
  return StaticPropertyTarget(cls_type, field_name);
}

static FieldTarget ResolveStaticHandleField(const Expr* lhs, SimContext& ctx,
                                            bool* handled) {
  *handled = false;
  StaticPropertyRef ref;
  std::string path;
  if (!ResolveStaticHandlePath(lhs, ctx, ctx.GetArena(), ref, path)) return {};
  std::string_view declared_key;
  ClassObject* obj = StaticPropertyObject(ref, ctx, &declared_key);
  if (obj == nullptr) return {};
  *handled = true;
  return ResolveClassFieldTarget(obj, ctx.FindClassType(declared_key), path,
                                 ctx);
}

static FieldTarget ResolvePackageClassStaticField(const Expr* lhs,
                                                  SimContext& ctx,
                                                  bool* handled) {
  *handled = false;
  std::string_view member;
  const ClassTypeInfo* cls = PackageQualifiedClassOf(lhs, ctx, member);
  if (cls == nullptr) return {};
  *handled = true;
  return StaticPropertyTarget(cls, member);
}

static FieldTarget ResolveVirtualInterfaceField(const Expr* lhs,
                                                SimContext& ctx, bool report,
                                                bool* handled) {
  *handled = false;
  if (lhs->kind != ExprKind::kMemberAccess || lhs->is_scope_resolution ||
      lhs->rhs == nullptr || lhs->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  VirtualInterfaceBase base =
      ResolveVirtualInterfaceBaseExpr(lhs->lhs, ctx, ctx.GetArena());
  std::string field(lhs->rhs->text);
  if (!base.is_virtual_interface) {
    base = ResolveVirtualInterfaceInnerPath(lhs, ctx, ctx.GetArena(), field);
  }
  if (!base.is_virtual_interface) return {};
  *handled = true;
  if (base.handle == kNullVirtualInterface) {
    if (report) ReportNullVirtualInterface(lhs->range.start, ctx);
    FieldTarget target;
    target.kind = FieldTarget::Kind::kNoOp;
    return target;
  }
  auto* component =
      ctx.FindVariable(VirtualInterfaceComponentName(base.handle, field, ctx));
  if (!component) return {};
  FieldTarget target;
  target.kind = FieldTarget::Kind::kVariable;
  target.var = component;
  return target;
}

static FieldTarget ResolveVariableField(std::string_view base_name,
                                        std::string_view field_name,
                                        SimContext& ctx, SourceLoc loc) {
  auto* base_var = ctx.FindVariable(base_name);
  if (!base_var) return {};
  const StructTypeInfo* info = StructLayoutOfName(base_name, ctx);
  if (info) {
    FieldTarget target;
    if (TaggedUnionTagMismatch(base_name, info, field_name, ctx, loc)) {
      target.kind = FieldTarget::Kind::kNoOp;
      return target;
    }
    if (ResolveStructFieldPath(info, field_name, &target.bit_offset,
                               &target.width, &target.member_kind)) {
      target.kind = FieldTarget::Kind::kBits;
      target.var = base_var;
      return target;
    }
  }
  return ResolveClassObjectField(base_var, base_name, field_name, ctx);
}

static size_t FieldTargetSplit(const Expr* lhs, const std::string& name) {
  const Expr* root = lhs;
  while (root->kind == ExprKind::kMemberAccess && !root->is_scope_resolution &&
         root->lhs != nullptr) {
    root = root->lhs;
  }
  bool scoped_root = root != lhs && root->kind == ExprKind::kMemberAccess &&
                     root->is_scope_resolution && root->lhs != nullptr &&
                     root->lhs->kind == ExprKind::kIdentifier &&
                     root->rhs != nullptr &&
                     root->rhs->kind == ExprKind::kIdentifier;
  if (scoped_root) return root->lhs->text.size() + 1 + root->rhs->text.size();
  return name.find('.');
}

static FieldTarget ResolveExpressionFieldTarget(const Expr* lhs,
                                                SimContext& ctx, bool report,
                                                bool* handled) {
  FieldTarget target = ResolveVirtualInterfaceField(lhs, ctx, report, handled);
  if (*handled) return target;
  target = ResolvePackageClassStaticField(lhs, ctx, handled);
  if (*handled) return target;
  target = ResolveStaticHandleField(lhs, ctx, handled);
  if (*handled) return target;
  target = ResolveSpecializationStaticField(lhs, ctx, handled);
  if (*handled) return target;
  const ClassTypeInfo* declared = nullptr;
  ClassObject* obj =
      DeclaredArrayElementObject(lhs, ctx, ctx.GetArena(), declared);
  *handled = obj != nullptr;
  return *handled ? ResolveClassFieldTarget(obj, declared, lhs->rhs->text, ctx)
                  : target;
}

static FieldTarget ResolveFieldTargetOf(const Expr* lhs, SimContext& ctx,
                                        bool report) {
  bool handled = false;
  FieldTarget target = ResolveExpressionFieldTarget(lhs, ctx, report, &handled);
  if (handled) return target;

  std::string name;
  BuildLhsName(lhs, name);
  auto dot = FieldTargetSplit(lhs, name);
  if (dot == std::string::npos) return {};
  auto base_name = std::string_view(name).substr(0, dot);
  auto field_name = std::string_view(name).substr(dot + 1);

  target = ResolveThisField(base_name, field_name, ctx, &handled);
  if (handled) return target;
  target = ResolveSuperField(base_name, field_name, ctx, &handled);
  if (handled) return target;
  target = ResolveStaticClassField(base_name, field_name, ctx, &handled);
  if (handled) return target;
  target = ResolveOwnPropertyMemberTarget(base_name, field_name, ctx, &handled);
  if (handled) return target;
  target = ResolveVariableField(base_name, field_name, ctx, lhs->range.start);
  if (target.kind != FieldTarget::Kind::kNone) return target;
  size_t split = MemberPathSplit(name, ctx);
  if (split == dot) return target;
  return ResolveVariableField(std::string_view(name).substr(0, split),
                              std::string_view(name).substr(split + 1), ctx,
                              lhs->range.start);
}

static void WriteWholeVariable(Variable* var, const Logic4Vec& val,
                               Arena& arena) {
  if (var->is_forced) return;
  if (var->is_string) {
    var->value = StripStringZeros(val, arena);
    var->NotifyWatchers();
    return;
  }
  var->value = ResizeToWidth(val, var->value.width, arena);
  if (!var->is_4state) CoerceTo2State(var->value);
  var->NotifyWatchers();
}

static Logic4Vec WidenToHolder(Logic4Vec held, uint32_t holder_width,
                               Arena& arena) {
  if (held.width >= holder_width) return held;
  held.is_signed = false;
  return ResizeToWidth(held, holder_width, arena);
}

void WriteResolvedField(const FieldTarget& target, const Logic4Vec& rhs_val,
                        SimContext& ctx, Arena& arena) {
  switch (target.kind) {
    case FieldTarget::Kind::kBits:
      DepositBitField(target.var->value, target.bit_offset,
                      MemberBitsOf(rhs_val, target.member_kind, arena),
                      target.width);
      target.var->NotifyWatchers();
      return;
    case FieldTarget::Kind::kVariable:
      WriteWholeVariable(target.var, rhs_val, arena);
      return;
    case FieldTarget::Kind::kProperty:
      SetClassField(target.obj, target.type, target.field, rhs_val, arena);
      if (target.notify) target.notify->NotifyWatchers();
      if (target.obj) ctx.NotifyClassHandleWatchers(target.obj->handle);
      return;
    case FieldTarget::Kind::kPropertyBits: {
      Logic4Vec held =
          target.type
              ? target.obj->GetPropertyForType(target.field, target.type, arena)
              : target.obj->GetProperty(target.field, arena);
      Logic4Vec updated =
          WidenToHolder(OwnRhsWords(held, arena), target.holder_width, arena);
      DepositBitField(updated, target.bit_offset,
                      MemberBitsOf(rhs_val, target.member_kind, arena),
                      target.width);
      SetClassField(target.obj, target.type, target.field, updated, arena);
      if (target.notify) target.notify->NotifyWatchers();
      if (target.obj) ctx.NotifyClassHandleWatchers(target.obj->handle);
      return;
    }
    case FieldTarget::Kind::kStatic:
      *target.slot =
          CoerceToPropertyType(target.type, target.field, rhs_val, arena);
      target.type->NotifyStaticWatchers();
      return;
    case FieldTarget::Kind::kNone:
    case FieldTarget::Kind::kNoOp:
      return;
  }
}

static FieldTarget SelectBaseFieldTarget(const Expr* base, SimContext& ctx) {
  if (base->kind == ExprKind::kMemberAccess)
    return ResolveFieldTarget(base, ctx);
  if (base->kind == ExprKind::kIdentifier &&
      !NameDenotesVariable(base->text, ctx))
    return ResolveBarePropertyTarget(base->text, ctx);
  return {};
}

bool TryWriteClassPropertyBits(const Expr* lhs, const Logic4Vec& rhs_val,
                               SimContext& ctx, Arena& arena) {
  if (!lhs || lhs->kind != ExprKind::kSelect || !lhs->base) return false;
  FieldTarget target = SelectBaseFieldTarget(lhs->base, ctx);
  if (target.kind != FieldTarget::Kind::kProperty || target.obj == nullptr)
    return false;
  const ClassTypeInfo* start = target.type ? target.type : target.obj->type;
  const auto* prop = FindPropertyInfo(start, target.field);
  if (prop == nullptr || !prop->width_is_declared || prop->is_real)
    return false;

  Variable elem;
  elem.value = target.type ? target.obj->GetPropertyForType(target.field,
                                                            target.type, arena)
                           : target.obj->GetProperty(target.field, arena);
  elem.is_4state = prop->is_4state;
  elem.is_signed = prop->is_signed;
  if (auto range = PropertyDeclaredRange(start, target.field, elem.value.width,
                                         ctx, arena)) {
    elem.packed_range = *range;
    elem.has_packed_range = true;
  }
  WriteBitSelect(&elem, lhs, rhs_val, ctx, arena);
  SetClassField(target.obj, target.type, target.field, elem.value, arena);
  if (target.notify) target.notify->NotifyWatchers();
  ctx.NotifyClassHandleWatchers(target.obj->handle);
  return true;
}

static uint32_t FieldTargetWidth(const FieldTarget& target) {
  switch (target.kind) {
    case FieldTarget::Kind::kBits:
      return target.width;
    case FieldTarget::Kind::kVariable:
      return target.var != nullptr ? target.var->value.width : 0;
    case FieldTarget::Kind::kProperty: {
      const ClassTypeInfo* start =
          target.type ? target.type : (target.obj ? target.obj->type : nullptr);
      const auto* prop = FindPropertyInfo(start, target.field);
      return (prop != nullptr && prop->width_is_declared) ? prop->width : 0;
    }
    case FieldTarget::Kind::kPropertyBits:
      return target.width;
    case FieldTarget::Kind::kStatic:
      return target.slot != nullptr ? target.slot->width : 0;
    case FieldTarget::Kind::kNone:
    case FieldTarget::Kind::kNoOp:
      return 0;
  }
  return 0;
}

FieldTarget ResolveFieldTarget(const Expr* lhs, SimContext& ctx) {
  return ResolveFieldTargetOf(lhs, ctx, true);
}

uint32_t FieldLhsWidth(const Expr* lhs, SimContext& ctx) {
  return FieldTargetWidth(ResolveFieldTargetOf(lhs, ctx, false));
}

bool WriteStructField(const Expr* lhs, const Logic4Vec& rhs_val,
                      SimContext& ctx, uint32_t* written_width) {
  if (TryWriteAssocMemberField(lhs, rhs_val, ctx, ctx.GetArena())) return true;
  FieldTarget target = ResolveFieldTarget(lhs, ctx);
  if (target.kind == FieldTarget::Kind::kNone) return false;
  if (written_width != nullptr) *written_width = FieldTargetWidth(target);
  WriteResolvedField(target, rhs_val, ctx, ctx.GetArena());
  return true;
}

}  // namespace delta
