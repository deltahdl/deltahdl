#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_callee_declaration.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

Logic4Vec ClassEnumLiteral(const ClassTypeInfo& cls, const std::string& name,
                           uint64_t value, Arena& arena) {
  auto it = cls.enum_literal_shapes.find(name);
  ClassTypeInfo::EnumLiteralShape shape =
      it == cls.enum_literal_shapes.end() ? ClassTypeInfo::EnumLiteralShape{}
                                          : it->second;
  Logic4Vec v = MakeLogic4VecVal(arena, shape.width, value);
  v.is_signed = shape.is_signed;
  return v;
}

bool TryClassScopeEnumLiteral(std::string_view name, const ClassTypeInfo* cls,
                              Arena& arena, Logic4Vec& out) {
  for (; cls != nullptr; cls = cls->parent) {
    auto it = cls->enum_members.find(std::string(name));
    if (it == cls->enum_members.end()) continue;
    out = ClassEnumLiteral(*cls, it->first, it->second, arena);
    return true;
  }
  return false;
}

static Logic4Vec MemberValue(const EnumMemberInfo& m, const EnumTypeInfo& info,
                             Arena& arena) {
  Logic4Vec v = MakeLogic4VecVal(arena, info.width, m.value);
  v.words[0].bval = m.xz;
  v.is_signed = info.is_signed;
  return v;
}

static Logic4Vec EnumFirst(const EnumTypeInfo& info, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  return MemberValue(info.members.front(), info, arena);
}

static Logic4Vec EnumLast(const EnumTypeInfo& info, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  return MemberValue(info.members.back(), info, arena);
}

static bool IsMemberValue(const EnumMemberInfo& m, uint32_t width,
                          Logic4Word current) {
  uint64_t mask =
      width == 0 || width >= 64 ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  return (m.value & mask) == current.aval && m.xz == current.bval;
}

static Logic4Vec EnumDefault(const EnumTypeInfo& info, Arena& arena) {
  Logic4Vec v = MakeLogic4Vec(arena, info.width);
  if (!info.is_4state) return v;
  for (uint32_t i = 0; i < v.nwords; ++i) {
    uint32_t bits = std::min<uint32_t>(64, info.width - i * 64);
    uint64_t mask = bits >= 64 ? ~uint64_t{0} : (uint64_t{1} << bits) - 1;
    v.words[i].aval = mask;
    v.words[i].bval = mask;
  }
  return v;
}

static int FindMemberIndex(const EnumTypeInfo& info, Logic4Word current) {
  for (size_t i = 0; i < info.members.size(); ++i) {
    if (IsMemberValue(info.members[i], info.width, current))
      return static_cast<int>(i);
  }
  return -1;
}

static Logic4Vec EnumNext(const EnumTypeInfo& info, Logic4Word current,
                          uint32_t count, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  int idx = FindMemberIndex(info, current);
  if (idx < 0) return EnumDefault(info, arena);
  auto n = static_cast<int>(info.members.size());
  int new_idx = (idx + static_cast<int>(count % n)) % n;
  return MemberValue(info.members[new_idx], info, arena);
}

static Logic4Vec EnumPrev(const EnumTypeInfo& info, Logic4Word current,
                          uint32_t count, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  int idx = FindMemberIndex(info, current);
  if (idx < 0) return EnumDefault(info, arena);
  auto n = static_cast<int>(info.members.size());
  int offset = static_cast<int>(count % n);
  int new_idx = ((idx - offset) % n + n) % n;
  return MemberValue(info.members[new_idx], info, arena);
}

static Logic4Vec EnumNum(const EnumTypeInfo& info, Arena& arena) {
  return MakeLogic4VecVal(arena, 32, info.members.size());
}

static Logic4Vec EnumName(const EnumTypeInfo& info, Logic4Word current,
                          Arena& arena) {
  for (auto& m : info.members) {
    if (!IsMemberValue(m, info.width, current)) continue;
    auto name = m.name;
    uint32_t width = static_cast<uint32_t>(name.size()) * 8;
    if (width == 0) width = 8;
    auto vec = MakeLogic4Vec(arena, width);
    for (size_t i = 0; i < name.size(); ++i) {
      auto byte_idx = static_cast<uint32_t>(name.size() - 1 - i);
      uint32_t word = (byte_idx * 8) / 64;
      uint32_t bit = (byte_idx * 8) % 64;
      vec.words[word].aval |= static_cast<uint64_t>(name[i]) << bit;
    }
    return vec;
  }

  return MakeLogic4VecVal(arena, 8, 0);
}

static uint32_t ParseStepCount(const Expr* call_expr, SimContext& ctx,
                               Arena& arena) {
  if (call_expr->args.empty()) return 1;
  return static_cast<uint32_t>(
      EvalExpr(call_expr->args[0], ctx, arena).ToUint64());
}

struct EnumMethodArgs {
  const EnumTypeInfo& info;
  Logic4Word current;
  const Expr* call_expr;
  SimContext& ctx;
  Arena& arena;
};

static bool DispatchEnumMethod(std::string_view method,
                               const EnumMethodArgs& args, Logic4Vec& out) {
  if (method == "first") {
    out = EnumFirst(args.info, args.arena);
    return true;
  }
  if (method == "last") {
    out = EnumLast(args.info, args.arena);
    return true;
  }
  if (method == "next") {
    uint32_t count = ParseStepCount(args.call_expr, args.ctx, args.arena);
    out = EnumNext(args.info, args.current, count, args.arena);
    return true;
  }
  if (method == "prev") {
    uint32_t count = ParseStepCount(args.call_expr, args.ctx, args.arena);
    out = EnumPrev(args.info, args.current, count, args.arena);
    return true;
  }
  if (method == "num") {
    out = EnumNum(args.info, args.arena);
    return true;
  }
  if (method == "name") {
    out = EnumName(args.info, args.current, args.arena);
    return true;
  }
  return false;
}

struct DeclScope {
  const ClassTypeInfo* cls = nullptr;
  std::string_view package;
};

static const EnumTypeInfo* ScopedEnumType(std::string_view scope,
                                          std::string_view type_name,
                                          SimContext& ctx) {
  if (scope.empty()) return nullptr;
  return ctx.FindEnumType(std::string(scope) + "::" + std::string(type_name));
}

static const EnumTypeInfo* ClassScopedEnumType(const ClassTypeInfo* cls,
                                               std::string_view type_name,
                                               SimContext& ctx) {
  for (; cls != nullptr; cls = cls->enclosing) {
    for (const ClassTypeInfo* c = cls; c != nullptr; c = c->parent) {
      if (const auto* info = ScopedEnumType(c->name, type_name, ctx))
        return info;
    }
  }
  return nullptr;
}

static const EnumTypeInfo* EnumTypeOfDeclaredType(const DataType& type,
                                                  const DeclScope& scope,
                                                  SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed || type.type_name.empty())
    return nullptr;
  if (const auto* info = ScopedEnumType(type.scope_name, type.type_name, ctx))
    return info;
  if (const auto* info = ClassScopedEnumType(scope.cls, type.type_name, ctx))
    return info;
  std::string_view package =
      scope.cls != nullptr ? scope.cls->package : scope.package;
  if (const auto* info = ScopedEnumType(package, type.type_name, ctx))
    return info;
  return ctx.FindEnumType(type.type_name);
}

const EnumTypeInfo* EnumTypeOfDataType(const DataType& type, SimContext& ctx) {
  return EnumTypeOfDeclaredType(type, {ctx.CurrentMethodClass(), {}}, ctx);
}

void RecordVariableEnumType(std::string_view var_name, const DataType& type,
                            SimContext& ctx) {
  const EnumTypeInfo* info = EnumTypeOfDataType(type, ctx);
  if (info == nullptr) return;
  ctx.SetVariableEnumType(var_name, info->type_name);
}

static bool ReturnsTheEnumType(std::string_view method) {
  return method == "first" || method == "last" || method == "next" ||
         method == "prev";
}

static const DataType* HeaderParamDeclaredType(const ClassDecl* decl,
                                               std::string_view name) {
  if (decl->type_param_names.count(name) != 0) return nullptr;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (decl->params[i].first != name) continue;
    return i < decl->param_types.size() ? &decl->param_types[i] : nullptr;
  }
  return nullptr;
}

static const DataType* ClassMemberDeclaredType(const ClassTypeInfo* cls,
                                               std::string_view name,
                                               const ClassTypeInfo*& declarer) {
  for (const ClassTypeInfo* c = cls; c != nullptr; c = c->parent) {
    if (c->decl == nullptr) continue;
    if (const DataType* type = HeaderParamDeclaredType(c->decl, name)) {
      declarer = c;
      return type;
    }
    for (const ClassMember* m : c->decl->members) {
      if (m->kind != ClassMemberKind::kProperty || m->name != name) continue;
      if (!m->unpacked_dims.empty()) return nullptr;
      declarer = c;
      return &m->data_type;
    }
  }
  return nullptr;
}

static const EnumTypeInfo* EnumTypeOfClassMember(const ClassTypeInfo* cls,
                                                 std::string_view name,
                                                 SimContext& ctx) {
  const ClassTypeInfo* declarer = nullptr;
  const DataType* type = ClassMemberDeclaredType(cls, name, declarer);
  if (type == nullptr) return nullptr;
  if (type->kind == DataTypeKind::kEnum)
    return ctx.FindEnumType(ClassInlineEnumKey(declarer->name, name));
  return EnumTypeOfDeclaredType(*type, {declarer, {}}, ctx);
}

static const ClassTypeInfo* BareNameClassScope(std::string_view name,
                                               SimContext& ctx) {
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  if (method_cls != nullptr) {
    const ClassTypeInfo* owner = method_cls->StaticPropertyOwner(name);
    return owner != nullptr ? owner : method_cls;
  }
  const ClassObject* self = ctx.CurrentThis();
  return self != nullptr ? self->type : nullptr;
}

static const EnumTypeInfo* EnumTypeOfLiteral(std::string_view name,
                                             const ClassTypeInfo* cls,
                                             SimContext& ctx) {
  for (; cls != nullptr; cls = cls->enclosing) {
    if (const auto* info = ctx.FindEnumTypeDeclaringMember(name, cls->name))
      return info;
  }
  return ctx.FindEnumTypeDeclaringMember(name, {});
}

static const EnumTypeInfo* VariableEnumTypeInScope(const std::string& key,
                                                   SimContext& ctx) {
  if (ctx.FindLocalVariable(key) == nullptr) {
    std::string prefixed = ctx.ActiveInstancePrefix() + key;
    if (const auto* info = ctx.GetVariableEnumType(prefixed)) return info;
  }
  return ctx.GetVariableEnumType(key);
}

static const EnumTypeInfo* EnumTypeOfName(const Expr* e, SimContext& ctx) {
  if (e->text == "this" || e->text == "super") return nullptr;
  std::string key = IdentifierLookupKey(e);
  if (NameDenotesVariable(key, ctx)) {
    if (const auto* info = VariableEnumTypeInScope(key, ctx)) return info;
    return EnumTypeOfLiteral(e->text, nullptr, ctx);
  }
  const ClassTypeInfo* cls = BareNameClassScope(e->text, ctx);
  if (const auto* info = EnumTypeOfClassMember(cls, e->text, ctx)) return info;
  return EnumTypeOfLiteral(e->text, cls, ctx);
}

static const EnumTypeInfo* EnumTypeOfScopedName(std::string_view scope,
                                                std::string_view member,
                                                SimContext& ctx) {
  if (const ClassTypeInfo* cls = ctx.FindClassType(scope)) {
    if (const auto* info = EnumTypeOfClassMember(cls, member, ctx)) return info;
    return EnumTypeOfLiteral(member, cls, ctx);
  }
  std::string key = std::string(scope) + "." + std::string(member);
  if (const auto* info = ctx.GetVariableEnumType(key)) return info;
  return ctx.FindEnumTypeDeclaringMember(member, scope);
}

static const EnumTypeInfo* EnumTypeOfSubroutineResult(const Expr* callee,
                                                      SimContext& ctx,
                                                      Arena& arena) {
  if (SelectsNamedMember(callee) && callee->rhs->text == "status" &&
      NamesProcessHandle(callee->lhs, ctx, arena))
    return ctx.FindEnumType("process::state");
  CalleeDeclaration decl = DeclarationOfCallee(callee, ctx, arena);
  return EnumTypeOfDeclaredType(*decl.result, {decl.cls, decl.package}, ctx);
}

static const EnumTypeInfo* EnumTypeOfMemberAccess(const Expr* e,
                                                  SimContext& ctx,
                                                  Arena& arena) {
  if (e->lhs == nullptr || e->rhs == nullptr ||
      e->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  if (!e->is_scope_resolution) {
    if (ReturnsTheEnumType(e->rhs->text)) {
      if (const auto* info = EnumTypeOfExpr(e->lhs, ctx, arena)) return info;
    }
    if (const auto* info = EnumTypeOfClassMember(
            ClassBehindHandle(e->lhs, ctx, arena), e->rhs->text, ctx))
      return info;
    return ctx.GetStorageEnumType(
        ctx.FindVariable(HierarchicalReferenceName(e)));
  }
  if (e->lhs->kind != ExprKind::kIdentifier) return nullptr;
  return EnumTypeOfScopedName(e->lhs->text, e->rhs->text, ctx);
}

static bool IsEnumTypedMethodCall(const Expr* e) {
  const Expr* callee = e->lhs;
  return callee != nullptr && callee->kind == ExprKind::kMemberAccess &&
         !callee->is_scope_resolution && callee->rhs != nullptr &&
         callee->rhs->kind == ExprKind::kIdentifier &&
         ReturnsTheEnumType(callee->rhs->text);
}

static const EnumTypeInfo* EnumTypeOfCast(const Expr* e, SimContext& ctx) {
  const Expr* type_node = e->rhs;
  DataType type;
  type.kind = DataTypeKind::kNamed;
  if (type_node == nullptr) {
    if (e->text.empty()) return nullptr;
    type.type_name = e->text;
  } else if (type_node->kind == ExprKind::kIdentifier) {
    type.scope_name = type_node->scope_prefix;
    type.type_name = type_node->text;
  } else if (type_node->kind == ExprKind::kMemberAccess &&
             type_node->is_scope_resolution && type_node->lhs != nullptr &&
             type_node->rhs != nullptr &&
             type_node->lhs->kind == ExprKind::kIdentifier &&
             type_node->rhs->kind == ExprKind::kIdentifier) {
    type.scope_name = type_node->lhs->text;
    type.type_name = type_node->rhs->text;
  } else {
    return nullptr;
  }
  return EnumTypeOfDeclaredType(type, {ctx.CurrentMethodClass(), {}}, ctx);
}

static const EnumTypeInfo* EnumTypeOfElement(const Expr* e, SimContext& ctx,
                                             Arena& arena) {
  const EnumTypeInfo* info = EnumTypeOfExpr(e->base, ctx, arena);
  if (info == nullptr) return nullptr;
  return EvalExpr(e, ctx, arena).width == info->width ? info : nullptr;
}

const EnumTypeInfo* EnumTypeOfExpr(const Expr* e, SimContext& ctx,
                                   Arena& arena) {
  if (e == nullptr) return nullptr;
  if (e->kind == ExprKind::kIdentifier) return EnumTypeOfName(e, ctx);
  if (e->kind == ExprKind::kCast) return EnumTypeOfCast(e, ctx);
  if (e->kind == ExprKind::kSelect) return EnumTypeOfElement(e, ctx, arena);
  if (e->kind == ExprKind::kMemberAccess)
    return EnumTypeOfMemberAccess(e, ctx, arena);
  if (e->kind != ExprKind::kCall || e->lhs == nullptr) return nullptr;
  if (IsEnumTypedMethodCall(e)) {
    if (const auto* info = EnumTypeOfExpr(e->lhs->lhs, ctx, arena)) return info;
  }
  return EnumTypeOfSubroutineResult(e->lhs, ctx, arena);
}

static Logic4Word LowWord(const Logic4Vec& v) {
  return v.nwords == 0 ? Logic4Word{} : v.words[0];
}

static Logic4Word CurrentValueOfBase(const Expr* base, SimContext& ctx,
                                     Arena& arena) {
  if (base->kind == ExprKind::kIdentifier) {
    std::string key = IdentifierLookupKey(base);
    if (NameDenotesVariable(key, ctx))
      return LowWord(ctx.FindVariable(key)->value);
  }
  return LowWord(EvalExpr(base, ctx, arena));
}

static bool IsEnumMethodName(std::string_view method) {
  return ReturnsTheEnumType(method) || method == "num" || method == "name";
}

static bool TryEvalEnumMethod(const Expr* access, const Expr* call_expr,
                              SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->lhs == nullptr ||
      access->rhs == nullptr || access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (!IsEnumMethodName(access->rhs->text)) return false;
  const auto* info = EnumTypeOfExpr(access->lhs, ctx, arena);
  if (!info) return false;
  Logic4Word current = CurrentValueOfBase(access->lhs, ctx, arena);
  EnumMethodArgs args{*info, current, call_expr, ctx, arena};
  return DispatchEnumMethod(access->rhs->text, args, out);
}

bool TryEvalEnumMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  return TryEvalEnumMethod(expr->lhs, expr, ctx, arena, out);
}

bool TryEvalEnumMethodWithoutArgs(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  return TryEvalEnumMethod(expr, expr, ctx, arena, out);
}

}  // namespace delta
