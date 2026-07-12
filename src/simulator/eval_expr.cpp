#include <algorithm>
#include <cmath>
#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/clocking.h"
#include "simulator/eval_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

namespace delta {

bool ExtractMethodCallParts(const Expr* expr, MethodCallParts& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;
  out.var_name = access->lhs->text;
  out.method_name = access->rhs->text;
  return true;
}

struct ReplicateInner {
  uint64_t aval = 0;
  uint64_t bval = 0;
  uint32_t width = 0;
  bool is_string = false;
};

static ReplicateInner EvalReplicateInner(const Expr* expr, SimContext& ctx,
                                         Arena& arena) {
  ReplicateInner inner;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    auto vec = EvalExpr(elem, ctx, arena);
    // The inner expression of a replication is a self-determined
    // context, so an unbased unsized literal contributes one bit
    // (per §5.7.1) rather than its default wide carrier.
    if (elem && elem->kind == ExprKind::kUnbasedUnsizedLiteral &&
        vec.width > 1) {
      auto bit = MakeLogic4Vec(arena, 1);
      if (vec.nwords > 0) {
        bit.words[0].aval = vec.words[0].aval & 1;
        bit.words[0].bval = vec.words[0].bval & 1;
      }
      vec = bit;
    }
    parts.push_back(vec);
    if (parts.back().is_string) inner.is_string = true;
    inner.width += parts.back().width;
  }
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    // Replication copies the operand's bits verbatim, so preserve the raw
    // 4-state encoding; ToUint64() would project unknown bits to 0.
    uint64_t av = (it->nwords > 0) ? it->words[0].aval : 0;
    uint64_t bv = (it->nwords > 0) ? it->words[0].bval : 0;
    inner.aval |= av << bit_pos;
    inner.bval |= bv << bit_pos;
    bit_pos += it->width;
  }
  return inner;
}

Logic4Vec EvalReplicate(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t count = static_cast<uint32_t>(
      EvalExpr(expr->repeat_count, ctx, arena).ToUint64());
  if (count == 0) {
    EvalReplicateInner(expr, ctx, arena);
    return MakeLogic4Vec(arena, 0);
  }
  if (expr->elements.empty()) return MakeLogic4Vec(arena, 0);

  auto inner = EvalReplicateInner(expr, ctx, arena);
  uint32_t total_width = inner.width * count;
  auto result = MakeLogic4Vec(arena, total_width);
  uint32_t bit_pos = 0;
  uint32_t ew = (inner.width > 64) ? 64 : inner.width;
  for (uint32_t i = 0; i < count; ++i) {
    uint32_t word = bit_pos / 64;
    uint32_t bit = bit_pos % 64;
    if (word < result.nwords) {
      result.words[word].aval |= inner.aval << bit;
      result.words[word].bval |= inner.bval << bit;
      if (bit + ew > 64 && word + 1 < result.nwords) {
        result.words[word + 1].aval |= inner.aval >> (64 - bit);
        result.words[word + 1].bval |= inner.bval >> (64 - bit);
      }
    }
    bit_pos += inner.width;
  }
  result.is_string = inner.is_string;
  return result;
}

// Applies a real-valued unary increment/decrement by unpacking the IEEE-754
// bits of old_val, adding delta (+1.0 for ++, -1.0 for --), and repacking.
static Logic4Vec ApplyRealUnaryOp(const Logic4Vec& old_val, double delta,
                                  Arena& arena) {
  double d = 0.0;
  uint64_t bits = old_val.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  d += delta;
  std::memcpy(&bits, &d, sizeof(double));
  Logic4Vec new_val = MakeLogic4VecVal(arena, 64, bits);
  new_val.is_real = true;
  return new_val;
}

// Shared by the prefix and postfix ++/-- operators: evaluates the operand,
// computes the incremented/decremented value, writes it back to the target,
// and returns the {old, new} pair so each caller can return its own side.
struct IncDecResult {
  Logic4Vec old_val;
  Logic4Vec new_val;
};

static IncDecResult EvalIncDec(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  auto old_val = EvalExpr(expr->lhs, ctx, arena);
  Logic4Vec new_val;
  if (old_val.is_real) {
    new_val = ApplyRealUnaryOp(
        old_val, (expr->op == TokenKind::kPlusPlus) ? 1.0 : -1.0, arena);
  } else {
    uint64_t v = old_val.ToUint64();
    uint64_t nv = (expr->op == TokenKind::kPlusPlus) ? v + 1 : v - 1;
    new_val = MakeLogic4VecVal(arena, old_val.width, nv);
  }
  if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) var->value = new_val;
  } else if (expr->lhs->kind == ExprKind::kSelect) {
    TryAssocIndexedWrite(expr->lhs, new_val, ctx, arena);
  }
  return {old_val, new_val};
}

Logic4Vec EvalPrefixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  return EvalIncDec(expr, ctx, arena).new_val;
}

Logic4Vec EvalPostfixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  return EvalIncDec(expr, ctx, arena).old_val;
}

static void BuildMemberName(const Expr* expr, std::string& out) {
  if (expr->kind == ExprKind::kIdentifier) {
    if (!expr->scope_prefix.empty()) {
      out += expr->scope_prefix;
      out += ".";
    }
    out += expr->text;
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    BuildMemberName(expr->lhs, out);
    out += ".";
    BuildMemberName(expr->rhs, out);
  }
}

std::string StripRootPrefix(const std::string& name) {
  constexpr std::string_view kPrefix = "$root.";
  if (name.size() > kPrefix.size() &&
      std::string_view(name).substr(0, kPrefix.size()) == kPrefix) {
    auto rest = std::string_view(name).substr(kPrefix.size());
    auto dot = rest.find('.');
    if (dot != std::string_view::npos) return std::string(rest.substr(dot + 1));
    return std::string(rest);
  }
  return name;
}

// §7.3.1: a packed union with any 4-state member has 4-state storage, so a
// 2-state member aliases bits that may hold x/z. Reading such a member performs
// an implicit 4-state-to-2-state conversion (x/z become 0). For 2-state storage
// this is a no-op, so it is safe to apply to every 2-state member read.
static bool IsTwoStateScalarKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
      return true;
    default:
      return false;
  }
}

static Logic4Vec ExtractStructField(Variable* base_var,
                                    const StructTypeInfo* info,
                                    std::string_view field, Arena& arena) {
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  DataTypeKind kind = DataTypeKind::kLogic;
  if (ResolveStructFieldPath(info, field, &bit_offset, &width, &kind)) {
    Logic4Vec slice =
        ExtractBitField(arena, base_var->value, bit_offset, width);
    if (IsTwoStateScalarKind(kind)) {
      for (uint32_t i = 0; i < slice.nwords; ++i) {
        slice.words[i].aval &= ~slice.words[i].bval;
        slice.words[i].bval = 0;
      }
    }
    return slice;
  }
  return MakeLogic4Vec(arena, 1);
}

static bool TryCollectionAccess(std::string_view base, std::string_view field,
                                SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (TryEvalArrayProperty(base, field, ctx, arena, out)) return true;
  if (TryExecArrayPropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalQueueProperty(base, field, ctx, arena, out)) return true;
  if (TryExecQueuePropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalAssocProperty(base, field, ctx, arena, out)) return true;
  if (TryExecAssocPropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalStringProperty(base, field, ctx, arena, out)) return true;
  return false;
}

// Bundles the subject of a member access (`base_name.field_name`) together with
// the resolved base variable (when one exists) and the evaluation context. A
// single instance is built once in ResolveMemberByType and shared across the
// per-feature member-access helpers below.
struct MemberAccess {
  std::string_view base_name;
  std::string_view field_name;
  Variable* base_var;
  SimContext& ctx;
  Arena& arena;
};

// Reads field `field` from class object `obj`, honoring declared-type scoping
// (§8.15) when `declared_type` is known so a base method reads a shadowed base
// field rather than the derived one.
static Logic4Vec ReadClassField(ClassObject* obj,
                                const ClassTypeInfo* declared_type,
                                std::string_view field, Arena& arena) {
  if (declared_type)
    return obj->GetPropertyForType(field, declared_type, arena);
  return obj->GetProperty(field, arena);
}

// Resolves a (possibly chained) field path against class object `obj`. A single
// field is read directly. A chained path `first.rest` (e.g. `a.next.data` for a
// forward-typedef linked list, §6.18) fetches `first` as a class handle and
// recurses into the referenced object; the inner fields carry no declared-type
// shadowing context, so they are read by bare name. When `first` does not name
// a live class handle, the chain falls back to reading the whole dotted path as
// a single flattened key on `obj` (the legacy nested-handle storage scheme).
static Logic4Vec ResolveClassFieldChain(ClassObject* obj,
                                        const ClassTypeInfo* declared_type,
                                        std::string_view field_path,
                                        SimContext& ctx, Arena& arena) {
  auto dot = field_path.find('.');
  if (dot == std::string_view::npos) {
    return ReadClassField(obj, declared_type, field_path, arena);
  }
  auto first = field_path.substr(0, dot);
  auto rest = field_path.substr(dot + 1);
  Logic4Vec handle_val = ReadClassField(obj, declared_type, first, arena);
  auto* next_obj = ctx.GetClassObject(handle_val.ToUint64());
  if (!next_obj) {
    return ReadClassField(obj, declared_type, field_path, arena);
  }
  return ResolveClassFieldChain(next_obj, nullptr, rest, ctx, arena);
}

static bool TryClassPropertyAccess(const MemberAccess& ma, Logic4Vec& out) {
  Variable* base_var = ma.base_var;
  if (!base_var) return false;
  auto* obj = ma.ctx.GetClassObject(base_var->value.ToUint64());
  if (!obj) return false;
  const ClassTypeInfo* declared_type = nullptr;
  auto declared = ma.ctx.GetVariableClassType(ma.base_name);
  if (!declared.empty()) declared_type = ma.ctx.FindClassType(declared);
  out = ResolveClassFieldChain(obj, declared_type, ma.field_name, ma.ctx,
                               ma.arena);
  return true;
}

static bool TryClassEnumAccess(Variable* base_var, std::string_view field_name,
                               SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (!base_var) return false;
  auto handle = base_var->value.ToUint64();
  auto* obj = ctx.GetClassObject(handle);
  if (!obj || !obj->type) return false;
  auto it = obj->type->enum_members.find(std::string(field_name));
  if (it == obj->type->enum_members.end()) return false;
  out = MakeLogic4VecVal(arena, 32, it->second);
  return true;
}

// Looks up a static property or enum member named `field_name` directly on
// `cls_type` (no inheritance walk). Returns true and fills `out` on a hit.
static bool TryLocalStaticMember(const ClassTypeInfo* cls_type,
                                 std::string_view field_name, Arena& arena,
                                 Logic4Vec& out) {
  auto it = cls_type->static_properties.find(std::string(field_name));
  if (it != cls_type->static_properties.end()) {
    out = it->second;
    return true;
  }
  auto eit = cls_type->enum_members.find(std::string(field_name));
  if (eit != cls_type->enum_members.end()) {
    out = MakeLogic4VecVal(arena, 32, eit->second);
    return true;
  }
  return false;
}

// Walks the interface-class inheritance graph rooted at `cls_type` (parent
// interface plus all extended interfaces) searching for a static property or
// enum member named `field_name`. Returns true and fills `out` on a hit.
static bool TryInterfaceStaticMember(const ClassTypeInfo* cls_type,
                                     std::string_view field_name, Arena& arena,
                                     Logic4Vec& out) {
  std::vector<const ClassTypeInfo*> stack;
  if (cls_type->parent && cls_type->parent->is_interface)
    stack.push_back(cls_type->parent);
  for (const auto* ei : cls_type->extended_interfaces) stack.push_back(ei);
  while (!stack.empty()) {
    const auto* cur = stack.back();
    stack.pop_back();
    if (TryLocalStaticMember(cur, field_name, arena, out)) return true;
    if (cur->parent && cur->parent->is_interface) stack.push_back(cur->parent);
    for (const auto* ei : cur->extended_interfaces) stack.push_back(ei);
  }
  return false;
}

static bool TryStaticMemberAccess(std::string_view base_name,
                                  std::string_view field_name, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  auto* cls_type = ctx.FindClassType(base_name);
  if (!cls_type) return false;
  if (TryLocalStaticMember(cls_type, field_name, arena, out)) return true;
  if (cls_type->is_interface &&
      TryInterfaceStaticMember(cls_type, field_name, arena, out)) {
    return true;
  }
  return false;
}

// Resolves member access on the implicit `this`/`super` object. `is_super`
// selects the parent-type property view used by super. Returns true and fills
// `out` when `base_name` named one of those keywords.
static bool TryThisSuperMember(std::string_view base_name,
                               std::string_view field_name, SimContext& ctx,
                               Arena& arena, Logic4Vec& out) {
  if (base_name == "this") {
    auto* self = ctx.CurrentThis();
    out = self ? self->GetProperty(field_name, arena) : MakeLogic4Vec(arena, 1);
    return true;
  }
  if (base_name == "super") {
    auto* self = ctx.CurrentThis();
    // §8.15: super resolves against the parent of the lexically enclosing class
    // (tracked during method execution); fall back to the dynamic type's parent
    // when no enclosing-class context is active.
    const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
    const ClassTypeInfo* super_type =
        enclosing ? enclosing->parent
                  : (self && self->type ? self->type->parent : nullptr);
    if (self && super_type) {
      out = self->GetPropertyForType(field_name, super_type, arena);
    } else {
      out = MakeLogic4Vec(arena, 1);
    }
    return true;
  }
  return false;
}

// §11.4.13 union access: if `sinfo` describes a tagged union with an active
// tag that does not match the (top-level) field being read, reports the
// runtime error and fills `out` with all-X. Returns true when the mismatch
// fired and `out` was set.
static bool TryUnionTagMismatch(const MemberAccess& ma,
                                const StructTypeInfo* sinfo, Logic4Vec& out) {
  if (!sinfo->is_union) return false;
  auto tag = ma.ctx.GetVariableTag(ma.base_name);
  if (tag.empty()) return false;
  auto top = ma.field_name;
  auto subdot = top.find('.');
  if (subdot != std::string_view::npos) top = top.substr(0, subdot);
  if (tag == top) return false;
  ma.ctx.GetDiag().Error(
      {}, "run-time error: accessing member '" + std::string(ma.field_name) +
              "' of tagged union '" + std::string(ma.base_name) +
              "' which currently has tag '" + std::string(tag) + "'");
  out = MakeAllX(ma.arena, sinfo->total_width);
  return true;
}

// Handles the named-event `.triggered` and named-sequence `.triggered`/`.ended`
// pseudo-methods. Returns true and fills `out` when `field_name` named one of
// these and the base referred to a matching event/sequence.
static bool TryEventSequenceMethod(const MemberAccess& ma, Logic4Vec& out) {
  Variable* base_var = ma.base_var;
  SimContext& ctx = ma.ctx;
  Arena& arena = ma.arena;
  std::string_view base_name = ma.base_name;
  std::string_view field_name = ma.field_name;
  if (base_var && base_var->is_event && field_name == "triggered") {
    // §15.5.3: the triggered method of a null named event evaluates to false,
    // independent of any triggered state recorded for the current time step.
    out = base_var->is_null_event
              ? MakeLogic4VecVal(arena, 1, 0u)
              : MakeLogic4VecVal(arena, 1,
                                 ctx.IsEventTriggered(base_name) ? 1u : 0u);
    return true;
  }
  if (!base_var && field_name == "triggered" &&
      ctx.FindSequenceDecl(base_name)) {
    std::string ep_name = std::string("__seq_") + std::string(base_name);
    out = MakeLogic4VecVal(arena, 1, ctx.IsEventTriggered(ep_name) ? 1u : 0u);
    return true;
  }
  if (!base_var && field_name == "ended" && ctx.FindSequenceDecl(base_name)) {
    // Annex C.2.3: IEEE 1800-2005 supplied the ended sequence method to detect
    // a sequence end point inside a sequence expression, while triggered served
    // the same role in other contexts. The two had identical meaning but
    // mutually exclusive uses, so this version retires ended and lets triggered
    // cover both. A reference to ended on a named sequence therefore names a
    // removed method and is reported rather than silently evaluated.
    ctx.GetDiag().Error(
        {},
        "the ended sequence method has been removed; use the triggered "
        "method to detect the end point of sequence '" +
            std::string(base_name) + "'");
    out = MakeLogic4Vec(arena, 1);
    return true;
  }
  return false;
}

// §15.5.3: the triggered method is prototyped as `function bit triggered()`, so
// a program may invoke it with explicit empty parentheses (ev.triggered()) as
// well as omitting them (ev.triggered). The bare-member form is handled by
// TryEventSequenceMethod during member-access evaluation; this routine covers
// the call form, which arrives as a kCall whose receiver is the named event.
// It yields the same single-bit result: the event's triggered state for the
// current time step, or 1'b0 when the named event is null.
bool TryEvalEventTriggeredCall(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.method_name != "triggered") return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var || !var->is_event) return false;
  out = var->is_null_event
            ? MakeLogic4VecVal(arena, 1, 0u)
            : MakeLogic4VecVal(arena, 1,
                               ctx.IsEventTriggered(parts.var_name) ? 1u : 0u);
  return true;
}

// §14.13: reading a clockvar (cb.data) yields the value sampled at the clocking
// block's most recent input event, not the signal's live value.
// ResolveClockingMember confirms `base_name` names a clocking block carrying
// signal `field_name` and yields the underlying variable for its width. Returns
// true and fills `out` when the access resolved to a clockvar.
static bool TryClockvarMemberAccess(std::string_view base_name,
                                    std::string_view field_name,
                                    SimContext& ctx, Arena& arena,
                                    Logic4Vec& out) {
  auto* mgr = ctx.GetClockingManager();
  if (!mgr) return false;
  auto* sig_var = mgr->ResolveClockingMember(base_name, field_name, ctx);
  if (!sig_var) return false;
  uint64_t sampled = mgr->GetSampledValue(base_name, field_name);
  out = MakeLogic4VecVal(arena, sig_var->value.width, sampled);
  return true;
}

static Logic4Vec ResolveMemberByType(std::string_view base_name,
                                     std::string_view field_name,
                                     SimContext& ctx, Arena& arena) {
  Logic4Vec out;
  if (TryThisSuperMember(base_name, field_name, ctx, arena, out)) return out;

  auto* base_var = ctx.FindVariable(base_name);
  auto* sinfo = ctx.GetVariableStructType(base_name);

  MemberAccess ma{base_name, field_name, base_var, ctx, arena};

  if (base_var && sinfo) {
    if (TryUnionTagMismatch(ma, sinfo, out)) {
      return out;
    }
    return ExtractStructField(base_var, sinfo, field_name, arena);
  }

  if (TryEventSequenceMethod(ma, out)) {
    return out;
  }

  // §8.26: a class-scoped enum literal accessed through an instance handle
  // (p.ERR_OVERFLOW) resolves to its enum value. This is tried before the
  // general property read, which would otherwise claim the (unknown) name and
  // return 0; a name that is not an enum member falls through to it.
  if (TryClassEnumAccess(base_var, field_name, ctx, arena, out)) return out;
  if (TryClassPropertyAccess(ma, out)) return out;
  if (TryCollectionAccess(base_name, field_name, ctx, arena, out)) return out;
  if (TryEvalEnumProperty(base_name, field_name, ctx, arena, out)) return out;
  if (TryStaticMemberAccess(base_name, field_name, ctx, arena, out)) return out;
  if (TryClockvarMemberAccess(base_name, field_name, ctx, arena, out))
    return out;
  return MakeLogic4Vec(arena, 1);
}

// §25.9: a component referenced through a virtual interface redirects to the
// bound interface instance. Referencing a component of an unbound (null or
// uninitialized) virtual interface is a fatal runtime error. Returns true and
// fills `out` when `expr` accessed a member through a virtual interface var.
static bool TryVirtualInterfaceMember(const Expr* expr, SimContext& ctx,
                                      Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier) return false;
  auto* base = ctx.FindVariable(expr->lhs->text);
  if (!ctx.IsVirtualInterfaceVar(base)) return false;
  if (!ctx.VirtualInterfaceIsBound(base)) {
    ctx.GetDiag().Error({}, "reference through a null virtual interface");
    out = MakeLogic4Vec(arena, 1);
    return true;
  }
  std::string_view field =
      (expr->rhs && expr->rhs->kind == ExprKind::kIdentifier)
          ? expr->rhs->text
          : std::string_view(expr->text);
  std::string target =
      std::string(ctx.VirtualInterfaceBinding(base)) + "." + std::string(field);
  auto* tv = ctx.FindVariable(target);
  out = tv ? tv->value : MakeLogic4Vec(arena, 1);
  return true;
}

// §8.25.1: an explicit specialization used as the scope-resolution prefix
// (`C#(3)::p`) denotes the parameter in that specialization, not the class's
// default. When the accessed name is a value parameter port that the prefix
// overrides -- by ordered position or by name -- evaluate the override
// expression instead of falling through to the default stored on the class.
// Type parameters carry no value and body-local parameters are not overridable
// through `#(...)`, so both are left to the ordinary member-access path.
static bool TryParameterizedScopeParam(const Expr* expr, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier ||
      !expr->lhs->has_param_spec || expr->lhs->elements.empty())
    return false;
  if (!expr->rhs || expr->rhs->kind != ExprKind::kIdentifier) return false;
  const ClassTypeInfo* cls = ctx.FindClassType(expr->lhs->text);
  if (!cls || !cls->decl) return false;
  const auto& params = cls->decl->params;
  size_t pos = params.size();
  for (size_t i = 0; i < params.size(); ++i) {
    if (params[i].first == expr->rhs->text) {
      pos = i;
      break;
    }
  }
  if (pos == params.size()) return false;
  if (cls->decl->type_param_names.count(expr->rhs->text)) return false;
  const auto& elems = expr->lhs->elements;
  const auto& names = expr->lhs->arg_names;
  // A named override binding this parameter takes precedence regardless of its
  // position in the override list.
  for (size_t j = 0; j < elems.size(); ++j) {
    if (j < names.size() && !names[j].empty() && names[j] == expr->rhs->text &&
        elems[j]) {
      out = EvalExpr(elems[j], ctx, arena);
      return true;
    }
  }
  // Otherwise the ordered override occupying this parameter's port position.
  bool ordered = names.empty() || (pos < names.size() && names[pos].empty());
  if (ordered && pos < elems.size() && elems[pos]) {
    out = EvalExpr(elems[pos], ctx, arena);
    return true;
  }
  return false;
}

Logic4Vec EvalMemberAccess(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec reduce_out;
  if (TryEvalArrayReductionWithClause(expr, ctx, arena, reduce_out))
    return reduce_out;

  Logic4Vec spec_out;
  if (TryParameterizedScopeParam(expr, ctx, arena, spec_out)) return spec_out;

  Logic4Vec vif_out;
  if (TryVirtualInterfaceMember(expr, ctx, arena, vif_out)) return vif_out;

  std::string name;
  BuildMemberName(expr, name);
  auto resolved = StripRootPrefix(name);
  auto* var = ctx.FindVariable(resolved);
  if (var) return var->value;

  auto dot = resolved.find('.');
  if (dot == std::string::npos) return MakeLogic4Vec(arena, 1);
  auto base_name = std::string_view(resolved).substr(0, dot);
  auto field_name = std::string_view(resolved).substr(dot + 1);
  return ResolveMemberByType(base_name, field_name, ctx, arena);
}

static bool IsRealCastTarget(std::string_view name) {
  return name == "real" || name == "realtime" || name == "shortreal";
}

static double ExtractDouble(const Logic4Vec& vec) {
  double d = 0.0;
  uint64_t bits = vec.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

// §6.24.3: packs the elements of a bit-stream source into a single packed
// value. The first element (index 0 of a fixed unpacked, dynamic, or queue
// array) takes the most significant bit positions of the result. The aval
// and bval (4-state mask) are propagated independently so a source carrying
// any X or Z bit yields a 4-state packed value.
//
// BitStreamPack bundles the packing layout for one unpacked array: the source
// array's name and shape (`info`) plus the element count, total packed width,
// and the per-element bit mask derived from the element width.
struct BitStreamPack {
  std::string_view name;
  const ArrayInfo& info;
  uint32_t elem_count;
  uint32_t total_bits;
  uint32_t elem_mask;
};

// Accumulated packed result: the aval/bval mask pair of the packed value.
struct PackedBits {
  uint64_t aval = 0;
  uint64_t bval = 0;
};

// Packs the low word of each queue element into the accumulated result using
// the element-major shift expected by PackArrayBitStream (element 0 most
// significant).
static void PackQueueElements(const BitStreamPack& pack, SimContext& ctx,
                              PackedBits& out) {
  auto* q = ctx.FindQueue(pack.name);
  if (!q) return;
  for (uint32_t i = 0; i < pack.elem_count; ++i) {
    const auto& v = q->elements[i];
    uint64_t aval = v.nwords > 0 ? v.words[0].aval : 0;
    uint64_t bval = v.nwords > 0 ? v.words[0].bval : 0;
    uint32_t shift = pack.total_bits - (i + 1) * pack.info.elem_width;
    out.aval |= (aval & pack.elem_mask) << shift;
    out.bval |= (bval & pack.elem_mask) << shift;
  }
}

// Packs the low word of each fixed-unpacked-array element into `out` using the
// same element-major shift.
static void PackFixedArrayElements(const BitStreamPack& pack, SimContext& ctx,
                                   PackedBits& out) {
  for (uint32_t i = 0; i < pack.elem_count; ++i) {
    uint32_t idx = pack.info.lo + i;
    auto elem_name = std::string(pack.name) + "[" + std::to_string(idx) + "]";
    auto* elem = ctx.FindVariable(elem_name);
    if (!elem) continue;
    uint64_t aval = elem->value.nwords > 0 ? elem->value.words[0].aval : 0;
    uint64_t bval = elem->value.nwords > 0 ? elem->value.words[0].bval : 0;
    uint32_t shift = pack.total_bits - (i + 1) * pack.info.elem_width;
    out.aval |= (aval & pack.elem_mask) << shift;
    out.bval |= (bval & pack.elem_mask) << shift;
  }
}

static Logic4Vec PackArrayBitStream(std::string_view name,
                                    const ArrayInfo& info, SimContext& ctx,
                                    Arena& arena) {
  // §6.24.3: a queue and a dynamic array are both dynamically sized bit-stream
  // types, and at runtime both keep their elements in a QueueObject rather than
  // in individually named element variables. A fixed-size unpacked array has no
  // such backing store. Pack from the queue whenever one backs this name so the
  // element count and values are taken from the live queue; index 0 still
  // occupies the most significant bits either way.
  auto* q = ctx.FindQueue(name);
  uint32_t elem_count = info.size;
  if (q) elem_count = static_cast<uint32_t>(q->elements.size());
  uint32_t total_bits = elem_count * info.elem_width;
  uint32_t elem_mask = info.elem_width >= 64
                           ? ~uint32_t{0}
                           : (uint32_t{1} << info.elem_width) - 1;
  BitStreamPack pack{name, info, elem_count, total_bits, elem_mask};
  PackedBits packed;
  if (q) {
    PackQueueElements(pack, ctx, packed);
  } else {
    PackFixedArrayElements(pack, ctx, packed);
  }
  auto vec = MakeLogic4Vec(arena, total_bits);
  if (vec.nwords > 0) {
    uint64_t width_mask =
        total_bits >= 64 ? ~uint64_t{0} : (uint64_t{1} << total_bits) - 1;
    vec.words[0].aval = packed.aval & width_mask;
    vec.words[0].bval = packed.bval & width_mask;
  }
  return vec;
}

// §6.24.3: packs an associative-array bit-stream source. Items are packed in
// index-sorted order -- the underlying std::map keeps its keys ordered -- with
// the first key's element occupying the most significant bits, mirroring the
// queue/array packing. Both halves of the 4-state encoding are carried so an
// x/z in any element propagates into the packed value.
static Logic4Vec PackAssocBitStream(const AssocArrayObject& aa, Arena& arena) {
  uint32_t elem_width = aa.elem_width;
  uint32_t elem_count = aa.Size();
  uint32_t total_bits = elem_count * elem_width;
  uint32_t elem_mask =
      elem_width >= 64 ? ~uint32_t{0} : (uint32_t{1} << elem_width) - 1;
  PackedBits packed;
  uint32_t i = 0;
  auto pack_one = [&](const Logic4Vec& v) {
    uint64_t aval = v.nwords > 0 ? v.words[0].aval : 0;
    uint64_t bval = v.nwords > 0 ? v.words[0].bval : 0;
    uint32_t shift = total_bits - (i + 1) * elem_width;
    packed.aval |= (aval & elem_mask) << shift;
    packed.bval |= (bval & elem_mask) << shift;
    ++i;
  };
  if (aa.is_string_key) {
    for (const auto& entry : aa.str_data) pack_one(entry.second);
  } else {
    for (const auto& entry : aa.int_data) pack_one(entry.second);
  }
  auto vec = MakeLogic4Vec(arena, total_bits);
  if (vec.nwords > 0) {
    uint64_t width_mask =
        total_bits >= 64 ? ~uint64_t{0} : (uint64_t{1} << total_bits) - 1;
    vec.words[0].aval = packed.aval & width_mask;
    vec.words[0].bval = packed.bval & width_mask;
  }
  return vec;
}

static Logic4Vec CastRealConversion(const Logic4Vec& inner,
                                    std::string_view type_name,
                                    uint32_t target_width, Arena& arena) {
  if (inner.is_real && !IsRealCastTarget(type_name)) {
    auto val = static_cast<uint64_t>(
        static_cast<int64_t>(std::llround(ExtractDouble(inner))));
    if (target_width < 64) val &= (uint64_t{1} << target_width) - 1;
    auto result = MakeLogic4VecVal(arena, target_width, val);
    result.is_signed = true;
    return result;
  }
  auto d = static_cast<double>(inner.ToUint64());
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto result = MakeLogic4VecVal(arena, target_width, bits);
  result.is_real = true;
  return result;
}

uint32_t ResolveCastWidth(std::string_view type_name, SimContext& ctx) {
  uint32_t w = CastTargetWidth(type_name);
  if (w > 0) return w;

  uint32_t tw = ctx.FindTypeWidth(type_name);
  return tw > 0 ? tw : 32;
}

// §6.24.3 bit-stream cast: when the cast source names an unpacked/dynamic/queue
// array or an associative array, packs it and width-masks into the destination,
// carrying both halves of the 4-state encoding so any X/Z in the source
// propagates. Returns true and fills `out` when `expr` named such a source.
static bool TryArrayBitStreamCast(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier) return false;
  auto name = expr->lhs->text;
  auto* arr_info = ctx.FindArrayInfo(name);
  // §6.24.3: a queue is a bit-stream type, but unlike a fixed unpacked array or
  // a dynamic array it registers no ArrayInfo -- only a QueueObject. Synthesize
  // the packing shape from the queue so a bare queue can be a bit-stream cast
  // source and be packed like any other dynamically sized array.
  ArrayInfo synth;
  if (!arr_info) {
    if (auto* q = ctx.FindQueue(name)) {
      synth.is_queue = true;
      synth.elem_width = q->elem_width;
      synth.size = static_cast<uint32_t>(q->elements.size());
      arr_info = &synth;
    }
  }

  Logic4Vec inner;
  if (arr_info &&
      (arr_info->size > 0 || arr_info->is_queue || arr_info->is_dynamic)) {
    inner = PackArrayBitStream(name, *arr_info, ctx, arena);
  } else if (auto* aa = ctx.FindAssocArray(name)) {
    // §6.24.3: an associative array is a legal bit-stream cast source (it is
    // illegal only as a destination), packed in index-sorted order.
    inner = PackAssocBitStream(*aa, arena);
  } else {
    return false;
  }

  uint32_t target_width = ResolveCastWidth(expr->text, ctx);
  auto result = MakeLogic4Vec(arena, target_width);
  if (result.nwords > 0 && inner.nwords > 0) {
    uint64_t width_mask =
        target_width >= 64 ? ~uint64_t{0} : (uint64_t{1} << target_width) - 1;
    result.words[0].aval = inner.words[0].aval & width_mask;
    result.words[0].bval = inner.words[0].bval & width_mask;
  }
  out = result;
  return true;
}

// §6.24.1: a numeric size cast (a constant_primary casting type) records its
// target width in an expression node rather than a type-name string: the parser
// leaves `text` empty and carries the width expression in `rhs` and the operand
// in `lhs`. Evaluate that width and pad/truncate the operand to it, letting the
// operand's own signedness pass through unchanged. Returns true and fills `out`
// when `expr` is such a cast. A cast that names a type (nonempty `text`), an
// assignment-pattern cast (`lhs` is an assignment pattern), or a type-reference
// cast (`rhs` is a type reference) is not a size cast and is left to the
// caller.
static bool TrySizeCast(const Expr* expr, SimContext& ctx, Arena& arena,
                        Logic4Vec& out) {
  if (!expr->text.empty() || expr->rhs == nullptr || expr->lhs == nullptr)
    return false;
  if (expr->lhs->kind == ExprKind::kAssignmentPattern ||
      expr->rhs->kind == ExprKind::kTypeRef)
    return false;
  auto width_v = EvalExpr(expr->rhs, ctx, arena);
  if (!width_v.IsKnown()) return false;
  uint64_t w64 = width_v.ToUint64();
  if (w64 == 0 || w64 > 0xFFFF) return false;
  uint32_t tw = static_cast<uint32_t>(w64);

  auto inner = EvalExpr(expr->lhs, ctx, arena);
  auto result = MakeLogic4Vec(arena, tw);
  uint64_t mask = tw >= 64 ? ~uint64_t{0} : (uint64_t{1} << tw) - 1;
  if (result.nwords > 0 && inner.nwords > 0) {
    uint64_t aval = inner.words[0].aval;
    uint64_t bval = inner.words[0].bval;
    // §6.24.1: the result is the value a packed [tw-1:0] vector would hold
    // after being assigned the operand, and the operand's own (self-determined)
    // signedness passes through unchanged. Widening a signed operand therefore
    // replicates its sign bit -- in both the value and the x/z plane -- across
    // the new high bits, exactly as an assignment of a signed source does; a
    // narrowing cast or an unsigned operand simply masks to the target width.
    if (inner.is_signed && inner.width > 0 && inner.width < tw &&
        inner.width < 64) {
      uint64_t high_bits = mask & ~((uint64_t{1} << inner.width) - 1);
      if ((aval >> (inner.width - 1)) & 1) aval |= high_bits;
      if ((bval >> (inner.width - 1)) & 1) bval |= high_bits;
    }
    result.words[0].aval = aval & mask;
    result.words[0].bval = bval & mask;
  }
  result.is_signed = inner.is_signed;
  out = result;
  return true;
}

// Handles the signedness/const/void cast keywords that simply re-tag or empty
// the inner value. Returns true and fills `out` when `type_name` was one of
// those keywords. `inner` may be mutated in place for the signedness cases.
static bool TryKeywordCast(std::string_view type_name, Logic4Vec& inner,
                           Arena& arena, Logic4Vec& out) {
  if (type_name == "signed") {
    inner.is_signed = true;
    out = inner;
    return true;
  }
  if (type_name == "unsigned") {
    inner.is_signed = false;
    out = inner;
    return true;
  }
  if (type_name == "const") {
    out = inner;
    return true;
  }
  if (type_name == "void") {
    out = MakeLogic4Vec(arena, 0);
    return true;
  }
  return false;
}

Logic4Vec EvalCast(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec stream_out;
  if (TryArrayBitStreamCast(expr, ctx, arena, stream_out)) return stream_out;

  Logic4Vec size_out;
  if (TrySizeCast(expr, ctx, arena, size_out)) return size_out;

  auto inner = EvalExpr(expr->lhs, ctx, arena);
  std::string_view type_name = expr->text;

  Logic4Vec kw_out;
  if (TryKeywordCast(type_name, inner, arena, kw_out)) return kw_out;

  uint32_t target_width = ResolveCastWidth(type_name, ctx);

  if (inner.is_real != IsRealCastTarget(type_name)) {
    return CastRealConversion(inner, type_name, target_width, arena);
  }
  uint64_t val = inner.ToUint64();
  if (target_width < 64) val &= (uint64_t{1} << target_width) - 1;
  return MakeLogic4VecVal(arena, target_width, val);
}

static uint64_t ResolveDollarBound(uint32_t width, bool lower) {
  if (lower) return 0;
  if (width >= 64) return ~uint64_t{0};
  return (uint64_t{1} << width) - 1;
}

static void ComputeToleranceBounds(uint64_t a, uint64_t b, TokenKind op,
                                   uint64_t& lo, uint64_t& hi) {
  uint64_t tol = b;
  if (op == TokenKind::kPlusPercentMinus) tol = a * b / 100;
  lo = (a >= tol) ? a - tol : 0;
  hi = a + tol;
  if (lo > hi) std::swap(lo, hi);
}

static int InsideMatchTolerance(uint64_t lv, const Expr* elem, SimContext& ctx,
                                Arena& arena) {
  auto a_v = EvalExpr(elem->index, ctx, arena);
  auto b_v = EvalExpr(elem->index_end, ctx, arena);
  if (!a_v.IsKnown() || !b_v.IsKnown()) return 2;
  uint64_t lo = 0;
  uint64_t hi = 0;
  ComputeToleranceBounds(a_v.ToUint64(), b_v.ToUint64(), elem->op, lo, hi);
  return (lv >= lo && lv <= hi) ? 1 : 0;
}

static bool IsDollarExpr(const Expr* e) {
  return e->kind == ExprKind::kIdentifier && e->text == "$";
}

static int InsideMatchRange(Logic4Vec lhs, const Expr* elem, SimContext& ctx,
                            Arena& arena) {
  if (elem->op == TokenKind::kPlusSlashMinus ||
      elem->op == TokenKind::kPlusPercentMinus) {
    if (!lhs.IsKnown()) return 2;
    return InsideMatchTolerance(lhs.ToUint64(), elem, ctx, arena);
  }

  uint64_t lo = IsDollarExpr(elem->index)
                    ? ResolveDollarBound(lhs.width, true)
                    : EvalExpr(elem->index, ctx, arena).ToUint64();
  uint64_t hi = IsDollarExpr(elem->index_end)
                    ? ResolveDollarBound(lhs.width, false)
                    : EvalExpr(elem->index_end, ctx, arena).ToUint64();
  if (lo > hi) return 0;

  // §11.4.13: with x/z bits in the left operand the comparison ranges over
  // every concretization of the unknown bits. ToUint64() projects those bits to
  // 0 (the minimum); setting them to 1 gives the maximum. If the whole span
  // lies inside [lo, hi] the membership is a definite 1; if it lies entirely
  // outside, a definite 0; otherwise the comparison is ambiguous (x) and
  // OR-reduces with the other set members.
  uint64_t unknown = lhs.nwords > 0 ? lhs.words[0].bval : 0;
  uint64_t lv_min = lhs.ToUint64();
  uint64_t lv_max = lv_min | unknown;
  if (lv_min >= lo && lv_max <= hi) return 1;
  if (lv_max < lo || lv_min > hi) return 0;
  return 2;
}

// Compares the left-hand expression against one singular set member, returning
// 1 for a match, 0 for a mismatch, and 2 when the comparison is ambiguous (x).
// Integral members use wildcard equality so an x or z bit on the member side is
// a do-not-care, while an x or z bit that survives on the left-hand side leaves
// the comparison ambiguous (§11.4.13, §11.4.6).
static int CompareInsideValue(const Logic4Vec& lhs, const Logic4Vec& ev) {
  uint64_t rhs_dc = ev.nwords > 0 ? ev.words[0].bval : 0;
  uint64_t lhs_x = lhs.nwords > 0 ? lhs.words[0].bval : 0;
  if (lhs_x & ~rhs_dc) return 2;
  if (rhs_dc || lhs_x) {
    return (((lhs.ToUint64() ^ ev.ToUint64()) & ~rhs_dc) == 0) ? 1 : 0;
  }
  return (lhs.ToUint64() == ev.ToUint64()) ? 1 : 0;
}

static int InsideMatchValue(Logic4Vec lhs, const Expr* elem, SimContext& ctx,
                            Arena& arena) {
  return CompareInsideValue(lhs, EvalExpr(elem, ctx, arena));
}

// §11.4.13: descends every unpacked dimension of a multidimensional array set
// member, gathering the singular per-element leaf values named arr[i0][i1]...
// in row-major order (matching how lowerer_var.cpp materialized them). A
// missing leaf contributes a default value of the element width so the count of
// scanned members is preserved.
static void CollectMultiDimSetLeaves(const ArrayInfo& info, size_t d,
                                     const std::string& prefix, SimContext& ctx,
                                     std::vector<Logic4Vec>& out) {
  if (d == info.dim_sizes.size()) {
    auto* var = ctx.FindVariable(prefix);
    out.push_back(var ? var->value
                      : MakeLogic4Vec(ctx.GetArena(), info.elem_width));
    return;
  }
  uint32_t lo = info.dim_los[d];
  for (uint32_t i = 0; i < info.dim_sizes[d]; ++i) {
    CollectMultiDimSetLeaves(
        info, d + 1, prefix + "[" + std::to_string(lo + i) + "]", ctx, out);
  }
}

// §11.4.13: a set member that names an unpacked array is not compared as an
// aggregate. Instead its elements are traversed down to singular values, so the
// membership test sees each element as if it had been listed individually.
// Returns true (filling `out`) when `elem` named an unpacked array, covering
// queues/dynamic arrays, single-dimension fixed arrays, and (by full descent
// through every dimension) multidimensional fixed arrays.
static bool CollectUnpackedSetMembers(const Expr* elem, SimContext& ctx,
                                      std::vector<Logic4Vec>& out) {
  if (elem->kind != ExprKind::kIdentifier) return false;
  if (auto* q = ctx.FindQueue(elem->text)) {
    for (auto& e : q->elements) out.push_back(e);
    return true;
  }
  if (auto* info = ctx.FindArrayInfo(elem->text)) {
    if (info->dim_sizes.size() >= 2) {
      CollectMultiDimSetLeaves(*info, 0, std::string(elem->text), ctx, out);
      return true;
    }
    for (uint32_t i = 0; i < info->size; ++i) {
      std::string elem_name =
          std::string(elem->text) + "[" + std::to_string(info->lo + i) + "]";
      auto* var = ctx.FindVariable(elem_name);
      out.push_back(var ? var->value
                        : MakeLogic4Vec(ctx.GetArena(), info->elem_width));
    }
    return true;
  }
  return false;
}

// Tests `lhs` against each singular value collected from an unpacked-array set
// member. Returns 1 on the first match, 2 if any comparison was ambiguous (and
// none matched), and 0 otherwise.
static int MatchUnpackedSetMembers(const Logic4Vec& lhs,
                                   const std::vector<Logic4Vec>& members) {
  int result = 0;
  for (const auto& member : members) {
    int mr = CompareInsideValue(lhs, member);
    if (mr == 1) return 1;
    if (mr == 2) result = 2;
  }
  return result;
}

// When `elem` (in a non-range position) names an unpacked array, traverses it
// to singular values per §11.4.13 and reports the membership result through
// `out`/the return value. Returns true when `elem` was such an array.
static bool TryMatchUnpackedSetMember(const Logic4Vec& lhs, const Expr* elem,
                                      SimContext& ctx, int& out) {
  std::vector<Logic4Vec> members;
  if (!CollectUnpackedSetMembers(elem, ctx, members)) return false;
  out = MatchUnpackedSetMembers(lhs, members);
  return true;
}

// Evaluates `lhs inside { elem }` for one set member. Returns 1 on a match, 0
// on a definite mismatch, and 2 when the comparison was ambiguous (x). Handles
// ranges, unpacked-array members (traversed to singular values per §11.4.13),
// and plain singular values.
static int EvalInsideElement(const Logic4Vec& lhs, const Expr* elem,
                             SimContext& ctx, Arena& arena) {
  bool is_range =
      elem->kind == ExprKind::kSelect && elem->index && elem->index_end;
  if (!is_range) {
    int unpacked_result = 0;
    if (TryMatchUnpackedSetMember(lhs, elem, ctx, unpacked_result)) {
      return unpacked_result;
    }
  }
  return is_range ? InsideMatchRange(lhs, elem, ctx, arena)
                  : InsideMatchValue(lhs, elem, ctx, arena);
}

Logic4Vec EvalInside(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto lhs = EvalExpr(expr->lhs, ctx, arena);
  bool ambiguous = false;
  for (auto* elem : expr->elements) {
    int r = EvalInsideElement(lhs, elem, ctx, arena);
    if (r == 1) return MakeLogic4VecVal(arena, 1, 1);
    if (r == 2) ambiguous = true;
  }
  if (ambiguous) {
    auto x = MakeLogic4Vec(arena, 1);
    x.words[0] = {~uint64_t{0}, ~uint64_t{0}};
    return x;
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

TokenKind CompoundAssignBaseOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlusEq:
      return TokenKind::kPlus;
    case TokenKind::kMinusEq:
      return TokenKind::kMinus;
    case TokenKind::kStarEq:
      return TokenKind::kStar;
    case TokenKind::kSlashEq:
      return TokenKind::kSlash;
    case TokenKind::kPercentEq:
      return TokenKind::kPercent;
    case TokenKind::kAmpEq:
      return TokenKind::kAmp;
    case TokenKind::kPipeEq:
      return TokenKind::kPipe;
    case TokenKind::kCaretEq:
      return TokenKind::kCaret;
    case TokenKind::kLtLtEq:
      return TokenKind::kLtLt;
    case TokenKind::kGtGtEq:
      return TokenKind::kGtGt;
    case TokenKind::kLtLtLtEq:
      return TokenKind::kLtLtLt;
    case TokenKind::kGtGtGtEq:
      return TokenKind::kGtGtGt;
    default:
      return TokenKind::kEof;
  }
}

bool IsCompoundAssignOp(TokenKind op) {
  return CompoundAssignBaseOp(op) != TokenKind::kEof;
}

Logic4Vec EvalCompoundAssign(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto lhs_val = EvalExpr(expr->lhs, ctx, arena);
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);
  auto base_op = CompoundAssignBaseOp(expr->op);
  auto result = EvalBinaryOp(base_op, lhs_val, rhs_val, arena);
  if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) var->value = result;
  } else if (expr->lhs->kind == ExprKind::kSelect) {
    TryAssocIndexedWrite(expr->lhs, result, ctx, arena);
  }
  return result;
}

}  // namespace delta
