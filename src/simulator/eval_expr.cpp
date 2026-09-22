#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/assoc_element.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/clocking.h"
#include "simulator/eval_array.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_array_handles.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/eval_string.h"
#include "simulator/eval_struct_property.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/virtual_interface.h"

namespace delta {

bool ExtractMethodCallParts(const Expr* expr, MethodCallParts& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;
  out.var_name = access->lhs->text;
  out.method_name = access->rhs->text;
  out.loc = access->rhs->range.start;
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
  // §11.4.12.1: the inner expression of a replication is self-determined, an
  // unbased unsized literal among its operands one bit wide (§5.7.1).
  for (auto* elem : expr->elements) {
    parts.push_back(EvalExpr(elem, ctx, arena));
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

// §6.12: a real, shortreal or realtime member holds a real, so the bits read
// from it are that real and not an integer of the same pattern.
static bool IsRealKind(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
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
    slice.is_real = IsRealKind(kind);
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
// the resolved base variable (when one exists), the evaluation context and the
// position the access was written at. A single instance is built once in
// ResolveMemberByType and shared across the per-feature member-access helpers
// below. The name is rebuilt from the expression before the helpers run and no
// longer points back at it, so the position is carried here rather than
// recovered: it is what a report from one of those helpers names.
struct MemberAccess {
  std::string_view base_name;
  std::string_view field_name;
  Variable* base_var;
  SimContext& ctx;
  Arena& arena;
  SourceLoc loc;
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
Logic4Vec ResolveClassFieldChain(ClassObject* obj,
                                 const ClassTypeInfo* declared_type,
                                 std::string_view field_path, SimContext& ctx,
                                 Arena& arena) {
  auto dot = field_path.find('.');
  if (dot == std::string_view::npos) {
    return ReadClassField(obj, declared_type, field_path, arena);
  }
  auto first = field_path.substr(0, dot);
  auto rest = field_path.substr(dot + 1);
  Logic4Vec handle_val = ReadClassField(obj, declared_type, first, arena);
  // §7.2.1: `first` declared with a structure's type holds that structure
  // rather than a handle, so the rest of the path selects a member of the
  // value just read. Asked before the handle lookup, because a structure
  // whose bits happen to equal a live handle's number is still a structure.
  // The flattened key below names a property the class never declared, which
  // answers what an earlier write to the same path left there and a known
  // zero where there was none.
  PropertyFieldWindow window = ResolveClassPropertyField(
      declared_type ? declared_type : obj->type, field_path, ctx);
  if (window.valid) {
    return ExtractBitField(arena, handle_val, window.bit_offset, window.width);
  }
  auto* next_obj = ctx.GetClassObject(handle_val.ToUint64());
  if (!next_obj) return ReadClassField(obj, declared_type, field_path, arena);
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

// §8.13 (printed pages 189-190) with §8.9 (printed 186): `D::n` reads the
// static property D declares or inherits, the nearest declaration first, so
// where D extends C it reads C's one storage, what `C::n = 5` wrote. Read
// from D's own static_properties alone, which hold D's declarations, it
// answered 0.
static bool TryStaticMemberAccess(std::string_view base_name,
                                  std::string_view field_name, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  auto* cls_type = ctx.FindClassType(base_name);
  if (!cls_type) return false;
  for (const auto* t = cls_type; t != nullptr; t = t->parent) {
    if (TryLocalStaticMember(t, field_name, arena, out)) return true;
  }
  return cls_type->is_interface &&
         TryInterfaceStaticMember(cls_type, field_name, arena, out);
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

// §11.9 (printed page 304): a member read inconsistent with the tagged
// union's current tag is a run-time error, and §7.3.2 (printed 151) makes
// that so for a tagged union wherever it stands -- the variable `u.Other`
// reads or the member `s.u.Other` reads, whose tag `s.u = tagged Valid 9`
// set under the member's own key. The walk FindUnionTagMismatch shares with
// the write side asks each tagged union on the path; this checked the base
// variable's own layout alone, a structure, and so read `s.u.Other` against
// no tag. Reports the error and fills `out` with all-X; true when it fired.
static bool TryUnionTagMismatch(const MemberAccess& ma,
                                const StructTypeInfo* sinfo, Logic4Vec& out) {
  UnionTagMismatch m =
      FindUnionTagMismatch(ma.base_name, sinfo, ma.field_name, ma.ctx);
  if (!m.found) return false;
  ma.ctx.GetDiag().Error(ma.loc,
                         "run-time error: accessing member '" + m.member +
                             "' of tagged union '" + m.union_name +
                             "' which currently has tag '" + m.tag + "'",
                         Subclause("11.9"));
  out = MakeAllX(ma.arena, sinfo->total_width);
  return true;
}

// Handles the named-event `.triggered` and named-sequence `.triggered`/`.ended`
// §16.13.5: whether the end point named `ep_name` is matched as read now,
// its match stored until the first tick of the reading clock after it.
static bool SequenceMatched(std::string_view ep_name, SimContext& ctx) {
  auto* ep = ctx.FindVariable(ep_name);
  if (ep == nullptr) return false;
  return ctx.ConsumeSequenceMatch(ep_name, ep->triggered_ticks,
                                  ctx.CurrentTime().ticks);
}

// §16.9.11 and §16.13.5: `triggered` and `matched` on the named sequence
// `base_name`, the first true at the time step of the match alone and the
// second storing a match until the first tick of the reading clock after
// it; false where `field_name` names neither.
static bool TrySequenceEndPointMethod(std::string_view base_name,
                                      std::string_view field_name,
                                      SimContext& ctx, Arena& arena,
                                      Logic4Vec& out) {
  if (field_name != "triggered" && field_name != "matched") return false;
  std::string ep_name = std::string("__seq_") + std::string(base_name);
  bool reached = field_name == "matched" ? SequenceMatched(ep_name, ctx)
                                         : ctx.IsEventTriggered(ep_name);
  out = MakeLogic4VecVal(arena, 1, reached ? 1u : 0u);
  return true;
}

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
  if (!base_var && ctx.FindSequenceDecl(base_name) &&
      TrySequenceEndPointMethod(base_name, field_name, ctx, arena, out)) {
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
        ma.loc,
        "the ended sequence method has been removed; use the triggered "
        "method to detect the end point of sequence '" +
            std::string(base_name) + "'",
        Subclause("C.2.3"));
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
// current time step, or 1'b0 when the named event is null. §26.3 admits a
// package's event as the receiver, `p::e.triggered()`, by the "p.e" key
// ExtractHandleMethodCallParts answers; taken as an identifier alone, the
// scoped call fell to the user-method lookup, which found no method.
bool TryEvalEventTriggeredCall(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractHandleMethodCallParts(expr, arena, parts)) return false;
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
  // §23.9: `cb.data` spells the block by the bare name the module declared, so
  // the sampled value read back is the one belonging to the instance this
  // expression is running in, which is what the block was registered under.
  const ClockingBlock* block = mgr->FindInScope(base_name, ctx);
  if (block == nullptr) return false;
  auto* sig_var = mgr->ResolveClockingMember(base_name, field_name, ctx);
  if (!sig_var) return false;
  uint64_t sampled = mgr->GetSampledValue(block->name, field_name);
  out = MakeLogic4VecVal(arena, sig_var->value.width, sampled);
  return true;
}

static Logic4Vec ResolveMemberByType(std::string_view base_name,
                                     std::string_view field_name,
                                     SimContext& ctx, Arena& arena,
                                     SourceLoc loc) {
  Logic4Vec out;
  if (TryThisSuperMember(base_name, field_name, ctx, arena, out)) return out;

  auto* base_var = ctx.FindVariable(base_name);
  // §23.9: the base resolves within the running instance, so its layout is
  // asked for by the key that instance's storage was created under.
  const StructTypeInfo* sinfo = StructLayoutOfName(base_name, ctx);

  MemberAccess ma{base_name, field_name, base_var, ctx, arena, loc};

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
  if (TryStaticMemberAccess(base_name, field_name, ctx, arena, out)) return out;
  if (TryClockvarMemberAccess(base_name, field_name, ctx, arena, out))
    return out;
  if (TryImplicitThisHandleMember(base_name, field_name, ctx, arena, out))
    return out;
  return MakeLogic4Vec(arena, 1);
}

// §25.9: a component referenced through a virtual interface redirects to the
// bound interface instance. Referencing a component of an unbound (null or
// uninitialized) virtual interface is a fatal runtime error. Returns true and
// fills `out` when `expr` accessed a member through a virtual interface: a
// variable declared so, a property declared so of the class whose method is
// running, or, `this.vif.a` and `d.vif.a`, a property declared so of the
// object a handle expression denotes, which ResolveVirtualInterfaceBaseExpr
// tells apart from any other base. Before the base was resolved as an
// expression, `d.vif.a` fell to the class field chain, which took the
// interface handle for a class handle, found no object, and read a flattened
// key the class never declared.
static bool TryVirtualInterfaceMember(const Expr* expr, SimContext& ctx,
                                      Arena& arena, Logic4Vec& out) {
  VirtualInterfaceBase base =
      ResolveVirtualInterfaceBaseExpr(expr->lhs, ctx, arena);
  if (!base.is_virtual_interface) return false;
  if (base.handle == kNullVirtualInterface) {
    ctx.GetDiag().Error(expr->range.start,
                        "reference through a null virtual interface",
                        Subclause("25.9"));
    out = MakeLogic4Vec(arena, 1);
    return true;
  }
  std::string_view field =
      (expr->rhs && expr->rhs->kind == ExprKind::kIdentifier)
          ? expr->rhs->text
          : std::string_view(expr->text);
  auto* tv =
      ctx.FindVariable(VirtualInterfaceComponentName(base.handle, field, ctx));
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
// §8.25.1: the port position `name` occupies in a class's parameter port list.
// A type parameter carries no value and is not overridable through #(...), so
// it has no position here.
static size_t ValueParamPosition(const ClassDecl& decl, std::string_view name) {
  if (decl.type_param_names.count(name)) return decl.params.size();
  for (size_t i = 0; i < decl.params.size(); ++i) {
    if (decl.params[i].first == name) return i;
  }
  return decl.params.size();
}

// §8.25.1: the specialization argument that overrides `name`. A named override
// binding the parameter takes precedence regardless of its position in the
// override list; otherwise the ordered override occupying the parameter's own
// port position applies.
static const Expr* FindSpecializationOverride(const Expr& base,
                                              const ClassDecl& decl,
                                              std::string_view name) {
  size_t pos = ValueParamPosition(decl, name);
  if (pos == decl.params.size()) return nullptr;
  const auto& elems = base.elements;
  const auto& names = base.arg_names;
  for (size_t j = 0; j < elems.size(); ++j) {
    if (j < names.size() && !names[j].empty() && names[j] == name && elems[j])
      return elems[j];
  }
  bool ordered = names.empty() || (pos < names.size() && names[pos].empty());
  if (ordered && pos < elems.size()) return elems[pos];
  return nullptr;
}

static bool TryParameterizedScopeParam(const Expr* expr, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier ||
      !expr->lhs->has_param_spec || expr->lhs->elements.empty())
    return false;
  if (!expr->rhs || expr->rhs->kind != ExprKind::kIdentifier) return false;
  const ClassTypeInfo* cls = ctx.FindClassType(expr->lhs->text);
  if (!cls || !cls->decl) return false;
  const Expr* override_expr =
      FindSpecializationOverride(*expr->lhs, *cls->decl, expr->rhs->text);
  if (override_expr == nullptr) return false;
  out = EvalExpr(override_expr, ctx, arena);
  return true;
}

// §16.9.11, §16.13.5 and §16.13.6: whether the expression applies
// `triggered` or `matched` to a sequence instance with arguments, `e2(ready,
// proc1, proc2).triggered`, or to a sequence actual, the identifier
// carrying it standing where the formal of `subseq.triggered` stood.
static bool ReadsAMonitorEndPoint(const Expr* expr, SimContext& ctx) {
  if (expr->lhs == nullptr || expr->rhs == nullptr ||
      (expr->rhs->text != "triggered" && expr->rhs->text != "matched")) {
    return false;
  }
  if (expr->lhs->kind == ExprKind::kCall) {
    return ctx.FindSequenceDecl(expr->lhs->callee) != nullptr;
  }
  return expr->lhs->kind == ExprKind::kIdentifier &&
         expr->lhs->property_actual != nullptr;
}

// §16.9.11, §16.13.5 and §16.13.6: `.triggered` or `.matched` applied to a
// sequence instance with arguments or to a sequence actual reads the
// endpoint of the monitor the lowering gave it; answers false where no
// monitor was made for it.
static bool TryInstanceTriggered(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  if (!ReadsAMonitorEndPoint(expr, ctx)) return false;
  std::string_view ep_name = ctx.FindSequenceInstanceEndpoint(expr->lhs);
  bool triggered = !ep_name.empty() && (expr->rhs->text == "matched"
                                            ? SequenceMatched(ep_name, ctx)
                                            : ctx.IsEventTriggered(ep_name));
  out = MakeLogic4VecVal(arena, 1, triggered ? 1u : 0u);
  return true;
}

// The member selects that are something other than a read of a member of a
// value: a sequence's end point (§16.9.11), an array reduction or ordering
// method with a with clause (§7.12), a parameter of a parameterized class
// scope (§8.25.1), and an enumeration method written without an argument
// list (§6.19.5.7), `c.name` or `c.next`, asked ahead of the member reads
// since a receiver of an enumeration type leaves no member of the name for
// them to read. True with `out` set when the select was one of them.
static bool TryMemberSelectThatIsNoRead(const Expr* expr, SimContext& ctx,
                                        Arena& arena, Logic4Vec& out) {
  if (TryInstanceTriggered(expr, ctx, arena, out)) return true;
  if (TryEvalArrayReductionWithClause(expr, ctx, arena, out)) return true;
  // §7.12.2: a bare-member sort()/rsort() carrying a with clause (parenthesis-
  // free form, or any queue receiver) reorders in place; yield a void result.
  if (TryExecArrayOrderingWithClauseStmt(expr, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryParameterizedScopeParam(expr, ctx, arena, out)) return true;
  if (TryScopeSpecializationStaticMember(expr, ctx, arena, out)) return true;
  return TryEvalEnumMethodWithoutArgs(expr, ctx, arena, out);
}

Logic4Vec EvalMemberAccess(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec out;
  if (TryMemberSelectThatIsNoRead(expr, ctx, arena, out)) return out;

  if (TryVirtualInterfaceMember(expr, ctx, arena, out)) return out;

  // §7.8.7: `b[2].x` reads a member of an associative array element, and §8.4
  // `q[1].v` or `a[1].v` a property of the object an element of a queue or of
  // an array property (§7.4.2) refers to; the name built below reaches none.
  // §8.6: nor `n.self().v`, a property of the object a method call returned.
  // §8.9 with §8.4: nor `C::m_inst.k` or a static method's bare `m_inst.k`,
  // a property of the object a static property holds a handle to.
  if (TryEvalAssocMemberField(expr, ctx, arena, out) ||
      TryEvalElementObjectMember(expr, ctx, arena, out) ||
      TryEvalCallResultMember(expr, ctx, arena, out) ||
      TryPackageClassStaticMember(expr, ctx, arena, out) ||
      TryStaticHandleMember(expr, ctx, arena, out))
    return out;

  std::string name;
  BuildMemberName(expr, name);
  auto resolved = StripRootPrefix(name);
  // §18.7.1: a name qualified by local:: — the local::x used to steer an inline
  // randomize()...with constraint from the calling scope — bypasses the
  // randomized object's class scope and resolves in the scope containing the
  // method call, which is exactly the scope this expression is evaluated in.
  // `local` is a reserved keyword and cannot name any declaration, so a leading
  // "local." segment can only be that qualifier: drop it and resolve the
  // remaining name here, so local::x denotes the same declaration an
  // unqualified x written in this scope would.
  constexpr std::string_view kLocalScopePrefix = "local.";
  if (std::string_view(resolved).substr(0, kLocalScopePrefix.size()) ==
      kLocalScopePrefix) {
    resolved = resolved.substr(kLocalScopePrefix.size());
    // §18.7.1: local::this binds to the scope containing the call, whose
    // `this` the constraint evaluation keeps aside while the randomized
    // object stands in scope as `this`.
    constexpr std::string_view kThisPrefix = "this.";
    ClassObject* caller = ctx.ConstraintCallerThis();
    if (caller != nullptr && std::string_view(resolved).substr(
                                 0, kThisPrefix.size()) == kThisPrefix) {
      return ResolveClassFieldChain(
          caller, nullptr, resolved.substr(kThisPrefix.size()), ctx, arena);
    }
  }
  auto* var = ctx.FindVariable(resolved);
  if (var) {
    // §16.5.2: "In an assertion, the sampled value is the only valid value of a
    // variable during a clock tick", and §16.5.1 puts no condition on where the
    // variable is declared, so a variable a property reaches across an instance
    // boundary reads the value sampled for this time slot exactly as one the
    // module declares itself. The store answers nothing outside a clocked
    // concurrent assertion's property and nothing for a variable no such
    // property reads, so every other hierarchical read is the live read it was.
    const Logic4Vec* sampled =
        ctx.AssertionSamples().ReadWithinProperty(var, ctx.CurrentTime());
    return sampled != nullptr ? *sampled : var->value;
  }

  auto dot = MemberPathSplit(resolved, ctx);
  if (dot == std::string::npos) return MakeLogic4Vec(arena, 1);
  auto base_name = std::string_view(resolved).substr(0, dot);
  auto field_name = std::string_view(resolved).substr(dot + 1);
  return ResolveMemberByType(base_name, field_name, ctx, arena,
                             expr->range.start);
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
int EvalInsideElement(const Logic4Vec& lhs, const Expr* elem, SimContext& ctx,
                      Arena& arena) {
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

}  // namespace delta
