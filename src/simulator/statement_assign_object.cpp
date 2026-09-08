// The blocking assignments whose left-hand side names an object rather than a
// vector: §7.9's associative-array whole-array forms and §8.3's class `new`.
//
// §7.9.11 lets a whole associative array be written at once -- by copying
// another array, by assigning the result of §7.12.5's map(), or from an
// '{index:value} literal -- and §8.3 has `new` construct a class object and
// return the handle the target then holds, in the bare, the shallow-copy, the
// class-scope `C::new` and the `obj.field = new` forms. Neither family sizes a
// right-hand value against the width of its target the way §10.7 does for a
// vector, so each is answered whole before the generic path evaluates an rhs
// at all, and all of them are reached from one run of
// TryDispatchSpecialBlockingAssign.
//
// That dispatch, and the vector-target writers around it, stay in
// src/simulator/statement_assign_core.cpp, which reached 948 lines against the
// 950 assert-no-oversized-source-files in .github/workflows/deltahdl.yml fails
// at. The names this side owes that one are declared in
// simulator/statement_assign_internal.h, save TryClassNewAssign, which
// simulator/statement_assign.h already declares for eval_function_body.cpp.

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

bool TryAssocCopyAssign(const Stmt* stmt, SimContext& ctx) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (stmt->rhs->kind != ExprKind::kIdentifier) return false;
  auto* dst = ctx.FindAssocArray(stmt->lhs->text);
  auto* src = ctx.FindAssocArray(stmt->rhs->text);
  if (!dst || !src) return false;
  dst->int_data = src->int_data;
  dst->str_data = src->str_data;
  return true;
}

// §7.12.5 — assigning the result of `src.map() with (...)` to an
// associative-array target, where the source is itself an associative array.
// map() returns an array whose set of index values matches the source, with
// each stored value replaced by the value of the with expression; copy those
// key/value pairs into the destination, replacing its previous contents. This
// is the associative analogue of the indexed-array map (whose result flows
// through the queue/dynamic-array element-collection path); without it a bare
// `dst = src.map() with (...)` between two associative arrays would leave the
// destination empty.
bool TryAssocMapAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs) return false;
  auto* dst = ctx.FindAssocArray(stmt->lhs->text);
  if (!dst) return false;
  AssocArrayObject mapped;
  if (!TryCollectAssocMapResult(stmt->rhs, ctx, arena, mapped)) return false;
  dst->int_data = mapped.int_data;
  dst->str_data = mapped.str_data;
  return true;
}

static std::string StripAssocKeyQuotes(std::string_view key) {
  if (key.size() >= 2 && key.front() == '"' && key.back() == '"')
    return std::string(key.substr(1, key.size() - 2));
  return std::string(key);
}

// §7.9.11: besides writing an associative array one entry at a time, the whole
// array contents can be replaced by assigning an '{index:value} array literal.
// Discard the existing entries and repopulate keyed entries and the optional
// default from the pattern, mirroring the declaration-time initialization.
bool TryAssocLiteralAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kAssignmentPattern)
    return false;
  if (stmt->rhs->pattern_keys.empty()) return false;
  auto* aa = ctx.FindAssocArray(stmt->lhs->text);
  if (!aa) return false;
  aa->int_data.clear();
  aa->str_data.clear();
  const Expr* rhs = stmt->rhs;
  for (size_t i = 0; i < rhs->pattern_keys.size(); ++i) {
    if (i >= rhs->elements.size()) break;
    const auto* key = rhs->pattern_keys[i];
    auto val = EvalExpr(rhs->elements[i], ctx, arena);
    if (key->text == "default") {
      aa->has_default = true;
      aa->default_value = val;
    } else if (aa->is_string_key) {
      aa->str_data[StripAssocKeyQuotes(key->text)] = val;
    } else {
      // §7.9.11: the entry goes at the index the key evaluates to, read as an
      // index of this array's declared index type -- the same reading a key
      // written on the left of a single-element assignment gets.
      auto key_val = EvalExpr(key, ctx, arena);
      aa->int_data[AssocIntKey(key_val, aa->is_wildcard, aa->index_width,
                               aa->is_index_signed)] = val;
    }
  }
  return true;
}

// `new src_obj` shallow-copy form: returns true (and writes the copy handle to
// the target) when the rhs argument resolves to an existing class object.
static bool TryClassCopyNewAssign(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (!stmt->rhs->lhs || stmt->rhs->lhs->kind != ExprKind::kIdentifier)
    return false;
  auto src_val = EvalExpr(stmt->rhs->lhs, ctx, arena);
  auto* src_obj = ctx.GetClassObject(src_val.ToUint64());
  if (!src_obj) return false;
  auto* copy = src_obj->ShallowCopy(arena);
  auto copy_handle = ctx.AllocateClassObject(copy);
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (var) {
    var->value = MakeLogic4VecVal(arena, 64, copy_handle);
    var->NotifyWatchers();
  }
  return true;
}

// `new (referent)` for a weak_reference-typed target: allocate the weak
// reference wrapper and write its handle to the target.
static void AssignWeakReferenceNew(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  uint64_t referent = kNullClassHandle;
  if (!stmt->rhs->args.empty()) {
    auto val = EvalExpr(stmt->rhs->args[0], ctx, arena);
    referent = val.ToUint64();
  }
  auto wr_handle = ctx.AllocateWeakReference(referent, arena);
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (var) {
    var->value = MakeLogic4VecVal(arena, 64, wr_handle);
    var->NotifyWatchers();
  }
}

bool TryClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall) return false;
  if (stmt->rhs->text != "new") return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  auto type_name = ctx.GetVariableClassType(stmt->lhs->text);
  if (type_name.empty()) return false;

  if (TryClassCopyNewAssign(stmt, ctx, arena)) return true;

  if (type_name == "weak_reference") {
    AssignWeakReferenceNew(stmt, ctx, arena);
    return true;
  }

  auto handle =
      EvalClassNew(type_name, stmt->rhs, ctx, arena, stmt->rhs->range.start);
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (var) {
    var->value = handle;
    var->NotifyWatchers();
  }
  ApplyClassParamOverrides(stmt->lhs->text, handle.ToUint64(), ctx, arena);
  return true;
}

bool TryTypedClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kMemberAccess) return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs->lhs || stmt->rhs->lhs->kind != ExprKind::kIdentifier)
    return false;
  if (!stmt->rhs->rhs || stmt->rhs->rhs->kind != ExprKind::kIdentifier)
    return false;
  if (stmt->rhs->rhs->text != "new") return false;
  auto* cls = ctx.FindClassType(stmt->rhs->lhs->text);
  if (!cls) return false;
  // §8.25: a parameterized class scope (E#(.N(77))::new) carries its
  // specialization overrides in the base identifier's elements. Bind them as
  // locals in a fresh scope before constructing so the constructor body reads
  // the overridden parameter values, mirroring the class-scope method path.
  bool parameterized = !stmt->rhs->lhs->elements.empty();
  if (parameterized) {
    ctx.PushScope();
    BindClassParams(cls, stmt->rhs->lhs, ctx, arena);
  }
  auto handle = EvalClassNew(stmt->rhs->lhs->text, nullptr, ctx, arena,
                             stmt->rhs->range.start);
  if (parameterized) ctx.PopScope();
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (var) {
    var->value = handle;
    var->NotifyWatchers();
  }
  return true;
}

// §8.4 / §8.12: `obj.field = new` where field is a class handle. The bare `new`
// carries no type context, so resolve field's declared class type from the AST,
// construct the object, and store the resulting handle through the member chain
// (WriteStructField reaches the real nested handle, so a later shallow copy
// shares it rather than falling back to a flat "field.x" key).
bool TryMemberClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall) return false;
  if (stmt->rhs->text != "new") return false;
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kMemberAccess) return false;
  if (!stmt->lhs->lhs || stmt->lhs->lhs->kind != ExprKind::kIdentifier)
    return false;
  if (!stmt->lhs->rhs || stmt->lhs->rhs->kind != ExprKind::kIdentifier)
    return false;
  auto base_type = ctx.GetVariableClassType(stmt->lhs->lhs->text);
  if (base_type.empty()) return false;
  const auto* cls = ctx.FindClassType(base_type);
  if (cls == nullptr) return false;
  auto field_type = MemberClassTypeName(cls, stmt->lhs->rhs->text);
  if (field_type.empty() || ctx.FindClassType(field_type) == nullptr)
    return false;
  auto handle =
      EvalClassNew(field_type, stmt->rhs, ctx, arena, stmt->rhs->range.start);
  WriteStructField(stmt->lhs, handle, ctx);
  return true;
}

}  // namespace delta
