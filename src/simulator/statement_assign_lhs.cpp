#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

// The variable a blocking assignment's left-hand side names when it is a
// name, a select on an unpacked array's element (§7.4) or a select on a
// compound of them: the spelling of the target (BuildLhsName,
// BuildCompoundLhsName, CompoundRootName) and the variable of the run's
// tables it stands for (TryResolveArrayElement, TryResolveCompoundElement,
// ResolveLhsVariable), each declared in statement_assign.h.

void BuildLhsName(const Expr* expr, std::string& out) {
  if (expr->kind == ExprKind::kIdentifier) {
    if (!expr->scope_prefix.empty()) {
      out += expr->scope_prefix;
      out += ".";
    }
    out += expr->text;
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    BuildLhsName(expr->lhs, out);
    out += ".";
    BuildLhsName(expr->rhs, out);
  }
}

// §7.4.6 (printed page 156) with §26.3 (printed 808): the array an indexed
// name writes an element of is a bare name's or, through the package scope
// resolution operator, a package's, `p1::a[1] = 7` targeting the element
// "p1.a[1]" CreatePackageArray (lowerer_register.cpp) created under the
// "p1.a" key ScopedOrBareTargetKey builds. An identifier base alone was
// taken before, so the scoped write fell through to a bit-select of the
// "p1.a" carrier and set its bit 1.
Variable* TryResolveArrayElement(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind != ExprKind::kSelect || !lhs->base || !lhs->index)
    return nullptr;
  if (lhs->index_end) return nullptr;
  std::string_view key = ScopedOrBareTargetKey(lhs->base, ctx.GetArena());
  if (key.empty()) return nullptr;
  auto idx = EvalExpr(lhs->index, ctx, ctx.GetArena());
  // An x or z bit anywhere in the index makes it invalid; an invalid-index
  // write is a no-op, so fail to resolve the element just as an out-of-range
  // index does.
  if (HasUnknownBits(idx)) return nullptr;
  auto elem_name =
      std::string(key) + "[" + std::to_string(idx.ToUint64()) + "]";
  return ctx.FindVariable(elem_name);
}

bool BuildCompoundLhsName(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string& name) {
  if (expr->kind == ExprKind::kIdentifier) {
    name = expr->text;
    return true;
  }
  if (expr->kind != ExprKind::kSelect || expr->index_end) return false;
  if (!BuildCompoundLhsName(expr->base, ctx, arena, name)) return false;
  auto idx_val = EvalExpr(expr->index, ctx, arena);
  // A dimension indexed with an x or z bit is invalid; refuse to build a name
  // for it so the surrounding write resolves to nothing and is a no-op.
  if (HasUnknownBits(idx_val)) return false;
  name += "[" + std::to_string(idx_val.ToUint64()) + "]";
  return true;
}

// The name of the identifier a compound indexed name stands on, `a` for
// `a[i][j]`, or empty where the chain does not stand on one.
std::string_view CompoundRootName(const Expr* e) {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  return (e != nullptr && e->kind == ExprKind::kIdentifier)
             ? e->text
             : std::string_view{};
}

// Whether the outermost index of a compound name lies outside the extent the
// array's ArrayInfo records for the dimension that name it. Only that dimension
// is asked: it is the one every such array has recorded, and a dimension the
// info does not describe cannot say the index is invalid.
static bool OutermostIndexIsOutOfRange(const Expr* lhs, const ArrayInfo& info,
                                       SimContext& ctx, Arena& arena) {
  const Expr* outer = lhs;
  while (outer->base != nullptr && outer->base->kind == ExprKind::kSelect)
    outer = outer->base;
  if (outer->index == nullptr) return false;
  auto idx = EvalExpr(outer->index, ctx, arena);
  if (HasUnknownBits(idx)) return true;
  auto value = idx.ToUint64();
  return value < info.lo || value >= static_cast<uint64_t>(info.lo) + info.size;
}

Variable* TryResolveCompoundElement(const Expr* lhs, SimContext& ctx,
                                    Arena& arena, bool* absent_element) {
  if (absent_element != nullptr) *absent_element = false;
  if (lhs->kind != ExprKind::kSelect || !lhs->base) return nullptr;
  if (lhs->base->kind != ExprKind::kSelect) return nullptr;
  if (lhs->index_end) return nullptr;
  std::string compound;
  if (!BuildCompoundLhsName(lhs, ctx, arena, compound)) return nullptr;
  if (auto* var = ctx.FindVariable(compound)) return var;
  const ArrayInfo* info = ctx.FindArrayInfo(CompoundRootName(lhs));
  // §7.4.5: "Writing to an array with an invalid index shall perform no
  // operation, with the exceptions of writing to element [$+1] of a queue
  // (described in 7.10.1) and creating a new element of an associative array
  // (described in 7.8.6)" -- and neither exception is an indexed name of this
  // shape, both being reached by their own writers before this one. The caller
  // is told rather than left to fall through, because the fallback resolution
  // walks the name down to the array's base carrier and would write a bit of
  // that instead.
  if (info != nullptr && OutermostIndexIsOutOfRange(lhs, *info, ctx, arena)) {
    if (absent_element != nullptr) *absent_element = true;
    return nullptr;
  }
  // The index is one the array holds, or one no recorded extent contradicts:
  // §7.4.4's dimensions may be "defined in stages with typedef", and only the
  // range the declaration itself wrote is recorded, so a second index of such
  // an array is answered by no extent at all and the element is materialized
  // here. It takes the array's own element width rather than a fixed 32 --
  // WriteVar sizes the value to the cell -- and the scope the write happens in,
  // so a name §23.9 keeps inside an instance can be read back where it was
  // written.
  uint32_t width = info != nullptr ? info->elem_width : 32;
  auto& name = *arena.Create<std::string>(std::move(compound));
  return ctx.HasLocalScope() ? ctx.CreateLocalVariable(name, width)
                             : ctx.CreateVariable(name, width);
}

Variable* ResolveLhsVariable(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind == ExprKind::kIdentifier) {
    // §3.12.1 (printed page 56): `$unit::g = 3` writes the compilation
    // unit's g under its "$unit.g" key (CreateUnitDataVariables in
    // lowerer_package_data.cpp) past a module's own `int g`, and a
    // `$root.`-prefixed target (§23.6) its "$root.g" key, which FindVariable
    // answers from the top of the design; both are the keys EvalIdentifier
    // (evaluation.cpp) reads by (IdentifierLookupKey). By the text alone
    // the write landed in the module's.
    return ctx.FindVariable(IdentifierLookupKey(lhs));
  }
  if (lhs->kind == ExprKind::kMemberAccess) {
    std::string name;
    BuildLhsName(lhs, name);
    auto resolved = StripRootPrefix(name);
    return ctx.FindVariable(resolved);
  }
  if (lhs->kind == ExprKind::kSelect && lhs->base) {
    return ResolveLhsVariable(lhs->base, ctx);
  }
  return nullptr;
}

}  // namespace delta
