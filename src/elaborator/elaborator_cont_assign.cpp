#include <cstdint>
#include <format>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::ValidateContAssignIdentLhs(ModuleItem* item,
                                            RtlirModule* mod) {
  auto name = item->assign_lhs->text;
  MaybeCreateImplicitNet(name, item->loc, mod);
  if (!cont_assign_targets_.emplace(name, item->loc).second) {
    if (net_names_.count(name) == 0) {
      diag_.Error(item->loc,
                  std::format("multiple continuous assignments to '{}'", name),
                  Subclause::Unread());
    } else {
      auto it = var_types_.find(name);
      if (it != var_types_.end() && it->second == DataTypeKind::kUwire) {
        diag_.Error(
            item->loc,
            std::format("uwire '{}' cannot have multiple drivers", name),
            Subclause::Unread());
      }
    }
  }
  if (var_init_names_.count(name) != 0) {
    diag_.Error(item->loc,
                std::format("variable '{}' has both an initializer and a "
                            "continuous assignment",
                            name),
                Subclause::Unread());
  }
}

void Elaborator::ValidateContAssignNettypeAndDelay(ModuleItem* item) {
  if (item->assign_lhs->kind == ExprKind::kSelect) {
    auto* base = item->assign_lhs->base;
    if (base && base->kind == ExprKind::kIdentifier &&
        nettype_net_names_.count(base->text) != 0) {
      diag_.Error(item->loc,
                  "continuous assignment to a nettype net shall not contain "
                  "indexing or select",
                  Subclause::Unread());
    }
  }
  if (item->assign_lhs->kind == ExprKind::kMemberAccess) {
    auto* base = item->assign_lhs->lhs;
    if (base && base->kind == ExprKind::kIdentifier &&
        nettype_net_names_.count(base->text) != 0) {
      diag_.Error(item->loc,
                  "continuous assignment to a nettype net shall not contain "
                  "indexing or select",
                  Subclause::Unread());
    }
  }
  if (item->assign_lhs->kind == ExprKind::kIdentifier &&
      nettype_net_names_.count(item->assign_lhs->text) != 0) {
    if (item->assign_delay_fall || item->assign_delay_decay) {
      diag_.Error(item->loc,
                  "continuous assignment to a nettype net shall have at most "
                  "a single delay",
                  Subclause::Unread());
    }
  }
}

void Elaborator::ValidateContAssignDriveStrength(ModuleItem* item,
                                                 RtlirModule* mod) {
  if (item->assign_lhs->kind != ExprKind::kIdentifier) return;
  uint32_t lhs_width = LookupLhsWidth(item->assign_lhs, mod);
  if (lhs_width <= 1) return;
  bool is_supply = false;
  for (const auto& n : mod->nets) {
    if (n.name == item->assign_lhs->text) {
      is_supply =
          (n.net_type == NetType::kSupply0 || n.net_type == NetType::kSupply1);
      break;
    }
  }
  if (!is_supply) {
    diag_.Error(item->loc,
                "drive strength on continuous assignment applies only to "
                "scalar nets",
                Subclause::Unread());
  }
}

namespace {

void ValidateContAssignVarTarget(ModuleItem* item, DiagEngine& diag) {
  if (item->drive_strength0 != 0 || item->drive_strength1 != 0) {
    diag.Error(item->loc,
               "drive strength not allowed on continuous assignment "
               "to a variable",
               Subclause::Unread());
  }
  if (item->assign_delay_fall || item->assign_delay_decay) {
    diag.Error(item->loc,
               "multiple delays not allowed on continuous assignment "
               "to a variable",
               Subclause::Unread());
  }
}

RtlirContAssign BuildContAssignFor(ModuleItem* item, Expr* lhs, Expr* rhs,
                                   uint32_t width, DiagEngine& diag) {
  RtlirContAssign ca;
  ca.lhs = lhs;
  ca.rhs = rhs;
  ca.width = width;
  ca.drive_strength0 = item->drive_strength0;
  ca.drive_strength1 = item->drive_strength1;
  ca.delay = item->assign_delay;
  ca.delay_fall = item->assign_delay_fall;
  ca.delay_decay = item->assign_delay_decay;
  ca.attrs = ResolveAttributes(item->attrs, diag);
  return ca;
}

RtlirContAssign BuildContAssign(ModuleItem* item, RtlirModule* mod,
                                DiagEngine& diag) {
  return BuildContAssignFor(item, item->assign_lhs, item->assign_rhs,
                            LookupLhsWidth(item->assign_lhs, mod), diag);
}

// §11.4.1/§10.10: total bit width of a continuous-assignment concatenation
// left-hand side (a nested concatenation sums its elements; identifiers reduce
// to their declared width).
uint32_t ConcatLhsWidth(const Expr* e, const RtlirModule* mod) {
  if (e->kind != ExprKind::kConcatenation) return LookupLhsWidth(e, mod);
  uint32_t total = 0;
  for (const auto* sub : e->elements) total += ConcatLhsWidth(sub, mod);
  return total;
}

// `rhs[first:second]`. Both operands are indices of `rhs` in the range its
// declaration was written with, which is what §11.5.1 resolves a select
// against; the caller maps the bits it wants onto them.
Expr* MakeRhsPartSelect(Expr* rhs, int64_t first, int64_t second,
                        Arena& arena) {
  auto* hi_lit = arena.Create<Expr>();
  hi_lit->kind = ExprKind::kIntegerLiteral;
  hi_lit->int_val = static_cast<uint64_t>(first);
  auto* lo_lit = arena.Create<Expr>();
  lo_lit->kind = ExprKind::kIntegerLiteral;
  lo_lit->int_val = static_cast<uint64_t>(second);
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = rhs;
  sel->index = hi_lit;
  sel->index_end = lo_lit;
  return sel;
}

// Recursion-invariant context for splitting a concatenation continuous-assign
// lvalue (bundled to keep the helper within the parameter-count threshold).
// `scope` folds the packed dimension of whatever signal the right-hand side
// names, so the slices below can be written in its declared range.
struct ConcatContAssignCtx {
  ModuleItem* item;
  RtlirModule* mod;
  Arena& arena;
  DiagEngine& diag;
  const ScopeMap& scope;
};

// §11.5.1: the range a select on this right-hand side resolves against. A named
// signal carries the packed dimension of its declaration; anything else -- a
// literal, a concatenation, the nested part-select the recursion below builds
// -- carries no declaration of its own and is addressed as [`width`-1:0].
DeclaredPackedRange RhsSelectRange(const Expr* rhs, uint32_t width,
                                   const ConcatContAssignCtx& cx) {
  if (rhs && rhs->kind == ExprKind::kIdentifier) {
    return SignalDeclaredRange(rhs->text, cx.mod, cx.scope);
  }
  return DeclaredPackedRange::Implicit(width);
}

// §11.4.1: a continuous assignment to a concatenation drives each element from
// its own slice of the right-hand side; the leftmost element takes the most
// significant bits. Emit one assignment per (recursively flattened) element so
// each whole-identifier target registers its own net driver.
void EmitConcatContAssigns(const ConcatContAssignCtx& cx, Expr* lhs,
                           Expr* rhs) {
  uint32_t hi = ConcatLhsWidth(lhs, cx.mod);
  // §11.5.1: `hi` counts bits up from the least significant end of the
  // right-hand side, and the select naming a run of them has to name them by
  // their index in the range the right-hand side was declared with -- the most
  // significant bit of `wire [8:1] src` is src[8], not src[7].
  DeclaredPackedRange range = RhsSelectRange(rhs, hi, cx);
  for (auto* el : lhs->elements) {
    uint32_t w = ConcatLhsWidth(el, cx.mod);
    if (w == 0) continue;
    Expr* elem_rhs = MakeRhsPartSelect(rhs, range.IndexAtOffset(hi - 1),
                                       range.IndexAtOffset(hi - w), cx.arena);
    hi -= w;
    if (el->kind == ExprKind::kConcatenation) {
      EmitConcatContAssigns(cx, el, elem_rhs);
    } else {
      cx.mod->assigns.push_back(
          BuildContAssignFor(cx.item, el, elem_rhs, w, cx.diag));
    }
  }
}

}  // namespace

void Elaborator::ElaborateContAssign(ModuleItem* item, RtlirModule* mod) {
  if (item->assign_lhs && item->assign_lhs->kind == ExprKind::kIdentifier) {
    ValidateContAssignIdentLhs(item, mod);

    bool is_var_target = net_names_.count(item->assign_lhs->text) == 0;
    if (is_var_target) {
      ValidateContAssignVarTarget(item, diag_);
    }
  }
  if (item->assign_lhs) {
    ValidateContAssignNettypeAndDelay(item);
  }
  if ((item->drive_strength0 != 0 || item->drive_strength1 != 0) &&
      item->assign_lhs) {
    ValidateContAssignDriveStrength(item, mod);
  }
  if (item->assign_lhs && item->assign_lhs->kind == ExprKind::kConcatenation) {
    ScopeMap scope = BuildParamScope(mod);
    ConcatContAssignCtx cx{item, mod, arena_, diag_, scope};
    EmitConcatContAssigns(cx, item->assign_lhs, item->assign_rhs);
    return;
  }
  mod->assigns.push_back(BuildContAssign(item, mod, diag_));
}

}  // namespace delta
