#include <cmath>
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
                  Subclause("10.3.2"));
    } else {
      auto it = var_types_.find(name);
      if (it != var_types_.end() && it->second == DataTypeKind::kUwire) {
        diag_.Error(
            item->loc,
            std::format("uwire '{}' cannot have multiple drivers", name),
            Subclause("6.6.2"));
      }
    }
  }
  if (var_init_names_.count(name) != 0) {
    diag_.Error(item->loc,
                std::format("variable '{}' has both an initializer and a "
                            "continuous assignment",
                            name),
                Subclause("10.3.2"));
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
                  Subclause("10.3.2"));
    }
  }
  if (item->assign_lhs->kind == ExprKind::kMemberAccess) {
    auto* base = item->assign_lhs->lhs;
    if (base && base->kind == ExprKind::kIdentifier &&
        nettype_net_names_.count(base->text) != 0) {
      diag_.Error(item->loc,
                  "continuous assignment to a nettype net shall not contain "
                  "indexing or select",
                  Subclause("10.3.2"));
    }
  }
  if (item->assign_lhs->kind == ExprKind::kIdentifier &&
      nettype_net_names_.count(item->assign_lhs->text) != 0) {
    if (item->assign_delay_fall || item->assign_delay_decay) {
      diag_.Error(item->loc,
                  "continuous assignment to a nettype net shall have at most "
                  "a single delay",
                  Subclause("10.3.3"));
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
                Subclause("10.3.4"));
  }
}

namespace {

void ValidateContAssignVarTarget(ModuleItem* item, DiagEngine& diag) {
  if (item->drive_strength0 != 0 || item->drive_strength1 != 0) {
    diag.Error(item->loc,
               "drive strength not allowed on continuous assignment "
               "to a variable",
               Subclause("10.3.4"));
  }
  if (item->assign_delay_fall || item->assign_delay_decay) {
    diag.Error(item->loc,
               "multiple delays not allowed on continuous assignment "
               "to a variable",
               Subclause("10.3.3"));
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

// §11.5.1: the width of a select written as an element of a concatenation
// left-hand side, which the clause makes "always constant": the span its two
// indices name for `[msb:lsb]`, the width expression for the two indexed forms,
// and one bit for a bit-select. Zero where a bound does not fold, which is the
// answer for an element this cannot size at all.
uint32_t SelectLhsWidth(const Expr* e, const ScopeMap& scope) {
  if (e->index == nullptr) return 0;
  if (e->index_end == nullptr) return 1;
  if (e->is_part_select_plus || e->is_part_select_minus) {
    auto w = ConstEvalInt(e->index_end, scope);
    return (w && *w > 0) ? static_cast<uint32_t>(*w) : 0;
  }
  auto msb = ConstEvalInt(e->index, scope);
  auto lsb = ConstEvalInt(e->index_end, scope);
  if (!msb || !lsb) return 0;
  return static_cast<uint32_t>(std::abs(*msb - *lsb) + 1);
}

// §11.4.1/§10.10: total bit width of a continuous-assignment concatenation
// left-hand side (a nested concatenation sums its elements; identifiers reduce
// to their declared width).
//
// A select element is sized by its own indices rather than by the signal it
// selects from. LookupLhsWidth answers 0 for anything that is not a bare
// identifier, and the emission below passes over an element of width 0, so
// `assign {b, a[1:0]} = 3'b111;` emitted no assignment for `a` at all: the bits
// reached neither a driver nor the net's storage, and `b` took its slice from
// the wrong end of the value besides, the running offset never having advanced
// past the element that was skipped.
uint32_t ConcatLhsWidth(const Expr* e, const RtlirModule* mod,
                        const ScopeMap& scope) {
  if (e->kind == ExprKind::kSelect) return SelectLhsWidth(e, scope);
  if (e->kind != ExprKind::kConcatenation) return LookupLhsWidth(e, mod);
  uint32_t total = 0;
  for (const auto* sub : e->elements) total += ConcatLhsWidth(sub, mod, scope);
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
// names, so a slice of one can be written in its declared range.
struct ConcatContAssignCtx {
  ModuleItem* item;
  RtlirModule* mod;
  Arena& arena;
  DiagEngine& diag;
  const ScopeMap& scope;
};

// §11.5.1: the range a select on this right-hand side resolves against. A named
// signal carries the packed dimension of its declaration; anything else -- a
// literal, a concatenation, the widened expression below -- carries no
// declaration of its own and is addressed as [`width`-1:0].
PackedRange RhsSelectRange(const Expr* rhs, uint32_t width,
                           const ConcatContAssignCtx& cx) {
  if (rhs && rhs->kind == ExprKind::kIdentifier) {
    return SignalDeclaredRange(rhs->text, cx.mod, cx.scope);
  }
  return PackedRange::Implicit(width);
}

// §11.6.1 makes the whole target the context the right-hand side is evaluated
// in, and §11.8.2 propagates that width down into the context-determined
// operands of the expression. Splitting the assignment element by element takes
// the context away, each emitted assignment carrying only the width of the
// element it drives, so the expression under the slice is evaluated at the
// width its own operands give it. §10.3.2's Example 2 is what that loses:
// `assign {carry_out, sum_out} = ina + inb + carry_in;` has to add at five bits
// for the carry to exist at all.
//
// The width is put back the way §11.6.2 puts it back -- "adding an integer
// value of 0 to the expression will cause the evaluation to be performed using
// the bit size of integers" -- with a zero of the target's width rather than an
// integer's, so the addition is performed at the width the concatenation gives
// it and at no other. The zero is signed so that the widening does not change
// the type of what it widens: §11.8.1 makes a result unsigned "if any operand
// is unsigned", so an unsigned right-hand side stays unsigned and zero-extends
// into the new bits, and a signed one stays signed and sign-extends.
Expr* MakeWidenedRhs(Expr* rhs, uint32_t width, Arena& arena) {
  std::string text = std::format("{}'sd0", width);
  auto* zero = arena.Create<Expr>();
  zero->kind = ExprKind::kIntegerLiteral;
  zero->text = {arena.AllocString(text.c_str(), text.size()), text.size()};
  zero->range = rhs->range;
  auto* sum = arena.Create<Expr>();
  sum->kind = ExprKind::kBinary;
  sum->op = TokenKind::kPlus;
  sum->lhs = rhs;
  sum->rhs = zero;
  sum->range = rhs->range;
  return sum;
}

// §11.4.1: a continuous assignment to a concatenation drives each element from
// its own slice of the right-hand side; the leftmost element takes the most
// significant bits. Emit one assignment per (recursively flattened) element so
// each whole-identifier target registers its own net driver.
void EmitConcatContAssigns(const ConcatContAssignCtx& cx, Expr* lhs,
                           Expr* rhs) {
  uint32_t hi = ConcatLhsWidth(lhs, cx.mod, cx.scope);
  // Nothing to drive from, and nothing to drive into: a target whose elements
  // are all of unknown width leaves no assignment to emit, and a source the
  // parser never built leaves nothing to widen.
  if (hi == 0 || rhs == nullptr) return;
  // A signal named as the whole right-hand side and already as wide as the
  // target has nothing to widen: it has no operands of its own to evaluate, and
  // its bits are the target's bits. It is left as it stands, so the select
  // below goes on naming its bits in the range its declaration was written with
  // -- the most significant bit of `wire [8:1] src` is src[8], not src[7].
  uint32_t named_width =
      rhs->kind == ExprKind::kIdentifier ? LookupLhsWidth(rhs, cx.mod) : 0;
  Expr* source = named_width >= hi ? rhs : MakeWidenedRhs(rhs, hi, cx.arena);
  PackedRange range = RhsSelectRange(source, hi, cx);
  for (auto* el : lhs->elements) {
    uint32_t w = ConcatLhsWidth(el, cx.mod, cx.scope);
    if (w == 0) continue;
    Expr* elem_rhs = MakeRhsPartSelect(source, range.IndexAtOffset(hi - 1),
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
