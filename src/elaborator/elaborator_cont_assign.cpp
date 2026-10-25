#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_attribute.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

// §6.10 and §10.3.2 for an element of a continuous assignment's target that is
// a whole name: an undeclared one is an implicit net, a variable takes one
// continuous assignment and no initializer, and a uwire net one driver.
//
// §27.4 makes each generate block a scope of its own, and each iteration of a
// loop generate construct a block, so the targets are told apart by the
// declaration the name binds rather than by how it is spelled: a `w` each
// iteration declares is a variable of that iteration's and takes one
// assignment there.
void Elaborator::ValidateContAssignIdentLhs(std::string_view name,
                                            ModuleItem* item,
                                            RtlirModule* mod) {
  MaybeCreateImplicitNet(name, item->loc, mod);
  std::string_view declared =
      DeclaredScopedName(name, gen_prefix_scopes_, declared_names_);
  if (!cont_assign_targets_.emplace(declared, item->loc).second) {
    if (net_names_.count(name) == 0) {
      // §6.5 states the rule in full: multiple continuous assignments to any
      // term in the expansion of a variable's longest static prefix are an
      // error. §10.3.2 restates it and refers back, so the report cites §6.5.
      diag_.Error(item->loc,
                  std::format("multiple continuous assignments to '{}'", name),
                  Subclause("6.5"));
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
}

// §10.3.4 (printed page 251): a drive strength applies only to an assignment
// to a scalar net other than one of type supply0 or supply1, so a target that
// is a supply net or a select of one is excepted as the net is, and a select of
// a vector net, a member of a net of a packed structure type or a concatenation
// is no more a scalar net than a whole vector net is.
void Elaborator::ValidateContAssignDriveStrength(ModuleItem* item,
                                                 RtlirModule* mod) {
  const Expr* lhs = item->assign_lhs;
  std::string_view root = LhsBaseName(lhs);
  for (const auto& n : mod->nets) {
    if (n.name != root) continue;
    if (n.net_type != NetType::kSupply0 && n.net_type != NetType::kSupply1)
      break;
    diag_.Error(item->loc,
                "drive strength on continuous assignment does not apply to "
                "supply0 or supply1 nets",
                Subclause("10.3.4"));
    return;
  }
  if (lhs->kind == ExprKind::kIdentifier && LookupLhsWidth(lhs, mod) <= 1)
    return;
  diag_.Error(item->loc,
              "drive strength on continuous assignment applies only to "
              "scalar nets",
              Subclause("10.3.4"));
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

// §5.12: `attrs` are the item's attributes, resolved once for every
// assignment it splits into.
RtlirContAssign BuildContAssignFor(
    ModuleItem* item, Expr* lhs, Expr* rhs, uint32_t width,
    const std::vector<ResolvedAttribute>& attrs) {
  RtlirContAssign ca;
  ca.lhs = lhs;
  ca.rhs = rhs;
  ca.source_item = item;
  ca.width = width;
  ca.drive_strength0 = item->drive_strength0;
  ca.drive_strength1 = item->drive_strength1;
  ca.delay = item->assign_delay;
  ca.delay_fall = item->assign_delay_fall;
  ca.delay_decay = item->assign_delay_decay;
  ca.attrs = attrs;
  return ca;
}

RtlirContAssign BuildContAssign(ModuleItem* item, RtlirModule* mod,
                                const std::vector<ResolvedAttribute>& attrs) {
  return BuildContAssignFor(item, item->assign_lhs, item->assign_rhs,
                            LookupLhsWidth(item->assign_lhs, mod), attrs);
}

}  // namespace

// §11.5.1: the width of a select written as an element of a concatenation
// left-hand side, which the clause keeps constant: the span its two indices
// name for `[msb:lsb]`, the width expression for the two indexed forms, and one
// bit for a bit-select. Zero where a bound does not fold, which is the answer
// for an element this cannot size at all.
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

namespace {

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
// names, so a slice of one can be written in its declared range; `attrs` are
// the item's resolved attributes, which each split assignment carries.
struct ConcatContAssignCtx {
  ModuleItem* item;
  RtlirModule* mod;
  Arena& arena;
  const std::vector<ResolvedAttribute>& attrs;
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
// The width is put back the way §11.6.2 puts it back -- adding an integer 0 to
// an expression makes it evaluate at an integer's bit size -- with a zero of
// the target's width rather than an integer's, so the addition is performed at
// the width the concatenation gives it and at no other. The zero is signed so
// that the widening does not change the type of what it widens: §11.8.1 makes a
// result unsigned when any operand is unsigned, so an unsigned right-hand side
// stays unsigned and zero-extends into the new bits, and a signed one stays
// signed and sign-extends.
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
          BuildContAssignFor(cx.item, el, elem_rhs, w, cx.attrs));
    }
  }
}

}  // namespace

// One element of a continuous assignment's target: the expression, the name
// it is rooted at, how many selects stand between that name and the first
// member access over it, and whether it holds a member access at all.
struct ContTargetLeaf {
  const Expr* expr = nullptr;
  std::string_view root = {};
  size_t selects = 0;
  bool has_member = false;
};

// The element `e` of a target, walked down through its selects and member
// accesses to the name it is rooted at; the root is empty where that is no
// name.
static ContTargetLeaf LeafOf(const Expr* e) {
  ContTargetLeaf leaf{.expr = e};
  while (e->kind == ExprKind::kSelect || e->kind == ExprKind::kMemberAccess) {
    if (e->kind == ExprKind::kMemberAccess) {
      leaf.has_member = true;
      leaf.selects = 0;
      e = e->lhs;
    } else {
      ++leaf.selects;
      e = e->base;
    }
  }
  if (e->kind == ExprKind::kIdentifier) leaf.root = e->text;
  return leaf;
}

// §10.3 Syntax 10-1: a continuous assignment's target is a net_lvalue or a
// variable_lvalue -- a name under constant selects and member accesses, a
// concatenation of those, or an assignment pattern of them with or without a
// type, whose keys §10.9's own rule reports. A.8.5 writes none of them in
// parentheses. Collects its elements, answering false for any other form.
static bool CollectContTargetLeaves(const Expr* e,
                                    std::vector<ContTargetLeaf>& out) {
  if (e->is_parenthesized) return false;
  if (e->kind == ExprKind::kCast &&
      e->lhs->kind == ExprKind::kAssignmentPattern)
    e = e->lhs;
  if (e->kind == ExprKind::kConcatenation ||
      e->kind == ExprKind::kAssignmentPattern) {
    for (const Expr* el : e->elements)
      if (!CollectContTargetLeaves(el, out)) return false;
    return true;
  }
  if (e->kind == ExprKind::kStreamingConcat) return true;
  ContTargetLeaf leaf = LeafOf(e);
  if (leaf.root.empty()) return false;
  out.push_back(leaf);
  return true;
}

// Whether `name` is a parameter of `mod` that a reference standing in the
// generate blocks `scopes` sees: §23.9 keeps a block's parameter from the
// module and from the block's siblings.
static bool NamesParameter(std::string_view name, const RtlirModule* mod,
                           const std::vector<std::string_view>& scopes) {
  for (const auto& p : mod->params) {
    if (p.name == name && ParamVisibleFromScopes(p.gen_block_prefix, scopes))
      return true;
  }
  return false;
}

// A driven terminal is read as a continuous assignment's target is, since
// A.8.5's net_lvalue gives the two their elements; a form the parser already
// reported as no net_lvalue yields no element, or fewer. A terminal left empty
// on a UDP instance written before its primitive's declaration is a null, and
// yields none: Elaborator::ReclassifyForwardUdpInstances
// (src/elaborator/elaborator_udp_inst.cpp) has already reported it.
void ValidatePrimitiveDrivenTerminals(
    const ModuleItem* item, const RtlirModule* mod, const ScopeMap& scope,
    const std::vector<std::string_view>& gen_scopes, DiagEngine& diag) {
  std::vector<ContTargetLeaf> leaves;
  for (size_t i : PrimitiveDrivenTerminalIndices(item)) {
    if (item->gate_terminals[i] == nullptr) continue;
    CollectContTargetLeaves(item->gate_terminals[i], leaves);
  }
  for (const ContTargetLeaf& leaf : leaves) {
    if (NamesParameter(leaf.root, mod, gen_scopes)) {
      diag.Error(item->loc,
                 std::format("a primitive's output or inout terminal names "
                             "parameter '{}', a constant no primitive drives",
                             leaf.root),
                 Subclause("A.8.5"));
    } else if (!SelectPathIsConstant(leaf.expr, scope)) {
      diag.Error(item->loc,
                 "a primitive's output or inout terminal selects with an "
                 "expression that is not constant",
                 Subclause("A.8.5"));
    }
  }
}

static size_t UnpackedDimsOfNet(std::string_view name, const RtlirModule* mod) {
  for (const auto& n : mod->nets)
    if (n.name == name) return n.num_unpacked_dims;
  return 0;
}

// The rules §10.3 and §10.3.2 state of one element of a continuous
// assignment's target, and whether it is a variable, whose form (Syntax 10-1)
// takes no drive strength and a delay_control alone.
bool Elaborator::ValidateContAssignLeaf(ModuleItem* item, RtlirModule* mod,
                                        const ContTargetLeaf& leaf,
                                        const ScopeMap& scope) {
  // §10.2 and §10.3: a continuous assignment drives a net or a variable, and a
  // parameter is a constant (§6.20).
  if (NamesParameter(leaf.root, mod, gen_prefix_scopes_)) {
    diag_.Error(
        item->loc,
        std::format("continuous assignment to parameter '{}'", leaf.root),
        Subclause("10.3"));
    return false;
  }
  // Table 10-1 (printed page 247): every select on the left-hand side of a
  // continuous assignment is a constant one, however deep it stands.
  if (!SelectPathIsConstant(leaf.expr, scope)) {
    diag_.Error(item->loc,
                "continuous assignment left-hand side requires a "
                "constant select expression",
                Subclause("10.3.2"));
  }
  if (leaf.expr->kind == ExprKind::kIdentifier)
    ValidateContAssignIdentLhs(leaf.root, item, mod);
  // A name reached through a member access may be an instance's or an
  // interface's, which names no variable of this module, so only a name the
  // target writes directly or through selects is judged as a variable here.
  bool is_net = net_names_.count(leaf.root) != 0;
  bool is_var = !is_net && !leaf.has_member;
  if (is_var) ValidateContAssignVarLeaf(item, leaf.root);
  // §10.3.2: an assignment to a net of a user-defined nettype drives the whole
  // net, so it may select an element of an array of such nets and nothing
  // within the nettype's data type.
  if (nettype_net_names_.count(leaf.root) != 0 &&
      (leaf.has_member || leaf.selects > UnpackedDimsOfNet(leaf.root, mod))) {
    diag_.Error(item->loc,
                "a continuous assignment to a net of a user-defined nettype "
                "drives the whole net and cannot index or select into it",
                Subclause("10.3.2"));
  }
  // A.6.1: a member of a variable this module declares is a variable_lvalue as
  // the variable is, so the assignment takes the variable form all the same.
  return is_var || (!is_net && var_types_.count(leaf.root) != 0);
}

// §6.5 and §10.3.2 of a variable an element of a continuous assignment's
// target writes. The module's procedural assignments were recorded before its
// generate blocks are elaborated, so an assignment a block makes is weighed
// against them here; a module's own is weighed by
// Elaborator::ValidateMixedAssignments once all of them are known. A variable
// a continuous assignment writes any part of has no initializer.
void Elaborator::ValidateContAssignVarLeaf(ModuleItem* item,
                                           std::string_view name) {
  std::string_view declared =
      DeclaredScopedName(name, gen_prefix_scopes_, declared_names_);
  if (!gen_prefix_scopes_.empty() &&
      proc_assign_targets_.count(declared) != 0) {
    diag_.Error(item->loc,
                std::format("variable '{}' has both continuous and "
                            "procedural assignments",
                            name),
                Subclause("6.5"));
  }
  if (var_init_names_.count(declared) != 0) {
    diag_.Error(item->loc,
                std::format("variable '{}' has both an initializer and a "
                            "continuous assignment",
                            name),
                Subclause("10.3.2"));
  }
}

// Whether any element of a continuous assignment's target is a variable.
bool Elaborator::ValidateContAssignLeaves(
    ModuleItem* item, RtlirModule* mod,
    const std::vector<ContTargetLeaf>& leaves) {
  // §11.2.1 with §27.4: a select index may name a parameter, or the genvar of
  // the loop generate block the assignment stands in.
  ScopeMap scope = BuildParamScope(mod);
  for (const auto& [name, value] : gen_const_scope_) scope[name] = value;
  bool any_var = false;
  for (const ContTargetLeaf& leaf : leaves) {
    if (ValidateContAssignLeaf(item, mod, leaf, scope)) any_var = true;
  }
  return any_var;
}

// §28.3.2 with §10.3.4 (printed page 251): (highz0, highz1) is no drive
// strength a net declaration, a continuous assignment or a gate may take.
void CheckHighzStrengthPair(const ModuleItem* item, DiagEngine& diag) {
  if ((item->kind == ModuleItemKind::kNetDecl ||
       item->kind == ModuleItemKind::kContAssign ||
       item->kind == ModuleItemKind::kGateInst ||
       item->kind == ModuleItemKind::kUdpInst) &&
      item->drive_strength0 == 1 && item->drive_strength1 == 1) {
    diag.Error(item->loc, "drive strength (highz0, highz1) is illegal",
               Subclause("28.3.2"));
  }
}

// §27.3 (printed page 818): a generate block's items act as the module's own
// would, so the strength pair §10.3.4 forbids, §10.4's rule that a procedural
// assignment writes no net and the one-driver rule of §6.5 and §10.3.2 reach
// them. The module's own checks run before its generate blocks are
// elaborated, so each item of a block is checked as the block is, against the
// targets the module's items and the earlier items recorded. Both tables hold
// a variable under the declaration the name binds, as
// ValidateContAssignIdentLhs records it.
void Elaborator::ValidateGeneratedItem(const ModuleItem* item) {
  CheckHighzStrengthPair(item, diag_);
  if (!IsProceduralItemKind(item->kind)) return;
  std::unordered_map<std::string_view, SourceLoc> targets;
  CollectProcTargets({}, {item->body}, targets);
  for (const auto& [name, loc] : targets) {
    if (net_names_.count(name) != 0) {
      diag_.Error(loc,
                  std::format("net '{}' cannot be the target of a "
                              "procedural assignment",
                              name),
                  Subclause("10.4"));
      continue;
    }
    std::string_view declared =
        DeclaredScopedName(name, gen_prefix_scopes_, declared_names_);
    if (cont_assign_targets_.count(declared) != 0) {
      diag_.Error(loc,
                  std::format("variable '{}' has both continuous and "
                              "procedural assignments",
                              name),
                  Subclause("6.5"));
    }
    proc_assign_targets_.emplace(declared, loc);
  }
}

// §10.3.2 (printed page 249): a variable may be driven by one primitive
// output as by one continuous assignment, and one so driven takes neither an
// initializer nor a procedural assignment. An n-output gate drives every
// terminal but its last (§28.4); every other primitive drives its first.
void Elaborator::RecordGateOutputDrivers(const ModuleItem* item) {
  size_t count = item->gate_terminals.size();
  bool n_output =
      item->gate_kind == GateKind::kBuf || item->gate_kind == GateKind::kNot;
  size_t outputs = std::min<size_t>(count, n_output ? count - 1 : 1);
  for (size_t i = 0; i < outputs; ++i) {
    std::string_view name = ExprIdent(item->gate_terminals[i]);
    if (name.empty() || net_names_.count(name) != 0) continue;
    std::string_view declared =
        DeclaredScopedName(name, gen_prefix_scopes_, declared_names_);
    if (!cont_assign_targets_.emplace(declared, item->loc).second) {
      diag_.Error(item->loc,
                  std::format("variable '{}' is driven by more than one "
                              "continuous assignment or primitive output",
                              name),
                  Subclause("10.3.2"));
    }
    if (var_init_names_.count(declared) != 0) {
      diag_.Error(item->loc,
                  std::format("variable '{}' has both an initializer and a "
                              "primitive output driving it",
                              name),
                  Subclause("10.3.2"));
    }
  }
}

// Whether an element of a target reaches a net through a member access taken
// of a name that is no net of this module -- an instance's or an interface
// port's -- whose declaration this module does not hold. A member of this
// module's own net is part of that net.
static bool ReachesAnotherScope(
    const std::vector<ContTargetLeaf>& leaves,
    const std::unordered_set<std::string_view>& net_names) {
  return std::ranges::any_of(leaves, [&](const ContTargetLeaf& leaf) {
    return leaf.has_member && net_names.count(leaf.root) == 0;
  });
}

// §11.4.14.3 (printed page 292): a streaming concatenation written as a target
// unpacks the stream into variables, as A.8.5 writes the form among
// variable_lvalue's alone, so a net among its stream expressions, a nested
// streaming concatenation's or a concatenation's among them, is reported.
static void ReportStreamTargetNets(
    const Expr* e, const std::unordered_set<std::string_view>& net_names,
    SourceLoc loc, DiagEngine& diag) {
  if (e->kind == ExprKind::kStreamingConcat ||
      e->kind == ExprKind::kConcatenation) {
    for (const Expr* el : e->elements)
      ReportStreamTargetNets(el, net_names, loc, diag);
    return;
  }
  std::string_view name = LhsBaseName(e);
  if (net_names.count(name) == 0) return;
  diag.Error(loc,
             std::format("a streaming concatenation written as a target "
                         "unpacks into variables, and '{}' is a net",
                         name),
             Subclause("11.4.14.3"));
}

void Elaborator::ElaborateContAssign(ModuleItem* item, RtlirModule* mod) {
  std::vector<ContTargetLeaf> leaves;
  if (!CollectContTargetLeaves(item->assign_lhs, leaves)) {
    diag_.Error(item->loc,
                "continuous assignment target is not a net or variable "
                "lvalue",
                Subclause("10.3"));
    return;
  }
  // A.8.5 writes a streaming concatenation among variable_lvalue's alone, so
  // an assignment to one takes A.6.1's variable form.
  bool streaming = item->assign_lhs->kind == ExprKind::kStreamingConcat;
  if (streaming)
    ReportStreamTargetNets(item->assign_lhs, net_names_, item->loc, diag_);
  // A net reached through a member access of another scope's name is that
  // scope's, whose declaration this module does not hold, so its strength goes
  // unjudged.
  if (ValidateContAssignLeaves(item, mod, leaves) || streaming) {
    ValidateContAssignVarTarget(item, diag_);
  } else if ((item->drive_strength0 != 0 || item->drive_strength1 != 0) &&
             !ReachesAnotherScope(leaves, net_names_)) {
    ValidateContAssignDriveStrength(item, mod);
  }
  if (item->assign_lhs->kind == ExprKind::kIdentifier &&
      nettype_net_names_.count(item->assign_lhs->text) != 0 &&
      (item->assign_delay_fall || item->assign_delay_decay)) {
    diag_.Error(item->loc,
                "continuous assignment to a nettype net shall have at most "
                "a single delay",
                Subclause("10.3.3"));
  }
  ValidateGetpatternContAssign(item, mod);
  // §5.12: the attributes fold their values against the module's parameters.
  ScopeMap scope = BuildParamScope(mod);
  const std::vector<ResolvedAttribute> kAttrs =
      ResolveAttributes(item->attrs, diag_, scope);
  if (item->assign_lhs->kind == ExprKind::kConcatenation) {
    ConcatContAssignCtx cx{item, mod, arena_, kAttrs, scope};
    EmitConcatContAssigns(cx, item->assign_lhs, item->assign_rhs);
    return;
  }
  mod->assigns.push_back(BuildContAssign(item, mod, kAttrs));
}

}  // namespace delta
