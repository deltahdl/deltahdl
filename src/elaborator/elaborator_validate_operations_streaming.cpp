#include <charconv>
#include <format>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

bool Elaborator::ConcatContainsStringElement(const Expr* expr) {
  if (!expr) return false;
  if (expr->kind == ExprKind::kIdentifier) {
    auto it = var_types_.find(expr->text);
    return it != var_types_.end() && it->second == DataTypeKind::kString;
  }
  if (expr->kind == ExprKind::kStringLiteral) return true;
  if (expr->kind == ExprKind::kConcatenation) {
    for (const auto* elem : expr->elements) {
      if (ConcatContainsStringElement(elem)) return true;
    }
  }
  return false;
}

void Elaborator::CheckStringConcatLvalue(const Expr* lhs) {
  if (!lhs) return;
  if (lhs->kind != ExprKind::kConcatenation) return;
  if (ConcatContainsStringElement(lhs)) {
    diag_.Error(lhs->range.start,
                "string concatenation is not allowed on the left-hand side "
                "of an assignment");
  }
}

void Elaborator::WalkStmtsForStringConcatLvalue(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign || s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    CheckStringConcatLvalue(s->lhs);
  }
  for (auto* sub : s->stmts) WalkStmtsForStringConcatLvalue(sub);
  WalkStmtsForStringConcatLvalue(s->then_branch);
  WalkStmtsForStringConcatLvalue(s->else_branch);
  WalkStmtsForStringConcatLvalue(s->body);
  WalkStmtsForStringConcatLvalue(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForStringConcatLvalue(ci.body);
}

void Elaborator::ValidateStringConcatLvalue(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForStringConcatLvalue(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckStringConcatLvalue(item->assign_lhs);
    }
  }
}

static bool ClassHasHiddenMember(const ClassDecl* cls);

namespace {

// §11.4.14.1: validate a single streaming-concatenation operand for the two
// statically recognisable illegal cases (a class handle exposing local or
// protected members, and a non-bit-stream scalar type).
void CheckStreamingConcatOperand(
    const Expr* elem, DiagEngine& diag,
    const std::unordered_map<std::string_view, std::string_view>&
        class_var_types,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types,
    CompilationUnit* unit) {
  // §11.4.14.1: when a non-null class handle is streamed, its data members
  // are packed in turn. Streaming a handle whose class exposes local or
  // protected members is illegal unless those members are accessible at
  // the streaming operator, approximated here (as in the bit-stream cast
  // rule of §6.24.3) by allowing only the current instance `this`.
  if (elem && elem->kind == ExprKind::kIdentifier && elem->text != "this") {
    auto it = class_var_types.find(elem->text);
    if (it != class_var_types.end() &&
        ClassHasHiddenMember(FindClassDecl(it->second, unit))) {
      diag.Error(elem->range.start,
                 std::format("class handle '{}' is illegal as a streaming "
                             "concatenation operand: its class has local "
                             "or protected members",
                             elem->text));
    }
  }
  // §11.4.14.1: an operand that is none of a bit-stream type, an unpacked
  // array, a struct, an untagged union, or a class handle cannot be packed
  // into the stream; such an operand is skipped and an error is issued. The
  // statically recognizable non-bit-stream scalar types are the real
  // family, event, chandle, and virtual interface.
  if (elem && elem->kind == ExprKind::kIdentifier) {
    auto vt = var_types.find(elem->text);
    if (vt != var_types.end()) {
      auto k = vt->second;
      if (IsRealType(k) || k == DataTypeKind::kEvent ||
          k == DataTypeKind::kChandle || k == DataTypeKind::kVirtualInterface) {
        diag.Error(elem->range.start,
                   std::format("'{}' is not a bit-stream type and cannot "
                               "be a streaming concatenation operand",
                               elem->text));
      }
    }
  }
}

// §11.4.14.2: a slice_size written as a constant integral expression names
// the block width used to re-order the generic stream, so its value must be
// positive; a zero or negative slice size is illegal. A slice_size given as
// a simple type instead names a block width equal to that type's size,
// which is inherently positive and therefore exempt from this check. The
// parser records a bare numeric slice_size as an identifier carrying the
// literal text, while a non-numeric identifier names a type.
void CheckStreamingSliceSize(const Expr* slice, DiagEngine& diag,
                             const ScopeMap& param_scope) {
  if (!slice) return;
  std::optional<int64_t> value;
  if (slice->kind == ExprKind::kIdentifier) {
    int64_t parsed = 0;
    const char* begin = slice->text.data();
    const char* end = begin + slice->text.size();
    auto [ptr, ec] = std::from_chars(begin, end, parsed);
    if (ec == std::errc() && ptr == end) value = parsed;
  } else {
    // A constant-expression slice_size may name a parameter or localparam
    // (§11.2.1), so fold it in the module's parameter scope; a bare literal
    // folds identically whether or not the scope carries any names.
    value = ConstEvalInt(slice, param_scope);
  }
  if (value && *value <= 0) {
    diag.Error(slice->range.start,
               "streaming slice_size shall be a positive constant");
  }
}

}  // namespace

void Elaborator::WalkExprForStreamingContext(const Expr* expr,
                                             bool is_valid_context) {
  if (!expr) return;
  if (expr->kind == ExprKind::kStreamingConcat) {
    if (!is_valid_context) {
      diag_.Error(expr->range.start,
                  "streaming concatenation shall not be used as an operand "
                  "of an expression other than an assignment or bit-stream "
                  "cast");
    }

    for (auto* elem : expr->elements) {
      CheckStreamingConcatOperand(elem, diag_, class_var_types_, var_types_,
                                  unit_);
      WalkExprForStreamingContext(elem, true);
    }

    CheckStreamingSliceSize(expr->lhs, diag_, streaming_slice_size_scope_);

    WalkExprForStreamingContext(expr->lhs, false);
    return;
  }
  if (expr->kind == ExprKind::kCast) {
    WalkExprForStreamingContext(expr->lhs, true);
    return;
  }

  WalkExprForStreamingContext(expr->lhs, false);
  WalkExprForStreamingContext(expr->rhs, false);
  WalkExprForStreamingContext(expr->condition, false);
  WalkExprForStreamingContext(expr->true_expr, false);
  WalkExprForStreamingContext(expr->false_expr, false);
  for (auto* elem : expr->elements) WalkExprForStreamingContext(elem, false);
  for (auto* arg : expr->args) WalkExprForStreamingContext(arg, false);
}

// §11.4.14: a streaming_concatenation used as the source of an assignment
// requires a target that is either another streaming_concatenation or a data
// object of bit-stream type. Reject the obviously-non-bit-stream targets we
// can recognise from the variable-type map (real family, event, chandle,
// virtual interface). Targets we cannot type-check from a simple identifier
// (selects, member accesses) are left to type-aware downstream checks.
void Elaborator::CheckStreamingSourceTargetType(const Expr* lhs,
                                                const Expr* rhs) {
  if (!lhs || !rhs) return;
  if (rhs->kind != ExprKind::kStreamingConcat) return;
  if (lhs->kind == ExprKind::kStreamingConcat) return;
  if (lhs->kind != ExprKind::kIdentifier) return;
  auto it = var_types_.find(lhs->text);
  if (it == var_types_.end()) return;
  auto k = it->second;
  bool not_bitstream = IsRealType(k) || k == DataTypeKind::kEvent ||
                       k == DataTypeKind::kChandle ||
                       k == DataTypeKind::kVirtualInterface;
  if (not_bitstream) {
    diag_.Error(lhs->range.start,
                "target of a streaming concatenation source assignment must "
                "be a bit-stream type");
  }
}

void Elaborator::WalkStmtsForStreamingContext(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign || s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    WalkExprForStreamingContext(s->lhs, true);
    WalkExprForStreamingContext(s->rhs, true);
    CheckStreamingSourceTargetType(s->lhs, s->rhs);
  } else {
    WalkExprForStreamingContext(s->lhs, false);
    WalkExprForStreamingContext(s->rhs, false);
  }
  WalkExprForStreamingContext(s->expr, false);
  WalkExprForStreamingContext(s->condition, false);
  WalkExprForStreamingContext(s->assert_expr, false);
  for (auto* sub : s->stmts) WalkStmtsForStreamingContext(sub);
  WalkStmtsForStreamingContext(s->then_branch);
  WalkStmtsForStreamingContext(s->else_branch);
  WalkStmtsForStreamingContext(s->body);
  WalkStmtsForStreamingContext(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForStreamingContext(ci.body);
}

void Elaborator::ValidateStreamingConcatContext(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForStreamingContext(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForStreamingContext(item->assign_lhs, true);
      WalkExprForStreamingContext(item->assign_rhs, true);
      CheckStreamingSourceTargetType(item->assign_lhs, item->assign_rhs);
    }
  }
}

// §6.24.3: a class is illegal as a bit-stream-cast source when it exposes any
// local or protected member, except when the source handle is the keyword
// `this` (the current instance retains private access).
static bool ClassHasHiddenMember(const ClassDecl* cls) {
  if (!cls) return false;
  for (const auto* m : cls->members) {
    if (m && (m->is_local || m->is_protected)) return true;
  }
  return false;
}

static uint32_t CastTargetSimpleWidth(std::string_view t) {
  if (t == "byte") return 8;
  if (t == "shortint") return 16;
  if (t == "int" || t == "integer") return 32;
  if (t == "longint") return 64;
  if (t == "bit" || t == "logic" || t == "reg") return 1;
  return 0;
}

namespace {

// §6.24.3: the bit-stream cast under validation, named for the two domain
// facts that identify it -- the cast operand expression and the destination
// type the operand is being cast to.
struct BitStreamCast {
  const Expr* expr;
  std::string_view target;
};

// §6.24.3: the elaboration context the bit-stream-cast checks consult to
// resolve the types named in a cast: the diagnostic sink plus the type maps
// (class names, class-handle variable types, unpacked-array variable info,
// typedefs) and the enclosing compilation unit.
struct BitStreamCastCtx {
  DiagEngine& diag;
  const std::unordered_set<std::string_view>& class_names;
  const std::unordered_map<std::string_view, std::string_view>& class_var_types;
  const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
      var_array_info;
  const TypedefMap& typedefs;
  CompilationUnit* unit;
};

// §6.24.3: a class handle whose class exposes local or protected members is an
// illegal bit-stream-cast source, except for the current instance `this` and
// when the destination is itself a class type. Returns true if the operand was
// flagged (the caller must then stop checking this cast).
bool CheckBitStreamCastClassSource(const BitStreamCast& cast,
                                   const BitStreamCastCtx& ctx) {
  const Expr* expr = cast.expr;
  if (expr->lhs && expr->lhs->kind == ExprKind::kIdentifier &&
      expr->lhs->text != "this" && ctx.class_names.count(cast.target) == 0) {
    auto it = ctx.class_var_types.find(expr->lhs->text);
    if (it != ctx.class_var_types.end()) {
      const auto* cls = FindClassDecl(it->second, ctx.unit);
      if (ClassHasHiddenMember(cls)) {
        ctx.diag.Error(expr->range.start,
                       std::format("class handle '{}' is illegal as a "
                                   "bit-stream cast source: its class has "
                                   "local or protected members",
                                   expr->lhs->text));
        return true;
      }
    }
  }
  return false;
}

// §6.24.3: when both source and destination are fixed-size types of different
// sizes and either is unpacked, the cast generates a compile-time error. This
// handles the case where the operand is a fixed-size unpacked-array variable.
void CheckBitStreamCastUnpackedOperand(const BitStreamCast& cast,
                                       const BitStreamCastCtx& ctx) {
  const Expr* expr = cast.expr;
  if (expr->lhs->kind != ExprKind::kIdentifier) return;
  auto src_name = expr->lhs->text;
  auto var_it = ctx.var_array_info.find(src_name);
  if (var_it == ctx.var_array_info.end()) return;
  const auto& info = var_it->second;
  if (info.is_dynamic || info.is_assoc) return;
  if (info.unpacked_size == 0 || info.elem_width == 0) return;
  uint32_t src_width = info.unpacked_size * info.elem_width;

  uint32_t dst_width = CastTargetSimpleWidth(cast.target);
  if (dst_width == 0) {
    auto td = ctx.typedefs.find(cast.target);
    if (td != ctx.typedefs.end())
      dst_width = EvalTypeWidth(td->second, ctx.typedefs);
  }
  if (dst_width == 0) return;
  if (src_width == dst_width) return;
  ctx.diag.Error(expr->range.start,
                 std::format("bit-stream cast between fixed-size types of "
                             "different sizes ({} bits to {} bits) with an "
                             "unpacked operand is illegal",
                             src_width, dst_width));
}

}  // namespace

void Elaborator::CheckBitStreamCastExpr(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kCast) return;
  auto target = expr->text;
  if (target.empty()) return;

  // §6.24.3: an associative array type shall be illegal as a destination type
  // for a bit-stream cast.
  if (assoc_typedef_names_.count(target) > 0) {
    diag_.Error(expr->range.start,
                std::format("associative array type '{}' is illegal as a "
                            "bit-stream cast destination",
                            target));
    return;
  }

  BitStreamCast cast{expr, target};
  BitStreamCastCtx ctx{diag_,           class_names_, class_var_types_,
                       var_array_info_, typedefs_,    unit_};

  // §6.24.3: a class handle whose class exposes local or protected members
  // shall be illegal as a source type, except when the handle is the current
  // instance `this`. The rule applies to a bit-stream cast, i.e., when the
  // destination is not itself a class type.
  if (CheckBitStreamCastClassSource(cast, ctx)) {
    return;
  }

  // §6.24.3: when both source and destination are fixed-size types of
  // different sizes and either is unpacked, the cast generates a compile-time
  // error. Two paths are checked: the operand is an unpacked-array variable,
  // or the destination is an unpacked-array typedef. Dynamic-size cases are
  // left to the simulator since their sizes are not known until runtime.
  if (!expr->lhs) return;

  auto dst_unpacked_it = fixed_unpacked_typedef_widths_.find(target);
  if (dst_unpacked_it != fixed_unpacked_typedef_widths_.end()) {
    uint32_t src_width = InferExprWidth(expr->lhs, typedefs_);
    if (src_width > 0 && src_width != dst_unpacked_it->second) {
      diag_.Error(expr->range.start,
                  std::format("bit-stream cast between fixed-size types of "
                              "different sizes ({} bits to {} bits) with an "
                              "unpacked destination is illegal",
                              src_width, dst_unpacked_it->second));
      return;
    }
  }

  CheckBitStreamCastUnpackedOperand(cast, ctx);
}

void Elaborator::WalkExprForBitStreamCast(const Expr* expr) {
  if (!expr) return;
  CheckBitStreamCastExpr(expr);
  WalkExprForBitStreamCast(expr->lhs);
  WalkExprForBitStreamCast(expr->rhs);
  WalkExprForBitStreamCast(expr->base);
  WalkExprForBitStreamCast(expr->index);
  WalkExprForBitStreamCast(expr->index_end);
  WalkExprForBitStreamCast(expr->condition);
  WalkExprForBitStreamCast(expr->true_expr);
  WalkExprForBitStreamCast(expr->false_expr);
  for (const auto* elem : expr->elements) WalkExprForBitStreamCast(elem);
  for (const auto* arg : expr->args) WalkExprForBitStreamCast(arg);
}

void Elaborator::WalkStmtsForBitStreamCast(const Stmt* s) {
  if (!s) return;
  WalkExprForBitStreamCast(s->lhs);
  WalkExprForBitStreamCast(s->rhs);
  WalkExprForBitStreamCast(s->expr);
  WalkExprForBitStreamCast(s->condition);
  for (auto* sub : s->stmts) WalkStmtsForBitStreamCast(sub);
  WalkStmtsForBitStreamCast(s->then_branch);
  WalkStmtsForBitStreamCast(s->else_branch);
  WalkStmtsForBitStreamCast(s->body);
  WalkStmtsForBitStreamCast(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForBitStreamCast(ci.body);
}

void Elaborator::ValidateBitStreamCast(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForBitStreamCast(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForBitStreamCast(item->assign_lhs);
      WalkExprForBitStreamCast(item->assign_rhs);
    }
    if (item->kind == ModuleItemKind::kVarDecl) {
      WalkExprForBitStreamCast(item->init_expr);
    }
  }
}

static std::string_view HierRefLeftmost(const Expr* e) {
  if (e->kind == ExprKind::kIdentifier) return e->text;
  if (e->kind == ExprKind::kMemberAccess && e->lhs)
    return HierRefLeftmost(e->lhs);
  return {};
}

static bool ExprRefersToChecker(
    const Expr* e, const std::unordered_set<std::string_view>& checker_names) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    auto leftmost = HierRefLeftmost(e);
    if (!leftmost.empty() && checker_names.count(leftmost)) return true;
  }
  if (ExprRefersToChecker(e->lhs, checker_names)) return true;
  if (ExprRefersToChecker(e->rhs, checker_names)) return true;
  if (ExprRefersToChecker(e->base, checker_names)) return true;
  for (auto* elem : e->elements) {
    if (ExprRefersToChecker(elem, checker_names)) return true;
  }
  return false;
}

static void WalkStmtsForCheckerRef(
    const Stmt* s, const std::unordered_set<std::string_view>& checker_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->lhs && ExprRefersToChecker(s->lhs, checker_names))
    diag.Error(s->range.start,
               "hierarchical reference into a checker is not permitted");
  if (s->rhs && ExprRefersToChecker(s->rhs, checker_names))
    diag.Error(s->range.start,
               "hierarchical reference into a checker is not permitted");
  for (auto* sub : s->stmts) WalkStmtsForCheckerRef(sub, checker_names, diag);
  WalkStmtsForCheckerRef(s->then_branch, checker_names, diag);
  WalkStmtsForCheckerRef(s->else_branch, checker_names, diag);
  WalkStmtsForCheckerRef(s->body, checker_names, diag);
  WalkStmtsForCheckerRef(s->for_body, checker_names, diag);
  for (auto* init : s->for_inits)
    WalkStmtsForCheckerRef(init, checker_names, diag);
  for (auto* step : s->for_steps)
    WalkStmtsForCheckerRef(step, checker_names, diag);
  for (auto* fs : s->fork_stmts)
    WalkStmtsForCheckerRef(fs, checker_names, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForCheckerRef(ci.body, checker_names, diag);
}

void Elaborator::ValidateHierRefIntoChecker(const ModuleDecl* decl) {
  if (checker_inst_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      if (ExprRefersToChecker(item->assign_lhs, checker_inst_names_))
        diag_.Error(item->loc,
                    "hierarchical reference into a checker is not permitted");
      if (ExprRefersToChecker(item->assign_rhs, checker_inst_names_))
        diag_.Error(item->loc,
                    "hierarchical reference into a checker is not permitted");
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body)
      WalkStmtsForCheckerRef(item->body, checker_inst_names_, diag_);
  }
}

// §17.7.1: flags any blocking procedural assignment whose target is one of the
// checker's free variables. A free variable may only be updated by a
// nonblocking assignment (from an always_ff procedure), so a blocking
// assignment to it — in any procedure — is illegal.
static void WalkStmtsForFreeBlockingAssign(
    const Stmt* s, const std::unordered_set<std::string_view>& free_vars,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign && s->lhs) {
    auto target = HierRefLeftmost(s->lhs);
    if (!target.empty() && free_vars.count(target))
      diag.Error(
          s->range.start,
          std::format("a blocking assignment cannot target free checker "
                      "variable '{}'; a free variable is updated only by "
                      "a nonblocking assignment",
                      target));
  }
  for (auto* sub : s->stmts)
    WalkStmtsForFreeBlockingAssign(sub, free_vars, diag);
  WalkStmtsForFreeBlockingAssign(s->then_branch, free_vars, diag);
  WalkStmtsForFreeBlockingAssign(s->else_branch, free_vars, diag);
  WalkStmtsForFreeBlockingAssign(s->body, free_vars, diag);
  WalkStmtsForFreeBlockingAssign(s->for_body, free_vars, diag);
  for (auto* step : s->for_steps)
    WalkStmtsForFreeBlockingAssign(step, free_vars, diag);
  for (auto* fs : s->fork_stmts)
    WalkStmtsForFreeBlockingAssign(fs, free_vars, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForFreeBlockingAssign(ci.body, free_vars, diag);
}

// §17.7.1: continuous assignments and blocking procedural assignments to a free
// checker variable are illegal; a free variable is left to the nonblocking form
// only. Collects the free (rand) checker variables declared in the checker body
// and rejects any continuous assign or blocking procedural assign that targets
// one. Runs only on checker declarations.
void Elaborator::ValidateFreeCheckerVariableAssignments(
    const ModuleDecl* decl) {
  if (decl->decl_kind != ModuleDeclKind::kChecker) return;
  std::unordered_set<std::string_view> free_vars;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->is_rand &&
        !item->name.empty())
      free_vars.insert(item->name);
  }
  if (free_vars.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      auto target = HierRefLeftmost(item->assign_lhs);
      if (!target.empty() && free_vars.count(target))
        diag_.Error(
            item->loc,
            std::format("a continuous assignment cannot target free checker "
                        "variable '{}'; a free variable is updated only by a "
                        "nonblocking assignment",
                        target));
    }
    bool is_proc = item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock;
    if (is_proc && item->body)
      WalkStmtsForFreeBlockingAssign(item->body, free_vars, diag_);
  }
}

// §17.7.1: flags a blocking or nonblocking assignment inside an initial
// procedure whose target names one of the checker's variables. A checker
// variable may only be initialized in its declaration, never assigned from an
// initial procedure. Variables declared locally inside the initial block are
// not checker variables and so are not in `checker_vars`.
static void WalkStmtsForCheckerVarAssignInInitial(
    const Stmt* s, const std::unordered_set<std::string_view>& checker_vars,
    DiagEngine& diag) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs) {
    auto target = HierRefLeftmost(s->lhs);
    if (!target.empty() && checker_vars.count(target))
      diag.Error(s->range.start,
                 std::format("checker variable '{}' cannot be assigned in an "
                             "initial procedure; initialize it in its "
                             "declaration instead",
                             target));
  }
  for (auto* sub : s->stmts)
    WalkStmtsForCheckerVarAssignInInitial(sub, checker_vars, diag);
  WalkStmtsForCheckerVarAssignInInitial(s->then_branch, checker_vars, diag);
  WalkStmtsForCheckerVarAssignInInitial(s->else_branch, checker_vars, diag);
  WalkStmtsForCheckerVarAssignInInitial(s->body, checker_vars, diag);
  WalkStmtsForCheckerVarAssignInInitial(s->for_body, checker_vars, diag);
  for (auto* init : s->for_inits)
    WalkStmtsForCheckerVarAssignInInitial(init, checker_vars, diag);
  for (auto* step : s->for_steps)
    WalkStmtsForCheckerVarAssignInInitial(step, checker_vars, diag);
  for (auto* fs : s->fork_stmts)
    WalkStmtsForCheckerVarAssignInInitial(fs, checker_vars, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForCheckerVarAssignInInitial(ci.body, checker_vars, diag);
}

// §17.7.1: a checker variable may not be assigned in an initial procedure (it
// may only be initialized in its declaration). Collects the variables declared
// in the checker body and rejects any assignment to one of them from an initial
// procedure. Runs only on checker declarations.
void Elaborator::ValidateCheckerVariableInitialAssignment(
    const ModuleDecl* decl) {
  if (decl->decl_kind != ModuleDeclKind::kChecker) return;
  std::unordered_set<std::string_view> checker_vars;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && !item->name.empty())
      checker_vars.insert(item->name);
  }
  if (checker_vars.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock && item->body)
      WalkStmtsForCheckerVarAssignInInitial(item->body, checker_vars, diag_);
  }
}

static bool ExprRefersToProgram(
    const Expr* e, const std::unordered_set<std::string_view>& program_names) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    auto leftmost = HierRefLeftmost(e);
    if (!leftmost.empty() && program_names.count(leftmost)) return true;
  }
  if (ExprRefersToProgram(e->lhs, program_names)) return true;
  if (ExprRefersToProgram(e->rhs, program_names)) return true;
  if (ExprRefersToProgram(e->base, program_names)) return true;
  for (auto* elem : e->elements) {
    if (ExprRefersToProgram(elem, program_names)) return true;
  }
  return false;
}

static void WalkStmtsForProgramRef(
    const Stmt* s, const std::unordered_set<std::string_view>& program_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->lhs && ExprRefersToProgram(s->lhs, program_names))
    diag.Error(s->range.start,
               "hierarchical reference to program signal from outside the "
               "program is not permitted");
  if (s->rhs && ExprRefersToProgram(s->rhs, program_names))
    diag.Error(s->range.start,
               "hierarchical reference to program signal from outside the "
               "program is not permitted");
  for (auto* sub : s->stmts) WalkStmtsForProgramRef(sub, program_names, diag);
  WalkStmtsForProgramRef(s->then_branch, program_names, diag);
  WalkStmtsForProgramRef(s->else_branch, program_names, diag);
  WalkStmtsForProgramRef(s->body, program_names, diag);
  WalkStmtsForProgramRef(s->for_body, program_names, diag);
  for (auto* init : s->for_inits)
    WalkStmtsForProgramRef(init, program_names, diag);
  for (auto* step : s->for_steps)
    WalkStmtsForProgramRef(step, program_names, diag);
  for (auto* fs : s->fork_stmts)
    WalkStmtsForProgramRef(fs, program_names, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForProgramRef(ci.body, program_names, diag);
}

void Elaborator::ValidateHierRefIntoProgram(const ModuleDecl* decl) {
  if (program_inst_names_.empty()) return;
  if (decl->decl_kind == ModuleDeclKind::kProgram) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      if (ExprRefersToProgram(item->assign_lhs, program_inst_names_))
        diag_.Error(item->loc,
                    "hierarchical reference to program signal from outside "
                    "the program is not permitted");
      if (ExprRefersToProgram(item->assign_rhs, program_inst_names_))
        diag_.Error(item->loc,
                    "hierarchical reference to program signal from outside "
                    "the program is not permitted");
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body)
      WalkStmtsForProgramRef(item->body, program_inst_names_, diag_);
  }
}

void Elaborator::ValidateAnonymousProgramHierRefs() {
  std::unordered_set<std::string_view> program_names;
  for (const auto* p : unit_->programs) {
    if (!p->name.empty()) program_names.insert(p->name);
  }
  if (program_names.empty()) return;
  for (const auto* item : unit_->cu_items) {
    if (!item->from_anonymous_program) continue;
    if (item->body) WalkStmtsForProgramRef(item->body, program_names, diag_);
    // §24.3: a hierarchical reference to a program from an anonymous program is
    // illegal wherever it appears, including inside a task or function the
    // anonymous program declares (whose body is in func_body_stmts, not body).
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      for (const auto* s : item->func_body_stmts)
        WalkStmtsForProgramRef(s, program_names, diag_);
    }
  }
}

static void CollectHierPathComponents(const Expr* e,
                                      std::vector<std::string_view>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e->text);
    return;
  }
  if (e->kind == ExprKind::kMemberAccess) {
    CollectHierPathComponents(e->lhs, out);
    CollectHierPathComponents(e->rhs, out);
  }
}

static bool ExprRefersToAutomatic(
    const Expr* e, const std::unordered_set<std::string_view>& auto_names) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    std::vector<std::string_view> components;
    CollectHierPathComponents(e, components);
    for (size_t i = 0; i + 1 < components.size(); ++i) {
      if (auto_names.count(components[i])) return true;
    }
  }
  if (ExprRefersToAutomatic(e->lhs, auto_names)) return true;
  if (ExprRefersToAutomatic(e->rhs, auto_names)) return true;
  if (ExprRefersToAutomatic(e->base, auto_names)) return true;
  for (auto* elem : e->elements) {
    if (ExprRefersToAutomatic(elem, auto_names)) return true;
  }
  return false;
}

static void WalkStmtsForAutoRef(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->lhs && ExprRefersToAutomatic(s->lhs, auto_names))
    diag.Error(s->range.start,
               "hierarchical reference to object in automatic task or "
               "function is not permitted");
  if (s->rhs && ExprRefersToAutomatic(s->rhs, auto_names))
    diag.Error(s->range.start,
               "hierarchical reference to object in automatic task or "
               "function is not permitted");
  for (auto* sub : s->stmts) WalkStmtsForAutoRef(sub, auto_names, diag);
  WalkStmtsForAutoRef(s->then_branch, auto_names, diag);
  WalkStmtsForAutoRef(s->else_branch, auto_names, diag);
  WalkStmtsForAutoRef(s->body, auto_names, diag);
  WalkStmtsForAutoRef(s->for_body, auto_names, diag);
  for (auto* init : s->for_inits) WalkStmtsForAutoRef(init, auto_names, diag);
  for (auto* step : s->for_steps) WalkStmtsForAutoRef(step, auto_names, diag);
  for (auto* fs : s->fork_stmts) WalkStmtsForAutoRef(fs, auto_names, diag);
  for (auto& ci : s->case_items) WalkStmtsForAutoRef(ci.body, auto_names, diag);
}

void Elaborator::ValidateHierRefToAutomatic(const ModuleDecl* decl) {
  if (auto_task_func_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      if (ExprRefersToAutomatic(item->assign_lhs, auto_task_func_names_))
        diag_.Error(item->loc,
                    "hierarchical reference to object in automatic task or "
                    "function is not permitted");
      if (ExprRefersToAutomatic(item->assign_rhs, auto_task_func_names_))
        diag_.Error(item->loc,
                    "hierarchical reference to object in automatic task or "
                    "function is not permitted");
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body)
      WalkStmtsForAutoRef(item->body, auto_task_func_names_, diag_);
  }
}

static bool IsProgramSubroutineCallExpr(
    const Expr* e, const std::unordered_set<std::string_view>& program_names) {
  if (!e || e->kind != ExprKind::kCall) return false;
  const Expr* callee = e->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  auto leftmost = HierRefLeftmost(callee);
  return !leftmost.empty() && program_names.count(leftmost) > 0;
}

static void WalkExprForProgramCall(
    const Expr* e, const std::unordered_set<std::string_view>& program_names,
    DiagEngine& diag, SourceLoc loc) {
  if (!e) return;
  if (IsProgramSubroutineCallExpr(e, program_names)) {
    diag.Error(loc,
               "calling a program subroutine from within a design module is "
               "not permitted");
  }
  WalkExprForProgramCall(e->lhs, program_names, diag, loc);
  WalkExprForProgramCall(e->rhs, program_names, diag, loc);
  WalkExprForProgramCall(e->condition, program_names, diag, loc);
  WalkExprForProgramCall(e->true_expr, program_names, diag, loc);
  WalkExprForProgramCall(e->false_expr, program_names, diag, loc);
  WalkExprForProgramCall(e->base, program_names, diag, loc);
  WalkExprForProgramCall(e->index, program_names, diag, loc);
  WalkExprForProgramCall(e->index_end, program_names, diag, loc);
  WalkExprForProgramCall(e->with_expr, program_names, diag, loc);
  WalkExprForProgramCall(e->repeat_count, program_names, diag, loc);
  for (auto* arg : e->args)
    WalkExprForProgramCall(arg, program_names, diag, loc);
  for (auto* elem : e->elements)
    WalkExprForProgramCall(elem, program_names, diag, loc);
}

static void WalkStmtForProgramCall(
    const Stmt* s, const std::unordered_set<std::string_view>& program_names,
    DiagEngine& diag) {
  if (!s) return;
  auto loc = s->range.start;
  WalkExprForProgramCall(s->lhs, program_names, diag, loc);
  WalkExprForProgramCall(s->rhs, program_names, diag, loc);
  WalkExprForProgramCall(s->expr, program_names, diag, loc);
  WalkExprForProgramCall(s->condition, program_names, diag, loc);
  for (auto* sub : s->stmts) WalkStmtForProgramCall(sub, program_names, diag);
  WalkStmtForProgramCall(s->then_branch, program_names, diag);
  WalkStmtForProgramCall(s->else_branch, program_names, diag);
  WalkStmtForProgramCall(s->body, program_names, diag);
  WalkStmtForProgramCall(s->for_body, program_names, diag);
  for (auto* init : s->for_inits)
    WalkStmtForProgramCall(init, program_names, diag);
  for (auto* step : s->for_steps)
    WalkStmtForProgramCall(step, program_names, diag);
  for (auto* fs : s->fork_stmts)
    WalkStmtForProgramCall(fs, program_names, diag);
  for (auto& ci : s->case_items)
    WalkStmtForProgramCall(ci.body, program_names, diag);
}

void Elaborator::ValidateProgramSubroutineCall(const ModuleDecl* decl) {
  if (program_inst_names_.empty()) return;
  if (decl->decl_kind == ModuleDeclKind::kProgram) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForProgramCall(item->assign_lhs, program_inst_names_, diag_,
                             item->loc);
      WalkExprForProgramCall(item->assign_rhs, program_inst_names_, diag_,
                             item->loc);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body)
      WalkStmtForProgramCall(item->body, program_inst_names_, diag_);
  }
}

}  // namespace delta
