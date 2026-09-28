#include <charconv>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <system_error>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

bool ElaboratorOperationRules::ConcatContainsStringElement(const Expr* expr) {
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

void ElaboratorOperationRules::CheckStringConcatLvalue(const Expr* lhs) {
  if (!lhs) return;
  if (lhs->kind != ExprKind::kConcatenation) return;
  if (ConcatContainsStringElement(lhs)) {
    diag_.Error(lhs->range.start,
                "string concatenation is not allowed on the left-hand side "
                "of an assignment",
                Subclause("11.4.12.2"));
  }
}

void ElaboratorOperationRules::WalkStmtsForStringConcatLvalue(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign || s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    CheckStringConcatLvalue(s->lhs);
  }
  // §11.4.12.2 bars a concatenation of strings from the left-hand side of an
  // assignment and names no statement the assignment is allowed to stand in,
  // so every position a statement holds a statement in is one this report
  // reaches. ForEachChildStmt in elaborator_validate_internal.h states those
  // positions once for the whole elaborator, which is why the list is not
  // written out again here.
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtsForStringConcatLvalue(sub); });
}

void ElaboratorOperationRules::ValidateStringConcatLvalue(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
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
                             elem->text),
                 Subclause("11.4.14.1"));
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
                               elem->text),
                   Subclause("11.4.14.1"));
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
               "streaming slice_size shall be a positive constant",
               Subclause("11.4.14.2"));
  }
}

}  // namespace

void ElaboratorOperationRules::WalkExprForStreamingContext(
    const Expr* expr, bool is_valid_context) {
  if (!expr) return;
  if (expr->kind == ExprKind::kStreamingConcat) {
    if (!is_valid_context) {
      diag_.Error(expr->range.start,
                  "streaming concatenation shall not be used as an operand "
                  "of an expression other than an assignment or bit-stream "
                  "cast",
                  Subclause("11.4.14"));
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
void ElaboratorOperationRules::CheckStreamingSourceTargetType(const Expr* lhs,
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
                "be a bit-stream type",
                Subclause("11.4.14"));
  }
}

// §11.4.14.3: when a streaming_concatenation is the target of an assignment (an
// unpack), the source expression shall be of bit-stream type or the result of
// another streaming_concatenation. This is the mirror of the pack-direction
// rule above: reject the obviously-non-bit-stream sources we can recognise from
// the variable-type map (real family, event, chandle, virtual interface). A
// source that is itself a streaming_concatenation is allowed, and any source we
// cannot type-check from a simple identifier is left to downstream checks.
void ElaboratorOperationRules::CheckStreamingUnpackSourceType(const Expr* lhs,
                                                              const Expr* rhs) {
  if (!lhs || !rhs) return;
  if (lhs->kind != ExprKind::kStreamingConcat) return;
  if (rhs->kind == ExprKind::kStreamingConcat) return;
  if (rhs->kind != ExprKind::kIdentifier) return;
  auto it = var_types_.find(rhs->text);
  if (it == var_types_.end()) return;
  auto k = it->second;
  bool not_bitstream = IsRealType(k) || k == DataTypeKind::kEvent ||
                       k == DataTypeKind::kChandle ||
                       k == DataTypeKind::kVirtualInterface;
  if (not_bitstream) {
    diag_.Error(rhs->range.start,
                "source of a streaming concatenation unpack must be a "
                "bit-stream type or another streaming concatenation",
                Subclause("11.4.14.3"));
  }
}

void ElaboratorOperationRules::WalkStmtsForStreamingContext(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign || s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    WalkExprForStreamingContext(s->lhs, true);
    WalkExprForStreamingContext(s->rhs, true);
    CheckStreamingSourceTargetType(s->lhs, s->rhs);
    CheckStreamingUnpackSourceType(s->lhs, s->rhs);
  } else {
    WalkExprForStreamingContext(s->lhs, false);
    WalkExprForStreamingContext(s->rhs, false);
  }
  WalkExprForStreamingContext(s->expr, false);
  WalkExprForStreamingContext(s->condition, false);
  WalkExprForStreamingContext(s->assert_expr, false);
  // §11.4.14 confines a streaming concatenation to an assignment or a
  // bit-stream cast, §11.4.14.1 rules on its operands and §11.4.14.2 on its
  // slice_size, and none of the three names a statement the concatenation is
  // allowed to stand in, so every position a statement holds a statement in is
  // one these reports reach. ForEachChildStmt in
  // elaborator_validate_internal.h states those positions once for the whole
  // elaborator, which is why the list is not written out again here.
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtsForStreamingContext(sub); });
}

void ElaboratorOperationRules::ValidateStreamingConcatContext(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForStreamingContext(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForStreamingContext(item->assign_lhs, true);
      WalkExprForStreamingContext(item->assign_rhs, true);
      CheckStreamingSourceTargetType(item->assign_lhs, item->assign_rhs);
      CheckStreamingUnpackSourceType(item->assign_lhs, item->assign_rhs);
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
// typedefs, the widths of the unpacked-array typedefs, the module variables'
// declared types) and the enclosing compilation unit.
struct BitStreamCastCtx {
  DiagEngine& diag;
  const std::unordered_set<std::string_view>& class_names;
  const std::unordered_map<std::string_view, std::string_view>& class_var_types;
  const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
      var_array_info;
  const TypedefMap& typedefs;
  const std::unordered_map<std::string_view, uint32_t>& unpacked_typedef_widths;
  const std::unordered_map<std::string_view, const DataType*>& var_decl_types;
  CompilationUnit* unit;
};

// The number of elements a declaration's unpacked dimensions give it, each
// written `[size]` or `[left:right]`; zero where one does not fold to a fixed
// size, a dynamic, queue or associative dimension among them.
uint32_t FixedUnpackedElementCount(const std::vector<Expr*>& dims) {
  uint32_t count = 1;
  for (const Expr* dim : dims) {
    if (dim == nullptr) return 0;
    if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
      auto left = ConstEvalInt(dim->lhs);
      auto right = ConstEvalInt(dim->rhs);
      if (!left || !right) return 0;
      count *= static_cast<uint32_t>(std::abs(*left - *right) + 1);
    } else if (auto size = ConstEvalInt(dim); size && *size > 0) {
      count *= static_cast<uint32_t>(*size);
    } else {
      return 0;
    }
  }
  return count;
}

// §6.24.3 (printed page 142): the size of a fixed-size bit-stream type is the
// number of bits it holds, an unpacked structure's being every bit of every
// member, so its `byte command [2]` holds sixteen. EvalTypeWidth gives such a
// member the width of one element, so an unpacked structure is summed here,
// each member's element size times its element count, and any other type is
// EvalTypeWidth's. Zero where a member's size is not fixed. The depth bounds a
// cyclic typedef.
uint32_t BitStreamTypeWidth(const DataType& type, const TypedefMap& typedefs,
                            int depth = 0);

// One member's share of an unpacked structure's bit-stream size: its element
// size times its unpacked element count, zero where either is not fixed.
uint32_t MemberBitStreamWidth(const StructMember& m, const TypedefMap& typedefs,
                              int depth) {
  const DataType* member_type =
      m.nested_type != nullptr ? m.nested_type : MemberNamedType(m, typedefs);
  uint32_t element = member_type == nullptr
                         ? EvalStructMemberWidth(m, typedefs)
                         : BitStreamTypeWidth(*member_type, typedefs, depth);
  return element * FixedUnpackedElementCount(m.unpacked_dims);
}

uint32_t BitStreamTypeWidth(const DataType& type, const TypedefMap& typedefs,
                            int depth) {
  if (depth > 8) return 0;
  if (type.kind == DataTypeKind::kNamed) {
    auto td = typedefs.find(type.type_name);
    if (td == typedefs.end()) return 0;
    return BitStreamTypeWidth(td->second, typedefs, depth + 1);
  }
  if (type.kind != DataTypeKind::kStruct || type.is_packed)
    return EvalTypeWidth(type, typedefs);
  uint32_t total = 0;
  for (const StructMember& m : type.struct_members) {
    uint32_t member = MemberBitStreamWidth(m, typedefs, depth + 1);
    if (member == 0) return 0;
    total += member;
  }
  return total;
}

// The size of the cast's destination type, a keyword type, an unpacked-array
// typedef, or another typedef; zero where none is known.
uint32_t BitStreamDestinationWidth(std::string_view target,
                                   const BitStreamCastCtx& ctx) {
  if (uint32_t simple = CastTargetSimpleWidth(target)) return simple;
  auto unpacked = ctx.unpacked_typedef_widths.find(target);
  if (unpacked != ctx.unpacked_typedef_widths.end()) return unpacked->second;
  auto td = ctx.typedefs.find(target);
  if (td == ctx.typedefs.end()) return 0;
  return BitStreamTypeWidth(td->second, ctx.typedefs);
}

// The size of the unpacked operand named `name`, a fixed-size unpacked array or
// a variable of an unpacked structure; zero for any other operand.
uint32_t UnpackedOperandWidth(std::string_view name,
                              const BitStreamCastCtx& ctx) {
  auto var_it = ctx.var_array_info.find(name);
  if (var_it != ctx.var_array_info.end()) {
    const auto& info = var_it->second;
    if (info.is_dynamic || info.is_assoc) return 0;
    return info.unpacked_size * info.elem_width;
  }
  auto decl = ctx.var_decl_types.find(name);
  if (decl == ctx.var_decl_types.end()) return 0;
  const DataType* type = decl->second;
  for (int hops = 0; hops < 8 && type->kind == DataTypeKind::kNamed; ++hops) {
    auto td = ctx.typedefs.find(type->type_name);
    if (td == ctx.typedefs.end()) return 0;
    type = &td->second;
  }
  if (type->kind != DataTypeKind::kStruct || type->is_packed) return 0;
  return BitStreamTypeWidth(*type, ctx.typedefs);
}

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
                                   expr->lhs->text),
                       Subclause("6.24.3"));
        return true;
      }
    }
  }
  return false;
}

// §6.24.3: when both source and destination are fixed-size types of different
// sizes and either is unpacked, the cast generates a compile-time error. This
// handles the case where the operand is a fixed-size unpacked-array variable
// or a variable of an unpacked structure.
void CheckBitStreamCastUnpackedOperand(const BitStreamCast& cast,
                                       const BitStreamCastCtx& ctx) {
  const Expr* expr = cast.expr;
  if (expr->lhs->kind != ExprKind::kIdentifier) return;
  uint32_t src_width = UnpackedOperandWidth(expr->lhs->text, ctx);
  if (src_width == 0) return;
  uint32_t dst_width = BitStreamDestinationWidth(cast.target, ctx);
  if (dst_width == 0) return;
  if (src_width == dst_width) return;
  ctx.diag.Error(expr->range.start,
                 std::format("bit-stream cast between fixed-size types of "
                             "different sizes ({} bits to {} bits) with an "
                             "unpacked operand is illegal",
                             src_width, dst_width),
                 Subclause("6.24.3"));
}

}  // namespace

void ElaboratorOperationRules::CheckBitStreamCastExpr(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kCast) return;
  auto target = expr->text;
  if (target.empty()) return;

  // §6.24.3: an associative array type shall be illegal as a destination type
  // for a bit-stream cast.
  if (assoc_typedef_names_.count(target) > 0) {
    diag_.Error(expr->range.start,
                std::format("associative array type '{}' is illegal as a "
                            "bit-stream cast destination",
                            target),
                Subclause("6.24.3"));
    return;
  }

  BitStreamCast cast{expr, target};
  BitStreamCastCtx ctx{diag_,
                       class_names_,
                       class_var_types_,
                       var_array_info_,
                       typedefs_,
                       fixed_unpacked_typedef_widths_,
                       bit_stream_var_types_,
                       unit_};

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
    // An unpacked structure operand is as wide as all its members' elements,
    // which InferExprWidth, answering one element of an unpacked member, is
    // not.
    uint32_t src_width = expr->lhs->kind == ExprKind::kIdentifier
                             ? UnpackedOperandWidth(expr->lhs->text, ctx)
                             : 0;
    if (src_width == 0) src_width = InferExprWidth(expr->lhs, typedefs_);
    if (src_width > 0 && src_width != dst_unpacked_it->second) {
      diag_.Error(expr->range.start,
                  std::format("bit-stream cast between fixed-size types of "
                              "different sizes ({} bits to {} bits) with an "
                              "unpacked destination is illegal",
                              src_width, dst_unpacked_it->second),
                  Subclause("6.24.3"));
      return;
    }
  }

  CheckBitStreamCastUnpackedOperand(cast, ctx);
}

void ElaboratorOperationRules::WalkExprForBitStreamCast(const Expr* expr) {
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

void ElaboratorOperationRules::WalkStmtsForBitStreamCast(const Stmt* s) {
  if (!s) return;
  WalkExprForBitStreamCast(s->lhs);
  WalkExprForBitStreamCast(s->rhs);
  WalkExprForBitStreamCast(s->expr);
  WalkExprForBitStreamCast(s->condition);
  // §6.24.3 rules on the source and destination types of a bit-stream cast
  // and names no statement the cast is allowed to stand in, so every position
  // a statement holds a statement in is one these reports reach.
  // ForEachChildStmt in elaborator_validate_internal.h states those positions
  // once for the whole elaborator, which is why the list is not written out
  // again here.
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { WalkStmtsForBitStreamCast(sub); });
}

void ElaboratorOperationRules::ValidateBitStreamCast(const ModuleDecl* decl) {
  bit_stream_var_types_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->unpacked_dims.empty())
      bit_stream_var_types_[item->name] = &item->data_type;
  }
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
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

}  // namespace delta
