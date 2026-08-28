#include <unordered_map>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

static bool IsEqualityOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

void ElaboratorOperationRules::CheckAssocOperandInBinaryExpr(const Expr* e) {
  if (!e) return;
  if (e->kind == ExprKind::kBinary && !IsEqualityOp(e->op)) {
    for (const Expr* side : {e->lhs, e->rhs}) {
      if (!side || side->kind != ExprKind::kIdentifier) continue;
      auto it = var_array_info_.find(side->text);
      if (it == var_array_info_.end() || !it->second.is_assoc) continue;
      diag_.Error(side->range.start,
                  "associative array operand requires an element "
                  "selection before use in this expression",
                  Subclause("7.4.6"));
    }
  }
  CheckAssocOperandInBinaryExpr(e->lhs);
  CheckAssocOperandInBinaryExpr(e->rhs);
  CheckAssocOperandInBinaryExpr(e->condition);
  CheckAssocOperandInBinaryExpr(e->true_expr);
  CheckAssocOperandInBinaryExpr(e->false_expr);
  CheckAssocOperandInBinaryExpr(e->base);
  CheckAssocOperandInBinaryExpr(e->index);
  CheckAssocOperandInBinaryExpr(e->index_end);
  for (const auto* a : e->args) CheckAssocOperandInBinaryExpr(a);
  for (const auto* el : e->elements) CheckAssocOperandInBinaryExpr(el);
}

void ElaboratorOperationRules::WalkStmtsForAssocOperand(const Stmt* s) {
  if (!s) return;
  CheckAssocOperandInBinaryExpr(s->rhs);
  CheckAssocOperandInBinaryExpr(s->expr);
  CheckAssocOperandInBinaryExpr(s->condition);
  CheckAssocOperandInBinaryExpr(s->for_cond);
  // §7.4.6 requires an associative array to be selected down to an element
  // before an operator other than equality takes it, and names no statement the
  // requirement is suspended in, so this descends every link ForEachChildStmt
  // in elaborator_validate_internal.h names and names none itself. It wrote out
  // six of the thirteen, so `x = aa + 1` written in a fork arm or in a
  // randcase item was never looked at rather than looked at and allowed.
  ForEachChildStmt(s,
                   [this](Stmt* const& sub) { WalkStmtsForAssocOperand(sub); });
}

void ElaboratorOperationRules::ValidateAssocOperandInExpr(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      WalkStmtsForAssocOperand(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckAssocOperandInBinaryExpr(item->assign_rhs);
    }
  }
}

namespace {
// Flags a single assignment-pattern item that names an array-typed identifier,
// which is illegal as an element of a pattern targeting an unpacked array.
void CheckArrayPatternIdentElem(
    const Expr* elem,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    DiagEngine& diag) {
  if (elem->kind == ExprKind::kIdentifier && var_array_info.count(elem->text)) {
    diag.Error(elem->range.start,
               "array-typed identifier in assignment pattern targeting "
               "unpacked array",
               Subclause("10.9.1"));
  }
}

// Scans every item of an assignment pattern targeting a one-dimensional
// unpacked array, descending through a replication so its replicated element
// is inspected too, and flags any array-typed item (§10.10.1: every element
// item shall match the target's element type).
void ScanArrayPatternElems(
    const Expr* pattern,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    DiagEngine& diag) {
  for (auto* elem : pattern->elements) {
    if (elem->kind == ExprKind::kReplicate) {
      for (auto* inner : elem->elements) {
        CheckArrayPatternIdentElem(inner, var_array_info, diag);
      }
    } else {
      CheckArrayPatternIdentElem(elem, var_array_info, diag);
    }
  }
}
}  // namespace

void ElaboratorOperationRules::CheckArrayPatternElemTypeInAssign(
    const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kAssignmentPattern) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  if (it->second.num_unpacked_dims != 1) return;

  ScanArrayPatternElems(s->rhs, var_array_info_, diag_);
}

// §10.10.1: the element-type rule also governs a pattern that initializes the
// array in its declaration (`int A9[1:9] = '{A3, ...};`), an assignment-like
// context the procedural walk above never reaches.
void ElaboratorOperationRules::CheckArrayPatternElemTypeInInit(
    const ModuleItem* item) {
  if (!item->init_expr) return;
  if (item->init_expr->kind != ExprKind::kAssignmentPattern) return;
  auto it = var_array_info_.find(item->name);
  if (it == var_array_info_.end()) return;
  if (it->second.num_unpacked_dims != 1) return;

  ScanArrayPatternElems(item->init_expr, var_array_info_, diag_);
}

void ElaboratorOperationRules::WalkStmtsForArrayPatternElemType(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckArrayPatternElemTypeInAssign(s);
  }
  // §10.9.1 requires every element of an assignment pattern targeting an
  // unpacked array to match that array's element type, and conditions the rule
  // on the assignment rather than on where it stands, so this descends every
  // link ForEachChildStmt in elaborator_validate_internal.h names and names
  // none itself. It wrote out six of the thirteen, so `A9 = '{A3, ...}` written
  // in an assertion action block or in a randsequence production code block
  // reached CheckArrayPatternElemTypeInAssign in neither.
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForArrayPatternElemType(sub); });
}

void ElaboratorOperationRules::ValidateArrayPatternElemType(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      WalkStmtsForArrayPatternElemType(item->body);
    }
    CheckArrayPatternElemTypeInInit(item);
  }
}

void ElaboratorOperationRules::CheckReplicateTargetingArrayInAssign(
    const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kReplicate) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  diag_.Error(s->rhs->range.start,
              "replication cannot target an unpacked array",
              Subclause("10.10.1"));
}

// §10.10.1: unpacked array concatenations forbid replication. The ban holds
// when the replication initializes the array in its declaration
// (`int A9[1:9] = {9{1}};`), not only in a procedural assignment.
void ElaboratorOperationRules::CheckReplicateTargetingArrayInit(
    const ModuleItem* item) {
  if (!item->init_expr) return;
  if (item->init_expr->kind != ExprKind::kReplicate) return;
  if (var_array_info_.find(item->name) == var_array_info_.end()) return;
  diag_.Error(item->init_expr->range.start,
              "replication cannot target an unpacked array",
              Subclause("10.10.1"));
}

void ElaboratorOperationRules::WalkStmtsForReplicateTargetingArray(
    const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckReplicateTargetingArrayInAssign(s);
  }
  // §10.10.1 forbids a replication from targeting an unpacked array, and puts
  // no condition on the statement the assignment is written in, so this
  // descends every link ForEachChildStmt in elaborator_validate_internal.h
  // names and names none itself. It wrote out six of the thirteen, so
  // `A9 = {9{1}}` written in a fork arm or in a randcase item elaborated clean.
  ForEachChildStmt(s, [this](Stmt* const& sub) {
    WalkStmtsForReplicateTargetingArray(sub);
  });
}

void ElaboratorOperationRules::ValidateReplicateTargetingArray(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      WalkStmtsForReplicateTargetingArray(item->body);
    }
    CheckReplicateTargetingArrayInit(item);
  }
}

namespace {

// The addresses already supplied to an array reference: how many index selects
// sit between a trailing range and the array's name, and that name. §11.5.2
// writes an array access as the name followed by "an integer expression for
// each addressed dimension", so this count says how many dimensions the range
// has left to reach.
struct AddressedDims {
  uint32_t count = 0;
  std::string_view array_name;
};

AddressedDims CountAddressedDims(const Expr* base) {
  AddressedDims addressed;
  for (const Expr* cur = base; cur != nullptr; cur = cur->base) {
    if (cur->kind == ExprKind::kIdentifier) {
      addressed.array_name = cur->text;
      break;
    }
    // Anything else leaves the name unset: the base is not a plain array
    // reference and no dimension count can be read off it.
    if (cur->kind != ExprKind::kSelect) break;
    if (cur->index) ++addressed.count;
  }
  return addressed;
}

}  // namespace

// §7.4.5 / §11.5.2 — a trailing range written after an array reference is one
// of two different operations, and the number of dimensions already carrying an
// address is what tells them apart.
//
// Address every dimension and a single element has been selected, so the range
// selects contiguous bits of that element: a part-select, which §11.5.2 permits
// once the addressing is complete — "To express bit-selects or part-selects of
// array elements, the desired word shall first be selected by supplying an
// address for each dimension" — and which §11.5.1 governs from there.
//
// Leave a dimension unaddressed and the range selects contiguous *elements* of
// that dimension instead. §7.4.5 calls that a slice, and permits one: "Slices
// of an array can only apply to one dimension, but other dimensions can have
// single index values in an expression." So an unaddressed dimension does not
// make the range illegal.
//
// What a slice may not do is run against the dimension it slices. §11.5.1
// requires the first index of a range to "address a more significant bit than
// the second expression", and §11.5.2 sends an array's ranges to that same
// rule. On a dimension declared [0:7] the more significant element is the one
// with the smaller index, so [0:3] slices the first four elements and [3:0]
// addresses them backwards. That is what makes §11.5.2's own
// threed_array[14][1][3:0] illegal on wire threed_array[0:255][0:255][0:7]: the
// third dimension counts upward, and threed_array[14][1][0:7] slices that same
// dimension legally.
//
// The indexed forms need no test here. §11.5.1 fixes them to the declared
// direction whichever way it runs — on logic [0:31] b_vect, b_vect[0 +: 8] is
// b_vect[0:7] and b_vect[15 -: 8] is b_vect[8:15] — so an indexed range cannot
// be written backwards.
void ElaboratorOperationRules::CheckArrayElementPartSelectNode(const Expr* e) {
  AddressedDims addressed = CountAddressedDims(e->base);
  if (addressed.array_name.empty()) return;
  // §11.5.2 states this rule of net and variable arrays alike, so a net array's
  // dimensions are consulted as well. They are held in their own map because
  // every other reader of var_array_info_ is a rule written about variables.
  const VarArrayInfo* found = nullptr;
  if (auto it = var_array_info_.find(addressed.array_name);
      it != var_array_info_.end()) {
    found = &it->second;
  } else if (auto nit = net_array_info_.find(addressed.array_name);
             nit != net_array_info_.end()) {
    found = &nit->second;
  }
  if (found == nullptr) return;
  const auto& info = *found;
  if (info.is_dynamic || info.is_assoc) return;
  // Every dimension addressed: a part-select of the one element that addressing
  // selected, which this rule does not reach.
  if (addressed.count >= info.num_unpacked_dims) return;
  if (e->is_part_select_plus || e->is_part_select_minus) return;
  // A dimension whose bounds did not fold to constants contributed no entry, so
  // a short vector no longer lines up with the declaration and the dimension
  // being sliced cannot be identified.
  if (info.declared_dims.size() != info.num_unpacked_dims) return;
  auto first = ConstEvalInt(e->index);
  auto second = ConstEvalInt(e->index_end);
  if (!first || !second) return;
  const auto& sliced = info.declared_dims[addressed.count];
  bool reversed =
      sliced.IsDescending() ? (*first < *second) : (*first > *second);
  if (reversed) {
    diag_.Error(e->range.start,
                "slice's first index must address a more significant element "
                "than its second index",
                Subclause("11.5.2"));
  }
}

void ElaboratorOperationRules::WalkExprForArrayElementPartSelect(
    const Expr* e) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect &&
      (e->index_end || e->is_part_select_plus || e->is_part_select_minus)) {
    CheckArrayElementPartSelectNode(e);
  }
  WalkExprForArrayElementPartSelect(e->lhs);
  WalkExprForArrayElementPartSelect(e->rhs);
  WalkExprForArrayElementPartSelect(e->base);
  WalkExprForArrayElementPartSelect(e->index);
  WalkExprForArrayElementPartSelect(e->index_end);
  WalkExprForArrayElementPartSelect(e->condition);
  WalkExprForArrayElementPartSelect(e->true_expr);
  WalkExprForArrayElementPartSelect(e->false_expr);
  for (auto* elem : e->elements) WalkExprForArrayElementPartSelect(elem);
  for (auto* arg : e->args) WalkExprForArrayElementPartSelect(arg);
}

void ElaboratorOperationRules::WalkStmtsForArrayElementPartSelect(
    const Stmt* s) {
  if (!s) return;
  WalkExprForArrayElementPartSelect(s->rhs);
  WalkExprForArrayElementPartSelect(s->lhs);
  WalkExprForArrayElementPartSelect(s->expr);
  WalkExprForArrayElementPartSelect(s->condition);
  WalkExprForArrayElementPartSelect(s->assert_expr);
  // §11.5.2 sends an array's trailing range to §11.5.1's ordering rule, which
  // governs the range itself and not the statement holding it, so this descends
  // every link ForEachChildStmt in elaborator_validate_internal.h names and
  // names none itself. It wrote out six of the thirteen, so `r = A[1][1:0]`
  // written in a fork arm or in an assertion action block was never looked at.
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForArrayElementPartSelect(sub); });
}

void ElaboratorOperationRules::ValidateArrayElementPartSelect(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForArrayElementPartSelect(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForArrayElementPartSelect(item->assign_rhs);
      WalkExprForArrayElementPartSelect(item->assign_lhs);
    }
  }
}

void ElaboratorOperationRules::CheckArrayConcatNestingInAssign(const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kConcatenation) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  if (it->second.elem_type == DataTypeKind::kString) return;
  const auto& info = it->second;
  for (auto* elem : s->rhs->elements) {
    if (elem->kind == ExprKind::kConcatenation) {
      if (info.num_unpacked_dims == 1 && info.elem_width > 0 &&
          InferExprWidth(elem, typedefs_) == info.elem_width) {
        continue;
      }
      diag_.Error(elem->range.start,
                  "nested concatenation in unpacked array "
                  "concatenation is not self-determined",
                  Subclause("10.10.3"));
    }
  }
}

// Element types for which the literal `null` is a legal item in an unpacked
// array concatenation. Kinds outside this set make a null item illegal.
// `kNamed` is conservatively treated as legal because the named type could
// be a class or interface class; the elem-type record does not carry the
// resolved name, so we err on the permissive side rather than reject a
// legitimate class array.
static bool NullItemIsLegalForElemType(DataTypeKind k) {
  return k == DataTypeKind::kEvent || k == DataTypeKind::kChandle ||
         k == DataTypeKind::kVirtualInterface || k == DataTypeKind::kNamed;
}

void ElaboratorOperationRules::CheckNullItemInArrayConcatAssign(const Stmt* s) {
  if (!s->lhs || !s->rhs) return;
  if (s->lhs->kind != ExprKind::kIdentifier) return;
  if (s->rhs->kind != ExprKind::kConcatenation) return;
  auto it = var_array_info_.find(s->lhs->text);
  if (it == var_array_info_.end()) return;
  if (NullItemIsLegalForElemType(it->second.elem_type)) return;
  for (auto* elem : s->rhs->elements) {
    if (elem->kind == ExprKind::kIdentifier && elem->text == "null") {
      diag_.Error(elem->range.start,
                  "null is not a legal item in an unpacked array "
                  "concatenation for this target element type",
                  Subclause("10.10"));
    }
  }
}

// §10.10.3: a complete unpacked array concatenation has no self-determined
// type, so it shall not itself appear as an item of another unpacked array
// concatenation. The prohibition governs the concatenation that initializes an
// array in its declaration (`int B[9] = {A, {4, 5, 6, 7, 8, 9}};`), an
// assignment-like context that the procedural walk never reaches. A nested
// `{...}` whose self-determined width matches the target element is a
// vector/string concatenation and stays legal, mirroring the procedural check.
void ElaboratorOperationRules::CheckArrayConcatNestingInInit(
    const ModuleItem* item) {
  if (!item->init_expr) return;
  if (item->init_expr->kind != ExprKind::kConcatenation) return;
  auto it = var_array_info_.find(item->name);
  if (it == var_array_info_.end()) return;
  if (it->second.elem_type == DataTypeKind::kString) return;
  const auto& info = it->second;
  for (auto* elem : item->init_expr->elements) {
    if (elem->kind == ExprKind::kConcatenation) {
      if (info.num_unpacked_dims == 1 && info.elem_width > 0 &&
          InferExprWidth(elem, typedefs_) == info.elem_width) {
        continue;
      }
      diag_.Error(elem->range.start,
                  "nested concatenation in unpacked array "
                  "concatenation is not self-determined",
                  Subclause("10.10.3"));
    }
  }
}

void ElaboratorOperationRules::WalkStmtsForArrayConcatNesting(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckArrayConcatNestingInAssign(s);
    CheckNullItemInArrayConcatAssign(s);
  }
  // §10.10.3 bars an unpacked array concatenation from being an item of
  // another, and §10.10 admits `null` as an item only for the element types
  // that have a null value; neither rule mentions the statement the assignment
  // is written in, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names and names none itself. It wrote out
  // six of the thirteen, so `q = {null, null}` on a queue of ints written in a
  // fork arm or in a randsequence production code block went unreported.
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForArrayConcatNesting(sub); });
}

void ElaboratorOperationRules::ValidateUnpackedArrayConcatNesting(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      WalkStmtsForArrayConcatNesting(item->body);
    }
    CheckArrayConcatNestingInInit(item);
  }
}

namespace {
// Flags any unsized integer literal sitting directly inside a concatenation;
// such literals lack a self-determined width and are illegal there.
void CheckConcatElementsForUnsized(const Expr* concat, DiagEngine& diag) {
  for (auto* elem : concat->elements) {
    if (elem->kind == ExprKind::kIntegerLiteral) {
      auto tick = elem->text.find('\'');
      if (tick == std::string_view::npos || tick == 0) {
        diag.Error(elem->range.start,
                   "unsized constant is not allowed in a concatenation",
                   Subclause("11.4.12"));
      }
    }
  }
}
}  // namespace

void ElaboratorOperationRules::WalkExprForUnsizedInConcat(const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kConcatenation) {
    CheckConcatElementsForUnsized(expr, diag_);
  }
  WalkExprForUnsizedInConcat(expr->lhs);
  WalkExprForUnsizedInConcat(expr->rhs);
  WalkExprForUnsizedInConcat(expr->condition);
  WalkExprForUnsizedInConcat(expr->true_expr);
  WalkExprForUnsizedInConcat(expr->false_expr);
  for (auto* elem : expr->elements) {
    // §11.4.12.1: the unsized-constant restriction is a packed-concatenation
    // rule. A concatenation that is an item of an assignment pattern '{...} is
    // an unpacked array concatenation (§10.10), where unsized constants are
    // legal, so descend into it without applying the element check to it.
    if (expr->kind == ExprKind::kAssignmentPattern &&
        elem->kind == ExprKind::kConcatenation) {
      for (auto* sub : elem->elements) WalkExprForUnsizedInConcat(sub);
      continue;
    }
    WalkExprForUnsizedInConcat(elem);
  }
  for (auto* arg : expr->args) WalkExprForUnsizedInConcat(arg);
}

void ElaboratorOperationRules::WalkStmtsForUnsizedInConcat(const Stmt* s) {
  if (!s) return;

  bool is_array_concat_rhs = s->rhs &&
                             s->rhs->kind == ExprKind::kConcatenation &&
                             s->lhs && s->lhs->kind == ExprKind::kIdentifier &&
                             (s->kind == StmtKind::kBlockingAssign ||
                              s->kind == StmtKind::kNonblockingAssign) &&
                             var_array_info_.count(s->lhs->text);
  if (is_array_concat_rhs) {
    for (auto* elem : s->rhs->elements) WalkExprForUnsizedInConcat(elem);
  } else {
    WalkExprForUnsizedInConcat(s->rhs);
  }
  WalkExprForUnsizedInConcat(s->lhs);
  WalkExprForUnsizedInConcat(s->expr);
  WalkExprForUnsizedInConcat(s->condition);
  WalkExprForUnsizedInConcat(s->assert_expr);
  // §11.4.12 says "Unsized constant numbers shall not be allowed in
  // concatenations", a property of the concatenation and not of the statement
  // holding it, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names and names none itself. It wrote out
  // six of the thirteen, so `a = {x, 1}` written in a fork arm or in an
  // assertion action block was never looked at rather than looked at and
  // allowed.
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForUnsizedInConcat(sub); });
}

void ElaboratorOperationRules::ValidateUnsizedInConcat(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForUnsizedInConcat(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForUnsizedInConcat(item->assign_lhs);
      WalkExprForUnsizedInConcat(item->assign_rhs);
    }
    CheckVarInitUnsizedInConcat(item);
  }
  for (const auto& p : decl->params) {
    WalkExprForUnsizedInConcat(p.second);
  }
}

void ElaboratorOperationRules::CheckVarInitUnsizedInConcat(
    const ModuleItem* item) {
  if (!item->init_expr) return;
  // §10.10: when the initializer of an array variable is a `{...}`
  // concatenation, it is an unpacked array concatenation where unsized integer
  // literals are legal — unlike a packed §11.4.12 concatenation. Descend into
  // the elements without applying the top-level unsized-constant check,
  // mirroring the procedural array-concat assignment path.
  if (item->init_expr->kind == ExprKind::kConcatenation &&
      var_array_info_.count(item->name)) {
    for (auto* elem : item->init_expr->elements)
      WalkExprForUnsizedInConcat(elem);
    return;
  }
  WalkExprForUnsizedInConcat(item->init_expr);
}

static bool IsSelectOnConcat(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kSelect) return false;
  const Expr* base = expr->base;
  while (base && base->kind == ExprKind::kSelect) base = base->base;
  return base && base->kind == ExprKind::kConcatenation;
}

void ElaboratorOperationRules::CheckSelectOnConcatLvalue(const Expr* lhs) {
  if (!lhs) return;
  if (IsSelectOnConcat(lhs)) {
    diag_.Error(lhs->range.start,
                "select of a concatenation shall not be used as an lvalue",
                Subclause("11.4.12"));
  }
  if (lhs->kind == ExprKind::kConcatenation) {
    for (auto* elem : lhs->elements) CheckSelectOnConcatLvalue(elem);
  }
}

void ElaboratorOperationRules::WalkStmtsForSelectOnConcatLvalue(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign || s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    CheckSelectOnConcatLvalue(s->lhs);
  }
  // §11.4.12 says of a select of a concatenation that "Such a select shall not
  // be legal as a net_lvalue, variable_lvalue, or in any equivalent use, such
  // as on the left-hand side of an assignment", which is a rule about the
  // lvalue and not about the statement holding it, so this descends every link
  // ForEachChildStmt in elaborator_validate_internal.h names, naming none
  // itself. It wrote out six of the thirteen, so `{a, b}[2] = 1'b1` written in
  // a fork arm or in a randcase item elaborated clean.
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForSelectOnConcatLvalue(sub); });
}

void ElaboratorOperationRules::ValidateSelectOnConcatLvalue(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForSelectOnConcatLvalue(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckSelectOnConcatLvalue(item->assign_lhs);
    }
  }
}

static bool ExprContainsReplicate(const Expr* expr) {
  if (!expr) return false;
  if (expr->kind == ExprKind::kReplicate) return true;
  if (expr->kind == ExprKind::kConcatenation) {
    for (const auto* elem : expr->elements) {
      if (ExprContainsReplicate(elem)) return true;
    }
  }
  return false;
}

void ElaboratorOperationRules::CheckReplicateLvalue(const Expr* lhs) {
  if (!lhs) return;
  if (ExprContainsReplicate(lhs)) {
    diag_.Error(lhs->range.start,
                "replication shall not appear on the left-hand side "
                "of an assignment",
                Subclause("11.4.12.1"));
  }
}

void ElaboratorOperationRules::WalkStmtsForReplicateLvalue(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign || s->kind == StmtKind::kAssign ||
      s->kind == StmtKind::kForce) {
    CheckReplicateLvalue(s->lhs);
  }
  // §11.4.12.1 says a replication "shall not appear on the left-hand side of an
  // assignment", a rule about the lvalue and not about the statement the
  // assignment stands in, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names and names none itself. It wrote out
  // six of the thirteen, so `{2{a}} = b` written in a fork arm or in an
  // assertion action block reached CheckReplicateLvalue in neither.
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForReplicateLvalue(sub); });
}

void ElaboratorOperationRules::ValidateReplicateLvalue(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForReplicateLvalue(item->body);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckReplicateLvalue(item->assign_lhs);
    }
  }
}

static bool RepeatCountHasXZ(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kIntegerLiteral) {
    auto apos = e->text.find('\'');
    if (apos != std::string_view::npos) {
      return e->text.substr(apos + 1).find_first_of("xXzZ") !=
             std::string_view::npos;
    }
  }
  return false;
}

namespace {
// Validates the repeat count of a single replication: it must not contain x/z
// and, when constant, must not be negative. The multiplier is a constant
// expression, so it is evaluated in the module parameter scope — a parameter
// or localparam multiplier resolves the same way a literal one does.
void CheckReplicateRepeatCount(const Expr* replicate, const ScopeMap& scope,
                               DiagEngine& diag) {
  const Expr* rc = replicate->repeat_count;
  if (RepeatCountHasXZ(rc)) {
    diag.Error(rc->range.start,
               "replication multiplier shall not contain x or z",
               Subclause("11.4.12.1"));
    return;
  }
  auto val = ConstEvalInt(rc, scope);
  if (val && *val < 0) {
    diag.Error(rc->range.start, "replication multiplier shall not be negative",
               Subclause("11.4.12.1"));
  }
}
}  // namespace

void ElaboratorOperationRules::WalkExprForReplicateMultiplier(
    const Expr* expr) {
  if (!expr) return;
  if (expr->kind == ExprKind::kReplicate) {
    CheckReplicateRepeatCount(expr, replicate_multiplier_scope_, diag_);
  }
  WalkExprForReplicateMultiplier(expr->lhs);
  WalkExprForReplicateMultiplier(expr->rhs);
  WalkExprForReplicateMultiplier(expr->condition);
  WalkExprForReplicateMultiplier(expr->true_expr);
  WalkExprForReplicateMultiplier(expr->false_expr);
  for (auto* elem : expr->elements) WalkExprForReplicateMultiplier(elem);
  for (auto* arg : expr->args) WalkExprForReplicateMultiplier(arg);
}

static bool IsZeroReplicate(const Expr* expr, const ScopeMap& scope) {
  if (!expr || expr->kind != ExprKind::kReplicate) return false;
  auto val = ConstEvalInt(expr->repeat_count, scope);
  return val && *val == 0;
}

static void CheckZeroReplicateStandalone(const Expr* expr,
                                         const ScopeMap& scope,
                                         DiagEngine& diag);

// True when a concatenation is non-empty and every operand is a zero
// replication, which leaves no positive-size operand to host them.
static bool ConcatIsAllZeroReplicate(const Expr* concat,
                                     const ScopeMap& scope) {
  if (concat->elements.empty()) return false;
  for (const auto* elem : concat->elements) {
    if (!IsZeroReplicate(elem, scope)) return false;
  }
  return true;
}

// Handles the concatenation arm of CheckZeroReplicateStandalone: a
// concatenation built entirely of zero replications is illegal, and any
// non-zero-replication operand is recursed into.
static void CheckZeroReplicateInConcat(const Expr* concat,
                                       const ScopeMap& scope,
                                       DiagEngine& diag) {
  if (ConcatIsAllZeroReplicate(concat, scope)) {
    diag.Error(concat->range.start,
               "zero replication shall appear only within a concatenation "
               "in which at least one operand has a positive size",
               Subclause("11.4.12.1"));
  }
  for (const auto* elem : concat->elements) {
    if (!IsZeroReplicate(elem, scope)) {
      CheckZeroReplicateStandalone(elem, scope, diag);
    }
  }
}

static void CheckZeroReplicateStandalone(const Expr* expr,
                                         const ScopeMap& scope,
                                         DiagEngine& diag) {
  if (!expr) return;
  if (IsZeroReplicate(expr, scope)) {
    diag.Error(expr->range.start,
               "zero replication shall appear only within a concatenation "
               "in which at least one operand has a positive size",
               Subclause("11.4.12.1"));
  }
  if (expr->kind == ExprKind::kConcatenation) {
    CheckZeroReplicateInConcat(expr, scope, diag);
    return;
  }
  CheckZeroReplicateStandalone(expr->lhs, scope, diag);
  CheckZeroReplicateStandalone(expr->rhs, scope, diag);
  CheckZeroReplicateStandalone(expr->condition, scope, diag);
  CheckZeroReplicateStandalone(expr->true_expr, scope, diag);
  CheckZeroReplicateStandalone(expr->false_expr, scope, diag);
  for (const auto* elem : expr->elements)
    CheckZeroReplicateStandalone(elem, scope, diag);
  for (const auto* arg : expr->args)
    CheckZeroReplicateStandalone(arg, scope, diag);
}

static void WalkStmtsForZeroReplicateStandalone(const Stmt* s,
                                                const ScopeMap& scope,
                                                DiagEngine& diag) {
  if (!s) return;
  CheckZeroReplicateStandalone(s->rhs, scope, diag);
  CheckZeroReplicateStandalone(s->lhs, scope, diag);
  CheckZeroReplicateStandalone(s->expr, scope, diag);
  CheckZeroReplicateStandalone(s->condition, scope, diag);
  CheckZeroReplicateStandalone(s->assert_expr, scope, diag);
  // §11.4.12.1 allows a zero replication only inside a concatenation holding an
  // operand of positive size, and says nothing about the statement the
  // replication is written in, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names and names none itself. It wrote out
  // six of the thirteen, so `result = {0{a}}` written in a fork arm or in a
  // randcase item was never looked at.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForZeroReplicateStandalone(sub, scope, diag);
  });
}

void ElaboratorOperationRules::WalkStmtsForReplicateMultiplier(const Stmt* s) {
  if (!s) return;
  WalkExprForReplicateMultiplier(s->rhs);
  WalkExprForReplicateMultiplier(s->lhs);
  WalkExprForReplicateMultiplier(s->expr);
  WalkExprForReplicateMultiplier(s->condition);
  WalkExprForReplicateMultiplier(s->assert_expr);
  // §11.4.12.1 requires a replication multiplier to be a constant expression
  // that is neither negative nor x/z, a rule about the multiplier and not about
  // the statement around it, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names and names none itself. It wrote out
  // six of the thirteen, so `a = {1'bx{1'b0}}` written in a fork arm or in a
  // randsequence production code block went unreported.
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForReplicateMultiplier(sub); });
}

void ElaboratorOperationRules::ValidateReplicateMultiplier(
    const ModuleDecl* decl) {
  const ScopeMap& scope = replicate_multiplier_scope_;
  for (const auto* item : decl->items) {
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForReplicateMultiplier(item->body);
      WalkStmtsForZeroReplicateStandalone(item->body, scope, diag_);
    }
    if (item->kind == ModuleItemKind::kContAssign) {
      WalkExprForReplicateMultiplier(item->assign_lhs);
      WalkExprForReplicateMultiplier(item->assign_rhs);
      CheckZeroReplicateStandalone(item->assign_lhs, scope, diag_);
      CheckZeroReplicateStandalone(item->assign_rhs, scope, diag_);
    }
    if (item->init_expr) {
      WalkExprForReplicateMultiplier(item->init_expr);
      CheckZeroReplicateStandalone(item->init_expr, scope, diag_);
    }
  }
  for (const auto& p : decl->params) {
    WalkExprForReplicateMultiplier(p.second);
    CheckZeroReplicateStandalone(p.second, scope, diag_);
  }
}

}  // namespace delta
