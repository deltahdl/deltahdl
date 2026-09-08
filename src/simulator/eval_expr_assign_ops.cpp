// The read-modify-write assignment expressions: §11.4.1's assignment operators
// (`+=`, `<<=` and the rest) and §11.4.2's increment and decrement. Both read a
// target, compute a new value from it and write it back in one expression, and
// §11.4.1 states them as blocking assignments -- "An assignment operator is
// semantically equivalent to a blocking assignment, with the exception that any
// left-hand index expression is only evaluated once" -- which is why they share
// the writers a statement uses and the snapshot that exception needs.
//
// src/simulator/eval_expr.cpp holds the rest of the expression evaluator, which
// reads rather than writes.

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/assoc_element.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// Applies a real-valued unary increment/decrement by unpacking the IEEE-754
// bits of old_val, adding delta (+1.0 for ++, -1.0 for --), and repacking. The
// result is packed at the operand's own width because incrementing does not
// change the declared type: a §6.12 shortreal stays 32 bits wide, and widening
// it here would leave a single-precision variable holding a double pattern.
static Logic4Vec ApplyRealUnaryOp(const Logic4Vec& old_val, double delta,
                                  Arena& arena) {
  return MakeRealVec(arena, RealVecToDouble(old_val) + delta, old_val.width);
}

// Shared by the prefix and postfix ++/-- operators: evaluates the operand,
// computes the incremented/decremented value, writes it back to the target,
// and returns the {old, new} pair so each caller can return its own side.
struct IncDecResult {
  Logic4Vec old_val;
  Logic4Vec new_val;
};

// §11.4.2: "These increment and decrement assignment operators behave as
// blocking assignments", so §10.4's list of left-hand sides governs them and
// §11.4.1's once-only left-hand index rule comes with it. This wrote a plain
// identifier and handed a select to TryAssocIndexedWrite, which answers only
// for an associative element, so an unpacked array element, a queue element, a
// bit-select, a part-select, a compound a[i][j] and the byte a string's index
// names were all incremented by nothing, with nothing reported; a member access
// had no arm at all. EvalCompoundAssign below is the same read-modify-write
// over the same targets and asks the same two writers.
// Writes an increment's or decrement's new value to whichever of §10.4's
// variable lvalues the operand names. §11.4.2 states these operators as
// blocking assignments, so the target forms are the ones a blocking assignment
// admits and the writers are the ones it uses. new_val is taken by reference
// because §6.11.2's coercion is applied to it here and the operator yields it.
static void WriteIncDecTarget(const Expr* lhs, Logic4Vec& new_val,
                              SimContext& ctx, Arena& arena) {
  if (lhs->kind == ExprKind::kSelect) {
    TrySelectBlockingAssign(lhs, new_val, ctx, arena);
    return;
  }
  if (lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(lhs, new_val, ctx);
    return;
  }
  if (lhs->kind != ExprKind::kIdentifier) return;
  auto* var = ctx.FindVariable(lhs->text);
  if (var == nullptr) return;
  // §6.11.2 gives a 2-state type no x and no z, so an unknown result is coerced
  // before it is stored, as WriteVar and EvalCompoundAssign coerce theirs.
  // Nothing had to do this while the arithmetic could only produce known bits.
  if (!var->is_4state) CoerceTo2State(new_val);
  // §10.6.2: a force "shall override a procedural assignment ... until a
  // release procedural statement is executed on the variable". Only the write
  // is overridden: the operator still yields the value it computed, which is
  // what the enclosing expression reads.
  //
  // §9.4.2: "A non-edge implicit event shall be detected on any change in the
  // value of the expression", and a value "referenced by a method or function"
  // that changes "shall cause the event expression to be reevaluated". The
  // clause exempts no writer, so an increment is a change exactly as an `=` is.
  // This stored and said nothing, and NotifyWatchers is the only route by which
  // a parked process is resumed, so the wake-up ended rather than waiting. It
  // sits inside the gate, where WriteVar and ExecFuncIdentifierAssign put
  // theirs, because a write that did not land is no change to detect. It is
  // otherwise unconditional: whether a change counts is the awaiter's own test,
  // which ChangeGatePasses and CheckEdge already make.
  if (!var->is_forced) {
    var->value = new_val;
    var->NotifyWatchers();
  }
}

static IncDecResult EvalIncDec(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  // §11.4.1's exception, inherited: the allocation, the read and the write each
  // re-derive the target from expr->lhs, so a side-effecting index would run
  // once apiece. This is taken before the allocation, which is one of them.
  SnapshotSelectIndices(expr->lhs, ctx, arena);
  // §7.8.7: an increment reads and writes in one statement, so a nonexistent
  // associative array element is allocated with its initial value before the
  // read below rather than by the write after it.
  AllocateAssocEntryForModify(expr->lhs, ctx, arena);
  auto old_val = EvalExpr(expr->lhs, ctx, arena);
  Logic4Vec new_val;
  if (old_val.is_real) {
    new_val = ApplyRealUnaryOp(
        old_val, (expr->op == TokenKind::kPlusPlus) ? 1.0 : -1.0, arena);
  } else {
    // §11.4.2 states these operators as blocking assignments, and §11.4.1
    // states `i += 1` as one too, so the two spellings are one assignment of
    // one arithmetic result and are computed by one arithmetic. That is
    // EvalBinaryOp, which EvalCompoundAssign below already reaches, rather than
    // a uint64_t. ToUint64 projects `aval & ~bval`, which reads an x or a z as
    // a 0 and hands back a value every bit of which is known, so §11.4.3's
    // "if any operand bit value is the unknown value x or the high-impedance
    // value z, then the entire result value shall be x" was not applied to an
    // increment at all: `integer i = 'x; i++;` left i at 1.
    //
    // The 1 is built at the operand's own width because EvalBinaryArith sizes
    // its result at the wider operand: a 32-bit literal would widen a
    // bit-select's or a part-select's result past the window being written.
    auto one = MakeLogic4VecVal(arena, old_val.width, 1);
    // §11.4.3.1 fixes an operand's interpretation by its declaration, and
    // EvalBinaryArith reads signed arithmetic from both operands rather than
    // either, so the 1 carries what the target carries. It is what leaves the
    // result signed, an unknown result included.
    one.is_signed = old_val.is_signed;
    new_val =
        EvalBinaryOp((expr->op == TokenKind::kPlusPlus) ? TokenKind::kPlus
                                                        : TokenKind::kMinus,
                     old_val, one, arena);
  }
  WriteIncDecTarget(expr->lhs, new_val, ctx, arena);
  ClearSelectIndices(expr->lhs, ctx);
  return {old_val, new_val};
}

Logic4Vec EvalPrefixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  return EvalIncDec(expr, ctx, arena).new_val;
}

Logic4Vec EvalPostfixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  return EvalIncDec(expr, ctx, arena).old_val;
}

// §11.4.1 lists the assignment operators as the simple `=` plus "the C
// assignment operators and special bitwise assignment operators: +=, -=, *=,
// /=, %=, &=, |=, ^=, <<=, >>=, <<<=, and >>>=". This gives the binary operator
// each of those assigns the result of, and answers kEof for a token that is not
// one of them, which is what IsCompoundAssignOp reads.
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

// §11.4.1: "An assignment operator is semantically equivalent to a blocking
// assignment, with the exception that any left-hand index expression is only
// evaluated once", and writes `a[i]+=2;` as the same statement as
// `a[i] = a[i] +2;`. So §11.6.1 sizes the operation by the target and §10.7
// truncates the result into it, neither of which happened: the operation was
// evaluated with no context and the result written over the target, so
// `logic [3:0] v; v += 8'hFF;` left v eight bits wide.
//
// §11.3.6 settles the value the expression yields as well as the one it stores.
// An assignment expression "evaluates the right-hand side, casts the right-hand
// side to the left-hand data type, stacks it, updates the left-hand side, and
// returns the stacked value", and "the data type of the value that is returned
// is the data type of the left-hand side" -- so the coerced value is what is
// returned, which is what `b = (a += 1)`, the clause's own example, reads.
Logic4Vec EvalCompoundAssign(const Expr* expr, SimContext& ctx, Arena& arena) {
  // §11.4.1's one exception to this being an ordinary blocking assignment:
  // "any left-hand index expression is only evaluated once". The allocation,
  // the read and the write below each re-derive the target from expr->lhs and
  // would call a side-effecting index once apiece, so the indices are evaluated
  // here and stashed for those to find. This runs before the allocation, which
  // is itself one of the readers.
  SnapshotSelectIndices(expr->lhs, ctx, arena);
  // §7.8.7: as in EvalIncDec, the element this reads and writes is allocated
  // before the read.
  AllocateAssocEntryForModify(expr->lhs, ctx, arena);
  uint32_t target_width = LhsContextWidth(expr->lhs, ctx, arena);
  // §11.6.1 sizes the operation from the left-hand side and §11.3.6 sizes the
  // value the expression yields from it too, so the two start from one answer;
  // the member arm below replaces it with the one its writer resolved.
  uint32_t yield_width = target_width;
  auto lhs_val = EvalExpr(expr->lhs, ctx, arena);
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);
  auto base_op = CompoundAssignBaseOp(expr->op);
  auto result = EvalBinaryOp(base_op, lhs_val, rhs_val, arena, target_width);
  if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) {
      result =
          ConvertRealOnAssign(result, expr->lhs, var->value.width, ctx, arena);
      if (!var->is_4state) CoerceTo2State(result);
      // §10.6.2, as in EvalIncDec above. §11.3.6 has the expression "stack" the
      // value and return it whether or not the update lands, so the return
      // below is the value computed rather than what the target still holds.
      //
      // §9.4.2 again, as in WriteIncDecTarget: the update is a change in the
      // variable's value and its watchers are told so, inside the same gate,
      // because the write that does not land is not a change.
      if (!var->is_forced) {
        var->value = result;
        var->NotifyWatchers();
      }
    }
  } else if (expr->lhs->kind == ExprKind::kSelect) {
    // TrySelectBlockingAssign is what the statement form reaches, and it
    // answers for every select §10.4 admits: an unpacked array element, a queue
    // or associative element, the bits of an associative element, a compound
    // a[i][j], the byte a string's index names, and otherwise the window a
    // bit-select or part-select opens. Asking only TryAssocIndexedWrite left
    // every one of the others writing nothing and reporting nothing.
    //
    // The value is handed over as the operation produced it, each of those
    // writers sizing it by what it is writing into -- an element's own width,
    // or the bits a select names. What the expression yields is sized below,
    // from LhsContextWidth, which answers the two shapes apart: the bits a
    // select names within a packed object, and the whole element an unpacked
    // array, queue or associative index names.
    TrySelectBlockingAssign(expr->lhs, result, ctx, arena);
  } else if (expr->lhs->kind == ExprKind::kMemberAccess) {
    // §10.4 admits a member access as a left-hand side too, and the statement
    // form reaches WriteStructField for it. This arm did not exist, so
    // `q = (s.lo += 3)` wrote nothing. The width comes back from the writer:
    // a member access resolves to a window of a packed variable, an interface
    // component or a class property, and LhsContextWidth answers for none of
    // them -- ResolveLhsVariable looks the flattened name `s.lo` up and finds
    // no variable.
    WriteStructField(expr->lhs, result, ctx, &yield_width);
  }
  ClearSelectIndices(expr->lhs, ctx);
  // §11.3.6: an assignment expression "evaluates the right-hand side, casts the
  // right-hand side to the left-hand data type, stacks it, updates the
  // left-hand side, and returns the stacked value. The data type of the value
  // that is returned is the data type of the left-hand side." The write itself
  // was already right -- each writer sizes the value by what it is writing into
  // -- and it is the value the surrounding expression reads that carried the
  // operation's width instead of the target's. Zero means no width was found
  // for the left-hand side, and the value is left as it is rather than resized
  // to nothing.
  if (yield_width != 0 && yield_width != result.width)
    return ResizeToWidth(result, yield_width, arena);
  return result;
}

}  // namespace delta
