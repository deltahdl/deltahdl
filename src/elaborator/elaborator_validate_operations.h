#pragma once

#include <cstdint>
#include <optional>
#include <string_view>

#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_data.h"
#include "parser/ast.h"

namespace delta {

class Arena;
class DiagEngine;
struct Expr;

// The rules an expression has to keep, whatever statement or declaration it is
// written in. Clause 11 states most of them -- §11.4.12 on concatenation and
// §11.4.12.1 on replication, §11.5 and §11.5.1 on the selects, §11.4.4 on
// comparison, §11.4.14 on streaming concatenation -- and §6.23's type reference
// and §6.24's casts state the rest. What they share is the question they ask:
// whether one expression is well formed, given the types of its operands and
// the context it stands in.
//
// They are a class of their own because src/elaborator/elaborator.h reached the
// 950 lines at which assert-no-oversized-source-files in
// .github/workflows/deltahdl.yml asks for a split, and this is the group whose
// boundary the standard draws for itself: no declaration here elaborates
// anything, and none is reached from anywhere but Elaborator's validation
// drivers. The definitions were already gathered in
// src/elaborator/elaborator_validate_operations.cpp and the two files beside
// it, so the header a group is declared in is now the one its definitions live
// in.
//
// Elaborator derives from this rather than holding one, because every check
// here reports through `diag_` and reads the compilation unit through `unit_`,
// and those three references are what the whole elaborator is built on. They
// are declared here for the same reason: a base cannot reach a derived class's
// members, so the state the base needs has to be the base's own.
class ElaboratorOperationRules : public ElaboratorData {
 protected:
  ElaboratorOperationRules(Arena& arena, DiagEngine& diag,
                           CompilationUnit* unit)
      : arena_(arena), diag_(diag), unit_(unit) {}

  void ValidateAssocConcatTarget(const ModuleDecl* decl);
  void WalkStmtsForAssocConcatTarget(const Stmt* s);
  void CheckAssocConcatTargetInAssign(const Stmt* s);

  void ValidateAssocOperandInExpr(const ModuleDecl* decl);
  void WalkStmtsForAssocOperand(const Stmt* s);
  void CheckAssocOperandInBinaryExpr(const Expr* e);

  void ValidateArrayPatternElemType(const ModuleDecl* decl);
  void WalkStmtsForArrayPatternElemType(const Stmt* s);
  void CheckArrayPatternElemTypeInAssign(const Stmt* s);
  void CheckArrayPatternElemTypeInInit(const ModuleItem* item);
  void ValidateReplicateTargetingArray(const ModuleDecl* decl);
  void WalkStmtsForReplicateTargetingArray(const Stmt* s);
  void CheckReplicateTargetingArrayInAssign(const Stmt* s);
  void CheckReplicateTargetingArrayInit(const ModuleItem* item);

  void ValidateArrayElementPartSelect(const ModuleDecl* decl);
  void WalkStmtsForArrayElementPartSelect(const Stmt* s);
  void WalkExprForArrayElementPartSelect(const Expr* e);
  void CheckArrayElementPartSelectNode(const Expr* e);

  void ValidateUnpackedArrayConcatNesting(const ModuleDecl* decl);
  void WalkStmtsForArrayConcatNesting(const Stmt* s);
  void CheckArrayConcatNestingInAssign(const Stmt* s);
  void CheckArrayConcatNestingInInit(const ModuleItem* item);
  void CheckNullItemInArrayConcatAssign(const Stmt* s);

  void ValidateAggregateComparisons(const ModuleDecl* decl);
  void WalkExprForAggregateCompare(const Expr* expr);
  void CheckAggregateCompareOp(const Expr* expr);
  void WalkStmtsForAggregateCompare(const Stmt* s);

  void ValidateTypeRefComparisons(const ModuleDecl* decl);
  void WalkExprForTypeRefCompare(const Expr* expr);
  void CheckTypeRefCompareOp(const Expr* expr);
  void WalkStmtsForTypeRefCompare(const Stmt* s);

  // §6.23: resolve one type-reference operand of a comparison to the concrete
  // data type it denotes, following the typedef/type-parameter tables. Returns
  // nullopt when the operand is not a type reference or names a type this pass
  // cannot resolve (e.g. a plain variable), so the caller leaves it unfolded.
  std::optional<DataType> ResolveTypeRefOperandType(const Expr* op) const;
  // §6.23: fold a type-reference equality/inequality/case-equality comparison
  // to a constant 0/1 using §6.22.1 type matching. Returns nullopt when `expr`
  // is not such a comparison or an operand cannot be resolved.
  std::optional<int64_t> EvalConstTypeRefCompare(const Expr* expr) const;

  void ValidateTypeRefArgs(const ModuleDecl* decl);
  void WalkExprForTypeRefArg(const Expr* expr);
  void WalkStmtsForTypeRefArg(const Stmt* s);
  void CheckTypeRefArgInner(const Expr* inner, SourceLoc loc);
  bool TypeRefArgUsesDynamicElement(const Expr* e) const;

  void ValidateTaggedUnionMembers(const ModuleDecl* decl);
  void WalkStmtsForTaggedExpr(const Stmt* s);
  void CheckTaggedExprMember(const Expr* lhs, const Expr* rhs);
  void CheckTaggedMemberName(std::string_view var_name, const Expr* rhs);

  void ValidateRealOperatorRestrictions(const ModuleDecl* decl);
  void WalkExprForRealOps(const Expr* expr);
  void WalkStmtsForRealOps(const Stmt* s);

  // §6.24.1: size-cast width and size/signing-cast integral-operand rules, and
  // §11.7's same integral-argument rule for $signed and $unsigned.
  void ValidateCastOperations(const ModuleDecl* decl);
  void WalkExprForCast(const Expr* expr);
  void WalkStmtsForCast(const Stmt* s);
  void CheckCastExpr(const Expr* expr);
  // §11.7: rejects a real argument to $signed or $unsigned, which shall return
  // a packed array holding the bits of its input. Called from CheckCastExpr,
  // which WalkExprForCast reaches for every expression.
  void CheckSigningSystemCallExpr(const Expr* expr);
  bool CastOperandIsReal(const Expr* operand) const;

  void ValidateAssignInExprRestrictions(const ModuleDecl* decl);
  void WalkExprForAssignInExpr(const Expr* expr, bool in_event_or_cont);
  void WalkStmtsForAssignInExpr(const Stmt* s);

  void ValidateUnsizedInConcat(const ModuleDecl* decl);
  void CheckVarInitUnsizedInConcat(const ModuleItem* item);
  void WalkExprForUnsizedInConcat(const Expr* expr);
  void WalkStmtsForUnsizedInConcat(const Stmt* s);

  void ValidateSelectOnConcatLvalue(const ModuleDecl* decl);
  void CheckSelectOnConcatLvalue(const Expr* lhs);
  void WalkStmtsForSelectOnConcatLvalue(const Stmt* s);

  void ValidateReplicateLvalue(const ModuleDecl* decl);
  void CheckReplicateLvalue(const Expr* lhs);
  void WalkStmtsForReplicateLvalue(const Stmt* s);

  void ValidateReplicateMultiplier(const ModuleDecl* decl);
  void WalkExprForReplicateMultiplier(const Expr* expr);
  void WalkStmtsForReplicateMultiplier(const Stmt* s);

  void ValidateStringConcatLvalue(const ModuleDecl* decl);
  void CheckStringConcatLvalue(const Expr* lhs);
  void WalkStmtsForStringConcatLvalue(const Stmt* s);
  bool ConcatContainsStringElement(const Expr* expr);

  void ValidateStreamingConcatContext(const ModuleDecl* decl);
  void WalkExprForStreamingContext(const Expr* expr, bool is_valid_context);
  void WalkStmtsForStreamingContext(const Stmt* s);
  void CheckStreamingSourceTargetType(const Expr* lhs, const Expr* rhs);
  void CheckStreamingUnpackSourceType(const Expr* lhs, const Expr* rhs);

  // §6.24.3: enforces the destination/source/size constraints on a bit-stream
  // cast. Walks every expression in a module and rejects illegal forms before
  // the simulator ever sees them.
  void ValidateBitStreamCast(const ModuleDecl* decl);
  void WalkExprForBitStreamCast(const Expr* expr);
  void WalkStmtsForBitStreamCast(const Stmt* s);
  void CheckBitStreamCastExpr(const Expr* expr);
  Arena& arena_;
  DiagEngine& diag_;
  CompilationUnit* unit_;
};

}  // namespace delta
