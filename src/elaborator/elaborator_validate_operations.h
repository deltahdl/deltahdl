#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <span>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_class_typedef_specialization.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/net_data_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_ref_walks.h"
#include "elaborator/unpacked_array_type.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;
class DiagEngine;
struct Expr;
struct ExprTypeScope;

class ElaboratorOperationRules : public ElaboratorData {
 protected:
  ElaboratorOperationRules(Arena& arena, DiagEngine& diag,
                           CompilationUnit* unit)
      : arena_(arena), diag_(diag), unit_(unit) {}

  void ValidateAssocConcatTarget(const ModuleDecl* decl);
  void WalkStmtsForAssocConcatTarget(const Stmt* s);
  void CheckAssocConcatTargetInAssign(const Stmt* s);
  bool DeclaresAssocArray(const std::vector<Expr*>& dims) const;
  void CheckAssocConcatInit(const Expr* init, const std::vector<Expr*>& dims);

  void ValidateAggregateOperands(const ModuleDecl* decl);

  void ValidateArrayPatternElemType(const ModuleDecl* decl);
  void WalkStmtsForArrayPatternElemType(const Stmt* s);
  void CheckArrayPatternElemTypeInAssign(const Stmt* s);
  void CheckArrayPatternElemTypeInInit(const ModuleItem* item);
  void ValidateProceduralArrayPatterns(const ModuleDecl* decl);
  void WalkStmtsForProceduralArrayPattern(const Stmt* s);
  void CheckContinuousArrayPattern(const ModuleItem* item);
  std::unordered_map<std::string_view, const ModuleItem*>
      pattern_target_arrays_;
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
  void CheckNestedArrayConcatItems(const Expr* concat);
  void CheckArrayConcatItemTypes(const Expr* concat, const VarArrayInfo& info);
  void CheckArrayConcatNestingInAssign(const Stmt* s);
  void CheckArrayConcatNestingInInit(const ModuleItem* item);
  void CheckNullItemInArrayConcatAssign(const Stmt* s);

  void ValidateAggregateComparisons(const ModuleDecl* decl);
  void WalkExprForAggregateCompare(const Expr* expr);
  void CheckAggregateCompareOp(const Expr* expr);
  bool ReportNonEquivalentArrayOperands(const Expr* expr);
  std::optional<bool> ArrayOperandsEquivalent(const Expr* lhs,
                                              const Expr* rhs) const;
  void WalkStmtsForAggregateCompare(const Stmt* s);

  void ValidateTypeRefComparisons(const ModuleDecl* decl);
  void WalkExprForTypeRefCompare(const Expr* expr);
  void ReportTypeRefOperand(const Expr* operand, const Expr* op);
  void CheckTypeRefCompareOp(const Expr* expr);
  void WalkStmtsForTypeRefCompare(const Stmt* s);

  std::optional<DataType> CalledFunctionType(const Expr* e) const;
  const ModuleItem* BareNamedFunction(std::string_view name) const;
  std::optional<DataType> ClassScopedCallType(const Expr* scoped) const;
  std::optional<ClassSpecialization> ClassTypeOf(const DataType& type) const;
  std::optional<UnpackedArrayType> MemberTypeOf(
      const ClassSpecialization& handle, std::string_view name,
      const ScopeMap& constants) const;
  std::optional<UnpackedArrayType> ClassMemberType(
      const DataType& handle, std::string_view name,
      const ScopeMap& constants) const;
  std::optional<bool> DataTypesMatch(const DataType& a, const DataType& b,
                                     const ScopeMap& constants) const;
  std::optional<bool> TypeRefsMatch(const Expr* a, const Expr* b,
                                    const RtlirModule* mod) const;
  std::optional<UnpackedArrayType> ResolveTypeRefOperandArray(
      const Expr* op, const RtlirModule* mod = nullptr) const;
  std::optional<UnpackedArrayType> TypeRefOperandArray(
      const Expr* op, const RtlirModule* mod) const;
  std::optional<DataType> ResolveTypeRefOperandType(
      const Expr* op, const RtlirModule* mod = nullptr) const;
  TypeShapeTables ArrayTables() const;
  void InExprTypeScope(
      const RtlirModule& mod,
      const std::function<void(const ExprTypeScope&)>& use) const;
  void InUnitExprTypeScope(
      const std::function<void(const ExprTypeScope&)>& use) const;
  std::optional<DataType> UnitCallType(const Expr* call) const;
  void ValidateUnitScopeTypeRefArgs();
  void ElaborateUnitScopeProcedures();
  bool InOperandScope(
      const RtlirModule* mod,
      const std::function<void(const ExprTypeScope&)>& use) const;
  std::optional<DataType> TypeRefExprType(const Expr* expr,
                                          const RtlirModule* mod) const;
  std::optional<UnpackedArrayType> TypeRefArrayType(
      const Expr* expr, const RtlirModule* mod) const;
  std::optional<UnpackedArrayType> TypeRefValueArray(
      const Expr* ref, const RtlirModule* mod) const;
  std::vector<Expr*> TypeRefUnpackedDims(const Expr* ref,
                                         const RtlirModule* mod) const;
  std::optional<int64_t> EvalConstTypeRefCompare(
      const Expr* expr, const RtlirModule* mod = nullptr) const;
  TypeRefComparer type_ref_compare_ = [this](const Expr* expr,
                                             const RtlirModule* mod) {
    return EvalConstTypeRefCompare(expr, mod);
  };

  void ValidateTypeRefArgs(const ModuleDecl* decl);
  void WalkItemExprsForTypeRefArg(const ModuleItem* item);
  void WalkExprForTypeRefArg(const Expr* expr);
  void WalkStmtsForTypeRefArg(const Stmt* s);
  void CheckTypeRefArgInner(const Expr* inner, SourceLoc loc,
                            const RtlirModule* mod);
  bool ReportHierarchicalArg(const Expr* inner, SourceLoc loc);
  void ReportDynamicElementArg(const Expr* inner, SourceLoc loc,
                               const RtlirModule* mod);
  void CheckDynamicElementArgsOfStmt(const Stmt* s, const RtlirModule* mod);
  bool TypeRefArgUsesDynamicElement(const Expr* e,
                                    const RtlirModule* mod) const;
  bool IsHierarchicalMemberAccess(const Expr* e) const;
  bool NamesSelectableValue(const Expr* root) const;
  bool NamesModuleValue(std::string_view name) const;
  static bool DeclaresSelectableType(const DataType& type);
  bool DeclaresSelectableValue(const std::vector<ModuleItem*>& items,
                               std::string_view name) const;
  bool ImportsSelectableValue(const std::vector<ModuleItem*>& items,
                              std::string_view name) const;
  const ModuleDecl* TypeRefModule() const;
  bool TypeRefArgHasMemberAccess(const Expr* e) const;
  struct BlockValue {
    std::string_view name;
    bool selectable;
    const DataType* type;
    const std::vector<Expr*>* dims;
  };
  std::vector<BlockValue> type_ref_block_vars_;
  const BlockValue* InnermostBlockValue(std::string_view name) const;
  void InLocals(std::span<const ProceduralLocal> locals,
                const std::function<void()>& use);
  const ModuleDecl* type_ref_module_ = nullptr;
  const RtlirModule* type_ref_mod_ = nullptr;
  const PackageDecl* type_ref_package_ = nullptr;
  std::vector<UnitScopeTypeRef> unit_scope_type_refs_;
  std::vector<TypeRefCompareResult> unit_type_ref_compares_;
  bool type_ref_in_unit_procedure_ = false;
  std::unordered_set<const Expr*> reported_type_ref_args_;
  TypeRefResolver ResolverAmongLocals(
      const RtlirModule* mod,
      std::function<void(DataType&, SourceLoc)> resolve);

  void ValidateTaggedUnionMembers(const ModuleDecl* decl);

  void ValidateRealOperatorRestrictions(const ModuleDecl* decl);
  void WalkExprForRealOps(const Expr* expr);
  void WalkStmtsForRealOps(const Stmt* s);
  void WalkItemsForRealOps(const std::vector<ModuleItem*>& items);
  void WalkSubroutineForRealOps(const ModuleItem* item);

  void ValidateCastOperations(const ModuleDecl* decl);
  void WalkExprForCast(const Expr* expr);
  void WalkStmtsForCast(const Stmt* s);
  void CheckCastExpr(const Expr* expr);
  void CheckSigningSystemCallExpr(const Expr* expr);
  bool CastOperandIsReal(const Expr* operand) const;
  bool CastOperandIsNonIntegral(const Expr* operand) const;
  std::unordered_set<std::string_view> cast_unpacked_structs_;

  void ValidateLetScope(const ModuleDecl* decl);
  void CheckLetUsedBeforeDeclared(const ModuleDecl* decl);
  void CheckLetReferencedHierarchically(const ModuleDecl* decl);
  void CheckLetActualTypes(const ModuleDecl* decl);
  void CheckUnitLetActualTypes();

  void ValidateAssignInExprRestrictions(const ModuleDecl* decl);
  void WalkExprForAssignInExpr(const Expr* expr, bool in_event_or_cont);
  void WalkStmtsForAssignInExpr(const Stmt* s);

  void ValidateUnsizedInConcat(const ModuleDecl* decl);
  void CheckVarInitUnsizedInConcat(const ModuleItem* item);
  void CheckContAssignUnsizedInConcat(const ModuleItem* item);
  bool IsUnpackedArrayConcatTarget(const Expr* lhs) const;
  void WalkExprForUnsizedInConcat(const Expr* expr);
  void WalkStmtsForUnsizedInConcat(const Stmt* s);
  void WalkItemsOrExprForUnsizedInConcat(const Expr* e, bool is_array_concat);
  void CheckBlockVarInitUnsizedInConcat(const Stmt* s);
  std::vector<std::pair<std::string_view, bool>> block_decls_;
  bool returns_unpacked_array_ = false;
  std::unordered_map<std::string_view, const DataType*> concat_target_types_;
  bool SelectsArrayElementArray(const Expr* sel) const;
  std::optional<bool> StructMemberIsArray(const Expr* lhs) const;

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
  std::unordered_map<std::string_view, const DataType*> stream_operand_types_;
  void CheckStreamingSourceTargetType(const Expr* lhs, const Expr* rhs);
  void CheckStreamingUnpackSourceType(const Expr* lhs, const Expr* rhs);

  void ValidateBitStreamCast(const ModuleDecl* decl);
  void WalkExprForBitStreamCast(const Expr* expr);
  void WalkStmtsForBitStreamCast(const Stmt* s);
  void CheckBitStreamCastExpr(const Expr* expr);
  std::unordered_map<std::string_view, const DataType*> bit_stream_var_types_;
  Arena& arena_;
  DiagEngine& diag_;
  CompilationUnit* unit_;
};

}  // namespace delta
