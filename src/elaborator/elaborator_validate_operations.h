#pragma once

#include <cstdint>
#include <functional>
#include <optional>
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
// src/elaborator/elaborator_validate_operations.cpp and the files beside
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
  bool DeclaresAssocArray(const std::vector<Expr*>& dims) const;
  void CheckAssocConcatInit(const Expr* init, const std::vector<Expr*>& dims);

  // §11.3 and §11.4.13: an unpacked structure or union as an operand of an
  // operator that takes no aggregate, and an unpacked array or structure as
  // the left operand of `inside`; §7.4.6: an unpacked array, an associative
  // one among them, treated as an integer.
  void ValidateAggregateOperands(const ModuleDecl* decl);

  void ValidateArrayPatternElemType(const ModuleDecl* decl);
  void WalkStmtsForArrayPatternElemType(const Stmt* s);
  void CheckArrayPatternElemTypeInAssign(const Stmt* s);
  void CheckArrayPatternElemTypeInInit(const ModuleItem* item);
  // §5.10, §5.11 and §10.9.1: the checks ArrayPatternCheck makes of a
  // module-level declaration's initializer, made of a pattern a procedure
  // assigns to one of the module's arrays and of one initializing an array a
  // block declares, packed (§7.4) or unpacked.
  void ValidateProceduralArrayPatterns(const ModuleDecl* decl);
  void WalkStmtsForProceduralArrayPattern(const Stmt* s);
  void CheckContinuousArrayPattern(const ModuleItem* item);
  // The module's variables and nets by name, each with its declaration, filled
  // by ValidateProceduralArrayPatterns for the module it walks; a pattern
  // assigned to one is checked against the dimensions it declares.
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
  // §6.22.2: whether two comparison operands that are unpacked arrays, each a
  // variable named whole or a slice of one, are of equivalent types; empty
  // where either is not such an operand. Defined in
  // elaborator_validate_operations_aggregate.cpp.
  bool ReportNonEquivalentArrayOperands(const Expr* expr);
  std::optional<bool> ArrayOperandsEquivalent(const Expr* lhs,
                                              const Expr* rhs) const;
  void WalkStmtsForAggregateCompare(const Stmt* s);

  void ValidateTypeRefComparisons(const ModuleDecl* decl);
  void WalkExprForTypeRefCompare(const Expr* expr);
  void ReportTypeRefOperand(const Expr* operand, const Expr* op);
  void CheckTypeRefCompareOp(const Expr* expr);
  void WalkStmtsForTypeRefCompare(const Stmt* s);

  // §6.23 with §13.4.1: the type a call of a function returns, which a type
  // reference to the call stands for without the call being made: a function
  // or imported DPI function (§35.5.4) the module, a package called through
  // `p::f()` (§26.3) or the compilation unit (§3.12.1) declares; nullopt for
  // any other expression, a method's call among them. The function is looked
  // for first among those a ConstFuncRegistryGuard has installed, which while
  // a queued generate construct is elaborated are its module's own,
  // func_decls_ holding by then the enclosing module's; then as
  // BareNamedFunction finds one, for a pass run once the guard is gone.
  std::optional<DataType> CalledFunctionType(const Expr* e) const;
  const ModuleItem* BareNamedFunction(std::string_view name) const;
  // §8.10 with §8.23: the return type of the static method a call written
  // through the class scope operator, `scoped` being `C::f` or `p::C::f`,
  // names; nothing where the scope reaches no class or the class no method.
  std::optional<DataType> ClassScopedCallType(const Expr* scoped) const;
  // §8.4 with §6.18: the class, and the specialization of it, a handle of
  // `type` refers to, each typedef naming it read through; nothing where
  // `type` names no class.
  std::optional<ClassSpecialization> ClassTypeOf(const DataType& type) const;
  // §8.5, §8.6 and §8.13: the type of the member `name` of `handle`'s class or
  // a class it extends, as a handle of that specialization reads it: a
  // property's declared type and unpacked dimensions, or a function's return
  // type. Nothing where the class has no such member, or one a parameterized
  // base class declares. Values fold against `constants`.
  std::optional<UnpackedArrayType> MemberTypeOf(
      const ClassSpecialization& handle, std::string_view name,
      const ScopeMap& constants) const;
  // The same member of the class a handle of `handle` refers to.
  std::optional<UnpackedArrayType> ClassMemberType(
      const DataType& handle, std::string_view name,
      const ScopeMap& constants) const;
  // §6.22.1: whether `a` and `b` match once each name they are written with is
  // read through, a class matching only the same specialization of itself
  // (SameSpecialization); nothing where a name resolves to no type.
  std::optional<bool> DataTypesMatch(const DataType& a, const DataType& b,
                                     const ScopeMap& constants) const;
  // §6.23 with §6.22.1: whether the types the type references `a` and `b`
  // stand for in `mod` match; nothing where either does not resolve.
  std::optional<bool> TypeRefsMatch(const Expr* a, const Expr* b,
                                    const RtlirModule* mod) const;
  // §6.23 with §7.4: resolve one type-reference operand of a comparison to
  // the type it denotes, an unpacked array's element type with its unpacked
  // dimensions: a value `mod` declares by the name written its declared type
  // and dimensions, a type as written, a call of a function its return type
  // (CalledFunctionType), and any other expression its self-determined type
  // (TypeRefArrayType); then each typedef name read through, an array
  // typedef's dimensions taken inside those already held (WithTypedefDims).
  // Returns nullopt when the operand is not a type reference or names a type
  // this pass cannot resolve, so the caller leaves it unfolded.
  std::optional<UnpackedArrayType> ResolveTypeRefOperandArray(
      const Expr* op, const RtlirModule* mod = nullptr) const;
  // The same operand before its typedef names are read through.
  std::optional<UnpackedArrayType> TypeRefOperandArray(
      const Expr* op, const RtlirModule* mod) const;
  // The operand ResolveTypeRefOperandArray gives, where it is of no unpacked
  // array type, which a data type alone carries.
  std::optional<DataType> ResolveTypeRefOperandType(
      const Expr* op, const RtlirModule* mod = nullptr) const;
  // The typedefs, their unpacked dimensions and the class names, which tell
  // the kind of array an unpacked dimension makes.
  TypeShapeTables ArrayTables() const;
  // Hands `use` the scope an expression in a type reference is typed in, each
  // name in it read as `mod` declares it where the reference stands.
  void InExprTypeScope(
      const RtlirModule& mod,
      const std::function<void(const ExprTypeScope&)>& use) const;
  // §6.23: the self-determined type of the expression `expr` a type reference
  // names (ExprSelfType), each name in it read as `mod` declares it where the
  // reference stands: a net, variable or port, a value parameter, or an
  // enumeration's named constant. Nothing where `mod` is null or the
  // expression is of no type a data type alone carries.
  std::optional<DataType> TypeRefExprType(const Expr* expr,
                                          const RtlirModule* mod) const;
  // §6.23 with §7.4: the same expression's type as ExprSelfArrayType gives
  // it, an unpacked array's included.
  std::optional<UnpackedArrayType> TypeRefArrayType(
      const Expr* expr, const RtlirModule* mod) const;
  // §6.23 with §7.4.4: the unpacked array type of the expression `ref` a
  // declaration's type reference names, an array typedef's dimensions taken
  // inside the value's, and its element type left as written; nothing where
  // the expression is no unpacked array. TypeRefUnpackedDims gives its
  // dimensions, which the declaration takes inside those it writes, and none
  // for any other expression.
  std::optional<UnpackedArrayType> TypeRefValueArray(
      const Expr* ref, const RtlirModule* mod) const;
  std::vector<Expr*> TypeRefUnpackedDims(const Expr* ref,
                                         const RtlirModule* mod) const;
  // §6.23: fold a type-reference equality/inequality/case-equality comparison
  // to a constant 0/1 using §6.22.1 type matching, its operands resolved in
  // `mod`. Returns nullopt when `expr` is not such a comparison or an operand
  // cannot be resolved.
  std::optional<int64_t> EvalConstTypeRefCompare(
      const Expr* expr, const RtlirModule* mod = nullptr) const;
  // What constant evaluation asks a comparison of two type references through
  // (TypedefRegistryGuard), answered as EvalConstTypeRefCompare answers it.
  TypeRefComparer type_ref_compare_ = [this](const Expr* expr,
                                             const RtlirModule* mod) {
    return EvalConstTypeRefCompare(expr, mod);
  };

  void ValidateTypeRefArgs(const ModuleDecl* decl);
  void WalkItemExprsForTypeRefArg(const ModuleItem* item);
  void WalkExprForTypeRefArg(const Expr* expr);
  void WalkStmtsForTypeRefArg(const Stmt* s);
  void CheckTypeRefArgInner(const Expr* inner, SourceLoc loc);
  bool TypeRefArgUsesDynamicElement(const Expr* e) const;
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
  // The variables the statements WalkStmtsForTypeRefArg is inside declare,
  // innermost last, each with whether a `.` after it selects a member of it
  // rather than naming a scope (NamesSelectableValue): a block's declaration
  // hides a module's of the same name for the rest of the block (§6.21).
  std::vector<std::pair<std::string_view, bool>> type_ref_block_vars_;
  // The module ValidateTypeRefArgs walks, whose ports and imports a name in a
  // type reference may name a value by (TypeRefModule); null outside it.
  const ModuleDecl* type_ref_module_ = nullptr;
  // §6.21 with §6.23: the TypeRefResolver for the declarations a procedure
  // writes, which resolves each through `resolve` with the names the
  // procedure declares ahead of it innermost in type_ref_block_vars_, so that
  // a `.` written after one selects a member of the procedure's value. It
  // answers the unpacked dimensions an array value of `mod` the reference
  // names gives the declaration (TypeRefUnpackedDims).
  TypeRefResolver ResolverAmongLocals(
      const RtlirModule* mod,
      std::function<void(DataType&, SourceLoc)> resolve);

  // §11.9: each tagged union expression against the type its context gives
  // it. Defined in elaborator_validate_operations_tagged.cpp.
  void ValidateTaggedUnionMembers(const ModuleDecl* decl);

  void ValidateRealOperatorRestrictions(const ModuleDecl* decl);
  void WalkExprForRealOps(const Expr* expr);
  void WalkStmtsForRealOps(const Stmt* s);
  void WalkItemsForRealOps(const std::vector<ModuleItem*>& items);
  void WalkSubroutineForRealOps(const ModuleItem* item);

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
  // §6.24.1: whether a size or a signing cast's operand is of a type that is
  // not integral. Defined in elaborator_validate_cast_operand.cpp.
  bool CastOperandIsNonIntegral(const Expr* operand) const;
  // The module's variables of an unpacked structure or union type, filled by
  // ValidateCastOperations for the module it walks.
  std::unordered_set<std::string_view> cast_unpacked_structs_;

  // §11.12: a let used before its declaration in its scope, and a let
  // referenced through a hierarchical name.
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
  // §10.10 with §7.10.4: whether `lhs` designates an unpacked array, so that
  // a `{...}` assigned to it is an unpacked array concatenation and not the
  // vector concatenation §11.4.12 keeps an unsized constant out of. A declared
  // array by its bare name, a property of an object through a handle (`h.q`,
  // §8.5 putting no restriction on a property's type) and a static property
  // through its class (`C::s`, §8.9) each answer yes.
  bool IsUnpackedArrayConcatTarget(const Expr* lhs) const;
  void WalkExprForUnsizedInConcat(const Expr* expr);
  void WalkStmtsForUnsizedInConcat(const Stmt* s);
  void WalkItemsOrExprForUnsizedInConcat(const Expr* e, bool is_array_concat);
  void CheckBlockVarInitUnsizedInConcat(const Stmt* s);
  // The variables the statements WalkStmtsForUnsizedInConcat or
  // WalkStmtsForProceduralArrayPattern is inside declare, innermost last, each
  // with whether it is an unpacked array: a block's declaration hides a
  // module's of the same name for the rest of the block (§6.21, §23.9), and
  // var_array_info_ knows the module's alone.
  std::vector<std::pair<std::string_view, bool>> block_decls_;
  // Whether the subroutine whose statements WalkStmtsForUnsizedInConcat walks
  // returns an unpacked array, whose returned braces are then an unpacked array
  // concatenation (§10.10).
  bool returns_unpacked_array_ = false;
  // §10.10.2: the declared type of each module variable, which tells whether
  // a member a target names is an unpacked array.
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
  // The declared type of each module variable, which tells whether a
  // streaming operand named by it is an unpacked tagged union (§11.4.14.1);
  // ValidateStreamingConcatContext fills it for the module it walks.
  std::unordered_map<std::string_view, const DataType*> stream_operand_types_;
  void CheckStreamingSourceTargetType(const Expr* lhs, const Expr* rhs);
  void CheckStreamingUnpackSourceType(const Expr* lhs, const Expr* rhs);

  // §6.24.3: enforces the destination/source/size constraints on a bit-stream
  // cast. Walks every expression in a module and rejects illegal forms before
  // the simulator ever sees them.
  void ValidateBitStreamCast(const ModuleDecl* decl);
  void WalkExprForBitStreamCast(const Expr* expr);
  void WalkStmtsForBitStreamCast(const Stmt* s);
  void CheckBitStreamCastExpr(const Expr* expr);
  // The declared type of each module variable without an unpacked dimension,
  // which says whether a bit-stream cast's operand is an unpacked structure;
  // ValidateBitStreamCast fills it for the module it walks.
  std::unordered_map<std::string_view, const DataType*> bit_stream_var_types_;
  Arena& arena_;
  DiagEngine& diag_;
  CompilationUnit* unit_;
};

}  // namespace delta
