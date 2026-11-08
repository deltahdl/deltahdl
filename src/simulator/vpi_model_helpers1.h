#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "simulator/vpi_object.h"

namespace delta {

struct Expr;

struct VpiTypeDeclEntry {
  std::string name;
  bool user_defined = false;
  bool declared_in_instance = false;
};

std::vector<const VpiTypeDeclEntry*> VpiInstanceTypedefs(
    const std::vector<VpiTypeDeclEntry>& entries);

std::vector<const VpiTypeDeclEntry*> VpiInstanceNetTypedefs(
    const std::vector<VpiTypeDeclEntry>& entries);

bool VpiIsInstanceType(int type);

VpiHandle VpiInstanceOf(VpiHandle obj);

VpiHandle VpiModuleOf(VpiHandle obj);

int VpiMemoryIterationItemType();

std::string VpiCompilationUnitFullName(std::string_view object_path);

std::string VpiPackageFullName(std::string_view package_name);

std::string VpiPackageMemberFullName(std::string_view package_name,
                                     std::string_view member_path);

std::string_view VpiNameSeparator(bool package_or_class_defn_boundary);

bool VpiHandleByNameAccessible(const VpiObject& obj);

int VpiSmallestTimePrecision(const std::vector<int>& precisions);

bool VpiIsAssertionType(int type);

bool VpiIsConstraintItemType(int type);

VpiHandle VpiConstraintConditionExpr(VpiHandle container);

void VpiCollectConstraintExprs(VpiObject* ref, VpiObject* iter);

bool VpiIsConstraintExprContainerType(int type);

bool VpiIsClassMethodType(int type);

bool VpiIsClassMemberValueType(int type);

VpiHandle VpiAssertionClockingBlock(VpiHandle assertion);

bool VpiIsConcurrentAssertionType(int type);

bool VpiIsConcurrentAssertionPropertyType(int type);

VpiHandle VpiConcurrentAssertionProperty(VpiHandle assertion);

VpiHandle VpiConcurrentAssertionClockingEvent(VpiHandle assertion);

bool VpiConcurrentAssertionHasPassStmt(int type);

bool VpiConcurrentAssertionHasElseStmt(int type);

VpiHandle VpiConcurrentAssertionStmt(VpiHandle assertion);

VpiHandle VpiConcurrentAssertionElseStmt(VpiHandle assertion);

bool VpiConcurrentAssertionIsSimulated(int type);

bool VpiIsImmediateAssertionType(int type);

bool VpiImmediateAssertionHasElseStmt(int type);

VpiHandle VpiImmediateAssertionExpr(VpiHandle assertion);

VpiHandle VpiImmediateAssertionStmt(VpiHandle assertion);

VpiHandle VpiImmediateAssertionElseStmt(VpiHandle assertion);

bool VpiIsSequenceExprType(int type);

bool VpiIsSequenceExprOpType(int op);

std::vector<VpiHandle> VpiUnaryCycleDelayOperands(VpiHandle sequence,
                                                  VpiHandle left_range,
                                                  VpiHandle right_range);

std::vector<VpiHandle> VpiCycleDelayOperands(VpiHandle lhs_sequence,
                                             VpiHandle rhs_sequence,
                                             VpiHandle left_range,
                                             VpiHandle right_range);

std::vector<VpiHandle> VpiRepeatOperands(VpiHandle sequence,
                                         VpiHandle left_bound,
                                         VpiHandle right_bound);

struct VpiSequenceFormal {
  VpiHandle default_value = nullptr;
};

std::vector<VpiHandle> VpiSequenceInstArguments(
    const std::vector<VpiSequenceFormal>& formals,
    const std::vector<VpiHandle>& provided);

bool VpiIsSequenceArgumentType(int type);

VpiHandle VpiSequenceInstDecl(VpiHandle sequence_inst);

bool VpiIsMatchItemType(int type);

std::vector<VpiHandle> VpiExprMatchItems(VpiHandle expr);

bool VpiIsPropertyExprType(int type);

bool VpiIsPropertyExprOpType(int op);

std::vector<VpiHandle> VpiNexttimeOperands(VpiHandle property,
                                           VpiHandle constant,
                                           bool constant_differs_from_one);

std::vector<VpiHandle> VpiAlwaysEventuallyOperands(VpiHandle property,
                                                   VpiHandle left_range,
                                                   VpiHandle right_range);

bool VpiIsOpStrongValidOp(int op);

bool VpiIsPropertyVariableValueAccessible();

std::vector<VpiHandle> VpiCaseItemConditions(VpiHandle case_item);

bool VpiIsPatternType(int type);

VpiHandle VpiPatternOf(VpiHandle pattern);

VpiHandle VpiCaseConditionExpr(VpiHandle case_stmt);

bool VpiIsCaseItemConditionType(int type);

std::vector<VpiHandle> VpiCaseItemMatchExprs(VpiHandle case_item);

bool VpiIsDisableConditionType(int type);

VpiHandle VpiClockingEvent(VpiHandle obj);

VpiHandle VpiPropertyExprChild(VpiHandle obj);

VpiHandle VpiCasePropertyConditionExpr(VpiHandle case_property);

std::vector<VpiHandle> VpiPropFormals(VpiHandle property_decl);

int VpiPropFormalDirection(bool is_local_variable_argument);

VpiHandle VpiPropFormalTypespec(VpiHandle formal);

VpiHandle VpiPropFormalInitExpr(VpiHandle formal);

struct VpiPropertyFormal {
  VpiHandle default_value = nullptr;
};

std::vector<VpiHandle> VpiPropertyInstArguments(
    const std::vector<VpiPropertyFormal>& formals,
    const std::vector<VpiHandle>& provided);

bool VpiIsPropertyArgumentType(int type);

VpiHandle VpiPropertyInstDecl(VpiHandle property_inst);

std::vector<VpiHandle> VpiMulticlockSequenceClockedSeqs(
    VpiHandle multiclock_seq);

VpiHandle VpiClockedSeqSequenceExpr(VpiHandle clocked_seq);

std::vector<VpiHandle> VpiSeqFormals(VpiHandle sequence_decl);

VpiHandle VpiSeqDeclBodyExpr(VpiHandle sequence_decl);

int VpiSeqFormalDirection(bool is_local_variable_argument, int local_direction);

VpiHandle VpiSeqFormalTypespec(VpiHandle formal);

VpiHandle VpiSeqFormalInitExpr(VpiHandle formal);

struct VpiLetFormal {
  VpiHandle default_value = nullptr;
};

VpiHandle VpiLetFormalDefault(VpiHandle formal);

std::vector<VpiHandle> VpiLetExprArguments(
    const std::vector<VpiLetFormal>& formals,
    const std::vector<VpiHandle>& provided);

bool VpiIsTfCallType(int type);

bool VpiIsMethodCallType(int type);

bool VpiIsTfCallArgumentType(int type);

void VpiMakeEmptyArgument(VpiHandle arg);

void VpiMakeNullArgument(VpiHandle arg);

bool VpiSimpleExprVectorUseAccessesUse(bool references_vector,
                                       bool references_part_select_of_vector,
                                       bool references_bit_select_of_vector);

bool VpiSimpleExprBitSelectUseAccessesUse(
    bool references_this_bit, bool references_parent_vector,
    bool references_part_select_containing_bit);

bool VpiSimpleExprBitSelectConstantSelect(bool all_indices_constant,
                                          bool parent_constant_select);

bool VpiBitSelectConstantSelectOf(VpiHandle select);

bool VpiIsDynamicPrefixSourceType(int type);

bool VpiObjectHasActual(int actual_origin, bool has_current_actual);

bool VpiIsExprType(int type);

bool VpiExpressionHasSideEffects(const VpiObject* obj);

bool VpiSourceExprHasSideEffects(const Expr* expr);

bool VpiObjectCarriesSourceDelay(int type);

VpiHandle VpiSourceDelayExpr(VpiHandle obj);

bool VpiSourceDelayExprIsListOp(VpiHandle expr);

bool VpiIsAtomicStmtType(int type);

int VpiAssignmentOpType(std::string_view assign_operator);

bool VpiIsAlwaysType(int always_type);

std::vector<VpiHandle> VpiOperationOperands(VpiHandle operation);

bool VpiIsProcessType(int type);

VpiHandle VpiEventControlStmt(VpiHandle event_control);

VpiHandle VpiEventControlConditionExpr(VpiHandle event_control);

VpiHandle VpiDelayControlStmt(VpiHandle delay_control);

VpiHandle VpiDelayControlDelayExpr(VpiHandle delay_control);

bool VpiIsWhileOrRepeatType(int type);

VpiHandle VpiLoopConditionExpr(VpiHandle loop);

VpiHandle VpiDoWhileConditionExpr(VpiHandle loop);

VpiHandle VpiReturnConditionExpr(VpiHandle return_stmt);

bool VpiIsWaitType(int type);

bool VpiIsDisableType(int type);

VpiHandle VpiWaitConditionExpr(VpiHandle wait);

VpiHandle VpiOrderedWaitElseStmt(VpiHandle wait);

bool VpiIsContAssignKind(int type);

VpiHandle VpiRepeatControlExpr(VpiHandle repeat_control);

bool VpiIsDisableTargetType(int type);

VpiHandle VpiDisableExpr(VpiHandle disable);

bool VpiIsIfOrIfElseType(int type);

VpiHandle VpiIfConditionExpr(VpiHandle if_stmt);

VpiHandle VpiIfElseStmt(VpiHandle if_stmt);

VpiHandle VpiForConditionExpr(VpiHandle for_stmt);

bool VpiIsBlockItemDeclType(int type);

bool VpiBlockScopeIsScope(VpiHandle block);

bool VpiIsLoopControlVarType(int type);

bool VpiIsJoinType(int join_type);

bool VpiIsTaskFuncType(int type);

VpiHandle VpiTaskFuncStmt(VpiHandle task_func);

std::vector<VpiHandle> VpiMultiConcatOperands(
    VpiHandle multiplier, const std::vector<VpiHandle>& concat_exprs);

std::vector<VpiHandle> VpiMultiAssignmentPatternOperands(
    VpiHandle multiplier, const std::vector<VpiHandle>& pattern_exprs);

std::vector<VpiHandle> VpiCastOpOperands(VpiHandle cast_expr);

struct VpiAssignmentPatternEntry {
  int position = 0;
  VpiHandle value = nullptr;
};

std::vector<VpiHandle> VpiAssignmentPatternPositionalOperands(
    int slots, const std::vector<VpiAssignmentPatternEntry>& positioned,
    VpiHandle default_value);

bool VpiTypespecAlwaysAvailable(int op_type, bool is_simple_expr,
                                bool assignment_pattern_has_type_prefix);

struct VpiPartSelectConstantSelectQuery {
  bool parent_constant_select = false;
  bool parent_array_has_static_bounds = false;
  bool all_range_exprs_constant = false;
};
bool VpiPartSelectConstantSelect(const VpiPartSelectConstantSelectQuery& query);

std::string VpiPartSelectParentExpr(std::string_view select_expr);

std::string VpiDecompileJoin(const std::vector<std::string>& pieces);

std::string VpiDecompileParenthesize(std::string_view inner);

}  // namespace delta
