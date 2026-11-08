#pragma once

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "lexer/token.h"

namespace delta {

struct ArrayInfo;
struct AssocArraySpec;
struct DataType;
struct Expr;
struct Stmt;
struct StructFieldInfo;
struct StructTypeInfo;
struct Variable;
class SimContext;
class Arena;
enum class DataTypeKind : uint8_t;

void CoerceTo2State(Logic4Vec& v);

void RecordPropertyTags(const Stmt* stmt, SimContext& ctx, Arena& arena);

Logic4Vec OwnRhsWords(const Logic4Vec& val, Arena& arena);

Logic4Vec ConvertRealOnAssign(Logic4Vec rhs_val, const Expr* lhs,
                              const Variable& var, SimContext& ctx,
                              Arena& arena);

Logic4Vec ConvertRealForKnownLhs(Logic4Vec rhs_val, bool lhs_is_real,
                                 uint32_t target_width, Arena& arena);

bool IsRealMemberKind(DataTypeKind kind);

void ApplyCompoundAssignOp(const Stmt* stmt, SimContext& ctx, Arena& arena);

void AssignToScalarLhs(const Stmt* stmt, Logic4Vec rhs_val, SimContext& ctx,
                       Arena& arena);

Logic4Vec EvalWeakReferenceNew(const Expr* call, SimContext& ctx, Arena& arena);

void WriteVar(Variable* var, const Logic4Vec& val, Arena& arena);

void SnapshotSelectIndices(const Expr* lhs, SimContext& ctx, Arena& arena);
void ClearSelectIndices(const Expr* lhs, SimContext& ctx);

using LhsIndexSnapshots = std::vector<std::pair<const Expr*, Logic4Snapshot>>;
LhsIndexSnapshots CollectLhsIndexSnapshots(const Expr* lhs, SimContext& ctx,
                                           Arena& arena);
void InstallLhsIndexSnapshots(const LhsIndexSnapshots& snaps, SimContext& ctx);
void ClearLhsIndexSnapshots(const LhsIndexSnapshots& snaps, SimContext& ctx);

class LhsIndexPin {
 public:
  LhsIndexPin(const Expr* lhs, SimContext& ctx, Arena& arena);
  ~LhsIndexPin();
  LhsIndexPin(const LhsIndexPin&) = delete;
  LhsIndexPin& operator=(const LhsIndexPin&) = delete;
  LhsIndexPin(LhsIndexPin&&) = delete;
  LhsIndexPin& operator=(LhsIndexPin&&) = delete;

 private:
  SimContext* ctx_;
  LhsIndexSnapshots snaps_;
};

void CreateDeclAggregate(const Stmt* stmt, uint32_t elem_width, SimContext& ctx,
                         Arena& arena);
void AssignDeclAggregateInit(const Stmt* stmt, SimContext& ctx, Arena& arena);
const Stmt* DeclParameterTypedByValue(const Stmt* stmt, SimContext& ctx,
                                      Arena& arena);
void CreateBlockArrayElements(const Stmt* stmt, uint32_t elem_width,
                              SimContext& ctx, Arena& arena);

void RecordClassParamActuals(std::string_view var_name,
                             std::string_view class_name,
                             const std::vector<DataType>& type_params,
                             SimContext& ctx);

bool IsAssocIndexDim(const Expr* dim, SimContext& ctx);

DataType AssocIndexType(const Expr* dim, SimContext& ctx);

bool IsStringIndexDim(const Expr* dim, SimContext& ctx);

AssocArraySpec AssocIndexSpec(const Expr* dim, bool elem_4state,
                              SimContext& ctx);

AssocArraySpec AssocIndexSpecOfType(const DataType& index_type,
                                    bool elem_4state, SimContext& ctx);

bool TrySelectBlockingAssign(const Expr* lhs, Logic4Vec& rhs_val,
                             SimContext& ctx, Arena& arena);

bool IsConcatLhs(const Expr* lhs);

const Expr* UnwrapTypedPattern(const Expr* expr);

const Expr* UnpackedArrayTypedPattern(const Expr* expr, SimContext& ctx);

const Expr* TypedUnpackedArrayPattern(const Expr* expr, SimContext& ctx);

void CollectFixedArrayElements(std::string_view name, const ArrayInfo& ai,
                               SimContext& ctx, std::vector<Logic4Vec>& out);

std::vector<Logic4Vec> CollectConcatElements(const Expr* rhs, SimContext& ctx,
                                             Arena& arena);

void DistributeConcatToArray(std::string_view arr_name, const ArrayInfo& info,
                             const Expr* rhs, SimContext& ctx, Arena& arena);

struct SubarrayRef {
  const ArrayInfo& info;
  const std::string& prefix;
  size_t dim;
};
void DistributeConcatToSubarray(const SubarrayRef& sub, const Expr* concat,
                                SimContext& ctx, Arena& arena);

size_t StoreSubarrayElements(const SubarrayRef& sub,
                             const std::vector<Logic4Vec>& elems,
                             SimContext& ctx, Arena& arena);

bool CollectArrayItemElements(const Expr* item, SimContext& ctx, Arena& arena,
                              std::vector<Logic4Vec>& out);

bool CopyArrayItemToSubarray(const SubarrayRef& sub, const Expr* item,
                             SimContext& ctx, Arena& arena);

uint32_t SelectExprWidth(const Variable& var, const Expr* sel, SimContext& ctx,
                         Arena& arena);

uint32_t ConcatLhsElemWidth(const Expr* e, SimContext& ctx, Arena& arena);

struct SelectedElementMember {
  const StructTypeInfo* layout = nullptr;
  const StructFieldInfo* field = nullptr;
  uint32_t offset = 0;
};
SelectedElementMember ResolveSelectedElementMember(const Expr* lhs,
                                                   SimContext& ctx);

bool ConcatLhsElemHasWritableBits(const Expr* e, const Variable& var,
                                  SimContext& ctx, Arena& arena);

void ReportZeroWidthPartSelect(const Expr* sel, SimContext& ctx, Arena& arena);

bool TryUnpackConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                        SimContext& ctx, Arena& arena);

uint32_t LhsContextWidth(const Expr* lhs, SimContext& ctx, Arena& arena);

void CopyTagChain(std::string src, std::string dst,
                  const StructTypeInfo* layout, SimContext& ctx, Arena& arena);

bool TryConditionalCollectionAssign(const Stmt* stmt, SimContext& ctx,
                                    Arena& arena);
bool TryConditionalArrayAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

uint32_t CompoundOperandWidth(TokenKind base_op, const Expr* lhs,
                              SimContext& ctx, Arena& arena);

std::optional<Logic4Vec> EvalTaggedForLayout(const Expr* expr,
                                             const StructTypeInfo& layout,
                                             SimContext& ctx, Arena& arena);
Logic4Vec EvalTaggedOrPlain(const Expr* init, const StructTypeInfo* layout,
                            SimContext& ctx, Arena& arena,
                            uint32_t context_width = 0);

Logic4Vec EvalRhsWithStructContext(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena);

std::string LhsIdentName(const Expr* lhs);

bool TryUnpackedSliceAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

bool TrySubarrayAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

void DistributePatternToArray(std::string_view arr_name, const ArrayInfo& info,
                              const Expr* rhs, SimContext& ctx, Arena& arena);

bool TryAssocCopyAssign(const Stmt* stmt, SimContext& ctx);
bool TryAssocMapAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);
bool TryAssocLiteralAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

bool TryTypedClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);
bool TryMemberClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);
bool TryStructMemberClassNewAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena);

Logic4Vec ApplyStreamPackToTargetWidening(const Stmt* stmt, Logic4Vec rhs_val,
                                          SimContext& ctx, Arena& arena);
Logic4Vec WidenStreamPackToFixedTarget(Logic4Vec stream, uint32_t target_width,
                                       SourceLoc loc, SimContext& ctx,
                                       Arena& arena);
Logic4Vec RightPadStreamToWidth(const Logic4Vec& stream, uint32_t stream_w,
                                uint32_t total_w, Arena& arena);

bool TryUnpackStreamIntoProperties(const Expr* lhs, const Logic4Vec& rhs_val,
                                   SimContext& ctx, Arena& arena);
void UnpackStreamingConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena);

bool TryStreamingConcatToQueueTarget(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);

struct ArrayGeom {
  uint32_t size;
  uint32_t lo;
};

struct StreamSliceRange {
  uint32_t start;
  uint32_t count;
};

bool ResolveWithRange(const Expr* with_expr, SimContext& ctx, Arena& arena,
                      ArrayGeom geom, StreamSliceRange& out_range);

uint32_t PatternKeyIndex(const Expr* key, SimContext& ctx, Arena& arena);

struct ArrayPatternTarget {
  const ArrayInfo& info;
  const StructTypeInfo* layout;
};

Logic4Vec PatternItemAt(const Expr* rhs, const ArrayPatternTarget& target,
                        uint32_t i, SimContext& ctx, Arena& arena);

void CollectQueueElements(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::vector<Logic4Vec>& out);

void WritePartSelect(Variable* var, const PartSelectBits& bits,
                     const Logic4Vec& rhs_val, Arena& arena);

std::vector<std::string> MultiDimLeafSuffixes(const ArrayInfo& info);

void CopyArrayElements(std::string_view dst_name, const ArrayInfo& dst,
                       std::string_view src_name, const ArrayInfo& src,
                       SimContext& ctx);

}  // namespace delta
