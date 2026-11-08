#pragma once

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast_type.h"
#include "simulator/scheduler.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

namespace delta {

struct ArrayInfo;
struct Expr;
struct Stmt;
struct StructTypeInfo;
struct Variable;
struct Net;
struct ClassObject;
struct ClassTypeInfo;
struct QueueObject;
class SimContext;
class Arena;

StmtResult ExecBlockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena);

bool TryDispatchSpecialBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                      Arena& arena);
void ApplyGenericBlockingAssign(const Stmt* stmt, Logic4Vec rhs_val,
                                SimContext& ctx, Arena& arena);
StmtResult ExecNonblockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);
StmtResult ExecVarDeclImpl(const Stmt* stmt, SimContext& ctx, Arena& arena);
StmtResult ExecBlockItemDeclImpl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena);
StmtResult ExecForceOrAssignImpl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena);
StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);
void ReleaseForcedTarget(Variable* var, Net* net, SimContext& ctx,
                         Arena& arena);

void PerformBlockingAssign(const Expr* lhs, const Logic4Vec& rhs_val,
                           SimContext& ctx, Arena& arena);

struct NbaUpdateTag {
  std::string_view key;
  std::string_view tag;
  bool Carries() const { return !tag.empty(); }
};

struct NbaSample {
  Logic4Vec value;
  NbaUpdateTag tag;
};

NbaSample SampleNonblockingRhs(const Stmt* stmt, SimContext& ctx, Arena& arena);

void ScheduleNonblockingAssign(const Stmt* stmt, const NbaSample& sample,
                               uint64_t delay_ticks, SimContext& ctx,
                               Arena& arena);

Scheduler::NbaCapture* CaptureNonblockingAssign(const Stmt* stmt,
                                                const NbaSample& sample,
                                                SimContext& ctx, Arena& arena);

void ReleaseNbaUpdates(const Scheduler::NbaCapture& updates, SimContext& ctx);

void BuildLhsName(const Expr* expr, std::string& out);

struct UnionTagMismatch {
  std::string union_name;
  std::string member;
  std::string tag;
  bool found = false;
};
UnionTagMismatch FindUnionTagMismatch(std::string_view base_name,
                                      const StructTypeInfo* info,
                                      std::string_view field_name,
                                      SimContext& ctx);

struct MemberLayout {
  const StructTypeInfo* layout = nullptr;
  std::string tag;
};
MemberLayout ResolveMemberLayout(std::string_view base_name,
                                 const StructTypeInfo* info,
                                 std::string_view field_name, SimContext& ctx);
Variable* TryResolveArrayElement(const Expr* lhs, SimContext& ctx);
bool BuildCompoundLhsName(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string& name);
std::string_view CompoundRootName(const Expr* e);

Variable* TryResolveCompoundElementBase(const Expr* lhs, SimContext& ctx,
                                        Arena& arena);

Variable* TryResolveCompoundElement(const Expr* lhs, SimContext& ctx,
                                    Arena& arena,
                                    bool* absent_element = nullptr);
Variable* ResolveLhsVariable(const Expr* lhs, SimContext& ctx);

struct PropertyFieldWindow {
  std::string_view property;
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  uint32_t total_width = 0;
  DataTypeKind member_kind = DataTypeKind::kImplicit;
  bool valid = false;
};

PropertyFieldWindow ResolveClassPropertyField(const ClassTypeInfo* type,
                                              std::string_view path,
                                              SimContext& ctx);

struct FieldTarget {
  enum class Kind : uint8_t {
    kNone,
    kNoOp,
    kBits,
    kVariable,
    kProperty,
    kPropertyBits,
    kStatic,
  };
  Kind kind = Kind::kNone;

  Variable* var = nullptr;
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  DataTypeKind member_kind = DataTypeKind::kImplicit;
  uint32_t holder_width = 0;

  ClassObject* obj = nullptr;
  const ClassTypeInfo* type = nullptr;
  Variable* notify = nullptr;

  Logic4Vec* slot = nullptr;

  std::string field;

  bool HasDeposit() const { return kind != Kind::kNone && kind != Kind::kNoOp; }
};

FieldTarget ResolveFieldTarget(const Expr* lhs, SimContext& ctx);

FieldTarget ResolveBarePropertyTarget(std::string_view name, SimContext& ctx);

void WriteResolvedField(const FieldTarget& target, const Logic4Vec& rhs_val,
                        SimContext& ctx, Arena& arena);

bool TryWriteClassPropertyBits(const Expr* lhs, const Logic4Vec& rhs_val,
                               SimContext& ctx, Arena& arena);

std::optional<PackedRange> PropertyDeclaredRange(const ClassTypeInfo* type,
                                                 std::string_view field,
                                                 uint32_t width,
                                                 SimContext& ctx, Arena& arena);

std::optional<PackedRange> CalledFunctionRange(const Expr* base, uint32_t width,
                                               SimContext& ctx, Arena& arena);

std::optional<PackedLevel> CastTypeLevel(const Expr* base, uint32_t width,
                                         SimContext& ctx, Arena& arena);

bool WriteStructField(const Expr* lhs, const Logic4Vec& rhs_val,
                      SimContext& ctx, uint32_t* written_width = nullptr);

uint32_t FieldLhsWidth(const Expr* lhs, SimContext& ctx);

size_t SelectDepthWithin(const Variable& var, const Expr* sel, SimContext& ctx,
                         Arena& arena);

PartSelectBits SelectStorageBits(const Variable& var, const Expr* sel,
                                 SimContext& ctx, Arena& arena);

void WriteBitSelect(Variable* var, const Expr* lhs, const Logic4Vec& rhs_val,
                    SimContext& ctx, Arena& arena);
Logic4Vec ResizeToWidth(Logic4Vec val, uint32_t target_width, Arena& arena);
Logic4Vec SizedForQueueElement(const QueueObject& q, Logic4Vec val,
                               Arena& arena);

void SizeAndOwnQueueElements(const QueueObject& q,
                             std::vector<Logic4Vec>& elems, Arena& arena);

Logic4Vec CoerceToPropertyType(const ClassTypeInfo* type, std::string_view name,
                               Logic4Vec val, Arena& arena);
bool TryArrayBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);
bool TryArrayAggregateAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);
bool TryFillArrayFromValue(const Stmt* stmt, const ArrayInfo& dst,
                           SimContext& ctx, Arena& arena);
int64_t QueueElementIndex(const Expr* index, QueueObject* q, SimContext& ctx,
                          Arena& arena, bool* has_xz);

bool TryAssocIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena);
bool TryQueueIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena);
bool TryQueueBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

bool TryClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
