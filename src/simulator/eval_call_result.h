#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "common/types.h"

namespace delta {

struct Expr;
struct Stmt;
class SimContext;
class Arena;

struct StructTypeInfo;
struct ReturnedAggregate {
  std::vector<Logic4Vec> elements;
  uint32_t elem_width = 32;
  uint32_t lo = 0;
  bool is_descending = false;
  bool is_4state = true;
  const StructTypeInfo* elem_layout = nullptr;
};

class FunctionBodyResultScope {
 public:
  explicit FunctionBodyResultScope(SimContext& ctx);
  ~FunctionBodyResultScope();
  FunctionBodyResultScope(const FunctionBodyResultScope&) = delete;
  FunctionBodyResultScope& operator=(const FunctionBodyResultScope&) = delete;

 private:
  SimContext& ctx_;
  const Expr* set_aside_base_ = nullptr;
  Logic4Vec set_aside_value_;
  std::optional<ReturnedAggregate> set_aside_aggregate_;
};

class CallResultReceiverScope {
 public:
  CallResultReceiverScope(const Expr* call, SimContext& ctx, Arena& arena);
  ~CallResultReceiverScope();
  CallResultReceiverScope(const CallResultReceiverScope&) = delete;
  CallResultReceiverScope& operator=(const CallResultReceiverScope&) = delete;

  bool Holds() const { return base_ != nullptr; }
  void Release();

 private:
  const Expr* base_ = nullptr;
  const Expr* outer_base_ = nullptr;
  std::optional<ReturnedAggregate> outer_aggregate_;
  SimContext& ctx_;
};

bool StartsAtHeldCall(const Expr* side);

bool SelectsNamedMember(const Expr* expr);

void RecordReturnedAggregate(const Expr* returned, SimContext& ctx,
                             Arena& arena);

Logic4Vec EvalWithReturnedAggregate(const Expr* expr, SimContext& ctx,
                                    Arena& arena,
                                    std::optional<ReturnedAggregate>& returned);

void RecordReturnedTag(const Expr* returned);

void RecordReturnedVariableTag(const Expr* returned, SimContext& ctx);

Logic4Vec EvalWithReturnedTag(const Expr* expr, SimContext& ctx, Arena& arena,
                              std::string& tag, uint32_t context_width = 0);

Logic4Vec EvalRhsCarryingReturnedTag(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);

const Expr* TaggedElementTarget(const Stmt* stmt);

bool TaggedUnionMemberKey(const Expr* lhs, SimContext& ctx, std::string& key);

bool ElementTagKey(const Expr* select, SimContext& ctx, Arena& arena,
                   std::string& key);

bool TryCallResultArrayAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

Logic4Vec ElementOfReturnedAggregate(const ReturnedAggregate& returned,
                                     int64_t idx, Arena& arena);

bool TryEvalCallResultMember(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

bool TryEvalCallResultMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

}  // namespace delta
