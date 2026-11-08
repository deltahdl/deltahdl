#pragma once

#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "simulator/assoc_index.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

struct StructFieldInfo;

class ConstraintEvalScope {
 public:
  ConstraintEvalScope(ClassObject* obj, SimContext& ctx)
      : ctx_(ctx), bound_(obj != nullptr && obj->type != nullptr) {
    if (!bound_) return;
    caller_this_ = ctx_.SetConstraintCallerThis(ctx_.CurrentThis());
    ctx_.PushThis(obj);
    ctx_.PushMethodClass(obj->type);
  }

  ~ConstraintEvalScope() {
    if (!bound_) return;
    ctx_.PopMethodClass();
    ctx_.PopThis();
    ctx_.SetConstraintCallerThis(caller_this_);
  }

  ConstraintEvalScope(const ConstraintEvalScope&) = delete;
  ConstraintEvalScope& operator=(const ConstraintEvalScope&) = delete;
  ConstraintEvalScope(ConstraintEvalScope&&) = delete;
  ConstraintEvalScope& operator=(ConstraintEvalScope&&) = delete;

 private:
  SimContext& ctx_;
  bool bound_;
  ClassObject* caller_this_ = nullptr;
};

struct RandInfo {
  std::string name;
  const ClassTypeInfo* level = nullptr;
  bool is_static = false;
  RandVariable var;

  std::string member;
  ClassObject* owner = nullptr;

  std::string array_base;
  int64_t array_index = 0;
  bool in_queue = false;
  bool in_assoc = false;
  AssocIndex int_key;
  std::string str_key;
  std::string struct_base;
  uint32_t struct_offset = 0;
  const StructFieldInfo* dyn_field = nullptr;
};

bool AddRandStructMembers(const ClassMember* m, const ClassTypeInfo* level,
                          SimContext& ctx, std::vector<RandInfo>& out);

struct JointVarScope;

struct RandomizeCtx {
  ClassObject* obj;
  SimContext& ctx;
  Arena& arena;
  const ConstraintSolver* solver = nullptr;
  std::vector<std::unique_ptr<ConstraintExpr>> soft_inners = {};
  std::unordered_map<std::string, Variable*> trial_locals = {};
  const ClassMember* inline_block = nullptr;
  std::string solver_prefix = {};
  JointVarScope* joint = nullptr;
  std::string inline_receiver = {};
};

void AddRandStructDynamicElements(const ClassMember* m,
                                  const ClassTypeInfo* level,
                                  std::vector<RandInfo>& out, RandomizeCtx& rc);

struct JointObject {
  ClassObject* obj;
  std::string prefix;
};

struct JointVarScope {
  ClassObject* owner = nullptr;
  std::vector<RandInfo> rands = {};
  std::unordered_set<std::string> names = {};
};

bool IsJointVariable(const std::string& name, const RandomizeCtx& rc);
std::string JointVariableName(const Expr* e, const RandomizeCtx& rc);
bool TryJointRelation(const Expr* rel, std::vector<RandInfo>& rands,
                      RandomizeCtx& rc, bool fold, ConstraintExpr& out);

const Expr* PackedMembersAsSelects(const Expr* rel,
                                   std::vector<RandInfo>& rands,
                                   RandomizeCtx& rc);

using ExprRewrite = std::function<Expr*(const Expr*)>;
Expr* RewriteExpr(const Expr* e, const ExprRewrite& rewrite, Arena& arena);
Expr* IdentifierExpr(std::string_view text, const Expr* like, Arena& arena);

RandInfo* FindRand(std::vector<RandInfo>& rands, std::string_view name);
bool RefsRandVar(const Expr* e, std::vector<RandInfo>& rands);
bool AnyRefsRandVar(const std::vector<Expr*>& list,
                    std::vector<RandInfo>& rands);
bool TrySetMembershipConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                                RandomizeCtx& rc, ConstraintExpr& out);
bool TryImplicationConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                              RandomizeCtx& rc, ConstraintExpr& out);
void AttachConstraintGuard(const Expr* rel,
                           const std::function<bool(const Expr*)>& refs_rand,
                           ClassObject* owner, RandomizeCtx& rc,
                           ConstraintExpr& out);
ConstraintExpr SoftImplication(const Expr* rel, std::vector<RandInfo>& rands,
                               RandomizeCtx& rc);
bool EvalCustomRelation(const Expr* rel, const std::vector<std::string>& names,
                        RandomizeCtx& rc,
                        const std::unordered_map<std::string, int64_t>& vals);
int64_t EvalCustomValue(const Expr* e, const std::vector<std::string>& names,
                        RandomizeCtx& rc,
                        const std::unordered_map<std::string, int64_t>& vals);
bool RefsNamedRandVar(const Expr* e, std::string_view name);
void SetLocalWords(Logic4Vec& value, int64_t v);
int64_t HeldToVariable(int64_t v, const std::string& name, RandomizeCtx& rc);
ConstraintExpr MakeCustomConstraint(const Expr* rel,
                                    std::vector<RandInfo>& rands,
                                    RandomizeCtx& rc);
bool TryArrayReductionConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                                 RandomizeCtx& rc, ConstraintExpr& out);
void AddForeachConstraints(const ClassMember* m, std::vector<RandInfo>& rands,
                           RandomizeCtx& rc, ConstraintBlock& block);
bool TryConjunctionConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                              RandomizeCtx& rc, ConstraintExpr& out, bool fold);
void CollectRandVariables(const ClassTypeInfo* type, SimContext& ctx,
                          std::vector<RandInfo>& out);
RandInfo BuildRandMember(const ClassMember* m, const ClassTypeInfo* level,
                         SimContext& ctx);
void AddDynamicArrayVariables(std::vector<RandInfo>& rands, RandomizeCtx& rc);
const Expr* ResolveArraySizes(const Expr* rel, RandomizeCtx& rc);
bool ComparisonKind(TokenKind op, ConstraintKind& out);
void FoldBound(RandInfo& ri, ConstraintKind kind, int64_t c);
void FoldRealBound(RandInfo& ri, ConstraintKind kind, double c);
void FoldComparison(std::vector<RandInfo>& rands, std::string_view name,
                    ConstraintKind kind, const Logic4Vec& cv, int64_t c);
Logic4Vec SolvedValue(const RandInfo& ri, const ConstraintSolver& solver,
                      const std::string& prefix, Arena& arena);
bool IsObjectConstraintActive(const ClassObject* obj, std::string_view name);
const ClassTypeInfo* StaticRandOwner(const ClassObject* obj,
                                     std::string_view name);
bool IsObjectRandActive(const ClassObject* obj, std::string_view name);
void InvokePostRandomize(ClassObject* obj, const Expr* expr, SimContext& ctx,
                         Arena& arena);
void CollectRandObjectMembers(const ClassTypeInfo* type, SimContext& ctx,
                              std::vector<std::string>& out);

TokenKind MirrorComparison(TokenKind op);

std::vector<std::pair<std::string, ClassObject*>> ActiveRandObjectMembers(
    const ClassObject* obj, SimContext& ctx);
std::vector<JointObject> CollectActiveRandomObjects(ClassObject* obj,
                                                    const Expr* expr,
                                                    SimContext& ctx,
                                                    Arena& arena);
bool RandomizeObjectTree(SimContext& ctx, Arena& arena, const Expr* expr,
                         const std::vector<JointObject>& objects,
                         const ClassMember* inline_block);
bool EnumerateInsideItems(const std::vector<Expr*>& elements,
                          ClassObject* owner, RandomizeCtx& rc,
                          std::vector<int64_t>& out);

bool BuildRealSetDist(const Expr* rel, RandomizeCtx& rc, ConstraintExpr& out);

bool BuildDistConstraint(const ConstraintDistRef& ref, RandomizeCtx& rc,
                         ConstraintExpr& out);
void CollectConstraintArgRefs(const Expr* e, bool in_arg,
                              std::unordered_set<std::string>& all_names,
                              std::unordered_set<std::string>& arg_names);
bool IsClassHandleMember(const ClassMember* m, SimContext& ctx);
ConstraintExpr TranslateRelation(const Expr* rel, std::vector<RandInfo>& rands,
                                 RandomizeCtx& rc, bool fold = true);
void AddConstraintMember(const ClassMember* m, std::vector<RandInfo>& rands,
                         RandomizeCtx& rc, ConstraintSolver& solver);
std::vector<const ClassMember*> ConstraintMembersInOrder(
    const ClassTypeInfo* type);
void CollectConstraintBlocks(const ClassTypeInfo* type,
                             std::vector<RandInfo>& rands, RandomizeCtx& rc,
                             ConstraintSolver& solver);
const ClassMember* FindNamedProperty(const ClassTypeInfo* type, SimContext& ctx,
                                     std::string_view name,
                                     const ClassTypeInfo** out_level);
std::string_view InlineRandomArgName(const Expr* arg);
void InvokePreRandomize(ClassObject* obj, const Expr* expr, SimContext& ctx,
                        Arena& arena);
ClassObject* ResolveRandomizeTarget(SimContext& ctx,
                                    const MethodCallParts& parts);
void WriteBackSolved(ClassObject* obj, std::vector<RandInfo>& rands,
                     const ConstraintSolver& solver, const std::string& prefix,
                     Arena& arena);

bool ExtractConstraintModeParts(const Expr* expr, std::string_view& obj_name,
                                std::string_view& constraint_name);
bool ExtractRandModeParts(const Expr* expr, std::string_view& obj_name,
                          std::string_view& var_name, const Expr*& element);
void BindCallersMembers(const Expr* expr, ClassObject* obj, SimContext& ctx,
                        Arena& arena);
void BindCallersVariables(const Expr* expr, ClassObject* obj, SimContext& ctx,
                          Arena& arena);
void BindLocalQualifiedNames(const Expr* expr, SimContext& ctx, Arena& arena);
void BindObjectHandleHeads(const Expr* expr, ClassObject* obj, SimContext& ctx,
                           Arena& arena);
std::string InlineReceiverName(const Expr* call);

struct InlineRandomizeCall {
  const Expr* expr;
  const ClassMember* inline_block;
  const std::unordered_set<std::string>* inline_random;
  bool null_checker;
};

struct ObjectSolve {
  ClassObject* obj = nullptr;
  std::string prefix = {};
  std::unique_ptr<RandomizeCtx> rc = nullptr;
  std::vector<RandInfo> rands = {};
  std::unique_ptr<ConstraintSolver> solver = nullptr;
  JointVarScope joint = {};
};

bool SolveObject(ObjectSolve& part, const InlineRandomizeCall& call,
                 SimContext& ctx, Arena& arena);
bool RandomizeEachObject(const std::vector<JointObject>& objects,
                         const InlineRandomizeCall& call, SimContext& ctx,
                         Arena& arena);
void PrepareRandVariables(ClassObject* obj, std::vector<RandInfo>& rands,
                          const std::unordered_set<std::string>* inline_random,
                          ConstraintSolver& solver);
void SetObjectConstraintActive(ClassObject* obj, std::string_view name,
                               bool active);
std::unordered_map<std::string, bool>& RandModesOf(ClassObject* obj,
                                                   std::string_view name);
void SetObjectRandActive(ClassObject* obj, std::string_view name, bool active);

}  // namespace delta
