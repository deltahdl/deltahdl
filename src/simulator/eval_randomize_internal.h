#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

// Shared between eval_randomize.cpp, which randomizes a single object, and
// eval_randomize_joint.cpp, which randomizes an object tree in one solve.

// 18.5.11: a constraint expression is written inside a class body, so it names
// the class's own members without qualification -- a property, or a call to one
// of its own methods. Resolving either needs the object in scope: an
// unqualified identifier is read as a property of `this` against the enclosing
// class (8.6/8.15), and an unqualified call is resolved against the enclosing
// class and the classes it inherits from (8.13). Evaluating a constraint
// expression with neither in scope leaves an unqualified call resolving to no
// method at all, and a call that resolves to nothing yields zero -- which is
// exactly the value 18.5.11 requires be the function's return value, "treated
// as a state variable" by the constraint that consumes it.
//
// Holds the object in scope for as long as the guard lives, and steps back out
// when it is destroyed, so an evaluation that returns early cannot leave the
// scope stack unbalanced. A null object (or one with no class type) binds
// nothing, leaving whatever scope the caller was already in.
class ConstraintEvalScope {
 public:
  ConstraintEvalScope(ClassObject* obj, SimContext& ctx)
      : ctx_(ctx), bound_(obj != nullptr && obj->type != nullptr) {
    if (!bound_) return;
    ctx_.PushThis(obj);
    ctx_.PushMethodClass(obj->type);
  }

  ~ConstraintEvalScope() {
    if (!bound_) return;
    ctx_.PopMethodClass();
    ctx_.PopThis();
  }

  ConstraintEvalScope(const ConstraintEvalScope&) = delete;
  ConstraintEvalScope& operator=(const ConstraintEvalScope&) = delete;
  ConstraintEvalScope(ConstraintEvalScope&&) = delete;
  ConstraintEvalScope& operator=(ConstraintEvalScope&&) = delete;

 private:
  SimContext& ctx_;
  bool bound_;
};

// A rand/randc variable discovered on the randomized object, paired with the
// class level that declares it (for the scoped "Class::name" property alias)
// and the solver variable being built for it.
struct RandInfo {
  std::string name;
  const ClassTypeInfo* level = nullptr;
  // 18.4.2: a static randc shares its cyclic permutation across every instance
  // of the declaring class, so its history is stored on the (shared) class type
  // rather than on the object. Track the static-ness of the source member here.
  bool is_static = false;
  RandVariable var;

  // 18.5.8: in a joint (global-constraint) solve the same variable name can
  // appear on several objects, so 'name' carries a path-qualified name unique
  // across the whole active random object tree while 'member' keeps the plain
  // property name and 'owner' names the object the value is written back to.
  // For an ordinary single-object solve owner stays null and member stays
  // empty, and the single object's own name/level are used, so nothing changes
  // there.
  std::string member;
  ClassObject* owner = nullptr;
};

// State threaded through the randomize() build helpers; bundled to keep helper
// parameter lists small.
struct RandomizeCtx {
  ClassObject* obj;
  SimContext& ctx;
  Arena& arena;
  // 18.5.13: stable storage for the inner relation of each soft constraint. A
  // kSoft ConstraintExpr points to its inner relation through a raw pointer, so
  // the inner must outlive the solve; owning it on the heap here keeps that
  // address stable even as the solver copies the block holding the kSoft.
  std::vector<std::unique_ptr<ConstraintExpr>> soft_inners = {};
};

// 18.5.8: one active random object taking part in a joint solve, paired with
// the dotted path prefix under which its variables and constraints are named in
// the single shared solver. The root object has an empty prefix; an object
// reached through the root's rand handle 'h' has prefix "h.", one two levels
// down "h.g.", and so on.
struct JointObject {
  ClassObject* obj;
  std::string prefix;
};

// 18.5.8: the joint solve's variable set as one object's constraints see it --
// the object whose scope a relation is evaluated in, the path prefix its
// members are named under in the shared solver, the shared list of joint random
// variables, and the set of their qualified solver names.
struct JointVarScope {
  ClassObject* owner;
  const std::string& prefix;
  std::vector<RandInfo>& rands;
  const std::unordered_set<std::string>& names;
};

RandInfo* FindRand(std::vector<RandInfo>& rands, std::string_view name);
void CollectRandVariables(const ClassTypeInfo* type, SimContext& ctx,
                          std::vector<RandInfo>& out);
bool ComparisonKind(TokenKind op, ConstraintKind& out);
void FoldBound(RandInfo& ri, ConstraintKind kind, int64_t c);
bool IsObjectConstraintActive(const ClassObject* obj, std::string_view name);
bool IsObjectRandActive(const ClassObject* obj, std::string_view name);
void InvokePostRandomize(ClassObject* obj, const Expr* expr, SimContext& ctx,
                         Arena& arena);
void CollectRandObjectMembers(const ClassTypeInfo* type, SimContext& ctx,
                              std::vector<std::string>& out);

TokenKind MirrorComparison(TokenKind op);

void CollectActiveRandomObjects(
    ClassObject* obj, const std::string& prefix, SimContext& ctx,
    std::vector<JointObject>& out,
    std::unordered_set<const ClassObject*>& visited);
bool RandomizeObjectTree(SimContext& ctx, Arena& arena, const Expr* expr,
                         const std::vector<JointObject>& objects);

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
void CollectConstraintBlocks(const ClassTypeInfo* type,
                             std::vector<RandInfo>& rands, RandomizeCtx& rc,
                             ConstraintSolver& solver);
const ClassMember* FindNamedProperty(const ClassTypeInfo* type, SimContext& ctx,
                                     std::string_view name,
                                     const ClassTypeInfo** out_level);
std::string_view InlineRandomArgName(const Expr* arg);
void RegisterPreRandomize(ClassObject* obj, const Expr* expr, SimContext& ctx,
                          Arena& arena, ConstraintSolver& solver);
ClassObject* ResolveRandomizeTarget(SimContext& ctx,
                                    const MethodCallParts& parts);
void WriteBackSolved(ClassObject* obj, std::vector<RandInfo>& rands,
                     ConstraintSolver& solver, Arena& arena);

bool ExtractConstraintModeParts(const Expr* expr, std::string_view& obj_name,
                                std::string_view& constraint_name);
bool ExtractRandModeParts(const Expr* expr, std::string_view& obj_name,
                          std::string_view& var_name);
// 18.7/18.11/18.11.1: what one randomize() call adds on top of the object's own
// declaration -- the call expression, the inline constraint block of a
// `with { ... }` clause, the argument list naming the call's complete active
// random set (null when the call takes no arguments), and whether this is the
// randomize(null) inline constraint checker.
struct InlineRandomizeCall {
  const Expr* expr;
  const ClassMember* inline_block;
  const std::unordered_set<std::string>* inline_random;
  bool null_checker;
};

bool RandomizeObject(ClassObject* obj, SimContext& ctx, Arena& arena,
                     const InlineRandomizeCall& call,
                     std::unordered_set<const ClassObject*>& visited);
void SetObjectConstraintActive(ClassObject* obj, std::string_view name,
                               bool active);
void SetObjectRandActive(ClassObject* obj, std::string_view name, bool active);

}  // namespace delta
