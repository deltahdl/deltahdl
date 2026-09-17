#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

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

  // 18.5.7: for an element of a rand member declared as an array, the name of
  // that member, so a relation naming the array whole -- a reduction method
  // over it, a select at an index the solver does not fold -- is read as
  // referencing the element, and the element's index. 18.5.7.1: for the size
  // of a rand member declared as a dynamic array, which `var.is_array_size`
  // marks, the name of that member as well, so that rand_mode() on the
  // member holds the size with the elements. Empty for a variable that is
  // neither.
  std::string array_base;
  int64_t array_index = 0;
};

// State threaded through the randomize() build helpers; bundled to keep helper
// parameter lists small.
struct RandomizeCtx {
  ClassObject* obj;
  SimContext& ctx;
  Arena& arena;
  // 18.5.5: the solver the relations are built for, which a relation
  // evaluated over a trial reads the real variables' draws from: the trial
  // handed to it holds the integral draws alone, a real variable being drawn
  // into the solver's real values (18.4.1), so an antecedent or relation
  // written over a real variable read it as 0 without this.
  const ConstraintSolver* solver = nullptr;
  // 18.5.13: stable storage for the inner relation of each soft constraint. A
  // kSoft ConstraintExpr points to its inner relation through a raw pointer, so
  // the inner must outlive the solve; owning it on the heap here keeps that
  // address stable even as the solver copies the block holding the kSoft.
  std::vector<std::unique_ptr<ConstraintExpr>> soft_inners = {};
  // The locals a trial binds the random variables to, by name, made once
  // per randomize() call and bound to each trial's values in place: a
  // relation over a wide domain is evaluated some hundred times per call,
  // and a local made per evaluation is arena storage the run never gets
  // back (eval_randomize_custom.cpp).
  std::unordered_map<std::string, Variable*> trial_locals = {};
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

// A copy of an expression with the nodes `rewrite` answers for replaced by
// its answer, the others copied over their rewritten children; a node the
// rewrite answers null for is copied (eval_randomize_iterative.cpp).
using ExprRewrite = std::function<Expr*(const Expr*)>;
Expr* RewriteExpr(const Expr* e, const ExprRewrite& rewrite, Arena& arena);
// An identifier node spelling `text`, the text held by the arena, placed
// where `like` was (eval_randomize_iterative.cpp).
Expr* IdentifierExpr(std::string_view text, const Expr* like, Arena& arena);

RandInfo* FindRand(std::vector<RandInfo>& rands, std::string_view name);
// Whether `e`, or any expression in `list`, references one of the random
// variables.
bool RefsRandVar(const Expr* e, std::vector<RandInfo>& rands);
bool AnyRefsRandVar(const std::vector<Expr*>& list,
                    std::vector<RandInfo>& rands);
// 18.5.4: `rel` as `x inside { ... }` over a rand variable and items free of
// random variables, a set membership the solver draws a member of; fills
// `out` and answers true, any other shape answering false
// (eval_randomize_membership.cpp).
bool TrySetMembershipConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                                RandomizeCtx& rc, ConstraintExpr& out);
// 18.5.5: `rel` as `antecedent -> relation`, the parser's form of every
// implication and if-else constraint, as the solver's implication over the
// relation translated, which the solver applies where the antecedent holds;
// answers false where the relation would be a tried one anyway
// (eval_randomize_membership.cpp).
bool TryImplicationConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                              RandomizeCtx& rc, ConstraintExpr& out);
// Evaluates `rel` with each name in `names` bound to its value in `vals`,
// as a truth or as the value it takes.
bool EvalCustomRelation(const Expr* rel, const std::vector<std::string>& names,
                        RandomizeCtx& rc,
                        const std::unordered_map<std::string, int64_t>& vals);
int64_t EvalCustomValue(const Expr* e, const std::vector<std::string>& names,
                        RandomizeCtx& rc,
                        const std::unordered_map<std::string, int64_t>& vals);
// Whether `e` references the random variable `name`, bare or as this.name.
bool RefsNamedRandVar(const Expr* e, std::string_view name);
// Writes the integral `v` into the words of `value`, held to its width: how
// a trial binds a local it made once to each value it evaluates over
// (eval_randomize_custom.cpp).
void SetLocalWords(Logic4Vec& value, int64_t v);
// 18.5: `rel` as the solver's kCustom relation, evaluated against the values
// drawn, referencing the random variables it names and, where it is `x ==
// expression` over the others, deriving x from them
// (eval_randomize_custom.cpp).
ConstraintExpr MakeCustomConstraint(const Expr* rel,
                                    std::vector<RandInfo>& rands,
                                    RandomizeCtx& rc);
// 18.5.7: `rel` as an array reduction method over a rand array member --
// sum, product, and, or or xor, with no with clause -- compared against a
// value free of random variables, as the solver's reduction over the
// element variables in index order; answers false for any other shape
// (eval_randomize_iterative.cpp).
bool TryArrayReductionConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                                 RandomizeCtx& rc, ConstraintExpr& out);
// 18.5.7: build each foreach iterative constraint of the member `m` into
// `block`: the relations of its constraint_set instanced once per element of
// the array, the loop variable standing for the element's index and a select
// of the array at the loop variable for the element's variable, each
// translated as a relation written in the block would be
// (eval_randomize_iterative.cpp).
void AddForeachConstraints(const ClassMember* m, std::vector<RandInfo>& rands,
                           RandomizeCtx& rc, ConstraintBlock& block);
// 18.5: `rel` as `a && b`, which holds where both do, as the solver's
// implication of both under an antecedent that always holds, each side
// translated on its own so that a comparison among them folds the domain
// as it would alone; answers false for any other shape
// (eval_randomize_membership.cpp).
bool TryConjunctionConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                              RandomizeCtx& rc, ConstraintExpr& out, bool fold);
void CollectRandVariables(const ClassTypeInfo* type, SimContext& ctx,
                          std::vector<RandInfo>& out);
// 18.4: the solver variable for the rand/randc data member `m` declared at
// `level`, drawn over the range its declared type admits; a member declared
// as an array is built once and copied per element by the caller.
RandInfo BuildRandMember(const ClassMember* m, const ClassTypeInfo* level,
                         SimContext& ctx);
// 18.4/18.5.7.1: add the random variables of each rand member of the object
// declared as a dynamic array: where an active constraint block constrains
// the member's size method, one variable for the size, drawn ahead of the
// others, and one per element up to the largest size the size constraints
// admit; otherwise one per element the array holds, its size being left as
// it is (eval_randomize_dynamic.cpp).
void AddDynamicArrayVariables(std::vector<RandInfo>& rands, RandomizeCtx& rc);
// 18.5.7.1: `rel` with each size method call on a dynamic array property of
// the object's class, `A.size` or `A.size()`, replaced by the identifier of
// the key the size is held under, which is the size variable's name where
// the size is solved and the object's own count where it is not; `rel`
// itself where it holds no such call (eval_randomize_dynamic.cpp).
const Expr* ResolveArraySizes(const Expr* rel, RandomizeCtx& rc);
bool ComparisonKind(TokenKind op, ConstraintKind& out);
void FoldBound(RandInfo& ri, ConstraintKind kind, int64_t c);
// 18.4.1: the same for a real variable's range, a bound on one side leaving
// the other and an equality closing both on the value.
void FoldRealBound(RandInfo& ri, ConstraintKind kind, double c);
// Folds the comparison of the rand variable `name` against the constant
// `cv`, `c` as an integer, into its domain, a real one's range through
// FoldRealBound and an integral one's bounds through FoldBound; a name that
// is no rand variable folds nothing.
void FoldComparison(std::vector<RandInfo>& rands, std::string_view name,
                    ConstraintKind kind, const Logic4Vec& cv, int64_t c);
// 18.6.1: the value the solver drew for `ri` as the member holds it, 18.4.1
// a real as the real it is and 6.11.3 an integral one in the member's
// declared signedness.
Logic4Vec SolvedValue(const RandInfo& ri, const ConstraintSolver& solver,
                      Arena& arena);
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
// 18.5/18.5.2/18.5.13.1: the constraint members of the class chain of `type`
// with a body the solver can act on, a base class's ahead of a derived
// one's and a same-named base one replaced by the derived one
// (eval_randomize_blocks.cpp).
std::vector<const ClassMember*> ConstraintMembersInOrder(
    const ClassTypeInfo* type);
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
