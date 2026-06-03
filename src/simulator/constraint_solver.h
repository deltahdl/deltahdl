#pragma once

#include <cstdint>
#include <functional>
#include <memory>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace delta {

enum class RandQualifier : uint8_t {
  kNone,
  kRand,
  kRandc,
};

enum class ConstraintKind : uint8_t {
  kRange,
  kSetMembership,
  kEqual,
  kNotEqual,
  kLessThan,
  kGreaterThan,
  kLessEqual,
  kGreaterEqual,
  kImplication,
  kIfElse,
  kForeach,
  kUnique,
  kDist,
  kSoft,
  kArrayReduction,
  kCustom,
};

// 18.5.7.2: the operand by which an array reduction method joins the elements.
// sum folds with addition, product with multiplication, and/or/xor with the
// corresponding bitwise operator — the "relevant operand for each method".
enum class ArrayReductionOp : uint8_t {
  kSum,
  kProduct,
  kAnd,
  kOr,
  kXor,
};

// 18.5.3: one entry of a distribution's weighted-value set. A plain integral
// item weights the single 'value'; setting is_range weights the inclusive range
// [lo, hi] instead. The weight itself is an unsigned magnitude (LRM: the weight
// expression is interpreted as an unsigned value), with an absent weight
// defaulting to 1. per_element distinguishes the two range operators: the ':='
// operator applies the weight to each element of the range, whereas ':/' (and a
// single value) applies it to the item as a whole. is_default marks the single
// 'default :/ weight' item, which stands for every domain value not named by
// any other item.
struct DistWeight {
  int64_t value = 0;
  uint32_t weight = 1;
  int64_t lo = 0;
  int64_t hi = 0;
  bool is_range = false;
  bool per_element = false;
  bool is_default = false;
};

// 18.5.12: a constraint guard is a predicate expression that gates whether a
// constraint is created, rather than a relation the solver must satisfy. Its
// subexpressions are evaluated in a four-state logic so that one that would
// otherwise raise an evaluation error (a comparison against a null handle, an
// out-of-range index) can be sifted away instead of failing randomize().
enum class GuardValue : uint8_t {
  kFalse,   // 0: the subexpression evaluates to false
  kTrue,    // 1: the subexpression evaluates to true
  kError,   // E: the subexpression causes an evaluation error
  kRandom,  // R: the subexpression involves as-yet-unsolved random variables
};

// 18.5.12 / Figure 18-3: combine guard subexpression values under the three
// logical operators. These reproduce the conjunction, disjunction, and
// negation truth tables over {FALSE, TRUE, ERROR, RANDOM}.
GuardValue GuardAnd(GuardValue a, GuardValue b);
GuardValue GuardOr(GuardValue a, GuardValue b);
GuardValue GuardNot(GuardValue a);

// 18.5.12: the action that a fully evaluated guard imposes on its guarded set.
enum class GuardOutcome : uint8_t {
  kUnconditional,  // final TRUE: the guarded constraint is generated outright
  kEliminated,     // final FALSE: the guarded constraint is dropped, no error
  kError,          // final ERROR: an error is generated and randomize() fails
  kConditional,    // final RANDOM: a conditional constraint is generated
};

GuardOutcome GuardFinalOutcome(GuardValue final_value);

// 18.5.12: a guard predicate is a tree of subexpressions joined by the logical
// operators. A leaf reports the four-state value of one atomic subexpression
// over the current variable values, so it can yield kError (e.g., a null
// handle comparison) or kRandom (the subexpression depends on a random
// variable). The operators are applied recursively until every subexpression
// has been evaluated.
struct GuardPredicate {
  enum class Op : uint8_t { kLeaf, kAnd, kOr, kNot } op = Op::kLeaf;
  std::function<GuardValue(const std::unordered_map<std::string, int64_t>&)>
      leaf_fn;
  std::vector<GuardPredicate> operands;
};

GuardValue EvaluateGuard(
    const GuardPredicate& pred,
    const std::unordered_map<std::string, int64_t>& values);

struct ConstraintExpr {
  ConstraintKind kind = ConstraintKind::kRange;
  std::string var_name;
  int64_t lo = 0;
  int64_t hi = 0;
  std::vector<int64_t> set_values;
  std::vector<DistWeight> dist_weights;

  std::string cond_var;
  int64_t cond_value = 0;
  std::vector<ConstraintExpr> sub_constraints;

  // 18.5.7.1: for a foreach iterative constraint over a dynamically sized array
  // (dynamic array or queue), size_var names the array's size method. The size
  // is fixed by the size constraints, which are solved before this iterative
  // constraint; within the foreach block the size method is therefore a state
  // variable, so the solver reads its already-committed value and imposes the
  // per-element constraints (sub_constraints) only on the elements that exist,
  // i.e. those whose index is below that size. Left empty for a fixed-size
  // array, in which case every per-element constraint applies.
  std::string size_var;

  // 18.5.5: the antecedent of an implication ("a" in a -> b) may be any
  // integral or real expression, not only an equality test. When cond_fn is
  // set it supplies the truth of the antecedent over the current values and
  // takes precedence over the cond_var == cond_value short form above.
  std::function<bool(const std::unordered_map<std::string, int64_t>&)> cond_fn;

  // 18.5.6: an if-else constraint guards two constraint sets with a condition.
  // sub_constraints holds the "then" set applied when the condition is true;
  // else_constraints holds the optional "else" set applied when it is false.
  // The condition is supplied by cond_fn (any integral or real expression) or
  // the cond_var == cond_value short form, exactly as for an implication.
  std::vector<ConstraintExpr> else_constraints;

  std::vector<std::string> unique_vars;

  // 18.5.7.2: an array reduction iterative constraint. In a constraint, an array
  // reduction method is treated as an expression iterated over each element of
  // the array, joined by the operand for that method (reduce_op). reduce_vars
  // names the array's element variables in index order; reduce_with, when set,
  // is the with-clause expression applied to each element value (the with-clause
  // 'item') before it is folded, defaulting to the element value itself. The
  // folded result — a single value — is compared against 'lo' under the relation
  // reduce_cmp. reduce_width is the bit width of that result's type: the array
  // element type by default, or the type of the with-clause expression when one
  // is given, so the fold is truncated to that width exactly as the result type
  // demands. As with a foreach iterative constraint, when the array is
  // dynamically sized size_var names its size method; the size constraints are
  // solved first, so only the elements whose index is below the committed size
  // take part in the reduction.
  ArrayReductionOp reduce_op = ArrayReductionOp::kSum;
  std::vector<std::string> reduce_vars;
  std::function<int64_t(int64_t)> reduce_with;
  ConstraintKind reduce_cmp = ConstraintKind::kLessThan;
  uint32_t reduce_width = 32;

  ConstraintExpr* inner = nullptr;

  std::function<bool(const std::unordered_map<std::string, int64_t>&)> eval_fn;

  // 18.5.12: an optional constraint guard. When has_guard is set, the guard is
  // evaluated before this constraint is imposed: a FALSE guard eliminates the
  // constraint with no error, an ERROR guard makes randomize() fail, and a
  // TRUE or RANDOM guard lets the constraint be generated (unconditionally or
  // conditionally). Both implication (->) and if...else may serve as guards.
  bool has_guard = false;
  GuardPredicate guard;
};

struct ConstraintBlock {
  std::string name;
  bool enabled = true;
  std::vector<ConstraintExpr> constraints;

  // 18.5.10: a constraint block declared static shares one on/off state across
  // every instance of the class, so a constraint_mode() call on any instance
  // turns the constraint on or off for all of them. is_static marks such a
  // block; shared_enabled, when set, holds that one shared state and is
  // consulted in place of the per-instance 'enabled' flag. A nonstatic block
  // leaves shared_enabled null and keeps its own independent state.
  bool is_static = false;
  std::shared_ptr<bool> shared_enabled;
};

struct RandVariable {
  std::string name;
  RandQualifier qualifier = RandQualifier::kRand;
  int64_t min_val = 0;
  int64_t max_val = 0xFFFF;
  uint32_t width = 32;

  // 18.4.1: a rand variable may be of real type, in which case its random value
  // is uniformly distributed over its range rather than over an integral
  // domain. is_real selects the real generation path; [real_min, real_max) is
  // the range the value is drawn from with a flat density, so that equal-width
  // subranges are equally likely (18.4 forbids declaring a real variable randc,
  // so only the noncyclical rand path applies here). real_value holds the
  // variable's current real value, kept as a constant when it is inactive.
  bool is_real = false;
  double real_min = 0.0;
  double real_max = 0.0;
  double real_value = 0.0;

  // 18.8: a random variable carries an active state that rand_mode() controls
  // and that is initially ON. 18.5.8: only the active random variables are the
  // ones randomized; every other variable reference is treated as a state
  // variable whose current value is used as a constant. 'enabled' is that
  // active state, shared by both clauses.
  bool enabled = true;

  // 18.8 / 18.5.8: the variable's current value. When the variable is inactive
  // (rand_mode() OFF) the solver does not draw a fresh value for it; instead it
  // holds this value as a constant, so a global constraint (18.5.8) that
  // references the inactive variable from an active variable solved alongside
  // it sees a fixed operand rather than a random one.
  int64_t value = 0;

  // 18.3: for an active random variable of enum type, the solver shall select
  // a value only from the set of named constants of that enum. When non-empty,
  // enum_values is that named-constant set and confines the chosen value.
  std::vector<int64_t> enum_values;

  // 18.4: an enum member of a packed structure or packed untagged union that
  // is declared rand is exempt from the 18.3 enum-domain restriction. Clearing
  // this flag keeps the enum_values set for reference but lets the solver draw
  // from the full declared range.
  bool apply_enum_restriction = true;

  std::unordered_set<int64_t> randc_history;

  // 18.4.2: when a random variable is declared static, its randc state is
  // static as well — a single cyclic permutation is shared by every instance of
  // the class, so randomize() advances that one sequence no matter which
  // instance drives it. is_static marks such a variable. shared_randc_state,
  // when set, is the one shared permutation history; it is used in place of the
  // per-instance randc_history above so all instances draw from and advance the
  // same cycle. A nonstatic randc leaves this null and keeps its own history.
  bool is_static = false;
  std::shared_ptr<std::unordered_set<int64_t>> shared_randc_state;

  // 18.5.7.1: marks a variable that holds a dynamic array's size method. Such a
  // variable is committed in a pass that runs before the general rand variables
  // — mirroring the rule that an array's size constraints are solved before the
  // iterative (foreach) constraints over that array — so a foreach reading the
  // size sees the value already chosen and treats it as a state variable.
  bool is_array_size = false;
};

using RandomizeCallback = std::function<void()>;

class ConstraintSolver {
 public:
  explicit ConstraintSolver(uint32_t seed = 0);

  void AddVariable(const RandVariable& var);

  void AddConstraintBlock(const ConstraintBlock& block);

  // 18.5.9: record a 'solve before_list before after_list' ordering constraint.
  // Every variable in 'before' is to be solved before every variable in 'after',
  // which alters the probability distribution over legal value combinations
  // without changing the set of legal combinations. The ordering is partial:
  // calling this more than once accumulates the constraints. A solve...before
  // ordering never removes a solution, so it cannot by itself cause a solve to
  // fail.
  void AddSolveBefore(const std::vector<std::string>& before,
                      const std::vector<std::string>& after);

  bool Solve();

  bool SolveWith(const std::vector<ConstraintExpr>& inline_constraints);

  // 18.12: a scope randomize invoked with no random-variable arguments behaves
  // as a checker rather than a generator. It shall not change the value of any
  // variable; instead every constraint expression — those of the enabled blocks
  // together with any passed in 'constraints' (the with constraint_block) — is
  // evaluated against the variables' current values. The call returns false (0)
  // as soon as one expression is false and true (1) only when all of them hold.
  bool Check(const std::vector<ConstraintExpr>& constraints = {});

  // 18.11.1: the inline constraint checker. Passing the special argument null to
  // randomize() designates an empty set of random variables for the duration of
  // the call, so every class member — including any declared rand or randc —
  // behaves as a state variable and the solver assigns no new value to any of
  // them. With no active random variable left, randomize() acts as a checker
  // rather than a generator: it evaluates every constraint (the enabled blocks
  // plus any 'constraints' supplied by a with clause) against the members'
  // current values and returns true (1) only when all of them hold, false (0)
  // as soon as one does not. A class that declares no random variables at all
  // reduces to this same checker behavior even without the null argument.
  bool InlineConstraintCheck(const std::vector<ConstraintExpr>& constraints = {});

  int64_t GetValue(std::string_view name) const;

  // 18.4.1: the real value drawn for a rand real variable by the most recent
  // solve. Returns 0.0 for an unknown name or a variable that is not real.
  double GetRealValue(std::string_view name) const;

  void SetRandMode(std::string_view name, bool enabled);
  bool GetRandMode(std::string_view name) const;

  // 18.8: when rand_mode() names no specific random_variable, the void form
  // applies to every random variable in the object at once. This sets the
  // active state of all known variables in a single call.
  void SetAllRandMode(bool enabled);

  // 18.11: apply the inline random variable control list, i.e. the argument
  // list passed to randomize(). The named variables become the complete set of
  // active random variables for the call; every other variable known to the
  // solver is treated as a state variable (made inactive). This is equivalent
  // to a set of rand_mode() calls that enable the named variables and disable
  // all the others. The cyclical random mode is never affected: a variable
  // keeps its rand/randc qualifier, so a noncyclical variable named in the list
  // is not promoted to cyclical and a randc variable is not demoted.
  void ApplyInlineRandomList(const std::vector<std::string>& names);

  // 18.8 / 18.5.8: record a variable's current value. An inactive variable
  // keeps this value as a constant while the active variables are randomized,
  // which is the state-variable treatment that global constraints rely on.
  void SetValue(std::string_view name, int64_t value);

  void SetConstraintMode(std::string_view block_name, bool enabled);
  bool GetConstraintMode(std::string_view block_name) const;

  void SetPreRandomize(RandomizeCallback cb);
  void SetPostRandomize(RandomizeCallback cb);

  const std::unordered_map<std::string, int64_t>& GetValues() const;

 private:

  int64_t GenerateRandValue(RandVariable& var);

  // 18.4.1: draw a uniformly distributed real value over [real_min, real_max).
  // A flat density makes any two equal-width subranges equally probable, which
  // is the uniform-distribution guarantee the clause states for rand real.
  double GenerateRandRealValue(RandVariable& var);

  int64_t DistributionSample(const std::vector<DistWeight>& weights,
                             int64_t domain_lo, int64_t domain_hi);

  int64_t SampleDefaultValue(const std::vector<DistWeight>& weights,
                             int64_t domain_lo, int64_t domain_hi);

  int64_t SampleDist(const ConstraintExpr& c);

  // 18.5.3: a dist operation shall not be applied to a randc variable. True if
  // any enabled constraint block applies a distribution to a randc variable.
  bool HasDistOnRandc() const;

  // 18.5.3: a dist expression requires that it contain at least one rand
  // variable. In the solver model a distribution names the single variable it
  // constrains, so that variable must be an active rand variable. True if any
  // enabled distribution targets a variable that supplies no rand variable
  // (one that is unknown to the solver or declared without the rand
  // qualifier).
  bool DistLacksRandVariable() const;

  // 18.5.4: no randc variable shall appear in the group of a uniqueness
  // constraint. True if any enabled unique constraint names a variable that is
  // declared randc, in which case randomization fails outright.
  bool HasRandcInUnique() const;

  // 18.5.4: all members of a uniqueness constraint group shall be of equivalent
  // type. The solver characterizes a member's type by whether it is real and by
  // its bit width, so members that disagree on either are not of equivalent
  // type. True if any enabled unique constraint mixes such members, which is an
  // illegal group and makes randomization fail.
  bool UniqueMembersNotEquivalentType() const;

  bool ApplyConstraint(const ConstraintExpr& expr);

  // 18.5.13: when include_soft is set, the soft constraints are enforced
  // alongside the hard constraints; when clear, the soft constraints are
  // discarded (each treated as the value true) and only the hard constraints
  // are checked.
  bool CheckAllConstraints(const std::vector<ConstraintExpr>& extra,
                           bool include_soft);

  bool EvalConstraint(const ConstraintExpr& expr) const;

  bool EvalImplication(const ConstraintExpr& expr) const;

  bool EvalIfElse(const ConstraintExpr& expr) const;

  bool EvalForeach(const ConstraintExpr& expr) const;

  // 18.5.7.2: evaluate an array reduction iterative constraint. Fold the array's
  // existing elements (those below the committed size when the array is
  // dynamically sized) with the method's operand, applying the with-clause
  // expression to each element first, then truncate to the result type's width
  // and test the configured relation against the target value.
  bool EvalArrayReduction(const ConstraintExpr& expr) const;

  bool EvalUnique(const ConstraintExpr& expr) const;

  // 18.5.10: refresh each static block's per-instance 'enabled' flag from its
  // shared state, so a constraint_mode() call routed through another instance of
  // the class is observed here before the constraints are evaluated.
  void RefreshStaticBlockState();

  void ApplyDistConstraints();

  void ApplyDirectConstraints(const std::vector<ConstraintExpr>& extra,
                              bool include_soft);

  bool SolveIterative(const std::vector<ConstraintExpr>& extra,
                      bool include_soft);

  // 18.5.9: partition the given active rand variables into ordered solve groups
  // honoring the recorded solve...before constraints. Each group is solved in
  // turn, earliest first; a variable is placed as late as the ordering allows
  // (its distance to the end of the longest chain that depends on it), so that
  // variables with nothing ordered after them — including every variable that is
  // not explicitly ordered — fall into the final group and are solved last. The
  // groups are returned earliest-first; empty groups are omitted.
  std::vector<std::vector<std::string>> ComputeSolveGroups(
      const std::vector<std::string>& vars) const;

  // 18.5.9: solve the ordered groups by staged generate-and-test. Variables in
  // an earlier group are drawn and committed before the later groups are solved
  // against them, so an earlier variable's value is held fixed while the later
  // variables are completed. An earlier value is kept whenever some completion of
  // the remaining groups satisfies every constraint; only when no completion
  // exists is it redrawn. This reproduces the solve...before distribution (an
  // ordered variable is chosen over its own legal values, then the dependent
  // variables subject to it) while preserving the full solution space.
  bool SolveOrderedGroups(const std::vector<std::vector<std::string>>& groups,
                          size_t idx, const std::vector<ConstraintExpr>& extra,
                          bool include_soft);

  std::mt19937 rng_;
  std::unordered_map<std::string, RandVariable> variables_;
  std::vector<ConstraintBlock> blocks_;
  std::unordered_map<std::string, int64_t> values_;
  // 18.4.1: solved values for rand real variables, kept apart from the integral
  // values_ map since their domain is the reals.
  std::unordered_map<std::string, double> real_values_;
  RandomizeCallback pre_randomize_;
  RandomizeCallback post_randomize_;

  // 18.5.9: the recorded solve...before ordering edges. Each pair (before,
  // after) requires 'before' to be solved ahead of 'after'. Empty when no
  // ordering constraint applies, in which case the solver uses its default
  // single-pass generate-and-test, which already draws each legal value
  // combination with uniform probability.
  std::vector<std::pair<std::string, std::string>> solve_before_edges_;

  // 18.5.12: set when a guard evaluates to ERROR. An ERROR guard generates an
  // unconditional error, so the solve fails outright and is not retried.
  bool guard_error_ = false;
};

}
